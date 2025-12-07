// VMemDemote - Video Memory Demotion and Allocation ETW Tracker
// Tracks video memory allocations and when they are demoted to system memory

#define INITGUID
#include <windows.h>
#include <evntrace.h>
#include <evntcons.h>
#include <tdh.h>
#include <psapi.h>
#include <tlhelp32.h>
#include <stdio.h>
#include <string>
#include <atomic>
#include <algorithm>
#include <cwctype>
#include <unordered_map>
#include <unordered_set>
#include <mutex>

#pragma comment(lib, "tdh.lib")
#pragma comment(lib, "advapi32.lib")

// Microsoft-Windows-DxgKrnl provider GUID
// {802ec45a-1e99-4b83-9920-87c98277ba9d}
DEFINE_GUID(DXGKRNL_PROVIDER_GUID,
    0x802ec45a, 0x1e99, 0x4b83, 0x99, 0x20, 0x87, 0xc9, 0x82, 0x77, 0xba, 0x9d);

// Session name for our ETW trace
static const wchar_t* SESSION_NAME = L"VMemDemoteSession";

// Global state
static std::wstring g_targetExeName;
static std::atomic<bool> g_running{ true };
static TRACEHANDLE g_sessionHandle = 0;
static TRACEHANDLE g_traceHandle = INVALID_PROCESSTRACE_HANDLE;
static bool g_debugMode = false;

// Track the current target process PID (0 = no active target)
static std::atomic<DWORD> g_currentTargetPid{ 0 };

// Statistics tracking
static std::atomic<ULONGLONG> g_totalAllocated{ 0 };
static std::atomic<ULONGLONG> g_totalFreed{ 0 };
static std::atomic<ULONGLONG> g_totalEvicted{ 0 };
static std::atomic<ULONGLONG> g_totalMadeResident{ 0 };
static std::atomic<ULONG> g_allocationCount{ 0 };
static std::atomic<ULONG> g_freeCount{ 0 };
static std::atomic<ULONG> g_evictionCount{ 0 };
static std::atomic<ULONG> g_madeResidentCount{ 0 };

// Track demoted commitment from VidMmProcessDemotedCommitmentChange events
static std::atomic<ULONGLONG> g_currentDemotedCommitment{ 0 };
static std::atomic<ULONGLONG> g_peakDemotedCommitment{ 0 };

// Allocation tracking: maps allocation pointer (hVidMmGlobalAlloc) to size
static std::unordered_map<ULONGLONG, ULONGLONG> g_allocationSizeMap;
static std::mutex g_allocationMapMutex;

// Track pVidMmAlloc pointers that belong to our target process -> size
// We learn ownership from VidMmMakeResident events where header ProcessId is target
static std::unordered_map<ULONGLONG, ULONGLONG> g_targetAllocSizeMap;
static std::mutex g_targetAllocMutex;

// Track pDxgAdapterAllocation from Start events to correlate with Stop events
// Maps pDxgAdapterAllocation -> (process belongs to target)
static std::unordered_set<ULONGLONG> g_targetAdapterAllocations;
static std::mutex g_adapterAllocMutex;


// Event type enumeration
enum class EventType {
    Allocation,      // VidMmAlloc - memory allocated
    Free,            // VidMmFree - memory freed
    Eviction,        // VidMmEvictAllocation - memory demoted/evicted from VRAM
    MadeResident,    // VidMmMakeResident - memory made resident in VRAM (undemoted)
    Unknown
};

// DxgKrnl task names we're interested in (discovered via -debug mode)
static const wchar_t* TASK_ADAPTER_ALLOCATION = L"AdapterAllocation";         // Allocation created (has allocSize)
static const wchar_t* TASK_TERMINATE_ALLOCATION = L"TerminateAllocation";     // Allocation freed
static const wchar_t* TASK_VIDMM_EVICT = L"VidMmEvict";                       // Memory evicted from VRAM
static const wchar_t* TASK_VIDMM_MAKE_RESIDENT = L"VidMmMakeResident";        // Memory made resident in VRAM
static const wchar_t* TASK_VIDMM_PROCESS_USAGE_CHANGE = L"VidMmProcessUsageChange"; // Memory usage delta (has size info)

// Convert string to lowercase for case-insensitive comparison
std::wstring ToLower(const std::wstring& str) {
    std::wstring result = str;
    std::transform(result.begin(), result.end(), result.begin(),
        [](wchar_t c) { return static_cast<wchar_t>(std::towlower(c)); });
    return result;
}

// Get process name from PID
std::wstring GetProcessName(DWORD pid) {
    std::wstring name;
    HANDLE hProcess = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (hProcess) {
        wchar_t buffer[MAX_PATH];
        DWORD size = MAX_PATH;
        if (QueryFullProcessImageNameW(hProcess, 0, buffer, &size)) {
            // Extract just the filename
            wchar_t* lastSlash = wcsrchr(buffer, L'\\');
            name = lastSlash ? (lastSlash + 1) : buffer;
        }
        CloseHandle(hProcess);
    }
    return name;
}

// Check if a PID belongs to our target process
bool IsTargetProcess(DWORD pid) {
    std::wstring processName = GetProcessName(pid);
    if (processName.empty()) {
        return false;
    }
    return ToLower(processName) == ToLower(g_targetExeName);
}

// Reset all statistics and tracking data (called when target process restarts)
void ResetStatistics() {
    // Reset counters
    g_totalAllocated = 0;
    g_totalFreed = 0;
    g_totalEvicted = 0;
    g_totalMadeResident = 0;
    g_allocationCount = 0;
    g_freeCount = 0;
    g_evictionCount = 0;
    g_madeResidentCount = 0;
    g_currentDemotedCommitment = 0;
    g_peakDemotedCommitment = 0;

    // Clear allocation tracking maps
    {
        std::lock_guard<std::mutex> lock(g_allocationMapMutex);
        g_allocationSizeMap.clear();
    }
    {
        std::lock_guard<std::mutex> lock(g_targetAllocMutex);
        g_targetAllocSizeMap.clear();
    }
    {
        std::lock_guard<std::mutex> lock(g_adapterAllocMutex);
        g_targetAdapterAllocations.clear();
    }
}

// Check if a PID is our target and handle process start/restart
// Returns true if this is the target process, false otherwise
bool CheckTargetProcess(DWORD pid) {
    if (pid == 0) {
        return false;
    }

    // Quick check: if this is the current tracked PID, it's definitely target
    DWORD currentPid = g_currentTargetPid.load();
    if (currentPid != 0 && pid == currentPid) {
        return true;
    }

    // Check if this PID matches our target process name
    if (!IsTargetProcess(pid)) {
        return false;
    }

    // This PID matches target process name
    // Check if this is a new/different process instance
    if (currentPid == 0) {
        // First time seeing the target process
        g_currentTargetPid = pid;
        wprintf(L"\n[PROCESS] Target process started: %s (PID: %lu)\n", g_targetExeName.c_str(), pid);
        fflush(stdout);
    } else if (pid != currentPid) {
        // Different PID - process was restarted
        wprintf(L"\n[PROCESS] Target process restarted: %s (PID: %lu -> %lu)\n",
                g_targetExeName.c_str(), currentPid, pid);
        wprintf(L"[PROCESS] Resetting statistics for new instance...\n\n");
        fflush(stdout);

        ResetStatistics();
        g_currentTargetPid = pid;
    }

    return true;
}

// Get property value from event record
bool GetEventPropertyDWORD(PEVENT_RECORD pEvent, PTRACE_EVENT_INFO pInfo,
                           const wchar_t* propertyName, DWORD* outValue) {
    for (ULONG i = 0; i < pInfo->TopLevelPropertyCount; i++) {
        PROPERTY_DATA_DESCRIPTOR dataDesc;
        ZeroMemory(&dataDesc, sizeof(dataDesc));

        const wchar_t* propName = (const wchar_t*)((BYTE*)pInfo +
            pInfo->EventPropertyInfoArray[i].NameOffset);

        if (_wcsicmp(propName, propertyName) == 0) {
            dataDesc.PropertyName = (ULONGLONG)propName;
            dataDesc.ArrayIndex = ULONG_MAX;

            ULONG propertySize = 0;
            if (TdhGetPropertySize(pEvent, 0, NULL, 1, &dataDesc, &propertySize) == ERROR_SUCCESS) {
                if (propertySize == sizeof(DWORD)) {
                    if (TdhGetProperty(pEvent, 0, NULL, 1, &dataDesc, propertySize,
                                      (PBYTE)outValue) == ERROR_SUCCESS) {
                        return true;
                    }
                }
            }
            break;
        }
    }
    return false;
}

// Get property value as ULONGLONG
bool GetEventPropertyULONGLONG(PEVENT_RECORD pEvent, PTRACE_EVENT_INFO pInfo,
                               const wchar_t* propertyName, ULONGLONG* outValue) {
    for (ULONG i = 0; i < pInfo->TopLevelPropertyCount; i++) {
        PROPERTY_DATA_DESCRIPTOR dataDesc;
        ZeroMemory(&dataDesc, sizeof(dataDesc));

        const wchar_t* propName = (const wchar_t*)((BYTE*)pInfo +
            pInfo->EventPropertyInfoArray[i].NameOffset);

        if (_wcsicmp(propName, propertyName) == 0) {
            dataDesc.PropertyName = (ULONGLONG)propName;
            dataDesc.ArrayIndex = ULONG_MAX;

            ULONG propertySize = 0;
            if (TdhGetPropertySize(pEvent, 0, NULL, 1, &dataDesc, &propertySize) == ERROR_SUCCESS) {
                if (propertySize == sizeof(ULONGLONG)) {
                    if (TdhGetProperty(pEvent, 0, NULL, 1, &dataDesc, propertySize,
                                      (PBYTE)outValue) == ERROR_SUCCESS) {
                        return true;
                    }
                }
                else if (propertySize == sizeof(DWORD)) {
                    DWORD temp = 0;
                    if (TdhGetProperty(pEvent, 0, NULL, 1, &dataDesc, propertySize,
                                      (PBYTE)&temp) == ERROR_SUCCESS) {
                        *outValue = temp;
                        return true;
                    }
                }
            }
            break;
        }
    }
    return false;
}

// Print debug information for an event (all metadata and properties)
void PrintDebugEventInfo(PEVENT_RECORD pEvent, PTRACE_EVENT_INFO pInfo) {
    wprintf(L"--- DxgKrnl Event ---\n");
    wprintf(L"  EventID: %u, Version: %u, Channel: %u, Level: %u\n",
            pEvent->EventHeader.EventDescriptor.Id,
            pEvent->EventHeader.EventDescriptor.Version,
            pEvent->EventHeader.EventDescriptor.Channel,
            pEvent->EventHeader.EventDescriptor.Level);
    wprintf(L"  Task: %u, Opcode: %u, Keyword: 0x%llx\n",
            pEvent->EventHeader.EventDescriptor.Task,
            pEvent->EventHeader.EventDescriptor.Opcode,
            pEvent->EventHeader.EventDescriptor.Keyword);
    wprintf(L"  ProcessId: %lu, ThreadId: %lu\n",
            pEvent->EventHeader.ProcessId,
            pEvent->EventHeader.ThreadId);

    // Get names from TRACE_EVENT_INFO
    const wchar_t* taskName = (pInfo->TaskNameOffset != 0) ?
        (const wchar_t*)((BYTE*)pInfo + pInfo->TaskNameOffset) : L"(none)";
    const wchar_t* opcodeName = (pInfo->OpcodeNameOffset != 0) ?
        (const wchar_t*)((BYTE*)pInfo + pInfo->OpcodeNameOffset) : L"(none)";
    const wchar_t* eventName = (pInfo->EventNameOffset != 0) ?
        (const wchar_t*)((BYTE*)pInfo + pInfo->EventNameOffset) : L"(none)";

    wprintf(L"  TaskName: %s\n", taskName);
    wprintf(L"  OpcodeName: %s\n", opcodeName);
    wprintf(L"  EventName: %s\n", eventName);

    // Print all properties
    wprintf(L"  Properties (%lu):\n", pInfo->TopLevelPropertyCount);
    for (ULONG i = 0; i < pInfo->TopLevelPropertyCount; i++) {
        const wchar_t* propName = (const wchar_t*)((BYTE*)pInfo +
            pInfo->EventPropertyInfoArray[i].NameOffset);

        PROPERTY_DATA_DESCRIPTOR dataDesc;
        ZeroMemory(&dataDesc, sizeof(dataDesc));
        dataDesc.PropertyName = (ULONGLONG)propName;
        dataDesc.ArrayIndex = ULONG_MAX;

        ULONG propertySize = 0;
        TDHSTATUS status = TdhGetPropertySize(pEvent, 0, NULL, 1, &dataDesc, &propertySize);

        if (status == ERROR_SUCCESS && propertySize > 0 && propertySize <= 8) {
            ULONGLONG value = 0;
            if (TdhGetProperty(pEvent, 0, NULL, 1, &dataDesc, propertySize, (PBYTE)&value) == ERROR_SUCCESS) {
                wprintf(L"    %s = %llu (0x%llx) [%lu bytes]\n", propName, value, value, propertySize);
            } else {
                wprintf(L"    %s [%lu bytes] (read failed)\n", propName, propertySize);
            }
        } else {
            wprintf(L"    %s [%lu bytes]\n", propName, propertySize);
        }
    }
    wprintf(L"\n");
    fflush(stdout);
}

// Format size for display
void FormatSize(ULONGLONG size, wchar_t* buffer, size_t bufferSize) {
    if (size >= 1024ULL * 1024ULL * 1024ULL) {
        swprintf_s(buffer, bufferSize, L"%.2f GB", (double)size / (1024.0 * 1024.0 * 1024.0));
    } else if (size >= 1024ULL * 1024ULL) {
        swprintf_s(buffer, bufferSize, L"%.2f MB", (double)size / (1024.0 * 1024.0));
    } else if (size >= 1024ULL) {
        swprintf_s(buffer, bufferSize, L"%.2f KB", (double)size / 1024.0);
    } else {
        swprintf_s(buffer, bufferSize, L"%llu bytes", size);
    }
}

// Get event type name
const wchar_t* GetEventTypeName(EventType type) {
    switch (type) {
        case EventType::Allocation:   return L"ALLOC";
        case EventType::Free:         return L"FREE";
        case EventType::Eviction:     return L"EVICT";
        case EventType::MadeResident: return L"RESIDENT";
        default:                      return L"UNKNOWN";
    }
}

// Print event properties for debugging/information
void PrintEventInfo(PEVENT_RECORD pEvent, PTRACE_EVENT_INFO /*pInfo*/, DWORD pid, EventType eventType, ULONGLONG size) {
    // Update statistics first
    switch (eventType) {
        case EventType::Allocation:
            g_totalAllocated += size;
            g_allocationCount++;
            break;
        case EventType::Free:
            g_totalFreed += size;
            g_freeCount++;
            break;
        case EventType::Eviction:
            g_totalEvicted += size;
            g_evictionCount++;
            break;
        case EventType::MadeResident:
            g_totalMadeResident += size;
            g_madeResidentCount++;
            break;
        default:
            break;
    }

    FILETIME ft;
    ft.dwLowDateTime = pEvent->EventHeader.TimeStamp.LowPart;
    ft.dwHighDateTime = pEvent->EventHeader.TimeStamp.HighPart;

    SYSTEMTIME st;
    FileTimeToSystemTime(&ft, &st);

    // Format size
    wchar_t sizeStr[64] = L"";
    if (size > 0) {
        FormatSize(size, sizeStr, _countof(sizeStr));
    }

    // Format running totals
    wchar_t allocTotalStr[64], evictTotalStr[64], residentTotalStr[64];
    ULONGLONG allocated = g_totalAllocated.load();
    ULONGLONG resident = g_totalMadeResident.load();
    ULONGLONG peakDemoted = g_peakDemotedCommitment.load();

    FormatSize(allocated, allocTotalStr, _countof(allocTotalStr));
    FormatSize(peakDemoted, evictTotalStr, _countof(evictTotalStr));
    FormatSize(resident, residentTotalStr, _countof(residentTotalStr));

    // Print based on event type
    const wchar_t* eventTypeName = GetEventTypeName(eventType);

    wprintf(L"[%02d:%02d:%02d.%03d] %-10s - PID: %lu (%s)",
            st.wHour, st.wMinute, st.wSecond, st.wMilliseconds,
            eventTypeName, pid, g_targetExeName.c_str());

    if (size > 0) {
        wprintf(L" - Size: %s", sizeStr);
    }

    // Print running totals (Evict shows peak demoted commitment from VidMmProcessDemotedCommitmentChange)
    wprintf(L" | Totals: Alloc=%s, Evict=%s, Resident=%s\n",
            allocTotalStr, evictTotalStr, residentTotalStr);

    fflush(stdout);
}

// Print current statistics summary
void PrintStatistics() {
    wchar_t allocStr[64], freeStr[64], demotedStr[64], residentStr[64], netStr[64];

    ULONGLONG allocated = g_totalAllocated.load();
    ULONGLONG freed = g_totalFreed.load();
    ULONGLONG peakDemoted = g_peakDemotedCommitment.load();
    ULONGLONG madeResident = g_totalMadeResident.load();
    LONGLONG net = (LONGLONG)allocated - (LONGLONG)freed;

    FormatSize(allocated, allocStr, _countof(allocStr));
    FormatSize(freed, freeStr, _countof(freeStr));
    FormatSize(peakDemoted, demotedStr, _countof(demotedStr));
    FormatSize(madeResident, residentStr, _countof(residentStr));
    FormatSize(net > 0 ? (ULONGLONG)net : (ULONGLONG)(-net), netStr, _countof(netStr));

    wprintf(L"\n=== Video Memory Statistics ===\n");
    wprintf(L"Allocations:   %lu (Total: %s)\n", g_allocationCount.load(), allocStr);
    wprintf(L"Frees:         %lu (Total: %s)\n", g_freeCount.load(), freeStr);
    wprintf(L"Net Memory:    %s%s\n", net < 0 ? L"-" : L"", netStr);
    wprintf(L"Peak Demoted:  %s\n", demotedStr);
    wprintf(L"Made Resident: %lu (Total: %s)\n", g_madeResidentCount.load(), residentStr);
    wprintf(L"===============================\n\n");
}

// Determine event type from task name
EventType GetEventTypeFromTaskName(const wchar_t* taskName) {
    if (!taskName) {
        return EventType::Unknown;
    }

    if (_wcsicmp(taskName, TASK_ADAPTER_ALLOCATION) == 0) {
        return EventType::Allocation;
    }
    if (_wcsicmp(taskName, TASK_TERMINATE_ALLOCATION) == 0) {
        return EventType::Free;
    }
    if (_wcsicmp(taskName, TASK_VIDMM_EVICT) == 0) {
        return EventType::Eviction;
    }
    if (_wcsicmp(taskName, TASK_VIDMM_MAKE_RESIDENT) == 0) {
        return EventType::MadeResident;
    }

    return EventType::Unknown;
}

// ETW event callback
void WINAPI EventRecordCallback(PEVENT_RECORD pEvent) {
    if (!g_running) {
        return;
    }

    // Check if this is from DxgKrnl
    if (!IsEqualGUID(pEvent->EventHeader.ProviderId, DXGKRNL_PROVIDER_GUID)) {
        return;
    }

    // Get event metadata
    ULONG bufferSize = 0;
    TDHSTATUS status = TdhGetEventInformation(pEvent, 0, NULL, NULL, &bufferSize);
    if (status != ERROR_INSUFFICIENT_BUFFER) {
        return;
    }

    PTRACE_EVENT_INFO pInfo = (PTRACE_EVENT_INFO)malloc(bufferSize);
    if (!pInfo) {
        return;
    }

    status = TdhGetEventInformation(pEvent, 0, NULL, pInfo, &bufferSize);
    if (status != ERROR_SUCCESS) {
        free(pInfo);
        return;
    }

    // Debug mode: print all event info and skip normal processing
    if (g_debugMode) {
        PrintDebugEventInfo(pEvent, pInfo);
        free(pInfo);
        return;
    }

    // Get task name from event info
    const wchar_t* taskName = nullptr;
    if (pInfo->TaskNameOffset != 0) {
        taskName = (const wchar_t*)((BYTE*)pInfo + pInfo->TaskNameOffset);
    }

    // Handle VidMmProcessDemotedCommitmentChange - this tracks DEMOTED memory (evictions)
    if (taskName && _wcsicmp(taskName, L"VidMmProcessDemotedCommitmentChange") == 0) {
        DWORD eventPid = 0;
        GetEventPropertyDWORD(pEvent, pInfo, L"ProcessId", &eventPid);

        if (CheckTargetProcess(eventPid)) {
            ULONGLONG newDemoted = 0, oldDemoted = 0;
            // Property names are "Commitment" and "OldCommitment" for this event type
            GetEventPropertyULONGLONG(pEvent, pInfo, L"Commitment", &newDemoted);
            GetEventPropertyULONGLONG(pEvent, pInfo, L"OldCommitment", &oldDemoted);

            // Update global tracking of demoted commitment
            g_currentDemotedCommitment = newDemoted;
            ULONGLONG currentPeak = g_peakDemotedCommitment.load();
            while (newDemoted > currentPeak && !g_peakDemotedCommitment.compare_exchange_weak(currentPeak, newDemoted)) {}

            LONGLONG delta = (LONGLONG)newDemoted - (LONGLONG)oldDemoted;
            if (delta > 0) {
                g_evictionCount++;
            }

            // Print demoted commitment changes
            wchar_t newVal[64], peakVal[64];
            FormatSize(newDemoted, newVal, _countof(newVal));
            FormatSize(g_peakDemotedCommitment.load(), peakVal, _countof(peakVal));
            wprintf(L"[DEMOTED] Current: %s, Peak: %s\n", newVal, peakVal);
            fflush(stdout);
        }
        free(pInfo);
        return;
    }

    // Handle VidMmProcessUsageChange - tracks memory usage changes in VRAM
    // Positive delta = memory made resident, Negative delta = memory evicted
    if (taskName && _wcsicmp(taskName, TASK_VIDMM_PROCESS_USAGE_CHANGE) == 0) {
        // This event has ProcessId property and NewUsage/OldUsage
        DWORD eventPid = 0;
        ULONGLONG hProcessId = 0;
        if (!GetEventPropertyDWORD(pEvent, pInfo, L"ProcessId", &eventPid) || eventPid == 0) {
            if (GetEventPropertyULONGLONG(pEvent, pInfo, L"hProcessId", &hProcessId) && hProcessId != 0) {
                eventPid = (DWORD)hProcessId;
            }
        }

        if (CheckTargetProcess(eventPid)) {
            ULONGLONG newUsage = 0, oldUsage = 0;
            DWORD segmentGroup = 0;
            GetEventPropertyULONGLONG(pEvent, pInfo, L"NewUsage", &newUsage);
            GetEventPropertyULONGLONG(pEvent, pInfo, L"OldUsage", &oldUsage);
            GetEventPropertyDWORD(pEvent, pInfo, L"MemorySegmentGroup", &segmentGroup);

            LONGLONG delta = (LONGLONG)newUsage - (LONGLONG)oldUsage;

            // Only track segment 0 (local VRAM) changes
            if (delta != 0 && segmentGroup == 0) {
                ULONGLONG size = (delta > 0) ? (ULONGLONG)delta : (ULONGLONG)(-delta);

                if (delta < 0) {
                    PrintEventInfo(pEvent, pInfo, eventPid, EventType::Eviction, size);
                } else {
                    PrintEventInfo(pEvent, pInfo, eventPid, EventType::MadeResident, size);
                }
            }
        }
        free(pInfo);
        return;
    }

    // Determine event type from task name
    EventType eventType = GetEventTypeFromTaskName(taskName);

    // Skip events we're not interested in
    if (eventType == EventType::Unknown) {
        free(pInfo);
        return;
    }

    ULONGLONG size = 0;
    ULONGLONG allocPtr = 0;
    DWORD pid = 0;

    // Track VidMmMakeResident to learn which allocations belong to our target
    if (eventType == EventType::MadeResident) {
        DWORD headerPid = pEvent->EventHeader.ProcessId;

        if (CheckTargetProcess(headerPid)) {
            ULONGLONG pVidMmAlloc = 0;
            ULONGLONG allocSize = 0;
            GetEventPropertyULONGLONG(pEvent, pInfo, L"pVidMmAlloc", &pVidMmAlloc);
            GetEventPropertyULONGLONG(pEvent, pInfo, L"Size", &allocSize);

            if (pVidMmAlloc != 0) {
                std::lock_guard<std::mutex> lock(g_targetAllocMutex);
                if (allocSize > 0) {
                    g_targetAllocSizeMap[pVidMmAlloc] = allocSize;
                } else if (g_targetAllocSizeMap.find(pVidMmAlloc) == g_targetAllocSizeMap.end()) {
                    g_targetAllocSizeMap[pVidMmAlloc] = 0;
                }
            }
        }
        free(pInfo);
        return;
    }

    // Track VidMmEvict - check if the allocation belongs to our target
    // Note: VidMmEvict events don't have reliable ProcessId, so we correlate via allocation pointers
    // The main eviction tracking is done via VidMmProcessDemotedCommitmentChange
    if (eventType == EventType::Eviction) {
        ULONGLONG hVidMmAlloc = 0;
        ULONGLONG pVidMmAlloc = 0;
        ULONGLONG evictEventSize = 0;
        GetEventPropertyULONGLONG(pEvent, pInfo, L"hVidMmAlloc", &hVidMmAlloc);
        GetEventPropertyULONGLONG(pEvent, pInfo, L"pVidMmAlloc", &pVidMmAlloc);
        GetEventPropertyULONGLONG(pEvent, pInfo, L"Size", &evictEventSize);

        // Look up size from allocation map using hVidMmAlloc
        ULONGLONG evictSize = 0;
        {
            std::lock_guard<std::mutex> lock(g_allocationMapMutex);
            auto it = g_allocationSizeMap.find(hVidMmAlloc);
            if (it != g_allocationSizeMap.end()) {
                evictSize = it->second;
            }
        }

        // Also check pVidMmAlloc in target allocations map
        if (evictSize == 0 && pVidMmAlloc != 0) {
            std::lock_guard<std::mutex> lock(g_targetAllocMutex);
            auto it = g_targetAllocSizeMap.find(pVidMmAlloc);
            if (it != g_targetAllocSizeMap.end()) {
                evictSize = (evictEventSize > 0) ? evictEventSize : it->second;
                g_targetAllocSizeMap.erase(it);
            }
        }

        free(pInfo);
        return;
    }

    // For Allocation and Free events: use standard process ID lookup
    ULONGLONG hProcessId = 0;
    bool foundPid = GetEventPropertyDWORD(pEvent, pInfo, L"ProcessId", &pid);
    if (!foundPid || pid == 0) {
        if (GetEventPropertyULONGLONG(pEvent, pInfo, L"hProcessId", &hProcessId) && hProcessId != 0) {
            pid = (DWORD)hProcessId;
            foundPid = true;
        }
    }
    if (!foundPid || pid == 0) {
        foundPid = GetEventPropertyDWORD(pEvent, pInfo, L"hProcess", &pid) ||
                   GetEventPropertyDWORD(pEvent, pInfo, L"Context", &pid);
    }

    // If no PID in properties, use event header PID
    if (!foundPid || pid == 0) {
        pid = pEvent->EventHeader.ProcessId;
    }

    // Check if this is our target process
    if (CheckTargetProcess(pid)) {
        if (eventType == EventType::Allocation) {
            // AdapterAllocation: get allocSize and hVidMmGlobalAlloc
            GetEventPropertyULONGLONG(pEvent, pInfo, L"allocSize", &size);
            ULONGLONG globalAlloc = 0;
            GetEventPropertyULONGLONG(pEvent, pInfo, L"hVidMmGlobalAlloc", &globalAlloc);

            allocPtr = globalAlloc;

            if (size != 0 && globalAlloc != 0) {
                std::lock_guard<std::mutex> lock(g_allocationMapMutex);
                g_allocationSizeMap[globalAlloc] = size;
            }
        }
        else if (eventType == EventType::Free) {
            // TerminateAllocation: get hVidMmAlloc, look up size, remove from map
            GetEventPropertyULONGLONG(pEvent, pInfo, L"hVidMmAlloc", &allocPtr);

            if (allocPtr != 0) {
                std::lock_guard<std::mutex> lock(g_allocationMapMutex);
                auto it = g_allocationSizeMap.find(allocPtr);
                if (it != g_allocationSizeMap.end()) {
                    size = it->second;
                    g_allocationSizeMap.erase(it);
                }
            }
        }

        PrintEventInfo(pEvent, pInfo, pid, eventType, size);
    }

    free(pInfo);
}

// Buffer callback (required but not used for real-time)
ULONG WINAPI BufferCallback(PEVENT_TRACE_LOGFILEW pLogFile) {
    (void)pLogFile;
    return g_running ? TRUE : FALSE;
}

// Console control handler for graceful shutdown
BOOL WINAPI ConsoleHandler(DWORD ctrlType) {
    if (ctrlType == CTRL_C_EVENT || ctrlType == CTRL_BREAK_EVENT) {
        wprintf(L"\nStopping trace...\n");
        g_running = false;

        // Print final statistics
        PrintStatistics();

        if (g_traceHandle != INVALID_PROCESSTRACE_HANDLE) {
            CloseTrace(g_traceHandle);
        }
        return TRUE;
    }
    return FALSE;
}

// Stop and clean up any existing session
void CleanupExistingSession() {
    ULONG bufferSize = sizeof(EVENT_TRACE_PROPERTIES) + (MAX_PATH * sizeof(wchar_t)) * 2;
    PEVENT_TRACE_PROPERTIES pProperties = (PEVENT_TRACE_PROPERTIES)malloc(bufferSize);
    if (pProperties) {
        ZeroMemory(pProperties, bufferSize);
        pProperties->Wnode.BufferSize = bufferSize;
        ControlTraceW(0, SESSION_NAME, pProperties, EVENT_TRACE_CONTROL_STOP);
        free(pProperties);
    }
}

int wmain(int argc, wchar_t* argv[]) {
    wprintf(L"VMemDemote - Video Memory Allocation & Demotion Tracker\n");
    wprintf(L"=======================================================\n\n");

    // Parse command line
    if (argc < 2) {
        wprintf(L"Usage: %s [-debug] <executable_name>\n", argv[0]);
        wprintf(L"Example: %s game.exe\n", argv[0]);
        wprintf(L"Example: %s -debug notepad.exe\n", argv[0]);
        wprintf(L"\nThis tool monitors video memory operations for the specified process.\n");
        wprintf(L"\nOptions:\n");
        wprintf(L"  -debug   Dump all DxgKrnl events with full metadata (for diagnostics)\n");
        wprintf(L"\nEvents tracked (DxgKrnl ETW events):\n");
        wprintf(L"  ALLOC    - AdapterAllocation: Video memory allocated\n");
        wprintf(L"  FREE     - TerminateAllocation: Video memory freed\n");
        wprintf(L"  EVICT    - VidMmEvict: Memory evicted/demoted from VRAM\n");
        wprintf(L"  RESIDENT - VidMmMakeResident: Memory made resident in VRAM\n");
        wprintf(L"\nNote: Requires Administrator privileges for ETW tracing.\n");
        return 1;
    }

    // Parse arguments
    int argIndex = 1;
    if (_wcsicmp(argv[argIndex], L"-debug") == 0) {
        g_debugMode = true;
        argIndex++;
        if (argIndex >= argc) {
            wprintf(L"Error: Missing executable name after -debug\n");
            return 1;
        }
    }

    g_targetExeName = argv[argIndex];

    if (g_debugMode) {
        wprintf(L"DEBUG MODE: Dumping all DxgKrnl events\n");
        wprintf(L"Target process filter: %s\n", g_targetExeName.c_str());
    } else {
        wprintf(L"Monitoring process: %s\n", g_targetExeName.c_str());
    }
    wprintf(L"Press Ctrl+C to stop.\n\n");

    // Set up console handler
    SetConsoleCtrlHandler(ConsoleHandler, TRUE);

    // Clean up any existing session with same name
    CleanupExistingSession();

    // Calculate buffer sizes
    ULONG bufferSize = sizeof(EVENT_TRACE_PROPERTIES) + (MAX_PATH * sizeof(wchar_t)) * 2;
    PEVENT_TRACE_PROPERTIES pSessionProperties = (PEVENT_TRACE_PROPERTIES)malloc(bufferSize);
    if (!pSessionProperties) {
        wprintf(L"Error: Failed to allocate memory for session properties.\n");
        return 1;
    }

    ZeroMemory(pSessionProperties, bufferSize);
    pSessionProperties->Wnode.BufferSize = bufferSize;
    pSessionProperties->Wnode.Flags = WNODE_FLAG_TRACED_GUID;
    pSessionProperties->Wnode.ClientContext = 1; // QPC clock resolution
    pSessionProperties->LogFileMode = EVENT_TRACE_REAL_TIME_MODE;
    pSessionProperties->LoggerNameOffset = sizeof(EVENT_TRACE_PROPERTIES);

    // Start the trace session
    ULONG status = StartTraceW(&g_sessionHandle, SESSION_NAME, pSessionProperties);
    if (status != ERROR_SUCCESS) {
        if (status == ERROR_ACCESS_DENIED) {
            wprintf(L"Error: Access denied. Please run as Administrator.\n");
        } else {
            wprintf(L"Error: Failed to start trace session. Error code: %lu\n", status);
        }
        free(pSessionProperties);
        return 1;
    }

    wprintf(L"Trace session started.\n");

    // Enable the DxgKrnl provider
    // Using keywords to capture memory-related events
    ULONGLONG matchAnyKeyword = 0xFFFFFFFFFFFFFFFF; // Capture all keywords

    status = EnableTraceEx2(
        g_sessionHandle,
        &DXGKRNL_PROVIDER_GUID,
        EVENT_CONTROL_CODE_ENABLE_PROVIDER,
        TRACE_LEVEL_VERBOSE,  // Use VERBOSE to get all events
        matchAnyKeyword,
        0,
        0,
        NULL
    );

    if (status != ERROR_SUCCESS) {
        wprintf(L"Error: Failed to enable DxgKrnl provider. Error code: %lu\n", status);
        ControlTraceW(g_sessionHandle, NULL, pSessionProperties, EVENT_TRACE_CONTROL_STOP);
        free(pSessionProperties);
        return 1;
    }

    wprintf(L"DxgKrnl provider enabled. Waiting for video memory events...\n\n");

    // Open trace for processing
    EVENT_TRACE_LOGFILEW logFile;
    ZeroMemory(&logFile, sizeof(logFile));
    logFile.LoggerName = const_cast<LPWSTR>(SESSION_NAME);
    logFile.ProcessTraceMode = PROCESS_TRACE_MODE_REAL_TIME | PROCESS_TRACE_MODE_EVENT_RECORD;
    logFile.EventRecordCallback = EventRecordCallback;
    logFile.BufferCallback = BufferCallback;

    g_traceHandle = OpenTraceW(&logFile);
    if (g_traceHandle == INVALID_PROCESSTRACE_HANDLE) {
        wprintf(L"Error: Failed to open trace. Error code: %lu\n", GetLastError());
        ControlTraceW(g_sessionHandle, NULL, pSessionProperties, EVENT_TRACE_CONTROL_STOP);
        free(pSessionProperties);
        return 1;
    }

    // Process events (this blocks until trace is stopped)
    status = ProcessTrace(&g_traceHandle, 1, NULL, NULL);
    if (status != ERROR_SUCCESS && status != ERROR_CANCELLED) {
        wprintf(L"ProcessTrace ended with error: %lu\n", status);
    }

    // Cleanup
    wprintf(L"Cleaning up...\n");

    if (g_traceHandle != INVALID_PROCESSTRACE_HANDLE) {
        CloseTrace(g_traceHandle);
    }

    ControlTraceW(g_sessionHandle, NULL, pSessionProperties, EVENT_TRACE_CONTROL_STOP);
    free(pSessionProperties);

    wprintf(L"Done.\n");
    return 0;
}

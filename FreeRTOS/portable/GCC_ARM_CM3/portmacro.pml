#ifndef _PORTMACRO_
#define _PORTMACRO_

#define portMAX_DELAY       255

inline portYIELD(_id)
{
    AWAIT(_id, set_pending(PendSV_ID); v7m_memory_barrier(_id, hidden_var))
}

#define portDISABLE_INTERRUPTS(_id) vPortRaiseBASEPRI(_id)
#define portENABLE_INTERRUPTS(_id)  vPortSetBASEPRI(_id, 0)
#define portENTER_CRITICAL(_id)     vPortEnterCritical(_id)
#define portEXIT_CRITICAL(_id)      vPortExitCritical(_id)

#define portTASK_FUNCTION(vFunction) proctype vFunction()

/* Architecture specific optimisations */
#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION
    #define configUSE_PORT_OPTIMISED_TASK_SELECTION 1
#endif

#if (configUSE_PORT_OPTIMISED_TASK_SELECTION == 1)

    #if (configMAX_PRIORITIES > 8)
        #error When the optimised selection is set, priority levels must not exceed 8.
    #endif

    #define portRECORD_READY_PRIORITY(Priority, ReadyPriorities) \
        ReadyPriorities = ReadyPriorities | (1 << (Priority))

    #define portRESET_READY_PRIORITY(Priority, ReadyPriorities) \
        ReadyPriorities = ReadyPriorities & ~(1 << (Priority))

    hidden byte clzCount, clzTemp;
    #define portGET_HIGHEST_PRIORITY(TopPriority, ReadyPriorities) \
        clzCount = 0; clzTemp = ReadyPriorities; \
        clzCount = ((clzTemp & 240) -> clzCount : clzCount + 4); \
        clzTemp = ((clzTemp & 240) -> clzTemp : clzTemp << 4); \
        clzCount = ((clzTemp & 192) -> clzCount : clzCount + 2); \
        clzTemp = ((clzTemp & 192) -> clzTemp : clzTemp << 2); \
        clzCount = ((clzTemp & 128) -> clzCount : clzCount + 1); \
        clzTemp = ((clzTemp & 128) -> clzTemp : clzTemp << 1); \
        TopPriority = 7 - clzCount;

#endif

inline vPortRaiseBASEPRI(_id)
{
    // v7m_memory_barrier(_id, hidden_var)
    AWAIT(_id, MSR_BASEPRI(configMAX_SYSCALL_INTERRUPT_PRIORITY); assert(!BASEPRI_MASK(SysTick_ID) && !BASEPRI_MASK(PendSV_ID)))
}

inline vPortSetBASEPRI(_id, ulNewMaskValue)
{
    AWAIT(_id, MSR_BASEPRI(ulNewMaskValue); v7m_memory_barrier(_id, hidden_var))
}

#endif

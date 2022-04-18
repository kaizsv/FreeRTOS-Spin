#ifndef _PORTMACRO_
#define _PORTMACRO_

#define portMAX_DELAY   255

/* Scheduler utilities */
inline portYIELD(_id)
{
    AWAIT(_id, ecall());
}

/* Critical section management */
#define portCRITICAL_NESTING_IN_TCB 1 // TODO: To be released
#define portDISABLE_INTERRUPTS(_id) AWAIT_SAFE(_id, CLR_MSTATUS_MIE())
#define portENABLE_INTERRUPTS(_id)  AWAIT(_id, SET_MSTATUS_MIE())

// TODO: To be released
#define portENTER_CRITICAL(_id)     vTaskEnterCritical(_id)
#define portEXIT_CRITICAL(_id)      vTaskExitCritical(_id)

/* Architecture specific optimisations */
#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION
    #define configUSE_PORT_OPTIMISED_TASK_SELECTION 1
#endif

#if ( configUSE_PORT_OPTIMISED_TASK_SELECTION == 1 )

    #if ( configMAX_PRIORITIES > 8 )
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

/* Task function macros */
#define portTASK_FUNCTION(vFunction) proctype vFunction()

#endif

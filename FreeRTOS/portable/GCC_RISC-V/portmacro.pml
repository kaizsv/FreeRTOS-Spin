#ifndef _PORTMACRO_
#define _PORTMACRO_

#define portMAX_DELAY   255

/* Scheduler utilities */
// TODO: portYIELD_BLOCKED_BY_BASEPRI
#define portYIELD_BLOCKED_BY_BASEPRI    portYIELD
inline portYIELD(_id, _)
{
    AWAIT(_id, ecall(_id));
}

/* Critical section management */
#define portCRITICAL_NESTING_IN_TCB 1
#define portDISABLE_INTERRUPTS(_id, ...)    AWAIT(_id, CLR_MSTATUS_MIE())
#define portENABLE_INTERRUPTS(_id, ...)     AWAIT(_id, SET_MSTATUS_MIE())
#define portENTER_CRITICAL(_id, ...)        vTaskEnterCritical(_id)
#define portEXIT_CRITICAL(_id, ...)         vTaskExitCritical(_id)

/* Architecture specific optimisations */
#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION
    #define configUSE_PORT_OPTIMISED_TASK_SELECTION 1
#endif

#if ( configUSE_PORT_OPTIMISED_TASK_SELECTION == 1 )
    // TODO portRECORD_READY_PRIORITY
    // TODO portRESET_READY_PRIORITY
    // TODO portGET_HIGHEST_PRIORITY
#endif

/* Task function macros */
#define portTASK_FUNCTION(vFunction) proctype vFunction()

#endif

#ifndef _PORTMACRO_
#define _PORTMACRO_

#define portMAX_DELAY       255

inline portYIELD(_id, temp_var)
{
    AWAIT_A(_id, set_pending(PendSV_ID); v7m_memory_barrier(_id, temp_var))
}

#define portDISABLE_INTERRUPTS(_id, temp_var)   vPortRaiseBASEPRI(_id, temp_var)
#define portENABLE_INTERRUPTS(_id, temp_var)    vPortSetBASEPRI(_id, 0, temp_var)
#define portENTER_CRITICAL(_id, temp_var)       vPortEnterCritical(_id, temp_var)
#define portEXIT_CRITICAL(_id, temp_var)        vPortExitCritical(_id, temp_var)

#define portTASK_FUNCTION(vFunction) proctype vFunction()

inline vPortRaiseBASEPRI(_id, temp_var)
{
    AWAIT_A(_id, MSR_BASEPRI(configMAX_SYSCALL_INTERRUPT_PRIORITY); v7m_memory_barrier(_id, temp_var))
}

inline vPortSetBASEPRI(_id, ulNewMaskValue, temp_var)
{
    AWAIT_A(_id, MSR_BASEPRI(ulNewMaskValue); v7m_memory_barrier(_id, temp_var))
}

#endif

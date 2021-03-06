#ifndef _PORTMACRO_
#define _PORTMACRO_

#define portMAX_DELAY       255

inline portYIELD_DETERMINISTIC(_id, temp_var)
{
    AWAIT_DS(_id, set_pending(PendSV_ID); assert(!BASEPRI_MASK(SysTick_ID) && !BASEPRI_MASK(PendSV_ID)))
}

inline portYIELD(_id, temp_var)
{
    AWAIT(_id, set_pending(PendSV_ID); v7m_memory_barrier(_id, temp_var))
}

#define portDISABLE_INTERRUPTS(_id, temp_var)   vPortRaiseBASEPRI(_id, temp_var)
#define portENABLE_INTERRUPTS(_id, temp_var)    vPortSetBASEPRI(_id, 0, temp_var)
#define portENTER_CRITICAL(_id, temp_var)       vPortEnterCritical(_id, temp_var)
#define portEXIT_CRITICAL(_id, temp_var)        vPortExitCritical(_id, temp_var)

#define portTASK_FUNCTION(vFunction) proctype vFunction()

inline vPortRaiseBASEPRI(_id, temp_var)
{
    // v7m_memory_barrier(_id, temp_var)
    AWAIT(_id, MSR_BASEPRI(configMAX_SYSCALL_INTERRUPT_PRIORITY); assert(!BASEPRI_MASK(SysTick_ID) && !BASEPRI_MASK(PendSV_ID)))
}

inline vPortSetBASEPRI(_id, ulNewMaskValue, temp_var)
{
    AWAIT(_id, MSR_BASEPRI(ulNewMaskValue); v7m_memory_barrier(_id, temp_var))
}

#endif

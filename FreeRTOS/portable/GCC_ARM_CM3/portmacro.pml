#ifndef _PORTMACRO_
#define _PORTMACRO_

#define portMAX_DELAY       255

inline portYIELD(_id, temp_var)
{
    AWAIT_D(_id, set_pending(PendSV_ID));
    AWAIT_A(_id, v7m_memory_barrier(temp_var))
}

#define portDISABLE_INTERRUPTS(_id, temp_var)    vPortRaiseBASEPRI(_id, temp_var)
#define portENABLE_INTERRUPTS(_id, temp_var)     vPortSetBASEPRI(_id, 0, temp_var)
#define portENTER_CRITICAL(_id, temp_var)        vPortEnterCritical(_id, temp_var)
#define portEXIT_CRITICAL(_id, temp_var)         vPortExitCritical(_id, temp_var)

#define portTASK_FUNCTION(vFunction) proctype vFunction()

inline vPortRaiseBASEPRI(_id, temp_var)
{
    AWAIT_D(_id, MSR_BASEPRI(configMAX_SYSCALL_INTERRUPT_PRIORITY));
    /** Memory barrier
    * __asm volatile (
    *     "isb \n\t" \
    *     "dsb \n\t" \
    * )
    */
    AWAIT_A(_id, v7m_memory_barrier(temp_var))
}

inline vPortSetBASEPRI(_id, ulNewMaskValue, temp_var)
{
    AWAIT_D(_id, MSR_BASEPRI(ulNewMaskValue));
    /** Memory barrier
    * __asm volatile (
    *     "isb \n\t" \
    *     "dsb \n\t" \
    * )
    */
    AWAIT_A(_id, v7m_memory_barrier(temp_var))
}

#endif

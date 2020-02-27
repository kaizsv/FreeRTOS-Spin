#ifndef _PORT_
#define _PORT_

#define SYS_EXP                 2 /* SysTick and PendSV */
#define NVIC_INT                0 /* number of interrupts */
#define promela_EXP_NUMBER      (SYS_EXP + NVIC_INT)

#define PendSV_ID               0 /* ARMv7-M exp number: 14 */
#define SysTick_ID              1 /* ARMv7-M exp number: 15 */

#define RUN_ALL_EXPS()          \
    atomic {                    \
        run PendSV_Handler();   \
        run SysTick_Handler();  \
    }

#include "../../../arch/v7m.pml"
#include "../../../FreeRTOS.pml"
#include "../../tasks.pml"

/** Default configurations: modification has no effects in the model **
portSTACK_GROWTH                (-1)
portUSING_MPU_WRAPPERS          0
portSUPPRESS_TICKS_AND_SLEEP    UNDEFINED
TODO RISC-V: portCRITICAL_NESTING_IN_TCB     0
**********************************************************************/

#define portNVIC_PENDSV_PRI     configKERNEL_INTERRUPT_PRIORITY
#define portNVIC_SYSTICK_PRI    configKERNEL_INTERRUPT_PRIORITY

byte uxCriticalNesting = 170; /* 0xaa */

#define vPortSVCHandler \
    EP = pxCurrentTCB;  \
    MSR_BASEPRI(0)

inline xPortStartScheduler()
{
    assert(configMAX_SYSCALL_INTERRUPT_PRIORITY);
    /* It is unnecessary to check the group priority. */

    SET_PRIO_EXP(PendSV_ID, portNVIC_PENDSV_PRI);
    SET_PRIO_EXP(SysTick_ID, portNVIC_PENDSV_PRI);

    uxCriticalNesting = 0;

    /* prvPortStartFirstTask */
    assert(!HAS_PENDING_EXPS && !HAS_INOPERATIVE_EXP && !syst_count);
    RUN_ALL_EXPS();

    RUN_ALL_TASKS(vPortSVCHandler)

    /* Should never get vTaskSwitchContext */
}

inline vPortEnterCritical(_id, temp_var)
{
    portDISABLE_INTERRUPTS(_id, temp_var);
    AWAIT_D(_id, uxCriticalNesting = uxCriticalNesting + 1);
    /* ensure VECTACTIVE is zero. In other words, the running task can only be
     * user tasks. */
    if
    :: SELE(_id, uxCriticalNesting == 1) ->
        AWAIT_A(_id, assert(EP >= FIRST_TASK))
    :: ELSE(_id, uxCriticalNesting == 1)
    fi
}

inline vPortExitCritical(_id, temp_var)
{
    AWAIT_D(_id, assert(uxCriticalNesting); uxCriticalNesting = uxCriticalNesting - 1);
    if
    :: SELE(_id, uxCriticalNesting == 0) -> portENABLE_INTERRUPTS(_id, temp_var)
    :: ELSE(_id, uxCriticalNesting == 0)
    fi
}

proctype PendSV_Handler()
{
    byte idx = 0;
    byte local_var = NULL_byte;
    assert(PendSV_ID == _PID);
loop:
    soft_gen_irq(_PID);
    AWAIT_A(_PID, assert(LAST_EP_STACK >= FIRST_TASK); MSR_BASEPRI(configMAX_SYSCALL_INTERRUPT_PRIORITY));
    vTaskSwitchContext(_PID);
    AWAIT_D(_PID, MSR_BASEPRI(0));
    AWAIT_D(_PID, switch_context(pxCurrentTCB));
    AWAIT_D(_PID, exp_return(local_var));

    goto loop
}

proctype SysTick_Handler()
{
    bit local_bit = 0;
    byte idx = 0;
    byte local_var = NULL_byte;
    assert(SysTick_ID == _PID);
loop:
    irq(_PID);
    portDISABLE_INTERRUPTS(_PID, local_var);
    xTaskIncrementTick(_PID, local_bit, local_var);
    if
    :: SELE(_PID, local_bit != false) ->
        AWAIT_D(_PID, local_bit = 0; set_pending(PendSV_ID))
    :: ELSE(_PID, local_bit != false)
    fi;
    portENABLE_INTERRUPTS(_PID, local_var);
    AWAIT_D(_PID, exp_return(local_var));

    goto loop
}

#endif

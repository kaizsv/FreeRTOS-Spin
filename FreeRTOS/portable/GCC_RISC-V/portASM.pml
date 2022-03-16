#ifndef _PORTASM_
#define _PORTASM_

/* This model can also represent the "Vectored" mode of the mtvec register. */
#define freertos_vector_table freertos_risc_v_trap_handler
proctype freertos_risc_v_trap_handler()
{
    byte local_var = NULL_byte;
    bool local_bit = false;
#if (configUSE_TICK_HOOK == 1)
    vApplicationTickHook_Declaration();
#endif
    assert(_PID == TRAP_ID);
do
::  trap_entry();

    AWAIT_DS(_PID, mstatus_store[__OWNER_OF(pxCurrentTCB)] = mstatus);

    /* test_if_asynchronous */
    if
    :: SELE_AS(_PID, mcause & 1, assert(mcause == M_TIMER_INTERRUPT));
        /* handle_asynchronous */
        xTaskIncrementTick(_PID, local_bit, local_var);
        if
        :: SELE_AS(_PID, local_bit != false, local_bit = false);
            vTaskSwitchContext(_PID, local_var);
        :: ELSE_AS(_PID, local_bit != false)
        fi;
    :: ELSE_AS(_PID, mcause & 1, assert(mcause == M_ECALL_EXCEPTION));
        /* handle_synchronous */
        vTaskSwitchContext(_PID, local_var);
    fi;

    /* processed_source */
    AWAIT_DS(_PID,
        mepc = pxCurrentTCB;
        mstatus = mstatus_store[__OWNER_OF(pxCurrentTCB)];
    );

    AWAIT(_PID, mret());
od
}

inline xPortStartFirstTask()
{
    assert(mtvec == TRAP_ID);

    mstatus = mstatus_store[__OWNER_OF(pxCurrentTCB)];
    // TODO: To be released; xCriticalNesting = 0;
    SET_MSTATUS_MIE();
    RUN_ALL_EXPS();

    RUN_ALL_TASKS(EP = pxCurrentTCB);
}

inline pxPortInitialiseStack(pcName)
{
    mstatus_store[__OWNER_OF(pcName)] =
        (mstatus & ~MSTATUS_MIE_Msk) | MSTATUS_MPIE_Msk | MSTATUS_MPP_Msk;
}

#endif

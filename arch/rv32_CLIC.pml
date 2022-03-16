#ifndef _RV32_CLIC_
#define _RV32_CLIC_

/* References:
 *
 * RISC-V CLIC: https://github.com/riscv/riscv-fast-interrupt
 * ISA specification, volume 2, version 20210915-Public-Review-draft
 *
 * Interrupt (exception) entry and return:
 * SiFive FE310-G002 Manual v1p1: 8.2.1
 * SiFive Interrupt Cookbook V1.2: 2.1.4
 */

#include "rv32_CLIC_CSRs.pml"

inline _trap_entry(ecode)
{
    mcause = ecode;

    /* Copy mstatus.MIE to mstatus.MPIE */
    mstatus = (GET_MSTATUS_MIE() ->
        (mstatus | MSTATUS_MPIE_Msk) : (mstatus & ~MSTATUS_MPIE_Msk));
    /* Clear mstatus.MIE */
    CLR_MSTATUS_MIE();

    /* Set privilege mode */
    SET_MSTATUS_MPP_M_MODE();

    mepc = EP;
    EP = mtvec;
}

/* Synchronous Environment Call instruction */
inline ecall()
{
    _trap_entry(M_ECALL_EXCEPTION);
}

inline trap_entry()
{
atomic { (EP == TRAP_ID) ->
    if
    :: mcause == M_TIMER_INTERRUPT ->
        CLR_MIP_MTIP(); // Is this the correct position to clear mip.MTIP?
    :: else
    fi
}   }

inline mret()
{
    assert(GET_MSTATUS_MIE() == 0);

    /* Set privilege mode */
    SET_MSTATUS_MPP_U_MODE();

    /* mstatus.MIE is set to the value of mstatus.MPIE */
    mstatus = (GET_MSTATUS_MPIE() ->
        (mstatus | MSTATUS_MIE_Msk) : (mstatus & ~MSTATUS_MIE_Msk));

    EP = mepc;

    /* reset variables as soon as possible */
    mepc = 0; mcause = 0;
}

#endif

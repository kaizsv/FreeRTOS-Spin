#ifndef _RV32_CLIC_CSRs_
#define _RV32_CLIC_CSRs_

#define CSRS(csr, rs)       csr = csr | rs
#define CSRC(csr, rs)       csr = csr & ~rs
#define __GET_CSR_BIT(csr, Msk, Pos)    ((csr & Msk) >> Pos)

/***** mstatus *****/

/* user and machine modes only */
#define U_MODE  0   /* User mode */
#define M_MODE  1   /* Machine mode (encoding 3 in the real hardware) */

#define MSTATUS_MIE_Pos     0
#define MSTATUS_MIE_Msk     1

#define MSTATUS_MPIE_Pos    1
#define MSTATUS_MPIE_Msk    2

byte mstatus = 0;

#define GET_MSTATUS_MIE()   __GET_CSR_BIT(mstatus, MSTATUS_MIE_Msk, \
                                MSTATUS_MIE_Pos)
#define SET_MSTATUS_MIE()   CSRS(mstatus, MSTATUS_MIE_Msk)
#define CLR_MSTATUS_MIE()   CSRC(mstatus, MSTATUS_MIE_Msk)

#define GET_MSTATUS_MPIE()  __GET_CSR_BIT(mstatus, MSTATUS_MPIE_Msk, \
                                MSTATUS_MPIE_Pos)
#define SET_MSTATUS_MPIE()  CSRS(mstatus, MSTATUS_MPIE_Msk)
#define CLR_MSTATUS_MPIE()  CSRC(mstatus, MSTATUS_MPIE_Msk)

// Reactivate mstatus.MPP if necessary.
#if 0

#define MSTATUS_MPP_Pos     2
#define MSTATUS_MPP_Msk     4

#define GET_MSTATUS_MPP()   __GET_CSR_BIT(mstatus, MSTATUS_MPP_Msk, \
                                MSTATUS_MPP_Pos)
#define SET_MSTATUS_MPP_U_MODE()    CSRC(mstatus, MSTATUS_MPP_Msk)
#define SET_MSTATUS_MPP_M_MODE()    CSRS(mstatus, MSTATUS_MPP_Msk)

#else

#define MSTATUS_MPP_Pos     0
#define MSTATUS_MPP_Msk     0

#define GET_MSTATUS_MPP()
#define SET_MSTATUS_MPP_U_MODE()
#define SET_MSTATUS_MPP_M_MODE()

#endif

/***** mstatus_store *****/
byte mstatus_store[promela_TASK_NUMBER+1]; // Include the idle task

/***** mtvec *****/

/* mtvec register references the trap handler */
#define mtvec   TRAP_ID

/***** mepc *****/

/* In the real hardware, mepc register points to the interrupted instruction.
 * In our model, however, mepc register references the identification number
 * of the interrupted user task.
 */
byte mepc = 0;

/***** mcause *****/

byte mcause = 0;

/***** mie and mip *****/

// TODO: MIE_MEIE (machine external interrupt)

/* Upper two bits represent mie register */
#define MIE_MTIE_Pos    2
#define MIE_MTIE_Msk    4

/* Lower two bits represent mip register */
#define MIP_MTIP_Pos    0
#define MIP_MTIP_Msk    1

byte mie_mip = 0;

#define GET_MIE_MTIE()  __GET_CSR_BIT(mie_mip, MIE_MTIE_Msk, MIE_MTIE_Pos)
#define SET_MIE_MTIE()  CSRS(mie_mip, MIE_MTIE_Msk)
#define CLR_MIE_MTIE()  CSRC(mie_mip, MIE_MTIE_Msk)

#define GET_MIP_MTIP()  __GET_CSR_BIT(mie_mip, MIP_MTIP_Msk, MIP_MTIP_Pos)
#define SET_MIP_MTIP()  CSRS(mie_mip, MIP_MTIP_Msk)
#define CLR_MIP_MTIP()  CSRC(mie_mip, MIP_MTIP_Msk)

// TODO: Use mtimer and mtimecmp to model the timer interrupt?
#define INT_TAKE    (GET_MSTATUS_MIE() && GET_MIE_MTIE() && GET_MIP_MTIP())
#define INT_SAFE    (!INT_TAKE)
#define EXP_IS_NOT_TAKEN    (mcause != M_ECALL_EXCEPTION)

#define D_TAKEN_INT(_id) \
    if \
    :: EXP_IS_NOT_TAKEN && INT_TAKE -> \
        _trap_entry(M_TIMER_INTERRUPT); \
    :: else \
    fi

#define TIMER_INT_IRQ   SET_MIP_MTIP()

#endif

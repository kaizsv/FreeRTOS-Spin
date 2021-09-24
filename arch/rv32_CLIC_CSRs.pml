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

#define MSTATUS_MPP_Pos     2
#define MSTATUS_MPP_Msk     4

unsigned mstatus : 4 = 0;

#define GET_MSTATUS_MIE()   __GET_CSR_BIT(mstatus, MSTATUS_MIE_Msk, \
                                MSTATUS_MIE_Pos)
#define SET_MSTATUS_MIE()   CSRS(mstatus, MSTATUS_MIE_Msk)
#define CLR_MSTATUS_MIE()   CSRC(mstatus, MSTATUS_MIE_Msk)

#define GET_MSTATUS_MPIE()  __GET_CSR_BIT(mstatus, MSTATUS_MPIE_Msk, \
                                MSTATUS_MPIE_Pos)
#define SET_MSTATUS_MPIE()  CSRS(mstatus, MSTATUS_MPIE_Msk)
#define CLR_MSTATUS_MPIE()  CSRC(mstatus, MSTATUS_MPIE_Msk)

#define GET_MSTATUS_MPP()   __GET_CSR_BIT(mstatus, MSTATUS_MPP_Msk, \
                                MSTATUS_MPP_Pos)
#define SET_MSTATUS_MPP_U_MODE()    CSRC(mstatus, MSTATUS_MPP_Msk)
#define SET_MSTATUS_MPP_M_MODE()    CSRS(mstatus, MSTATUS_MPP_Msk)

/***** mstatus_store *****/
typedef mstatus_t {
    unsigned sp : 4 = 0;
}
mstatus_t mstatus_store[promela_TASK_NUMBER+1]; // Include the idle task

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

unsigned mie_mip : 4 = 0;

#define GET_MIE_MTIE()  __GET_CSR_BIT(mie_mip, MIE_MTIE_Msk, MIE_MTIE_Pos)
#define SET_MIE_MTIE()  CSRS(mie_mip, MIE_MTIE_Msk)
#define CLR_MIE_MTIE()  CSRC(mie_mip, MIE_MTIE_Msk)

#define GET_MIP_MTIP()  __GET_CSR_BIT(mie_mip, MIP_MTIP_Msk, MIP_MTIP_Pos)
#define SET_MIP_MTIP()  CSRS(mie_mip, MIP_MTIP_Msk)
#define CLR_MIP_MTIP()  CSRC(mie_mip, MIP_MTIP_Msk)

// TODO: mtimer or mtimecmp
// TODO: How to model SYST in risc-v?
#define SET_SYST_FLAG() SET_MIP_MTIP()

#endif

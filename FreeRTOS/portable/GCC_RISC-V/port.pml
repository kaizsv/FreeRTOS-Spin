#ifndef _PORT_
#define _PORT_

#define N_TRAP              1   /* Number of trap handlers */
#define promela_EXP_NUMBER  N_TRAP

#define TRAP_ID             0

/* Machine Interrupts
 *
 * Machine Timer Interrupt
 * ID in real hardware      MSB is 1; exception code is 7
 * ID in our mode           exception code is 7; LSB is 1
 *
 * TODO: M_EXTERNAL_INTERRUPT
 */
#define N_MACHINE_INTERRUPT 1   /* Number of machine interrupts */
#define M_TIMER_INTERRUPT   15

/* Machine Exceptions
 *
 * Environment Call from M-Mode
 * ID in real hardware      MSB is 0; exception code is 11
 * ID in our model          exception code is 11; LSB is 0
 */
#define N_MACHINE_EXCEPTION 1   /* Number of machine exceptions */
#define M_ECALL_EXCEPTION   22

#define RUN_ALL_EXPS()  \
    atomic {            \
        run freertos_risc_v_trap_handler(); \
    }

#include "../../../arch/rv32_CLIC.pml"
#include "portmacro.pml"
#include "../../tasks.pml"

inline xPortStartScheduler()
{
    // Should our model set up the timer registers?

    SET_MIE_MTIE();

    xPortStartFirstTask();
}

#include "portASM.pml"

#endif

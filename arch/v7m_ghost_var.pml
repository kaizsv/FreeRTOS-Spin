#ifndef _V7M_GHOST_VAR_
#define _V7M_GHOST_VAR_

#include "../PROMELA.pml"

/* The low-order 4 bits are ignored. */
#define NON_IMPLEMENTED_LOW_BITS(val) (val >> 4)

// TODO: when to set pending bit.
byte BASEPRI = 0;
#define BASEPRI_MASK(id) ((BASEPRI == 0) || (GET_PRIO_EXP(id) < BASEPRI))

inline MSR_BASEPRI(val)
{
    assert(0 <= NON_IMPLEMENTED_LOW_BITS(val) && NON_IMPLEMENTED_LOW_BITS(val) < 16);
    BASEPRI = NON_IMPLEMENTED_LOW_BITS(val)
}

/** exception priorities
* SHPR3: exp_prio[0] and exp_prio[1]
* NVIC IP register: other exceptions
*/
byte exp_prio[promela_EXP_NUMBER] = 0;
#define GET_PRIO_EXP(PID)       exp_prio[PID]

inline SET_PRIO_EXP(id, prio)
{
    assert(0 <= NON_IMPLEMENTED_LOW_BITS(prio) && NON_IMPLEMENTED_LOW_BITS(prio) < 16);
    exp_prio[id] = NON_IMPLEMENTED_LOW_BITS(prio)
}

/** exception pending bits
* ICSR: SysTick and PendSV pending bits
* ISPR: others
*/
#define GET_PENDING(ID) ((pending_exp >> ID) & 1)
#define HAS_PENDING_EXPS (pending_exp != 0)
byte pending_exp = 0;

inline set_pending(id)
{
    assert(id < FIRST_TASK && id < 8);
    pending_exp = pending_exp | (1 << id)
}

inline clear_pending(id)
{
    assert(id < FIRST_TASK && id < 8);
    pending_exp = pending_exp & ~(1 << id)
}

/** The stack of executing processes
* EP_Stack stores the tasks, user threads or exceptions, interrupted by a high
* priority exception. The last element of the stack must be a user thread.
*/
#define STACK_SIZE      promela_EXP_NUMBER + 1
#define LAST_EP_STACK   EP_Stack[EP_Top - 1]
byte EP_Stack[STACK_SIZE] = NULL_byte;
byte EP_Top = 0;

inline push(id)
{
    assert(EP_Top < STACK_SIZE);
    EP_Stack[EP_Top] = id;
    EP_Top = EP_Top + 1;
    assert(EP_Top <= STACK_SIZE)
}

inline pop(ret)
{
    assert(EP_Top > 0)
    EP_Top = EP_Top - 1;
    ret = EP_Stack[EP_Top];
    EP_Stack[EP_Top] = NULL_byte
}

inline switch_context(new_context)
{
    assert(EP_Top == 1 && LAST_EP_STACK >= FIRST_TASK && new_context >= FIRST_TASK);
    EP_Stack[0] = new_context
}

/** exp_inactive_yet
* The variable is to record the situation that a pending exption is selected to
* become active at the exception return. This is similar to the late-arriving
* mechanism. Since the selected exception is not active yet, the model uses an
* additional variable to restore this situation.
*
* The eighth bit of the variable is used to record the situation of calling dsb
* and isb instructions. The situation clears the remaining data in the pipeline
* that the processor can active a pending exception.
*/
#define DSB_ISB         7
byte exp_inactive_yet = 0;
#define GET_INACTIVE_YET_EXP(id) ((exp_inactive_yet >> id) & 1)

inline set_exp_inactive(id)
{
    assert(id < FIRST_TASK || id == DSB_ISB);
    exp_inactive_yet = exp_inactive_yet | (1 << id)
}

inline clear_exp_inactive(id)
{
    assert(id < FIRST_TASK || id == DSB_ISB);
    exp_inactive_yet = exp_inactive_yet & ~(1 << id)
}

#endif

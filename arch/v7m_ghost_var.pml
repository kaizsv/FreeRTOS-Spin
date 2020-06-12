#ifndef _V7M_GHOST_VAR_
#define _V7M_GHOST_VAR_

#include "../PROMELA.pml"

/* The low-order 4 bits are ignored. */
#define NON_IMPLEMENTED_LOW_BITS(val) (val >> 4)

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
#define HAS_PENDING_EXPS (pending_exp > 0)
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

inline stack_check(id)
{
    if
    :: EP_Top > 0 ->
        for (idx: 0 .. (EP_Top - 1)) {
            assert(EP_Stack[idx] != id)
        }
        idx = 0
    :: else ->
        assert(EP_Stack[0] == NULL_byte)
    fi
}

inline switch_context(new_context)
{
    assert(EP_Top == 1 && LAST_EP_STACK >= FIRST_TASK && new_context >= FIRST_TASK);
    EP_Stack[0] = new_context
}

/* exp_inoperative
 * Tail-chaining and memroy barrier mechanisms assign a pending exception to EP.
 * In reality, the operation sets the pending exception to active state. In
 * PROMELA model, however, the assigned EP is not in active state yet. The
 * variable indicates that EP is inoperative and needs to be recognized at the
 * abstraction of irq.
 */
bit exp_inoperative = 0;
#define HAS_INOPERATIVE_EXP (exp_inoperative == 1)

inline set_exp_inoperative()
{
    exp_inoperative = 1
}

inline clear_exp_inoperative()
{
    exp_inoperative = 0
}

/* SysTick control */
#if (promela_TASK_NUMBER > 7)
    #error Increase data size of the SysTick counter
#endif
byte syst_count = 0;

#define SET_SYST_FLAG(cond, id) syst_count = (cond -> syst_count | (1 << (id - FIRST_TASK)) : syst_count)
#define CLEAR_SYST_FLAG()       syst_count = 0

#define SYST_USER   (syst_count & (1 << (pxCurrentTCB - FIRST_TASK)))
#define SYST_EXP    (SYST_USER && (syst_count & ~(1 << (pxCurrentTCB - FIRST_TASK))))

#endif

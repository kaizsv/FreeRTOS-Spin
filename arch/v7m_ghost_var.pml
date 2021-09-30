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

/* exception priority */
#ifdef promela_NVIC_NUMBER
    /*
    * SHPR3: exp_prio[0] and exp_prio[1]
    * NVIC IP register: other exceptions
    */
    byte exp_prio[promela_EXP_NUMBER] = 16;
    #define GET_PRIO_EXP(_id)   exp_prio[_id]
    inline SET_PRIO_EXP(_id, prio)
    {
        assert(0 <= NON_IMPLEMENTED_LOW_BITS(prio) && NON_IMPLEMENTED_LOW_BITS(prio) < 16);
        exp_prio[_id] = NON_IMPLEMENTED_LOW_BITS(prio)
    }
#else
    /* Since the priority of SysTick and PendSV are static, it is unnecessary
     * to declare the exp_prio array. */
    #define THE_STATIC_PRIORITY 15
    #define GET_PRIO_EXP(_id)   THE_STATIC_PRIORITY
    inline SET_PRIO_EXP(_id, prio)
    {
        assert(NON_IMPLEMENTED_LOW_BITS(prio) == THE_STATIC_PRIORITY);
        assert(_id == PendSV_ID || _id == SysTick_ID);
    }
#endif

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
#if (promela_EXP_NUMBER != 2)
    #error Extend this macro if promela_NVIC_NUMBER is not equal to 2.
#endif
    if
    :: EP_Top > 0 ->
        assert(
            EP_Stack[0] != id &&
            EP_Stack[1] != id &&
            EP_Stack[2] != id
        );
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
#define SET_SYST_FLAG()     pending_exp = pending_exp | 2
#define CLEAR_SYST_FLAG()   clear_pending(SysTick_ID)

#define SYST                GET_PENDING(SysTick_ID)

#endif

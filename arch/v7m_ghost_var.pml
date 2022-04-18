#ifndef _V7M_GHOST_VAR_
#define _V7M_GHOST_VAR_

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
    /* SHPR3: exp_prio[0] and exp_prio[1]
     * NVIC IP register: other exceptions */
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

#if (promela_EXP_NUMBER == 2 && GET_PRIO_EXP(PendSV_ID) == GET_PRIO_EXP(SysTick_ID))

#define STACK_SIZE      1
#define LAST_EP_STACK   EP_Stack
byte EP_Stack = NULL_byte;

inline push(id)
{
    assert(LAST_EP_STACK == NULL_byte);
    EP_Stack = id;
}

inline pop(ret)
{
    assert(LAST_EP_STACK != NULL_byte);
    ret = EP_Stack;
    EP_Stack = NULL_byte;
}

inline stack_check(id)
{
    assert((LAST_EP_STACK == NULL_byte || LAST_EP_STACK >= FIRST_TASK));
}

#define INT_TAKE \
    (((GET_PENDING(PendSV_ID) && BASEPRI_MASK(PendSV_ID)) || \
        (GET_PENDING(SysTick_ID) && BASEPRI_MASK(SysTick_ID))) && \
        EP >= FIRST_TASK)
#define INT_SAFE (!INT_TAKE)

/* According to the Application Note 321, the Cortex-M3/M4 processor will
 * recoginze interrupts are dis/enabled in the following three processor
 * clocks after the system registers are changed (Cortex-M3/M4 has a three
 * stages pipeline). */
#define D_TAKEN_INT() \
    if \
    :: INT_TAKE -> \
        /* Expanding the macro __exp_taken(id) */ \
        push(EP); \
        /* __exp_taken(id) without clearing the pending bit. */ \
        EP = (GET_PENDING(PendSV_ID) -> PendSV_ID : SysTick_ID); \
    :: else \
    fi

#else

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

#error Implement the macros, stack_check(id), INT_TAKE, INT_SAFE, and D_TAKEN_INT(id).

#endif

inline switch_context(new_context)
{
#if (promela_EXP_NUMBER == 2 && GET_PRIO_EXP(PendSV_ID) == GET_PRIO_EXP(SysTick_ID))
    assert(LAST_EP_STACK != NULL_byte && LAST_EP_STACK >= FIRST_TASK && new_context >= FIRST_TASK);
#else
    assert(EP_Top == 1 && LAST_EP_STACK >= FIRST_TASK && new_context >= FIRST_TASK);
#endif
    EP_Stack[0] = new_context
}

/* SysTick control */
#define TIMER_INT_IRQ       set_pending(SysTick_ID)

#endif

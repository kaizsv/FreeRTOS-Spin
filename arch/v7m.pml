#ifndef _V7M_
#define _V7M_

#include "v7m_ghost_var.pml"

inline get_high_prio_pending(ret)
{
    /* at least one exception is pending */
    assert(HAS_PENDING_EXPS && ret == NULL_byte);

#if (promela_EXP_NUMBER == 2 && GET_PRIO_EXP(PendSV_ID) == GET_PRIO_EXP(SysTick_ID))
    /* NOTE: Since PendSV has smaller exception number than SysTick,
     * PendSV is first selected when both of them are pending. */
    ret = (GET_PENDING(PendSV_ID) -> PendSV_ID : SysTick_ID);
#elif (promela_EXP_NUMBER < NULL_byte)
    for (hidden_idx: 0 .. (promela_EXP_NUMBER - 1)) {
        ret = (GET_PENDING(hidden_idx) &&
            ((ret == NULL_byte) || (GET_PRIO_EXP(hidden_idx) < GET_PRIO_EXP(ret))) ->
            hidden_idx : ret);
    }
    hidden_idx = NULL_byte;
    assert(ret != NULL_byte);
#else
    #error
#endif
}

#if 0
inline __exp_taken(id)
{
    clear_pending(id);
    EP = id
}

inline __exp_entry(id)
{
    push(EP);
    exp_taken(id)
}
#endif

inline exp_entry(gen_id)
{
    atomic { (EP == gen_id) -> clear_pending(gen_id); }
}

// TODO: redesign tail chaining if the last process in the stack is an interrupt.
inline tail_chaining(high_pending_exp)
{
    get_high_prio_pending(high_pending_exp);
    assert(BASEPRI_MASK(high_pending_exp) && LAST_EP_STACK >= FIRST_TASK);
    /* __exp_taken(high_pending_exp) without clearing the pending bit. */
    EP = high_pending_exp;
    high_pending_exp = NULL_byte /* reset local variable */
}

inline exp_return(temp_var)
{
    if
    :: HAS_PENDING_EXPS ->
        tail_chaining(temp_var)
    :: else ->
        pop(EP)
    fi
}

#endif

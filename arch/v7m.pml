#ifndef _V7M_
#define _V7M_

#include "v7m_ghost_var.pml"

inline get_high_prio_pending(ret)
{
#if (promela_EXP_NUMBER != 2)
    #error Extend this macro if promela_NVIC_NUMBER is not equal to 2.
#endif
#if (GET_PRIO_EXP(PendSV_ID) != GET_PRIO_EXP(SysTick_ID))
    #error Extend this macro if exceptions have different priority setting.
#endif
    /* at least one exception is pending */
    assert(HAS_PENDING_EXPS && ret == NULL_byte);

    ret = (GET_PENDING(PendSV_ID) -> PendSV_ID : SysTick_ID);

    /* NOTE: Since PendSV has smaller exception number than SysTick,
     * PendSV is first selected when both of them are pending. */
}

/* According to section 4.10 in Application Note 321, the dsb instruction
 * followed by the isb force the new state is recognized by the subsequent
 * instructions. */
inline v7m_memory_barrier(_wait_unil, high_pending_exp)
{
    d_step {
        assert(_wait_unil == EP && high_pending_exp == NULL_byte);
        if
        :: HAS_PENDING_EXPS ->
            assert(!HAS_INOPERATIVE_EXP);
            get_high_prio_pending(high_pending_exp);
            if
            :: BASEPRI_MASK(high_pending_exp) && (EP >= FIRST_TASK || GET_PRIO_EXP(high_pending_exp) < GET_PRIO_EXP(EP)) ->
                inoperative_exp_entry(high_pending_exp);
            :: else ->
                assert(high_pending_exp != EP);
            fi;
            high_pending_exp = NULL_byte; /* reset variable */
        :: else
        fi
    };
    (EP == _wait_unil)
}

inline inoperative_exp_taken(id)
{
    set_exp_inoperative();
    EP = id
}

inline inoperative_exp_entry(id)
{
    push(EP);
    inoperative_exp_taken(id)
}

inline exp_taken(id)
{
    clear_pending(id);
    EP = id
}

inline exp_entry(id)
{
    push(EP);
    exp_taken(id)
}

/* an abstraction of SysTick interrupt request */
inline syst_irq(gen_id)
{
atomic {
    if
    :: SYST && BASEPRI_MASK(gen_id) && (EP >= FIRST_TASK) ->
        /* EP is a user task. */
        assert(!HAS_INOPERATIVE_EXP && EP_Top == 0);
        stack_check(gen_id);
        exp_entry(gen_id)
    :: SYST && BASEPRI_MASK(gen_id) && (EP < FIRST_TASK) && (GET_PRIO_EXP(gen_id) < GET_PRIO_EXP(EP)) ->
        assert(!GET_PENDING(gen_id) && (EP != gen_id));
        stack_check(gen_id);
        if
        :: HAS_INOPERATIVE_EXP ->
            /* late-arriving entry:
             * EP is inoperative that cannot be pushed onto EP_Stack */
            clear_exp_inoperative();
            exp_taken(gen_id)
        :: else ->
            /* interrupt entry */
            exp_entry(gen_id)
        fi
    :: SYST && BASEPRI_MASK(gen_id) && (EP < FIRST_TASK) && (GET_PRIO_EXP(gen_id) >= GET_PRIO_EXP(EP)) ->
        assert((EP != gen_id) || HAS_INOPERATIVE_EXP);

        /* wait for re-entrying from tail-chaining */
        (EP == gen_id);

        /* tail-chaining entry */
        assert(BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && HAS_INOPERATIVE_EXP);
        stack_check(gen_id);
        clear_exp_inoperative();
        exp_taken(gen_id)
    :: SYST && !BASEPRI_MASK(gen_id) ->
        assert(!HAS_INOPERATIVE_EXP && (EP != gen_id));

        /* wait for re-entrying from memory barrier */
        (EP == gen_id);

        /* memory barrier entry */
        assert(BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && HAS_INOPERATIVE_EXP);
        stack_check(gen_id);
        clear_exp_inoperative();
        exp_taken(gen_id)
    fi
}   }

/* an abstraction of a software-generated interrupt request */
inline soft_gen_irq(gen_id)
{
atomic {
    if
    :: BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && (EP >= FIRST_TASK) ->
        /* EP is a user task. */
        assert(!HAS_INOPERATIVE_EXP && EP_Top == 0);
        stack_check(gen_id);
        exp_entry(gen_id);
        assert(!HAS_PENDING_EXPS)
    :: BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && (EP < FIRST_TASK) && (GET_PRIO_EXP(gen_id) < GET_PRIO_EXP(EP)) ->
        assert(false)
    :: GET_PENDING(gen_id) && (EP == gen_id) ->
        /* entry of memory barrier or tail-chaining */
        assert(BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && HAS_INOPERATIVE_EXP);
        stack_check(gen_id);
        clear_exp_inoperative();
        exp_taken(gen_id)
    fi
}   }

inline tail_chaining(high_pending_exp)
{
    get_high_prio_pending(high_pending_exp);
    // redesign tail chaining if the last process in the stack is an interrupt.
    assert(BASEPRI_MASK(high_pending_exp) && !HAS_INOPERATIVE_EXP && LAST_EP_STACK >= FIRST_TASK);
    inoperative_exp_taken(high_pending_exp);
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

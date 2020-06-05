#ifndef _V7M_
#define _V7M_

#include "v7m_ghost_var.pml"

inline get_high_prio_pending(ret)
{
    /* ensure there is at least one pending exception. */
    assert(ret == NULL_byte && promela_EXP_NUMBER < NULL_byte);
    for (idx: 0 .. (promela_EXP_NUMBER - 1)) {
        if
        :: GET_PENDING(idx) && (ret == NULL_byte || GET_PRIO_EXP(idx) < GET_PRIO_EXP(ret)) ->
            ret = idx
        :: else
        fi
    }
    idx = 0;
    assert(ret != NULL_byte)
}

/* According to section 4.10 in Application Note 321, the dsb instruction
 * followed by the isb force the new state is recognized by the subsequent
 * instructions. */
inline v7m_memory_barrier(_wait_unil, high_pending_exp)
{
    if
    :: HAS_PENDING_EXPS ->
        assert(!HAS_INOPERATIVE_EXP);
        get_high_prio_pending(high_pending_exp);
        if
        :: BASEPRI_MASK(high_pending_exp) && (EP >= FIRST_TASK || GET_PRIO_EXP(high_pending_exp) < GET_PRIO_EXP(EP)) ->
            inoperative_exp_entry(high_pending_exp);
            high_pending_exp = NULL_byte; /* reset local variable */

            (EP == _wait_unil)
        :: else ->
            assert(high_pending_exp != EP);
            high_pending_exp = NULL_byte /* reset local variable */
        fi
    :: else
    fi
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
    do
    :: atomic { SYST && BASEPRI_MASK(gen_id) && (EP >= FIRST_TASK) ->
        /* EP is a user task. */
        assert(!HAS_PENDING_EXPS && !HAS_INOPERATIVE_EXP && EP_Top == 0);
        stack_check(gen_id);
        exp_entry(gen_id);
        break
       }
#if 0
    :: atomic { SYST && BASEPRI_MASK(gen_id) && (EP < FIRST_TASK) && (GET_PRIO_EXP(gen_id) < GET_PRIO_EXP(EP)) ->
        assert(!GET_PENDING(gen_id) && (gen_id != EP));
        stack_check(gen_id);
        if
        :: HAS_INOPERATIVE_EXP ->
            /* late-arriving entry:
             * EP is inoperative that cannot be pushed onto EP_Stack */
            clear_exp_inoperative();
            exp_taken(gen_id)
        :: else ->
            /* preemption entry */
            exp_entry(gen_id)
        fi
       }
#endif
    :: atomic { SYST && BASEPRI_MASK(gen_id) && (EP < FIRST_TASK) && (GET_PRIO_EXP(gen_id) >= GET_PRIO_EXP(EP)) ->
        if
        :: (gen_id == EP) ->
            /* memory barrier or tail-chaining entry */
            assert(GET_PENDING(gen_id) && HAS_INOPERATIVE_EXP);
            stack_check(gen_id);
            clear_exp_inoperative();
            exp_taken(gen_id);
            break
        :: else ->
            // TODO: solve the proble of re-setting pending state
            // assert(!GET_PENDING(gen_id));
            set_pending(gen_id)
        fi
       }
    :: atomic { SYST && !BASEPRI_MASK(gen_id) ->
        assert(!HAS_INOPERATIVE_EXP);
        set_pending(gen_id)
       }
    od
}

/* an abstraction of a software-generated interrupt request */
inline soft_gen_irq(gen_id)
{
    do
    :: atomic { BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && (EP >= FIRST_TASK) ->
        /* EP is a user task. */
        assert(!HAS_INOPERATIVE_EXP && EP_Top == 0);
        stack_check(gen_id);
        exp_entry(gen_id);
        assert(!HAS_PENDING_EXPS);
        break
       }
    :: atomic { BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && (GET_PRIO_EXP(gen_id) < GET_PRIO_EXP(EP)) ->
        assert(false)
       }
    :: atomic { BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && (GET_PRIO_EXP(gen_id) >= GET_PRIO_EXP(EP)) ->
        if
        :: (gen_id == EP) ->
            /* memory barrier or tail-chaining entry */
            assert(HAS_INOPERATIVE_EXP);
            stack_check(gen_id);
            clear_exp_inoperative();
            exp_taken(gen_id);
            break
        :: else
        fi
       }
    od
}

inline tail_chaining(high_pending_exp)
{
    get_high_prio_pending(high_pending_exp);
    assert(BASEPRI_MASK(high_pending_exp) && !HAS_INOPERATIVE_EXP);
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

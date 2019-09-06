#ifndef _V7M_
#define _V7M_

#include "v7m_ghost_var.pml"

inline get_high_prio_pending(ret)
{
    /* make sure at least one exception is pended. */
    assert(ret == NULL_byte);
    for (idx: 0 .. (promela_EXP_NUMBER - 1)) {
        if
        :: GET_PENDING(idx) && ret == NULL_byte ->
            ret = idx
        :: else ->
            if
            :: GET_PENDING(idx) && (GET_PRIO_EXP(idx) < GET_PRIO_EXP(ret)) ->
                ret = idx
            :: else
            fi
        fi
    }
    idx = 0;
    /* check the pending bit if the return value is the first exp. */
    assert(ret != NULL_byte)
}

/** Document: Application Note 321--4.10 Changing priority level of an interrupt
* To let the processor recognize a pending exception, the memory barrier flushes
* the pipe lines.
**
* https://developer.arm.com/docs/dai0321/latest
**/
inline v7m_memory_barrier(high_pending_exp)
{
    if
    :: HAS_PENDING_EXPS ->
        assert(exp_inactive_yet == 0);
        get_high_prio_pending(high_pending_exp);
        if
        :: BASEPRI_MASK(high_pending_exp) && (EP >= FIRST_TASK || GET_PRIO_EXP(high_pending_exp) < GET_PRIO_EXP(EP)) ->
            set_exp_inactive(DSB_ISB);

            push(EP);
            EP = high_pending_exp;
            /* reset variable as soon as possible */
            high_pending_exp = NULL_byte;

            (EP == _PID)
        :: else ->
            assert(high_pending_exp != EP);
            /* reset variable as soon as possible */
            high_pending_exp = NULL_byte
        fi
    :: else
    fi
}

inline exp_entry(id)
{
    assert(!GET_INACTIVE_YET_EXP(id));
    clear_pending(id);
    push(EP);
    EP = id
}

// TODO: in stack check
/* The generation of the exception is from hardware that the generation is
 * arbitrary. */
inline hard_exp_request(gen_id)
{
    do
    :: atomic { BASEPRI_MASK(gen_id) && (gen_id == EP) ->
        /* assure the process is a pended exception. */
        assert(gen_id < FIRST_TASK && GET_PENDING(gen_id));
        /* clear the pending bit and enter the handler. */
        clear_pending(gen_id);
        if
        :: GET_INACTIVE_YET_EXP(gen_id) ->
            /* The generated exception is selected through the tail-chaining
             * mechanism. */
            assert(!GET_INACTIVE_YET_EXP(DSB_ISB));
            clear_exp_inactive(gen_id)
        :: else ->
            /* The generated exception is selected because the dsb and the isb
             * instructions flush the pipeline. */
            assert(GET_INACTIVE_YET_EXP(DSB_ISB));
            clear_exp_inactive(DSB_ISB);
        fi;
        break
       }
    :: atomic { BASEPRI_MASK(gen_id) && (gen_id != EP) && (EP >= FIRST_TASK) ->
        /* The executing process is a user task. Since the pending bit of the
        *  generated exp will be cleared in exp_entry, there is no need to set
        *  the bit. Moreover, it is necessary to separate the situations if EP
        *  is a user task or an exception. Because they have different priority
        *  setting. */
        if
        :: !HAS_PENDING_EXPS ->
            exp_entry(gen_id);
            break
        :: else
        fi
       }
    :: atomic { BASEPRI_MASK(gen_id) && (gen_id != EP) && (EP < FIRST_TASK) ->
        assert(!GET_INACTIVE_YET_EXP(gen_id));
        if
        :: GET_PRIO_EXP(gen_id) < GET_PRIO_EXP(EP) ->
            assert(false)
//            if
//            :: GET_INACTIVE_YET_EXP(EP) ->
//                /** late-arriving mechanism
//                * The executing exp can not be added into the stack since it
//                * is not active yet. */
//                assert(!GET_PENDING(gen_id));
//                clear_exp_inactive(EP);
//                EP = gen_id
//            :: else ->
//                exp_entry(gen_id)
//            fi;
//            break
        :: else ->
            /* The priority of the generated exception is insufficient to
            *  preemptive the executing task. Set the pending bit. */
            set_pending(gen_id)
        fi
       }
    :: atomic { else ->
        assert(!BASEPRI_MASK(gen_id));
        set_pending(gen_id)
       }
    od
}

// TODO: in stack check
/* The generation of the exception is from software (pending bit) that the
 * exception is taken only if the pending bit is set. */
inline soft_exp_request(gen_id)
{
    do
    :: atomic { BASEPRI_MASK(gen_id) && (gen_id == EP) ->
        /* assure the process is a pended exception. */
        assert(gen_id == PendSV_ID && GET_PENDING(gen_id));
        /* clear the pending bit and enter the handler. */
        clear_pending(gen_id);
        if
        :: GET_INACTIVE_YET_EXP(gen_id) ->
            /* The generated exception is selected through the tail-chaining
             * mechanism. */
            assert(!GET_INACTIVE_YET_EXP(DSB_ISB));
            clear_exp_inactive(gen_id)
        :: else ->
            /* The generated exception is selected because the dsb and the isb
             * instructions flush the pipeline. */
            assert(GET_INACTIVE_YET_EXP(DSB_ISB));
            clear_exp_inactive(DSB_ISB);
        fi;
        break
       }
    :: atomic { BASEPRI_MASK(gen_id) && GET_PENDING(gen_id) && (gen_id != EP) && (EP >= FIRST_TASK) ->
        /* PendSV exception needs to have the lowest priority. */
        assert(EP_Top == 0);
        /* The generated exception can interrupt user tasks only if it is pending. */
        if
        :: (pending_exp & ~(1 << gen_id)) == 0 ->
            exp_entry(gen_id);
            break
        :: else
        fi
       }
    :: atomic { else ->
        /* FIXME: Only PendSV is software request and it has the lowest priority. */
        assert(EP >= FIRST_TASK || GET_PRIO_EXP(gen_id) >= GET_PRIO_EXP(EP))
       }
    od
}

inline exp_return(high_pending_exp, tail_chaining)
{
    assert(tail_chaining == 0);
    if
    :: HAS_PENDING_EXPS ->
        /** tail-chaining mechanism
        * Check the high priority pending exceptions can preempt the last active
        * processe. */
        get_high_prio_pending(high_pending_exp);
        /* exp_request has the same conditions. */
        if
        :: BASEPRI_MASK(high_pending_exp) && (LAST_EP_STACK >= FIRST_TASK || GET_PRIO_EXP(high_pending_exp) < GET_PRIO_EXP(LAST_EP_STACK)) ->
            tail_chaining = 1
        :: else ->
            assert(high_pending_exp != LAST_EP_STACK)
        fi
    :: else
    fi;
    if
    :: tail_chaining ->
        /* set the inactive ghost bit and change EP directly. */
        set_exp_inactive(high_pending_exp);
        EP = high_pending_exp;
        /* reset local variable */
        tail_chaining = 0
    :: else ->
        /* return to the last task in the stack. */
        pop(EP)
    fi;
    /* check memory barrier flag if the exception was interrupted by others. */
    assert(!GET_INACTIVE_YET_EXP(DSB_ISB));
    /* reset local variable */
    high_pending_exp = NULL_byte
}

#endif

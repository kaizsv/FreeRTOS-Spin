#ifndef _QUEUE_
#define _QUEUE_

#include "../FreeRTOS.pml"
#include "tasks.pml"
#include "queue.h.pml"

/* FIXME: To reduce the size of a single state, we merged the Rx and Tx Locks
 * into a single variable. This modification causes the UNLOCKED value is 15. */
#define queueUNLOCKED                       15
#define queueLOCKED_UNMODIFIED              0

#if (configUSE_PREEMPTION == 0)
    #define queueYIELD_IF_USING_PREEMPTION()
#else
    #define queueYIELD_IF_USING_PREEMPTION(_id, temp_var) portYIELD_WITHIN_API(_id, temp_var)
#endif

#include "include/Queue_Declarator.pml"

#define queueQUEUE_IS_MUTEX(pxQueue) \
    (queueGET_uxQueueType(pxQueue) == queueQUEUE_TYPE_MUTEX || queueGET_uxQueueType(pxQueue) == queueQUEUE_TYPE_RECURSIVE_MUTEX)
/* If the item size of a Queue is zero, then the queue is not the base type. */
#define queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue) (queueGET_uxQueueType(pxQueue) > queueQUEUE_TYPE_BASE)

#define prvIsQueueEmpty(pxQueue)    (pxQueue.uxMessagesWaiting == 0)
#define prvIsQueueFull(pxQueue)     (pxQueue.uxMessagesWaiting == pxQueue.uxLength)

inline prvLockQueue(_id, pxQueue, temp_var)
{
    taskENTER_CRITICAL(_id, temp_var);
    if
    :: SELE(_id, queueGET_cRxLock(pxQueue) == queueUNLOCKED) ->
        AWAIT_D(_id, queueSET_cRxLock(pxQueue, queueLOCKED_UNMODIFIED))
    :: ELSE(_id, queueGET_cRxLock(pxQueue) == queueUNLOCKED)
    fi;
    if
    :: SELE(_id, queueGET_cTxLock(pxQueue) == queueUNLOCKED) ->
        AWAIT_D(_id, queueSET_cTxLock(pxQueue, queueLOCKED_UNMODIFIED))
    :: ELSE(_id, queueGET_cTxLock(pxQueue) == queueUNLOCKED)
    fi;
    taskEXIT_CRITICAL(_id, temp_var)
}

inline xQueueGenericCreate(pxNewQueue, QueueID, uxQueueLength, ucQueueType)
{
    assert(QueueID < promela_QUEUE_NUMBER && 0 < uxQueueLength);

    /* Initialize Queue Storage */
    for (idx: 0 .. (uxQueueLength - 1)) {
        pxNewQueue.u.multi_bytes[idx] = NULL_byte
    }
    idx = 0;

    /* prvInitialseNewQueue */
    queueSET_ListIndex(pxNewQueue, QueueID * 2);
    queueSET_uxQueueType(pxNewQueue, ucQueueType);
    pxNewQueue.uxLength = uxQueueLength;
    // TODO: configUSE_QUEUE_SETS

    /* xQueueReset: FIXME: reuse*/
//    taskENTER_CRITICAL();
    pxNewQueue.uxMessagesWaiting = 0;
    queueSET_pcWriteTo(pxNewQueue, 0);
    queueSET_pcReadFrom(pxNewQueue, uxQueueLength - 1);
    queueSET_cRxLock(pxNewQueue, queueUNLOCKED);
    queueSET_cTxLock(pxNewQueue, queueUNLOCKED);

    /* xNewQueue == true */
    vListInitialise(LISTs[queueGET_ListIndex(pxNewQueue) + xTasksWaitingToSend]);
    vListInitialise(LISTs[queueGET_ListIndex(pxNewQueue) + xTasksWaitingToReceive]);
//    taskEXIT_CRITICAL()

    // TODO: configUSE_QUEUE_SETS
}

#if (configUSE_MUTEXES == 1)

inline prvInitialiseMutex(pxNewQueue, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id)
{
    pxNewQueue.xSemaphore.xMutexHolder = NULL_byte;
    pxNewQueue.xSemaphore.uxRecursiveCallCount = 0;
    assert(queueQUEUE_IS_MUTEX(pxNewQueue));

    xQueueGenericSend(pxNewQueue, NULL_byte, 0, queueSEND_TO_BACK, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id)
}

inline xQueueCreateMutex(ucQueueType, pxNewQueue, QueueID, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id)
{
    xQueueGenericCreate(pxNewQueue, QueueID, 1, ucQueueType);
    prvInitialiseMutex(pxNewQueue, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id)
}

#endif /* configUSE_MUTEXES */

inline xQueueGenericSend(pxQueue, pvItemToQueue, xTicksToWait, xCopyPosition, xReturn, xYieldRequired, xIsNDTimeOut, temp_var, temp_var2, _id)
{
    AWAIT_A(_id, xReturn = 0;
        assert(xYieldRequired == false && xIsNDTimeOut == false);
        assert(temp_var == NULL_byte && temp_var2 == NULL_byte);
        assert(!((pvItemToQueue == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue))));
        assert(!((xCopyPosition == queueOVERWRITE) && pxQueue.uxLength != 1)));
    // TODO: xTaskGetSchedulerState

loop_send:
    taskENTER_CRITICAL(_id, temp_var);
    if
    :: SELE(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE) ->
        #if (configUSE_QUEUE_SETS == 1)
            // TODO: configUSE_QUEUE_SETS
        #else
        prvCopyDataToQueue(_id, pxQueue, pvItemToQueue, xCopyPosition, xYieldRequired, temp_var, temp_var2);

        if
        :: SELE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])) ->
            xTaskRemoveFromEventList(_id, temp_var, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], xReturn);
            if
            :: atomic { SELE(_id, xReturn != false) -> xReturn = false };
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var);
            :: atomic { ELSE(_id, xReturn != false) -> assert(xReturn == false) }
            fi
        :: ELSE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])) ->
            if
            :: atomic { SELE(_id, xYieldRequired != false) -> xYieldRequired = false };
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: atomic { ELSE(_id, xYieldRequired != false) -> assert(xYieldRequired == false) }
            fi
        fi;
        #endif /* configUSE_QUEUE_SETS */

        taskEXIT_CRITICAL(_id, temp_var);

        AWAIT_A(_id, xReturn = true; goto return_send)
    :: ELSE(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE) ->
#ifdef QUEUE_SEND_EXIT_CRITICAL
        if
        :: SELE(_id, xTicksToWait == 0) ->
            taskEXIT_CRITICAL(_id, temp_var);
            AWAIT_A(_id, assert(xReturn == false); goto return_send)
        :: SELE(_id, xTicksToWait != 0 && xTicksToWait != portMAX_DELAY) ->
            /* non-deterministic timed out */
            if
            :: SELE(_id, xIsNDTimeOut == false) ->
                AWAIT_D(_id, xIsNDTimeOut = false)
            :: SELE(_id, xIsNDTimeOut == false) ->
                AWAIT_D(_id, xIsNDTimeOut = true)
            :: ELSE(_id, xIsNDTimeOut == false)
            fi
        :: ELSE(_id, xTicksToWait != portMAX_DELAY)
        fi
#else /* QUEUE_SEND_EXIT_CRITICAL */
        assert(false)
#endif /* QUEUE_SEND_EXIT_CRITICAL */
    fi;
#ifdef QUEUE_SEND_EXIT_CRITICAL
    taskEXIT_CRITICAL(_id, temp_var);

    vTaskSuspendAll(_id);
    prvLockQueue(_id, pxQueue, temp_var);

    if
    :: SELE(_id, xIsNDTimeOut == false) ->
        if
        :: SELE(_id, prvIsQueueFull(pxQueue)) ->
            vTaskPlaceOnEventList(_id, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], queueGET_ListIndex(pxQueue) + xTasksWaitingToSend, xTicksToWait, temp_var);

            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);

            xTaskResumeAll(_id, temp_var, xReturn, temp_var2);
            if
            :: atomic { SELE(_id, xReturn == false) -> assert(xReturn == false) };
                portYIELD_WITHIN_API(_id, temp_var)
            :: atomic { ELSE(_id, xReturn == false) -> xReturn = false }
            fi
        :: ELSE(_id, prvIsQueueFull(pxQueue)) ->
            /* Try again. */
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
            xTaskResumeAll(_id, temp_var, _, temp_var2)
        fi
    :: ELSE(_id, xIsNDTimeOut == false) ->
        /* The timeout has expired. */
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
        xTaskResumeAll(_id, temp_var, _, temp_var2);

        AWAIT_A(_id, assert(xReturn == false); goto return_send)
    fi;

    AWAIT_A(_id, goto loop_send);
#else /* QUEUE_SEND_EXIT_CRITICAL */
    assert(false)
#endif /* QUEUE_SEND_EXIT_CRITICAL */
return_send:
    /* reset variables as soon as possible */
    AWAIT_A(_id, xIsNDTimeOut = false;
        assert(xYieldRequired == false && temp_var == NULL_byte && temp_var2 == NULL_byte))
}

inline xQueueReceive(pxQueue, pvBuffer, xTicksToWait, xReturn, xIsNDTimeOut, temp_var, temp_var2, _id)
{
    AWAIT_A(_id, xReturn = false;
        assert(xIsNDTimeOut == false && temp_var == NULL_byte && temp_var2 == NULL_byte);
        assert(!((pvBuffer == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)))));
    // TODO xTaskGetSchedulerState

loop_receive:
    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, temp_var2 = pxQueue.uxMessagesWaiting); /* uxMessagesWaiting */
    if
    :: atomic { SELE(_id, temp_var2 > 0) -> assert(temp_var2 > 0) };
        prvCopyDataFromQueue(_id, pxQueue, pvBuffer);
        AWAIT_D(_id, pxQueue.uxMessagesWaiting = temp_var2 - 1; temp_var2 = NULL_byte);

        if
        :: SELE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])) ->
            xTaskRemoveFromEventList(_id, temp_var, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], xReturn);
            if
            :: atomic { SELE(_id, xReturn != false) -> xReturn = false };
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: atomic { ELSE(_id, xReturn != false) -> assert(xReturn == false) }
            fi
        :: ELSE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]))
        fi;

        taskEXIT_CRITICAL(_id, temp_var);
        AWAIT_A(_id, xReturn = true; goto return_receive)
    :: atomic { ELSE(_id, temp_var2 > 0) -> temp_var2 = NULL_byte };
#ifdef QUEUE_RECEIVE_EXIT_CRITICAL
        if
        :: SELE(_id, xTicksToWait == 0) ->
            taskEXIT_CRITICAL(_id, temp_var);
            AWAIT_A(_id, assert(xReturn == false); goto return_receive)
        :: SELE(_id, xTicksToWait != 0 && xTicksToWait != portMAX_DELAY) ->
            /* non-deterministic timed out */
            if
            :: SELE(_id, xIsNDTimeOut == false) ->
                AWAIT_D(_id, xIsNDTimeOut = false)
            :: SELE(_id, xIsNDTimeOut == false) ->
                AWAIT_D(_id, xIsNDTimeOut = true)
            :: ELSE(_id, xIsNDTimeOut == false)
            fi
        :: ELSE(_id, xTicksToWait != portMAX_DELAY)
        fi
#else /* QUEUE_RECEIVE_EXIT_CRITICAL */
        assert(false)
#endif /* QUEUE_RECEIVE_EXIT_CRITICAL */
    fi;
#ifdef QUEUE_RECEIVE_EXIT_CRITICAL
    taskEXIT_CRITICAL(_id, temp_var);

    vTaskSuspendAll(_id);
    prvLockQueue(_id, pxQueue, temp_var);

    if
    :: SELE(_id, xIsNDTimeOut == false) ->
        /* The timeout has not expired. */
        if
        :: SELE(_id, prvIsQueueEmpty(pxQueue)) ->
            vTaskPlaceOnEventList(_id, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive, xTicksToWait, temp_var);
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);

            xTaskResumeAll(_id, temp_var, xReturn, temp_var2);
            if
            :: atomic { SELE(_id, xReturn == false) -> assert(xReturn == false) };
                portYIELD_WITHIN_API(_id, temp_var)
            :: atomic { ELSE(_id, xReturn == false) -> xReturn = false }
            fi
        :: ELSE(_id, prvIsQueueEmpty(pxQueue)) ->
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
            xTaskResumeAll(_id, temp_var, _, temp_var2)
        fi
    :: ELSE(_id, xIsNDTimeOut == false) ->
        /* Timed out. */
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
        xTaskResumeAll(_id, temp_var, _, temp_var2);

        if
        :: SELE(_id, prvIsQueueEmpty(pxQueue)) ->
            AWAIT_A(_id, assert(xReturn == false); goto return_receive)
        :: ELSE(_id, prvIsQueueEmpty(pxQueue))
        fi
    fi;

    AWAIT_A(_id, goto loop_receive);
#else /* QUEUE_RECEIVE_EXIT_CRITICAL */
    assert(false)
#endif /* QUEUE_RECEIVE_EXIT_CRITICAL */
return_receive:
    /* reset variables as soon as possible */
    AWAIT_A(_id, xIsNDTimeOut = false; assert(temp_var == NULL_byte && temp_var2 == NULL_byte))
}

inline xQueueSemaphoreTake(pxQueue, xTicksToWait, xReturn, xInheritanceOccurred, xIsNDTimeOut, temp_var, temp_var2, _id)
{
    AWAIT_A(_id, xReturn = false;
        assert(xInheritanceOccurred == false && xIsNDTimeOut == false);
        assert(temp_var == NULL_byte && temp_var2 == NULL_byte);
        assert(queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)));
    /* TODO xTaskGetSchedulerState */

loop_take:
    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, temp_var2 = pxQueue.uxMessagesWaiting); /* uxSemaphoreCount */
    if
    :: atomic { SELE(_id, temp_var2 > 0) -> assert(temp_var2 > 0) };
        AWAIT_D(_id, pxQueue.uxMessagesWaiting = temp_var2 - 1; temp_var2 = NULL_byte);

        #if (configUSE_MUTEXES == 1)
        if
        :: SELE(_id, queueQUEUE_IS_MUTEX(pxQueue)) ->
            pvTaskIncrementMutexHeldCount(_id, pxQueue.xSemaphore.xMutexHolder)
        :: ELSE(_id, queueQUEUE_IS_MUTEX(pxQueue))
        fi;
        #endif

        if
        :: SELE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])) ->
            xTaskRemoveFromEventList(_id, temp_var, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], xReturn);
            if
            :: atomic { SELE(_id, xReturn != false) -> xReturn = false };
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: atomic { ELSE(_id, xReturn != false) -> assert(xReturn == false) }
            fi
        :: ELSE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]))
        fi;

        taskEXIT_CRITICAL(_id, temp_var);
        AWAIT_A(_id, xReturn = true; goto return_take)
    :: atomic { ELSE(_id, temp_var2 > 0) -> temp_var2 = NULL_byte };
#ifdef QUEUE_TAKE_EXIT_CRITICAL
        if
        :: SELE(_id, xTicksToWait == 0) ->
            #if (configUSE_MUTEXES == 1)
            AWAIT_A(_id, assert(xInheritanceOccurred == false));
            #endif
            taskEXIT_CRITICAL(_id, temp_var);
            AWAIT_A(_id, assert(xReturn == false); goto return_take)
        :: SELE(_id, xTicksToWait != 0 && xTicksToWait != portMAX_DELAY) ->
            /* non-deterministic timed out */
            if
            :: SELE(_id, xIsNDTimeOut == false) ->
                AWAIT_D(_id, xIsNDTimeOut = false)
            :: SELE(_id, xIsNDTimeOut == false) ->
                AWAIT_D(_id, xIsNDTimeOut = true)
            :: ELSE(_id, xIsNDTimeOut == false)
            fi
        :: ELSE(_id, xTicksToWait != portMAX_DELAY)
        fi
#else /* QUEUE_TAKE_EXIT_CRITICAL */
        assert(false)
#endif /* QUEUE_TAKE_EXIT_CRITICAL */
    fi;
#ifdef QUEUE_TAKE_EXIT_CRITICAL
    taskEXIT_CRITICAL(_id, temp_var);

    vTaskSuspendAll(_id);
    prvLockQueue(_id, pxQueue, temp_var);

    if
    :: SELE(_id, xIsNDTimeOut == false) ->
        if
        :: SELE(_id, prvIsQueueEmpty(pxQueue) != false) ->
            #if (configUSE_MUTEXES == 1)
            if
            :: SELE(_id, queueQUEUE_IS_MUTEX(pxQueue)) ->
                taskENTER_CRITICAL(_id, temp_var);
                xTaskPriorityInherit(_id, pxQueue.xSemaphore.xMutexHolder, xInheritanceOccurred, temp_var);
                taskEXIT_CRITICAL(_id, temp_var)
            :: ELSE(_id, queueQUEUE_IS_MUTEX(pxQueue))
            fi;
            #endif

            vTaskPlaceOnEventList(_id, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive, xTicksToWait, temp_var);
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);

            xTaskResumeAll(_id, temp_var, xReturn, temp_var2);
            if
            :: atomic { SELE(_id, xReturn == false) -> assert(xReturn == false) };
                portYIELD_WITHIN_API(_id, temp_var)
            :: atomic { ELSE(_id, xReturn == false) -> xReturn = false }
            fi
        :: ELSE(_id, prvIsQueueEmpty(pxQueue) != false) ->
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
            xTaskResumeAll(_id, temp_var, _, temp_var2)
        fi
    :: ELSE(_id, xIsNDTimeOut == false) ->
        /* Timed out. */
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
        xTaskResumeAll(_id, temp_var, _, temp_var2);

        if
        :: SELE(_id, prvIsQueueEmpty(pxQueue)) ->
            #if (configUSE_MUTEXES == 1)
            if
            :: atomic { SELE(_id, xInheritanceOccurred != false) -> xInheritanceOccurred = false };
                taskENTER_CRITICAL(_id, temp_var);
                prvGetDisinheritPriorityAfterTimeout(_id, pxQueue, temp_var /* uxHighestWaitingPriority */);
                vTaskPriorityDisinheritAfterTimeout(_id, pxQueue.xSemaphore.xMutexHolder, temp_var /* uxHighestWaitingPriority */, temp_var2);

                taskEXIT_CRITICAL(_id, temp_var)
            :: atomic { ELSE(_id, xInheritanceOccurred != false) -> assert(xInheritanceOccurred == false) }
            fi;
            #endif

            AWAIT_A(_id, assert(xReturn == false); goto return_take)
        :: ELSE(_id, prvIsQueueEmpty(pxQueue))
        fi
    fi;

    AWAIT_A(_id, goto loop_take);
#else /* QUEUE_TAKE_EXIT_CRITICAL */
    assert(false);
#endif /* QUEUE_TAKE_EXIT_CRITICAL */
return_take:
    /* reset variables as soon as possible */
    AWAIT_A(_id, xIsNDTimeOut = false;
        assert(xInheritanceOccurred == false && temp_var == NULL_byte && temp_var2 == NULL_byte))
}

#define uxQueueMessagesWaiting(xQueue) xQueue.uxMessagesWaiting

#if (configUSE_MUTEXES == 1)

inline prvGetDisinheritPriorityAfterTimeout(_id, pxQueue, uxHighestPriorityOfWaitingTasks)
{
    if
    :: SELE(_id, listLIST_LENGTH_IS_EXCEEDING_ZERO(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])) ->
        AWAIT_D(_id, assert(uxHighestPriorityOfWaitingTasks == false);
            uxHighestPriorityOfWaitingTasks = configMAX_PRIORITIES - listGET_ITEM_VALUE_OF_HEAD_ENTRY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]))
    :: ELSE(_id, listLIST_LENGTH_IS_EXCEEDING_ZERO(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])) ->
        AWAIT_D(_id, assert(uxHighestPriorityOfWaitingTasks == false);
            uxHighestPriorityOfWaitingTasks = tskIDLE_PRIORITY)
    fi
}

#endif /* configUSE_MUTEXES */

inline prvCopyDataToQueue(_id, pxQueue, pvItemToQueue, xPosition, xReturn, temp_var, uMessagesWaiting)
{
    AWAIT_D(_id, xReturn = false);
    AWAIT_D(_id, uMessagesWaiting = pxQueue.uxMessagesWaiting);
    if
    :: SELE(_id, queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)) ->
        #if (configUSE_MUTEXES == 1)
        if
        :: SELE(_id, queueQUEUE_IS_MUTEX(pxQueue)) ->
            /* The mutex is no longer being held. */
            xTaskPriorityDisinherit(_id, pxQueue.xSemaphore.xMutexHolder, xReturn, temp_var);
            AWAIT_D(_id, pxQueue.xSemaphore.xMutexHolder = NULL_byte)
        :: ELSE(_id, queueQUEUE_IS_MUTEX(pxQueue))
        fi
        #endif
    :: ELSE(_id, queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)) ->
        if
        :: SELE(_id, xPosition == queueSEND_TO_BACK) ->
            AWAIT_D(_id, pxQueue.xQueue.pucQueueStorage(queueGET_pcWriteTo(pxQueue)) = pvItemToQueue); // FIXME: memcpy
            AWAIT_D(_id, queueSET_pcWriteTo(pxQueue, queueGET_pcWriteTo(pxQueue) + 1));
            if
            :: SELE(_id, queueGET_pcWriteTo(pxQueue) >= pxQueue.uxLength) ->
                AWAIT_D(_id, queueSET_pcWriteTo(pxQueue, 0))
            :: ELSE(_id, queueGET_pcWriteTo(pxQueue) >= pxQueue.uxLength)
            fi
        :: ELSE(_id, xPosition == queueSEND_TO_BACK) ->
            AWAIT_D(_id, pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)) = pvItemToQueue); // FIXME: memcpy
            if
            :: SELE(_id, queueGET_pcReadFrom(pxQueue) == 0) ->
                AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, pxQueue.uxLength - 1))
            :: ELSE(_id, queueGET_pcReadFrom(pxQueue) == 0) ->
                AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, queueGET_pcReadFrom(pxQueue) - 1))
            fi;

            if
            :: SELE(_id, xPosition == queueOVERWRITE && uMessagesWaiting > 0) ->
                AWAIT_D(_id, uMessagesWaiting = uMessagesWaiting - 1)
            :: ELSE(_id, xPosition == queueOVERWRITE && uMessagesWaiting > 0)
            fi
        fi
    fi;

    AWAIT_D(_id, pxQueue.uxMessagesWaiting = uMessagesWaiting + 1; uMessagesWaiting = NULL_byte)
}

inline prvCopyDataFromQueue(_id, pxQueue, pvBuffer)
{
    if
    :: SELE(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)) ->
        AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, queueGET_pcReadFrom(pxQueue) + 1));
        if
        :: SELE(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength) ->
            AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, 0))
        :: ELSE(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength)
        fi;

        AWAIT_D(_id, pvBuffer = pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)); // FIXME: memcpy
            /* reset data in queue as soon as possible */
            pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)) = NULL_byte);
    :: ELSE(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue))
    fi
}

inline prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, temp_xReturn)
{
    AWAIT_A(_id, assert(temp_var == NULL_byte && temp_var2 == NULL_byte && temp_xReturn == false));

    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, temp_var2 = queueGET_cTxLock(pxQueue));
    do
    :: SELE(_id, temp_var2 > queueLOCKED_UNMODIFIED) ->
        #if (configUSE_QUEUE_SETS == 1)
        // TODO
        #else /* configUSE_QUEUE_SETS */
        if
        :: SELE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])) ->
            xTaskRemoveFromEventList(_id, temp_var, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], temp_xReturn);
            if
            :: atomic { SELE(_id, temp_xReturn != false) -> temp_xReturn = false };
                vTaskMissedYield(_id)
            :: atomic { ELSE(_id, temp_xReturn != false) -> assert(temp_xReturn == false) }
            fi
        :: ELSE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])) ->
            AWAIT_A(_id, break)
        fi;
        #endif /* configUSE_QUEUE_SETS */

        AWAIT_D(_id, temp_var2 = temp_var2 - 1)
    :: ELSE(_id, temp_var2 > queueLOCKED_UNMODIFIED) ->
        AWAIT_A(_id, break)
    od;
    AWAIT_A(_id, temp_var2 = NULL_byte; queueSET_cTxLock(pxQueue, queueUNLOCKED));
    taskEXIT_CRITICAL(_id, temp_var);

    /* Do the same for the Rx lock. */
    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, temp_var2 = queueGET_cRxLock(pxQueue));
    do
    :: SELE(_id, temp_var2 > queueLOCKED_UNMODIFIED) ->
        if
        :: SELE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])) ->
            xTaskRemoveFromEventList(_id, temp_var, LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], temp_xReturn);
            if
            :: atomic { SELE(_id, temp_xReturn != false) -> temp_xReturn = false };
                vTaskMissedYield(_id)
            :: atomic { ELSE(_id, temp_xReturn != false) -> assert(temp_xReturn == false) }
            fi;

            AWAIT_D(_id, temp_var2 = temp_var2 - 1)
        :: ELSE(_id, !listLIST_IS_EMPTY(LISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])) ->
            AWAIT_A(_id, break)
        fi;
    :: ELSE(_id, temp_var2 > queueLOCKED_UNMODIFIED) ->
        AWAIT_A(_id, break)
    od;
    AWAIT_A(_id, temp_var2 = NULL_byte; queueSET_cRxLock(pxQueue, queueUNLOCKED));
    taskEXIT_CRITICAL(_id, temp_var)
}

#endif

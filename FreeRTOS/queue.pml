#ifndef _QUEUE_
#define _QUEUE_

#include "../FreeRTOS.pml"
#include "tasks.pml"
#include "queue.h.pml"

/* FIXME: To reduce the size of a single state, we merged the Rx and Tx Locks
 * into a single variable. This modification causes the UNLOCKED value is 15. */
#define NULL_nibble                         15  /* 0b1111 */
#define queueUNLOCKED                       NULL_nibble
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
    :: SELE2(_id, queueGET_cRxLock(pxQueue) == queueUNLOCKED);
        AWAIT_D(_id, queueSET_cRxLock(pxQueue, queueLOCKED_UNMODIFIED))
    :: ELSE2(_id, queueGET_cRxLock(pxQueue) == queueUNLOCKED)
    fi;
    if
    :: SELE2(_id, queueGET_cTxLock(pxQueue) == queueUNLOCKED);
        AWAIT_D(_id, queueSET_cTxLock(pxQueue, queueLOCKED_UNMODIFIED))
    :: ELSE2(_id, queueGET_cTxLock(pxQueue) == queueUNLOCKED)
    fi;
    taskEXIT_CRITICAL(_id, temp_var)
}

inline xQueueGenericCreate_fixed(pxNewQueue, QueueID, uxQueueLength, ucQueueType)
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

    /* xQueueReset */
    pxNewQueue.uxMessagesWaiting = 0;
    queueSET_pcWriteTo(pxNewQueue, 0);
    queueSET_pcReadFrom(pxNewQueue, uxQueueLength - 1);
    queueSET_cRxLock(pxNewQueue, queueUNLOCKED);
    queueSET_cTxLock(pxNewQueue, queueUNLOCKED);

    /* xNewQueue == true */
    vListInitialise(QLISTs[queueGET_ListIndex(pxNewQueue) + xTasksWaitingToSend], QLIST_SIZE);
    vListInitialise(QLISTs[queueGET_ListIndex(pxNewQueue) + xTasksWaitingToReceive], QLIST_SIZE);
}

#if (configUSE_MUTEXES == 1)

inline prvInitialiseMutex(pxNewQueue, xReturn, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id)
{
    pxNewQueue.xSemaphore.xMutexHolder = NULL_byte;
    pxNewQueue.xSemaphore.uxRecursiveCallCount = 0;
    assert(queueQUEUE_IS_MUTEX(pxNewQueue));

    xQueueGenericSend(pxNewQueue, NULL_byte, 0, queueSEND_TO_BACK, xReturn, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id)
}

inline xQueueCreateMutex(ucQueueType, pxNewQueue, QueueID, xReturn, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id)
{
    xQueueGenericCreate_fixed(pxNewQueue, QueueID, 1, ucQueueType);
    prvInitialiseMutex(pxNewQueue, xReturn, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id)
}

#endif /* configUSE_MUTEXES */

inline xQueueGenericSend(pxQueue, pvItemToQueue, xTicksToWait, xCopyPosition, xReturn, xYieldRequired, xIsTimeOut, temp_var, temp_var2, _id)
{
    AWAIT_D(_id, xReturn = 0;
        assert((!xYieldRequired & !xIsTimeOut) && ((temp_var & temp_var2) == NULL_byte) &&
            (!((pvItemToQueue == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)))) &&
            (!((xCopyPosition == queueOVERWRITE) && (pxQueue.uxLength != 1)))));
do
::  taskENTER_CRITICAL(_id, temp_var);
    if
    :: SELE2(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE);
        #if (configUSE_QUEUE_SETS == 1)
            // TODO: configUSE_QUEUE_SETS
        #else
        prvCopyDataToQueue(_id, pxQueue, pvItemToQueue, xCopyPosition, xYieldRequired, temp_var, temp_var2);

        if
        :: SELE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], xReturn);
            if
            :: SELE3(_id, xReturn != false, xReturn = false);
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var);
            :: ELSE2(_id, xReturn != false)
            fi
        :: ELSE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
            if
            :: SELE3(_id, xYieldRequired != false, xYieldRequired = false);
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: ELSE2(_id, xYieldRequired != false)
            fi
        fi;
        #endif /* configUSE_QUEUE_SETS */

        taskEXIT_CRITICAL(_id, temp_var);

        AWAIT_A(_id, xIsTimeOut = false; xReturn = true; break)
    :: ELSE2(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE);
#ifdef QUEUE_SEND_EXIT_CRITICAL
        if
        :: SELE2(_id, xTicksToWait == 0);
            taskEXIT_CRITICAL(_id, temp_var);
            AWAIT_A(_id, assert(!xIsTimeOut && xReturn == false); break)
        :: ELSE2(_id, xTicksToWait == 0)
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
    :: SELE2(_id, xIsTimeOut == false);
        if
        :: SELE2(_id, prvIsQueueFull(pxQueue));
            vTaskPlaceOnEventList(_id, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], queueGET_ListIndex(pxQueue) + xTasksWaitingToSend, xTicksToWait, temp_var);

            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);

            xTaskResumeAll(_id, temp_var, xReturn, temp_var2);
            if
            :: SELE3(_id, xReturn == false, xIsTimeOut = true);
                portYIELD_WITHIN_API(_id, temp_var)
            :: ELSE3(_id, xReturn == false, xReturn = false)
            fi
        :: ELSE2(_id, prvIsQueueFull(pxQueue));
            /* Try again. */
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
            xTaskResumeAll(_id, temp_var, _, temp_var2)
        fi
    :: ELSE3(_id, xIsTimeOut == false, xIsTimeOut = false);
        /* The timeout has expired. */
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
        xTaskResumeAll(_id, temp_var, _, temp_var2);

        AWAIT_A(_id, assert(xReturn == false); break)
    fi;
#else /* QUEUE_SEND_EXIT_CRITICAL */
    assert(false)
#endif /* QUEUE_SEND_EXIT_CRITICAL */
od
}

inline xQueueReceive(pxQueue, pvBuffer, xTicksToWait, xReturn, xIsTimeOut, temp_var, temp_var2, _id)
{
    AWAIT_D(_id, xReturn = false;
        assert((!xIsTimeOut) && ((temp_var & temp_var2) == NULL_byte) &&
            (!((pvBuffer == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue))))));
do
::  taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, temp_var2 = pxQueue.uxMessagesWaiting);
    if
    :: SELE2(_id, temp_var2 > 0);
        prvCopyDataFromQueue(_id, pxQueue, pvBuffer);
        AWAIT_D(_id, pxQueue.uxMessagesWaiting = temp_var2 - 1; temp_var2 = NULL_byte);

        if
        :: SELE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]));
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], xReturn);
            if
            :: SELE3(_id, xReturn != false, xReturn = false);
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: ELSE2(_id, xReturn != false)
            fi
        :: ELSE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]))
        fi;

        taskEXIT_CRITICAL(_id, temp_var);
        AWAIT_A(_id, xIsTimeOut = false; xReturn = true; break)
    :: ELSE3(_id, temp_var2 > 0, temp_var2 = NULL_byte);
#ifdef QUEUE_RECEIVE_EXIT_CRITICAL
        if
        :: SELE2(_id, xTicksToWait == 0);
            taskEXIT_CRITICAL(_id, temp_var);
            AWAIT_A(_id, assert(!xIsTimeOut && xReturn == false); break)
        :: ELSE2(_id, xTicksToWait == 0)
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
    :: SELE2(_id, xIsTimeOut == false);
        /* The timeout has not expired. */
        if
        :: SELE2(_id, prvIsQueueEmpty(pxQueue));
            vTaskPlaceOnEventList(_id, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive, xTicksToWait, temp_var);
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);

            xTaskResumeAll(_id, temp_var, xReturn, temp_var2);
            if
            :: SELE3(_id, xReturn == false, xIsTimeOut = true);
                portYIELD_WITHIN_API(_id, temp_var)
            :: ELSE3(_id, xReturn == false, xReturn = false)
            fi
        :: ELSE2(_id, prvIsQueueEmpty(pxQueue));
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
            xTaskResumeAll(_id, temp_var, _, temp_var2)
        fi
    :: ELSE2(_id, xIsTimeOut == false);
        /* Timed out. */
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
        xTaskResumeAll(_id, temp_var, _, temp_var2);

        if
        :: SELE2(_id, prvIsQueueEmpty(pxQueue));
            AWAIT_A(_id, xIsTimeOut = false; assert(xReturn == false); break)
        :: ELSE2(_id, prvIsQueueEmpty(pxQueue))
        fi
    fi;
#else /* QUEUE_RECEIVE_EXIT_CRITICAL */
    assert(false)
#endif /* QUEUE_RECEIVE_EXIT_CRITICAL */
od
}

#define uxSemaphoreCount            temp_var2
#define uxHighestWaitingPriority    temp_var

inline xQueueSemaphoreTake(pxQueue, xTicksToWait, xReturn, xInheritanceOccurred, xIsTimeOut, temp_var, temp_var2, _id)
{
    AWAIT_D(_id, xReturn = false;
        assert((!xInheritanceOccurred & !xIsTimeOut) && ((temp_var & temp_var2) == NULL_byte) &&
            queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)));
do
::  taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, uxSemaphoreCount = pxQueue.uxMessagesWaiting);
    if
    :: SELE2(_id, uxSemaphoreCount > 0);
        AWAIT_D(_id, pxQueue.uxMessagesWaiting = uxSemaphoreCount - 1; uxSemaphoreCount = NULL_byte);

        #if (configUSE_MUTEXES == 1)
        if
        :: SELE2(_id, queueQUEUE_IS_MUTEX(pxQueue));
            pvTaskIncrementMutexHeldCount(_id, pxQueue.xSemaphore.xMutexHolder)
        :: ELSE2(_id, queueQUEUE_IS_MUTEX(pxQueue))
        fi;
        #endif

        if
        :: SELE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]));
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], xReturn);
            if
            :: SELE3(_id, xReturn != false, xReturn = false);
                queueYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: ELSE2(_id, xReturn != false)
            fi
        :: ELSE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]))
        fi;

        taskEXIT_CRITICAL(_id, temp_var);
        AWAIT_A(_id, xIsTimeOut = false; xReturn = true; break)
    :: ELSE3(_id, uxSemaphoreCount > 0, uxSemaphoreCount = NULL_byte);
#ifdef QUEUE_TAKE_EXIT_CRITICAL
        if
        :: SELE2(_id, xTicksToWait == 0);
            #if (configUSE_MUTEXES == 1)
            AWAIT_D(_id, assert(xInheritanceOccurred == false));
            #endif
            taskEXIT_CRITICAL(_id, temp_var);
            AWAIT_A(_id, assert(!xIsTimeOut && xReturn == false); break)
        :: ELSE2(_id, xTicksToWait == 0)
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
    :: SELE2(_id, xIsTimeOut == false);
        if
        :: SELE2(_id, prvIsQueueEmpty(pxQueue) != false);
            #if (configUSE_MUTEXES == 1)
            if
            :: SELE2(_id, queueQUEUE_IS_MUTEX(pxQueue));
                taskENTER_CRITICAL(_id, temp_var);
                xTaskPriorityInherit(_id, pxQueue.xSemaphore.xMutexHolder, xInheritanceOccurred, temp_var);
                taskEXIT_CRITICAL(_id, temp_var)
            :: ELSE2(_id, queueQUEUE_IS_MUTEX(pxQueue))
            fi;
            #endif

            vTaskPlaceOnEventList(_id, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive, xTicksToWait, temp_var);
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);

            xTaskResumeAll(_id, temp_var, xReturn, temp_var2);
            if
            :: SELE3(_id, xReturn == false, xIsTimeOut = true);
                portYIELD_WITHIN_API(_id, temp_var)
            :: ELSE3(_id, xReturn == false, xReturn = false)
            fi
        :: ELSE2(_id, prvIsQueueEmpty(pxQueue) != false);
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
            xTaskResumeAll(_id, temp_var, _, temp_var2)
        fi
    :: ELSE2(_id, xIsTimeOut == false);
        /* Timed out. */
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, xReturn);
        xTaskResumeAll(_id, temp_var, _, temp_var2);

        if
        :: SELE2(_id, prvIsQueueEmpty(pxQueue));
            #if (configUSE_MUTEXES == 1)
            if
            :: SELE3(_id, xInheritanceOccurred != false, xInheritanceOccurred = false);
                taskENTER_CRITICAL(_id, temp_var);
                prvGetDisinheritPriorityAfterTimeout(_id, pxQueue, uxHighestWaitingPriority);
                vTaskPriorityDisinheritAfterTimeout(_id, pxQueue.xSemaphore.xMutexHolder, uxHighestWaitingPriority, temp_var2);

                taskEXIT_CRITICAL(_id, temp_var)
            :: ELSE2(_id, xInheritanceOccurred != false)
            fi;
            #endif

            AWAIT_A(_id, xIsTimeOut = false; assert(xReturn == false); break)
        :: ELSE2(_id, prvIsQueueEmpty(pxQueue))
        fi
    fi;
#else /* QUEUE_TAKE_EXIT_CRITICAL */
    assert(false);
#endif /* QUEUE_TAKE_EXIT_CRITICAL */
od
}

#define uxQueueMessagesWaiting(xQueue) xQueue.uxMessagesWaiting

#if (configUSE_MUTEXES == 1)

inline prvGetDisinheritPriorityAfterTimeout(_id, pxQueue, uxHighestPriorityOfWaitingTasks)
{
    if
    :: SELE2(_id, listLENGTH_IS_EXCEEDING_0(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
        AWAIT_D(_id, assert(uxHighestPriorityOfWaitingTasks == false);
            uxHighestPriorityOfWaitingTasks = configMAX_PRIORITIES - listGET_ITEM_VALUE_OF_HEAD_ENTRY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]))
    :: ELSE2(_id, listLENGTH_IS_EXCEEDING_0(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
        AWAIT_D(_id, assert(uxHighestPriorityOfWaitingTasks == false);
            uxHighestPriorityOfWaitingTasks = tskIDLE_PRIORITY)
    fi
}

#endif /* configUSE_MUTEXES */

inline prvCopyDataToQueue(_id, pxQueue, pvItemToQueue, xPosition, xReturn, temp_var, uMessagesWaiting)
{
    AWAIT_D(_id, assert(xReturn == false); uMessagesWaiting = pxQueue.uxMessagesWaiting);
    if
    :: SELE2(_id, queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue));
        #if (configUSE_MUTEXES == 1)
        if
        :: SELE2(_id, queueQUEUE_IS_MUTEX(pxQueue));
            /* The mutex is no longer being held. */
            xTaskPriorityDisinherit(_id, pxQueue.xSemaphore.xMutexHolder, xReturn, temp_var);
            AWAIT_D(_id, pxQueue.xSemaphore.xMutexHolder = NULL_byte)
        :: ELSE2(_id, queueQUEUE_IS_MUTEX(pxQueue))
        fi
        #endif
    :: ELSE2(_id, queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue));
        if
        :: SELE2(_id, xPosition == queueSEND_TO_BACK);
            AWAIT_D(_id, pxQueue.xQueue.pucQueueStorage(queueGET_pcWriteTo(pxQueue)) = pvItemToQueue);
            AWAIT_D(_id, queueSET_pcWriteTo(pxQueue, queueGET_pcWriteTo(pxQueue) + 1));
            if
            :: SELE2(_id, queueGET_pcWriteTo(pxQueue) >= pxQueue.uxLength);
                AWAIT_D(_id, queueSET_pcWriteTo(pxQueue, 0))
            :: ELSE2(_id, queueGET_pcWriteTo(pxQueue) >= pxQueue.uxLength)
            fi
        :: ELSE2(_id, xPosition == queueSEND_TO_BACK);
            AWAIT_D(_id, pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)) = pvItemToQueue);
            if
            :: SELE2(_id, queueGET_pcReadFrom(pxQueue) == 0);
                AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, pxQueue.uxLength - 1))
            :: ELSE2(_id, queueGET_pcReadFrom(pxQueue) == 0);
                AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, queueGET_pcReadFrom(pxQueue) - 1))
            fi;

            if
            :: SELE2(_id, xPosition == queueOVERWRITE && uMessagesWaiting > 0);
                AWAIT_D(_id, uMessagesWaiting = uMessagesWaiting - 1)
            :: ELSE2(_id, xPosition == queueOVERWRITE && uMessagesWaiting > 0)
            fi
        fi
    fi;

    AWAIT_D(_id, pxQueue.uxMessagesWaiting = uMessagesWaiting + 1; uMessagesWaiting = NULL_byte)
}

inline prvCopyDataFromQueue(_id, pxQueue, pvBuffer)
{
    if
    :: SELE2(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue));
        AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, queueGET_pcReadFrom(pxQueue) + 1));
        if
        :: SELE2(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength);
            AWAIT_D(_id, queueSET_pcReadFrom(pxQueue, 0))
        :: ELSE2(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength)
        fi;

        AWAIT_D(_id, pvBuffer = pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue));
            /* reset data in queue as soon as possible */
            pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)) = NULL_byte);
    :: ELSE2(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue))
    fi
}

#define cTxLock temp_var2
#define cRxLock temp_var2

inline prvUnlockQueue(_id, pxQueue, temp_var, temp_var2, temp_xReturn)
{
    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, assert(cTxLock == NULL_byte); cTxLock = queueGET_cTxLock(pxQueue));
    do
    :: SELE2(_id, cTxLock > queueLOCKED_UNMODIFIED);
        #if (configUSE_QUEUE_SETS == 1)
        // TODO
        #else /* configUSE_QUEUE_SETS */
        if
        :: SELE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], temp_xReturn);
            if
            :: SELE3(_id, temp_xReturn != false, temp_xReturn = false);
                vTaskMissedYield(_id)
            :: ELSE2(_id, temp_xReturn != false)
            fi
        :: ELSE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
            AWAIT_A(_id, cTxLock = NULL_byte; break)
        fi;
        #endif /* configUSE_QUEUE_SETS */

        AWAIT_D(_id, cTxLock = cTxLock - 1)
    :: ELSE3(_id, cTxLock > queueLOCKED_UNMODIFIED, cTxLock = NULL_byte; break)
    od;
    AWAIT_A(_id, queueSET_cTxLock(pxQueue, queueUNLOCKED));
    taskEXIT_CRITICAL(_id, temp_var);

    /* Do the same for the Rx lock. */
    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, assert(cRxLock == NULL_byte); cRxLock = queueGET_cRxLock(pxQueue));
    do
    :: SELE2(_id, cRxLock > queueLOCKED_UNMODIFIED);
        if
        :: SELE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]));
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], temp_xReturn);
            if
            :: SELE3(_id, temp_xReturn != false, temp_xReturn = false);
                vTaskMissedYield(_id)
            :: ELSE2(_id, temp_xReturn != false)
            fi;

            AWAIT_D(_id, cRxLock = cRxLock - 1)
        :: ELSE2(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]));
            AWAIT_A(_id, cRxLock = NULL_byte; break)
        fi;
    :: ELSE3(_id, cRxLock > queueLOCKED_UNMODIFIED, cRxLock = NULL_byte; break)
    od;
    AWAIT_A(_id, queueSET_cRxLock(pxQueue, queueUNLOCKED));
    taskEXIT_CRITICAL(_id, temp_var)
}

#endif

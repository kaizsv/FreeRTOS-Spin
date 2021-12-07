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

#define queueSEMAPHORE_QUEUE_ITEM_LENGTH    0
#define queueMUTEX_GIVE_BLOCK_TIME          0

#if (configUSE_PREEMPTION == 0)
    #define queueYIELD_IF_USING_PREEMPTION(_id)
#else
    #define queueYIELD_IF_USING_PREEMPTION(_id) portYIELD_WITHIN_API(_id)
#endif

#include "include/Queue_Declarator.pml"

#define queueQUEUE_IS_MUTEX(pxQueue) \
    (queueGET_uxQueueType(pxQueue) == queueQUEUE_TYPE_MUTEX || queueGET_uxQueueType(pxQueue) == queueQUEUE_TYPE_RECURSIVE_MUTEX)
/* If the item size of a Queue is zero, then the queue is not the base type. */
#define queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue) (queueGET_uxQueueType(pxQueue) > queueQUEUE_TYPE_BASE)

#define prvIsQueueEmpty(pxQueue)    (pxQueue.uxMessagesWaiting == 0)
#define prvIsQueueFull(pxQueue)     (pxQueue.uxMessagesWaiting == pxQueue.uxLength)

inline prvLockQueue(_id, pxQueue)
{
    taskENTER_CRITICAL(_id);
    if
    :: SELE_AS(_id, queueGET_cRxLock(pxQueue) == queueUNLOCKED);
        AWAIT_DS(_id, queueSET_cRxLock(pxQueue, queueLOCKED_UNMODIFIED))
    :: ELSE_AS(_id, queueGET_cRxLock(pxQueue) == queueUNLOCKED)
    fi;
    if
    :: SELE_AS(_id, queueGET_cTxLock(pxQueue) == queueUNLOCKED);
        AWAIT_DS(_id, queueSET_cTxLock(pxQueue, queueLOCKED_UNMODIFIED))
    :: ELSE_AS(_id, queueGET_cTxLock(pxQueue) == queueUNLOCKED)
    fi;
    taskEXIT_CRITICAL(_id)
}

inline xQueueGenericReset(_id, pxQueue, temp_var)
{
    taskENTER_CRITICAL(_id);
    AWAIT_DS(_id,
        assert(pxQueue.uxLength != 0); // The queue is already declared.
        pxQueue.uxMessagesWaiting = 0;
        queueSET_pcWriteTo(pxQueue, 0);
        queueSET_pcReadFrom(pxQueue, pxQueue.uxLength - 1);
        queueSET_cRxLock(pxQueue, queueUNLOCKED);
        queueSET_cTxLock(pxQueue, queueUNLOCKED);
    );
    if
    :: SELE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]) == false);
        xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]);
        if
        :: SELE_AS(_id, temp_var != false, temp_var = NULL_byte);
            queueYIELD_IF_USING_PREEMPTION(_id)
        :: ELSE_AS(_id, temp_var != false, temp_var = NULL_byte);
        fi
    :: ELSE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]) == false);
    fi;
    taskEXIT_CRITICAL(_id);
}

inline xQueueGenericCreate_fixed(pxNewQueue, QueueID, uxQueueLength, ucQueueType)
{
    assert(QueueID < promela_QUEUE_NUMBER && 0 < uxQueueLength);

    /* Initialize Queue Storage */
    if
    :: ucQueueType == queueQUEUE_TYPE_BASE ->
        for (hidden_idx: 0 .. (uxQueueLength - 1)) {
            pxNewQueue.u.multi_bytes[hidden_idx] = NULL_byte
        }
        hidden_idx = NULL_byte;
    :: else ->
        pxNewQueue.u.multi_bytes[0] = NULL_byte
    fi;

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

inline prvInitialiseMutex(pxNewQueue, temp_xIsTimeOut, temp_var, temp_var2, _id)
{
    xQueueGenericSend_NB(pxNewQueue, NULL_byte, 0, queueSEND_TO_BACK, _, temp_xIsTimeOut, temp_var, temp_var2, _id)
}

inline xQueueCreateMutex(ucQueueType, pxNewQueue, QueueID, temp_xIsTimeOut, temp_var, temp_var2, _id)
{
    d_step {
        xQueueGenericCreate_fixed(pxNewQueue, QueueID, 1, ucQueueType);

        /* prvInitialiseMutex */
        pxNewQueue.xSemaphore.xMutexHolder = NULL_byte;
        pxNewQueue.xSemaphore.uxRecursiveCallCount = 0;
        assert(queueQUEUE_IS_MUTEX(pxNewQueue));
    };
    prvInitialiseMutex(pxNewQueue, temp_xIsTimeOut, temp_var, temp_var2, _id)
}

#endif /* configUSE_MUTEXES */

#if (configUSE_RECURSIVE_MUTEXES == 1)

inline xQueueGiveMutexRecursive(_id, pxMutex, xReturn, xIsTimeOut, temp_var, temp_var2)
{
    if
    :: SELE(_id, pxMutex.xSemaphore.xMutexHolder == pxCurrentTCB, assert(xReturn == false); xReturn = true);
        AWAIT(_id, pxMutex.xSemaphore.uxRecursiveCallCount = pxMutex.xSemaphore.uxRecursiveCallCount - 1);

        if
        :: SELE(_id, pxMutex.xSemaphore.uxRecursiveCallCount == 0);
            xQueueGenericSend_NB(pxMutex, NULL_byte, queueMUTEX_GIVE_BLOCK_TIME, queueSEND_TO_BACK, _, xIsTimeOut, temp_var, temp_var2, _id)
        :: ELSE(_id, pxMutex.xSemaphore.uxRecursiveCallCount == 0);
        fi
    :: ELSE(_id, pxMutex.xSemaphore.xMutexHolder == pxCurrentTCB, assert(xReturn == false))
    fi
}

inline xQueueTakeMutexRecursive(_id, pxMutex, xTicksToWait, xReturn, xInheritanceOccurred, xIsTimeOut, temp_var, temp_var2)
{
    if
    :: SELE(_id, pxMutex.xSemaphore.xMutexHolder == pxCurrentTCB, assert(xReturn == false); xReturn = true);
        AWAIT(_id, pxMutex.xSemaphore.uxRecursiveCallCount = pxMutex.xSemaphore.uxRecursiveCallCount + 1)
    :: ELSE(_id, pxMutex.xSemaphore.xMutexHolder == pxCurrentTCB, assert(xReturn == false));
        xQueueSemaphoreTake(pxMutex, xTicksToWait, xReturn, xInheritanceOccurred, xIsTimeOut, temp_var, temp_var2, _id);
        if
        :: SELE(_id, xReturn != false);
            AWAIT(_id, pxMutex.xSemaphore.uxRecursiveCallCount = pxMutex.xSemaphore.uxRecursiveCallCount + 1)
        :: ELSE(_id, xReturn != false)
        fi
    fi
}

#endif

#if (configUSE_COUNTING_SEMAPHORES == 1)

inline xQueueCreateCountingSemaphore_fixed(xHandle, xHandleQueueID, uxMaxCount, uxInitialCount)
{
    xQueueGenericCreate_fixed(xHandle, xHandleQueueID, uxMaxCount, queueQUEUE_TYPE_COUNTING_SEMAPHORE);
    xHandle.uxMessagesWaiting = uxInitialCount
}

#endif

#if (configUSE_QUEUE_SETS == 1)
    #error Define another __xQueueGenericSend_BODY
#endif

// xYieldRequired does not conflict with temp_var
#define alias_xYieldRequired temp_var

#define __xQueueGenericSend_BODY(__BH) \
    AWAIT(_id, xReturn = 0; \
        assert((!xIsTimeOut) && ((temp_var & temp_var2) == NULL_byte) && \
            (!((pvItemToQueue == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)))) && \
            (!((xCopyPosition == queueOVERWRITE) && (pxQueue.uxLength != 1))))); \
do \
::  taskENTER_CRITICAL(_id); \
    if \
    :: SELE_AS(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE); \
        prvCopyDataToQueue(_id, pxQueue, pvItemToQueue, xCopyPosition, alias_xYieldRequired, temp_var2); \
        /* TODO: instruction reordering? */ \
        if \
        :: SELE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]), temp_var = NULL_byte); \
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]); \
            if \
            :: SELE_AS(_id, temp_var != false, temp_var = NULL_byte; temp_var = NULL_byte); \
                queueYIELD_IF_USING_PREEMPTION(_id); \
            :: ELSE_AS(_id, temp_var != false, temp_var = NULL_byte; temp_var = NULL_byte) \
            fi \
        :: ELSE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])); \
            if \
            :: SELE_AS(_id, alias_xYieldRequired != false, alias_xYieldRequired = NULL_byte); \
                queueYIELD_IF_USING_PREEMPTION(_id) \
            :: ELSE_AS(_id, alias_xYieldRequired != false, alias_xYieldRequired = NULL_byte) \
            fi \
        fi; \
        taskEXIT_CRITICAL(_id); \
        AWAIT(_id, xIsTimeOut = false; xReturn = true; break) \
    :: ELSE_AS(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE); \
        if \
        :: SELE_AS(_id, xTicksToWait == 0); \
            taskEXIT_CRITICAL(_id); \
            AWAIT(_id, assert(!xIsTimeOut); xReturn = false; break) \
        :: ELSE_AS(_id, xTicksToWait == 0) \
        fi \
    fi; \
    __BH \
od

#define __xQueueGenericSend_BH \
    taskEXIT_CRITICAL(_id); \
    vTaskSuspendAll(_id); \
    prvLockQueue(_id, pxQueue); \
    if \
    :: SELE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait)); \
        if \
        :: SELE(_id, prvIsQueueFull(pxQueue), xIsTimeOut = true); \
            vTaskPlaceOnEventList(_id, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], queueGET_ListIndex(pxQueue) + xTasksWaitingToSend, xTicksToWait); \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, xReturn); \
            if \
            :: SELE(_id, xReturn == false); \
                portYIELD_WITHIN_API(_id) \
            :: ELSE(_id, xReturn == false, xReturn = false) \
            fi \
        :: ELSE(_id, prvIsQueueFull(pxQueue)); \
            /* Try again. */ \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, _) \
        fi \
    :: ELSE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait), xIsTimeOut = false); \
        /* The timeout has expired. */ \
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
        xTaskResumeAll(_id, temp_var, _); \
        AWAIT(_id, xReturn = false; break) \
    fi;

/* Simply for 0 xTicksToWait by removing the bottom half statements */
inline xQueueGenericSend_NB(pxQueue, pvItemToQueue, xTicksToWait, xCopyPosition, xReturn, xIsTimeOut, temp_var, temp_var2, _id)
{
    __xQueueGenericSend_BODY(assert(false))
}

inline xQueueGenericSend(pxQueue, pvItemToQueue, xTicksToWait, xCopyPosition, xReturn, xIsTimeOut, temp_var, temp_var2, _id)
{
    __xQueueGenericSend_BODY(__xQueueGenericSend_BH)
}

#define __xQueueReceive_BODY(__BH) \
    AWAIT(_id, xReturn = false; \
        assert((!xIsTimeOut) && ((temp_var & temp_var2) == NULL_byte) && \
            (!((pvBuffer == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)))))); \
do \
::  taskENTER_CRITICAL(_id); \
    AWAIT_DS(_id, temp_var2 = pxQueue.uxMessagesWaiting); \
    if \
    :: SELE_AS(_id, temp_var2 > 0); \
        prvCopyDataFromQueue(_id, pxQueue, pvBuffer); \
        AWAIT_DS(_id, pxQueue.uxMessagesWaiting = temp_var2 - 1; temp_var2 = NULL_byte); \
        if \
        :: SELE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])); \
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]); \
            if \
            :: SELE_AS(_id, temp_var != false, temp_var = NULL_byte); \
                queueYIELD_IF_USING_PREEMPTION(_id) \
            :: ELSE_AS(_id, temp_var != false, temp_var = NULL_byte) \
            fi \
        :: ELSE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])) \
        fi; \
        taskEXIT_CRITICAL(_id); \
        AWAIT(_id, xIsTimeOut = false; xReturn = true; break) \
    :: ELSE_AS(_id, temp_var2 > 0, temp_var2 = NULL_byte); \
        if \
        :: SELE_AS(_id, xTicksToWait == 0); \
            taskEXIT_CRITICAL(_id); \
            AWAIT(_id, assert(!xIsTimeOut && xReturn == false); break) \
        :: ELSE_AS(_id, xTicksToWait == 0) \
        fi \
    fi; \
    __BH \
od

#define __xQueueReceive_BH \
    taskEXIT_CRITICAL(_id); \
    vTaskSuspendAll(_id); \
    prvLockQueue(_id, pxQueue); \
    if \
    :: SELE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait)); \
        /* The timeout has not expired. */ \
        if \
        :: SELE(_id, prvIsQueueEmpty(pxQueue), xIsTimeOut = true); \
            vTaskPlaceOnEventList(_id, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive, xTicksToWait); \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, xReturn); \
            if \
            :: SELE(_id, xReturn == false); \
                portYIELD_WITHIN_API(_id) \
            :: ELSE(_id, xReturn == false, xReturn = false) \
            fi \
        :: ELSE(_id, prvIsQueueEmpty(pxQueue)); \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, _) \
        fi \
    :: ELSE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait)); \
        /* Timed out. */ \
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
        xTaskResumeAll(_id, temp_var, _); \
        if \
        :: SELE(_id, prvIsQueueEmpty(pxQueue)); \
            AWAIT(_id, xIsTimeOut = false; assert(xReturn == false); break) \
        :: ELSE(_id, prvIsQueueEmpty(pxQueue)) \
        fi \
    fi;

/* Simply for 0 xTicksToWait by removing the bottom half statements */
inline xQueueReceive_NB(pxQueue, pvBuffer, xTicksToWait, xReturn, xIsTimeOut, temp_var, temp_var2, _id)
{
    __xQueueReceive_BODY(assert(false))
}

inline xQueueReceive(pxQueue, pvBuffer, xTicksToWait, xReturn, xIsTimeOut, temp_var, temp_var2, _id)
{
    __xQueueReceive_BODY(__xQueueReceive_BH)
}

#define pcOriginalReadPosition  temp_var2

#define __xQueuePeek_BODY(__BH) \
    AWAIT(_id, assert((!xReturn & !xIsTimeOut) && ((temp_var & temp_var2) == NULL_byte) && \
        (!((pvBuffer == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)))))); \
do \
::  taskENTER_CRITICAL(_id); \
    if \
    :: SELE_AS(_id, pxQueue.uxMessagesWaiting > 0); \
        AWAIT_DS(_id, pcOriginalReadPosition = queueGET_pcReadFrom(pxQueue)); \
        prvCopyDataFromQueue_NO_RESET_QUEUE(_id, pxQueue, pvBuffer); \
        AWAIT_DS(_id, queueSET_pcReadFrom(pxQueue, pcOriginalReadPosition); pcOriginalReadPosition = NULL_byte); \
        if \
        :: SELE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])); \
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]); \
            if \
            :: SELE_AS(_id, temp_var != false, temp_var = NULL_byte); \
                queueYIELD_IF_USING_PREEMPTION(_id) \
            :: ELSE_AS(_id, temp_var != false, temp_var = NULL_byte) \
            fi \
        :: ELSE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive])) \
        fi; \
        taskEXIT_CRITICAL(_id); \
        AWAIT(_id, xIsTimeOut = false; xReturn = true; break) \
    :: ELSE_AS(_id, pxQueue.uxMessagesWaiting > 0); \
        if \
        :: SELE_AS(_id, xTicksToWait == 0); \
            taskEXIT_CRITICAL(_id); \
            AWAIT(_id, assert(!xIsTimeOut && xReturn == false); break) \
        :: ELSE_AS(_id, xTicksToWait == 0) \
        fi \
    fi; \
    __BH \
od

#define __xQueuePeek_BH(__AGAIN_AFTER_TIMED_OUT) \
    taskEXIT_CRITICAL(_id); \
    vTaskSuspendAll(_id); \
    prvLockQueue(_id, pxQueue); \
    if \
    :: SELE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait)); \
        if \
        :: SELE(_id, prvIsQueueEmpty(pxQueue) != false, xIsTimeOut = true); \
            vTaskPlaceOnEventList(_id, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive, xTicksToWait); \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, xReturn); \
            if \
            :: SELE(_id, xReturn == false); \
                portYIELD_WITHIN_API(_id) \
            :: ELSE(_id, xReturn == false, xReturn = false) \
            fi \
        :: ELSE(_id, prvIsQueueEmpty(pxQueue) != false); \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, _) \
        fi \
    :: ELSE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait)); \
        __AGAIN_AFTER_TIMED_OUT \
    fi

#define __xQueuePeek_AGAIN_AFTER_TIMED_OUT \
   prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
   xTaskResumeAll(_id, temp_var, _); \
   if \
   :: SELE(_id, prvIsQueueEmpty(pxQueue), xIsTimeOut = false; assert(!xReturn); break) \
   :: ELSE(_id, prvIsQueueEmpty(pxQueue)) \
   fi

/* Simply for 0 xTicksToWait by removing the bottom half statements */
inline xQueuePeek_NB(_id, pxQueue, pvBuffer, xTicksToWait, xReturn, xIsTimeOut, temp_var, temp_var2)
{
    __xQueuePeek_BODY(assert(false))
}

/* Simply for portMAX_DELAY xTicksToWait by removing the statements after timed out */
inline xQueuePeek_PR(_id, pxQueue, pvBuffer, xTicksToWait, xReturn, xIsTimeOut, temp_var, temp_var2)
{
    __xQueuePeek_BODY(__xQueuePeek_BH(assert(false)))
}

inline xQueuePeek(_id, pxQueue, pvBuffer, xTicksToWait, xReturn, xIsTimeOut, temp_var, temp_var2)
{
    __xQueuePeek_BODY(__xQueuePeek_BH(__xQueuePeek_AGAIN_AFTER_TIMED_OUT))
}

#if (configUSE_MUTEXES == 0)
    #error Define another __xQueueSemaphoreTake__BODY and __xQueueSemaphoreTake_BH
#endif

#define uxSemaphoreCount            temp_var2
#define uxHighestWaitingPriority    temp_var

#define __xQueueSemaphoreTake__BODY(__BH) \
    AWAIT(_id, xReturn = false; \
        assert((!xInheritanceOccurred & !xIsTimeOut) && ((temp_var & temp_var2) == NULL_byte) && \
            queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue))); \
do \
::  taskENTER_CRITICAL(_id); \
    AWAIT_DS(_id, uxSemaphoreCount = pxQueue.uxMessagesWaiting); \
    if \
    :: SELE_AS(_id, uxSemaphoreCount > 0); \
        AWAIT_DS(_id, pxQueue.uxMessagesWaiting = uxSemaphoreCount - 1; uxSemaphoreCount = NULL_byte); \
        if \
        :: SELE_AS(_id, queueQUEUE_IS_MUTEX(pxQueue)); \
            pvTaskIncrementMutexHeldCount(_id, pxQueue.xSemaphore.xMutexHolder) \
        :: ELSE_AS(_id, queueQUEUE_IS_MUTEX(pxQueue)) \
        fi; \
        if \
        :: SELE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])); \
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]); \
            if \
            :: SELE_AS(_id, temp_var != false, temp_var = NULL_byte); \
                queueYIELD_IF_USING_PREEMPTION(_id) \
            :: ELSE_AS(_id, temp_var != false, temp_var = NULL_byte) \
            fi \
        :: ELSE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend])) \
        fi; \
        taskEXIT_CRITICAL(_id); \
        AWAIT(_id, xIsTimeOut = false; xInheritanceOccurred = false; xReturn = true; break) \
    :: ELSE_AS(_id, uxSemaphoreCount > 0, uxSemaphoreCount = NULL_byte); \
        if \
        :: SELE_AS(_id, xTicksToWait == 0); \
            taskEXIT_CRITICAL(_id); \
            AWAIT(_id, assert(!xInheritanceOccurred && !xIsTimeOut && xReturn == false); break) \
        :: ELSE_AS(_id, xTicksToWait == 0) \
        fi \
    fi; \
    __BH \
od

#define __xQueueSemaphoreTake_BH \
    taskEXIT_CRITICAL(_id); \
    vTaskSuspendAll(_id); \
    prvLockQueue(_id, pxQueue); \
    if \
    :: SELE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait)); \
        if \
        :: SELE(_id, prvIsQueueEmpty(pxQueue) != false, xIsTimeOut = true); \
            if \
            :: SELE(_id, queueQUEUE_IS_MUTEX(pxQueue)); \
                taskENTER_CRITICAL(_id); \
                xTaskPriorityInherit(_id, pxQueue.xSemaphore.xMutexHolder, xInheritanceOccurred); \
                taskEXIT_CRITICAL(_id) \
            :: ELSE(_id, queueQUEUE_IS_MUTEX(pxQueue)) \
            fi; \
            vTaskPlaceOnEventList(_id, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive, xTicksToWait); \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, xReturn); \
            if \
            :: SELE(_id, xReturn == false); \
                portYIELD_WITHIN_API(_id) \
            :: ELSE(_id, xReturn == false, xReturn = false) \
            fi \
        :: ELSE(_id, prvIsQueueEmpty(pxQueue) != false); \
            prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
            xTaskResumeAll(_id, temp_var, _) \
        fi \
    :: ELSE(_id, xTaskCheckForTimeOut(xIsTimeOut, xTicksToWait)); \
        /* Timed out. */ \
        prvUnlockQueue(_id, pxQueue, temp_var, temp_var2); \
        xTaskResumeAll(_id, temp_var, _); \
        if \
        :: SELE(_id, prvIsQueueEmpty(pxQueue)); \
            if \
            :: SELE(_id, xInheritanceOccurred != false, xInheritanceOccurred = false); \
                taskENTER_CRITICAL(_id); \
                prvGetDisinheritPriorityAfterTimeout(_id, pxQueue, uxHighestWaitingPriority); \
                vTaskPriorityDisinheritAfterTimeout(_id, pxQueue.xSemaphore.xMutexHolder, uxHighestWaitingPriority, temp_var2); \
                taskEXIT_CRITICAL(_id) \
            :: ELSE(_id, xInheritanceOccurred != false) \
            fi; \
            AWAIT(_id, xIsTimeOut = false; assert(xReturn == false); break) \
        :: ELSE(_id, prvIsQueueEmpty(pxQueue)) \
        fi \
    fi;

/* Simply for 0 xTicksToWait by removing the bottom half statements */
inline xQueueSemaphoreTake_NB(pxQueue, xTicksToWait, xReturn, xInheritanceOccurred, xIsTimeOut, temp_var, temp_var2, _id)
{
    __xQueueSemaphoreTake__BODY(assert(false))
}

inline xQueueSemaphoreTake(pxQueue, xTicksToWait, xReturn, xInheritanceOccurred, xIsTimeOut, temp_var, temp_var2, _id)
{
    __xQueueSemaphoreTake__BODY(__xQueueSemaphoreTake_BH)
}

#define uxQueueMessagesWaiting(xQueue) xQueue.uxMessagesWaiting

#if (configUSE_MUTEXES == 1)

inline prvGetDisinheritPriorityAfterTimeout(_id, pxQueue, uxHighestPriorityOfWaitingTasks)
{
    if
    :: SELE_AS(_id, listLENGTH_IS_EXCEEDING_0(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
        AWAIT_DS(_id, assert(uxHighestPriorityOfWaitingTasks == NULL_byte);
            uxHighestPriorityOfWaitingTasks = configMAX_PRIORITIES - listGET_ITEM_VALUE_OF_HEAD_ENTRY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]))
    :: ELSE_AS(_id, listLENGTH_IS_EXCEEDING_0(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
        AWAIT_DS(_id, assert(uxHighestPriorityOfWaitingTasks == NULL_byte);
            uxHighestPriorityOfWaitingTasks = tskIDLE_PRIORITY)
    fi
}

#endif /* configUSE_MUTEXES */

inline prvCopyDataToQueue(_id, pxQueue, pvItemToQueue, xPosition, xReturn, uMessagesWaiting)
{
    AWAIT_DS(_id, xReturn = false; uMessagesWaiting = pxQueue.uxMessagesWaiting);
    if
    :: SELE_AS(_id, queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue));
        #if (configUSE_MUTEXES == 1)
        if
        :: SELE_AS(_id, queueQUEUE_IS_MUTEX(pxQueue));
            /* The mutex is no longer being held. */
            xTaskPriorityDisinherit(_id, pxQueue.xSemaphore.xMutexHolder, xReturn);
            AWAIT_DS(_id, pxQueue.xSemaphore.xMutexHolder = NULL_byte)
        :: ELSE_AS(_id, queueQUEUE_IS_MUTEX(pxQueue))
        fi
        #endif
    :: ELSE_AS(_id, queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue));
        if
        :: SELE_AS(_id, xPosition == queueSEND_TO_BACK);
            AWAIT_DS(_id, pxQueue.xQueue.pucQueueStorage(queueGET_pcWriteTo(pxQueue)) = pvItemToQueue);
            AWAIT_DS(_id, queueSET_pcWriteTo(pxQueue, queueGET_pcWriteTo(pxQueue) + 1));
            if
            :: SELE_AS(_id, queueGET_pcWriteTo(pxQueue) >= pxQueue.uxLength);
                AWAIT_DS(_id, queueSET_pcWriteTo(pxQueue, 0))
            :: ELSE_AS(_id, queueGET_pcWriteTo(pxQueue) >= pxQueue.uxLength)
            fi
        :: ELSE_AS(_id, xPosition == queueSEND_TO_BACK);
            AWAIT_DS(_id, pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)) = pvItemToQueue);
            if
            :: SELE_AS(_id, queueGET_pcReadFrom(pxQueue) == 0);
                AWAIT_DS(_id, queueSET_pcReadFrom(pxQueue, pxQueue.uxLength - 1))
            :: ELSE_AS(_id, queueGET_pcReadFrom(pxQueue) == 0);
                AWAIT_DS(_id, queueSET_pcReadFrom(pxQueue, queueGET_pcReadFrom(pxQueue) - 1))
            fi;

            if
            :: SELE_AS(_id, xPosition == queueOVERWRITE && uMessagesWaiting > 0);
                AWAIT_DS(_id, uMessagesWaiting = uMessagesWaiting - 1)
            :: ELSE_AS(_id, xPosition == queueOVERWRITE && uMessagesWaiting > 0)
            fi
        fi
    fi;

    AWAIT_DS(_id, pxQueue.uxMessagesWaiting = uMessagesWaiting + 1; uMessagesWaiting = NULL_byte)
}

inline prvCopyDataFromQueue(_id, pxQueue, pvBuffer)
{
    if
    :: SELE_AS(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue));
        AWAIT_DS(_id, queueSET_pcReadFrom(pxQueue, queueGET_pcReadFrom(pxQueue) + 1));
        if
        :: SELE_AS(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength);
            AWAIT_DS(_id, queueSET_pcReadFrom(pxQueue, 0))
        :: ELSE_AS(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength)
        fi;

        AWAIT_DS(_id, pvBuffer = pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue));
            /* reset data in queue as soon as possible */
            pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)) = NULL_byte);
    :: ELSE_AS(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue))
    fi
}

/* For xQueuePeek only */
inline prvCopyDataFromQueue_NO_RESET_QUEUE(_id, pxQueue, pvBuffer)
{
    if
    :: SELE_AS(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue));
        AWAIT_DS(_id, queueSET_pcReadFrom(pxQueue, queueGET_pcReadFrom(pxQueue) + 1));
        if
        :: SELE_AS(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength);
            AWAIT_DS(_id, queueSET_pcReadFrom(pxQueue, 0))
        :: ELSE_AS(_id, queueGET_pcReadFrom(pxQueue) >= pxQueue.uxLength)
        fi;

        AWAIT_DS(_id, pvBuffer = pxQueue.xQueue.pucQueueStorage(queueGET_pcReadFrom(pxQueue)))
    :: ELSE_AS(_id, !queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue))
    fi
}

#define cTxLock temp_var2
#define cRxLock temp_var2

inline prvUnlockQueue(_id, pxQueue, temp_var, temp_var2)
{
    taskENTER_CRITICAL(_id);
    AWAIT_DS(_id, assert(cTxLock == NULL_byte); cTxLock = queueGET_cTxLock(pxQueue));
    do
    :: SELE_AS(_id, cTxLock > queueLOCKED_UNMODIFIED);
        #if (configUSE_QUEUE_SETS == 1)
        // TODO
        #else /* configUSE_QUEUE_SETS */
        if
        :: SELE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]);
            if
            :: SELE_AS(_id, temp_var != false, temp_var = NULL_byte);
                vTaskMissedYield(_id)
            :: ELSE_AS(_id, temp_var != false, temp_var = NULL_byte)
            fi
        :: ELSE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]));
            AWAIT_AS(_id, cTxLock = NULL_byte; break)
        fi;
        #endif /* configUSE_QUEUE_SETS */

        AWAIT_DS(_id, cTxLock = cTxLock - 1)
    :: ELSE_AS(_id, cTxLock > queueLOCKED_UNMODIFIED, cTxLock = NULL_byte; break)
    od;
    AWAIT_AS(_id, queueSET_cTxLock(pxQueue, queueUNLOCKED));
    taskEXIT_CRITICAL(_id);

    /* Do the same for the Rx lock. */
    taskENTER_CRITICAL(_id);
    AWAIT_DS(_id, assert(cRxLock == NULL_byte); cRxLock = queueGET_cRxLock(pxQueue));
    do
    :: SELE_AS(_id, cRxLock > queueLOCKED_UNMODIFIED);
        if
        :: SELE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]));
            xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]);
            if
            :: SELE_AS(_id, temp_var != false, temp_var = NULL_byte);
                vTaskMissedYield(_id)
            :: ELSE_AS(_id, temp_var != false, temp_var = NULL_byte)
            fi;

            AWAIT_DS(_id, cRxLock = cRxLock - 1)
        :: ELSE_AS(_id, !listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]));
            AWAIT_AS(_id, cRxLock = NULL_byte; break)
        fi;
    :: ELSE_AS(_id, cRxLock > queueLOCKED_UNMODIFIED, cRxLock = NULL_byte; break)
    od;
    AWAIT_AS(_id, queueSET_cRxLock(pxQueue, queueUNLOCKED));
    taskEXIT_CRITICAL(_id)
}

#endif

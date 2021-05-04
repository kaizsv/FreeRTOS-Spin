#ifndef _QUEUE_FROM_ISR_
#define _QUEUE_FROM_ISR_

           /*inline xQueueGenericSend(pxQueue, pvItemToQueue, xTicksToWait, xCopyPosition, xReturn, xIsTimeOut, temp_var, temp_var2, _id)*/

#define xQueueGenericSendFromISR(_id, pxQueue, pvItemToQueue, xCopyPosition, temp_var1) \
    AWAIT(_id, assert((temp_var1 == NULL_byte) && \
            (!((pvItemToQueue == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)))) && \
            (!((xCopyPosition == queueOVERWRITE) && (pxQueue.uxLength != 1))))); \
    /* Skip interrupt priority test */ \
    /* uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR(_id, pxTCB);*/ \
    if \
    :: SELE_AS(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE); \
        prvCopyDataToQueue(_id, pxQueue, pvItemToQueue, xCopyPosition, _, temp_var1); \
        if \
        :: SELE_AS(_id, queueGET_cTxLock(pxQueue) == 15); \
            /* configUSE_QUEUE_SETS */ \
            if \
            :: SELE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]) == false); \
                xTaskRemoveFromEventList(_id, temp_var1, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], _); \
            :: ELSE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]) == false); \
            fi; \
        :: ELSE_AS(_id, queueGET_cTxLock(pxQueue) == 15); \
            AWAIT_DS(_id, queueSET_cTxLock(pxQueue, queueGET_cTxLock(pxQueue) + 1)); \
        fi; \
    :: ELSE_AS(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength || xCopyPosition == queueOVERWRITE); \
    fi; \
    /* portCLEAR_INTERRUPT_MASK_FROM_ISR(_id, 0, temp_var); */

#define xQueueGiveFromISR(_id, pxQueue, temp_var) \
    AWAIT_DS(_id, assert(queueGET_uxQueueType(pxQueue) != 0 /*queueQUEUE_TYPE_BASE*/); \
        assert((!(queueGET_uxQueueType(pxQueue) == 1 || queueGET_uxQueueType(pxQueue) == 4) || \
                !(FIRST_TASK <= pxQueue.xSemaphore.xMutexHolder && pxQueue.xSemaphore.xMutexHolder < NULL_byte))) \
    ); \
    /* Skip interrupt priority test */ \
    /* uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR(_id, pxTCB);*/ \
    if \
    :: SELE_AS(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength); \
        AWAIT_DS(_id, pxQueue.uxMessagesWaiting = pxQueue.uxMessagesWaiting + 1); \
        if \
        :: SELE_AS(_id, queueGET_cTxLock(pxQueue) == 15); \
            if \
            :: SELE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]) == false); \
                /* TODO: pxHigherPriorityTaskWoken */ \
                xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive], _); \
            :: ELSE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]) == false); \
            fi; \
        :: ELSE_AS(_id, queueGET_cTxLock(pxQueue) == 15); \
            AWAIT_DS(_id, queueSET_cTxLock(pxQueue, queueGET_cTxLock(pxQueue) + 1)); \
        fi; \
    :: ELSE_AS(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength); \
    fi; \
    /* portCLEAR_INTERRUPT_MASK_FROM_ISR(_id, 0, pxTCB); */

#define xQueueReceiveFromISR(_id, pxQueue, pvBuffer, local_xReturn, temp_var) \
    AWAIT_DS(_id, assert(local_xReturn == false && \
        (!((pvBuffer == NULL_byte) && (!queueQUEUE_IS_ITEMSIZE_ZERO(pxQueue)))))); \
    /* Skip interrupt priority test */ \
    /* uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR(_id, pxTCB);*/ \
    if \
    :: SELE_AS(_id, pxQueue.uxMessagesWaiting > 0); \
        /* TODO: cRxLock */ \
        prvCopyDataFromQueue(_id, pxQueue, pvBuffer); \
        AWAIT_DS(_id, pxQueue.uxMessagesWaiting = pxQueue.uxMessagesWaiting - 1); \
        if \
        :: SELE_AS(_id, queueGET_cTxLock(pxQueue) == 15); \
            if \
            :: SELE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]) == false); \
                /* TODO: pxHigherPriorityTaskWoken */ \
                xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend], _); \
            :: ELSE_AS(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToSend]) == false); \
            fi; \
        :: ELSE_AS(_id, queueGET_cTxLock(pxQueue) == 15); \
            AWAIT_DS(_id, queueSET_cTxLock(pxQueue, queueGET_cTxLock(pxQueue) + 1)); \
        fi; \
        AWAIT_DS(_id, local_xReturn = true); \
    :: ELSE_AS(_id, pxQueue.uxMessagesWaiting > 0); \
        /* local_xReturn is already 0 */ \
    fi; \
    /* portCLEAR_INTERRUPT_MASK_FROM_ISR(_id, 0, temp_var); */

#endif

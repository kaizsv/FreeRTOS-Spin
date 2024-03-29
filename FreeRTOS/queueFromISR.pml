#ifndef _QUEUE_FROM_ISR_
#define _QUEUE_FROM_ISR_

#define xQueueGiveFromISR(_id, pxQueue, temp_var) \
    AWAIT_SAFE(_id, assert(queueGET_uxQueueType(pxQueue) != 0 /*queueQUEUE_TYPE_BASE*/); \
        assert((!(queueGET_uxQueueType(pxQueue) == 1 || queueGET_uxQueueType(pxQueue) == 4) || \
                !(FIRST_TASK <= pxQueue.xSemaphore.xMutexHolder && pxQueue.xSemaphore.xMutexHolder < NULL_byte))) \
    ); \
    /* Skip interrupt priority test */ \
    /* uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR(_id, pxTCB);*/ \
    if \
    :: SELE_SAFE(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength); \
        AWAIT_SAFE(_id, pxQueue.uxMessagesWaiting = pxQueue.uxMessagesWaiting + 1); \
        if \
        :: SELE_SAFE(_id, queueGET_cTxLock(pxQueue) == 15); \
            if \
            :: SELE_SAFE(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]) == false); \
                /* TODO: pxHigherPriorityTaskWoken */ \
                xTaskRemoveFromEventList(_id, temp_var, QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]); \
                AWAIT_SAFE(_id, temp_var = NULL_byte); \
            :: ELSE_SAFE(_id, listLIST_IS_EMPTY(QLISTs[queueGET_ListIndex(pxQueue) + xTasksWaitingToReceive]) == false); \
            fi; \
        :: ELSE_SAFE(_id, queueGET_cTxLock(pxQueue) == 15); \
            AWAIT_SAFE(_id, queueSET_cTxLock(pxQueue, queueGET_cTxLock(pxQueue) + 1)); \
        fi; \
    :: ELSE_SAFE(_id, pxQueue.uxMessagesWaiting < pxQueue.uxLength); \
    fi; \
    /* portCLEAR_INTERRUPT_MASK_FROM_ISR(_id, 0, pxTCB); */

#endif

#ifndef _Queue_Declarator_
#define _Queue_Declarator_

/* __QueuePointers_t */
#define xQueue                      u
#define pcWriteTo_pcReadFrom        single_byte
#define pucQueueStorage(index)      multi_bytes[index]
/* __SemaphoreData_t */
#define xSemaphore                  u
#define xMutexHolder                single_byte
#define uxRecursiveCallCount        multi_bytes[0]

#define __UnionDeclarator(uxQueueLength, uxItemType)    \
    typedef __Union_ ## uxItemType ## uxQueueLength {   \
        byte single_byte;                               \
        uxItemType multi_bytes[uxQueueLength];          \
    }

#define queueGET_pcWriteTo(pxQueue) get_upper_byte(pxQueue.xQueue.pcWriteTo_pcReadFrom)
inline queueSET_pcWriteTo(pxQueue, value)
{
    assert(0 <= value && value < 16);
    set_upper_byte(pxQueue.xQueue.pcWriteTo_pcReadFrom, value)
}

#define queueGET_pcReadFrom(pxQueue) get_lower_byte(pxQueue.xQueue.pcWriteTo_pcReadFrom)
inline queueSET_pcReadFrom(pxQueue, value)
{
    assert(0 <= value && value < 16);
    set_lower_byte(pxQueue.xQueue.pcWriteTo_pcReadFrom, value)
}

/* The two List_t's are declared in the array, LISTs. */
#define xTasksWaitingToSend     0
#define xTasksWaitingToReceive  1

#define __QueueDeclarator(uxQueueLength, uxItemType)            \
    typedef __QueueHandle_t_ ## uxItemType ## uxQueueLength {   \
        byte ListIndex_uxQueueType;                             \
                                                                \
        __Union_ ## uxItemType ## uxQueueLength u;              \
                                                                \
        byte uxMessagesWaiting;                                 \
        byte uxLength;                                          \
                                                                \
        byte cRxLock_cTxLock;                                   \
    }

#define QueueDeclarator(uxQueueLength, uxItemType)      \
    __UnionDeclarator(uxQueueLength, uxItemType)        \
    __QueueDeclarator(uxQueueLength, uxItemType)

#define QueueHandle_t(NAME, uxQueueLength, uxItemType)  \
    __QueueHandle_t_ ## uxItemType ## uxQueueLength NAME;

#define queueGET_ListIndex(pxQueue) get_upper_byte(pxQueue.ListIndex_uxQueueType)
inline queueSET_ListIndex(pxQueue, value)
{
    assert(0 <= value && value < 16);
    set_upper_byte(pxQueue.ListIndex_uxQueueType, value)
}

#define queueGET_uxQueueType(pxQueue) get_lower_byte(pxQueue.ListIndex_uxQueueType)
inline queueSET_uxQueueType(pxQueue, value)
{
    assert(0 <= value && value < 16);
    set_lower_byte(pxQueue.ListIndex_uxQueueType, value)
}

#define queueGET_cRxLock(pxQueue) get_upper_byte(pxQueue.cRxLock_cTxLock)
inline queueSET_cRxLock(pxQueue, value)
{
    assert(0 <= value && value < 16);
    set_upper_byte(pxQueue.cRxLock_cTxLock, value)
}

#define queueGET_cTxLock(pxQueue) get_lower_byte(pxQueue.cRxLock_cTxLock)
inline queueSET_cTxLock(pxQueue, value)
{
    assert(0 <= value && value < 16);
    set_lower_byte(pxQueue.cRxLock_cTxLock, value)
}

#endif

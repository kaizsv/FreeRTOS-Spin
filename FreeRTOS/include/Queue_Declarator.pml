#ifndef _Queue_Declarator_
#define _Queue_Declarator_

#define get_upper_byte(word)            ((word >> 4) & 15)
#define get_lower_byte(word)            (word & 15)
#define set_upper_byte(word, value)     word = (word & 15) | ((value) << 4)
#define set_lower_byte(word, value)     word = (word & 240) | (value)

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

/* A counter is enough for a mutex or semaphore. */
#define __UnionSemDeclarator(uxQueueLength, uxItemType)     \
    typedef __UnionSem_ ## uxItemType ## uxQueueLength {    \
        byte single_byte;                                   \
        uxItemType multi_bytes[1];                          \
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

/* The two List_t's are declared at QLISTs. */
#define xTasksWaitingToSend     0
#define xTasksWaitingToReceive  1

#define __QueueDeclarator(uxQueueLength, uxItemType)            \
    typedef __QueueHandle_t_ ## uxItemType ## uxQueueLength {   \
        byte ListIndex_uxQueueType;                             \
        __Union_ ## uxItemType ## uxQueueLength u;              \
        byte uxMessagesWaiting;                                 \
        byte uxLength;                                          \
        byte cRxLock_cTxLock;                                   \
    }

#define __SemDeclarator(uxQueueLength, uxItemType)          \
    typedef __SemHandle_t_ ## uxItemType ## uxQueueLength { \
        byte ListIndex_uxQueueType;                         \
        __UnionSem_ ## uxItemType ## uxQueueLength u;       \
        byte uxMessagesWaiting;                             \
        byte uxLength;                                      \
        byte cRxLock_cTxLock;                               \
    }

#define QueueDeclarator(uxQueueLength, uxItemType)  \
    __UnionDeclarator(uxQueueLength, uxItemType);   \
    __QueueDeclarator(uxQueueLength, uxItemType)

#define SemaphoreDeclarator(uxQueueLength, uxItemType)  \
    __UnionSemDeclarator(uxQueueLength, uxItemType);    \
    __SemDeclarator(uxQueueLength, uxItemType)

#define __Handler_t(TYPE, NAME, uxQueueLength, uxItemType)  \
    TYPE ## uxItemType ## uxQueueLength NAME

#define QueueHandle_t(NAME, uxQueueLength, uxItemType)  \
    __Handler_t(__QueueHandle_t_, NAME, uxQueueLength, uxItemType)

#define SemaphoreHandle_t(NAME, uxQueueLength, uxItemType)  \
    __Handler_t(__SemHandle_t_, NAME, uxQueueLength, uxItemType)

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

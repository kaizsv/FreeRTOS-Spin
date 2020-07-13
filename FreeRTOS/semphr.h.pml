#ifndef _SEMPHR_H_
#define _SEMPHR_H_

#include "queue.h.pml"

#define SemaphoreHandle_t   QueueHandle_t

#define semBINARY_SEMAPHORE_QUEUE_LENGTH    1
#define semCOUNTING_SEMAPHORE_QUEUE_LENGTH  0
#define semSEMAPHORE_QUEUE_ITEM_LENGTH      0
#define semGIVE_BLOCK_TIME                  0

#define vSemaphoreCreateBinary(xSemaphore, QueueID, xIsTimeOut, xReturn, temp_bool, temp_var)   \
    xQueueGenericCreate_fixed(xSemaphore, QueueID, 1, queueQUEUE_TYPE_BINARY_SEMAPHORE);        \
    xSemaphoreGive(xSemaphore, xIsTimeOut, xReturn, temp_bool, temp_var)

#define xSemaphoreCreateBinary(xSemaphore, QueueID) \
    xQueueGenericCreate_fixed(xSemaphore, QueueID, 1, queueQUEUE_TYPE_BINARY_SEMAPHORE)

#define xSemaphoreTake_NB(xSemaphore, xBlockTime, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id) \
    xQueueSemaphoreTake_NB(xSemaphore, xBlockTime, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id)

#define xSemaphoreTake(xSemaphore, xBlockTime, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id) \
    xQueueSemaphoreTake(xSemaphore, xBlockTime, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id)

#if (configUSE_RECURSIVE_MUTEXES == 1)
    #define xSemaphoreTakeRecursive(_id, pxMutex, xTicksToWait, xReturn, xInheritanceOccurred, xIsTimeOut, temp_var, temp_var2) \
        xQueueTakeMutexRecursive(_id, pxMutex, xTicksToWait, xReturn, xInheritanceOccurred, xIsTimeOut, temp_var, temp_var2)
#endif

#define xSemaphoreGive(xSemaphore, xReturn, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend_NB(xSemaphore, NULL_byte, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, xReturn, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id)

#if (configUSE_RECURSIVE_MUTEXES == 1)
    #define xSemaphoreGiveRecursive(_id, pxMutex, xReturn, xYieldRequired, xIsTimeOut, temp_var, temp_var2) \
        xQueueGiveMutexRecursive(_id, pxMutex, xReturn, xYieldRequired, xIsTimeOut, temp_var, temp_var2)
#endif

#define xSemaphoreCreateMutex(pxNewQueue, QueueID, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueCreateMutex(queueQUEUE_TYPE_MUTEX, pxNewQueue, QueueID, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id)

#if (configUSE_RECURSIVE_MUTEXES == 1)
    #define xSemaphoreCreateRecursiveMutex(pxNewQueue, QueueID, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id) \
        xQueueCreateMutex(queueQUEUE_TYPE_RECURSIVE_MUTEX, pxNewQueue, QueueID, temp_bool, temp_xIsTimeOut, temp_var, temp_var2, _id)
#endif

// TODO: FromISR version of semaphore
// TODO: xSemaphoreCreateCounting
// FIXME: CountingSemaphore has zero queue length.

#endif

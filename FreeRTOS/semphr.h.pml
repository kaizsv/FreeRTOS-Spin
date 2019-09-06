#ifndef _SEMPHR_H_
#define _SEMPHR_H_

#include "queue.h.pml"

#define SemaphoreHandle_t   QueueHandle_t

#define semBINARY_SEMAPHORE_QUEUE_LENGTH    1
#define semCOUNTING_SEMAPHORE_QUEUE_LENGTH  0
#define semSEMAPHORE_QUEUE_ITEM_LENGTH      0
#define semGIVE_BLOCK_TIME                  0

#define vSemaphoreCreateBinary(xSemaphore, QueueID, xIsNDTimeOut, xReturn, temp_bool, temp_var) \
    xQueueGenericCreate(xSemaphore, QueueID, 1, queueQUEUE_TYPE_BINARY_SEMAPHORE);              \
    xSemaphoreGive(xSemaphore, xIsNDTimeOut, xReturn, temp_bool, temp_var)

#define xSemaphoreCreateBinary(xSemaphore, QueueID) \
    xQueueGenericCreate(xSemaphore, QueueID, 1, queueQUEUE_TYPE_BINARY_SEMAPHORE)

#define xSemaphoreTake(xSemaphore, xBlockTime, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var1, temp_var2, _id) \
    xQueueSemaphoreTake(xSemaphore, xBlockTime, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var1, temp_var2, _id)

#define xSemaphoreGive(xSemaphore, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend(xSemaphore, NULL_byte, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id)

#define xSemaphoreCreateMutex(pxNewQueue, QueueID, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id) \
    xQueueCreateMutex(queueQUEUE_TYPE_MUTEX, pxNewQueue, QueueID, xReturn, temp_bool, temp_xIsNDTimeOut, temp_var, temp_var2, _id)

// TODO: recursive version of semaphore take and give
// TODO: FromISR version of semaphore
// TODO: xSemaphoreCreateCounting
// FIXME: CountingSemaphore has zero queue length.

#endif

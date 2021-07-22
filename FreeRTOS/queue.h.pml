#ifndef _QUEUE_H_
#define _QUEUE_H_

#include "tasks.pml"

#define queueSEND_TO_BACK                   0
#define queueSEND_TO_FRONT                  1
#define queueOVERWRITE                      2

// TODO: queueQUEUE_TYPE_SET
#define queueQUEUE_TYPE_BASE                0
#define queueQUEUE_TYPE_MUTEX               1 // uxLength: 1; itemSize: 0; pcHead (uxQueueType): NULL
#define queueQUEUE_TYPE_COUNTING_SEMAPHORE  2 // uxLength: 0; itemSize: 0
#define queueQUEUE_TYPE_BINARY_SEMAPHORE    3 // uxLength: 1; itemSize: 0
#define queueQUEUE_TYPE_RECURSIVE_MUTEX     4 // uxLength: 1; itemSize: 0; pcHead (uxQueueType): NULL

#include "queue.pml"

#define xQueueCreate(xQueue, QueueID, uxQueueLength) \
    xQueueGenericCreate_fixed(xQueue, QueueID, uxQueueLength, queueQUEUE_TYPE_BASE)

#define xQueueSendToFront_NB(xQueue, pvItemToQueue, xTicksToWait, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend_NB(xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_FRONT, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id)

#define xQueueSendToFront(xQueue, pvItemToQueue, xTicksToWait, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend(xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_FRONT, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id)

#define xQueueSendToBack_NB(xQueue, pvItemToQueue, xTicksToWait, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend_NB(xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_BACK, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id)

#define xQueueSendToBack(xQueue, pvItemToQueue, xTicksToWait, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend(xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_BACK, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id)

#define xQueueSend(xQueue, pvItemToQueue, xTicksToWait, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend(xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_BACK, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id)

#define xQueueOverwrite(xQueue, pvItemToQueue, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id) \
    xQueueGenericSend_NB(xQueue, pvItemToQueue, 0, queueOVERWRITE, xReturn, temp_xIsTimeOut, temp_var, temp_var2, _id)

// TODO: xQueueSendFromISR
// TODO: xQueueReset

#endif

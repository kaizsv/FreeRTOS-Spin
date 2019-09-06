#ifndef _LIST_DECLARATOR_
#define _LIST_DECLARATOR_

/* The List inside the queues are combined together. This modification is aim to
 * deal with the list removal at the uxListRemove function. */
#define pxReadyTasksLists   (promela_QUEUE_NUMBER * 2 + 0)
#define xDelayedTaskList1   (promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES + 0)
#define xPendingReadyList   (promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES + 1)

/** FIXME
* Since we do not model the timer ticks (xTickCount), the model will not suffer
* from ticks overflow. Thus, the overflow delayed task list can be dismissed.
*
* #define xDelayedTaskList2           (configMAX_PRIORITIES + 1)
* bit swapDelayedTaskList = 0;
* #define pxDelayedTaskList           (configMAX_PRIORITIES + (0 | swapDelayedTaskList))
* #define pxOverflowDelayedTaskList   (configMAX_PRIORITIES + (1 ^ swapDelayedTaskList))
*/
#define pxDelayedTaskList   xDelayedTaskList1

#if (INCLUDE_vTaskSuspend == 1)
    #define xSuspendedTaskList  (promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES + 2)
    List_t LISTs[promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES + 3];
#else
    List_t LISTs[promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES + 2];
#endif

#endif

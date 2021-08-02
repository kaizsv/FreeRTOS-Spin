#ifndef _LIST_DECLARATOR_
#define _LIST_DECLARATOR_

#ifndef __SPECIFIED_TASK_LISTS_SIZE__

    TYPEDEF_List_t(LIST_SIZE2);
    TYPEDEF_List_t(LIST_SIZE3);
    TYPEDEF_List_t_WITH_PXINDEX(LIST_SIZE5);

    #define QLIST_SIZE  LIST_SIZE3  /* Size of the Queue lists */
    #define RLIST_SIZE  LIST_SIZE5  /* Size of pxReadyTasksLists */
    #define DLIST_SIZE  LIST_SIZE3  /* Size of pxDelayedTaskList */
    #define PLIST_SIZE  LIST_SIZE2  /* Size of xPendingReadyList */
    #define SLIST_SIZE  LIST_SIZE3  /* Size of xSuspendedTaskList */

    #define QList_t List3_t
    #define RList_t List5_pxIndex_t
    #define DList_t List3_t
    #define PList_t List2_t
    #define SList_t List3_t

#else

    /* define lists with specified size */
    __SPECIFIED_TASK_LISTS_SIZE__

    #if !defined(QLIST_SIZE) || !defined(QList_t) || \
        !defined(RLIST_SIZE) || !defined(RList_t) || \
        !defined(DLIST_SIZE) || !defined(DList_t) || \
        !defined(PLIST_SIZE) || !defined(PList_t) || \
        !defined(SLIST_SIZE) || !defined(SList_t)
        #error Please make sure the size of 5 task lists are well defined!
    #endif

#endif

#if (promela_QUEUE_NUMBER > 0)
    QList_t QLISTs[promela_QUEUE_NUMBER * 2];
#endif

/* Container ID of Lists */
#define CID_READY_LISTS     (promela_QUEUE_NUMBER * 2)
#define CID_DELAYED_TASK    (promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES)
#define CID_PENDING_READY   (promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES + 1)

RList_t pxReadyTasksLists[configMAX_PRIORITIES];
DList_t xDelayedTaskList1;
PList_t xPendingReadyList;

#define pxDelayedTaskList   xDelayedTaskList1

#if (INCLUDE_vTaskSuspend == 1)
    #define CID_SUSPENDED_TASK  (promela_QUEUE_NUMBER * 2 + configMAX_PRIORITIES + 2)
    SList_t xSuspendedTaskList;
#endif

#endif

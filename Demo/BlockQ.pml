/* FreeRTOS/Demo/Common/Full/BlockQ.c */
/* Only four tasks can be verified completely. */

#define promela_TASK_NUMBER     4
#define promela_QUEUE_NUMBER    2

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run QProdB1();      \
        run QConsB2();      \
        run QProdB3();      \
        run QConsB4();      \
    }
//        run QProdB5();      \
//        run QConsB6();      \

#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#define xBlockTime  portMAX_DELAY
#define xDontBlock  0

QueueDeclarator(1, byte);
//QueueDeclarator(5, byte);

QueueHandle_t(pxQueueParameters1_xQueue, 1, byte);
#define pxQueueParameters1_xBlockTime       xBlockTime

#define pxQueueParameters2_xQueue           pxQueueParameters1_xQueue
#define pxQueueParameters2_xBlockTime       xDontBlock

QueueHandle_t(pxQueueParameters3_xQueue, 1, byte);
#define pxQueueParameters3_xBlockTime       xDontBlock

#define pxQueueParameters4_xQueue           pxQueueParameters3_xQueue
#define pxQueueParameters4_xBlockTime       xBlockTime

//QueueHandle_t(pxQueueParameters5_xQueue, 5, byte);
//#define pxQueueParameters5_xBlockTime       xBlockTime
//
//#define pxQueueParameters6_xQueue           pxQueueParameters5_xQueue
//#define pxQueueParameters6_xBlockTime       xBlockTime

#define INCREASE_VAR_AND_INTOVERFLOW(var)   \
    AWAIT_D(_PID, var = var + 1;            \
        if                                  \
        :: var == 8 -> var = 0              \
        :: else                             \
        fi                                  \
    )

proctype QProdB1()
{
    byte idx;
    byte usValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    assert(_PID == FIRST_TASK + 0);
loop:
    xQueueSend(pxQueueParameters1_xQueue, usValue, pxQueueParameters1_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn != true) ->
        AWAIT_D(_PID, assert(false))
    :: ELSE(_PID, local_xReturn != true) ->
        INCREASE_VAR_AND_INTOVERFLOW(usValue);
    fi;
    AWAIT_A(_PID, goto loop)
}

proctype QConsB2()
{
    byte idx;
    byte usData, usExpectedValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    bit local_xIsNDTimeOut = false;
    assert(_PID == FIRST_TASK + 1);
loop:
    xQueueReceive(pxQueueParameters2_xQueue, usData, pxQueueParameters2_xBlockTime, local_xReturn, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, usData != usExpectedValue) ->
            AWAIT_D(_PID, assert(false))
        :: ELSE(_PID, usData != usExpectedValue) ->
            INCREASE_VAR_AND_INTOVERFLOW(usExpectedValue);
        fi
    :: ELSE(_PID, local_xReturn == true)
    fi;
    AWAIT_A(_PID, goto loop)
}

proctype QProdB3()
{
    byte idx;
    byte usValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    assert(_PID == FIRST_TASK + 2);
loop:
    xQueueSend(pxQueueParameters3_xQueue, usValue, pxQueueParameters3_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn != true) ->
        AWAIT_D(_PID, assert(false))
    :: ELSE(_PID, local_xReturn != true) ->
        INCREASE_VAR_AND_INTOVERFLOW(usValue);
    fi;
    AWAIT_A(_PID, goto loop)
}

proctype QConsB4()
{
    byte idx;
    byte usData, usExpectedValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    bit local_xIsNDTimeOut = false;
    assert(_PID == FIRST_TASK + 3);
loop:
    xQueueReceive(pxQueueParameters4_xQueue, usData, pxQueueParameters4_xBlockTime, local_xReturn, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, usData != usExpectedValue) ->
            AWAIT_D(_PID, assert(false))
        :: ELSE(_PID, usData != usExpectedValue) ->
            INCREASE_VAR_AND_INTOVERFLOW(usExpectedValue);
        fi
    :: ELSE(_PID, local_xReturn == true)
    fi;
    AWAIT_A(_PID, goto loop)
}

//proctype QProdB5()
//{
//    byte idx;
//    byte usValue = 0;
//    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
//    bit local_xReturn = false, local_bit = false;
//    bit local_xIsNDTimeOut = false;
//    assert(_PID == FIRST_TASK + 4);
//loop:
//    xQueueSend(pxQueueParameters5_xQueue, usValue, pxQueueParameters5_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
//    if
//    :: SELE(_PID, local_xReturn != true) ->
//        AWAIT_D(_PID, assert(false));
//    :: ELSE(_PID, local_xReturn != true) ->
//        INCREASE_VAR_AND_INTOVERFLOW(usValue);
//    fi;
//    AWAIT_A(_PID, goto loop)
//}
//
//proctype QConsB6()
//{
//    byte idx;
//    byte usData, usExpectedValue = 0;
//    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
//    bit local_xReturn = false;
//    bit local_xIsNDTimeOut = false;
//    assert(_PID == FIRST_TASK + 5);
//loop:
//    xQueueReceive(pxQueueParameters6_xQueue, usData, pxQueueParameters6_xBlockTime, local_xReturn, local_xIsNDTimeOut, local_var1, local_var2, _PID);
//    if
//    :: SELE(_PID, local_xReturn == true) ->
//        if
//        :: SELE(_PID, usData != usExpectedValue) ->
//            AWAIT_D(_PID, assert(false));
//        :: ELSE(_PID, usData != usExpectedValue) ->
//            INCREASE_VAR_AND_INTOVERFLOW(usExpectedValue);
//        fi
//    :: ELSE(_PID, local_xReturn == true)
//    fi;
//    AWAIT_A(_PID, goto loop)
//}

init {
    byte idx;
    byte local_var1 = NULL_byte;

    d_step {
        xQueueCreate(pxQueueParameters1_xQueue, 0, 1);
        xQueueCreate(pxQueueParameters3_xQueue, 1, 1);
//        xQueueCreate(pxQueueParameters5_xQueue, 2, 5);

        prvInitialiseTaskLists(local_var1);

        xTaskCreate_fixed(FIRST_TASK + 0, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, tskIDLE_PRIORITY);

        xTaskCreate_fixed(FIRST_TASK + 2, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 3, 1);

//        xTaskCreate_fixed(FIRST_TASK + 4, tskIDLE_PRIORITY);
//        xTaskCreate_fixed(FIRST_TASK + 5, tskIDLE_PRIORITY);
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}

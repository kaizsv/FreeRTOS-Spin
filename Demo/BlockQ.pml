/* FreeRTOS/Demo/Common/Full/BlockQ.c */

#define promela_TASK_NUMBER     6
#define promela_QUEUE_NUMBER    3

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS()     \
    atomic {                \
        run QProdB1();      \
        run QConsB2();      \
        run QProdB3();      \
        run QConsB4();      \
        run QProdB5();      \
        run QConsB6();      \
                            \
        run IDLE_TASK();    \
    }

#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#define blckqNUM_TASK_SETS 3

#define xBlockTime  1
#define xDontBlock  0

byte sBlockingConsumerCount[blckqNUM_TASK_SETS];
byte sBlockingProducerCount[blckqNUM_TASK_SETS];

QueueDeclarator(1, byte);
QueueDeclarator(5, byte);

QueueHandle_t(pxQueueParameters1_xQueue, 1, byte);
#define pxQueueParameters1_xBlockTime       xBlockTime
#define pxQueueParameters1_psCheckVariable  sBlockingConsumerCount[0]

#define pxQueueParameters2_xQueue           pxQueueParameters1_xQueue
#define pxQueueParameters2_xBlockTime       xDontBlock
#define pxQueueParameters2_psCheckVariable  sBlockingProducerCount[0]

QueueHandle_t(pxQueueParameters3_xQueue, 1, byte);
#define pxQueueParameters3_xBlockTime       xDontBlock
#define pxQueueParameters3_psCheckVariable  sBlockingConsumerCount[1]

#define pxQueueParameters4_xQueue           pxQueueParameters3_xQueue
#define pxQueueParameters4_xBlockTime       xBlockTime
#define pxQueueParameters4_psCheckVariable  sBlockingProducerCount[1]

QueueHandle_t(pxQueueParameters5_xQueue, 5, byte);
#define pxQueueParameters5_xBlockTime       xBlockTime
#define pxQueueParameters5_psCheckVariable  sBlockingConsumerCount[2]

#define pxQueueParameters6_xQueue           pxQueueParameters5_xQueue
#define pxQueueParameters6_xBlockTime       xBlockTime
#define pxQueueParameters6_psCheckVariable  sBlockingProducerCount[2]

proctype QProdB1()
{
    byte idx;
    byte usValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    bit sErrorEverOccureed = 0;
    assert(FIRST_TASK == _PID);
loop:
    xQueueSend(pxQueueParameters1_xQueue, usValue, pxQueueParameters1_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn != true) ->
        AWAIT_D(_PID, sErrorEverOccureed = true)
    :: ELSE(_PID, local_xReturn != true) ->
        if
        :: SELE(_PID, sErrorEverOccureed == false) ->
            AWAIT_D(_PID, pxQueueParameters1_psCheckVariable = pxQueueParameters1_psCheckVariable + 1)
        :: ELSE(_PID, sErrorEverOccureed == false)
        fi;
        AWAIT_D(_PID,
            if
            :: usValue == NULL_byte - 1 ->
                usValue = 0 /* integer overflow */
            :: else ->
                usValue = usValue + 1
            fi )
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
    bit sErrorEverOccureed = 0;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xQueueReceive(pxQueueParameters2_xQueue, usData, pxQueueParameters2_xBlockTime, local_xReturn, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, usData != usExpectedValue) ->
            AWAIT_D(_PID, usExpectedValue = usData);
            AWAIT_D(_PID, sErrorEverOccureed = true; assert(false))
        :: ELSE(_PID, usData != usExpectedValue) ->
            if
            :: SELE(_PID, sErrorEverOccureed == false) ->
                AWAIT_D(_PID, pxQueueParameters2_psCheckVariable = pxQueueParameters2_psCheckVariable + 1)
            :: ELSE(_PID, sErrorEverOccureed == false)
            fi;
            AWAIT_D(_PID,
                if
                :: usExpectedValue == NULL_byte - 1 ->
                    usExpectedValue = 0 /* integer overflow */
                :: else ->
                    usExpectedValue = usExpectedValue + 1
                fi )
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
    bit sErrorEverOccureed = 0;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xQueueSend(pxQueueParameters3_xQueue, usValue, pxQueueParameters3_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn != true) ->
        AWAIT_D(_PID, sErrorEverOccureed = true)
    :: ELSE(_PID, local_xReturn != true) ->
        if
        :: SELE(_PID, sErrorEverOccureed == false) ->
            AWAIT_D(_PID, pxQueueParameters3_psCheckVariable = pxQueueParameters3_psCheckVariable + 1)
        :: ELSE(_PID, sErrorEverOccureed == false)
        fi;
        AWAIT_D(_PID,
            if
            :: usValue == NULL_byte - 1 ->
                usValue = 0 /* integer overflow */
            :: else ->
                usValue = usValue + 1
            fi )
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
    bit sErrorEverOccureed = 0;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xQueueReceive(pxQueueParameters2_xQueue, usData, pxQueueParameters2_xBlockTime, local_xReturn, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, usData != usExpectedValue) ->
            AWAIT_D(_PID, usExpectedValue = usData);
            AWAIT_D(_PID, sErrorEverOccureed = true; assert(false))
        :: ELSE(_PID, usData != usExpectedValue) ->
            if
            :: SELE(_PID, sErrorEverOccureed == false) ->
                AWAIT_D(_PID, pxQueueParameters2_psCheckVariable = pxQueueParameters2_psCheckVariable + 1)
            :: ELSE(_PID, sErrorEverOccureed == false)
            fi;
            AWAIT_D(_PID,
                if
                :: usExpectedValue == NULL_byte - 1 ->
                    usExpectedValue = 0 /* integer overflow */
                :: else ->
                    usExpectedValue = usExpectedValue + 1
                fi )
        fi
    :: ELSE(_PID, local_xReturn == true)
    fi;
    AWAIT_A(_PID, goto loop)
}

proctype QProdB5()
{
    byte idx;
    byte usValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    bit sErrorEverOccureed = 0;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xQueueSend(pxQueueParameters5_xQueue, usValue, pxQueueParameters5_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn != true) ->
        AWAIT_D(_PID, sErrorEverOccureed = true)
    :: ELSE(_PID, local_xReturn != true) ->
        if
        :: SELE(_PID, sErrorEverOccureed == false) ->
            AWAIT_D(_PID, pxQueueParameters5_psCheckVariable = pxQueueParameters5_psCheckVariable + 1)
        :: ELSE(_PID, sErrorEverOccureed == false)
        fi;
        AWAIT_D(_PID,
            if
            :: usValue == NULL_byte - 1 ->
                usValue = 0 /* integer overflow */
            :: else ->
                usValue = usValue + 1
            fi )
    fi;
    AWAIT_A(_PID, goto loop)
}

proctype QConsB6()
{
    byte idx;
    byte usData, usExpectedValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    bit local_xIsNDTimeOut = false;
    bit sErrorEverOccureed = 0;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xQueueReceive(pxQueueParameters2_xQueue, usData, pxQueueParameters2_xBlockTime, local_xReturn, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, usData != usExpectedValue) ->
            AWAIT_D(_PID, usExpectedValue = usData);
            AWAIT_D(_PID, sErrorEverOccureed = true; assert(false))
        :: ELSE(_PID, usData != usExpectedValue) ->
            if
            :: SELE(_PID, sErrorEverOccureed == false) ->
                AWAIT_D(_PID, pxQueueParameters2_psCheckVariable = pxQueueParameters2_psCheckVariable + 1)
            :: ELSE(_PID, sErrorEverOccureed == false)
            fi;
            AWAIT_D(_PID,
                if
                :: usExpectedValue == NULL_byte - 1 ->
                    usExpectedValue = 0 /* integer overflow */
                :: else ->
                    usExpectedValue = usExpectedValue + 1
                fi )
        fi
    :: ELSE(_PID, local_xReturn == true)
    fi;
    AWAIT_A(_PID, goto loop)
}

init {
    byte idx;
    byte local_var1 = NULL_byte;

    xQueueCreate(pxQueueParameters1_xQueue, 0, 1);
    xQueueCreate(pxQueueParameters3_xQueue, 1, 1);
    xQueueCreate(pxQueueParameters5_xQueue, 2, 5);

    prvInitialiseTaskLists(local_var1);

    xTaskCreate(EP, FIRST_TASK + 0, 1, local_var1);
    xTaskCreate(EP, FIRST_TASK + 1, tskIDLE_PRIORITY, local_var1);

    xTaskCreate(EP, FIRST_TASK + 2, tskIDLE_PRIORITY, local_var1);
    xTaskCreate(EP, FIRST_TASK + 3, 1, local_var1);

    xTaskCreate(EP, FIRST_TASK + 4, tskIDLE_PRIORITY, local_var1);
    xTaskCreate(EP, FIRST_TASK + 5, tskIDLE_PRIORITY, local_var1);

    vTaskStartScheduler(EP, local_var1)
}

/* FreeRTOS/Demo/Common/Minimal/semtest.c */

#define promela_TASK_NUMBER     4
#define promela_QUEUE_NUMBER    2

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS()     \
    atomic {                \
        run prvSemaphoreTest1(); \
        run prvSemaphoreTest2(); \
        run prvSemaphoreTest3(); \
        run prvSemaphoreTest4(); \
        run IDLE_TASK();    \
    }

#define QUEUE_TAKE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
#include "../property/semtest.pml"
#endif

#define semtstBLOCKING_EXPECTED_VALUE       254 /* 0xff */
#define semtstNON_BLOCKING_EXPECTED_VALUE   15  /* 0xf */

QueueDeclarator(1, byte);

SemaphoreHandle_t(pxFirstSemaphore_xSemaphore, 1, byte);
byte pxFirstSemaphore_pulSharedVariable = semtstNON_BLOCKING_EXPECTED_VALUE;
#define pxFirstSemaphore_xBlockTime 0

SemaphoreHandle_t(pxSecondSemaphore_xSemaphore, 1, byte);
byte pxSecondSemaphore_pulSharedVariable = semtstBLOCKING_EXPECTED_VALUE;
#define pxSecondSemaphore_xBlockTime 1

proctype prvSemaphoreTest1()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    assert(FIRST_TASK == _PID);
loop:
    xSemaphoreTake(pxFirstSemaphore_xSemaphore, pxFirstSemaphore_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxFirstSemaphore_pulSharedVariable != semtstNON_BLOCKING_EXPECTED_VALUE) ->
            assert(false)
        :: ELSE(_PID, pxFirstSemaphore_pulSharedVariable != semtstNON_BLOCKING_EXPECTED_VALUE)
        fi;

        for (idx: 0 .. semtstNON_BLOCKING_EXPECTED_VALUE) {
            AWAIT_D(_PID, pxFirstSemaphore_pulSharedVariable = idx);
            if
            :: SELE(_PID, pxFirstSemaphore_pulSharedVariable != idx) ->
                assert(false)
            :: ELSE(_PID, pxFirstSemaphore_pulSharedVariable != idx)
            fi
        }
        AWAIT_A(_PID, idx = 0);

        xSemaphoreGive(pxFirstSemaphore_xSemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
        if
        :: SELE(_PID, local_xReturn == false) ->
            assert(false)
        :: ELSE(_PID, local_xReturn == false)
        fi;
    :: ELSE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxFirstSemaphore_xBlockTime == 0) ->
            taskYIELD(_PID, local_var1);
        :: ELSE(_PID, pxFirstSemaphore_xBlockTime == 0)
        fi
    fi;
    // TODO: vTaskDelay
liveness:
    goto loop
}

proctype prvSemaphoreTest2()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xSemaphoreTake(pxFirstSemaphore_xSemaphore, pxFirstSemaphore_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxFirstSemaphore_pulSharedVariable != semtstNON_BLOCKING_EXPECTED_VALUE) ->
            assert(false)
        :: ELSE(_PID, pxFirstSemaphore_pulSharedVariable != semtstNON_BLOCKING_EXPECTED_VALUE)
        fi;

        for (idx: 0 .. semtstNON_BLOCKING_EXPECTED_VALUE) {
            AWAIT_D(_PID, pxFirstSemaphore_pulSharedVariable = idx);
            if
            :: SELE(_PID, pxFirstSemaphore_pulSharedVariable != idx) ->
                assert(false)
            :: ELSE(_PID, pxFirstSemaphore_pulSharedVariable != idx)
            fi
        }
        AWAIT_A(_PID, idx = 0);

        xSemaphoreGive(pxFirstSemaphore_xSemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
        if
        :: SELE(_PID, local_xReturn == false) ->
            assert(false)
        :: ELSE(_PID, local_xReturn == false)
        fi;
    :: ELSE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxFirstSemaphore_xBlockTime == 0) ->
            taskYIELD(_PID, local_var1);
        :: ELSE(_PID, pxFirstSemaphore_xBlockTime == 0)
        fi
    fi;
    // TODO: vTaskDelay
liveness:
    goto loop
}

proctype prvSemaphoreTest3()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xSemaphoreTake(pxSecondSemaphore_xSemaphore, pxSecondSemaphore_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxSecondSemaphore_pulSharedVariable != semtstBLOCKING_EXPECTED_VALUE) ->
            assert(false)
        :: ELSE(_PID, pxSecondSemaphore_pulSharedVariable != semtstBLOCKING_EXPECTED_VALUE)
        fi;

        for (idx: 0 .. semtstBLOCKING_EXPECTED_VALUE) {
            AWAIT_D(_PID, pxSecondSemaphore_pulSharedVariable = idx);
            if
            :: SELE(_PID, pxSecondSemaphore_pulSharedVariable != idx) ->
                assert(false)
            :: ELSE(_PID, pxSecondSemaphore_pulSharedVariable != idx)
            fi
        }
        AWAIT_A(_PID, idx = 0);

        xSemaphoreGive(pxSecondSemaphore_xSemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
        if
        :: SELE(_PID, local_xReturn == false) ->
            assert(false)
        :: ELSE(_PID, local_xReturn == false)
        fi;
    :: ELSE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxFirstSemaphore_xBlockTime == 0) ->
            taskYIELD(_PID, local_var1);
        :: ELSE(_PID, pxFirstSemaphore_xBlockTime == 0)
        fi
    fi;
    // TODO: vTaskDelay
liveness:
    goto loop
}

proctype prvSemaphoreTest4()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xSemaphoreTake(pxSecondSemaphore_xSemaphore, pxSecondSemaphore_xBlockTime, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxSecondSemaphore_pulSharedVariable != semtstBLOCKING_EXPECTED_VALUE) ->
            assert(false)
        :: ELSE(_PID, pxSecondSemaphore_pulSharedVariable != semtstBLOCKING_EXPECTED_VALUE)
        fi;

        for (idx: 0 .. semtstBLOCKING_EXPECTED_VALUE) {
            AWAIT_D(_PID, pxSecondSemaphore_pulSharedVariable = idx);
            if
            :: SELE(_PID, pxSecondSemaphore_pulSharedVariable != idx) ->
                assert(false)
            :: ELSE(_PID, pxSecondSemaphore_pulSharedVariable != idx)
            fi
        }
        AWAIT_A(_PID, idx = 0);

        xSemaphoreGive(pxSecondSemaphore_xSemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
        if
        :: SELE(_PID, local_xReturn == false) ->
            assert(false)
        :: ELSE(_PID, local_xReturn == false)
        fi;
    :: ELSE(_PID, local_xReturn == true) ->
        if
        :: SELE(_PID, pxFirstSemaphore_xBlockTime == 0) ->
            taskYIELD(_PID, local_var1);
        :: ELSE(_PID, pxFirstSemaphore_xBlockTime == 0)
        fi
    fi;
    // TODO: vTaskDelay
liveness:
    goto loop
}

init {
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;

    xSemaphoreCreateBinary(pxFirstSemaphore_xSemaphore, 0);
    xSemaphoreGive(pxFirstSemaphore_xSemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, EP);

    xSemaphoreCreateBinary(pxSecondSemaphore_xSemaphore, 1);
    xSemaphoreGive(pxSecondSemaphore_xSemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, EP);

    prvInitialiseTaskLists(local_var1);
    xTaskCreate(EP, FIRST_TASK, tskIDLE_PRIORITY, local_var1);
    xTaskCreate(EP, FIRST_TASK + 1, tskIDLE_PRIORITY, local_var1);
    xTaskCreate(EP, FIRST_TASK + 2, 1, local_var1);
    xTaskCreate(EP, FIRST_TASK + 3, 1, local_var1);
    vTaskStartScheduler(EP, local_var1)
}

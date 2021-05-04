/* FreeRTOS/Demo/Common/Minimal/comtest.c */

#define promela_TASK_NUMBER     2
#define promela_NVIC_NUMBER     1 /* #define promela_EXP_NUMBER (SYS_EXP + promela_NVIC_NUMBER) */
#define promela_QUEUE_NUMBER    2

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#if 0
#ifdef RUN_ALL_NVICS
    RUN_ALL_NVICS();
#endif
#endif
#define RUN_ALL_NVICS() \
    atomic {            \
        run vUARTInterruptHandler(); \
    }

#define RUN_ALL_TASKS(stmts)    \
    atomic {            \
        stmts;          \
        run COMTx();    \
        run COMRx();    \
        run loopback_connector(); /* Simulate the physical loopback connector */ \
    }

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"

#define comTOTAL_PERMISSIBLE_ERRORS 2

#define comTX_MAX_BLOCK_TIME    150 /* 0x96 */
#define comTX_MIN_BLOCK_TIME    50  /* 0x32 */

#define comNO_BLOCK             0

#define comRX_BLOCK_TIME        253

#define comFIRST_BYTE           ('A')
#define comLAST_BYTE            ('B')

// TODO: maximum queue length is 15 in the model
#define comBUFFER_LEN           2 /* 'B' - 'A' + 1 */
#define comINITIAL_RX_COUNT_VAL 0

#include "serial/serial.pml"

proctype COMTx()
{
    byte idx;
    bit local_xReturn = 0, local_xIsTimeOut = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    byte cByteToSend;
    assert(_PID == FIRST_TASK);
do
::  for (cByteToSend: comFIRST_BYTE .. comLAST_BYTE) {
        xSerialPutChar(_PID, cByteToSend, comNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2);
        AWAIT(_PID, local_xReturn = false);
    }
    vTaskDelay(_PID, 50, local_xReturn, local_var1, local_var2);
od
}

proctype COMRx()
{
    byte idx;
    bit xResyncRequired = 0;
    bit local_xReturn = 0, local_xIsTimeOut = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    byte cExpectedByte, cByteRxed = NULL_byte, xErrorOccured = 0;
    assert(_PID == FIRST_TASK + 1);
do
::  for (cExpectedByte: comFIRST_BYTE .. comLAST_BYTE) {
        xSerialGetChar(_PID, cByteRxed, comRX_BLOCK_TIME, local_xReturn, local_xIsTimeOut, local_var1, local_var2)
        if
        :: SELE(_PID, local_xReturn == true, local_xReturn = false);
            if
            :: SELE(_PID, cByteRxed != cExpectedByte);
                AWAIT(_PID, xResyncRequired = true; break)
            :: ELSE(_PID, cByteRxed != cExpectedByte);
            fi;
        :: ELSE(_PID, local_xReturn == true);
        fi;
    }

    if
    :: SELE(_PID, xResyncRequired == true);
        do
        :: SELE(_PID, cByteRxed != comLAST_BYTE, local_xReturn = false);
            xSerialGetChar(_PID, cByteRxed, comRX_BLOCK_TIME, local_xReturn, local_xIsTimeOut, local_var1, local_var2)
        :: ELSE(_PID, cByteRxed != comLAST_BYTE, local_xReturn = false; break);
        od;
        AWAIT(_PID, xErrorOccured = xErrorOccured + 1; xResyncRequired = false);
    :: ELSE(_PID, xResyncRequired == true);
running:
        AWAIT(_PID, assert(xErrorOccured < comTOTAL_PERMISSIBLE_ERRORS));
    fi;
od
}

init
{
    byte idx;
    byte local_var1 = NULL_byte;

    /* Initial com port */
    atomic {
        xSerialPortInitMinimal_fixed();
    };

    /* Create Tx and Rx tasks */
    d_step {
        prvInitialiseTaskLists(local_var1);
        xTaskCreate_fixed(FIRST_TASK + 0, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 1, tskIDLE_PRIORITY + 1);
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}

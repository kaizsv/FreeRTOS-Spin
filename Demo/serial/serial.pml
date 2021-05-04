/* FreeRTOS/Demo/CORTEX_STM32F103_IAR/serial/serial.c */

#ifndef _SERIAL_
#define _SERIAL_

#include "../../FreeRTOS.pml"
#include "../../FreeRTOS/queue.pml"
#include "../../FreeRTOS/queue.h.pml"
#include "../../FreeRTOS/queueFromISR.pml"

/* Abstraction of USART IT */
#define DISABLE 0
#define ENABLE  1

typedef USARTx {
    byte tdr;   /* Transmit data register */
    byte rdr;   /* Receive data register */
    bit TXEIE;
    bit RXNEIE;
};

QueueDeclarator(2, byte);
QueueDeclarator(3, byte);

QueueHandle_t(xRxedChars, 2, byte);
QueueHandle_t(xCharsForTx, 3, byte);

#define vUARTInterruptHandler_ID    SYS_EXP

#define USART1_USART_IT_TXE_IS_SET  (USART1.tdr == NULL_byte)
#define USART1_USART_IT_RXNE_IS_SET (USART1.rdr != NULL_byte)
USARTx USART1;

inline xSerialPortInitMinimal_fixed()
{
    xQueueCreate(xRxedChars, 0, comBUFFER_LEN);
    xQueueCreate(xCharsForTx, 1, comBUFFER_LEN + 1);

    /* Ignore Baud Rate and GPIO setting */
    USART1.tdr = NULL_byte;
    USART1.rdr = NULL_byte;
    SET_PRIO_EXP(vUARTInterruptHandler_ID, 240);
}

inline xSerialGetChar(_id, pcRxedChar, xBlockTime, temp_xReturn, temp_xIsTimeOut, temp_var1, temp_var2)
{
    xQueueReceive(xRxedChars, pcRxedChar, xBlockTime, temp_xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
}

inline xSerialPutChar(_id, cOutChar, xBlockTime, temp_xReturn, temp_xIsTimeOut, temp_var1, temp_var2)
{
    //xQueueSend(xCharsForTx, cOutChar, xBlockTime, temp_xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    xQueueGenericSend(xCharsForTx, cOutChar, xBlockTime, queueSEND_TO_BACK, temp_xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    if
    :: SELE(_id, temp_xReturn == true);
        AWAIT(_id, USART1.TXEIE = 1);
    :: ELSE(_id, temp_xReturn == true);
    fi
}

#define USART1_IRQ_TRIGGERED    ((USART1.TXEIE && USART1_USART_IT_TXE_IS_SET) || \
                                (USART1.RXNEIE && USART1_USART_IT_RXNE_IS_SET))

proctype vUARTInterruptHandler()
{
    byte idx;
    bit local_bit = 0;
    byte cChar = NULL_byte, local_var = NULL_byte;
    assert(_PID == vUARTInterruptHandler_ID);
do
::  irq(_PID, USART1_IRQ_TRIGGERED);
    if
    :: SELE_AS(_PID, USART1_USART_IT_TXE_IS_SET);
        xQueueReceiveFromISR(_PID, xCharsForTx, cChar, local_bit, local_var);
        if
        :: SELE_AS(_PID, local_bit == 1, local_bit = 0);
            AWAIT_DS(_PID, USART1.tdr = cChar; cChar = NULL_byte);
        :: ELSE_AS(_PID, local_bit == 1);
            AWAIT_DS(_PID, USART1.TXEIE = 0);
        fi;
    :: ELSE_AS(_PID, USART1_USART_IT_TXE_IS_SET);
    fi;

    if
    :: SELE_AS(_PID, USART1_USART_IT_RXNE_IS_SET);
        AWAIT_DS(_PID, cChar = USART1.rdr; USART1.rdr = NULL_byte; assert(cChar != NULL_byte));
        xQueueSendFromISR(_PID, xRxedChars, cChar, local_var);
    :: ELSE_AS(_PID, USART1_USART_IT_RXNE_IS_SET);
    fi;
    AWAIT_DS(_PID, cChar = NULL_byte; exp_return(local_var))
od
}

proctype loopback_connector()
{
    assert(_PID == FIRST_TASK + promela_TASK_NUMBER);
do
::  d_step { USART1.TXEIE && !USART1_USART_IT_TXE_IS_SET ->
        USART1.rdr = USART1.tdr; USART1.tdr = NULL_byte
    };
od;
}

#endif

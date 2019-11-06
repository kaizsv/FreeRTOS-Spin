#ifndef _PROMELA_
#define _PROMELA_

#define NULL_byte       255 /* 0xff */

/** Executing process
*
*      init PendSV SysTick <<exp handlers>>  FIRST_TASK  SEC_TASK  <<user tasks>>
* _pid  0     1      2          ... (incremental numbers)
* _PID        0      1          ... (incremental numbers)
*
* _pid is a read-only variable assignend by Spin to identify the executing
* processes. However, the "init" process, only starting the other processes, is
* not an executing process in the model. We shift the value of _pid by 1 to skip
* the "init" process.
*/
#define _PID (_pid - 1)
byte EP = NULL_byte; /* Executing Process */
#define AWAIT_D(id, stmt) d_step { (id == EP) -> stmt }
#define AWAIT_A(id, stmt) atomic { (id == EP) -> stmt }
#define SELE(id, cond) ((id == EP) && (cond))
#define ELSE(id, cond) ((id == EP) && !(cond))

#endif

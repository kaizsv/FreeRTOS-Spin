A PROMELA model of [FreeRTOS](https://www.freertos.org/) kernel.

## Requirement

- the Spin model checker (on Ubuntu)
    ```
    apt install spin
    ```
    or (source code)
    ```
    git clone https://github.com/nimble-code/Spin.git
    cd Spin && make
    ```

## Quick Start

1. Check free RAM on your machine and set the memory limitation in `mk/config.mk`.
By default, memory usage is bounded to 20GB. Also, set max search depth if
the verification reaches the max depth. There are some predefined depth
configurations below.

2. Check configurations in `platform/stm32p103_FreeRTOSConfig.pml`, especially
the configurations of scheduling policies. Check architecture in `FreeRTOS.pml`.
Currently, we only have a **ARMv7-M** architecture model.

3. Perform verification
    * Safety verification (*depth-first search* algorithm)
    ```
    make safety_dfs TARGET=Demo/<<APP_NAME>>
    ```
    or simply `make safety_dfs` if the default target is set in `mk/config.mk`.
    Change `safety_dfs` to `safety_bfs` to perform the verification with
    the *breadth-first search* algorithm.
    * Liveness verification (LTL formulas are defined in `./Demo/property/`)
    ```
    make acceptance TARGET=Demo/<<APP_NAME>>
    ```
    or simply `make acceptance` if the default target is set.
    * Some applications have a correction. Append term `CORRECTION=1` behind
    a verification `make` command to apply it.
    * We provide a script `./scripts/verify_all.sh` to perform verification to
    all the applications in `Demo` folder. Results are stored in `./output`
    folder. Usages:
    ```
    ./scripts/verify_all [-dfs|-bfs|-ltl] [-correction]
    ```

4. Trace a counterexample.
    * Simple (for safety verification only)
    ```
    make trail
    ```
    * Full (for safety verification only)
    ```
    make trail_full
    ```
    * Full (for acceptance verification only)
    ```
    make trail_ltl
    ```
    * Use `J=<<N_STEPS>>` to jump over N steps and `U=<<Nth_STEP>>` to stop the
    trail at Nth setp. Use `grep` command to highlight key words. For example:
    ```
    make trail J=<<N_STEPS>> U=<<Nth_STEP>> | grep <<KEY_WORDS>>
    ```

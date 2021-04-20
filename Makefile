include mk/config.mk
TARGET ?= $(DEFAULT_TARGET)

TARGET_DIR = Demo
TARGET_PATH = $(addprefix $(TARGET_DIR)/, $(notdir $(TARGET)))

ifdef $(notdir $(basename $(TARGET)))_APP_DEPTH
	MAX_DEPTH = $($(notdir $(basename $(TARGET)))_APP_DEPTH)
endif

CC = gcc
PAN = pan
SPIN = spin

include mk/flags.mk

$(PAN).c:
	$(SPIN) $(SPINFLAGS) $(TARGET_PATH)

$(PAN): $(PAN).c
	$(CC) $(CFLAGS) -DMEMLIM=$(MAX_MEMORY) $(COMPILETIME_FLAGS) -o $@ $<

safety_bfs: clean .safety .bfs $(PAN)
	./$(PAN)

safety_dfs: clean .safety $(PAN)
	./$(PAN) $(RUNTIME_FLAGS)

acceptance: clean .ltl $(PAN)
	./$(PAN) $(RUNTIME_FLAGS)

non-progress: clean .np $(PAN)
	./$(PAN) $(RUNTIME_FLAGS)

.PHONY: trail trail_full trail_ltl clean distclean
trail:
	$(SPIN) $(TRAIL_FLAGS) $(TARGET_PATH)

trail_full:
	$(SPIN) -s -r -l -g $(TRAIL_FLAGS) $(TARGET_PATH)

trail_ltl:
	$(SPIN) -s -r -l -g -DLTL $(TRAIL_FLAGS) $(TARGET_PATH)

clean:
	rm -rf $(PAN)*

distclean: clean
	rm -rf *.pml.trail _spin_nvr.tmp ./outputs

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
	./$(PAN) $(RUNTIME_FLAGS)

safety_bfs: clean .safety .bfs $(PAN)

safety_dfs: clean .safety $(PAN)

acceptance: clean .ltl $(PAN)

non-progress: clean .np $(PAN)

.PHONY: trail trail_full trail_ltl clean distclean
trail:
	$(SPIN) $(TRAIL_FLAGS) $(TARGET_PATH)

trail_full: .trail.full trail

trail_ltl: .trail.full .trail.ltl trail

clean:
	rm -rf $(PAN)*

distclean: clean
	rm -rf *.pml.trail _spin_nvr.tmp ./outputs

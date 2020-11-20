#------------------------------------------------------------------------------------
# Copyright (C) Amazon
#------------------------------------------------------------------------------------

EXE = p256

SRCDIR = ./src
BUILDDIR = ./build


CFLAGS = -I$(SRCDIR) -std=c11 -MMD
CFLAGS += -Wall -Wextra -Wpedantic
CFLAGS += -Werror -Wshadow -Wconversion
CFLAGS += -march=armv8.4-a+sve -g -O2

SRC_C := $(wildcard $(SRCDIR)/*.c)
SRC_ASM := $(wildcard $(SRCDIR)/*.S)

OBJ_C := $(patsubst $(SRCDIR)/%.c, $(BUILDDIR)/%.s, $(SRC_C))

.PHONY: all
all: build_directory executable

DEPS := $(OBJ_C:%.s=%.d)

-include $(DEPS)

$(BUILDDIR)/%.s: $(SRCDIR)/%.c
	$(CC) $(CFLAGS) $< -S -fverbose-asm -o $@

.PHONY: build_directory
build_directory:
	@mkdir -pv $(BUILDDIR)

.PHONY: executable
executable: $(OBJ_C) $(SRC_ASM)
	$(CC) $(CFLAGS) $^ -o $(BUILDDIR)/$(EXE)

.PHONY: clean
clean:
	rm -fv $(BUILDDIR)/*.d $(BUILDDIR)/*.s $(BUILDDIR)/$(EXE)

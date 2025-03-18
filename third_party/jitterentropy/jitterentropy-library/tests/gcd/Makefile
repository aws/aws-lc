#
# Copyright (C) 2021 - 2025, Stephan Mueller <smueller@chronox.de>
#

CC		?= gcc
CFLAGS		+= -Wextra -Wall -pedantic -fPIC -O2 -std=gnu18
#Hardening
CFLAGS		+= -D_FORTIFY_SOURCE=2 -fstack-protector-strong -fwrapv --param ssp-buffer-size=4 -fvisibility=hidden -fPIE -Wconversion -Wcast-align -Wmissing-field-initializers -Wshadow -Wswitch-enum

#Optimizations
CFLAGS		+= -flto
LDFLAGS		+= -flto

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
LDFLAGS		+= -Wl,-z,relro,-z,now,--as-needed -pie
endif

NAME		:= gcd

DESTDIR		:=
ETCDIR		:= /etc
BINDIR		:= /bin
SBINDIR		:= /sbin
SHAREDIR	:= /usr/share/keyutils
MANDIR		:= /usr/share/man
MAN1		:= $(MANDIR)/man1
MAN3		:= $(MANDIR)/man3
MAN5		:= $(MANDIR)/man5
MAN7		:= $(MANDIR)/man7
MAN8		:= $(MANDIR)/man8
INCLUDEDIR	:= /usr/include
LN		:= ln
LNS		:= $(LN) -sf
STRIP		?= strip -s

###############################################################################
#
# Define compilation options
#
###############################################################################
INCLUDE_DIRS	:= ../../ ../../src
LIBRARY_DIRS	:=
LIBRARIES	:=

CFLAGS		+= $(foreach includedir,$(INCLUDE_DIRS),-I$(includedir))
LDFLAGS		+= $(foreach librarydir,$(LIBRARY_DIRS),-L$(librarydir))
LDFLAGS		+= $(foreach library,$(LIBRARIES),-l$(library))

###############################################################################
#
# Get version name and cross check
#
###############################################################################
VERFILE    := gcd.c

APPMAJOR   := $(shell grep '^\#define.*MAJVERSION' $(VERFILE) | awk '{print $$3}')
APPMINOR   := $(shell grep '^\#define.*MINVERSION' $(VERFILE) | awk '{print $$3}')
APPPATCH   := $(shell grep '^\#define.*PATCHLEVEL' $(VERFILE) | awk '{print $$3}')
APPVERSION := $(APPMAJOR).$(APPMINOR).$(APPPATCH)

###############################################################################
#
# Guess at the appropriate lib directory and word size
#
###############################################################################
ifeq ($(UNAME_S),Linux)

ifeq ($(origin LIBDIR),undefined)
LIBDIR		:= $(shell ldd /usr/bin/make | grep '\(/libc\.\)' | sed -e 's!.*\(/.*\)/libc[.].*!\1!')
endif
ifeq ($(origin USRLIBDIR),undefined)
USRLIBDIR	:= $(patsubst /lib/%,/usr/lib/%,$(LIBDIR))
endif
BUILDFOR	:= $(shell file /usr/bin/make | sed -e 's!.*ELF \(32\|64\)-bit.*!\1!')-bit

ifeq ($(origin CFLAGS),undefined)
ifeq ($(BUILDFOR),32-bit)
CFLAGS		+= -m32
LIBDIR		:= /lib
USRLIBDIR	:= /usr/lib
else
ifeq ($(BUILDFOR),64-bit)
CFLAGS		+= -m64
LIBDIR		:= /lib64
USRLIBDIR	:= /usr/lib64
endif
endif
endif

else
LIBDIR		:= /lib
USRLIBDIR	:= /usr/lib
endif


###############################################################################
#
# Define files to be compiled
#
###############################################################################
C_SRCS := $(wildcard *.c) ../../src/jitterentropy-gcd.c
C_OBJS := ${C_SRCS:.c=.o}
C_GCOV := ${C_SRCS:.c=.gcda}
C_GCOV += ${C_SRCS:.c=.gcno}
C_GCOV += ${C_SRCS:.c=.gcov}
OBJS := $(C_OBJS)

analyze_srcs = $(filter %.c, $(sort $(C_SRCS)))
analyze_plists = $(analyze_srcs:%.c=%.plist)

.PHONY: all scan install clean cppcheck distclean debug asanaddress asanthread leak gcov

all: $(NAME)

debug: CFLAGS += -g -DDEBUG
debug: DBG-$(NAME)

asanaddress: CFLAGS += -g -DDEBUG -fsanitize=address -fno-omit-frame-pointer
asanaddress: LDFLAGS += -fsanitize=address
asanaddress: DBG-$(NAME)

asanthread: CFLAGS += -g -DDEBUG -fsanitize=thread -fno-omit-frame-pointer
asanthread: LDFLAGS += -fsanitize=thread
asanthread: DBG-$(NAME)

leak: CFLAGS += -g -DDEBUG -fsanitize=leak -fno-omit-frame-pointer
leak: LDFLAGS += -fsanitize=leak
leak: DBG-$(NAME)

# Compile for the use of GCOV
# Usage after compilation: gcov <file>.c
gcov: CFLAGS += -g -DDEBUG -fprofile-arcs -ftest-coverage
gcov: LDFLAGS += -fprofile-arcs
gcov: DBG-$(NAME)

###############################################################################
#
# Build the library
#
##############################################################################

$(NAME): $(OBJS)
	$(CC) -o $(NAME) $(OBJS) $(LDFLAGS)
	$(STRIP) $(NAME)

DBG-$(NAME): $(OBJS)
	$(CC) -g -DDEBUG -o $(NAME) $(OBJS) $(LDFLAGS)

$(analyze_plists): %.plist: %.c
	@echo "  CCSA  " $@
	clang --analyze $(CFLAGS) $< -o $@

scan: $(analyze_plists)

cppcheck:
	cppcheck --force -q --enable=performance --enable=warning --enable=portability *.h *.c ../lib/*.c ../lib/*.h

asm:
	$(foreach b, $(C_SRCS), $(CC) $(CFLAGS) -S -fverbose-asm -o ${b:.c=.s} $(b);)

install:
	install -m 0755 $(NAME) -D -t $(DESTDIR)$(BINDIR)/

###############################################################################
#
# Clean
#
###############################################################################

clean:
	@- $(RM) $(OBJS)
	@- $(RM) $(NAME)
	@- $(RM) $(C_GCOV)
	@- $(RM) *.gcov
	@- $(RM) $(analyze_plists)

distclean: clean

###############################################################################
#
# Show variables
#
###############################################################################
show_vars:
	@echo APPVERSION=$(APPVERSION)
	@echo DESTDIR=$(DESTDIR)
	@echo BINDIR=$(BINDIR)
	@echo LIBDIR=$(LIBDIR)
	@echo USRLIBDIR=$(USRLIBDIR)
	@echo BUILDFOR=$(BUILDFOR)
	@echo NAME=$(NAME)
	@echo LDFLAGS=$(LDFLAGS)
	@echo CFLAGS=$(CFLAGS)

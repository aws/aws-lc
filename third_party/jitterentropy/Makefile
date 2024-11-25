# Compile Noise Source as user space application

CC ?= gcc
#Hardening
ENABLE_STACK_PROTECTOR ?= 1
CFLAGS ?= -fwrapv --param ssp-buffer-size=4 -fvisibility=hidden -fPIE -Wcast-align -Wmissing-field-initializers -Wshadow -Wswitch-enum
CFLAGS +=-Wextra -Wall -pedantic -fPIC -O0 -fwrapv -Wconversion
LDFLAGS +=-Wl,-z,relro,-z,now -lpthread

# Enable internal timer support
CFLAGS += -DJENT_CONF_ENABLE_INTERNAL_TIMER

GCCVERSIONFORMAT := $(shell echo `$(CC) -dumpversion | sed 's/\./\n/g' | wc -l`)
ifeq "$(GCCVERSIONFORMAT)" "3"
  GCC_GTEQ_490 := $(shell expr `$(CC) -dumpversion | sed -e 's/\.\([0-9][0-9]\)/\1/g' -e 's/\.\([0-9]\)/0\1/g' -e 's/^[0-9]\{3,4\}$$/&00/'` \>= 40900)
else
  GCC_GTEQ_490 := $(shell expr `$(CC) -dumpfullversion | sed -e 's/\.\([0-9][0-9]\)/\1/g' -e 's/\.\([0-9]\)/0\1/g' -e 's/^[0-9]\{3,4\}$$/&00/'` \>= 40900)
endif

ifeq "$(ENABLE_STACK_PROTECTOR)" "1"
  ifeq "$(GCC_GTEQ_490)" "1"
    CFLAGS += -fstack-protector-strong
  else
    CFLAGS += -fstack-protector-all
  endif
endif

# Change as necessary
PREFIX := /usr/local
# library target directory (either lib or lib64)
LIBDIR := lib

# include target directory
INCDIR := include
SRCDIR := src

INSTALL_STRIP ?= install -s

NAME := jitterentropy
LIBMAJOR=$(shell cat jitterentropy.h | egrep "define\s+JENT_MAJVERSION" | awk '{print $$3}')
LIBMINOR=$(shell cat jitterentropy.h | egrep "define\s+JENT_MINVERSION" | awk '{print $$3}')
LIBPATCH=$(shell cat jitterentropy.h | egrep "define\s+JENT_PATCHLEVEL" | awk '{print $$3}')
LIBVERSION := $(LIBMAJOR).$(LIBMINOR).$(LIBPATCH)

VPATH := $(SRCDIR)
C_SRCS := $(notdir $(sort $(wildcard $(SRCDIR)/*.c)))
C_OBJS := ${C_SRCS:.c=.o}
OBJS := $(C_OBJS)

analyze_srcs = $(filter %.c, $(sort $(C_SRCS)))
analyze_plists = $(analyze_srcs:%.c=%.plist)

INCLUDE_DIRS := . $(SRCDIR)
LIBRARY_DIRS :=
LIBRARIES := rt

CFLAGS += $(foreach includedir,$(INCLUDE_DIRS),-I$(includedir))
LDFLAGS += $(foreach librarydir,$(LIBRARY_DIRS),-L$(librarydir))
LDFLAGS += $(foreach library,$(LIBRARIES),-l$(library))

.PHONY: all scan install clean distclean check $(NAME) $(NAME)-static

all: $(NAME) $(NAME)-static

lib$(NAME).a: $(OBJS)
	$(AR) rcs lib$(NAME).a $(OBJS)

lib$(NAME).so.$(LIBVERSION): $(OBJS)
	$(CC) -shared -Wl,-soname,lib$(NAME).so.$(LIBMAJOR) -o lib$(NAME).so.$(LIBVERSION) $(OBJS) $(LDFLAGS)

$(NAME)-static: lib$(NAME).a
$(NAME): lib$(NAME).so.$(LIBVERSION)

$(analyze_plists): %.plist: %.c
	@echo "  CCSA  " $@
	clang --analyze $(CFLAGS) $< -o $@

scan: $(analyze_plists)

cppcheck:
	cppcheck --force -q --enable=performance --enable=warning --enable=portability $(shell find * -name \*.h -o -name \*.c)

install: install-man install-shared install-includes

install-man:
	install -d -m 0755 $(DESTDIR)$(PREFIX)/share/man/man3
	install -m 644 doc/$(NAME).3 $(DESTDIR)$(PREFIX)/share/man/man3/
	gzip -n -f -9 $(DESTDIR)$(PREFIX)/share/man/man3/$(NAME).3

install-shared:
	install -d -m 0755 $(DESTDIR)$(PREFIX)/$(LIBDIR)
	$(INSTALL_STRIP) -m 0755 lib$(NAME).so.$(LIBVERSION) $(DESTDIR)$(PREFIX)/$(LIBDIR)/
	$(RM) $(DESTDIR)$(PREFIX)/$(LIBDIR)/lib$(NAME).so.$(LIBMAJOR)
	ln -sf lib$(NAME).so.$(LIBVERSION) $(DESTDIR)$(PREFIX)/$(LIBDIR)/lib$(NAME).so.$(LIBMAJOR)
	ln -sf lib$(NAME).so.$(LIBMAJOR) $(DESTDIR)$(PREFIX)/$(LIBDIR)/lib$(NAME).so

install-includes:
	install -d -m 0755 $(DESTDIR)$(PREFIX)/$(INCDIR)
	install -m 0644 jitterentropy.h $(DESTDIR)$(PREFIX)/$(INCDIR)/
	install -m 0644 jitterentropy-base-user.h $(DESTDIR)$(PREFIX)/$(INCDIR)/

install-static:
	install -d -m 0755 $(DESTDIR)$(PREFIX)/$(LIBDIR)
	install -m 0755 lib$(NAME).a $(DESTDIR)$(PREFIX)/$(LIBDIR)/

clean:
	@- $(RM) $(NAME)
	@- $(RM) $(OBJS)
	@- $(RM) lib$(NAME).so*
	@- $(RM) lib$(NAME).a
	@- $(RM) $(analyze_plists)

distclean: clean

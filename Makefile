# fiwix/Makefile
#
# Copyright 2018-2022, Jordi Sanfeliu. All rights reserved.
# Distributed under the terms of the Fiwix License.
#

TOPDIR := $(shell if [ "$$PWD" != "" ] ; then echo $$PWD ; else pwd ; fi)
INCLUDE = $(TOPDIR)/include

ARCH = -m32
CPU = -march=i386
LANG = -std=c89

CCEXE=gcc
CC = $(CROSS_COMPILE)$(CCEXE) $(ARCH) $(CPU) $(LANG) -D__KERNEL__ $(CONFFLAGS) #-D__DEBUG__
CFLAGS = -I$(INCLUDE) -O2 -fno-pie -fno-common -ffreestanding -Wall -Wstrict-prototypes #-Wextra -Wno-unused-parameter

ifeq ($(CCEXE),gcc)
LD = $(CROSS_COMPILE)ld
LIBGCC := $(shell dirname `$(CC) -print-libgcc-file-name`)
LDFLAGS = -m elf_i386 -nostartfiles -nostdlib -nodefaultlibs -nostdinc
endif

ifeq ($(CCEXE),tcc)
CC += -D__VERSION__=\"tcc\"
LD = $(CROSS_COMPILE)$(CCEXE) $(ARCH)
LDFLAGS = -static -nostdlib -nostdinc
endif


DIRS =	kernel \
	kernel/syscalls \
	mm \
	fs \
	drivers/char \
	drivers/block \
	drivers/pci \
	drivers/video \
	lib

OBJS = 	kernel/*.o \
	kernel/syscalls/*.o \
	mm/*.o \
	fs/*.o \
	fs/ext2/*.o \
	fs/iso9660/*.o \
	fs/minix/*.o \
	fs/pipefs/*.o \
	fs/procfs/*.o \
	drivers/char/*.o \
	drivers/block/*.o \
	drivers/pci/*.o \
	drivers/video/*.o \
	lib/*.o

export CC LD CFLAGS LDFLAGS INCLUDE

all:
	@echo "#define UTS_VERSION \"`date`\"" > include/fiwix/version.h
	@for n in $(DIRS) ; do (cd $$n ; $(MAKE)) || exit ; done
ifeq ($(CCEXE),gcc)
	$(LD) -N -T fiwix.ld $(LDFLAGS) $(OBJS) -L$(LIBGCC) -lgcc -o fiwix
	nm fiwix | sort | gzip -9c > System.map.gz
endif
ifeq ($(CCEXE),tcc)
	$(LD) -Wl,-Ttext=0xC0100000 $(LDFLAGS) $(OBJS) -o fiwix
endif

clean:
	@for n in $(DIRS) ; do (cd $$n ; $(MAKE) clean) ; done
	rm -f *.o fiwix System.map.gz


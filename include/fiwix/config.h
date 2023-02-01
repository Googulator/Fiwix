/*
 * fiwix/include/fiwix/config.h
 *
 * Copyright 2018-2023, Jordi Sanfeliu. All rights reserved.
 * Distributed under the terms of the Fiwix License.
 */

#ifndef _FIWIX_CONFIG_H
#define _FIWIX_CONFIG_H

/* kernel tuning */

#define NR_PROCS		64	/* max. number of processes */
#define NR_CALLOUTS		NR_PROCS	/* max. active callouts */
#define NR_MOUNT_POINTS		8	/* max. number of mounted filesystems */
#define NR_OPENS		1024	/* max. number of opened files */
#define NR_FLOCKS		(NR_PROCS * 5)	/* max. number of flocks */

#define FREE_PAGES_RATIO	5	/* % minimum of free memory pages */
#define BUFFER_PERCENTAGE	100	/* % of memory for buffer cache */
#define BUFFER_HASH_PERCENTAGE	10	/* % of hash buckets relative to the
					   size of the buffer table */
#define NR_BUF_RECLAIM		250	/* buffers reclaimed in a single shot */
#define BUFFER_DIRTY_RATIO	5	/* % of dirty buffers in buffer cache */
#define INODE_PERCENTAGE	1	/* % of memory for the inode table and
					   hash table */
#define INODE_HASH_PERCENTAGE	10	/* % of hash buckets relative to the
					   size of the inode table */

#define MAX_PID_VALUE		32767	/* max. value for PID */
#define SCREENS_LOG		6	/* max. number of screens in console's
					   scroll back */
#define MAX_SPU_NOTICES		10	/* max. number of messages on spurious
					   interrupts */
#define USER_FREE_STACK_PAGES	16	/* number of stack pages usable by a
					   user process */


/* toggle configuration options */

#define CONFIG_PCI
#define CONFIG_PCI_NAMES
#undef CONFIG_SYSCALL_6TH_ARG
#define CONFIG_SYSVIPC
#define CONFIG_LAZY_USER_ADDR_CHECK
#define CONFIG_BGA


/* configuration options to help debug or to test new features */
#define CONFIG_VERBOSE_SEGFAULTS
#undef CONFIG_QEMU_DEBUGCON


#endif /* _FIWIX_CONFIG_H */

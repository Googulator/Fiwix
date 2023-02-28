/*
 * fiwix/kernel/syscalls/madvise.c
 *
 * Copyright 2018, Jordi Sanfeliu. All rights reserved.
 * Distributed under the terms of the Fiwix License.
 */

#include <fiwix/process.h>
#include <fiwix/stdio.h>

int sys_madvise(void *addr, __size_t length, int advice)
{
#ifdef CONFIG_NOT_IMPLEMENTED_WARNING
	printk("(pid %d) sys_madvise: WARNING: madvise not implemented!\n", current->pid);
#endif
	return 0;
}

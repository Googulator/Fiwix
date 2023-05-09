/*
 * fiwix/kernel/syscalls/exit_group.c
 *
 * Copyright 2018-2022, Jordi Sanfeliu. All rights reserved.
 * Distributed under the terms of the Fiwix License.
 */

#include <fiwix/syscalls.h>
#include <fiwix/stdio.h>

int sys_exit_group(int exit_code)
{
#ifdef CONFIG_NOT_IMPLEMENTED_WARNING
	printk("sys_exit_group(pid %d, ppid %d, exit_code %d): WARNING: same implementation as exit.\n", current->pid, current->ppid, exit_code);
#endif
	return sys_exit(exit_code);
}

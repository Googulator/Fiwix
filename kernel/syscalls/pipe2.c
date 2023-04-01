/*
 * fiwix/kernel/syscalls/pipe2.c
 *
 * Copyright 2022, Jordi Sanfeliu. All rights reserved.
 * Distributed under the terms of the Fiwix License.
 */

#include <fiwix/fs.h>
#include <fiwix/filesystems.h>
#include <fiwix/fcntl.h>
#include <fiwix/stat.h>
#include <fiwix/errno.h>
#include <fiwix/stdio.h>

int sys_pipe2(int pipefd[2], int flags)
{
	int rfd, rufd;
	int wfd, wufd;
	struct filesystems *fs;
	struct inode *i;
	int errno;

#ifdef __DEBUG__
	printk("(pid %d) sys_pipe2(flags=0x%x)", current->pid, flags);
#endif /*__DEBUG__ */

	if(!(fs = get_filesystem("pipefs"))) {
		printk("WARNING: %s(): pipefs filesystem is not registered!\n", __FUNCTION__);
		return -EINVAL;
	}
	if((errno = check_user_area(VERIFY_WRITE, pipefd, sizeof(int) * 2))) {
		return errno;
	}
	if(!(i = ialloc(&fs->mp->sb, S_IFIFO))) {
		return -EINVAL;
	}
	if((rfd = get_new_fd(i)) < 0) {
		iput(i);
		return -ENFILE;
	}
	if((wfd = get_new_fd(i)) < 0) {
		release_fd(rfd);
		iput(i);
		return -ENFILE;
	}
	if((rufd = get_new_user_fd(0)) < 0) {
		release_fd(rfd);
		release_fd(wfd);
		iput(i);
		return -EMFILE;
	}
	if((wufd = get_new_user_fd(0)) < 0) {
		release_fd(rfd);
		release_fd(wfd);
		release_user_fd(rufd);
		iput(i);
		return -EMFILE;
	}

	pipefd[0] = rufd;
	pipefd[1] = wufd;
	current->fd[rufd] = rfd;
	current->fd[wufd] = wfd;
	fd_table[rfd].flags = O_RDONLY;
	fd_table[wfd].flags = O_WRONLY;
	if (flags & O_CLOEXEC) {
	    current->fd_flags[rufd] |= FD_CLOEXEC;
	    current->fd_flags[wufd] |= FD_CLOEXEC;
	}
	if (flags & O_NONBLOCK) {
	    fd_table[rfd].flags |= O_NONBLOCK;
	    fd_table[wfd].flags |= O_NONBLOCK;
	}

#ifdef __DEBUG__
	printk(" -> inode=%d, rufd=%d wufd=%d (rfd=%d wfd=%d)\n", i->inode, rufd, wufd, rfd, wfd);
#endif /*__DEBUG__ */

	return 0;
}

/*
 * fiwix/kernel/syscalls/getcwd.c
 *
 * Copyright 2018, Jordi Sanfeliu. All rights reserved.
 * Copyright 2022, Alwin Berger. All rights reserved.
 * Distributed under the terms of the Fiwix License.
 */

#include <fiwix/types.h>
#include <fiwix/fs.h>
#include <fiwix/errno.h>
#include <fiwix/string.h>
#include <fiwix/mm.h>

#ifdef __DEBUG__
#include <fiwix/stdio.h>
#include <fiwix/process.h>
#endif /*__DEBUG__ */

int sys_getcwd(char *buf, __size_t size)
{
	int errno;

#ifdef __DEBUG__
	printk("(pid %d) sys_getcwd(0x%08x, %d)\n", current->pid, (unsigned int)buf, size);
#endif /*__DEBUG__ */

	if((errno = check_user_area(VERIFY_WRITE, buf, size))) {
		return errno;
	}
	/* Buffer self-allocation not supported. */
	if (size==0 || buf==NULL) {
		return -EINVAL;
	}
	/* The shortest possible path is "/". */
	if (size<2) {
		return -ERANGE;
	}
	struct dirent *dirent_buf;
	struct dirent *d_ptr;
	struct inode *cur = current->pwd;
	struct inode *up = cur;
	struct inode *tmp_ino = NULL;
	int tmp_fd, done;
	int namelength, bytes_read;
	__size_t marker = size-2;	/* Reserve '\0' at the end. */
	buf[size-1] = 0;
	__size_t x;

	if(cur == current->root) {
		/* This case needs special handling, otherwise the loop skips over root. */
		buf[0]='/';
		buf[1]='\0';
		return (unsigned int)buf;
	}
	if(!(dirent_buf = (void *)kmalloc())) {
		return -ENOMEM;
	}

	do {
		if((errno = parse_namei("..", cur, &up, 0, FOLLOW_LINKS))) {
			if (cur != current->pwd) {
				iput(cur);
			}
			kfree((unsigned int)dirent_buf);
			return errno;
		}
		if((tmp_fd = get_new_fd(up)) < 0) {
			iput(up);
			if (cur != current->pwd) {
				iput(cur);
			}
			kfree((unsigned int)dirent_buf);
			return tmp_fd;
		}
		do {
			done = 0;
			bytes_read = up->fsop->readdir(up, &fd_table[tmp_fd], dirent_buf, PAGE_SIZE);
			if (bytes_read < 0) {
				release_fd(tmp_fd);
				iput(up);
				if (cur != current->pwd) {
					iput(cur);
				}
				kfree((unsigned int)dirent_buf);
				return bytes_read;
			}
			d_ptr = dirent_buf;
			while((void *) d_ptr < ((void *) dirent_buf + bytes_read)) {
				if((errno = parse_namei(d_ptr->d_name, up, &tmp_ino, 0, FOLLOW_LINKS))) {
					/* Keep going if sibling dirents fail. */
					break;
				}
				if(tmp_ino->inode == cur->inode) {
					if(strcmp("..", d_ptr->d_name)) {
						namelength = strlen(d_ptr->d_name);
						if (marker < namelength+1) {
							release_fd(tmp_fd);
							iput(up);
							if (cur != current->pwd) {
								iput(cur);
							}
							kfree((unsigned int)dirent_buf);
							return -ERANGE;
						}
						while(--namelength >= 0) {
							buf[marker--] = d_ptr->d_name[namelength];
						}
						buf[marker--] = '/';
						iput(tmp_ino);
						done = 1;
						break;
					}
				}
				d_ptr = (struct dirent *) ((void *)d_ptr + d_ptr->d_reclen);
				iput(tmp_ino);
			}
		} while(bytes_read!=0 && !done);

		release_fd(tmp_fd);
		if(!done) {
			/* Parent dir was fully read, child still not found. */
			iput(up);
			if (cur != current->pwd) {
				iput(cur);
			}
			kfree((unsigned int)dirent_buf);
			return -ENOENT;
		}
		if (cur != current->pwd) {
			iput(cur);
		}
		cur = up;
	} while(cur != current->root);

	kfree((unsigned int)dirent_buf);
	iput(cur);
	/* Move the String to the start of the buffer. */
	for (x = ++marker; x < size; x++) {
		buf[x-marker] = buf[x];
	}
	return (unsigned int)buf;
}

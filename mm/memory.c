/*
 * fiwix/mm/memory.c
 *
 * Copyright 2018-2023, Jordi Sanfeliu. All rights reserved.
 * Distributed under the terms of the Fiwix License.
 */

#include <fiwix/kernel.h>
#include <fiwix/asm.h>
#include <fiwix/mm.h>
#include <fiwix/mman.h>
#include <fiwix/bios.h>
#include <fiwix/ramdisk.h>
#include <fiwix/process.h>
#include <fiwix/buffer.h>
#include <fiwix/fs.h>
#include <fiwix/stdio.h>
#include <fiwix/string.h>

#define KERNEL_TEXT_SIZE	((int)_etext - (PAGE_OFFSET + KERNEL_ENTRY_ADDR))
#define KERNEL_DATA_SIZE	((int)_edata - (int)_etext)
#define KERNEL_BSS_SIZE		((int)_end - (int)_edata)

#define PGDIR_4MB_ADDR		0x50000
#define PGDIR_INITIAL_4MB_UNITS	1

unsigned int *kpage_dir;

unsigned int proc_table_size = 0;

unsigned int buffer_table_size = 0;
unsigned int buffer_hash_table_size = 0;

unsigned int inode_table_size = 0;
unsigned int inode_hash_table_size = 0;

unsigned int fd_table_size = 0;

unsigned int page_table_size = 0;
unsigned int page_hash_table_size = 0;

void setup_more_minmem(void);


unsigned int map_kaddr(unsigned int from, unsigned int to, unsigned int addr, int flags)
{
	unsigned int n;
	unsigned int *pgtbl;
	unsigned int pde, pte;

	for(n = from; n < to; n += PAGE_SIZE) {
		pde = GET_PGDIR(n);
		pte = GET_PGTBL(n);
		if(!(kpage_dir[pde] & ~PAGE_MASK)) {
			kpage_dir[pde] = addr | flags;
			memset_b((void *)addr, 0, PAGE_SIZE);
			addr += PAGE_SIZE;
		}
		pgtbl = (unsigned int *)(kpage_dir[pde] & PAGE_MASK);
		pgtbl[pte] = n | flags;
	}

	return addr;
}

void bss_init(void)
{
	memset_b((void *)((int)_edata), 0, KERNEL_BSS_SIZE);
}

/*
 * This function creates a minimal Page Directory covering only the first 4MB
 * of physical memory. Just enough to boot the kernel.
 * (it returns the address to be used by the CR3 register)
 */
unsigned int setup_minmem(void)
{
	int n;
	unsigned int addr;
	unsigned int *pgtbl;
	short int pd, mb4;

	mb4 = PGDIR_INITIAL_4MB_UNITS;
	addr = PAGE_OFFSET + PGDIR_4MB_ADDR;

	kpage_dir = (unsigned int *)addr;
	memset_b(kpage_dir, 0, PAGE_SIZE);

	addr += PAGE_SIZE;
	pgtbl = (unsigned int *)addr;
	memset_b(pgtbl, 0, PAGE_SIZE * mb4);

	for(n = 0; n < (1024 * mb4); n++) {
		pgtbl[n] = (n << PAGE_SHIFT) | PAGE_PRESENT | PAGE_RW;
		if(!(n % 1024)) {
			pd = n / 1024;
			kpage_dir[pd] = (unsigned int)(addr + (PAGE_SIZE * pd) + 0x40000000) | PAGE_PRESENT | PAGE_RW;
			kpage_dir[GET_PGDIR(PAGE_OFFSET) + pd] = (unsigned int)(addr + (PAGE_SIZE * pd) + 0x40000000) | PAGE_PRESENT | PAGE_RW;
		}
	}
	return (unsigned int)kpage_dir + 0x40000000;
}

void setup_more_minmem()
{
	int n;
	unsigned int addr;
	unsigned int * kpage_dir, * kpage_table;
	short int pd, mb4;

	addr = PAGE_OFFSET + PGDIR_4MB_ADDR;
	kpage_dir = (unsigned int *)addr;

	addr += PAGE_SIZE;
	kpage_table = (unsigned int *)addr;

	mb4 = ((_last_data_addr + MAX_PGTABLE_SIZE) / 0x400000) + 1;
	for(n = 0; n < (1024 * mb4); n++) {
		kpage_table[n] = (n << PAGE_SHIFT) | PAGE_PRESENT | PAGE_RW;
		if(!(n % 1024)) {
			pd = n / 1024;
			kpage_dir[pd] = (unsigned int)(addr + (PAGE_SIZE * pd) + 0x40000000) | PAGE_PRESENT | PAGE_RW;
			kpage_dir[GET_PGDIR(PAGE_OFFSET) + pd] = (unsigned int)(addr + (PAGE_SIZE * pd) + 0x40000000) | PAGE_PRESENT | PAGE_RW;
		}
	}
	return;
}

/* returns the mapped address of a virtual address */
unsigned int get_mapped_addr(struct proc *p, unsigned int addr)
{
	unsigned int *pgdir, *pgtbl;
	unsigned int pde, pte;

	pgdir = (unsigned int *)P2V(p->tss.cr3);
	pde = GET_PGDIR(addr);
	pte = GET_PGTBL(addr);
	pgtbl = (unsigned int *)P2V((pgdir[pde] & PAGE_MASK));
	return pgtbl[pte];
}

int clone_pages(struct proc *child)
{
	unsigned int *src_pgdir, *dst_pgdir;
	unsigned int *src_pgtbl, *dst_pgtbl;
	unsigned int pde, pte;
	unsigned int p_addr, c_addr;
	unsigned int n, pages;
	struct page *pg;
	struct vma *vma;

	src_pgdir = (unsigned int *)P2V(current->tss.cr3);
	dst_pgdir = (unsigned int *)P2V(child->tss.cr3);
	vma = current->vma_table;
	pages = 0;

	while(vma) {
		if(vma->flags & MAP_SHARED) {
			vma = vma->next;
			continue;
		}
		for(n = vma->start; n < vma->end; n += PAGE_SIZE) {
			pde = GET_PGDIR(n);
			pte = GET_PGTBL(n);
			if(src_pgdir[pde] & PAGE_PRESENT) {
				src_pgtbl = (unsigned int *)P2V((src_pgdir[pde] & PAGE_MASK));
				if(!(dst_pgdir[pde] & PAGE_PRESENT)) {
					if(!(c_addr = kmalloc())) {
						printk("%s(): returning 0!\n", __FUNCTION__);
						return 0;
					}
					current->rss++;
					pages++;
					dst_pgdir[pde] = V2P(c_addr) | PAGE_PRESENT | PAGE_RW | PAGE_USER;
					memset_b((void *)c_addr, 0, PAGE_SIZE);
				}
				dst_pgtbl = (unsigned int *)P2V((dst_pgdir[pde] & PAGE_MASK));
				if(src_pgtbl[pte] & PAGE_PRESENT) {
					p_addr = src_pgtbl[pte] >> PAGE_SHIFT;
					pg = &page_table[p_addr];
					if(pg->flags & PAGE_RESERVED) {
						continue;
					}
					src_pgtbl[pte] &= ~PAGE_RW;
					/* mark write-only pages as copy-on-write */
					if(vma->prot & PROT_WRITE) {
						pg->flags |= PAGE_COW;
					}
					dst_pgtbl[pte] = src_pgtbl[pte];
					if(!is_valid_page((dst_pgtbl[pte] & PAGE_MASK) >> PAGE_SHIFT)) {
						PANIC("%s: missing page %d during copy-on-write process.\n", __FUNCTION__, (dst_pgtbl[pte] & PAGE_MASK) >> PAGE_SHIFT);
					}
					pg = &page_table[(dst_pgtbl[pte] & PAGE_MASK) >> PAGE_SHIFT];
					pg->count++;
				}
			}
		}
		vma = vma->next;
	}
	return pages;
}

int free_page_tables(struct proc *p)
{
	unsigned int *pgdir;
	int n, count;

	pgdir = (unsigned int *)P2V(p->tss.cr3);
	for(n = 0, count = 0; n < PD_ENTRIES; n++) {
		if((pgdir[n] & (PAGE_PRESENT | PAGE_RW | PAGE_USER)) == (PAGE_PRESENT | PAGE_RW | PAGE_USER)) {
			kfree(P2V(pgdir[n]) & PAGE_MASK);
			pgdir[n] = 0;
			count++;
		}
	}
	return count;
}

unsigned int map_page(struct proc *p, unsigned int vaddr, unsigned int addr, unsigned int prot)
{
	unsigned int *pgdir, *pgtbl;
	unsigned int newaddr;
	int pde, pte;

	pgdir = (unsigned int *)P2V(p->tss.cr3);
	pde = GET_PGDIR(vaddr);
	pte = GET_PGTBL(vaddr);

	if(!(pgdir[pde] & PAGE_PRESENT)) {	/* allocating page table */
		if(!(newaddr = kmalloc())) {
			return 0;
		}
		p->rss++;
		pgdir[pde] = V2P(newaddr) | PAGE_PRESENT | PAGE_RW | PAGE_USER;
		memset_b((void *)newaddr, 0, PAGE_SIZE);
	}
	pgtbl = (unsigned int *)P2V((pgdir[pde] & PAGE_MASK));
	if(!(pgtbl[pte] & PAGE_PRESENT)) {	/* allocating page */
		if(!addr) {
			if(!(addr = kmalloc())) {
				return 0;
			}
			addr = V2P(addr);
			p->rss++;
		}
		pgtbl[pte] = addr | PAGE_PRESENT | PAGE_USER;
	}
	if(prot & PROT_WRITE) {
		pgtbl[pte] |= PAGE_RW;
	}
	return P2V(addr);
}

int unmap_page(unsigned int vaddr)
{
	unsigned int *pgdir, *pgtbl;
	unsigned int addr;
	int pde, pte;

	pgdir = (unsigned int *)P2V(current->tss.cr3);
	pde = GET_PGDIR(vaddr);
	pte = GET_PGTBL(vaddr);
	if(!(pgdir[pde] & PAGE_PRESENT)) {
		printk("WARNING: %s(): trying to unmap an unallocated pde '0x%08x'\n", __FUNCTION__, vaddr);
		return 1;
	}

	pgtbl = (unsigned int *)P2V((pgdir[pde] & PAGE_MASK));
	if(!(pgtbl[pte] & PAGE_PRESENT)) {
		printk("WARNING: %s(): trying to unmap an unallocated page '0x%08x'\n", __FUNCTION__, vaddr);
		return 1;
	}

	addr = pgtbl[pte] & PAGE_MASK;
	pgtbl[pte] = 0;
	kfree(P2V(addr));
	current->rss--;
	return 0;
}

void mem_init(void)
{
	unsigned int sizek;
	unsigned int physical_page_tables;
	unsigned int physical_memory;
	unsigned int *pgtbl;
	int n, pages;

	physical_page_tables = (kstat.physical_pages / 1024) + ((kstat.physical_pages % 1024) ? 1 : 0);
	physical_memory = (kstat.physical_pages << PAGE_SHIFT);	/* in bytes */

	/* Page Directory will be aligned to the next page */
	_last_data_addr = PAGE_ALIGN(_last_data_addr);

	if(kparm_ramdisksize > 0 && kparm_initrdsize > kparm_ramdisksize * 1024) {
		printk("WARNING: initrd ignored, size %u is larger than ramdisk size %u.\n", kparm_initrdsize, kparm_ramdisksize);
		ramdisk_table[0].addr = 0;
	}

	if (_last_data_addr + MAX_PGTABLE_SIZE > PGDIR_INITIAL_4MB_UNITS * 0x400000) {
		setup_more_minmem();
	}

	kpage_dir = (unsigned int *)_last_data_addr;
	memset_b(kpage_dir, 0, PAGE_SIZE);
	_last_data_addr += PAGE_SIZE;

	/* Page Tables */
	pgtbl = (unsigned int *)_last_data_addr;
	memset_b(pgtbl, 0, physical_page_tables * PAGE_SIZE);
	_last_data_addr += physical_page_tables * PAGE_SIZE;

	/* Page Directory and Page Tables initialization */
	for(n = 0; n < kstat.physical_pages; n++) {
		pgtbl[n] = (n << PAGE_SHIFT) | PAGE_PRESENT | PAGE_RW;
		if(!(n % 1024)) {
			kpage_dir[GET_PGDIR(PAGE_OFFSET) + (n / 1024)] = (unsigned int)&pgtbl[n] | PAGE_PRESENT | PAGE_RW;
		}
	}

	_last_data_addr = map_kaddr(0xA0000, 0xA0000 + video.memsize, _last_data_addr, PAGE_PRESENT | PAGE_RW);

	/*
	 * FIXME:
	 * Why do I need to reserve the page tables for video framebuffer
	 * here, instead of using kmalloc() in fbcon_init() and bga_init()?
	 */
	video.pgtbl_addr = _last_data_addr;
	if(video.flags & VPF_VESAFB) {
		/* reserve 4 page tables (16MB) */
		_last_data_addr += (PAGE_SIZE * 4);
	}

	_last_data_addr = map_kaddr(KERNEL_ENTRY_ADDR, _last_data_addr, _last_data_addr, PAGE_PRESENT | PAGE_RW);
	activate_kpage_dir();

	/* since Page Directory is now activated we can use virtual addresses */
	_last_data_addr = P2V(_last_data_addr);


	/* reserve memory space for proc_table[NR_PROCS] */
	proc_table_size = PAGE_ALIGN(sizeof(struct proc) * NR_PROCS);
	if(!addr_in_bios_map(V2P(_last_data_addr) + proc_table_size)) {
		PANIC("Not enough memory for proc_table.\n");
	}
	proc_table = (struct proc *)_last_data_addr;
	_last_data_addr += proc_table_size;


	/* reserve memory space for buffer_table */
	buffer_table_size = (kstat.physical_pages * BUFFER_PERCENTAGE) / 100;
	buffer_table_size *= sizeof(struct buffer);
	pages = buffer_table_size >> PAGE_SHIFT;
	buffer_table_size = !pages ? 4096 : pages << PAGE_SHIFT;

	/* reserve memory space for buffer_hash_table */
	kstat.max_buffers = buffer_table_size / sizeof(struct buffer);
	n = (kstat.max_buffers * BUFFER_HASH_PERCENTAGE) / 100;
	n = MAX(n, 10);	/* 10 buffer hashes as minimum */
	/* buffer_hash_table is an array of pointers */
	pages = ((n * sizeof(unsigned int)) / PAGE_SIZE) + 1;
	buffer_hash_table_size = pages << PAGE_SHIFT;
	if(!addr_in_bios_map(V2P(_last_data_addr) + buffer_hash_table_size)) {
		PANIC("Not enough memory for buffer_hash_table.\n");
	}
	buffer_hash_table = (struct buffer **)_last_data_addr;
	_last_data_addr += buffer_hash_table_size;


	/* reserve memory space for inode_hash_table */
	sizek = physical_memory / 1024;	/* this helps to avoid overflow */
	inode_table_size = (sizek * INODE_PERCENTAGE) / 100;
	inode_table_size *= 1024;
	pages = inode_table_size >> PAGE_SHIFT;
	inode_table_size = pages << PAGE_SHIFT;

	kstat.max_inodes = inode_table_size / sizeof(struct inode);
	n = (kstat.max_inodes * INODE_HASH_PERCENTAGE) / 100;
	n = MAX(n, 10);	/* 10 inode hash buckets as minimum */
	/* inode_hash_table is an array of pointers */
	pages = ((n * sizeof(unsigned int)) / PAGE_SIZE) + 1;
	inode_hash_table_size = pages << PAGE_SHIFT;
	if(!addr_in_bios_map(V2P(_last_data_addr) + inode_hash_table_size)) {
		PANIC("Not enough memory for inode_hash_table.\n");
	}
	inode_hash_table = (struct inode **)_last_data_addr;
	_last_data_addr += inode_hash_table_size;


	/* reserve memory space for fd_table[NR_OPENS] */
	fd_table_size = PAGE_ALIGN(sizeof(struct fd) * NR_OPENS);
	if(!addr_in_bios_map(V2P(_last_data_addr) + fd_table_size)) {
		PANIC("Not enough memory for fd_table.\n");
	}
	fd_table = (struct fd *)_last_data_addr;
	_last_data_addr += fd_table_size;


	/* reserve memory space for RAMdisk(s) */
	if(kparm_ramdisksize > 0) {
		/*
		 * If the 'initrd=' parameter was supplied, then the first
		 * ramdisk device was already assigned to the initial ramdisk
		 * image.
		 */
		if(ramdisk_table[0].addr) {
			n = 1;
		} else {
			n = 0;
		}
		for(; n < RAMDISK_MINORS; n++) {
			if(!addr_in_bios_map(V2P(_last_data_addr) + (kparm_ramdisksize * 1024))) {
				printk("WARNING: RAMdisk device disabled (not enough physical memory).\n");
				break;
			}
			ramdisk_table[n].addr = (char *)_last_data_addr;
			_last_data_addr += kparm_ramdisksize * 1024;
		}
	}

	/*
	 * FIXME: this is ugly!
	 * It should go in console_init() once we have a proper kernel memory/page management.
	 */
	#include <fiwix/console.h>
	for(n = 1; n <= NR_VCONSOLES; n++) {
		vc_screen[n] = (short int *)_last_data_addr;
		_last_data_addr += (video.columns * video.lines * 2);
	}
	/*
	 * FIXME: this is ugly!
	 * It should go in console_init() once we have a proper kernel memory/page management.
	 */
	vcbuf = (short int *)_last_data_addr;
	_last_data_addr += (video.columns * video.lines * SCREENS_LOG * 2 * sizeof(short int));


	/* the last one must be the page_table structure */
	page_hash_table_size = 1 * PAGE_SIZE;	/* only 1 page size */
	if(!addr_in_bios_map(V2P(_last_data_addr) + page_hash_table_size)) {
		PANIC("Not enough memory for page_hash_table.\n");
	}
	page_hash_table = (struct page **)_last_data_addr;
	_last_data_addr += page_hash_table_size;

	page_table_size = PAGE_ALIGN(kstat.physical_pages * sizeof(struct page));
	if(!addr_in_bios_map(V2P(_last_data_addr) + page_table_size)) {
		PANIC("Not enough memory for page_table.\n");
	}
	page_table = (struct page *)_last_data_addr;
	_last_data_addr += page_table_size;

	page_init(kstat.physical_pages);
	buddy_low_init();
}

void mem_stats(void)
{
	printk("\n");
	printk("memory: total=%dKB, user=%dKB, kernel=%dKB, reserved=%dKB\n", kstat.physical_pages << 2, kstat.total_mem_pages << 2, kstat.kernel_reserved, kstat.physical_reserved);
	printk("kernel: text=%dKB, data=%dKB, bss=%dKB, i/o buffers=%d, inodes=%d\n\n", KERNEL_TEXT_SIZE / 1024, KERNEL_DATA_SIZE / 1024, KERNEL_BSS_SIZE / 1024, buffer_table_size / sizeof(struct buffer), inode_table_size / sizeof(struct inode));
}

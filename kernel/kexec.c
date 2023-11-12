/*
 * fiwix/kernel/kexec.c
 *
 * Copyright 2023, Jordi Sanfeliu. All rights reserved.
 * Copyright (C) 2019-2023 mintsuki and contributors.
 * Copyright 2023, Richard Masters.
 * Distributed under the terms of the Fiwix License.
 */

#include <fiwix/asm.h>
#include <fiwix/kernel.h>
#include <fiwix/system.h>
#include <fiwix/config.h>
#include <fiwix/kexec.h>
#include <fiwix/segments.h>
#include <fiwix/mm.h>
#include <fiwix/sched.h>
#include <fiwix/ramdisk.h>
#include <fiwix/multiboot1.h>
#include <fiwix/bios.h>
#include <fiwix/i386elf.h>
#include <fiwix/stdio.h>
#include <fiwix/string.h>

#ifdef CONFIG_KEXEC

int kexec_proto;
int kexec_size;
char kexec_cmdline[NAME_MAX + 1];

static void _memcpy_b(void *dest, const void *src, unsigned int count)
{
	unsigned char *d, *s;

	s = (unsigned char *)src;
	d = (unsigned char *)dest;
	while(count--) {
		*d = *s;
		d++;
		s++;
	}
}

static void _memset_b(void *dest, unsigned char value, unsigned int count)
{
	unsigned char *d;

	d = (unsigned char *)dest;
	while(count--) {
		*d = 0;
		d++;
	}
}

static void multiboot1_trampoline(unsigned int ramdisk_addr, unsigned int kernel_addr, int size, struct multiboot_info *info)
{
	struct elf32_phdr *elf32_ph;
	struct elf32_hdr *elf32_h;
	unsigned int start, length, offset;
	unsigned int entry_addr;

	struct gate_desc idt[64];
	struct desc_r idtr = {
		sizeof(idt) - 1,
		(unsigned int)&idt
	};

	struct seg_desc gdt[3];
	struct desc_r gdtr = {
		sizeof(gdt) - 1,
		(unsigned int)&gdt
	};

	int n, cr0;


	CLI();

	/* invalidate IDT */
	_memset_b(&idt, 0, sizeof(idt));
	__asm__ __volatile__ (
		"lidt %0\n\t"
		: /* no output */
		: "m"(idtr)
	);

	/* configure a new flat GDT */
	gdt[0].sd_lolimit = 0;
	gdt[0].sd_lobase = 0;
	gdt[0].sd_loflags = 0;
	gdt[0].sd_hilimit = 0;
	gdt[0].sd_hiflags = 0;
	gdt[0].sd_hibase = 0;

	gdt[1].sd_lolimit = 0xFFFF;
	gdt[1].sd_lobase = 0x00000000 & 0xFFFFFF;
	gdt[1].sd_loflags = SD_CODE | SD_CD | SD_DPL0 | SD_PRESENT;
	gdt[1].sd_hilimit = (0xFFFFFFFF >> 16) & 0x0F;
	gdt[1].sd_hiflags = SD_OPSIZE32 | SD_PAGE4KB;
	gdt[1].sd_hibase = (0x00000000 >> 24) & 0xFF;

	gdt[2].sd_lolimit = 0xFFFF;
	gdt[2].sd_lobase = 0x00000000 & 0xFFFFFF;
	gdt[2].sd_loflags = SD_DATA | SD_CD | SD_DPL0 | SD_PRESENT;
	gdt[2].sd_hilimit = (0xFFFFFFFF >> 16) & 0x0F;
	gdt[2].sd_hiflags = SD_OPSIZE32 | SD_PAGE4KB;
	gdt[2].sd_hibase = (0x00000000 >> 24) & 0xFF;
	__asm__ __volatile__ (
		"lgdt %0\n\t"
		: /* no output */
		: "m"(gdtr)
	);

	/* disable paging and others */
	cr0 = 0x11;	/* preserve ET & PE */
	__asm__ __volatile__(
		"mov	%0, %%cr0"
		: /* no output */
		: "r"(cr0)
	);

	/* flush TLB (needed?) */
	__asm__ __volatile__(
		"xorl	%%eax, %%eax\n\t"
		"movl	%%eax, %%cr3\n\t"
		: /* no output */
		: /* no input */
		: "eax"	/* clobbered registers */
	);

	/*
	 * Clear memory. This is intended to avoid unexpected results if the
	 * new kernel guesses its uninitialized variables are zeroed.
	 */
	_memset_b(0x0, 0, KEXEC_BOOT_ADDR);
	_memset_b((void *)0x100000, 0, ramdisk_addr - 0x100000);

	/* install the kernel previously stored in RAMdisk by the user */
	elf32_h = (struct elf32_hdr *)ramdisk_addr;
	entry_addr = elf32_h->e_entry;

	for(n = 0; n < elf32_h->e_phnum; n++) {
		elf32_ph = (struct elf32_phdr *)(ramdisk_addr + elf32_h->e_phoff + (sizeof(struct elf32_phdr) * n));
		if(elf32_ph->p_type == PT_LOAD) {
			start = elf32_ph->p_paddr;
			length = elf32_ph->p_filesz;
			offset = elf32_ph->p_offset;
			_memcpy_b((void *)start, (unsigned char *)(ramdisk_addr + offset), length);
		}
	}

	/* flush TLB (needed?) */
	__asm__ __volatile__(
		"xorl	%%eax, %%eax\n\t"
		"movl	%%eax, %%cr3\n\t"
		: /* no output */
		: /* no input */
		: "eax"	/* clobbered registers */
	);

	/* load all the segment registers with the kernel data segment value */
	__asm__ __volatile__(
		"movw	$0x10, %%ax\n\t"
		"movw	%%ax, %%ds\n\t"
		"movw	%%ax, %%es\n\t"
		"movw	%%ax, %%fs\n\t"
		"movw	%%ax, %%gs\n\t"
		"movw	%%ax, %%ss\n\t"
		: /* no output */
		: /* no input */
		: "eax"	/* clobbered registers */
	);

	/* Multiboot 1 */
#ifdef __TINYC__
	unsigned int multiboot_magic = MULTIBOOT_BOOTLOADER_MAGIC;
	__asm__ __volatile__(
		"movl	%0, %%eax\n\t"
		"movl	%1, %%ebx\n\t"
		: /* no output */
		: "r"(multiboot_magic), "r"((unsigned int)info)
	);
#else
	__asm__ __volatile__(
		"movl	%0, %%eax\n\t"
		"movl	%1, %%ebx\n\t"
		: /* no output */
		: "eax"(MULTIBOOT_BOOTLOADER_MAGIC), "ebx"((unsigned int)info)
	);
#endif

	/*
	 * This jumps to the kernel entry address.
	 *
	 * Formerly: ljmp $0x08, $entry_addr
	 */
	__asm__ __volatile__(
		"pushw	$0x08\n\t"
		"pushl	%0\n\t"
		"ljmp	*(%%esp)\n\t"
		: /* no output */
		: "c"(entry_addr)
	);

	/* not reached */
}

void kexec_multiboot1(void)
{
	unsigned int *esp, ramdisk_addr;
	struct proc *idle, *prev;
	struct multiboot_info *info;
	struct multiboot_mmap_entry *map, *map_orig;
	struct elf32_hdr *elf32_h;
	char *cmdline;
	char *boot_loader_name;
	int n, nmaps;

	CLI();

	ramdisk_addr = (unsigned int)ramdisk_table[ramdisk_minors - 1].addr;
	elf32_h = (struct elf32_hdr *)ramdisk_addr;
	if(check_elf(elf32_h)) {
		printk("WARNING: %s(): unrecognized i386 binary ELF.\n", __FUNCTION__);
		return;
	}

	memcpy_b((void *)KEXEC_BOOT_ADDR, multiboot1_trampoline, PAGE_SIZE);

	/* the IDLE process will do the job */
	idle = &proc_table[IDLE];
	idle->tss.eip = (unsigned int)KEXEC_BOOT_ADDR;

	/* stack starts at the end of the page */
	esp = (unsigned int *)(KEXEC_BOOT_ADDR + PAGE_SIZE - 4);

	/* space reserved for the cmdline string (256 bytes) */
	esp -= 256 / sizeof(unsigned int);
	cmdline = (char *)esp;
	sprintk(cmdline, "%s %s", UTS_SYSNAME, kexec_cmdline);

	/* space reserved for the boot_loader_name string (16 bytes) */
	esp -= 16 / sizeof(unsigned int);
	boot_loader_name = (char *)esp;
	sprintk(boot_loader_name, "Fiwix kexec");

	/* space reserved for the memory map structure */
	nmaps = 0;
	while(bios_mem_map[nmaps].to) {
		nmaps++;
	}
	esp -= sizeof(struct multiboot_mmap_entry) * nmaps;
	map_orig = map = (struct multiboot_mmap_entry *)esp;
	/* setup the memory map */
	for(n = 0; n < nmaps; n++) {
		map->size = sizeof(struct multiboot_mmap_entry) - sizeof(map->size);
		map->addr = bios_mem_map[n].from_hi;
		map->addr = map->addr << 32 | bios_mem_map[n].from;
		map->len = bios_mem_map[n].to_hi;
		map->len = map->len << 32 | bios_mem_map[n].to
		map->len -= map->addr - 1;
		map->type = bios_mem_map[n].type;
		map++;
	}

	/* space reserved for the multiboot_info structure */
	esp -= sizeof(struct multiboot_info) / sizeof(unsigned int);
	memset_b(esp, 0, sizeof(struct multiboot_info));
	info = (struct multiboot_info *)esp;

	/* setup Multiboot structure */
	info->flags = MULTIBOOT_INFO_MEMORY;
	info->mem_lower = kparm_memsize;
	info->mem_upper = kparm_extmemsize;
	info->flags |= MULTIBOOT_INFO_CMDLINE;
	info->cmdline = (unsigned int)cmdline;
	info->flags |= MULTIBOOT_INFO_BOOT_LOADER_NAME;
	info->boot_loader_name = (unsigned int)boot_loader_name;
	info->flags |= MULTIBOOT_INFO_MEM_MAP;
	info->mmap_length = sizeof(struct multiboot_mmap_entry) * nmaps;
	info->mmap_addr = (unsigned int)map_orig;
	esp--;

	/* now put the four parameters into the stack */
	*esp = (unsigned int)info;
	esp--;
	*esp = kexec_size * 1024;
	esp--;
	*esp = KERNEL_ADDR;
	esp--;
	*esp = V2P(ramdisk_addr);
	esp--;
	idle->tss.esp = (unsigned int)esp;

	printk("%s(): jumping to multiboot1_trampoline() ...\n", __FUNCTION__);
	prev = current;
	set_tss(idle);
	do_switch(&prev->tss.esp, &prev->tss.eip, idle->tss.esp, idle->tss.eip, idle->tss.cr3, TSS);
}

/*
 The following definitions and struct were copied and adapted from Linux
 kernel headers released under GPL-2.0 WITH Linux-syscall-note
 allowing their inclusion in non GPL compliant code.
*/

#define EDD_MBR_SIG_MAX 16
#define E820_MAX_ENTRIES_ZEROPAGE 128
#define EDDMAXNR 6

struct setup_header {
	uint8_t	 setup_sects;
	uint16_t root_flags;
	uint32_t syssize;
	uint16_t ram_size;
	uint16_t vid_mode;
	uint16_t root_dev;
	uint16_t boot_flag;
	uint16_t jump;
	uint32_t header;
	uint16_t version;
	uint32_t realmode_swtch;
	uint16_t start_sys_seg;
	uint16_t kernel_version;
	uint8_t  type_of_loader;
	uint8_t  loadflags;
	uint16_t setup_move_size;
	uint32_t code32_start;
	uint32_t ramdisk_image;
	uint32_t ramdisk_size;
	uint32_t bootsect_kludge;
	uint16_t heap_end_ptr;
	uint8_t  ext_loader_ver;
	uint8_t  ext_loader_type;
	uint32_t cmd_line_ptr;
	uint32_t initrd_addr_max;
	uint32_t kernel_alignment;
	uint8_t  relocatable_kernel;
	uint8_t  min_alignment;
	uint16_t xloadflags;
	uint32_t cmdline_size;
	uint32_t hardware_subarch;
	uint64_t hardware_subarch_data;
	uint32_t payload_offset;
	uint32_t payload_length;
	uint64_t setup_data;
	uint64_t pref_address;
	uint32_t init_size;
	uint32_t handover_offset;
	uint32_t kernel_info_offset;
} __attribute__((packed));

struct screen_info {
	uint8_t  orig_x;             /* 0x00 */
	uint8_t  orig_y;             /* 0x01 */
	uint16_t ext_mem_k;          /* 0x02 */
	uint16_t orig_video_page;    /* 0x04 */
	uint8_t  orig_video_mode;    /* 0x06 */
	uint8_t  orig_video_cols;    /* 0x07 */
	uint8_t  flags;              /* 0x08 */
	uint8_t  unused2;            /* 0x09 */
	uint16_t orig_video_ega_bx;  /* 0x0a */
	uint16_t unused3;            /* 0x0c */
	uint8_t  orig_video_lines;   /* 0x0e */
	uint8_t  orig_video_isVGA;   /* 0x0f */
	uint16_t orig_video_points;  /* 0x10 */

    /* VESA graphic mode -- linear frame buffer */
	uint16_t lfb_width;          /* 0x12 */
	uint16_t lfb_height;         /* 0x14 */
	uint16_t lfb_depth;          /* 0x16 */
	uint32_t lfb_base;           /* 0x18 */
	uint32_t lfb_size;           /* 0x1c */
	uint16_t cl_magic, cl_offset; /* 0x20 */
	uint16_t lfb_linelength;     /* 0x24 */
	uint8_t  red_size;           /* 0x26 */
	uint8_t  red_pos;            /* 0x27 */
	uint8_t  green_size;         /* 0x28 */
	uint8_t  green_pos;          /* 0x29 */
	uint8_t  blue_size;          /* 0x2a */
	uint8_t  blue_pos;           /* 0x2b */
	uint8_t  rsvd_size;          /* 0x2c */
	uint8_t  rsvd_pos;           /* 0x2d */
	uint16_t vesapm_seg;         /* 0x2e */
	uint16_t vesapm_off;         /* 0x30 */
	uint16_t pages;              /* 0x32 */
	uint16_t vesa_attributes;    /* 0x34 */
	uint32_t capabilities;       /* 0x36 */
	uint32_t ext_lfb_base;       /* 0x3a */
	uint8_t  _reserved[2];       /* 0x3e */
} __attribute__((packed));

#define VIDEO_TYPE_MDA        0x10    /* Monochrome Text Display    */
#define VIDEO_TYPE_CGA        0x11    /* CGA Display             */
#define VIDEO_TYPE_EGAM       0x20    /* EGA/VGA in Monochrome Mode    */
#define VIDEO_TYPE_EGAC       0x21    /* EGA in Color Mode        */
#define VIDEO_TYPE_VGAC       0x22    /* VGA+ in Color Mode        */
#define VIDEO_TYPE_VLFB       0x23    /* VESA VGA in graphic mode    */

#define VIDEO_TYPE_PICA_S3    0x30    /* ACER PICA-61 local S3 video    */
#define VIDEO_TYPE_MIPS_G364  0x31    /* MIPS Magnum 4000 G364 video  */
#define VIDEO_TYPE_SGI        0x33    /* Various SGI graphics hardware */

#define VIDEO_TYPE_TGAC       0x40    /* DEC TGA */

#define VIDEO_TYPE_SUN        0x50    /* Sun frame buffer. */
#define VIDEO_TYPE_SUNPCI     0x51    /* Sun PCI based frame buffer. */

#define VIDEO_TYPE_PMAC       0x60    /* PowerMacintosh frame buffer. */

#define VIDEO_TYPE_EFI        0x70    /* EFI graphic mode        */

#define VIDEO_FLAGS_NOCURSOR  (1 << 0) /* The video mode has no cursor set */

#define VIDEO_CAPABILITY_SKIP_QUIRKS   (1 << 0)
#define VIDEO_CAPABILITY_64BIT_BASE    (1 << 1)    /* Frame buffer base is 64-bit */

struct apm_bios_info {
	uint16_t    version;
	uint16_t    cseg;
	uint32_t    offset;
	uint16_t    cseg_16;
	uint16_t    dseg;
	uint16_t    flags;
	uint16_t    cseg_len;
	uint16_t    cseg_16_len;
	uint16_t    dseg_len;
};

struct ist_info {
	uint32_t signature;
	uint32_t command;
	uint32_t event;
	uint32_t perf_level;
};

struct sys_desc_table {
	uint16_t length;
	uint8_t  table[14];
};

struct olpc_ofw_header {
	uint32_t ofw_magic;    /* OFW signature */
	uint32_t ofw_version;
	uint32_t cif_handler;    /* callback into OFW */
	uint32_t irq_desc_table;
} __attribute__((packed));

struct edid_info {
	unsigned char dummy[128];
};

struct efi_info {
	uint32_t efi_loader_signature;
	uint32_t efi_systab;
	uint32_t efi_memdesc_size;
	uint32_t efi_memdesc_version;
	uint32_t efi_memmap;
	uint32_t efi_memmap_size;
	uint32_t efi_systab_hi;
	uint32_t efi_memmap_hi;
};

struct boot_e820_entry {
	uint64_t addr;
	uint64_t size;
	uint32_t type;
} __attribute__((packed));

struct edd_device_params {
	uint16_t length;
	uint16_t info_flags;
	uint32_t num_default_cylinders;
	uint32_t num_default_heads;
	uint32_t sectors_per_track;
	uint64_t number_of_sectors;
	uint16_t bytes_per_sector;
	uint32_t dpte_ptr;   /* 0xFFFFFFFF for our purposes */
	uint16_t key;        /* = 0xBEDD */
	uint8_t device_path_info_length;    /* = 44 */
	uint8_t reserved2;
	uint16_t reserved3;
	uint8_t host_bus_type[4];
	uint8_t interface_type[8];
	union {
		struct {
			uint16_t base_address;
			uint16_t reserved1;
			uint32_t reserved2;
		} __attribute__ ((packed)) isa;
		struct {
			uint8_t bus;
			uint8_t slot;
			uint8_t function;
			uint8_t channel;
			uint32_t reserved;
		} __attribute__ ((packed)) pci;
		/* pcix is same as pci */
		struct {
			uint64_t reserved;
		} __attribute__ ((packed)) ibnd;
		struct {
			uint64_t reserved;
		} __attribute__ ((packed)) xprs;
		struct {
			uint64_t reserved;
		} __attribute__ ((packed)) htpt;
		struct {
			uint64_t reserved;
		} __attribute__ ((packed)) unknown;
	} interface_path;
	union {
		struct {
			uint8_t device;
			uint8_t reserved1;
			uint16_t reserved2;
			uint32_t reserved3;
			uint64_t reserved4;
		} __attribute__ ((packed)) ata;
		struct {
			uint8_t device;
			uint8_t lun;
			uint8_t reserved1;
			uint8_t reserved2;
			uint32_t reserved3;
			uint64_t reserved4;
		} __attribute__ ((packed)) atapi;
		struct {
			uint16_t id;
			uint64_t lun;
			uint16_t reserved1;
			uint32_t reserved2;
		} __attribute__ ((packed)) scsi;
		struct {
			uint64_t serial_number;
			uint64_t reserved;
		} __attribute__ ((packed)) usb;
		struct {
			uint64_t eui;
			uint64_t reserved;
		} __attribute__ ((packed)) i1394;
		struct {
			uint64_t wwid;
			uint64_t lun;
		} __attribute__ ((packed)) fibre;
		struct {
			uint64_t identity_tag;
			uint64_t reserved;
		} __attribute__ ((packed)) i2o;
		struct {
			uint32_t array_number;
			uint32_t reserved1;
			uint64_t reserved2;
		} __attribute__ ((packed)) raid;
		struct {
			uint8_t device;
			uint8_t reserved1;
			uint16_t reserved2;
			uint32_t reserved3;
			uint64_t reserved4;
		} __attribute__ ((packed)) sata;
		struct {
			uint64_t reserved1;
			uint64_t reserved2;
		} __attribute__ ((packed)) unknown;
	} device_path;
	uint8_t reserved4;
	uint8_t checksum;
} __attribute__ ((packed));

struct edd_info {
	uint8_t device;
	uint8_t version;
	uint16_t interface_support;
	uint16_t legacy_max_cylinder;
	uint8_t legacy_max_head;
	uint8_t legacy_sectors_per_track;
	struct edd_device_params params;
} __attribute__ ((packed));

struct boot_params {
	struct   screen_info screen_info;                        /* 0x000 */
	struct   apm_bios_info apm_bios_info;                    /* 0x040 */
	uint8_t  _pad2[4];                                       /* 0x054 */
	uint64_t  tboot_addr;                                    /* 0x058 */
	struct ist_info ist_info;                                /* 0x060 */
	uint64_t acpi_rsdp_addr;                                 /* 0x070 */
	uint8_t  _pad3[8];                                       /* 0x078 */
	uint8_t  hd0_info[16];                  /* obsolete! */  /* 0x080 */
	uint8_t  hd1_info[16];                  /* obsolete! */  /* 0x090 */
	struct   sys_desc_table sys_desc_table; /* obsolete! */  /* 0x0a0 */
	struct   olpc_ofw_header olpc_ofw_header;                /* 0x0b0 */
	uint32_t ext_ramdisk_image;                              /* 0x0c0 */
	uint32_t ext_ramdisk_size;                               /* 0x0c4 */
	uint32_t ext_cmd_line_ptr;                               /* 0x0c8 */
	uint8_t  _pad4[116];                                     /* 0x0cc */
	struct   edid_info edid_info;                            /* 0x140 */
	struct   efi_info efi_info;                              /* 0x1c0 */
	uint32_t alt_mem_k;                                      /* 0x1e0 */
	uint32_t scratch;                  /* Scratch field! */  /* 0x1e4 */
	uint8_t  e820_entries;                                   /* 0x1e8 */
	uint8_t  eddbuf_entries;                                 /* 0x1e9 */
	uint8_t  edd_mbr_sig_buf_entries;                        /* 0x1ea */
	uint8_t  kbd_status;                                     /* 0x1eb */
	uint8_t  secure_boot;                                    /* 0x1ec */
	uint8_t  _pad5[2];                                       /* 0x1ed */
	/*
	* The sentinel is set to a nonzero value (0xff) in header.S.
	*
	* A bootloader is supposed to only take setup_header and put
	* it into a clean boot_params buffer. If it turns out that
	* it is clumsy or too generous with the buffer, it most
	* probably will pick up the sentinel variable too. The fact
	* that this variable then is still 0xff will let kernel
	* know that some variables in boot_params are invalid and
	* kernel should zero out certain portions of boot_params.
	*/
	uint8_t  sentinel;                                /* 0x1ef */
	uint8_t  _pad6[1];                                /* 0x1f0 */
	struct setup_header hdr;    /* setup header */    /* 0x1f1 */
	uint8_t  _pad7[0x290-0x1f1-sizeof(struct setup_header)];
	uint32_t edd_mbr_sig_buffer[EDD_MBR_SIG_MAX];     /* 0x290 */
	struct boot_e820_entry e820_table[E820_MAX_ENTRIES_ZEROPAGE]; /* 0x2d0 */
	uint8_t  _pad8[48];                               /* 0xcd0 */
	struct edd_info eddbuf[EDDMAXNR];                 /* 0xd00 */
	uint8_t  _pad9[276];                              /* 0xeec */
} __attribute__((packed));

/* End of Linux code */

static void linux_trampoline(char *kernel_src_addr, unsigned int kernel_size,
		char *initrd_src_addr, unsigned int initrd_size,
		char *initrd_dst_addr,
		struct boot_params *boot_params)
{
	struct gate_desc idt[64];
	struct desc_r idtr = {
		sizeof(idt) - 1,
		(unsigned int)&idt
	};

	struct seg_desc gdt[4];
	struct desc_r gdtr = {
		sizeof(gdt) - 1,
		(unsigned int)&gdt
	};

	int cr0;

	CLI();

	/* invalidate IDT */
#ifdef __TINYC__
	char *dst, *src;
	unsigned int len;
	for (dst = (char *)&idt, len = sizeof(idt); len; len--) {
		*dst++ = 0;
	}
#else
	_memset_b(&idt, 0, sizeof(idt));
#endif
	__asm__ __volatile__ (
		"lidt %0\n\t"
		: /* no output */
		: "m"(idtr)
	);

	/* configure a new flat GDT */
	gdt[0].sd_lolimit = 0;
	gdt[0].sd_lobase = 0;
	gdt[0].sd_loflags = 0;
	gdt[0].sd_hilimit = 0;
	gdt[0].sd_hiflags = 0;
	gdt[0].sd_hibase = 0;

	gdt[1].sd_lolimit = 0;
	gdt[1].sd_lobase = 0;
	gdt[1].sd_loflags = 0;
	gdt[1].sd_hilimit = 0;
	gdt[1].sd_hiflags = 0;
	gdt[1].sd_hibase = 0;

	gdt[2].sd_lolimit = 0xFFFF;
	gdt[2].sd_lobase = 0x00000000 & 0xFFFFFF;
	gdt[2].sd_loflags = SD_CODE | SD_CD | SD_DPL0 | SD_PRESENT;
	gdt[2].sd_hilimit = (0xFFFFFFFF >> 16) & 0x0F;
	gdt[2].sd_hiflags = SD_OPSIZE32 | SD_PAGE4KB;
	gdt[2].sd_hibase = (0x00000000 >> 24) & 0xFF;

	gdt[3].sd_lolimit = 0xFFFF;
	gdt[3].sd_lobase = 0x00000000 & 0xFFFFFF;
	gdt[3].sd_loflags = SD_DATA | SD_CD | SD_DPL0 | SD_PRESENT;
	gdt[3].sd_hilimit = (0xFFFFFFFF >> 16) & 0x0F;
	gdt[3].sd_hiflags = SD_OPSIZE32 | SD_PAGE4KB;
	gdt[3].sd_hibase = (0x00000000 >> 24) & 0xFF;
	__asm__ __volatile__ (
		"lgdt %0\n\t"
		: /* no output */
		: "m"(gdtr)
	);

	/* disable paging and others */
	cr0 = 0x11;	/* preserve ET & PE */
	__asm__ __volatile__(
		"mov	%0, %%cr0"
		: /* no output */
		: "r"(cr0)
	);

	/* flush TLB (needed?) */
	__asm__ __volatile__(
		"xorl	%%eax, %%eax\n\t"
		"movl	%%eax, %%cr3\n\t"
		: /* no output */
		: /* no input */
		: "eax"	/* clobbered registers */
	);

	/*
	 * Clear memory. This is intended to avoid unexpected results if the
	 * new kernel guesses its uninitialized variables are zeroed.
	 */
#ifdef __TINYC__
	for (dst = (char *)0, len = KEXEC_BOOT_ADDR; len; len--) {
		*dst++ = 0;
	}
#else
	_memset_b(0x0, 0, KEXEC_BOOT_ADDR);
#endif
#ifdef __TINYC__
	for (dst = (char *)0x100000, len = (unsigned int)kernel_src_addr - 0x100000; len; len--) {
		*dst++ = 0;
	}
#else
	_memset_b((void *)0x100000, 0, (unsigned int)kernel_src_addr - 0x100000);
#endif

	/* install the kernel previously stored in RAMdisk by the user */
#ifdef __TINYC__
	for (dst = (char *)0x100000, src = kernel_src_addr, len = kernel_size; len; len--) {
		*dst++ = *src++;
	}
#else
	_memcpy_b((void *)0x100000, kernel_src_addr, kernel_size);
#endif
	/* install the ramdisk previously stored in RAMdisk by the user */
#ifdef __TINYC__
	for (dst = (char *)initrd_dst_addr, src = initrd_src_addr, len = initrd_size; len; len--) {
		*dst++ = *src++;
	}
#else
	_memcpy_b((void *)initrd_dst_addr, initrd_src_addr, initrd_size);
#endif

	/* flush TLB (needed?) */
	__asm__ __volatile__(
		"xorl	%%eax, %%eax\n\t"
		"movl	%%eax, %%cr3\n\t"
		: /* no output */
		: /* no input */
		: "eax"	/* clobbered registers */
	);

	/* load all the segment registers with the kernel data segment value */
	__asm__ __volatile__(
		"movw	$0x18, %%ax\n\t"
		"movw	%%ax, %%ds\n\t"
		"movw	%%ax, %%es\n\t"
		"movw	%%ax, %%fs\n\t"
		"movw	%%ax, %%gs\n\t"
		"movw	%%ax, %%ss\n\t"
		: /* no output */
		: /* no input */
		: "eax"	/* clobbered registers */
	);

	/* Linux boot */
#ifdef __TINYC__
	__asm__ __volatile__(
		"movl	%0, %%eax\n\t"
		"movl	%%eax, %%esi\n\t"
		: /* no output */
		: "r"((unsigned int)boot_params)
	);
#else
	__asm__ __volatile__(
		"movl	%0, %%eax\n\t"
		"movl	%%eax, %%esi\n\t"
		: /* no output */
		: "eax"((unsigned int)boot_params)
	);
#endif

	/*
	 * This jumps to the kernel entry address.
	 *
	 */
	__asm__ __volatile__(
		"pushw	$0x10\n\t"
		"pushl	%0\n\t"
		"ljmp	*(%%esp)\n\t"
		: /* no output */
		: "c"(KERNEL_ADDR)
	);

	/* not reached */
}


void kexec_linux(void) {
	struct proc *idle, *prev;
	unsigned int *esp;
	char *kernel_src_addr, *initrd_src_addr;
	uint32_t kernel_size, initrd_size;
	struct boot_params *boot_params;
	char *cmdline;

	kernel_size = *((uint32_t *)ramdisk_table[ramdisk_minors - 1].addr);
	printk("kexec_linux: kernel file size: %u\n", kernel_size);
	initrd_size = *((uint32_t *) (ramdisk_table[ramdisk_minors - 1].addr + sizeof(uint32_t)));

	/* space reserved for the memory map structure */
	kernel_src_addr = ramdisk_table[ramdisk_minors - 1].addr + (sizeof(uint32_t) * 2);

	uint32_t signature;
	memcpy_b(&signature, kernel_src_addr + 0x202, sizeof(uint32_t));

	/* validate signature */
	if (signature != 0x53726448) {
		printk("kexec_linux: Invalid kernel signature\n");
		return;
	} else {
		printk("kexec_linux: Valid kernel signature\n");
	}

	size_t setup_code_size = 0;
	memcpy_b(&setup_code_size, kernel_src_addr + 0x1f1, 1);
	if (setup_code_size == 0)
		setup_code_size = 4;
	setup_code_size *= 512;

	size_t real_mode_code_size = 512 + setup_code_size;

	memcpy_b((void *)KEXEC_BOOT_ADDR, linux_trampoline, PAGE_SIZE);

	/* the IDLE process will do the job */
	idle = &proc_table[IDLE];
	idle->tss.eip = (unsigned int)KEXEC_BOOT_ADDR;

	/* stack starts at the end of the page */
	esp = (unsigned int *)(KEXEC_BOOT_ADDR + (PAGE_SIZE * 2) - 4);

	/* space reserved for the cmdline string (256 bytes) */
	esp -= 256 / sizeof(unsigned int);
	cmdline = (char *)esp;
	strcpy(cmdline, kexec_cmdline);

	/* space reserved for the multiboot_info structure */
	esp -= sizeof(struct boot_params) / sizeof(unsigned int);
	memset_b(esp, 0, sizeof(struct boot_params));
	boot_params = (struct boot_params *)esp;

	struct setup_header *setup_header = &boot_params->hdr;

	size_t setup_header_end = ({
		uint8_t x;
		memcpy_b(&x, kernel_src_addr + 0x201, 1);
		0x202 + x;
	});

	memcpy_b(setup_header, kernel_src_addr + 0x1f1, setup_header_end - 0x1f1);

	printk("kexec_linux: Boot protocol: %u.%u\n",
		setup_header->version >> 8, setup_header->version & 0xff);

	if (setup_header->version < 0x203) {
		printk("kexec_linux: Protocols < 2.03 are not supported");
		return;
	}

	setup_header->cmd_line_ptr = (uint32_t)(uintptr_t)cmdline;

	/* vid_mode. 0xffff means "normal" */
	setup_header->vid_mode = 0xffff;

	setup_header->type_of_loader = 0xff;

	if (!(setup_header->loadflags & (1 << 0))) {
		printk("kexec_linux: Kernels that load at 0x10000 are not supported");
		return;
	}

	setup_header->loadflags &= ~(1 << 5);     /* print early messages */

	/* Modules */

	uint32_t modules_mem_base = setup_header->initrd_addr_max;
	if (modules_mem_base == 0)
		modules_mem_base = 0x38000000;

	initrd_src_addr = kernel_src_addr + kernel_size; 

	modules_mem_base -= initrd_size;

	setup_header->ramdisk_image = (uint32_t)modules_mem_base;
	setup_header->ramdisk_size  = (uint32_t)initrd_size;

	struct screen_info *screen_info = &boot_params->screen_info;

	screen_info->orig_video_mode = 3;
	screen_info->orig_video_ega_bx = 3;
	screen_info->orig_video_lines = 25;
	screen_info->orig_video_cols = 80;
	screen_info->orig_video_points = 16;

	screen_info->orig_video_isVGA = VIDEO_TYPE_VGAC;

	/* e820 */

	struct boot_e820_entry *e820_table = boot_params->e820_table;

	size_t i, j;
	for (i = 0, j = 0; i < NR_BIOS_MM_ENT; i++) {
                if(!bios_mem_map[i].type || bios_mem_map[i].type > 0x1000) {
			continue;
		}
		e820_table[j].addr = bios_mem_map[i].from_hi;
		e820_table[j].addr = (e820_table[j].addr << 32) | bios_mem_map[i].from;
		e820_table[j].size = bios_mem_map[i].to_hi;
		e820_table[j].size = (e820_table[j].size << 32) | bios_mem_map[i].to;
		e820_table[j].size -= e820_table[j].addr;
		e820_table[j].type = bios_mem_map[i].type;
		j++;
		boot_params->e820_entries = j;
	}

	/* now put the four parameters into the stack */
	esp--;
	*esp = (unsigned int)boot_params;
	esp--;
	*esp = modules_mem_base;
	esp--;
	*esp = initrd_size;
	esp--;
	*esp = V2P(initrd_src_addr);
	esp--;
	*esp = (kernel_size - real_mode_code_size);
	esp--;
	*esp = V2P(kernel_src_addr + real_mode_code_size);
	esp--;
	idle->tss.esp = (unsigned int)esp;

	printk("kexec_linux: boot_params: %x\n", boot_params);
	printk("kexec_linux: modules_mem_base: %x\n", modules_mem_base);
	printk("kexec_linux: initrd_size: %u\n", initrd_size);
	printk("kexec_linux: initrd_src_addr: %x\n", initrd_src_addr);
	printk("kexec_linux: initrd_src_addr: %x\n", V2P(initrd_src_addr));
	printk("kexec_linux: kernel_size: %u\n", kernel_size - real_mode_code_size);
	printk("kexec_linux: kernel_src_addr: %x\n", kernel_src_addr + real_mode_code_size);
	printk("kexec_linux: kernel_src_addr: %x\n", V2P(kernel_src_addr + real_mode_code_size));

	printk("kexec_linux: jumping to linux_trampoline() ...\n");
	prev = current;
	set_tss(idle);
	do_switch(&prev->tss.esp, &prev->tss.eip, idle->tss.esp, idle->tss.eip, idle->tss.cr3, TSS);
	/* not reached */
	return;
}

#endif /* CONFIG_KEXEC */

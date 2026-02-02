# Makefile for Monster HDD Sampler Kernel Module

obj-m += monster_sampler.o

KDIR := /lib/modules/$(shell uname -r)/build
PWD := $(shell pwd)

all:
	$(MAKE) -C $(KDIR) M=$(PWD) modules

clean:
	$(MAKE) -C $(KDIR) M=$(PWD) clean

install:
	sudo insmod monster_sampler.ko

uninstall:
	sudo rmmod monster_sampler

test:
	sudo dmesg | tail -20

shards:
	cat /sys/kernel/monster_sampler/shards

.PHONY: all clean install uninstall test shards

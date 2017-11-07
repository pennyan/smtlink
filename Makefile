# Copyright (C) 2015, University of British Columbia
# Written by Yan Peng (July 12th 2017)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with this software
#

# Usage:
#  make ACL2=... PYTHON=... SAVE_PY_TO=.../nil JOBS=...
#  make clean ACL2=...

.PHONY: all clean

ACL2 := /Users/penny/bin/acl2
ACL2_BOOKS := /Users/penny/Software/acl2/books
BUILD_DIR := /Users/penny/Software/acl2/books/build

JOBS ?= 2

all: example

top:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) top

doc:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) doc

example:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) examples/examples.lisp


clean:
	$(BUILD_DIR)/clean.pl
	rm -rf manual

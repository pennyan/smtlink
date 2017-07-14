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

ifndef ACL2
 $(error Variable ACL2 is undefined.)
endif
BUILD_DIR := $(dir $(ACL2))books/build
JOBS ?= 2

all:
	if [ -z "$$PYTHON" ]; then echo "Variable PYTHON is undefined"; exit 1; fi
	if [ -z "$$SAVE_PY_TO" ]; then echo "Variable SAVE_PY_TO is undefined"; exit 1; fi
	$(PYTHON) py_utils/gen_ACL22SMT.py ./z3_interface/ACL2_to_Z3.py ./trusted/z3-py/ACL22SMT.lisp
	$(PYTHON) py_utils/gen_config.py -i ./verified/SMT-config-template.lisp \
                                   -o ./verified/SMT-config.lisp \
                                   -p $(PYTHON) \
                                   -z $(SAVE_PY_TO)
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) top


clean:
	$(BUILD_DIR)/clean.pl

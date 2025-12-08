MIR_SRCS=test
include ../support/mir-blobs.mk

SAW        ?= saw
TEST_SHELL ?= bash
SUPPORTDIR ?= ../support

saw-run:
	SAW=$(SAW) TEST_SHELL=$(TEST_SHELL) $(TEST_SHELL) $(SUPPORTDIR)/test-and-diff.sh run-tests

saw-log: saw-run
	SAW=$(SAW) TEST_SHELL=$(TEST_SHELL) $(TEST_SHELL) $(SUPPORTDIR)/test-and-diff.sh good

# asn1c's ALIGNED decoder and encoder for one PDU type, from the C asn1c made
# of the protocol's schema (bench/run.sh makes it):
#   make SRC=DIR PDU=NGAP-PDU OPT=-O3 O=OUTDIR    -> OUTDIR/bench_asn1c
SRC ?= src
PDU ?= NGAP-PDU
CC ?= gcc
OPT ?= -O3
O ?= obj
include $(SRC)/Makefile.am.libasncodec
vpath %.c $(SRC)
CFLAGS := $(OPT) $(ASN_MODULE_CFLAGS) -DASN_PDU_COLLECTION -I$(SRC) -w
OBJ := $(addprefix $(O)/,$(ASN_MODULE_SRCS:.c=.o))
PDEF := asn_DEF_$(subst -,_,$(PDU))

$(O)/bench_asn1c: bench_pdu.c $(O)/libasncodec.a
	$(CC) $(CFLAGS) -DAPER -DPDU_H='"$(PDU).h"' -DPDU_DEF=$(PDEF) -DPDU_NAME='"$(PDU)"' -o $@ $< $(O)/libasncodec.a -lm
$(O)/libasncodec.a: $(OBJ)
	$(AR) rcs $@ $^
$(O)/%.o: %.c | $(O)
	$(CC) $(CFLAGS) -c $< -o $@
$(O):
	mkdir -p $(O)

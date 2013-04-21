CC = gcc
CFLAGS = -g -O2 -Wall

.PHONY: do_test

# テストプログラムが増えたら、これを増やす
TESTS = print sum-tail gcd sum fib ack even-odd \
adder funcomp cls-rec cls-bug cls-bug2 \
shuffle spill spill2 spill3 join-stack join-stack2 join-stack3 \
join-reg join-reg2 non-tail-if non-tail-if2 \
inprod inprod-rec inprod-loop matmul matmul-flat

do_test: $(TESTS:%=%.cmp)

.PRECIOUS: %.s % %.res %.ans %.cmp
TRASH = $(TESTS:%=%.s) $(TESTS:%=%) $(TESTS:%=%.res) $(TESTS:%=%.ans) $(TESTS:%=%.cmp)

%.s: %.ml
	$(MINCAML) $*
	llc --march=x86 $*.bc -o $@

%.out: %.s $(STUB)/libmincaml.c $(STUB)/stub.c
	$(CC) $(CFLAGS) -m32 $^ -lm -o $@

%.res: %.out
	./$< > $@

%.ans: %.ml
	ocaml $< > $@

%.cmp: %.res %.ans
	diff $^ > $@

clean:
	rm -rf $(TRASH)

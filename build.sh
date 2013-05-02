#!/bin/sh -x
./main.native $1 && \
llc --march=x86 $1.bc -o $1.s && \
gcc -g -m32 -lm $1.s stub/stub.c  stub/libmincaml.c -o $1

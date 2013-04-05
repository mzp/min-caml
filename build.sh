#!/bin/sh -x
./main.native $1 && \
llc --march=x86 $1.bc -o $1.s && \
gcc -m32 $1.s stub/stub.c  stub/libmincaml.c -o $1

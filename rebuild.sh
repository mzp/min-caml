#!/bin/sh -x
llc --march=x86 $1.ll -o $1.s && \
gcc -g -m32 -lm $1.s stub/stub.c  stub/libmincaml.c -o $1

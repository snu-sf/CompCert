#!/usr/bin/env bash
make -f sepcomp/Makefile depend &&
make -f sepcomp/Makefile -j $1 proof &&
make -f sepcomp/Makefile extraction &&
make -f sepcomp/Makefile ccomp &&
make -f sepcomp/Makefile runtime &&
make -f sepcomp/Makefile cchecklink

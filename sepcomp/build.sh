#!/usr/bin/env bash
make -f sepcomp/Makefile depend
make -f sepcomp/Makefile -j $1 proof
make -f sepcomp/Makefile extraction
make -f sepcomp/Makefile ccomp


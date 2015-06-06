#!/usr/bin/env bash

if [ -z "$1" ]; then
  jobs=1
else
  jobs=$1
fi

cd ..
make -f sepcomp/Makefile depend &&
make -f sepcomp/Makefile -j $jobs proof &&
make -f sepcomp/Makefile extraction &&
make -f sepcomp/Makefile ccomp &&
make -f sepcomp/Makefile runtime &&
make -f sepcomp/Makefile cchecklink

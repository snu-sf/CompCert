# Separate Compilation for CompCert 2.4 #

Jeehoon Kang and Chung-Kil Hur
Seoul National University

We provide a correctness proof of separate compilation for CompCert 2.4, the latest version. It means that the semantics preservation result of CompCert 2.4 is still valid even when you do separate compilation and linking.

## Installation ##

This distribution is an add-on package to CompCert 2.4. Install and build as follows:

- Download [CompCert 2.4](http://compcert.inria.fr/release/compcert-2.4.tgz) and extract.
- Download [Separation Compilation of CompCert 2.4](http://sf.snu.ac.kr/compcertsep/release/compcert-2.4-sep-p1.tgz) and extract at the same directory.
- Configure CompCert (e.g., `./configure ia32-linux` if Linux is installed in your x86 machine).
- Build CompCert with Separate Compilation (e.g., `./build.sh 8` in `sepcomp` directory if you have 8 CPU cores).

## Result ##

Our main result is `linker_correct` at `sepcomp/Linkerproof.v:237`. Basically, it says: if some C programs are compiled to some assembly programs and C programs are successfully linked to a C program `c`, then the assembly programs are successfully linked to an assembly program `a` and `a` behaviorally refines `c`.

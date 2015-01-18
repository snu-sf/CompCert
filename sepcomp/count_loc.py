#!/usr/bin/env python

import os, subprocess

if __name__ == "__main__":
    sum = 0

    difffiles = \
    ["backend/Renumberproof", 
     "backend/Constpropproof",
     "backend/Deadcodeproof",
     "backend/CSEproof",
     "backend/Tailcallproof",
     "backend/Inliningproof",
     "backend/Selectionproof",
     "backend/ValueAnalysis",
     "cfrontend/SimplExprproof"]

    otherfiles = \
    ["Linker",
     "Linkerproof",
     "backend/RTL_linker",
     "common/Adequacy",
     "common/FunctionLSim",
     "common/Language",
     "common/Linkeq",
     "common/LinkerBasicproof",
     "common/LinkerProp",
     "common/ProgramLSim",
     "common/Sig",
     "common/Smallstep_linker",
     "lib/Coqlib_linker",
     "lib/Maps_linker",
     "lib/Tree",
     "lib/WFType"]

    for filename in difffiles:
        num = int(subprocess.check_output("diff ../%s.v %s_linker.v | grep \"^>\" | wc -l" % (filename, filename), shell=True))
        print("%s:\t%d (*)" % (filename, num))
        sum += num
    print("")

    for filename in otherfiles:
        num = int(subprocess.check_output("cat %s.v | wc -l" % filename, shell=True))
        print("%s:\t%d" % (filename, num))
        sum += num
    print("")

    print("%s:\t%d" % ("\tTotal", sum))

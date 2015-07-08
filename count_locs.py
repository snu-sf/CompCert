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
     "common/Language",
     "common/Linksub",
     "common/LinkerBasicproof",
     "common/LinkerProp",
     "common/SepcompRel",
     "common/Sig",
     "lib/Coqlib_sepcomp",
     "lib/Maps_sepcomp",
     "lib/Tree",
     "lib/WFType"]

    for filename in difffiles:
        num = int(subprocess.check_output("diff ../%s.v %s_sepcomp.v | grep \"^>\" | wc -l" % (filename, filename), shell=True))
        print("%s:\t%d (*)" % (filename, num))
        sum += num
    print("")

    for filename in otherfiles:
        num = int(subprocess.check_output("cat %s.v | wc -l" % filename, shell=True))
        print("%s:\t%d" % (filename, num))
        sum += num
    print("")

    print("%s:\t%d" % ("\tTotal", sum))

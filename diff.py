#!/usr/bin/env python

import os, subprocess

if __name__ == "__main__":
    s1 = 0
    s2 = 0
    s3 = 0
    for passname in ["Renumberproof", "Constpropproof", "Deadcodeproof", "CSEproof", "Tailcallproof", "Inliningproof", "Selectionproof", "SimplExprproof", "ValueAnalysis"]:
        output1 = subprocess.check_output("diff ../*/%s.v */%s_linker.v | grep \"^>\" | wc -l" % (passname, passname), shell=True)
        output2 = subprocess.check_output("diff ../*/%s.v */%s_linker.v | grep \"^> (\*\" | wc -l" % (passname, passname), shell=True)
        print("%s:\t%d \t- 1.5*%d \t= %d" % (passname, int(output1), int(output2), int(int(output1) - int(output2) * 1.5)))
        s1 += int(output1)
        s2 += int(output2)
        s3 += int(int(output1) - int(output2) * 1.5)
    print("")
    print("%s:\t%d \t- 1.5*%d \t= %d" % ("\tTotal", s1, s2, s3))

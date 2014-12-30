#!/usr/bin/env python

import os, subprocess

if __name__ == "__main__":
    for passname in ["Renumber", "Constprop", "Deadcode", "CSE", "Tailcall", "Inlining"]:
        output1 = subprocess.check_output("diff ../backend/%sproof.v backend/%sproof_linker.v | grep \"^>\" | wc -l" % (passname, passname), shell=True)
        output2 = subprocess.check_output("diff ../backend/%sproof.v backend/%sproof_linker.v | grep \"^> (\*\" | wc -l" % (passname, passname), shell=True)
        print("%s:\t%d \t- 1.5*%d \t= %d" % (passname, int(output1), int(output2), int(int(output1) - int(output2) * 1.5)))

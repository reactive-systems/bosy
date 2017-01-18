#!/usr/bin/env python
# coding=utf8

import sys
import re
regex = r"^aag.(\d+)\D(\d+)\D(\d+)\D(\d+)\D(\d+)$"

def matchaigstat(line):
  matches = re.match(regex,line)
  if matches:
    print "AIGER circuit statistics. Inputs: "+matches.group(2)+" Outputs: "+matches.group(4)+" Latches: "+matches.group(3)+" AND Gates: "+matches.group(5)
  
def main(argv):
  if len(sys.argv) == 1:
    for line in sys.stdin:
      matchaigstat(line)
  else:
    with open(sys.argv[1], 'r') as f:
      for line in f:
        matchaigstat(line)
  
if __name__ == "__main__":
   main(sys.argv[1:])
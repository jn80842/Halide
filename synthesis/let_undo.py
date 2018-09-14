import string
import re
import argparse

def let_exists(s):
  return len(s) > 4 and s[:4] == '(let'

def unwind_let(s):
  m = re.search('^\(let( v\d+ )= (.+?) in (.*)\)$',s)
  if m is not None:
    captures = m.groups()
    varname = captures[0]
    term = captures[1]
    expr = captures[2]
    return string.replace(expr,varname,term)
  else:
    return s

def unwind_all_lets(s):
  while let_exists(s):
#    print("unwind" + s)
    s = unwind_let(s)
  return s

def rename_bools(s):
  s = string.replace(s,"(uint1)1","true")
  s = string.replace(s,"(uint1)0","false")
  return s

parser = argparse.ArgumentParser()
parser.add_argument("termfile")
args = parser.parse_args()


with open(args.termfile,'r') as f:
  for line in f:
    print(rename_bools(unwind_all_lets(line)))
    print("\n")

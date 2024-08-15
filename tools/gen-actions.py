#!/usr/bin/python3

# This scripts generates a list of actions that equivalence checker tactic
# (EQUIV_STEPS_TAC) must take from diff of two assembly files,
# `diff` linux commandline tool is necessary because this script internally
# invokes it.
# See also: arm/proofs/p256_montjadd.ml
import os
import subprocess
import sys
import tempfile

if len(sys.argv) != 3:
  print("gen-actions.py <assembly 1> <assembly 2>")
  exit(1)

def interpret(s):
  s = s.strip()
  assert(s != "---" and not s.startswith(">") and not s.startswith("<")), s
  if "c" in s:
    ss = s.split("c")
    cmd = "replace"
  elif "a" in s:
    ss = s.split("a")
    cmd = "insert"
  elif "d" in s:
    ss = s.split("d")
    cmd = "delete"
  else:
    assert False, "Unknown string"

  assert(len(ss) == 2)
  def r(x):
    if "," not in x:
      # [begin, end) where begin starts from zero
      return (int(x) - 1,int(x))
    xs = x.split(",")
    assert(len(xs) == 2)
    return (int(xs[0]) - 1, int(xs[1]))

  lr = r(ss[0]) if cmd != "insert" else (int(ss[0]), int(ss[0]))
  rr = r(ss[1]) if cmd != "delete" else (int(ss[1]), int(ss[1]))
  return (cmd, lr, rr)


def add_equal_if_necessary(res, lend, rend):
  if len(res) > 0:
    _,_,lr_prev_end,_,rr_prev_end = res[-1]
    res.append(("equal", lr_prev_end, lend, rr_prev_end, rend))
  elif lend != 0 and rend != 0:
    res.append(("equal", 0, lend, 0, rend))


# Store diff
asm1path = sys.argv[1]
asm2path = sys.argv[2]
diffh,diffpath = tempfile.mkstemp()
os.close(diffh)
with open(diffpath, "w") as f:
  subprocess.run(["diff", asm1path, asm2path], stdout=f)

# Now get the actions.
with open(diffpath, "r") as f:
  ls = list(f.readlines())
with open(asm1path, "r") as f:
  lnlines = len(list(f.readlines()))
with open(asm2path, "r") as f:
  rnlines = len(list(f.readlines()))

i = 0
res = []
while i < len(ls):
  cmd,lr,rr = interpret(ls[i])
  i += 1
  if cmd == "insert":
    i += rr[1] - rr[0]
  elif cmd == "delete":
    i += lr[1] - lr[0]
  else:
    i += lr[1] - lr[0]
    i += 1 # ---
    i += rr[1] - rr[0]

  add_equal_if_necessary(res, lr[0], rr[0])
  res.append((cmd,lr[0],lr[1],rr[0],rr[1]))

add_equal_if_necessary(res, lnlines, rnlines)

for tag,i1,i2,j1,j2 in res:
  print('("%s", %d, %d, %d, %d);' % (tag,i1,i2,j1,j2))

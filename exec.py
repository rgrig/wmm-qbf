#!/usr/bin/env python3
import sys

if len(sys.argv) > 1 and (sys.argv[1] == "-h" or sys.argv[1] == "--help"):
    print("Converts qcir output from qfun-enum into an execution set.")
    print("Usage:")
    print("  {} <filename>".format(sys.argv[0]))

if len(sys.argv) > 1:
    with open(sys.argv[1], 'r') as content_file:
        content = content_file.read()
else:
    content = sys.stdin.read()

words = content.split(" ")
execs = [x for x in words if "+execution" in x]
rfs = [x for x in words if "+do_decide_rf" in x]
cos = [x for x in words if "+do_decide_co" in x]

events = [x.split("_")[1] for x in execs]
rf_edges = ["({}, {})".format(x.split("_")[3], x.split("_")[4]) for x in rfs]
co_edges = ["({}, {})".format(x.split("_")[3], x.split("_")[4]) for x in cos]

print("Exec: {{{}}}".format(", ".join(events)))
print("rf:   {{{}}}".format(", ".join(rf_edges)))
print("co:   {{{}}}".format(", ".join(co_edges)))

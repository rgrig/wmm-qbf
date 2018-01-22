#!/usr/bin/python
# (This is Python 3)

import sys

if len(sys.argv) != 2 or sys.argv[1] == "-h" or sys.argv[1] == "--help":
	if len(sys.argv) == 1:
		name = sys.argv[0]
	else:
		name = "store_buffer.py"
	print("Usage: {} number-of-threads".format(name))
	print("This script generates a store buffer test with an arbitrary number of threads in LISA.")
	exit(0)

no_threads = int(sys.argv[1])
assert(no_threads > 1)
numbers = range(no_threads)
print("LISA store buffer with {} threads".format(no_threads))
print("{ " + " ".join(map(lambda x: "x{}=0;".format(x), numbers)) + "}")
print(" | ".join(map(lambda x: "P{}       ".format(x), numbers)) + " ;")
print(" | ".join(map(lambda x: "w[] x{} 1 ".format((x + 1) % no_threads), numbers)) + " ;")
print(" | ".join(map(lambda x: "r[] r{} x{}".format(x, x), numbers)) + " ;")
print("(* Nonsense condition; this isn't meant to be tested. *)")
print("exists P0:r0=42")

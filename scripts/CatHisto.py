#!/usr/bin/env python3

from collections import defaultdict

import re
import sys

ast_node_re = re.compile(r'ModelAst.([A-Za-z]*)')

counts = defaultdict(int)
for m in ast_node_re.finditer(sys.stdin.read()):
  counts[m.group(1)] += 1
for k, v in sorted(counts.items(),key=lambda x:x[1])[::-1]:
  sys.stdout.write('{:6} {}\n'.format(v,k))


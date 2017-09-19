#!/usr/bin/env python3
from os import listdir
from os.path import isfile, join
from subprocess import check_output
from sys import argv

TEST_DIRECTORIES = [
    ("data/pes-regression", "pes"),
    ("data/pes-regression/certifies", "pes-certifies"),
    ("data/pes-regression/transitions", "pes-transitions"),
    ("data/pes-regression/transitions/make-promise", "pes-make-promise"),
    ("data/common-regression/valid-conf", "common-valid-conf")
#    ("data/jctc", "j+r")
]

PRIDE_BIN = "./bin/Pride"
QUIET = "-q" in argv or "--quiet" in argv

def result_to_bool(res):
    _, _, result = res
    return result

results = []
for directory, model in TEST_DIRECTORIES:
    files = [path for path in listdir(directory) if isfile(join(directory, path))]
    for test in files:
        output = check_output(
            [PRIDE_BIN, "--model", model, join(directory, test)]
        )
        qbf_result = b"true" in output
        expected = "pass" in test
        result = qbf_result is expected
        if not result and not QUIET:
            print("Failed: {:20s}{}".format(model, join(directory, test)))
        results.append((model, test, result))
        
passed = [p for p in results if result_to_bool(p)]
print("Passed: {} of {}. {:.1f}%".format(
    len(passed),
    len(results),
    len(passed)/len(results) * 100.0)
)

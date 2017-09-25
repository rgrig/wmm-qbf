#!/usr/bin/env python3
from os import listdir
from os.path import isfile, join
from subprocess import check_output, CalledProcessError
from sys import argv


PRIDE_BIN = "./bin/Pride"
QUIET = "-q" in argv or "--quiet" in argv

def snd(x):
    return x[1]

def get_suite(args, tests):
    for i in range(len(args)):
        if(args[i] == "--suite"):
            suites = args[i+1].split(",")
            return [test for test in tests if snd(test) in suites]
    return tests

TESTS = get_suite(argv, [
    ("data/pes-regression", "pes"),
    ("data/pes-regression/certifies", "pes-certifies"),
    ("data/pes-regression/transitions", "pes-transitions"),
    ("data/pes-regression/transitions/make-promise", "pes-make-promise"),
    ("data/pes-regression/transitions/promise-read", "pes-promise-read"),
    ("data/common-regression/valid-conf", "common-valid-conf"),
    #    ("data/jctc", "j+r"), # disabled, because it's slow AF
    ("data/jctc", "pes")
])


def result_to_bool(res):
    _, _, result = res
    return result

results = []
if TESTS == []:
    print("No tests to run.")
    exit(1)

for directory, model in TESTS:
    files = [path for path in listdir(directory) if isfile(join(directory, path))]
    for test in files:
        try:
            output = check_output(
                [PRIDE_BIN, "--model", model, join(directory, test)]
            )
            qbf_result = b"true" in output
            expected = "pass" in test
            result = qbf_result is expected
        except CalledProcessError:
            # Something went wrong with the Pride tool, the test could not be run
            result = False
            results.append((model, test, result))
            continue
            
        if not QUIET:
            if result:
                print("Passed: {:20s}{}".format(model, join(directory, test)))
            else:
                print("Failed: {:20s}{}".format(model, join(directory, test)))
        results.append((model, test, result))

passed = [p for p in results if result_to_bool(p)]
print(
    "Passed: {} of {}. {:.1f}%".format(
        len(passed),
        len(results),
        len(passed)/len(results) * 100.0
    )
)

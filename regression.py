#!/usr/bin/env python3
from os import listdir
from os.path import isfile, join
from subprocess import check_output, CalledProcessError
from sys import argv
import sys


PRIDE_BIN = "./bin/Pride"
QUIET = "-q" in argv or "--quiet" in argv
USE_COLORS = sys.stdout.isatty()

def get_suite(args, tests):
    for i in range(len(args)):
        if(args[i] == "--suite"):
            suites = args[i+1].split(",")
            return [test for test in tests if test[1] in suites]
    return tests

def get_skip(args, tests):
    for i in range(len(args)):
        if(args[i] == "--skip"):
            suites = args[i+1].split(",")
            return [test for test in tests if test[1] not in suites]
    return tests


TESTS = get_suite(argv, get_skip(argv, [
    # -- PES Regression Tests --
    ("data/pes-regression", "pes"),
    ("data/pes-regression/certifies", "pes-certifies"),
    # Control. We should check that the data represents a test that
    # actually passes
    ("data/pes-regression/transitions", "j+r"),
    ("data/pes-regression/transitions", "pes-transitions"),
    ("data/pes-regression/transitions/make-promise", "pes-make-promise"),
    ("data/pes-regression/transitions/promise-read", "pes-promise-read"),
    ("data/pes-regression/transitions/follows", "pes-follows"),

    # -- Common Model Validation --
    ("data/common-regression/valid-conf", "common-valid-conf"),

    # -- Java Causaility Test Cases --
    ("data/jctc", "j+r"), # disabled, because it's slow AF
    ("data/jctc", "pes")
]))


def result_to_bool(res):
    _, _, result = res
    return result

results = []
if TESTS == []:
    print("No tests to run.")
    exit(1)

def colorise(color, text):
    if USE_COLORS:
        return "{}{}{}".format(color, text, "\033[0m")
    else:
        return text
    
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
                print("{}: {:20s}{}".format(colorise("\033[34m", "Passed"), model, join(directory, test)))
            else:
                print("{}: {:20s}{}".format(colorise("\033[33m", "Failed"), model, join(directory, test)))
        results.append((model, test, result))

passed = [p for p in results if result_to_bool(p)]
print(
    "Passed: {} of {}. {:.1f}%".format(
        len(passed),
        len(results),
        len(passed)/len(results) * 100.0
    )
)

#!/usr/bin/env python3
from functools import reduce
from os import listdir
from os.path import isfile, join
from subprocess import check_output, CalledProcessError
from sys import argv
import sys
import time

PRIDE_BIN = "./bin/Pride"
QUIET = "-q" in argv or "--quiet" in argv
USE_COLORS = sys.stdout.isatty()
TTY_RESET = "\033[0m"
TTY_BLUE = "\033[34m"
TTY_ORANGE = "\033[33m"

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

def get_passthrough_args(args):
    for i in range(len(args)):
        if args[i] == "--args":
            return args[i+1:]
    return []

TESTS = get_suite(argv, get_skip(argv, [
    # -- PES Regression Tests --
    ("data/pes-regression", "pes", "qbf"),
    ("data/pes-regression/certifies", "pes-certifies", "qbf"),
    # Control. We should check that the data represents a test that
    # actually passes
    ("data/pes-regression/transitions", "j+r", "qbf"),
    ("data/pes-regression/transitions", "pes-transitions", "qbf"),
    ("data/pes-regression/transitions/make-promise", "pes-make-promise", "qbf"),
    ("data/pes-regression/transitions/promise-read", "pes-promise-read", "qbf"),
    ("data/pes-regression/transitions/follows", "pes-follows", "qbf"),

    # -- Common Model Validation --
    ("data/common-regression/valid-conf", "common-valid-conf", "qbf"),
    ("data/common-regression/valid-conf", "j+r-so2-valid-conf", "qbf"),
    ("data/common-regression/valid-conf", "j+r-so2-valid-conf", "so"),
    
    # -- Java Causaility Test Cases --
    ("data", "j+r", "qbf"),
    ("data/jctc", "j+r", "qbf"),
    ("data", "j+r-acyclic", "qbf"),
    ("data/jctc", "j+r-acyclic", "qbf"),
    ("data/jctc", "pes", "qbf"),

    ("data/jctc", "j+r-so", "so"),
    ("data/jctc", "j+r-so", "qbf"),
    
    ("data/jctc", "j+r-so2", "so"),
    ("data/jctc", "j+r-so2", "qbf"),
    
#    ("data/jctc-lisa", "cat-so", "so"),
    ("data/mark-sc-tests", "cat-so", "so")

]))


def result_to_bool(res):
    return res[2]

results = []
if TESTS == []:
    print("No tests to run.")
    exit(1)

def colorise(color, text):
    if USE_COLORS:
        return "{}{}{}".format(color, text, TTY_RESET)
    else:
        return text

aditional_args = get_passthrough_args(argv)
    
for directory, model, solver in TESTS:
    files = [path for path in listdir(directory) if (isfile(join(directory, path)) and ".es" in path)]
    for test in files:
        try:
            start_time = time.time()
            if not QUIET:
                sys.stdout.write("{:6s}: {:20s} {:3s}         {}\r".format("...", model, solver, join(directory, test)))
            output = check_output(
                [PRIDE_BIN, "--model", model, join(directory, test), "--solver", solver] + aditional_args
            )
            elapsed_time = time.time() - start_time
            qbf_result = b"true" in output
            expected = not ("fail" in test)
            result = qbf_result is expected
        except CalledProcessError:
            # Something went wrong with the Pride tool, the test could not be run
            result = False
            elapsed_time = time.time() - start_time
            results.append((model, test, result, elapsed_time))
            continue
            
        if not QUIET:
            result_string = colorise(TTY_BLUE, "Passed") if result else colorise(TTY_ORANGE, "Failed")
            print("{}: {:20s} {:3s} {:6.02f}s {}".format(result_string, model, solver, elapsed_time, join(directory, test)))
        results.append((model, test, result, elapsed_time))

passed = [p for p in results if result_to_bool(p)]
total_time = reduce((lambda x,y: x + y[3]), results, 0)
print(
    "Passed: {} of {}. {:.1f}% in {:.1f}s".format(
        len(passed),
        len(results),
        len(passed)/len(results) * 100.0,
        total_time
    )
)

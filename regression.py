#!/usr/bin/env python3
from functools import reduce
from natsort import natsorted
from os import listdir
from os.path import isfile, join
import signal
from subprocess import check_output, CalledProcessError
from sys import argv
import sys
import time

PRIDE_BIN = "./bin/Pride"
QUIET = "-q" in argv or "--quiet" in argv
USE_COLORS = sys.stdout.isatty()
TTY_RESET = "\033[0m"
TTY_RED = "\033[31m"
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
    ("data/mark-sc-tests", "cat-cpp", "so"),

    ("data/jctc-lisa", "j+r-so", "so"),
    ("data/jctc-lisa", "j+r-so", "qbf"),

    ("data/ra", "cat-ra", "qbf"),
    
    ("data/sc", "cat-sc", "qbf"),
#    ("data/mark-sc-tests", "cat-sc", "so"),
#    ("data/store_buffer", "cat-sc", "so")
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


def interrupt(signal, frame):
    print("\nExecution interrupted.")
    passed = [p for p in results if result_to_bool(p)]
    total_time = reduce((lambda x,y: x + y[3]), results, 0)
    print(
        "Passed: {} of {}. {:.1f}% in {:.1f}s\n".format(
            len(passed),
            len(results),
            len(passed)/len(results) * 100.0,
            total_time
        )
    )
    sys.exit()

signal.signal(signal.SIGINT, interrupt)


for directory, model, solver in TESTS:
    files = [path for path in listdir(directory) if (isfile(join(directory, path)) and (".es" in path or ".lisa" in path))]
    files = natsorted(files)
    for test in files:
        vals = ["--values", "0,1"]
        try:
            start_time = time.time()
            if "vals" in test:
                index = test.split("-").index("vals")
                vals = ["--values", test.split("-")[index+1]]
            
            if not QUIET:
                low = int(vals[1].split(',')[0]) or 0
                high = int(vals[1].split(',')[1]) or 1
                sys.stdout.write("{:6s}: {:20s} {:3s} {:d}-{:d}     {}\r".format("...", model, solver, low, high, join(directory, test)))
            output = check_output(
                [PRIDE_BIN, "--model", model, join(directory, test), "--solver", solver] + vals + aditional_args
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
            result_string = colorise(TTY_RED, "Except")
            print("{}: {:20s} {:3s} {:6.02f}s {}".format(result_string, model, solver, elapsed_time, join(directory, test)))
            continue
            
        if not QUIET:
            result_string = colorise(TTY_BLUE, "Passed") if result else colorise(TTY_ORANGE, "Failed")
            print("{}: {:20s} {:3s} {:6.02f}s {}".format(result_string, model, solver, elapsed_time, join(directory, test)))
        results.append((model, test, result, elapsed_time))

passed = [p for p in results if result_to_bool(p)]
total_time = reduce((lambda x,y: x + y[3]), results, 0)
print(
    "\nPassed: {} of {}. {:.1f}% in {:.1f}s".format(
        len(passed),
        len(results),
        len(passed)/len(results) * 100.0,
        total_time
    )
)

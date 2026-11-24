"""Run all 924 independent searches. Use an optional argument to set the worker count."""
import concurrent.futures
import csv
import itertools
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
program = here / "search"
workers = int(sys.argv[1]) if len(sys.argv) > 1 else 2

def run(case):
    nots, (left, right) = case
    line = subprocess.check_output([str(program), str(nots), str(left), str(right)], text=True)
    return [int(value) for value in line.split()]

cases = itertools.product(range(13, -1, -1), itertools.combinations_with_replacement(range(11), 2))
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
    writer = csv.writer(sys.stdout)
    writer.writerow(["left", "right", "not_gates", "initial_states", "visited_states", "found"])
    for result in pool.map(run, cases):
        writer.writerow(result)
        sys.stdout.flush()

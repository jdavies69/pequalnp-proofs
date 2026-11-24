"""Evaluate a restricted family for L-meta-2262 using Python 3.

Two dirty ANDs are read directly by a common AND. Each of the four bottom
operands is an OR of a nonempty subset of one raw neighborhood. Other output
terms are centered stars. All maximal independent sets must turn the common
term off. Every edge it misses must be assigned to a star at one endpoint.

For factors A,B,C,D with common edge set J, first discard the pairs for which
19 + tau(G minus J) - |J| exceeds 21. This is the desk counting constraint
specialized to one centreless top and zero charged OR gates. On each remaining
orientation, charge three gates for the pair of bottom ANDs and their common
top, plus two per used star centre (the star AND and its share of the output
OR tree). The raw OR lower bound at a centre is the maximum of three numbers:
the number of distinct nontrivial bottom factors at that centre, one less than
the largest factor's size, and one less than its assigned neighbor count.
Distinct centers cannot own the same nonsingleton raw union, since G is
4-cycle-free. The calculation allows free sharing within this lower bound.
The minimum score is a lower bound in this model. The full desk statement
also admits circuits outside the model.
"""

from functools import lru_cache
from itertools import combinations_with_replacement
from collections import Counter

EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
VERTICES = range(11)
NEIGHBORS = [sum(1 << (b if a == v else a) for a, b in EDGES if v in (a, b))
             for v in VERTICES]
EDGE_INPUTS = [(1 << a) | (1 << b) for a, b in EDGES]


def count(mask):
    return bin(mask).count("1")


def contained(small, large):
    return small & large == small


def induced_edges(vertices):
    return sum(1 << i for i, pair in enumerate(EDGE_INPUTS) if contained(pair, vertices))


def hit_inputs(vertices, inputs):
    return sum(1 << i for i, sample in enumerate(inputs) if sample & vertices)


def residual_covers():
    values = [11] * (1 << len(EDGES))
    for vertices in range(1 << 11):
        edges = induced_edges(vertices)
        values[edges] = min(values[edges], 11 - count(vertices))
    for i in range(len(EDGES)):
        for edges in range(len(values)):
            if edges & (1 << i):
                values[edges] = min(values[edges], values[edges ^ (1 << i)])
    return values


@lru_cache(None)
def orientations(joint):
    rows = [(0,) * 11]
    for i, (a, b) in enumerate(EDGES):
        if joint & (1 << i):
            continue
        extended = []
        for row in rows:
            for center, leaf in ((a, b), (b, a)):
                assigned = list(row)
                assigned[center] |= 1 << leaf
                extended.append(tuple(assigned))
        rows = extended
    return rows


@lru_cache(None)
def orientation_minimum(joint, factors_by_center):
    raw_floor = [max([len(factors)] + [count(factor) - 1 for factor in factors])
                 for factors in factors_by_center]
    best = 100
    for assignment in orientations(joint):
        star_cost = 2 * sum(bool(neighbors) for neighbors in assignment)
        if 3 + star_cost + sum(raw_floor) >= best:
            continue
        raw_cost = sum(max(floor, count(neighbors) - 1)
                       for floor, neighbors in zip(raw_floor, assignment))
        best = min(best, 3 + star_cost + raw_cost)
    return best


def main():
    inputs = range(1 << 11)
    negative = [s for s in inputs if not induced_edges(s) and
                all(induced_edges(s | (1 << v)) for v in VERTICES if not s & (1 << v))]
    factors = [s for s in inputs if s and any(contained(s, n) for n in NEIGHBORS)]
    owner = {}
    for s in factors:
        if count(s) > 1:
            centers = [v for v, n in enumerate(NEIGHBORS) if contained(s, n)]
            assert len(centers) == 1
            owner[s] = centers[0]
    gates = []
    for a, b in combinations_with_replacement(factors, 2):
        bad = hit_inputs(a, negative) & hit_inputs(b, negative)
        if bad:
            gates.append((a, b, bad, hit_inputs(a, EDGE_INPUTS) & hit_inputs(b, EDGE_INPUTS)))
    residual = residual_covers()
    histogram = Counter()
    for left, right in combinations_with_replacement(gates, 2):
        a, b, misses_left, edges_left = left
        c, d, misses_right, edges_right = right
        joint = edges_left & edges_right
        if misses_left & misses_right or 19 + residual[joint] - count(joint) > 21:
            continue
        required = tuple(frozenset(s for s in (a, b, c, d) if owner.get(s) == v)
                         for v in VERTICES)
        histogram[orientation_minimum(joint, required)] += 1
    print("Pairs surviving the counting constraint:", sum(histogram.values()))
    print("Lower-bound score and number of pairs:", sorted(histogram.items()))
    assert sum(histogram.values()) == 3219 and min(histogram) == 23


if __name__ == "__main__":
    main()

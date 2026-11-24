"""Classify positive flags that three OR clauses can accept while rejecting every quadrangle.

An OR clause accepts a set of flags precisely when its raw inputs form a
vertex cover of those incidence edges. Removing inputs down to a minimal
cover retains those positives and can only remove negative responses.
It therefore suffices to enumerate triples of minimal covers. Each cover's
negative responses are represented by a bitset of the 234 quadrangles.

First test all three-edge matchings in the bipartite incidence graph. When
all fail, König's theorem places every feasible flag family inside two stars.
Then test every subset of every union of two stars. No symmetry assumption
is used in either enumeration. The model concerns a conjunction of three
OR clauses on the raw input wires.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement

D = {0, 1, 3, 9}
FLAGS = [(p, l + 13) for p in range(13) for l in range(13) if (p - l) % 13 in D]
LINES = [sum(1 << p for p in range(13) if (p - l) % 13 in D) for l in range(13)]
STARS = [sum(1 << i for i, edge in enumerate(FLAGS) if v in edge) for v in range(26)]


def size(mask):
    return bin(mask).count("1")


def quadrangles():
    rows = []
    for points in combinations(range(13), 4):
        q = sum(1 << p for p in points)
        if all(size(q & line) <= 2 for line in LINES):
            missing = sum(1 << (l + 13) for l, line in enumerate(LINES) if not q & line)
            rows.append(q | missing)
    assert len(rows) == 234
    return rows


ROWS = quadrangles()
ACTIVE = [sum(1 << i for i, row in enumerate(ROWS) if row & (1 << v)) for v in range(26)]


@lru_cache(None)
def negative_rows(vertices):
    if not vertices:
        return 0
    first = vertices & -vertices
    return ACTIVE[first.bit_length() - 1] | negative_rows(vertices ^ first)


@lru_cache(None)
def minimal_covers(edges):
    if not edges:
        return (0,)
    first = (edges & -edges).bit_length() - 1
    candidates = {cover | (1 << vertex) for vertex in FLAGS[first]
                  for cover in minimal_covers(edges & ~STARS[vertex])}
    return tuple(c for c in candidates if not any(d != c and d & c == d for d in candidates))


def feasible(edges):
    negative = [negative_rows(vertices) for vertices in minimal_covers(edges)]
    return any(a & b & c == 0 for a, b, c in combinations_with_replacement(negative, 3))


def main():
    matchings = 0
    for triple in combinations(range(52), 3):
        if len({v for i in triple for v in FLAGS[i]}) == 6:
            matchings += 1
            assert not feasible(sum(1 << i for i in triple))
    assert matchings == 14976
    print("Rejected every three-flag matching:", matchings, flush=True)
    candidates = set()
    for a, b in combinations_with_replacement(STARS, 2):
        union = a | b
        subset = union
        while subset:
            candidates.add(subset)
            subset = (subset - 1) & union
    double_stars = {STARS[p] | STARS[l] for p, l in FLAGS}
    assert len(double_stars) == 52 and all(size(star) == 7 for star in double_stars)
    counts = Counter()
    for edges in candidates:
        fits = feasible(edges)
        inside_double_star = any(edges & star == edges for star in double_stars)
        assert fits == inside_double_star, (edges, fits, inside_double_star)
        if fits:
            is_star = any(edges & star == edges for star in STARS)
            counts[size(edges), is_star] += 1
    assert sum(counts.values()) == 5434 and max(k for k, _ in counts) == 7
    print("Every feasible family fits in an incident double star, and conversely.")
    print("Distinct nonempty feasible families:", sum(counts.values()))
    print("Distinct nonempty subsets of two stars:", len(candidates))
    print("Counts by (flag count, contained in one star):", sorted(counts.items()))


if __name__ == "__main__":
    main()

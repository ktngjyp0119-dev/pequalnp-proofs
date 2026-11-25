"""Optimal quadrangle test families for minimal terms of widths 1, 2, 3.
Run with Python 3, without -O (assertions provide the verification).
Point variables are 0..12; line variables are 13..25.
"""
from itertools import combinations

N = 13
points = range(N)
lines = [{(t + d) % N for d in (0, 1, 3, 9)} for t in points]
flags = {frozenset((p, N + l)) for l, line in enumerate(lines) for p in line}
rows = {}
for quad in combinations(points, 4):
    q = set(quad)
    if all(len(q & line) <= 2 for line in lines):
        missing = [l for l, line in enumerate(lines) if line.isdisjoint(q)]
        assert len(missing) == 3
        rows[quad] = q | {N + l for l in missing}

assert len(rows) == 234 and len(flags) == 52
universe = set(range(2 * N))
five = [(0, 1, 7, 10), (0, 2, 4, 6), (1, 4, 5, 9),
        (3, 4, 10, 11), (6, 8, 11, 12)]
assert set.union(*(rows[q] for q in five)) == universe
assert 4 * 3 < N  # four rows cannot cover all line variables

def orbit(quad):
    return {tuple(sorted((p+t) % N for p in quad)) for t in points}

def covered_pairs(quads):
    return {frozenset(pair) for q in quads for pair in combinations(rows[q], 2)}

nonflags = {frozenset(pair) for pair in combinations(universe, 2)} - flags
assert len(nonflags) == 273
sample = orbit((0, 1, 4, 6)) | orbit((0, 1, 5, 11))
assert len(sample) == 26 and covered_pairs(sample) == nonflags
assert 25 * 3 < N * (N-1) // 2  # each row contains three unordered line pairs
representatives = sorted({min(orbit(q)) for q in rows})
assert len(representatives) == 18
good = [(q, r) for q, r in combinations(representatives, 2)
        if covered_pairs(orbit(q) | orbit(r)) == nonflags]
assert good == [((0, 1, 4, 6), (0, 1, 5, 11)),
                ((0, 1, 4, 6), (0, 1, 8, 10))]

for q, row in rows.items():
    triple = {v for v in row if v >= N}
    assert len(triple) == 3
    assert set(q) == set(points) - set.union(*(lines[v-N] for v in triple))
    assert sum(triple <= other for other in rows.values()) == 1

# For width >= 3, the goal certified here is rejection on every quadrangle.
# All quadrangles together do not rule out every larger nonincident term.
print(f'{len(flags)} flags, {len(rows)} quadrangles, {len(nonflags)} nonflag pairs')
print('Minimum negative tests for rejection on all quadrangles: width 1 = 5, width 2 = 26, width 3 = 234')
print(f'{len(good)} pairs of whole translation orbits cover every nonflag pair')

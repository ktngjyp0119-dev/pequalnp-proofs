"""Exact checks on the Singer plane of order 3; run with Python 3, assertions on."""
from collections import Counter
from itertools import combinations

I = range(13)
LINES = [{(l+d) % 13 for d in (0, 1, 3, 9)} for l in I]
FLAGS = {(p, 13+l) for l in I for p in LINES[l]}
PAIRS = sorted(set(combinations(range(26), 2)) - FLAGS)
INDEX = {p: i for i, p in enumerate(PAIRS)}
FULL = (1 << len(PAIRS)) - 1
SAMPLE = [
    (1,2,5,7,16,21,23), (1,3,4,7,22,23,25), (3,5,6,14,21,24,25),
    (0,2,4,11,18,20,22), (0,4,8,15,19,22,24), (7,9,12,14,15,18,23),
    (1,8,9,10,15,16,17), (2,6,10,12,13,17,21), (0,3,10,18,19,21,24),
    (2,3,9,17,18,23,24), (4,5,12,13,19,20,23), (1,5,10,16,19,21,25),
    (0,5,9,11,14,16,20), (0,2,7,16,18,21,22), (4,6,9,15,20,24,25),
    (4,7,10,11,13,18,25), (2,5,8,13,16,23,24), (3,8,11,12,14,17,19),
    (1,6,11,17,20,22,25), (0,1,6,12,15,20,21), (6,7,8,13,14,15,22)
]
def negatives():
    out = set()
    for mask in range(1 << 13):
        points = {p for p in I if mask >> p & 1}
        missing = {l for l in I if points.isdisjoint(LINES[l])}
        if set(I) - points != {p for l in missing for p in LINES[l]}: continue
        if any(points <= line for line in LINES): continue
        if any(all(p in LINES[l] for l in missing) for p in I): continue
        out.add(tuple(sorted(points | {13+l for l in missing})))
    return out

def pack(row):
    return sum(1 << INDEX[p] for p in combinations(row, 2))

def dual(row):
    return tuple(sorted((13 if i < 13 else 0) + (-i) % 13 for i in row))

def mul3(row):
    return tuple(sorted((13 if i >= 13 else 0) + (3*i) % 13 for i in row))

def orbit(r):
    base = [r, mul3(r), mul3(mul3(r))]
    return tuple(sorted(set(base + [dual(v) for v in base])))

def union(masks):
    out = 0
    for m in masks: out |= m
    return out

def main():
    rows = negatives()
    assert len(FLAGS) == 52 and len(PAIRS) == 273
    assert Counter(sum(v < 13 for v in r) for r in rows) == {3:234, 4:234}
    assert union(pack(r) for r in rows) == FULL
    assert len(set(SAMPLE)) == len(SAMPLE) and set(SAMPLE) <= rows
    assert union(map(pack, SAMPLE)) == FULL
    groups = {orbit(r) for r in rows}
    assert all(set(g) <= rows for g in groups)
    assert Counter(map(len, groups)) == {2:3, 6:77}
    starts = [(0,1,7,15,16,21,22), (0,2,5,6,20,21,24), (0,4,10,12,15,18,19),
              (1,2,6,11,17,20,22), (1,3,4,8,19,22,23)]
    symmetric = {r for s in starts for r in orbit(s)}
    assert len(symmetric) == 22 and symmetric <= rows
    assert union(map(pack,symmetric)) == FULL
    small = [union(map(pack,g)) for g in groups if len(g)==2]
    large = [union(map(pack,g)) for g in groups if len(g)==6]
    tested = 0
    for i in range(4):
        for ss in combinations(small,i):
            sm = union(ss)
            for j in range((21-2*i)//6 + 1):
                for ll in combinations(large,j):
                    assert (sm | union(ll)) != FULL
                    tested += 1
    assert tested == 316632
    assert 17*9 < 156
    print(f'{len(rows)} generic rows; {len(SAMPLE)} explicit rows cover all {len(PAIRS)} nonflag pairs.')
    print(f'Under the two symmetries the exact minimum is 22; {tested} smaller orbit unions checked.')
    print('Unrestricted lower bound: 18.')
if __name__ == '__main__':
    main()

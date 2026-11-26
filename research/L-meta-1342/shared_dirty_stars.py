"""Enumerate shared disjunctions feeding at least three productive dirty AND gates.
Vertices are numbered as in L-meta-1342. Python 3, assertions enabled.
"""
from collections import Counter
from itertools import combinations

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
N = [0]*11
for u,v in EDGES:
    N[u] |= 1 << v
    N[v] |= 1 << u
POSITIVES = [(1<<u) | (1<<v) for u,v in EDGES]
assert all((a & b).bit_count() <= 1 for a,b in combinations(N,2))

def star(x, c, u):
    return bool((x & (1 << c)) and (x & u))

def graph(x):
    return any(x & e == e for e in POSITIVES)

def subsets(options):
    for k in range(3, len(options)+1):
        yield from combinations(options, k)

def main():
    histogram = Counter()
    profitable = []
    guard_overhead = Counter()
    best = None
    assignments = range(1 << 11)
    graph_values = [graph(x) for x in assignments]
    assert sum(graph_values) == 1923
    for u in range(1,1<<11):
        options = []
        for c in range(11):
            neighbors = u & N[c]
            if u >> c & 1 or neighbors.bit_count() < 2 or neighbors == u:
                continue
            options.append(c)
            # On every minimal positive both stars agree. The cleaned star never
            # fires spuriously. Each original star has a false-pair witness.
            assert all(star(x,c,u) == star(x,c,neighbors) for x in POSITIVES)
            false_vertex = (u & ~neighbors) & -(u & ~neighbors)
            witness = (1 << c) | false_vertex
            assert star(witness,c,u) and not graph_values[witness]
        for centers in subsets(options):
            clean_or = sum((u & N[c]).bit_count()-1 for c in centers)
            dirty_or = u.bit_count()-1
            saving = clean_or - dirty_or
            histogram[saving] += 1
            guard_overhead[len(centers) - saving] += 1
            if saving > 0: profitable.append((u,centers,saving))
            if best is None or saving > best[2]: best=(u,centers,saving)
    print('Distinct (neighbor pool, centers) choices:',sum(histogram.values()))
    print('Clean OR cost minus shared dirty OR cost:',sorted(histogram.items()))
    assert sum(histogram.values()) == 3207 and len(profitable) == 473
    assert max(histogram) == 3 and histogram[3] == 2
    assert min(guard_overhead) == 2 and guard_overhead[2] == 201
    print('Positive savings:',len(profitable))
    print('Least extra cost with a private AND guard per star:',min(guard_overhead))
    print('Maximum and example:',best[2], [i for i in range(11) if best[0] >> i & 1],best[1])
    # One common disjunction H over raw variables can clean all dirty outputs
    # and retain every originally accepted flag iff no required variable is also
    # forbidden. Test this exact criterion on all choices with positive savings.
    common = []
    for u,centers,s in profitable:
        required=0
        forbidden=0
        for c in centers:
            required |= u & N[c]
            forbidden |= (1<<c) | (u & ~N[c])
        if not required & forbidden:common.append((u,centers,s))
    assert not common
    print('Profitable choices permitting one common OR guard:',len(common))

if __name__=='__main__':
    main()

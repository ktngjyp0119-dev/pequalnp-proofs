"""If 18 generic rows suffice, their family has no nonidentity plane symmetry.
Run next to generic_rows.py with Python 3 and assertions enabled.
"""
from itertools import combinations, permutations
from generic_rows import I, LINES, PAIRS, dual, negatives

point_pairs = list(combinations(I, 2))
line_pairs = list(combinations(range(13,26), 2))
cross_pairs = [pair for pair in PAIRS if pair[0] < 13 <= pair[1]]
all_pairs = point_pairs + line_pairs + cross_pairs
index = {pair: i for i,pair in enumerate(all_pairs)}
same_side = (1 << 156) - 1
full = (1 << 273) - 1
identity = tuple(range(26))
duality = tuple(dual([i])[0] for i in range(26))
rows = sorted(negatives())
join_lookup = {p:l for l,line in enumerate(LINES) for p in combinations(sorted(line),2)}
meet_lookup = {(l,k):next(iter(LINES[l]&LINES[k])) for l,k in combinations(I,2)}

def intersect(a,b,c,d):
    l=join_lookup[tuple(sorted((a,b)))]; k=join_lookup[tuple(sorted((c,d)))]
    return None if l==k else meet_lookup[tuple(sorted((l,k)))]

def frame_construction():
    points = [0,1,4,6]
    steps = []
    while len(points)<13:
        pairs=list(combinations(range(len(points)),2))
        for (a,b),(c,d) in combinations(pairs,2):
            p=intersect(points[a],points[b],points[c],points[d])
            if p is not None and p not in points:
                steps.append((a,b,c,d)); points.append(p); break
        else:
            raise AssertionError('frame did not generate the plane')
    return points,steps

def compose(g,h):
    return tuple(g[i] for i in h)

def inverse(g):
    result=[0]*len(g)
    for i,j in enumerate(g): result[j]=i
    return tuple(result)

def plane_group():
    points,steps=frame_construction()
    lookup={tuple(sorted(line)):l for l,line in enumerate(LINES)}
    group=set()
    for r in rows:
        quad=tuple(v for v in r if v<13)
        if len(quad)!=4: continue
        for ordered in permutations(quad):
            image=list(ordered)
            for a,b,c,d in steps:
                image.append(intersect(image[a],image[b],image[c],image[d]))
            assert set(image)==set(I)
            perm=dict(zip(points,image))
            g=tuple(perm[p] for p in I)+tuple(13+lookup[tuple(sorted(perm[p] for p in l))] for l in LINES)
            group.add(g)
    assert len(group)==5616
    group.update([compose(duality,g) for g in group])
    assert len(group)==11232
    return group

def cyclic(g):
    h=g; group=[identity]
    while h!=identity:
        group.append(h);h=compose(g,h)
    return group

def has_cover(g):
    """Exact enumeration of orbit unions of cost at most 18, using safe pruning."""
    h=cyclic(g)
    orbits=sorted({tuple(sorted({tuple(sorted(t[v] for v in r)) for t in h})) for r in rows})
    assert sum(map(len,orbits))==468 and all(r in row_set for orb in orbits for r in orb)
    weights=[len(o) for o in orbits]
    masks=[sum(1<<index[p] for p in {p for r in orb for p in combinations(r,2)}) for orb in orbits]
    choices=[sum(1<<i for i,m in enumerate(masks) if m>>j&1) for j in range(273)]
    def bits(s):
        while s:
            bit=s & -s
            yield bit.bit_length()-1
            s-=bit
    def visit(covered,remaining,budget):
        if covered==full: return True
        if not budget: return False
        # Each row contributes at most nine same-side and 21 total pairs.
        eligible=0
        for i in bits(remaining):
            left=budget-weights[i]
            if left<0: continue
            merged=covered | masks[i]
            if (merged & same_side).bit_count()+9*left<156: continue
            if merged.bit_count()+21*left<273: continue
            eligible |= 1<<i
        pivot=min((choices[j]&eligible for j in bits(full ^ covered)),key=int.bit_count)
        for i in bits(pivot):
            remaining ^= 1<<i
            if visit(covered|masks[i],remaining,budget-weights[i]): return True
        return False
    return visit(0,(1<<len(orbits))-1,18)

row_set=set(rows)
def main():
    group=plane_group()
    left=group-{identity}
    checked=[]
    while left:
        g=min(left)
        conjugates={compose(t,compose(g,inverse(t))) for t in group}
        left-=conjugates
        order=len(cyclic(g))
        # Every finite nontrivial stabilizer contains an element of prime order.
        if any(order%d==0 for d in range(2,int(order**0.5)+1)): continue
        assert not has_cover(g)
        checked.append(order)
    assert sorted(checked)==[2,2,3,3,13,13]
    print('11,232 incidence-graph symmetries; six prime-order conjugacy classes.')
    print('No family of at most 18 rows fixed by a nonidentity symmetry covers all 273 pairs.')
if __name__=='__main__':
    main()

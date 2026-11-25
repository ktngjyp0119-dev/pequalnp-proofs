"""Run with Python 3. No dependencies. Wire numbers start at zero."""
from itertools import combinations

def build(lines):
    gates = []
    n = 14
    def gate(op, a, b):
        gates.append((op, a, b))
        return n + len(gates) - 1
    def points(l):
        return gate('|', gate('|', l, (l+1)%7), (l+3)%7)
    def star(l):
        return gate('&', points(l), 7+l)
    t = star(lines[0])
    l = lines[1]
    a = gate('|', t, points(l))
    b = gate('|', t, 7+l)
    out = gate('&', a, b)
    for l in lines[2:]:
        out = gate('|', out, star(l))
    return gates, out

def run(lines):
    gates, out = build(lines)
    flags = [(p,l) for l in lines for p in (l,(l+1)%7,(l+3)%7)]
    inputs = [[bool(i & (1<<j)) for j in range(14)] for i in range(1<<14)]
    expected = [any(x[p] and x[7+l] for p,l in flags) for x in inputs]
    def pack(values):
        return sum(1<<k for k,v in enumerate(values) if v)
    def signatures(rows):
        return [pack(x[j] for x in rows) for j in range(14)]
    def value(op,a,b):
        return a&b if op=='&' else a|b
    def eval_gates(start):
        w=start.copy()
        for op,a,b in gates:
            w.append(value(op,w[a],w[b]))
        return w
    assert eval_gates(signatures(inputs))[out] == pack(expected)
    def derivative(op,a,b):
        av,ad=a
        bv,bd=b
        return (av&bv,(av&bd)|(ad&bv)) if op=='&' else (av|bv,ad|bd)
    # One bit per flag in each direction, point singleton first, then line singleton.
    cases=[(p,7+l) for p,l in flags]+[(7+l,p) for p,l in flags]
    dw=[(pack(i==a for a,b in cases),pack(i==b for a,b in cases)) for i in range(14)]
    for op,a,b in gates:
        dw.append(derivative(op,dw[a],dw[b]))
    def double(mask):
        return [pl for i,pl in enumerate(flags) if not (mask>>i&1 or mask>>(i+len(flags))&1)]
    print(f'{len(lines)} lines, {len(gates)} gates, all 16384 rows correct, double reads {double(dw[out][1])}')
    assert (0,0) in double(dw[out][1])
    rows=[i for i,hit in enumerate(expected) if (hit and i.bit_count()==2) or
          (not hit and all(expected[i|(1<<j)] for j in range(14) if not i>>j&1))]
    sw=eval_gates(signatures([inputs[i] for i in rows]))
    goal=pack(expected[i] for i in rows)
    # Every gate is monotone. Agreement on minimal positives and maximal negatives
    # implies agreement everywhere. For every three-gate region with one external
    # output, try every replacement of size 0, 1 or 2 over its original input wires.
    regions=valid=equal=survivors=0
    for triple in combinations(range(14,14+len(gates)),3):
        region=set(triple)
        exits={w for i,(_,a,b) in enumerate(gates,14) if i not in region
               for w in (a,b) if w in region}
        if out in region: exits.add(out)
        if exits!={triple[-1]}: continue
        regions+=1
        root=triple[-1]
        boundary=sorted({w for i in triple for w in gates[i-14][1:] if w not in region})
        def candidates():
            for a in boundary: yield [],a
            for a,b in combinations(boundary,2):
                for op in '&|':
                    first=(op,a,b)
                    yield [first],-1
                    for c in boundary:
                        for op2 in '&|':yield [first,(op2,-1,c)],-2
        for local,exitwire in candidates():
            # A direct bypass can make a retained gate read a wire twice.
            if not local and any(i not in region and {a,b}=={exitwire,root}
                                 for i,(_,a,b) in enumerate(gates,14)): continue
            valid+=1
            def result(w,apply):
                w=dict(enumerate(w))
                for k,(op,a,b) in enumerate(local,1):
                    w[-k]=apply(op,w[a],w[b])
                w[root]=w[exitwire]
                for i in range(root+1,14+len(gates)):
                    op,a,b=gates[i-14]
                    w[i]=apply(op,w[a],w[b])
                return w[out]
            if result(sw,value)!=goal:continue
            equal+=1
            survivors+=bool(double(result(dw,derivative)[1]))
    print(f'{len(rows)} boundary rows; {regions} regions; {valid} legal descriptions; '
          f'{equal} preserve incidence; {survivors} also retain a double read.')
    return survivors

if __name__=='__main__':
    for lines in (list(range(2)),list(range(3)),list(range(4)),list(range(5)),list(range(6)),list(range(7))):
        run(lines)

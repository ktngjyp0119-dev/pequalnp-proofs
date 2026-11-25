"""Reproduce a 12-gate monotone upper bound and an 11-gate local search.

Every integer signature stores the values on all 128 assignments in its bits.
Run with Python 3. Gates use input wires 0..6; the last gate is the output.
"""

edges = [(0,3), (1,3), (0,4), (2,4), (0,5), (1,5), (3,5), (4,5),
         (1,6), (2,6), (3,6), (4,6)]
base = [('|',3,4), ('|',7,5), ('|',7,1), ('|',5,6), ('|',4,6),
        ('&',0,8), ('&',1,3), ('&',2,11), ('&',9,10),
        ('|',12,13), ('|',14,15), ('|',16,17)]
mask = (1 << 128) - 1
inputs = [sum(1 << x for x in range(128) if x & (1 << i)) for i in range(7)]
goal = sum(1 << x for x in range(128) if any(x >> a & x >> b & 1 for a, b in edges))

def evaluate(circuit, output):
    wires = inputs.copy()
    for op, a, b in circuit:
        if op == '!':
            v = mask ^ wires[a]
        elif op == '&':
            v = wires[a] & wires[b]
        else:
            v = wires[a] | wires[b]
        wires.append(v)
    return wires[output]

def bypass(deleted, source):
    def new(wire):
        if wire == 7 + deleted:
            return source
        return wire - (wire > 7 + deleted)
    return ([(op,new(a),new(b)) for i,(op,a,b) in enumerate(base) if i != deleted],
            new(7 + len(base) - 1))

def search():
    assert evaluate(base, 18) == goal
    tried = {'binary':0, 'not':0}
    matches = {'binary':0, 'not':0}
    for deleted in range(len(base)):
        for source in range(7 + deleted):
            circuit, out = bypass(deleted, source)
            for i, original in enumerate(circuit):
                # All distinct pairs, plus repeated inputs (a binary pass-through).
                choices = [('!',a,a) for a in range(7+i)]
                choices.extend((op,a,b) for a in range(7+i) for b in range(a,7+i)
                               for op in ('&','|'))
                for candidate in choices:
                    kind = 'not' if candidate[0]=='!' else 'binary'
                    tried[kind] += 1
                    circuit[i] = candidate
                    if evaluate(circuit, out) == goal:
                        matches[kind] += 1
                circuit[i] = original
    return tried, matches

if __name__ == '__main__':
    counts, correct = search()
    print('12-gate baseline verified on 128 inputs;', goal.bit_count(), 'positives')
    print('11-gate edit descriptions and matches (descriptions may overlap):')
    for kind in counts:
        print(kind, counts[kind], correct[kind])

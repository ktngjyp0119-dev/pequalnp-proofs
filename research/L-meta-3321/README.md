# Clean optimal circuits for all 334 four-cycle-free 3-by-3 incidences

A computational case study for L-meta-3321. Vertices are labelled. A circuit accepts a set of active vertices if the set contains both endpoints of an edge. We count fan-in-at-most-two monotone AND and OR gates. For each eligible graph the script constructs a minimum-size circuit in which every AND firing already certifies an active edge. Consequently every AND is false on singleton inputs and satisfies the posted cleanliness condition. The unrestricted theorem and upstream Lean verification remain open in this note.

| Minimum gates | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Number of labelled graphs | 1 | 9 | 18 | 24 | 72 | 87 | 45 | 72 | 6 |

## Reproduce

Run `node check-cover-two.mjs` from this directory using Node.js 18 or later. No dependencies are required. The script tests every candidate circuit on every Boolean assignment, checks that gates read earlier wires, and checks each AND separately. Its independent breadth-first synthesis on all 54 four-cycle-free 2-by-3 graphs gives counts 1, 6, 9, 8, 18 and 12 at sizes zero through five.

## Upper bound

Find a minimum vertex cover and assign each edge to one of its endpoints in the cover. Form one term per center by ANDing the center with the OR of its assigned neighbors. OR the terms. Every AND in this circuit implies an edge. With e edges and k nonempty centers it uses e + k − 1 gates. The empty case uses the project's out-of-range false output wire and no gates.

## Lower bound and enumeration

Every nonisolated vertex is an essential input, witnessed by activating a single neighbor. Replace isolated inputs by zero, simplify constants, remove useless gates, and restrict to the output cone. For a nonempty edge function a minimum circuit then has binary gates. If v inputs are essential and g gates are used, connectedness of the cone and the count of its 2g incoming edges imply g ≥ v − 1. The total number of uses of signals beyond their first uses is g − v + 1, counting all nodes except the output.

At g = v − 1 the circuit is a read-once formula. The script builds its possible truth tables by partitioning each leaf set into disjoint children. At g = v exactly one signal is used twice. Its input leaves form an exclusive block B; the upper formula uses the signal twice and every remaining variable once. For fixed external inputs, every nonconstant section on B must equal the same inner function by monotonicity. Conversely the outer truth table is obtained by setting the block to all zeros or all ones. The checker tests both the inferred inner and outer functions by formula enumeration. If the shared signal is an input, B has size one. Upper and lower bounds meet in 328 of the 334 cases.

The six remaining graphs are cycle graphs on six vertices. The constructions use eight gates. A seven-gate minimum circuit on six essential inputs would have exactly two excess uses. Exhaust the following alternatives.

1. No internal wire is reused. The formula has eight leaves. One input occurs three times or two inputs occur twice each. Up to cycle symmetries the repeated inputs have distance 0, 1, 2, or 3. None of the four truth-table searches realizes the cycle.
2. Consider the first reused internal wire in topological order. If all its input variables reach the output only through this wire, every nonconstant section on its block of inputs agrees. The checker rules this out on every proper block of size at least two. A one-variable monotone wire is redundant. A block containing every variable and having no other way out would make the entire suffix redundant.
3. Otherwise an input is used both inside and outside that wire's subcircuit. These two forks account for both excess uses. Rotate the shared input to vertex zero. The inner formula is read-once on that input and a nonempty set of private inputs. For each fixed value of the shared input, every nonconstant section on the private inputs must equal the same restriction of the inner formula. Exhausting all 8,474 block and inner-table combinations rules out all of them.

## Arbitrary graph size with vertex cover at most two

A four-cycle-free bipartite graph covered by at most two vertices is a forest: a cycle of length at least six requires at least three cover vertices. A nonempty disjoint union of stars has optimum v − 1 by the construction and the connected-cone lower bound. If a nonstar component exists it alone needs both centers, is a tree on v nonisolated vertices, and has v − 1 edges. The two-center construction costs v gates.

For the matching lower bound, this tree contains an induced path on four vertices. Restrict all other variables to zero. A read-once formula remains read-once after constant simplification. It cannot realize the four-vertex path: a root OR allows no edge between its disjoint variable groups, contradicting connectedness. A root AND forces a complete bipartite graph across the two groups. Both children are zero on the all-zero input; every edge must cross the groups, and as every vertex is incident to an edge both children accept every singleton on their own sides. The four-vertex path is not complete bipartite. Equality at v − 1 is therefore impossible.

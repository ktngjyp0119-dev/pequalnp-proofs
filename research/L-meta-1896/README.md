# Generic negative tests and OR counts on the order-three plane

A positive input selects a point together with an incident line. A generic negative selects a point set X and all lines missing X. Each point outside X must lie on a selected line, X must not lie on a single line, and the selected lines must not all contain a common point. There are 468 such negative inputs, split equally between 4 points plus 3 lines and 3 points plus 4 lines.

## Negative test families

The explicit 21-row family in GenericTestSample.lean covers all 273 distinct pairs other than flags, as well as every singleton. For a monotone predicate in which every true input contains a true subset of size at most two, testing these negatives and the 52 positive flags determines the answer on every input. Indeed, a false acceptance on an input containing no flag has a witness of size zero, one or two. Some selected negative contains that witness and would be accepted. A true flag forces acceptance of every input containing it by monotonicity.

The unrestricted minimum lies between 18 and 21. There are 78 point pairs and 78 line pairs, and each eligible row covers only nine same-side pairs. Seventeen rows therefore fall short. If the selected family is invariant under simultaneous multiplication of indices by three and under the duality exchanging point p with line −p, the exact minimum is 22. The Python program checks a 22-row witness and every one of the 316,632 smaller unions of whole orbits. The 21-row family does not have to respect those symmetries.

### An 18-row solution would have to break every plane symmetry

The incidence graph is connected and bipartite, so an automorphism preserves the point and line parts or interchanges them. A part-preserving automorphism is determined by an ordered quadrangle: starting with the four vertices, intersections of their joining lines generate all 13 points. The checker builds this generating sequence and verifies the image of every line for all 5,616 ordered quadrangles. Composing with point-line duality gives all 11,232 incidence-graph symmetries.

Any nontrivial stabilizer of a family contains an element of prime order. There are six prime-order conjugacy classes, with orders 2, 2, 3, 3, 13 and 13. For each representative, the checker searches families made of whole orbits. It branches on an uncovered pair and tests the orbit choices that could cover it. At most nine same-side pairs and 21 total pairs can be added per remaining row. Exhausting all six searches rules out a symmetric 18-row family. A possible asymmetric 18-row family remains open.

## Why one layer of AND gates needs exactly 51 OR gates

This result concerns circuits in which no live input-to-output path passes through two AND gates. It allows arbitrary OR sharing. The general lower bound in L-meta-1896 allows nested AND gates.

1. Prune dead gates, propagate constants, and bypass unary gates, repeated operands and OR subcircuits supported on just one variable. These operations preserve the function and do not increase size. A variable connected directly through ORs to the output would accept its singleton, and every singleton lies in a tested negative. The output must therefore be a disjunction of products. Each product is an AND of two nonempty disjunctions of variables.
2. The two operand disjunctions have disjoint supports because a common variable would accept a singleton. Every pair across the two supports is a flag: any other pair lies in a rejected input. It follows that one side consists entirely of points and the other entirely of lines. The product is a star, since two different points cannot share two different lines. Choose a center on a singleton side, breaking the tie arbitrarily for a single edge.
3. A live lower OR has at least two different variables in its support. It can serve the neighborhood side of stars only at one center: two points determine at most one common line, and two lines determine at most one common point. Its raw variable inputs can therefore be tagged by the corresponding flags consistently across fan-out. Lower ORs cannot also feed the output along an AND-free path because that would accept a singleton.
4. Write k for the number of lower ORs, m for the number of products and t for the number of upper ORs. All 52 flag labels occur on the neighborhood side of some product because the circuit accepts every two-variable flag input. Each of these labels and each lower OR output occurs in an operand position of a lower OR or as the neighborhood root of a product. Thus 52 + k ≤ 2k + m. Likewise, every product output and upper OR output occurs at an upper OR operand or is the final output, giving m + t ≤ 2t + 1. Combining gives 51 ≤ k + t.
5. The explicit circuit uses three ORs to combine the four points on each of 13 lines, one AND per line, and twelve ORs to combine the resulting stars. It has 51 OR and 13 AND gates and computes incidence on all inputs.

## Verification

* GenericTestSample.lean formally checks that the 21 point sets are distinct, that all rows satisfy the generic negative conditions, and that every required pair is covered.
* StarOrBudget.lean proves uniqueness of the center, rectangular soundness from mixed-pair coverage, and the gate-count inequalities given the finite operand and root sets. The pruning and tagging that produce these sets from an arbitrary single-AND-layer circuit are the written argument above.
* StarWitness.lean uses the project's circuit type. It proves legality, counts, and equality to incidence on all 26-input assignments.
* eighteen_symmetry.py verifies the obstruction for all nonidentity symmetries using integer bit sets. Run it alongside generic_rows.py.
* generic_rows.py independently enumerates the generic inputs and checks the stated covers and symmetry-restricted optimum with exact integer arithmetic. Run with Python 3 and assertions enabled.

The Lean files were tested with project revision 1738dd7e4d5a6a52ceca99852b852c25d6236de4. From its lean directory, after building PEqualNP.Defs and Mathlib.Tactic, run lake env lean followed by the path to each file.

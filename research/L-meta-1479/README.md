# Double reads on the Fano incidence function

The pinned project uses Lean 4.36.0. The file Fano28.lean proves the exact formula of L-meta-1479 with the budget changed from 27 to 28. It supplies all 28 AND/OR gates, proves correctness for every assignment, and gives both directional traces at the incident pair (0,0).

A usual line star is its line bit AND the OR of its three point bits. Let T be the star for line 0, P the OR of the point bits on line 1, and L the line-1 bit. Combine the first two stars as (T OR P) AND (T OR L), then append the five remaining stars using OR. The formula computes the union of all stars. At either singleton of the flag (0,0), both operands of the displayed AND are false. The directional derivative of this AND is zero in both directions. No other line star reads the input pair as an edge. Direct evaluation also finds the double read (3,0).

## An exact two-line result

Keep lines 0 and 1 only. Their stars share one point. The resulting graph is connected and uses seven essential inputs. The construction above uses eight gates. Eight is the minimum for the two-line function with a double read, by the following gate-count argument.

Consider a connected simple graph on n essential input vertices. Trim a fan-in-two AND/OR circuit to the gates feeding its output. If it has g gates, there are 2g operand occurrences and n+g−1 wires that must be read at least once (all inputs and all gates except the output). Thus g≤n allows at most one additional read. With no additional read, expanding the circuit as a formula reads each variable only once.

At a true two-endpoint input there is a proof tree: keep one true operand at each OR and both at each AND. Every such tree uses both endpoints, since both singleton inputs are false. If one endpoint occurs only once in the expanded formula, it occurs exactly once in this tree. The directional trace seeded at that endpoint, at the other singleton, is then true. Follow the unique occurrence up the selected tree: the other branch at each AND remains true without the seed bit, and OR propagates the true trace. Thus a double read requires *both* endpoints to occur more than once in the expansion.

With exactly one additional read, only one wire can be read twice. Both endpoints must feed that wire, since all repeated occurrences arise in its expanded subtree. Let S be the inputs feeding this wire. Their sole connection to the rest of the circuit is this wire. When every outside input is zero, the output is a monotone function of its single value, and is nonconstant because the empty assignment is false and the selected edge is true. It must be the identity. The shared wire therefore evaluates to false on every singleton in S. Any edge crossing from S to its complement would make its outside singleton and the full edge indistinguishable at the output, a contradiction. By connectivity S contains every input. The first gate after the shared wire would have to read it twice: a second distinct wire from its subtree would itself have to be read again. The project requires distinct operands. This rules out g≤n.

The seven essential inputs must all be in the output cone. If the two-line circuit also uses any of the inactive input wires, a seven-gate cone has at least eight input wires and allows no additional read at all. Thus the lower bound also holds with all 14 input positions available.

More generally, for two lines of arbitrary degrees sharing exactly one point, choose an endpoint on the first line outside the second. Provided the first line has at least two points, the same construction costs n+1 gates and the same lower bound is sharp. For distinct-operand implementations with singleton point groups, use the point wire directly for the OR of a single point.

## Finite search

Run search.py with Python 3. The script checks every one of the 16,384 assignments and computes both traces on every flag. It tests six successive sets of lines. It also tries replacing three gates having just one external output by any circuit with at most two live gates over their original incoming wires. Two-gate candidates enumerate both operators and both operands up to commutativity. Candidates must retain distinct operands.

For the full seven-line witness there are 29 such regions. Exactly one of 3,181 legal descriptions keeps the incidence truth table, and it loses the double read. For each of the other five sizes the same experiment also finds exactly one truth-table-preserving description and no solution with a double read. The scope is a local edit family. The existence of a different 27-gate full-plane witness remains open.

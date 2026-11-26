# A shared first disjunction for three or more dirty stars

This calculation concerns shard 1 of L-meta-1342. Its target is a binary monotone circuit of at most 21 gates for the specified 11-vertex graph. A dirty AND is an AND gate which is true on some input containing no edge.

Consider a nonempty vertex pool U, a binary OR tree combining its variables, and at least three distinct center vertices outside U. Center c takes the AND of its variable with the common OR. Write d(c) for the number of its neighbors in U. Restrict to 2 ≤ d(c) < |U|. The dirty gate then accepts at least two minimal positive inputs (edges) and at least one nonedge pair. A clean version uses only the d(c) genuine neighbors as its OR operands. It agrees on all minimal positives and its true inputs are a subset of those of the dirty star.

## Counts and a local rewrite

There are 3,207 pairs consisting of such a pool and an eligible center set for this labeled graph. Replacing separate clean input ORs by the unguarded common OR saves gates in 473 cases, with a maximum saving of three, attained in two cases. One example uses the pool {0,2,4,6,7,8} and centers {1,3,5,9,10}.

Suppose the pool OR and its intermediate wires are dedicated to these stars, the dirty stars have no other consumers, and each is followed by its own AND with a monotone guard that preserves all of its genuine edges. The shared construction pays at least |U|−1 + 2|C| gates before charging for any guard computation. Building the separate clean stars costs at most the sum of d(c) over C. For every one of the 3,207 choices, the former count exceeds the latter by at least two. This even allows arbitrary reuse of the guard computations elsewhere: no saving from deleting them is needed.

The replacement preserves the enclosing circuit's correctness if that circuit recognized the edge function. On every minimal positive edge the guarded output and the corresponding clean replacement agree. On every assignment, a true clean replacement contains a genuine edge for that star, so monotonicity and the guard hypothesis imply that the guarded output was also true. The enclosing monotone circuit therefore retains all positive edge inputs and cannot introduce a false positive. Consequently a size-minimal circuit cannot have this entire dedicated, individually guarded arrangement. More elaborate downstream uses of the dirty wires are still possible.

A single shared OR of raw variables as a guard would have to omit every center (or it would pass a false pair) and, within U, include exactly the neighbor set of each center. The graph has no four-cycle, so two different centers have at most one common neighbor. Their neighbor sets, each of size at least two, cannot be identical.

## Reproduction

Run shared_dirty_stars.py with Python 3 and assertions enabled. The checker enumerates all pools and center sets, verifies positive support and false witnesses, and checks the counts. It finds 201 choices giving a two-gate gap when all guard computations have zero charge.

SharedDirtyStars.lean checks the arithmetic bound with the actual neighbor lists. For a fixed pool, the sum of d(c)−2 is maximized by including all eligible centers since every term is nonnegative. Lean checks the 2,048 vertex masks and proves the resulting inequality for every subset of at least three centers. It also checks an equality case, with U = {0,4,5} and centers {8,9,10}. From the project's lean directory, run lake env lean followed by the file path with Mathlib.Tactic available. The embedding of the local gate count as a rewrite in a whole circuit is the written argument above.

# The rectangle cost after deleting flags in the order-three plane

## From rectangles to a graph invariant

Let F be any subset of the 52 flags. An admissible rectangle contains only true flags of the original plane and may cover flags outside F. Its cost is the number of rows plus the number of columns. Let m be the number of flags in F and let τ be the smallest number of points and lines meeting all flags of F. The least total cost of a rectangle cover is **m + τ**, including when F is empty.

Two distinct lines meet in just one point, so a nonempty admissible rectangle has one row or one column. Trim away any flags outside F and assign each flag covered more than once to just one rectangle. Each remaining rectangle is a star of k assigned flags and costs k+1. Its center covers every assigned flag, giving the lower bound m+τ. Conversely, start with a minimum vertex cover, assign each flag to one of its endpoints in the cover, and group by the chosen endpoint. The resulting rectangles have total cost at most m+τ. This proof applies to any bipartite graph without a four-cycle.

By König's theorem τ is also the maximum matching size. In the circuit-extraction child of PR 10876 the rectangle requirement is therefore equivalent to bounding m+τ by the circuit size plus one, where F consists of the accepted incident pairs. The circuit bound itself remains open.

## Exact costs for zero through four deletions

| Deleted flags | Minimum cover cost | Number of deletion sets |
| ---: | ---: | ---: |
| 0 | 65 | 1 |
| 1 | 64 | 52 |
| 2 | 63 | 1,326 |
| 3 | 62 | 22,100 |
| 4, all incident to one point or line | 60 | 26 |
| 4, every other pattern | 61 | 270,699 |

For each shift in {0,1,3,9} modulo 13, pairing line l with point l+shift gives a perfect matching. The four matchings are edge-disjoint. After deleting at most three flags at least one survives.

Suppose four deletions destroy every perfect matching. By Hall's theorem there is a nonempty point set U with fewer than |U| surviving neighbor lines. Call the set of those lines V. There were 4|U| flags at U and at most 4|V| of them can end in V. The four deletions therefore force |V|=|U|−1, and all four original points of every line in V belong to U.

Put k=|V|. If 1≤k≤11, write r(x) for the number of lines of V through point x. Then the sum of r(x) is 4k. Counting ordered pairs of distinct lines gives a sum of r(x)(r(x)−1) equal to k(k−1). By Cauchy–Schwarz the union of these lines has at least 16k/(k+3) points. This exceeds k+1 for every integer from 1 through 11, contradicting containment in U. For k=0, U is an isolated point. For k=12, U is all the points and the omitted line is isolated. Conversely, removing an entire point or line star destroys all perfect matchings. A matching of size 12 survives by dropping that vertex's edge from any original perfect matching. The 13 point stars and 13 line stars give the 26 exceptions.

The companion C++ program enumerates every deletion set of size at most four, computes maximum matching by augmenting paths, and checks the isolation criterion in each case. Compile with assertions enabled as indicated in the source.

Reference for the matching theorems: [Darij Grinberg, Lecture 24, §§1.3–1.4](https://www.cip.ifi.lmu.de/~grinberg/t/22s/lec24.pdf).

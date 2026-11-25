# Rectangle cover costs after up to seven flag deletions

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

## All obstructions after up to seven deletions

In the order-three plane a perfect matching fails after at most seven deletions if and only if the deletions contain at least one of the following 182 sets.

- All four flags at one point or one line (26 choices).
- For two points, their six flags off the unique line through them (78 choices). There are another 78 choices obtained by exchanging points and lines.

Each of the four disjoint shift matchings would have to lose two edges for the maximum matching size to fall below 12. Thus failure in this range means the maximum matching has size exactly 12. For r deletions, the rectangle cost is 65−r in the perfect case and 64−r in the deficient case.

| Deleted | Deficient sets | Perfect sets |
| ---: | ---: | ---: |
| 4 | 26 | 270,699 |
| 5 | 1,248 | 2,597,712 |
| 6 | 29,484 | 20,329,036 |
| 7 | 456,508 | 133,328,052 |

**Proof.** A Hall obstruction consists of u points U and u−1 lines V such that all flags from U to lines outside V have been removed. One can enlarge the surviving neighborhood to get exactly u−1 lines. Taking complementary sets on the opposite sides gives an obstruction of size 14−u, so by duality assume 1≤u≤7. Let e be the number of original flags between U and V. At least 4u−e deletions are necessary.

Write r(x) for the number of lines of V through point x in U. Then e is their sum. Since distinct lines meet once, the sum of r(x)(r(x)−1) over U is at most (u−1)(u−2). Cauchy–Schwarz gives e² ≤ u[e+(u−1)(u−2)]. For u=3,4,5,6,7 this implies e≤4,7,10,14,18 respectively. The corresponding cut costs at least 8,9,10,10,10, exceeding seven. For u=1 the cut is an entire star. For u=2, if the two points both meet the single allowed line, the cut is the listed six-flag set. Otherwise at least one point loses every incident flag. Each listed set conversely certifies a Hall obstruction.

The program hall_cuts.cpp independently generates cuts from every choice of U and V of the stated sizes on the original point side, including sizes 8 through 13. It removes redundant cuts, checks exact equality with the list above and counts distinct deletion sets containing at least one obstruction. This accounts for coincidences between patterns. It does not run one matching algorithm per seven-deletion set.

## Extension to planes of any finite order

In a projective plane of order q≥2, put N=q²+q+1. At most q deletions preserve a perfect matching: for a Hall obstruction with |V|=|U|−1 the degree count alone requires at least q+1 deletions. At exactly q+1 deletions, equality forces every point on every line in V to belong to U. Write k=|V|. The incidence count and the line-intersection count put at least (q+1)²k/(q+k) points in the union of the k lines when k>0. For 1≤k≤N−2 this exceeds k+1, since k(N−1−k)≥N−2>q. It contradicts |U|=k+1. The remaining possibilities k=0 and k=N−1 isolate a point or a line, and both patterns do destroy every perfect matching. Dropping the edge at the isolated vertex from an original perfect matching leaves N−1 matching edges. Thus the first matching failure and its exceptional deletion patterns are completely determined at every order for which a plane exists.

Background on the matching theorems: [Diestel, Graph Theory, chapter 2](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch2.pdf).

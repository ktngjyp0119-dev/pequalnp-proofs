# How many quadrangle negatives must be tested?

Consider the order-three projective plane in the project's Singer coordinates. An input selects some of the 13 points and 13 lines. Incidence accepts the input exactly when a selected point lies on a selected line. A quadrangle consists of four points, no three collinear. Its negative test selects its four points and every line disjoint from them. There are 234 such tests.

Say a monotone predicate has positive witnesses of width at most k if every accepted input contains an accepted subset of size at most k. Ask for the smallest subfamily of the 234 tests whose rejection implies rejection on all 234, for every predicate in that class.

| Maximum witness width | Minimum number of negative tests |
| --- | ---: |
| 1 | 5 |
| 2 | 26 |
| 3 or larger | 234 |

## Why these bounds hold

Each quadrangle's four points contribute 16 point-line incidences. Its six pairs lie on six different secants, each counted twice. The remaining four incidences are on four tangent lines. Exactly ten lines meet the quadrangle, leaving three disjoint lines.

At width one, all 26 variables must be covered. An uncovered variable, used as the entire predicate, escapes the selected tests and fails a quadrangle containing it. Four tests cover at most twelve lines. The five point sets below, together with their disjoint lines, cover every variable.

    (0,1,7,10)  (0,2,4,6)  (1,4,5,9)  (3,4,10,11)  (6,8,11,12)

At width two, every unordered pair of different variables except the 52 incident point-line pairs must be covered. These 273 pairs consist of 78 point pairs, 78 line pairs and 117 nonincident mixed pairs. Take the 13 cyclic translates of each of the two rows below. Add the shift modulo 13 to every index in both columns.

| Points | Disjoint lines |
| --- | --- |
| 0, 1, 4, 6 | 2, 7, 9 |
| 0, 1, 5, 11 | 3, 6, 7 |

These 26 rows cover every nonincident pair and every singleton. Thus every possible nonempty positive witness of width at most two on an incidence-negative input is contained in one of the rows. The empty witness is contained in every row. Monotonicity then detects any false acceptance. Conversely, each row covers only three distinct line pairs, so covering all 78 line pairs requires at least 26 rows. If a line pair is missed, its conjunction passes the chosen tests and fails some quadrangle. To preserve all positive tests too, take the disjunction of that conjunction with incidence.

The 26 negatives plus the 52 positive flag inputs therefore characterize incidence on all 67,108,864 inputs for monotone predicates of width at most two. Each positive is independently necessary among these tests: deleting one flag term from the disjunction of the 52 flag conjunctions gives a width-two counterexample for that positive. This optimality concerns quadrangle negatives and the specified flag positives.

At width three, the three disjoint lines of any quadrangle cannot be concurrent: three concurrent lines cover ten points, leaving only three available for the quadrangle. Three nonconcurrent lines cover nine points, so their complement is exactly the original set of four. Consequently, the conjunction of those three line variables fires on precisely one of the 234 negative rows. Adding it to incidence preserves all positive tests and defeats any family omitting that row. Testing all 234 clearly suffices for rejection on those 234 rows. This last assertion alone does not certify equality on all Boolean inputs at width three.

## Reproduction

Run `python3 plane_tests.py` to verify all explicit families, the three-line complements, and the two successful pairs of translation orbits among the 18 orbits. Run `lake env lean /path/to/PlaneNegativeTests.lean` from the project's `lean` directory with its pinned Lean 4.36.0 and built `PEqualNP.Defs.HeptadCover` module. The Lean proof of `complete_test` works for an arbitrary monotone predicate satisfying the width hypothesis.

The Lean file also proves the counting lower bounds for one- and two-variable coverage, verifies the five singleton rows, and proves that three exterior lines determine their four-point complement. The enumeration that all 234 rows have such a triple is checked by the Python file, with the incidence count above supplying a direct proof.

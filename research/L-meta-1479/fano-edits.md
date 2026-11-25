# One- and two-gate edits of four 27-gate Fano circuits

The baseline circuit forms one star per line: OR its three point inputs, then AND the result with its line input. It ORs the seven stars together. Each edit replaces one fixed gate with either binary AND or binary OR over any unordered pair of distinct earlier wires, excluding only the identical original gate. The output stays at wire 40. Unused gates are allowed. Two edits use different positions in the same circuit.

| Layout | Single edits | Two edits | Correct singles | Correct two edits | Correct with a double read |
| --- | ---: | ---: | ---: | ---: | ---: |
| Build each star and immediately append to the output chain | 20,565 | 201,287,619 | 0 | 14 | 0 |
| Build all stars, then a left-associated output chain | 20,565 | 201,287,619 | 0 | 49 | 0 |
| Build all stars, then a balanced output tree | 20,565 | 201,287,619 | 0 | 58 | 0 |
| Build all point ORs, then all star ANDs, then a balanced output tree | 20,565 | 201,287,619 | 0 | 79 | 0 |

The search uses the 21 minimal true inputs and 37 maximal false inputs. Agreement there determines the full truth table by monotonicity. For a fixed first edit and second gate position, each boundary input induces a monotone unary function of the second gate's output. Evaluating the suffix with that wire forced to zero and to one gives both endpoints. Substituting any second gate's signature into these endpoints gives the exact output; many positions can be rejected for every proposed replacement at once.

Every candidate passing the boundary test is rechecked on all 16,384 assignments. The program also computes the project's two directional trace values at each of the 21 incident pairs. A double read requires both traces to vanish at the same pair. Counts are per layout; different template neighborhoods may overlap. A globally different 27-gate construction remains possible.

Compile with `g++ -std=c++17 -O3 -Wall -Wextra -pedantic fano_edits.cpp -o fano_edits` and run `./fano_edits` with assertions enabled.

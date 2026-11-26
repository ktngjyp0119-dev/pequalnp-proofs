import PEqualNP.Defs.HeptadCover
import Mathlib.Tactic

namespace GenericTestSample
open PEqualNP.HeptadCover
abbrev I := Fin 13
abbrev R := Fin 21
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def points : R → Finset I :=
  ![{0,1,6,12},
    {0,2,4,11},
    {0,2,7},
    {0,3,10},
    {0,4,8},
    {0,5,9,11},
    {1,2,5,7},
    {1,3,4,7},
    {1,5,10},
    {1,6,11},
    {1,8,9,10},
    {2,3,9},
    {2,5,8},
    {2,6,10,12},
    {3,5,6},
    {3,8,11,12},
    {4,5,12},
    {4,6,9},
    {4,7,10,11},
    {6,7,8},
    {7,9,12}]
def lines : R → Finset I :=
  ![{2,7,8},
    {5,7,9},
    {3,5,8,9},
    {5,6,8,11},
    {2,6,9,11},
    {1,3,7},
    {3,8,10},
    {9,10,12},
    {3,6,8,12},
    {4,7,9,12},
    {2,3,4},
    {4,5,10,11},
    {0,3,10,11},
    {0,4,8},
    {1,8,11,12},
    {1,4,6},
    {0,6,7,10},
    {2,7,11,12},
    {0,5,12},
    {0,1,2,9},
    {1,2,5,10}]

theorem distinct : Function.Injective points := by
  intro i j eq
  have certified : ∀ i j : R, points i = points j → i = j := by decide
  exact certified i j eq

theorem generic : ∀ i : R,
    lines i = missLines singerLines3 (points i) ∧
    (∀ p : I, p ∉ points i → ∃ l ∈ lines i, p ∈ singerLines3 l) ∧
    (¬ ∃ l : I, ∀ p ∈ points i, p ∈ singerLines3 l) ∧
    (¬ ∃ p : I, ∀ l ∈ lines i, p ∈ singerLines3 l) := by
  intro i
  fin_cases i <;> decide

/-- Repeated variables also test singleton witnesses. -/
theorem complete_pairs :
    (∀ p q : I, ∃ i : R, p ∈ points i ∧ q ∈ points i) ∧
    (∀ l k : I, ∃ i : R, l ∈ lines i ∧ k ∈ lines i) ∧
    (∀ p l : I, p ∉ singerLines3 l → ∃ i : R, p ∈ points i ∧ l ∈ lines i) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals intro a; fin_cases a <;> decide

#print axioms distinct
#print axioms generic
#print axioms complete_pairs
end GenericTestSample

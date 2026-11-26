import PEqualNP.Defs.ReadTwo
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Tactic

namespace StarWitness
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

def circuit : Circuit := ⟨[
  ⟨.or, [3, 9]⟩,
  ⟨.or, [1, 26]⟩,
  ⟨.or, [0, 27]⟩,
  ⟨.and, [28, 13]⟩,
  ⟨.or, [4, 10]⟩,
  ⟨.or, [2, 30]⟩,
  ⟨.or, [1, 31]⟩,
  ⟨.and, [32, 14]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.or, [3, 34]⟩,
  ⟨.or, [2, 35]⟩,
  ⟨.and, [36, 15]⟩,
  ⟨.or, [6, 12]⟩,
  ⟨.or, [4, 38]⟩,
  ⟨.or, [3, 39]⟩,
  ⟨.and, [40, 16]⟩,
  ⟨.or, [7, 0]⟩,
  ⟨.or, [5, 42]⟩,
  ⟨.or, [4, 43]⟩,
  ⟨.and, [44, 17]⟩,
  ⟨.or, [8, 1]⟩,
  ⟨.or, [6, 46]⟩,
  ⟨.or, [5, 47]⟩,
  ⟨.and, [48, 18]⟩,
  ⟨.or, [9, 2]⟩,
  ⟨.or, [7, 50]⟩,
  ⟨.or, [6, 51]⟩,
  ⟨.and, [52, 19]⟩,
  ⟨.or, [10, 3]⟩,
  ⟨.or, [8, 54]⟩,
  ⟨.or, [7, 55]⟩,
  ⟨.and, [56, 20]⟩,
  ⟨.or, [11, 4]⟩,
  ⟨.or, [9, 58]⟩,
  ⟨.or, [8, 59]⟩,
  ⟨.and, [60, 21]⟩,
  ⟨.or, [12, 5]⟩,
  ⟨.or, [10, 62]⟩,
  ⟨.or, [9, 63]⟩,
  ⟨.and, [64, 22]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [11, 66]⟩,
  ⟨.or, [10, 67]⟩,
  ⟨.and, [68, 23]⟩,
  ⟨.or, [1, 7]⟩,
  ⟨.or, [12, 70]⟩,
  ⟨.or, [11, 71]⟩,
  ⟨.and, [72, 24]⟩,
  ⟨.or, [2, 8]⟩,
  ⟨.or, [0, 74]⟩,
  ⟨.or, [12, 75]⟩,
  ⟨.and, [76, 25]⟩,
  ⟨.or, [73, 77]⟩,
  ⟨.or, [69, 78]⟩,
  ⟨.or, [65, 79]⟩,
  ⟨.or, [61, 80]⟩,
  ⟨.or, [57, 81]⟩,
  ⟨.or, [53, 82]⟩,
  ⟨.or, [49, 83]⟩,
  ⟨.or, [45, 84]⟩,
  ⟨.or, [41, 85]⟩,
  ⟨.or, [37, 86]⟩,
  ⟨.or, [33, 87]⟩,
  ⟨.or, [29, 88]⟩], 89⟩

theorem counts : circuit.size = 64 ∧ ReadTwo.nOr circuit = 51 ∧ ReadTwo.nAnd circuit = 13 := by decide

theorem legal : Monotone2 circuit := by
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

def incidence (x : Fin 26 → Bool) : Bool := (List.finRange 13).any fun l =>
  (([l,l+1,l+3,l+9] : List (Fin 13)).any fun p => x (Fin.castAdd 13 p)) && x (Fin.natAdd 13 l)

theorem specification (x : Fin 26 → Bool) : incidence x = true ↔
    ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  simp only [incidence, List.any_eq_true, Bool.and_eq_true, List.mem_finRange,
    true_and, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨l,⟨p,h,hp⟩,hl⟩
    exact ⟨p,l,h,hp,hl⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨l,⟨p,h,hp⟩,hl⟩

theorem computes (x : Fin 26 → Bool) : circuitFun 26 circuit x = incidence x := by
  have xs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := by rfl
  have ls : List.finRange 13 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by decide
  unfold circuitFun Circuit.eval incidence
  rw [xs,ls]
  simp [circuit, Circuit.wires, GateOp.eval, List.getD, List.foldl, List.any, List.all]

#print axioms computes
#print axioms specification
end StarWitness

import PEqualNP.Defs
import Mathlib.Tactic

open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace FanoDoubleRead
local instance : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

-- The first two stars use T OR (P AND L) = (T OR P) AND (T OR L).
def circuit : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [14, 3]⟩,
  ⟨.and, [15, 7]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [17, 4]⟩,
  ⟨.or, [16, 18]⟩,
  ⟨.or, [16, 8]⟩,
  ⟨.and, [19, 20]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [22, 5]⟩,
  ⟨.and, [23, 9]⟩,
  ⟨.or, [21, 24]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [26, 6]⟩,
  ⟨.and, [27, 10]⟩,
  ⟨.or, [25, 28]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [30, 0]⟩,
  ⟨.and, [31, 11]⟩,
  ⟨.or, [29, 32]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [34, 1]⟩,
  ⟨.and, [35, 12]⟩,
  ⟨.or, [33, 36]⟩,
  ⟨.or, [6, 0]⟩,
  ⟨.or, [38, 2]⟩,
  ⟨.and, [39, 13]⟩,
  ⟨.or, [37, 40]⟩], 41⟩

private theorem legal (j : ℕ) (g : Gate) (h : circuit.gates[j]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j := by
  have bound : j < 28 := (List.getElem?_eq_some_iff.mp h).1
  interval_cases j <;> simp [circuit] at h <;> subst g <;>
    exact ⟨by simp, _, _, rfl, by decide, by decide, by decide⟩

private theorem correct (x : Fin 14 → Bool) : circuit.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  let flags : Prop := (x 0 = true ∧ x 7 = true) ∨
    (x 1 = true ∧ x 7 = true) ∨
    (x 3 = true ∧ x 7 = true) ∨
    (x 1 = true ∧ x 8 = true) ∨
    (x 2 = true ∧ x 8 = true) ∨
    (x 4 = true ∧ x 8 = true) ∨
    (x 2 = true ∧ x 9 = true) ∨
    (x 3 = true ∧ x 9 = true) ∨
    (x 5 = true ∧ x 9 = true) ∨
    (x 3 = true ∧ x 10 = true) ∨
    (x 4 = true ∧ x 10 = true) ∨
    (x 6 = true ∧ x 10 = true) ∨
    (x 4 = true ∧ x 11 = true) ∨
    (x 5 = true ∧ x 11 = true) ∨
    (x 0 = true ∧ x 11 = true) ∨
    (x 5 = true ∧ x 12 = true) ∨
    (x 6 = true ∧ x 12 = true) ∨
    (x 1 = true ∧ x 12 = true) ∨
    (x 6 = true ∧ x 13 = true) ∨
    (x 0 = true ∧ x 13 = true) ∨
    (x 2 = true ∧ x 13 = true)
  have flagIff : flags ↔ ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    constructor
    · intro h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact ⟨0,0,by decide,h⟩
      · exact ⟨1,0,by decide,h⟩
      · exact ⟨3,0,by decide,h⟩
      · exact ⟨1,1,by decide,h⟩
      · exact ⟨2,1,by decide,h⟩
      · exact ⟨4,1,by decide,h⟩
      · exact ⟨2,2,by decide,h⟩
      · exact ⟨3,2,by decide,h⟩
      · exact ⟨5,2,by decide,h⟩
      · exact ⟨3,3,by decide,h⟩
      · exact ⟨4,3,by decide,h⟩
      · exact ⟨6,3,by decide,h⟩
      · exact ⟨4,4,by decide,h⟩
      · exact ⟨5,4,by decide,h⟩
      · exact ⟨0,4,by decide,h⟩
      · exact ⟨5,5,by decide,h⟩
      · exact ⟨6,5,by decide,h⟩
      · exact ⟨1,5,by decide,h⟩
      · exact ⟨6,6,by decide,h⟩
      · exact ⟨0,6,by decide,h⟩
      · exact ⟨2,6,by decide,h⟩
    · rintro ⟨p,l,inc,hp,hl⟩
      rcases inc with e | e | e <;> subst p <;> fin_cases l <;> unfold flags <;>
        repeat' first | exact ⟨hp,hl⟩ | exact Or.inl ⟨hp,hl⟩ | apply Or.inr
  rw [← flagIff]
  have xs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by rfl
  unfold Circuit.eval
  rw [xs]
  simp [circuit, Circuit.wires, GateOp.eval, List.getD, flags,
    List.foldl, List.any, List.all]
  simp only [← or_and_left]
  simp only [or_and_right, or_assoc]

private def pointTrace (i : ℕ) : Bool := decide (i ∈ ([7, 16, 19, 20] : List ℕ))

private theorem pointStep : ∀ j : Fin 28, ∀ g ∈ circuit.gates[j.val]?.toList,
    ∀ a ∈ g.inputs, ∀ b ∈ g.inputs, g.inputs = [a,b] →
    let w := circuit.wires (List.ofFn (fun i : Fin 14 => decide (i = Fin.castAdd 7 (0 : Fin 7))))
    (g.op = .and → pointTrace (14+j.val) = ((w.getD a false && pointTrace b) || (pointTrace a && w.getD b false))) ∧
    (g.op = .or → pointTrace (14+j.val) = (pointTrace a || pointTrace b)) := by
  decide

private def lineTrace (i : ℕ) : Bool := decide (i ∈ ([0, 14, 15, 16, 19, 20, 31, 38, 39] : List ℕ))

private theorem lineStep : ∀ j : Fin 28, ∀ g ∈ circuit.gates[j.val]?.toList,
    ∀ a ∈ g.inputs, ∀ b ∈ g.inputs, g.inputs = [a,b] →
    let w := circuit.wires (List.ofFn (fun i : Fin 14 => decide (i = Fin.natAdd 7 (0 : Fin 7))))
    (g.op = .and → lineTrace (14+j.val) = ((w.getD a false && lineTrace b) || (lineTrace a && w.getD b false))) ∧
    (g.op = .or → lineTrace (14+j.val) = (lineTrace a || lineTrace b)) := by
  decide

theorem witness28 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 28 ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧
      ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧
      (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧
      (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  refine ⟨circuit, by decide, legal, correct, 0, 0, Or.inl rfl, ?_, ?_⟩
  · refine ⟨pointTrace, by decide, ?_, by decide⟩
    intro j g a b hj hg
    have bound : j < 28 := (List.getElem?_eq_some_iff.mp hj).1
    exact pointStep ⟨j,bound⟩ g (by simp [hj]) a (by simp [hg]) b (by simp [hg]) hg
  · refine ⟨lineTrace, by decide, ?_, by decide⟩
    intro j g a b hj hg
    have bound : j < 28 := (List.getElem?_eq_some_iff.mp hj).1
    exact lineStep ⟨j,bound⟩ g (by simp [hj]) a (by simp [hg]) b (by simp [hg]) hg

end FanoDoubleRead

import Mathlib.Tactic

namespace SharedDirtyStars

/-- The public graph of L-meta-1342, given by its neighbor lists. -/
def neighbors : ℕ → List ℕ
  | 0 => [9,10]
  | 1 => [4,8]
  | 2 => [5,10]
  | 3 => [6,7]
  | 4 => [1,8,10]
  | 5 => [2,8,9]
  | 6 => [3,7,10]
  | 7 => [3,6,9]
  | 8 => [1,4,5,9]
  | 9 => [0,5,7,8]
  | 10 => [0,2,4,6]
  | _ => []

def poolSize (u : ℕ) := (List.range 11).countP (fun i => u.testBit i)
def degree (u c : ℕ) := (neighbors c).countP (fun i => u.testBit i)

def centers (u : ℕ) := (Finset.range 11).filter fun c =>
  u.testBit c = false ∧ 2 ≤ degree u c ∧ degree u c < poolSize u

def bonus (u : ℕ) (C : Finset ℕ) := ∑ c ∈ C, (degree u c - 2)

def validPool (u : ℕ) : Prop := 3 ≤ (centers u).card → bonus u (centers u) + 3 ≤ poolSize u
instance (u : ℕ) : Decidable (validPool u) := inferInstanceAs (Decidable (_ → _))

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

/-- Every pool of at most eleven vertex bits is covered by one of the 64 blocks. -/
private theorem blocks : ∀ high : Fin 64, ∀ low : Fin 32,
    validPool (32 * high.val + low.val) := by
  intro high
  fin_cases high <;> decide +kernel

/-- Even if the guard disjunctions were free, individually gating each dirty
star costs at least two gates more than building the clean stars directly.
The comparison concerns a dedicated pool; external consumers are not charged. -/
theorem guarded_penalty (u : Fin 2048) (C : Finset ℕ)
    (sub : C ⊆ centers u) (three : 3 ≤ C.card) :
    bonus u C + 3 ≤ poolSize u := by
  let hi : Fin 64 := ⟨u.val / 32, by have := u.isLt; omega⟩
  let lo : Fin 32 := ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩
  have h := blocks hi lo
  have he : 32 * hi.val + lo.val = u.val := by
    dsimp [hi, lo]
    omega
  rw [he] at h
  have maxBound := h (three.trans (Finset.card_le_card sub))
  have mono : bonus u C ≤ bonus u (centers u) := Finset.sum_le_sum_of_subset sub
  omega

theorem gate_gap (u : Fin 2048) (C : Finset ℕ)
    (sub : C ⊆ centers u) (three : 3 ≤ C.card) :
    (∑ c ∈ C, degree u c) + 2 ≤ poolSize u - 1 + 2 * C.card := by
  have lower := guarded_penalty u C sub three
  have identity : (∑ c ∈ C, degree u c) = bonus u C + 2 * C.card := by
    calc
      _ = ∑ c ∈ C, ((degree u c - 2) + 2) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hd := (Finset.mem_filter.mp (sub hc)).2.2.1
        omega
      _ = _ := by simp [Finset.sum_add_distrib, bonus, Nat.mul_comm]
  omega

/-- For the indicated pool and centers the two-gate arithmetic gap is sharp
if the ORs used in the guards are credited at zero cost. -/
theorem sharp_accounting :
    let u := 49
    let C : Finset ℕ := {8,9,10}
    C ⊆ centers u ∧ 3 ≤ C.card ∧
    (∑ c ∈ C, degree u c) + 2 = poolSize u - 1 + 2*C.card := by decide

#print axioms gate_gap
#print axioms sharp_accounting
end SharedDirtyStars

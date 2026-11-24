import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover
open scoped BigOperators

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.FlagRectangleBudget :
    ∀ R : Finset (Finset (Fin 13) × Finset (Fin 13)),
        R.biUnion (fun r => r.1 ×ˢ r.2) = incidences singerLines3 →
        65 ≤ ∑ r ∈ R, (r.1.card + r.2.card) := by
  intro R hUnion
  have flagCount : (incidences singerLines3).card = 52 := by decide
  have diag : ∀ t : Fin 13, t ∈ singerLines3 t := by decide
  have unique : ∀ a b : Fin 13, a ≠ b → (singerLines3 a ∩ singerLines3 b).card ≤ 1 := by
    decide
  have sound {r : Finset (Fin 13) × Finset (Fin 13)} (hr : r ∈ R)
      {p l} (hp : p ∈ r.1) (hl : l ∈ r.2) : p ∈ singerLines3 l := by
    have hm : (p,l) ∈ R.biUnion (fun s => s.1 ×ˢ s.2) :=
      Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_product.mpr ⟨hp,hl⟩⟩
    rw [hUnion] at hm
    exact (Finset.mem_filter.mp hm).2
  have singleSide (r : Finset (Fin 13) × Finset (Fin 13)) (hr : r ∈ R) :
      r.1.card ≤ 1 ∨ r.2.card ≤ 1 := by
    by_cases small : r.2.card ≤ 1
    · exact Or.inr small
    left
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge small)
    have sub : r.1 ⊆ singerLines3 a ∩ singerLines3 b := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨sound hr hp ha, sound hr hp hb⟩
    exact (Finset.card_le_card sub).trans (unique a b hne)
  have charge (r : Finset (Fin 13) × Finset (Fin 13)) (hr : r ∈ R) :
      (r.1 ×ˢ r.2).card + (r.1 ∩ r.2).card ≤ r.1.card + r.2.card := by
    rw [Finset.card_product]
    have hLeft : (r.1 ∩ r.2).card ≤ r.1.card := Finset.card_le_card Finset.inter_subset_left
    have hRight : (r.1 ∩ r.2).card ≤ r.2.card := Finset.card_le_card Finset.inter_subset_right
    rcases singleSide r hr with h | h
    · rcases (show r.1.card = 0 ∨ r.1.card = 1 by omega) with he | he <;>
        simp only [he, Nat.zero_mul, Nat.one_mul] at * <;> omega
    · rcases (show r.2.card = 0 ∨ r.2.card = 1 by omega) with he | he <;>
        simp only [he, Nat.mul_zero, Nat.mul_one] at * <;> omega
  have flags : 52 ≤ ∑ r ∈ R, (r.1 ×ˢ r.2).card := by
    rw [← flagCount, ← hUnion]
    exact Finset.card_biUnion_le
  have diagCover : (Finset.univ : Finset (Fin 13)) ⊆ R.biUnion (fun r => r.1 ∩ r.2) := by
    intro t _
    have hm : (t,t) ∈ incidences singerLines3 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, diag t⟩
    rw [← hUnion] at hm
    obtain ⟨r, hr, hin⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_inter.mpr (Finset.mem_product.mp hin)⟩
  have matching : 13 ≤ ∑ r ∈ R, (r.1 ∩ r.2).card := by
    simpa using (Finset.card_le_card diagCover).trans Finset.card_biUnion_le
  calc
    65 = 52 + 13 := rfl
    _ ≤ (∑ r ∈ R, (r.1 ×ˢ r.2).card) + ∑ r ∈ R, (r.1 ∩ r.2).card :=
      Nat.add_le_add flags matching
    _ = ∑ r ∈ R, ((r.1 ×ˢ r.2).card + (r.1 ∩ r.2).card) := Finset.sum_add_distrib.symm
    _ ≤ ∑ r ∈ R, (r.1.card + r.2.card) := Finset.sum_le_sum charge

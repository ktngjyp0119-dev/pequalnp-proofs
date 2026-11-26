import PEqualNP.Defs.HeptadCover
import Mathlib.Tactic

/-! Counting certificates for fan-in-two OR networks on either side of one AND layer. -/
namespace StarOrBudget
open PEqualNP.HeptadCover
abbrev I := Fin 13
abbrev Flag := I × I

theorem plane_facts :
    (incidences singerLines3).card = 52 ∧
    (∀ l k : I, l ≠ k → (singerLines3 l ∩ singerLines3 k).card ≤ 1) ∧
    (∀ p q : I, p ≠ q →
      ((Finset.univ : Finset I).filter (fun l => p ∈ singerLines3 l ∧ q ∈ singerLines3 l)).card ≤ 1) := by
  decide

theorem rectangle_sound {n : ℕ} (P L : Fin n → Finset I) {A B : Finset I}
    (cover : ∀ p l : I, p ∉ singerLines3 l → ∃ i, p ∈ P i ∧ l ∈ L i)
    (silent : ∀ i, ¬ ((∃ p ∈ A, p ∈ P i) ∧ (∃ l ∈ B, l ∈ L i))) :
    A ×ˢ B ⊆ incidences singerLines3 := by
  intro z hz
  obtain ⟨p,l⟩ := z
  obtain ⟨hp,hl⟩ := Finset.mem_product.mp hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_contra no
  obtain ⟨i,h,k⟩ := cover p l no
  exact silent i ⟨⟨p,hp,h⟩,⟨l,hl,k⟩⟩

theorem rectangle_star {A B : Finset I} (sound : A ×ˢ B ⊆ incidences singerLines3) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  have on {p l : I} (hp : p ∈ A) (hl : l ∈ B) : p ∈ singerLines3 l := by
    have hm : (p,l) ∈ incidences singerLines3 :=
      sound (show (p,l) ∈ A ×ˢ B from Finset.mem_product.mpr ⟨hp,hl⟩)
    exact (Finset.mem_filter.mp hm).2
  by_cases hb : B.card ≤ 1
  · exact Or.inr hb
  left
  obtain ⟨l,hl,k,hk,ne⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hb)
  have sub : A ⊆ singerLines3 l ∩ singerLines3 k := by
    intro p hp
    exact Finset.mem_inter.mpr ⟨on hp hl, on hp hk⟩
  exact (Finset.card_le_card sub).trans (plane_facts.2.1 l k ne)

/-- Each leaf and each internal output occupies an operand or a root. -/
theorem port_count {α : Type*} [DecidableEq α] (leaves : Finset α) {k m : ℕ}
    (ports : Fin k → Finset (α ⊕ Fin k)) (roots : Fin m → (α ⊕ Fin k))
    (binary : ∀ i, (ports i).card ≤ 2)
    (live : leaves.disjSum Finset.univ ⊆
      (Finset.univ.biUnion ports) ∪ (Finset.univ.image roots)) :
    leaves.card ≤ k + m := by
  have cap : (Finset.univ.biUnion ports).card ≤ k*2 := by
    calc
      _ ≤ ∑ i : Fin k, (ports i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin k, 2 := Finset.sum_le_sum (fun i _ => binary i)
      _ = _ := by simp
  have h := (Finset.card_le_card live).trans (Finset.card_union_le _ _)
  have r : (Finset.univ.image roots).card ≤ m := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := roots))
  rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The lower counting certificate uses flags as leaf labels. The upper one
uses product gates as leaves. See the written proof for the tagging argument. -/
theorem or_lower_bound {pre products top : ℕ}
    (lowerPorts : Fin pre → Finset (Flag ⊕ Fin pre))
    (lowerRoots : Fin products → (Flag ⊕ Fin pre))
    (upperPorts : Fin top → Finset (Fin products ⊕ Fin top))
    (output : Fin 1 → (Fin products ⊕ Fin top))
    (lowerBinary : ∀ i, (lowerPorts i).card ≤ 2)
    (upperBinary : ∀ i, (upperPorts i).card ≤ 2)
    (lowerLive : (incidences singerLines3).disjSum Finset.univ ⊆
      (Finset.univ.biUnion lowerPorts) ∪ (Finset.univ.image lowerRoots))
    (upperLive : (Finset.univ : Finset (Fin products)).disjSum Finset.univ ⊆
      (Finset.univ.biUnion upperPorts) ∪ (Finset.univ.image output)) :
    51 ≤ pre + top := by
  have h := port_count _ lowerPorts lowerRoots lowerBinary lowerLive
  have g := port_count _ upperPorts output upperBinary upperLive
  rw [plane_facts.1] at h
  simp only [Finset.card_univ, Fintype.card_fin] at g
  omega

#print axioms rectangle_star
#print axioms rectangle_sound
#print axioms or_lower_bound
end StarOrBudget

import PEqualNP.Defs.HeptadCover
import Mathlib.Tactic

/-! Exact finite coverage certificate and the width-two incidence test theorem. -/
namespace PlaneNegativeTests
open PEqualNP.HeptadCover
abbrev I := Fin 13
abbrev V := I ⊕ I
abbrev S := singerLines3

def points (b : Bool) (t : I) : Finset I :=
  if b then {t, t+1, t+5, t+11} else {t, t+1, t+4, t+6}

def lines (b : Bool) (t : I) : Finset I :=
  if b then {t+3, t+6, t+7} else {t+2, t+7, t+9}

def sample : Finset (Finset I) :=
  Finset.univ.biUnion fun t : I => {points false t, points true t}

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem sample_size : sample.card = 26 := by decide

theorem rotations_checked : ∀ (b : Bool) (t : I),
    IsQuadrangle S (points b t) ∧ missLines S (points b t) = lines b t := by decide

theorem pair_certificate :
    (∀ p q : I, ∃ b t, p ∈ points b t ∧ q ∈ points b t) ∧
    (∀ l k : I, ∃ b t, l ∈ lines b t ∧ k ∈ lines b t) ∧
    (∀ p l : I, p ∉ S l → ∃ b t, p ∈ points b t ∧ l ∈ lines b t) := by decide

def incidence (A : Finset V) : Prop :=
  ∃ p l : I, p ∈ S l ∧ Sum.inl p ∈ A ∧ Sum.inr l ∈ A

private theorem point_mem (b t p) :
    Sum.inl p ∈ supp S (points b t) ↔ p ∈ points b t := by simp [supp]

private theorem line_mem (b t l) :
    Sum.inr l ∈ supp S (points b t) ↔ l ∈ lines b t := by
  simp [supp, (rotations_checked b t).2]

private theorem pair_subset {A : Finset V} (free : ¬ incidence A)
    (u v : V) (hu : u ∈ A) (hv : v ∈ A) :
    ∃ b t, ({u, v} : Finset V) ⊆ supp S (points b t) := by
  cases u with
  | inl p =>
    cases v with
    | inl q =>
      obtain ⟨b,t,h,k⟩ := pair_certificate.1 p q
      exact ⟨b,t,Finset.insert_subset ((point_mem b t p).2 h) (Finset.singleton_subset_iff.mpr ((point_mem b t q).2 k))⟩
    | inr l =>
      obtain ⟨b,t,h,k⟩ := pair_certificate.2.2 p l (fun inc => free ⟨p,l,inc,hu,hv⟩)
      exact ⟨b,t,Finset.insert_subset ((point_mem b t p).2 h) (Finset.singleton_subset_iff.mpr ((line_mem b t l).2 k))⟩
  | inr l =>
    cases v with
    | inl p =>
      obtain ⟨b,t,h,k⟩ := pair_certificate.2.2 p l (fun inc => free ⟨p,l,inc,hv,hu⟩)
      exact ⟨b,t,Finset.insert_subset ((line_mem b t l).2 k) (Finset.singleton_subset_iff.mpr ((point_mem b t p).2 h))⟩
    | inr k =>
      obtain ⟨b,t,h,h'⟩ := pair_certificate.2.1 l k
      exact ⟨b,t,Finset.insert_subset ((line_mem b t l).2 h) (Finset.singleton_subset_iff.mpr ((line_mem b t k).2 h'))⟩

/-- A monotone predicate with positive witnesses of size at most two agrees with
incidence everywhere if it accepts each flag and rejects the 26 specified rows. -/
theorem complete_test (f : Finset V → Prop)
    (mono : ∀ {A B}, A ⊆ B → f A → f B)
    (width : ∀ A, f A → ∃ T ⊆ A, T.card ≤ 2 ∧ f T)
    (positive : ∀ p l : I, p ∈ S l → f {Sum.inl p, Sum.inr l})
    (negative : ∀ b t, ¬ f (supp S (points b t))) :
    ∀ A, f A ↔ incidence A := by
  intro A
  constructor
  · intro yes
    by_contra free
    obtain ⟨T, sub, small, ht⟩ := width A yes
    by_cases empty : T = ∅
    · subst T
      exact negative false 0 (mono (Finset.empty_subset _) ht)
    by_cases one : T.card = 1
    · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp one
      have hu := sub (Finset.mem_singleton_self u)
      obtain ⟨b,t,h⟩ := pair_subset free u u hu hu
      exact negative b t (mono (by simpa using h) ht)
    have nonempty := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    have two : T.card = 2 := by omega
    obtain ⟨u,v,_,rfl⟩ := Finset.card_eq_two.mp two
    obtain ⟨b,t,h⟩ := pair_subset free u v (sub (by simp)) (sub (by simp))
    exact negative b t (mono h ht)
  · rintro ⟨p,l,h,hp,hl⟩
    exact mono (Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hl)) (positive p l h)


private theorem plane_counts : (∀ l : I, (S l).card = 4) ∧
    (∀ l k : I, l ≠ k → (S l ∩ S k).card = 1) := by decide

/-- Count the line-point incidences, losing at most one for each line pair. -/
private theorem line_union_bound (T : Finset I) :
    4 * T.card ≤ (T.biUnion S).card + T.card.choose 2 := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert l T fresh ih =>
    have overlap : (S l ∩ T.biUnion S).card ≤ T.card := by
      rw [Finset.inter_biUnion]
      refine Finset.card_biUnion_le.trans ?_
      calc
        ∑ k ∈ T, (S l ∩ S k).card ≤ ∑ _k ∈ T, 1 := by
          apply Finset.sum_le_sum
          intro k hk
          exact (plane_counts.2 l k (fun eq => fresh (eq ▸ hk))).le
        _ = T.card := by simp
    have add := Finset.card_union_add_card_inter (S l) (T.biUnion S)
    rw [plane_counts.1] at add
    rw [Finset.card_insert_of_notMem fresh, Finset.biUnion_insert]
    have choose : (T.card + 1).choose 2 = T.card + T.card.choose 2 := by
      simpa using Nat.choose_succ_succ T.card 1
    rw [choose]
    omega

private theorem at_most_three (Q : Finset I) (hQ : Q.card = 4) :
    (missLines S Q).card ≤ 3 := by
  by_contra! many
  obtain ⟨T, sub, four⟩ := Finset.exists_subset_card_eq (show 4 ≤ (missLines S Q).card by omega)
  have dj : Disjoint (T.biUnion S) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨l,hl,inc⟩ := Finset.mem_biUnion.mp hp
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp (sub hl)).2 inc hq
  have capacity := Finset.card_le_univ ((T.biUnion S) ∪ Q)
  rw [Finset.card_union_of_disjoint dj, hQ, Fintype.card_fin] at capacity
  have lower := line_union_bound T
  rw [four] at lower
  change 16 ≤ (T.biUnion S).card + 6 at lower
  omega

/-- A family of actual quadrangle rows testing all distinct line pairs needs 26 rows. -/
theorem pair_lower_bound (F : Finset (Finset I))
    (rows : ∀ Q ∈ F, IsQuadrangle S Q)
    (covers : ∀ P ∈ (Finset.univ : Finset I).powersetCard 2,
      ∃ Q ∈ F, P ⊆ missLines S Q) : 26 ≤ F.card := by
  let pairs (Q : Finset I) := (missLines S Q).powersetCard 2
  have incl : (Finset.univ : Finset I).powersetCard 2 ⊆ F.biUnion pairs := by
    intro P hP
    obtain ⟨Q, hQ, h⟩ := covers P hP
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_powersetCard.mpr
      ⟨h, (Finset.mem_powersetCard.mp hP).2⟩⟩
  have each (Q) (hQ : Q ∈ F) : (pairs Q).card ≤ 3 := by
    have h := at_most_three Q (rows Q hQ).1
    exact (Finset.card_powersetCard 2 _).le.trans (Nat.choose_le_choose 2 h)
  have sum_bound := Finset.sum_le_sum each
  have total := (Finset.card_le_card incl).trans (Finset.card_biUnion_le.trans sum_bound)
  have n : ((Finset.univ : Finset I).powersetCard 2).card = 78 := by
    rw [Finset.card_powersetCard]; decide
  rw [n] at total
  have bound : 78 ≤ F.card * 3 := by simpa using total
  omega

def singletonRow : Fin 5 → Finset I :=
  ![{0,1,7,10}, {0,2,4,6}, {1,4,5,9}, {3,4,10,11}, {6,8,11,12}]

theorem singleton_cover :
    (Finset.univ.image singletonRow).card = 5 ∧
    (∀ i, IsQuadrangle S (singletonRow i)) ∧
    (∀ v : V, ∃ i, v ∈ supp S (singletonRow i)) := by decide

theorem singleton_lower_bound (F : Finset (Finset I))
    (rows : ∀ Q ∈ F, IsQuadrangle S Q)
    (covers : ∀ l : I, ∃ Q ∈ F, l ∈ missLines S Q) : 5 ≤ F.card := by
  have incl : (Finset.univ : Finset I) ⊆ F.biUnion (missLines S) :=
    fun l _ => Finset.mem_biUnion.mpr (covers l)
  have each (Q) (hQ : Q ∈ F) := at_most_three Q (rows Q hQ).1
  have total := (Finset.card_le_card incl).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum each))
  have bound : 13 ≤ F.card * 3 := by simpa using total
  omega

/-- Three exterior lines determine their four-point complement uniquely. -/
theorem recover_from_three (Q T : Finset I) (hQ : Q.card = 4)
    (three : T.card = 3) (sub : T ⊆ missLines S Q) :
    Q = (T.biUnion S)ᶜ := by
  have incl : Q ⊆ (T.biUnion S)ᶜ := by
    intro p hp
    apply Finset.mem_compl.mpr
    intro hu
    obtain ⟨l,hl,inc⟩ := Finset.mem_biUnion.mp hu
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp (sub hl)).2 inc hp
  apply Finset.eq_of_subset_of_card_le incl
  rw [Finset.card_compl, Fintype.card_fin, hQ]
  have lower := line_union_bound T
  rw [three] at lower
  change 12 ≤ (T.biUnion S).card + 3 at lower
  omega

#print axioms complete_test
#print axioms pair_lower_bound
#print axioms singleton_cover
#print axioms singleton_lower_bound
#print axioms recover_from_three
end PlaneNegativeTests

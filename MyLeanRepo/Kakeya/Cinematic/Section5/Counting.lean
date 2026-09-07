import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Section 5 finite counting lemmas

This module contains the closed finite combinatorial arguments used in PYZ
Section 5.
-/

namespace Kakeya.Cinematic

theorem good_pair_counting :
    GoodPairCountingStatement := by
  intro α _ S bad₁ bad₂ hbad₁ hbad₂
  let good : α → Finset α := fun g =>
    S.filter (fun h => h ∉ bad₁ g ∧ h ∉ bad₂ g)
  have hgood (g : α) (hg : g ∈ S) : S.card ≤ 3 * (good g).card := by
    have hcover : S ⊆ good g ∪ (S ∩ bad₁ g) ∪ (S ∩ bad₂ g) := by
      intro h hh
      by_cases h₁ : h ∈ bad₁ g
      · simp [h₁, hh]
      · by_cases h₂ : h ∈ bad₂ g
        · simp [h₂, hh]
        · simp [good, h₁, h₂, hh]
    have hcard := Finset.card_le_card hcover
    have hunion₁ :=
      Finset.card_union_le (good g ∪ (S ∩ bad₁ g)) (S ∩ bad₂ g)
    have hunion₂ := Finset.card_union_le (good g) (S ∩ bad₁ g)
    have hb₁ := hbad₁ g hg
    have hb₂ := hbad₂ g hg
    omega
  have hcard_good :
      ((S.product S).filter
        (fun pair => pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1)).card =
        ∑ g ∈ S, (good g).card := by
    calc
      _ = ∑ pair ∈ S.product S,
          if pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1 then 1 else 0 := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ g ∈ S, ∑ h ∈ S,
          if h ∉ bad₁ g ∧ h ∉ bad₂ g then 1 else 0 := by
            exact Finset.sum_product S S
              (fun pair =>
                if pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1 then 1 else 0)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    S.card ^ 2 = ∑ g ∈ S, S.card := by simp [pow_two]
    _ ≤ ∑ g ∈ S, 3 * (good g).card := by
      exact Finset.sum_le_sum fun g hg => hgood g hg
    _ = 3 * ((S.product S).filter
          (fun pair => pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1)).card := by
      rw [hcard_good, Finset.mul_sum]

theorem good_pair_counting_one_diagonal
    (α : Type) [DecidableEq α]
    (S : Finset α) (bad₁ bad₂ : α → Finset α)
    (hcard : 2 ≤ S.card)
    (hbad₁ : ∀ g ∈ S, (S ∩ bad₁ g).card ≤ 1)
    (hbad₂ : ∀ g ∈ S, 3 * (S ∩ bad₂ g).card ≤ S.card) :
    S.card ^ 2 ≤
      3 * ((S.product S).filter
        (fun pair => pair.2 ∉ bad₁ pair.1 ∧
          pair.2 ∉ bad₂ pair.1)).card := by
  let good : α → Finset α := fun g =>
    S.filter (fun h => h ∉ bad₁ g ∧ h ∉ bad₂ g)
  have hgood (g : α) (hg : g ∈ S) :
      S.card ≤ 3 * (good g).card := by
    have hcover :
        S ⊆ good g ∪ (S ∩ bad₁ g) ∪ (S ∩ bad₂ g) := by
      intro h hh
      by_cases h₁ : h ∈ bad₁ g
      · simp [h₁, hh]
      · by_cases h₂ : h ∈ bad₂ g
        · simp [h₂, hh]
        · simp [good, h₁, h₂, hh]
    have hcover_card := Finset.card_le_card hcover
    have hunion₁ :=
      Finset.card_union_le (good g ∪ (S ∩ bad₁ g)) (S ∩ bad₂ g)
    have hunion₂ := Finset.card_union_le (good g) (S ∩ bad₁ g)
    have hb₁ := hbad₁ g hg
    have hb₂ := hbad₂ g hg
    omega
  have hcard_good :
      ((S.product S).filter
        (fun pair => pair.2 ∉ bad₁ pair.1 ∧
          pair.2 ∉ bad₂ pair.1)).card =
        ∑ g ∈ S, (good g).card := by
    calc
      _ = ∑ pair ∈ S.product S,
          if pair.2 ∉ bad₁ pair.1 ∧
              pair.2 ∉ bad₂ pair.1 then 1 else 0 := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ g ∈ S, ∑ h ∈ S,
          if h ∉ bad₁ g ∧ h ∉ bad₂ g then 1 else 0 := by
            exact Finset.sum_product S S
              (fun pair =>
                if pair.2 ∉ bad₁ pair.1 ∧
                    pair.2 ∉ bad₂ pair.1 then 1 else 0)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    S.card ^ 2 = ∑ g ∈ S, S.card := by simp [pow_two]
    _ ≤ ∑ g ∈ S, 3 * (good g).card := by
      exact Finset.sum_le_sum fun g hg => hgood g hg
    _ = 3 * ((S.product S).filter
          (fun pair => pair.2 ∉ bad₁ pair.1 ∧
            pair.2 ∉ bad₂ pair.1)).card := by
      rw [hcard_good, Finset.mul_sum]

theorem pair_incidence_counting :
    PairIncidenceCountingStatement := by
  intro ρ σ _ _ rectangles pairs incidence q L h_lower h_upper
  let total := ∑ R ∈ rectangles, (pairs ∩ incidence R).card
  calc
    rectangles.card * q = ∑ R ∈ rectangles, q := by simp
    _ ≤ total := by
      dsimp [total]
      exact Finset.sum_le_sum fun R hR => h_lower R hR
    _ = ∑ R ∈ rectangles, ∑ p ∈ pairs,
          if p ∈ incidence R then 1 else 0 := by
      dsimp [total]
      apply Finset.sum_congr rfl
      intro R _hR
      simpa [Finset.mem_inter] using
        (Finset.card_eq_sum_ite
          (s := pairs ∩ incidence R) (t := pairs) Finset.inter_subset_left)
    _ = ∑ p ∈ pairs, ∑ R ∈ rectangles,
          if p ∈ incidence R then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ pairs,
          (rectangles.filter (fun R => p ∈ incidence R)).card := by
      apply Finset.sum_congr rfl
      intro p _hp
      symm
      simpa [Finset.mem_filter] using
        (Finset.card_eq_sum_ite
          (s := rectangles.filter (fun R => p ∈ incidence R))
          (t := rectangles)
          (Finset.filter_subset (fun R => p ∈ incidence R) rectangles))
    _ ≤ ∑ _p ∈ pairs, L := by
      exact Finset.sum_le_sum fun p hp => h_upper p hp
    _ = pairs.card * L := by simp

end Kakeya.Cinematic

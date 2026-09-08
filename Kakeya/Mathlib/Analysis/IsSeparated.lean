/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Separated finite sets of reals

Elementary cardinality bounds for finite subsets of `ℝ` whose points are
pairwise separated by at least `ε` in absolute value. These facts are
independent of the tube machinery.

TODO: The proof of `card_le_of_pairwise_le_subset_Icc` is more complicated than needed.
-/

@[expose] public section

/-- A finite set of reals contained in `[a, b]` whose points are pairwise
`ε`-separated has at most `(b - a) / ε + 1` elements.

Proved by a pigeonhole argument: the map `x ↦ ⌊(x - a) / ε⌋` lands in
`{0, …, ⌊(b - a) / ε⌋}` and is injective on the set, since two points in the
same bucket would differ by less than `ε`. -/
lemma card_le_of_pairwise_le_subset_Icc
    {s : Finset ℝ} {a b ε : ℝ} (hε : 0 < ε) (hab : a ≤ b)
    (hsub : ∀ x ∈ s, x ∈ Set.Icc a b)
    (hsep : (s : Set ℝ).Pairwise (fun x y => ε ≤ |x - y|)) :
    (s.card : ℝ) ≤ (b - a) / ε + 1 := by
  classical
  have hεne : ε ≠ 0 := hε.ne'
  have hmono : ∀ p q : ℝ, p ≤ q → p / ε ≤ q / ε := fun p q h => by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hε.le)
  set N : ℤ := ⌊(b - a) / ε⌋ with hN_def
  set f : ℝ → ℤ := fun x => ⌊(x - a) / ε⌋ with hf_def
  have hN_nonneg : (0 : ℤ) ≤ N := by
    rw [hN_def]; exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hε.le)
  have hmaps : ∀ x ∈ s, f x ∈ Finset.Icc (0 : ℤ) N := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hsub x hx
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · simp only [hf_def]
      exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hε.le)
    · simp only [hf_def, hN_def, Int.le_floor]
      calc ((⌊(x - a) / ε⌋ : ℤ) : ℝ) ≤ (x - a) / ε := Int.floor_le _
        _ ≤ (b - a) / ε := hmono _ _ (by linarith)
  have hinj : Set.InjOn f ↑s := by
    intro x hx y hy hfxy
    by_contra hne
    have hsep_xy : ε ≤ |x - y| := hsep hx hy hne
    simp only [hf_def] at hfxy
    set u := (x - a) / ε with hu_def
    set v := (y - a) / ε with hv_def
    have hu_lb : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
    have hu_ub : u < (⌊u⌋ : ℝ) + 1 := Int.lt_floor_add_one u
    have hv_lb : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
    have hv_ub : v < (⌊v⌋ : ℝ) + 1 := Int.lt_floor_add_one v
    have hcast : (⌊u⌋ : ℝ) = (⌊v⌋ : ℝ) := by exact_mod_cast hfxy
    have hu_mul : u * ε = x - a := by rw [hu_def]; field_simp
    have hv_mul : v * ε = y - a := by rw [hv_def]; field_simp
    rcases le_abs.mp hsep_xy with hcase | hcase
    · have hdiff : u - v < 1 := by linarith
      nlinarith [hu_mul, hv_mul, hcase, mul_lt_mul_of_pos_right hdiff hε]
    · have hdiff : v - u < 1 := by linarith
      nlinarith [hu_mul, hv_mul, hcase, mul_lt_mul_of_pos_right hdiff hε]
  have hcard_Icc : (Finset.Icc (0 : ℤ) N).card = (N + 1).toNat := by
    rw [Int.card_Icc, sub_zero]
  have hcard : (s.card : ℝ) ≤ (N : ℝ) + 1 := by
    have h := Finset.card_le_card_of_injOn f hmaps hinj
    rw [hcard_Icc] at h
    have hcast : ((N + 1).toNat : ℝ) = (N : ℝ) + 1 := by
      have h0 : ((N + 1).toNat : ℤ) = N + 1 := Int.toNat_of_nonneg (by linarith)
      exact_mod_cast h0
    calc (s.card : ℝ) ≤ ((N + 1).toNat : ℝ) := by exact_mod_cast h
      _ = (N : ℝ) + 1 := hcast
  have hNle : (N : ℝ) ≤ (b - a) / ε := by rw [hN_def]; exact Int.floor_le _
  linarith

/-- A finite set of reals whose points are pairwise `ε`-separated spreads its
extremes apart: `(card - 1) * ε ≤ max' - min'`. Deduced from
`card_le_of_pairwise_le_subset_Icc` applied on `[min', max']`. -/
lemma max'_sub_min'_ge_of_separated
    {s : Finset ℝ} (hne : s.Nonempty) {ε : ℝ}
    (hsep : (s : Set ℝ).Pairwise (fun x y => ε ≤ |x - y|)) :
    ((s.card : ℝ) - 1) * ε ≤ s.max' hne - s.min' hne := by
  have hcard1 : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hne.card_pos
  rcases le_or_gt ε 0 with hε | hε
  · nlinarith [s.min'_le_max' hne, hcard1, hε,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (s.card : ℝ) - 1) (by linarith : (0 : ℝ) ≤ -ε)]
  · have hεne : ε ≠ 0 := hε.ne'
    have hsub : ∀ x ∈ s, x ∈ Set.Icc (s.min' hne) (s.max' hne) :=
      fun x hx => ⟨s.min'_le x hx, s.le_max' x hx⟩
    have hab : s.min' hne ≤ s.max' hne := s.min'_le_max' hne
    have h := card_le_of_pairwise_le_subset_Icc hε hab hsub hsep
    have hkey : (s.card : ℝ) - 1 ≤ (s.max' hne - s.min' hne) / ε := by linarith
    calc ((s.card : ℝ) - 1) * ε
        ≤ ((s.max' hne - s.min' hne) / ε) * ε := mul_le_mul_of_nonneg_right hkey hε.le
      _ = s.max' hne - s.min' hne := by field_simp

/-- A finite set of reals in `[-r, r]` whose points are pairwise `1/4`-separated
has at most `10 * r` elements (when `1/2 ≤ r`). -/
lemma card_le_ten_r_of_pairwise_quarter_separated
    {s : Finset ℝ} {r : ℝ} (hr : 1 / 2 ≤ r)
    (hsub : ∀ x ∈ s, x ∈ Set.Icc (-r) r)
    (hsep : (s : Set ℝ).Pairwise (fun x y => 1 / 4 ≤ |x - y|)) :
    (s.card : ℝ) ≤ 10 * r := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hab : -r ≤ r := by linarith
  have h := card_le_of_pairwise_le_subset_Icc hε hab hsub hsep
  have h' : (s.card : ℝ) ≤ 8 * r + 1 := by
    have heq : (r - -r) / (1 / 4) = 8 * r := by ring
    linarith
  linarith

/-- **Finite maximal `ε`-separated subset.** For a finite `S`, a symmetric
"distance" `d` with `d a a < ε`, there is `P ⊆ S` that is `ε`-separated and
maximal: every `r ∈ S` is within `ε` of some `w ∈ P`. (Greedy: take a subset of
maximum cardinality among the `ε`-separated ones.) -/
theorem exists_maximal_separated_finset {α : Type*}
    (S : Finset α) (d : α → α → ℝ) {ε : ℝ}
    (hd_self : ∀ a, d a a < ε) (hd_symm : ∀ a b, d a b = d b a) :
    ∃ P : Finset α, P ⊆ S ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → ε ≤ d a b) ∧
      (∀ r ∈ S, ∃ w ∈ P, d r w < ε) := by
  classical
  let pred : Finset α → Prop := fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ε ≤ d a b
  obtain ⟨P, hP_mem, hP_max⟩ :=
    (S.powerset.filter pred).exists_max_image Finset.card
      ⟨∅, Finset.mem_filter.mpr ⟨by simp, by intro a ha; simp at ha⟩⟩
  obtain ⟨hP_pow, hP_sep⟩ := Finset.mem_filter.mp hP_mem
  have hP_sub : P ⊆ S := Finset.mem_powerset.mp hP_pow
  refine ⟨P, hP_sub, hP_sep, ?_⟩
  intro r hr
  by_contra hcon
  push Not at hcon
  have hr_notin : r ∉ P := fun hrP => absurd (hd_self r) (not_lt.mpr (hcon r hrP))
  have hP'_sep : pred (insert r P) := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hcon b hb
    · rw [hd_symm]; exact hcon a ha
    · exact hP_sep a ha b hb hab
  have hP'_mem : insert r P ∈ S.powerset.filter pred :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hr hP_sub), hP'_sep⟩
  have hle := hP_max (insert r P) hP'_mem
  rw [Finset.card_insert_of_notMem hr_notin] at hle
  omega

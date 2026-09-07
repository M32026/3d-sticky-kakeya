module

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Induction on Scales Team
-/
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.ExtraBasic
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Minimal coarse tube cover

Given fine dyadic tubes intersecting `unitSquare`, construct a coarse tube cover
of cardinality `O(Δ^{-2})`.

## Whiteprint node
`proposition2_minimal_cover` under `InductionOnScales/Proposition2/MinimalCover/`.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace InductionOnScales

section MinimalCover

/-- The coarse ancestor of a fine tube in the allowed parameter strip is itself
in the allowed strip at the coarse scale. -/
lemma coarseAnc_in_allowed_strip {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n)
    (hT : T.IsInAllowedParameterStrip) :
    (deprecatedCoordinatewiseAncestor hnm T).IsInAllowedParameterStrip := by
  set U := deprecatedCoordinatewiseAncestor hnm T with hU
  set f : ℕ := coarseRefinementFactor n m with hf
  have ha1 : (U.a : ℤ) * (f : ℤ) ≤ T.a := (coarseParentIndex_spec n m hnm T.a).1
  have ha2 : T.a < (U.a + 1) * (f : ℤ) := (coarseParentIndex_spec n m hnm T.a).2
  have hfm : (f : ℤ) = 2 ^ (n - m) := by
    simp [hf, coarseRefinementFactor] <;> norm_cast
  have h_pow : (2 ^ m : ℤ) * (f : ℤ) = (2 ^ n : ℤ) := by
    rw [hfm]
    have h1 : m + (n - m) = n := by omega
    have h2 : (2 ^ m : ℤ) * (2 ^ (n - m) : ℤ) = (2 ^ (m + (n - m)) : ℤ) := by
      rw [←pow_add] <;> ring
    rw [h2, h1]
  constructor
  · -- Lower bound: -2^m ≤ U.a
    by_contra h
    have h' : U.a < -((2 ^ m : ℕ) : ℤ) := by linarith
    have h'' : U.a + 1 ≤ -((2 ^ m : ℕ) : ℤ) := by linarith
    have h3 : (U.a + 1) * (f : ℤ) ≤ -((2 ^ m : ℕ) : ℤ) * (f : ℤ) := by gcongr
    have h41 : ((2 ^ m : ℕ) : ℤ) * (f : ℤ) = ((2 ^ n : ℕ) : ℤ) := h_pow
    have h42 : -((2 ^ m : ℕ) : ℤ) * (f : ℤ) = -(((2 ^ m : ℕ) : ℤ) * (f : ℤ)) := by ring
    have h4 : -((2 ^ m : ℕ) : ℤ) * (f : ℤ) = -((2 ^ n : ℕ) : ℤ) := by
      rw [h42]
      exact congr_arg (fun x : ℤ => -x) h41
    have h5 : (U.a + 1) * (f : ℤ) ≤ -((2 ^ n : ℕ) : ℤ) := by
      calc (U.a + 1) * (f : ℤ)
        ≤ -((2 ^ m : ℕ) : ℤ) * (f : ℤ) := h3
        _ = -((2 ^ n : ℕ) : ℤ) := h4
    have h6 : T.a < (U.a + 1) * (f : ℤ) := ha2
    have h7 : -((2 ^ n : ℕ) : ℤ) ≤ T.a := hT.1
    linarith
  · -- Upper bound: U.a < 2^m
    by_contra h
    have h' : ((2 ^ m : ℕ) : ℤ) ≤ U.a := by linarith
    have h3 : ((2 ^ m : ℕ) : ℤ) * (f : ℤ) ≤ U.a * (f : ℤ) := by gcongr
    have h41 : ((2 ^ m : ℕ) : ℤ) * (f : ℤ) = ((2 ^ n : ℕ) : ℤ) := h_pow
    have h5 : ((2 ^ n : ℕ) : ℤ) ≤ U.a * (f : ℤ) := by
      calc ((2 ^ n : ℕ) : ℤ)
        = ((2 ^ m : ℕ) : ℤ) * (f : ℤ) := h41.symm
        _ ≤ U.a * (f : ℤ) := h3
    have h6 : U.a * (f : ℤ) ≤ T.a := ha1
    have h7 : T.a < ((2 ^ n : ℕ) : ℤ) := hT.2
    linarith

/-- If a coarse tube in the allowed strip intersects `unitSquare`, its
intercept index is bounded: `-2^m ≤ U.b < 2^(m+1)`. -/
lemma coarse_tube_bounded_intercept {m : ℕ} (U : DyadicTube m)
    (hU : U.IsInAllowedParameterStrip)
    (h_int : (U.toSet ∩ unitSquare).Nonempty) :
    -((2 ^ m : ℕ) : ℤ) ≤ U.b ∧ U.b < ((2 ^ (m + 1) : ℕ) : ℤ) := by
  set Δ : ℝ := dyadicDelta m with hΔ
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  rcases h_int with ⟨p, hp⟩
  have h_p_in_square : p ∈ unitSquare := hp.2
  have h_p_in_tube : p ∈ U.toSet := hp.1
  rcases h_p_in_tube with ⟨slope, hslope, intercept, hintercept, h_eq⟩
  have hx_nonneg : 0 ≤ p.1 := (Set.mem_prod.mp h_p_in_square).1.1
  have hx_lt_one : p.1 < 1 := (Set.mem_prod.mp h_p_in_square).1.2
  have hy_nonneg : 0 ≤ p.2 := (Set.mem_prod.mp h_p_in_square).2.1
  have hy_lt_one : p.2 < 1 := (Set.mem_prod.mp h_p_in_square).2.2
  have h_slope_ge : -1 ≤ slope := by
    have h1 : -((2 ^ m : ℕ) : ℝ) ≤ (U.a : ℝ) := by exact_mod_cast hU.1
    have h2 : (U.a : ℝ) * Δ ≤ slope := hslope.1
    have h3 : -1 ≤ (U.a : ℝ) * Δ := by
      have h4 : (U.a : ℝ) * Δ ≥ (-((2 ^ m : ℕ) : ℝ)) * Δ := by gcongr
      have h5 : (-((2 ^ m : ℕ) : ℝ)) * Δ = -1 := by
        simp [hΔ, dyadicDelta] <;> field_simp <;> ring
      linarith
    linarith
  have h_slope_lt : slope < 1 := by
    have h1 : (U.a + 1 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
      have h2 : U.a < ((2 ^ m : ℕ) : ℤ) := hU.2
      have h3 : U.a + 1 ≤ ((2 ^ m : ℕ) : ℤ) := by omega
      exact_mod_cast h3
    have h4 : slope < ((U.a + 1 : ℝ) * Δ) := hslope.2
    have h5 : ((U.a + 1 : ℝ) * Δ) ≤ (((2 ^ m : ℕ) : ℝ) * Δ) := by gcongr
    have h6 : (((2 ^ m : ℕ) : ℝ) * Δ) = 1 := by
      simp [hΔ, dyadicDelta] <;> field_simp <;> ring
    linarith
  have h_intercept_eq : intercept = p.2 - slope * p.1 := by linarith
  have h_intercept_gt : -1 < intercept := by
    rw [h_intercept_eq]
    by_cases hsl : 0 ≤ slope
    · -- slope ≥ 0: slope * p.1 < 1
      have h : slope * p.1 < 1 := by
        by_cases hx : 0 < p.1
        · have h2 : slope * p.1 < 1 * p.1 := mul_lt_mul_of_pos_right h_slope_lt hx
          have h3 : 1 * p.1 < 1 := by rw [one_mul] <;> linarith
          linarith
        · have hx0 : p.1 = 0 := by linarith
          rw [hx0] <;> norm_num
      linarith
    · -- slope < 0: slope * p.1 ≤ 0, so intercept ≥ p.2 ≥ 0 > -1
      have h_nonpos : slope * p.1 ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hx_nonneg
      have h_ge : p.2 - slope * p.1 ≥ p.2 := by linarith
      linarith
  have h_intercept_lt : intercept < 2 := by
    rw [h_intercept_eq]
    by_cases hsl : 0 ≤ slope
    · -- slope ≥ 0: intercept ≤ p.2 < 1 < 2
      have h : slope * p.1 ≥ 0 := mul_nonneg hsl hx_nonneg
      linarith
    · -- slope < 0: slope * p.1 ≥ -p.1 > -1, so -slope*p.1 < 1
      have h_ge : slope * p.1 ≥ -p.1 := by
        have h2 : slope ≥ -1 := h_slope_ge
        have h3 : slope * p.1 ≥ (-1 : ℝ) * p.1 := by gcongr
        linarith
      have h4 : -p.1 > -1 := by linarith
      have h5 : slope * p.1 > -1 := by linarith
      have h6 : -slope * p.1 < 1 := by linarith
      linarith
  have h_b1 : (U.b : ℝ) * Δ ≤ intercept := hintercept.1
  have h_b2 : intercept < (U.b + 1 : ℝ) * Δ := hintercept.2
  constructor
  · -- Lower bound: -2^m ≤ U.b
    by_contra h
    have h' : U.b < -((2 ^ m : ℕ) : ℤ) := by linarith
    have h'' : U.b + 1 ≤ -((2 ^ m : ℕ) : ℤ) := by linarith
    have h6 : (U.b + 1 : ℝ) * Δ ≤ -1 := by
      have h7 : (U.b + 1 : ℝ) ≤ -((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h''
      have h8 : (U.b + 1 : ℝ) * Δ ≤ (-((2 ^ m : ℕ) : ℝ)) * Δ := by gcongr
      have h9 : (-((2 ^ m : ℕ) : ℝ)) * Δ = -1 := by
        simp [hΔ, dyadicDelta] <;> field_simp <;> ring
      linarith
    linarith
  · -- Upper bound: U.b < 2^(m+1)
    by_contra h
    have h' : ((2 ^ (m + 1) : ℕ) : ℤ) ≤ U.b := by linarith
    have h6 : 2 ≤ (U.b : ℝ) * Δ := by
      have h7 : ((2 ^ (m + 1) : ℕ) : ℝ) ≤ (U.b : ℝ) := by exact_mod_cast h'
      have h8 : ((2 ^ (m + 1) : ℕ) : ℝ) * Δ ≤ (U.b : ℝ) * Δ := by gcongr
      have h9 : ((2 ^ (m + 1) : ℕ) : ℝ) * Δ = 2 := by
        simp [hΔ, dyadicDelta, pow_succ] <;> field_simp <;> ring
      linarith
    linarith

/-- The finset of all coarse tubes with indices in the bounded ranges. -/
noncomputable def boundedTubes (m : ℕ) : Finset (DyadicTube m) :=
  (Finset.Ico (-(2 ^ m)) (2 ^ m)).product (Finset.Ico (-(2 ^ m)) (2 ^ (m + 1)))
  |>.image (fun p : ℤ × ℤ => ⟨p.1, p.2⟩)

/-- Any coarse tube in the allowed strip that intersects `unitSquare` belongs
to `boundedTubes m`. -/
lemma coarse_tube_mem_bounded {m : ℕ} (U : DyadicTube m)
    (hU : U.IsInAllowedParameterStrip)
    (h_int : (U.toSet ∩ unitSquare).Nonempty) :
    U ∈ boundedTubes m := by
  have h_a : U.a ∈ Finset.Ico (-(2 ^ m)) (2 ^ m) := by
    simp only [Finset.mem_Ico]
    exact ⟨hU.1, hU.2⟩
  have h_b := coarse_tube_bounded_intercept U hU h_int
  have h_b' : U.b ∈ Finset.Ico (-(2 ^ m)) (2 ^ (m + 1)) := by
    simp only [Finset.mem_Ico]
    exact ⟨h_b.1, h_b.2⟩
  have h : (U.a, U.b) ∈ (Finset.Ico (-(2 ^ m)) (2 ^ m)).product
      (Finset.Ico (-(2 ^ m)) (2 ^ (m + 1))) := by
    exact Finset.mem_product.mpr ⟨h_a, h_b'⟩
  exact Finset.mem_image.mpr ⟨(U.a, U.b), h, by
    simp [DyadicTube.mk.injEq] <;> aesop⟩

/-- Cardinality of `boundedTubes m` is at most `100 * 2^(2m)`. -/
lemma boundedTubes_card (m : ℕ) :
    (boundedTubes m).card ≤ 100 * 2 ^ (2 * m) := by
  let aSet := Finset.Ico (-(2 ^ m)) (2 ^ m)
  let bSet := Finset.Ico (-(2 ^ m)) (2 ^ (m + 1))
  have h_inj : Set.InjOn (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : DyadicTube m))
      (aSet.product bSet) := by
    intro p _ q _ h
    have h1 : p.1 = q.1 ∧ p.2 = q.2 := by
      cases p <;> cases q <;> simp [DyadicTube.mk.injEq] at h <;> exact ⟨h.1, h.2⟩
    exact Prod.ext h1.1 h1.2
  have h_card : (boundedTubes m).card = (aSet.product bSet).card := by
    rw [boundedTubes, Finset.card_image_of_injOn h_inj]
  have h_prod : (aSet.product bSet).card = aSet.card * bSet.card := by
    simp [Finset.product]
    <;> rw [Finset.card_biUnion]
    <;> simp [Finset.card_image_of_injOn]
    <;> ring
  rw [h_card, h_prod]
  have h_a_card : aSet.card = 2 ^ (m + 1) := by
    have h1 : aSet.card = ((2 ^ m : ℤ) - (-(2 ^ m : ℤ))).toNat := by
      simpa [aSet] using Int.card_Ico (-(2 ^ m : ℤ)) (2 ^ m : ℤ)
    rw [h1]
    have h2 : ((2 ^ m : ℤ) - (-(2 ^ m : ℤ))) = (2 * (2 ^ m : ℤ)) := by ring
    rw [h2]
    <;> norm_cast <;> omega
  have h_b_card : bSet.card = 3 * 2 ^ m := by
    have h1 : bSet.card = ((2 ^ (m + 1) : ℤ) - (-(2 ^ m : ℤ))).toNat := by
      simpa [bSet] using Int.card_Ico (-(2 ^ m : ℤ)) (2 ^ (m + 1) : ℤ)
    rw [h1]
    have h2 : ((2 ^ (m + 1) : ℤ) - (-(2 ^ m : ℤ))) = (3 * (2 ^ m : ℤ)) := by
      simp [pow_succ] <;> ring
    rw [h2]
    <;> norm_cast <;> omega
  rw [h_a_card, h_b_card]
  have h_pow2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ] <;> ring
  rw [h_pow2]
  have h_main : (2 * 2 ^ m) * (3 * 2 ^ m) ≤ 100 * 2 ^ (2 * m) := by
    have h5 : (2 * 2 ^ m) * (3 * 2 ^ m) = 6 * (2 ^ m * 2 ^ m) := by ring
    rw [h5]
    have h6 : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by
      rw [←pow_add] <;> ring
    rw [h6]
    have h_pos : 0 ≤ 2 ^ (2 * m) := by positivity
    nlinarith
  exact h_main

/-- Minimal coarse tube cover: every fine tube is contained in its coarse
ancestor, and the number of distinct ancestors is `O(Δ^{-2})`. -/
theorem minimal_coarse_cover {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n))
    (h_incidence : ∀ T ∈ F, (T.toSet ∩ unitSquare).Nonempty)
    (h_params : ∀ T ∈ F, T.IsInAllowedParameterStrip) :
    ∃ (cover : Finset (DyadicTube m)),
      (∀ T ∈ F, ∃ U ∈ cover, T.toSet ⊆ U.toSet) ∧
      (cover.card : ℝ) ≤ 100 * (dyadicDelta m)^(-2 : ℝ) := by
  let cover : Finset (DyadicTube m) :=
    F.image (deprecatedCoordinatewiseAncestor hnm)
  have h_cover : ∀ T ∈ F, ∃ U ∈ cover, T.toSet ⊆ U.toSet := by
    intro T hT
    let U := deprecatedCoordinatewiseAncestor hnm T
    have hU_in : U ∈ cover := by
      exact Finset.mem_image.mpr ⟨T, hT, rfl⟩
    exact ⟨U, hU_in, coarseAnc_contains hnm T⟩
  have h_cover_subset : cover ⊆ boundedTubes m := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨T, hT, rfl⟩
    let U' := deprecatedCoordinatewiseAncestor hnm T
    have hU'_strip : U'.IsInAllowedParameterStrip :=
      coarseAnc_in_allowed_strip hnm T (h_params T hT)
    have hT_int : (T.toSet ∩ unitSquare).Nonempty := h_incidence T hT
    have hU'_int : (U'.toSet ∩ unitSquare).Nonempty := by
      rcases hT_int with ⟨p, hp⟩
      have h1 : p ∈ T.toSet := hp.1
      have h2 : p ∈ unitSquare := hp.2
      have h3 : p ∈ U'.toSet := (coarseAnc_contains hnm T) h1
      exact ⟨p, h3, h2⟩
    exact coarse_tube_mem_bounded U' hU'_strip hU'_int
  have h_card : cover.card ≤ (boundedTubes m).card := Finset.card_le_card h_cover_subset
  have h_main : (cover.card : ℝ) ≤ (100 * 2 ^ (2 * m) : ℝ) := by
    exact_mod_cast h_card.trans (boundedTubes_card m)
  have h_eq : (2 ^ (2 * m) : ℝ) = (dyadicDelta m)^(-2 : ℝ) := by
    simp [dyadicDelta, Real.rpow_neg] <;> field_simp <;> ring
  rw [h_eq] at h_main
  exact ⟨cover, h_cover, h_main⟩

end MinimalCover

end InductionOnScales

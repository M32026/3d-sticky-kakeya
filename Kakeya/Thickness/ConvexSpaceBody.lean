/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Volume
public import Kakeya.Mathlib.ENNReal
public import Kakeya.Thickness.Cthickening
public import Kakeya.ConvexSpaceBody

/-! # Thickness of convex bodies

We collect basic estimates about affine thicknesses of convex body.

TODO: Make these available for `NormedAddTorsor`s of `InnerProductSpace`s
-/

open Metric Module MeasureTheory

@[expose] public section

variable
  {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem thickness_le_smul_thickness_iff (W W' : ConvexSpaceBody E) (a : NNReal) :
    thickness ℝ W.carrier ≤ a • thickness ℝ W'.carrier ↔
      ethickness ℝ W.carrier ≤ a • ethickness ℝ W'.carrier := by
  rw [Pi.le_def, Pi.le_def]
  apply forall_congr'
  intro k
  simp only [Pi.smul_apply]
  rw [ethickness_thickness W.isCompact'.isBounded]
  rw [ethickness_thickness W'.isCompact'.isBounded]
  simp only [Function.comp_apply]
  refine (ENNReal.ofReal_smul_le_ofReal_iff ?_ a).symm
  apply thickness_nonneg

example {x : ℕ → ℝ} {a : ℕ} : a • x = (a : NNReal) • x := by
  exact Eq.symm (Nat.cast_smul_eq_nsmul NNReal a x)

theorem thickness_le_nsmul_thickness_iff {W W' : ConvexSpaceBody E} {a : ℕ} :
    thickness ℝ W.carrier ≤ a • thickness ℝ W'.carrier ↔
      ethickness ℝ W.carrier ≤ a • ethickness ℝ W'.carrier := by
  -- convert to the NNReal version
  have h := thickness_le_smul_thickness_iff W W' (a : NNReal)
  simpa [← Nat.cast_smul_eq_nsmul NNReal] using h

variable
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The constant in `volume_le_of_ethickness_le` etc. -/
@[nolint defsWithUnderscore]
noncomputable abbrev Metric.volume_comparison.C (n : ℕ) : NNReal := 4 ^ n / lt_volume_convexHull.c n

lemma Metric.volume_comparison.C_pos n : 0 < C n := by
  positivity

lemma Metric.volume_comparison.C_two : C 2 = 32 := by
  norm_num

private lemma Metric.volume_comparison.C_mul_convexHullC {n} :
    (volume_comparison.C n : ENNReal) * (lt_volume_convexHull.c n : ENNReal) = 2 ^ n * 2 ^ n := by
  norm_cast
  rw [← mul_pow]
  norm_num
  refine mul_inv_cancel_right₀ ?_ (4 ^ n)
  norm_cast
  apply Nat.factorial_ne_zero

/-- Volume bound from `ethickness` bound -/
theorem ConvexSpaceBody.volume_le_of_ethickness_le {W W' : ConvexSpaceBody E}
    (h : ethickness ℝ W.carrier ≤ 2 • ethickness ℝ W'.carrier) :
    volume W.carrier ≤ volume_comparison.C (finrank ℝ E) * (volume W'.carrier) := by
  set n := finrank ℝ E
  have hc0 : (lt_volume_convexHull.c n : ENNReal) ≠ 0 := by
    exact_mod_cast (lt_volume_convexHull.c_pos n).ne'
  -- Per-factor ethickness comparison gives the product comparison.
  have hprodcmp : (∏ k ∈ Finset.range n, ethickness ℝ W.carrier k)
      ≤ 2 ^ n * ∏ k ∈ Finset.range n, ethickness ℝ W'.carrier k := by
    calc
      _ ≤ ∏ k ∈ Finset.range n, (2 * ethickness ℝ W'.carrier k) :=
          Finset.prod_le_prod' fun k _ => by
            simpa [Pi.smul_apply, nsmul_eq_mul] using h k
      _ = 2 ^ n * ∏ k ∈ Finset.range n, ethickness ℝ W'.carrier k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  calc
    _ ≤ 2 ^ n * ∏ k ∈ Finset.range n, ethickness ℝ W.carrier k := volume_le_prod_ethickness _
    _ ≤ 2 ^ n * (2 ^ n * ∏ k ∈ Finset.range n, ethickness ℝ W'.carrier k) := by gcongr
    _ = volume_comparison.C n *
          (lt_volume_convexHull.c n * ∏ k ∈ Finset.range n, ethickness ℝ W'.carrier k) := by
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        rw [volume_comparison.C_mul_convexHullC]
    _ ≤ _ := by
        gcongr
        exact W'.convex.ethickness_prod_le_volume

/-- Volume bound from `ethickness` bound -/
theorem ConvexSpaceBody.volume_le_of_thickness_le {W W' : ConvexSpaceBody E}
    (h : thickness ℝ W.carrier ≤ 2 • thickness ℝ W'.carrier) :
    volume W.carrier ≤ volume_comparison.C (finrank ℝ E) * (volume W'.carrier) := by
  apply volume_le_of_ethickness_le
  exact thickness_le_nsmul_thickness_iff.mp h

namespace Kakeya

/-- Lower bound for the volume of the 1-thickening of a nonempty compact set:
since a closed ball of radius 1 about any point of `K` is contained in the
1-thickening, the volume of the 1-thickening dominates the volume of the unit
ball. -/
lemma convexBody_cthickening_one_volume_ge_unit_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK_ne : K.Nonempty) :
    volume (Metric.closedBall (0 : E) 1) ≤ volume (Metric.cthickening (1 : ℝ) K) := by
  obtain ⟨p, hp⟩ := hK_ne
  have h_p_ball : Metric.closedBall p 1 ⊆ Metric.cthickening 1 K := by
    intro x hx
    refine Metric.mem_cthickening_of_dist_le x p 1 K hp ?_
    rwa [Metric.mem_closedBall] at hx
  have h_vol_eq :
      volume (Metric.closedBall p (1 : ℝ)) = volume (Metric.closedBall (0 : E) (1 : ℝ)) :=
    MeasureTheory.Measure.addHaar_closedBall_center (volume : MeasureTheory.Measure E) p 1
  rw [← h_vol_eq]
  exact measure_mono h_p_ball

/-- Volume bound for closed thickening using a containment ball of the same radius:
if `closedBall p δ ⊆ K` for a convex compact `K`, then
`vol(cthickening δ K) ≤ 2^n · vol(K)`. -/
lemma convexBody_cthickening_volume_le_2pow_of_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Set E) (hK_conv : Convex ℝ K) (hK_compact : IsCompact K)
    (p : E) {δ : ℝ} (hδ_nn : 0 ≤ δ)
    (hp_ball : Metric.closedBall p δ ⊆ K) :
    volume (Metric.cthickening δ K)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E) * volume K := by
  have h_sub : Metric.cthickening δ K ⊆ (AffineMap.homothety p (2 : ℝ)) '' K :=
    cthickening_subset_homothety_two K hK_conv hK_compact p hδ_nn hp_ball
  calc volume (Metric.cthickening δ K)
      ≤ volume ((AffineMap.homothety p (2 : ℝ)) '' K) := measure_mono h_sub
    _ = ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E) * volume K := by
          rw [MeasureTheory.Measure.addHaar_image_homothety volume p (2 : ℝ) K,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ Module.finrank ℝ E)]

/-- **Doubling lemma.** For a convex body `K` and `0 < r ≤ 4`, the volume of the
`4r`-cthickening is bounded by a dimension-only constant times the volume of the
`r`-cthickening. -/
lemma volume_cthickening_four_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] :
    ∃ Cdbl : ℝ, 0 < Cdbl ∧ ∀ (K : ConvexSpaceBody E) (r : ℝ), 0 < r → r ≤ 4 →
      volume.real (Metric.cthickening (4 * r) K.carrier)
        ≤ Cdbl * volume.real (Metric.cthickening r K.carrier) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hC₁_pos : (0 : NNReal) < 2 ^ n := by positivity
  have hC₁ : ∀ (S : Set E), Bornology.IsBounded S → S.Nonempty →
      MeasureTheory.volume S
        ≤ ((2 : NNReal) ^ n : ENNReal) * ∏ j : Fin n,
            ENNReal.ofReal (Metric.thickness ℝ S j.val) := by
    intro S hS_bdd _
    have h := _root_.volume_le_prod_thickness hS_bdd
    rw [← hn_def] at h
    rw [← Fin.prod_univ_eq_prod_range
      (fun i : ℕ => ENNReal.ofReal (Metric.thickness ℝ S i)) n] at h
    exact h
  set C₁ : NNReal := 2 ^ n with hC₁_def
  have hC₁R_pos : 0 < (C₁ : ℝ) := by exact_mod_cast hC₁_pos
  have hC₁_real : ∀ (S : Set E), Bornology.IsBounded S → S.Nonempty →
      volume.real S ≤ (C₁ : ℝ) * ∏ j : Fin n, Metric.thickness ℝ S j.val := by
    intro S hS_bdd hS_ne
    have h := hC₁ S hS_bdd hS_ne
    have hRHS_ne_top : (C₁ : ENNReal) *
        ∏ j : Fin n, ENNReal.ofReal (Metric.thickness ℝ S j.val) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_ne_top h
    simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_prod,
      ENNReal.toReal_ofReal (Metric.thickness_nonneg S _)] using hreal
  obtain ⟨c_K, hc_K_pos, hc_K⟩ := convex_body_volume_thickness_lower_bound (E := E)
  refine ⟨C₁ * (5 : ℝ) ^ n / c_K, by positivity, ?_⟩
  intro K r hr_pos hr_le_four
  set W : Set E := Metric.cthickening r K.carrier with hW_def
  have hr_nn : (0 : ℝ) ≤ r := hr_pos.le
  have hW_bdd : Bornology.IsBounded W := K.isCompact.cthickening.isBounded
  have hW_ne : W.Nonempty := K.nonempty.mono (Metric.self_subset_cthickening _)
  have hW_conv : Convex ℝ W := K.convex.cthickening _
  have hW_compact : IsCompact W := K.isCompact.cthickening
  have h_eq : Metric.cthickening (4 * r) K.carrier = Metric.cthickening (3 * r) W := by
    rw [hW_def, cthickening_cthickening (by linarith) hr_nn]
    congr 1; ring
  let a : Fin n → ℝ := fun j => Metric.thickness ℝ W j.val
  have ha_nn : ∀ j, 0 ≤ a j := fun j => Metric.thickness_nonneg _ _
  have h_thick_le : ∀ j : Fin n,
      Metric.thickness ℝ (Metric.cthickening (3 * r) W) j.val ≤ a j + 3 * r :=
    fun j => Metric.thickness_cthickening_le hW_bdd hW_ne (by linarith) j.val
  have ha_ge : ∀ j : Fin n, r ≤ a j := by
    intro j
    obtain ⟨p, hp⟩ := K.nonempty
    have h_ball_sub : Metric.closedBall p r ⊆ W := by
      rw [hW_def]
      exact Metric.closedBall_subset_cthickening hp r
    have h_mono : Metric.thickness ℝ (Metric.closedBall p r) j.val ≤ a j :=
      Metric.thickness_monotone hW_bdd h_ball_sub j.val
    exact (Metric.thickness_closedBall_ge hr_nn j.isLt).trans h_mono
  have h_le_five : ∀ j : Fin n, a j + 3 * r ≤ 5 * a j := by
    intro j
    have := ha_ge j
    linarith
  have h_upper : volume.real (Metric.cthickening (4 * r) K.carrier)
      ≤ C₁ * ((5 : ℝ) ^ n * ∏ j : Fin n, a j) := by
    rw [h_eq]
    have h1 : volume.real (Metric.cthickening (3 * r) W)
        ≤ C₁ * ∏ j : Fin n, Metric.thickness ℝ (Metric.cthickening (3 * r) W) j.val :=
      hC₁_real (Metric.cthickening (3 * r) W) hW_bdd.cthickening
        (hW_ne.mono (Metric.self_subset_cthickening _))
    have h_prod_le :
        ∏ j : Fin n, Metric.thickness ℝ (Metric.cthickening (3 * r) W) j.val
          ≤ ∏ j : Fin n, (5 * a j) := by
      apply Finset.prod_le_prod
      · intro j _; exact Metric.thickness_nonneg _ _
      · intro j _; exact (h_thick_le j).trans (h_le_five j)
    have h_prod_eq : ∏ j : Fin n, (5 * a j) = (5 : ℝ) ^ n * ∏ j : Fin n, a j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc volume.real (Metric.cthickening (3 * r) W)
        ≤ C₁ * ∏ j : Fin n, Metric.thickness ℝ (Metric.cthickening (3 * r) W) j.val := h1
      _ ≤ C₁ * ∏ j : Fin n, (5 * a j) :=
        mul_le_mul_of_nonneg_left h_prod_le hC₁R_pos.le
      _ = C₁ * ((5 : ℝ) ^ n * ∏ j : Fin n, a j) := by rw [h_prod_eq]
  have h_lower : c_K * (∏ j : Fin n, a j) ≤ volume.real (Metric.cthickening r K.carrier) := by
    have := hc_K W hW_conv hW_compact hW_ne
    rwa [hW_def] at this
  have h_prod_a_nn : 0 ≤ ∏ j : Fin n, a j := Finset.prod_nonneg (fun j _ => ha_nn j)
  calc volume.real (Metric.cthickening (4 * r) K.carrier)
      ≤ C₁ * ((5 : ℝ) ^ n * ∏ j : Fin n, a j) := h_upper
    _ = (C₁ * (5 : ℝ) ^ n / c_K) * (c_K * (∏ j : Fin n, a j)) := by
        field_simp
    _ ≤ (C₁ * (5 : ℝ) ^ n / c_K) * volume.real (Metric.cthickening r K.carrier) :=
        mul_le_mul_of_nonneg_left h_lower (by positivity)

end Kakeya

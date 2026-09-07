module

/-
  ScaleConversionHelpers.lean

  Scale-conversion lemmas for the FrontEndComposition point-mass wiring.

  Contains:
  - `sqrt_cover_to_delta_cover`: convert Ncover(√δ, P) bound to Ncover(Δ, P)
    with factor-4 absorption.

  Requires BOTH inequalities from `exists_even_dyadic_scale_above`:
    hδ_leδn : δ ≤ δ_n        (used for scale monotonicity √δ ≤ Δ)
    hδ_n_le_4δ : δ_n ≤ 4 * δ  (used only for factor-4 exponent absorption)

  This complements Kestrel's EndpointAdapter, which handles exponent identity
  transfer at the SAME scale √δ. This module handles the DIFFERENT scale
  conversion √δ → Δ needed for the coarse cardinality upper bound.

  Whiteprint: supports Phase 4 (point-mass wiring) of INTEGRATION_PLAN_v2.md.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Convert an Ncover bound at scale √δ to a bound at scale Δ.

    Requires BOTH:
      hδ_leδn : δ ≤ δ_n       → √δ ≤ √δ_n = Δ  →  Ncover(Δ,P) ≤ Ncover(√δ,P)
      hδ_n_le_4δ : δ_n ≤ 4δ   → δ ≥ Δ²/4       →  factor 4^{u/2+εA} absorption

    Input:  Ncover(√δ, P) ≤ δ^{-(u/2 + εA)}
    Output: Ncover(Δ, P) ≤ 4^(u/2 + εA) · Δ^{-(u + 2*εA)}

    Both inequalities are returned by `exists_even_dyadic_scale_above`.
    Do NOT derive δ ≤ δ_n from δ_n ≤ 4δ; that implication is false.

    Used to wire the top-level `hNcover_sqrt` hypothesis to the B1
    coarse cardinality upper bound at scale Δ.
-/
lemma sqrt_cover_to_delta_cover
    {δ δ_n Δ u εA : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_n_pos : 0 < δ_n)
    (hΔ_pos : 0 < Δ)
    (hδ_n_eq2 : δ_n = Δ^2)
    (hδ_leδn : δ ≤ δ_n)
    (hδ_n_le_4δ : δ_n ≤ 4 * δ)
    (hu_pos : 0 < u)
    (hεA_pos : 0 < εA)
    {P : Set EuclideanPlane}
    (hNcover_sqrt : Ncover (Real.sqrt δ) P ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA)))) :
    Ncover Δ P ≤
      ENNReal.ofReal ((4 : ℝ)^(u / 2 + εA) * Real.rpow Δ (-(u + 2 * εA))) := by
  set f : ℝ := u / 2 + εA with hf_def
  have hf_pos : 0 < f := by linarith
  -- Step 1: scale monotonicity — δ ≤ δ_n = Δ² implies √δ ≤ Δ,
  -- so covering at larger scale Δ needs no more balls than at √δ.
  have h1 : Real.sqrt δ ≤ Δ := by
    have h2 : Real.sqrt δ ≤ Real.sqrt δ_n := Real.sqrt_le_sqrt hδ_leδn
    have h3 : Real.sqrt δ_n = Δ := by
      rw [hδ_n_eq2]
      rw [Real.sqrt_sq (by linarith)]
    rw [h3] at h2
    exact h2
  have h41 : (Real.sqrt δ).toNNReal ≤ Δ.toNNReal := by
    have h_coe : ((Real.sqrt δ).toNNReal : ℝ) ≤ (Δ.toNNReal : ℝ) := by
      simp [Real.toNNReal_of_nonneg (Real.sqrt_nonneg δ), Real.toNNReal_of_nonneg hΔ_pos.le, h1]
    exact NNReal.coe_le_coe.mp h_coe
  have h4 : Ncover Δ P ≤ Ncover (Real.sqrt δ) P := by
    simpa [Ncover] using Metric.externalCoveringNumber_anti h41
  -- Step 2: factor-4 absorption — δ_n ≤ 4δ implies δ ≥ Δ²/4,
  -- so δ^{-f} ≤ (Δ²/4)^{-f} = 4^f · Δ^{-2f}.
  have h5 : δ ≥ Δ^2 / 4 := by linarith [hδ_n_le_4δ, hδ_n_eq2]
  have h71 : 0 < Δ^2 / 4 := by positivity
  have h72 : Δ^2 / 4 ≤ δ := by linarith
  have h73 : -f ≤ 0 := by linarith
  have h7 : Real.rpow δ (-f) ≤ Real.rpow (Δ^2 / 4) (-f) :=
    Real.rpow_le_rpow_of_nonpos h71 h72 h73
  have h_posΔ : 0 < Δ := hΔ_pos
  have h_pos4 : 0 < (4 : ℝ) := by norm_num
  have h_pos2 : 0 < Δ^2 := by positivity
  have h_pos_le : 0 ≤ Δ := hΔ_pos.le
  -- Key identity: (Δ²/4)^{-f} = 4^f · Δ^{-2f}, proved in ^ notation
  have hA : (Δ^2 / 4 : ℝ) ^ (-f) = (((Δ^2 / 4 : ℝ) ^ f)⁻¹) :=
    Real.rpow_neg (by positivity) f
  have hB : (Δ^2 / 4 : ℝ) ^ f = (Δ^2 : ℝ) ^ f / (4 : ℝ) ^ f :=
    Real.div_rpow (by positivity) (by positivity) f
  have hC1 : (Δ^2 : ℝ) = (Δ : ℝ) ^ (2 : ℝ) := by
    have h : (Δ : ℝ) ^ (2 : ℝ) = (Δ : ℝ) ^ (2 : ℕ) := Real.rpow_natCast Δ (2 : ℕ)
    exact h.symm
  have hC : (Δ^2 : ℝ) ^ f = (Δ : ℝ) ^ (2 * f) := by
    rw [hC1]
    exact (Real.rpow_mul h_pos_le (2 : ℝ) f).symm
  have hD : (Δ : ℝ) ^ (-(2 * f)) = ((Δ : ℝ) ^ (2 * f))⁻¹ :=
    Real.rpow_neg h_pos_le (2 * f)
  have h8 : (Δ^2 / 4 : ℝ) ^ (-f) =
      (4 : ℝ)^f * (Δ : ℝ) ^ (-(u + 2 * εA)) := by
    calc (Δ^2 / 4 : ℝ) ^ (-f)
      = (((Δ^2 / 4 : ℝ) ^ f)⁻¹) := hA
    _ = (((Δ^2 : ℝ) ^ f / (4 : ℝ) ^ f)⁻¹) := by rw [hB]
    _ = (((Δ : ℝ) ^ (2 * f) / (4 : ℝ) ^ f)⁻¹) := by rw [hC]
    _ = (4 : ℝ) ^ f / (Δ : ℝ) ^ (2 * f) := by
      field_simp [h_pos2.ne', h_pos4.ne'] <;> ring
    _ = (4 : ℝ) ^ f * ((Δ : ℝ) ^ (2 * f))⁻¹ := by
      field_simp [h_pos2.ne'] <;> ring
    _ = (4 : ℝ) ^ f * (Δ : ℝ) ^ (-(2 * f)) := by rw [← hD]
    _ = (4 : ℝ) ^ f * (Δ : ℝ) ^ (-(u + 2 * εA)) := by
      have h_eq : -(2 * f) = -(u + 2 * εA) := by dsimp only [f] <;> ring
      rw [h_eq]
  have h7' : (δ : ℝ) ^ (-f) ≤
      (4 : ℝ)^(u / 2 + εA) * (Δ : ℝ) ^ (-(u + 2 * εA)) := by
    calc (δ : ℝ) ^ (-f)
      ≤ (Δ^2 / 4 : ℝ) ^ (-f) := h7
    _ = (4 : ℝ)^f * (Δ : ℝ) ^ (-(u + 2 * εA)) := h8
    _ = (4 : ℝ)^(u / 2 + εA) * (Δ : ℝ) ^ (-(u + 2 * εA)) := by
      have hf : f = u / 2 + εA := by dsimp only [f] <;> ring
      rw [hf]
  calc Ncover Δ P
    ≤ Ncover (Real.sqrt δ) P := h4
  _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-f)) := hNcover_sqrt
  _ ≤ ENNReal.ofReal ((4 : ℝ)^(u / 2 + εA) * (Δ : ℝ) ^ (-(u + 2 * εA))) :=
    ENNReal.ofReal_le_ofReal h7'

end DirecretisedFurstenbergEstimate.FrontEndLemmas

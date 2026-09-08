/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.Thickness.HasThicknesses
public import Kakeya.Thickness.Scale
public import Kakeya.KatzTao

/-! # Controlled closed neighborhoods

This file records the stability properties of a convex body under a closed neighborhood whose
radius is at most the body's scale.  The construction-specific results are separated from the
abstract property needed by density arguments: memberwise containment together with controlled
volume inflation.
-/

@[expose] public section

open Convexity MeasureTheory Metric Module

namespace ConvexSpaceBody

section Geometry

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Thickening a convex body by `r` adds exactly `r` to every affine thickness below the
ambient dimension. -/
theorem ethickness_cthickening_eq (K : ConvexSpaceBody E) (r : NNReal) {k : ℕ}
    (hk : k < finrank ℝ E) :
    ethickness ℝ (K.cthickening (r : ℝ)).carrier k =
      (r : ENNReal) + ethickness ℝ K.carrier k := by
  apply le_antisymm
  · simpa using ethickness_cthickening_le (s := K.carrier) r k
  · change (r : ENNReal) + ethickness ℝ K.carrier k ≤
      ethickness ℝ (Metric.cthickening (r : ℝ) K.carrier) k
    have h := le_ethickness_cthickening K.nonempty' (ρ := (r : ℝ)) hk
    simpa only [ENNReal.ofReal_coe_nnreal, add_comm] using h

variable [Nontrivial E]

/-- Thickening a convex body by `r` adds exactly `r` to its `ethickness.scale`. -/
theorem ethickness_scale_cthickening_eq (K : ConvexSpaceBody E) (r : NNReal) :
    ethickness.scale ℝ (K.cthickening (r : ℝ)).carrier =
      (r : ENNReal) + ethickness.scale ℝ K.carrier := by
  rw [ethickness.scale_eq, ethickness.scale_eq]
  exact ethickness_cthickening_eq K r (Nat.sub_one_lt (finrank_pos.ne'))

/-- A radius bounded by the real-valued scale is also bounded by `ethickness.scale`. -/
  theorem coe_le_ethickness_scale_of_le_scale (K : ConvexSpaceBody E) (r : NNReal)
    (hr : (r : ℝ) ≤ K.scale) :
    (r : ENNReal) ≤ ethickness.scale ℝ K.carrier := by
  rw [ethickness.scale_eq]
  have h := ethickness_thickness' (𝕜 := ℝ) K.isCompact'.isBounded (finrank ℝ E - 1)
  rw [h]
  simpa using ENNReal.ofReal_le_ofReal hr

/-- If `r` is at most the scale of `K`, then every affine thickness grows by at most a factor
of two. -/
theorem ethickness_cthickening_le_two (K : ConvexSpaceBody E) (r : NNReal)
    (hr : (r : ℝ) ≤ K.scale) :
    ethickness ℝ (K.cthickening (r : ℝ)).carrier ≤ 2 • ethickness ℝ K.carrier := by
  intro k
  by_cases hk : k < finrank ℝ E
  · rw [ethickness_cthickening_eq K r hk]
    simp only [Pi.smul_apply]
    have hr' := (coe_le_ethickness_scale_of_le_scale K r hr).trans
      (ethickness.scale_le K.carrier hk)
    calc
      (r : ENNReal) + ethickness ℝ K.carrier k =
          ethickness ℝ K.carrier k + r := add_comm _ _
      _ ≤ ethickness ℝ K.carrier k + ethickness ℝ K.carrier k :=
        add_le_add_right hr' _
      _ = 2 • ethickness ℝ K.carrier k := (two_nsmul _).symm
  · have hk' : finrank ℝ E ≤ k := Nat.le_of_not_gt hk
    simp only [Pi.smul_apply]
    rw [ethickness_eq_zero_of_finrank_le hk', ethickness_eq_zero_of_finrank_le hk', smul_zero]

/-- **Thickness profiles survive a small closed neighborhood** (blueprint
`lem:hasThicknessesCthickening`): if `K` has affine thicknesses comparable to `t` with constant
`C₀`, and `r` is at most the scale of `K`, then `N_r K` has affine thicknesses comparable to `t`
with constant `2 * C₀`.

Only the upper half of the profile is affected: the lower half is inherited from
`K ≤ K.cthickening r` and then weakened to match the doubled constant; that weakening needs
`0 ≤ t k` and nothing else, so no lower bound on `C₀` is assumed. The length of the prescribed
sequence `t` is arbitrary; the intended instantiation is at the ambient dimension. -/
theorem hasThicknesses_cthickening {m : ℕ} {C₀ : NNReal} {t : Fin m → ℝ}
    (K : ConvexSpaceBody E) (r : NNReal) (hr : (r : ℝ) ≤ K.scale)
    (ht : ∀ k, 0 ≤ t k) (hK : Kakeya.HasThicknesses K.carrier C₀ t) :
    Kakeya.HasThicknesses (K.cthickening (r : ℝ)).carrier (2 * C₀) t := by
  intro k
  constructor
  · -- lower bound
    have hmono : Metric.thickness ℝ K.carrier ≤
        Metric.thickness ℝ (K.cthickening (r : ℝ)).carrier := by
      exact Metric.thickness_monotone (K.cthickening (r : ℝ)).isCompact'.isBounded
        (Metric.self_subset_cthickening K.carrier)
    have hinv : ((2 * C₀ : NNReal) : ℝ)⁻¹ ≤ (C₀ : ℝ)⁻¹ := by
      have hcast : ((2 * C₀ : NNReal) : ℝ) = 2 * (C₀ : ℝ) := by norm_cast
      rw [hcast]
      by_cases hC : C₀ = 0
      · simp [hC]
      · have hcpos : 0 < (C₀ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.2 hC)
        have h2pos : 0 < 2 * (C₀ : ℝ) := mul_pos (by norm_num) hcpos
        exact (inv_le_inv₀ h2pos hcpos).2 (by linarith)
    calc
      ((2 * C₀ : NNReal) : ℝ)⁻¹ * t k ≤ (C₀ : ℝ)⁻¹ * t k := by
        exact mul_le_mul_of_nonneg_right hinv (ht k)
      _ ≤ Metric.thickness ℝ K.carrier k := (hK k).1
      _ ≤ Metric.thickness ℝ (K.cthickening (r : ℝ)).carrier k := hmono k
  · -- upper bound
    have hE : Metric.thickness ℝ (K.cthickening (r : ℝ)).carrier ≤
        2 • Metric.thickness ℝ K.carrier :=
      thickness_le_nsmul_thickness_iff.mpr (ethickness_cthickening_le_two K r hr)
    calc
      Metric.thickness ℝ (K.cthickening (r : ℝ)).carrier k
          ≤ 2 * Metric.thickness ℝ K.carrier k := by
        simpa [Pi.smul_apply, nsmul_eq_mul] using hE k
      _ ≤ ((2 * C₀ : NNReal) : ℝ) * t k := by
        have h2' : ((2 * C₀ : NNReal) : ℝ) = 2 * (C₀ : ℝ) := by norm_cast
        rw [h2', mul_assoc]
        exact mul_le_mul_of_nonneg_left (hK k).2 (by norm_num)

/-- **Thickness profiles survive a squeeze between a body and a small closed neighborhood**
(blueprint `lem:hasThicknessesBetween`): if `K` has affine thicknesses comparable to `t` with
constant `C₀`, and `L` is sandwiched between `K` and `N_r K` for a radius `r` at most the scale
of `K`, then `L` has affine thicknesses comparable to `t` with constant `2 * C₀`.

This is the construction-independent form of `ConvexSpaceBody.hasThicknesses_cthickening`: the
lower half of the profile comes from `K ≤ L` and the upper half from `L ≤ N_r K`, so no formula
for `L` is needed, only the two containments. It is the shape in which a consumer holding an
enlargement sandwich — such as the fields `Wb_le_W` and `W_le_cthickening` of
`Kakeya.ThinCase.ThinBall` — can read off the profile of the enlarged body. -/
theorem hasThicknesses_of_between {m : ℕ} {C₀ : NNReal} {t : Fin m → ℝ}
    (K L : ConvexSpaceBody E) (r : NNReal) (hr : (r : ℝ) ≤ K.scale)
    (hKL : K ≤ L) (hLK : L ≤ K.cthickening (r : ℝ))
    (ht : ∀ k, 0 ≤ t k) (hK : Kakeya.HasThicknesses K.carrier C₀ t) :
    Kakeya.HasThicknesses L.carrier (2 * C₀) t := by
  have hct := hasThicknesses_cthickening K r hr ht hK
  intro k
  constructor
  · -- lower bound
    have hKLset : (K : Set E) ⊆ (L : Set E) := by
      exact SetLike.coe_subset_coe.mpr hKL
    have hmono : Metric.thickness ℝ K.carrier ≤ Metric.thickness ℝ L.carrier := by
      exact Metric.thickness_monotone L.isCompact'.isBounded hKLset
    have hinv : ((2 * C₀ : NNReal) : ℝ)⁻¹ ≤ (C₀ : ℝ)⁻¹ := by
      have hcast : ((2 * C₀ : NNReal) : ℝ) = 2 * (C₀ : ℝ) := by norm_cast
      rw [hcast]
      by_cases hC : C₀ = 0
      · simp [hC]
      · have hcpos : 0 < (C₀ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.2 hC)
        have h2pos : 0 < 2 * (C₀ : ℝ) := mul_pos (by norm_num) hcpos
        exact (inv_le_inv₀ h2pos hcpos).2 (by linarith)
    calc
      ((2 * C₀ : NNReal) : ℝ)⁻¹ * t k ≤ (C₀ : ℝ)⁻¹ * t k := by
        exact mul_le_mul_of_nonneg_right hinv (ht k)
      _ ≤ Metric.thickness ℝ K.carrier k := (hK k).1
      _ ≤ Metric.thickness ℝ L.carrier k := hmono k
  · -- upper bound
    have hLKset : (L : Set E) ⊆ (K.cthickening (r : ℝ) : Set E) := by
      exact SetLike.coe_subset_coe.mpr hLK
    have hmono : Metric.thickness ℝ L.carrier ≤
        Metric.thickness ℝ (K.cthickening (r : ℝ)).carrier := by
      exact Metric.thickness_monotone (K.cthickening (r : ℝ)).isCompact'.isBounded hLKset
    calc
      Metric.thickness ℝ L.carrier k
          ≤ Metric.thickness ℝ (K.cthickening (r : ℝ)).carrier k := hmono k
      _ ≤ ((2 * C₀ : NNReal) : ℝ) * t k := (hct k).2

variable [MeasurableSpace E] [BorelSpace E]

/-- A closed `r`-neighborhood with `r` at most the scale inflates volume by at most the
dimensional comparison constant. -/
theorem volume_cthickening_le (K : ConvexSpaceBody E) (r : NNReal)
    (hr : (r : ℝ) ≤ K.scale) :
    volume (K.cthickening (r : ℝ)).carrier ≤
      (volume_comparison.C (finrank ℝ E) : ENNReal) * volume K.carrier :=
  volume_le_of_ethickness_le (ethickness_cthickening_le_two K r hr)

end Geometry

section Family

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E]
  {iota : Type*}

/-- `V` is a `C`-volume-controlled enlargement of `W` on `s` if each relevant body grows by
inclusion and its volume grows by at most the factor `C`.  This is the construction-independent
interface used by density stability results. -/
def IsVolumeControlledEnlargement (s : Finset iota)
    (W V : iota → ConvexSpaceBody E) (C : ENNReal) : Prop :=
  ∀ i ∈ s, W i ≤ V i ∧ volume (V i).carrier ≤ C * volume (W i).carrier

end Family

section Density

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {iota : Type*}

namespace IsVolumeControlledEnlargement

/-- A volume-controlled enlargement raises `Δ_max` by at most its volume factor. -/
theorem maxDensity_le {s : Finset iota} {W V : iota → ConvexSpaceBody E} {C : ENNReal}
    (h : IsVolumeControlledEnlargement s W V C) :
    Kakeya.maxDensity s V ≤ C * Kakeya.maxDensity s W := by
  rw [Kakeya.maxDensity_le_iff]
  intro K
  have hVK : Kakeya.densityIn s V K ≤ C * Kakeya.densityIn s W K := by
    rw [Kakeya.densityIn_le_iff s V K]
    calc
      ∑ i ∈ s with V i ≤ K, volume (V i).carrier
          ≤ ∑ i ∈ s with V i ≤ K, C * volume (W i).carrier := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            exact (h i (Finset.mem_filter.mp hi).1).2
      _ = C * ∑ i ∈ s with V i ≤ K, volume (W i).carrier := by
            rw [Finset.mul_sum]
      _ ≤ C * ∑ i ∈ s with W i ≤ K, volume (W i).carrier := by
            apply mul_le_mul_right
            apply Finset.sum_le_sum_of_subset
            intro i hi
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1, (h i hi.1).1.trans hi.2⟩
      _ = (C * Kakeya.densityIn s W K) * volume K.carrier := by
            rw [Kakeya.sum_volume_eq_densityIn_mul_volume s W K]
            ac_rfl
  exact hVK.trans (mul_le_mul_right (Kakeya.le_maxDensity s W K) C)

/-- The Katz--Tao property is stable under a volume-controlled enlargement. -/
theorem isKatzTao {s : Finset iota} {W V : iota → ConvexSpaceBody E} {C D : ENNReal}
    (h : IsVolumeControlledEnlargement s W V C) (hKT : IsKatzTao s W D) :
    IsKatzTao s V (C * D) :=
  h.maxDensity_le.trans (mul_le_mul_right hKT C)

end IsVolumeControlledEnlargement

end Density

section EuclideanFamily

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {iota : Type*}

/-- Small closed neighborhoods form a volume-controlled enlargement. -/
theorem isVolumeControlledEnlargement_cthickening (s : Finset iota)
    (W : iota → ConvexSpaceBody E) (r : iota → NNReal)
    (hr : ∀ i ∈ s, (r i : ℝ) ≤ (W i).scale) :
    IsVolumeControlledEnlargement s W (fun i ↦ (W i).cthickening (r i : ℝ))
      (volume_comparison.C (finrank ℝ E) : ENNReal) := by
  intro i hi
  exact ⟨self_le_cthickening _ _, volume_cthickening_le (W i) (r i) (hr i hi)⟩

end EuclideanFamily

end ConvexSpaceBody

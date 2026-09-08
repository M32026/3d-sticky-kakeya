/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Projection
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Thickness under a homothety

Write `h x t` for `AffineMap.homothety x t`, the homothety of centre `x` and ratio `t`.
This file records that a homothety scales displacements and distances by `t`, and deduces that
it scales `Metric.ethickness` (and hence `Metric.ethickness.scale`) by `|t|`.

These are the blueprint results `lem:homothety_vsub`, `lem:homothety_lipschitz`,
`lem:ethickness_homothety_le`, `lem:ethickness_homothety` and
`lem:ethickness_scale_homothety` of `GWZAdapted/thickness_homothety.tex`.
-/

@[expose] public section

namespace Kakeya

section Algebraic

variable {E S : Type*} [AddCommGroup E] [Module ℝ E] [AddTorsor E S]

/-- **A homothety scales displacements**: it sends `y -ᵥ z` to `t • (y -ᵥ z)`. This is a purely
affine identity, so no metric on `S` is needed. -/
theorem homothety_vsub_homothety (x : S) (t : ℝ) (y z : S) :
    AffineMap.homothety x t y -ᵥ AffineMap.homothety x t z = t • (y -ᵥ z) := by
  calc
    AffineMap.homothety x t y -ᵥ AffineMap.homothety x t z
        = (AffineMap.homothety x t).linear (y -ᵥ z) := by
      rw [AffineMap.linearMap_vsub]
    _ = (t • LinearMap.id) (y -ᵥ z) := by rw [AffineMap.homothety_linear]
    _ = t • (y -ᵥ z) := by simp

end Algebraic

section InnerProduct

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [AddTorsor E S]

/-- **A homothety scales the coordinates of a displacement.** Every coordinate of the
displacement `y -ᵥ z` in an orthonormal basis is multiplied by `t`. -/
theorem repr_homothety_vsub_homothety {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (x : S) (t : ℝ) (y z : S) (i : ι) :
    b.repr (AffineMap.homothety x t y -ᵥ AffineMap.homothety x t z) i
      = t * b.repr (y -ᵥ z) i := by
  calc
    b.repr (AffineMap.homothety x t y -ᵥ AffineMap.homothety x t z) i
        = b.repr (t • (y -ᵥ z)) i := by rw [homothety_vsub_homothety]
    _ = (t • b.repr (y -ᵥ z)) i := by rw [b.repr.map_smul]
    _ = t * b.repr (y -ᵥ z) i := by simp

end InnerProduct

section Distances

variable {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace S] [NormedAddTorsor E S]

/-- **A homothety is Lipschitz**, sharply: it multiplies every distance by `|t|`. -/
theorem dist_homothety_homothety (x : S) (t : ℝ) (y z : S) :
    dist (AffineMap.homothety x t y) (AffineMap.homothety x t z) = |t| * dist y z := by
  calc
    dist (AffineMap.homothety x t y) (AffineMap.homothety x t z)
        = ‖AffineMap.homothety x t y -ᵥ AffineMap.homothety x t z‖ := by
      rw [dist_eq_norm_vsub]
    _ = ‖t • (y -ᵥ z)‖ := by
      rw [homothety_vsub_homothety]
    _ = ‖t‖ * ‖(y -ᵥ z)‖ := by
      rw [norm_smul]
    _ = |t| * ‖(y -ᵥ z)‖ := by
      rw [Real.norm_eq_abs]
    _ = |t| * dist y z := by
      rw [dist_eq_norm_vsub]

/-- The homothety of centre `x` and ratio `t` is Lipschitz with constant `‖t‖₊`. -/
theorem lipschitzWith_homothety (x : S) (t : ℝ) :
    LipschitzWith ‖t‖₊ (AffineMap.homothety x t : S → S) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_homothety_homothety x t y z]
  have h : (|t| : ℝ) = (‖t‖₊ : ℝ) := by simp [Real.norm_eq_abs]
  rw [h]

end Distances

end Kakeya

namespace Metric

section Torsor

variable {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace S] [NormedAddTorsor E S]

/-- **Ethickness under a homothety, one-sided.** A homothety of ratio `t` does not increase the
`ethickness` by more than the factor `|t|`. -/
theorem ethickness_homothety_image_le (x : S) (t : ℝ) (X : Set S) (n : ℕ) :
    ethickness ℝ (AffineMap.homothety x t '' X) n ≤ ‖t‖₊ * ethickness ℝ X n := by
  have hlip : LipschitzWith ‖t‖₊ (AffineMap.homothety x t : S → S) :=
    Kakeya.lipschitzWith_homothety x t
  have h := hlip.ethickness_image_le X
  have hn := h n
  simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using hn

/-- **Ethickness under a homothety.** For a nonzero ratio the inequality of
`Metric.ethickness_homothety_image_le` is an equality. -/
theorem ethickness_homothety_image (x : S) {t : ℝ} (ht : t ≠ 0) (X : Set S) (n : ℕ) :
    ethickness ℝ (AffineMap.homothety x t '' X) n = ‖t‖₊ * ethickness ℝ X n := by
  -- For a nonzero ratio, `homothety x t⁻¹` inverts `homothety x t`.
  have h_comp : (AffineMap.homothety x t⁻¹).comp (AffineMap.homothety x t) = AffineMap.id ℝ S := by
    rw [← AffineMap.homothety_mul, inv_mul_cancel₀ ht, AffineMap.homothety_one]
  have h_func : (AffineMap.homothety x t⁻¹ : S → S) ∘ (AffineMap.homothety x t : S → S) = id := by
    simpa [AffineMap.coe_comp, AffineMap.coe_id] using
      congrArg (fun (f : S →ᵃ[ℝ] S) => (f : S → S)) h_comp
  have h_inv_image : AffineMap.homothety x t⁻¹ '' (AffineMap.homothety x t '' X) = X := by
    rw [← Set.image_comp, h_func, Set.image_id]
  have hle := ethickness_homothety_image_le x t X n
  have hle_inv : ethickness ℝ X n ≤ ‖t⁻¹‖₊ * ethickness ℝ (AffineMap.homothety x t '' X) n := by
    have htemp : ethickness ℝ (AffineMap.homothety x t⁻¹ '' (AffineMap.homothety x t '' X)) n
        ≤ ‖t⁻¹‖₊ * ethickness ℝ (AffineMap.homothety x t '' X) n :=
      ethickness_homothety_image_le x (t⁻¹) (AffineMap.homothety x t '' X) n
    rw [h_inv_image] at htemp
    exact htemp
  have h_norm_ne_zero : (‖t‖₊ : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (NNReal.coe_ne_zero.mp (norm_ne_zero_iff.mpr ht))
  have h_norm_ne_top : (‖t‖₊ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_nnnorm_inv : (‖t⁻¹‖₊ : ENNReal) = ((‖t‖₊ : ENNReal)⁻¹ : ENNReal) := by
    have h0 : ‖t‖₊ ≠ 0 := by
      have : (‖t‖₊ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr ht
      exact NNReal.coe_ne_zero.mp this
    simp [ENNReal.coe_inv h0, nnnorm_inv]
  have h_mul_nnnorm : (‖t‖₊ : ENNReal) * (‖t⁻¹‖₊ : ENNReal) = (1 : ENNReal) := by
    rw [h_nnnorm_inv]
    exact ENNReal.mul_inv_cancel h_norm_ne_zero h_norm_ne_top
  have h_ge : ‖t‖₊ * ethickness ℝ X n ≤ ethickness ℝ (AffineMap.homothety x t '' X) n := by
    have h1 : ‖t‖₊ * ethickness ℝ X n
        ≤ ‖t‖₊ * (‖t⁻¹‖₊ * ethickness ℝ (AffineMap.homothety x t '' X) n) := by
      gcongr
    have h2 : ‖t‖₊ * (‖t⁻¹‖₊ * ethickness ℝ (AffineMap.homothety x t '' X) n)
        = (‖t‖₊ * ‖t⁻¹‖₊) * ethickness ℝ (AffineMap.homothety x t '' X) n := by rw [mul_assoc]
    have h3 : (‖t‖₊ * ‖t⁻¹‖₊) * ethickness ℝ (AffineMap.homothety x t '' X) n
        = ethickness ℝ (AffineMap.homothety x t '' X) n := by
      rw [h_mul_nnnorm, one_mul]
    have h4 : ‖t‖₊ * (‖t⁻¹‖₊ * ethickness ℝ (AffineMap.homothety x t '' X) n)
        = ethickness ℝ (AffineMap.homothety x t '' X) n := by rw [h2, h3]
    exact h1.trans h4.le
  exact le_antisymm hle h_ge

/-- **The scale of a set under a homothety.** `Metric.ethickness.scale` is homogeneous of degree
one under homotheties of nonzero ratio. -/
theorem ethickness.scale_homothety_image [FiniteDimensional ℝ E] [Nontrivial E] (x : S) {t : ℝ}
    (ht : t ≠ 0) (X : Set S) :
    ethickness.scale ℝ (AffineMap.homothety x t '' X) = ‖t‖₊ * ethickness.scale ℝ X := by
  calc
    ethickness.scale ℝ (AffineMap.homothety x t '' X) =
        ethickness ℝ (AffineMap.homothety x t '' X) (Module.finrank ℝ E - 1) := by
      rw [ethickness.scale_eq]
    _ = ‖t‖₊ * ethickness ℝ X (Module.finrank ℝ E - 1) := by
      rw [ethickness_homothety_image x ht X (Module.finrank ℝ E - 1)]
    _ = ‖t‖₊ * ethickness.scale ℝ X := by
      rw [ethickness.scale_eq]

end Torsor

end Metric

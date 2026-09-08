/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRescale
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardBand
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyClosed
public import Kakeya.PartialEstimatesWindowed
public import Kakeya.Tube.CoverCountComparable

/-!
# The affine squeeze: is the cardinality band of Main Lemma 2 vacuous?

Adversarial file for steps.  See the module docstring at the bottom for the verdict.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

namespace Kakeya.ML2Squeeze

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The orthogonal complement of a unit vector -/

/-- The component of `z` orthogonal to `u` (meaningful when `‖u‖ = 1`). -/
noncomputable def perp (u z : E) : E := z - (inner ℝ u z : ℝ) • u

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_eq (u z : E) : perp u z = z - (inner ℝ u z : ℝ) • u := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_perp {u : E} (hu : ‖u‖ = 1) (z : E) : (inner ℝ u (perp u z) : ℝ) = 0 := by
  simp [perp, inner_sub_right, real_inner_smul_right, hu]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_add (u z w : E) : perp u (z + w) = perp u z + perp u w := by
  simp only [perp, inner_add_right, add_smul]
  abel

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_smul (u : E) (a : ℝ) (z : E) : perp u (a • z) = a • perp u z := by
  simp only [perp, real_inner_smul_right, smul_sub, smul_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_self {u : E} (hu : ‖u‖ = 1) : perp u u = 0 := by
  simp [perp, hu]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pythagoras for the decomposition `z = ⟪u,z⟫ u + perp u z`. -/
theorem norm_sq_eq_inner_sq_add_norm_perp_sq {u : E} (hu : ‖u‖ = 1) (z : E) :
    ‖z‖ ^ 2 = (inner ℝ u z : ℝ) ^ 2 + ‖perp u z‖ ^ 2 := by
  have hz : z = (inner ℝ u z : ℝ) • u + perp u z := by
    rw [perp]; abel
  have hinner : (inner ℝ ((inner ℝ u z : ℝ) • u) (perp u z) : ℝ) = 0 := by
    rw [real_inner_smul_left, inner_perp hu, mul_zero]
  calc ‖z‖ ^ 2 = ‖(inner ℝ u z : ℝ) • u + perp u z‖ ^ 2 := by rw [← hz]
    _ = ‖(inner ℝ u z : ℝ) • u‖ ^ 2 + 2 * (inner ℝ ((inner ℝ u z : ℝ) • u) (perp u z) : ℝ)
          + ‖perp u z‖ ^ 2 := norm_add_sq_real _ _
    _ = (inner ℝ u z : ℝ) ^ 2 + ‖perp u z‖ ^ 2 := by
        rw [hinner, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
        ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_perp_le {u : E} (hu : ‖u‖ = 1) (z : E) : ‖perp u z‖ ≤ ‖z‖ := by
  have h := norm_sq_eq_inner_sq_add_norm_perp_sq hu z
  nlinarith [norm_nonneg (perp u z), norm_nonneg z, sq_nonneg (inner ℝ u z : ℝ)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem abs_inner_le_norm_of_unit {u : E} (hu : ‖u‖ = 1) (z : E) :
    |(inner ℝ u z : ℝ)| ≤ ‖z‖ := by
  have := abs_real_inner_le_norm u z
  rwa [hu, one_mul] at this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖a • u + w‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2` when `‖u‖ = 1` and `w ⊥ u`. -/
theorem norm_smul_add_sq {u : E} (hu : ‖u‖ = 1) (a : ℝ) {w : E}
    (hw : (inner ℝ u w : ℝ) = 0) : ‖a • u + w‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2 := by
  have hinner : (inner ℝ (a • u) w : ℝ) = 0 := by rw [real_inner_smul_left, hw, mul_zero]
  calc ‖a • u + w‖ ^ 2
      = ‖a • u‖ ^ 2 + 2 * (inner ℝ (a • u) w : ℝ) + ‖w‖ ^ 2 := norm_add_sq_real _ _
    _ = a ^ 2 + ‖w‖ ^ 2 := by
        rw [hinner, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]; ring

end Geometry

/-! ## The squeeze map `A = ¼ · diag(σ, …, σ, 1)` -/

section Squeeze

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A dummy tube used only to name the frame direction `e` for `Tube.dilateAux`. -/
noncomputable def frame (σ : NNReal) {e : E} (he : ‖e‖ = 1) : Tube σ E :=
  Tube.mk' σ (x := (0 : E)) (y := e) (by rw [dist_eq_norm, zero_sub, norm_neg, he])

@[simp] theorem frame_x (σ : NNReal) {e : E} (he : ‖e‖ = 1) : (frame σ he).x = 0 := rfl
@[simp] theorem frame_y (σ : NNReal) {e : E} (he : ‖e‖ = 1) : (frame σ he).y = e := rfl

@[simp] theorem frame_direction (σ : NNReal) {e : E} (he : ‖e‖ = 1) :
    (frame σ he).direction = e := by
  show e - (0 : E) = e
  exact sub_zero e

/-- **The squeeze.**  In an orthonormal frame whose last axis is `e` this is
`¼ · diag(σ, …, σ, 1)`: the dilation by `¼` along `e` and by `σ/4` on `e^⊥`. -/
noncomputable def sqL (σ : NNReal) {e : E} (he : ‖e‖ = 1) : E →L[ℝ] E :=
  (1 / 4 : ℝ) • (frame σ he).dilateAux (σ : ℝ)

/-- The inverse map, `4 · diag(σ⁻¹, …, σ⁻¹, 1)`. -/
noncomputable def sqLinv (σ : NNReal) {e : E} (he : ‖e‖ = 1) : E →L[ℝ] E :=
  (4 : ℝ) • (frame σ he).dilateAux ((σ : ℝ)⁻¹)

theorem sqL_apply' (σ : NNReal) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqL σ he z = (1 / 4 : ℝ) • ((frame σ he).dilateAux (σ : ℝ) z) := rfl

/-- The normal form of the squeeze: `A z = ¼ (⟪e,z⟫ e + σ · perp e z)`. -/
theorem sqL_apply (σ : NNReal) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqL σ he z = (1 / 4 : ℝ) • ((inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z) := by
  rw [sqL_apply', Tube.dilateAux_apply, frame_direction, perp]
  congr 1
  module

theorem norm_sqL_le {σ : NNReal} (hσ1 : σ ≤ 1) {e : E} (he : ‖e‖ = 1) (z : E) :
    ‖sqL σ he z‖ ≤ (1 / 4 : ℝ) * ‖z‖ := by
  have hσ1' : (σ : ℝ) ≤ 1 := by exact_mod_cast hσ1
  have hσ0' : (0 : ℝ) ≤ (σ : ℝ) := σ.coe_nonneg
  have hw : (inner ℝ e ((σ : ℝ) • perp e z) : ℝ) = 0 := by
    rw [real_inner_smul_right, inner_perp he, mul_zero]
  have hsq : ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ ^ 2
      = (inner ℝ e z : ℝ) ^ 2 + ((σ : ℝ) * ‖perp e z‖) ^ 2 := by
    rw [norm_smul_add_sq he _ hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ0']
  have hle : ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hsq, norm_sq_eq_inner_sq_add_norm_perp_sq he z]
    have hp : (0 : ℝ) ≤ ‖perp e z‖ := norm_nonneg _
    have hexp : ((σ : ℝ) * ‖perp e z‖) ^ 2 = (σ : ℝ) ^ 2 * ‖perp e z‖ ^ 2 := by ring
    have hs2 : (σ : ℝ) ^ 2 ≤ 1 := by nlinarith
    have h1 : ((σ : ℝ) * ‖perp e z‖) ^ 2 ≤ ‖perp e z‖ ^ 2 := by
      rw [hexp]
      nlinarith [sq_nonneg ‖perp e z‖, mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg ‖perp e z‖)]
    linarith
  have hnn : (0 : ℝ) ≤ ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ := norm_nonneg _
  have hbase : ‖(inner ℝ e z : ℝ) • e + (σ : ℝ) • perp e z‖ ≤ ‖z‖ := by
    nlinarith [norm_nonneg z]
  rw [sqL_apply, norm_smul, Real.norm_eq_abs]
  have : |(1 / 4 : ℝ)| = 1 / 4 := by norm_num
  rw [this]
  linarith

/-- The transverse part of the squeeze is small: `A z` differs from `¼⟪e,z⟫e` by at most
`(σ/4)‖z‖`. -/
theorem norm_sqL_sub_le {σ : NNReal} {e : E} (he : ‖e‖ = 1) (z : E) :
    ‖sqL σ he z - (1 / 4 : ℝ) • ((inner ℝ e z : ℝ) • e)‖ ≤ ((σ : ℝ) / 4) * ‖z‖ := by
  have hσ0' : (0 : ℝ) ≤ (σ : ℝ) := σ.coe_nonneg
  have hrw : sqL σ he z - (1 / 4 : ℝ) • ((inner ℝ e z : ℝ) • e)
      = ((σ : ℝ) / 4) • perp e z := by
    rw [sqL_apply]
    module
  rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (σ:ℝ)/4)]
  have := norm_perp_le he z
  nlinarith [norm_nonneg (perp e z)]

theorem sqL_sqLinv {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqL σ he (sqLinv σ he z) = z := by
  have hσ' : (σ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hσ)
  show (1 / 4 : ℝ) • ((frame σ he).dilateAux (σ : ℝ)
      ((4 : ℝ) • (frame σ he).dilateAux ((σ : ℝ)⁻¹) z)) = z
  rw [map_smul, Tube.dilateAux_comp, mul_inv_cancel₀ hσ', Tube.dilateAux_one]
  simp

theorem sqLinv_sqL {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqLinv σ he (sqL σ he z) = z := by
  have hσ' : (σ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hσ)
  show (4 : ℝ) • ((frame σ he).dilateAux ((σ : ℝ)⁻¹)
      ((1 / 4 : ℝ) • (frame σ he).dilateAux (σ : ℝ) z)) = z
  rw [map_smul, Tube.dilateAux_comp, inv_mul_cancel₀ hσ', Tube.dilateAux_one]
  simp

/-- The squeeze as a linear equivalence. -/
noncomputable def sqLE {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofLinear (sqL σ he).toLinearMap (sqLinv σ he).toLinearMap
    (by ext z; exact sqL_sqLinv hσ he z) (by ext z; exact sqLinv_sqL hσ he z)

/-- The squeeze as an affine equivalence, which is what the transport laws consume. -/
noncomputable def sqA {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) : E ≃ᵃ[ℝ] E :=
  (sqLE hσ he).toAffineEquiv

@[simp] theorem sqA_apply {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    sqA hσ he z = sqL σ he z := rfl

theorem sqA_coe {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) :
    ⇑(sqA hσ he) = ⇑(sqL σ he) := rfl

end Squeeze

/-! ## The volume factor of the squeeze -/

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
theorem normalization_frame (σ : NNReal) {e : E} (he : ‖e‖ = 1) (z : E) :
    (frame σ he).normalization z = (frame σ he).dilateAux ((σ : ℝ)⁻¹) z := by
  rw [Tube.normalization_apply, Tube.dilateAux_apply, frame_direction, frame_x, sub_zero,
    zero_add]
  module

omit [Nontrivial E] in
theorem normalization_frame_dilate {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (z : E) :
    (frame σ he).normalization ((frame σ he).dilateAux (σ : ℝ) z) = z := by
  have hσ' : (σ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hσ)
  rw [normalization_frame, Tube.dilateAux_comp, inv_mul_cancel₀ hσ', Tube.dilateAux_one]
  simp

/-- **The anisotropic dilation multiplies every volume by `σ ^ (n-1)`.** -/
theorem volume_dilate_image {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (B : Set E) :
    volume ((frame σ he).dilateAux (σ : ℝ) '' B)
      = (σ : ENNReal) ^ (Module.finrank ℝ E - 1) * volume B := by
  set k := Module.finrank ℝ E - 1 with hk
  have hne : (σ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_pos.mpr hσ).ne'
  have htop : (σ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have himg : (frame σ he).normalization '' ((frame σ he).dilateAux (σ : ℝ) '' B) = B := by
    rw [Set.image_image]
    have : ∀ x ∈ B, (frame σ he).normalization ((frame σ he).dilateAux (σ : ℝ) x) = x :=
      fun x _ => normalization_frame_dilate hσ he x
    rw [Set.image_congr this]
    exact Set.image_id' B
  have hvol := Tube.volume_image_normalization hσ (frame σ he)
    ((frame σ he).dilateAux (σ : ℝ) '' B)
  rw [himg] at hvol
  have hcancel : (σ : ENNReal) ^ k * ((σ : ENNReal)⁻¹) ^ k = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hne htop, one_pow]
  calc volume ((frame σ he).dilateAux (σ : ℝ) '' B)
      = 1 * volume ((frame σ he).dilateAux (σ : ℝ) '' B) := (one_mul _).symm
    _ = ((σ : ENNReal) ^ k * ((σ : ENNReal)⁻¹) ^ k)
          * volume ((frame σ he).dilateAux (σ : ℝ) '' B) := by rw [hcancel]
    _ = (σ : ENNReal) ^ k * (((σ : ENNReal)⁻¹) ^ k
          * volume ((frame σ he).dilateAux (σ : ℝ) '' B)) := by ring
    _ = (σ : ENNReal) ^ k * volume B := by rw [← hvol]

/-- **The squeeze multiplies every volume by `4^{-n} σ^{n-1}`.** -/
theorem volume_sqL_image {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (B : Set E) :
    volume (sqL σ he '' B)
      = ENNReal.ofReal |(1 / 4 : ℝ) ^ Module.finrank ℝ E|
        * ((σ : ENNReal) ^ (Module.finrank ℝ E - 1) * volume B) := by
  have himg : (sqL σ he) '' B = (1 / 4 : ℝ) • (((frame σ he).dilateAux (σ : ℝ)) '' B : Set E) := by
    rw [← Set.image_smul, Set.image_image]
    rfl
  rw [himg, Measure.addHaar_smul, volume_dilate_image hσ he]

end Volume

/-! ## The squeezed tube is contained in an honest `δ`-tube -/

section Containment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- Every point of the core segment of a tube is `midpoint + t • direction`, `|t| ≤ 1/2`. -/
theorem exists_param_of_mem_segment {ρ : NNReal} (S : Tube ρ E) {c : E}
    (hc : c ∈ segment ℝ S.x S.y) :
    ∃ t : ℝ, |t| ≤ 1 / 2 ∧ c = S.midpoint + t • S.direction := by
  obtain ⟨α, β, hα, hβ, hab, hcc⟩ := hc
  refine ⟨(β - α) / 2, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · rw [← hcc]
    show α • S.x + β • S.y
        = (1 / 2 : ℝ) • (S.x + S.y) + ((β - α) / 2) • (S.y - S.x)
    have hα' : α = 1 - β := by linarith
    rw [hα']
    module

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem sqL_injective {σ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) :
    Function.Injective (sqL σ he) := by
  intro z w h
  have := congrArg (sqLinv σ he) h
  rwa [sqLinv_sqL hσ he, sqLinv_sqL hσ he] at this

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem sqL_x_ne_sqL_y {σ ρ : NNReal} (hσ : 0 < σ) {e : E} (he : ‖e‖ = 1) (S : Tube ρ E) :
    sqL σ he S.x ≠ sqL σ he S.y := fun h => by
  have hxy : S.x ≠ S.y := by
    intro hxy
    have := S.dist_eq_one
    rw [hxy, dist_self] at this
    exact zero_ne_one this
  exact hxy (sqL_injective hσ he h)

variable {σ ρ δ : NNReal} {e : E}

/-- **The squeezed tube.**  The honest `δ`-tube that receives `A '' S.carrier`. -/
noncomputable def sqTube (hσ : 0 < σ) (he : ‖e‖ = 1) (δ : NNReal) (S : Tube ρ E) : Tube δ E :=
  Tube.centredExtension δ (sqL_x_ne_sqL_y hσ he S)

omit [Nontrivial E] in
theorem sqTube_direction (hσ : 0 < σ) (he : ‖e‖ = 1) (δ : NNReal) (S : Tube ρ E) :
    (sqTube hσ he δ S).direction
      = ‖sqL σ he S.y - sqL σ he S.x‖⁻¹ • (sqL σ he S.y - sqL σ he S.x) :=
  Tube.direction_centredExtension _

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem sqTube_midpoint (hσ : 0 < σ) (he : ‖e‖ = 1) (δ : NNReal) (S : Tube ρ E) :
    (sqTube hσ he δ S).midpoint = sqL σ he S.midpoint := by
  set p := sqL σ he S.x
  set q := sqL σ he S.y
  set g : E := ‖q - p‖⁻¹ • (q - p) with hg
  have hx : (sqTube hσ he δ S).x = _root_.midpoint ℝ p q - (1 / 2 : ℝ) • g := rfl
  have hy : (sqTube hσ he δ S).y = _root_.midpoint ℝ p q + (1 / 2 : ℝ) • g := rfl
  have hmap : sqL σ he S.midpoint = (1 / 2 : ℝ) • (p + q) := by
    show sqL σ he ((1 / 2 : ℝ) • (S.x + S.y)) = _
    rw [map_smul, map_add]
  show (1 / 2 : ℝ) • ((sqTube hσ he δ S).x + (sqTube hσ he δ S).y) = _
  rw [hx, hy, hmap, midpoint_eq_smul_add, invOf_eq_inv]
  module

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem norm_perp_unit_le {u : E} (hu : ‖u‖ = 1) (v : E) : ‖perp u v‖ ≤ ‖u - v‖ := by
  have hsplit : perp u v = perp u (v - u) := by
    have : v = (v - u) + u := by abel
    rw [this, perp_add, perp_self hu, add_zero, add_sub_cancel_right]
  rw [hsplit]
  exact (norm_perp_le hu _).trans_eq (norm_sub_rev v u)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The transverse displacement of the squeeze.**  If the axis `u` is within `4σ` of the frame
direction `e`, then `A w` is within `(5/4)σr` of the line `ℝ ∙ u` whenever `‖w‖ ≤ r`. -/
theorem norm_perp_sqL_le (hσ0 : 0 < σ) (he : ‖e‖ = 1) {u : E} (hu : ‖u‖ = 1)
    (hue : ‖u - e‖ ≤ 4 * (σ : ℝ)) {w : E} {r : ℝ} (hw : ‖w‖ ≤ r) :
    ‖perp u (sqL σ he w)‖ ≤ (5 / 4) * ((σ : ℝ) * r) := by
  have hσ0' : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr hσ0
  have hr : (0 : ℝ) ≤ r := le_trans (norm_nonneg w) hw
  have hexp : perp u (sqL σ he w)
      = (1 / 4 : ℝ) • ((inner ℝ e w : ℝ) • perp u e + (σ : ℝ) • perp u (perp e w)) := by
    rw [sqL_apply, perp_smul, perp_add, perp_smul, perp_smul]
  have h1 : ‖perp u e‖ ≤ 4 * (σ : ℝ) := (norm_perp_unit_le hu e).trans hue
  have h2 : ‖perp u (perp e w)‖ ≤ r :=
    ((norm_perp_le hu _).trans (norm_perp_le he w)).trans hw
  have h3 : |(inner ℝ e w : ℝ)| ≤ r := (abs_inner_le_norm_of_unit he w).trans hw
  have hb : ‖(inner ℝ e w : ℝ) • perp u e + (σ : ℝ) • perp u (perp e w)‖
      ≤ 5 * ((σ : ℝ) * r) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hσ0'.le]
    have hA : |(inner ℝ e w : ℝ)| * ‖perp u e‖ ≤ r * (4 * (σ : ℝ)) :=
      mul_le_mul h3 h1 (norm_nonneg _) hr
    have hB : (σ : ℝ) * ‖perp u (perp e w)‖ ≤ (σ : ℝ) * r :=
      mul_le_mul_of_nonneg_left h2 hσ0'.le
    nlinarith
  rw [hexp, norm_smul, Real.norm_eq_abs, show |(1 / 4 : ℝ)| = 1 / 4 by norm_num]
  linarith

omit [Nontrivial E] in
set_option maxHeartbeats 1000000 in
/-- **The geometric core.**  Inside a cap of directions around `e`, the squeeze `A` maps a
`ρ`-tube into an honest `δ`-tube, provided `2σρ ≤ δ`. -/
theorem sqL_image_subset_sqTube (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (he : ‖e‖ = 1) (S : Tube ρ E) (hcap : (1 : ℝ) / 2 ≤ (inner ℝ e S.direction : ℝ))
    (hδ : 2 * σ * ρ ≤ δ) :
    (sqL σ he) '' S.carrier ⊆ (sqTube hσ0 he δ S).carrier := by
  have hσ0' : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr hσ0
  have hσ1' : ((σ : ℝ)) ≤ 1 := by exact_mod_cast hσ1
  have hρ0' : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hρ1' : ((ρ : ℝ)) ≤ 1 := by exact_mod_cast hρ1
  have hδ' : 2 * (σ : ℝ) * (ρ : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  set d : E := S.direction with hd
  set a : ℝ := (inner ℝ e d : ℝ) with ha_def
  set P : E := perp e d with hP_def
  set n : ℝ := ‖a • e + (σ : ℝ) • P‖ with hn_def
  set T' : Tube δ E := sqTube hσ0 he δ S with hT'
  have hd1 : ‖d‖ = 1 := S.norm_direction
  have hP1 : ‖P‖ ≤ 1 := by
    rw [hP_def]
    exact (norm_perp_le he d).trans_eq hd1
  have hP0 : (0 : ℝ) ≤ ‖P‖ := norm_nonneg _
  have ha1 : a ≤ 1 := by
    have h := abs_inner_le_norm_of_unit he d
    rw [hd1] at h
    exact le_trans (le_abs_self a) h
  have hw0 : (inner ℝ e ((σ : ℝ) • P) : ℝ) = 0 := by
    rw [real_inner_smul_right, hP_def, inner_perp he, mul_zero]
  have hn2 : n ^ 2 = a ^ 2 + ((σ : ℝ) * ‖P‖) ^ 2 := by
    rw [hn_def, norm_smul_add_sq he a hw0, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hσ0'.le]
  have hn0' : (0 : ℝ) ≤ n := norm_nonneg _
  have hna : a ≤ n := by nlinarith [sq_nonneg ((σ : ℝ) * ‖P‖)]
  have hnu : n ≤ a + (σ : ℝ) * ‖P‖ := by nlinarith [mul_nonneg hσ0'.le hP0]
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by linarith) hna
  have hnne : n ≠ 0 := ne_of_gt hn0
  have hdsq : (1 : ℝ) = a ^ 2 + ‖P‖ ^ 2 := by
    rw [hP_def, ha_def, ← norm_sq_eq_inner_sq_add_norm_perp_sq he d, hd1, one_pow]
  have hs2 : (σ : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hnsq1 : n ^ 2 ≤ 1 := by
    have hexp : ((σ : ℝ) * ‖P‖) ^ 2 = (σ : ℝ) ^ 2 * ‖P‖ ^ 2 := by ring
    nlinarith [sq_nonneg ‖P‖, mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg ‖P‖)]
  have hnle1 : n ≤ 1 := by nlinarith
  -- the image of the core direction
  have hAd : sqL σ he d = (1 / 4 : ℝ) • (a • e + (σ : ℝ) • P) := sqL_apply σ he d
  have hqp : sqL σ he S.y - sqL σ he S.x = sqL σ he d := by
    rw [hd]
    show _ = sqL σ he (S.y - S.x)
    rw [map_sub]
  have hAdnorm : ‖sqL σ he d‖ = n / 4 := by
    rw [hAd, norm_smul, Real.norm_eq_abs, show |(1 / 4 : ℝ)| = 1 / 4 by norm_num, ← hn_def]
    ring
  have hAdne : ‖sqL σ he d‖ ≠ 0 := by rw [hAdnorm]; positivity
  -- the axis of the image tube
  have hdirT : T'.direction = ‖sqL σ he d‖⁻¹ • sqL σ he d := by
    rw [hT', sqTube_direction, hqp]
  have hquart : ((n : ℝ) / 4)⁻¹ * (1 / 4 : ℝ) = (n : ℝ)⁻¹ := by
    rw [inv_div, div_mul_eq_mul_div]
    norm_num
  have hu : T'.direction = (n : ℝ)⁻¹ • (a • e + (σ : ℝ) • P) := by
    rw [hdirT, hAdnorm, hAd, smul_smul, hquart]
  have hu1 : ‖T'.direction‖ = 1 := T'.norm_direction
  have hue : ‖T'.direction - e‖ ≤ 4 * (σ : ℝ) := by
    have hstep : (n : ℝ)⁻¹ • (a • e + (σ : ℝ) • P) - e
        = (n : ℝ)⁻¹ • ((a - n) • e + (σ : ℝ) • P) := by
      match_scalars <;> field_simp [hnne]
    have hinv0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hn0)
    have h3 : (n : ℝ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hn0 (by norm_num : (0:ℝ) < 2)]
      linarith
    have h1 : ‖(a - n) • e + (σ : ℝ) • P‖ ≤ |a - n| + (σ : ℝ) * ‖P‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he, mul_one,
        abs_of_nonneg hσ0'.le]
    have h2 : |a - n| ≤ (σ : ℝ) * ‖P‖ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ n - a)]
      linarith
    rw [hu, hstep, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv0]
    have hbound : ‖(a - n) • e + (σ : ℝ) • P‖ ≤ 2 * ((σ : ℝ) * ‖P‖) := by linarith
    have hnn : (0 : ℝ) ≤ ‖(a - n) • e + (σ : ℝ) • P‖ := norm_nonneg _
    nlinarith [mul_nonneg hσ0'.le hP0]
  have hAd_u : sqL σ he d = ‖sqL σ he d‖ • T'.direction := by
    rw [hdirT, smul_smul, mul_inv_cancel₀ hAdne, one_smul]
  have hmid : T'.midpoint = sqL σ he S.midpoint := by
    rw [hT']
    exact sqTube_midpoint hσ0 he δ S
  clear_value T'
  -- the containment
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [S.carrier_eq] at hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨t, ht, rfl⟩ := exists_param_of_mem_segment S hc
  set w : E := z - (S.midpoint + t • d) with hw_def
  have hwnorm : ‖w‖ ≤ (ρ : ℝ) := by
    rw [hw_def, ← dist_eq_norm]
    exact Metric.mem_closedBall.mp hzc
  have hzw : z = (S.midpoint + t • d) + w := by rw [hw_def]; abel
  clear_value w
  set τ : ℝ := t * ‖sqL σ he d‖ + (inner ℝ T'.direction (sqL σ he w) : ℝ) with hτ
  have hlin : sqL σ he z = sqL σ he (S.midpoint + t • d) + sqL σ he w := by
    conv_lhs => rw [hzw]
    exact map_add (sqL σ he) _ _
  have hlinmid : sqL σ he (S.midpoint + t • d)
      = sqL σ he S.midpoint + t • sqL σ he d := by
    simp only [Tube.midpoint, map_add, map_smul]
  have hcore : sqL σ he (S.midpoint + t • d)
      = T'.midpoint + (t * ‖sqL σ he d‖) • T'.direction := by
    rw [hlinmid, hmid, mul_smul, ← hAd_u]
  have hAz : sqL σ he z
      = (T'.midpoint + τ • T'.direction) + perp T'.direction (sqL σ he w) := by
    rw [hlin, hcore, hτ, perp]
    module
  -- the scalar bounds on `τ`
  have hb1 : |t * ‖sqL σ he d‖| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg (norm_nonneg _), hAdnorm]
    have hmul : |t| * (n / 4) ≤ (1 / 2) * (1 / 4) :=
      mul_le_mul ht (by linarith) (by positivity) (by norm_num)
    linarith
  have hAwsmall : ‖sqL σ he w‖ ≤ 1 / 4 := by
    have hb := norm_sqL_le hσ1 he w
    linarith
  have hb2 : |(inner ℝ T'.direction (sqL σ he w) : ℝ)| ≤ 1 / 4 :=
    le_trans (abs_inner_le_norm_of_unit hu1 (sqL σ he w)) hAwsmall
  have hτabs : |τ| ≤ 1 / 2 := by
    have h1 := abs_le.mp hb1
    have h2 := abs_le.mp hb2
    rw [hτ, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [T'.carrier_eq]
  refine Set.mem_iUnion₂.mpr ⟨T'.midpoint + τ • T'.direction, ?_, ?_⟩
  · exact T'.midpoint_add_smul_direction_mem_segment (by linarith [abs_le.mp hτabs])
      (abs_le.mp hτabs).2
  · rw [Metric.mem_closedBall, dist_eq_norm, hAz]
    have hcancel : (T'.midpoint + τ • T'.direction) + perp T'.direction (sqL σ he w)
        - (T'.midpoint + τ • T'.direction) = perp T'.direction (sqL σ he w) := by abel
    rw [hcancel]
    have hfin := norm_perp_sqL_le hσ0 he hu1 hue hwnorm
    have hcmp : (5 / 4) * ((σ : ℝ) * (ρ : ℝ)) ≤ 2 * (σ : ℝ) * (ρ : ℝ) := by
      nlinarith [mul_nonneg hσ0'.le hρ0']
    linarith

/-! ## The squeezed tube lies in `B₁`, and its volume is comparable -/

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem tube_x_mem_carrier (S : Tube ρ E) : S.x ∈ S.carrier := by
  rw [S.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨S.x, left_mem_segment ℝ S.x S.y,
    Metric.mem_closedBall_self ρ.coe_nonneg⟩

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem tube_y_mem_carrier (S : Tube ρ E) : S.y ∈ S.carrier := by
  rw [S.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨S.y, right_mem_segment ℝ S.x S.y,
    Metric.mem_closedBall_self ρ.coe_nonneg⟩

omit [Nontrivial E] in
theorem sqTube_subset_closedBall (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (he : ‖e‖ = 1) (S : Tube ρ E)
    (hS : S.carrier ⊆ Metric.closedBall (0 : E) 1) (hδ4 : (δ : ℝ) ≤ 1 / 4) :
    (sqTube hσ0 he δ S).carrier ⊆ Metric.closedBall (0 : E) 1 := by
  refine Tube.centredExtension_subset_closedBall _ ?_ ?_ hδ4
  · rw [dist_zero_right]
    have h1 : ‖S.x‖ ≤ 1 := by
      simpa [dist_zero_right] using hS (tube_x_mem_carrier S)
    have h2 := norm_sqL_le hσ1 he S.x
    linarith
  · rw [dist_zero_right]
    have h1 : ‖S.y‖ ≤ 1 := by
      simpa [dist_zero_right] using hS (tube_y_mem_carrier S)
    have h2 := norm_sqL_le hσ1 he S.y
    linarith

/-- The volume loss of re-presenting the squeezed tube as an honest `δ`-tube.  It is an
absolute constant: it depends on the ambient dimension and on nothing else. -/
noncomputable def fatLoss : NNReal :=
  1 + 256 * Tube.volume_le.C 3 / Tube.le_volume.c 3

theorem one_le_fatLoss : 1 ≤ fatLoss := le_self_add

theorem fatLoss_ne_zero : fatLoss ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_fatLoss)

theorem four_mul_volume_le_C_le : 4 * Tube.volume_le.C 3
    ≤ fatLoss * ((1 / 64 : NNReal) * Tube.le_volume.c 3) := by
  have hc : Tube.le_volume.c 3 ≠ 0 := ne_of_gt (Tube.le_volume.c_pos 3)
  have hkey : (256 * Tube.volume_le.C 3 / Tube.le_volume.c 3)
      * ((1 / 64 : NNReal) * Tube.le_volume.c 3) = 4 * Tube.volume_le.C 3 := by
    field_simp
    ring
  calc 4 * Tube.volume_le.C 3
      = (256 * Tube.volume_le.C 3 / Tube.le_volume.c 3)
          * ((1 / 64 : NNReal) * Tube.le_volume.c 3) := hkey.symm
    _ ≤ fatLoss * ((1 / 64 : NNReal) * Tube.le_volume.c 3) := by
        gcongr
        exact le_add_self

/-- **The re-presentation costs one absolute constant in volume.** -/
theorem sqTube_volume_le (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (he : ‖e‖ = 1)
    (S : Tube ρ E) (hδ1 : 2 * σ * ρ ≤ 1) :
    volume (sqTube hσ0 he (2 * σ * ρ) S).carrier
      ≤ (fatLoss : ENNReal) * volume ((sqL σ he) '' S.carrier) := by
  have hup : volume (sqTube hσ0 he (2 * σ * ρ) S).carrier
      ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal) * ((2 * σ * ρ : NNReal) : ENNReal) ^ 2 := by
    have h := Tube.volume_le hδ1 (sqTube hσ0 he (2 * σ * ρ) S)
    rw [hn] at h
    simpa using h
  have hlow0 : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((ρ : NNReal) : ENNReal) ^ 2
      ≤ volume S.carrier := by
    have h := Tube.le_volume (E := E) S
    rw [hn] at h
    simpa using h
  have hvol : volume ((sqL σ he) '' S.carrier)
      = ENNReal.ofReal |(1 / 4 : ℝ) ^ 3| * (((σ : NNReal) : ENNReal) ^ 2 * volume S.carrier) := by
    have h := volume_sqL_image hσ0 he S.carrier
    rw [hn] at h
    simpa using h
  have hofReal : ENNReal.ofReal |(1 / 4 : ℝ) ^ 3| = ((1 / 64 : NNReal) : ENNReal) := by
    rw [show |(1 / 4 : ℝ) ^ 3| = ((1 / 64 : NNReal) : ℝ) by norm_num]
    exact ENNReal.ofReal_coe_nnreal
  rw [hvol, hofReal]
  have hsq : ((2 * σ * ρ : NNReal) : ENNReal) ^ 2
      = ((4 : NNReal) : ENNReal)
        * (((σ : NNReal) : ENNReal) ^ 2 * ((ρ : NNReal) : ENNReal) ^ 2) := by
    push_cast
    ring
  refine le_trans hup ?_
  rw [hsq]
  have hstep1 : ((1 / 64 : NNReal) : ENNReal)
        * (((σ : NNReal) : ENNReal) ^ 2 * (((Tube.le_volume.c 3 : NNReal) : ENNReal)
          * ((ρ : NNReal) : ENNReal) ^ 2))
      ≤ ((1 / 64 : NNReal) : ENNReal)
        * (((σ : NNReal) : ENNReal) ^ 2 * volume S.carrier) := by
    gcongr
  refine le_trans ?_ (mul_le_mul_right hstep1 ((fatLoss : NNReal) : ENNReal))
  have hconst : ((Tube.volume_le.C 3 : NNReal) : ENNReal) * ((4 : NNReal) : ENNReal)
      ≤ ((fatLoss : NNReal) : ENNReal)
        * (((1 / 64 : NNReal) : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal)) := by
    rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    exact_mod_cast (by rw [mul_comm]; exact four_mul_volume_le_C_le)
  calc ((Tube.volume_le.C 3 : NNReal) : ENNReal)
        * (((4 : NNReal) : ENNReal) * ((((σ : NNReal) : ENNReal) ^ 2)
            * ((ρ : NNReal) : ENNReal) ^ 2))
      = (((Tube.volume_le.C 3 : NNReal) : ENNReal) * ((4 : NNReal) : ENNReal))
          * (((σ : NNReal) : ENNReal) ^ 2 * ((ρ : NNReal) : ENNReal) ^ 2) := by ring
    _ ≤ (((fatLoss : NNReal) : ENNReal)
          * (((1 / 64 : NNReal) : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal)))
          * (((σ : NNReal) : ENNReal) ^ 2 * ((ρ : NNReal) : ENNReal) ^ 2) := by
        gcongr
    _ = ((fatLoss : NNReal) : ENNReal) * (((1 / 64 : NNReal) : ENNReal)
          * (((σ : NNReal) : ENNReal) ^ 2 * (((Tube.le_volume.c 3 : NNReal) : ENNReal)
            * ((ρ : NNReal) : ENNReal) ^ 2))) := by ring

/-! ## The squeezed family as honest `δ`-tubes -/

/-- **The squeezed shaded tube.**  Carrier the honest outer `δ`-tube, shade the squeezed shade
intersected with that carrier, so that the definition is total. -/
noncomputable def sqShadedTube (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : NNReal)
    (S : ShadedTube ρ E) : ShadedTube δ E where
  toTube := sqTube hσ0 he δ S.toTube
  shade := ((sqA hσ0 he) '' S.shade) ∩ (sqTube hσ0 he δ S.toTube).carrier
  measurableSet_shade :=
    (Kakeya.measurableSet_affineEquiv_image (sqA hσ0 he) S.measurableSet_shade).inter
      (sqTube hσ0 he δ S.toTube).isCompact'.isClosed.measurableSet
  shade_subset := Set.inter_subset_right

omit [Nontrivial E] in
@[simp] theorem sqShadedTube_carrier (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : NNReal)
    (S : ShadedTube ρ E) :
    (sqShadedTube hσ0 he δ S).carrier = (sqTube hσ0 he δ S.toTube).carrier := rfl

omit [Nontrivial E] in
@[simp] theorem sqShadedTube_shade (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : NNReal)
    (S : ShadedTube ρ E) :
    (sqShadedTube hσ0 he δ S).shade
      = ((sqA hσ0 he) '' S.shade) ∩ (sqTube hσ0 he δ S.toTube).carrier := rfl

omit [Nontrivial E] in
theorem sqShadedTube_shade_eq (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (S : ShadedTube ρ E) (hcap : (1 : ℝ) / 2 ≤ (inner ℝ e S.direction : ℝ))
    (hδ : 2 * σ * ρ ≤ δ) :
    (sqShadedTube hσ0 he δ S).shade = (sqA hσ0 he) '' S.shade := by
  refine Set.inter_eq_self_of_subset_left ?_
  refine (Set.image_mono S.shade_subset).trans ?_
  exact sqL_image_subset_sqTube hσ0 hσ1 hρ1 he S.toTube hcap hδ

/-- The squeezed family. -/
noncomputable def sqFamily {ι : Type*} (hσ0 : 0 < σ) (he : ‖e‖ = 1) (δ : NNReal)
    (T : ι → ShadedTube ρ E) : ι → ShadedTube δ E :=
  fun i => sqShadedTube hσ0 he δ (T i)

section Family

variable {ι : Type*} {s : Finset ι} {T : ι → ShadedTube ρ E}

omit [Nontrivial E] in
theorem sqFamily_shade_eq (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    ∀ i ∈ s, (sqFamily hσ0 he δ T i).toShadedBody.shade
      = (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).shade := fun i hi =>
  sqShadedTube_shade_eq hσ0 hσ1 hρ1 he (T i) (hcap i hi) hδ

omit [Nontrivial E] in
theorem sqFamily_le (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    ∀ i ∈ s, (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).toConvexSpaceBody
      ≤ (sqFamily hσ0 he δ T i).toConvexSpaceBody := by
  intro i hi
  change (sqA hσ0 he) '' (T i).carrier ⊆ (sqTube hσ0 he δ (T i).toTube).carrier
  exact sqL_image_subset_sqTube hσ0 hσ1 hρ1 he (T i).toTube (hcap i hi) hδ

theorem sqFamily_volume_le (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (he : ‖e‖ = 1)
    (hδ1 : 2 * σ * ρ ≤ 1) :
    ∀ i ∈ s, volume (sqFamily hσ0 he (2 * σ * ρ) T i).carrier
      ≤ (fatLoss : ENNReal)
        * volume (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).carrier := fun i _ =>
  sqTube_volume_le hn hσ0 he (T i).toTube hδ1

omit [Nontrivial E] in
theorem sqFamily_carrier_subset_closedBall (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (he : ‖e‖ = 1)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) (hδ4 : (δ : ℝ) ≤ 1 / 4) :
    ∀ i ∈ s, (sqFamily hσ0 he δ T i).carrier ⊆ Metric.closedBall (0 : E) 1 := fun i hi =>
  sqTube_subset_closedBall hσ0 hσ1 he (T i).toTube (hball i hi) hδ4

/-- **`Δ_max` of the squeezed family costs one absolute constant.** -/
theorem sqFamily_maxDensity_le (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ1 : 2 * σ * ρ ≤ 1) :
    Kakeya.maxDensity s (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toConvexSpaceBody)
      ≤ (fatLoss : ENNReal) * Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) := by
  have h := Kakeya.maxDensity_le_of_comparable (E := E) one_le_fatLoss s
    (fun i => (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T i).toConvexSpaceBody)
    (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toConvexSpaceBody)
    (sqFamily_le hσ0 hσ1 hρ1 he hcap le_rfl)
    (sqFamily_volume_le hn hσ0 he hδ1)
  rwa [Kakeya.ML2Reduction.spineFamily_maxDensity] at h

/-- **Fullness of the squeezed family costs one absolute constant.** -/
theorem sqFamily_le_fullness (hn : Module.finrank ℝ E = 3) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ1 : 2 * σ * ρ ≤ 1) :
    fatLoss⁻¹ * ShadedBody.fullness s (fun i => (T i).toShadedBody)
      ≤ ShadedBody.fullness s
          (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toShadedBody) := by
  have h := Tube.le_fullness_of_volume_le (E := E) one_le_fatLoss s
    (Kakeya.ML2Reduction.spineFamily (sqA hσ0 he) T)
    (fun i => (sqFamily hσ0 he (2 * σ * ρ) T i).toShadedBody)
    (sqFamily_shade_eq hσ0 hσ1 hρ1 he hcap le_rfl)
    (sqFamily_volume_le hn hσ0 he hδ1)
  rwa [Kakeya.ML2Reduction.spineFamily_fullness] at h

omit [Nontrivial E] in
/-- The shade mass of the squeezed family is the Jacobian times the original. -/
theorem sqFamily_sum_shade (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    ∑ i ∈ s, volume (sqFamily hσ0 he δ T i).shade
      = Kakeya.affineJacobian (sqA hσ0 he) * ∑ i ∈ s, volume (T i).shade := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show (sqFamily hσ0 he δ T i).shade = (sqA hσ0 he) '' (T i).shade from
    sqShadedTube_shade_eq hσ0 hσ1 hρ1 he (T i) (hcap i hi) hδ]
  exact Kakeya.volume_image_affineEquiv _ _

omit [Nontrivial E] in
theorem sqFamily_iUnion_shade (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (he : ‖e‖ = 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ (inner ℝ e (T i).direction : ℝ)) (hδ : 2 * σ * ρ ≤ δ) :
    volume (⋃ i ∈ s, (sqFamily hσ0 he δ T i).shade)
      = Kakeya.affineJacobian (sqA hσ0 he) * volume (⋃ i ∈ s, (T i).shade) := by
  have himg : (⋃ i ∈ s, (sqFamily hσ0 he δ T i).shade)
      = (sqA hσ0 he) '' (⋃ i ∈ s, (T i).shade) := by
    rw [Set.image_iUnion₂]
    refine Set.iUnion₂_congr fun i hi => ?_
    exact sqShadedTube_shade_eq hσ0 hσ1 hρ1 he (T i) (hcap i hi) hδ
  rw [himg]
  exact Kakeya.volume_image_affineEquiv _ _

end Family

end Containment

/-! ## The six direction caps of `S²` -/

section Caps

/-- The ambient space of Main Lemma 2. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- The six cap centres `± e_j`.  Every unit vector of `ℝ³` makes an inner product at least
`1/2` with one of them, because some coordinate has square at least `1/3`. -/
noncomputable def capVec (k : Fin 3 × Bool) : Space3 :=
  if k.2 then EuclideanSpace.single k.1 (1 : ℝ) else -(EuclideanSpace.single k.1 (1 : ℝ))

theorem norm_capVec (k : Fin 3 × Bool) : ‖capVec k‖ = 1 := by
  unfold capVec
  split <;> simp

theorem inner_capVec (k : Fin 3 × Bool) (d : Space3) :
    (inner ℝ (capVec k) d : ℝ) = if k.2 then d k.1 else -(d k.1) := by
  unfold capVec
  split <;> simp [EuclideanSpace.inner_single_left]

theorem exists_cap {d : Space3} (hd : ‖d‖ = 1) :
    ∃ k : Fin 3 × Bool, (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) d : ℝ) := by
  have hsum : ∑ j : Fin 3, (d j) ^ 2 = 1 := by
    have h : ‖d‖ ^ 2 = ∑ j : Fin 3, (d j) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      simp [sq]
    rw [← h, hd, one_pow]
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin 3)))
    (f := fun _ : Fin 3 => (1 : ℝ) / 3) (g := fun j => (d j) ^ 2)
    Finset.univ_nonempty (by simp [hsum])
  rcases le_or_gt 0 (d j) with h | h
  · exact ⟨(j, true), by rw [inner_capVec]; simp only [if_pos]; nlinarith⟩
  · refine ⟨(j, false), ?_⟩
    rw [inner_capVec]
    simp only [Bool.false_eq_true, if_false]
    nlinarith

open Classical in
/-- The cap a unit direction belongs to. -/
noncomputable def capIndex (d : Space3) : Fin 3 × Bool :=
  if h : ∃ k : Fin 3 × Bool, (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) d : ℝ) then h.choose
  else (0, true)

theorem capIndex_spec {d : Space3} (hd : ‖d‖ = 1) :
    (1 : ℝ) / 2 ≤ (inner ℝ (capVec (capIndex d)) d : ℝ) := by
  classical
  rw [capIndex, dif_pos (exists_cap hd)]
  exact (exists_cap hd).choose_spec

/-- **The pigeonhole over the six caps.**  Some cap carries at least a sixth of the shade
mass. -/
theorem exists_heavy_cap {ρ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → ShadedTube ρ Space3) :
    ∃ k : Fin 3 × Bool,
      ∑ i ∈ s, volume (T i).shade
        ≤ 6 * ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade := by
  classical
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3 × Bool))
    (fun k => ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade)
    ⟨(0, true), Finset.mem_univ _⟩
  refine ⟨k, ?_⟩
  calc ∑ i ∈ s, volume (T i).shade
      = ∑ k' : Fin 3 × Bool,
          ∑ i ∈ s with capIndex (T i).direction = k', volume (T i).shade :=
        (Finset.sum_fiberwise s (fun i => capIndex (T i).direction)
          (fun i => volume (T i).shade)).symm
    _ ≤ ∑ _k' : Fin 3 × Bool,
          ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade :=
        Finset.sum_le_sum fun k' _ => hk k' (Finset.mem_univ k')
    _ = 6 * ∑ i ∈ s with capIndex (T i).direction = k, volume (T i).shade := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_num

end Caps

/-! ## Fullness of a heavy subfamily -/

section Fullness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A subfamily carrying a `c`-fraction of the shade mass keeps a `c`-fraction of the
fullness.**  No positivity hypothesis is needed: both bounds are ratios of the same two sums. -/
theorem mul_fullness_le_of_subset {ι : Type*} {s' s : Finset ι} (hsub : s' ⊆ s)
    (V : ι → ShadedBody E) {c : NNReal}
    (hmass : (c : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s', volume (V i).shade) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.fullness_def, ShadedBody.fullness_def]
  have hD : (∑ i ∈ s', volume (V i).carrier) ≤ ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum_of_subset hsub
  calc (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier))
      = ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade)
          / (∑ i ∈ s, volume (V i).carrier) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv]
    _ ≤ (∑ i ∈ s', volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) :=
        ENNReal.div_le_div_right hmass _
    _ ≤ (∑ i ∈ s', volume (V i).shade) / (∑ i ∈ s', volume (V i).carrier) :=
        ENNReal.div_le_div le_rfl hD

end Fullness

/-! ## The numerology of the squeeze -/

section Numerology

/-- The `δ`-scale of the squeeze at parent scale `ρ`: `δ = 2σρ` with `σ = ρ³`. -/
theorem sqScale_rpow {ρ : NNReal} (t : ℝ) :
    ((2 * ρ ^ 3 * ρ : NNReal)) ^ t = (2 : NNReal) ^ t * ρ ^ (4 * t) := by
  have h : (2 * ρ ^ 3 * ρ : NNReal) = 2 * ρ ^ 4 := by ring
  rw [h, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_natCast ρ 4, ← NNReal.rpow_mul]
  norm_num

theorem two_rpow_le_two {t : ℝ} (ht : t ≤ 1) : (2 : NNReal) ^ t ≤ 2 := by
  calc (2 : NNReal) ^ t ≤ (2 : NNReal) ^ (1 : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le one_le_two ht
    _ = 2 := NNReal.rpow_one 2

theorem half_le_two_rpow {t : ℝ} (ht : -1 ≤ t) : (2 : NNReal)⁻¹ ≤ (2 : NNReal) ^ t := by
  calc (2 : NNReal)⁻¹ = (2 : NNReal) ^ (-1 : ℝ) := by
        rw [NNReal.rpow_neg_one]
    _ ≤ (2 : NNReal) ^ t := NNReal.rpow_le_rpow_of_exponent_le one_le_two ht

/-- **The Katz–Tao budget.** -/
theorem katzTao_budget {ρ : NNReal} (hρ0 : 0 < ρ) {η₁ : ℝ} (_hη₁0 : 0 < η₁) (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (7 * η₁ / 2) ≤ 1) :
    fatLoss * ρ ^ (-(η₁ / 2)) ≤ ((2 * ρ ^ 3 * ρ : NNReal)) ^ (-η₁) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hsplit : ρ ^ (-(η₁ / 2)) = ρ ^ (7 * η₁ / 2) * ρ ^ (4 * -η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hhead : fatLoss * ρ ^ (7 * η₁ / 2) ≤ (2 : NNReal) ^ (-η₁) := by
    have h12 : (12 : NNReal) * (fatLoss * ρ ^ (7 * η₁ / 2)) ≤ 12 * (2 : NNReal)⁻¹ := by
      calc (12 : NNReal) * (fatLoss * ρ ^ (7 * η₁ / 2))
          = 12 * fatLoss * ρ ^ (7 * η₁ / 2) := by ring
        _ ≤ 1 := hbud
        _ ≤ 12 * (2 : NNReal)⁻¹ := by norm_num
    have h12' : fatLoss * ρ ^ (7 * η₁ / 2) ≤ (2 : NNReal)⁻¹ :=
      le_of_mul_le_mul_left h12 (by norm_num : (0 : NNReal) < 12)
    exact le_trans h12' (half_le_two_rpow (by linarith))
  rw [sqScale_rpow, hsplit, ← mul_assoc]
  gcongr

/-- **The fullness budget.** -/
theorem fullness_budget {ρ : NNReal} (hρ0 : 0 < ρ) {η₁ : ℝ} (_hη₁0 : 0 < η₁) (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (7 * η₁ / 2) ≤ 1) :
    ((2 * ρ ^ 3 * ρ : NNReal)) ^ η₁ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hc : (fatLoss * 6 : NNReal) ≠ 0 := by
    simp [fatLoss_ne_zero]
  have hsplit : ρ ^ (η₁ / 2) = ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hkey : (fatLoss * 6) * ((2 * ρ ^ 3 * ρ : NNReal)) ^ η₁ ≤ ρ ^ (η₁ / 2) := by
    rw [sqScale_rpow, hsplit]
    have h2 : (2 : NNReal) ^ η₁ ≤ 2 := two_rpow_le_two hη₁1
    have hstep : (fatLoss * 6) * ((2 : NNReal) ^ η₁ * ρ ^ (4 * η₁))
        ≤ (fatLoss * 6) * (2 * ρ ^ (4 * η₁)) := by gcongr
    refine le_trans hstep ?_
    have hpow : ρ ^ (7 * η₁ / 2) * ρ ^ (-(7 * η₁ / 2)) = 1 := by
      rw [← NNReal.rpow_add hρne]
      simp
    have hmain : (fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2) ≤ 1 := by
      calc (fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2) = 12 * fatLoss * ρ ^ (7 * η₁ / 2) := by ring
        _ ≤ 1 := hbud
    calc (fatLoss * 6) * (2 * ρ ^ (4 * η₁))
        = ((fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2))
            * (ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁)) := by
          rw [show (fatLoss * 6) * 2 * ρ ^ (7 * η₁ / 2)
              * (ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁))
            = (fatLoss * 6) * 2 * (ρ ^ (7 * η₁ / 2) * ρ ^ (-(7 * η₁ / 2))) * ρ ^ (4 * η₁) from
              by ring, hpow]
          ring
      _ ≤ 1 * (ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁)) := by gcongr
      _ = ρ ^ (-(7 * η₁ / 2)) * ρ ^ (4 * η₁) := one_mul _
  calc ((2 * ρ ^ 3 * ρ : NNReal)) ^ η₁
      = (fatLoss * 6)⁻¹ * ((fatLoss * 6) * ((2 * ρ ^ 3 * ρ : NNReal)) ^ η₁) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by gcongr

/-- **The accuracy budget.** -/
theorem accuracy_budget {ρ : NNReal} (hρ0 : 0 < ρ) {ε : ℝ} (hε : 0 < ε)
    (hbud : 6 * ρ ^ (ε / 2) ≤ 1) :
    (6 : NNReal) * ((2 * ρ ^ 3 * ρ : NNReal)) ^ (-(ε / 8)) ≤ ρ ^ (-ε) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hsplit : ρ ^ (-ε) = ρ ^ (ε / 2) * ρ ^ (4 * -(ε / 8)) * ρ ^ (-ε) := by
    rw [← NNReal.rpow_add hρne, ← NNReal.rpow_add hρne]
    congr 1
    ring
  rw [sqScale_rpow]
  have h2 : (2 : NNReal) ^ (-(ε / 8)) ≤ 1 := by
    calc (2 : NNReal) ^ (-(ε / 8)) ≤ (2 : NNReal) ^ (0 : ℝ) :=
          NNReal.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 := NNReal.rpow_zero 2
  calc (6 : NNReal) * ((2 : NNReal) ^ (-(ε / 8)) * ρ ^ (4 * -(ε / 8)))
      ≤ 6 * (1 * ρ ^ (4 * -(ε / 8))) := by gcongr
    _ = 6 * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (4 * -(ε / 8))) := by
        rw [show (6 : NNReal) * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (4 * -(ε / 8)))
            = 6 * (ρ ^ (ε / 2) * ρ ^ (-(ε / 2))) * ρ ^ (4 * -(ε / 8)) from by ring,
          ← NNReal.rpow_add hρne]
        simp
    _ ≤ 1 * (ρ ^ (-(ε / 2)) * ρ ^ (4 * -(ε / 8))) := by gcongr
    _ = ρ ^ (-ε) := by
        rw [one_mul, ← NNReal.rpow_add hρne]
        congr 1
        ring

end Numerology

/-! ## The main theorem -/

section Main

universe u

set_option maxHeartbeats 1000000 in
/-- **`SmallCard γ` implies the full Katz–Tao estimate at `γ`.**

The band `|𝕋| < δ^{-1}` of `Kakeya.ML2Assembly.SmallCard` is *affinely vacuous*: squeezing a
family of `ρ`-tubes transversally by `σ = ρ³` presents it as a family of `δ`-tubes with
`δ = 2ρ⁴`, whose cardinality `≲ ρ^{-3}` is far below `δ^{-1} ≍ ρ^{-4}`. -/
theorem katzTaoEstimate_of_smallCard {γ : ℝ} (hγ : 0 ≤ γ)
    (hsc : Kakeya.ML2Assembly.SmallCard.{u} γ) :
    Kakeya.KatzTaoEstimate.{u} Space3 γ := by
  classical
  have hn : Module.finrank ℝ Space3 = 3 := finrank_euclideanSpace_fin
  intro ε hε
  obtain ⟨η₁, hη₁0, hη₁1, hsm⟩ := hsc (ε / 8) (by linarith)
  refine ⟨η₁ / 2, by positivity, ?_⟩
  have hmap : Filter.Tendsto (fun ρ : NNReal => 2 * ρ ^ 3 * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun ρ : NNReal => 2 * ρ ^ 3 * ρ) := by fun_prop
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      simpa using hcont.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ0 : (0 : NNReal) < ρ := hρ
      exact Set.mem_Ioi.mpr (by positivity)
  filter_upwards [hmap.eventually hsm,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const
      (4 * Tube.card_le_of_densityIn_le.C 3) 1 one_pos (p := 1) one_pos,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const (12 * fatLoss) 1 one_pos
      (p := 7 * η₁ / 2) (by positivity),
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const 6 1 one_pos
      (p := ε / 2) (by positivity),
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num),
    self_mem_nhdsWithin] with ρ hδsm hcardbud hktbud haccbud hρhalf hρpos
  intro ι s T hball hKT hfull
  have hρ0 : (0 : NNReal) < ρ := hρpos
  have hρne : (ρ : NNReal) ≠ 0 := hρ0.ne'
  have hρ12 : ρ ≤ 1 / 2 := hρhalf.2.le
  have hρ1 : ρ ≤ 1 := le_trans hρ12 (by norm_num)
  have hσ0 : (0 : NNReal) < ρ ^ 3 := by positivity
  have hσ1 : (ρ : NNReal) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hρ1
  have hδpos : (0 : NNReal) < 2 * ρ ^ 3 * ρ := by positivity
  have hδne : (2 * ρ ^ 3 * ρ : NNReal) ≠ 0 := hδpos.ne'
  have hδ8 : (2 * ρ ^ 3 * ρ : NNReal) ≤ 1 / 8 := by
    have hstep : (2 * ρ ^ 3 * ρ : NNReal) ≤ 2 * (1 / 2 : NNReal) ^ 3 * (1 / 2 : NNReal) := by
      gcongr
    calc (2 * ρ ^ 3 * ρ : NNReal) ≤ 2 * (1 / 2 : NNReal) ^ 3 * (1 / 2 : NNReal) := hstep
      _ = 1 / 8 := by norm_num
  have hδ1 : (2 * ρ ^ 3 * ρ : NNReal) ≤ 1 := by
    refine le_trans hδ8 ?_
    rw [← NNReal.coe_le_coe]
    norm_num
  have hδ4 : ((2 * ρ ^ 3 * ρ : NNReal) : ℝ) ≤ 1 / 4 := by
    have h : ((2 * ρ ^ 3 * ρ : NNReal) : ℝ) ≤ ((1 / 8 : NNReal) : ℝ) := by exact_mod_cast hδ8
    simpa using le_trans h (by norm_num)
  -- the heavy cap
  obtain ⟨k, hk⟩ := exists_heavy_cap s T
  set s' : Finset ι := s.filter (fun i => capIndex (T i).direction = k) with hs'def
  have hs'sub : s' ⊆ s := Finset.filter_subset _ _
  have he : ‖capVec k‖ = 1 := norm_capVec k
  have hcap : ∀ i ∈ s', (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) (T i).direction : ℝ) := by
    intro i hi
    have hmem := Finset.mem_filter.mp (hs'def ▸ hi)
    have hspec := capIndex_spec (T i).toTube.norm_direction
    rwa [hmem.2] at hspec
  have hball' : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    fun i hi => hball i (hs'sub hi)
  -- the squeezed family
  set U : ι → ShadedTube (2 * ρ ^ 3 * ρ) Space3 :=
    sqFamily hσ0 he (2 * ρ ^ 3 * ρ) T with hUdef
  -- (H1) the squeezed carriers lie in the unit ball
  have hH1 : ∀ i ∈ s', (U i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    sqFamily_carrier_subset_closedBall hσ0 hσ1 he hball' hδ4
  -- (H2) the Katz--Tao hypothesis at the new scale
  have hmaxs' : Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (ρ : ENNReal) ^ (-(η₁ / 2)) := le_trans (Kakeya.maxDensity_mono _ hs'sub) hKT
  have hH2 : ConvexSpaceBody.IsKatzTao s' (fun i => (U i).toConvexSpaceBody)
      (((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-η₁)) := by
    refine le_trans (sqFamily_maxDensity_le hn hσ0 hσ1 hρ1 he hcap hδ1) ?_
    refine le_trans (by gcongr : (fatLoss : ENNReal)
        * Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (fatLoss : ENNReal) * (ρ : ENNReal) ^ (-(η₁ / 2))) ?_
    have hb := ENNReal.coe_le_coe.mpr (katzTao_budget hρ0 hη₁0 hη₁1 hktbud)
    rwa [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hρne,
      ENNReal.coe_rpow_of_ne_zero hδne] at hb
  -- (H3) the fullness hypothesis at the new scale
  have hmass : (((6 : NNReal)⁻¹ : NNReal) : ENNReal)
        * ∑ i ∈ s, volume (T i).toShadedBody.shade
      ≤ ∑ i ∈ s', volume (T i).toShadedBody.shade := by
    rw [ENNReal.coe_inv (by norm_num : (6 : NNReal) ≠ 0),
      ENNReal.inv_mul_le_iff (by simp) (by simp)]
    simpa using hk
  have hfulls' : (6 : NNReal)⁻¹ * ρ ^ (η₁ / 2)
      ≤ ShadedBody.fullness s' (fun i => (T i).toShadedBody) := by
    refine le_trans ?_ (mul_fullness_le_of_subset hs'sub (fun i => (T i).toShadedBody) hmass)
    gcongr
  have hH3 : ShadedBody.fullness s' (fun i => (U i).toShadedBody)
      ≥ (2 * ρ ^ 3 * ρ : NNReal) ^ η₁ := by
    refine le_trans ?_ (sqFamily_le_fullness hn hσ0 hσ1 hρ1 he hcap hδ1)
    refine le_trans (fullness_budget hρ0 hη₁0 hη₁1 hktbud) ?_
    rw [mul_inv, mul_assoc]
    gcongr
  -- (H4) the cardinality hypothesis
  have hH4 : ((s'.card : ℝ)) < ((2 * ρ ^ 3 * ρ : NNReal) : ℝ)⁻¹ := by
    have hdens : Kakeya.densityIn s' (fun i => ((T i).toTube).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≤ ((ρ : ENNReal))⁻¹ := by
      refine le_trans (Kakeya.le_maxDensity _ _ _) (le_trans hmaxs' ?_)
      have hρE : (ρ : ENNReal) ≤ 1 := by exact_mod_cast hρ1
      rw [show ((ρ : ENNReal))⁻¹ = (ρ : ENNReal) ^ (-1 : ℝ) by
        rw [ENNReal.rpow_neg_one]]
      exact ENNReal.rpow_le_rpow_of_exponent_ge hρE (by linarith)
    have hcard := Tube.card_le_of_densityIn_le (E := Space3) (s := s') hρne
      (T := fun i => (T i).toTube) hball' hdens
    rw [hn] at hcard
    have hzpN : (ρ : NNReal) ^ (-((3 : ℕ) - 1 : ℤ)) = (ρ ^ 2)⁻¹ := by
      rw [show (-((3 : ℕ) - 1 : ℤ)) = (-2 : ℤ) by norm_num, zpow_neg]
      norm_num
      rfl
    have hzp : ((ρ : ENNReal)) ^ (-((3 : ℕ) - 1 : ℤ))
        = (((ρ ^ 2 : NNReal)⁻¹ : NNReal) : ENNReal) := by
      rw [← ENNReal.coe_zpow hρne, hzpN]
    rw [hzp, show ((ρ : ENNReal))⁻¹ = (((ρ⁻¹ : NNReal)) : ENNReal) from
      (ENNReal.coe_inv hρne).symm, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
      ← ENNReal.coe_natCast] at hcard
    have hcardN : (s'.card : NNReal)
        ≤ Tube.card_le_of_densityIn_le.C 3 * ρ⁻¹ * (ρ ^ 2)⁻¹ := ENNReal.coe_le_coe.mp hcard
    have hprod : (s'.card : NNReal) * (2 * ρ ^ 3 * ρ) ≤ 1 / 2 := by
      calc (s'.card : NNReal) * (2 * ρ ^ 3 * ρ)
          ≤ (Tube.card_le_of_densityIn_le.C 3 * ρ⁻¹ * (ρ ^ 2)⁻¹) * (2 * ρ ^ 3 * ρ) := by gcongr
        _ = 2 * (Tube.card_le_of_densityIn_le.C 3 * ρ) := by field_simp
        _ ≤ 1 / 2 := by
            have h4 : 4 * Tube.card_le_of_densityIn_le.C 3 * ρ ≤ 1 := by
              simpa using hcardbud
            calc 2 * (Tube.card_le_of_densityIn_le.C 3 * ρ)
                = (4 * Tube.card_le_of_densityIn_le.C 3 * ρ) * (1 / 2 : NNReal) := by ring
              _ ≤ 1 * (1 / 2 : NNReal) := by gcongr
              _ = 1 / 2 := one_mul _
    have hprodR : ((s'.card : ℝ)) * ((2 * ρ ^ 3 * ρ : NNReal) : ℝ) ≤ 1 / 2 := by
      have h := NNReal.coe_le_coe.mpr hprod
      push_cast at h
      simpa using h
    have hδR : (0 : ℝ) < ((2 * ρ ^ 3 * ρ : NNReal) : ℝ) := by
      exact_mod_cast hδpos
    have hlt : ((s'.card : ℝ)) * ((2 * ρ ^ 3 * ρ : NNReal) : ℝ) < 1 := by linarith
    calc ((s'.card : ℝ))
        = (((s'.card : ℝ)) * ((2 * ρ ^ 3 * ρ : NNReal) : ℝ))
            * ((2 * ρ ^ 3 * ρ : NNReal) : ℝ)⁻¹ := by field_simp
      _ < 1 * ((2 * ρ ^ 3 * ρ : NNReal) : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_right hlt (inv_pos.mpr hδR)
      _ = ((2 * ρ ^ 3 * ρ : NNReal) : ℝ)⁻¹ := one_mul _
  -- apply `SmallCard` at the squeezed scale
  have hconc := hδsm s' U hH1 hH2 hH3 hH4
  rw [sqFamily_sum_shade hσ0 hσ1 hρ1 he hcap le_rfl,
    sqFamily_iUnion_shade hσ0 hσ1 hρ1 he hcap le_rfl] at hconc
  have hJ0 : Kakeya.affineJacobian (sqA hσ0 he) ≠ 0 := Kakeya.affineJacobian_ne_zero _
  have hJt : Kakeya.affineJacobian (sqA hσ0 he) ≠ ⊤ := Kakeya.affineJacobian_ne_top _
  have hconc' : ∑ i ∈ s', volume (T i).shade
      ≤ ((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-(ε / 8)) * (s'.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s', (T i).shade) := by
    rw [show ((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-(ε / 8)) * (s'.card : ENNReal) ^ γ
          * (Kakeya.affineJacobian (sqA hσ0 he) * volume (⋃ i ∈ s', (T i).shade))
        = Kakeya.affineJacobian (sqA hσ0 he)
          * (((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-(ε / 8)) * (s'.card : ENNReal) ^ γ
            * volume (⋃ i ∈ s', (T i).shade)) from by ring] at hconc
    exact (ENNReal.mul_le_mul_iff_right hJ0 hJt).mp hconc
  -- assemble
  have hcardle : (s'.card : ENNReal) ^ γ ≤ (s.card : ENNReal) ^ γ := by
    have hle : ((s'.card : ENNReal)) ≤ (s.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hs'sub
    exact ENNReal.rpow_le_rpow hle hγ
  have hunionle : volume (⋃ i ∈ s', (T i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) :=
    measure_mono (Set.biUnion_subset_biUnion_left hs'sub)
  have hacc : (6 : ENNReal) * ((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-(ε / 8))
      ≤ (ρ : ENNReal) ^ (-ε) := by
    have hb := ENNReal.coe_le_coe.mpr (accuracy_budget hρ0 hε haccbud)
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne,
      ENNReal.coe_rpow_of_ne_zero hρne] at hb
    simpa using hb
  calc ∑ i ∈ s, volume (T i).shade
      ≤ 6 * ∑ i ∈ s', volume (T i).shade := hk
    _ ≤ 6 * (((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-(ε / 8)) * (s'.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s', (T i).shade)) := by gcongr
    _ ≤ 6 * (((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-(ε / 8)) * (s.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s, (T i).shade)) := by gcongr
    _ = (6 * ((2 * ρ ^ 3 * ρ : NNReal) : ENNReal) ^ (-(ε / 8))) * (s.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s, (T i).shade) := by ring
    _ ≤ (ρ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-! ## The equivalence, the tripwires, and the consequence for the assembly -/

/-- **`SmallCard γ ⟺ K_KT γ`.**  The band `|𝕋| < δ^{-1}` of `Kakeya.ML2Assembly.SmallCard` is
affinely vacuous for every `γ ≥ 0`. -/
theorem smallCard_iff_katzTaoEstimate {γ : ℝ} (hγ : 0 ≤ γ) :
    Kakeya.ML2Assembly.SmallCard.{u} γ ↔ Kakeya.KatzTaoEstimate.{u} Space3 γ :=
  ⟨katzTaoEstimate_of_smallCard hγ, Kakeya.ML2Band.smallCard_of_katzTaoEstimate⟩

set_option linter.unusedVariables false in
/-- **The consequence for `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`.**

Its hypotheses are reproduced verbatim *except* `hdich : Dichotomy β (β/2) g η` — the GWZ Lemma
9.1 input and the whole geometric core — which is **not used**.  So its conclusion already
follows from `hsmall` alone. -/
theorem katzTaoEstimate_sub_of_smallCard_alone {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hsmall : Kakeya.ML2Assembly.SmallCard.{u} (β - c)) :
    Kakeya.KatzTaoEstimate.{u} Space3 (β - c) :=
  katzTaoEstimate_of_smallCard (by linarith) hsmall

/-! ### Tripwires

If `Kakeya.ML2Assembly.SmallCard` or `Kakeya.KatzTaoEstimate` drifts — a binder moved, a
hypothesis added or dropped — the `example`s below stop compiling. -/

example {γ : ℝ} (hγ : 0 ≤ γ) (h : Kakeya.ML2Assembly.SmallCard.{u} γ) :
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ :=
  katzTaoEstimate_of_smallCard hγ h

example {β c : ℝ} (hc : 0 < c) (hcβ : 2 * c ≤ β)
    (hsmall : Kakeya.ML2Assembly.SmallCard.{u} (β - c)) :
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
  katzTaoEstimate_of_smallCard (by linarith) hsmall

/-- compatibility on `Kakeya.ML2Assembly.SmallCard`'s body, restated verbatim. -/
def SmallCardTarget (γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

theorem smallCardTarget_eq : SmallCardTarget.{u} = Kakeya.ML2Assembly.SmallCard.{u} := rfl

/-! ### The aperture of the cap does not depend on `σ`

The geometric core `Kakeya.ML2Squeeze.sqL_image_subset_sqTube` is stated under
`1/2 ≤ ⟪e, S.direction⟫` — an aperture of `60°`, with **no `σ` in it**.  The reason is that the
squeeze *itself* contracts directions towards `e`: the image core direction `u` satisfies
`‖u - e‖ ≤ 4σ` (inside the proof), so the transverse spread of `A(S)` is `O(σρ)` even though the
image of a cross-sectional vector can have length `≍ ρ`, that length being spent
*longitudinally*.  Six caps therefore suffice, not `σ^{-2}` of them. -/
theorem sqL_image_subset_sqTube_capIndex {σ ρ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ1 : ρ ≤ 1) (S : Tube ρ Space3) :
    (sqL σ (norm_capVec (capIndex S.direction))) '' S.carrier
      ⊆ (sqTube hσ0 (norm_capVec (capIndex S.direction)) (2 * σ * ρ) S).carrier :=
  sqL_image_subset_sqTube hσ0 hσ1 hρ1 (norm_capVec (capIndex S.direction)) S
    (capIndex_spec S.norm_direction) le_rfl

/-! ### The squeeze is asymmetric: the reverse squeeze is not free

Presenting a `ρ`-tube as a `δ`-tube with `δ ≥ ρ` costs a factor `≳ (δ/ρ)²` in volume — hence in
`Δ_max` and in fullness — and *that* is not an absolute constant.  So the mechanism that empties
`Kakeya.ML2Assembly.SmallCard`'s band does **not** touch `Kakeya.ML2Assembly.Dichotomy`'s
`δ⁻¹ ≤ |𝕋|`. -/
theorem reverse_squeeze_cost {ρ δ : NNReal} (hρ1 : ρ ≤ 1) (S : Tube ρ Space3) {C : NNReal}
    (h : volume (S.rescale δ).carrier ≤ (C : ENNReal) * volume S.carrier) :
    (Tube.le_volume.c 3 : NNReal) * δ ^ 2 ≤ C * (Tube.volume_le.C 3) * ρ ^ 2 := by
  have hn : Module.finrank ℝ Space3 = 3 := finrank_euclideanSpace_fin
  have hlow : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((δ : NNReal) : ENNReal) ^ 2
      ≤ volume (S.rescale δ).carrier := by
    have h1 := Tube.le_volume (E := Space3) (S.rescale δ)
    rw [hn] at h1
    simpa using h1
  have hup : volume S.carrier
      ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal) * ((ρ : NNReal) : ENNReal) ^ 2 := by
    have h1 := Tube.volume_le (E := Space3) hρ1 S
    rw [hn] at h1
    simpa using h1
  have hchain : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((δ : NNReal) : ENNReal) ^ 2
      ≤ ((C : ENNReal)) * (((Tube.volume_le.C 3 : NNReal) : ENNReal)
        * ((ρ : NNReal) : ENNReal) ^ 2) :=
    le_trans hlow (le_trans h (by gcongr))
  have hcast : (((Tube.le_volume.c 3 * δ ^ 2 : NNReal)) : ENNReal)
      ≤ (((C * Tube.volume_le.C 3 * ρ ^ 2 : NNReal)) : ENNReal) := by
    push_cast
    calc ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((δ : NNReal) : ENNReal) ^ 2
        ≤ ((C : ENNReal)) * (((Tube.volume_le.C 3 : NNReal) : ENNReal)
          * ((ρ : NNReal) : ENNReal) ^ 2) := hchain
      _ = ((C : ENNReal)) * ((Tube.volume_le.C 3 : NNReal) : ENNReal)
          * ((ρ : NNReal) : ENNReal) ^ 2 := by ring
  exact_mod_cast hcast

/-- The case `δ = 1`: any constant pricing the reverse squeeze from scale `ρ` to scale `1`
must be at least `c₃ / (C₃ ρ²)`, which is unbounded as `ρ → 0`. -/
theorem reverse_squeeze_cost_one {ρ : NNReal} (hρ1 : ρ ≤ 1) (S : Tube ρ Space3) {C : NNReal}
    (h : volume (S.rescale 1).carrier ≤ (C : ENNReal) * volume S.carrier) :
    (Tube.le_volume.c 3 : NNReal) ≤ C * (Tube.volume_le.C 3) * ρ ^ 2 := by
  simpa using reverse_squeeze_cost hρ1 S h

/-- **No absolute constant prices the reverse squeeze.**  For every candidate `C`, once `ρ` is
small enough that `C · C₃ · ρ² < c₃` the comparison fails outright.  Contrast `fatLoss`, which
prices the *forward* squeeze at every scale at once. -/
theorem reverse_squeeze_not_absolute (C : NNReal) {ρ : NNReal} (hρ1 : ρ ≤ 1)
    (hsmall : C * Tube.volume_le.C 3 * ρ ^ 2 < Tube.le_volume.c 3) (S : Tube ρ Space3) :
    ¬ volume (S.rescale 1).carrier ≤ (C : ENNReal) * volume S.carrier :=
  fun h => absurd (reverse_squeeze_cost_one hρ1 S h) (not_le.mpr hsmall)

/-! ### The aperture claim, refuted

The informal objection to the squeeze is that `A = ¼·diag(σ,σ,1)` maps a `ρ`-tube to a `2σρ`-tube
only for directions within angle `≈ σ` of the axis, so that covering `S²` would need `≈ σ^{-2}`
caps and the partition would cost a *power* of the scale.  That is false, and the reason is
`Kakeya.ML2Squeeze.norm_perp_sqL_le`: the image of a cross-sectional vector `w` can indeed have
length `≍ ρ`, but that length is spent **longitudinally** — its component perpendicular to the
image core direction `u` is `O(σρ)` — because the squeeze contracts *directions* towards `e`
(`‖u - e‖ ≤ 4σ`) uniformly over a cap of aperture `60°`.

`Kakeya.ML2Squeeze.narrowApertureClaim_false` refutes the objection with a witness at
`3/5`-`4/5`, i.e. at angle `≈ 53°` from the cap centre, at every `σ ≤ 1/5`. -/

/-- The `3-4-5` unit vector, at angle `arccos(3/5) ≈ 53°` from `e₁`. -/
noncomputable def diag345 : Space3 :=
  (3 / 5 : ℝ) • EuclideanSpace.single 0 (1 : ℝ) + (4 / 5 : ℝ) • EuclideanSpace.single 1 (1 : ℝ)

theorem diag345_apply (j : Fin 3) :
    diag345 j = if j = 0 then (3 / 5 : ℝ) else if j = 1 then (4 / 5 : ℝ) else 0 := by
  fin_cases j <;> simp [diag345]

theorem norm_diag345 : ‖diag345‖ = 1 := by
  have hsq : ‖diag345‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [Fin.sum_univ_three]
    simp [diag345_apply]
    norm_num
  nlinarith [norm_nonneg diag345, hsq]

theorem inner_e1_diag345 :
    (inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) diag345 : ℝ) = 3 / 5 := by
  rw [EuclideanSpace.inner_single_left]
  simp [diag345_apply]

theorem norm_diag345_sub_e1 :
    (4 : ℝ) / 5 ≤ ‖diag345 - EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ := by
  have he1 : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space3)‖ = 1 := by simp
  have hsq : ‖diag345 - EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ ^ 2 = 4 / 5 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_diag345, he1,
      real_inner_comm, inner_e1_diag345]
    norm_num
  nlinarith [norm_nonneg (diag345 - EuclideanSpace.single (0 : Fin 3) (1 : ℝ)), hsq]

/-- The claim that the squeeze only works inside a cap of aperture `O(σ)`. -/
def NarrowApertureClaim : Prop :=
  ∀ (σ ρ : NNReal) (hσ0 : 0 < σ), σ ≤ 1 → ρ ≤ 1 →
    ∀ (e : Space3) (he : ‖e‖ = 1) (S : Tube ρ Space3),
      (sqL σ he) '' S.carrier ⊆ (sqTube hσ0 he (2 * σ * ρ) S).carrier →
      ‖S.direction - e‖ ≤ 4 * (σ : ℝ)

/-- **The aperture claim is false.**  At `σ = 1/8` the squeeze handles a direction at angle
`≈ 53°` from the cap centre, sixteen times the claimed aperture `4σ = 1/2`. -/
theorem narrowApertureClaim_false : ¬ NarrowApertureClaim := by
  intro h
  have he : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space3)‖ = 1 := by simp
  set S : Tube 1 Space3 := Tube.ofMidpointDirection 1 0 diag345 norm_diag345 with hS
  have hdir : S.direction = diag345 := by
    show (0 : Space3) + (1 / 2 : ℝ) • diag345 - ((0 : Space3) - (1 / 2 : ℝ) • diag345) = diag345
    module
  have hcap : (1 : ℝ) / 2
      ≤ (inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space3) S.direction : ℝ) := by
    rw [hdir, inner_e1_diag345]
    norm_num
  have hσ0 : (0 : NNReal) < 1 / 8 := by norm_num
  have hσ1 : (1 / 8 : NNReal) ≤ 1 := by rw [← NNReal.coe_le_coe]; norm_num
  have hsub := sqL_image_subset_sqTube hσ0 hσ1 (le_refl (1 : NNReal)) he S hcap le_rfl
  have hbad := h (1 / 8) 1 hσ0 hσ1 le_rfl _ he S hsub
  rw [hdir] at hbad
  have hnum : ((1 / 8 : NNReal) : ℝ) = 1 / 8 := by norm_num
  rw [hnum] at hbad
  have := norm_diag345_sub_e1
  linarith

/-- **One cap, every `σ`.**  The aperture of `Kakeya.ML2Squeeze.sqL_image_subset_sqTube` carries
no `σ`: the same tube is handled by the same frame at every squeeze ratio. -/
theorem aperture_sigma_free {ρ : NNReal} (hρ1 : ρ ≤ 1) (S : Tube ρ Space3)
    {e : Space3} (he : ‖e‖ = 1) (hcap : (1 : ℝ) / 2 ≤ (inner ℝ e S.direction : ℝ))
    (σ : NNReal) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (sqL σ he) '' S.carrier ⊆ (sqTube hσ0 he (2 * σ * ρ) S).carrier :=
  sqL_image_subset_sqTube hσ0 hσ1 hρ1 he S hcap le_rfl

/-! ### The producer question

"Is the hypothesis weaker than the goal as a `Prop`?" is the wrong test for circularity; the right
one is **what must be built to discharge it**.  Here the answer is stark, and it is quantified over
*every* candidate producer: anything at all that discharges the small-cardinality slot at `γ ≥ 0`
has thereby discharged Main Lemma 2's conclusion at `γ`.  There is no route to `hsmall` that lands
anywhere easier than the goal, because `hsmall` *is* the goal. -/

/-- **Every producer of `hsmall` is a producer of the goal.** -/
theorem producer_of_smallCard_is_producer_of_goal {γ : ℝ} (hγ : 0 ≤ γ) (P : Prop)
    (h : P → Kakeya.ML2Assembly.SmallCard.{u} γ) :
    P → Kakeya.KatzTaoEstimate.{u} Space3 γ :=
  fun hp => katzTaoEstimate_of_smallCard hγ (h hp)

/-- The instance at the two named candidate producers in the tree.  `BandDichotomy` is not a
reduction of the band: it already gives the improved estimate outright. -/
theorem katzTaoEstimate_of_bandDichotomy {β g c : ℝ} (hc : 0 < c) (hcg : c ≤ g)
    (hγ : 0 ≤ β - c) (h : Kakeya.ML2Band.BandDichotomy.{u} β g) :
    Kakeya.KatzTaoEstimate.{u} Space3 (β - c) :=
  katzTaoEstimate_of_smallCard hγ (Kakeya.ML2Band.smallCard_of_bandDichotomy hc hcg hγ h)

/-- **`Kakeya.ML2Band.BandKakeya` is not a band statement at all.**  It gives `K_KT γ` for *every*
`γ ≥ 0` — including `γ = 0`, the full Kakeya multiplicity estimate in `ℝ³`.  So the multilinear
input scoped in `Reduction/BandMultilinear.lean` would, if proved, prove the whole of Main Lemma 2
without any of the reduction. -/
theorem katzTaoEstimate_of_bandKakeya {γ : ℝ} (hγ : 0 ≤ γ) (h : Kakeya.ML2Band.BandKakeya.{u}) :
    Kakeya.KatzTaoEstimate.{u} Space3 γ :=
  katzTaoEstimate_of_smallCard hγ (Kakeya.ML2Band.smallCard_of_bandKakeya hγ h)

/-- **Round trip at `γ = 1`**, where the conclusion is independently known
(`Kakeya.KatzTao_one`): the squeeze reproduces it from the band form.  A smoke test that the
pipeline is not vacuous at the type level. -/
example : Kakeya.KatzTaoEstimate.{u} Space3 1 :=
  katzTaoEstimate_of_smallCard zero_le_one
    (Kakeya.ML2Band.smallCard_of_katzTaoEstimate (Kakeya.KatzTao_one (n := 3)))

end Main

/-! ## Part II — any `β`-only cardinality cut is circular

`Kakeya.ML2Squeeze.katzTaoEstimate_of_smallCard` empties the band `|𝕋| < δ^{-1}`.  The obvious
next thought is that a *smaller* threshold might survive: the assembly's `δ^{-1}` came from
reading Theorem 7.3(B) at the absolute accuracy `ε₀ = β/2`, and a smaller `ε₀` would buy a
smaller threshold (`Kakeya.ML2Band.absoluteLossRoute_insufficient` prices it at
`θ ≈ (ε₀-ε)/(β-ν)`).  It does not survive.  For **every** `θ > 0` the complementary case
`|𝕋| < δ^{-θ}` is again the full estimate: take the squeeze at `σ = ρ^m` with `m` large enough
that `(m+1)θ ≥ 4`, and the image cardinality `≲ ρ^{-3}` still falls below
`δ^{-θ} = (2ρ^{m+1})^{-θ} ≳ ρ^{-4}`.  The extra depth costs only a factor `m+1` in the accuracy,
and the accuracy may be chosen after `ε`. -/

section Cut

universe v

/-- `Kakeya.ML2Assembly.SmallCard` with the threshold `δ^{-1}` replaced by `δ^{-θ}`. -/
def SmallCardCut (θ γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ) ^ (-θ) →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-- A smaller cut is a weaker hypothesis, so `SmallCardCut` is antitone in `θ`. -/
theorem smallCardCut_mono {θ θ' γ : ℝ} (hθ : θ' ≤ θ) (h : SmallCardCut.{v} θ γ) :
    SmallCardCut.{v} θ' γ := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull hcard
  refine hδev s T hball hKT hfull (lt_of_lt_of_le hcard ?_)
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1' : ((δ : ℝ)) ≤ 1 := by exact_mod_cast hδ1.le
  exact Real.rpow_le_rpow_of_exponent_ge hδ0' hδ1' (by linarith)

/-- At `θ = 1` the cut is the assembly's own. -/
theorem smallCardCut_one_of_smallCard {γ : ℝ} (h : Kakeya.ML2Assembly.SmallCard.{v} γ) :
    SmallCardCut.{v} 1 γ := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev] with δ hδev
  intro ι s T hball hKT hfull hcard
  refine hδev s T hball hKT hfull ?_
  rwa [Real.rpow_neg_one] at hcard

theorem smallCard_of_smallCardCut_one {γ : ℝ} (h : SmallCardCut.{v} 1 γ) :
    Kakeya.ML2Assembly.SmallCard.{v} γ := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev] with δ hδev
  intro ι s T hball hKT hfull hcard
  refine hδev s T hball hKT hfull ?_
  rwa [Real.rpow_neg_one]

/-! ### The numerology at depth `m` -/

theorem sqScaleN_rpow (m : ℕ) {ρ : NNReal} (t : ℝ) :
    ((2 * ρ ^ m * ρ : NNReal)) ^ t = (2 : NNReal) ^ t * ρ ^ (((m : ℝ) + 1) * t) := by
  have h : (2 * ρ ^ m * ρ : NNReal) = 2 * ρ ^ (m + 1) := by rw [pow_succ]; ring
  rw [h, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_natCast ρ (m + 1), ← NNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- **The Katz--Tao budget at depth `m`.** -/
theorem katzTao_budgetN {ρ : NNReal} (hρ0 : 0 < ρ) (m : ℕ) {η₁ : ℝ} (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (((m : ℝ) + 1) * η₁ - η₁ / 2) ≤ 1) :
    fatLoss * ρ ^ (-(η₁ / 2)) ≤ ((2 * ρ ^ m * ρ : NNReal)) ^ (-η₁) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  set M : ℝ := (m : ℝ) + 1 with hM
  have hsplit : ρ ^ (-(η₁ / 2)) = ρ ^ (M * η₁ - η₁ / 2) * ρ ^ (M * -η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hhead : fatLoss * ρ ^ (M * η₁ - η₁ / 2) ≤ (2 : NNReal) ^ (-η₁) := by
    have h12 : (12 : NNReal) * (fatLoss * ρ ^ (M * η₁ - η₁ / 2)) ≤ 12 * (2 : NNReal)⁻¹ := by
      calc (12 : NNReal) * (fatLoss * ρ ^ (M * η₁ - η₁ / 2))
          = 12 * fatLoss * ρ ^ (M * η₁ - η₁ / 2) := by ring
        _ ≤ 1 := hbud
        _ ≤ 12 * (2 : NNReal)⁻¹ := by norm_num
    exact le_trans (le_of_mul_le_mul_left h12 (by norm_num : (0 : NNReal) < 12))
      (half_le_two_rpow (by linarith))
  rw [sqScaleN_rpow, hsplit, ← mul_assoc]
  gcongr

/-- **The fullness budget at depth `m`.** -/
theorem fullness_budgetN {ρ : NNReal} (hρ0 : 0 < ρ) (m : ℕ) {η₁ : ℝ} (hη₁1 : η₁ ≤ 1)
    (hbud : 12 * fatLoss * ρ ^ (((m : ℝ) + 1) * η₁ - η₁ / 2) ≤ 1) :
    ((2 * ρ ^ m * ρ : NNReal)) ^ η₁ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hc : (fatLoss * 6 : NNReal) ≠ 0 := by simp [fatLoss_ne_zero]
  set M : ℝ := (m : ℝ) + 1 with hM
  have hsplit : ρ ^ (η₁ / 2) = ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁) := by
    rw [← NNReal.rpow_add hρne]
    congr 1
    ring
  have hkey : (fatLoss * 6) * ((2 * ρ ^ m * ρ : NNReal)) ^ η₁ ≤ ρ ^ (η₁ / 2) := by
    rw [sqScaleN_rpow, hsplit]
    have h2 : (2 : NNReal) ^ η₁ ≤ 2 := two_rpow_le_two hη₁1
    have hstep : (fatLoss * 6) * ((2 : NNReal) ^ η₁ * ρ ^ (M * η₁))
        ≤ (fatLoss * 6) * (2 * ρ ^ (M * η₁)) := by gcongr
    refine le_trans hstep ?_
    have hpow : ρ ^ (M * η₁ - η₁ / 2) * ρ ^ (-(M * η₁ - η₁ / 2)) = 1 := by
      rw [← NNReal.rpow_add hρne]; simp
    have hmain : (fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2) ≤ 1 := by
      calc (fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2)
          = 12 * fatLoss * ρ ^ (M * η₁ - η₁ / 2) := by ring
        _ ≤ 1 := hbud
    calc (fatLoss * 6) * (2 * ρ ^ (M * η₁))
        = ((fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2))
            * (ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁)) := by
          rw [show (fatLoss * 6) * 2 * ρ ^ (M * η₁ - η₁ / 2)
              * (ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁))
            = (fatLoss * 6) * 2 * (ρ ^ (M * η₁ - η₁ / 2) * ρ ^ (-(M * η₁ - η₁ / 2)))
              * ρ ^ (M * η₁) from by ring, hpow]
          ring
      _ ≤ 1 * (ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁)) := by gcongr
      _ = ρ ^ (-(M * η₁ - η₁ / 2)) * ρ ^ (M * η₁) := one_mul _
  calc ((2 * ρ ^ m * ρ : NNReal)) ^ η₁
      = (fatLoss * 6)⁻¹ * ((fatLoss * 6) * ((2 * ρ ^ m * ρ : NNReal)) ^ η₁) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ ≤ (fatLoss * 6)⁻¹ * ρ ^ (η₁ / 2) := by gcongr

/-- **The accuracy budget at depth `m`.**  The accuracy handed to `SmallCardCut` is
`ε / (2(m+1))`, which is legal because it is chosen *after* `ε`. -/
theorem accuracy_budgetN {ρ : NNReal} (hρ0 : 0 < ρ) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hbud : 6 * ρ ^ (ε / 2) ≤ 1) :
    (6 : NNReal) * ((2 * ρ ^ m * ρ : NNReal)) ^ (-(ε / (2 * ((m : ℝ) + 1)))) ≤ ρ ^ (-ε) := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  set M : ℝ := (m : ℝ) + 1 with hM
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hMne : M ≠ 0 := by linarith
  have hexp : M * -(ε / (2 * M)) = -(ε / 2) := by field_simp
  rw [sqScaleN_rpow, hexp]
  have h2 : (2 : NNReal) ^ (-(ε / (2 * M))) ≤ 1 := by
    calc (2 : NNReal) ^ (-(ε / (2 * M))) ≤ (2 : NNReal) ^ (0 : ℝ) :=
          NNReal.rpow_le_rpow_of_exponent_le one_le_two
            (by have : (0:ℝ) < ε / (2 * M) := by positivity
                linarith)
      _ = 1 := NNReal.rpow_zero 2
  calc (6 : NNReal) * ((2 : NNReal) ^ (-(ε / (2 * M))) * ρ ^ (-(ε / 2)))
      ≤ 6 * (1 * ρ ^ (-(ε / 2))) := by gcongr
    _ = 6 * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (-(ε / 2))) := by
        rw [show (6 : NNReal) * ρ ^ (ε / 2) * (ρ ^ (-(ε / 2)) * ρ ^ (-(ε / 2)))
            = 6 * (ρ ^ (ε / 2) * ρ ^ (-(ε / 2))) * ρ ^ (-(ε / 2)) from by ring,
          ← NNReal.rpow_add hρne]
        simp
    _ ≤ 1 * (ρ ^ (-(ε / 2)) * ρ ^ (-(ε / 2))) := by gcongr
    _ = ρ ^ (-ε) := by
        rw [one_mul, ← NNReal.rpow_add hρne]
        congr 1
        ring

/-! ### The main theorem of Part II -/

set_option maxHeartbeats 2000000 in
/-- **The squeeze at depth `m`.**  If the cut `θ` satisfies `4 ≤ (m+1)θ` and `θ ≤ 1`, and
`4 ≤ m`, then `SmallCardCut θ γ` already gives the full estimate. -/
theorem katzTaoEstimate_of_smallCardCut_aux {γ θ : ℝ} (hγ : 0 ≤ γ) (_hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (m : ℕ) (hm4 : 4 ≤ m) (hmθ : 4 ≤ ((m : ℝ) + 1) * θ)
    (hsc : SmallCardCut.{v} θ γ) :
    Kakeya.KatzTaoEstimate.{v} Space3 γ := by
  classical
  have hn : Module.finrank ℝ Space3 = 3 := finrank_euclideanSpace_fin
  set C₀ : NNReal := Tube.card_le_of_densityIn_le.C 3 with hC₀def
  clear_value C₀
  have hC₀0 : (0 : ℝ) ≤ (C₀ : ℝ) := NNReal.coe_nonneg _
  have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  set M : ℝ := (m : ℝ) + 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  intro ε hε
  obtain ⟨η₁, hη₁0, hη₁1, hsm⟩ := hsc (ε / (2 * M)) (by positivity)
  refine ⟨η₁ / 2, by positivity, ?_⟩
  have hmap : Filter.Tendsto (fun ρ : NNReal => 2 * ρ ^ m * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun ρ : NNReal => 2 * ρ ^ m * ρ) := by fun_prop
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      simpa [zero_pow (by omega : m ≠ 0)] using hcont.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ0 : (0 : NNReal) < ρ := hρ
      exact Set.mem_Ioi.mpr (by positivity)
  filter_upwards [hmap.eventually hsm,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const
      (4 * C₀) 1 one_pos (p := 1) one_pos,
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const (12 * fatLoss) 1 one_pos
      (p := M * η₁ - η₁ / 2) (by nlinarith),
    Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_const 6 1 one_pos
      (p := ε / 2) (by positivity),
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num),
    self_mem_nhdsWithin] with ρ hδsm hcardbud hktbud haccbud hρhalf hρpos
  intro ι s T hball hKT hfull
  have hρ0 : (0 : NNReal) < ρ := hρpos
  have hρne : (ρ : NNReal) ≠ 0 := hρ0.ne'
  have hρ12 : ρ ≤ 1 / 2 := hρhalf.2.le
  have hρ1 : ρ ≤ 1 := le_trans hρ12 (by rw [← NNReal.coe_le_coe]; norm_num)
  have hρ0R : (0 : ℝ) < (ρ : ℝ) := hρ0
  have hρ1R : ((ρ : ℝ)) ≤ 1 := by exact_mod_cast hρ1
  have hρ12R : ((ρ : ℝ)) ≤ 1 / 2 := by
    have := NNReal.coe_le_coe.mpr hρ12
    simpa using this
  have hσ0 : (0 : NNReal) < ρ ^ m := by positivity
  have hσ1 : (ρ : NNReal) ^ m ≤ 1 := pow_le_one₀ (by positivity) hρ1
  have hδpos : (0 : NNReal) < 2 * ρ ^ m * ρ := by positivity
  have hδne : (2 * ρ ^ m * ρ : NNReal) ≠ 0 := hδpos.ne'
  have hδ16 : (2 * ρ ^ m * ρ : NNReal) ≤ 1 / 16 := by
    have hpm : (ρ : NNReal) ^ m ≤ (1 / 2 : NNReal) ^ m := by gcongr
    have hp4 : (1 / 2 : NNReal) ^ m ≤ (1 / 2 : NNReal) ^ 4 :=
      pow_le_pow_of_le_one (by positivity) (by rw [← NNReal.coe_le_coe]; norm_num) hm4
    have hpm4 : (ρ : NNReal) ^ m ≤ (1 / 2 : NNReal) ^ 4 := le_trans hpm hp4
    calc (2 * ρ ^ m * ρ : NNReal) ≤ 2 * ((1 / 2 : NNReal) ^ 4) * (1 / 2 : NNReal) := by
          gcongr
      _ = 1 / 16 := by norm_num
  have hδ1 : (2 * ρ ^ m * ρ : NNReal) ≤ 1 := by
    refine le_trans hδ16 ?_
    rw [← NNReal.coe_le_coe]; norm_num
  have hδ4 : ((2 * ρ ^ m * ρ : NNReal) : ℝ) ≤ 1 / 4 := by
    have h : ((2 * ρ ^ m * ρ : NNReal) : ℝ) ≤ ((1 / 16 : NNReal) : ℝ) := by exact_mod_cast hδ16
    simpa using le_trans h (by norm_num)
  -- the heavy cap
  obtain ⟨k, hk⟩ := exists_heavy_cap s T
  set s' : Finset ι := s.filter (fun i => capIndex (T i).direction = k) with hs'def
  have hs'sub : s' ⊆ s := Finset.filter_subset _ _
  have he : ‖capVec k‖ = 1 := norm_capVec k
  have hcap : ∀ i ∈ s', (1 : ℝ) / 2 ≤ (inner ℝ (capVec k) (T i).direction : ℝ) := by
    intro i hi
    have hmem := Finset.mem_filter.mp (hs'def ▸ hi)
    have hspec := capIndex_spec (T i).toTube.norm_direction
    rwa [hmem.2] at hspec
  have hball' : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    fun i hi => hball i (hs'sub hi)
  set U : ι → ShadedTube (2 * ρ ^ m * ρ) Space3 :=
    sqFamily hσ0 he (2 * ρ ^ m * ρ) T with hUdef
  have hH1 : ∀ i ∈ s', (U i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    sqFamily_carrier_subset_closedBall hσ0 hσ1 he hball' hδ4
  have hmaxs' : Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (ρ : ENNReal) ^ (-(η₁ / 2)) := le_trans (Kakeya.maxDensity_mono _ hs'sub) hKT
  have hH2 : ConvexSpaceBody.IsKatzTao s' (fun i => (U i).toConvexSpaceBody)
      (((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-η₁)) := by
    refine le_trans (sqFamily_maxDensity_le hn hσ0 hσ1 hρ1 he hcap hδ1) ?_
    refine le_trans (by gcongr : (fatLoss : ENNReal)
        * Kakeya.maxDensity s' (fun i => (T i).toConvexSpaceBody)
      ≤ (fatLoss : ENNReal) * (ρ : ENNReal) ^ (-(η₁ / 2))) ?_
    have hb := ENNReal.coe_le_coe.mpr (katzTao_budgetN hρ0 m hη₁1 hktbud)
    rwa [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hρne,
      ENNReal.coe_rpow_of_ne_zero hδne] at hb
  have hmass : (((6 : NNReal)⁻¹ : NNReal) : ENNReal)
        * ∑ i ∈ s, volume (T i).toShadedBody.shade
      ≤ ∑ i ∈ s', volume (T i).toShadedBody.shade := by
    rw [ENNReal.coe_inv (by norm_num : (6 : NNReal) ≠ 0),
      ENNReal.inv_mul_le_iff (by simp) (by simp)]
    simpa using hk
  have hfulls' : (6 : NNReal)⁻¹ * ρ ^ (η₁ / 2)
      ≤ ShadedBody.fullness s' (fun i => (T i).toShadedBody) := by
    refine le_trans ?_ (mul_fullness_le_of_subset hs'sub (fun i => (T i).toShadedBody) hmass)
    gcongr
  have hH3 : ShadedBody.fullness s' (fun i => (U i).toShadedBody)
      ≥ (2 * ρ ^ m * ρ : NNReal) ^ η₁ := by
    refine le_trans ?_ (sqFamily_le_fullness hn hσ0 hσ1 hρ1 he hcap hδ1)
    refine le_trans (fullness_budgetN hρ0 m hη₁1 hktbud) ?_
    rw [mul_inv, mul_assoc]
    gcongr
  -- the cardinality hypothesis, now at the cut `θ`
  have hH4 : ((s'.card : ℝ)) < ((2 * ρ ^ m * ρ : NNReal) : ℝ) ^ (-θ) := by
    have hdens : Kakeya.densityIn s' (fun i => ((T i).toTube).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≤ ((ρ : ENNReal))⁻¹ := by
      refine le_trans (Kakeya.le_maxDensity _ _ _) (le_trans hmaxs' ?_)
      have hρE : (ρ : ENNReal) ≤ 1 := by exact_mod_cast hρ1
      rw [show ((ρ : ENNReal))⁻¹ = (ρ : ENNReal) ^ (-1 : ℝ) by rw [ENNReal.rpow_neg_one]]
      exact ENNReal.rpow_le_rpow_of_exponent_ge hρE (by linarith)
    have hcard := Tube.card_le_of_densityIn_le (E := Space3) (s := s') hρne
      (T := fun i => (T i).toTube) hball' hdens
    rw [hn, ← hC₀def] at hcard
    have hzpN : (ρ : NNReal) ^ (-((3 : ℕ) - 1 : ℤ)) = (ρ ^ 2)⁻¹ := by
      rw [show (-((3 : ℕ) - 1 : ℤ)) = (-2 : ℤ) by norm_num, zpow_neg]
      norm_num
      rfl
    have hzp : ((ρ : ENNReal)) ^ (-((3 : ℕ) - 1 : ℤ))
        = (((ρ ^ 2 : NNReal)⁻¹ : NNReal) : ENNReal) := by
      rw [← ENNReal.coe_zpow hρne, hzpN]
    rw [hzp, show ((ρ : ENNReal))⁻¹ = (((ρ⁻¹ : NNReal)) : ENNReal) from
      (ENNReal.coe_inv hρne).symm, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
      ← ENNReal.coe_natCast] at hcard
    have hcardN : (s'.card : NNReal) ≤ C₀ * ρ⁻¹ * (ρ ^ 2)⁻¹ := ENNReal.coe_le_coe.mp hcard
    have hx3 : (0 : ℝ) < (ρ : ℝ) ^ 3 := by positivity
    have hx4 : (0 : ℝ) < (ρ : ℝ) ^ 4 := by positivity
    have hcardR : ((s'.card : ℝ)) ≤ (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ := by
      have h := NNReal.coe_le_coe.mpr hcardN
      rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_inv, NNReal.coe_pow] at h
      calc ((s'.card : ℝ)) = ((s'.card : NNReal) : ℝ) := by push_cast; ring
        _ ≤ (C₀ : ℝ) * ((ρ : ℝ))⁻¹ * (((ρ : ℝ)) ^ 2)⁻¹ := h
        _ = (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ := by field_simp
    have h4R : (4 : ℝ) * (C₀ : ℝ) * (ρ : ℝ) ≤ 1 := by
      have hb : (4 * C₀ * ρ : NNReal) ≤ 1 := by simpa using hcardbud
      have h := NNReal.coe_le_coe.mpr hb
      rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_one] at h
      simpa using h
    have h4R' : 4 * ((C₀ : ℝ) * (ρ : ℝ)) ≤ 1 := by
      have hre : 4 * ((C₀ : ℝ) * (ρ : ℝ)) = 4 * (C₀ : ℝ) * (ρ : ℝ) := by ring
      rw [hre]
      exact h4R
    have hstrict : (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ < (2 * (ρ : ℝ) ^ 4)⁻¹ := by
      rw [show (2 * (ρ : ℝ) ^ 4)⁻¹ = 1 / (2 * (ρ : ℝ) ^ 4) from (one_div _).symm,
        lt_div_iff₀ (by positivity)]
      have hre : (C₀ : ℝ) * ((ρ : ℝ) ^ 3)⁻¹ * (2 * (ρ : ℝ) ^ 4)
          = 2 * ((C₀ : ℝ) * (ρ : ℝ)) := by
        field_simp
      rw [hre]
      linarith only [h4R']
    have hcoe : ((2 * ρ ^ m * ρ : NNReal) : ℝ) = 2 * (ρ : ℝ) ^ (m + 1) := by
      push_cast
      rw [pow_succ]
      ring
    have hd0 : (0 : ℝ) < 2 * (ρ : ℝ) ^ (m + 1) := by positivity
    have hup : (2 * (ρ : ℝ) ^ (m + 1)) ^ θ ≤ 2 * (ρ : ℝ) ^ 4 := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast ((ρ : ℝ)) (m + 1), ← Real.rpow_mul hρ0R.le]
      have h2 : (2 : ℝ) ^ θ ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) one_le_two hθ1
        rwa [Real.rpow_one] at h
      have hp : ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ) ≤ (ρ : ℝ) ^ 4 := by
        rw [show ((ρ : ℝ) ^ 4) = ((ρ : ℝ)) ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast _ 4).symm]
        refine Real.rpow_le_rpow_of_exponent_ge hρ0R hρ1R ?_
        have hc : ((((m : ℕ) + 1 : ℕ) : ℝ)) = M := by rw [hMdef]; push_cast; ring
        rw [hc]
        push_cast
        linarith
      have hnn : (0 : ℝ) ≤ ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ) :=
        Real.rpow_nonneg hρ0R.le _
      calc (2 : ℝ) ^ θ * ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ)
          ≤ 2 * ((ρ : ℝ)) ^ ((((m : ℕ) + 1 : ℕ) : ℝ) * θ) := by
            exact mul_le_mul_of_nonneg_right h2 hnn
        _ ≤ 2 * (ρ : ℝ) ^ 4 := by
            exact mul_le_mul_of_nonneg_left hp (by norm_num)
    have hge : (2 * (ρ : ℝ) ^ 4)⁻¹ ≤ ((2 * ρ ^ m * ρ : NNReal) : ℝ) ^ (-θ) := by
      rw [hcoe, Real.rpow_neg hd0.le]
      have hpos : (0 : ℝ) < (2 * (ρ : ℝ) ^ (m + 1)) ^ θ := Real.rpow_pos_of_pos hd0 θ
      exact one_div_le_one_div_of_le hpos hup |>.trans_eq (by rw [one_div]) |>.trans_eq' (by
        rw [one_div])
    linarith
  -- apply the hypothesis at the squeezed scale
  have hconc := hδsm s' U hH1 hH2 hH3 hH4
  rw [sqFamily_sum_shade hσ0 hσ1 hρ1 he hcap le_rfl,
    sqFamily_iUnion_shade hσ0 hσ1 hρ1 he hcap le_rfl] at hconc
  have hJ0 : Kakeya.affineJacobian (sqA hσ0 he) ≠ 0 := Kakeya.affineJacobian_ne_zero _
  have hJt : Kakeya.affineJacobian (sqA hσ0 he) ≠ ⊤ := Kakeya.affineJacobian_ne_top _
  have hconc' : ∑ i ∈ s', volume (T i).shade
      ≤ ((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-(ε / (2 * M))) * (s'.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s', (T i).shade) := by
    rw [show ((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-(ε / (2 * M))) * (s'.card : ENNReal) ^ γ
          * (Kakeya.affineJacobian (sqA hσ0 he) * volume (⋃ i ∈ s', (T i).shade))
        = Kakeya.affineJacobian (sqA hσ0 he)
          * (((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-(ε / (2 * M)))
            * (s'.card : ENNReal) ^ γ * volume (⋃ i ∈ s', (T i).shade)) from by ring] at hconc
    exact (ENNReal.mul_le_mul_iff_right hJ0 hJt).mp hconc
  have hcardle : (s'.card : ENNReal) ^ γ ≤ (s.card : ENNReal) ^ γ := by
    have hle : ((s'.card : ENNReal)) ≤ (s.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hs'sub
    exact ENNReal.rpow_le_rpow hle hγ
  have hunionle : volume (⋃ i ∈ s', (T i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) :=
    measure_mono (Set.biUnion_subset_biUnion_left hs'sub)
  have hacc : (6 : ENNReal) * ((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-(ε / (2 * M)))
      ≤ (ρ : ENNReal) ^ (-ε) := by
    have hb := ENNReal.coe_le_coe.mpr (accuracy_budgetN hρ0 m hε haccbud)
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne,
      ENNReal.coe_rpow_of_ne_zero hρne] at hb
    simpa using hb
  calc ∑ i ∈ s, volume (T i).shade
      ≤ 6 * ∑ i ∈ s', volume (T i).shade := hk
    _ ≤ 6 * (((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-(ε / (2 * M)))
        * (s'.card : ENNReal) ^ γ * volume (⋃ i ∈ s', (T i).shade)) := by gcongr
    _ ≤ 6 * (((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-(ε / (2 * M)))
        * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)) := by gcongr
    _ = (6 * ((2 * ρ ^ m * ρ : NNReal) : ENNReal) ^ (-(ε / (2 * M))))
        * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade) := by ring
    _ ≤ (ρ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- **Every `β`-only cardinality cut is circular.**  For every `θ > 0`, `SmallCardCut θ γ`
already gives the full estimate. -/
theorem katzTaoEstimate_of_smallCardCut {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 < θ)
    (hsc : SmallCardCut.{v} θ γ) : Kakeya.KatzTaoEstimate.{v} Space3 γ := by
  classical
  set θ' : ℝ := min θ 1 with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ one_pos
  have hθ'1 : θ' ≤ 1 := min_le_right _ _
  have hsc' : SmallCardCut.{v} θ' γ := smallCardCut_mono (min_le_left _ _) hsc
  set m : ℕ := max 4 ⌈4 / θ'⌉₊ with hmdef
  have hm4 : 4 ≤ m := le_max_left _ _
  have hmθ : 4 ≤ ((m : ℝ) + 1) * θ' := by
    have h1 : (4 / θ' : ℝ) ≤ (⌈4 / θ'⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈4 / θ'⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_right 4 ⌈4 / θ'⌉₊
    have h3 : (4 / θ' : ℝ) * θ' = 4 := by field_simp
    nlinarith [hθ'0, h1, h2, h3]
  exact katzTaoEstimate_of_smallCardCut_aux hγ hθ'0 hθ'1 m hm4 hmθ hsc'

/-- The converse is the trivial direction: `SmallCardCut` only adds a hypothesis. -/
theorem smallCardCut_of_katzTaoEstimate {γ θ : ℝ}
    (h : Kakeya.KatzTaoEstimate.{v} Space3 γ) : SmallCardCut.{v} θ γ := by
  intro ε hε
  obtain ⟨η, hη0, hev⟩ := h ε hε
  refine ⟨min η 1, lt_min hη0 one_pos, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull _
  exact hδev s T hball
    (Kakeya.ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT)
    (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull)

/-- **The headline of Part II.**  At *every* cut, the small-cardinality case is the theorem. -/
theorem smallCardCut_iff_katzTaoEstimate {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 < θ) :
    SmallCardCut.{v} θ γ ↔ Kakeya.KatzTaoEstimate.{v} Space3 γ :=
  ⟨katzTaoEstimate_of_smallCardCut hγ hθ, smallCardCut_of_katzTaoEstimate⟩

/-- **No `β`-only threshold survives.**  Lowering the assembly's `δ^{-1}` — which is what a
smaller absolute accuracy `ε₀` in Theorem 7.3(B) would buy, by
`Kakeya.ML2Band.absoluteLossRoute_insufficient` — does not help at any positive `θ`. -/
theorem forall_cut_circular {γ : ℝ} (hγ : 0 ≤ γ) :
    ∀ θ > (0 : ℝ), (SmallCardCut.{v} θ γ ↔ Kakeya.KatzTaoEstimate.{v} Space3 γ) :=
  fun _ hθ => smallCardCut_iff_katzTaoEstimate hγ hθ

/-- The acceptance test, at every cut. -/
theorem producer_of_smallCardCut_is_producer_of_goal {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 < θ)
    (P : Prop) (h : P → SmallCardCut.{v} θ γ) :
    P → Kakeya.KatzTaoEstimate.{v} Space3 γ :=
  fun hp => katzTaoEstimate_of_smallCardCut hγ hθ (h hp)

end Cut

/-! ## Part III — what the GWZ route actually delivers, and where the residue is

`Kakeya.ML2Assembly.Dichotomy`'s **gain** alternative needs no cardinality hypothesis at all: it
converts through `Kakeya.ML2Assembly.card_le_rpow_neg_four` at the budget `4c ≤ g`.  Only the
**absolute-accuracy** alternative needs one, and it needs it precisely because the accuracy `ε₀`
is `β`-only while the goal's accuracy `ε` is arbitrary
(`Kakeya.ML2Band.absoluteLossRoute_insufficient`).

So the honest conclusion of the route is the *banded* estimate, and the residue is exactly the
band's complement — which Part II shows is the whole theorem, at every band. -/

section Banded

universe w

/-- `Kakeya.KatzTaoEstimate` restricted to families with `δ^{-θ} ≤ |𝕋|`. -/
def KatzTaoEstimateGE (θ γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ) ^ (-θ) ≤ (s.card : ℝ) →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

theorem katzTaoEstimateGE_of_katzTaoEstimate {γ θ : ℝ}
    (h : Kakeya.KatzTaoEstimate.{w} Space3 γ) : KatzTaoEstimateGE.{w} θ γ := by
  intro ε hε
  obtain ⟨η, hη0, hev⟩ := h ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hev] with δ hδev
  intro ι s T hball hKT hfull _
  exact hδev s T hball hKT hfull

/-- **The split.**  The banded estimate together with the band's complement is the estimate. -/
theorem katzTaoEstimate_of_GE_of_cut {γ θ : ℝ} (hGE : KatzTaoEstimateGE.{w} θ γ)
    (hcut : SmallCardCut.{w} θ γ) : Kakeya.KatzTaoEstimate.{w} Space3 γ := by
  intro ε hε
  obtain ⟨η, hη0, hev⟩ := hGE ε hε
  obtain ⟨η', hη'0, hη'1, hev'⟩ := hcut ε hε
  refine ⟨min η η', lt_min hη0 hη'0, ?_⟩
  filter_upwards [hev, hev', Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hδev hδev' hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull
  rcases lt_or_ge (s.card : ℝ) ((δ : ℝ) ^ (-θ)) with hlt | hge
  · exact hδev' s T hball
      (Kakeya.ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_right _ _) hKT)
      (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_right _ _) hfull) hlt
  · exact hδev s T hball
      (Kakeya.ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT)
      (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull) hge

/-- **The restructured reduction.**  `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` with
the `hsmall : SmallCard (β - c)` slot **deleted** and the conclusion banded instead.  Its
hypotheses are the dichotomy and the two `ε`-free budgets, and nothing else: this is exactly what
the GWZ route delivers, and it is *not* circular — `Kakeya.ML2Assembly.Dichotomy` is a statement
about families with `δ⁻¹ ≤ |𝕋|` and cannot, by its own shape, reach the band. -/
theorem katzTaoEstimateGE_sub_of_dichotomy {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : Kakeya.ML2Assembly.Dichotomy.{w} β (β / 2) g η) :
    KatzTaoEstimateGE.{w} 1 (β - c) := by
  intro ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hdich, Kakeya.ML2Assembly.eventually_card_thresholds] with δ hδdich hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull hcard
  have hge : (δ : ℝ)⁻¹ ≤ (s.card : ℝ) := by rwa [Real.rpow_neg_one] at hcard
  rcases hδdich s T hball hKT hfull hge with hmass | hmass
  · exact Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge hδ0 hδ1
      (V := fun i ↦ (T i).toShadedBody) (ε := ε) (ε₀ := β / 2) (γ := β - c)
      (by linarith) (by linarith) hge hmass
  · rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    have hcardle : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
      Kakeya.ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hKT
    have hcoef : (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) :=
      Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 4) hδ0 hδ1 hpos hc.le
        (by linarith) hcardle le_rfl
    calc ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := hmass
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c)
            * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- **Where the residue is.**  Once the banded estimate is in hand, what is left is exactly the
band's complement — and by Part II that is the estimate itself, at every band.  So banding the
*conclusion* does not by itself make the reduction non-circular: the band has to be carried by the
**consumer**, not discharged by the producer. -/
theorem residue_of_banded {γ θ : ℝ} (_hγ : 0 ≤ γ) (_hθ : 0 < θ)
    (hGE : KatzTaoEstimateGE.{w} θ γ) :
    (Kakeya.KatzTaoEstimate.{w} Space3 γ ↔ SmallCardCut.{w} θ γ) :=
  ⟨fun h => smallCardCut_of_katzTaoEstimate h, fun h => katzTaoEstimate_of_GE_of_cut hGE h⟩

end Banded

/-! ## Part IV — the `ε`-freeness trilemma, and what GWZ's branch (i) actually needs

GWZ Definition 3.4 puts the accuracy **inside** `K_KT`: `K_{KT}(β)` is *"for every `ε > 0` there
exist `η = η(ε,β)` and `δ₀ = δ₀(ε,β)` such that …"*.  Main Lemma 2's `ν = ν(β)` therefore sits
outside that `∀ ε`, and the protected Lean statement renders exactly that.

GWZ's proof of branch (i) reads Theorem 7.3(B) **at the outer `ε`** (*"Let `ε₁` and `δ₁` be the
output of Theorem 7.3(B) with `ε` as above"*), obtains `μ ≤ δ^{-ε}`, and closes because
`|𝕋|^{β-ν} ≥ 1`.  That step needs **no cardinality hypothesis** —
`Kakeya.ML2Squeeze.branchOne_closes_of_accuracy_le` below — but it makes `ε₁ = E ε`, hence
`ν ≤ η₁ ≤ ε₂ ≤ ε₁/5 = E ε/5`, an `ε`-dependent gain.  The published parenthesis *"(since `ε₁` and
`ϖ` depend only on `β`, `ε₂` depends only on `β`)"* is inconsistent with the sentence before it;
that is the typo Prof. Hong Wang identified.

Her repair reads 7.3(B) at a `β`-only accuracy `ε₀`.  That restores `ε`-freeness and forces a
`β`-only cardinality cut (`Kakeya.ML2Band.absoluteLossRoute_insufficient`), whose complement Part
II shows to be the theorem itself — at *every* cut.

The two horns are `Kakeya.ML2Squeeze.ml2_epsFree_horns`. -/

section Horns

variable {δ : ℝ}

/-- **GWZ's branch (i), at the outer accuracy.**  If Theorem 7.3(B) is read at an accuracy `a ≤ ε`
then `μ ≤ δ^{-a}` closes the goal for every nonempty family: only `1 ≤ |𝕋|` is used.  This is the
step that carries no cardinality hypothesis, and it is the step Prof. Wang's repair gives up. -/
theorem branchOne_closes_of_accuracy_le {a ε γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (haε : a ≤ ε) (hγ : 0 ≤ γ) {N : ℝ} (hN : 1 ≤ N) :
    δ ^ (-a) ≤ δ ^ (-ε) * N ^ γ := by
  have h1 : δ ^ (-a) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have h2 : (1 : ℝ) ≤ N ^ γ := Real.one_le_rpow hN hγ
  calc δ ^ (-a) ≤ δ ^ (-ε) := h1
    _ = δ ^ (-ε) * 1 := (mul_one _).symm
    _ ≤ δ ^ (-ε) * N ^ γ := by
        exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hδ0.le _)

/-- **The two horns of the `ε`-freeness trilemma.**

*First horn.*  If Theorem 7.3(B) is read at the outer accuracy — the published reading — then no
`ε`-free gain `ν > 0` survives the spine chain: `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`,
under the harmless normalisation `E a ≤ a` (one may always shrink a Katz--Tao exponent).

*Second horn.*  If it is read at a `β`-only accuracy, the every-scale branch closes only above a
`β`-only cardinality cut `θ > 0`, and at every such `θ` the complementary case is the full
estimate.

There is no third alternative inside this architecture: the gain alternative of
`Kakeya.ML2Assembly.Dichotomy` needs no cut (`Kakeya.ML2Squeeze.katzTaoEstimateGE_sub_of_dichotomy`
uses it at every cardinality), so the cut is forced by, and only by, the absolute-accuracy
alternative. -/
theorem ml2_epsFree_horns {E : ℝ → ℝ} (hE : ∀ a : ℝ, 0 < a → E a ≤ a)
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} {ν : ℝ} (hν : 0 < ν) {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 < θ) :
    (¬ ∀ ε : ℝ, 0 < ε → ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
        Kakeya.ML2Spine.IsSpine β ϖ (E ε) gain dens ε₂ e N η ∧ ν ≤ η 1)
      ∧ (SmallCardCut.{v} θ γ ↔ Kakeya.KatzTaoEstimate.{v} Space3 γ) :=
  ⟨fun h => Kakeya.ML2Spine.not_epsFree_of_outerAccuracy' hE hν h,
    smallCardCut_iff_katzTaoEstimate hγ hθ⟩

end Horns

/-! ## Part V — the replacement: a gain-only core needs no cut at all

GWZ Lemma 9.1's conclusion is a genuine `δ`-**gain**, `μ ≤ δ^ν |𝕋|^β`, with no accuracy in it;
`Kakeya.ML2Assembly.Dichotomy`'s alternative (ii) has the same shape.  A gain converts to the goal
at **every** cardinality, through the crude bound `|𝕋| ≤ δ^{-4}`
(`Kakeya.ML2Assembly.card_le_rpow_neg_four`) at the `ε`-free budget `4c ≤ g`.  So the cardinality
split is forced by, and only by, the *other* alternative — the absolute-accuracy bound
`μ ≤ δ^{-ε₀}` coming from Theorem 7.3(B) read at a `β`-only accuracy.

`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnly` is the statement of that: a geometric core
that always produces a gain gives Main Lemma 2's drop outright, with no `SmallCard`, no
`KatzTaoEstimateGE`, and no case split.  Together with
`Kakeya.ML2Squeeze.forall_cut_circular` this is the whole diagnosis:

* every-scale branch as a **gain** — no cut, no circularity;
* every-scale branch as an **`ε`-free accuracy** — a `β`-only cut is forced
  (`Kakeya.OmegaAssessment.oneParam_fixed_loss_forces_card`), and every `β`-only cut is the
  theorem;
* every-scale branch as an **`ε`-dependent accuracy** — no cut, but the gain is `ε`-dependent
  (`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`). -/

section GainOnly

universe w'

/-- **RETRACTED — this predicate is FALSE for `g > 0`; see Part VII,
`Kakeya.ML2Squeeze.not_gainOnly`.**

`Kakeya.ML2Assembly.Dichotomy` with the absolute-accuracy alternative **and** the cardinality
hypothesis both deleted: the geometric core always delivers a genuine `δ`-gain.  There is no `ε`
in this predicate — it has the shape of GWZ Lemma 9.1's own conclusion. -/
def GainOnly (β g η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w'} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- **RETRACTED as a route — the hypothesis is unsatisfiable; see Part VII,
`Kakeya.ML2Squeeze.not_gainOnly`.**  The theorem is true and is kept as the record.

**A gain-only core gives Main Lemma 2's drop with no cardinality split.**

Compare `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`: the `hsmall : SmallCard (β - c)`
slot is gone, and so is the `2 * c ≤ β` budget, which existed only to pay for the
absolute-accuracy alternative. -/
theorem katzTaoEstimate_sub_of_gainOnly {β g η c : ℝ}
    (hc : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hgain : GainOnly.{w'} β g η) :
    Kakeya.KatzTaoEstimate.{w'} Space3 (β - c) := by
  intro ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hgain, Kakeya.ML2Assembly.eventually_card_thresholds] with δ hδgain hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull
  have hmass := hδgain s T hball hKT hfull
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]
    simp
  have hcardle : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
    Kakeya.ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hKT
  have hcoef : (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) :=
    Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 4) hδ0 hδ1 hpos hc.le
      (by linarith) hcardle le_rfl
  calc ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := hmass
    _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c)
          * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- The gain-only core is not vacuous as a *shape*: `Kakeya.ML2Assembly.Dichotomy`'s second
alternative has exactly it, and dropping the first alternative and the cardinality hypothesis is
the only change. -/
theorem gainOnly_of_dichotomy_second {β g η : ℝ}
    (h : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w'} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade)) :
    GainOnly.{w'} β g η := h

end GainOnly

/-! ## Part VI — the bridge from GWZ Lemma 9.1 to `GainOnly`

GWZ Lemma 9.1's conclusion, `μ(𝕋,Y) ≤ δ^ν |𝕋|^β`, already has the gain shape, so the *currency*
conversion is free (`Kakeya.ML2Squeeze.gainOnly_iff_gainOnlyMult`), and the finish is
`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnlyMult`: a core that produces 9.1's conclusion for
every admissible family gives Main Lemma 2's drop, with **no** cardinality split.

What 9.1 does *not* give is the two extra hypotheses it carries on the family — the uniformity
witness and the `ρ`-tube count.  Both are named below, transcribed verbatim, and the count is the
obstruction: `Kakeya.ML2Squeeze.scaleCount_forces_band` shows that 9.1's third bullet, read at
`ρ = δ^{1-ϖ}` against any essentially-distinct cover at that scale, **already forces
`δ⁻¹ ≤ |𝕋|`**.  So Lemma 9.1 applied *directly* to the given family fires only on the band and
delivers `Kakeya.ML2Squeeze.KatzTaoEstimateGE 1`, which
`Kakeya.ML2Squeeze.residue_of_banded` and `Kakeya.ML2Squeeze.forall_cut_circular` show to be
circular.  **The count must be supplied at a rescaled scale** — which is exactly what GWZ's
two-scale split does, and exactly what R1 is for. -/

section Bridge

universe w2

/-- **RETRACTED — FALSE for `g > 0`; see `Kakeya.ML2Squeeze.not_gainOnlyMult`.**

`Kakeya.ML2Squeeze.GainOnly` in GWZ Lemma 9.1's own currency: the conclusion is the
multiplicity bound `μ ≤ δ^g |𝕋|^β` that Lemma 9.1 states verbatim. -/
def GainOnlyMult (β g η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w2} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β

/-- **The currency conversion is free.**  `ShadedBody.multiplicity_le_iff` is an unconditional
`iff`, so the mass form and the multiplicity form of a gain are the same statement. -/
theorem gainOnly_iff_gainOnlyMult {β g η : ℝ} :
    GainOnly.{w2} β g η ↔ GainOnlyMult.{w2} β g η := by
  constructor
  · intro h
    filter_upwards [h] with δ hδ
    intro ι s T hball hKT hfull
    exact (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mpr
      (hδ s T hball hKT hfull)
  · intro h
    filter_upwards [h] with δ hδ
    intro ι s T hball hKT hfull
    exact (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mp
      (hδ s T hball hKT hfull)

/-- **RETRACTED as a target — the hypothesis is unsatisfiable; see
`Kakeya.ML2Squeeze.not_gainOnlyMult`.**  Kept as the record.

**The finish, in Lemma 9.1's currency.** -/
theorem katzTaoEstimate_sub_of_gainOnlyMult {β g η c : ℝ}
    (hc : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hgain : GainOnlyMult.{w2} β g η) :
    Kakeya.KatzTaoEstimate.{w2} Space3 (β - c) :=
  katzTaoEstimate_sub_of_gainOnly hc hη0 hη1 hg (gainOnly_iff_gainOnlyMult.mpr hgain)

/-! ### The two hypotheses Lemma 9.1 carries that `GainOnly` does not supply -/

/-- GWZ Lemma 9.1's uniformity hypothesis, as a predicate on one family; transcribed verbatim
from `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`: Definition 2.1/2.2 on the standard grid
at a constant `1 ≤ C ≤ δ^{-η}`. The exponent is a parameter because the predicate is stated on a bare
family, before `η` is fixed. -/
def UniformWitness (η : ℝ) {δ : NNReal} {ι : Type w2} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) : Prop :=
  ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
    Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)

/-- GWZ Lemma 9.1's third bullet as a predicate on one family: at each scale
of the window there exists an essentially distinct, all-used `ρ`-tube family
of cardinality at least `ρ^{-2-ζ}`. -/
def ScaleCount (ϖ ζ : ℝ) {δ : NNReal} {ι : Type w2} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) : Prop :=
  ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
    ∃ (κ : Type w2) (tρ : Finset κ) (Tρ : κ → Tube ρ Space3),
      (tρ : Set κ).Pairwise
        (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
      (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
      (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)

/-- **GWZ Lemma 9.1's conclusion, at fixed parameters**, transcribed verbatim from
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` and stated as a hypothesis, because that
theorem is currently `sorryAx`-tainted through its leaf `exists_setup_caseSideData`.  When that
leaf closes, every consumer of `Lemma91Body` goes clean at once. -/
def Lemma91Body (β ϖ ζ ν η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w2} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∀ i ∈ s, (T i).toTube.IsCentred) →
      UniformWitness.{w2} η s T →
      Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ScaleCount.{w2} ϖ ζ s T →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β

/-- **The conditional bridge.**  Lemma 9.1 gives `GainOnlyMult` on exactly the families that
satisfy its two extra hypotheses; the residue is those two hypotheses and nothing else. -/
theorem gainOnlyMult_of_lemma91Body {β ϖ ζ ν η : ℝ} (h91 : Lemma91Body.{w2} β ϖ ζ ν η)
    (hside : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w2} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ i ∈ s, (T i).toTube.IsCentred) ∧ UniformWitness.{w2} η s T ∧ ScaleCount.{w2} ϖ ζ s T) :
    GainOnlyMult.{w2} β ν η := by
  filter_upwards [h91, hside] with δ h91δ hsideδ
  intro ι s T hball hKT hfull
  obtain ⟨hcen, huni, hcount⟩ := hsideδ s T hball hKT hfull
  exact h91δ s T hball hcen huni hKT hfull hcount

/-- **The count clause already forces the band, up to the cover-comparison constant.**  At the
scale `ρ = δ^{1-ϖ}` of the window (or `ρ = δ` when `ϖ < 0`), GWZ Lemma 9.1's third bullet supplies
an essentially distinct all-used `ρ`-tube family with at least `ρ^{-2-ζ} ≥ δ⁻¹` members, and
`Tube.card_le_mul_card_of_chordCover` against the trivial cover `Tube.rescale (T i) ρ` bounds any
such family by `Tube.coverCountLoss 3 · |𝕋|`.  Hence `δ⁻¹ ≤ C |𝕋|` with `C = Tube.coverCountLoss 3`.

The bare `δ⁻¹ ≤ |𝕋|` of the earlier `∀`-over-covers rendering of the bullet does not survive the
/6 repair (at `ϖ = 1/2`, `ζ = 0` there is no slack to absorb `C`); its content is kept,
independently of `ScaleCount`, in `Kakeya.ML2Band.not_scaleCount_of_card_lt_inv`.

So the second half of `Kakeya.ML2Squeeze.gainOnlyMult_of_lemma91Body`'s residue is **not** a
condition one may hope to verify for every admissible family: it fails on every family below the
band `|𝕋| < δ⁻¹/C`, and by `Kakeya.ML2Squeeze.forall_cut_circular` those are among the families
that carry the theorem. -/
theorem scaleCount_forces_band {ϖ ζ : ℝ} (hϖ : ϖ ≤ 1 / 2) (hζ : 0 ≤ ζ) {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ι : Type w2} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (hcount : ScaleCount.{w2} ϖ ζ s T) :
    (δ : ℝ)⁻¹ ≤ (Tube.coverCountLoss 3 : ℝ) * (s.card : ℝ) := by
  have hfr : Module.finrank ℝ Space3 = 3 := by simp
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  -- the scale at which the bullet is read: `δ^{1-ϖ}` if `0 ≤ ϖ`, else `δ` itself
  obtain ⟨ρ, hρmem, hδρ, hρ1, hρ2⟩ : ∃ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) ∧
      δ ≤ ρ ∧ ρ ≤ 1 ∧ (δ : ℝ)⁻¹ ≤ (ρ : ℝ) ^ (-2 - ζ) := by
    rcases le_or_gt 0 ϖ with hϖ0 | hϖ0
    · refine ⟨δ ^ (1 - ϖ), ⟨le_rfl, NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)⟩,
        ?_, NNReal.rpow_le_one hδ1 (by linarith), ?_⟩
      · calc δ = δ ^ (1 : ℝ) := (NNReal.rpow_one δ).symm
          _ ≤ δ ^ (1 - ϖ) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      · rw [NNReal.coe_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hδR.le]
        exact Real.rpow_le_rpow_of_exponent_ge hδR hδ1R (by nlinarith)
    · refine ⟨δ, ⟨?_, ?_⟩, le_rfl, hδ1, ?_⟩
      · calc δ ^ (1 - ϖ) ≤ δ ^ (1 : ℝ) :=
              NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
          _ = δ := NNReal.rpow_one δ
      · calc δ = δ ^ (1 : ℝ) := (NNReal.rpow_one δ).symm
          _ ≤ δ ^ ϖ := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      · rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_ge hδR hδ1R (by linarith)
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ hρmem
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  -- ED ∧ all-used ⟹ `|tρ| ≤ C |𝕋|`, against the trivial cover by the rescaled tubes themselves
  have hcmp := Tube.card_le_mul_card_of_chordCover (E := Space3) hρ0 hρ1 (K := 1) le_rfl
    (fun i => (T i).toConvexSpaceBody) s tρ Tρ s (fun i => (T i).toTube.rescale ρ)
    (fun i _ => by simpa using Tube.exists_chord_of_shadedTube (T i)) hED hused
    (fun i hi => ⟨i, hi, by
      have h := Tube.rescale_le_rescale_of_radius_le (T i).toTube hδρ
      rwa [Tube.toConvexSpaceBody_rescale_self] at h⟩)
  rw [hfr] at hcmp
  calc (δ : ℝ)⁻¹ ≤ (ρ : ℝ) ^ (-2 - ζ) := hρ2
    _ ≤ (tρ.card : ℝ) := hcard
    _ ≤ (Tube.coverCountLoss 3 : ℝ) * (s.card : ℝ) := hcmp

/-- The contrapositive, in the form the reduction meets it: **below the band `|𝕋| < δ⁻¹/C`,
Lemma 9.1's own hypothesis is false**, so 9.1 cannot be the source of the gain there. -/
theorem not_scaleCount_of_card_lt_delta_inv {ϖ ζ : ℝ} (hϖ : ϖ ≤ 1 / 2) (hζ : 0 ≤ ζ)
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ι : Type w2} (s : Finset ι)
    (T : ι → ShadedTube δ Space3)
    (hlt : (Tube.coverCountLoss 3 : ℝ) * (s.card : ℝ) < (δ : ℝ)⁻¹) :
    ¬ ScaleCount.{w2} ϖ ζ s T :=
  fun hcount =>
    absurd (scaleCount_forces_band hϖ hζ hδ0 hδ1 s T hcount) (not_le.mpr hlt)

/-! ### The chain, and the fidelity compatibility on Lemma 9.1 -/

/-- **The whole chain, conditionally on GWZ Lemma 9.1.**  Given 9.1 at parameters `(β,ϖ,ζ,ν,η)`
and a producer for its two side conditions, Main Lemma 2's drop follows — with no cardinality
split, no `SmallCard`, and no `KatzTaoEstimateGE`.  The `ε`-free budget is `4c ≤ ν`, and `ν` is
Lemma 9.1's own gain, which carries no `ε`. -/
theorem katzTaoEstimate_sub_of_lemma91Body {β ϖ ζ ν η c : ℝ}
    (hc : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ ν)
    (h91 : Lemma91Body.{w2} β ϖ ζ ν η)
    (hside : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w2} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ i ∈ s, (T i).toTube.IsCentred) ∧ UniformWitness.{w2} η s T ∧ ScaleCount.{w2} ϖ ζ s T) :
    Kakeya.KatzTaoEstimate.{w2} Space3 (β - c) :=
  katzTaoEstimate_sub_of_gainOnlyMult hc hη0 hη1 hg (gainOnlyMult_of_lemma91Body h91 hside)

/-- **Fidelity compatibility on GWZ Lemma 9.1.**  `Kakeya.ML2Squeeze.Lemma91Body` is
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`'s body verbatim; if that theorem's statement
drifts by one binder, this declaration stops compiling.

**This is the one declaration in this file that is deliberately not axiom-clean**: it *quotes*
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, which is currently `sorryAx`-tainted through
its remaining leaf `Kakeya.VeryNotSticky.exists_setup_caseSideData`.
Nothing else in this file depends on it — every other declaration is stated conditionally on
`Lemma91Body` — so when that leaf closes the whole chain goes clean with no edit here. -/
theorem lemma91Body_of_lemma91 {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ),
      Kakeya.KatzTaoEstimate.{w2} Space3 β →
      Kakeya.FrostmanEstimate.{w2} Space3 β →
      Lemma91Body.{w2} β ϖ ζ ν η :=
  Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1

/-! ### The missing piece, named

`Kakeya.ML2Squeeze.gainOnlyMult_of_lemma91Body` reduces `GainOnly` to Lemma 9.1's two side
conditions, and `Kakeya.ML2Squeeze.not_scaleCount_of_card_lt_delta_inv` shows the second of them
**fails on every family below the band** `|𝕋| < δ⁻¹/C`.  That is not a defect of the bridge: it is
the correct
statement of where Lemma 9.1 lives.  In GWZ §9, Lemma 9.1 is applied only inside the *window*
branch, to a rescaled family for which the count is supplied by the two-scale structure; the other
branch — the every-scale branch — is closed by Theorem 7.3(B), and that is the branch that
produces an *accuracy* rather than a gain, hence the cardinality cut.

So the single missing input is the **upgrade of the every-scale branch from an accuracy to a
gain**.  `Kakeya.ML2Squeeze.GainDichotomy` names it: it is `Kakeya.ML2Assembly.Dichotomy` with its
first alternative `μ ≤ δ^{-ε₀}` replaced by a gain `μ ≤ δ^{g₁}|𝕋|^β`, and with the cardinality
hypothesis deleted — that hypothesis existed only to convert the accuracy. -/

/-- **RETRACTED — FALSE under the budget of `katzTaoEstimate_sub_of_gainDichotomy`; see
`Kakeya.ML2Squeeze.not_gainDichotomy_of_budget`.**

**The target.**  Both alternatives of the dividing-scales dichotomy as gains. -/
def GainDichotomy (β g₁ g₂ η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w2} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ g₁ * (s.card : ENNReal) ^ β)
        ∨ (ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ g₂ * (s.card : ENNReal) ^ β)

/-- A gain-only dichotomy gives `GainOnlyMult` at the smaller of the two gains. -/
theorem gainOnlyMult_of_gainDichotomy {β g₁ g₂ η : ℝ} (h : GainDichotomy.{w2} β g₁ g₂ η) :
    GainOnlyMult.{w2} β (min g₁ g₂) η := by
  filter_upwards [h, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1.le
  rcases hδ s T hball hKT hfull with hg | hg
  · refine hg.trans ?_
    have hstep : (δ : ENNReal) ^ g₁ ≤ (δ : ENNReal) ^ (min g₁ g₂) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (min_le_left _ _)
    exact mul_le_mul' hstep le_rfl
  · refine hg.trans ?_
    have hstep : (δ : ENNReal) ^ g₂ ≤ (δ : ENNReal) ^ (min g₁ g₂) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (min_le_right _ _)
    exact mul_le_mul' hstep le_rfl

/-- **RETRACTED as a route — the hypothesis is unsatisfiable under this very budget; see
`Kakeya.ML2Squeeze.not_gainDichotomy_of_budget`.**  Kept as the record.

**Main Lemma 2 from the gain-only dichotomy.** -/
theorem katzTaoEstimate_sub_of_gainDichotomy {β g₁ g₂ η c : ℝ}
    (hc : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ min g₁ g₂)
    (h : GainDichotomy.{w2} β g₁ g₂ η) :
    Kakeya.KatzTaoEstimate.{w2} Space3 (β - c) :=
  katzTaoEstimate_sub_of_gainOnlyMult hc hη0 hη1 hg (gainOnlyMult_of_gainDichotomy h)

end Bridge

/-! ## Part VII — CORRECTION: `GainOnly` is **false**, and the third arm of the filter

**This part retracts the reading of Part V.**  `Kakeya.ML2Squeeze.GainOnly` and
`Kakeya.ML2Squeeze.GainDichotomy` are **inconsistent**, so
`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnly`,
`katzTaoEstimate_sub_of_gainOnlyMult` and `katzTaoEstimate_sub_of_gainDichotomy` — all true
theorems — have hypotheses that no core can supply.  They are kept, with this cross-reference, as
the record of a closed column.

The mechanism is independent of every loss budget and survives deleting the accuracy.  A single
fully shaded `δ`-tube meets **every** hypothesis those predicates impose — ball containment,
`Δ_max ≤ δ^{-η}` (a singleton has `Δ_max ≤ 1`), and `λ ≥ δ^η` (a singleton is fully shaded, so
`λ = 1`) — and for it `∑|Y| = |⋃ Y| ∈ (0,∞)` and `|𝕋| = 1`.  So any conclusion of the shape
`∑|Y| ≤ F(δ)·|𝕋|^β·|⋃ Y|` forces `1 ≤ F(δ)`.  A gain has `F(δ) = δ^{g} < 1`.

Stated once, for arbitrary `F`, this is `Kakeya.ML2Squeeze.one_le_of_massBound`: **the third arm of
the acceptance test**.  Its two corollaries are `not_gainOnly` and `not_gainDichotomy_of_budget`,
the latter under exactly the budget of `katzTaoEstimate_sub_of_gainDichotomy`.

The error was mine, and it was avoidable: the `μ ≥ 1` floor is recorded in this very file's Part IV
discussion of why the *gain* alternative of `Kakeya.ML2Assembly.Dichotomy` cannot cover small
families.  I applied it to the dichotomy's second alternative and then failed to apply it to
`GainOnly`, which is that alternative with the cardinality clause deleted. -/

section Refutation

universe w3

/-- **The single-tube witness.**  For every `δ ∈ (0, 1/2)` and every `η ≥ 0` there is a family
of `δ`-tubes in `B₁` with **one** member, satisfying `Δ_max ≤ δ^{-η}` and `λ ≥ δ^η`, whose shade
mass equals its shaded-union volume and is positive and finite.

Nothing about the geometry of tube families is used beyond `Tube.le_volume` (the carrier has
positive volume) and compactness (it has finite volume).  Built here rather than imported, so that
this refutation of my own construction is independent of any other file. -/
theorem exists_admissible_singleton {η : ℝ} (hη : 0 ≤ η) {δ : NNReal} (hδ0 : 0 < δ)
    (hδhalf : (δ : ℝ) < 1 / 2) :
    ∃ T : PUnit.{w3 + 1} → ShadedTube δ Space3,
      (∀ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}),
          (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1) ∧
        ConvexSpaceBody.IsKatzTao ({PUnit.unit} : Finset PUnit.{w3 + 1})
            (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) ∧
          ShadedBody.fullness ({PUnit.unit} : Finset PUnit.{w3 + 1})
              (fun i ↦ (T i).toShadedBody) ≥ δ ^ η ∧
            (∑ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}), volume (T i).shade)
                = volume (⋃ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}), (T i).shade) ∧
              volume (⋃ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}), (T i).shade) ≠ 0 ∧
                volume (⋃ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}), (T i).shade) ≠ ⊤ := by
  classical
  set e : Space3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by simp [hedef]
  set W : Tube δ Space3 := Tube.ofMidpointDirection δ 0 e he with hWdef
  set T : PUnit.{w3 + 1} → ShadedTube δ Space3 := fun _ =>
    { toTube := W
      shade := W.carrier
      measurableSet_shade := W.isCompact'.isClosed.measurableSet
      shade_subset := subset_rfl } with hTdef
  set s : Finset PUnit.{w3 + 1} := {PUnit.unit} with hsdef
  have hshade : (T PUnit.unit).shade = (T PUnit.unit).carrier := rfl
  have hcarr : (T PUnit.unit).carrier = W.carrier := rfl
  have hv0 : volume (T PUnit.unit).carrier ≠ 0 := by
    rw [hcarr]
    have hlow := Tube.le_volume (E := Space3) W
    have hn : Module.finrank ℝ Space3 = 3 := finrank_euclideanSpace_fin
    rw [hn] at hlow
    intro hzero
    rw [hzero, le_zero_iff, mul_eq_zero] at hlow
    rcases hlow with hc | hd
    · exact absurd (ENNReal.coe_eq_zero.mp hc) (Tube.le_volume.c_pos 3).ne'
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp hd) (by
        simpa using (ENNReal.coe_eq_zero.not.mpr hδ0.ne'))
  have hvt : volume (T PUnit.unit).carrier ≠ ⊤ := by
    rw [hcarr]
    exact W.isCompact'.measure_ne_top
  have hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1 := by
    intro i _
    have hmid : _root_.midpoint ℝ W.x W.y = (0 : Space3) := by
      show _root_.midpoint ℝ ((0 : Space3) - (1 / 2 : ℝ) • e) ((0 : Space3) + (1 / 2 : ℝ) • e) = 0
      rw [midpoint_eq_smul_add]
      module
    have h := Kakeya.Tube.carrier_subset_closedBall_midpoint Space3 W
    rw [hmid] at h
    refine (show (T i).carrier = W.carrier from rfl) ▸ h.trans ?_
    exact Metric.closedBall_subset_closedBall (by linarith)
  have hδ1E : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
    rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
    exact ENNReal.rpow_le_one (by exact_mod_cast (le_of_lt (lt_trans hδhalf (by norm_num)))) hη
  have hmax1 : Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ 1 := by
    rw [Kakeya.maxDensity_le_iff]
    intro K
    rw [Kakeya.densityIn_le_iff, hsdef]
    by_cases hle : (T PUnit.unit).toConvexSpaceBody ≤ K
    · rw [Finset.filter_singleton, if_pos hle, Finset.sum_singleton, one_mul]
      exact measure_mono hle
    · rw [Finset.filter_singleton, if_neg hle]
      simp
  have hKT : ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
      ((δ : ENNReal) ^ (-η)) := le_trans hmax1 hδ1E
  have hfull1 : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) = 1 := by
    rw [← ENNReal.coe_inj, ShadedBody.coe_fullness]
    unfold ShadedBody.fullness'
    rw [hsdef]
    simp only [Finset.sum_singleton]
    show volume (T PUnit.unit).shade / volume (T PUnit.unit).carrier = ((1 : NNReal) : ENNReal)
    rw [hshade, ENNReal.div_self hv0 hvt]
    simp
  have hδη1 : (δ : NNReal) ^ η ≤ 1 := by
    refine NNReal.rpow_le_one ?_ hη
    have : (δ : ℝ) < 1 := lt_trans hδhalf (by norm_num)
    exact_mod_cast this.le
  have hfull : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η := by
    rw [hfull1]; exact hδη1
  have hunionv : volume (⋃ i ∈ s, (T i).shade) = volume (T PUnit.unit).carrier := by
    rw [hsdef]
    simp [hshade, Set.iUnion_const]
  have hsumv : (∑ i ∈ s, volume (T i).shade) = volume (⋃ i ∈ s, (T i).shade) := by
    rw [hunionv, hsdef, Finset.sum_singleton, hshade]
  exact ⟨T, hball, hKT, hfull, hsumv, by rw [hunionv]; exact hv0, by rw [hunionv]; exact hvt⟩

/-- **The single-tube consistency test — the third arm of the acceptance test.**

Any obligation of the shape *"for every admissible family, `∑|Y| ≤ F(δ)·|𝕋|^β·|⋃Y|`"* forces
`1 ≤ F(δ)` at some `δ ∈ (0, 1/2)`.  Consequently a candidate whose conclusion carries **no factor
`≥ 1`** — in particular any pure `δ`-gain — is refuted on sight unless it also carries a
cardinality lower bound. -/
theorem one_le_of_massBound {η β : ℝ} (hη : 0 ≤ η) (F : NNReal → ENNReal)
    (h : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w3} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        ∑ i ∈ s, volume (T i).shade
          ≤ F δ * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade)) :
    ∃ δ : NNReal, 0 < δ ∧ (δ : ℝ) < 1 / 2 ∧ 1 ≤ F δ := by
  classical
  obtain ⟨δ, hδP, hδmem⟩ :=
    (h.and (Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num))).exists
  obtain ⟨hδ0, hδhalf⟩ := hδmem
  have hδhalfR : (δ : ℝ) < 1 / 2 := by
    have := NNReal.coe_lt_coe.mpr hδhalf
    simpa using this
  obtain ⟨T, hball, hKT, hfull, hsumv, hv0, hvt⟩ :=
    exists_admissible_singleton.{w3} hη hδ0 hδhalfR
  refine ⟨δ, hδ0, hδhalfR, ?_⟩
  have hconc := hδP ({PUnit.unit} : Finset PUnit.{w3 + 1}) T hball hKT hfull
  have hcard : (((({PUnit.unit} : Finset PUnit.{w3 + 1}).card : ℕ) : ENNReal)) ^ β = 1 := by
    rw [Finset.card_singleton]
    simp
  rw [hsumv, hcard, mul_one] at hconc
  have hone : (1 : ENNReal) * volume (⋃ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}), (T i).shade)
      ≤ F δ * volume (⋃ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}), (T i).shade) := by
    rw [one_mul]; exact hconc
  exact (ENNReal.mul_le_mul_iff_left hv0 hvt).mp hone

/-! ### The corollaries: the gain column is empty -/

/-- **`Kakeya.ML2Squeeze.GainOnly` is false.**  Independently re-derived here, pinned to the
declaration it refutes. -/
theorem not_gainOnly {β g η : ℝ} (hη : 0 ≤ η) (hg : 0 < g) : ¬ GainOnly.{w3} β g η := by
  intro h
  obtain ⟨δ, hδ0, hδhalf, hone⟩ :=
    one_le_of_massBound.{w3} (β := β) hη (fun d => (d : ENNReal) ^ g) h
  have hδ1 : (δ : ENNReal) < 1 := by
    have : (δ : ℝ) < 1 := lt_trans hδhalf (by norm_num)
    exact_mod_cast this
  exact absurd hone (not_le.mpr (ENNReal.rpow_lt_one hδ1 hg))

/-- The same, in Lemma 9.1's currency. -/
theorem not_gainOnlyMult {β g η : ℝ} (hη : 0 ≤ η) (hg : 0 < g) :
    ¬ GainOnlyMult.{w3} β g η :=
  fun h => not_gainOnly.{w3} hη hg (gainOnly_iff_gainOnlyMult.mpr h)

/-- **`Kakeya.ML2Squeeze.GainDichotomy` is false under exactly the budget of
`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainDichotomy`.**  So that theorem, though true, can
never fire. -/
theorem not_gainDichotomy_of_budget {β g₁ g₂ η c : ℝ} (hη : 0 ≤ η) (hc : 0 < c)
    (hg : 4 * c ≤ min g₁ g₂) : ¬ GainDichotomy.{w3} β g₁ g₂ η :=
  fun h => not_gainOnlyMult.{w3} hη (by linarith) (gainOnlyMult_of_gainDichotomy.{w3} h)

/-- **No device can produce a cardinality floor unconditionally.**  For every `θ > 0` it is false
that every admissible family satisfies `δ^{-θ} ≤ |𝕋|`; the one fully shaded tube has `|𝕋| = 1`.

So a "floor-producing" device — broad--narrow, bilinearity — cannot produce the floor for *all*
admissible families.  It can only produce it under extra structure, and the families without that
structure are then a residue; if that residue is delimited by a cardinality cut it is circular by
`Kakeya.ML2Squeeze.forall_cut_circular`. -/
theorem no_unconditional_card_floor {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 < θ) :
    ¬ ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type w3} (s : Finset ι) (T : ι → ShadedTube δ Space3),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
          (δ : ℝ) ^ (-θ) ≤ (s.card : ℝ) := by
  intro h
  obtain ⟨δ, hδP, hδmem⟩ :=
    (h.and (Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num))).exists
  obtain ⟨hδ0, hδhalf⟩ := hδmem
  have hδhalfR : (δ : ℝ) < 1 / 2 := by
    have := NNReal.coe_lt_coe.mpr hδhalf
    simpa using this
  obtain ⟨T, hball, hKT, hfull, _, _, _⟩ := exists_admissible_singleton.{w3} hη hδ0 hδhalfR
  have hone := hδP ({PUnit.unit} : Finset PUnit.{w3 + 1}) T hball hKT hfull
  rw [Finset.card_singleton] at hone
  have hδ0R : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδ1R : (δ : ℝ) < 1 := lt_trans hδhalfR (by norm_num)
  have hbig : (1 : ℝ) < (δ : ℝ) ^ (-θ) := by
    rw [show (1 : ℝ) = (δ : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
    exact Real.rpow_lt_rpow_of_exponent_gt hδ0R hδ1R (by linarith)
  simp only [Nat.cast_one] at hone
  linarith

/-! ### Candidate 1: the Ω-budget, and its own trilemma

`Kakeya.KatzTaoEstimateOmega β ω` replaces the accuracy factor `δ^{-ε}` by `δ^{-ω-ε}`, with the
budget `ω` quantified **before** `ε`.  It **passes the third arm**: at `|𝕋| = 1` its conclusion
factor is `δ^{-ω-ε} ≥ 1`, so `Kakeya.ML2Squeeze.one_le_of_massBound` does not touch it.  That is
the real content of the donor branch's *"branch (i) of the assembly below is unconditional"*.

But the budget must still dominate the accuracy at which Theorem 7.3(B) is read, and that
reproduces the `ε`-trilemma one level up.

* **Horn A** — if `ε₀` is fixed before the budget (`β`-only), then at every budget `ω < ε₀` the
  every-scale bound `μ ≤ δ^{-ε₀}` fails to give the `ω`-form's goal at the single tube, for every
  `ε < ε₀ - ω` (`Kakeya.ML2Squeeze.omega_branchOne_needs_budget`).  So the branch is *not*
  unconditional at small budget and needs a cardinality floor — which
  `Kakeya.ML2Squeeze.no_unconditional_card_floor` says nothing supplies unconditionally and
  `Kakeya.ML2Squeeze.forall_cut_circular` says is circular once assumed.
* **Horn B** — horn A therefore forces `ε₀ ≤ ω`, and then the spine gives
  `g ≤ E(ε₀)/25 ≤ ω/25`, so no positive drop is uniform in the budget
  (`Kakeya.ML2Squeeze.omega_no_uniform_drop`).  That is
  `Kakeya.OmegaAssessment.no_uniform_floor_of_starved_drop` explained rather than observed: the
  drop is starved *because* the branch only closes above the budget.

The descent `ω → 0` needs exactly the uniform floor horn B denies.  So the Ω-budget removes the
cardinality split (which the gain column could not) but pays for it in the drop. -/

/-- **Horn A.**  At a budget below the accuracy, the `ω`-form's every-scale branch fails at the
single tube (`|𝕋| = 1`, so the cardinality factor is `1`). -/
theorem omega_branchOne_needs_budget {δ ε₀ ω ε β' : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hlt : ω + ε < ε₀) :
    δ ^ (-ω - ε) * (1 : ℝ) ^ β' < δ ^ (-ε₀) := by
  rw [Real.one_rpow, mul_one]
  exact Real.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 (by linarith)

/-- **Horn B.**  With the accuracy tied to the budget, the spine chain admits no budget-uniform
positive drop.  This is `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'` read with the budget in
place of the accuracy — the same theorem, one level up. -/
theorem omega_no_uniform_drop {E : ℝ → ℝ} (hE : ∀ a : ℝ, 0 < a → E a ≤ a)
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} {g : ℝ} (hg : 0 < g)
    (h : ∀ ω : ℝ, 0 < ω → ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
      Kakeya.ML2Spine.IsSpine β ϖ (E ω) gain dens ε₂ e N η ∧ g ≤ η 1) : False :=
  Kakeya.ML2Spine.not_epsFree_of_outerAccuracy' hE hg h

/-! ### Candidate 2: a device that *produces* the cardinality floor

`Kakeya.ML2Squeeze.no_unconditional_card_floor` is the whole of what can be said cheaply, and it is
decisive about the *shape*: no device produces `δ^{-θ} ≤ |𝕋|` for **all** admissible families,
because the single fully shaded tube is admissible and has `|𝕋| = 1`.  A floor-producing device
must therefore be conditional on extra structure (bilinearity, broadness, very-not-stickiness), and
the families lacking that structure are a residue.  If that residue is delimited by a cardinality
cut, `Kakeya.ML2Squeeze.forall_cut_circular` closes it; if it is handled by a rescaling induction,
 already prices that induction at `b_N(1-a)` — a fixed power of `δ` —
unless the planar case is discharged.

This is why the two candidates are not symmetric: the Ω-budget's open slot is a *bound on a
function* (`exists_uniformDrop`), while candidate 2's open slot is a *geometric theorem about a
structured subclass*, and the unstructured complement is the residue that has closed three times
now. -/


/-! ### Where the wall actually is: the spine dominates the drop

Collecting the three columns, the every-scale branch can deliver its bound in exactly three shapes,
and each is now closed:

* a **gain** `μ ≤ δ^{g}|𝕋|^β` — **false**, by `Kakeya.ML2Squeeze.not_gainOnly` (single tube);
* an **accuracy** `μ ≤ δ^{-ε₀}` with `ε₀` fixed before `ε` — needs a cardinality floor at the
  single tube (`Kakeya.ML2Squeeze.omega_branchOne_needs_budget` at `ω = 0`), and every floor is
  **circular** (`Kakeya.ML2Squeeze.forall_cut_circular`);
* an **accuracy at the outer `ε`** — closes with only `1 ≤ |𝕋|`
  (`Kakeya.ML2Squeeze.branchOne_closes_of_accuracy_le`), but the spine then forces `ν ≤ ε₁/25`.

The third item is the only one that is not a refutation, and its obstruction is **structural, not
geometric**: `Kakeya.ML2Spine.IsSpine`'s own fields chain `ν ≤ η₁ ≤ e ≤ ε₁/25`, so the drop is
dominated by the every-scale exponent whatever that exponent is.  That domination — not any
property of `E`, and not any budget — is the binding constraint.

`Kakeya.ML2Squeeze.not_dropDominationFree` states it, and it is stronger and cleaner than
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`: no hypothesis on `E` at all. -/

/-- The property that would make the outer-`ε` reading work: a positive drop available at
*every* every-scale exponent `ε₁`, i.e. a drop not dominated by that exponent. -/
def DropDominationFree (β ϖ : ℝ) (gain dens : ℝ → ℝ) : Prop :=
  ∃ ν > (0 : ℝ), ∀ ε₁ : ℝ, 0 < ε₁ → ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
    Kakeya.ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧ ν ≤ η 1

/-- **The spine architecture forbids it, with no hypothesis on Theorem 7.3(B) at all.**

`IsSpine.rung_le_div` gives `η 1 ≤ e` and `IsSpine.div_le_everyScale` gives `e ≤ ε₁/25`, so
`ν ≤ ε₁/25` for every `ε₁ > 0`; taking `ε₁ = 12 ν` contradicts `ν > 0`.  Breaking this domination
is the one move the three columns leave open. -/
theorem not_dropDominationFree {β ϖ : ℝ} {gain dens : ℝ → ℝ} :
    ¬ DropDominationFree β ϖ gain dens := by
  rintro ⟨ν, hν, h⟩
  obtain ⟨ε₂, e, N, η, hspine, hle⟩ := h (12 * ν) (by linarith)
  have h1 : η 1 ≤ e := hspine.rung_le_div 1
  have h2 : e ≤ (12 * ν) / 25 := hspine.div_le_everyScale
  linarith


/-! ### Is the domination ours or GWZ's?  **GWZ's.**

`Kakeya.ML2Spine.IsSpine` is this development's own bookkeeping structure — it carries **no**
blueprint `\lean{}` tag, so it renders no labelled statement.  That makes "the fraction is
self-imposed" a live hypothesis, and this development has imposed tightest-available readings
before.  It is not the case here, and the check is short: two of GWZ §9's own sentences already
give the fraction, quoted verbatim from `blueprint/src/GWZAdapted/section9.tex`.

> *"Define `N = ⌈25/ε₂²⌉`, and let `η ≤ η₁ ≤ … ≤ η_N ≤ ε₂` be a sequence of numbers to be chosen
> later."*

> *"If Conclusion (i) holds, then (provided we select `ε₂ ≤ ε₁/5`) we have that `𝕋` is `δ^{-ε₁}`
> Katz–Tao at every scale."*

> *"The quantity `ν` from the conclusion of Main Lemma 2 will be selected small compared to `η₁`"*
> … *"in order to prove establish (mugoalml2quant) with `ν = η₁`."*

So `ν ≤ η₁ ≤ ε₂ ≤ ε₁/5` **in GWZ's own text**, with no field of this development involved.
`Kakeya.ML2Squeeze.GWZSpineChain` transcribes exactly those three, and
`Kakeya.ML2Squeeze.not_gwzDropDominationFree` shows they already forbid an `ε₁`-free drop.

Where the development *does* tighten: GWZ's rung ceiling is `ε₂`, and `IsSpine.rung_top` sets the
top rung to `e = 1/√N ≤ ε₂/5` instead (documented in `SpineParams.lean` as *"replacing `ε₂` by `e`
in every denominator makes each constraint strictly harder"*).  That is a factor `5`, and
`Kakeya.ML2Squeeze.gwzSpineChain_of_isSpine` shows the tighter chain **implies** GWZ's, so
`Kakeya.ML2Squeeze.not_dropDominationFree` is not an artefact of the tighter reading: relaxing all
the way back to the paper still gives `ν ≤ ε₁/5`, and `not_gwzDropDominationFree` still fires.

*Filter note.*  `Kakeya.ML2Squeeze.one_le_of_massBound` does not apply to anything in this section
and that is a certification, not an omission: these are scalar statements about the parameter
chain, with no per-family conclusion of the shape `∑|Y| ≤ F(δ)·|𝕋|^β·|⋃Y|` for it to test. -/

/-- **GWZ §9's parameter chain**, transcribed from the three quoted sentences and nothing else:
`ν ≤ η₁`, `η₁ ≤ ε₂`, `ε₂ ≤ ε₁/5`.  No `IsSpine` field appears. -/
def GWZSpineChain (ν η₁ ε₂ ε₁ : ℝ) : Prop :=
  ν ≤ η₁ ∧ η₁ ≤ ε₂ ∧ ε₂ ≤ ε₁ / 5

theorem gwzSpineChain_le {ν η₁ ε₂ ε₁ : ℝ} (h : GWZSpineChain ν η₁ ε₂ ε₁) : ν ≤ ε₁ / 5 := by
  obtain ⟨h1, h2, h3⟩ := h
  linarith

/-- **The domination is GWZ's, not this development's.**  From the paper's own three sentences,
no positive drop is available at every every-scale exponent. -/
theorem not_gwzDropDominationFree :
    ¬ ∃ ν : ℝ, 0 < ν ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ∃ η₁ ε₂ : ℝ, GWZSpineChain ν η₁ ε₂ ε₁ := by
  rintro ⟨ν, hν, h⟩
  obtain ⟨η₁, ε₂, hchain⟩ := h (4 * ν) (by linarith)
  have := gwzSpineChain_le hchain
  linarith

/-- **The development's chain implies the paper's.**  So `Kakeya.ML2Squeeze.not_dropDominationFree`
is a consequence of GWZ's constraints and not of the factor-`5` tightening in `IsSpine.rung_top`. -/
theorem gwzSpineChain_of_isSpine {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : Kakeya.ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) {ν : ℝ} (hν : ν ≤ η 1) :
    GWZSpineChain ν (η 1) ε₂ ε₁ :=
  ⟨hν, le_trans (h.rung_le_div 1) h.div_le_eps₂, h.eps₂_le_everyScale⟩

/-- **The `ε`-indexed family of drops does not assemble.**  This is the shape of the failure at the
level of the statement rather than the chain: GWZ Definition 3.4 puts the accuracy *inside*
`K_KT`, so `K_KT(β − ν)` requires a single real `ν` fixed before `∀ ε`; a route delivering only
`ν(ε) ≤ ε/5` supplies no such `ν`. -/
theorem no_uniform_drop_of_fraction {νf : ℝ → ℝ} (hf : ∀ ε : ℝ, 0 < ε → νf ε ≤ ε / 5)
    {ν : ℝ} (hν : 0 < ν) (h : ∀ ε : ℝ, 0 < ε → ν ≤ νf ε) : False := by
  have h1 := h (4 * ν) (by linarith)
  have h2 := hf (4 * ν) (by linarith)
  linarith


/-! ### Does the single-tube witness cover the *de-duplicated* count?  **Yes.**

's carried-cardinality induction transports by `R`-fold duplication, which multiplies `|𝕋|`
and `Δ_max` by the same `R`; so the transport-invariant quantity is the ratio `|𝕋| / Δ_max`, and
CAR's next target is a lower bound on *that* rather than on `|𝕋|`.  The worry is that
`Kakeya.ML2Squeeze.no_unconditional_card_floor` might be blind to it, because a
duplication-generated witness has `|𝕋|` large while `|𝕋|/Δ_max` is not.

It is not blind, and the reason is that the witness is at the **opposite** extreme: the single
fully shaded tube is duplication-*minimal*.  It has `|𝕋| = 1` and `Δ_max = 1` — the upper bound
because a singleton family's density in any test body is at most one, the lower bound by testing
the density at the member's own body — so the ratio is `1`, and `δ^{-θ} ≤ 1` fails for every
`θ > 0`.  `Kakeya.ML2Squeeze.no_unconditional_dedup_floor`.

So **that candidate stays shut**: no device produces a lower bound on `|𝕋|/Δ_max` for all
admissible families either.  As with `no_unconditional_card_floor`, this constrains the *shape* of
a floor-producing device — it must be conditional on structure — and says nothing against the
carried-band re-encoding itself, whose transport is between families that already exist.

*Filter note, taking the correction.*  Filter 1 cannot discriminate at the top of the reduction,
since `Kakeya.ML2Squeeze.forall_cut_circular` makes every sufficient condition satisfy it by the
letter; the discriminator there is whether **both directions compile**.  The results of this file
that sit at the top are stated as biconditionals for exactly that reason
(`smallCardCut_iff_katzTaoEstimate`, `smallCard_iff_katzTaoEstimate`,
`gainOnly_iff_gainOnlyMult`), and `Kakeya.ML2Squeeze.one_le_of_massBound` is unaffected. -/

/-- A singleton family's density in any test body is at most one. -/
theorem maxDensity_le_one_of_singleton {ι : Type w3} [DecidableEq ι] (i₀ : ι)
    (W : ι → ConvexSpaceBody Space3) : Kakeya.maxDensity {i₀} W ≤ 1 := by
  rw [Kakeya.maxDensity_le_iff]
  intro K
  rw [Kakeya.densityIn_le_iff]
  by_cases hle : W i₀ ≤ K
  · rw [Finset.filter_singleton, if_pos hle, Finset.sum_singleton, one_mul]
    exact measure_mono hle
  · rw [Finset.filter_singleton, if_neg hle]
    simp

/-- Any family with a member of positive finite volume has `Δ_max ≥ 1`: test the density at that
member's own body. -/
theorem one_le_maxDensity_of_member {ι : Type w3} {s : Finset ι} {W : ι → ConvexSpaceBody Space3}
    {i₀ : ι} (hi₀ : i₀ ∈ s) (h0 : volume (W i₀).carrier ≠ 0)
    (ht : volume (W i₀).carrier ≠ ⊤) : 1 ≤ Kakeya.maxDensity s W := by
  refine le_trans ?_ (Kakeya.le_maxDensity s W (W i₀))
  have h := Kakeya.le_densityIn s W (W i₀) hi₀ (le_refl (W i₀))
  rwa [ENNReal.div_self h0 ht] at h

/-- **The de-duplicated floor fails too.**  No device produces `δ^{-θ} ≤ |𝕋| / Δ_max(𝕋)` for all
admissible families: the single fully shaded tube has `|𝕋| = 1` and `Δ_max = 1`. -/
theorem no_unconditional_dedup_floor {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 < θ) :
    ¬ ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type w3} (s : Finset ι) (T : ι → ShadedTube δ Space3),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
          (δ : ℝ) ^ (-θ)
            ≤ (s.card : ℝ)
              / (Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal := by
  classical
  intro h
  obtain ⟨δ, hδP, hδmem⟩ :=
    (h.and (Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num))).exists
  obtain ⟨hδ0, hδhalf⟩ := hδmem
  have hδhalfR : (δ : ℝ) < 1 / 2 := by
    have := NNReal.coe_lt_coe.mpr hδhalf
    simpa using this
  obtain ⟨T, hball, hKT, hfull, _hsumv, hv0, _hvt⟩ :=
    exists_admissible_singleton.{w3} hη hδ0 hδhalfR
  -- the witness has `Δ_max = 1`
  have hsub : (⋃ i ∈ ({PUnit.unit} : Finset PUnit.{w3 + 1}), (T i).shade)
      ⊆ (T PUnit.unit).carrier := by
    refine Set.iUnion₂_subset fun i _ => ?_
    rw [Subsingleton.elim i PUnit.unit]
    exact (T PUnit.unit).shade_subset
  have hcarr0 : volume (T PUnit.unit).carrier ≠ 0 := fun hz =>
    hv0 (measure_mono_null hsub hz)
  have hcarrT : volume (T PUnit.unit).carrier ≠ ⊤ :=
    (T PUnit.unit).isCompact'.measure_ne_top
  have hge : (1 : ENNReal)
      ≤ Kakeya.maxDensity ({PUnit.unit} : Finset PUnit.{w3 + 1})
          (fun i ↦ (T i).toConvexSpaceBody) :=
    one_le_maxDensity_of_member (Finset.mem_singleton_self _) hcarr0 hcarrT
  have hle : Kakeya.maxDensity ({PUnit.unit} : Finset PUnit.{w3 + 1})
      (fun i ↦ (T i).toConvexSpaceBody) ≤ 1 :=
    maxDensity_le_one_of_singleton PUnit.unit (fun i ↦ (T i).toConvexSpaceBody)
  have hone : Kakeya.maxDensity ({PUnit.unit} : Finset PUnit.{w3 + 1})
      (fun i ↦ (T i).toConvexSpaceBody) = 1 := le_antisymm hle hge
  have hbound := hδP ({PUnit.unit} : Finset PUnit.{w3 + 1}) T hball hKT hfull
  rw [hone, Finset.card_singleton] at hbound
  simp only [ENNReal.toReal_one, Nat.cast_one, div_one] at hbound
  have hδ0R : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδ1R : (δ : ℝ) < 1 := lt_trans hδhalfR (by norm_num)
  have hbig : (1 : ℝ) < (δ : ℝ) ^ (-θ) := by
    rw [show (1 : ℝ) = (δ : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
    exact Real.rpow_lt_rpow_of_exponent_gt hδ0R hδ1R (by linarith)
  linarith


end Refutation

end Kakeya.ML2Squeeze

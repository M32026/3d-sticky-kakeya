/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.AffineMap
public import Kakeya.Multiplicity
public import Kakeya.Thickness.HasThicknesses
public import Kakeya.Thickness.Projection

/-!
# The rescaling `L_B` of the plank presentation

Throughout the non-slab case, `L_B(y) = r₁⁻¹ (y - ctr)` is the affine change of variables
carrying the `r₁`-ball `B = B̄(ctr, r₁)` onto the closed unit ball. It is a homothety of centre
`ctr` and ratio `r₁⁻¹` *followed by a translation*, so for `r₁ = 1` it is a translation and not
a homothety and the homothety lemmas of `Kakeya.Homothety` do not apply to it directly. This
file records `L_B` as a bundled affine equivalence `Kakeya.VeryNotSticky.plankRescale` and
transports across it everything the plank presentation `lem:ml2plankpresentation` needs:

* distances, balls and volumes (blueprint `lem:ml2plankRescalingMap`,
  `lem:ml2plankRescalingBalls`, `lem:ml2plankRescalingVolume`);
* affine thicknesses (blueprint `lem:ml2plankEthicknessScaling`,
  `lem:ml2plankThicknessTransport`);
* essential distinctness, multiplicity, `c`-refinements and `Δ_max` (blueprint
  `lem:ml2plankEssDistinctTransport`, `lem:ml2plankMultTransport`,
  `lem:ml2plankRefinementPullback`, `lem:ml2plankCRefinementCongrCarrier`,
  `lem:ml2plankRefinementTransport`, `lem:ml2plankFamilyInTransport`,
  `lem:ml2plankMaxDensityTransport`);
* local volume estimates (blueprint `lem:volumeInterClosedBallEqBall`,
  `lem:ml2plankRescalingBridge`).

Only three properties of `L_B` are ever used: it is a bijection of `ℝ³`, it multiplies every
distance by exactly `r₁⁻¹`, and it multiplies every volume by exactly `r₁⁻³`.
-/

@[expose] public section

open Finset MeasureTheory Metric Set ShadedBody
open scoped NNReal Pointwise Real

noncomputable section

namespace Kakeya.VeryNotSticky

/-- Shorthand for the ambient space of the non-slab case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-! ### The change of variables -/

/-- **The rescaling `L_B`** of the plank presentation: the affine equivalence
`L_B(y) = r₁⁻¹ • (y - ctr)` of `ℝ³`, the homothety of centre `ctr` and ratio `r₁⁻¹` followed by
the translation by `-ctr`. It carries `B̄(ctr, r₁)` onto `B̄(0, 1)`, and its inverse is
`z ↦ ctr + r₁ • z`. -/
def plankRescale (ctr : E₃) {r₁ : ℝ} (hr₁ : r₁ ≠ 0) : E₃ ≃ᵃ[ℝ] E₃ :=
  (AffineEquiv.vaddConst ℝ ctr).symm.trans
    (AffineEquiv.homothetyUnitsMulHom (0 : E₃) (Units.mk0 r₁ hr₁)⁻¹)

variable (ctr : E₃) {r₁ : ℝ}

/-- The rescaling in coordinates. -/
@[simp]
theorem plankRescale_apply (hr₁ : r₁ ≠ 0) (y : E₃) :
    plankRescale ctr hr₁ y = r₁⁻¹ • (y - ctr) := by
  unfold plankRescale
  simp only [AffineEquiv.trans_apply, AffineEquiv.vaddConst_symm_apply]
  simp only [AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  simp only [vsub_eq_sub, vadd_eq_add, sub_zero, add_zero]

/-- The inverse rescaling in coordinates. -/
@[simp]
theorem plankRescale_symm_apply (hr₁ : r₁ ≠ 0) (z : E₃) :
    (plankRescale ctr hr₁).symm z = ctr + r₁ • z := by
  rw [eq_comm, ← AffineEquiv.apply_eq_iff_eq_symm_apply]
  rw [plankRescale_apply]
  rw [add_sub_cancel_left]
  rw [inv_smul_smul₀ hr₁]

/-- The rescaling is continuous. -/
theorem plankRescale_continuous (hr₁ : r₁ ≠ 0) : Continuous (plankRescale ctr hr₁) := by
  exact (plankRescale ctr hr₁).continuous_of_finiteDimensional

/-- The inverse rescaling is continuous. -/
theorem plankRescale_symm_continuous (hr₁ : r₁ ≠ 0) :
    Continuous (plankRescale ctr hr₁).symm := by
  exact (plankRescale ctr hr₁).symm.continuous_of_finiteDimensional

/-- The rescaling is a measurable embedding, which is what
`ShadedBody.affineImage` needs to keep the image of a shading measurable. -/
theorem plankRescale_measurableEmbedding (hr₁ : r₁ ≠ 0) :
    MeasurableEmbedding (plankRescale ctr hr₁) := by
  exact (plankRescale ctr hr₁).toContinuousAffineEquiv.toHomeomorph.measurableEmbedding

/-- The inverse rescaling is a measurable embedding. -/
theorem plankRescale_symm_measurableEmbedding (hr₁ : r₁ ≠ 0) :
    MeasurableEmbedding (plankRescale ctr hr₁).symm := by
  exact (plankRescale ctr hr₁).symm.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding

/-- **The rescaling is a similarity of `ℝ³` of ratio `r₁⁻¹`** (blueprint
`lem:ml2plankRescalingMap`).

Clause (i) of the blueprint statement — that `L_B` is a continuous affine bijection with
continuous affine inverse `z ↦ ctr + r₁ z` — is carried by the *type* of
`Kakeya.VeryNotSticky.plankRescale` together with
`Kakeya.VeryNotSticky.plankRescale_symm_apply`,
`Kakeya.VeryNotSticky.plankRescale_continuous` and
`Kakeya.VeryNotSticky.plankRescale_symm_continuous`. What remains is clause (ii), the exact
distance scaling, from which both Lipschitz bounds follow. -/
theorem plankRescale_dist (hr₁ : 0 < r₁) (y z : E₃) :
    dist (plankRescale ctr hr₁.ne' y) (plankRescale ctr hr₁.ne' z) = r₁⁻¹ * dist y z := by
  rw [plankRescale_apply, plankRescale_apply, dist_eq_norm]
  rw [← smul_sub]
  rw [show (y - ctr) - (z - ctr) = y - z by abel]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr₁)]
  rfl

/-- `L_B` is Lipschitz with constant `r₁⁻¹`. -/
theorem lipschitzWith_plankRescale (hr₁ : 0 < r₁) :
    LipschitzWith (Real.toNNReal r₁⁻¹) (plankRescale ctr hr₁.ne') := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  calc
    dist (plankRescale ctr hr₁.ne' y) (plankRescale ctr hr₁.ne' z) = r₁⁻¹ * dist y z :=
      plankRescale_dist ctr hr₁ y z
    _ ≤ (Real.toNNReal r₁⁻¹ : ℝ) * dist y z := by
      rw [Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hr₁))]

/-- `L_B⁻¹` is Lipschitz with constant `r₁`. -/
theorem lipschitzWith_plankRescale_symm (hr₁ : 0 < r₁) :
    LipschitzWith (Real.toNNReal r₁) (plankRescale ctr hr₁.ne').symm := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  calc
    dist ((plankRescale ctr hr₁.ne').symm y) ((plankRescale ctr hr₁.ne').symm z)
        = ‖r₁ • (y - z)‖ := by
          rw [plankRescale_symm_apply, plankRescale_symm_apply, dist_eq_norm]
          rw [add_sub_add_left_eq_sub]
          rw [← smul_sub]
    _ = |r₁| * ‖y - z‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = r₁ * ‖y - z‖ := by rw [abs_of_pos hr₁]
    _ = r₁ * dist y z := by rw [dist_eq_norm]
    _ ≤ (Real.toNNReal r₁ : ℝ) * dist y z := by
          rw [Real.coe_toNNReal _ hr₁.le]

/-- **The rescaling carries closed balls onto closed balls** (blueprint
`lem:ml2plankRescalingBalls`).

Degenerate radii are covered, both sides being empty for `t < 0`. In particular
`L_B(B̄(ctr, r₁)) = B̄(0, 1)`, which is the sense in which `L_B` "takes `B` to `B₁`". -/
theorem plankRescale_image_closedBall (hr₁ : 0 < r₁) (x : E₃) (t : ℝ) :
    plankRescale ctr hr₁.ne' '' closedBall x t
      = closedBall (plankRescale ctr hr₁.ne' x) (t / r₁) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_closedBall] at hy ⊢
    rw [le_div_iff₀ hr₁, plankRescale_dist ctr hr₁ y x]
    calc
      (r₁⁻¹ * dist y x) * r₁ = dist y x := by
        rw [mul_comm (r₁⁻¹ * dist y x), ← mul_assoc, mul_inv_cancel₀ hr₁.ne', one_mul]
      _ ≤ t := hy
  · intro hz
    refine ⟨(plankRescale ctr hr₁.ne').symm z, ?_, ?_⟩
    · rw [mem_closedBall] at hz ⊢
      have hdist : dist z (plankRescale ctr hr₁.ne' x)
          = r₁⁻¹ * dist ((plankRescale ctr hr₁.ne').symm z) x := by
        simpa only [(plankRescale ctr hr₁.ne').apply_symm_apply z] using
          (plankRescale_dist ctr hr₁ ((plankRescale ctr hr₁.ne').symm z) x)
      have hmid : r₁⁻¹ * dist ((plankRescale ctr hr₁.ne').symm z) x ≤ t / r₁ := by
        simpa only [hdist] using hz
      have hm : (r₁⁻¹ * dist ((plankRescale ctr hr₁.ne').symm z) x) * r₁
          ≤ (t / r₁) * r₁ :=
        mul_le_mul_of_nonneg_right hmid hr₁.le
      have hL : (r₁⁻¹ * dist ((plankRescale ctr hr₁.ne').symm z) x) * r₁
          = dist ((plankRescale ctr hr₁.ne').symm z) x := by
        rw [mul_comm (r₁⁻¹ * dist ((plankRescale ctr hr₁.ne').symm z) x), ← mul_assoc,
          mul_inv_cancel₀ hr₁.ne', one_mul]
      have hR : (t / r₁) * r₁ = t := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hr₁.ne', mul_one]
      simpa only [hL, hR] using hm
    · exact (plankRescale ctr hr₁.ne').apply_symm_apply z

/-- **The rescaling carries open balls onto open balls** (blueprint
`lem:ml2plankRescalingBalls`). -/
theorem plankRescale_image_ball (hr₁ : 0 < r₁) (x : E₃) (t : ℝ) :
    plankRescale ctr hr₁.ne' '' ball x t = ball (plankRescale ctr hr₁.ne' x) (t / r₁) := by
  set L : E₃ ≃ᵃ[ℝ] E₃ := plankRescale ctr hr₁.ne'
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball] at hy ⊢
    rw [dist_comm] at hy ⊢
    rw [plankRescale_dist ctr hr₁ x y]
    rw [div_eq_inv_mul]
    exact mul_lt_mul_of_pos_left hy (inv_pos.mpr hr₁)
  · intro hz
    use L.symm z
    constructor
    · rw [mem_ball] at hz ⊢
      rw [dist_comm] at hz
      have hd : dist (L x) z = r₁⁻¹ * dist (L.symm z) x := by
        have hw : dist z (L x) = r₁⁻¹ * dist (L.symm z) x := by
          calc
            dist z (L x) = dist (L (L.symm z)) (L x) := by rw [L.apply_symm_apply]
            _ = r₁⁻¹ * dist (L.symm z) x := plankRescale_dist ctr hr₁ (L.symm z) x
        simpa [dist_comm] using hw
      rw [hd] at hz
      rw [div_eq_inv_mul] at hz
      exact (mul_lt_mul_iff_of_pos_left (inv_pos.mpr hr₁)).mp hz
    · exact L.apply_symm_apply z

/-- **The inverse rescaling carries closed balls onto closed balls** (blueprint
`lem:ml2plankRescalingBalls`). -/
theorem plankRescale_symm_image_closedBall (hr₁ : 0 < r₁) (x : E₃) (t : ℝ) :
    (plankRescale ctr hr₁.ne').symm '' closedBall x t
      = closedBall ((plankRescale ctr hr₁.ne').symm x) (r₁ * t) := by
  ext z
  simp_rw [mem_image, mem_closedBall]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hdist : dist ((plankRescale ctr hr₁.ne').symm y) ((plankRescale ctr hr₁.ne').symm x)
        = r₁ * dist y x := by
      calc
        dist ((plankRescale ctr hr₁.ne').symm y) ((plankRescale ctr hr₁.ne').symm x)
            = ‖r₁ • (y - x)‖ := by
              rw [plankRescale_symm_apply, plankRescale_symm_apply, dist_eq_norm]
              rw [add_sub_add_left_eq_sub]
              rw [← smul_sub]
        _ = |r₁| * ‖y - x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = r₁ * ‖y - x‖ := by rw [abs_of_pos hr₁]
        _ = r₁ * dist y x := by rw [dist_eq_norm]
    rw [hdist]
    exact mul_le_mul_of_nonneg_left hy hr₁.le
  · intro hz
    refine ⟨plankRescale ctr hr₁.ne' z, ?_, ?_⟩
    · have hdist : dist (plankRescale ctr hr₁.ne' z) x
          = r₁⁻¹ * dist z ((plankRescale ctr hr₁.ne').symm x) := by
        calc
          dist (plankRescale ctr hr₁.ne' z) x
              = dist (plankRescale ctr hr₁.ne' z)
                  (plankRescale ctr hr₁.ne' ((plankRescale ctr hr₁.ne').symm x)) := by
                rw [(plankRescale ctr hr₁.ne').apply_symm_apply]
          _ = r₁⁻¹ * dist z ((plankRescale ctr hr₁.ne').symm x) :=
                plankRescale_dist ctr hr₁ z ((plankRescale ctr hr₁.ne').symm x)
      rw [hdist]
      calc
        r₁⁻¹ * dist z ((plankRescale ctr hr₁.ne').symm x) ≤ r₁⁻¹ * (r₁ * t) :=
          mul_le_mul_of_nonneg_left hz (le_of_lt (inv_pos.mpr hr₁))
        _ = t := by
          rw [← mul_assoc, inv_mul_cancel₀ hr₁.ne', one_mul]
    · exact (plankRescale ctr hr₁.ne').symm_apply_apply z

/-- **The inverse rescaling carries open balls onto open balls** (blueprint
`lem:ml2plankRescalingBalls`). -/
theorem plankRescale_symm_image_ball (hr₁ : 0 < r₁) (x : E₃) (t : ℝ) :
    (plankRescale ctr hr₁.ne').symm '' ball x t
      = ball ((plankRescale ctr hr₁.ne').symm x) (r₁ * t) := by
  ext z
  simp_rw [mem_image, mem_ball]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hdist : dist ((plankRescale ctr hr₁.ne').symm y) ((plankRescale ctr hr₁.ne').symm x)
        = r₁ * dist y x := by
      calc
        dist ((plankRescale ctr hr₁.ne').symm y) ((plankRescale ctr hr₁.ne').symm x)
            = ‖r₁ • (y - x)‖ := by
              rw [plankRescale_symm_apply, plankRescale_symm_apply, dist_eq_norm]
              rw [add_sub_add_left_eq_sub]
              rw [← smul_sub]
        _ = |r₁| * ‖y - x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = r₁ * ‖y - x‖ := by rw [abs_of_pos hr₁]
        _ = r₁ * dist y x := by rw [dist_eq_norm]
    rw [hdist]
    exact mul_lt_mul_of_pos_left hy hr₁
  · intro hz
    refine ⟨plankRescale ctr hr₁.ne' z, ?_, ?_⟩
    · have hdist : dist (plankRescale ctr hr₁.ne' z) x
          = r₁⁻¹ * dist z ((plankRescale ctr hr₁.ne').symm x) := by
        calc
          dist (plankRescale ctr hr₁.ne' z) x
              = dist (plankRescale ctr hr₁.ne' z)
                  (plankRescale ctr hr₁.ne' ((plankRescale ctr hr₁.ne').symm x)) := by
                rw [(plankRescale ctr hr₁.ne').apply_symm_apply]
          _ = r₁⁻¹ * dist z ((plankRescale ctr hr₁.ne').symm x) :=
                plankRescale_dist ctr hr₁ z ((plankRescale ctr hr₁.ne').symm x)
      rw [hdist]
      calc
        r₁⁻¹ * dist z ((plankRescale ctr hr₁.ne').symm x) < r₁⁻¹ * (r₁ * t) :=
          mul_lt_mul_of_pos_left hz (inv_pos.mpr hr₁)
        _ = t := by
          rw [← mul_assoc, inv_mul_cancel₀ hr₁.ne', one_mul]
    · exact (plankRescale ctr hr₁.ne').symm_apply_apply z

/-- **The rescaling multiplies every volume by `r₁⁻³`** (blueprint
`lem:ml2plankRescalingVolume`).

The identity holds for *every* set, measurable or not: the homothety half is
`MeasureTheory.Measure.addHaar_image_homothety`, stated for an arbitrary set, and the
translation half is add-invariance of Lebesgue measure. The factor is a single element of
`(0, ∞)`, so it cancels from any ratio of volumes and may be multiplied through any inequality
between sums of volumes. -/
theorem volume_plankRescale_image (hr₁ : 0 < r₁) (A : Set E₃) :
    volume (plankRescale ctr hr₁.ne' '' A) = ENNReal.ofReal (r₁⁻¹ ^ 3) * volume A := by
  have himg : plankRescale ctr hr₁.ne' '' A = r₁⁻¹ • ((fun y : E₃ => y - ctr) '' A) := by
    rw [← Set.image_smul, ← Set.image_comp]
    exact Set.image_congr (by intro y hy; exact plankRescale_apply ctr hr₁.ne' y)
  rw [himg]
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume (inv_pos.mpr hr₁).le]
  rw [show (fun y : E₃ => y - ctr) = (fun y : E₃ => -ctr + y) by
    funext y
    rw [sub_eq_add_neg, add_comm]]
  rw [MeasureTheory.measure_image_add volume (-ctr) A]
  rw [finrank_euclideanSpace_fin]

/-- **The inverse rescaling multiplies every volume by `r₁³`** (blueprint
`lem:ml2plankRescalingVolume`). -/
theorem volume_plankRescale_symm_image (hr₁ : 0 < r₁) (A : Set E₃) :
    volume ((plankRescale ctr hr₁.ne').symm '' A) = ENNReal.ofReal (r₁ ^ 3) * volume A := by
  have himg : (plankRescale ctr hr₁.ne').symm '' A = (fun y : E₃ => ctr + y) '' (r₁ • A) := by
    rw [← Set.image_smul, ← Set.image_comp]
    exact Set.image_congr (by intro y hy; exact plankRescale_symm_apply ctr hr₁.ne' y)
  rw [himg]
  rw [MeasureTheory.measure_image_add volume ctr (r₁ • A)]
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume hr₁.le]
  rw [finrank_euclideanSpace_fin]

/-- The volume scaling of the rescaling for a merely nonzero ratio, which is the form the
refinement and density statements need: they are stated for `r₁ ≠ 0` rather than `0 < r₁`,
and all they use of the factor is that it is a single element of `(0, ∞)`. -/
theorem volume_plankRescale_image_of_ne_zero (hr₁ : r₁ ≠ 0) (A : Set E₃) :
    volume (plankRescale ctr hr₁ '' A) = ENNReal.ofReal |r₁⁻¹ ^ 3| * volume A := by
  have himg : plankRescale ctr hr₁ '' A = r₁⁻¹ • ((fun y : E₃ => y - ctr) '' A) := by
    rw [← Set.image_smul, ← Set.image_comp]
    exact Set.image_congr (by intro y hy; exact plankRescale_apply ctr hr₁ y)
  rw [himg]
  rw [MeasureTheory.Measure.addHaar_smul volume r₁⁻¹]
  rw [show (fun y : E₃ => y - ctr) = (fun y : E₃ => -ctr + y) by
    funext y
    rw [sub_eq_add_neg, add_comm]]
  rw [MeasureTheory.measure_image_add volume (-ctr) A]
  rw [finrank_euclideanSpace_fin]

/-- The volume scaling of the inverse rescaling for a merely nonzero ratio. -/
theorem volume_plankRescale_symm_image_of_ne_zero (hr₁ : r₁ ≠ 0) (A : Set E₃) :
    volume ((plankRescale ctr hr₁).symm '' A) = ENNReal.ofReal |r₁ ^ 3| * volume A := by
  have himg : (plankRescale ctr hr₁).symm '' A = (fun y : E₃ => ctr + y) '' (r₁ • A) := by
    rw [← Set.image_smul, ← Set.image_comp]
    exact Set.image_congr (by intro y hy; exact plankRescale_symm_apply ctr hr₁ y)
  rw [himg]
  rw [MeasureTheory.measure_image_add volume ctr (r₁ • A)]
  rw [MeasureTheory.Measure.addHaar_smul volume r₁]
  rw [finrank_euclideanSpace_fin]

/-! ### Thicknesses -/

/-- **`ethickness` scales exactly under the rescaling** (blueprint
`lem:ml2plankEthicknessScaling`).

`LipschitzWith.ethickness_image_le` applied to `L_B` and to `L_B⁻¹` gives the two inequalities,
and `0 < r₁⁻¹ < ∞` turns them into an equality in `[0, ∞]`. -/
theorem ethickness_plankRescale_image (hr₁ : 0 < r₁) (X : Set E₃) (k : ℕ) :
    Metric.ethickness ℝ (plankRescale ctr hr₁.ne' '' X) k
      = ENNReal.ofReal r₁⁻¹ * Metric.ethickness ℝ X k := by
  let L : E₃ ≃ᵃ[ℝ] E₃ := plankRescale ctr hr₁.ne'
  have hle : Metric.ethickness ℝ (L '' X) k ≤ ENNReal.ofReal r₁⁻¹ * Metric.ethickness ℝ X k := by
    have h := (LipschitzWith.ethickness_image_le
      (f := L.toAffineMap) (C := Real.toNNReal r₁⁻¹)
      (lipschitzWith_plankRescale ctr hr₁) X) k
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal] using h
  have hle_inv : Metric.ethickness ℝ X k ≤ ENNReal.ofReal r₁ * Metric.ethickness ℝ (L '' X) k := by
    have h := (LipschitzWith.ethickness_image_le
      (f := L.symm.toAffineMap) (C := Real.toNNReal r₁)
      (lipschitzWith_plankRescale_symm ctr hr₁) (L '' X)) k
    have himg : L.symm.toAffineMap '' (L '' X) = X := by
      change (L.symm : E₃ → E₃) '' (L '' X) = X
      rw [Set.image_image]
      rw [show (fun x : E₃ => L.symm (L x)) = id by
        funext y
        exact AffineEquiv.symm_apply_apply L y]
      simp
    rw [himg] at h
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal] using h
  have hge : ENNReal.ofReal r₁⁻¹ * Metric.ethickness ℝ X k
      ≤ Metric.ethickness ℝ (L '' X) k := by
    calc
      ENNReal.ofReal r₁⁻¹ * Metric.ethickness ℝ X k
          ≤ ENNReal.ofReal r₁⁻¹ * (ENNReal.ofReal r₁ * Metric.ethickness ℝ (L '' X) k) := by
              gcongr
      _ = (ENNReal.ofReal r₁⁻¹ * ENNReal.ofReal r₁) * Metric.ethickness ℝ (L '' X) k := by
              rw [← mul_assoc]
      _ = ENNReal.ofReal (r₁⁻¹ * r₁) * Metric.ethickness ℝ (L '' X) k := by
              rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr₁.le)]
      _ = Metric.ethickness ℝ (L '' X) k := by
              rw [inv_mul_cancel₀ hr₁.ne', ENNReal.ofReal_one, one_mul]
  exact le_antisymm hle hge

set_option linter.unusedVariables false in
/-- **Thickness transport under the rescaling** (blueprint
`lem:ml2plankThicknessTransport`).

A bounded set whose affine thicknesses are comparable, with constant `C₀`, to `(r₁, b, a)` is
carried by `L_B` to a bounded set whose affine thicknesses are comparable, with the **same**
constant `C₀`, to `(1, b/r₁, a/r₁)`: the transport is an *equality* of thicknesses rank by
rank, so no slack is created and none of the slack in the hypothesis is consumed.

No ordering of `a` and `b` is assumed — the transport does not see it — and `K ≠ ∅` is not
assumed either, being forced by the lower half of the hypothesis at rank `0` when
`r₁ > 0`. Boundedness of the image is not part of the conclusion: it is
`LipschitzWith.isBounded_image` applied to
`Kakeya.VeryNotSticky.lipschitzWith_plankRescale`. -/
@[nolint unusedArguments]
theorem hasThicknesses_plankRescale_image {C₀ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁)
    {a b : ℝ} {K : Set E₃} (hK : Bornology.IsBounded K)
    (hthick : HasThicknesses K C₀ ![r₁, b, a]) :
    HasThicknesses (plankRescale ctr hr₁.ne' '' K) C₀ ![1, b / r₁, a / r₁] := by
  have himg : Bornology.IsBounded (plankRescale ctr hr₁.ne' '' K) :=
    LipschitzWith.isBounded_image (lipschitzWith_plankRescale ctr hr₁) hK
  have hth_image : ∀ k : ℕ, Metric.thickness ℝ (plankRescale ctr hr₁.ne' '' K) k
      = r₁⁻¹ * Metric.thickness ℝ K k := by
    intro k
    rw [← Metric.toReal_ethickness himg k]
    rw [ethickness_plankRescale_image ctr hr₁ K k]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hr₁.le)]
    rw [Metric.toReal_ethickness hK k]
  have htransport : ∀ x τ : ℝ, (C₀ : ℝ)⁻¹ * x ≤ τ → τ ≤ C₀ * x →
      (C₀ : ℝ)⁻¹ * (x / r₁) ≤ r₁⁻¹ * τ ∧ r₁⁻¹ * τ ≤ C₀ * (x / r₁) := by
    intro x τ hLE hGE
    constructor
    · calc
        (C₀ : ℝ)⁻¹ * (x / r₁) = (C₀ : ℝ)⁻¹ * (x * r₁⁻¹) := by rw [div_eq_mul_inv]
        _ = (C₀ : ℝ)⁻¹ * x * r₁⁻¹ := by rw [mul_assoc]
        _ ≤ τ * r₁⁻¹ := mul_le_mul_of_nonneg_right hLE (inv_nonneg.mpr hr₁.le)
        _ = r₁⁻¹ * τ := by rw [mul_comm]
    · calc
        r₁⁻¹ * τ = τ * r₁⁻¹ := by rw [mul_comm]
        _ ≤ C₀ * x * r₁⁻¹ := mul_le_mul_of_nonneg_right hGE (inv_nonneg.mpr hr₁.le)
        _ = C₀ * (x * r₁⁻¹) := by rw [mul_assoc]
        _ = C₀ * (x / r₁) := by rw [div_eq_mul_inv]
  rw [show ![1, b / r₁, a / r₁] = (fun k : Fin 3 => ![r₁, b, a] k / r₁) by
    funext k
    fin_cases k <;> simp [div_self hr₁.ne']]
  intro k
  rw [hth_image]
  change (C₀ : ℝ)⁻¹ * (![r₁, b, a] k / r₁) ≤ r₁⁻¹ * Metric.thickness ℝ K (k : ℕ) ∧
    r₁⁻¹ * Metric.thickness ℝ K (k : ℕ) ≤ C₀ * (![r₁, b, a] k / r₁)
  exact htransport (![r₁, b, a] k) (Metric.thickness ℝ K (k : ℕ)) (hthick k).1 (hthick k).2

/-! ### Bodies, shadings and families -/

/-- **`L_B(K)`**: the image of a convex body under the rescaling. -/
def _root_.ConvexSpaceBody.plankRescale (K : ConvexSpaceBody E₃) (ctr : E₃) {r₁ : ℝ}
    (hr₁ : r₁ ≠ 0) : ConvexSpaceBody E₃ :=
  K.affineImage (Kakeya.VeryNotSticky.plankRescale ctr hr₁).toAffineMap
    (plankRescale_continuous ctr hr₁)

/-- **`L_B(W, Y(W))`**: the image of a shaded body under the rescaling. -/
def _root_.ShadedBody.plankRescale (W : ShadedBody E₃) (ctr : E₃) {r₁ : ℝ} (hr₁ : r₁ ≠ 0) :
    ShadedBody E₃ :=
  W.affineImage (Kakeya.VeryNotSticky.plankRescale ctr hr₁).toAffineMap
    (plankRescale_continuous ctr hr₁) (plankRescale_measurableEmbedding ctr hr₁)

/-- **`L_B⁻¹(W, Y(W))`**: the image of a shaded body under the inverse rescaling. -/
def _root_.ShadedBody.plankRescaleSymm (W : ShadedBody E₃) (ctr : E₃) {r₁ : ℝ} (hr₁ : r₁ ≠ 0) :
    ShadedBody E₃ :=
  W.affineImage (Kakeya.VeryNotSticky.plankRescale ctr hr₁).symm.toAffineMap
    (plankRescale_symm_continuous ctr hr₁) (plankRescale_symm_measurableEmbedding ctr hr₁)

/-- **Essential distinctness is preserved by the rescaling** (blueprint
`lem:ml2plankEssDistinctTransport`).

A corollary of the general statement `Kakeya.IsEssentiallyDistinct.image_affineEquiv`, `L_B`
being an invertible affine self-map of `ℝ³`. -/
theorem isEssentiallyDistinct_plankRescale_image (hr₁ : r₁ ≠ 0) {U V : Set E₃}
    (h : IsEssentiallyDistinct U V) :
    IsEssentiallyDistinct (plankRescale ctr hr₁ '' U) (plankRescale ctr hr₁ '' V) := by
  exact h.image_affineEquiv (plankRescale ctr hr₁)

variable {ι : Type*}

/-- **The shaded union of the rescaled family is the rescaled shaded union** (blueprint
`lem:ml2plankMultTransport`).

A set-theoretic identity, needing no positivity and no measurability. -/
theorem iUnionShade_plankRescale (hr₁ : r₁ ≠ 0) (s : Finset ι) (V : ι → ShadedBody E₃) :
    iUnionShade s (fun i => (V i).plankRescale ctr hr₁)
      = plankRescale ctr hr₁ '' iUnionShade s V := by
  simp [ShadedBody.plankRescale, ShadedBody.affineImage_shade, iUnionShade, ← Set.image_iUnion₂]

set_option linter.unusedVariables false in
/-- **Multiplicity is unchanged by the rescaling** (blueprint `lem:ml2plankMultTransport`).

By `Kakeya.VeryNotSticky.iUnionShade_plankRescale` both the numerator and the denominator of
`μ` are multiplied by the single factor `r₁⁻³`, so the ratio is unchanged *exactly*.

The positivity `|U(𝒱, Y)| > 0` is **not** automatic; at the call site it is obligation (O2) of
the note following blueprint `lem:ml2plankpresentation`, carried there as
`Kakeya.VeryNotSticky.plankPresentation`'s hypothesis `hUpos`. Measurability of the shadings
is part of the data of a `ShadedBody`. -/
@[nolint unusedArguments]
theorem multiplicity_plankRescale (hr₁ : r₁ ≠ 0) (s : Finset ι) (V : ι → ShadedBody E₃)
    (hpos : 0 < volume (iUnionShade s V)) :
    multiplicity s (fun i => (V i).plankRescale ctr hr₁) = multiplicity s V := by
  unfold _root_.ShadedBody.plankRescale
  exact ShadedBody.multiplicity_affineImage s V (plankRescale ctr hr₁)
    (plankRescale_continuous ctr hr₁) (plankRescale_measurableEmbedding ctr hr₁)

/-- **A `c`-refinement pulls back along the rescaling** (blueprint
`lem:ml2plankRefinementPullback`).

The pulled-back bodies are the `V i` *themselves* and not merely supersets of them, which is
what `ShadedBody.IsRefinement` demands; and the mass inequality survives because both sides
are multiplied by the same factor `r₁³`. -/
theorem isCRefinement_comap_plankRescale (hr₁ : r₁ ≠ 0) {s' s : Finset ι}
    {V' V : ι → ShadedBody E₃} {c : NNReal}
    (h : IsCRefinement s' V' s (fun i => (V i).plankRescale ctr hr₁) c) :
    IsCRefinement s' (fun i => (V' i).plankRescaleSymm ctr hr₁) s V c := by
  have hL_inv_set : ∀ X : Set E₃,
      (plankRescale ctr hr₁).symm.toAffineMap '' ((plankRescale ctr hr₁).toAffineMap '' X)
        = X := fun X => (plankRescale ctr hr₁).toEquiv.symm_image_image X
  refine ⟨⟨h.1.1, fun i hi => ⟨?_, ?_⟩⟩, ?_⟩
  · -- carrier
    change (((V' i).toConvexSpaceBody).affineImage (plankRescale ctr hr₁).symm.toAffineMap
        (plankRescale_symm_continuous ctr hr₁)) = (V i).toConvexSpaceBody
    rw [(h.1.2 i hi).1]
    exact SetLike.coe_injective (hL_inv_set (V i).carrier)
  · -- shade
    change (plankRescale ctr hr₁).symm.toAffineMap '' (V' i).shade ⊆ (V i).shade
    rw [← hL_inv_set (V i).shade]
    exact Set.image_mono (by
      simpa only [ShadedBody.plankRescale, ShadedBody.affineImage_shade] using (h.1.2 i hi).2)
  · -- mass
    set A : ENNReal := ∑ i ∈ s, volume ((V i).shade)
    set B : ENNReal := ∑ i ∈ s', volume ((V' i).shade)
    set kL : ENNReal := ENNReal.ofReal |r₁ ^ 3|
    set kLinv : ENNReal := ENNReal.ofReal |(r₁⁻¹) ^ 3|
    have hAl : (∑ i ∈ s, volume (((V i).plankRescale ctr hr₁).shade)) = kLinv * A := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        volume_plankRescale_image_of_ne_zero ctr hr₁ (V i).shade
    have hsumR : (∑ i ∈ s', volume (((V' i).plankRescaleSymm ctr hr₁).shade)) = kL * B := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        volume_plankRescale_symm_image_of_ne_zero ctr hr₁ (V' i).shade
    have hprod : kL * kLinv = 1 := by
      rw [show kL * kLinv = ENNReal.ofReal |r₁ ^ 3 * r₁⁻¹ ^ 3| from
          (ENNReal.ofReal_mul (abs_nonneg _)).symm.trans (by rw [abs_mul]),
        ← mul_pow, mul_inv_cancel₀ hr₁, one_pow, abs_one, ENNReal.ofReal_one]
    rw [hsumR, ← one_mul ((c : ENNReal) * A), ← hprod, mul_assoc,
      mul_left_comm kLinv (c : ENNReal) A]
    exact mul_le_mul_right (by simpa only [hAl] using h.2) kL

/-- **`c`-refinement depends on the shadings alone** (blueprint
`lem:ml2plankCRefinementCongrCarrier`).

Let `V` and `V♯` be families on the same index set with the *same* shadings, the carriers being
allowed to differ, and let `V'` be a `c`-refinement of `V♯`. Then the family `V''` obtained
from `V'` by replacing its carriers by those of `V` is a `c`-refinement of `V`.

This is the `c`-refinement analogue of `ShadedBody.multiplicity_congr`, and it is needed
because `ShadedBody.IsRefinement` demands the carriers of a refinement to be *equal* to those
of the refined family: a `c`-refinement of one of two shading-congruent families is not
literally a `c`-refinement of the other, only after the carriers have been swapped. -/
theorem isCRefinement_congr_carrier {s' s : Finset ι} {V Vsharp V' V'' : ι → ShadedBody E₃}
    {c : NNReal} (hshade : ∀ i ∈ s, (Vsharp i).shade = (V i).shade)
    (h : IsCRefinement s' V' s Vsharp c)
    (hcarrier : ∀ i ∈ s', (V'' i).toConvexSpaceBody = (V i).toConvexSpaceBody)
    (hsh : ∀ i ∈ s', (V'' i).shade = (V' i).shade) :
    IsCRefinement s' V'' s V c := by
  constructor
  · constructor
    · exact h.1.1
    · intro i hi
      exact ⟨hcarrier i hi, by
        rw [hsh i hi, ← hshade i (h.1.1 hi)]
        exact (h.1.2 i hi).2⟩
  · rw [show (∑ i ∈ s, volume (V i).shade) = ∑ i ∈ s, volume (Vsharp i).shade by
      exact Finset.sum_congr rfl (fun i hi => by rw [← hshade i hi])]
    rw [show (∑ i ∈ s', volume (V'' i).shade) = ∑ i ∈ s', volume (V' i).shade by
      exact Finset.sum_congr rfl (fun i hi => by rw [hsh i hi])]
    exact h.2

set_option linter.unusedVariables false in
/-- **Transporting a refinement of the enclosing family back** (blueprint
`lem:ml2plankRefinementTransport`).

Let `(𝕎, Y)` be a finite shaded family, let `𝒫` be a family of bodies containing the rescaled
bodies `L_B(W j)`, and give `𝒫` the transported shadings `Y_𝒫(j) = L_B(Y j)`. A `c`-refinement
`(𝒫', Y_{𝒫'})` of `(𝒫, Y_𝒫)` then pulls back to a `c`-refinement of `(𝕎, Y)` whose bodies are
the `W j` themselves and whose shadings are `L_B⁻¹(Y_{𝒫'}(j))`.

This composite is consumed twice in the assembly of blueprint `lem:ml2plankpresentation` —
once for the refinement clause itself and once to feed
`Kakeya.VeryNotSticky.plankRescalingBridge` — which is why it is named rather than left as the
two-step argument (`Kakeya.VeryNotSticky.isCRefinement_congr_carrier` followed by
`Kakeya.VeryNotSticky.isCRefinement_comap_plankRescale`) that it abbreviates. -/
theorem exists_isCRefinement_of_plankRescale (hr₁ : r₁ ≠ 0) {s s' : Finset ι}
    (W : ι → ShadedBody E₃) (P : ι → ConvexSpaceBody E₃)
    (hPW : ∀ i ∈ s, plankRescale ctr hr₁ '' (W i).carrier ⊆ (P i).carrier)
    (YP : ι → ShadedBody E₃) (hYPcarrier : ∀ i ∈ s, (YP i).toConvexSpaceBody = P i)
    (hYPshade : ∀ i ∈ s, (YP i).shade = plankRescale ctr hr₁ '' (W i).shade)
    {c : NNReal} {YP' : ι → ShadedBody E₃} (h : IsCRefinement s' YP' s YP c) :
    ∃ W''' : ι → ShadedBody E₃,
      (∀ i ∈ s', (W''' i).toConvexSpaceBody = (W i).toConvexSpaceBody) ∧
      (∀ i ∈ s', (W''' i).shade = (plankRescale ctr hr₁).symm '' (YP' i).shade) ∧
      IsCRefinement s' W''' s W c := by
  classical
  have hL_inv : ∀ x : E₃,
      (plankRescale ctr hr₁).symm.toAffineMap ((plankRescale ctr hr₁).toAffineMap x) = x := by
    intro x
    change (plankRescale ctr hr₁).symm ((plankRescale ctr hr₁) x) = x
    exact AffineEquiv.symm_apply_apply (plankRescale ctr hr₁) x
  have hL_inv_set : ∀ X : Set E₃,
      (plankRescale ctr hr₁).symm.toAffineMap '' ((plankRescale ctr hr₁).toAffineMap '' X)
        = X := by
    intro X
    rw [Set.image_image]
    rw [show (fun x : E₃ => (plankRescale ctr hr₁).symm.toAffineMap
        ((plankRescale ctr hr₁).toAffineMap x)) = (fun x : E₃ => x) by
      funext x
      exact hL_inv x]
    simp
  have hshade_subset : ∀ (i) (hi : i ∈ s'),
      (YP' i).shade ⊆ plankRescale ctr hr₁ '' (W i).carrier := by
    intro i hi
    calc
      (YP' i).shade ⊆ (YP i).shade := (h.1.2 i hi).2
      _ = plankRescale ctr hr₁ '' (W i).shade := hYPshade i (h.1.1 hi)
      _ ⊆ plankRescale ctr hr₁ '' (W i).carrier := Set.image_mono (W i).shade_subset
  let V'' : ι → ShadedBody E₃ := fun i =>
    if hi : i ∈ s' then
      { toConvexSpaceBody := ((W i).plankRescale ctr hr₁).toConvexSpaceBody,
        shade := (YP' i).shade,
        measurableSet_shade := (YP' i).measurableSet_shade,
        shade_subset := hshade_subset i hi }
    else (W i).plankRescale ctr hr₁
  have hstep1 : IsCRefinement s' V'' s (fun i => (W i).plankRescale ctr hr₁) c :=
    isCRefinement_congr_carrier (V := fun i => (W i).plankRescale ctr hr₁) (Vsharp := YP)
      (fun i hi => (hYPshade i hi)) h (fun i hi => by simp [V'', dif_pos hi])
      (fun i hi => by simp [V'', dif_pos hi])
  refine ⟨fun i => (V'' i).plankRescaleSymm ctr hr₁, ?_, ?_,
    isCRefinement_comap_plankRescale ctr hr₁ hstep1⟩
  · intro i hi
    change (((V'' i).toConvexSpaceBody).affineImage (plankRescale ctr hr₁).symm.toAffineMap
        (plankRescale_symm_continuous ctr hr₁)) = (W i).toConvexSpaceBody
    rw [show (V'' i).toConvexSpaceBody = ((W i).plankRescale ctr hr₁).toConvexSpaceBody by
      simp [V'', dif_pos hi]]
    change ((((W i).toConvexSpaceBody).affineImage (plankRescale ctr hr₁).toAffineMap
        (plankRescale_continuous ctr hr₁)).affineImage (plankRescale ctr hr₁).symm.toAffineMap
        (plankRescale_symm_continuous ctr hr₁)) = (W i).toConvexSpaceBody
    apply SetLike.coe_injective
    change (plankRescale ctr hr₁).symm.toAffineMap
        '' ((plankRescale ctr hr₁).toAffineMap '' (W i).carrier) = (W i).carrier
    exact hL_inv_set (W i).carrier
  · intro i hi
    simp [V'', dif_pos hi, ShadedBody.plankRescaleSymm, ShadedBody.affineImage_shade]

/-- **The test subfamily is unchanged by the rescaling** (blueprint
`lem:ml2plankFamilyInTransport`).

`L_B` is injective, so it both preserves and reflects inclusion and the two index sets
`𝕎[K]` agree. This is the exact analogue, for `L_B`, of `Kakeya.familyIn_homothety`. -/
theorem familyIn_plankRescale (hr₁ : r₁ ≠ 0) (s : Finset ι)
    (W : ι → ConvexSpaceBody E₃) (K : ConvexSpaceBody E₃) :
    familyIn s (fun i => (W i).plankRescale ctr hr₁) (K.plankRescale ctr hr₁)
      = familyIn s W K := by
  classical
  exact Finset.filter_congr (fun i hi => by
    rw [← SetLike.coe_subset_coe]
    change (plankRescale ctr hr₁) '' (W i).carrier ⊆ (plankRescale ctr hr₁) '' K.carrier
      ↔ (W i).carrier ⊆ K.carrier
    exact Set.image_subset_image_iff (plankRescale ctr hr₁).injective)

/-- **The density is unchanged by the rescaling** (blueprint
`lem:ml2plankFamilyInTransport`).

The numerator and denominator of `Δ(𝕎, K)` are both multiplied by `r₁⁻³`, which cancels; the
index set is `Kakeya.VeryNotSticky.familyIn_plankRescale`. This is the exact analogue, for
`L_B`, of `Kakeya.densityIn_homothety`. -/
theorem densityIn_plankRescale (hr₁ : r₁ ≠ 0) (s : Finset ι)
    (W : ι → ConvexSpaceBody E₃) (K : ConvexSpaceBody E₃) :
    densityIn s (fun i => (W i).plankRescale ctr hr₁) (K.plankRescale ctr hr₁)
      = densityIn s W K := by
  classical
  have hc0 : ENNReal.ofReal |(r₁⁻¹) ^ 3| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (pow_ne_zero 3 (inv_ne_zero hr₁)))
  have hfam := familyIn_plankRescale ctr hr₁ s W K
  unfold familyIn at hfam
  have hsum : (∑ i ∈ {i ∈ s | W i ≤ K}, volume ((W i).plankRescale ctr hr₁).carrier)
      = ENNReal.ofReal |(r₁⁻¹) ^ 3| * (∑ i ∈ {i ∈ s | W i ≤ K}, volume (W i).carrier) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      volume_plankRescale_image_of_ne_zero ctr hr₁ (W i).carrier
  have hden : volume (K.plankRescale ctr hr₁).carrier
      = ENNReal.ofReal |(r₁⁻¹) ^ 3| * volume K.carrier :=
    volume_plankRescale_image_of_ne_zero ctr hr₁ K.carrier
  unfold densityIn
  rw [hfam, hsum, hden, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

/-- **Maximal density is unchanged by the rescaling** (blueprint
`lem:ml2plankMaxDensityTransport`).

`K ↦ L_B(K)` is a bijection of the convex bodies of `ℝ³` onto themselves, so the two suprema
defining `Δ_max` are taken over the same set of values. This is the exact analogue, for `L_B`,
of `Kakeya.maxDensity_homothety`. -/
theorem maxDensity_plankRescale (hr₁ : r₁ ≠ 0) (s : Finset ι) (W : ι → ConvexSpaceBody E₃) :
    maxDensity s (fun i => (W i).plankRescale ctr hr₁) = maxDensity s W := by
  have hp (K : ConvexSpaceBody E₃) :
      (plankRescale ctr hr₁).toAffineMap
          '' ((plankRescale ctr hr₁).symm.toAffineMap '' K.carrier)
        = K.carrier := by
    rw [Set.image_image]
    change ((fun x : E₃ => plankRescale ctr hr₁ ((plankRescale ctr hr₁).symm x)) '' K.carrier)
        = K.carrier
    rw [show (fun x : E₃ => plankRescale ctr hr₁ ((plankRescale ctr hr₁).symm x)) = id by
      funext x
      exact (plankRescale ctr hr₁).apply_symm_apply x]
    simp
  have hKbody (K : ConvexSpaceBody E₃) :
      (K.affineImage (plankRescale ctr hr₁).symm.toAffineMap
        (plankRescale_symm_continuous ctr hr₁)).plankRescale ctr hr₁ = K := by
    refine ConvexSpaceBody.ext ?_
    change (plankRescale ctr hr₁).toAffineMap
      '' ((plankRescale ctr hr₁).symm.toAffineMap '' K.carrier) = ↑K
    exact hp K
  apply le_antisymm
  · rw [maxDensity_le_iff]
    intro K
    have hK : K = (K.affineImage (plankRescale ctr hr₁).symm.toAffineMap
        (plankRescale_symm_continuous ctr hr₁)).plankRescale ctr hr₁ :=
      (hKbody K).symm
    rw [hK]
    rw [densityIn_plankRescale ctr hr₁ s W (K.affineImage (plankRescale ctr hr₁).symm.toAffineMap
      (plankRescale_symm_continuous ctr hr₁))]
    exact le_maxDensity s W _
  · rw [maxDensity_le_iff]
    intro K
    rw [← densityIn_plankRescale ctr hr₁ s W K]
    exact le_maxDensity s (fun i => (W i).plankRescale ctr hr₁) _

/-! ### Transporting a local volume estimate -/

/-- **Closed and open balls have the same trace volume** (blueprint
`lem:volumeInterClosedBallEqBall`).

Spheres are Lebesgue null, and only subadditivity and monotonicity of the outer measure are
used, which is why no measurability of `S` is required.

The untraced half, `|B̄(x, t)| = |B(x, t)|`, is Mathlib's
`MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball` and is not restated. -/
theorem volume_inter_closedBall_eq_ball (S : Set E₃) (x : E₃) (t : ℝ) :
    volume (S ∩ closedBall x t) = volume (S ∩ ball x t) := by
  have hsphere : volume (S ∩ sphere x t) = 0 := by
    apply le_antisymm
    · calc
        volume (S ∩ sphere x t) ≤ volume (sphere x t) :=
          measure_mono (by intro y hy; exact hy.2)
        _ = 0 := MeasureTheory.Measure.addHaar_sphere (μ := volume) x t
    · exact zero_le
  have hle : volume (S ∩ closedBall x t) ≤ volume (S ∩ ball x t) := by
    calc
      volume (S ∩ closedBall x t) ≤ volume ((S ∩ ball x t) ∪ (S ∩ sphere x t)) := by
        apply measure_mono
        intro y hy
        rw [← Metric.ball_union_sphere] at hy
        rcases hy with ⟨hS, hb | hs⟩
        · exact Or.inl ⟨hS, hb⟩
        · exact Or.inr ⟨hS, hs⟩
      _ ≤ volume (S ∩ ball x t) + volume (S ∩ sphere x t) := measure_union_le _ _
      _ = volume (S ∩ ball x t) := by simp [hsphere]
  exact le_antisymm hle (measure_mono (by
    intro y hy
    exact ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩))

/-- **The rescaling bridge** (blueprint `lem:ml2plankRescalingBridge`).

If two shaded families on a common index set have shadings related by
`Y_{𝕎'''}(j) = L_B⁻¹(Y_{𝒫'}(j))`, then a lower bound for the shaded mass of `(𝒫', Y_{𝒫'})` in a
ball transports, at the witness `x = L_B⁻¹(x')` and with the radii multiplied by `r₁`, to the
same lower bound for `(𝕎''', Y_{𝕎'''})`.

Two radii appear because the estimate to be transported — item `itemballfull` of
`ShadedPlank.reduction_to_slab` — compares the volume of a ball of one radius with the shaded
mass in a concentric ball of a larger one. No comparison constant is lost: both sides are
multiplied by the same factor `r₁³` and `K` is not multiplied at all. The hypothesis is stated
for closed balls and the conclusion for open ones, which is what the consumer needs and costs
nothing. -/
theorem plankRescalingBridge (hr₁ : 0 < r₁) {s : Finset ι} (YP' Wsh' : ι → ShadedBody E₃)
    (hshade : ∀ j ∈ s, (Wsh' j).shade = (plankRescale ctr hr₁.ne').symm '' (YP' j).shade)
    (x' : E₃) (r' s' : ℝ) (K : ENNReal)
    (hK : K * volume (closedBall x' r') ≤ volume (iUnionShade s YP' ∩ closedBall x' s')) :
    K * volume (ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * r'))
      ≤ volume (iUnionShade s Wsh' ∩ ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * s')) := by
  have hshadeun : iUnionShade s Wsh' = (plankRescale ctr hr₁.ne').symm '' iUnionShade s YP' := by
    unfold iUnionShade
    rw [Set.image_iUnion₂]
    exact Set.iUnion₂_congr (fun j hj => hshade j hj)
  have hLvol : volume (ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * r'))
      = ENNReal.ofReal (r₁ ^ 3) * volume (closedBall x' r') := by
    calc
      volume (ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * r'))
          = volume (closedBall ((plankRescale ctr hr₁.ne').symm x') (r₁ * r')) := by
              rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball]
      _ = volume ((plankRescale ctr hr₁.ne').symm '' closedBall x' r') := by
              rw [← plankRescale_symm_image_closedBall ctr hr₁ x' r']
      _ = ENNReal.ofReal (r₁ ^ 3) * volume (closedBall x' r') :=
              volume_plankRescale_symm_image ctr hr₁ (closedBall x' r')
  have hRvol : volume (iUnionShade s Wsh' ∩ ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * s'))
      = ENNReal.ofReal (r₁ ^ 3) * volume (iUnionShade s YP' ∩ closedBall x' s') := by
    calc
      volume (iUnionShade s Wsh' ∩ ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * s'))
          = volume (iUnionShade s Wsh'
              ∩ closedBall ((plankRescale ctr hr₁.ne').symm x') (r₁ * s')) := by
              rw [volume_inter_closedBall_eq_ball (iUnionShade s Wsh')
                ((plankRescale ctr hr₁.ne').symm x') (r₁ * s')]
      _ = volume (iUnionShade s Wsh' ∩ (plankRescale ctr hr₁.ne').symm '' closedBall x' s') := by
              rw [← plankRescale_symm_image_closedBall ctr hr₁ x' s']
      _ = volume ((plankRescale ctr hr₁.ne').symm '' iUnionShade s YP'
            ∩ (plankRescale ctr hr₁.ne').symm '' closedBall x' s') := by
              rw [hshadeun]
      _ = volume ((plankRescale ctr hr₁.ne').symm '' (iUnionShade s YP' ∩ closedBall x' s')) := by
              rw [Set.image_inter (plankRescale ctr hr₁.ne').symm.injective]
      _ = ENNReal.ofReal (r₁ ^ 3) * volume (iUnionShade s YP' ∩ closedBall x' s') :=
              volume_plankRescale_symm_image ctr hr₁ (iUnionShade s YP' ∩ closedBall x' s')
  calc
    K * volume (ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * r'))
        = K * (ENNReal.ofReal (r₁ ^ 3) * volume (closedBall x' r')) := by
            rw [hLvol]
    _ = ENNReal.ofReal (r₁ ^ 3) * (K * volume (closedBall x' r')) := by
            rw [← mul_assoc, mul_comm K (ENNReal.ofReal (r₁ ^ 3)), mul_assoc]
    _ ≤ ENNReal.ofReal (r₁ ^ 3) * volume (iUnionShade s YP' ∩ closedBall x' s') := by
            have hnp : 0 ≤ ENNReal.ofReal (r₁ ^ 3) := by positivity
            exact mul_le_mul_of_nonneg_left hK hnp
    _ = volume (iUnionShade s Wsh' ∩ ball ((plankRescale ctr hr₁.ne').symm x') (r₁ * s')) :=
            hRvol.symm

end Kakeya.VeryNotSticky

end

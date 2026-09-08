/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Kakeya.IsBesicovitch

/-! ### Auxiliary lemmas about `μH[d]` on `EuclideanSpace ℝ (Fin d)`

This file provides lemmas relating the volume measure on Euclidean space to
the d-dimensional Hausdorff measure, and shows that positive volume implies
positive Hausdorff measure.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory
open MeasureTheory Set Metric Real

namespace Kakeya.IsBesicovitch.HausdorffTwoUnitSphere

/-- The volume measure on `EuclideanSpace ℝ (Fin d)` is a constant multiple
of the d-Hausdorff measure: `volume = c • μH[d]`. -/
private lemma volume_eq_smul_hausdorffMeasure (d : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))) =
      MeasureTheory.Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[(d : ℕ)] •
        (μH[(d : ℕ)] : Measure (EuclideanSpace ℝ (Fin d))) :=
  MeasureTheory.Measure.isAddLeftInvariant_eq_smul _ _

private lemma scalarFactor_ne_zero (d : ℕ) :
    MeasureTheory.Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[(d : ℕ)] ≠ 0 :=
  MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d

/-- The volume = c · μH[d] relation rewritten in measure-application form. -/
private lemma volume_eq_scalar_mul_hausdorff (d : ℕ)
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))) s =
      (MeasureTheory.Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[(d : ℕ)] : ℝ≥0∞) *
        (μH[(d : ℕ)] : Measure (EuclideanSpace ℝ (Fin d))) s := by
  conv_lhs => rw [volume_eq_smul_hausdorffMeasure d]
  rfl

/-- If `volume s` is positive on `EuclideanSpace ℝ (Fin d)`, then so is `μH[d] s`. -/
private lemma hausdorffMeasure_pos_of_volume_pos {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (h : 0 < volume s) :
    0 < (μH[(d : ℕ)] : Measure (EuclideanSpace ℝ (Fin d))) s := by
  by_contra hne
  push Not at hne
  have h0 : (μH[(d : ℕ)] : Measure (EuclideanSpace ℝ (Fin d))) s = 0 :=
    le_antisymm hne bot_le
  rw [volume_eq_scalar_mul_hausdorff d s] at h
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

/-- If `volume s < ⊤` on `EuclideanSpace ℝ (Fin d)`, then `μH[d] s < ⊤`. -/
private lemma hausdorffMeasure_lt_top_of_volume_lt_top {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (h : volume s < ⊤) :
    (μH[(d : ℕ)] : Measure (EuclideanSpace ℝ (Fin d))) s < ⊤ := by
  by_contra htop
  push Not at htop
  have heq : (μH[(d : ℕ)] : Measure (EuclideanSpace ℝ (Fin d))) s = ⊤ :=
    eq_top_iff.mpr htop
  rw [volume_eq_scalar_mul_hausdorff d s, heq] at h
  have hc_ne_zero : (MeasureTheory.Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[(d : ℕ)] : ℝ≥0∞) ≠ 0 := by
    intro habsurd
    have h2 : MeasureTheory.Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[(d : ℕ)] = 0 := by
      exact_mod_cast habsurd
    exact scalarFactor_ne_zero d h2
  rw [ENNReal.mul_top hc_ne_zero] at h
  exact lt_irrefl _ h

/-! ### Key sub-claims: positivity and finiteness of μH²(sphere). -/

/-- The "drop the third coordinate" projection from `EuclideanSpace ℝ (Fin 3)`
to `EuclideanSpace ℝ (Fin 2)`. -/
private noncomputable def proj32 :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
  fun v => (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    (fun i => v ⟨i.val, by omega⟩)

/-- `proj32` is `1`-Lipschitz: dropping a coordinate cannot increase the
Euclidean norm. -/
private lemma lipschitzWith_proj32 : LipschitzWith 1 proj32 := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have h2 : (Finset.univ : Finset (Fin 2)).sum
      (fun i => ‖(proj32 v - proj32 w) i‖ ^ 2) =
      ‖v 0 - w 0‖ ^ 2 + ‖v 1 - w 1‖ ^ 2 := by
    simp [Fin.sum_univ_two, proj32, WithLp.equiv]
  have h3 : (Finset.univ : Finset (Fin 3)).sum
      (fun i => ‖(v - w) i‖ ^ 2) =
      ‖v 0 - w 0‖ ^ 2 + ‖v 1 - w 1‖ ^ 2 + ‖v 2 - w 2‖ ^ 2 := by
    simp [Fin.sum_univ_three]
  rw [h2, h3]
  have h_nonneg : (0 : ℝ) ≤ ‖v 2 - w 2‖ ^ 2 := sq_nonneg _
  linarith

/-- Image of the unit sphere under `proj32` contains the closed unit disk. -/
private lemma closedBall_subset_proj32_sphere :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆
      proj32 '' {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} := by
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right] at hp
  have hp_sq : p 0 ^ 2 + p 1 ^ 2 ≤ 1 := by
    have hpn := EuclideanSpace.norm_eq p
    have hsum : (Finset.univ : Finset (Fin 2)).sum (fun i => ‖p i‖ ^ 2) =
        p 0 ^ 2 + p 1 ^ 2 := by
      simp [Fin.sum_univ_two, sq_abs]
    rw [hsum] at hpn
    have hsq_nonneg : (0 : ℝ) ≤ p 0 ^ 2 + p 1 ^ 2 := by positivity
    nlinarith [Real.sqrt_nonneg (p 0 ^ 2 + p 1 ^ 2),
      Real.sq_sqrt hsq_nonneg,
      sq_nonneg (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) - 1),
      hp, hpn]
  set z : ℝ := Real.sqrt (1 - p 0 ^ 2 - p 1 ^ 2) with hz_def
  have hz_sq : z ^ 2 = 1 - p 0 ^ 2 - p 1 ^ 2 :=
    Real.sq_sqrt (by linarith)
  let v : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![p 0, p 1, z]
  refine ⟨v, ?_, ?_⟩
  · change ‖v‖ = 1
    rw [EuclideanSpace.norm_eq]
    have hsum : (Finset.univ : Finset (Fin 3)).sum (fun i => ‖v i‖ ^ 2) =
        p 0 ^ 2 + p 1 ^ 2 + z ^ 2 := by
      simp [v, Fin.sum_univ_three, sq_abs]
    rw [hsum, hz_sq]
    have : p 0 ^ 2 + p 1 ^ 2 + (1 - p 0 ^ 2 - p 1 ^ 2) = 1 := by ring
    rw [this]; exact Real.sqrt_one
  · apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
    funext i
    fin_cases i <;> simp [proj32, v, WithLp.equiv]

/-- The 2-Hausdorff measure of the unit sphere in `EuclideanSpace ℝ (Fin 3)` is positive. -/
private lemma hausdorffMeasure_sphere_pos :
    0 < (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 3))) {v | ‖v‖ = 1} := by
  have h_lip := lipschitzWith_proj32.hausdorffMeasure_image_le (d := (2 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 2) {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}
  have h_subset := closedBall_subset_proj32_sphere
  have h_mono : (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 2)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≤
      (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 2)))
        (proj32 '' {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}) :=
    measure_mono h_subset
  have h_pos_disk : 0 < (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 2)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    have h_vol_pos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin 2)))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      Metric.measure_closedBall_pos _ _ one_pos
    have := hausdorffMeasure_pos_of_volume_pos (d := 2) h_vol_pos
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num] at this
    convert this
  calc 0 < (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 2)))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := h_pos_disk
    _ ≤ (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 2)))
        (proj32 '' {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}) := h_mono
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 3)))
          {v | ‖v‖ = 1} := h_lip
    _ = (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 3))) {v | ‖v‖ = 1} := by
        simp

/-- Spherical parametrization, viewed as a function from `EuclideanSpace ℝ (Fin 2)` to
`EuclideanSpace ℝ (Fin 3)`. Sends `(θ, φ)` to `(sin θ cos φ, sin θ sin φ, cos θ)`. -/
private noncomputable def sphericalParam :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
  fun p => (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![Real.sin (p 0) * Real.cos (p 1),
      Real.sin (p 0) * Real.sin (p 1),
      Real.cos (p 0)]

set_option linter.flexible false in
-- Several `simp [WithLp.equiv]` and `simp [sphericalParam,...]` invocations
-- here use `<;>` / `fin_cases` to discharge multiple divergent subgoals at once,
-- so a uniform `simp only` is awkward.
/-- Every unit vector in `EuclideanSpace ℝ (Fin 3)` lies in the image of the
spherical parametrization restricted to `[0, π] × [0, 2π]`. -/
private lemma sphere_subset_sphericalParam_image :
    {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} ⊆
      sphericalParam ''
        {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧
          0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi} := by
  intro v hv
  rw [Set.mem_setOf_eq] at hv
  have hv_sq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    have hpn := EuclideanSpace.norm_eq v
    have hsum : (Finset.univ : Finset (Fin 3)).sum (fun i => ‖v i‖ ^ 2) =
        v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
      simp [Fin.sum_univ_three, sq_abs]
    rw [hsum] at hpn
    have h1 : Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) = 1 := by rw [← hpn]; exact hv
    have h_nonneg : (0 : ℝ) ≤ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by positivity
    have h_sq := Real.sq_sqrt h_nonneg
    rw [h1] at h_sq; linarith
  have hv2_le : v 2 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2 - 1)]
  have hv2_ge : -1 ≤ v 2 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2 + 1)]
  set θ := Real.arccos (v 2)
  have hθ_range : 0 ≤ θ ∧ θ ≤ Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos_θ : Real.cos θ = v 2 := Real.cos_arccos hv2_ge hv2_le
  have hsin_θ_eq : Real.sin θ = Real.sqrt (1 - v 2 ^ 2) := Real.sin_arccos _
  have hsin_θ_nonneg : 0 ≤ Real.sin θ := by
    rw [hsin_θ_eq]; exact Real.sqrt_nonneg _
  have hsin_θ_sq : Real.sin θ ^ 2 = 1 - v 2 ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hcos_θ] at this; linarith
  by_cases hs : Real.sin θ = 0
  · have h_zero : Real.sin θ ^ 2 = 0 := by rw [hs]; ring
    rw [hsin_θ_sq] at h_zero
    have hv01 : v 0 ^ 2 + v 1 ^ 2 = 0 := by linarith
    have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    refine ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![θ, 0], ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [WithLp.equiv]
      · exact hθ_range.1
      · exact hθ_range.2
      · positivity
    · apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
      funext i
      fin_cases i <;>
        simp [sphericalParam, WithLp.equiv, hv0, hv1, hcos_θ, hs]
  · have hs_pos : 0 < Real.sin θ := lt_of_le_of_ne hsin_θ_nonneg (Ne.symm hs)
    have hs_sq_pos : 0 < Real.sin θ ^ 2 := by positivity
    have h_cs : (v 0 / Real.sin θ) ^ 2 + (v 1 / Real.sin θ) ^ 2 = 1 := by
      have h1 : v 0 ^ 2 + v 1 ^ 2 = Real.sin θ ^ 2 := by rw [hsin_θ_sq]; linarith
      field_simp
      linarith
    have hcsx_le : v 0 / Real.sin θ ≤ 1 := by
      nlinarith [sq_nonneg (v 1 / Real.sin θ),
        sq_nonneg (v 0 / Real.sin θ - 1), h_cs]
    have hcsx_ge : -1 ≤ v 0 / Real.sin θ := by
      nlinarith [sq_nonneg (v 1 / Real.sin θ),
        sq_nonneg (v 0 / Real.sin θ + 1), h_cs]
    set α := Real.arccos (v 0 / Real.sin θ)
    have hα_range : 0 ≤ α ∧ α ≤ Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have hcos_α : Real.cos α = v 0 / Real.sin θ := Real.cos_arccos hcsx_ge hcsx_le
    have hsin_α : Real.sin α = Real.sqrt (1 - (v 0 / Real.sin θ) ^ 2) := Real.sin_arccos _
    have hsin_α_sq : Real.sin α ^ 2 = (v 1 / Real.sin θ) ^ 2 := by
      have h_nonneg : (0 : ℝ) ≤ 1 - (v 0 / Real.sin θ) ^ 2 := by
        nlinarith [sq_nonneg (v 0 / Real.sin θ), sq_nonneg (v 1 / Real.sin θ), h_cs]
      rw [hsin_α, Real.sq_sqrt h_nonneg]
      linarith
    have hsin_α_nonneg : 0 ≤ Real.sin α := by rw [hsin_α]; exact Real.sqrt_nonneg _
    by_cases hv1_nonneg : 0 ≤ v 1 / Real.sin θ
    · refine ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![θ, α], ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [WithLp.equiv]
        · exact hθ_range.1
        · exact hθ_range.2
        · exact hα_range.1
        · linarith [hα_range.2, Real.pi_pos]
      · apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
        funext i
        have hsinα_eq : Real.sin α = v 1 / Real.sin θ := by
          have habs : |Real.sin α| = |v 1 / Real.sin θ| := by
            rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, hsin_α_sq]
          rw [abs_of_nonneg hsin_α_nonneg, abs_of_nonneg hv1_nonneg] at habs
          exact habs
        fin_cases i <;>
          simp [sphericalParam, WithLp.equiv, hcos_α, hsinα_eq, hcos_θ]
        all_goals (field_simp; try ring)
    · push Not at hv1_nonneg
      have hv1_neg : v 1 / Real.sin θ < 0 := hv1_nonneg
      have hv1_neg' : v 1 / Real.sin θ = -|v 1 / Real.sin θ| := by
        rw [abs_of_neg hv1_neg]; ring
      refine ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![θ, 2 * Real.pi - α], ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [WithLp.equiv]
        · exact hθ_range.1
        · exact hθ_range.2
        · linarith [hα_range.2, Real.pi_pos]
        · linarith [hα_range.1]
      · apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
        funext i
        have hsinα_eq : Real.sin α = -(v 1 / Real.sin θ) := by
          have habs : |Real.sin α| = |v 1 / Real.sin θ| := by
            rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, hsin_α_sq]
          rw [abs_of_nonneg hsin_α_nonneg, abs_of_neg hv1_neg] at habs
          linarith
        have hcos_2pi_α : Real.cos (2 * Real.pi - α) = Real.cos α := by
          rw [show 2 * Real.pi - α = -α + 2 * Real.pi from by ring, Real.cos_add_two_pi,
              Real.cos_neg]
        have hsin_2pi_α : Real.sin (2 * Real.pi - α) = -Real.sin α := by
          rw [show 2 * Real.pi - α = -α + 2 * Real.pi from by ring, Real.sin_add_two_pi,
              Real.sin_neg]
        fin_cases i <;>
          simp [sphericalParam, WithLp.equiv, hcos_α, hcos_2pi_α, hsin_2pi_α,
            hsinα_eq, hcos_θ]
        all_goals (field_simp; try ring)

/-- The parametrization domain `[0, π] × [0, 2π]` is bounded. -/
private lemma sphericalParam_domain_bounded :
    Bornology.IsBounded
      ({p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧
        0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi}) := by
  apply Metric.isBounded_iff.mpr
  refine ⟨2 * (3 * Real.pi), ?_⟩
  intro p hp q hq
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := hp
  obtain ⟨hq0, hq0', hq1, hq1'⟩ := hq
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  have hsum : (Finset.univ : Finset (Fin 2)).sum (fun i => ‖(p - q) i‖ ^ 2) =
      (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
    simp [Fin.sum_univ_two, sq_abs]
  rw [hsum]
  have hpq0 : (p 0 - q 0) ^ 2 ≤ Real.pi ^ 2 := by nlinarith
  have hpq1 : (p 1 - q 1) ^ 2 ≤ (2 * Real.pi) ^ 2 := by nlinarith
  have hsum_le : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 ≤
      Real.pi ^ 2 + (2 * Real.pi) ^ 2 := by linarith
  have hbound : Real.pi ^ 2 + (2 * Real.pi) ^ 2 = 5 * Real.pi ^ 2 := by ring
  rw [hbound] at hsum_le
  have h_sqrt_le : Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) ≤
      Real.sqrt (5 * Real.pi ^ 2) := Real.sqrt_le_sqrt hsum_le
  have h_simplify : Real.sqrt (5 * Real.pi ^ 2) = Real.sqrt 5 * Real.pi := by
    rw [show (5 : ℝ) * Real.pi ^ 2 = (Real.sqrt 5) ^ 2 * Real.pi ^ 2 by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]]
    rw [show (Real.sqrt 5) ^ 2 * Real.pi ^ 2 = (Real.sqrt 5 * Real.pi) ^ 2 by ring]
    rw [Real.sqrt_sq (by positivity)]
  rw [h_simplify] at h_sqrt_le
  have h5_le : Real.sqrt 5 ≤ 6 := by
    rw [show (6 : ℝ) = Real.sqrt 36 by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 6)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  calc Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2)
      ≤ Real.sqrt 5 * Real.pi := h_sqrt_le
    _ ≤ 6 * Real.pi := by nlinarith
    _ = 2 * (3 * Real.pi) := by ring

/-- `sphericalParam` is `3`-Lipschitz: each component is a product of bounded
1-Lipschitz functions, so each component is 2-Lipschitz, and aggregation by
the Euclidean norm gives `√(4 + 4 + 1) = 3`. -/
private lemma lipschitzWith_sphericalParam :
    LipschitzWith (3 : ℝ≥0) sphericalParam := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have hp_dist : ∀ i : Fin 2, |p i - q i| ≤ dist p q := by
    intro i
    have := PiLp.dist_apply_le p q i
    simpa [Real.dist_eq] using this
  have h_dist_nonneg : 0 ≤ dist p q := dist_nonneg
  rw [EuclideanSpace.dist_eq]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h_sum_eq : (Finset.univ : Finset (Fin 3)).sum
      (fun i => dist (sphericalParam p i) (sphericalParam q i) ^ 2) =
      (sphericalParam p 0 - sphericalParam q 0) ^ 2 +
      (sphericalParam p 1 - sphericalParam q 1) ^ 2 +
      (sphericalParam p 2 - sphericalParam q 2) ^ 2 := by
    simp [Fin.sum_univ_three, Real.dist_eq, sq_abs]
  rw [h_sum_eq]
  have hsp0 : sphericalParam p 0 = Real.sin (p 0) * Real.cos (p 1) := by
    simp [sphericalParam, WithLp.equiv]
  have hsp1 : sphericalParam p 1 = Real.sin (p 0) * Real.sin (p 1) := by
    simp [sphericalParam, WithLp.equiv]
  have hsp2 : sphericalParam p 2 = Real.cos (p 0) := by
    simp [sphericalParam, WithLp.equiv]
  have hsq0 : sphericalParam q 0 = Real.sin (q 0) * Real.cos (q 1) := by
    simp [sphericalParam, WithLp.equiv]
  have hsq1 : sphericalParam q 1 = Real.sin (q 0) * Real.sin (q 1) := by
    simp [sphericalParam, WithLp.equiv]
  have hsq2 : sphericalParam q 2 = Real.cos (q 0) := by
    simp [sphericalParam, WithLp.equiv]
  have hsin_diff_0 : |Real.sin (p 0) - Real.sin (q 0)| ≤ |p 0 - q 0| := by
    have := Real.lipschitzWith_sin.dist_le_mul (p 0) (q 0)
    simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
  have hcos_diff_0 : |Real.cos (p 0) - Real.cos (q 0)| ≤ |p 0 - q 0| := by
    have := Real.lipschitzWith_cos.dist_le_mul (p 0) (q 0)
    simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
  have hsin_diff_1 : |Real.sin (p 1) - Real.sin (q 1)| ≤ |p 1 - q 1| := by
    have := Real.lipschitzWith_sin.dist_le_mul (p 1) (q 1)
    simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
  have hcos_diff_1 : |Real.cos (p 1) - Real.cos (q 1)| ≤ |p 1 - q 1| := by
    have := Real.lipschitzWith_cos.dist_le_mul (p 1) (q 1)
    simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
  have habs_sin_p0 : |Real.sin (p 0)| ≤ 1 := Real.abs_sin_le_one _
  have habs_cos_q0 : |Real.cos (q 0)| ≤ 1 := Real.abs_cos_le_one _
  have habs_sin_q1 : |Real.sin (q 1)| ≤ 1 := Real.abs_sin_le_one _
  have habs_cos_q1 : |Real.cos (q 1)| ≤ 1 := Real.abs_cos_le_one _
  have hbound0 : |sphericalParam p 0 - sphericalParam q 0| ≤
      |p 0 - q 0| + |p 1 - q 1| := by
    rw [hsp0, hsq0]
    have hsplit : Real.sin (p 0) * Real.cos (p 1) - Real.sin (q 0) * Real.cos (q 1) =
        Real.sin (p 0) * (Real.cos (p 1) - Real.cos (q 1)) +
        Real.cos (q 1) * (Real.sin (p 0) - Real.sin (q 0)) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |Real.sin (p 0)| * |Real.cos (p 1) - Real.cos (q 1)| ≤
        1 * |p 1 - q 1| := by
      apply mul_le_mul habs_sin_p0 hcos_diff_1 (abs_nonneg _) (by norm_num)
    have h2 : |Real.cos (q 1)| * |Real.sin (p 0) - Real.sin (q 0)| ≤
        1 * |p 0 - q 0| := by
      apply mul_le_mul habs_cos_q1 hsin_diff_0 (abs_nonneg _) (by norm_num)
    linarith
  have hbound1 : |sphericalParam p 1 - sphericalParam q 1| ≤
      |p 0 - q 0| + |p 1 - q 1| := by
    rw [hsp1, hsq1]
    have hsplit : Real.sin (p 0) * Real.sin (p 1) - Real.sin (q 0) * Real.sin (q 1) =
        Real.sin (p 0) * (Real.sin (p 1) - Real.sin (q 1)) +
        Real.sin (q 1) * (Real.sin (p 0) - Real.sin (q 0)) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |Real.sin (p 0)| * |Real.sin (p 1) - Real.sin (q 1)| ≤
        1 * |p 1 - q 1| := by
      apply mul_le_mul habs_sin_p0 hsin_diff_1 (abs_nonneg _) (by norm_num)
    have h2 : |Real.sin (q 1)| * |Real.sin (p 0) - Real.sin (q 0)| ≤
        1 * |p 0 - q 0| := by
      apply mul_le_mul habs_sin_q1 hsin_diff_0 (abs_nonneg _) (by norm_num)
    linarith
  have hbound2 : |sphericalParam p 2 - sphericalParam q 2| ≤ |p 0 - q 0| := by
    rw [hsp2, hsq2]; exact hcos_diff_0
  set d0 := |p 0 - q 0|
  set d1 := |p 1 - q 1|
  have hd0 : d0 ≤ dist p q := hp_dist 0
  have hd1 : d1 ≤ dist p q := hp_dist 1
  have hd0_nn : 0 ≤ d0 := abs_nonneg _
  have hd1_nn : 0 ≤ d1 := abs_nonneg _
  have hsq0 : (sphericalParam p 0 - sphericalParam q 0) ^ 2 ≤ (d0 + d1) ^ 2 := by
    have h := hbound0
    have h_abs : |sphericalParam p 0 - sphericalParam q 0| ≤ d0 + d1 := h
    have hpos : 0 ≤ d0 + d1 := by linarith
    rw [sq_abs (sphericalParam p 0 - sphericalParam q 0) |>.symm]
    exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
  have hsq1' : (sphericalParam p 1 - sphericalParam q 1) ^ 2 ≤ (d0 + d1) ^ 2 := by
    rw [sq_abs (sphericalParam p 1 - sphericalParam q 1) |>.symm]
    exact pow_le_pow_left₀ (abs_nonneg _) hbound1 2
  have hsq2' : (sphericalParam p 2 - sphericalParam q 2) ^ 2 ≤ d0 ^ 2 := by
    rw [sq_abs (sphericalParam p 2 - sphericalParam q 2) |>.symm]
    exact pow_le_pow_left₀ (abs_nonneg _) hbound2 2
  have h_total : (sphericalParam p 0 - sphericalParam q 0) ^ 2 +
      (sphericalParam p 1 - sphericalParam q 1) ^ 2 +
      (sphericalParam p 2 - sphericalParam q 2) ^ 2 ≤
      2 * (d0 + d1) ^ 2 + d0 ^ 2 := by linarith
  have h_dpq_sq : (dist p q) ^ 2 ≥ d0 ^ 2 + d1 ^ 2 := by
    have hsum : (Finset.univ : Finset (Fin 2)).sum
        (fun i => dist (p i) (q i) ^ 2) = d0 ^ 2 + d1 ^ 2 := by
      simp [Fin.sum_univ_two, Real.dist_eq, sq_abs, d0, d1]
    have heq : dist p q ^ 2 = d0 ^ 2 + d1 ^ 2 := by
      rw [EuclideanSpace.dist_eq]
      rw [Real.sq_sqrt (by positivity)]
      exact hsum
    linarith [heq]
  have h_final : 2 * (d0 + d1) ^ 2 + d0 ^ 2 ≤ 9 * (dist p q) ^ 2 := by
    have hAMGM : (d0 - d1) ^ 2 ≥ 0 := sq_nonneg _
    have hsum_le_dist_sq : d0 ^ 2 + d1 ^ 2 ≤ (dist p q) ^ 2 := h_dpq_sq
    have h_expand : 2 * (d0 + d1) ^ 2 + d0 ^ 2 = 3 * d0 ^ 2 + 4 * d0 * d1 + 2 * d1 ^ 2 := by ring
    rw [h_expand]
    have h_step : 3 * d0 ^ 2 + 4 * d0 * d1 + 2 * d1 ^ 2 ≤ 5 * (d0 ^ 2 + d1 ^ 2) := by
      nlinarith [hAMGM]
    have h_step2 : 5 * (d0 ^ 2 + d1 ^ 2) ≤ 5 * (dist p q) ^ 2 := by linarith
    have h_step3 : 5 * (dist p q) ^ 2 ≤ 9 * (dist p q) ^ 2 := by
      have : 0 ≤ (dist p q) ^ 2 := sq_nonneg _
      linarith
    linarith
  have h_combined : (sphericalParam p 0 - sphericalParam q 0) ^ 2 +
      (sphericalParam p 1 - sphericalParam q 1) ^ 2 +
      (sphericalParam p 2 - sphericalParam q 2) ^ 2 ≤
      9 * (dist p q) ^ 2 := by linarith
  have h_rhs : ((3 : ℝ≥0) * dist p q : ℝ) ^ 2 = 9 * (dist p q) ^ 2 := by
    push_cast; ring
  rw [h_rhs]
  exact h_combined

/-- The 2-Hausdorff measure of `D = [0, π] × [0, 2π]` in `EuclideanSpace ℝ (Fin 2)`
is finite, since `D` is bounded. -/
private lemma hausdorffMeasure_domain_lt_top :
    (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 2)))
        {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧
          0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi} < ⊤ := by
  obtain ⟨R, hR⟩ := sphericalParam_domain_bounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))
  have h_vol_lt : (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧
        0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi} < ⊤ := by
    have h_sub : (volume : Measure (EuclideanSpace ℝ (Fin 2)))
        {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧
          0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi} ≤
        (volume : Measure (EuclideanSpace ℝ (Fin 2)))
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R) :=
      measure_mono hR
    refine lt_of_le_of_lt h_sub ?_
    exact measure_closedBall_lt_top
  have := hausdorffMeasure_lt_top_of_volume_lt_top (d := 2) h_vol_lt
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num] at this
  convert this

/-- The 2-Hausdorff measure of the unit sphere in `EuclideanSpace ℝ (Fin 3)` is finite. -/
private lemma hausdorffMeasure_sphere_lt_top :
    (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 3))) {v | ‖v‖ = 1} < ⊤ := by
  have h_lip := lipschitzWith_sphericalParam.hausdorffMeasure_image_le
    (d := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
    {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧
      0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi}
  have h_mono := measure_mono (μ := (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 3))))
    sphere_subset_sphericalParam_image
  have hD_lt := hausdorffMeasure_domain_lt_top
  have hK_lt : ((3 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) < ⊤ := by
    rw [show ((3 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofNNReal 3 from rfl]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simp)
  have h_prod_lt : ((3 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) *
      (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 2)))
        {p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧
          0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi} < ⊤ :=
    ENNReal.mul_lt_top hK_lt hD_lt
  exact lt_of_le_of_lt (le_trans h_mono h_lip) h_prod_lt

/-- The 2-dimensional Hausdorff measure of the unit sphere in
`EuclideanSpace ℝ (Fin 3)` is a positive real constant. -/
theorem hausdorff_two_unitSphere :
    ∃ c_n : ℝ, 0 < c_n ∧
      (μH[(2 : ℝ)] : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        {v | ‖v‖ = 1} = ENNReal.ofReal c_n := by
  set μS := (μH[(2 : ℝ)] : Measure (EuclideanSpace ℝ (Fin 3))) {v | ‖v‖ = 1}
  have hpos : 0 < μS := hausdorffMeasure_sphere_pos
  have hlt : μS < ⊤ := hausdorffMeasure_sphere_lt_top
  have hne_top : μS ≠ ⊤ := ne_of_lt hlt
  refine ⟨μS.toReal, ?_, ?_⟩
  · exact ENNReal.toReal_pos hpos.ne' hne_top
  · exact (ENNReal.ofReal_toReal hne_top).symm

end Kakeya.IsBesicovitch.HausdorffTwoUnitSphere

-- `IsBesicovitch` is defined in `Kakeya.IsBesicovitch` (imported above).

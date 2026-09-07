/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kestrel
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaIntegral
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.VectorMeasureInner
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.SphereHausdorff
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

private lemma cutoff_lhs_tendsto
    (μ : Measure (E n)) [IsFiniteMeasure μ]
    (D : VectorMeasure (E n) (E n))
    (f : E n → E n) (x ν0 : E n) (r : ℝ)
    (hD_eq : D = μ.withDensityᵥ f)
    (hf_int : Integrable f μ)
    (hf_norm_le_one : ∀ᵐ y ∂μ, ‖f y‖ ≤ 1)
    (hν0_unit : ‖ν0‖ = 1)
    (hr_pos : 0 < r) (hr_sphere : μ (sphere x r) = 0) :
    Tendsto
      (fun L : ℝ =>
        ∫ᵛ y, radialCutoff x r L y • ν0
          ∂[innerBilinear; D])
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (inner ℝ (D (closedBall x r)) ν0)) := by
  classical
  let η : ℝ → E n → ℝ := fun L => radialCutoff x r L
  let ψ : ℝ → E n → E n := fun L y => η L y • ν0
  let f_limit : E n → E n :=
    fun y => if y ∈ closedBall x r then ν0 else 0
  let g : ℝ → E n → ℝ := fun L y => inner ℝ (ψ L y) (f y)
  let g_limit : E n → ℝ := fun y => inner ℝ (f_limit y) (f y)
  have h_pointwise : ∀ y ∉ sphere x r,
      Tendsto (fun L : ℝ => ψ L y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_limit y)) := by
    intro y hy
    have h_dist : dist y x ≠ r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy
    by_cases h_in : y ∈ closedBall x r
    · have h_lt : dist y x < r := by
        have h_le : dist y x ≤ r := by
          simpa [closedBall] using h_in
        exact lt_of_le_of_ne h_le h_dist
      have h_nhds : Set.Ioi (0 : ℝ) ∈
          nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :=
        self_mem_nhdsWithin
      have h_eventually :
          (fun L : ℝ => ψ L y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            fun _ => ν0 := by
        filter_upwards [h_nhds] with L hL
        have hη : η L y = 1 :=
          radialCutoff_one_of_mem_closedBall hr_pos hL h_in
        simp [ψ, hη]
      have hf : f_limit y = ν0 := by
        dsimp only [f_limit]
        rw [if_pos h_in]
      rw [hf]
      exact tendsto_const_nhds.congr' h_eventually.symm
    · have h_gt : r < dist y x := by
        by_contra h
        exact h_in (by
          change dist y x ≤ r
          exact le_of_not_gt h)
      have h_small : Set.Ioo (0 : ℝ) (dist y x - r) ∈
          nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
        have h_pos : 0 < dist y x - r := by
          linarith
        apply mem_nhdsWithin.mpr
        refine ⟨Set.Iio (dist y x - r), isOpen_Iio, h_pos, ?_⟩
        intro z hz
        exact ⟨hz.2, hz.1⟩
      have h_eventually :
          (fun L : ℝ => ψ L y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            fun _ => 0 := by
        filter_upwards [h_small] with L hL
        have hnot : y ∉ ball x (r + L) := by
          intro hy
          have hy' : dist y x < r + L := hy
          have hL_lt : L < dist y x - r := hL.2
          linarith
        have hη : η L y = 0 :=
          radialCutoff_zero_of_not_mem_ball hr_pos hL.1 hnot
        simp [ψ, hη]
      have hf : f_limit y = 0 := by
        dsimp only [f_limit]
        rw [if_neg h_in]
      rw [hf]
      exact tendsto_const_nhds.congr' h_eventually.symm
  have h_sphere_ae : ∀ᵐ y ∂μ, y ∉ sphere x r := by
    rw [ae_iff]
    have hset : {y : E n | ¬ y ∉ sphere x r} = sphere x r := by
      ext y
      simp
    rwa [hset]
  have hψ_ae : ∀ᵐ y ∂μ,
      Tendsto (fun L : ℝ => ψ L y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_limit y)) := by
    filter_upwards [h_sphere_ae] with y hy
    exact h_pointwise y hy
  have hg_ae : ∀ᵐ y ∂μ,
      Tendsto (fun L : ℝ => g L y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g_limit y)) := by
    filter_upwards [hψ_ae] with y hy
    have hcont : Continuous (fun z : E n => inner ℝ z (f y)) := by
      fun_prop
    change Tendsto
      ((fun z : E n => inner ℝ z (f y)) ∘ fun L : ℝ => ψ L y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((fun z : E n => inner ℝ z (f y)) (f_limit y)))
    exact hcont.continuousAt.tendsto.comp hy
  have hg_bound :
      ∃ C : ℝ, ∀ᶠ L in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ y ∂μ, ‖g L y‖ ≤ C := by
    refine ⟨1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with L hL
    filter_upwards [hf_norm_le_one] with y hy
    have hψ : ‖ψ L y‖ ≤ 1 := by
      have hη0 : 0 ≤ η L y := smoothStep_range.1
      have hη1 : η L y ≤ 1 := smoothStep_range.2
      rw [show ‖ψ L y‖ = |η L y| * ‖ν0‖ by
        simp [ψ, norm_smul, Real.norm_eq_abs], hν0_unit, mul_one,
        abs_of_nonneg hη0]
      exact hη1
    calc
      ‖g L y‖ = |inner ℝ (ψ L y) (f y)| := by
        simp [g, Real.norm_eq_abs]
      _ ≤ ‖ψ L y‖ * ‖f y‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have hg_meas : ∀ᶠ L in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (g L) μ := by
    filter_upwards [self_mem_nhdsWithin] with L hL
    have hcont : Continuous (ψ L) :=
      (radialCutoff_contDiff hr_pos hL).continuous.smul continuous_const
    exact hcont.aestronglyMeasurable.inner hf_int.1
  have hψ_int : ∀ L : ℝ, 0 < L → Integrable (ψ L) μ := by
    intro L hL
    have hcont : Continuous (ψ L) :=
      (radialCutoff_contDiff hr_pos hL).continuous.smul continuous_const
    have hsupp : Function.support (ψ L) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ ball x (r + L)
      · exact ball_subset_closedBall h
      · have hη : η L y = 0 :=
          radialCutoff_zero_of_not_mem_ball hr_pos hL h
        exact False.elim (hy (by simp [ψ, hη]))
    exact hcont.integrable_of_hasCompactSupport
      ((isCompact_closedBall x (r + L)).of_isClosed_subset
        (isClosed_tsupport _)
        (closure_minimal hsupp isClosed_closedBall))
  have hlimit_int : Integrable f_limit μ := by
    have heq :
        f_limit = (closedBall x r).indicator fun _ : E n => ν0 := by
      funext y
      dsimp only [f_limit]
      by_cases h : y ∈ closedBall x r
      · rw [if_pos h, Set.indicator_apply, if_pos h]
      · rw [if_neg h, Set.indicator_apply, if_neg h]
    rw [heq]
    exact (integrable_const ν0).indicator isClosed_closedBall.measurableSet
  have hdct : Tendsto (fun L : ℝ => ∫ y, g L y ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ y, g_limit y ∂μ)) :=
    tendsto_integral_filter_of_norm_le_const hg_meas hg_bound hg_ae
  have hconv1 : ∀ L : ℝ, 0 < L →
      ∫ᵛ y, ψ L y ∂[innerBilinear; D] = ∫ y, g L y ∂μ := by
    intro L hL
    rw [hD_eq]
    exact integral_withDensityᵥ_inner hf_int hf_norm_le_one (hψ_int L hL)
  have hconv2 :
      ∫ᵛ y, f_limit y ∂[innerBilinear; D] =
        ∫ y, g_limit y ∂μ := by
    rw [hD_eq]
    exact integral_withDensityᵥ_inner hf_int hf_norm_le_one hlimit_int
  have heventually : ∀ᶠ L in nhdsWithin 0 (Set.Ioi 0),
      (∫ y, g L y ∂μ) = ∫ᵛ y, ψ L y ∂[innerBilinear; D] :=
    Filter.mem_of_superset self_mem_nhdsWithin fun L hL =>
      (hconv1 L hL).symm
  have hlhs : Tendsto
      (fun L : ℝ => ∫ᵛ y, ψ L y ∂[innerBilinear; D])
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ᵛ y, f_limit y ∂[innerBilinear; D])) := by
    rw [← hconv2] at hdct
    exact hdct.congr' heventually
  have hlimit :
      ∫ᵛ y, f_limit y ∂[innerBilinear; D] =
        inner ℝ (D (closedBall x r)) ν0 := by
    have hcb : MeasurableSet (closedBall x r) :=
      isClosed_closedBall.measurableSet
    have hglimit :
        g_limit = (closedBall x r).indicator
          fun y => inner ℝ ν0 (f y) := by
      funext y
      dsimp only [g_limit, f_limit]
      by_cases h : y ∈ closedBall x r
      · rw [if_pos h, Set.indicator_apply, if_pos h]
      · rw [if_neg h, Set.indicator_apply, if_neg h]
        simp only [inner_zero_left]
    have hDball : D (closedBall x r) =
        ∫ y in closedBall x r, f y ∂μ := by
      rw [hD_eq]
      exact withDensityᵥ_apply hf_int hcb
    rw [hconv2, hglimit, integral_indicator hcb, hDball,
      integral_inner hf_int.integrableOn ν0, real_inner_comm]
  rw [hlimit] at hlhs
  simpa [ψ, η] using hlhs

/-- **Cutoff inequality**: for a.e. r > 0,
`|inner(Dχ_U(closedBall x r), ν0)| ≤ C0 * r^(n-1)`
where `C0 = μHE[n-1](sphere(0,1)).toReal`. -/
lemma cutoff_inequality
    {U : Set (E n)} (hU : MeasurableSet U) (hBdd : Bornology.IsBounded U)
    (hfin : perimeter U < ⊤) (hn : 2 ≤ n) (x : E n) (ν0 : E n)
    (hν0_unit : ‖ν0‖ = 1) :
    ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      |inner ℝ ((distributionalDerivative U) (closedBall x r)) ν0| ≤
        (μHE[n - 1] (sphere (0 : E n) 1)).toReal * r ^ (n - 1) := by
  let D := distributionalDerivative U
  let μ := perimeterMeasure U
  let C0_ENN := μHE[n - 1] (sphere (0 : E n) 1)
  let C0 : ℝ := C0_ENN.toReal
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)

  have h_perim_eq : μ Set.univ = perimeter U := (perimeter_eq_variation U hfin).symm
  letI hμ_fin : IsFiniteMeasure μ :=
    ⟨by rw [h_perim_eq] <;> exact hfin⟩

  have hC0_lt_top : C0_ENN < ⊤ := unit_sphere_hausdorff_finite hn

  let f := measureTheoreticNormal U
  have hD_eq : D = μ.withDensityᵥ f := (measureTheoreticNormal_withDensity hfin).2
  have hf_int : Integrable f μ := (measureTheoreticNormal_withDensity hfin).1
  have hf_norm_one : ∀ᵐ y ∂μ, ‖f y‖ = 1 := norm_measureTheoreticNormal_eq_one hfin
  have hf_norm_le_one : ∀ᵐ y ∂μ, ‖f y‖ ≤ 1 := by
    filter_upwards [hf_norm_one] with y hy <;> rw [hy] <;> norm_num

  have h_sphere_null : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), μ (sphere x r) = 0 :=
    sphere_measure_null_ae x

  have h_fixed : ∀ (r : ℝ), 0 < r → μ (sphere x r) = 0 →
      |inner ℝ (D (closedBall x r)) ν0| ≤ C0 * r ^ (n - 1) := by
    intro r hr_pos hr_sphere

    let η : ℝ → E n → ℝ := fun L => radialCutoff x r L
    let ψ : ℝ → E n → E n := fun L y => η L y • ν0
    let w : ℝ → ℝ := fun s => |deriv smoothStep s|

    have hw_nonneg : ∀ t, 0 ≤ w t := fun t => abs_nonneg _
    have hw_int : ∫ t in (0 : ℝ)..1, w t = 1 := smoothStep_deriv_abs_integral
    have hw_support : ∀ t ∉ Set.Icc (0 : ℝ) 1, w t = 0 := by
      intro t ht
      have h : deriv smoothStep t = 0 := smoothStep_deriv_zero_outside ht
      simp [w, h]

    -- Step 1: Integral formula for each L > 0
    have h_eq : ∀ (L : ℝ), 0 < L →
        ∫ᵛ y, ψ L y ∂[innerBilinear; D] =
        ∫ y in U, fderiv ℝ (η L) y ν0 := by
      intro L hL
      have hη_smooth : ContDiff ℝ ∞ (η L) := radialCutoff_contDiff hr_pos hL
      have hν_const : ContDiff ℝ ∞ (fun (_ : E n) => ν0) := contDiff_const
      have hψ_smooth : ContDiff ℝ ∞ (ψ L) := hη_smooth.smul hν_const
      have hη_zero : ∀ y, y ∉ ball x (r + L) → η L y = 0 :=
        fun y hy => radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL) (h := hy)
      have hψ_support : Function.support (ψ L) ⊆ closedBall x (r + L) := by
        intro y hy
        by_cases h : y ∈ ball x (r + L)
        · exact ball_subset_closedBall h
        · have h2 : η L y = 0 := hη_zero y h
          have h3 : ψ L y = 0 := by simp [ψ, h2]
          simpa [Function.mem_support] using hy h3
      have hψ_compact : HasCompactSupport (ψ L) :=
        (isCompact_closedBall x (r + L)).of_isClosed_subset (isClosed_tsupport _)
          (closure_minimal hψ_support isClosed_closedBall)
      have h_div : ∀ y, divergence (ψ L) y = fderiv ℝ (η L) y ν0 := by
        intro y
        have h1 : divergence (ψ L) = fun y => fderiv ℝ (η L) y ν0 :=
          divergence_smul_const hη_smooth
        exact congrFun h1 y
      have h_main := distributionalDerivative_integral_formula U hfin (ψ L) hψ_smooth hψ_compact
      simpa [h_div] using h_main

    -- Step 2: Bound |∫_U fderiv η_L · ν0| ≤ ∫_U ‖fderiv η_L‖
    have h_bound : ∀ (L : ℝ), 0 < L →
        |∫ y in U, fderiv ℝ (η L) y ν0| ≤
        ∫ y in U, ‖fderiv ℝ (η L) y‖ := by
      intro L hL
      have hη_smooth : ContDiff ℝ ∞ (η L) := radialCutoff_contDiff hr_pos hL
      have h1 : ∀ y, |fderiv ℝ (η L) y ν0| ≤ ‖fderiv ℝ (η L) y‖ := by
        intro y
        have h2 : |fderiv ℝ (η L) y ν0| ≤ ‖fderiv ℝ (η L) y‖ * ‖ν0‖ :=
          ContinuousLinearMap.le_opNorm (fderiv ℝ (η L) y) ν0
        rw [hν0_unit] at h2 <;> linarith
      have hη1 : ContDiff ℝ 1 (η L) := ContDiff.of_le hη_smooth (by norm_num)
      have h_fderiv_cont : Continuous (fderiv ℝ (η L)) :=
        hη1.continuous_fderiv (by norm_num)
      have h_eval : Continuous (fun (g : E n →L[ℝ] ℝ) => g ν0) :=
        continuous_eval_const ν0
      have h_cont : Continuous (fun y : E n => fderiv ℝ (η L) y ν0) :=
        h_eval.comp h_fderiv_cont
      have h_fderiv_support : Function.support (fderiv ℝ (η L)) ⊆
          closedBall x (r + L) := by
        intro y hy
        by_cases h : y ∈ closedBall x (r + L)
        · exact h
        · have h_dist : r + L < dist y x := by
            simpa [closedBall, not_le] using h
          have h_dist_cont : Continuous (fun z : E n => dist z x) := by fun_prop
          have h4 : ∀ᶠ z in nhds y, r + L < dist z x :=
            h_dist_cont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h_dist)
          have h5 : ∀ᶠ z in nhds y, η L z = 0 := by
            filter_upwards [h4] with z hz
            have h6 : z ∉ ball x (r + L) := by
              simpa [ball, not_lt] using le_of_lt hz
            exact radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL) (h := h6)
          have h_const : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) y :=
            hasFDerivAt_const (0 : ℝ) y
          have h6 : HasFDerivAt (η L) (0 : E n →L[ℝ] ℝ) y :=
            h_const.congr_of_eventuallyEq h5
          have h7 : fderiv ℝ (η L) y = 0 := h6.fderiv
          simpa [Function.mem_support] using hy h7
      have h_support : Function.support (fun y : E n => fderiv ℝ (η L) y ν0) ⊆
          closedBall x (r + L) := by
        intro y hy
        have h8 : (fderiv ℝ (η L) y) ν0 ≠ 0 := by simpa [Function.mem_support] using hy
        have h9 : fderiv ℝ (η L) y ≠ 0 := by
          intro h10
          rw [h10] at h8
          simp at h8
        exact h_fderiv_support h9
      have h_cb : IsCompact (closedBall x (r + L)) := isCompact_closedBall x (r + L)
      have h_compact : HasCompactSupport (fun y : E n => fderiv ℝ (η L) y ν0) :=
        h_cb.of_isClosed_subset (isClosed_tsupport _)
          (closure_minimal h_support isClosed_closedBall)
      have h_int : Integrable (fun y : E n => fderiv ℝ (η L) y ν0) (volume.restrict U) :=
        h_cont.integrable_of_hasCompactSupport h_compact
      have h_norm_cont : Continuous (fun y : E n => ‖fderiv ℝ (η L) y‖) := h_fderiv_cont.norm
      have h_norm_support : Function.support (fun y : E n => ‖fderiv ℝ (η L) y‖) ⊆
          closedBall x (r + L) := by
        intro y hy
        have h7 : fderiv ℝ (η L) y ≠ 0 := by
          intro h8
          have h9 : ‖fderiv ℝ (η L) y‖ = 0 := by rw [h8] <;> simp
          exact hy h9
        exact h_fderiv_support h7
      have h_norm_compact : HasCompactSupport (fun y : E n => ‖fderiv ℝ (η L) y‖) :=
        h_cb.of_isClosed_subset (isClosed_tsupport _)
          (closure_minimal h_norm_support isClosed_closedBall)
      have h_norm_int : Integrable (fun y : E n => ‖fderiv ℝ (η L) y‖) (volume.restrict U) :=
        h_norm_cont.integrable_of_hasCompactSupport h_norm_compact
      have h_abs : |∫ y in U, fderiv ℝ (η L) y ν0| ≤ ∫ y in U, |fderiv ℝ (η L) y ν0| :=
        abs_integral_le_integral_abs
      have h_mono : ∫ y in U, |fderiv ℝ (η L) y ν0| ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ :=
        integral_mono_ae h_int.abs h_norm_int (by filter_upwards with z; exact h1 z)
      calc
        |∫ y in U, fderiv ℝ (η L) y ν0|
          ≤ ∫ y in U, |fderiv ℝ (η L) y ν0| := h_abs
        _ ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ := h_mono

    -- Step 3: Coarea bound for ∫_U ‖fderiv η_L‖
    have h_coarea : ∀ (L : ℝ), 0 < L →
        ∫ y in U, ‖fderiv ℝ (η L) y‖ ≤
        C0 * ∫ t in (0 : ℝ)..1, w t * (r + L * t) ^ (n - 1) := by
      intro L hL
      let A := U \ {x}
      have hA_meas : MeasurableSet A := hU.diff (measurableSet_singleton x)
      have hA_sub_U : A ⊆ U := by simp [A]
      have hA_bdd : Bornology.IsBounded A := by
        rcases hBdd with ⟨t, ht, hsub⟩
        exact ⟨t, ht, hsub.trans (Set.compl_subset_compl.mpr hA_sub_U)⟩
      have hA_sub : A ⊆ {y | 0 < infDist y ({x} : Set (E n))} := by
        intro y hy
        have h2 : y ≠ x := by simpa [A] using hy.2
        have h3 : 0 < dist y x := dist_pos.mpr h2
        have h4 : infDist y ({x} : Set (E n)) = dist y x := by
          simp [infDist_singleton] <;> rfl
        have h5 : 0 < infDist y ({x} : Set (E n)) := by
          rw [h4] <;> exact h3
        exact h5
      let g : ℝ → ℝ := fun t => w ((t - r) / L) / L
      let g' : ℝ → ENNReal := fun t => ENNReal.ofReal (g t)
      have hg_nonneg : ∀ t, 0 ≤ g t := by intro t; positivity
      have h_support_g : ∀ t ∉ Set.Icc r (r + L), g t = 0 := by
        intro t ht
        have h51 : t < r ∨ r + L < t := by
          simp only [Set.mem_Icc, not_and_or] at ht
          rcases ht with (h | h)
          · left; linarith
          · right; linarith
        have h5 : (t - r) / L ∉ Set.Icc (0 : ℝ) 1 := by
          rcases h51 with (h51 | h51)
          · have h52 : (t - r) / L < 0 := div_neg_of_neg_of_pos (by linarith) hL
            intro h53
            have h54 : 0 ≤ (t - r) / L := h53.1
            linarith
          · have h52 : 1 < (t - r) / L := by
              rw [one_lt_div hL] <;> linarith
            intro h53
            have h54 : (t - r) / L ≤ 1 := h53.2
            linarith
        have h6 : w ((t - r) / L) = 0 := hw_support ((t - r) / L) h5
        simp [g, h6]
      have h_grad_ae : ∀ᵐ (y : E n) ∂volume.restrict U,
          ‖fderiv ℝ (η L) y‖ ≤ g (dist y x) := by
        filter_upwards with y
        by_cases hy : y = x
        · rw [hy]
          have h_center : fderiv ℝ (η L) x = 0 := radialCutoff_fderiv_at_center hr_pos hL
          rw [h_center]
          have h_goal : ‖(0 : E n →L[ℝ] ℝ)‖ ≤ g (dist x x) := by
            simpa using hg_nonneg (dist x x)
          exact h_goal
        · have h : ‖fderiv ℝ (η L) y‖ ≤ w ((dist y x - r) / L) / L :=
            radialCutoff_fderiv_tight_bound hr_pos hL hy
          simpa [g, w] using h
      have hη_smooth2 : ContDiff ℝ ∞ (η L) := radialCutoff_contDiff hr_pos hL
      have hη2 : ContDiff ℝ 1 (η L) := ContDiff.of_le hη_smooth2 (by norm_num)
      have h_fderiv_cont2 : Continuous (fderiv ℝ (η L)) := hη2.continuous_fderiv (by norm_num)
      have h_norm_cont2 : Continuous (fun y : E n => ‖fderiv ℝ (η L) y‖) := h_fderiv_cont2.norm
      have h_fderiv_support2 : Function.support (fderiv ℝ (η L)) ⊆ closedBall x (r + L) := by
        intro y hy
        by_cases h : y ∈ closedBall x (r + L)
        · exact h
        · have h_dist : r + L < dist y x := by simpa [closedBall, not_le] using h
          have h_dist_cont : Continuous (fun z : E n => dist z x) := by fun_prop
          have h9 : ∀ᶠ z in nhds y, r + L < dist z x :=
            h_dist_cont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h_dist)
          have h10 : ∀ᶠ z in nhds y, η L z = 0 := by
            filter_upwards [h9] with z hz
            have h11 : z ∉ ball x (r + L) := by simpa [ball, not_lt] using le_of_lt hz
            exact radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL) (h := h11)
          have h_const : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) y :=
            hasFDerivAt_const (0 : ℝ) y
          have h11 : HasFDerivAt (η L) (0 : E n →L[ℝ] ℝ) y :=
            h_const.congr_of_eventuallyEq h10
          have h12 : fderiv ℝ (η L) y = 0 := h11.fderiv
          simpa [Function.mem_support] using hy h12
      have h_norm_support2 : Function.support (fun y : E n => ‖fderiv ℝ (η L) y‖) ⊆
          closedBall x (r + L) := by
        intro y hy
        have h7 : fderiv ℝ (η L) y ≠ 0 := by
          intro h8
          have h9 : ‖fderiv ℝ (η L) y‖ = 0 := by rw [h8] <;> simp
          exact hy h9
        exact h_fderiv_support2 h7
      have h_norm_compact2 : HasCompactSupport (fun y : E n => ‖fderiv ℝ (η L) y‖) :=
        (isCompact_closedBall x (r + L)).of_isClosed_subset (isClosed_tsupport _)
          (closure_minimal h_norm_support2 isClosed_closedBall)
      have h_norm_int2 : Integrable (fun y : E n => ‖fderiv ℝ (η L) y‖) (volume.restrict U) :=
        h_norm_cont2.integrable_of_hasCompactSupport h_norm_compact2
      have h2 : ∀ᵐ y ∂volume.restrict U,
          ENNReal.ofReal ‖fderiv ℝ (η L) y‖ ≤ g' (dist y x) := by
        filter_upwards [h_grad_ae] with y hy
        exact ENNReal.ofReal_le_ofReal hy
      have h3 : ∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ (η L) y‖ ≤
          ∫⁻ y in U, g' (dist y x) := lintegral_mono_ae h2
      have h4 : ∫ y in U, ‖fderiv ℝ (η L) y‖ =
          ENNReal.toReal (∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ (η L) y‖) := by
        rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (by filter_upwards with y; exact norm_nonneg _) h_norm_int2.1]
        <;> simp
      have h_ne_top : (∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ (η L) y‖) ≠ ⊤ := by
        have h_eq1 : (fun y : E n => ENNReal.ofReal ‖fderiv ℝ (η L) y‖) =
            fun y : E n => ‖fderiv ℝ (η L) y‖ₑ := by
          funext y
          simp
        rw [h_eq1]
        simpa using h_norm_int2.hasFiniteIntegral.ne
      have hUA_sub : U \ A ⊆ {x} := by
        intro y hy
        simp only [A, Set.mem_diff, Set.mem_singleton_iff] at hy
        have h_y_in_U : y ∈ U := hy.1
        have h_not : ¬(y ∈ U ∧ y ≠ x) := hy.2
        by_cases h : y = x
        · exact h
        · exfalso
          exact h_not ⟨h_y_in_U, h⟩
      have h6_null : volume (U \ A) = 0 := by
        have h7 : volume ({x} : Set (E n)) = 0 := by
          simpa using measure_singleton volume x
        exact measure_mono_null hUA_sub h7
      have h9_mset : MeasurableSet (U \ A) := hU.diff hA_meas
      have h8_disj : Disjoint A (U \ A) := by
        rw [Set.disjoint_left]
        intro y hy1 hy2
        exact hy2.2 hy1
      have h_union : A ∪ (U \ A) = U := by
        ext y
        simp only [A, Set.mem_union, Set.mem_diff]
        constructor
        · rintro (h | h) <;> exact h.1
        · intro hy
          by_cases h : y ∈ A
          · left; exact h
          · right; exact ⟨hy, h⟩
      have h5 : ∫⁻ y in U, g' (dist y x) = ∫⁻ y in A, g' (dist y x) := by
        let f : E n → ENNReal := fun y => g' (dist y x)
        have h_restrict : volume.restrict (A ∪ (U \ A)) = volume.restrict A + volume.restrict (U \ A) := by
          have h_inter_empty : A ∩ (U \ A) = ∅ := by
            rw [Set.disjoint_iff_inter_eq_empty] at h8_disj; exact h8_disj
          have h_eq := Measure.restrict_union_add_inter (μ := volume) A h9_mset
          have h_inter : volume.restrict (A ∩ (U \ A)) = 0 := by
            rw [h_inter_empty]; simp
          rw [h_inter] at h_eq
          simpa using h_eq
        have h10 : ∫⁻ y in (A ∪ (U \ A)), f y = (∫⁻ y in A, f y) + (∫⁻ y in (U \ A), f y) := by
          rw [h_restrict]
          exact MeasureTheory.lintegral_add_measure f (volume.restrict A) (volume.restrict (U \ A))
        have h11 : ∫⁻ y in U, g' (dist y x) = ∫⁻ y in (A ∪ (U \ A)), g' (dist y x) := by
          congr with z
          <;> rw [h_union]
        have h_f_eq : ∀ y, f y = g' (dist y x) := by intro y; rfl
        rw [h11]
        have h_eq1 : ∫⁻ y in (A ∪ (U \ A)), g' (dist y x) = ∫⁻ y in (A ∪ (U \ A)), f y := by
          rfl
        rw [h_eq1]
        rw [h10]
        have h12 : (∫⁻ y in (U \ A), f y) = 0 := by
          have h13 : volume.restrict (U \ A) = 0 := Measure.restrict_eq_zero.mpr h6_null
          rw [h13] <;> simp
        rw [h12]
        <;> simp [h_f_eq]
      have h_infDist_eq : ∀ y, infDist y ({x} : Set (E n)) = dist y x := by
        intro y; simp [infDist_singleton] <;> rfl
      have h_coarea1 : ∫⁻ y in A, g' (infDist y ({x} : Set (E n))) =
          ∫⁻ t, g' t * μHE[n - 1] {y ∈ A | infDist y ({x} : Set (E n)) = t} :=
        Perimeter.coarea_integral hn (isClosed_singleton) (singleton_nonempty x)
          hA_meas hA_bdd hA_sub (by fun_prop)
      have h6 : ∫⁻ y in A, g' (dist y x) =
          ∫⁻ t, g' t * μHE[n - 1] {y ∈ A | dist y x = t} := by
        simpa [h_infDist_eq] using h_coarea1
      have h7 : ∀ t, μHE[n - 1] {y ∈ A | dist y x = t} ≤ μHE[n - 1] (sphere x t) := by
        intro t
        have h_sub : {y ∈ A | dist y x = t} ⊆ sphere x t := by
          intro y hy; exact hy.2
        exact measure_mono h_sub
      -- Bound sphere measure a.e. (avoid t=0 singleton issue)
      have h8_ae : ∀ᵐ (t : ℝ) ∂volume,
          μHE[n - 1] (sphere x t) ≤ C0_ENN * ENNReal.ofReal (t ^ (n - 1)) := by
        filter_upwards [show ∀ᵐ (t : ℝ) ∂volume, t ≠ 0 from by
          simpa [ae_iff] using measure_singleton volume 0] with t ht
        by_cases hpos : 0 < t
        · rw [sphere_hausdorff_scale x hpos]
          <;> rw [mul_comm] <;> rfl
        · have hneg : t < 0 := by
            by_contra h
            have : t = 0 := by linarith
            exact ht this
          have h9 : sphere x t = ∅ := by
            ext y
            simp only [Set.mem_empty_iff_false, iff_false]
            intro h
            have h10 : 0 ≤ dist y x := dist_nonneg
            have h11 : dist y x = t := h
            rw [h11] at h10
            linarith
          rw [h9] <;> simp
      have h9_ae : ∀ᵐ (t : ℝ) ∂volume,
          g' t * μHE[n - 1] {y ∈ A | dist y x = t} ≤
          g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) := by
        filter_upwards [h8_ae] with t h8t
        exact mul_le_mul_left' (h7 t |>.trans h8t) (g' t)
      have h_main_lintegral : (∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ (η L) y‖) ≤
          C0_ENN * ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1)) := by
        calc
          (∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ (η L) y‖)
            ≤ ∫⁻ y in U, g' (dist y x) := h3
          _ = ∫⁻ y in A, g' (dist y x) := by rw [h5]
          _ = ∫⁻ t, g' t * μHE[n - 1] {y ∈ A | dist y x = t} := by rw [h6]
          _ ≤ ∫⁻ t, g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) :=
            lintegral_mono_ae h9_ae
          _ = ∫⁻ t in Set.Icc r (r + L), g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) := by
            have h11 : ∀ t ∉ Set.Icc r (r + L),
                g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) = 0 := by
              intro t ht
              have h12 : g t = 0 := h_support_g t ht
              have h13 : g' t = 0 := by
                simpa [g'] using congr_arg ENNReal.ofReal h12
              rw [h13] <;> simp
            rw [← lintegral_add_compl _ (isCompact_Icc.measurableSet)]
            have h14 : ∫⁻ t in (Set.Icc r (r + L))ᶜ,
                g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) = 0 := by
              have h15 : ∀ t ∈ (Set.Icc r (r + L))ᶜ,
                  g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) = 0 := by
                intro t ht
                exact h11 t ht
              have h_Icc_meas : MeasurableSet (Set.Icc r (r + L)) := isCompact_Icc.measurableSet
              have h16 : ∀ᵐ (t : ℝ) ∂volume.restrict ((Set.Icc r (r + L))ᶜ),
                  g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) = 0 := by
                filter_upwards [ae_restrict_mem h_Icc_meas.compl] with t ht
                exact h15 t ht
              have h_ae_meas : AEMeasurable (fun t : ℝ => g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))))
                  (volume.restrict ((Set.Icc r (r + L))ᶜ)) := by fun_prop
              rw [lintegral_eq_zero_iff' h_ae_meas]
              exact h16
            rw [h14, add_zero]
          _ = C0_ENN * ∫⁻ t in Set.Icc r (r + L), g' t * ENNReal.ofReal (t ^ (n - 1)) := by
            have h_comm : ∀ t, g' t * (C0_ENN * ENNReal.ofReal (t ^ (n - 1))) =
                C0_ENN * (g' t * ENNReal.ofReal (t ^ (n - 1))) := by
              intro t
              simp [mul_assoc, mul_left_comm]
            rw [lintegral_congr_ae (ae_of_all _ h_comm)]
            have h_mul : ∫⁻ t in Set.Icc r (r + L), C0_ENN * (g' t * ENNReal.ofReal (t ^ (n - 1))) =
                C0_ENN * ∫⁻ t in Set.Icc r (r + L), g' t * ENNReal.ofReal (t ^ (n - 1)) := by
              have h_meas : AEMeasurable (fun t : ℝ => g' t * ENNReal.ofReal (t ^ (n - 1)))
                  (volume.restrict (Set.Icc r (r + L))) := by fun_prop
              exact lintegral_const_mul'' C0_ENN h_meas
            exact h_mul
          _ = C0_ENN * ∫⁻ t in Set.Icc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1)) := by
            have h_mul_eq : ∀ t, g' t * ENNReal.ofReal (t ^ (n - 1)) =
                ENNReal.ofReal (g t * t ^ (n - 1)) := by
              intro t
              by_cases ht : 0 ≤ t
              · have h_nonneg_t : 0 ≤ t ^ (n - 1) := by positivity
                have h_nonneg_g : 0 ≤ g t := hg_nonneg t
                rw [← ENNReal.ofReal_mul h_nonneg_g, mul_comm] <;> rfl
              · have h_neg : t < 0 := by linarith
                have h_notin : t ∉ Set.Icc r (r + L) := by
                  intro h_cont
                  have : r ≤ t := h_cont.1
                  linarith [hr_pos]
                have hg0 : g t = 0 := h_support_g t h_notin
                have hg'0 : g' t = 0 := by simpa [g'] using congr_arg ENNReal.ofReal hg0
                rw [hg'0, hg0] <;> simp
            rw [lintegral_congr_ae (ae_of_all _ h_mul_eq)]
          _ = C0_ENN * ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1)) := by
            have h_Icc_eq_Ioc : ∫⁻ t in Set.Icc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1)) =
                ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1)) := by
              have h1 : Set.Icc r (r + L) = Set.Ioc r (r + L) ∪ {r} := by
                ext t
                simp only [Set.mem_Icc, Set.mem_Ioc, Set.mem_union, Set.mem_singleton_iff]
                constructor
                · intro h
                  by_cases h2 : t = r
                  · right; exact h2
                  · left
                    have h2' : r ≠ t := by
                      intro h
                      exact h2 (h.symm)
                    exact ⟨lt_of_le_of_ne h.1 h2', h.2⟩
                · rintro (h | h)
                  · exact ⟨le_of_lt h.1, h.2⟩
                  · rw [h] <;> exact ⟨by linarith, by linarith⟩
              rw [h1]
              have h_disj : Disjoint (Set.Ioc r (r + L)) ({r} : Set ℝ) := by
                rw [Set.disjoint_left]
                intro t ht1 ht2
                simp only [Set.mem_singleton_iff] at ht2
                rw [ht2] at ht1
                <;> simp at ht1 <;> linarith
              have h_singleton_meas : MeasurableSet ({r} : Set ℝ) := measurableSet_singleton r
              have h_Ioc_meas : MeasurableSet (Set.Ioc r (r + L)) := measurableSet_Ioc
              let f : ℝ → ENNReal := fun t => ENNReal.ofReal (g t * t ^ (n - 1))
              have h_restrict2 : volume.restrict (Set.Ioc r (r + L) ∪ {r}) =
                  volume.restrict (Set.Ioc r (r + L)) + volume.restrict ({r} : Set ℝ) := by
                have h_inter_empty2 : Set.Ioc r (r + L) ∩ ({r} : Set ℝ) = ∅ := by
                  rw [Set.disjoint_iff_inter_eq_empty] at h_disj; exact h_disj
                have h_eq2 := Measure.restrict_union_add_inter (μ := volume) (Set.Ioc r (r + L)) h_singleton_meas
                have h_inter2 : volume.restrict (Set.Ioc r (r + L) ∩ ({r} : Set ℝ)) = 0 := by
                  rw [h_inter_empty2]; simp
                rw [h_inter2] at h_eq2
                simpa using h_eq2
              have h_union_int : ∫⁻ t in (Set.Ioc r (r + L) ∪ {r}), f t =
                  (∫⁻ t in Set.Ioc r (r + L), f t) + (∫⁻ t in ({r} : Set ℝ), f t) := by
                rw [h_restrict2]
                exact MeasureTheory.lintegral_add_measure f (volume.restrict (Set.Ioc r (r + L))) (volume.restrict ({r} : Set ℝ))
              rw [h_union_int]
              have h_f_eq : ∀ t, f t = ENNReal.ofReal (g t * t ^ (n - 1)) := by intro t; rfl
              have h2 : ∫⁻ t in ({r} : Set ℝ), f t = 0 := by
                have h3 : volume.restrict ({r} : Set ℝ) = 0 :=
                  Measure.restrict_eq_zero.mpr (by simp)
                rw [h3] <;> simp
              rw [h2]
              have h4 : ∫⁻ t in Set.Ioc r (r + L), f t =
                  ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1)) := by
                rfl
              rw [h4] <;> simp
            rw [h_Icc_eq_Ioc]
          _ = C0_ENN * ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1)) := by
            have h_nonneg2 : ∀ t ∈ Set.Ioc r (r + L), 0 ≤ g t * t ^ (n - 1) := by
              intro t ht
              have h_t_pos : 0 < t := by linarith [hr_pos, ht.1]
              have h_gt : 0 ≤ g t := hg_nonneg t
              positivity
            have h_cont2 : Continuous (fun t : ℝ => g t * t ^ (n - 1)) := by
              have hg_cont : Continuous g := by
                have hw_cont' : Continuous w :=
                  (smoothStep_contDiff.continuous_deriv (by norm_num)).abs
                have hL_ne : L ≠ 0 := hL.ne'
                have h_inner : Continuous (fun t : ℝ => (t - r) / L) := by
                  fun_prop
                exact hw_cont'.comp h_inner |>.div continuous_const (by simp [hL_ne])
              exact hg_cont.mul (continuous_pow (n - 1))
            have h_int2 : IntervalIntegrable (fun t : ℝ => g t * t ^ (n - 1)) volume r (r + L) :=
              h_cont2.intervalIntegrable _ _
            have h_restrict_int : Integrable (fun t : ℝ => g t * t ^ (n - 1))
                (volume.restrict (Set.Ioc r (r + L))) :=
              h_int2.1
            have h_Ioc_meas2 : MeasurableSet (Set.Ioc r (r + L)) := measurableSet_Ioc
            have h_nonneg_ae : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc r (r + L)),
                0 ≤ g t * t ^ (n - 1) := by
              have h_mem : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc r (r + L)), t ∈ Set.Ioc r (r + L) :=
                ae_restrict_mem h_Ioc_meas2
              exact h_mem.mono (fun t ht => h_nonneg2 t ht)
            have h6 : (fun t : ℝ => ENNReal.ofReal (g t * t ^ (n - 1))) =ᵐ[volume.restrict (Set.Ioc r (r + L))]
                fun t : ℝ => ‖g t * t ^ (n - 1)‖ₑ := by
              have h_mem : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc r (r + L)), t ∈ Set.Ioc r (r + L) :=
                ae_restrict_mem h_Ioc_meas2
              filter_upwards [h_mem] with t ht
              have h7 : 0 ≤ g t * t ^ (n - 1) := h_nonneg2 t ht
              have h10 : ‖g t * t ^ (n - 1)‖ = g t * t ^ (n - 1) := by
                rw [Real.norm_eq_abs, abs_of_nonneg h7]
              have h11 : ‖g t * t ^ (n - 1)‖ₑ = ENNReal.ofReal ‖g t * t ^ (n - 1)‖ := by
                have h12 : ‖g t * t ^ (n - 1)‖ₑ = ENNReal.ofReal (g t * t ^ (n - 1)) :=
                  Real.enorm_eq_ofReal h7
                rw [h12, h10]
              rw [h11, h10]
            have h_fin : (∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1))) ≠ ⊤ := by
              have h9 : (∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1))) =
                  ∫⁻ t in Set.Ioc r (r + L), ‖g t * t ^ (n - 1)‖ₑ :=
                lintegral_congr_ae h6
              rw [h9]
              exact h_restrict_int.hasFiniteIntegral.ne
            have h_eq3 : ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1)) =
                ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1)) := by
              rw [intervalIntegral.integral_of_le (by linarith)]
              have h4 : ∫ t in Set.Ioc r (r + L), g t * t ^ (n - 1) ∂volume =
                  ENNReal.toReal (∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * t ^ (n - 1))) := by
                rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg_ae h_restrict_int.aestronglyMeasurable]
                <;> simp [Real.norm_eq_abs, abs_of_nonneg]
                <;> rfl
              rw [h4]
              rw [ENNReal.ofReal_toReal h_fin]
            rw [←h_eq3]
      have h_b_ne_top : (C0_ENN * ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1))) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · exact hC0_lt_top.ne
        · exact ENNReal.ofReal_ne_top
      have h13 : ∫ t in r..(r + L), g t * t ^ (n - 1) =
          ∫ t in (0 : ℝ)..1, w t * (r + L * t) ^ (n - 1) := by
        have h14 : ∫ t in r..(r + L), g t * t ^ (n - 1) =
            ∫ t in r..(r + L), (w ((t - r) / L) / L) * t ^ (n - 1) := by
          apply intervalIntegral.integral_congr
          intro t _
          rfl
        rw [h14]
        let H : ℝ → ℝ := fun t : ℝ => (w ((t - r) / L) / L) * t ^ (n - 1)
        let F : ℝ → ℝ := fun u : ℝ => w u * (r + L * u) ^ (n - 1)
        have hL_ne : L ≠ 0 := hL.ne'
        have hH_at : ∀ u : ℝ, H (L * u + r) = F u / L := by
          intro u
          have h_div : ((L * u + r) - r) / L = u := by field_simp [hL_ne] <;> ring
          have h_comm : r + L * u = L * u + r := by ring
          dsimp only [H, F]
          calc
            (w (((L * u + r) - r) / L) / L) * (L * u + r) ^ (n - 1)
              = (w u / L) * (L * u + r) ^ (n - 1) := by rw [h_div]
            _ = (w u * (r + L * u) ^ (n - 1)) / L := by rw [h_comm] <;> ring
        have h15_raw := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := L) (d := r) H (by linarith)
        have h15 : ∫ u in (0 : ℝ)..1, H (L * u + r) =
            L⁻¹ • ∫ t in r..(r + L), H t := by
          have h_end1 : L * (0 : ℝ) + r = r := by ring
          have h_end2 : L * (1 : ℝ) + r = r + L := by ring
          have h_int_eq : ∫ t in (L * (0 : ℝ) + r)..(L * (1 : ℝ) + r), H t =
              ∫ t in r..(r + L), H t := by
            congr <;> ring
          rw [h15_raw, h_int_eq]
        have h16 : ∫ u in (0 : ℝ)..1, H (L * u + r) = ∫ u in (0 : ℝ)..1, F u / L := by
          apply intervalIntegral.integral_congr
          intro u _
          exact hH_at u
        have h17 : ∫ u in (0 : ℝ)..1, F u / L = L⁻¹ • ∫ t in r..(r + L), H t := by
          rw [←h16, h15]
        have h18 : ∫ t in r..(r + L), H t = ∫ u in (0 : ℝ)..1, F u := by
          have h19 : L⁻¹ • ∫ t in r..(r + L), H t = ∫ u in (0 : ℝ)..1, F u / L := h17.symm
          have h_mult : L * (L⁻¹ • ∫ t in r..(r + L), H t) = L * (∫ u in (0 : ℝ)..1, F u / L) :=
            congr_arg (fun x : ℝ => L * x) h19
          have h_left : L * (L⁻¹ • ∫ t in r..(r + L), H t) = ∫ t in r..(r + L), H t := by
            simp [smul_eq_mul, hL_ne] <;> field_simp [hL_ne] <;> ring
          have h_right : L * (∫ u in (0 : ℝ)..1, F u / L) = ∫ u in (0 : ℝ)..1, F u := by
            simp [smul_eq_mul, hL_ne] <;> field_simp [hL_ne] <;> ring
          calc
            ∫ t in r..(r + L), H t
              = L * (L⁻¹ • ∫ t in r..(r + L), H t) := h_left.symm
            _ = L * (∫ u in (0 : ℝ)..1, F u / L) := h_mult
            _ = ∫ u in (0 : ℝ)..1, F u := h_right
        exact h18
      calc
        ∫ y in U, ‖fderiv ℝ (η L) y‖
          = ENNReal.toReal (∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ (η L) y‖) := h4
        _ ≤ ENNReal.toReal (C0_ENN * ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1))) :=
          ENNReal.toReal_mono h_b_ne_top h_main_lintegral
        _ = C0 * ∫ t in r..(r + L), g t * t ^ (n - 1) := by
          have h_mul : (C0_ENN * ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1))).toReal =
              C0 * (∫ t in r..(r + L), g t * t ^ (n - 1)) := by
            have h_toReal_mul : (C0_ENN * ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1))).toReal =
                C0_ENN.toReal * (ENNReal.ofReal (∫ t in r..(r + L), g t * t ^ (n - 1))).toReal :=
              ENNReal.toReal_mul
            have h_int_nonneg : 0 ≤ ∫ t in r..(r + L), g t * t ^ (n - 1) := by
              have h_le : r ≤ r + L := by linarith [hL]
              have h : ∀ t ∈ Set.uIoc r (r + L), 0 ≤ g t * t ^ (n - 1) := by
                intro t ht
                have h_t_in : t ∈ Set.Ioc r (r + L) := by
                  simpa [Set.uIoc_of_le h_le] using ht
                have h_t_pos : 0 < t := by linarith [hr_pos, h_t_in.1]
                have h_gt : 0 ≤ g t := hg_nonneg t
                positivity
              have h' : ∀ t ∈ Set.Icc r (r + L), 0 ≤ g t * t ^ (n - 1) := by
                intro t ht
                have h_t_nonneg : 0 ≤ t := by linarith [hr_pos, ht.1]
                have h_gt : 0 ≤ g t := hg_nonneg t
                positivity
              exact intervalIntegral.integral_nonneg h_le h'
            rw [h_toReal_mul]
            rw [ENNReal.toReal_ofReal h_int_nonneg]
            <;> rfl
          exact h_mul
        _ = C0 * ∫ t in (0 : ℝ)..1, w t * (r + L * t) ^ (n - 1) := by rw [h13]

    -- Step 4: RHS limit as L → 0
    have h_rhs_limit : Tendsto (fun L : ℝ => C0 * ∫ t in (0 : ℝ)..1, w t * (r + L * t) ^ (n - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (C0 * r ^ (n - 1))) := by
      have hw_cont : Continuous w :=
        (smoothStep_contDiff.continuous_deriv (by norm_num)).abs
      let F : ℝ → ℝ → ℝ := fun L t => w t * (r + L * t) ^ (n - 1)
      let bound : ℝ → ℝ := fun t => w t * (r + 1) ^ (n - 1)
      have hF_meas : ∀ (L : ℝ), AEStronglyMeasurable (F L) (volume.restrict (Set.uIoc 0 1)) := by
        intro L
        have h_cont : Continuous (F L) := by
          change Continuous (fun t => w t * (r + L * t) ^ (n - 1))
          exact hw_cont.mul ((continuous_const.add (continuous_const.mul continuous_id)).pow _)
        exact h_cont.aestronglyMeasurable
      have h_bound_nhds : ∀ᶠ (L : ℝ) in nhds 0,
          ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ‖F L t‖ ≤ bound t := by
        have h_nhds : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
        filter_upwards [h_nhds] with L hL
        filter_upwards with t
        intro ht
        have h_t_in : t ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        have h_t1 : 0 < t := h_t_in.1
        have h_t2 : t ≤ 1 := h_t_in.2
        have h_abs : |r + L * t| ≤ r + 1 := by
          calc
            |r + L * t| ≤ |r| + |L * t| := by
              simpa [Real.norm_eq_abs] using norm_add_le r (L * t)
            _ = r + |L * t| := by rw [abs_of_pos hr_pos]
            _ = r + |L| * |t| := by rw [abs_mul]
            _ ≤ r + 1 := by
              have hL1 : |L| < 1 := abs_lt.mpr hL
              have ht1 : |t| ≤ 1 := by
                rw [abs_le] <;> constructor <;> linarith
              have h_mul : |L| * |t| < 1 := by
                calc
                  |L| * |t| ≤ |L| * 1 := by gcongr <;> linarith
                  _ = |L| := by ring
                  _ < 1 := hL1
              linarith
        have h5 : |r + L * t| ^ (n - 1) ≤ (r + 1) ^ (n - 1) := by
          have h6 : 0 ≤ |r + L * t| := by positivity
          gcongr
        have h6 : 0 ≤ w t := abs_nonneg _
        simpa [F, bound, Real.norm_eq_abs, abs_mul, abs_of_nonneg h6] using
          mul_le_mul_of_nonneg_left h5 h6
      have h_bound_int : IntervalIntegrable bound volume 0 1 := by
        have h_cont : Continuous bound := by
          change Continuous (fun t => w t * (r + 1) ^ (n - 1))
          exact hw_cont.mul continuous_const
        exact h_cont.intervalIntegrable 0 1
      have h_cont_at : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
          ContinuousAt (fun L : ℝ => F L t) 0 := by
        filter_upwards with t
        intro _
        have h : Continuous (fun L : ℝ => F L t) := by
          change Continuous (fun L => w t * (r + L * t) ^ (n - 1))
          exact continuous_const.mul ((continuous_const.add (continuous_id.mul continuous_const)).pow _)
        exact h.continuousAt
      have h_unif_at : ContinuousAt (fun L : ℝ => ∫ t in (0 : ℝ)..1, F L t) 0 :=
        intervalIntegral.continuousAt_of_dominated_interval
          (by filter_upwards with L; exact hF_meas L)
          h_bound_nhds h_bound_int h_cont_at
      have h_val : (fun L : ℝ => ∫ t in (0 : ℝ)..1, F L t) 0 =
          ∫ t in (0 : ℝ)..1, w t * r ^ (n - 1) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp [F] <;> ring
      have h_final : ∫ t in (0 : ℝ)..1, w t * r ^ (n - 1) = r ^ (n - 1) := by
        have h_comm : (fun t : ℝ => w t * r ^ (n - 1)) = fun t : ℝ => r ^ (n - 1) * w t := by
          funext t; ring
        rw [h_comm, intervalIntegral.integral_const_mul, hw_int] <;> ring
      have h9 : (fun L : ℝ => ∫ t in (0 : ℝ)..1, F L t) 0 = r ^ (n - 1) := by
        rw [h_val, h_final]
      have h_tendsto_nhds : Tendsto (fun L : ℝ => ∫ t in (0 : ℝ)..1, F L t)
          (nhds 0) (nhds ((fun L : ℝ => ∫ t in (0 : ℝ)..1, F L t) 0)) := h_unif_at.tendsto
      have h_tendsto : Tendsto (fun L : ℝ => ∫ t in (0 : ℝ)..1, F L t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (r ^ (n - 1))) := by
        have h10 : (fun L : ℝ => ∫ t in (0 : ℝ)..1, F L t) 0 = r ^ (n - 1) := h9
        rw [h10] at h_tendsto_nhds
        exact h_tendsto_nhds.mono_left inf_le_left
      exact h_tendsto.const_mul C0

    -- Step 5: LHS limit as L → 0 via DCT
    have h_lhs_limit : Tendsto
        (fun L : ℝ => ∫ᵛ y, ψ L y ∂[innerBilinear; D])
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (inner ℝ (D (closedBall x r)) ν0)) := by
      simpa [ψ, η] using cutoff_lhs_tendsto
        μ D f x ν0 r hD_eq hf_int hf_norm_le_one
        hν0_unit hr_pos hr_sphere
    -- Step 6: Combine limits and bounds
    have h_final_bound : |inner ℝ (D (closedBall x r)) ν0| ≤ C0 * r ^ (n - 1) := by
      have h_main_bound : ∀ (L : ℝ), 0 < L →
          |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤ C0 * ∫ t in (0 : ℝ)..1, w t * (r + L * t) ^ (n - 1) := by
        intro L hL
        calc
          |∫ᵛ y, ψ L y ∂[innerBilinear; D]|
            = |∫ y in U, fderiv ℝ (η L) y ν0| := by rw [h_eq L hL]
          _ ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ := h_bound L hL
          _ ≤ C0 * ∫ t in (0 : ℝ)..1, w t * (r + L * t) ^ (n - 1) := h_coarea L hL
      have h_eventually : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
          |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤ C0 * ∫ t in (0 : ℝ)..1, w t * (r + L * t) ^ (n - 1) := by
        filter_upwards [self_mem_nhdsWithin] with L hL
        exact h_main_bound L hL
      exact le_of_tendsto_of_tendsto h_lhs_limit.abs h_rhs_limit h_eventually

    exact h_final_bound

  have h_pos : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), 0 < r := by
    filter_upwards [ae_restrict_mem isOpen_Ioi.measurableSet] with r hr
    exact hr
  filter_upwards [h_pos, h_sphere_null] with r hr_pos hr_sphere
  exact h_fixed r hr_pos hr_sphere

end Geometry.StructureTheorem

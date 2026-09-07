import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.LocalTranslationBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.LocalScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- `perimeterIn S Ω ≤ perimeterMeasure S Ω` for any set `Ω`. -/
lemma perimeterIn_le_perimeterMeasure' {S : Set (E n)} {Ω : Set (E n)}
    (hfin : perimeter S < ⊤) :
    perimeterIn S Ω ≤ perimeterMeasure S Ω := by
  let D := distributionalDerivative S
  let μ := perimeterMeasure S
  have hD_eq : D.variation = μ := by rfl
  have h_main : ∀ (Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω}),
      ENNReal.ofReal |∫ x in S, divergence Φ.val.toFun x| ≤ μ Ω := by
    intro Φ
    let φ := Φ.val.toFun
    have hφ_smooth := Φ.val.smooth
    have hφ_support : Function.support φ ⊆ Ω := Φ.property
    have hφ_bound : ∀ x, ‖φ x‖ ≤ 1 := Φ.val.bound
    have hφ_cont : Continuous φ := Φ.val.smooth.continuous
    have hφ_csupport : HasCompactSupport φ := Φ.val.compact
    have h_int : ∫ᵛ x, φ x ∂[innerBilinear; D] = ∫ x in S, divergence φ x :=
      distributionalDerivative_integral_formula S hfin φ hφ_smooth hφ_csupport
    have hμ_fin : μ Set.univ < ⊤ := by
      rw [← perimeter_eq_variation S hfin] <;> exact hfin
    letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
    have h_int' : Integrable φ μ := hφ_cont.integrable_of_hasCompactSupport hφ_csupport
    have hφ_int : D.Integrable φ := by
      have h_eq : D.variation = μ := by rfl
      simpa [VectorMeasure.Integrable, h_eq] using h_int'
    have h1 : |∫ᵛ x, φ x ∂[innerBilinear; D]| ≤ ∫ x, ‖φ x‖ ∂μ :=
      vectorMeasure_integral_abs_bound D φ hφ_int
    let s := Function.support φ
    have hs_open : IsOpen s := Continuous.isOpen_support hφ_cont
    have hs_meas : MeasurableSet s := hs_open.measurableSet
    have h_sub_s : s ⊆ Ω := hφ_support
    have h3 : ∀ x, ‖φ x‖ ≤ Set.indicator s (fun _ => (1 : ℝ)) x := by
      intro x
      classical
      by_cases hx : x ∈ s
      · have h_indic : Set.indicator s (fun _ => (1 : ℝ)) x = 1 := by
          simp [hx]
        rw [h_indic]
        exact hφ_bound x
      · have h_indic : Set.indicator s (fun _ => (1 : ℝ)) x = 0 := by
          rw [Set.indicator_apply, if_neg hx]
        have h4 : φ x = 0 := by
          have h5 : x ∉ Function.support φ := hx
          simpa [Function.mem_support] using h5
        rw [h_indic, h4] <;> norm_num
    have h4 : Integrable (fun x => ‖φ x‖) μ := h_int'.norm
    haveI : IsFiniteMeasure (μ.restrict s) := by
      have h : (μ.restrict s) Set.univ = μ s := by simp
      have h' : (μ.restrict s) Set.univ < ⊤ := by
        rw [h]
        exact measure_lt_top μ s
      exact ⟨h'⟩
    have h5 : Integrable (Set.indicator s (fun _ => (1 : ℝ))) μ := by
      rw [integrable_indicator_iff hs_meas]
      exact integrableOn_const
    have h6 : ∫ x, ‖φ x‖ ∂μ ≤ ∫ x, Set.indicator s (fun _ => (1 : ℝ)) x ∂μ :=
      integral_mono h4 h5 h3
    have h7 : ∫ x, Set.indicator s (fun _ => (1 : ℝ)) x ∂μ = (μ s).toReal := by
      rw [integral_indicator hs_meas]
      <;> simp [Measure.restrict_apply]
      <;> rfl
    have h_μs_le : (μ s).toReal ≤ (μ Ω).toReal := by
      have h_ne_s : μ s ≠ ⊤ := (measure_lt_top μ s).ne
      have h_ne_O : μ Ω ≠ ⊤ := (measure_lt_top μ Ω).ne
      have h : μ s ≤ μ Ω := measure_mono h_sub_s
      exact (ENNReal.toReal_le_toReal h_ne_s h_ne_O).mpr h
    have h2 : ∫ x, ‖φ x‖ ∂μ ≤ (μ Ω).toReal := by
      rw [h7] at h6
      exact h6.trans h_μs_le
    have h8 : |∫ x in S, divergence φ x| ≤ (μ Ω).toReal := by
      rw [← h_int]
      exact h1.trans h2
    have hμΩ_lt_top : μ Ω < ⊤ := (measure_mono (Set.subset_univ Ω)).trans_lt hμ_fin
    have h9 : ENNReal.ofReal (μ Ω).toReal = μ Ω := ENNReal.ofReal_toReal hμΩ_lt_top.ne
    have h10 : ENNReal.ofReal |∫ x in S, divergence φ x| ≤ ENNReal.ofReal (μ Ω).toReal :=
      ENNReal.ofReal_le_ofReal h8
    rw [h9] at h10
    exact h10
  exact iSup_le h_main

/-- **Core blow-up translation bound** (all radii).

The constant depends only on the upper density data and `K`, not on any
particular sequence, so the bound holds simultaneously for all `r > 0`. -/
lemma blow_up_translation_bound_main
    {U : Set (E n)} (hU : IsOpen U)
    (hfin : perimeter U < ⊤)
    (hn : 2 ≤ n)
    (x : E n)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    {K : Set (E n)} (hK : IsCompact K) :
    ∃ (C : ℝ), ∀ (r : ℝ), 0 < r → ∀ (h : E n),
      volume (symmDiff (blowUp U x r) ((fun y => y + h) '' (blowUp U x r)) ∩ K) ≤
      ENNReal.ofReal (C * ‖h‖) := by
  have h1n : 1 ≤ n := by linarith
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)
  rcases h_upper with ⟨C_ud, r0, hC_ud_pos, hr0_pos, h_ud⟩

  -- Embed K in ball 0 R'
  rcases hK.isBounded.subset_ball_lt 0 (0 : E n) with ⟨R, hR_pos, hKR⟩
  let R' := R + 1
  have hR'_pos : 0 < R' := by positivity
  have hK_sub : K ⊆ ball (0 : E n) R' := by
    intro y hy
    have h1 : dist y 0 < R := hKR hy
    have h2 : R < R' := by simp [R'] <;> linarith
    exact h1.trans h2

  let Ω : Set (E n) := ball (0 : E n) (R' + 1)
  have hΩ_open : IsOpen Ω := isOpen_ball

  let P_U : ℝ := (perimeter U).toReal
  have hP_U_eq : perimeter U = ENNReal.ofReal P_U := by
    rw [ENNReal.ofReal_toReal] <;> exact hfin.ne
  have hP_nonneg : 0 ≤ P_U := by positivity

  -- Scaling formula
  have h_perim_scale : ∀ (r : ℝ), 0 < r →
      perimeterIn (blowUp U x r) Ω =
        ENNReal.ofReal ((1 / r) ^ (n - 1)) * perimeterIn U (ball x (r * (R' + 1))) := by
    intro r hr
    let t : ℝ := 1 / r
    have ht_pos : 0 < t := by positivity
    have ht_ne : t ≠ 0 := ht_pos.ne'
    let S' : Set (E n) := translateSet U (-x)
    let Ω' : Set (E n) := ball (0 : E n) (r * (R' + 1))
    have hS'_meas : MeasurableSet S' := by
      have h_emb : MeasurableEmbedding (fun y : E n => y - x) :=
        (Homeomorph.addRight (-x)).measurableEmbedding
      exact h_emb.measurableSet_image.mpr hU.measurableSet
    have h1 : blowUp U x r = scaleSet t S' := by
      ext z
      simp only [blowUp, blowUpMap, scaleSet, translateSet, Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h_goal : t • (y - x) = (1 / r) • (y - x) := by rfl
        exact ⟨y - x, ⟨y, hy, by abel_nf⟩, h_goal⟩
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        have h_goal : t • (y - x) = (1 / r) • (y - x) := by rfl
        exact ⟨y, hy, h_goal⟩
    have h2 : Ω = scaleSet t Ω' := by
      ext z
      simp only [Ω, Ω', scaleSet, Set.mem_image, mem_ball]
      constructor
      · intro hz
        refine ⟨r • z, ?_, ?_⟩
        · have h3 : dist (r • z) 0 = r * dist z 0 := by
            have h4 : dist (r • z) 0 = ‖r • z‖ := by simp [dist_eq_norm]
            have h5 : ‖r • z‖ = r * ‖z‖ := by
              calc ‖r • z‖ = |r| * ‖z‖ := norm_smul r z
                   _ = r * ‖z‖ := by rw [abs_of_pos hr]
            have h6 : ‖z‖ = dist z 0 := by simp [dist_eq_norm]
            rw [h4, h5, h6]
          rw [h3]
          exact mul_lt_mul_of_pos_left hz hr
        · have h_goal : t • (r • z) = z := by
            simp [t, smul_smul] <;> field_simp [hr.ne'] <;> simp
          exact h_goal
      · rintro ⟨w, hw, rfl⟩
        have h3 : dist (t • w) 0 = t * dist w 0 := by
          have h4 : dist (t • w) 0 = ‖t • w‖ := by simp [dist_eq_norm]
          have h5 : ‖t • w‖ = t * ‖w‖ := by
            calc ‖t • w‖ = |t| * ‖w‖ := norm_smul t w
                 _ = t * ‖w‖ := by rw [abs_of_pos ht_pos]
          have h6 : ‖w‖ = dist w 0 := by simp [dist_eq_norm]
          rw [h4, h5, h6]
        rw [h3]
        have h4 : dist w 0 < r * (R' + 1) := hw
        have h5 : t * dist w 0 < R' + 1 := by
          calc t * dist w 0 < t * (r * (R' + 1)) := mul_lt_mul_of_pos_left h4 ht_pos
            _ = R' + 1 := by
              dsimp only [t]
              field_simp [hr.ne'] <;> ring
        exact h5
    rw [h1, h2]
    have h3 : perimeterIn (scaleSet t S') (scaleSet t Ω') =
        ENNReal.ofReal (t ^ (n - 1)) * perimeterIn S' Ω' :=
      perimeterIn_scaling S' Ω' hS'_meas ht_pos h1n
    rw [h3]
    have h4 : perimeterIn S' Ω' = perimeterIn U (translateSet Ω' x) := by
      have h5 : perimeterIn (translateSet S' x) (translateSet Ω' x) = perimeterIn S' Ω' :=
        perimeterIn_translation S' Ω' x
      have h6 : translateSet S' x = U := by
        ext y
        simp [S', translateSet] <;> abel
      rw [h6] at h5
      exact h5.symm
    rw [h4]
    have h7 : translateSet Ω' x = ball x (r * (R' + 1)) := by
      ext y
      simp [Ω', translateSet, ball, dist_eq_norm] <;> abel_nf
    rw [h7]
    <;> rfl

  -- Uniform perimeter bound for all r > 0
  let C_perim_small : ℝ := C_ud * (R' + 1) ^ (n - 1)
  let C_perim_large_factor : ℝ := ((R' + 1) / r0) ^ (n - 1)
  let C_perim_large : ℝ := C_perim_large_factor * P_U
  let C_perim : ℝ := max C_perim_small C_perim_large
  have hC_perim_nonneg : 0 ≤ C_perim := by positivity

  have h_perim_bound : ∀ (r : ℝ), 0 < r → perimeterIn (blowUp U x r) Ω ≤ ENNReal.ofReal C_perim := by
    intro r hr
    let ρ := r * (R' + 1)
    rw [h_perim_scale r hr]
    by_cases h_small : ρ < r0
    · -- Small radius
      have h1 : perimeterIn U (ball x ρ) ≤ perimeterMeasure U (ball x ρ) :=
        perimeterIn_le_perimeterMeasure' hfin
      have h2 : perimeterMeasure U (ball x ρ) ≤ perimeterMeasure U (closedBall x ρ) :=
        measure_mono ball_subset_closedBall
      have h3 : perimeterMeasure U (closedBall x ρ) ≤ ENNReal.ofReal (C_ud * ρ ^ (n - 1)) :=
        h_ud ρ (by positivity) h_small
      have h4 : perimeterIn U (ball x ρ) ≤ ENNReal.ofReal (C_ud * ρ ^ (n - 1)) :=
        le_trans (le_trans h1 h2) h3
      have h5 : ENNReal.ofReal ((1 / r) ^ (n - 1)) * perimeterIn U (ball x ρ) ≤
          ENNReal.ofReal ((1 / r) ^ (n - 1)) * ENNReal.ofReal (C_ud * ρ ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h6 : ENNReal.ofReal ((1 / r) ^ (n - 1)) * ENNReal.ofReal (C_ud * ρ ^ (n - 1)) =
          ENNReal.ofReal C_perim_small := by
        have h_pos1 : 0 ≤ (1 / r) ^ (n - 1) := by positivity
        have h_pos2 : 0 ≤ C_ud * ρ ^ (n - 1) := by positivity
        rw [← ENNReal.ofReal_mul h_pos1]
        congr 1
        have h7 : ρ = r * (R' + 1) := by rfl
        rw [h7]
        have h8 : (1 / r) ^ (n - 1) * (C_ud * (r * (R' + 1)) ^ (n - 1)) = C_ud * (R' + 1) ^ (n - 1) := by
          have h9 : (1 / r) ^ (n - 1) * (r * (R' + 1)) ^ (n - 1) = (R' + 1) ^ (n - 1) := by
            rw [← mul_pow]
            have h10 : (1 / r) * (r * (R' + 1)) = R' + 1 := by
              field_simp [hr.ne'] <;> ring
            rw [h10]
          calc
            (1 / r) ^ (n - 1) * (C_ud * (r * (R' + 1)) ^ (n - 1))
              = C_ud * ((1 / r) ^ (n - 1) * (r * (R' + 1)) ^ (n - 1)) := by ring
            _ = C_ud * (R' + 1) ^ (n - 1) := by rw [h9]
        exact h8
      rw [h6] at h5
      exact le_trans h5 (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · -- Large radius
      have h_ge : r0 ≤ ρ := by linarith
      have h9 : 1 / r ≤ (R' + 1) / r0 := by
        have h10 : r * (R' + 1) ≥ r0 := h_ge
        have h11 : 0 < r0 := hr0_pos
        field_simp [hr.ne', h11.ne'] <;> linarith
      have h10 : 0 ≤ 1 / r := by positivity
      have h11 : 0 ≤ (R' + 1) / r0 := by positivity
      have h_factor : (1 / r) ^ (n - 1) ≤ ((R' + 1) / r0) ^ (n - 1) := by
        exact pow_le_pow_left₀ h10 h9 (n - 1)
      have h1 : perimeterIn U (ball x ρ) ≤ perimeter U := by
        have h1a : perimeterIn U (ball x ρ) ≤ perimeterMeasure U (ball x ρ) :=
          perimeterIn_le_perimeterMeasure' hfin
        have h1b : perimeterMeasure U (ball x ρ) ≤ perimeterMeasure U Set.univ :=
          measure_mono (subset_univ _)
        have h1c : perimeterMeasure U Set.univ = perimeter U :=
          (perimeter_eq_variation U hfin).symm
        calc
          perimeterIn U (ball x ρ)
            ≤ perimeterMeasure U (ball x ρ) := h1a
          _ ≤ perimeterMeasure U Set.univ := h1b
          _ = perimeter U := h1c
      have h2 : ENNReal.ofReal ((1 / r) ^ (n - 1)) * perimeterIn U (ball x ρ) ≤
          ENNReal.ofReal ((1 / r) ^ (n - 1)) * perimeter U :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [hP_U_eq] at h2
      have h3 : ENNReal.ofReal ((1 / r) ^ (n - 1)) * ENNReal.ofReal P_U ≤
          ENNReal.ofReal C_perim_large := by
        have h_pos1 : 0 ≤ (1 / r) ^ (n - 1) := by positivity
        have h_pos2 : 0 ≤ P_U := by positivity
        have h_eq : ENNReal.ofReal ((1 / r) ^ (n - 1)) * ENNReal.ofReal P_U =
            ENNReal.ofReal (((1 / r) ^ (n - 1)) * P_U) := by
          rw [← ENNReal.ofReal_mul h_pos1]
        rw [h_eq]
        exact ENNReal.ofReal_le_ofReal (by
          simp only [C_perim_large, C_perim_large_factor]
          <;> gcongr <;> linarith)
      exact le_trans (le_trans h2 h3) (ENNReal.ofReal_le_ofReal (le_max_right _ _))

  -- Volume constant for large ‖h‖
  have hvolK_lt_top : volume K < ⊤ := hK.measure_lt_top
  let C_big : ℝ := (volume K).toReal + 1
  have hC_big_nonneg : 0 ≤ C_big := by positivity
  have hvolK_le : volume K ≤ ENNReal.ofReal C_big := by
    have h1 : volume K ≤ ENNReal.ofReal (volume K).toReal := by
      rw [ENNReal.ofReal_toReal] <;> exact hvolK_lt_top.ne
    have h2 : ENNReal.ofReal (volume K).toReal ≤ ENNReal.ofReal C_big := by
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact le_trans h1 h2

  let C_final : ℝ := max ((n : ℝ) * C_perim) C_big
  have hC_final_nonneg : 0 ≤ C_final := by positivity

  refine ⟨C_final, fun r hr h => ?_⟩

  by_cases h_big_h : 1 ≤ ‖h‖
  · -- ‖h‖ ≥ 1
    let S_diff := symmDiff (blowUp U x r) ((fun y : E n => y + h) '' (blowUp U x r))
    have h1 : volume (S_diff ∩ K) ≤ volume K := by
      have h_sub : (S_diff ∩ K) ⊆ K := Set.inter_subset_right
      exact OuterMeasureClass.measure_mono volume h_sub
    have h2 : C_big ≤ C_final * ‖h‖ := by
      have h3 : C_big ≤ C_final := le_max_right _ _
      have h4 : 0 ≤ ‖h‖ := by positivity
      nlinarith
    calc volume (S_diff ∩ K)
        ≤ volume K := h1
      _ ≤ ENNReal.ofReal C_big := hvolK_le
      _ ≤ ENNReal.ofReal (C_final * ‖h‖) := ENNReal.ofReal_le_ofReal h2
  · -- ‖h‖ < 1
    have h_small_h : ‖h‖ < 1 := by linarith
    let E_r := blowUp U x r
    have hE_meas : MeasurableSet E_r :=
      (blowUpMap_measurableEmbedding x hr.ne').measurableSet_image.mpr hU.measurableSet
    have hK_swept : ∀ t ∈ Set.Icc (0 : ℝ) 1, translateSet K (t • (-h)) ⊆ Ω := by
      intro t ht y hy
      rcases hy with ⟨z, hz, rfl⟩
      have h1 : ‖z‖ < R' := by simpa [dist_eq_norm] using hK_sub hz
      have h2 : ‖z - t • h‖ ≤ ‖z‖ + ‖t • h‖ := norm_sub_le z (t • h)
      have h3 : ‖t • h‖ = |t| * ‖h‖ := by
        rw [norm_smul] <;> rfl
      have h4 : 0 ≤ t := ht.1
      have h5 : t ≤ 1 := ht.2
      have h6 : |t| ≤ 1 := by
        rw [abs_of_nonneg h4] <;> exact h5
      have h7 : ‖t • h‖ ≤ ‖h‖ := by
        rw [h3]
        have h8 : |t| * ‖h‖ ≤ 1 * ‖h‖ := by gcongr
        linarith
      have h9 : ‖z + -(t • h)‖ < R' + 1 := by
        have h_eq : z + -(t • h) = z - t • h := by abel
        rw [h_eq]
        calc
          ‖z - t • h‖ ≤ ‖z‖ + ‖t • h‖ := h2
          _ ≤ ‖z‖ + ‖h‖ := by gcongr
          _ < R' + 1 := by
            have h10 : ‖z‖ < R' := h1
            have h11 : ‖h‖ < 1 := h_small_h
            linarith
      simpa [Ω, ball, dist_eq_norm] using h9
    have hK_sub_Ω : K ⊆ Ω := by
      intro y hy
      have h1 : dist y 0 < R' := hK_sub hy
      have h2 : R' < R' + 1 := by linarith
      have h3 : dist y 0 < R' + 1 := h1.trans h2
      simpa [Ω, ball] using h3
    have h_main := local_translation_bound (hS := hE_meas) (hΩ_open := hΩ_open)
      (hK_compact := hK) (hK_sub := hK_sub_Ω) (v := -h) (hv_small := hK_swept)
    have h_perim := h_perim_bound r hr
    have h_norm : ‖(-h : E n)‖ = ‖h‖ := by simp
    have h_main' : volume (symmDiff E_r (translateSet E_r (-(-h))) ∩ K) ≤
        (n : ENNReal) * ENNReal.ofReal ‖h‖ * perimeterIn E_r Ω := by
      have h_tmp := h_main
      rw [h_norm] at h_tmp
      exact h_tmp
    have h_n_eq : (n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
    have h_goal : volume (symmDiff E_r ((fun y : E n => y + h) '' E_r) ∩ K) ≤
        ENNReal.ofReal (C_final * ‖h‖) := by
      have h_eq1 : (fun y : E n => y + h) '' E_r = translateSet E_r h := by
        ext z; simp [translateSet] <;> abel
      rw [h_eq1]
      have h_eq2 : translateSet E_r h = translateSet E_r (-(-h)) := by
        have h10 : -(-h) = h := by simp
        rw [h10]
      rw [h_eq2]
      calc volume (symmDiff E_r (translateSet E_r (-(-h))) ∩ K)
        ≤ (n : ENNReal) * ENNReal.ofReal ‖h‖ * perimeterIn E_r Ω := h_main'
      _ ≤ (n : ENNReal) * ENNReal.ofReal ‖h‖ * ENNReal.ofReal C_perim := by gcongr
      _ = ENNReal.ofReal (((n : ℝ) * C_perim) * ‖h‖) := by
        rw [h_n_eq]
        have h_pos1 : 0 ≤ (n : ℝ) * C_perim := by positivity
        have h_pos2 : 0 ≤ ‖h‖ := by positivity
        have h_eq3 : ENNReal.ofReal (n : ℝ) * ENNReal.ofReal ‖h‖ * ENNReal.ofReal C_perim =
            ENNReal.ofReal (((n : ℝ) * C_perim) * ‖h‖) := by
          have h_assoc : ENNReal.ofReal (n : ℝ) * ENNReal.ofReal ‖h‖ * ENNReal.ofReal C_perim =
              ENNReal.ofReal (n : ℝ) * (ENNReal.ofReal ‖h‖ * ENNReal.ofReal C_perim) := by ring
          rw [h_assoc]
          have h_step1 : ENNReal.ofReal ‖h‖ * ENNReal.ofReal C_perim =
              ENNReal.ofReal (‖h‖ * C_perim) := by
            rw [← ENNReal.ofReal_mul h_pos2]
          rw [h_step1]
          have h_pos1' : 0 ≤ (n : ℝ) := by positivity
          have h_step2 : ENNReal.ofReal (n : ℝ) * ENNReal.ofReal (‖h‖ * C_perim) =
              ENNReal.ofReal ((n : ℝ) * (‖h‖ * C_perim)) := by
            rw [← ENNReal.ofReal_mul h_pos1']
          rw [h_step2]
          <;> ring_nf
        exact h_eq3
      _ ≤ ENNReal.ofReal (C_final * ‖h‖) := by
        have h_le : (n : ℝ) * C_perim ≤ C_final := le_max_left _ _
        have h_pos : 0 ≤ ‖h‖ := by positivity
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h_le h_pos)
    exact h_goal

/-- **Blow-up translation bound from upper perimeter density** (all radii).

Given an upper perimeter density bound at `x`, the blow-ups satisfy
uniform translation continuity on every compact set for all `r > 0`:
`volume(symmDiff(blowUp U x r, blowUp U x r + h) ∩ K) ≤ C * ‖h‖`. -/
theorem blow_up_translation_bound_all
    {U : Set (E n)} (hU : IsOpen U)
    (hfin : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) :
    ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ (r : ℝ), 0 < r → ∀ (h : E n),
        volume (symmDiff (blowUp U x r) ((fun y => y + h) '' (blowUp U x r)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖) :=
  fun K hK => blow_up_translation_bound_main hU hfin hn x h_upper hK

/-- **Blow-up translation bound from upper perimeter density** (sequence version).

For any sequence `r_seq → 0`, the blow-ups satisfy uniform translation
continuity on every compact set. -/
theorem blow_up_translation_bound
    {U : Set (E n)} (hU : IsOpen U)
    (hfin : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n) (r_seq : ℕ → ℝ) (hr_pos : ∀ k, 0 < r_seq k)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (_hr_tendsto : Tendsto r_seq atTop (nhds 0)) :
    ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ k, ∀ (h : E n),
        volume (symmDiff (blowUp U x (r_seq k)) ((fun y => y + h) '' (blowUp U x (r_seq k))) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖) := by
  intro K hK
  rcases blow_up_translation_bound_main hU hfin hn x h_upper hK with ⟨C, hC⟩
  exact ⟨C, fun k => hC (r_seq k) (hr_pos k)⟩

end Geometry.StructureTheorem

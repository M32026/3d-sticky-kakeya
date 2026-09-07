import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellScaleBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellPropertyTransfers
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellSourceAndWidth
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellContractionHelpers

namespace Kakeya.Assouad

open scoped ENNReal
open Classical

/-- Generalized delta₀ existence: find small delta₀ with `delta₀^p ≤ target`. -/
lemma wide_fixed_general_delta_zero_exists
    {p target : ℝ} (hp_pos : 0 < p) (h_target_pos : 0 < target)
    {delta₀_fixed : ℝ} (hdf_pos : 0 < delta₀_fixed) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧ delta₀ ≤ delta₀_fixed ∧
      Real.rpow delta₀ p ≤ target := by
  set x : ℝ := target ^ (1 / p) with hx_def
  have hx_pos : 0 < x := Real.rpow_pos_of_pos h_target_pos _
  have hx_rpow : x ^ p = target := by
    rw [hx_def]
    have h : (target ^ (1 / p)) ^ p = target ^ ((1 / p) * p) := by
      rw [← Real.rpow_mul h_target_pos.le] <;> ring
    rw [h]
    have h2 : (1 / p) * p = 1 := by field_simp [hp_pos.ne'] <;> ring
    rw [h2]
    simp
  set delta₀ : ℝ := min x (min 1 delta₀_fixed) with hdef
  have hpos : 0 < delta₀ := by
    rw [hdef]
    apply lt_min hx_pos
    apply lt_min (by norm_num) hdf_pos
  have hle_one : delta₀ ≤ 1 := by
    rw [hdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hle_fixed : delta₀ ≤ delta₀_fixed := by
    rw [hdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hle_x : delta₀ ≤ x := by
    rw [hdef]
    exact min_le_left _ _
  have h_main : delta₀ ^ p ≤ target := by
    have h : delta₀ ^ p ≤ x ^ p := Real.rpow_le_rpow (by linarith) hle_x (by linarith)
    rw [hx_rpow] at h
    exact h
  exact ⟨delta₀, hpos, hle_one, hle_fixed, h_main⟩

theorem wz1_wide_fixed_cell_normalization :
    WZ1Proposition8_9WideFixedCellNormalizationStatement := by
  intro hFixed
  intro epsilon parameters hepsilon_pos hepsilon_lt_one
  rcases hFixed epsilon parameters hepsilon_pos hepsilon_lt_one with ⟨etaCap, hEtaCap_pos, hEtaCap⟩
  refine' ⟨etaCap, hEtaCap_pos, _⟩
  intro eta hEta_pos hEta_le
  rcases hEtaCap eta hEta_pos hEta_le with ⟨delta₀_fixed, hdf_pos, hdf_le_one, hdf⟩
  set lambda : ℝ := parameters.projectionLambda with hlambda_def
  have hlambda_pos : 0 < lambda := parameters.projectionLambda_pos
  have hlambda_le_one : lambda ≤ 1 := parameters.projectionLambda_le_one
  set alpha : ℝ := parameters.alpha with halpha_def
  have halpha_pos : 0 < alpha := parameters.alpha_pos
  set zeta : ℝ := parameters.zeta with hzeta_def
  have hzeta_pos : 0 < zeta := parameters.zeta_pos
  have hzeta_nonneg : 0 ≤ zeta := by linarith
  set p : ℝ := epsilon * lambda / 40 with hp_def
  have hp_pos : 0 < p := by positivity
  set target : ℝ := (1 / 4 : ℝ) ^ (1 - lambda) with htarget_def
  have htarget_pos : 0 < target := Real.rpow_pos_of_pos (by norm_num) _
  rcases wide_fixed_general_delta_zero_exists hp_pos htarget_pos hdf_pos with
    ⟨delta₀, hd₀_pos, hd₀_le_one, hd₀_le_fixed, hd₀_small⟩
  refine' ⟨delta₀, hd₀_pos, hd₀_le_one, _⟩
  intro delta F G₁ G₂ H hdelta_pos hdelta_le data hwidth coarse fixed
  set firstScale : ℝ := WideFixedCellScaleBounds.firstScale fixed with hfirstScale_def
  set endpointScale : ℝ := WideFixedCellScaleBounds.endpointScale fixed with hendpointScale_def
  set endpointTranslation : Point2 := WideFixedCellScaleBounds.endpointTranslation fixed with hendpointTranslation_def
  set scaleFactor : ℝ := min 1 (min firstScale endpointScale) with hscaleFactor_def
  set scale : ℝ := scaleFactor * coarse.scale with hscale_def
  set effectiveWidth : ℝ := data.width / (firstScale * endpointScale) with heffectiveWidth_def
  set sourceError : ℝ := 1200 * effectiveWidth * coarse.scale with hsourceError_def
  set normalizedF : DiscreteSet 2 := fixed.cellF.image (fun point => firstScale • point) with hnormalizedF_def
  set normalizedG₁ : DiscreteSet 2 := fixed.cellG₁.image (fun point => endpointScale • point + endpointTranslation) with hnormalizedG₁_def
  set normalizedG₂ : DiscreteSet 2 := fixed.cellG₂.image (fun point => endpointScale • point + endpointTranslation) with hnormalizedG₂_def
  set normalizedH : Finset (Point2 × Point2 × Point2) := fixed.cellH.image (fun edge =>
      (firstScale • edge.1, endpointScale • edge.2.1 + endpointTranslation,
       endpointScale • edge.2.2 + endpointTranslation)) with hnormalizedH_def

  have hfirstScale_bounds := WideFixedCellScaleBounds.firstScale_bounds fixed
  have hendpointScale_bounds := WideFixedCellScaleBounds.endpointScale_bounds fixed
  have hfirstScale_pos : 0 < firstScale := by linarith [hfirstScale_bounds.1]
  have hfirstScale_lower : 1 / 4 ≤ firstScale := hfirstScale_bounds.1
  have hfirstScale_le : firstScale ≤ 100 := by linarith [hfirstScale_bounds.2]
  have hendpointScale_pos : 0 < endpointScale := by linarith [hendpointScale_bounds.1]
  have hendpointScale_lower : 1 / 4 ≤ endpointScale := hendpointScale_bounds.1
  have hendpointScale_le : endpointScale ≤ 100 := by linarith [hendpointScale_bounds.2]
  have hscale_product_lower : 1 / 16 ≤ firstScale * endpointScale :=
    WideFixedCellScaleBounds.scale_product_lower fixed
  have hscale_product_upper : firstScale * endpointScale ≤ 100 :=
    WideFixedCellScaleBounds.scale_product_upper fixed
  have hscaleFactor_pos : 0 < scaleFactor := by
    rw [hscaleFactor_def]
    have h1 : 0 < min firstScale endpointScale := by
      apply lt_min hfirstScale_pos hendpointScale_pos
    positivity
  have hscaleFactor_lower : 1 / 4 ≤ scaleFactor := by
    rw [hscaleFactor_def]
    have h1 : 1 / 4 ≤ min firstScale endpointScale := by
      exact le_min hfirstScale_lower hendpointScale_lower
    exact le_min (by norm_num) h1
  have hscaleFactor_le_one : scaleFactor ≤ 1 := by
    rw [hscaleFactor_def]
    exact min_le_left _ _
  have hscaleFactor_le_first : scaleFactor ≤ firstScale := by
    rw [hscaleFactor_def]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hscaleFactor_le_endpoint : scaleFactor ≤ endpointScale := by
    rw [hscaleFactor_def]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hscale_pos : 0 < scale := mul_pos hscaleFactor_pos coarse.scale_pos
  have hscale_le_coarse : scale ≤ coarse.scale := by
    rw [hscale_def]
    have h : scaleFactor * coarse.scale ≤ 1 * coarse.scale :=
      mul_le_mul_of_nonneg_right hscaleFactor_le_one coarse.scale_pos.le
    linarith
  have hscale_le_projectionDelta₀ : scale ≤ parameters.projectionDelta₀ := by
    calc scale ≤ coarse.scale := hscale_le_coarse
      _ ≤ parameters.projectionDelta₀ := coarse.scale_le_projectionDelta₀

  have h_coarseScale_lt_delta_exp : coarse.scale < delta ^ (epsilon / 10) := by
    have h1 : coarse.scale = delta / data.width := coarse.scale_eq
    rw [h1]
    have h2 : data.width > delta ^ (1 - epsilon / 10) := hwidth
    have hpos : 0 < delta ^ (1 - epsilon / 10) := Real.rpow_pos_of_pos hdelta_pos _
    have h4 : 0 < data.width := data.width_pos
    have h5 : delta * delta ^ (1 - epsilon / 10) < delta * data.width :=
      mul_lt_mul_of_pos_left h2 hdelta_pos
    have h9 : 0 < data.width * delta ^ (1 - epsilon / 10) := mul_pos h4 hpos
    have h10 : (delta / data.width) * (data.width * delta ^ (1 - epsilon / 10)) = delta * delta ^ (1 - epsilon / 10) := by
      field_simp [h4.ne'] <;> ring
    have h11 : (delta / delta ^ (1 - epsilon / 10)) * (data.width * delta ^ (1 - epsilon / 10)) = delta * data.width := by
      field_simp [hpos.ne'] <;> ring
    have h3 : delta / data.width < delta / delta ^ (1 - epsilon / 10) := by
      have h_formula : delta / data.width - delta / delta ^ (1 - epsilon / 10) =
          (delta * delta ^ (1 - epsilon / 10) - delta * data.width) / (data.width * delta ^ (1 - epsilon / 10)) := by
        field_simp [h4.ne', hpos.ne'] <;> ring
      have h_neg : (delta * delta ^ (1 - epsilon / 10) - delta * data.width) / (data.width * delta ^ (1 - epsilon / 10)) < 0 := by
        have h_num : delta * delta ^ (1 - epsilon / 10) - delta * data.width < 0 := by linarith
        have h_denom : 0 < data.width * delta ^ (1 - epsilon / 10) := h9
        exact div_neg_of_neg_of_pos h_num h_denom
      have h_lt : delta / data.width - delta / delta ^ (1 - epsilon / 10) < 0 := by
        rw [h_formula]
        exact h_neg
      linarith
    have h4 : delta / delta ^ (1 - epsilon / 10) = delta ^ (epsilon / 10) := by
      have h5 : 0 < delta := hdelta_pos
      have h6 : delta / delta ^ (1 - epsilon / 10) = delta ^ (1 : ℝ) / delta ^ (1 - epsilon / 10) := by simp
      rw [h6]
      have h7 : delta ^ (1 : ℝ) / delta ^ (1 - epsilon / 10) = delta ^ (1 - (1 - epsilon / 10)) := by
        rw [← Real.rpow_sub h5] <;> ring
      rw [h7]
      have h8 : 1 - (1 - epsilon / 10) = epsilon / 10 := by ring
      rw [h8]
    rw [h4] at h3
    exact h3

  have hsmall : Real.rpow coarse.scale (lambda / 4) ≤ Real.rpow scaleFactor (1 - lambda) := by
    have h1 : Real.rpow coarse.scale (lambda / 4) < Real.rpow delta (epsilon * lambda / 40) := by
      have h2 : Real.rpow coarse.scale (lambda / 4) < Real.rpow (delta ^ (epsilon / 10)) (lambda / 4) :=
        Real.rpow_lt_rpow (by linarith) h_coarseScale_lt_delta_exp (by linarith)
      have h3 : Real.rpow (delta ^ (epsilon / 10)) (lambda / 4) = Real.rpow delta (epsilon * lambda / 40) := by
        have h31 : (delta ^ (epsilon / 10)) ^ (lambda / 4) = delta ^ ((epsilon / 10) * (lambda / 4)) :=
          (Real.rpow_mul hdelta_pos.le (epsilon / 10) (lambda / 4)).symm
        have h32 : (epsilon / 10) * (lambda / 4) = epsilon * lambda / 40 := by ring
        simpa [h32] using h31
      rw [h3] at h2
      exact h2
    have h4 : Real.rpow delta (epsilon * lambda / 40) ≤ Real.rpow delta₀ (epsilon * lambda / 40) := by
      apply Real.rpow_le_rpow
      · linarith
      · exact hdelta_le
      · linarith
    have h5 : Real.rpow delta₀ (epsilon * lambda / 40) ≤ target := hd₀_small
    have h6 : target ≤ Real.rpow scaleFactor (1 - lambda) := by
      simp only [htarget_def]
      have h7 : (1 / 4 : ℝ) ≤ scaleFactor := hscaleFactor_lower
      have h8 : 0 ≤ 1 - lambda := by linarith
      exact Real.rpow_le_rpow (by norm_num) h7 h8
    linarith

  have hnormalizedF_nonempty : normalizedF.Nonempty :=
    fixed.cellF_nonempty.image _
  have hnormalizedG₁_nonempty : normalizedG₁.Nonempty :=
    fixed.cellG₁_nonempty.image _
  have hnormalizedG₂_nonempty : normalizedG₂.Nonempty :=
    fixed.cellG₂_nonempty.image _

  have hnormalizedF_ball : normalizedF.IsInUnitBall :=
    WideFixedCellScaleBounds.normalizedF_unit_ball fixed
  have hnormalizedG₁_ball : normalizedG₁.IsInUnitBall :=
    WideFixedCellScaleBounds.normalizedG₁_unit_ball fixed
  have hnormalizedG₂_ball : normalizedG₂.IsInUnitBall :=
    WideFixedCellScaleBounds.normalizedG₂_unit_ball fixed

  have hnormalized_standard_separation : WZ1StandardSeparation normalizedF normalizedG₁ normalizedG₂ :=
    WideFixedCellScaleBounds.normalized_standard_separation fixed

  have h_sep_expand_first : ∀ (x y : Point2), scaleFactor * dist x y ≤ dist (firstScale • x) (firstScale • y) := by
    intro x y
    have h : dist (firstScale • x) (firstScale • y) = firstScale * dist x y := by
      rw [dist_smul_real, abs_of_pos hfirstScale_pos]
    rw [h]
    gcongr <;> linarith
  have h_sep_expand_endpoint : ∀ (x y : Point2), scaleFactor * dist x y ≤
      dist (endpointScale • x + endpointTranslation) (endpointScale • y + endpointTranslation) := by
    intro x y
    have h : dist (endpointScale • x + endpointTranslation) (endpointScale • y + endpointTranslation) =
        endpointScale * dist x y := by
      rw [dist_add_right, dist_smul_real, abs_of_pos hendpointScale_pos]
    rw [h]
    gcongr <;> linarith

  have hnormalizedF_separated : normalizedF.IsDeltaSeparated scale :=
    DiscreteSet.isDeltaSeparated_map_expansive fixed.cellF_separated hscaleFactor_pos h_sep_expand_first
  have hnormalizedG₁_separated : normalizedG₁.IsDeltaSeparated scale :=
    DiscreteSet.isDeltaSeparated_map_expansive fixed.cellG₁_separated hscaleFactor_pos h_sep_expand_endpoint
  have hnormalizedG₂_separated : normalizedG₂.IsDeltaSeparated scale :=
    DiscreteSet.isDeltaSeparated_map_expansive fixed.cellG₂_separated hscaleFactor_pos h_sep_expand_endpoint

  have hcoarse_scale_le_one : coarse.scale ≤ 1 :=
    coarse.scale_le_projectionDelta₀.trans parameters.projectionDelta₀_le_one
  have hnormalizedF_frostman : normalizedF.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) :=
    frostman_transfer_scaling fixed.cellF_frostman_margin
      coarse.scale_pos hcoarse_scale_le_one
      hfirstScale_pos hscaleFactor_pos hscaleFactor_le_first hscaleFactor_le_one
      hlambda_pos hlambda_le_one hsmall

  let scaledG₁ : DiscreteSet 2 := fixed.cellG₁.image (fun x => endpointScale • x)
  have hscaledG₁_frostman : scaledG₁.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) :=
    frostman_transfer_scaling fixed.cellG₁_frostman_margin
      coarse.scale_pos hcoarse_scale_le_one
      hendpointScale_pos hscaleFactor_pos hscaleFactor_le_endpoint hscaleFactor_le_one
      hlambda_pos hlambda_le_one hsmall
  have hnormalizedG₁_frostman : normalizedG₁.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) := by
    have h_eq : normalizedG₁ = scaledG₁.image (fun y => y + endpointTranslation) := by
      ext z
      simp only [normalizedG₁, scaledG₁, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨endpointScale • x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [h_eq]
    exact DiscreteSet.isFrostman_translate hscaledG₁_frostman

  let scaledG₂ : DiscreteSet 2 := fixed.cellG₂.image (fun x => endpointScale • x)
  have hscaledG₂_frostman : scaledG₂.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) :=
    frostman_transfer_scaling fixed.cellG₂_frostman_margin
      coarse.scale_pos hcoarse_scale_le_one
      hendpointScale_pos hscaleFactor_pos hscaleFactor_le_endpoint hscaleFactor_le_one
      hlambda_pos hlambda_le_one hsmall
  have hnormalizedG₂_frostman : normalizedG₂.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) := by
    have h_eq : normalizedG₂ = scaledG₂.image (fun y => y + endpointTranslation) := by
      ext z
      simp only [normalizedG₂, scaledG₂, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨endpointScale • x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [h_eq]
    exact DiscreteSet.isFrostman_translate hscaledG₂_frostman

  have hfirst_line : WZ1LineNonConcentration scale lambda zeta normalizedG₁ :=
    WZ1LineNonConcentration.contraction
      fixed.first_line_nonconcentration_margin
      hendpointScale_pos hscaleFactor_pos hscaleFactor_le_endpoint
      hlambda_pos hlambda_le_one hzeta_nonneg coarse.scale_pos hsmall

  have hsecond_line : WZ1LineNonConcentration scale lambda zeta normalizedG₂ :=
    WZ1LineNonConcentration.contraction
      fixed.second_line_nonconcentration_margin
      hendpointScale_pos hscaleFactor_pos hscaleFactor_le_endpoint
      hlambda_pos hlambda_le_one hzeta_nonneg coarse.scale_pos hsmall

  let fF : Point2 → Point2 := fun x => firstScale • x
  let fG : Point2 → Point2 := fun x => endpointScale • x + endpointTranslation
  have hfF_inj : Function.Injective fF := by
    intro x y h
    have h2 : firstScale • x = firstScale • y := h
    have h3 : (1 / firstScale) • (firstScale • x) = (1 / firstScale) • (firstScale • y) := by rw [h2]
    simpa [hfirstScale_pos.ne'] using h3
  have hfG_inj : Function.Injective fG := by
    intro x y h
    have h2 : endpointScale • x + endpointTranslation = endpointScale • y + endpointTranslation := h
    have h3 : endpointScale • x = endpointScale • y := by simpa using h2
    have h4 : (1 / endpointScale) • (endpointScale • x) = (1 / endpointScale) • (endpointScale • y) := by rw [h3]
    simpa [hendpointScale_pos.ne'] using h4

  have h_uniform_mapped : WZ1UniformTripleDensity
      (Kakeya.realRpowENN coarse.scale alpha)
      normalizedF normalizedG₁ normalizedG₂ normalizedH :=
    WZ1UniformTripleDensity.map_injective fixed.uniform fF fG fG hfF_inj hfG_inj hfG_inj

  have hscale_le_coarse_scale : scale ≤ coarse.scale := hscale_le_coarse
  have h_const_le : Kakeya.realRpowENN scale alpha ≤ Kakeya.realRpowENN coarse.scale alpha := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow
    · positivity
    · exact hscale_le_coarse_scale
    · exact halpha_pos.le

  have h_uniform : WZ1UniformTripleDensity
      (Kakeya.realRpowENN scale alpha)
      normalizedF normalizedG₁ normalizedG₂ normalizedH :=
    WZ1UniformTripleDensity.mono h_uniform_mapped h_const_le

  have heffectiveWidth_pos : 0 < effectiveWidth := by
    rw [heffectiveWidth_def]
    exact div_pos data.width_pos (mul_pos hfirstScale_pos hendpointScale_pos)
  have heffectiveWidth_eq : effectiveWidth = data.width / (firstScale * endpointScale) :=
    heffectiveWidth_def
  have heffectiveWidth_scale_eq : effectiveWidth * scale =
      delta * scaleFactor / (firstScale * endpointScale) :=
    wide_fixed_effective_width_scale_eq
      coarse.scale_eq hscale_def heffectiveWidth_eq
      data.width_pos hfirstScale_pos hendpointScale_pos
  have h_ratio_lower : 1 / 100 ≤ scaleFactor / (firstScale * endpointScale) :=
    wide_fixed_scale_factor_ratio_lower
      hfirstScale_lower hendpointScale_lower hfirstScale_le hendpointScale_le
      hscale_product_upper hscaleFactor_def
  have h_ratio_upper : scaleFactor / (firstScale * endpointScale) ≤ 4 :=
    wide_fixed_scale_factor_ratio_upper
      hfirstScale_lower hendpointScale_lower hscaleFactor_def
  have heffectiveWidth_scale_lower : delta / 100 ≤ effectiveWidth * scale :=
    wide_fixed_effective_width_scale_lower
      hdelta_pos coarse.scale_eq hscale_def heffectiveWidth_eq
      data.width_pos hfirstScale_pos hendpointScale_pos h_ratio_lower
  have heffectiveWidth_scale_upper : effectiveWidth * scale ≤ 4 * delta :=
    wide_fixed_effective_width_scale_upper
      hdelta_pos coarse.scale_eq hscale_def heffectiveWidth_eq
      data.width_pos hfirstScale_pos hendpointScale_pos h_ratio_upper
  have heffectiveWidth_lower : data.width / 100 ≤ effectiveWidth :=
    wide_fixed_effective_width_lower
      heffectiveWidth_eq data.width_pos hfirstScale_pos hendpointScale_pos hscale_product_upper
  have heffectiveWidth_upper : effectiveWidth ≤ 100 * data.width :=
    wide_fixed_effective_width_upper
      heffectiveWidth_eq data.width_pos hfirstScale_pos hendpointScale_pos hscale_product_lower

  have hsourceError_nonneg : 0 ≤ sourceError := by
    rw [hsourceError_def]
    have hpos : 0 < effectiveWidth := heffectiveWidth_pos
    have hpos2 : 0 < coarse.scale := coarse.scale_pos
    positivity
  have hsourceError_bound : sourceError ≤ 1200 * effectiveWidth * coarse.scale := by
    rw [hsourceError_def] <;> ring

  have h_normH_support : ∀ edge ∈ normalizedH,
      edge.1 ∈ normalizedF ∧ edge.2.1 ∈ normalizedG₁ ∧ edge.2.2 ∈ normalizedG₂ := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with ⟨orig, horig, rfl⟩
    have h_sup := fixed.cellH_support orig horig
    exact ⟨
      Finset.mem_image.mpr ⟨orig.1, h_sup.1, rfl⟩,
      Finset.mem_image.mpr ⟨orig.2.1, h_sup.2.1, rfl⟩,
      Finset.mem_image.mpr ⟨orig.2.2, h_sup.2.2, rfl⟩⟩

  have hnormalized_dot_bound : ∀ value ∈ wz1DotDifferenceSet normalizedH, |value| ≤ 2 :=
    unitBall_imp_dot_bound
      (fun edge hedge => hnormalizedF_ball edge.1 ((h_normH_support edge hedge).1))
      (fun edge hedge => hnormalizedG₁_ball edge.2.1 ((h_normH_support edge hedge).2.1))
      (fun edge hedge => hnormalizedG₂_ball edge.2.2 ((h_normH_support edge hedge).2.2))

  have hsource_approximation : ∀ normalizedEdge ∈ normalizedH,
      ∃ sourceEdge ∈ data.refinedH,
        |inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) -
          effectiveWidth * inner ℝ normalizedEdge.1
            (normalizedEdge.2.1 - normalizedEdge.2.2)| ≤ sourceError := by
    intro normalizedEdge hnorm
    rcases Finset.mem_image.mp hnorm with ⟨edge, hedge, rfl⟩
    exact wide_fixed_source_approximation
      hfirstScale_pos hendpointScale_pos hscale_product_upper heffectiveWidth_eq
      edge.1 edge.2.1 edge.2.2 hedge

  exact Nonempty.intro {
    scale := scale,
    scale_pos := hscale_pos,
    scale_le_projectionDelta₀ := hscale_le_projectionDelta₀,
    firstScale := firstScale,
    firstScale_pos := hfirstScale_pos,
    firstScale_lower := hfirstScale_lower,
    firstScale_le := hfirstScale_le,
    endpointScale := endpointScale,
    endpointScale_pos := hendpointScale_pos,
    endpointScale_lower := hendpointScale_lower,
    endpointScale_le := hendpointScale_le,
    scaleFactor := scaleFactor,
    scaleFactor_eq := by rw [hscaleFactor_def],
    scaleFactor_pos := hscaleFactor_pos,
    scaleFactor_lower := hscaleFactor_lower,
    scaleFactor_le_one := hscaleFactor_le_one,
    scaleFactor_le_first := hscaleFactor_le_first,
    scaleFactor_le_endpoint := hscaleFactor_le_endpoint,
    scale_product_lower := hscale_product_lower,
    scale_product_le := hscale_product_upper,
    scale_eq := by rw [hscale_def],
    endpointTranslation := endpointTranslation,
    normalizedF := normalizedF,
    normalizedG₁ := normalizedG₁,
    normalizedG₂ := normalizedG₂,
    normalizedH := normalizedH,
    normalizedF_eq := by rw [hnormalizedF_def],
    normalizedG₁_eq := by rw [hnormalizedG₁_def],
    normalizedG₂_eq := by rw [hnormalizedG₂_def],
    normalizedH_eq := by rw [hnormalizedH_def],
    normalizedF_nonempty := hnormalizedF_nonempty,
    normalizedG₁_nonempty := hnormalizedG₁_nonempty,
    normalizedG₂_nonempty := hnormalizedG₂_nonempty,
    normalizedF_ball := hnormalizedF_ball,
    normalizedG₁_ball := hnormalizedG₁_ball,
    normalizedG₂_ball := hnormalizedG₂_ball,
    normalizedF_separated := hnormalizedF_separated,
    normalizedG₁_separated := hnormalizedG₁_separated,
    normalizedG₂_separated := hnormalizedG₂_separated,
    normalizedF_frostman := hnormalizedF_frostman,
    normalizedG₁_frostman := hnormalizedG₁_frostman,
    normalizedG₂_frostman := hnormalizedG₂_frostman,
    standardSeparation := hnormalized_standard_separation,
    first_line_nonconcentration := hfirst_line,
    second_line_nonconcentration := hsecond_line,
    uniform := h_uniform,
    effectiveWidth := effectiveWidth,
    effectiveWidth_pos := heffectiveWidth_pos,
    effectiveWidth_eq := heffectiveWidth_eq,
    effectiveWidth_scale_eq := heffectiveWidth_scale_eq,
    effectiveWidth_scale_lower := heffectiveWidth_scale_lower,
    effectiveWidth_scale_upper := heffectiveWidth_scale_upper,
    effectiveWidth_lower := heffectiveWidth_lower,
    effectiveWidth_upper := heffectiveWidth_upper,
    sourceError := sourceError,
    sourceError_nonneg := hsourceError_nonneg,
    sourceError_bound := hsourceError_bound,
    normalized_dot_bound := hnormalized_dot_bound,
    source_approximation := hsource_approximation
  }

end Kakeya.Assouad

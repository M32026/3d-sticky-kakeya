import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulExtremeCases
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulClosingArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.IncidenceGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanCoveringScale
import MyLeanRepo.Kakeya.Assouad.WZ1.CoveringNumber1D
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanProjectionFiber
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.ClosingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseningArithmetic

/-!
# Covering number transport for the faithful Kaufman closing

Combines the inclusion lemma, ENNReal coarsening arithmetic,
and the numerical inequality to prove the final covering estimate.
-/

namespace Kakeya.Assouad

open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Transport the Kaufman fiber covering bound to the original dot-difference
set at scale `rho = max delta transportedScale`. -/
lemma closing_covering_transport
    {delta epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1)
    {input : WZ1Lemma8_13ResidualInput
        delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine : WZ1Lemma8_13FaithfulViewpointAffineData input hdelta}
    {kaufman : WZ1Lemma8_13FaithfulKaufmanInputData affine}
    (direction : Point2)
    (hdirection : direction ∈ kaufman.radial.directions)
    (hdeltaOne : delta ≤ 1)
    (normalizedFiberCovering :
      ENNReal.ofReal
          (wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
            (2 * kaufman_total_const
              (max 1 kaufman.commonConstant) 1 1
              (2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2) *
              (2 : ℝ) ^ (2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2))) *
        Kakeya.realRpowENN (wz1Lemma8_13FaithfulAngularScale input)
          (-(2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2)) ≤
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal (wz1Lemma8_13FaithfulAngularScale input))
        (inner ℝ direction ''
          (kaufmanFiber kaufman.finalH
            (kaufman.firstEndpoint direction)
            (kaufman.secondEndpoint direction) : Set Point2))) : ENNReal))
    (hnumerical :
      7 * delta ^ (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
        (2 / wz1Lemma8_13FaithfulAngularScale input) ^ (1 - epsilon) ≤
      (delta ^ wz1Lemma8_13FaithfulNormalizedEta epsilon) ^ 2 /
        (2 * kaufman_total_const
          (delta ^ (-wz1Lemma8_13FaithfulNormalizedEta epsilon)) 1 1
          (2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2) *
          (2 : ℝ) ^ (2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2)) *
        (wz1Lemma8_13FaithfulAngularScale input) ^
          (-(2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2)))
    :
    Kakeya.realRpowENN
      (2 * (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
        dist (kaufman.firstEndpoint direction)
          (kaufman.secondEndpoint direction)) /
        max delta (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
          dist (kaufman.firstEndpoint direction)
            (kaufman.secondEndpoint direction) *
          wz1Lemma8_13FaithfulAngularScale input))
      (1 - epsilon) ≤
    (↑(Metric.externalCoveringNumber (Real.toNNReal
        (max delta (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
          dist (kaufman.firstEndpoint direction)
            (kaufman.secondEndpoint direction) *
          wz1Lemma8_13FaithfulAngularScale input)))
      (wz1DotDifferenceSet input.H ∩
        Metric.closedBall 0 (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
          dist (kaufman.firstEndpoint direction)
            (kaufman.secondEndpoint direction)))) : ENNReal) := by
  set normalizedEta := wz1Lemma8_13FaithfulNormalizedEta epsilon
  set gamma := 2 * normalizedEta + 1 - epsilon / 2
  set epsilonOne := wz1Lemma8_13FaithfulEpsilonOne epsilon
  set angularScale := wz1Lemma8_13FaithfulAngularScale input
  set normalizationWidth := wz1Lemma8_13FaithfulNormalizationWidth input
  set D := dist (kaufman.firstEndpoint direction) (kaufman.secondEndpoint direction)
  set transportedRadius := 4 * normalizationWidth * D
  set transportedScale := transportedRadius * angularScale
  set rho := max delta transportedScale
  set S_norm := inner ℝ direction '' (kaufmanFiber kaufman.finalH
      (kaufman.firstEndpoint direction) (kaufman.secondEndpoint direction) : Set Point2)
  set S_orig := wz1DotDifferenceSet input.H ∩ Metric.closedBall 0 transportedRadius
  set C_close : ENNReal :=
      ENNReal.ofReal
          (wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
            (2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma *
              (2 : ℝ) ^ gamma)) *
        Kakeya.realRpowENN angularScale (-gamma)
  set F : ENNReal := ENNReal.ofReal (7 * delta ^ (-epsilonOne))
  set D' : ENNReal := ENNReal.ofReal ((2 / angularScale) ^ (1 - epsilon))

  -- Positivity
  have hne_pos : 0 < normalizedEta := by
    simp [normalizedEta, wz1Lemma8_13FaithfulNormalizedEta] <;> positivity
  have hgamma_pos : 0 < gamma := by
    simp [gamma, normalizedEta, wz1Lemma8_13FaithfulNormalizedEta] <;> nlinarith [sq_pos_of_pos hepsilon]
  have hgamma_lt_one : gamma < 1 := by
    simp [gamma, normalizedEta, wz1Lemma8_13FaithfulNormalizedEta] <;> nlinarith [sq_pos_of_pos hepsilon]
  have heo_pos : 0 < epsilonOne := by
    simp [epsilonOne, wz1Lemma8_13FaithfulEpsilonOne] <;> positivity
  have has_pos : 0 < angularScale := affine.angularScale_pos
  have hnw_pos : 0 < normalizationWidth := affine.normalizationWidth_pos
  have hD_pos : 0 < D := by
    have hlower : 1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤ D :=
      kaufman.endpointDistance_lower direction hdirection
    have haspect_pos : 0 < wz1Lemma8_13FaithfulAspect input := by
      dsimp only [wz1Lemma8_13FaithfulAspect]
      exact zero_lt_one.trans_le (le_max_left _ _)
    have hpos : 0 < 1 / (4 * wz1Lemma8_13FaithfulAspect input) := by positivity
    linarith
  have htr_pos : 0 < transportedRadius := by positivity
  have hts_pos : 0 < transportedScale := by positivity

  -- Inclusion and scaling
  have h_inclusion : (fun x : ℝ => transportedRadius * x) '' S_norm ⊆ S_orig :=
    dot_diff_transport_inclusion direction hdirection
  have h_scaling :
      Metric.externalCoveringNumber (Real.toNNReal transportedScale)
        ((fun x : ℝ => transportedRadius * x) '' S_norm) =
      Metric.externalCoveringNumber (Real.toNNReal angularScale) S_norm :=
    external_covering_number_scaling_real has_pos htr_pos
  have h_kaufman_at_scale : C_close ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal transportedScale) S_orig) : ENNReal) := by
    have h_mono : Metric.externalCoveringNumber (Real.toNNReal transportedScale)
          ((fun x : ℝ => transportedRadius * x) '' S_norm) ≤
        Metric.externalCoveringNumber (Real.toNNReal transportedScale) S_orig :=
      Metric.externalCoveringNumber_mono_set h_inclusion
    rw [h_scaling] at h_mono
    exact normalizedFiberCovering.trans (by exact_mod_cast h_mono)

  -- Weaken numerical: closing coefficient ≥ numerical coefficient
  have h1 : 1 ≤ delta ^ (-normalizedEta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdeltaOne (by linarith)
  have h2 : kaufman.commonConstant ≤ delta ^ (-normalizedEta) :=
    kaufman.commonConstant_bound
  have h3 : max 1 kaufman.commonConstant ≤ delta ^ (-normalizedEta) := max_le h1 h2
  have hKang_pos : 0 < kaufman_K_ang 1 gamma := kaufman_K_ang_one_positive hgamma_lt_one
  have hKfrost_pos : 0 < kaufman_K_frost0 1 gamma := kaufman_K_frost0_one_positive hgamma_lt_one
  have hkt_mono : kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma ≤
      kaufman_total_const (delta ^ (-normalizedEta)) 1 1 gamma := by
    dsimp only [kaufman_total_const]
    have h4 : 0 ≤ kaufman_K_ang 1 gamma * kaufman_K_frost0 1 gamma := by positivity
    set a := kaufman_K_ang 1 gamma * kaufman_K_frost0 1 gamma with ha_def
    set b := kaufman_K_ang 1 gamma with hb_def
    have ha_nonneg : 0 ≤ a := h4
    have hb_nonneg : 0 ≤ b := by positivity
    have h_main : ∀ (x y : ℝ), 0 ≤ x → x ≤ y →
        (x + a * (1 + x) + b) * x ≤ (y + a * (1 + y) + b) * y := by
      intro x y hx hxy
      have h5 : (y + a * (1 + y) + b) * y - (x + a * (1 + x) + b) * x =
          (y - x) * ((1 + a) * (x + y) + (a + b)) := by ring
      have h6 : 0 ≤ y - x := by linarith
      have h7 : 0 ≤ y := by linarith
      have h8 : 0 ≤ (1 + a) * (x + y) + (a + b) := by positivity
      have h9 : 0 ≤ (y - x) * ((1 + a) * (x + y) + (a + b)) := mul_nonneg h6 h8
      have h10 : 0 ≤ (y + a * (1 + y) + b) * y - (x + a * (1 + x) + b) * x := by
        rw [h5]; exact h9
      exact sub_nonneg.mp h10
    exact h_main (max 1 kaufman.commonConstant) (delta ^ (-normalizedEta)) (by positivity) h3
  have hden_close_pos : 0 < kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma := by
    have h5 : 0 < (max 1 kaufman.commonConstant : ℝ) := by positivity
    dsimp only [kaufman_total_const]; positivity
  have hden_num_pos : 0 < kaufman_total_const (delta ^ (-normalizedEta)) 1 1 gamma := by
    have h6 : 0 < (delta ^ (-normalizedEta) : ℝ) := Real.rpow_pos_of_pos hdelta _
    dsimp only [kaufman_total_const]; positivity
  have hcoeff_close_ge_num :
      (wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
        (2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma * (2 : ℝ) ^ gamma)) ≥
      (delta ^ normalizedEta) ^ 2 /
        (2 * kaufman_total_const (delta ^ (-normalizedEta)) 1 1 gamma * (2 : ℝ) ^ gamma) := by
    have hgraph_eq : wz1Lemma8_13FaithfulGraphDensity delta epsilon = delta ^ normalizedEta := by
      simp [wz1Lemma8_13FaithfulGraphDensity, normalizedEta] <;> rfl
    rw [hgraph_eq]
    have h7 : 0 < (2 : ℝ) ^ gamma := by positivity
    have h8 : 0 < 2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma * (2 : ℝ) ^ gamma := by positivity
    have h9 : 0 < 2 * kaufman_total_const (delta ^ (-normalizedEta)) 1 1 gamma * (2 : ℝ) ^ gamma := by positivity
    have hden_mono : 2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma * (2 : ℝ) ^ gamma ≤
        2 * kaufman_total_const (delta ^ (-normalizedEta)) 1 1 gamma * (2 : ℝ) ^ gamma := by
      gcongr <;> linarith
    exact div_le_div_of_nonneg_left (by positivity) h8 hden_mono

  set coefficient : ℝ :=
      (wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
        (2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma * (2 : ℝ) ^ gamma)) *
      angularScale ^ (-gamma)
  have hcoefficient_nonneg : 0 ≤ coefficient := by
    have h10 : 0 < angularScale ^ (-gamma) := Real.rpow_pos_of_pos has_pos _
    have h11 : 0 ≤ wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
        (2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma * (2 : ℝ) ^ gamma) := by positivity
    exact mul_nonneg h11 h10.le

  have hnum_real_close :
      7 * delta ^ (-epsilonOne) * (2 / angularScale) ^ (1 - epsilon) ≤ coefficient := by
    have hgraph_eq : wz1Lemma8_13FaithfulGraphDensity delta epsilon = delta ^ normalizedEta := by
      simp [wz1Lemma8_13FaithfulGraphDensity, normalizedEta] <;> rfl
    calc
      7 * delta ^ (-epsilonOne) * (2 / angularScale) ^ (1 - epsilon)
        ≤ (delta ^ normalizedEta) ^ 2 /
            (2 * kaufman_total_const (delta ^ (-normalizedEta)) 1 1 gamma * (2 : ℝ) ^ gamma) *
          angularScale ^ (-gamma) := hnumerical
      _ ≤ coefficient := by
        simp only [coefficient]
        rw [hgraph_eq]
        gcongr <;> exact hcoeff_close_ge_num

  have hnum_ennreal : F * D' ≤ C_close := by
    have hfactor_nonneg : 0 ≤ 7 * delta ^ (-epsilonOne) := by positivity
    have h5 : F * D' = ENNReal.ofReal ((7 * delta ^ (-epsilonOne)) * ((2 / angularScale) ^ (1 - epsilon))) := by
      simp only [F, D']
      rw [← ENNReal.ofReal_mul hfactor_nonneg] <;> rfl
    have h6 : C_close = ENNReal.ofReal coefficient := by
      simp only [C_close, coefficient, Kakeya.realRpowENN]
      have h7 : 0 ≤ wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
          (2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma * (2 : ℝ) ^ gamma) := by positivity
      rw [← ENNReal.ofReal_mul h7] <;> rfl
    rw [h5, h6]
    exact ENNReal.ofReal_le_ofReal hnum_real_close

  by_cases hcase : transportedScale ≥ delta
  · -- Case A
    have hrho_eq : rho = transportedScale := by
      simp [rho, hcase] <;> exact max_eq_right hcase
    have hratio : 2 * transportedRadius / rho = 2 / angularScale := by
      rw [hrho_eq]
      have h : transportedScale = transportedRadius * angularScale := rfl
      rw [h]
      field_simp [htr_pos.ne', has_pos.ne'] <;> ring
    have hF_ge_one : (1 : ENNReal) ≤ F := by
      have h7 : (1 : ℝ) ≤ 7 * delta ^ (-epsilonOne) := by
        have h8 : (1 : ℝ) ≤ delta ^ (-epsilonOne) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdeltaOne (by linarith)
        linarith
      have h9 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h9]
      exact ENNReal.ofReal_le_ofReal h7
    have h9 : D' ≤ F * D' := by
      calc D' = (1 : ENNReal) * D' := by ring
           _ ≤ F * D' := by gcongr
    have h_goal : D' ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho) S_orig) : ENNReal) := by
      rw [hrho_eq]
      exact h9.trans (hnum_ennreal.trans h_kaufman_at_scale)
    have h_final : Kakeya.realRpowENN (2 * transportedRadius / rho) (1 - epsilon) = D' := by
      simp [Kakeya.realRpowENN, D', hratio] <;> rfl
    rw [h_final]
    exact h_goal

  · -- Case B
    have hcase' : transportedScale < delta := by linarith
    have hrho_eq : rho = delta := by
      exact max_eq_left (by linarith)
    have hratio_le : 2 * transportedRadius / rho ≤ 2 / angularScale := by
      rw [hrho_eq]
      have h : transportedRadius * angularScale < delta := hcase'
      have h10 : transportedRadius * angularScale ≤ delta := by linarith
      have h11 : transportedRadius / delta ≤ transportedRadius / (transportedRadius * angularScale) := by
        gcongr <;> linarith
      have h12 : transportedRadius / (transportedRadius * angularScale) = 1 / angularScale := by
        field_simp [htr_pos.ne', has_pos.ne'] <;> ring
      have h13 : transportedRadius / delta ≤ 1 / angularScale := by
        calc transportedRadius / delta
          ≤ transportedRadius / (transportedRadius * angularScale) := h11
        _ = 1 / angularScale := h12
      calc 2 * transportedRadius / delta
        = 2 * (transportedRadius / delta) := by ring
      _ ≤ 2 * (1 / angularScale) := by gcongr
      _ = 2 / angularScale := by ring
    have hpower_le : (2 * transportedRadius / rho) ^ (1 - epsilon) ≤ (2 / angularScale) ^ (1 - epsilon) := by
      have h10 : 0 ≤ 2 * transportedRadius / rho := by positivity
      have h11 : 0 ≤ 2 / angularScale := by positivity
      gcongr <;> linarith

    have hwindow := wz1Lemma8_13_endpoint_transport_window
      (hdelta := hdelta)
      (hdeltaWidth := input.delta_le_width)
      (haspect := by
        dsimp only [wz1Lemma8_13FaithfulAspect]
        exact zero_lt_one.trans_le (le_max_left _ _))
      (haspectUpper := affine.aspect_upper)
      (hendpointLower := kaufman.endpointDistance_lower direction hdirection)
      (hendpointUpper := kaufman.endpointDistance_upper direction hdirection)
      (hrho₀ := by
        have hscale_id : transportedScale = 4 * D * input.width :=
          wz1Lemma8_13_transport_scale_identity hnw_pos
            (by simp [angularScale, normalizationWidth, wz1Lemma8_13FaithfulAngularScale])
        exact hscale_id)
    have hscale_lower : delta ≤ 3 * delta ^ (-epsilonOne) * transportedScale := hwindow.1

    set K : ℕ := Nat.floor (2 * delta / transportedScale) + 1
    set B : ENNReal := (↑(Metric.externalCoveringNumber (Real.toNNReal delta) S_orig) : ENNReal)

    have h_coarsen_enat :
        Metric.externalCoveringNumber (Real.toNNReal transportedScale) S_orig ≤
        (K : ENat) * Metric.externalCoveringNumber (Real.toNNReal delta) S_orig :=
      external_covering_number_coarsen1D hts_pos (by linarith)
    have h_C_le_KB : C_close ≤ (K : ENNReal) * B := by
      have h10 : C_close ≤
          (↑(Metric.externalCoveringNumber (Real.toNNReal transportedScale) S_orig) : ENNReal) :=
        h_kaufman_at_scale
      have h11 : (↑(Metric.externalCoveringNumber (Real.toNNReal transportedScale) S_orig) : ENNReal) ≤
          (K : ENNReal) * B := by
        have h_cast : (↑(Metric.externalCoveringNumber (Real.toNNReal transportedScale) S_orig) : ENNReal) ≤
            (↑((K : ENat) * Metric.externalCoveringNumber (Real.toNNReal delta) S_orig) : ENNReal) := by
          exact_mod_cast h_coarsen_enat
        have h_mul : (↑((K : ENat) * Metric.externalCoveringNumber (Real.toNNReal delta) S_orig) : ENNReal) =
            (K : ENNReal) * B := by
          simp [B, ENat.coe_mul] <;> rfl
        rw [h_mul] at h_cast
        exact h_cast
      exact h10.trans h11

    have h_cancel : F⁻¹ * C_close ≤ B :=
      ennreal_coarsening_factor_cancel
        hdelta hdeltaOne heo_pos hts_pos hscale_lower h_C_le_KB

    have h_lift_raw := ennreal_coarsening_numerical_lift
        (delta := delta) (epsilonOne := epsilonOne)
        (target := (2 / angularScale) ^ (1 - epsilon))
        (coefficient := coefficient)
        hdelta heo_pos (by positivity) hcoefficient_nonneg hnum_real_close
    have hC_eq : C_close = ENNReal.ofReal coefficient := by
      simp only [C_close, coefficient, Kakeya.realRpowENN]
      have h7 : 0 ≤ wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
          (2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1 gamma * (2 : ℝ) ^ gamma) := by positivity
      rw [← ENNReal.ofReal_mul h7] <;> rfl
    have h_lift : D' ≤ F⁻¹ * C_close := by
      simpa [D', F, hC_eq] using h_lift_raw

    have h_goal : D' ≤ B := h_lift.trans h_cancel

    have h_final : Kakeya.realRpowENN (2 * transportedRadius / rho) (1 - epsilon) ≤ B := by
      have h12 : Kakeya.realRpowENN (2 * transportedRadius / rho) (1 - epsilon) =
          ENNReal.ofReal ((2 * transportedRadius / rho) ^ (1 - epsilon)) := by
        simp [Kakeya.realRpowENN] <;> rfl
      rw [h12]
      have h13 : ENNReal.ofReal ((2 * transportedRadius / rho) ^ (1 - epsilon)) ≤ D' := by
        have h14 : (2 * transportedRadius / rho) ^ (1 - epsilon) ≤ (2 / angularScale) ^ (1 - epsilon) := hpower_le
        exact ENNReal.ofReal_le_ofReal h14
      exact h13.trans h_goal
    simpa [hrho_eq, B] using h_final

end Kakeya.Assouad

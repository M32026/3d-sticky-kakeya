import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper
import MyLeanRepo.Kakeya.Assouad.Hairbrush.ExpandedAssemblyAlgebra
import MyLeanRepo.Kakeya.Assouad.Hairbrush.SelfContainedAssemblyHelpers
import MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAmbientStemSelection
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.Hairbrush.SmallScaleWeakening

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Scale dichotomy helper with simple explicit parameters. -/
lemma scale_dichotomy_helper
    (δ zeta separation angleScale : ℝ)
    (hairDensity : ENNReal)
    (radius : ℝ)
    (hδ : 0 < δ)
    (hzeta_pos : 0 < zeta)
    (hzeta_lt_one : zeta < 1)
    (hsep : 0 < separation)
    (hang : 0 < angleScale)
    (hradius_pos : 0 < radius)
    (hrel : hairDensity ≤ ENNReal.ofReal 100 *
        ENNReal.ofReal (Real.rpow radius (1 - zeta))) :
    hairDensity ≤ hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale ∨
    separation * δ ≤ angleScale * radius := by
  let threshold := hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale
  have threshold_def : threshold = ENNReal.ofReal 100 *
      ENNReal.ofReal (Real.rpow (separation * δ / angleScale) (1 - zeta)) := by rfl
  by_cases h_low : hairDensity ≤ threshold
  · exact Or.inl h_low
  · have h' : threshold < hairDensity := lt_of_not_ge h_low
    have h1 : threshold < ENNReal.ofReal 100 *
        ENNReal.ofReal (Real.rpow radius (1 - zeta)) :=
      lt_of_lt_of_le h' hrel
    have h_exp_pos : 0 < 1 - zeta := by linarith
    have h_pos1 : 0 < separation * δ / angleScale := by positivity
    have h_rpow_nonneg1 : 0 ≤ Real.rpow (separation * δ / angleScale) (1 - zeta) :=
      Real.rpow_nonneg (by positivity) _
    have h100_pos : 0 < (ENNReal.ofReal 100 : ENNReal) :=
      ENNReal.ofReal_pos.mpr (by norm_num)
    have h100_ne_zero : (ENNReal.ofReal 100 : ENNReal) ≠ 0 := h100_pos.ne'
    have h100_ne_top : (ENNReal.ofReal 100 : ENNReal) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h3 : ENNReal.ofReal 100 *
        ENNReal.ofReal (Real.rpow (separation * δ / angleScale) (1 - zeta)) <
        ENNReal.ofReal 100 *
        ENNReal.ofReal (Real.rpow radius (1 - zeta)) := by
      rw [threshold_def] at h1
      exact h1
    have h2 : ENNReal.ofReal (Real.rpow (separation * δ / angleScale) (1 - zeta)) <
        ENNReal.ofReal (Real.rpow radius (1 - zeta)) :=
      (ENNReal.mul_lt_mul_iff_right h100_ne_zero h100_ne_top).mp h3
    have h4 : Real.rpow (separation * δ / angleScale) (1 - zeta) <
        Real.rpow radius (1 - zeta) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_rpow_nonneg1).mp h2
    have h5 : separation * δ / angleScale < radius :=
      (Real.rpow_lt_rpow_iff (by positivity) (by positivity) h_exp_pos).mp h4
    have h6 : separation * δ < angleScale * radius := by
      have h7 : (separation * δ / angleScale) * angleScale < radius * angleScale :=
        mul_lt_mul_of_pos_right h5 hang
      have h8 : (separation * δ / angleScale) * angleScale = separation * δ := by
        field_simp [hang.ne'] <;> ring
      rw [h8] at h7
      linarith [mul_comm radius angleScale]
    have h_hard_scale : separation * δ ≤ angleScale * radius := by linarith
    exact Or.inr h_hard_scale

theorem hairbrush_self_contained_fiber_assembly :
    HairbrushSelfContainedFiberAssemblyStatement := by
  intro h_small_scale h_core h_incidence h_two_ends h_param_sel
        h_low_density h_scale_dich h_stem_sel h_angle_band
        h_far_radius h_far_shading h_oriented_far_shading
        h_oriented_transfer h_fixed_stem_cordoba h_denom_absorption
        h_cordoba_geom h_hard_power h_numerical_closure
  intro loss hloss

  -- Choose eta strictly less than min(loss/100, 1/100)
  set eta : ℝ := min (loss / 100) (1 / 100) / 2 with heta_def
  have heta_pos : 0 < eta := by
    rw [heta_def]
    have h1 : 0 < min (loss / 100) (1 / 100) := by positivity
    linarith
  have heta_le : eta ≤ min (loss / 100) (1 / 100) := by
    rw [heta_def] <;> linarith
  have heta_loss : eta ≤ loss / 100 := by
    exact le_trans heta_le (min_le_left _ _)
  have heta_one : eta ≤ 1 / 100 := by
    exact le_trans heta_le (min_le_right _ _)
  have heta_loss_200 : eta ≤ loss / 200 := by
    rw [heta_def]
    have h : min (loss / 100) (1 / 100) ≤ loss / 100 := min_le_left _ _
    linarith
  have heta_one_200 : eta ≤ 1 / 200 := by
    rw [heta_def]
    have h : min (loss / 100) (1 / 100) ≤ 1 / 100 := min_le_right _ _
    linarith
  have h4eta_lt_loss : 4 * eta < loss := by
    have h : 4 * eta ≤ 4 * (loss / 100) := by gcongr
    linarith
  have heta_lt_quarter : eta < 1 / 4 := by linarith
  have heta_lt_one : eta < 1 := by linarith

  -- Set all parameters
  set zeta : ℝ := eta with hzeta_def
  set inputExponent : ℝ := 4 * eta with hinput_def
  set layerLoss : ℝ := eta with hlayer_def
  set hairLoss : ℝ := eta with hhair_def
  set familyLoss : ℝ := eta with hfamily_def
  set stemLoss : ℝ := eta with hstem_def
  set bandLoss : ℝ := eta with hband_def
  set cordobaLoss : ℝ := 2 * eta with hcordoba_def
  set katzExponent : ℝ := eta with hkatz_def
  set angleLoss : ℝ := eta with hangle_def
  set cardExponent : ℝ := eta + 3 with hcard_def
  set outputExponent : ℝ := 1 + 7 * eta with houtput_def
  set constantLoss : ℝ := eta with hconstant_def

  -- Exponent inequalities
  have h_low_density_ineq :
      4 * (inputExponent + layerLoss) + katzExponent / 2 +
          3 * angleLoss * (1 - zeta) < loss := by
    simp only [hinput_def, hlayer_def, hkatz_def, hangle_def, hzeta_def]
    nlinarith [heta_loss]
  have h_hard_power_ineq :
      1 + stemLoss + bandLoss + familyLoss + hairLoss + cordobaLoss < outputExponent := by
    simp only [hstem_def, hband_def, hfamily_def, hhair_def, hcordoba_def, houtput_def]
    <;> linarith
  have h_p_zeta_pos : 0 < hairbrushHomogeneousDensityPower zeta := by
    rw [hairbrushHomogeneousDensityPower, hzeta_def]
    have h1 : 0 < 1 - eta := by linarith
    positivity
  have h_density_power_ge_one : 1 ≤ 3 + hairbrushHomogeneousDensityPower zeta := by
    linarith [h_p_zeta_pos]
  have h_numerical_ineq :
      (outputExponent + 2 + (inputExponent + layerLoss) *
            (3 + hairbrushHomogeneousDensityPower zeta + 1) +
          2 * constantLoss) / 2 < 3 / 2 + loss := by
    simpa only [hinput_def, hlayer_def, houtput_def, hconstant_def, hzeta_def] using
      self_contained_numerical_closure_inequality
        loss eta hloss heta_pos heta_loss_200 heta_one_200

  -- Obtain delta₀ from each leaf
  -- Parameter selection first, since scaleSeparation is needed by small-scale and low-density leaves
  rcases h_param_sel eta stemLoss (by positivity) (by positivity) with
    ⟨scaleSeparation, δ₀_ps, hscale_sep, hδ₀_ps_pos, hδ₀_ps_le, h_ps_main⟩
  rcases h_small_scale (4 * eta) loss (6 * scaleSeparation)
      (by positivity) h4eta_lt_loss (by linarith) with
    ⟨δ₀_ss, hδ₀_ss_pos, hδ₀_ss_le, h_ss_main⟩
  rcases h_core inputExponent cardExponent layerLoss hairLoss
    (by positivity) (by positivity) (by positivity) (by positivity) with
    ⟨δ₀_core, hδ₀_core_pos, hδ₀_core_le, h_core_main⟩
  rcases h_two_ends zeta familyLoss cardExponent
    (by positivity) (by linarith) (by positivity) (by positivity) with
    ⟨δ₀_te, hδ₀_te_pos, hδ₀_te_le, h_te_main⟩
  rcases h_far_radius zeta familyLoss (by positivity) (by linarith) with
    ⟨separation, farFraction, hsep_ge, hff_pos, hff_le, h_fr_main⟩
  have hsep_ge_one : 1 ≤ separation := by linarith
  rcases h_low_density zeta inputExponent layerLoss hairLoss angleLoss
      katzExponent loss separation 100000000
    (by positivity) (by linarith) (by positivity) (by linarith)
    (by linarith) (by linarith) hsep_ge_one (by norm_num)
    h_low_density_ineq with
    ⟨δ₀_ld, hδ₀_ld_pos, hδ₀_ld_le, h_ld_main⟩
  rcases h_angle_band 2 bandLoss (by norm_num) (by positivity) with
    ⟨δ₀_ab, hδ₀_ab_pos, hδ₀_ab_le, h_ab_main⟩
  rcases h_cordoba_geom h_oriented_transfer h_fixed_stem_cordoba h_denom_absorption
      katzExponent cordobaLoss farFraction
    (by linarith) (by linarith) (by positivity) with
    ⟨δ₀_cg, hδ₀_cg_pos, hδ₀_cg_le, h_cg_main⟩
  rcases h_hard_power zeta stemLoss bandLoss familyLoss hairLoss cordobaLoss outputExponent
    (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    h_hard_power_ineq with
    ⟨δ₀_hp, hδ₀_hp_pos, hδ₀_hp_le, h_hp_main⟩
  rcases h_numerical_closure (inputExponent + layerLoss) outputExponent
      (3 + hairbrushHomogeneousDensityPower zeta) constantLoss loss
    (by positivity) h_density_power_ge_one (by positivity) (by positivity)
    h_numerical_ineq with
    ⟨δ₀_nc, hδ₀_nc_pos, hδ₀_nc_le, h_nc_main⟩

  -- Uniform delta₀: minimum of all leaf thresholds plus 1/10^8 for cardinality
  -- and 2^(-1/eta) to ensure 2 ≤ δ^(-eta) for numerical closure.
  let δ₀ := min (Real.rpow 2 (-1 / eta)) <| min (1 / 100000000 : ℝ) <|
    min δ₀_ss <| min δ₀_core <| min δ₀_te <| min δ₀_ps <|
    min δ₀_ld <| min δ₀_ab <| min δ₀_cg <| min δ₀_hp δ₀_nc

  have hδ₀_pos : 0 < δ₀ := by
    dsimp only [δ₀]
    have h1 : 0 < (10 : ℝ) ^ (-8 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : 0 < Real.rpow 2 (-1 / eta) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have h_eta_le : eta ≤ 1 / 200 := by
    exact heta_one_200
  have h_rpow_le : Real.rpow 2 (-1 / eta) ≤ 1 / 1000 := by
    have h1 : -1 / eta ≤ -200 := by
      have h2 : 0 < eta := heta_pos
      have h3 : 1 / eta ≥ 200 := by
        calc
          1 / eta ≥ 1 / (1 / 200 : ℝ) := one_div_le_one_div_of_le (by positivity) h_eta_le
          _ = 200 := by norm_num
      have h4 : -1 / eta ≤ -200 := by
        calc
          -1 / eta = -(1 / eta) := by ring
          _ ≤ -200 := neg_le_neg h3
      exact h4
    have h4 : Real.rpow 2 (-1 / eta) ≤ Real.rpow 2 (-200 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    have h5 : Real.rpow 2 (-200 : ℝ) ≤ 1 / 1000 := by
      norm_num
    exact le_trans h4 h5
  have hδ₀_le : δ₀ ≤ 1 / 1000 := by
    dsimp only [δ₀]
    have h : δ₀ ≤ Real.rpow 2 (-1 / eta) := min_le_left _ _
    exact le_trans h h_rpow_le
  have hδ₀_card : δ₀ ≤ (1 / 100000000 : ℝ) := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ₀_ss' : δ₀ ≤ δ₀_ss := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₀_core' : δ₀ ≤ δ₀_core := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ₀_te' : δ₀ ≤ δ₀_te := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδ₀_ps' : δ₀ ≤ δ₀_ps := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδ₀_ld' : δ₀ ≤ δ₀_ld := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hδ₀_ab' : δ₀ ≤ δ₀_ab := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
  have hδ₀_cg' : δ₀ ≤ δ₀_cg := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))
  have hδ₀_hp' : δ₀ ≤ δ₀_hp := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))))
  have hδ₀_nc' : δ₀ ≤ δ₀_nc := by
    dsimp only [δ₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans (min_le_right _ _)))))))))
  have hδ₀_const : δ₀ ≤ Real.rpow 2 (-1 / eta) := by
    dsimp only [δ₀]; exact min_le_left _ _

  refine ⟨eta, δ₀, heta_pos, heta_le, hδ₀_pos, hδ₀_le, ?_⟩
  intro δ theta confinementScale hδ hδ₀ hδ_le_theta htheta_le_conf
        hconf_le_6theta hconf_le_one F hF_nonempty hF_ball hF_ed
        h_angle_separated h_angular_confined Y h_aggregate hKT h_card h_two_broad

  have hδ_one : δ ≤ 1 := by linarith
  have htheta_pos : 0 < theta := by linarith
  have htheta_le_one : theta ≤ 1 := by linarith
  have hδ_small : δ ≤ (1 / 100000000 : ℝ) := le_trans hδ₀ hδ₀_card
  have hδ_small' : δ ≤ 1 / 100000000 := hδ_small

  -- Cardinality bound reduction: F.enncard ≤ δ^(-(eta+3))
  have h_card_poly : F.enncard ≤ Kakeya.realRpowENN δ (-(eta + 3)) :=
    h_card.trans (cardinality_bound_reduction hδ hδ_small' (by linarith) htheta_le_one)

  -- Parameter selection
  have h_ps := h_ps_main δ hδ (le_trans hδ₀ hδ₀_ps') theta hδ_le_theta htheta_le_one
  rcases h_ps with (h_small | h_nonempty)

  -- ==================== SMALL-SCALE BRANCH ====================
  · -- theta ≤ scaleSeparation * δ
    have h_conf_small : confinementScale ≤ (6 * scaleSeparation) * δ := by
      calc
        confinementScale ≤ 6 * theta := hconf_le_6theta
        _ ≤ 6 * (scaleSeparation * δ) := by gcongr
        _ = (6 * scaleSeparation) * δ := by ring
    have h_ss : HairbrushFiberTarget (theta := confinementScale) (loss := loss) Y :=
      h_ss_main δ confinementScale hδ (le_trans hδ₀ hδ₀_ss')
        (by linarith) (by linarith) h_conf_small F hF_nonempty
        h_angle_separated h_angular_confined Y h_aggregate
    -- We have target with confinementScale, weaken to theta
    exact weaken_fiber_target_scale htheta_le_conf h_ss

  -- ==================== HARD BRANCH ====================
  · -- We have parameter data
    let param : HairbrushHomogeneousParameterData δ eta theta stemLoss :=
      Classical.choice h_nonempty
    let angleScale : ℝ := param.angleScale
    have h_angleScale_pos : 0 < angleScale := param.angleScale_pos
    have h_angleScale_le_one : angleScale ≤ 1 := param.angleScale_le_one
    have h_delta_le_angleScale : δ ≤ angleScale := param.delta_le_angleScale
    have h_twice_angleScale_le_theta : 2 * angleScale ≤ theta :=
      param.twice_angleScale_le_theta
    have h_transverse_cap_small :
        Real.rpow (2 * angleScale / theta) eta ≤ 1 / 4 :=
      param.transverse_cap_small
    have h_stem_factor_lower :
        Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta ≤
          ENNReal.ofReal angleScale / ENNReal.ofReal (1000 * Real.pi) :=
      param.stem_factor_lower
    have h_angle_polynomial_lower :
        Kakeya.realRpowENN δ 2 ≤ ENNReal.ofReal angleScale :=
      param.angle_polynomial_lower

    -- Step 1: Ambient multiplicity core
    rcases h_core_main δ hδ (le_trans hδ₀ hδ₀_core') F Y hF_nonempty
        h_card_poly h_aggregate with ⟨core⟩

    -- Two-broadness inheritance for layer
    have h_layer_two_broad : IsTwoBroadAtScale core.layer theta eta :=
      two_broad_inheritance h_two_broad core.layer_eq

    -- Step 2: Homogeneous two-ends on core.hairs
    have h_hairs_card : core.hairs.enncard ≤ F.enncard := by
      have hcard : core.hairs.card ≤ F.card := Finset.card_le_card core.hairs_subset
      exact Nat.cast_le.mpr hcard
    have h_hairs_card_poly : core.hairs.enncard ≤ Kakeya.realRpowENN δ (-(eta + 3)) :=
      le_trans h_hairs_card h_card_poly
    rcases h_te_main δ hδ (le_trans hδ₀ hδ₀_te') core.hairs core.hairShading
        core.hairs_nonempty h_hairs_card_poly
        core.hairDensity core.hairDensity_pos core.hairDensity_ne_top
        core.per_hair_density_lower core.per_hair_density_upper with
      ⟨twoEnds⟩

    -- Refined density
    let refinedDensity : ENNReal :=
      ENNReal.ofReal (Real.rpow twoEnds.radius eta) * core.hairDensity
    have h_radius_pos : 0 < twoEnds.radius :=
      lt_of_lt_of_le hδ twoEnds.delta_le_radius
    have h_rpow_pos : 0 < Real.rpow twoEnds.radius eta :=
      Real.rpow_pos_of_pos h_radius_pos eta
    have h_ofReal_ne_zero : ENNReal.ofReal (Real.rpow twoEnds.radius eta) ≠ 0 := by
      have h_pos : 0 < ENNReal.ofReal (Real.rpow twoEnds.radius eta) :=
        ENNReal.ofReal_pos.mpr h_rpow_pos
      exact h_pos.ne'
    have h_refined_pos : refinedDensity ≠ 0 :=
      mul_ne_zero h_ofReal_ne_zero core.hairDensity_pos
    have h_refined_top : refinedDensity ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top core.hairDensity_ne_top
    let refinedDensityReal : ℝ := refinedDensity.toReal
    have h_refined_real_pos : 0 < refinedDensityReal :=
      ENNReal.toReal_pos h_refined_pos h_refined_top
    have h_refined_ofReal : ENNReal.ofReal refinedDensityReal = refinedDensity :=
      ennreal_ofReal_toReal h_refined_top

    -- Step 3: Scale dichotomy via helper lemma
    have h_sep_pos : 0 < separation := by linarith
    have h_radius_pos2 : 0 < twoEnds.radius :=
      lt_of_lt_of_le hδ twoEnds.delta_le_radius
    let katzTaoConstant : ℝ := Real.rpow δ (-eta)
    have h_katz_nonneg : 0 ≤ katzTaoConstant :=
      Real.rpow_nonneg hδ.le (-eta)
    have h_katz_bound : ENNReal.ofReal katzTaoConstant ≤ Kakeya.realRpowENN δ (-katzExponent) := by
      have h_katz_eq : katzExponent = eta := hkatz_def
      rw [h_katz_eq] <;> rfl
    have h_tube_vol : ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
      canonical_volume_lower hδ
    have h_dich : core.hairDensity ≤ hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale ∨
        separation * δ ≤ angleScale * twoEnds.radius :=
      scale_dichotomy_helper δ zeta separation angleScale
        core.hairDensity twoEnds.radius
        hδ (by linarith [hzeta_def]) (by linarith [hzeta_def]) h_sep_pos h_angleScale_pos h_radius_pos2
        twoEnds.density_radius_relation
    rcases h_dich with (h_low | h_hard_scale)

    -- ---- LOW-DENSITY SUB-BRANCH ----
    · have h_ld := h_ld_main δ theta angleScale hδ (le_trans hδ₀ hδ₀_ld')
          hδ_le_theta htheta_le_one h_angleScale_pos
          h_stem_factor_lower
          katzTaoConstant h_katz_nonneg h_katz_bound
          F Y h_card core
          h_tube_vol
          h_low
      exact h_ld

    -- ---- HARD-SCALE SUB-BRANCH ----
    · -- separation * δ ≤ angleScale * twoEnds.radius
      have h_hard_scale' : separation * δ ≤ angleScale * twoEnds.radius :=
        h_hard_scale

      -- Step 4: Stem selection on twoEnds.family with refined density
      have hδ_le_thousand : δ ≤ 1 / 1000 := by
        exact le_trans hδ₀ hδ₀_le
      have h_stem_nonempty : Nonempty (HairbrushAmbientStemSelectionData
            (angleScale := angleScale) (hairDensity := refinedDensityReal)
            core.layer core.mu twoEnds.shading) :=
        hairbrush_ambient_stem_selection_core
          (eta := eta) (theta := theta) (angleScale := angleScale)
          (F := F) (layer := core.layer) (mu := core.mu)
          (H := twoEnds.family) (hairShading := twoEnds.shading)
          (hairDensity := refinedDensityReal)
          heta_pos htheta_pos htheta_le_one h_angleScale_pos
          h_twice_angleScale_le_theta h_transverse_cap_small
          hδ hδ_le_thousand h_delta_le_angleScale
          hF_nonempty core.mu_pos core.multiplicity_lower h_layer_two_broad
          twoEnds.family_nonempty
          (twoEnds.family_subset.trans core.hairs_subset)
          (fun T hT => by
            have h1 : twoEnds.shading.carrier T ⊆ core.hairShading.carrier T := twoEnds.shading_subset T hT
            have h2 : T ∈ core.hairs := twoEnds.family_subset hT
            have h3 : core.hairShading.carrier T = core.layer.carrier T := core.hair_shading_eq T h2
            rw [h3] at h1
            exact h1)
          h_refined_real_pos
          (fun T hT => by
            have h := twoEnds.per_hair_mass T hT
            simpa [refinedDensity, h_refined_ofReal] using h)
      rcases h_stem_nonempty with ⟨stemSel⟩

      let brush := stemSel.brush
      have h_brush_subset : brush ⊆ twoEnds.family := stemSel.brush_subset
      have h_brush_nonempty : brush.Nonempty :=
        brush_nonempty_of_stem_selection stemSel hδ h_angleScale_pos core.mu_pos
          h_refined_real_pos twoEnds.family_nonempty hF_nonempty
      have h_brush_subset_F : brush ⊆ F :=
        h_brush_subset.trans twoEnds.family_subset |>.trans core.hairs_subset
      have h_brush_ed : brush.IsEssentiallyDistinct :=
        essentially_distinct_of_subset hF_ed h_brush_subset_F

      -- Restrict twoEnds.shading to brush
      let ZB : Kakeya.Shading brush :=
        { carrier := twoEnds.shading.carrier
          measurable_carrier := fun {T} hT =>
            twoEnds.shading.measurable_carrier (h_brush_subset hT)
          subset_tube := fun {T} hT =>
            twoEnds.shading.subset_tube (h_brush_subset hT) }
      have hZB_eq : ∀ U ∈ brush, ZB.carrier U = twoEnds.shading.carrier U := by
        intro U _; rfl

      -- Brush intersects stem
      have h_brush_intersects : ∀ U ∈ brush, (stemSel.stem.carrier ∩ U.carrier).Nonempty := by
        intro U hU
        have h1 : volume (twoEnds.shading.carrier U ∩ core.layer.carrier stemSel.stem) ≠ 0 :=
          (stemSel.transverse_overlap U hU).2
        have h2 : (twoEnds.shading.carrier U ∩ core.layer.carrier stemSel.stem).Nonempty :=
          MeasureTheory.nonempty_of_measure_ne_zero h1
        rcases h2 with ⟨x, hx1, hx2⟩
        have h3 : x ∈ U.carrier := twoEnds.shading.subset_tube (h_brush_subset hU) hx1
        have h4 : x ∈ stemSel.stem.carrier :=
          core.layer.subset_tube stemSel.stem_mem hx2
        exact ⟨x, h4, h3⟩

      -- Step 5: Angle band
      rcases h_ab_main δ hδ (le_trans hδ₀ hδ₀_ab') angleScale
          h_angleScale_pos h_angle_polynomial_lower h_angleScale_le_one
          brush ZB h_brush_nonempty h_brush_ed stemSel.stem
          (fun U hU => by
            have h := (stemSel.transverse_overlap U hU).1
            rw [hairbrushAcuteAngle_symm' U stemSel.stem] at h
            exact h)
          h_brush_intersects with ⟨band⟩

      -- Step 6: Far radius (with band.sigma)
      have h_sigma_ge : angleScale ≤ band.sigma := band.angleScale_le_sigma
      have h_sigma_le_one : band.sigma ≤ 1 := band.sigma_le_one
      have h_sigma_pos : 0 < band.sigma := by linarith
      have h_hard_scale_sigma : separation * δ ≤ band.sigma * twoEnds.radius := by
        calc
          separation * δ ≤ angleScale * twoEnds.radius := h_hard_scale'
          _ ≤ band.sigma * twoEnds.radius := by gcongr
      rcases h_fr_main δ hδ band.sigma h_sigma_pos h_sigma_le_one
          core.hairs core.hairShading core.hairDensity twoEnds
          h_hard_scale_sigma with ⟨radii⟩

      -- Step 7: Far shading
      rcases h_oriented_far_shading h_far_shading δ zeta familyLoss bandLoss
          angleScale hδ core.hairs core.hairShading
          (essentially_distinct_of_subset hF_ed core.hairs_subset)
          core.hairDensity twoEnds
          brush ZB h_brush_subset hZB_eq
          stemSel.stem band farFraction radii with ⟨far⟩

      -- Step 8: Cordoba geometry (bound on volume Y.union)
      have h_cordoba := h_cg_main δ hδ (le_trans hδ₀ hδ₀_cg')
          (Real.rpow δ (-eta)) (by positivity)
          (by rw [hkatz_def] <;> rfl)
          F Y hF_ed hKT
          zeta familyLoss bandLoss angleScale
          core.hairs core.hairShading
          core.hairs_subset
          (let h_hair_subset_Y : ∀ T ∈ core.hairs, core.hairShading.carrier T ⊆ Y.carrier T := by
            intro T hT
            have h1 : core.hairShading.carrier T = core.layer.carrier T := core.hair_shading_eq T hT
            have h2 : core.layer.carrier T = Y.carrier T ∩ core.support := core.layer_eq T (core.hairs_subset hT)
            have h3 : core.layer.carrier T ⊆ Y.carrier T := by
              rw [h2]
              intro x hx
              exact hx.1
            rw [h1]
            exact h3
          h_hair_subset_Y)
          core.hairDensity core.hairDensity_ne_top
          twoEnds brush ZB h_brush_subset hZB_eq
          stemSel.stem band radii far

      -- Volume finiteness of Y.union
      have hY_union_sub : Y.union ⊆ Kakeya.DeltaTube.unitBall := by
        intro x hx
        rcases hx with ⟨T, hT, hxT⟩
        have h1 : Y.carrier T ⊆ T.carrier := Y.subset_tube hT
        have h2 : T.carrier ⊆ Kakeya.DeltaTube.unitBall := hF_ball hT
        exact h2 (h1 hxT)
      have h_vol_ne_top : volume Y.union ≠ ⊤ := by
        have h3 : volume Y.union ≤ volume Kakeya.DeltaTube.unitBall := measure_mono hY_union_sub
        have h4 : volume Kakeya.DeltaTube.unitBall ≠ ⊤ :=
          (isCompact_closedBall (0 : Point3) 1).measure_ne_top
        exact ne_top_of_le_ne_top h4 h3

      -- Step 9: Hard power
      have h_hp := h_hp_main δ hδ (le_trans hδ₀ hδ₀_hp') theta twoEnds.radius
          htheta_pos htheta_le_one
          twoEnds.delta_le_radius twoEnds.radius_le_two
          F.enncard core.hairs.enncard twoEnds.family.enncard
          brush.enncard band.oriented.enncard
          (core.mu : ENNReal)
          core.layerDensity core.hairDensity refinedDensity
          (volume Y.union)
          (by change (F.card : ENNReal) ≠ 0; exact_mod_cast hF_nonempty.card_pos.ne')
          (by change (F.card : ENNReal) ≠ ⊤; simp)
          (by change (core.hairs.card : ENNReal) ≠ 0; exact_mod_cast core.hairs_nonempty.card_pos.ne')
          (by change (core.hairs.card : ENNReal) ≠ ⊤; simp)
          (by change (twoEnds.family.card : ENNReal) ≠ 0; exact_mod_cast twoEnds.family_nonempty.card_pos.ne')
          (by change (twoEnds.family.card : ENNReal) ≠ ⊤; simp)
          (by change (brush.card : ENNReal) ≠ 0; exact_mod_cast h_brush_nonempty.card_pos.ne')
          (by change (brush.card : ENNReal) ≠ ⊤; simp)
          (by rw [band.oriented_card]; change (band.source.card : ENNReal) ≠ 0; exact_mod_cast band.source_nonempty.card_pos.ne')
          (by rw [band.oriented_card]; change (band.source.card : ENNReal) ≠ ⊤; simp)
          (by exact_mod_cast core.mu_pos.ne')
          (by simp)
          core.layerDensity_pos core.layerDensity_ne_top
          core.hairDensity_pos core.hairDensity_ne_top
          h_refined_pos h_refined_top
          h_vol_ne_top
          core.layer_density_le_hair
          core.weighted_hair_retention
          twoEnds.family_retention
          (by
            have hz : zeta = eta := hzeta_def
            have h : ENNReal.ofReal (Real.rpow twoEnds.radius zeta) * core.hairDensity = refinedDensity := by
              simp [refinedDensity, hz]
            rw [h])
          twoEnds.density_radius_relation
          (stem_cardinality_retention h_refined_ofReal h_stem_factor_lower
            stemSel.brush_cardinality_lower)
          (by
            have h_ret : Kakeya.realRpowENN δ bandLoss * brush.enncard ≤ band.source.enncard :=
              band.source_retention
            have h_card : band.oriented.enncard = band.source.enncard := band.oriented_card
            rw [h_card]
            exact h_ret)
          h_cordoba

      -- Step 10: Ambient incidence (on layer, then weaken to Y)
      have h_inc := h_incidence δ inputExponent layerLoss hairLoss hδ
          F Y core
          (canonical_volume_lower hδ)
      have h_layer_union_subset : core.layer.union ⊆ Y.union := by
        intro x hx
        rcases hx with ⟨T, hT, hxT⟩
        have h4 : x ∈ core.layer.carrier T := hxT
        have h5 : core.layer.carrier T ⊆ Y.carrier T := by
          rw [core.layer_eq T hT]
          intro x hx
          exact hx.1
        exact ⟨T, hT, h5 h4⟩
      have h_vol_layer_le_Y : volume core.layer.union ≤ volume Y.union :=
        measure_mono h_layer_union_subset
      have h_inc_Y : core.layerDensity * F.enncard * ENNReal.ofReal (δ ^ 2) ≤
          2 * (core.mu : ENNReal) * volume Y.union := by
        calc
          core.layerDensity * F.enncard * ENNReal.ofReal (δ ^ 2)
            ≤ 2 * (core.mu : ENNReal) * volume core.layer.union := h_inc
          _ ≤ 2 * (core.mu : ENNReal) * volume Y.union := by gcongr

      -- Step 11: Numerical closure
      have h_nc_at_scale :
          HairbrushLocalNumericalClosureAtScale
            (inputExponent + layerLoss) outputExponent
            (3 + hairbrushHomogeneousDensityPower zeta) constantLoss loss δ₀_nc :=
        h_nc_main
      exact close_hairbrush_fiber_target
          (F := F) (Y := Y) (mu := (core.mu : ENNReal))
          (density := core.layerDensity)
          h_nc_at_scale hδ (le_trans hδ₀ hδ₀_nc') htheta_pos htheta_le_one
          (by change (F.card : ENNReal) ≠ 0; exact_mod_cast hF_nonempty.card_pos.ne')
          (by change (F.card : ENNReal) ≠ ⊤; simp)
          (by exact_mod_cast core.mu_pos.ne')
          (by simp)
          core.layerDensity_pos core.layerDensity_ne_top
          h_vol_ne_top
          (by
            have h : Kakeya.realRpowENN δ (inputExponent + layerLoss) ≤ core.layerDensity :=
              core.input_density_retention
            simpa [hinput_def, hlayer_def] using h)
          (by
            have hδ_const : δ ≤ Real.rpow 2 (-1 / eta) := le_trans hδ₀ hδ₀_const
            simpa only [hconstant_def] using
              two_le_realRpowENN_neg hδ heta_pos hδ_const)
          (by
            simpa only [hconstant_def] using
              hairbrush_realRpowENN_le_one hδ hδ_one heta_pos.le)
          (by
            have h_hp' : ENNReal.ofReal (Real.rpow δ outputExponent) * (1 : ENNReal) * ENNReal.ofReal theta * ENNReal.rpow core.layerDensity (3 + hairbrushHomogeneousDensityPower zeta) * (core.mu : ENNReal) ≤ volume Y.union := by
              simpa [Kakeya.realRpowENN, houtput_def] using h_hp
            exact h_hp')
          h_inc_Y

end Kakeya.Assouad

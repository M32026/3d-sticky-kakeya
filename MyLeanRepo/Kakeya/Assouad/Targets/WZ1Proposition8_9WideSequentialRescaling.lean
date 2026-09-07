import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ActiveProjectionFrostmanTransfer

/-!
PDF Proposition 8.9 wide branch: sequentially rescale the active `G₁`,
`G₂`, and `F` coordinate classes, refining the induced graph after every
selection.
-/

namespace Kakeya.Assouad

open scoped ENNReal

theorem wz1_proposition8_9_wide_sequential_rescaling :
    WZ1Proposition8_9WideSequentialRescalingStatement := by
  intro hRefine hRescale epsilon parameters heps_pos heps_lt_one

  -- Choose etaCap to ensure both epsilon_r ≤ epsilon/10 and eta < workingLambda.
  set etaCap : ℝ := min (epsilon / parameters.stripEpsilon) (parameters.workingLambda / 2)
    with hetaCap_def
  have h1_pos : 0 < epsilon / parameters.stripEpsilon :=
    div_pos heps_pos parameters.stripEpsilon_pos
  have h2_pos : 0 < parameters.workingLambda / 2 :=
    div_pos parameters.workingLambda_pos (by norm_num)
  have hetaCap_pos : 0 < etaCap := lt_min h1_pos h2_pos
  refine ⟨etaCap, hetaCap_pos, ?_⟩

  intro eta heta_pos heta_le
  have h_eta_le1 : eta ≤ epsilon / parameters.stripEpsilon :=
    le_trans heta_le (by simp [hetaCap_def])
  have h_eta_le2 : eta ≤ parameters.workingLambda / 2 :=
    le_trans heta_le (by simp [hetaCap_def])

  set epsilon_r : ℝ := parameters.stripEpsilon * eta / 10 with hepsilon_r_def
  have hepsilon_r_pos : 0 < epsilon_r := by
    rw [hepsilon_r_def]
    have h : 0 < parameters.stripEpsilon * eta := mul_pos parameters.stripEpsilon_pos heta_pos
    exact div_pos h (by norm_num)
  have hepsilon_r_le_tenth : epsilon_r ≤ epsilon / 10 := by
    rw [hepsilon_r_def]
    have h_strip_le : parameters.stripEpsilon * eta ≤ epsilon := by
      have h : parameters.stripEpsilon * eta ≤ parameters.stripEpsilon * (epsilon / parameters.stripEpsilon) :=
        mul_le_mul_of_nonneg_left h_eta_le1 (le_of_lt parameters.stripEpsilon_pos)
      have h2 : parameters.stripEpsilon * (epsilon / parameters.stripEpsilon) = epsilon := by
        field_simp [parameters.stripEpsilon_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    linarith
  have heta_lt_wl : eta < parameters.workingLambda := by
    linarith [parameters.workingLambda_pos]
  set gamma : ℝ := parameters.workingLambda - eta with hgamma_def
  have hgamma_pos : 0 < gamma := by
    rw [hgamma_def] <;> linarith

  -- Obtain rescaling threshold from the supplied lemma.
  rcases hRescale epsilon_r hepsilon_r_pos with
    ⟨delta₀Rescale, hRescalePos, hRescaleLeOne, hRescaleBody⟩

  -- Additional threshold for Frostman constant absorption.
  set delta₀Frost : ℝ := Real.rpow (65536 : ℝ) (-1 / gamma) with hdelta₀Frost_def
  have hdelta₀Frost_pos : 0 < delta₀Frost :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hdelta₀Frost_le_one : delta₀Frost ≤ 1 := by
    have h2 : 1 < (65536 : ℝ) := by norm_num
    have h3 : -1 / gamma < 0 := by
      have h4 : 0 < gamma := hgamma_pos
      exact div_neg_of_neg_of_pos (by norm_num) h4
    have h4 : Real.rpow (65536 : ℝ) (-1 / gamma) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) h3
    rw [hdelta₀Frost_def]
    exact h4.le

  set delta₀ : ℝ := min delta₀Rescale delta₀Frost with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := lt_min hRescalePos hdelta₀Frost_pos
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    have h : delta₀ ≤ delta₀Rescale := by simp [hdelta₀_def]
    exact h.trans hRescaleLeOne

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta F G₁ G₂ H hdelta_pos hdelta_le data hwidth

  have hdelta_le_one : delta ≤ 1 := by linarith
  have hdelta_le_rescale : delta ≤ delta₀Rescale :=
    le_trans hdelta_le (by simp [hdelta₀_def])
  have hdelta_small : delta ≤ (65536 : ℝ)^(-1 / gamma) :=
    le_trans hdelta_le (by simp [hdelta₀_def, hdelta₀Frost_def])

  -- Density constants
  let d1_enn : ENNReal := (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta
  let d2_enn : ENNReal := d1_enn / 16
  let d3_enn : ENNReal := d2_enn / 16

  set C : ENNReal := Kakeya.realRpowENN delta (-(2 * parameters.workingLambda))
    with hC_def
  set C_old : ENNReal := Kakeya.realRpowENN delta (-parameters.workingLambda)
    with hC_old_def

  have hC_ge_one : 1 ≤ C := by
    rw [hC_def]
    have h_exp : -(2 * parameters.workingLambda) ≤ 0 := by linarith
    have h_real : Real.rpow delta (-(2 * parameters.workingLambda)) ≥ 1 := by
      have h : Real.rpow delta (-(2 * parameters.workingLambda)) ≥ Real.rpow delta 0 :=
        Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
      simpa using h
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h_real

  -- Width condition for rescaling
  have h_width_cond : Real.rpow delta (1 - epsilon_r) ≤ data.width := by
    have h1 : 1 - epsilon_r ≥ 1 - epsilon / 10 := by linarith
    have h2 : Real.rpow delta (1 - epsilon_r) ≤ Real.rpow delta (1 - epsilon / 10) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h1
    have h3 : Real.rpow delta (1 - epsilon / 10) < data.width := hwidth
    exact h2.trans h3.le

  -- Real-level density constants
  set d1_real : ℝ := (1 / 256 : ℝ) * Real.rpow delta eta with hd1_real_def
  set d2_real : ℝ := d1_real / 16 with hd2_real_def
  set d3_real : ℝ := d2_real / 16 with hd3_real_def

  have h_d1_real_pos : 0 < d1_real := by
    rw [hd1_real_def]; have h : 0 < Real.rpow delta eta := Real.rpow_pos_of_pos hdelta_pos eta; positivity
  have h_d2_real_pos : 0 < d2_real := by positivity
  have h_d3_real_pos : 0 < d3_real := by positivity

  -- Bridge ENNReal ↔ Real for density constants
  have h_ofReal_div256 : ENNReal.ofReal (1 / 256 : ℝ) = (1 / 256 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 256 by norm_num)]
    <;> simp
    <;> rfl
  have hd1_eq : d1_enn = ENNReal.ofReal d1_real := by
    dsimp only [d1_enn]
    rw [← h_ofReal_div256, Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 / 256 : ℝ) by norm_num)]
    <;> simp [hd1_real_def]
  have hd2_eq : d2_enn = ENNReal.ofReal d2_real := by
    dsimp only [d2_enn]
    rw [hd1_eq]
    have h : ENNReal.ofReal d1_real / (16 : ENNReal) = ENNReal.ofReal (d1_real / (16 : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < (16 : ℝ) by norm_num)]
      <;> norm_cast
    exact h
  have hd3_eq : d3_enn = ENNReal.ofReal d3_real := by
    dsimp only [d3_enn]
    rw [hd2_eq]
    have h : ENNReal.ofReal d2_real / (16 : ENNReal) = ENNReal.ofReal (d2_real / (16 : ℝ)) := by
      have h2 : ENNReal.ofReal (d2_real / (16 : ℝ)) = ENNReal.ofReal d2_real / (16 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < (16 : ℝ) by norm_num)]
        <;> simp
      exact h2.symm
    exact h

  have h_d1_ne_zero : d1_enn ≠ 0 := by
    rw [hd1_eq]
    exact (ENNReal.ofReal_pos.mpr h_d1_real_pos).ne'
  have h_d2_ne_zero : d2_enn ≠ 0 := by
    rw [hd2_eq]
    exact (ENNReal.ofReal_pos.mpr h_d2_real_pos).ne'
  have h_d3_ne_zero : d3_enn ≠ 0 := by
    rw [hd3_eq]
    exact (ENNReal.ofReal_pos.mpr h_d3_real_pos).ne'

  -- Real-level constant equality: C_old_real / dk_real = 256 * 16^k * delta^(-(wl+eta))
  have h_real_eq1 : Real.rpow delta (-parameters.workingLambda) / d1_real =
      (256 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta)) := by
    rw [hd1_real_def]
    have hpos_eta : 0 < Real.rpow delta eta := Real.rpow_pos_of_pos hdelta_pos eta
    have h_div : Real.rpow delta (-parameters.workingLambda) / Real.rpow delta eta =
        Real.rpow delta (-(parameters.workingLambda + eta)) := by
      have h_neg : Real.rpow delta (-eta) = (Real.rpow delta eta)⁻¹ := Real.rpow_neg hdelta_pos.le eta
      calc
        Real.rpow delta (-parameters.workingLambda) / Real.rpow delta eta
          = Real.rpow delta (-parameters.workingLambda) * (Real.rpow delta eta)⁻¹ := by rw [div_eq_mul_inv]
        _ = Real.rpow delta (-parameters.workingLambda) * Real.rpow delta (-eta) := by rw [h_neg]
        _ = Real.rpow delta (-(parameters.workingLambda + eta)) := by
          have h_add : (-parameters.workingLambda) + (-eta) = -(parameters.workingLambda + eta) := by ring
          have h_ne_zero : (-parameters.workingLambda) + (-eta) ≠ 0 := by linarith
          have h_rpow : Real.rpow delta ((-parameters.workingLambda) + (-eta)) =
              Real.rpow delta (-parameters.workingLambda) * Real.rpow delta (-eta) :=
            Real.rpow_add' hdelta_pos.le h_ne_zero
          rw [h_add] at h_rpow
          exact h_rpow.symm
    have h_main : Real.rpow delta (-parameters.workingLambda) / ((1 / 256 : ℝ) * Real.rpow delta eta) =
        (256 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta)) := by
      calc
        Real.rpow delta (-parameters.workingLambda) / ((1 / 256 : ℝ) * Real.rpow delta eta)
          = (256 : ℝ) * (Real.rpow delta (-parameters.workingLambda) / Real.rpow delta eta) := by
            field_simp [hpos_eta.ne'] <;> ring
        _ = (256 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta)) := by rw [h_div]
    exact h_main
  have h_real_eq2 : Real.rpow delta (-parameters.workingLambda) / d2_real =
      (4096 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta)) := by
    rw [hd2_real_def]
    have h : Real.rpow delta (-parameters.workingLambda) / (d1_real / 16) =
        16 * (Real.rpow delta (-parameters.workingLambda) / d1_real) := by
      field_simp [h_d1_real_pos.ne'] <;> ring
    rw [h, h_real_eq1] <;> ring
  have h_real_eq3 : Real.rpow delta (-parameters.workingLambda) / d3_real =
      (65536 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta)) := by
    rw [hd3_real_def]
    have h : Real.rpow delta (-parameters.workingLambda) / (d2_real / 16) =
        16 * (Real.rpow delta (-parameters.workingLambda) / d2_real) := by
      field_simp [h_d2_real_pos.ne'] <;> ring
    rw [h, h_real_eq2] <;> ring

  -- Retention bounds at ENNReal level
  have h_ret1_enn : (256 : ENNReal) * Kakeya.realRpowENN delta (-(parameters.workingLambda + eta)) ≤
      Kakeya.realRpowENN delta (-(2 * parameters.workingLambda)) :=
    wideSequentialFrostmanRetentionBound_round1
      hdelta_pos hdelta_le_one heta_pos parameters.workingLambda_pos heta_lt_wl hdelta_small
  have h_ret2_enn : (4096 : ENNReal) * Kakeya.realRpowENN delta (-(parameters.workingLambda + eta)) ≤
      Kakeya.realRpowENN delta (-(2 * parameters.workingLambda)) :=
    wideSequentialFrostmanRetentionBound_round2
      hdelta_pos hdelta_le_one heta_pos parameters.workingLambda_pos heta_lt_wl hdelta_small
  have h_ret3_enn : (65536 : ENNReal) * Kakeya.realRpowENN delta (-(parameters.workingLambda + eta)) ≤
      Kakeya.realRpowENN delta (-(2 * parameters.workingLambda)) :=
    wideSequentialFrostmanRetentionBound
      hdelta_pos hdelta_le_one heta_pos parameters.workingLambda_pos heta_lt_wl hdelta_small

  -- ENNReal division bridge
  have h_div1 : C_old / d1_enn = ENNReal.ofReal (Real.rpow delta (-parameters.workingLambda) / d1_real) := by
    rw [hC_old_def, hd1_eq, Kakeya.realRpowENN]
    rw [ENNReal.ofReal_div_of_pos h_d1_real_pos]
  have h_div2 : C_old / d2_enn = ENNReal.ofReal (Real.rpow delta (-parameters.workingLambda) / d2_real) := by
    rw [hC_old_def, hd2_eq, Kakeya.realRpowENN]
    rw [ENNReal.ofReal_div_of_pos h_d2_real_pos]
  have h_div3 : C_old / d3_enn = ENNReal.ofReal (Real.rpow delta (-parameters.workingLambda) / d3_real) := by
    rw [hC_old_def, hd3_eq, Kakeya.realRpowENN]
    rw [ENNReal.ofReal_div_of_pos h_d3_real_pos]

  -- Bridge: ofReal (n * rpow) = (n : ENNReal) * realRpowENN
  have h_bridge1 : ENNReal.ofReal ((256 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta))) =
      (256 : ENNReal) * Kakeya.realRpowENN delta (-(parameters.workingLambda + eta)) := by
    simp only [Kakeya.realRpowENN]
    have h : (256 : ENNReal) = ENNReal.ofReal (256 : ℝ) := by norm_cast
    rw [h, ENNReal.ofReal_mul (by positivity)]
  have h_bridge2 : ENNReal.ofReal ((4096 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta))) =
      (4096 : ENNReal) * Kakeya.realRpowENN delta (-(parameters.workingLambda + eta)) := by
    simp only [Kakeya.realRpowENN]
    have h : (4096 : ENNReal) = ENNReal.ofReal (4096 : ℝ) := by norm_cast
    rw [h, ENNReal.ofReal_mul (by positivity)]
  have h_bridge3 : ENNReal.ofReal ((65536 : ℝ) * Real.rpow delta (-(parameters.workingLambda + eta))) =
      (65536 : ENNReal) * Kakeya.realRpowENN delta (-(parameters.workingLambda + eta)) := by
    simp only [Kakeya.realRpowENN]
    have h : (65536 : ENNReal) = ENNReal.ofReal (65536 : ℝ) := by norm_cast
    rw [h, ENNReal.ofReal_mul (by positivity)]

  -- Round bounds
  have h_round_bound1 : C_old / d1_enn ≤ C := by
    rw [h_div1, h_real_eq1, h_bridge1]
    simpa [hC_def] using h_ret1_enn
  have h_round_bound2 : C_old / d2_enn ≤ C := by
    rw [h_div2, h_real_eq2, h_bridge2]
    simpa [hC_def] using h_ret2_enn
  have h_round_bound3 : C_old / d3_enn ≤ C := by
    rw [h_div3, h_real_eq3, h_bridge3]
    simpa [hC_def] using h_ret3_enn

  -- Affine maps
  let phiG : Point2 ≃ᵃ[ℝ] Point2 :=
    wideCoarsePhiG data.direction data.width data.width_pos
      data.base 0 data.direction_unit
  let phiF : Point2 ≃ᵃ[ℝ] Point2 :=
    wideCoarsePhiF data.direction data.width data.width_pos data.direction_unit

  have hphiG_nonexp : ∀ (x y : Point2),
      dist (phiG.symm x) (phiG.symm y) ≤ dist x y :=
    wideCoarsePhiG_symm_nonexpansive
      (hw := data.width_pos) (hw_le_one := data.width_le_one)
  have hphiF_nonexp : ∀ (x y : Point2),
      dist (phiF.symm x) (phiF.symm y) ≤ dist x y :=
    wideCoarsePhiF_symm_nonexpansive
      (hw := data.width_pos) (hw_le_one := data.width_le_one)

  -- =====================================================================
  -- ROUND 1: Rescale active G₁ projection
  -- =====================================================================
  set E1 : DiscreteSet 2 := wz1ActiveTripleProjection data.refinedH 1
    with hE1_def
  have hE1_subset_G1 : E1 ⊆ data.selectedG₁ :=
    active_triple_projection_subset data.uniform 1
  have hE1_nonempty : E1.Nonempty :=
    active_triple_projection_nonempty data.uniform 1
  have hE1_separated : E1.IsDeltaSeparated delta := by
    intro x hx y hy hxy
    exact data.selectedG₁_separated (hE1_subset_G1 hx) (hE1_subset_G1 hy) hxy
  have hE1_frostman_raw : E1.IsFrostman delta 1 (C_old / d1_enn) :=
    active_projection_frostman_transfer 1 data.uniform data.selectedG₁_frostman h_d1_ne_zero
  have hE1_frostman : E1.IsFrostman delta 1 C :=
    hE1_frostman_raw.mono h_round_bound1

  have hG1_strip : ∀ p ∈ E1,
      |inner ℝ (p - data.base) (wz1Perp2 data.direction)| ≤ data.width := by
    intro p hp
    have h5 : p ∈ data.selectedG₁ := hE1_subset_G1 hp
    have h6 : p ∈ wz1LineNeighborhood data.base data.direction data.width :=
      data.first_strip p h5
    simpa [wz1LineNeighborhood] using h6
  have hG1_ball : E1.IsInUnitBall := by
    intro p hp
    exact data.selectedG₁_ball p (hE1_subset_G1 hp)
  have hphiG1_bounded : ∀ p ∈ E1, dist (phiG p) 0 ≤ 2 :=
    wideCoarsePhiG_zero_anchor_image_bounded hG1_strip hG1_ball

  rcases hRescaleBody delta data.width hdelta_pos hdelta_le_rescale
      data.delta_le_width data.width_le_one h_width_cond
      E1 hE1_nonempty C hC_ge_one hE1_separated hE1_frostman
      phiG hphiG_nonexp hphiG1_bounded with
    ⟨firstRescale⟩

  have hactive1 : ∀ vertex ∈ firstRescale.selected,
      ∃ edge ∈ data.refinedH, edge.2.1 = vertex := by
    intro vertex hvertex
    have h_in_E1 : vertex ∈ E1 := firstRescale.selected_subset hvertex
    rcases Finset.mem_image.mp h_in_E1 with ⟨edge, hedge, heq⟩
    have hcoord : wz1TripleCoordinate edge 1 = edge.2.1 := by
      simp [wz1TripleCoordinate]
    rw [hcoord] at heq
    exact ⟨edge, hedge, heq⟩

  have hfirstSelected_subset_G1 : firstRescale.selected ⊆ data.selectedG₁ :=
    subset_trans firstRescale.selected_subset hE1_subset_G1

  rcases restrict_first_endpoint_and_refine data.uniform
      hfirstSelected_subset_G1 hactive1
      firstRescale.selected_nonempty hRefine with
    ⟨firstGraph, firstGraph_subset, firstGraph_nonempty, firstUniform⟩

  -- =====================================================================
  -- ROUND 2: Rescale active G₂ projection
  -- =====================================================================
  set E2 : DiscreteSet 2 := wz1ActiveTripleProjection firstGraph 2
    with hE2_def
  have hE2_subset_G2 : E2 ⊆ data.selectedG₂ :=
    active_triple_projection_subset firstUniform 2
  have hE2_nonempty : E2.Nonempty :=
    active_triple_projection_nonempty firstUniform 2
  have hE2_separated : E2.IsDeltaSeparated delta := by
    intro x hx y hy hxy
    exact data.selectedG₂_separated (hE2_subset_G2 hx) (hE2_subset_G2 hy) hxy
  have hE2_frostman_raw : E2.IsFrostman delta 1 (C_old / d2_enn) :=
    active_projection_frostman_transfer 2 firstUniform data.selectedG₂_frostman h_d2_ne_zero
  have hE2_frostman : E2.IsFrostman delta 1 C :=
    hE2_frostman_raw.mono h_round_bound2

  have hG2_strip : ∀ p ∈ E2,
      |inner ℝ (p - data.base) (wz1Perp2 data.direction)| ≤ data.width := by
    intro p hp
    have h5 : p ∈ data.selectedG₂ := hE2_subset_G2 hp
    have h6 : p ∈ wz1LineNeighborhood data.base data.direction data.width :=
      data.second_strip p h5
    simpa [wz1LineNeighborhood] using h6
  have hG2_ball : E2.IsInUnitBall := by
    intro p hp
    exact data.selectedG₂_ball p (hE2_subset_G2 hp)
  have hphiG2_bounded : ∀ p ∈ E2, dist (phiG p) 0 ≤ 2 :=
    wideCoarsePhiG_zero_anchor_image_bounded hG2_strip hG2_ball

  rcases hRescaleBody delta data.width hdelta_pos hdelta_le_rescale
      data.delta_le_width data.width_le_one h_width_cond
      E2 hE2_nonempty C hC_ge_one hE2_separated hE2_frostman
      phiG hphiG_nonexp hphiG2_bounded with
    ⟨secondRescale⟩

  have hactive2 : ∀ vertex ∈ secondRescale.selected,
      ∃ edge ∈ firstGraph, edge.2.2 = vertex := by
    intro vertex hvertex
    have h_in_E2 : vertex ∈ E2 := secondRescale.selected_subset hvertex
    rcases Finset.mem_image.mp h_in_E2 with ⟨edge, hedge, heq⟩
    have hcoord : wz1TripleCoordinate edge 2 = edge.2.2 := by
      simp [wz1TripleCoordinate]
    rw [hcoord] at heq
    exact ⟨edge, hedge, heq⟩

  have hsecondSelected_subset_G2 : secondRescale.selected ⊆ data.selectedG₂ :=
    subset_trans secondRescale.selected_subset hE2_subset_G2

  rcases restrict_second_endpoint_and_refine firstUniform
      hsecondSelected_subset_G2 hactive2
      secondRescale.selected_nonempty hRefine with
    ⟨secondGraph, secondGraph_subset, secondGraph_nonempty, secondUniform⟩

  -- =====================================================================
  -- ROUND 3: Rescale active F projection
  -- =====================================================================
  set E3 : DiscreteSet 2 := wz1ActiveTripleProjection secondGraph 0
    with hE3_def
  have hE3_subset_F : E3 ⊆ data.selectedF :=
    active_triple_projection_subset secondUniform 0
  have hE3_nonempty : E3.Nonempty :=
    active_triple_projection_nonempty secondUniform 0
  have hE3_separated : E3.IsDeltaSeparated delta := by
    intro x hx y hy hxy
    exact data.selectedF_separated (hE3_subset_F hx) (hE3_subset_F hy) hxy
  have hE3_frostman_raw : E3.IsFrostman delta 1 (C_old / d3_enn) :=
    active_projection_frostman_transfer 0 secondUniform data.selectedF_frostman h_d3_ne_zero
  have hE3_frostman : E3.IsFrostman delta 1 C :=
    hE3_frostman_raw.mono h_round_bound3

  have hF_strip : ∀ p ∈ E3, |inner ℝ p data.direction| ≤ data.width := by
    intro p hp
    have h5 : p ∈ data.selectedF := hE3_subset_F hp
    have h6 : p ∈ wz1LineNeighborhood 0 (wz1Perp2 data.direction) data.width :=
      data.orthogonal_strip p h5
    have h_perp2 : wz1Perp2 (wz1Perp2 data.direction) = -data.direction := by
      ext i; fin_cases i <;> simp [wz1Perp2] <;> decide
    simpa [wz1LineNeighborhood, h_perp2, abs_neg] using h6
  have hF_ball : E3.IsInUnitBall := by
    intro p hp
    exact data.selectedF_ball p (hE3_subset_F hp)
  have hphiF_bounded : ∀ p ∈ E3, dist (phiF p) 0 ≤ 2 :=
    wideCoarsePhiF_image_bounded hF_strip hF_ball

  rcases hRescaleBody delta data.width hdelta_pos hdelta_le_rescale
      data.delta_le_width data.width_le_one h_width_cond
      E3 hE3_nonempty C hC_ge_one hE3_separated hE3_frostman
      phiF hphiF_nonexp hphiF_bounded with
    ⟨thirdRescale⟩

  have hactive3 : ∀ vertex ∈ thirdRescale.selected,
      ∃ edge ∈ secondGraph, edge.1 = vertex := by
    intro vertex hvertex
    have h_in_E3 : vertex ∈ E3 := thirdRescale.selected_subset hvertex
    rcases Finset.mem_image.mp h_in_E3 with ⟨edge, hedge, heq⟩
    have hcoord : wz1TripleCoordinate edge 0 = edge.1 := by
      simp [wz1TripleCoordinate]
    rw [hcoord] at heq
    exact ⟨edge, hedge, heq⟩

  have hthirdSelected_subset_F : thirdRescale.selected ⊆ data.selectedF :=
    subset_trans thirdRescale.selected_subset hE3_subset_F

  rcases restrict_zeroth_vertex_and_refine secondUniform
      hthirdSelected_subset_F hactive3
      thirdRescale.selected_nonempty hRefine with
    ⟨sourceGraph, sourceGraph_subset, sourceGraph_nonempty, sourceUniform⟩

  -- Assemble output
  exact Nonempty.intro
    { firstRescale
    , firstGraph
    , firstGraph_subset
    , firstUniform
    , secondRescale
    , secondGraph
    , secondGraph_subset
    , secondUniform
    , thirdRescale
    , sourceGraph
    , sourceGraph_subset
    , sourceUniform }

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9CommonStripHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9TwoEndsPreparation
import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedRestriction
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionParameterTuning
import MyLeanRepo.Kakeya.Assouad.WZ1.RpowArithmeticHelpers
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# PDF Proposition 8.9: common strip from two-ends preparation

Apply Lemma 8.13 in both endpoint orders to the explicit two-ends preparation
and produce either a long projection or a common-strip configuration.
-/

namespace Kakeya.Assouad

open scoped ENNReal

theorem wz1_proposition8_9_common_strip_from_preparation :
    WZ1Proposition8_9CommonStripFromPreparationStatement := by
  intro hRefine hPrep
  intro epsilon parameters etaCap deltaCap
    hepsilon hepsilonOne hetaCap hdeltaCap
  classical
  let stripEps := parameters.stripEpsilon
  let stripEta := parameters.stripEta
  let stripD0 := parameters.stripDelta₀
  let wLambda := parameters.workingLambda
  let zeta := parameters.zeta

  have hstripEps_pos : 0 < stripEps := parameters.stripEpsilon_pos
  have hstripEps_lt_eps : stripEps < epsilon :=
    parameters.stripEpsilon_lt_epsilon
  have hstripEta_pos : 0 < stripEta := parameters.stripEta_pos
  have hstripD0_pos : 0 < stripD0 := parameters.stripDelta₀_pos
  have hstripD0_one : stripD0 ≤ 1 := parameters.stripDelta₀_le_one
  have hwLambda_pos : 0 < wLambda := parameters.workingLambda_pos
  have hzeta_pos : 0 < zeta := parameters.zeta_pos

  -- Step 1: Choose eta (stripEta/5 ensures 2*eta+zeta < stripEta for Frostman transfer)
  let eta := min (stripEta / 5) (min (wLambda / 4) etaCap)
  have heta_pos : 0 < eta := by
    dsimp only [eta]
    have h1 : 0 < stripEta / 5 := by linarith
    have h2 : 0 < min (wLambda / 4) etaCap := by
      exact lt_min (by linarith) hetaCap
    exact lt_min h1 h2
  have heta_le_etaCap : eta ≤ etaCap := by
    dsimp only [eta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have heta_lt_stripEta : eta < stripEta := by
    dsimp only [eta]
    have h : eta ≤ stripEta / 5 := min_le_left _ _
    linarith
  have heta_lt_wLambda4 : eta ≤ wLambda / 4 := by
    dsimp only [eta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have h2eta_zeta_lt_stripEta : 2 * eta + zeta < stripEta := by
    have h1 : 2 * eta ≤ 2 * stripEta / 5 := by
      dsimp only [eta]
      have h2 : eta ≤ stripEta / 5 := min_le_left _ _
      linarith
    have h3 : zeta ≤ stripEta / 2 := parameters.zeta_le_stripEta
    linarith
  have h2eta_zeta_nonneg : 0 ≤ 2 * eta + zeta := by positivity
  have h3eta_zeta_lt_wLambda : 3 * eta + zeta < wLambda := by
    have h1 : 3 * eta ≤ 3 * wLambda / 4 := by linarith [heta_lt_wLambda4]
    have h2 : zeta ≤ epsilon * wLambda / 30 :=
      parameters.zeta_le_epsilon_workingLambda
    have h3 : epsilon * wLambda / 30 < wLambda / 30 := by
      have h4 : epsilon < 1 := hepsilonOne
      have h5 : 0 < wLambda := hwLambda_pos
      nlinarith
    linarith
  have h3eta_zeta_nonneg : 0 ≤ 3 * eta + zeta := by positivity

  -- Step 1b: Choose delta₀
  rcases exists_delta₀_const_mul_rpow_le
      (256 : ℝ) (by norm_num) eta stripEta heta_lt_stripEta with
    ⟨deltaDensity, hdeltaDensity_pos, hdeltaDensity_one, hDensityCmp⟩
  rcases exists_scale_absorb_constant
      (4096 : ENNReal) (by norm_num)
      h3eta_zeta_nonneg h3eta_zeta_lt_wLambda with
    ⟨deltaFrostman, hdeltaFrostman_pos, hdeltaFrostman_one, hFrostmanCmp⟩
  -- For transferring Frostman to secondSelected: 16 * δ^{-(2*eta+zeta)} ≤ δ^{-stripEta}
  rcases exists_scale_absorb_constant
      (16 : ENNReal) (by norm_num)
      h2eta_zeta_nonneg h2eta_zeta_lt_stripEta with
    ⟨deltaFrostman2, hdeltaFrostman2_pos, hdeltaFrostman2_one, hFrostmanCmp2⟩
  let delta₀ := min stripD0 (min deltaCap (min 1 (min deltaDensity (min deltaFrostman deltaFrostman2))))
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le_deltaCap : delta₀ ≤ deltaCap := by
    dsimp only [delta₀]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    dsimp only [delta₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdelta₀_le_stripD0 : delta₀ ≤ stripD0 := by
    dsimp only [delta₀]
    exact min_le_left _ _
  have hdelta₀_le_density : delta₀ ≤ deltaDensity := by
    dsimp only [delta₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdelta₀_le_frostman : delta₀ ≤ deltaFrostman := by
    dsimp only [delta₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have hdelta₀_le_frostman2 : delta₀ ≤ deltaFrostman2 := by
    dsimp only [delta₀]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))

  refine ⟨eta, delta₀, heta_pos, heta_le_etaCap,
    hdelta₀_pos, hdelta₀_le_deltaCap, hdelta₀_le_one, ?_⟩

  intro delta hdelta hdelta₀ F G₁ G₂
    hF hG₁ hG₂ hFball hG₁ball hG₂ball
    hFsep hG₁sep hG₂sep hFfrost hG₁frost hG₂frost
    hstandard H hDensity

  have hdelta_one : delta ≤ 1 := hdelta₀.trans hdelta₀_le_one
  have hdelta_le_stripD0 : delta ≤ stripD0 :=
    hdelta₀.trans hdelta₀_le_stripD0
  have hDensityCmp' :
      (256 : ENNReal) * Kakeya.realRpowENN delta stripEta ≤
        Kakeya.realRpowENN delta eta := by
    have h := hDensityCmp delta hdelta (hdelta₀.trans hdelta₀_le_density)
    simpa [ENNReal.ofReal] using h
  have hFrostmanCmp' :
      (4096 : ENNReal) *
        Kakeya.realRpowENN delta (-(3 * eta + zeta)) ≤
      Kakeya.realRpowENN delta (-wLambda) :=
    hFrostmanCmp delta hdelta (hdelta₀.trans hdelta₀_le_frostman)

  have hFrostmanCmp2' :
      (16 : ENNReal) *
        Kakeya.realRpowENN delta (-(2 * eta + zeta)) ≤
      Kakeya.realRpowENN delta (-stripEta) :=
    hFrostmanCmp2 delta hdelta (hdelta₀.trans hdelta₀_le_frostman2)

  have hDensityWeak :
      Kakeya.realRpowENN delta stripEta ≤
        Kakeya.realRpowENN delta eta / 256 := by
    have h : (256 : ENNReal) * Kakeya.realRpowENN delta stripEta ≤
          Kakeya.realRpowENN delta eta := hDensityCmp'
    have hstripEta_pos' : 0 < Kakeya.realRpowENN delta stripEta := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_pos, Real.rpow_pos_of_pos hdelta]
    have h256_pos : (0 : ENNReal) < (256 : ENNReal) := by norm_num
    have h256_top : (256 : ENNReal) ≠ ⊤ := by norm_num
    have h3 : Kakeya.realRpowENN delta stripEta ≤
        Kakeya.realRpowENN delta eta / (256 : ENNReal) := by
      calc
        Kakeya.realRpowENN delta stripEta
          = (1 : ENNReal) * Kakeya.realRpowENN delta stripEta := by simp
        _ = ((256 : ENNReal)⁻¹ * (256 : ENNReal)) * Kakeya.realRpowENN delta stripEta := by
          rw [ENNReal.inv_mul_cancel h256_pos.ne' h256_top] <;> ring
        _ = (256 : ENNReal)⁻¹ * ((256 : ENNReal) * Kakeya.realRpowENN delta stripEta) := by ring
        _ ≤ (256 : ENNReal)⁻¹ * Kakeya.realRpowENN delta eta := by gcongr
        _ = Kakeya.realRpowENN delta eta / (256 : ENNReal) := by
          simp [div_eq_mul_inv] <;> ring
    exact h3

  have hFrostmanWeak :
      Kakeya.realRpowENN delta (-eta) ≤
        Kakeya.realRpowENN delta (-stripEta) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith

  -- Step 2: Two-ends preparation
  have hPrep' : Nonempty (WZ1Proposition8_9TwoEndsPreparationData
      delta eta zeta F G₁ G₂ H) :=
    hPrep hRefine hdelta hdelta_one heta_pos hzeta_pos
      F G₁ G₂ hF hG₁ hG₂ hFball hG₁ball hG₂ball
      hFsep hG₁sep hG₂sep hFfrost hG₁frost hG₂frost
      hstandard H hDensity
  rcases hPrep' with ⟨prep⟩

  let firstSelected := prep.firstSelected
  let secondSelected := prep.secondSelected
  let firstRefinedGraph := prep.firstRefinedGraph
  let refinedGraph := prep.refinedGraph
  let firstNormal := prep.firstNormal
  let firstLevel := prep.firstLevel
  let firstWidth := prep.firstWidth
  let secondNormal := prep.secondNormal
  let secondLevel := prep.secondLevel
  let secondWidth := prep.secondWidth

  have hfirstWidth_pos : 0 < firstWidth :=
    hdelta.trans_le prep.firstWidth_lower
  have hsecondWidth_pos : 0 < secondWidth :=
    hdelta.trans_le prep.secondWidth_lower

  -- Helper aliases using RpowArithmeticHelpers
  let h_rpow_div (a b : ℝ) := rpow_enn_div (hdelta := hdelta) (a := a) (b := b)
  let h_rpow_add (a b : ℝ) := rpow_enn_add (hdelta := hdelta) (a := a) (b := b)
  let h_rpow_inv (a : ℝ) := rpow_enn_inv (hdelta := hdelta) (a := a)

  -- Transfer Frostman from G₁ to firstSelected
  let ret1 := Kakeya.realRpowENN delta (eta + zeta)
  have hret1_pos : 0 < ret1 := by
    simp [ret1, Kakeya.realRpowENN, ENNReal.ofReal_pos, Real.rpow_pos_of_pos hdelta]
  have hret1_top : ret1 ≠ ⊤ := by simp [ret1, Kakeya.realRpowENN]
  have hfirstSelected_frostman0 :
      firstSelected.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta) / ret1) :=
    frostman_retained_subset hG₁frost
      prep.firstSelected_subset prep.firstSelected_retention hret1_pos hret1_top
  have hconst1 : Kakeya.realRpowENN delta (-eta) / ret1 =
      Kakeya.realRpowENN delta (-(2 * eta + zeta)) := by
    have hret1 : ret1 = Kakeya.realRpowENN delta (eta + zeta) := by rfl
    rw [hret1, h_rpow_div (-eta) (eta + zeta)]
    <;> ring
  have hfirstSelected_frostman :
      firstSelected.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-stripEta)) := by
    rw [hconst1] at hfirstSelected_frostman0
    have hweak : Kakeya.realRpowENN delta (-(2 * eta + zeta)) ≤
          Kakeya.realRpowENN delta (-stripEta) := by
      apply ENNReal.ofReal_mono
      apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
      linarith [h2eta_zeta_lt_stripEta]
    exact hfirstSelected_frostman0.mono hweak

  -- Transfer Frostman from G₂ to secondSelected
  let ret2 := (1 / 16 : ENNReal) * Kakeya.realRpowENN delta (eta + zeta)
  have hret2_pos : 0 < ret2 := by
    simp [ret2, Kakeya.realRpowENN, ENNReal.ofReal_pos, Real.rpow_pos_of_pos hdelta] <;> norm_num
  have hret2_top : ret2 ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · simp [Kakeya.realRpowENN]
  have hsecondSelected_frostman0 :
      secondSelected.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta) / ret2) :=
    frostman_retained_subset hG₂frost
      prep.secondSelected_subset prep.secondSelected_retention hret2_pos hret2_top
  have hconst2 : Kakeya.realRpowENN delta (-eta) / ret2 =
      (16 : ENNReal) * Kakeya.realRpowENN delta (-(2 * eta + zeta)) := by
    have hret2 : ret2 = (1 / 16 : ENNReal) * Kakeya.realRpowENN delta (eta + zeta) := by rfl
    rw [hret2]
    have hc_pos : (0 : ENNReal) < (1 / 16 : ENNReal) := by norm_num
    have hc_top : (1 / 16 : ENNReal) ≠ ⊤ := by simp
    have hdiv := rpow_enn_div_ennreal_scale hc_pos hc_top hdelta (a := -eta) (b := eta + zeta)
    have hcinv : (1 / 16 : ENNReal)⁻¹ = (16 : ENNReal) := by
      simp [one_div] <;> norm_num
    rw [hdiv, hcinv]
    have h_exp : (-eta) - (eta + zeta) = -(2 * eta + zeta) := by ring
    rw [h_exp]
  have hsecondSelected_frostman :
      secondSelected.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-stripEta)) := by
    rw [hconst2] at hsecondSelected_frostman0
    exact hsecondSelected_frostman0.mono hFrostmanCmp2'

  have hfirstStripConv :
      {point : Point2 |
        |inner ℝ point firstNormal - firstLevel| ≤ firstWidth} =
      wz1LineNeighborhood
        (firstLevel • firstNormal) (wz1Perp2 firstNormal) firstWidth :=
    wz1LineNeighborhood_eq_strip prep.firstNormal_unit

  -- Step 3: First strip application
  have hfirstDensity_lower2 :
      Kakeya.realRpowENN delta stripEta ≤ prep.firstDensity := by
    have h1 : prep.firstDensity ≥
        (1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta :=
      prep.firstDensity_lower
    have h2 : Kakeya.realRpowENN delta stripEta ≤
        (1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta := by
      have h3 : Kakeya.realRpowENN delta stripEta ≤
          Kakeya.realRpowENN delta eta / 256 := hDensityWeak
      have h4 : Kakeya.realRpowENN delta eta / 256 ≤
          (1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta := by
        have h5 : (1 / 256 : ENNReal) ≤ (1 / 16 : ENNReal) := by norm_num
        have h6 : Kakeya.realRpowENN delta eta / 256 =
            (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
          simp [div_eq_mul_inv, one_div] <;> ring
        rw [h6]
        gcongr
      exact h3.trans h4
    exact h2.trans h1
  let firstUniformWeak := prep.firstUniform.mono hfirstDensity_lower2

  have hFfrostWeak := hFfrost.mono hFrostmanWeak
  have hG₁frostWeak := hG₁frost.mono hFrostmanWeak
  have hG₂frostWeak := hG₂frost.mono hFrostmanWeak

  have hfirstSelectedStrip :
      ∀ point ∈ firstSelected,
        point ∈ wz1LineNeighborhood
          (firstLevel • firstNormal)
          (wz1Perp2 firstNormal) firstWidth := by
    intro point hpoint
    have h : |inner ℝ point firstNormal - firstLevel| ≤ firstWidth :=
      prep.firstSelected_strip point hpoint
    rw [← hfirstStripConv]
    exact h

  have hStrip1 := parameters.strip delta hdelta hdelta_le_stripD0
    F firstSelected G₂
    hF prep.firstSelected_nonempty hG₂
    hFball
    (fun p hp => hG₁ball p (prep.firstSelected_subset hp))
    hG₂ball
    hFsep
    (fun {x} hx {y} hy hne => hG₁sep (prep.firstSelected_subset hx) (prep.firstSelected_subset hy) hne)
    hG₂sep
    hFfrostWeak
    hfirstSelected_frostman
    hG₂frostWeak
    (hstandard.mono (F' := F) (G₁' := firstSelected) (G₂' := G₂)
      (by simp) prep.firstSelected_subset (by simp))
    firstRefinedGraph firstUniformWeak
    (firstLevel • firstNormal) (wz1Perp2 firstNormal)
    (by rw [wz1Perp2_norm firstNormal, prep.firstNormal_unit])
    firstWidth hfirstWidth_pos prep.firstWidth_lower
    hfirstSelectedStrip

  -- Step 4: Second strip application (swapped)
  have hstandardSwapped : WZ1StandardSeparation F G₂ G₁ := by
    rcases hstandard with ⟨hFdiam, hG₁diam, hG₂diam, hmutual, horigin⟩
    exact ⟨hFdiam, hG₂diam, hG₁diam,
      fun b hb a ha => by have h := hmutual a ha b hb; simpa [dist_comm] using h, horigin⟩
  let swappedGraph := refinedGraph.image wz1SwapTriple
  let swappedUniform := prep.uniform.swap
  have hswappedDensity_lower :
      Kakeya.realRpowENN delta stripEta ≤ prep.density := by
    have h2 : prep.firstDensity ≥
        (1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta :=
      prep.firstDensity_lower
    have h3 : prep.firstDensity / 16 ≥
        (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
      calc
        prep.firstDensity / 16
          ≥ ((1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta) / 16 := by gcongr
        _ = (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
          have h1 : ((1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta) / 16 =
              (1 / 16 : ENNReal) * (Kakeya.realRpowENN delta eta / 16) := by
            simp [div_eq_mul_inv, mul_assoc] <;> ring
          rw [h1]
          have h2 : Kakeya.realRpowENN delta eta / 16 =
              (1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta := by
            simp [div_eq_mul_inv, one_div] <;> ring
          rw [h2]
          have h3 : (1 / 16 : ENNReal) * (1 / 16 : ENNReal) = (1 / 256 : ENNReal) := by
            have h4 : (16 : ENNReal) * (16 : ENNReal) = (256 : ENNReal) := by norm_cast
            have h5 : (1 / 16 : ENNReal) = (16 : ENNReal)⁻¹ := by simp [one_div]
            simp only [h5]
            rw [← ENNReal.mul_inv (by simp) (by simp), h4]
            <;> simp [one_div]
          rw [← mul_assoc, h3]
    have h4 : Kakeya.realRpowENN delta stripEta ≤
        (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
      have h_conv : Kakeya.realRpowENN delta eta / 256 =
          (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
        simp [div_eq_mul_inv, one_div] <;> ring
      rw [h_conv] at hDensityWeak
      exact hDensityWeak
    exact h4.trans (h3.trans prep.density_lower)
  let swappedUniformWeak := swappedUniform.mono hswappedDensity_lower

  have hsecondStripConv :
      {point : Point2 |
        |inner ℝ point secondNormal - secondLevel| ≤ secondWidth} =
      wz1LineNeighborhood
        (secondLevel • secondNormal) (wz1Perp2 secondNormal) secondWidth :=
    wz1LineNeighborhood_eq_strip prep.secondNormal_unit

  have hsecondSelectedStrip :
      ∀ point ∈ secondSelected,
        point ∈ wz1LineNeighborhood
          (secondLevel • secondNormal)
          (wz1Perp2 secondNormal) secondWidth := by
    intro point hpoint
    have h : |inner ℝ point secondNormal - secondLevel| ≤ secondWidth :=
      prep.secondSelected_strip point hpoint
    rw [← hsecondStripConv]
    exact h

  have hStrip2 := parameters.strip delta hdelta hdelta_le_stripD0
    F secondSelected firstSelected
    hF prep.secondSelected_nonempty prep.firstSelected_nonempty
    hFball
    (fun p hp => hG₂ball p (prep.secondSelected_subset hp))
    (fun p hp => hG₁ball p (prep.firstSelected_subset hp))
    hFsep
    (fun {x} hx {y} hy hne => hG₂sep (prep.secondSelected_subset hx) (prep.secondSelected_subset hy) hne)
    (fun {x} hx {y} hy hne => hG₁sep (prep.firstSelected_subset hx) (prep.firstSelected_subset hy) hne)
    hFfrostWeak
    hsecondSelected_frostman
    hfirstSelected_frostman
    (hstandardSwapped.mono (F' := F) (G₁' := secondSelected) (G₂' := firstSelected)
      (by simp) prep.secondSelected_subset prep.firstSelected_subset)
    swappedGraph swappedUniformWeak
    (secondLevel • secondNormal) (wz1Perp2 secondNormal)
    (by rw [wz1Perp2_norm secondNormal, prep.secondNormal_unit])
    secondWidth hsecondWidth_pos prep.secondWidth_lower
    hsecondSelectedStrip

  -- Step 5: Active vertex classes
  let selectedF := wz1ActiveTripleProjection refinedGraph 0
  let selectedG₁ := wz1ActiveTripleProjection refinedGraph 1
  let selectedG₂ := wz1ActiveTripleProjection refinedGraph 2
  let refinedH := refinedGraph

  have hUniformActive :
      WZ1UniformTripleDensity prep.density
        selectedF selectedG₁ selectedG₂ refinedH :=
    uniform_density_on_active_projections prep.uniform

  have hden_exact : prep.density ≥
      (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
    have h2 : prep.firstDensity ≥
        (1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta :=
      prep.firstDensity_lower
    have h3 : prep.firstDensity / 16 ≥
        (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
      calc
        prep.firstDensity / 16
          ≥ ((1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta) / 16 := by gcongr
        _ = (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by
          have h1 : ((1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta) / 16 =
              (1 / 16 : ENNReal) * (Kakeya.realRpowENN delta eta / 16) := by
            simp [div_eq_mul_inv, mul_assoc] <;> ring
          rw [h1]
          have h2 : Kakeya.realRpowENN delta eta / 16 =
              (1 / 16 : ENNReal) * Kakeya.realRpowENN delta eta := by
            simp [div_eq_mul_inv, one_div] <;> ring
          rw [h2]
          have h3 : (1 / 16 : ENNReal) * (1 / 16 : ENNReal) = (1 / 256 : ENNReal) := by
            have h4 : (16 : ENNReal) * (16 : ENNReal) = (256 : ENNReal) := by norm_cast
            have h5 : (1 / 16 : ENNReal) = (16 : ENNReal)⁻¹ := by simp [one_div]
            simp only [h5]
            rw [← ENNReal.mul_inv (by simp) (by simp), h4]
            <;> simp [one_div]
          rw [← mul_assoc, h3]
    exact h3.trans prep.density_lower

  have hUniformExact :
      WZ1UniformTripleDensity
        ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta)
        selectedF selectedG₁ selectedG₂ refinedH :=
    hUniformActive.mono hden_exact

  have hselectedF_subset : selectedF ⊆ F :=
    active_triple_projection_subset prep.uniform 0
  have hselectedG₁_subset_first : selectedG₁ ⊆ firstSelected :=
    active_triple_projection_subset prep.uniform 1
  have hselectedG₂_subset_second : selectedG₂ ⊆ secondSelected :=
    active_triple_projection_subset prep.uniform 2
  have hselectedG₁_subset : selectedG₁ ⊆ G₁ :=
    hselectedG₁_subset_first.trans prep.firstSelected_subset
  have hselectedG₂_subset : selectedG₂ ⊆ G₂ :=
    hselectedG₂_subset_second.trans prep.secondSelected_subset

  have hselectedF_nonempty : selectedF.Nonempty :=
    active_triple_projection_nonempty prep.uniform 0
  have hselectedG₁_nonempty : selectedG₁.Nonempty :=
    active_triple_projection_nonempty prep.uniform 1
  have hselectedG₂_nonempty : selectedG₂.Nonempty :=
    active_triple_projection_nonempty prep.uniform 2

  have hcardF : prep.density * F.enncard ≤ selectedF.enncard :=
    active_triple_projection_card_lower prep.uniform 0
  have hcardG₁ : prep.density * firstSelected.enncard ≤ selectedG₁.enncard :=
    active_triple_projection_card_lower prep.uniform 1
  have hcardG₂ : prep.density * secondSelected.enncard ≤ selectedG₂.enncard :=
    active_triple_projection_card_lower prep.uniform 2

  let retentionF : ENNReal :=
    (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta
  have hretF : retentionF * F.enncard ≤ selectedF.enncard :=
    (mul_le_mul_right' hden_exact F.enncard).trans hcardF
  have hretF_pos : 0 < retentionF := by
    simp [retentionF, Kakeya.realRpowENN, ENNReal.ofReal_pos,
      Real.rpow_pos_of_pos hdelta] <;> norm_num
  have hretF_top : retentionF ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · simp [Kakeya.realRpowENN]
  have hretG₁ : retentionF * firstSelected.enncard ≤ selectedG₁.enncard :=
    (mul_le_mul_right' hden_exact firstSelected.enncard).trans hcardG₁
  have hretG₂ : retentionF * secondSelected.enncard ≤ selectedG₂.enncard :=
    (mul_le_mul_right' hden_exact secondSelected.enncard).trans hcardG₂

  -- Handle strip results
  rcases hStrip1 with (hStrip1Narrow | hLP1)
  · rcases hStrip2 with (hStrip2Narrow | hLP2)
    · -- Both narrow: construct common strip data
      let narrowWidth₁ := Real.rpow delta (-stripEps) * firstWidth
      let narrowWidth₂ := Real.rpow delta (-stripEps) * secondWidth
      have hnarrow₁_pos : 0 < narrowWidth₁ := by
        dsimp only [narrowWidth₁]
        have h1 : 0 < Real.rpow delta (-stripEps) := Real.rpow_pos_of_pos hdelta _
        exact mul_pos h1 hfirstWidth_pos
      have hnarrow₂_pos : 0 < narrowWidth₂ := by
        dsimp only [narrowWidth₂]
        have h1 : 0 < Real.rpow delta (-stripEps) := Real.rpow_pos_of_pos hdelta _
        exact mul_pos h1 hsecondWidth_pos

      -- selectedG₂ in narrow strip 1
      have hG₂_narrow :
          ∀ point ∈ selectedG₂,
            point ∈ wz1LineNeighborhood
              (firstLevel • firstNormal)
              (wz1Perp2 firstNormal) narrowWidth₁ := by
        intro point hpoint
        rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
        exact hStrip1Narrow.1 edge (prep.refinedGraph_subset hedge)

      -- selectedF in orthogonal strip 1
      have hF_narrow1 :
          ∀ point ∈ selectedF,
            point ∈ wz1LineNeighborhood 0
              (wz1Perp2 (wz1Perp2 firstNormal)) narrowWidth₁ := by
        intro point hpoint
        rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
        exact hStrip1Narrow.2 edge (prep.refinedGraph_subset hedge)

      -- selectedG₁ in narrow strip 2
      have hG₁_narrow :
          ∀ point ∈ selectedG₁,
            point ∈ wz1LineNeighborhood
              (secondLevel • secondNormal)
              (wz1Perp2 secondNormal) narrowWidth₂ := by
        intro point hpoint
        rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, h_eq_point⟩
        let swappedEdge := wz1SwapTriple edge
        have hswapped : swappedEdge ∈ swappedGraph :=
          Finset.mem_image_of_mem _ hedge
        have h := hStrip2Narrow.1 swappedEdge hswapped
        have h_swap_eq : swappedEdge.2.2 = edge.2.1 := by
          simp [swappedEdge, wz1SwapTriple]
        have h_final : swappedEdge.2.2 = point := by
          exact h_swap_eq.trans h_eq_point
        rwa [h_final] at h

      -- selectedG₁ in raw strip 1
      have hG₁_raw :
          ∀ point ∈ selectedG₁,
            point ∈ wz1LineNeighborhood
              (firstLevel • firstNormal)
              (wz1Perp2 firstNormal) firstWidth := by
        intro point hpoint
        exact hfirstSelectedStrip point (hselectedG₁_subset_first hpoint)

      -- selectedG₂ in raw strip 2
      have hG₂_raw :
          ∀ point ∈ selectedG₂,
            point ∈ wz1LineNeighborhood
              (secondLevel • secondNormal)
              (wz1Perp2 secondNormal) secondWidth := by
        intro point hpoint
        exact hsecondSelectedStrip point (hselectedG₂_subset_second hpoint)

      -- Frostman estimates (common to all width cases)
      let fG₁ : ENNReal :=
        Kakeya.realRpowENN delta (eta + zeta) * retentionF
      have hfG₁ : fG₁ * G₁.enncard ≤ selectedG₁.enncard := by
        dsimp only [fG₁]
        calc
          (Kakeya.realRpowENN delta (eta + zeta) * retentionF) * G₁.enncard
            = retentionF * (Kakeya.realRpowENN delta (eta + zeta) * G₁.enncard) := by ring
          _ ≤ retentionF * firstSelected.enncard := by gcongr; exact prep.firstSelected_retention
          _ ≤ selectedG₁.enncard := hretG₁
      have hfG₁_pos : 0 < fG₁ := by
        simp [fG₁, retentionF, Kakeya.realRpowENN, ENNReal.ofReal_pos,
          Real.rpow_pos_of_pos hdelta] <;> norm_num
      have hfG₁_top : fG₁ ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · simp [Kakeya.realRpowENN]
        · apply ENNReal.mul_ne_top <;> simp [Kakeya.realRpowENN]

      let fG₂ : ENNReal :=
        (1 / 16 : ENNReal) * Kakeya.realRpowENN delta (eta + zeta) * retentionF
      have hfG₂ : fG₂ * G₂.enncard ≤ selectedG₂.enncard := by
        dsimp only [fG₂]
        calc
          (((1 / 16 : ENNReal) * Kakeya.realRpowENN delta (eta + zeta)) * retentionF) * G₂.enncard
            = retentionF * (((1 / 16 : ENNReal) * Kakeya.realRpowENN delta (eta + zeta)) * G₂.enncard) := by ring
          _ ≤ retentionF * secondSelected.enncard := by gcongr; exact prep.secondSelected_retention
          _ ≤ selectedG₂.enncard := hretG₂
      have hfG₂_pos : 0 < fG₂ := by
        simp [fG₂, retentionF, Kakeya.realRpowENN, ENNReal.ofReal_pos,
          Real.rpow_pos_of_pos hdelta] <;> norm_num
      have hfG₂_top : fG₂ ≠ ⊤ := by
        dsimp only [fG₂]
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top <;> simp [Kakeya.realRpowENN]
        · exact hretF_top

      have hselectedG₁_frostman :
          selectedG₁.IsFrostman delta 1
            ((256 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta))) := by
        have h0 := frostman_retained_subset hG₁frost
          hselectedG₁_subset hfG₁ hfG₁_pos hfG₁_top
        have hc : Kakeya.realRpowENN delta (-eta) / fG₁ =
              (256 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta)) := by
          have h_fG₁ : fG₁ = (1 / 256 : ENNReal) * Kakeya.realRpowENN delta (2 * eta + zeta) := by
            dsimp only [fG₁, retentionF]
            have h_add : Kakeya.realRpowENN delta (2 * eta + zeta) =
                Kakeya.realRpowENN delta (eta + zeta) * Kakeya.realRpowENN delta eta := by
              rw [show (2 * eta + zeta) = (eta + zeta) + eta by ring]
              exact h_rpow_add (eta + zeta) eta
            calc
              Kakeya.realRpowENN delta (eta + zeta) * retentionF
                = Kakeya.realRpowENN delta (eta + zeta) * ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta) := by rfl
              _ = (1 / 256 : ENNReal) * (Kakeya.realRpowENN delta (eta + zeta) * Kakeya.realRpowENN delta eta) := by
                simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
              _ = (1 / 256 : ENNReal) * Kakeya.realRpowENN delta (2 * eta + zeta) := by
                rw [h_add.symm]
          rw [h_fG₁]
          have hc_pos : (0 : ENNReal) < (1 / 256 : ENNReal) := by norm_num
          have hc_top : (1 / 256 : ENNReal) ≠ ⊤ := by simp
          have hdiv := rpow_enn_div_ennreal_scale hc_pos hc_top hdelta (a := -eta) (b := 2 * eta + zeta)
          have hcinv : (1 / 256 : ENNReal)⁻¹ = (256 : ENNReal) := by
            simp [one_div] <;> norm_num
          rw [hdiv, hcinv]
          have h_exp2 : (-eta) - (2 * eta + zeta) = -(3 * eta + zeta) := by ring
          rw [h_exp2]
        rw [hc] at h0
        exact h0

      have hselectedG₁_frostman' :
          selectedG₁.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-wLambda)) := by
        have h : (256 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta)) ≤
              Kakeya.realRpowENN delta (-wLambda) := by
          have h2 : (256 : ENNReal) ≤ (4096 : ENNReal) := by norm_num
          have h3 : (256 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta)) ≤
              (4096 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta)) := by gcongr
          exact h3.trans hFrostmanCmp'
        exact hselectedG₁_frostman.mono h

      have hselectedG₂_frostman :
          selectedG₂.IsFrostman delta 1
            ((4096 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta))) := by
        have h0 := frostman_retained_subset hG₂frost
          hselectedG₂_subset hfG₂ hfG₂_pos hfG₂_top
        have hc : Kakeya.realRpowENN delta (-eta) / fG₂ =
              (4096 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta)) := by
          have h_fG₂ : fG₂ = (1 / 4096 : ENNReal) * Kakeya.realRpowENN delta (2 * eta + zeta) := by
            dsimp only [fG₂, retentionF]
            have h_add : Kakeya.realRpowENN delta (2 * eta + zeta) =
                Kakeya.realRpowENN delta (eta + zeta) * Kakeya.realRpowENN delta eta := by
              rw [show (2 * eta + zeta) = (eta + zeta) + eta by ring]
              exact h_rpow_add (eta + zeta) eta
            have h_mul : (1 / 16 : ENNReal) * (1 / 256 : ENNReal) = (1 / 4096 : ENNReal) := by
              have h4 : (16 : ENNReal) * (256 : ENNReal) = (4096 : ENNReal) := by norm_cast
              have h5 : (1 / 16 : ENNReal) = (16 : ENNReal)⁻¹ := by simp [one_div]
              have h6 : (1 / 256 : ENNReal) = (256 : ENNReal)⁻¹ := by simp [one_div]
              rw [h5, h6]
              rw [← ENNReal.mul_inv (by simp) (by simp), h4]
              <;> simp [one_div]
            calc
              ((1 / 16 : ENNReal) * Kakeya.realRpowENN delta (eta + zeta)) * retentionF
                = (1 / 16 : ENNReal) * (Kakeya.realRpowENN delta (eta + zeta) * retentionF) := by ring
              _ = (1 / 16 : ENNReal) * ((1 / 256 : ENNReal) * (Kakeya.realRpowENN delta (eta + zeta) * Kakeya.realRpowENN delta eta)) := by
                dsimp only [retentionF]
                simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
              _ = (1 / 16 : ENNReal) * ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta (2 * eta + zeta)) := by
                rw [h_add.symm]
              _ = (1 / 4096 : ENNReal) * Kakeya.realRpowENN delta (2 * eta + zeta) := by
                rw [← mul_assoc, h_mul]
          rw [h_fG₂]
          have hc_pos : (0 : ENNReal) < (1 / 4096 : ENNReal) := by norm_num
          have hc_top : (1 / 4096 : ENNReal) ≠ ⊤ := by simp
          have hdiv := rpow_enn_div_ennreal_scale hc_pos hc_top hdelta (a := -eta) (b := 2 * eta + zeta)
          have hcinv : (1 / 4096 : ENNReal)⁻¹ = (4096 : ENNReal) := by
            simp [one_div] <;> norm_num
          rw [hdiv, hcinv]
          have h_exp2 : (-eta) - (2 * eta + zeta) = -(3 * eta + zeta) := by ring
          rw [h_exp2]
        rw [hc] at h0
        exact h0

      have hselectedG₂_frostman' :
          selectedG₂.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-wLambda)) :=
        hselectedG₂_frostman.mono hFrostmanCmp'

      have hselectedF_frostman :
          selectedF.IsFrostman delta 1
            ((256 : ENNReal) * Kakeya.realRpowENN delta (-2 * eta)) := by
        have h0 := frostman_retained_subset hFfrost
          hselectedF_subset hretF hretF_pos hretF_top
        have hc : Kakeya.realRpowENN delta (-eta) / retentionF =
              (256 : ENNReal) * Kakeya.realRpowENN delta (-2 * eta) := by
          have h_retF : retentionF = (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta := by rfl
          rw [h_retF]
          have hc_pos : (0 : ENNReal) < (1 / 256 : ENNReal) := by norm_num
          have hc_top : (1 / 256 : ENNReal) ≠ ⊤ := by simp
          have hdiv := rpow_enn_div_ennreal_scale hc_pos hc_top hdelta (a := -eta) (b := eta)
          have hcinv : (1 / 256 : ENNReal)⁻¹ = (256 : ENNReal) := by
            simp [one_div] <;> norm_num
          rw [hdiv, hcinv]
          have h_exp : (-eta) - eta = -2 * eta := by ring
          rw [h_exp]
        rw [hc] at h0
        exact h0

      have hFrostmanF :
          (256 : ENNReal) * Kakeya.realRpowENN delta (-2 * eta) ≤
          Kakeya.realRpowENN delta (-wLambda) := by
        have h1 : (256 : ENNReal) * Kakeya.realRpowENN delta (-2 * eta) ≤
            (4096 : ENNReal) * Kakeya.realRpowENN delta (-(3 * eta + zeta)) := by
          have h2 : Kakeya.realRpowENN delta (-2 * eta) ≤
              Kakeya.realRpowENN delta (-(3 * eta + zeta)) := by
            apply ENNReal.ofReal_mono
            apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
            linarith
          gcongr <;> norm_num
        exact h1.trans hFrostmanCmp'

      have hselectedF_frostman' :
          selectedF.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-wLambda)) :=
        hselectedF_frostman.mono hFrostmanF

      -- Raw nonconcentration via transfer_subset
      let nonconcConst : ENNReal :=
        (256 : ENNReal) * Kakeya.realRpowENN delta (-eta)
      have hretG₁' : firstSelected.enncard ≤ nonconcConst * selectedG₁.enncard := by
        have h : retentionF * firstSelected.enncard ≤ selectedG₁.enncard := hretG₁
        have h2 : firstSelected.enncard ≤ (retentionF⁻¹) * selectedG₁.enncard := by
          have h3 : retentionF⁻¹ * (retentionF * firstSelected.enncard) ≤ retentionF⁻¹ * selectedG₁.enncard := by gcongr
          have h4 : retentionF⁻¹ * retentionF = 1 :=
            ENNReal.inv_mul_cancel hretF_pos.ne' hretF_top
          have h5 : retentionF⁻¹ * (retentionF * firstSelected.enncard) = firstSelected.enncard := by
            rw [← mul_assoc, h4, one_mul]
          rw [h5] at h3
          exact h3
        have h6 : retentionF⁻¹ = nonconcConst := by
          dsimp only [retentionF, nonconcConst]
          have h1 : ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta)⁻¹ =
              (1 / 256 : ENNReal)⁻¹ * (Kakeya.realRpowENN delta eta)⁻¹ := by
            rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          rw [h1]
          have h2 : (1 / 256 : ENNReal)⁻¹ = (256 : ENNReal) := by
            simp [one_div] <;> norm_num
          rw [h2, h_rpow_inv eta] <;> ring
        rw [h6] at h2
        exact h2

      have hfirstNonconcFinal :
          WZ1WeightedRawStripNonconcentration
            delta zeta firstWidth nonconcConst selectedG₁ :=
        prep.firstRawNonconcentration.transfer_subset
          hselectedG₁_subset_first hretG₁'

      have hretG₂' : secondSelected.enncard ≤ nonconcConst * selectedG₂.enncard := by
        have h : retentionF * secondSelected.enncard ≤ selectedG₂.enncard := hretG₂
        have h2 : secondSelected.enncard ≤ (retentionF⁻¹) * selectedG₂.enncard := by
          have h3 : retentionF⁻¹ * (retentionF * secondSelected.enncard) ≤ retentionF⁻¹ * selectedG₂.enncard := by gcongr
          have h4 : retentionF⁻¹ * retentionF = 1 :=
            ENNReal.inv_mul_cancel hretF_pos.ne' hretF_top
          have h5 : retentionF⁻¹ * (retentionF * secondSelected.enncard) = secondSelected.enncard := by
            rw [← mul_assoc, h4, one_mul]
          rw [h5] at h3
          exact h3
        have h6 : retentionF⁻¹ = nonconcConst := by
          dsimp only [retentionF, nonconcConst]
          have h1 : ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta)⁻¹ =
              (1 / 256 : ENNReal)⁻¹ * (Kakeya.realRpowENN delta eta)⁻¹ := by
            rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          rw [h1]
          have h2 : (1 / 256 : ENNReal)⁻¹ = (256 : ENNReal) := by
            simp [one_div] <;> norm_num
          rw [h2, h_rpow_inv eta] <;> ring
        rw [h6] at h2
        exact h2

      have hsecondNonconcFinal :
          WZ1WeightedRawStripNonconcentration
            delta zeta secondWidth nonconcConst selectedG₂ :=
        prep.secondRawNonconcentration.transfer_subset
          hselectedG₂_subset_second hretG₂'

      -- Standard separation, ball, separated
      have hstandard' : WZ1StandardSeparation selectedF selectedG₁ selectedG₂ :=
        hstandard.mono hselectedF_subset hselectedG₁_subset hselectedG₂_subset
      have hselectedF_ball : selectedF.IsInUnitBall :=
        fun p hp => hFball p (hselectedF_subset hp)
      have hselectedG₁_ball : selectedG₁.IsInUnitBall :=
        fun p hp => hG₁ball p (hselectedG₁_subset hp)
      have hselectedG₂_ball : selectedG₂.IsInUnitBall :=
        fun p hp => hG₂ball p (hselectedG₂_subset hp)
      have hselectedF_sep : selectedF.IsDeltaSeparated delta :=
        fun {p} hp {q} hq hne => hFsep (hselectedF_subset hp) (hselectedF_subset hq) hne
      have hselectedG₁_sep : selectedG₁.IsDeltaSeparated delta :=
        fun {p} hp {q} hq hne => hG₁sep (hselectedG₁_subset hp) (hselectedG₁_subset hq) hne
      have hselectedG₂_sep : selectedG₂.IsDeltaSeparated delta :=
        fun {p} hp {q} hq hne => hG₂sep (hselectedG₂_subset hp) (hselectedG₂_subset hq) hne

      have hfirstRawStrip :
          ∀ point ∈ selectedG₁,
            |inner ℝ point firstNormal - firstLevel| ≤ firstWidth := by
        intro point hpoint
        exact prep.firstSelected_strip point (hselectedG₁_subset_first hpoint)
      have hsecondRawStrip :
          ∀ point ∈ selectedG₂,
            |inner ℝ point secondNormal - secondLevel| ≤ secondWidth := by
        intro point hpoint
        exact prep.secondSelected_strip point (hselectedG₂_subset_second hpoint)

      have hrefinedH_subset : refinedH ⊆ H :=
        prep.refinedGraph_subset.trans prep.firstRefinedGraph_subset

      -- Width trichotomy
      by_cases hboth : narrowWidth₁ > 1 ∧ narrowWidth₂ > 1
      · -- Case A: both narrow widths > 1, use width=1, base=0
        let direction : Point2 := EuclideanSpace.single 0 1
        have hdir_unit : ‖direction‖ = 1 := by simp [direction] <;> norm_num
        let width : ℝ := 1
        have hwidth_pos : 0 < width := by norm_num
        have hdelta_le_width : delta ≤ width := hdelta_one
        have hwidth_le_one : width ≤ 1 := by norm_num
        have hwidth_le_first : width ≤ narrowWidth₁ := by linarith
        have hwidth_le_second : width ≤ narrowWidth₂ := by linarith

        have hball_strip : ∀ (s : DiscreteSet 2), (∀ p ∈ s, ‖p‖ ≤ 1) →
            ∀ p ∈ s, p ∈ wz1LineNeighborhood (0 : Point2) direction width := by
          intro s hs p hp
          have hnorm : ‖p‖ ≤ 1 := hs p hp
          have h : |inner ℝ p (wz1Perp2 direction)| ≤ ‖p‖ * ‖wz1Perp2 direction‖ :=
            abs_real_inner_le_norm p (wz1Perp2 direction)
          have hperp : ‖wz1Perp2 direction‖ = 1 := by
            rw [wz1Perp2_norm direction, hdir_unit]
          rw [hperp] at h
          have h' : |inner ℝ p (wz1Perp2 direction)| ≤ 1 := by linarith
          simpa [wz1LineNeighborhood, width] using h'

        have horth_strip : ∀ (s : DiscreteSet 2), (∀ p ∈ s, ‖p‖ ≤ 1) →
            ∀ p ∈ s, p ∈ wz1LineNeighborhood (0 : Point2) (wz1Perp2 direction) width := by
          intro s hs p hp
          have hnorm : ‖p‖ ≤ 1 := hs p hp
          have h : |inner ℝ p (wz1Perp2 (wz1Perp2 direction))| ≤ ‖p‖ * ‖wz1Perp2 (wz1Perp2 direction)‖ :=
            abs_real_inner_le_norm p (wz1Perp2 (wz1Perp2 direction))
          have hperp : ‖wz1Perp2 (wz1Perp2 direction)‖ = 1 := by
            rw [wz1Perp2_norm (wz1Perp2 direction), wz1Perp2_norm direction, hdir_unit]
          rw [hperp] at h
          have h' : |inner ℝ p (wz1Perp2 (wz1Perp2 direction))| ≤ 1 := by linarith
          simpa [wz1LineNeighborhood, width] using h'

        have hG₁ball' : ∀ p ∈ selectedG₁, ‖p‖ ≤ 1 :=
          fun p hp => by simpa [dist_zero_right] using hG₁ball p (hselectedG₁_subset hp)
        have hG₂ball' : ∀ p ∈ selectedG₂, ‖p‖ ≤ 1 :=
          fun p hp => by simpa [dist_zero_right] using hG₂ball p (hselectedG₂_subset hp)
        have hFball' : ∀ p ∈ selectedF, ‖p‖ ≤ 1 :=
          fun p hp => by simpa [dist_zero_right] using hFball p (hselectedF_subset hp)

        exact Or.inr ⟨{
          selectedF := selectedF, selectedG₁ := selectedG₁,
          selectedG₂ := selectedG₂, refinedH := refinedH,
          selectedF_subset := hselectedF_subset,
          selectedG₁_subset := hselectedG₁_subset,
          selectedG₂_subset := hselectedG₂_subset,
          refinedH_subset := hrefinedH_subset,
          selectedF_nonempty := hselectedF_nonempty,
          selectedG₁_nonempty := hselectedG₁_nonempty,
          selectedG₂_nonempty := hselectedG₂_nonempty,
          selectedF_ball := hselectedF_ball,
          selectedG₁_ball := hselectedG₁_ball,
          selectedG₂_ball := hselectedG₂_ball,
          selectedF_separated := hselectedF_sep,
          selectedG₁_separated := hselectedG₁_sep,
          selectedG₂_separated := hselectedG₂_sep,
          selectedF_frostman := hselectedF_frostman',
          selectedG₁_frostman := hselectedG₁_frostman',
          selectedG₂_frostman := hselectedG₂_frostman',
          firstRawNormal := firstNormal, firstRawLevel := firstLevel,
          firstRawWidth := firstWidth,
          firstRawNormal_unit := prep.firstNormal_unit,
          firstRawWidth_pos := hfirstWidth_pos,
          first_raw_strip := hfirstRawStrip,
          secondRawNormal := secondNormal, secondRawLevel := secondLevel,
          secondRawWidth := secondWidth,
          secondRawNormal_unit := prep.secondNormal_unit,
          secondRawWidth_pos := hsecondWidth_pos,
          second_raw_strip := hsecondRawStrip,
          first_raw_nonconcentration := hfirstNonconcFinal,
          second_raw_nonconcentration := hsecondNonconcFinal,
          standardSeparation := hstandard',
          uniform := hUniformExact,
          base := 0, direction := direction,
          direction_unit := hdir_unit,
          width := width, width_pos := hwidth_pos,
          delta_le_width := hdelta_le_width,
          width_le_one := hwidth_le_one,
          width_le_first_raw := hwidth_le_first,
          width_le_second_raw := hwidth_le_second,
          first_strip := hball_strip selectedG₁ hG₁ball',
          second_strip := hball_strip selectedG₂ hG₂ball',
          orthogonal_strip := horth_strip selectedF hFball'
        }⟩

      · -- Case B/C: at least one narrow width ≤ 1
        have hnotboth : ¬(narrowWidth₁ > 1 ∧ narrowWidth₂ > 1) := hboth
        by_cases horder : firstWidth ≤ secondWidth
        · -- firstWidth ≤ secondWidth, so narrowWidth₁ ≤ narrowWidth₂
          have hnw_le : narrowWidth₁ ≤ narrowWidth₂ := by
            dsimp only [narrowWidth₁, narrowWidth₂]
            have h_pos : 0 < Real.rpow delta (-stripEps) := Real.rpow_pos_of_pos hdelta _
            exact mul_le_mul_of_nonneg_left horder h_pos.le
          have hnw₁_le_one : narrowWidth₁ ≤ 1 := by
            by_contra h
            have h' : narrowWidth₁ > 1 := by linarith
            have h'' : narrowWidth₂ > 1 := by linarith
            exact hnotboth ⟨h', h''⟩
          let direction := wz1Perp2 firstNormal
          let base := firstLevel • firstNormal
          let width := narrowWidth₁
          have hdir_unit : ‖direction‖ = 1 := by
            rw [wz1Perp2_norm firstNormal, prep.firstNormal_unit]
          have hwidth_pos : 0 < width := hnarrow₁_pos
          have hdelta_le_width : delta ≤ width := by
            dsimp only [width, narrowWidth₁]
            have h1 : delta ≤ firstWidth := prep.firstWidth_lower
            have h2 : 1 ≤ Real.rpow delta (-stripEps) := by
              apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one
              linarith
            calc delta ≤ firstWidth := h1
              _ = 1 * firstWidth := by ring
              _ ≤ Real.rpow delta (-stripEps) * firstWidth := by gcongr
          have hwidth_le_one : width ≤ 1 := hnw₁_le_one
          have hwidth_le_first : width ≤ narrowWidth₁ := by rfl
          have hwidth_le_second : width ≤ narrowWidth₂ := hnw_le

          have hG₁_strip : ∀ point ∈ selectedG₁,
              point ∈ wz1LineNeighborhood base direction width := by
            intro point hpoint
            have h := hG₁_raw point hpoint
            have hw : firstWidth ≤ width := by
              dsimp only [width, narrowWidth₁]
              have h2 : 1 ≤ Real.rpow delta (-stripEps) := by
                apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one
                linarith
              calc firstWidth = 1 * firstWidth := by ring
                _ ≤ Real.rpow delta (-stripEps) * firstWidth := by gcongr
            have hmono : wz1LineNeighborhood base direction firstWidth ⊆
                wz1LineNeighborhood base direction width := by
              intro x hx
              simp only [wz1LineNeighborhood, Set.mem_setOf_eq] at hx ⊢
              linarith
            exact hmono h

          have hG₂_strip : ∀ point ∈ selectedG₂,
              point ∈ wz1LineNeighborhood base direction width :=
            hG₂_narrow

          have hF_strip : ∀ point ∈ selectedF,
              point ∈ wz1LineNeighborhood 0 (wz1Perp2 direction) width :=
            hF_narrow1

          exact Or.inr ⟨{
            selectedF := selectedF, selectedG₁ := selectedG₁,
            selectedG₂ := selectedG₂, refinedH := refinedH,
            selectedF_subset := hselectedF_subset,
            selectedG₁_subset := hselectedG₁_subset,
            selectedG₂_subset := hselectedG₂_subset,
            refinedH_subset := hrefinedH_subset,
            selectedF_nonempty := hselectedF_nonempty,
            selectedG₁_nonempty := hselectedG₁_nonempty,
            selectedG₂_nonempty := hselectedG₂_nonempty,
            selectedF_ball := hselectedF_ball,
            selectedG₁_ball := hselectedG₁_ball,
            selectedG₂_ball := hselectedG₂_ball,
            selectedF_separated := hselectedF_sep,
            selectedG₁_separated := hselectedG₁_sep,
            selectedG₂_separated := hselectedG₂_sep,
            selectedF_frostman := hselectedF_frostman',
            selectedG₁_frostman := hselectedG₁_frostman',
            selectedG₂_frostman := hselectedG₂_frostman',
            firstRawNormal := firstNormal, firstRawLevel := firstLevel,
            firstRawWidth := firstWidth,
            firstRawNormal_unit := prep.firstNormal_unit,
            firstRawWidth_pos := hfirstWidth_pos,
            first_raw_strip := hfirstRawStrip,
            secondRawNormal := secondNormal, secondRawLevel := secondLevel,
            secondRawWidth := secondWidth,
            secondRawNormal_unit := prep.secondNormal_unit,
            secondRawWidth_pos := hsecondWidth_pos,
            second_raw_strip := hsecondRawStrip,
            first_raw_nonconcentration := hfirstNonconcFinal,
            second_raw_nonconcentration := hsecondNonconcFinal,
            standardSeparation := hstandard',
            uniform := hUniformExact,
            base := base, direction := direction,
            direction_unit := hdir_unit,
            width := width, width_pos := hwidth_pos,
            delta_le_width := hdelta_le_width,
            width_le_one := hwidth_le_one,
            width_le_first_raw := hwidth_le_first,
            width_le_second_raw := hwidth_le_second,
            first_strip := hG₁_strip,
            second_strip := hG₂_strip,
            orthogonal_strip := hF_strip
          }⟩

        · -- secondWidth < firstWidth, so narrowWidth₂ < narrowWidth₁
          have horder' : secondWidth < firstWidth := by linarith
          have hnw_lt : narrowWidth₂ < narrowWidth₁ := by
            dsimp only [narrowWidth₁, narrowWidth₂]
            have h_pos : 0 < Real.rpow delta (-stripEps) := Real.rpow_pos_of_pos hdelta _
            exact mul_lt_mul_of_pos_left horder' h_pos
          have hnw₂_le_one : narrowWidth₂ ≤ 1 := by
            by_contra h
            have h' : narrowWidth₂ > 1 := by linarith
            have h'' : narrowWidth₁ > 1 := by linarith
            exact hnotboth ⟨h'', h'⟩
          let direction := wz1Perp2 secondNormal
          let base := secondLevel • secondNormal
          let width := narrowWidth₂
          have hdir_unit : ‖direction‖ = 1 := by
            rw [wz1Perp2_norm secondNormal, prep.secondNormal_unit]
          have hwidth_pos : 0 < width := hnarrow₂_pos
          have hdelta_le_width : delta ≤ width := by
            dsimp only [width, narrowWidth₂]
            have h1 : delta ≤ secondWidth := prep.secondWidth_lower
            have h2 : 1 ≤ Real.rpow delta (-stripEps) := by
              apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one
              linarith
            calc delta ≤ secondWidth := h1
              _ = 1 * secondWidth := by ring
              _ ≤ Real.rpow delta (-stripEps) * secondWidth := by gcongr
          have hwidth_le_one : width ≤ 1 := hnw₂_le_one
          have hwidth_le_first : width ≤ narrowWidth₁ := by linarith
          have hwidth_le_second : width ≤ narrowWidth₂ := by rfl

          have hG₂_strip : ∀ point ∈ selectedG₂,
              point ∈ wz1LineNeighborhood base direction width := by
            intro point hpoint
            have h := hG₂_raw point hpoint
            have hw : secondWidth ≤ width := by
              dsimp only [width, narrowWidth₂]
              have h2 : 1 ≤ Real.rpow delta (-stripEps) := by
                apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one
                linarith
              calc secondWidth = 1 * secondWidth := by ring
                _ ≤ Real.rpow delta (-stripEps) * secondWidth := by gcongr
            have hmono : wz1LineNeighborhood base direction secondWidth ⊆
                wz1LineNeighborhood base direction width := by
              intro x hx
              simp only [wz1LineNeighborhood, Set.mem_setOf_eq] at hx ⊢
              linarith
            exact hmono h

          have hG₁_strip : ∀ point ∈ selectedG₁,
              point ∈ wz1LineNeighborhood base direction width :=
            hG₁_narrow

          have hF_strip : ∀ point ∈ selectedF,
              point ∈ wz1LineNeighborhood 0 (wz1Perp2 direction) width := by
            intro point hpoint
            rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, h_eq_point⟩
            let swappedEdge := wz1SwapTriple edge
            have hswapped : swappedEdge ∈ swappedGraph :=
              Finset.mem_image_of_mem _ hedge
            have h := hStrip2Narrow.2 swappedEdge hswapped
            have h_swap_eq : swappedEdge.1 = edge.1 := by
              simp [swappedEdge, wz1SwapTriple]
            have h_final : swappedEdge.1 = point := by
              exact h_swap_eq.trans h_eq_point
            rwa [h_final] at h

          exact Or.inr ⟨{
            selectedF := selectedF, selectedG₁ := selectedG₁,
            selectedG₂ := selectedG₂, refinedH := refinedH,
            selectedF_subset := hselectedF_subset,
            selectedG₁_subset := hselectedG₁_subset,
            selectedG₂_subset := hselectedG₂_subset,
            refinedH_subset := hrefinedH_subset,
            selectedF_nonempty := hselectedF_nonempty,
            selectedG₁_nonempty := hselectedG₁_nonempty,
            selectedG₂_nonempty := hselectedG₂_nonempty,
            selectedF_ball := hselectedF_ball,
            selectedG₁_ball := hselectedG₁_ball,
            selectedG₂_ball := hselectedG₂_ball,
            selectedF_separated := hselectedF_sep,
            selectedG₁_separated := hselectedG₁_sep,
            selectedG₂_separated := hselectedG₂_sep,
            selectedF_frostman := hselectedF_frostman',
            selectedG₁_frostman := hselectedG₁_frostman',
            selectedG₂_frostman := hselectedG₂_frostman',
            firstRawNormal := firstNormal, firstRawLevel := firstLevel,
            firstRawWidth := firstWidth,
            firstRawNormal_unit := prep.firstNormal_unit,
            firstRawWidth_pos := hfirstWidth_pos,
            first_raw_strip := hfirstRawStrip,
            secondRawNormal := secondNormal, secondRawLevel := secondLevel,
            secondRawWidth := secondWidth,
            secondRawNormal_unit := prep.secondNormal_unit,
            secondRawWidth_pos := hsecondWidth_pos,
            second_raw_strip := hsecondRawStrip,
            first_raw_nonconcentration := hfirstNonconcFinal,
            second_raw_nonconcentration := hsecondNonconcFinal,
            standardSeparation := hstandard',
            uniform := hUniformExact,
            base := base, direction := direction,
            direction_unit := hdir_unit,
            width := width, width_pos := hwidth_pos,
            delta_le_width := hdelta_le_width,
            width_le_one := hwidth_le_one,
            width_le_first_raw := hwidth_le_first,
            width_le_second_raw := hwidth_le_second,
            first_strip := hG₁_strip,
            second_strip := hG₂_strip,
            orthogonal_strip := hF_strip
          }⟩

    · -- Second strip gave long projection
      have hLP2' : WZ1StripLocalizationLongProjection
          delta stripEps stripEta refinedGraph :=
        hLP2.swap
      have hgraph : refinedGraph ⊆ H :=
        prep.refinedGraph_subset.trans prep.firstRefinedGraph_subset
      have hLP2'' : WZ1StripLocalizationLongProjection
          delta epsilon eta H :=
        WZ1StripLocalizationLongProjection.mono
          hLP2'
          hstripEps_lt_eps.le
          heta_lt_stripEta.le
          hgraph
          hdelta hdelta_one hstripEta_pos
      exact Or.inl hLP2''

  · -- First strip gave long projection
    have hLP1' : WZ1StripLocalizationLongProjection
        delta epsilon eta H :=
      WZ1StripLocalizationLongProjection.mono
        hLP1
        hstripEps_lt_eps.le
        heta_lt_stripEta.le
        prep.firstRefinedGraph_subset
        hdelta hdelta_one hstripEta_pos
    exact Or.inl hLP1'

end Kakeya.Assouad

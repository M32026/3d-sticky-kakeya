import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseSplitStatements

/-!
# Final assembly of Proposition 8.9 wide coarse package from split leaves

This theorem constructs `WZ1Proposition8_9WideCoarseData` from the
sequential-rescaling and coarse line-nonconcentration leaves.

## Proof route

1. Obtain parameter caps from both leaves and shrink them to satisfy
   Frostman, density, and scale absorption conditions.
2. Apply the sequential rescaling leaf to get three synchronized
   anisotropic Frostman rescalings with a uniform source graph.
3. Apply the line nonconcentration leaf to both endpoint coarse sets.
4. Apply `anisotropic_balanced_coarse_graph_uniform` to snap the source
   graph to balanced coarse cells and recover uniform density.
5. Weaken the three coarse Frostman constants using
   `wideCoarseFrostmanBound` (instantiated with `2 * workingLambda`).
6. Weaken the refined density constant `delta^eta / 2^27` to
   `scale^alpha` using `wideCoarseDensityBound`.
7. Prove coarse set boundedness (≤ 3) via assignment surjectivity,
   image boundedness (≤ 2), and the triangle inequality.
8. Construct the source witness using `wideCoarseDotIdentity`,
   assignment closeness, image boundedness, and nonexpansive
   inverse transport of standard separation lower bounds.
-/

namespace Kakeya.Assouad

open scoped ENNReal

theorem wz1_proposition8_9_wide_coarse_from_split :
    WZ1Proposition8_9WideCoarseFromSplitStatement := by
  intro hSeq hLine hRefine hRescale epsilon parameters heps_pos heps_lt_one
  rcases hSeq hRefine hRescale epsilon parameters heps_pos heps_lt_one with
    ⟨etaCapSeq, hSeqEtaPos, hSeqBody⟩
  rcases hLine epsilon parameters heps_pos heps_lt_one with
    ⟨etaCapLine, hLineEtaPos, hLineBody⟩

  set beta : ℝ := parameters.alpha * epsilon / 20 with hbeta_def
  have hbeta_pos : 0 < beta := by
    rw [hbeta_def]
    have h1 : 0 < parameters.alpha * epsilon := mul_pos parameters.alpha_pos heps_pos
    exact div_pos h1 (by norm_num)
  set etaCapFrost : ℝ := parameters.projectionLambda / parameters.stripEpsilon
    with hetaCapFrost_def
  have hetaCapFrost_pos : 0 < etaCapFrost := by
    rw [hetaCapFrost_def]
    exact div_pos parameters.projectionLambda_pos parameters.stripEpsilon_pos
  set etaCap : ℝ :=
      min etaCapSeq (min etaCapLine (min beta etaCapFrost))
    with hetaCap_def
  have hetaCap_pos : 0 < etaCap := by
    have h1 : 0 < min beta etaCapFrost := lt_min hbeta_pos hetaCapFrost_pos
    have h2 : 0 < min etaCapLine (min beta etaCapFrost) := lt_min hLineEtaPos h1
    exact lt_min hSeqEtaPos h2
  have hetaCap_le_seq : etaCap ≤ etaCapSeq := by
    simp [hetaCap_def]
  have hetaCap_le_line : etaCap ≤ etaCapLine := by
    simp [hetaCap_def]
  have hetaCap_le_frost : etaCap ≤ etaCapFrost := by
    simp [hetaCap_def]
  have hetaCap_le_beta : etaCap ≤ beta := by
    simp [hetaCap_def]

  refine ⟨etaCap, hetaCap_pos, ?_⟩
  intro eta h_eta_pos h_eta_le
  have h_eta_le_seq : eta ≤ etaCapSeq := by linarith
  have h_eta_le_line : eta ≤ etaCapLine := by linarith
  have h_eta_le_frost : eta ≤ etaCapFrost := by linarith
  have h_eta_le_beta : eta ≤ beta := by linarith
  rcases hSeqBody eta h_eta_pos h_eta_le_seq with
    ⟨delta₀Seq, hSeqDeltaPos, hSeqDeltaLeOne, hSeqAt⟩
  rcases hLineBody eta h_eta_pos h_eta_le_line with
    ⟨delta₀Line, hLineDeltaPos, hLineDeltaLeOne, hLineAt⟩

  set dScale : ℝ := Real.rpow parameters.projectionDelta₀ (10 / epsilon) with hdScale_def
  have hdScale_pos : 0 < dScale := Real.rpow_pos_of_pos parameters.projectionDelta₀_pos _
  have hdScale_le_one : dScale ≤ 1 := by
    have h1 : parameters.projectionDelta₀ ≤ 1 := parameters.projectionDelta₀_le_one
    have h2 : 0 < 10 / epsilon := by apply div_pos <;> linarith
    exact Real.rpow_le_one parameters.projectionDelta₀_pos.le h1 h2.le
  have h_rpow_dScale : Real.rpow dScale (epsilon / 10) = parameters.projectionDelta₀ := by
    rw [hdScale_def]
    have h : Real.rpow parameters.projectionDelta₀ ((10 / epsilon) * (epsilon / 10)) =
        Real.rpow (Real.rpow parameters.projectionDelta₀ (10 / epsilon)) (epsilon / 10) :=
      Real.rpow_mul parameters.projectionDelta₀_pos.le (10 / epsilon) (epsilon / 10)
    have h3 : (10 / epsilon) * (epsilon / 10) = 1 := by field_simp [heps_pos.ne']
    rw [h3] at h
    simpa [dScale] using h.symm
  set dDensity : ℝ := Real.rpow (1 / (2 ^ 27 : ℝ)) (20 / (parameters.alpha * epsilon)) with hdDensity_def
  have hdDensity_pos : 0 < dDensity := Real.rpow_pos_of_pos (by norm_num) _
  have hdDensity_le_one : dDensity ≤ 1 := by
    have h1 : (1 / (2 ^ 27 : ℝ)) < 1 := by norm_num
    have h2 : 0 < 20 / (parameters.alpha * epsilon) := by
      apply div_pos <;> linarith [parameters.alpha_pos, heps_pos]
    exact Real.rpow_lt_one (by linarith) h1 h2 |>.le
  have h_rpow_dDensity : Real.rpow dDensity beta = 1 / (2 ^ 27 : ℝ) := by
    rw [hdDensity_def, hbeta_def]
    have h4 : 20 / (parameters.alpha * epsilon) * (parameters.alpha * epsilon / 20) = 1 := by
      field_simp [parameters.alpha_pos.ne', heps_pos.ne']
    have h : Real.rpow (1 / (2 ^ 27 : ℝ)) ((20 / (parameters.alpha * epsilon)) * (parameters.alpha * epsilon / 20)) =
        Real.rpow (Real.rpow (1 / (2 ^ 27 : ℝ)) (20 / (parameters.alpha * epsilon))) (parameters.alpha * epsilon / 20) :=
      Real.rpow_mul (by norm_num) _ _
    rw [h4] at h
    simpa [dDensity, beta] using h.symm
  set delta₀ : ℝ := min delta₀Seq (min delta₀Line (min dScale dDensity))
    with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by
    have h1 : 0 < min dScale dDensity := lt_min hdScale_pos hdDensity_pos
    have h2 : 0 < min delta₀Line (min dScale dDensity) := lt_min hLineDeltaPos h1
    exact lt_min hSeqDeltaPos h2
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    have h : delta₀ ≤ delta₀Seq := by simp [hdelta₀_def]
    linarith [hSeqDeltaLeOne]
  have hdelta₀_le_seq : delta₀ ≤ delta₀Seq := by simp [hdelta₀_def]
  have hdelta₀_le_line : delta₀ ≤ delta₀Line := by simp [hdelta₀_def]
  have hdelta₀_le_dDensity : delta₀ ≤ dDensity := by simp [hdelta₀_def]
  have hdelta₀_le_dScale : delta₀ ≤ dScale := by simp [hdelta₀_def]

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta F G₁ G₂ H hdelta_pos hdelta_le data hwidth

  have hdelta_le_one : delta ≤ 1 := by linarith

  have hSeqData : Nonempty (WZ1Proposition8_9WideSequentialRescalingData
      delta epsilon eta parameters F G₁ G₂ H data) :=
    hSeqAt hdelta_pos (hdelta_le.trans hdelta₀_le_seq)
      data hwidth
  rcases hSeqData with ⟨sequential⟩

  have hLineData : WZ1LineNonConcentration (delta / data.width)
        (parameters.projectionLambda / 2)
          parameters.zeta sequential.firstRescale.coarse ∧
      WZ1LineNonConcentration (delta / data.width)
        (parameters.projectionLambda / 2)
          parameters.zeta sequential.secondRescale.coarse :=
    hLineAt hdelta_pos (hdelta_le.trans hdelta₀_le_line)
      data hwidth sequential
  rcases hLineData with ⟨hLineMargin1, hLineMargin2⟩

  set scale : ℝ := delta / data.width with hscale_def
  have hscale_pos : 0 < scale := by
    rw [hscale_def]
    exact div_pos hdelta_pos data.width_pos
  have hscale_le_one : scale ≤ 1 := by
    rw [hscale_def]
    exact (div_le_one data.width_pos).mpr data.delta_le_width
  have hscale_lt_delta_pow : scale < Real.rpow delta (epsilon / 10) :=
    wideCoarseScaleBound hdelta_pos data.width_pos heps_pos hwidth
  have hscale_le_delta_pow : scale ≤ Real.rpow delta (epsilon / 10) :=
    hscale_lt_delta_pow.le
  have h_rpow_delta_beta : Real.rpow delta beta ≤ 1 / (2 ^ 27 : ℝ) := by
    have hdelta_le_dDensity : delta ≤ dDensity := le_trans hdelta_le hdelta₀_le_dDensity
    have h1 : Real.rpow delta beta ≤ Real.rpow dDensity beta :=
      Real.rpow_le_rpow hdelta_pos.le hdelta_le_dDensity hbeta_pos.le
    rw [h_rpow_dDensity] at h1
    exact h1
  have hscale_le_projectionDelta₀ : scale ≤ parameters.projectionDelta₀ := by
    calc
      scale ≤ Real.rpow delta (epsilon / 10) := hscale_le_delta_pow
      _ ≤ Real.rpow dScale (epsilon / 10) := by
        have hdelta_le_dScale : delta ≤ dScale := le_trans hdelta_le hdelta₀_le_dScale
        exact Real.rpow_le_rpow hdelta_pos.le hdelta_le_dScale (by linarith)
      _ = parameters.projectionDelta₀ := h_rpow_dScale

  set epsilon_r : ℝ := parameters.stripEpsilon * eta / 10 with hepsilon_r_def
  have hepsilon_r_pos : 0 < epsilon_r := by
    rw [hepsilon_r_def]
    exact mul_pos (mul_pos parameters.stripEpsilon_pos h_eta_pos) (by norm_num)
  have hepsilon_r_le_tenth : epsilon_r ≤ parameters.projectionLambda / 10 := by
    calc
      epsilon_r = parameters.stripEpsilon * eta / 10 := rfl
      _ ≤ parameters.stripEpsilon * etaCapFrost / 10 := by
        have h : parameters.stripEpsilon * eta ≤ parameters.stripEpsilon * etaCapFrost :=
          mul_le_mul_of_nonneg_left h_eta_le_frost parameters.stripEpsilon_pos.le
        linarith
      _ = parameters.projectionLambda / 10 := by
        rw [hetaCapFrost_def]
        field_simp [parameters.stripEpsilon_pos.ne']
  have hsum : 2 * parameters.workingLambda ≤
      (epsilon / 10) * (parameters.projectionLambda - epsilon_r) := by
    have h1 : 2 * parameters.workingLambda ≤ epsilon * parameters.projectionLambda / 50 := by
      have h2 : parameters.workingLambda ≤ epsilon * parameters.projectionLambda / 100 :=
        parameters.workingLambda_le_epsilon_projection
      linarith
    have h3 : parameters.projectionLambda - epsilon_r ≥ 9 * parameters.projectionLambda / 10 := by
      linarith [hepsilon_r_le_tenth]
    have h4 : (epsilon / 10) * (parameters.projectionLambda - epsilon_r) ≥
        9 * epsilon * parameters.projectionLambda / 100 := by
      have h5 : (epsilon / 10) * (parameters.projectionLambda - epsilon_r) ≥
          (epsilon / 10) * (9 * parameters.projectionLambda / 10) := by gcongr
      have h6 : (epsilon / 10) * (9 * parameters.projectionLambda / 10) =
          9 * epsilon * parameters.projectionLambda / 100 := by ring
      rw [h6] at h5
      exact h5
    have h7 : epsilon * parameters.projectionLambda / 50 ≤
        9 * epsilon * parameters.projectionLambda / 100 := by
      have h8 : 0 < epsilon * parameters.projectionLambda :=
        mul_pos heps_pos parameters.projectionLambda_pos
      linarith
    exact le_trans h1 (le_trans h7 h4)

  have hsupport : ∀ edge ∈ sequential.sourceGraph,
      edge.1 ∈ sequential.thirdRescale.selected ∧
      edge.2.1 ∈ sequential.firstRescale.selected ∧
      edge.2.2 ∈ sequential.secondRescale.selected := by
    intro edge hedge
    have h1 : wz1TripleCoordinate edge ∈ wz1EncodeTriples sequential.sourceGraph :=
      Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    have h2 := sequential.sourceUniform.2.1 (wz1TripleCoordinate edge) h1
    exact ⟨h2 0, h2 1, h2 2⟩

  rcases anisotropic_balanced_coarse_graph_uniform
      sequential.thirdRescale sequential.firstRescale sequential.secondRescale
      hsupport sequential.sourceUniform hRefine with
    ⟨coarseH, refinedH, hcoarseH_eq, hrefinedSubset, hrefinedUniform, hwitness⟩

  set coarseF : DiscreteSet 2 := sequential.thirdRescale.coarse with hcoarseF_def
  set coarseG₁ : DiscreteSet 2 := sequential.firstRescale.coarse with hcoarseG₁_def
  set coarseG₂ : DiscreteSet 2 := sequential.secondRescale.coarse with hcoarseG₂_def

  have h2wl_pos : 0 < 2 * parameters.workingLambda :=
    mul_pos (by norm_num) parameters.workingLambda_pos
  have h_inv_scale : data.width / delta = 1 / scale := by
    rw [hscale_def]
    field_simp [hdelta_pos.ne', data.width_pos.ne']
  have h_eps_r_eq : parameters.stripEpsilon * eta / 10 = epsilon_r := by
    rw [hepsilon_r_def]
  have hFrostBound : Kakeya.realRpowENN (1 / scale) epsilon_r *
      Kakeya.realRpowENN delta (-(2 * parameters.workingLambda)) ≤
      Kakeya.realRpowENN scale (-parameters.projectionLambda) :=
    wideCoarseFrostmanBound hdelta_pos hdelta_le_one hscale_pos hscale_le_one
      hscale_le_delta_pow h2wl_pos
      parameters.projectionLambda_pos hepsilon_r_pos heps_pos hsum
  have hFrostF : coarseF.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-parameters.projectionLambda)) := by
    have h1 := sequential.thirdRescale.coarse_frostman
    have h2 : Kakeya.realRpowENN (data.width / delta) (parameters.stripEpsilon * eta / 10) *
        Kakeya.realRpowENN delta (-(2 * parameters.workingLambda)) ≤
        Kakeya.realRpowENN scale (-parameters.projectionLambda) := by
      rw [h_inv_scale, h_eps_r_eq]
      exact hFrostBound
    exact h1.mono h2
  have hFrostG₁ : coarseG₁.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-parameters.projectionLambda)) := by
    have h1 := sequential.firstRescale.coarse_frostman
    have h2 : Kakeya.realRpowENN (data.width / delta) (parameters.stripEpsilon * eta / 10) *
        Kakeya.realRpowENN delta (-(2 * parameters.workingLambda)) ≤
        Kakeya.realRpowENN scale (-parameters.projectionLambda) := by
      rw [h_inv_scale, h_eps_r_eq]
      exact hFrostBound
    exact h1.mono h2
  have hFrostG₂ : coarseG₂.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-parameters.projectionLambda)) := by
    have h1 := sequential.secondRescale.coarse_frostman
    have h2 : Kakeya.realRpowENN (data.width / delta) (parameters.stripEpsilon * eta / 10) *
        Kakeya.realRpowENN delta (-(2 * parameters.workingLambda)) ≤
        Kakeya.realRpowENN scale (-parameters.projectionLambda) := by
      rw [h_inv_scale, h_eps_r_eq]
      exact hFrostBound
    exact h1.mono h2

  have hFrostMarginBound :
      Kakeya.realRpowENN (1 / scale) epsilon_r *
          Kakeya.realRpowENN
            delta (-(2 * parameters.workingLambda)) ≤
        Kakeya.realRpowENN
          scale (-(parameters.projectionLambda / 2)) := by
    apply wideCoarseFrostmanBound
      hdelta_pos hdelta_le_one hscale_pos hscale_le_one
      hscale_le_delta_pow h2wl_pos
      (div_pos parameters.projectionLambda_pos (by norm_num))
      hepsilon_r_pos heps_pos
    have h1 :
        2 * parameters.workingLambda ≤
          epsilon * parameters.projectionLambda / 50 := by
      linarith
        [parameters.workingLambda_le_epsilon_projection]
    have h2 :
        parameters.projectionLambda / 2 - epsilon_r ≥
          2 * parameters.projectionLambda / 5 := by
      linarith [hepsilon_r_le_tenth]
    have h3 :
        epsilon * parameters.projectionLambda / 50 ≤
          (epsilon / 10) *
            (parameters.projectionLambda / 2 - epsilon_r) := by
      nlinarith [mul_pos heps_pos parameters.projectionLambda_pos]
    exact h1.trans h3
  have hFrostMarginF :
      coarseF.IsFrostman scale 1
        (Kakeya.realRpowENN
          scale (-(parameters.projectionLambda / 2))) := by
    exact sequential.thirdRescale.coarse_frostman.mono (by
      rw [h_inv_scale, h_eps_r_eq]
      exact hFrostMarginBound)
  have hFrostMarginG₁ :
      coarseG₁.IsFrostman scale 1
        (Kakeya.realRpowENN
          scale (-(parameters.projectionLambda / 2))) := by
    exact sequential.firstRescale.coarse_frostman.mono (by
      rw [h_inv_scale, h_eps_r_eq]
      exact hFrostMarginBound)
  have hFrostMarginG₂ :
      coarseG₂.IsFrostman scale 1
        (Kakeya.realRpowENN
          scale (-(parameters.projectionLambda / 2))) := by
    exact sequential.secondRescale.coarse_frostman.mono (by
      rw [h_inv_scale, h_eps_r_eq]
      exact hFrostMarginBound)
  have hLine1 :
      WZ1LineNonConcentration scale
        parameters.projectionLambda parameters.zeta coarseG₁ := by
    exact hLineMargin1.mono_lambda
      hscale_pos hscale_le_one (by linarith)
      parameters.zeta_pos.le
  have hLine2 :
      WZ1LineNonConcentration scale
        parameters.projectionLambda parameters.zeta coarseG₂ := by
    exact hLineMargin2.mono_lambda
      hscale_pos hscale_le_one (by linarith)
      parameters.zeta_pos.le

  have hDensityBound : Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal) ≥
      Kakeya.realRpowENN scale parameters.alpha :=
    wideCoarseDensityBound hdelta_pos hdelta_le_one h_eta_pos parameters.alpha_pos
      heps_pos hscale_pos hscale_le_delta_pow h_eta_le_beta h_rpow_delta_beta

  have h_const27 : ((((1 / 256 : ENNReal) / 16) / 16) / 16) / 128 = (1 : ENNReal) / (2 ^ 27) := by
    have h_left : ((((1 / 256 : ENNReal) / 16) / 16) / 16) / 128 =
        ENNReal.ofReal ((((1 : ℝ) / 256 / 16 / 16 / 16) / 128)) := by
      simp [div_eq_mul_inv]
    have h_right : (1 : ENNReal) / (2 ^ 27) = ENNReal.ofReal ((1 : ℝ) / 2 ^ 27) := by
      simp [div_eq_mul_inv]
    rw [h_left, h_right]
    have h_real : (((1 : ℝ) / 256 / 16 / 16 / 16) / 128) = (1 : ℝ) / 2 ^ 27 := by norm_num
    rw [h_real]
  have h_refined_const : ((((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta) / 16) / 16) / 16 / 128 =
      Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal) := by
    have h_comm : ((((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta) / 16) / 16) / 16 / 128 =
        ((((1 / 256 : ENNReal) / 16) / 16) / 16) / 128 * Kakeya.realRpowENN delta eta := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm]
      <;> ac_rfl
    rw [h_comm, h_const27]
    <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm] <;> ac_rfl
  have hUniformFinal : WZ1UniformTripleDensity
      (Kakeya.realRpowENN scale parameters.alpha)
      coarseF coarseG₁ coarseG₂ refinedH := by
    rw [h_refined_const] at hrefinedUniform
    exact hrefinedUniform.mono hDensityBound

  let phiF := wideCoarsePhiF data.direction data.width data.width_pos data.direction_unit
  let phiG := wideCoarsePhiG data.direction data.width data.width_pos data.base 0 data.direction_unit

  have hdataSupport : ∀ edge ∈ data.refinedH,
      edge.1 ∈ data.selectedF ∧ edge.2.1 ∈ data.selectedG₁ ∧ edge.2.2 ∈ data.selectedG₂ := by
    intro edge hedge
    have h1 : wz1TripleCoordinate edge ∈ wz1EncodeTriples data.refinedH :=
      Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    have h2 := data.uniform.2.1 (wz1TripleCoordinate edge) h1
    exact ⟨h2 0, h2 1, h2 2⟩
  have hprojF_subset : wz1ActiveTripleProjection sequential.secondGraph 0 ⊆ data.selectedF := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨edge, hedge, rfl⟩
    have h3 : edge ∈ data.refinedH := by
      have h4 : sequential.secondGraph ⊆ data.refinedH :=
        subset_trans sequential.secondGraph_subset sequential.firstGraph_subset
      exact h4 hedge
    exact (hdataSupport edge h3).1
  have hprojG1_subset : wz1ActiveTripleProjection data.refinedH 1 ⊆ data.selectedG₁ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨edge, hedge, rfl⟩
    exact (hdataSupport edge hedge).2.1
  have hprojG2_subset : wz1ActiveTripleProjection sequential.firstGraph 2 ⊆ data.selectedG₂ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨edge, hedge, rfl⟩
    have h3 : edge ∈ data.refinedH := sequential.firstGraph_subset hedge
    exact (hdataSupport edge h3).2.2
  have hthirdSelected_subset : sequential.thirdRescale.selected ⊆ data.selectedF :=
    subset_trans sequential.thirdRescale.selected_subset hprojF_subset
  have hfirstSelected_subset : sequential.firstRescale.selected ⊆ data.selectedG₁ :=
    subset_trans sequential.firstRescale.selected_subset hprojG1_subset
  have hsecondSelected_subset : sequential.secondRescale.selected ⊆ data.selectedG₂ :=
    subset_trans sequential.secondRescale.selected_subset hprojG2_subset

  have hF_strip : ∀ p ∈ sequential.thirdRescale.selected,
      |inner ℝ p data.direction| ≤ data.width := by
    intro p hp
    have h5 : p ∈ data.selectedF := hthirdSelected_subset hp
    have h6 : p ∈ wz1LineNeighborhood 0 (wz1Perp2 data.direction) data.width :=
      data.orthogonal_strip p h5
    have h_perp2 : wz1Perp2 (wz1Perp2 data.direction) = -data.direction := by
      ext i; fin_cases i <;> simp [wz1Perp2]
    simpa [wz1LineNeighborhood, h_perp2, abs_neg] using h6
  have hF_ball : sequential.thirdRescale.selected.IsInUnitBall := by
    intro p hp
    exact data.selectedF_ball p (hthirdSelected_subset hp)
  have hphiF_bounded : ∀ p ∈ sequential.thirdRescale.selected,
      dist (phiF p) 0 ≤ 2 :=
    wideCoarsePhiF_image_bounded hF_strip hF_ball

  have hG1_strip : ∀ p ∈ sequential.firstRescale.selected,
      |inner ℝ (p - data.base) (wz1Perp2 data.direction)| ≤ data.width := by
    intro p hp
    have h5 : p ∈ data.selectedG₁ := hfirstSelected_subset hp
    have h6 : p ∈ wz1LineNeighborhood data.base data.direction data.width :=
      data.first_strip p h5
    simpa [wz1LineNeighborhood] using h6
  have hG1_ball : sequential.firstRescale.selected.IsInUnitBall := by
    intro p hp
    exact data.selectedG₁_ball p (hfirstSelected_subset hp)
  have hphiG1_bounded : ∀ p ∈ sequential.firstRescale.selected,
      dist (phiG p) 0 ≤ 2 :=
    wideCoarsePhiG_zero_anchor_image_bounded hG1_strip hG1_ball

  have hG2_strip : ∀ p ∈ sequential.secondRescale.selected,
      |inner ℝ (p - data.base) (wz1Perp2 data.direction)| ≤ data.width := by
    intro p hp
    have h5 : p ∈ data.selectedG₂ := hsecondSelected_subset hp
    have h6 : p ∈ wz1LineNeighborhood data.base data.direction data.width :=
      data.second_strip p h5
    simpa [wz1LineNeighborhood] using h6
  have hG2_ball : sequential.secondRescale.selected.IsInUnitBall := by
    intro p hp
    exact data.selectedG₂_ball p (hsecondSelected_subset hp)
  have hphiG2_bounded : ∀ p ∈ sequential.secondRescale.selected,
      dist (phiG p) 0 ≤ 2 :=
    wideCoarsePhiG_zero_anchor_image_bounded hG2_strip hG2_ball

  have hcoarseF_bounded : ∀ point ∈ coarseF, dist point 0 ≤ 3 := by
    intro q hq
    rcases sequential.thirdRescale.assignment_surjective q hq with ⟨x, hx, rfl⟩
    have h1 : dist (phiF x) (sequential.thirdRescale.assignment x) ≤ scale :=
      sequential.thirdRescale.assignment_close x hx
    have h2 : dist (phiF x) 0 ≤ 2 := hphiF_bounded x hx
    calc
      dist (sequential.thirdRescale.assignment x) 0 ≤
          dist (sequential.thirdRescale.assignment x) (phiF x) + dist (phiF x) 0 :=
        dist_triangle _ _ _
      _ = dist (phiF x) (sequential.thirdRescale.assignment x) + dist (phiF x) 0 := by
        rw [dist_comm]
      _ ≤ scale + 2 := by linarith
      _ ≤ 3 := by linarith [hscale_le_one]
  have hcoarseG1_bounded : ∀ point ∈ coarseG₁, dist point 0 ≤ 3 := by
    intro q hq
    rcases sequential.firstRescale.assignment_surjective q hq with ⟨x, hx, rfl⟩
    have h1 : dist (phiG x) (sequential.firstRescale.assignment x) ≤ scale :=
      sequential.firstRescale.assignment_close x hx
    have h2 : dist (phiG x) 0 ≤ 2 := hphiG1_bounded x hx
    calc
      dist (sequential.firstRescale.assignment x) 0 ≤
          dist (sequential.firstRescale.assignment x) (phiG x) + dist (phiG x) 0 :=
        dist_triangle _ _ _
      _ = dist (phiG x) (sequential.firstRescale.assignment x) + dist (phiG x) 0 := by
        rw [dist_comm]
      _ ≤ scale + 2 := by linarith
      _ ≤ 3 := by linarith [hscale_le_one]
  have hcoarseG2_bounded : ∀ point ∈ coarseG₂, dist point 0 ≤ 3 := by
    intro q hq
    rcases sequential.secondRescale.assignment_surjective q hq with ⟨x, hx, rfl⟩
    have h1 : dist (phiG x) (sequential.secondRescale.assignment x) ≤ scale :=
      sequential.secondRescale.assignment_close x hx
    have h2 : dist (phiG x) 0 ≤ 2 := hphiG2_bounded x hx
    calc
      dist (sequential.secondRescale.assignment x) 0 ≤
          dist (sequential.secondRescale.assignment x) (phiG x) + dist (phiG x) 0 :=
        dist_triangle _ _ _
      _ = dist (phiG x) (sequential.secondRescale.assignment x) + dist (phiG x) 0 := by
        rw [dist_comm]
      _ ≤ scale + 2 := by linarith
      _ ≤ 3 := by linarith [hscale_le_one]

  have hphiF_zero : phiF 0 = 0 := by
    simp only [phiF, wideCoarsePhiF]
    have hcenter : wz1Lemma49StripProjection 0 (wz1Perp2 data.direction) 0 = 0 := by
      simp [wz1Lemma49StripProjection]
    rw [wz1Lemma49StripNormalizationMap_apply, hcenter]
    <;> simp
  have hwidth_le_one : data.width ≤ 1 := data.width_le_one
  have hphiF_symm_nonexp : ∀ (x y : Point2),
      dist (phiF.symm x) (phiF.symm y) ≤ dist x y :=
    wideCoarsePhiF_symm_nonexpansive (hw := data.width_pos) (hw_le_one := hwidth_le_one)
  have hphiG_symm_nonexp : ∀ (x y : Point2),
      dist (phiG.symm x) (phiG.symm y) ≤ dist x y :=
    wideCoarsePhiG_symm_nonexpansive (hw := data.width_pos) (hw_le_one := hwidth_le_one)

  have hsource_witness : ∀ coarseEdge ∈ refinedH,
      ∃ sourceEdge ∈ data.refinedH,
        ∃ transformedEdge : Point2 × Point2 × Point2,
          inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) =
            data.width * inner ℝ transformedEdge.1 (transformedEdge.2.1 - transformedEdge.2.2) ∧
          dist transformedEdge.1 coarseEdge.1 ≤ scale ∧
          dist transformedEdge.2.1 coarseEdge.2.1 ≤ scale ∧
          dist transformedEdge.2.2 coarseEdge.2.2 ≤ scale ∧
          dist transformedEdge.1 0 ≤ 2 ∧
          dist transformedEdge.2.1 0 ≤ 2 ∧
          dist transformedEdge.2.2 0 ≤ 2 ∧
          1 / 2 ≤ dist transformedEdge.1 0 ∧
          1 / 2 ≤ dist transformedEdge.2.1 transformedEdge.2.2 := by
    intro coarseEdge hedge
    rcases hwitness coarseEdge hedge with
      ⟨sourceEdge, hsourceInGraph, hsourceF, hsourceG1, hsourceG2, hmapEq,
       hcloseF, hcloseG1, hcloseG2⟩
    have hsourceInRefinedH : sourceEdge ∈ data.refinedH := by
      have h1 : sourceEdge ∈ sequential.sourceGraph := hsourceInGraph
      have h2 : sequential.sourceGraph ⊆ sequential.secondGraph := sequential.sourceGraph_subset
      have h3 : sequential.secondGraph ⊆ sequential.firstGraph := sequential.secondGraph_subset
      have h4 : sequential.firstGraph ⊆ data.refinedH := sequential.firstGraph_subset
      exact h4 (h3 (h2 h1))
    set transformedEdge : Point2 × Point2 × Point2 :=
        (phiF sourceEdge.1, phiG sourceEdge.2.1, phiG sourceEdge.2.2)
      with htransformedEdge_def
    have hdot : inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) =
        data.width * inner ℝ transformedEdge.1
          (transformedEdge.2.1 - transformedEdge.2.2) :=
      wideCoarseDotIdentity data.direction data.width data.width_pos
        data.direction_unit data.base 0 sourceEdge.1 sourceEdge.2.1 sourceEdge.2.2
    have hcloseF' : dist transformedEdge.1 coarseEdge.1 ≤ scale := by
      simpa [htransformedEdge_def] using hcloseF
    have hcloseG1' : dist transformedEdge.2.1 coarseEdge.2.1 ≤ scale := by
      simpa [htransformedEdge_def] using hcloseG1
    have hcloseG2' : dist transformedEdge.2.2 coarseEdge.2.2 ≤ scale := by
      simpa [htransformedEdge_def] using hcloseG2
    have hboundF : dist transformedEdge.1 0 ≤ 2 := hphiF_bounded sourceEdge.1 hsourceF
    have hboundG1 : dist transformedEdge.2.1 0 ≤ 2 := hphiG1_bounded sourceEdge.2.1 hsourceG1
    have hboundG2 : dist transformedEdge.2.2 0 ≤ 2 := hphiG2_bounded sourceEdge.2.2 hsourceG2
    have hlowerF : 1 / 2 ≤ dist transformedEdge.1 0 := by
      have hstd : 1 / 2 ≤ dist sourceEdge.1 0 :=
        data.standardSeparation.2.2.2.2 sourceEdge.1 (hthirdSelected_subset hsourceF)
      have h5 : dist sourceEdge.1 0 ≤ dist (phiF sourceEdge.1) (phiF 0) := by
        have h6 := hphiF_symm_nonexp (phiF sourceEdge.1) (phiF 0)
        simpa using h6
      rw [hphiF_zero] at h5
      simpa [htransformedEdge_def] using le_trans hstd h5
    have hlowerG : 1 / 2 ≤ dist transformedEdge.2.1 transformedEdge.2.2 := by
      have hstd : 1 / 2 ≤ dist sourceEdge.2.1 sourceEdge.2.2 :=
        data.standardSeparation.2.2.2.1 sourceEdge.2.1
          (hfirstSelected_subset hsourceG1) sourceEdge.2.2
          (hsecondSelected_subset hsourceG2)
      have h5 : dist sourceEdge.2.1 sourceEdge.2.2 ≤
          dist (phiG sourceEdge.2.1) (phiG sourceEdge.2.2) := by
        have h6 := hphiG_symm_nonexp (phiG sourceEdge.2.1) (phiG sourceEdge.2.2)
        simpa using h6
      simpa [htransformedEdge_def] using le_trans hstd h5
    exact ⟨sourceEdge, hsourceInRefinedH, transformedEdge,
      hdot, hcloseF', hcloseG1', hcloseG2', hboundF, hboundG1, hboundG2, hlowerF, hlowerG⟩

  refine Nonempty.intro ⟨
    scale, rfl, hscale_pos, hscale_le_projectionDelta₀,
    coarseF, coarseG₁, coarseG₂, refinedH,
    sequential.thirdRescale.coarse_nonempty,
    sequential.firstRescale.coarse_nonempty,
    sequential.secondRescale.coarse_nonempty,
    hcoarseF_bounded, hcoarseG1_bounded, hcoarseG2_bounded,
    sequential.thirdRescale.coarse_separated,
    sequential.firstRescale.coarse_separated,
    sequential.secondRescale.coarse_separated,
    hFrostF, hFrostMarginF,
    hFrostG₁, hFrostMarginG₁,
    hFrostG₂, hFrostMarginG₂,
    hLine1, hLineMargin1,
    hLine2, hLineMargin2,
    by
      rw [h_refined_const] at hrefinedUniform
      exact hrefinedUniform,
    hUniformFinal,
    hsource_witness
  ⟩

end Kakeya.Assouad

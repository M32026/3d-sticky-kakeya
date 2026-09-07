import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointFrostmanSplitAssembly

/-!
PDF Proposition 8.9 wide branch: finite two-strip Frostman counting in the
fixed-projective-angle regime, conditional on the explicit ball radius being
at most one.
-/

namespace Kakeya.Assouad

theorem wz1_wide_coarse_endpoint_projective_frostman_count :
    WZ1WideCoarseEndpointProjectiveFrostmanCountStatement := by
  intro epsilon eta delta F G₁ G₂ ambient active H
    parameters hdelta data input normal hnormal haxial
    hprojective hsmallWidth level radius hradius hballRadiusOne
  classical
  let pullback :=
    wideCoarsePhiGPullbackVector
      data.direction data.width normal
  let sourceNormal := (1 / ‖pullback‖) • pullback
  let sourceLevel :=
    (level -
      inner ℝ
        (wideCoarsePhiG
          data.direction data.width data.width_pos
          data.base 0 data.direction_unit 0)
        normal) /
      ‖pullback‖
  let rawRadius :=
    wideCoarseEndpointSourceRawRadius data normal radius
  let signedNormal :=
    wideCoarseEndpointSignedNormal
      (wz1Perp2 data.direction) sourceNormal
  let signedLevel :=
    wideCoarseEndpointSignedLevel
      (wz1Perp2 data.direction) sourceNormal sourceLevel
  let ballRadius :=
    wideCoarseEndpointProjectiveFrostmanBallRadius
      data normal radius
  have hpullback :=
    anisotropic_coarse_strip_card_le_exact_source_strip
      (hwOne := data.width_le_one)
      input.rescale hdelta.le normal hnormal
      level radius
      ((div_pos hdelta data.width_pos).le.trans hradius)
  have hsourceNormal : ‖sourceNormal‖ = 1 := by
    simpa [pullback, sourceNormal, sourceLevel] using hpullback.1
  have hrawRadiusPos : 0 < rawRadius := by
    dsimp only [rawRadius, wideCoarseEndpointSourceRawRadius]
    exact hdelta.trans_le (le_max_left _ _)
  have hperpUnit : ‖wz1Perp2 data.direction‖ = 1 := by
    rw [wz1Lemma49_norm_perp, data.direction_unit]
  have hsignedUnit : ‖signedNormal‖ = 1 := by
    exact wideCoarseEndpoint_signedNormal_unit hsourceNormal
  have hsourcePerp :
      |inner ℝ (wz1Perp2 data.direction) sourceNormal| ≤
        1 / 2 := by
    simpa [pullback, sourceNormal] using
      wideCoarseEndpoint_projective_source_perp_upper
        data.width_pos data.direction_unit hnormal
        haxial hprojective
  have hangleLower :
      1 ≤ ‖wz1Perp2 data.direction - signedNormal‖ := by
    exact
      wideCoarseEndpoint_signedNormal_dist_lower
        hperpUnit hsourceNormal hsourcePerp
  have hangleUpper :
      ‖wz1Perp2 data.direction - signedNormal‖ ≤
        Real.sqrt 2 := by
    exact
      wideCoarseEndpoint_signedNormal_dist_upper
        hperpUnit hsourceNormal
  have hdeltaBall : delta ≤ ballRadius := by
    dsimp only [ballRadius,
      wideCoarseEndpointProjectiveFrostmanBallRadius]
    have hdeltaRaw : delta ≤ rawRadius := by
      dsimp only [rawRadius,
        wideCoarseEndpointSourceRawRadius]
      exact le_max_left _ _
    have hrawLe :
        rawRadius ≤ max data.width rawRadius :=
      le_max_right _ _
    have hscale :
        max data.width rawRadius ≤
          6 * max data.width rawRadius := by
      have hnonnegative :
          0 ≤ max data.width rawRadius := by
        exact data.width_pos.le.trans (le_max_left _ _)
      nlinarith
    exact hdeltaRaw.trans (hrawLe.trans hscale)
  have htwoStrip :=
    frostman_two_strip_intersection_card
      data.width_pos hrawRadiusPos (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) ≤ 1)
      (wz1Perp2 data.direction) signedNormal
      hperpUnit hsignedUnit hangleLower hangleUpper
      data.base (signedLevel • signedNormal)
      (by
        simpa [ballRadius,
          wideCoarseEndpointProjectiveFrostmanBallRadius] using
          hdeltaBall)
      (by
        simpa [ballRadius,
          wideCoarseEndpointProjectiveFrostmanBallRadius] using
          hballRadiusOne)
      input.ambient_frostman
  let sourcePredicate : Point2 → Prop :=
    fun point =>
      |inner ℝ point sourceNormal - sourceLevel| ≤ rawRadius
  have hsignedPredicate
      (point : Point2) :
      |inner ℝ (point - signedLevel • signedNormal) signedNormal| =
        |inner ℝ point sourceNormal - sourceLevel| := by
    have hfunctional :
        inner ℝ (point - signedLevel • signedNormal) signedNormal =
          inner ℝ point signedNormal - signedLevel := by
      rw [inner_sub_left, inner_smul_left,
        real_inner_self_eq_norm_sq, hsignedUnit]
      norm_num
    rw [hfunctional]
    exact
      wideCoarseEndpoint_signed_strip_eq
        (wz1Perp2 data.direction) sourceNormal point sourceLevel
  have hambient :
      ((ambient.filter sourcePredicate).card : ENNReal) ≤
        Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN ballRadius 1 *
          ambient.enncard := by
    have hsubset :
        ambient.filter sourcePredicate ⊆
          ambient.filter fun point =>
            |inner ℝ (point - data.base)
                (wz1Perp2 data.direction)| ≤ data.width ∧
              |inner ℝ
                  (point - signedLevel • signedNormal)
                  signedNormal| ≤ rawRadius := by
      intro point hpoint
      have hpointData := Finset.mem_filter.mp hpoint
      exact
        Finset.mem_filter.mpr
          ⟨hpointData.1,
            input.ambient_strip point hpointData.1,
            by
              rw [hsignedPredicate point]
              exact hpointData.2⟩
    have hcard :
        ((ambient.filter sourcePredicate).card : ENNReal) ≤
          ((ambient.filter fun point =>
            |inner ℝ (point - data.base)
                (wz1Perp2 data.direction)| ≤ data.width ∧
              |inner ℝ
                  (point - signedLevel • signedNormal)
                  signedNormal| ≤ rawRadius).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsubset
    calc
      ((ambient.filter sourcePredicate).card : ENNReal)
          ≤
        ((ambient.filter fun point =>
          |inner ℝ (point - data.base)
              (wz1Perp2 data.direction)| ≤ data.width ∧
            |inner ℝ
                (point - signedLevel • signedNormal)
                signedNormal| ≤ rawRadius).card : ENNReal) :=
        hcard
      _ ≤
        Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN
            (6 * max data.width rawRadius / 1) 1 *
          ambient.enncard := htwoStrip
      _ =
        Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN ballRadius 1 *
          ambient.enncard := by
            congr 2
            simp only [ballRadius,
              wideCoarseEndpointProjectiveFrostmanBallRadius,
              rawRadius]
            ring
  have hchain :=
    wideCoarseEndpoint_selected_card_le_frostman_chain
      input hdelta sourcePredicate ballRadius hambient
  simpa [WZ1WideCoarseEndpointFrostmanCountBound,
    sourcePredicate, pullback, sourceNormal, sourceLevel,
    rawRadius, ballRadius] using hchain

end Kakeya.Assouad

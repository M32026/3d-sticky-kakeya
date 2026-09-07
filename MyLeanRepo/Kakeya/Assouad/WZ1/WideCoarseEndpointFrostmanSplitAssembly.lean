import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointFrostmanSplitStatements

/-!
# Assemble the axial Frostman endpoint budgets from fine leaves
-/

namespace Kakeya.Assouad

open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- In the nontrivial target-coefficient branch, the test radius is bounded
by a fixed `zeta`-dependent constant times the positive coarse-scale power
`tau^(lambda/2)`. -/
lemma wideCoarseEndpoint_radius_lt_of_target_lt_two
    {tau radius lambda zeta : ℝ}
    (htau : 0 < tau)
    (hradius : 0 < radius)
    (hzeta : 0 < zeta)
    (htarget :
      ¬ (2 : ENNReal) ≤
        Kakeya.realRpowENN
          (Real.rpow tau (-(lambda / 2)) * radius)
          zeta) :
    radius <
      Real.rpow 2 (1 / zeta) *
        Real.rpow tau (lambda / 2) := by
  let base :=
    Real.rpow tau (-(lambda / 2)) * radius
  let constant := Real.rpow 2 (1 / zeta)
  have hbase : 0 < base := by
    dsimp only [base]
    exact
      mul_pos (Real.rpow_pos_of_pos htau _) hradius
  have hconstant : 0 < constant := by
    dsimp only [constant]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have htargetReal :
      Real.rpow base zeta < 2 := by
    have htargetENN :
        Kakeya.realRpowENN base zeta < (2 : ENNReal) :=
      lt_of_not_ge htarget
    simpa [Kakeya.realRpowENN,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 2)]
      using htargetENN
  have hconstantPower :
      Real.rpow constant zeta = 2 := by
    dsimp only [constant]
    calc
      Real.rpow (Real.rpow 2 (1 / zeta)) zeta =
          Real.rpow 2 ((1 / zeta) * zeta) := by
        exact
          (Real.rpow_mul
            (by norm_num : (0 : ℝ) ≤ 2)
            (1 / zeta) zeta).symm
      _ = Real.rpow 2 1 := by
        congr 1
        field_simp [hzeta.ne']
      _ = 2 := by simp
  have hbaseConstant : base < constant := by
    rw [←
      Real.rpow_lt_rpow_iff hbase.le hconstant.le hzeta]
    exact htargetReal.trans_eq hconstantPower.symm
  have htauHalfPos :
      0 < Real.rpow tau (lambda / 2) :=
    Real.rpow_pos_of_pos htau _
  have htauCancel :
      Real.rpow tau (-(lambda / 2)) *
          Real.rpow tau (lambda / 2) = 1 := by
    calc
      Real.rpow tau (-(lambda / 2)) *
          Real.rpow tau (lambda / 2) =
        Real.rpow tau
          (-(lambda / 2) + lambda / 2) :=
        (Real.rpow_add htau _ _).symm
      _ = Real.rpow tau 0 := by
        congr 1
        ring
      _ = 1 := by simp
  have hscaled :=
    mul_lt_mul_of_pos_right hbaseConstant htauHalfPos
  dsimp only [base, constant] at hscaled
  calc
    radius =
        (Real.rpow tau (-(lambda / 2)) * radius) *
          Real.rpow tau (lambda / 2) := by
      rw [mul_assoc, mul_comm radius,
        ← mul_assoc, htauCancel, one_mul]
    _ <
        Real.rpow 2 (1 / zeta) *
          Real.rpow tau (lambda / 2) := hscaled

/-- In the axial regime, the fixed-angle Frostman ball is controlled by the
larger of the common-strip width and the test radius. -/
lemma wideCoarseEndpoint_projective_frostmanBall_upper
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {normal : Point2} {radius : ℝ}
    (hdelta : 0 < delta)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 data.direction)| < 1 / 2)
    (hradius : delta / data.width ≤ radius) :
    wideCoarseEndpointProjectiveFrostmanBallRadius
        data normal radius ≤
      24 * max data.width radius := by
  have hraw :=
    wideCoarseEndpoint_axial_rawRadius_upper
      hdelta data.width_pos data.width_le_one hradius
      data.direction_unit hnormal haxial
  have hmax :
      max data.width
          (wideCoarseEndpointSourceRawRadius data normal radius) ≤
        4 * max data.width radius := by
    apply max_le
    · calc
        data.width ≤ max data.width radius := le_max_left _ _
        _ ≤ 4 * max data.width radius := by
          have hnonnegative :
              0 ≤ max data.width radius :=
            data.width_pos.le.trans (le_max_left _ _)
          nlinarith
    · calc
        wideCoarseEndpointSourceRawRadius data normal radius
            ≤ 4 * radius := by
              simpa [wideCoarseEndpointSourceRawRadius] using hraw
        _ ≤ 4 * max data.width radius := by
              exact mul_le_mul_of_nonneg_left
                (le_max_right _ _) (by norm_num)
  dsimp only [
    wideCoarseEndpointProjectiveFrostmanBallRadius]
  nlinarith

/--
In the non-projective axial regime, divide the two terms in the maximum by
the exact angle separately:

* `width / theta` is controlled by the perpendicular coefficient;
* `rawRadius / theta` is controlled by the coarse test radius.
-/
lemma wideCoarseEndpoint_smallCoefficient_frostmanBall_upper
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {normal : Point2} {radius : ℝ}
    (hdelta : 0 < delta)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 data.direction)| < 1 / 2)
    (hnotProjective :
      ¬ WZ1WideCoarseEndpointAxialProjectiveBranch
        data.direction normal data.width)
    (hradius : delta / data.width ≤ radius) :
    wideCoarseEndpointSmallCoefficientFrostmanBallRadius
        data normal radius ≤
      24 *
        (|inner ℝ normal (wz1Perp2 data.direction)| + radius) := by
  let parallel := |inner ℝ normal data.direction|
  let perpendicular :=
    |inner ℝ normal (wz1Perp2 data.direction)|
  let pullback :=
    wideCoarsePhiGPullbackVector
      data.direction data.width normal
  let pullbackNorm := ‖pullback‖
  let tau := delta / data.width
  let sourceRadius := (radius + tau) / pullbackNorm
  let rawRadius := max delta sourceRadius
  let theta := parallel / pullbackNorm
  let angleFactor := pullbackNorm / parallel
  have hparallel : 3 / 4 < parallel := by
    simpa [parallel] using
      wideCoarseEndpoint_axial_parallel_lower
        data.direction_unit hnormal haxial
  have hparallelPos : 0 < parallel := by linarith
  have hpullbackParallel :=
    wideCoarseEndpoint_pullback_norm_ge_parallel
      (width := data.width) (normal := normal)
      data.direction_unit
  have hpullbackPos : 0 < pullbackNorm := by
    change
      0 <
        ‖wideCoarsePhiGPullbackVector
          data.direction data.width normal‖
    exact hparallelPos.trans_le hpullbackParallel
  have htau : 0 < tau := div_pos hdelta data.width_pos
  have hradiusPos : 0 < radius := htau.trans_le hradius
  have hlarge :
      parallel / 2 < perpendicular / data.width := by
    simpa [WZ1WideCoarseEndpointAxialProjectiveBranch,
      parallel, perpendicular] using lt_of_not_ge hnotProjective
  have hwidthParallel :
      data.width * parallel < 2 * perpendicular := by
    have hparallelScaled :
        parallel < 2 * perpendicular / data.width := by
      calc
        parallel = 2 * (parallel / 2) := by ring
        _ < 2 * (perpendicular / data.width) := by
          exact mul_lt_mul_of_pos_left hlarge (by norm_num)
        _ = 2 * perpendicular / data.width := by ring
    have hproduct :=
      (lt_div_iff₀ data.width_pos).1 hparallelScaled
    simpa [mul_comm] using hproduct
  have hframe :=
    wideCoarsePhiGPullbackVector_norm_sq
      (w := data.width) (normal := normal)
      data.direction_unit
  have hpullbackUpper :
      pullbackNorm ≤ parallel + perpendicular / data.width := by
    have hparallelNonnegative : 0 ≤ parallel := abs_nonneg _
    have hscaledNonnegative :
        0 ≤ perpendicular / data.width :=
      div_nonneg (abs_nonneg _) data.width_pos.le
    apply
      (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg hparallelNonnegative hscaledNonnegative)).1
    change
      ‖wideCoarsePhiGPullbackVector
          data.direction data.width normal‖ ^ 2 ≤
        (parallel + perpendicular / data.width) ^ 2
    rw [hframe]
    have hparallelSq :
        (inner ℝ normal data.direction) ^ 2 = parallel ^ 2 := by
      simp [parallel, sq_abs]
    have hperpendicularSq :
        (inner ℝ normal (wz1Perp2 data.direction) /
            data.width) ^ 2 =
          (perpendicular / data.width) ^ 2 := by
      rw [div_pow, div_pow]
      simp [perpendicular, sq_abs]
    rw [hparallelSq, hperpendicularSq]
    nlinarith
  have hwidthAngle :
      data.width * angleFactor ≤ 4 * perpendicular := by
    dsimp only [angleFactor]
    rw [show
      data.width * (pullbackNorm / parallel) =
        (data.width * pullbackNorm) / parallel by ring]
    apply (div_le_iff₀ hparallelPos).2
    calc
      data.width * pullbackNorm ≤
          data.width *
            (parallel + perpendicular / data.width) := by
        exact mul_le_mul_of_nonneg_left
          hpullbackUpper data.width_pos.le
      _ = data.width * parallel + perpendicular := by
        field_simp [data.width_pos.ne']
      _ ≤ 4 * perpendicular * parallel := by
        have hparallelLower : 3 / 4 ≤ parallel := hparallel.le
        have hperpendicularNonnegative : 0 ≤ perpendicular := abs_nonneg _
        nlinarith [hwidthParallel]
  have hsourceAngle :
      sourceRadius * angleFactor =
        (radius + tau) / parallel := by
    dsimp only [sourceRadius, angleFactor]
    field_simp [hpullbackPos.ne', hparallelPos.ne']
  have hsourceAngleBound :
      sourceRadius * angleFactor ≤ 3 * radius := by
    rw [hsourceAngle]
    apply (div_le_iff₀ hparallelPos).2
    have htauRadius : tau ≤ radius := hradius
    have hparallelLower : 3 / 4 ≤ parallel := hparallel.le
    nlinarith
  have hdeltaEq : delta = tau * data.width := by
    dsimp only [tau]
    field_simp [data.width_pos.ne']
  have hdeltaAngle :
      delta * angleFactor ≤ 2 * radius := by
    rw [hdeltaEq, mul_assoc]
    calc
      tau * (data.width * angleFactor)
          ≤ tau * (4 * perpendicular) := by
        exact mul_le_mul_of_nonneg_left hwidthAngle htau.le
      _ ≤ tau * 2 := by
        exact mul_le_mul_of_nonneg_left
          (by linarith [haxial]) htau.le
      _ ≤ 2 * radius := by nlinarith
  have hangleFactorNonnegative : 0 ≤ angleFactor := by
    dsimp only [angleFactor]
    positivity
  have hrawAngle :
      rawRadius * angleFactor ≤ 3 * radius := by
    dsimp only [rawRadius]
    calc
      max delta sourceRadius * angleFactor =
          max (delta * angleFactor)
            (sourceRadius * angleFactor) := by
        exact max_mul_of_nonneg delta sourceRadius
          hangleFactorNonnegative
      _ ≤ 3 * radius := by
        exact max_le
          (hdeltaAngle.trans (by nlinarith))
          hsourceAngleBound
  have hmaxAngle :
      max data.width rawRadius * angleFactor ≤
        4 * (perpendicular + radius) := by
    calc
      max data.width rawRadius * angleFactor =
          max (data.width * angleFactor)
            (rawRadius * angleFactor) := by
        exact max_mul_of_nonneg
          data.width rawRadius hangleFactorNonnegative
      _ ≤ 4 * (perpendicular + radius) := by
        apply max_le
        · have hperpendicularNonnegative : 0 ≤ perpendicular := abs_nonneg _
          nlinarith [hwidthAngle]
        · have hperpendicularNonnegative : 0 ≤ perpendicular := abs_nonneg _
          nlinarith [hrawAngle]
  have htheta : theta = parallel / pullbackNorm := rfl
  have hballRewrite :
      wideCoarseEndpointSmallCoefficientFrostmanBallRadius
          data normal radius =
        6 * max data.width rawRadius * angleFactor := by
    rw [wideCoarseEndpointSmallCoefficientFrostmanBallRadius]
    change
      6 * max data.width rawRadius / theta =
        6 * max data.width rawRadius * angleFactor
    dsimp only [theta, angleFactor]
    field_simp [hparallelPos.ne', hpullbackPos.ne']
  rw [hballRewrite]
  calc
    6 * max data.width rawRadius * angleFactor =
        6 * (max data.width rawRadius * angleFactor) := by ring
    _ ≤ 6 * (4 * (perpendicular + radius)) := by
      exact mul_le_mul_of_nonneg_left hmaxAngle (by norm_num)
    _ =
        24 *
          (|inner ℝ normal (wz1Perp2 data.direction)| + radius) := by
      dsimp only [perpendicular]
      ring

/-- In the small-coefficient and target-`< 2` regime, both terms in the
exact-angle Frostman ball are controlled by the reserved
`tau^(3 * lambda / 20)` power. -/
lemma wideCoarseEndpoint_smallCoefficient_frostmanBall_tau_upper
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {normal : Point2} {radius : ℝ}
    (hdelta : 0 < delta)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 data.direction)| < 1 / 2)
    (hnotProjective :
      ¬ WZ1WideCoarseEndpointAxialProjectiveBranch
        data.direction normal data.width)
    (hsmallCoefficient :
      WZ1WideCoarseEndpointAxialSmallCoefficient
        parameters data normal)
    (hradius : delta / data.width ≤ radius)
    (htarget :
      ¬ (2 : ENNReal) ≤
        wideCoarseEndpointTargetCoefficient
          parameters data radius) :
    let tau := delta / data.width
    let widthExponent := 3 * parameters.projectionLambda / 20
    wideCoarseEndpointSmallCoefficientFrostmanBallRadius
        data normal radius ≤
      24 *
        (1 + Real.rpow 2 (1 / parameters.zeta)) *
          Real.rpow tau widthExponent := by
  dsimp only
  let tau := delta / data.width
  let widthExponent := 3 * parameters.projectionLambda / 20
  let radiusExponent := parameters.projectionLambda / 2
  have htau : 0 < tau := div_pos hdelta data.width_pos
  have htauOne : tau ≤ 1 :=
    (div_le_one data.width_pos).2 data.delta_le_width
  have hradiusPos : 0 < radius := htau.trans_le hradius
  have hperpendicular :
      |inner ℝ normal (wz1Perp2 data.direction)| ≤
        Real.rpow tau widthExponent := by
    simpa [WZ1WideCoarseEndpointAxialSmallCoefficient,
      tau, widthExponent] using hsmallCoefficient
  have hradiusBound :
      radius <
        Real.rpow 2 (1 / parameters.zeta) *
          Real.rpow tau radiusExponent := by
    apply
      wideCoarseEndpoint_radius_lt_of_target_lt_two
        htau hradiusPos parameters.zeta_pos
    simpa [wideCoarseEndpointTargetCoefficient,
      tau, radiusExponent] using htarget
  have hexponents : widthExponent ≤ radiusExponent := by
    dsimp only [widthExponent, radiusExponent]
    nlinarith [parameters.projectionLambda_pos]
  have hradiusPower :
      Real.rpow tau radiusExponent ≤
        Real.rpow tau widthExponent :=
    Real.rpow_le_rpow_of_exponent_ge
      htau htauOne hexponents
  have hradiusCoarse :
      radius ≤
        Real.rpow 2 (1 / parameters.zeta) *
          Real.rpow tau widthExponent := by
    calc
      radius ≤
          Real.rpow 2 (1 / parameters.zeta) *
            Real.rpow tau radiusExponent := hradiusBound.le
      _ ≤
          Real.rpow 2 (1 / parameters.zeta) *
            Real.rpow tau widthExponent := by
        exact mul_le_mul_of_nonneg_left
          hradiusPower
          (Real.rpow_nonneg (by norm_num) _)
  have hball :=
    wideCoarseEndpoint_smallCoefficient_frostmanBall_upper
      hdelta hnormal haxial hnotProjective hradius
  calc
    wideCoarseEndpointSmallCoefficientFrostmanBallRadius
          data normal radius
        ≤
      24 *
        (|inner ℝ normal (wz1Perp2 data.direction)| + radius) :=
      hball
    _ ≤
      24 *
        (Real.rpow tau widthExponent +
          Real.rpow 2 (1 / parameters.zeta) *
            Real.rpow tau widthExponent) := by
      gcongr
    _ =
      24 *
        (1 + Real.rpow 2 (1 / parameters.zeta)) *
          Real.rpow tau widthExponent := by ring

/-- The lower bound `tau ≤ radius` supplies the radius power needed by the
target coefficient in the width-dominant Frostman case. -/
lemma wideCoarseEndpoint_tau_power_le_target
    {tau radius lambda zeta : ℝ}
    (htau : 0 < tau)
    (hradius : 0 < radius)
    (htauRadius : tau ≤ radius)
    (hzeta : 0 < zeta) :
    Kakeya.realRpowENN tau
        (zeta * (1 - lambda / 2)) ≤
      Kakeya.realRpowENN tau (-(lambda * zeta / 2)) *
        Kakeya.realRpowENN radius zeta := by
  have hradiusPower :
      Kakeya.realRpowENN tau zeta ≤
        Kakeya.realRpowENN radius zeta := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow htau.le htauRadius hzeta.le)
  have hsplit :
      Kakeya.realRpowENN tau
          (zeta * (1 - lambda / 2)) =
        Kakeya.realRpowENN tau (-(lambda * zeta / 2)) *
          Kakeya.realRpowENN tau zeta := by
    rw [← realRpowENN_add htau]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hradiusPower (by positivity)

/-- Raising the target-`< 2` radius bound to the positive exponent
`1-zeta` preserves the positive coarse-scale gain. -/
lemma wideCoarseEndpoint_radius_loss_power_upper
    {tau radius lambda zeta : ℝ}
    (htau : 0 < tau)
    (hradius : 0 < radius)
    (hzeta : 0 < zeta)
    (hzetaOne : zeta < 1)
    (hradiusBound :
      radius <
        Real.rpow 2 (1 / zeta) *
          Real.rpow tau (lambda / 2)) :
    Kakeya.realRpowENN radius (1 - zeta) ≤
      Kakeya.realRpowENN 2 ((1 - zeta) / zeta) *
        Kakeya.realRpowENN tau
          ((lambda / 2) * (1 - zeta)) := by
  have hexponent : 0 ≤ 1 - zeta := by linarith
  have hboundNonnegative :
      0 ≤
        Real.rpow 2 (1 / zeta) *
          Real.rpow tau (lambda / 2) := by
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg htau.le _)
  have hreal :
      Real.rpow radius (1 - zeta) ≤
        Real.rpow
          (Real.rpow 2 (1 / zeta) *
            Real.rpow tau (lambda / 2))
          (1 - zeta) :=
    Real.rpow_le_rpow hradius.le hradiusBound.le hexponent
  have hproduct :
      Real.rpow
          (Real.rpow 2 (1 / zeta) *
            Real.rpow tau (lambda / 2))
          (1 - zeta) =
        Real.rpow 2 ((1 - zeta) / zeta) *
          Real.rpow tau
            ((lambda / 2) * (1 - zeta)) := by
    calc
      Real.rpow
          (Real.rpow 2 (1 / zeta) *
            Real.rpow tau (lambda / 2))
          (1 - zeta) =
        Real.rpow (Real.rpow 2 (1 / zeta)) (1 - zeta) *
          Real.rpow (Real.rpow tau (lambda / 2))
            (1 - zeta) := by
              exact Real.mul_rpow
                (Real.rpow_nonneg (by norm_num) _)
                (Real.rpow_nonneg htau.le _)
      _ =
        Real.rpow 2 ((1 / zeta) * (1 - zeta)) *
          Real.rpow tau
            ((lambda / 2) * (1 - zeta)) := by
              congr 1
              · exact
                  (Real.rpow_mul
                    (by norm_num : (0 : ℝ) ≤ 2)
                    (1 / zeta) (1 - zeta)).symm
              · exact
                  (Real.rpow_mul
                    htau.le (lambda / 2) (1 - zeta)).symm
      _ =
        Real.rpow 2 ((1 - zeta) / zeta) *
          Real.rpow tau
            ((lambda / 2) * (1 - zeta)) := by
              congr 2
              field_simp [hzeta.ne']
  rw [hproduct] at hreal
  simp only [Kakeya.realRpowENN]
  calc
    ENNReal.ofReal (Real.rpow radius (1 - zeta))
        ≤
      ENNReal.ofReal
        (Real.rpow 2 ((1 - zeta) / zeta) *
          Real.rpow tau ((lambda / 2) * (1 - zeta))) :=
      ENNReal.ofReal_mono hreal
    _ =
      ENNReal.ofReal
          (Real.rpow 2 ((1 - zeta) / zeta)) *
        ENNReal.ofReal
          (Real.rpow tau ((lambda / 2) * (1 - zeta))) := by
            exact ENNReal.ofReal_mul
              (Real.rpow_nonneg (by norm_num) _)

/-- Split the first power of a positive radius into the target radius power
and the retained positive factor `radius^(1-zeta)`. -/
lemma wideCoarseEndpoint_radius_power_split
    {radius zeta : ℝ} (hradius : 0 < radius) :
    Kakeya.realRpowENN radius 1 =
      Kakeya.realRpowENN radius (1 - zeta) *
        Kakeya.realRpowENN radius zeta := by
  rw [← realRpowENN_add hradius]
  congr 1
  ring

/-- The explicit Frostman coefficient is one fixed constant times the
coarse-scale Frostman loss and the supplied ball radius. -/
lemma wideCoarseEndpoint_frostmanCoefficient_upper
    {epsilon eta delta ballRadius : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta) :
    wideCoarseEndpointFrostmanCoefficient
        parameters input ballRadius ≤
      (8192 : ENNReal) *
        Kakeya.realRpowENN
          (delta / data.width)
          (-(wideCoarseEndpointFrostmanLoss parameters eta)) *
        Kakeya.realRpowENN ballRadius 1 := by
  let tau := delta / data.width
  have htau : 0 < tau :=
    div_pos hdelta data.width_pos
  have hactiveInv :=
    wideCoarseEndpoint_activeFraction_inv
      (delta := delta) (eta := eta) hdelta
  have hrescaleInv :=
    wideCoarseEndpoint_rescaleFraction_inv
      (delta := delta) (width := data.width)
      (exponent := parameters.stripEpsilon * eta / 10)
      hdelta data.width_pos
  have htauPower :
      tau ≤ Real.rpow delta (epsilon / 10) :=
    (wideCoarseScaleBound hdelta data.width_pos
      hepsilon input.width_large).le
  have hdeltaLoss :=
    wideCoarseEndpoint_delta_loss_to_tau
      hdelta htau hepsilon
      (add_nonneg parameters.workingLambda_pos.le heta.le)
      (loss := parameters.workingLambda + eta)
      htauPower
  have hdeltaAdd :
      Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN delta (-eta) =
        Kakeya.realRpowENN delta
          (-(parameters.workingLambda + eta)) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  have htauAdd :
      Kakeya.realRpowENN tau
            (-(10 * (parameters.workingLambda + eta) / epsilon)) *
          Kakeya.realRpowENN tau
            (-(parameters.stripEpsilon * eta / 10)) =
        Kakeya.realRpowENN tau
          (-(wideCoarseEndpointFrostmanLoss parameters eta)) := by
    rw [← realRpowENN_add htau]
    congr 1
    simp [wideCoarseEndpointFrostmanLoss]
    ring
  rw [wideCoarseEndpointFrostmanCoefficient,
    hactiveInv, hrescaleInv]
  calc
    Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN ballRadius 1 *
          ((4096 : ENNReal) *
            Kakeya.realRpowENN delta (-eta)) *
          Kakeya.realRpowENN tau
            (-(parameters.stripEpsilon * eta / 10)) *
          2
        =
      (8192 : ENNReal) *
        (Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN delta (-eta)) *
        Kakeya.realRpowENN tau
          (-(parameters.stripEpsilon * eta / 10)) *
        Kakeya.realRpowENN ballRadius 1 := by
          have hconstant :
              (4096 : ENNReal) * 2 = 8192 := by norm_num
          rw [← hconstant]
          ac_rfl
    _ =
      (8192 : ENNReal) *
        Kakeya.realRpowENN delta
          (-(parameters.workingLambda + eta)) *
        Kakeya.realRpowENN tau
          (-(parameters.stripEpsilon * eta / 10)) *
        Kakeya.realRpowENN ballRadius 1 := by
          rw [hdeltaAdd]
    _ ≤
      (8192 : ENNReal) *
        Kakeya.realRpowENN tau
          (-(10 * (parameters.workingLambda + eta) / epsilon)) *
        Kakeya.realRpowENN tau
          (-(parameters.stripEpsilon * eta / 10)) *
        Kakeya.realRpowENN ballRadius 1 := by
          gcongr
    _ =
      (8192 : ENNReal) *
        Kakeya.realRpowENN tau
          (-(wideCoarseEndpointFrostmanLoss parameters eta)) *
        Kakeya.realRpowENN ballRadius 1 := by
          calc
            (8192 : ENNReal) *
                  Kakeya.realRpowENN tau
                    (-(10 * (parameters.workingLambda + eta) / epsilon)) *
                  Kakeya.realRpowENN tau
                    (-(parameters.stripEpsilon * eta / 10)) *
                  Kakeya.realRpowENN ballRadius 1 =
                (8192 : ENNReal) *
                  (Kakeya.realRpowENN tau
                      (-(10 * (parameters.workingLambda + eta) / epsilon)) *
                    Kakeya.realRpowENN tau
                      (-(parameters.stripEpsilon * eta / 10))) *
                  Kakeya.realRpowENN ballRadius 1 := by ac_rfl
            _ = _ := by rw [htauAdd]

/-- Convert an ambient Frostman intersection count into the selected/coarse
count used by both axial Frostman leaves.  This is the common finite
retention chain; it contains no strip geometry or scale-power comparison. -/
lemma wideCoarseEndpoint_selected_card_le_frostman_chain
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (hdelta : 0 < delta)
    (predicate : Point2 → Prop)
    (ballRadius : ℝ)
    (hambient :
      ((ambient.filter predicate).card : ENNReal) ≤
        Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN ballRadius 1 *
          ambient.enncard) :
    ((input.rescale.selected.filter predicate).card : ENNReal) ≤
      wideCoarseEndpointFrostmanCoefficient
          parameters input ballRadius *
        (input.rescale.fiberMultiplicity : ENNReal) *
        input.rescale.coarse.enncard := by
  classical
  let activeFraction :=
    wideCoarseEndpointActiveFraction delta eta
  let rescaleFraction :=
    wideCoarseEndpointRescaleFraction
      delta data.width
      (parameters.stripEpsilon * eta / 10)
  have hselectedAmbient :
      input.rescale.selected ⊆ ambient :=
    input.rescale.selected_subset.trans input.active_subset
  have hselectedCount :
      ((input.rescale.selected.filter predicate).card : ENNReal) ≤
        ((ambient.filter predicate).card : ENNReal) := by
    exact_mod_cast
      Finset.card_le_card
        (Finset.filter_subset_filter
          predicate hselectedAmbient)
  have hactiveFractionPos : 0 < activeFraction := by
    have hrpowPos :
        0 < Kakeya.realRpowENN delta eta := by
      simp only [Kakeya.realRpowENN, ENNReal.ofReal_pos]
      exact Real.rpow_pos_of_pos hdelta _
    dsimp only [activeFraction,
      wideCoarseEndpointActiveFraction]
    exact
      ENNReal.div_pos
        (mul_ne_zero (by norm_num) hrpowPos.ne')
        (by norm_num)
  have hactiveFractionTop : activeFraction ≠ ⊤ := by
    dsimp only [activeFraction,
      wideCoarseEndpointActiveFraction]
    exact
      ENNReal.div_ne_top
        (ENNReal.mul_ne_top
          (by simp)
          (by simp [Kakeya.realRpowENN]))
        (by simp)
  have hambientActive :
      ambient.enncard ≤ activeFraction⁻¹ * active.enncard := by
    have hretention :
        activeFraction * ambient.enncard ≤ active.enncard := by
      simpa [activeFraction,
        wideCoarseEndpointActiveFraction] using
          input.active_retention
    have hscaled :=
      mul_le_mul_left' hretention activeFraction⁻¹
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel
        hactiveFractionPos.ne' hactiveFractionTop,
      one_mul] at hscaled
    exact hscaled
  have hrescaleFractionPos : 0 < rescaleFraction := by
    dsimp only [rescaleFraction,
      wideCoarseEndpointRescaleFraction,
      Kakeya.realRpowENN]
    rw [ENNReal.ofReal_pos]
    exact Real.rpow_pos_of_pos
      (div_pos hdelta data.width_pos) _
  have hrescaleFractionTop : rescaleFraction ≠ ⊤ := by
    dsimp only [rescaleFraction,
      wideCoarseEndpointRescaleFraction,
      Kakeya.realRpowENN]
    simp
  have hactiveSelected :
      active.enncard ≤
        rescaleFraction⁻¹ *
          input.rescale.selected.enncard := by
    have hretention :
        rescaleFraction * active.enncard ≤
          input.rescale.selected.enncard := by
      simpa [rescaleFraction,
        wideCoarseEndpointRescaleFraction] using
          input.rescale.retention
    have hscaled :=
      mul_le_mul_left' hretention rescaleFraction⁻¹
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel
        hrescaleFractionPos.ne' hrescaleFractionTop,
      one_mul] at hscaled
    exact hscaled
  have hselectedCoarse :=
    anisotropic_selected_card_le_two_fiber_coarse
      input.rescale
  calc
    ((input.rescale.selected.filter predicate).card : ENNReal)
        ≤ ((ambient.filter predicate).card : ENNReal) :=
      hselectedCount
    _ ≤
        Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN ballRadius 1 *
          ambient.enncard := hambient
    _ ≤
        Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN ballRadius 1 *
          (activeFraction⁻¹ * active.enncard) := by
      gcongr
    _ ≤
        Kakeya.realRpowENN delta (-parameters.workingLambda) *
          Kakeya.realRpowENN ballRadius 1 *
          (activeFraction⁻¹ *
            (rescaleFraction⁻¹ *
              input.rescale.selected.enncard)) := by
      gcongr
    _ ≤
        wideCoarseEndpointFrostmanCoefficient
            parameters input ballRadius *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard := by
      dsimp only [wideCoarseEndpointFrostmanCoefficient]
      simp only [activeFraction, rescaleFraction]
      calc
        Kakeya.realRpowENN delta
              (-parameters.workingLambda) *
            Kakeya.realRpowENN ballRadius 1 *
            ((wideCoarseEndpointActiveFraction delta eta)⁻¹ *
              ((wideCoarseEndpointRescaleFraction
                delta data.width
                (parameters.stripEpsilon * eta / 10))⁻¹ *
                input.rescale.selected.enncard))
            ≤
          Kakeya.realRpowENN delta
              (-parameters.workingLambda) *
            Kakeya.realRpowENN ballRadius 1 *
            ((wideCoarseEndpointActiveFraction delta eta)⁻¹ *
              ((wideCoarseEndpointRescaleFraction
                delta data.width
                (parameters.stripEpsilon * eta / 10))⁻¹ *
                ((2 : ENNReal) *
                  (input.rescale.fiberMultiplicity : ENNReal) *
                  input.rescale.coarse.enncard))) := by
              gcongr
        _ =
          (Kakeya.realRpowENN delta
              (-parameters.workingLambda) *
            Kakeya.realRpowENN ballRadius 1 *
            (wideCoarseEndpointActiveFraction delta eta)⁻¹ *
            (wideCoarseEndpointRescaleFraction
              delta data.width
              (parameters.stripEpsilon * eta / 10))⁻¹ *
            2) *
            (input.rescale.fiberMultiplicity : ENNReal) *
            input.rescale.coarse.enncard := by
              ac_rfl

lemma wideCoarseEndpoint_sourceBudget_of_frostman_count
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data}
    {normal : Point2} {level radius ballRadius : ℝ}
    (hcount :
      WZ1WideCoarseEndpointFrostmanCountBound
        parameters input normal level radius ballRadius)
    (hcoefficient :
      wideCoarseEndpointFrostmanCoefficient
          parameters input ballRadius ≤
        wideCoarseEndpointTargetCoefficient
          parameters data radius) :
    WZ1WideCoarseEndpointSourceBudget
      (ambient := ambient) (active := active)
      parameters input normal level radius := by
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
  have hscaled :
      wideCoarseEndpointFrostmanCoefficient
            parameters input ballRadius *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard ≤
        (input.rescale.fiberMultiplicity : ENNReal) *
          (wideCoarseEndpointTargetCoefficient
              parameters data radius *
            input.rescale.coarse.enncard) := by
    calc
      wideCoarseEndpointFrostmanCoefficient
            parameters input ballRadius *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard
          ≤
        wideCoarseEndpointTargetCoefficient
              parameters data radius *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard := by
            gcongr
      _ =
        (input.rescale.fiberMultiplicity : ENNReal) *
          (wideCoarseEndpointTargetCoefficient
              parameters data radius *
            input.rescale.coarse.enncard) := by
              ac_rfl
  simpa [WZ1WideCoarseEndpointSourceBudget,
    WZ1WideCoarseEndpointFrostmanCountBound,
    wideCoarseEndpointTargetCoefficient,
    wideCoarseEndpointSourceRawRadius,
    pullback, sourceNormal, sourceLevel, rawRadius] using
      hcount.trans hscaled

theorem wz1_wide_coarse_endpoint_projective_frostman_of_split
    (hCount :
      WZ1WideCoarseEndpointProjectiveFrostmanCountStatement)
    (hScalar :
      WZ1WideCoarseEndpointProjectiveFrostmanScalarStatement) :
    WZ1WideCoarseEndpointAxialProjectiveFrostmanBudgetStatement := by
  intro epsilon parameters hepsilon hepsilonOne
  rcases hScalar epsilon parameters hepsilon hepsilonOne with
    ⟨etaCap, hetaCap, hScalarAt⟩
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaSmall
  rcases hScalarAt eta heta hetaSmall with
    ⟨delta₀, hdelta₀, hdelta₀One, hScalarMain⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data input normal hnormal haxial
    hprojective hsmallWidth level radius hradius hradiusOne
  by_cases htarget :
      (2 : ENNReal) ≤
        wideCoarseEndpointTargetCoefficient
          parameters data radius
  · apply wideCoarseEndpoint_sourceBudget_of_target_ge_two
    simpa [wideCoarseEndpointTargetCoefficient] using htarget
  · have hscalar :=
      hScalarMain hdelta hdeltaSmall data input normal hnormal
        haxial hprojective hsmallWidth radius hradius hradiusOne
        htarget
    apply
      wideCoarseEndpoint_sourceBudget_of_frostman_count
        (hCount parameters hdelta data input normal hnormal
          haxial hprojective hsmallWidth level radius hradius
          hscalar.1)
    exact hscalar.2

theorem wz1_wide_coarse_endpoint_small_coefficient_of_split
    (hCount :
      WZ1WideCoarseEndpointSmallCoefficientFrostmanCountStatement)
    (hScalar :
      WZ1WideCoarseEndpointSmallCoefficientFrostmanScalarStatement) :
    WZ1WideCoarseEndpointAxialSmallCoefficientBudgetStatement := by
  intro epsilon parameters hepsilon hepsilonOne
  rcases hScalar epsilon parameters hepsilon hepsilonOne with
    ⟨etaCap, hetaCap, hScalarAt⟩
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaSmall
  rcases hScalarAt eta heta hetaSmall with
    ⟨delta₀, hdelta₀, hdelta₀One, hScalarMain⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data input normal hnormal haxial
    hnotProjective hsmallCoefficient level radius hradius hradiusOne
  by_cases htarget :
      (2 : ENNReal) ≤
        wideCoarseEndpointTargetCoefficient
          parameters data radius
  · apply wideCoarseEndpoint_sourceBudget_of_target_ge_two
    simpa [wideCoarseEndpointTargetCoefficient] using htarget
  · have hscalar :=
      hScalarMain hdelta hdeltaSmall data input normal hnormal
        haxial hnotProjective hsmallCoefficient radius
        hradius hradiusOne htarget
    apply
      wideCoarseEndpoint_sourceBudget_of_frostman_count
        (hCount parameters hdelta data input normal hnormal
          haxial hnotProjective hsmallCoefficient
          level radius hradius hscalar.1)
    exact hscalar.2

end Kakeya.Assouad

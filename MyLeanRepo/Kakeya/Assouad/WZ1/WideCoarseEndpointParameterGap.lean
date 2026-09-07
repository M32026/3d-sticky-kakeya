import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

/-!
# Parameter gap for wide coarse endpoint line synthesis

The supplied raw strip width contributes the loss
`delta^(-stripEpsilon * zeta)`.  This module reserves that loss explicitly
before either restricted-normal geometry is used.
-/

namespace Kakeya.Assouad

/--
After converting fixed `delta`-power losses to the coarse scale through
`scale < delta^(epsilon/10)`, the endpoint line argument retains a strict
`projectionLambda * zeta / 2` margin.

The middle term is the loss from comparing the supplied `rawWidth` with the
common strip width; it may not be omitted by replacing `rawWidth` with `1`.
-/
lemma wz1WideCoarseEndpoint_parameter_gap
    {epsilon eta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (heta : 0 < eta)
    (hetaSmall :
      eta ≤
        epsilon * parameters.projectionLambda *
          parameters.zeta / 100) :
    20 * eta / epsilon +
          10 * parameters.stripEpsilon * parameters.zeta / epsilon +
          parameters.stripEpsilon * eta / 10 <
      parameters.projectionLambda * parameters.zeta / 2 := by
  have hprojectionZeta :
      0 <
        parameters.projectionLambda * parameters.zeta :=
    mul_pos parameters.projectionLambda_pos parameters.zeta_pos
  have hepsilonNonnegative : 0 ≤ epsilon := hepsilon.le
  have hfirst :
      20 * eta / epsilon ≤
        parameters.projectionLambda * parameters.zeta / 5 := by
    have hscaled :
        20 * eta ≤
          20 *
            (epsilon * parameters.projectionLambda *
              parameters.zeta / 100) :=
      mul_le_mul_of_nonneg_left hetaSmall (by norm_num)
    apply (div_le_iff₀ hepsilon).2
    calc
      20 * eta ≤
          20 *
            (epsilon * parameters.projectionLambda *
              parameters.zeta / 100) := hscaled
      _ =
          (parameters.projectionLambda * parameters.zeta / 5) *
            epsilon := by ring
  have hmiddle :
      10 * parameters.stripEpsilon * parameters.zeta / epsilon ≤
        parameters.projectionLambda * parameters.zeta / 10 := by
    apply (div_le_iff₀ hepsilon).2
    calc
      10 * parameters.stripEpsilon * parameters.zeta
          ≤
        10 * (epsilon * parameters.projectionLambda / 100) *
          parameters.zeta := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                parameters.stripEpsilon_le_epsilon_lambda
                (by norm_num))
              parameters.zeta_pos.le
      _ =
          (parameters.projectionLambda * parameters.zeta / 10) *
            epsilon := by ring
  have hstripEpsilonOne :
      parameters.stripEpsilon < 1 :=
    parameters.stripEpsilon_lt_epsilon.trans hepsilonOne
  have hlast :
      parameters.stripEpsilon * eta / 10 ≤
        parameters.projectionLambda * parameters.zeta / 1000 := by
    have hstripEta :
        parameters.stripEpsilon * eta ≤ eta := by
      have hetaNonnegative : 0 ≤ eta := heta.le
      nlinarith [hstripEpsilonOne]
    calc
      parameters.stripEpsilon * eta / 10
          ≤ eta / 10 := by
            exact div_le_div_of_nonneg_right
              hstripEta (by norm_num)
      _ ≤
          (epsilon * parameters.projectionLambda *
            parameters.zeta / 100) / 10 := by
            exact div_le_div_of_nonneg_right
              hetaSmall (by norm_num)
      _ ≤
          parameters.projectionLambda * parameters.zeta / 1000 := by
            have hepsilonLe : epsilon ≤ 1 := hepsilonOne.le
            have hscaled :
                epsilon *
                    (parameters.projectionLambda * parameters.zeta) ≤
                  1 *
                    (parameters.projectionLambda * parameters.zeta) :=
              mul_le_mul_of_nonneg_right hepsilonLe
                hprojectionZeta.le
            calc
              (epsilon * parameters.projectionLambda *
                    parameters.zeta / 100) / 10 =
                  (epsilon *
                    (parameters.projectionLambda * parameters.zeta)) /
                    1000 := by ring
              _ ≤
                  (1 *
                    (parameters.projectionLambda * parameters.zeta)) /
                    1000 := by
                    exact div_le_div_of_nonneg_right
                      hscaled (by norm_num)
              _ =
                  parameters.projectionLambda * parameters.zeta /
                    1000 := by ring
  calc
    20 * eta / epsilon +
          10 * parameters.stripEpsilon * parameters.zeta / epsilon +
          parameters.stripEpsilon * eta / 10
        ≤
      parameters.projectionLambda * parameters.zeta / 5 +
        parameters.projectionLambda * parameters.zeta / 10 +
        parameters.projectionLambda * parameters.zeta / 1000 := by
          linarith
    _ <
      parameters.projectionLambda * parameters.zeta / 2 := by
        nlinarith

/--
Both axial raw-strip leaves may spend
`3 * projectionLambda * zeta / 20` on either the large-width comparison or
the reciprocal perpendicular coefficient.  The remaining losses still fit
strictly below the target `projectionLambda * zeta / 2` margin.
-/
lemma wz1WideCoarseEndpoint_axial_raw_parameter_gap
    {epsilon eta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (heta : 0 < eta)
    (hetaSmall :
      eta ≤
        epsilon * parameters.projectionLambda *
          parameters.zeta / 100) :
    20 * eta / epsilon +
          10 * parameters.stripEpsilon * parameters.zeta / epsilon +
          parameters.stripEpsilon * eta / 10 +
          3 * parameters.projectionLambda * parameters.zeta / 20 <
      parameters.projectionLambda * parameters.zeta / 2 := by
  have hbase :=
    wz1WideCoarseEndpoint_parameter_gap
      parameters hepsilon hepsilonOne heta hetaSmall
  have hprojectionZeta :
      0 <
        parameters.projectionLambda * parameters.zeta :=
    mul_pos parameters.projectionLambda_pos parameters.zeta_pos
  have hfirst :
      20 * eta / epsilon ≤
        parameters.projectionLambda * parameters.zeta / 5 := by
    have hscaled :
        20 * eta ≤
          20 *
            (epsilon * parameters.projectionLambda *
              parameters.zeta / 100) :=
      mul_le_mul_of_nonneg_left hetaSmall (by norm_num)
    apply (div_le_iff₀ hepsilon).2
    calc
      20 * eta ≤
          20 *
            (epsilon * parameters.projectionLambda *
              parameters.zeta / 100) := hscaled
      _ =
          (parameters.projectionLambda * parameters.zeta / 5) *
            epsilon := by ring
  have hmiddle :
      10 * parameters.stripEpsilon * parameters.zeta / epsilon ≤
        parameters.projectionLambda * parameters.zeta / 10 := by
    apply (div_le_iff₀ hepsilon).2
    calc
      10 * parameters.stripEpsilon * parameters.zeta
          ≤
        10 * (epsilon * parameters.projectionLambda / 100) *
          parameters.zeta := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                parameters.stripEpsilon_le_epsilon_lambda
                (by norm_num))
              parameters.zeta_pos.le
      _ =
          (parameters.projectionLambda * parameters.zeta / 10) *
            epsilon := by ring
  have hstripEpsilonOne :
      parameters.stripEpsilon < 1 :=
    parameters.stripEpsilon_lt_epsilon.trans hepsilonOne
  have hlast :
      parameters.stripEpsilon * eta / 10 ≤
        parameters.projectionLambda * parameters.zeta / 1000 := by
    have hstripEta :
        parameters.stripEpsilon * eta ≤ eta := by
      nlinarith [hstripEpsilonOne]
    calc
      parameters.stripEpsilon * eta / 10
          ≤ eta / 10 := by
            exact div_le_div_of_nonneg_right
              hstripEta (by norm_num)
      _ ≤
          (epsilon * parameters.projectionLambda *
            parameters.zeta / 100) / 10 := by
            exact div_le_div_of_nonneg_right
              hetaSmall (by norm_num)
      _ ≤
          parameters.projectionLambda * parameters.zeta / 1000 := by
            have hepsilonLe : epsilon ≤ 1 := hepsilonOne.le
            have hscaled :
                epsilon *
                    (parameters.projectionLambda * parameters.zeta) ≤
                  parameters.projectionLambda * parameters.zeta := by
              nlinarith
            calc
              (epsilon * parameters.projectionLambda *
                    parameters.zeta / 100) / 10 =
                  (epsilon *
                    (parameters.projectionLambda * parameters.zeta)) /
                    1000 := by ring
              _ ≤
                  (parameters.projectionLambda * parameters.zeta) /
                    1000 := by
                    exact div_le_div_of_nonneg_right
                      hscaled (by norm_num)
  calc
    20 * eta / epsilon +
          10 * parameters.stripEpsilon * parameters.zeta / epsilon +
          parameters.stripEpsilon * eta / 10 +
          3 * parameters.projectionLambda * parameters.zeta / 20
        ≤
      parameters.projectionLambda * parameters.zeta / 5 +
        parameters.projectionLambda * parameters.zeta / 10 +
        parameters.projectionLambda * parameters.zeta / 1000 +
        3 * parameters.projectionLambda * parameters.zeta / 20 := by
          linarith
    _ <
      parameters.projectionLambda * parameters.zeta / 2 := by
        nlinarith

/-- Total coarse-scale loss in either axial Frostman scalar leaf. -/
noncomputable def wideCoarseEndpointFrostmanLoss
    {epsilon : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (eta : ℝ) : ℝ :=
  10 * (parameters.workingLambda + eta) / epsilon +
    parameters.stripEpsilon * eta / 10

/-- The axial Frostman loss is nonnegative. -/
lemma wideCoarseEndpoint_frostman_loss_nonnegative
    {epsilon eta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta) :
    0 ≤ wideCoarseEndpointFrostmanLoss parameters eta := by
  dsimp only [wideCoarseEndpointFrostmanLoss]
  have hsum :
      0 ≤ parameters.workingLambda + eta :=
    add_nonneg parameters.workingLambda_pos.le heta.le
  have hfirst :
      0 ≤ 10 * (parameters.workingLambda + eta) / epsilon :=
    div_nonneg (mul_nonneg (by norm_num) hsum) hepsilon.le
  have hsecond :
      0 ≤ parameters.stripEpsilon * eta / 10 :=
    div_nonneg
      (mul_nonneg parameters.stripEpsilon_pos.le heta.le)
      (by norm_num)
  exact add_nonneg hfirst hsecond

/--
In the small-width fixed-angle branch, the `3 * lambda / 20` width gain
strictly pays both the Frostman/retention loss and the target power obtained
from the lower bound `radius ≥ tau`.
-/
lemma wz1WideCoarseEndpoint_frostman_width_parameter_gap
    {epsilon eta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (heta : 0 < eta)
    (hetaSmall :
      eta ≤
        epsilon * parameters.projectionLambda *
          parameters.zeta / 100) :
    wideCoarseEndpointFrostmanLoss parameters eta +
          parameters.zeta *
            (1 - parameters.projectionLambda / 2) <
      3 * parameters.projectionLambda / 20 := by
  let lambda := parameters.projectionLambda
  let zeta := parameters.zeta
  have hlambda : 0 < lambda :=
    parameters.projectionLambda_pos
  have hlambdaOne : lambda ≤ 1 :=
    parameters.projectionLambda_le_one
  have hzeta : 0 < zeta := parameters.zeta_pos
  have hworking :
      10 * parameters.workingLambda / epsilon ≤
        lambda / 10 := by
    apply (div_le_iff₀ hepsilon).2
    calc
      10 * parameters.workingLambda ≤
          10 * (epsilon * lambda / 100) := by
        exact mul_le_mul_of_nonneg_left
          parameters.workingLambda_le_epsilon_projection
          (by norm_num)
      _ = (lambda / 10) * epsilon := by ring
  have hetaLoss :
      10 * eta / epsilon ≤ lambda * zeta / 10 := by
    apply (div_le_iff₀ hepsilon).2
    calc
      10 * eta ≤
          10 * (epsilon * lambda * zeta / 100) := by
        exact mul_le_mul_of_nonneg_left hetaSmall (by norm_num)
      _ = (lambda * zeta / 10) * epsilon := by ring
  have hstripOne : parameters.stripEpsilon < 1 :=
    parameters.stripEpsilon_lt_epsilon.trans hepsilonOne
  have hstripLoss :
      parameters.stripEpsilon * eta / 10 ≤
        lambda * zeta / 1000 := by
    have hstripEta :
        parameters.stripEpsilon * eta ≤ eta := by
      nlinarith
    calc
      parameters.stripEpsilon * eta / 10 ≤ eta / 10 := by
        exact div_le_div_of_nonneg_right hstripEta (by norm_num)
      _ ≤ (epsilon * lambda * zeta / 100) / 10 := by
        exact div_le_div_of_nonneg_right hetaSmall (by norm_num)
      _ ≤ lambda * zeta / 1000 := by
        have hepsilonLe : epsilon ≤ 1 := hepsilonOne.le
        have hlambdaZeta : 0 ≤ lambda * zeta :=
          (mul_pos hlambda hzeta).le
        nlinarith
  have hzetaLambda :
      zeta ≤ lambda / 30 := by
    calc
      zeta ≤ epsilon * lambda / 30 :=
        parameters.zeta_le_epsilon_lambda
      _ ≤ lambda / 30 := by
        have hepsilonLe : epsilon ≤ 1 := hepsilonOne.le
        nlinarith
  have hlambdaZeta :
      lambda * zeta ≤ lambda / 30 := by
    calc
      lambda * zeta ≤ 1 * zeta := by
        exact mul_le_mul_of_nonneg_right hlambdaOne hzeta.le
      _ = zeta := one_mul zeta
      _ ≤ lambda / 30 := hzetaLambda
  have htarget :
      zeta * (1 - lambda / 2) ≤ lambda / 30 := by
    have hfactor : 1 - lambda / 2 ≤ 1 := by linarith
    calc
      zeta * (1 - lambda / 2) ≤ zeta * 1 := by
        exact mul_le_mul_of_nonneg_left hfactor hzeta.le
      _ = zeta := mul_one zeta
      _ ≤ lambda / 30 := hzetaLambda
  dsimp only [wideCoarseEndpointFrostmanLoss]
  have hloss :
      10 * (parameters.workingLambda + eta) / epsilon +
          parameters.stripEpsilon * eta / 10 ≤
        lambda / 10 +
          lambda * zeta / 10 +
          lambda * zeta / 1000 := by
    have hsplit :
        10 * (parameters.workingLambda + eta) / epsilon =
          10 * parameters.workingLambda / epsilon +
            10 * eta / epsilon := by ring
    rw [hsplit]
    linarith
  nlinarith

/-- The target-`< 2` radius gain leaves a much larger `lambda / 2` margin. -/
lemma wz1WideCoarseEndpoint_frostman_radius_parameter_gap
    {epsilon eta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (heta : 0 < eta)
    (hetaSmall :
      eta ≤
        epsilon * parameters.projectionLambda *
          parameters.zeta / 100) :
    wideCoarseEndpointFrostmanLoss parameters eta <
      parameters.projectionLambda / 2 := by
  have hzetaOne : parameters.zeta < 1 :=
    parameters.zeta_lt_one
  have hwidthGap :=
    wz1WideCoarseEndpoint_frostman_width_parameter_gap
      parameters hepsilon hepsilonOne heta hetaSmall
  have hprojection :
      3 * parameters.projectionLambda / 20 <
        parameters.projectionLambda / 2 := by
    nlinarith [parameters.projectionLambda_pos]
  have htargetNonnegative :
      0 ≤
        parameters.zeta *
          (1 - parameters.projectionLambda / 2) := by
    have hfactor :
        0 ≤ 1 - parameters.projectionLambda / 2 := by
      nlinarith [parameters.projectionLambda_le_one]
    exact mul_nonneg parameters.zeta_pos.le hfactor
  linarith

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteToSmoothedThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.LineNonconcentrationProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.OSWCommonSimilarityTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.OSWSupportNormalization
import MyLeanRepo.Kakeya.Assouad.WZ1.QuarterThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.SharpSmoothedFrostman
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedToDiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.ThinTubesLargeDotProduct
import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

/-!
# Shared parameter selection for WZ1 Proposition 8.9
-/

namespace Kakeya.Assouad

private lemma proposition8_9_rpow_neg_mono
    {delta first second : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hfirst : first ≤ second) :
    Kakeya.realRpowENN delta (-first) ≤
      Kakeya.realRpowENN delta (-second) := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge
    hdelta hdelta_one (by linarith)

private lemma proposition8_9_rpow_pos_antitone
    {delta first second : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hfirst : first ≤ second) :
    Kakeya.realRpowENN delta second ≤
      Kakeya.realRpowENN delta first := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one hfirst

private lemma proposition8_9_line_nonconcentration_mono_lambda
    {delta first second zeta : ℝ} {G : DiscreteSet 2}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hfirst : first ≤ second) (hzeta : 0 ≤ zeta)
    (h : WZ1LineNonConcentration delta first zeta G) :
    WZ1LineNonConcentration delta second zeta G := by
  intro normal hnormal t r hdelta_r hr_one
  have hr : 0 ≤ r := hdelta.le.trans hdelta_r
  have hpower :
      Real.rpow delta (-first) ≤ Real.rpow delta (-second) :=
    Real.rpow_le_rpow_of_exponent_ge
      hdelta hdelta_one (by linarith)
  have hbase :
      Real.rpow delta (-first) * r ≤
        Real.rpow delta (-second) * r := by gcongr
  have hbaseNonneg : 0 ≤ Real.rpow delta (-first) * r :=
    mul_nonneg (Real.rpow_nonneg hdelta.le _) hr
  have hrpow :
      Real.rpow (Real.rpow delta (-first) * r) zeta ≤
        Real.rpow (Real.rpow delta (-second) * r) zeta :=
    Real.rpow_le_rpow hbaseNonneg hbase hzeta
  exact (h normal hnormal t r hdelta_r hr_one).trans (by
    apply mul_le_mul_right'
    apply ENNReal.ofReal_mono
    exact hrpow)

theorem wz1_proposition8_9_parameter_selection :
    WZ1Proposition8_9ParameterSelectionStatement := by
  intro hProjection hOSW hStrip epsilon hepsilon hepsilon_tenth
  have hepsilon_one : epsilon / 2 < 1 := by linarith
  rcases
      hProjection hOSW wz1_quarter_thin_tubes
        wz1_thin_tubes_large_dot_product
        wz1_osw_support_normalization
        wz1_osw_common_similarity_transport
        wz1_discrete_to_smoothed_thin_tubes
        wz1_sharp_smoothed_frostman
        wz1_smoothed_to_discrete_thin_tubes
        (epsilon / 2) (by positivity) hepsilon_one with
    ⟨rawLambda, hrawLambda, hProjectionTail⟩
  let projectionLambda := min rawLambda 1
  have hprojectionLambda : 0 < projectionLambda := by
    dsimp only [projectionLambda]
    positivity
  have hprojectionLambdaOne : projectionLambda ≤ 1 := min_le_right _ _
  have hprojectionLambdaRaw : projectionLambda ≤ rawLambda := min_le_left _ _
  let workingLambda :=
    min projectionLambda
      (min (epsilon * projectionLambda / 200) (epsilon / 200))
  have hworking : 0 < workingLambda := by
    dsimp only [workingLambda]
    positivity
  have hworkingProjection : workingLambda ≤ projectionLambda := min_le_left _ _
  have hworkingEpsilonProjection :
      workingLambda ≤ epsilon * projectionLambda / 100 := by
    exact (min_le_right _ _).trans
      ((min_le_left _ _).trans (by nlinarith [hepsilon, hprojectionLambda]))
  have hworkingEpsilon : workingLambda ≤ epsilon / 100 := by
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (by nlinarith [hepsilon]))
  let stripEpsilon := epsilon * projectionLambda / 200
  have hstripEpsilon : 0 < stripEpsilon := by
    dsimp only [stripEpsilon]
    positivity
  have hstripEpsilonLt : stripEpsilon < epsilon := by
    dsimp only [stripEpsilon]
    have hprojectionNonneg : 0 ≤ projectionLambda := hprojectionLambda.le
    nlinarith
  have hstripEpsilonBudget :
      stripEpsilon ≤ epsilon * projectionLambda / 100 := by
    dsimp only [stripEpsilon]
    nlinarith [hepsilon, hprojectionLambda]
  rcases hStrip stripEpsilon hstripEpsilon with
    ⟨stripEta, stripDelta₀, hstripEta, hstripDelta₀,
      hstripDelta₀One, hstripTail⟩
  let zeta :=
    min (1 / 2 : ℝ)
      (min (stripEta / 4)
        (min (epsilon * workingLambda / 60)
          (epsilon * projectionLambda / 60)))
  have hzeta : 0 < zeta := by
    dsimp only [zeta]
    positivity
  have hzetaOne : zeta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hzetaStrip : zeta ≤ stripEta / 2 := by
    exact (min_le_right _ _).trans
      ((min_le_left _ _).trans (by linarith [hstripEta]))
  have hzetaWorking : zeta ≤ epsilon * workingLambda / 30 := by
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_left _ _).trans
          (by nlinarith [hepsilon, hworking])))
  have hzetaProjection : zeta ≤ epsilon * projectionLambda / 30 := by
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          (by nlinarith [hepsilon, hprojectionLambda])))
  rcases hProjectionTail zeta hzeta hzetaOne with
    ⟨rawAlpha, rawProjectionDelta₀, hrawAlpha,
      hrawProjectionDelta₀, hrawProjectionDelta₀One, hprojectionTail⟩
  let alpha := min rawAlpha (zeta * projectionLambda / 32)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  have halphaRaw : alpha ≤ rawAlpha := min_le_left _ _
  have halphaBudget : alpha ≤ zeta * projectionLambda / 16 := by
    exact (min_le_right _ _).trans
      (by nlinarith [hzeta, hprojectionLambda])
  refine ⟨{
    epsilon_le_tenth := hepsilon_tenth
    projectionLambda := projectionLambda
    projectionLambda_pos := hprojectionLambda
    projectionLambda_le_one := hprojectionLambdaOne
    workingLambda := workingLambda
    workingLambda_pos := hworking
    workingLambda_le_projection := hworkingProjection
    workingLambda_le_epsilon_projection := hworkingEpsilonProjection
    workingLambda_le_epsilon := hworkingEpsilon
    stripEpsilon := stripEpsilon
    stripEpsilon_pos := hstripEpsilon
    stripEpsilon_lt_epsilon := hstripEpsilonLt
    stripEpsilon_le_epsilon_lambda := hstripEpsilonBudget
    stripEta := stripEta
    stripEta_pos := hstripEta
    stripDelta₀ := stripDelta₀
    stripDelta₀_pos := hstripDelta₀
    stripDelta₀_le_one := hstripDelta₀One
    strip := hstripTail
    zeta := zeta
    zeta_pos := hzeta
    zeta_lt_one := hzetaOne
    zeta_le_stripEta := hzetaStrip
    zeta_le_epsilon_workingLambda := hzetaWorking
    zeta_le_epsilon_lambda := hzetaProjection
    alpha := alpha
    alpha_pos := halpha
    alpha_le_zeta_projectionLambda := halphaBudget
    projectionDelta₀ := rawProjectionDelta₀
    projectionDelta₀_pos := hrawProjectionDelta₀
    projectionDelta₀_le_one := hrawProjectionDelta₀One
    projection := ?_ }⟩
  intro tau htau htauSmall F G₁ G₂ hF hG₁ hG₂
    hFball hG₁ball hG₂ball hFsep hG₁sep hG₂sep
    hFfrost hG₁frost hG₂frost hstandard hnc₁ hnc₂ H huniform
  have htauOne : tau ≤ 1 := htauSmall.trans hrawProjectionDelta₀One
  have hFraw := hFfrost.mono_const
    (proposition8_9_rpow_neg_mono htau htauOne
      hprojectionLambdaRaw)
  have hG₁raw := hG₁frost.mono_const
    (proposition8_9_rpow_neg_mono htau htauOne
      hprojectionLambdaRaw)
  have hG₂raw := hG₂frost.mono_const
    (proposition8_9_rpow_neg_mono htau htauOne
      hprojectionLambdaRaw)
  have hnc₁Raw := proposition8_9_line_nonconcentration_mono_lambda
    htau htauOne hprojectionLambdaRaw hzeta.le hnc₁
  have hnc₂Raw := proposition8_9_line_nonconcentration_mono_lambda
    htau htauOne hprojectionLambdaRaw hzeta.le hnc₂
  have huniformRaw :
      WZ1UniformTripleDensity
        (Kakeya.realRpowENN tau rawAlpha) F G₁ G₂ H :=
    uniform_triple_density_mono huniform
      (proposition8_9_rpow_pos_antitone
        htau htauOne halphaRaw)
  exact hprojectionTail tau htau htauSmall F G₁ G₂
    hF hG₁ hG₂ hFball hG₁ball hG₂ball
    hFsep hG₁sep hG₂sep hFraw hG₁raw hG₂raw
    hstandard hnc₁Raw hnc₂Raw H huniformRaw

end Kakeya.Assouad

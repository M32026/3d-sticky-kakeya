import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineScalarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectNode6FixedScaleCertified

/-!
# Node 7b: direct affine parameter-Frostman preparation

The public Node-6 output intentionally erases the common-y source provenance
needed by paper Lemma 8.  This proof therefore reruns the existing proof-local
source construction from the Node-5 C2 grains, then applies the synchronized
Mobius rotation, affine-diagonal map, cubical saturation, and one analytic
cleanup.  Every runtime estimate below belongs to that same dependent affine
package.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- The independent Section-7 preparation output, constructed directly from
the C2-grain source rather than reconstructed from the provenance-erased
paper-facing Node-6 configuration. -/
theorem pure_wz2_node7b_preparation
    (h_subunit : PureWZ2SubunitPackageStatement)
    (h_critical : PureWZ2CriticalExtractionStatement)
    (h_propsticky : PureWZ2PropStickyStatement)
    (h_grains : PureWZ2GrainsStatement)
    (h_c2grains : PureWZ2C2GrainsStatement)
    (_h_largeslope : PureWZ2LargeSlopeStatement) :
    PureWZ2ParameterFrostmanPreparationStatement := by
  intro sigma critical analyticLoss scaleCeiling
    hanalyticPos hanalyticSigma hscaleCeiling
  let epsilon : ℝ := analyticLoss / 100000
  have hepsilon : 0 < epsilon := by positivity
  have hepsilonSixtyFourth : epsilon ≤ 1 / 64 := by
    dsimp only [epsilon]
    nlinarith [hanalyticSigma, critical.sigma_lt_one]
  have hC2 : PureWZ2C2GrainsFromCriticalStatement :=
    h_c2grains h_subunit h_critical h_propsticky h_grains
  rcases
      Prop62PaperAudit.V4.Prop62V4DirectNode6FixedScaleCertified.fixedScaleStatement
    with ⟨logExponent, certifiedProvider⟩
  rcases pure_wz2_node7_analytic_cleanup_cutoff
      sigma analyticLoss critical.sigma_pos critical.sigma_lt_one
      hanalyticPos hanalyticSigma with
    ⟨cleanupCutoff⟩
  let finalCeiling : ℝ := min scaleCeiling cleanupCutoff.r₀
  have hfinalCeiling : 0 < finalCeiling := by
    dsimp only [finalCeiling]
    exact lt_min hscaleCeiling cleanupCutoff.r₀_pos
  rcases
      PureWZ2Node7AffineDiagonalPreparationData.pure_wz2_node7_affine_scalar_schedule
        sigma analyticLoss finalCeiling critical.sigma_pos
        critical.sigma_lt_one hanalyticPos hanalyticSigma hfinalCeiling
    with ⟨schedule⟩
  rcases pureWZ2_direct_commonY_source_assembly hC2 certifiedProvider
      sigma critical epsilon schedule.sourceDelta₀ hepsilon
      hepsilonSixtyFourth schedule.sourceDelta₀_pos with
    ⟨sourceDelta, hsourceDelta, hsourceDeltaBound, ⟨commonSource⟩⟩
  have hsourceTwo : 2 < commonSource.commonBand.band.sourceConstant :=
    schedule.sourceConstant_gt_two commonSource hsourceDelta hsourceDeltaBound
  rcases pureWZ2_node7_affine_diagonal_preparation commonSource hsourceTwo with
    ⟨data⟩
  have hfinalCeilingBound : data.finalRadius ≤ finalCeiling :=
    schedule.finalRadius_le data hsourceDelta hsourceDeltaBound
  have hfinalScale : data.finalRadius ≤ scaleCeiling :=
    hfinalCeilingBound.trans (min_le_left _ _)
  have hfinalCleanup : data.finalRadius ≤ cleanupCutoff.r₀ :=
    hfinalCeilingBound.trans (min_le_right _ _)
  have hfinalLtOne : data.finalRadius < 1 :=
    hfinalCleanup.trans_lt <| cleanupCutoff.r₀_le_small.trans_lt (by norm_num)
  have hcwa : WZ2PaperConvexWolffBound data.ordinaryFamily
      (Kakeya.realRpowENN data.finalRadius (-(analyticLoss / 100))) :=
    schedule.ordinary_cwa data hsourceDelta hsourceDeltaBound
  have hdense : data.ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN data.finalRadius (analyticLoss / 100)) :=
    schedule.ordinary_dense data hsourceDelta hsourceDeltaBound
  have hglobalAD := data.localizedShading_global_ad
    critical.sigma_pos critical.sigma_lt_one
  have hconstantTop : data.Node7CubicalGlobalADConstant ≠ ⊤ := by
    unfold PureWZ2Node7AffineDiagonalPreparationData.Node7CubicalGlobalADConstant
      PureWZ2Node7AffineDiagonalPreparationData.Node7CubicalGlobalADProjectionFactor
      PureWZ2Lemma32DerivativeBandAssembly.sourceConstant
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num) (by norm_num)))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  have hprojection : volume
        (twistedUnion data.ordinaryShading data.analysisSlope) ≤
      Kakeya.realRpowENN data.finalRadius (sigma - analyticLoss) :=
    data.ordinaryShading_final_projection_upper_of_budget
      data.Node7CubicalGlobalADConstant (analyticLoss / 200) analyticLoss
      critical.sigma_pos critical.sigma_lt_one hconstantTop
      hglobalAD
      (schedule.final_projection_budget data hsourceDelta hsourceDeltaBound)
  rcases data.toParameterFrostmanPreparation cleanupCutoff hanalyticPos
      hfinalCleanup hcwa hdense hprojection with ⟨preparation⟩
  exact ⟨data.finalRadius, data.finalRadius_pos, hfinalScale,
    hfinalLtOne, ⟨preparation⟩⟩

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RescaledMetricFiber

/-!
# Rescale the chart-selected Proposition 6.3 shading

After choosing the heavier horizontal chart, restrict the source shading to
the retained intervals carrying that chart and refresh its literal/public
unit-rescaled image on the same frozen parent fibre.  This is the single
configuration used by both the global-slab and later local-grain steps.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The source shading retained after selecting one horizontal chart. -/
def Proposition63ChartSelectionData.sourceShading
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    WZ1PaperTubeShading input.fiberFamily.family :=
  proposition63IntervalRestriction input.selectedFiber
    (coarse.tube input.parent) hrho selection.intervals

lemma Proposition63ChartSelectionData.source_sub_commonSlice
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    PaperIsSubshading selection.sourceShading data.commonSlice.shading := by
  apply proposition63IntervalRestriction_sub_commonSlice
  intro interval hinterval
  exact selection.interval_meets interval hinterval

lemma Proposition63ChartSelectionData.source_sub_frozen
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    PaperIsSubshading selection.sourceShading input.sourceFiber :=
  fun index => (selection.source_sub_commonSlice index).trans
    (data.source_subshading index)

/-- The chart-selected source shading and its refreshed literal/public image. -/
structure Proposition63ChartRescaledData
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (outputLoss : ℝ) where
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := initial.incidence)
    selection.sourceShading sigma
    (Kakeya.realRpowENN delta (-localLoss))
    (Real.toNNReal coefficient)
  literalImage : WZ2PaperLiteralUnitRescaledShadingData
    input.frozenRescaled.familyData selection.sourceShading
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss
    input.frozenRescaled.rescalingCertificate.publicFamily
    (input.frozenRescaled.rescalingCertificate.publicShading
      literalImage.targetShading)
  source_mass :
    (sourceDensity / 2) * input.fiberFamily.family.enncard *
        Kakeya.realRpowENN delta 2 ≤ selection.sourceShading.mass

theorem proposition63_chart_rescaled
    {delta rho Delta sigma stickyLoss localLoss targetLoss outputLoss
      coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoOne : rho ≤ 1)
    (hscaleSmall : delta / rho ≤ 1 / 24)
    (hloss : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdensityAbsorb :
      Kakeya.realRpowENN (delta / rho) outputLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * (sourceDensity / 2)) :
    Nonempty (Proposition63ChartRescaledData selection outputLoss) := by
  let selected := selection.sourceShading
  have hsourceMass :
      (sourceDensity / 2) * input.fiberFamily.family.enncard *
          Kakeya.realRpowENN delta 2 ≤ selected.mass := by
    calc
      (sourceDensity / 2) * input.fiberFamily.family.enncard *
          Kakeya.realRpowENN delta 2 =
        (1 / 2 : ENNReal) *
          (sourceDensity * input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) := by
        simp only [div_eq_mul_inv, one_mul]
        ac_rfl
      _ ≤ (1 / 2 : ENNReal) * data.commonSlice.shading.mass := by
        gcongr
        exact data.commonSlice.retained_mass
      _ ≤ selected.mass := selection.half_commonSlice_mass_le_restriction
  let localGrains := data.localGrains.restrict selection.source_sub_commonSlice
  rcases proposition63_literal_unit_rescaled_shading input selected
      hrhoOne hscaleSmall with ⟨literalImage⟩
  have hextremal := rescaledSubfiber_extremal_of_source_density
    input.frozenRescaled selection.source_sub_frozen literalImage
    (sourceDensity / 2) hsourceMass hloss houtputLoss hscaleSmall
    hdensityAbsorb
  exact ⟨{
    localGrains := localGrains
    literalImage := literalImage
    extremal := hextremal
    source_mass := hsourceMass
  }⟩

namespace Proposition63ChartRescaledData

/-- Regard the refreshed literal image and its rebuilt extremality as a full
rescaled-fibre output on the same frozen family and rescaling certificate.
This changes only the source shading and literal image; all geometric
provenance remains the one supplied by the first sticky application. -/
noncomputable def refreshedFullFiberOutput
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    {selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio}
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss) :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      selection.sourceShading (coarse.tube input.parent) hrho where
  familyData := input.frozenRescaled.familyData
  literalShading := rescaled.literalImage
  jacobianConstant := input.frozenRescaled.jacobianConstant
  jacobianConstant_one := input.frozenRescaled.jacobianConstant_one
  jacobianConstant_finite :=
    input.frozenRescaled.jacobianConstant_finite
  rescalingCertificate := input.frozenRescaled.rescalingCertificate
  extremal := rescaled.extremal
  source_cardinality_eq := input.frozenRescaled.source_cardinality_eq

/-- The public target shading is only a reindexing of the literal shading. -/
def publicShading
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    {selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio}
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss) :
    WZ1PaperTubeShading
      input.frozenRescaled.rescalingCertificate.publicFamily :=
  input.frozenRescaled.rescalingCertificate.publicShading
    rescaled.literalImage.targetShading

@[simp] theorem publicShading_union_eq
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    {selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio}
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss) :
    rescaled.publicShading.union = rescaled.literalImage.targetShading.union :=
  input.frozenRescaled.rescalingCertificate.publicShading_union_eq
    rescaled.literalImage.targetShading

end Proposition63ChartRescaledData

end Kakeya.Assouad.PureWZ2

end

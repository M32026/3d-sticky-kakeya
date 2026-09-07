import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureNearbyFiniteVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperADScaleRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RescaledFiberLocalConfig
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRootCover

/-!
# The actual nearby cover used after the Proposition 6.3 chart normalization

The paper requests a cover at the distinguished scale `Delta`, but literal
Definition 2.12 returns an actual radius only known to be at least `Delta`
and within its prescribed multiplicative window.  This module records that
distinction on the normalized public rescaled fibre.  It also raises the
minimum scale in the already-proved exact-slice AD estimate from `Delta` to
the actual radius.

No exact-scale replacement of the nearby witness is made.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

namespace Proposition63ChartSelectionData

variable
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

/-- The whole public family after applying the one global horizontal chart. -/
def normalizedFamily
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss) :
    Kakeya.Streamlined.TubeFamily (delta / rho) :=
  transportFamily selection.chartLabel.chart.isometry
    input.frozenRescaled.rescalingCertificate.publicFamily

/-- The charted public shading on the same normalized public family. -/
def normalizedShading
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss) :
    WZ1PaperTubeShading (selection.normalizedFamily rescaled) :=
  selection.chartLabel.chart.transportPaperShading rescaled.publicShading

/-- The rescaled fine radius `delta / rho` is at most the paper-requested
coarse scale `Delta`. -/
lemma rescaledFine_le_Delta
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta) :
    delta / rho ≤ Delta := by
  rw [hrhoDelta, div_le_iff₀ hDelta]
  simpa [pow_two] using hdeltaDelta

/-- `Delta` as a legal requested scale for the normalized `delta / rho`
family. -/
def requestedDelta
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta) :
    WZ2PaperRequestedScale (delta / rho) :=
  ⟨Delta, selection.rescaledFine_le_Delta hrhoDelta,
    hDeltaSmall.trans (by norm_num)⟩

/-- The normalized family remains in the fixed paper line class. -/
lemma normalizedFamily_lineClass
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss) :
    WZ1PaperIsLineClass (selection.normalizedFamily rescaled) := by
  simpa [normalizedFamily] using
    selection.chartLabel.chart.transportFamily_lineClass
      input.frozenRescaled.rescalingCertificate.publicFamily
      (input.frozenRescaled.rescalingCertificate.publicFamily_line_class
        input.frozenRescaled.familyData.target_line_class)

/-- Exact literal-image axis provenance survives the public reindexing and
the selected horizontal chart.  Thus every tube in the first charted family
has the sharp positive vertical-direction margin `sqrt 3 / 2`. -/
lemma normalizedFamily_direction_vertical
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (hrhoOne : rho ≤ 1) :
    ∀ index, Real.sqrt 3 / 2 ≤
      wz1PaperDirection ((selection.normalizedFamily rescaled).tube index)
        (2 : Fin 3) := by
  intro index
  let certificate := input.frozenRescaled.rescalingCertificate
  let literal := input.frozenRescaled.familyData
  let literalIndex := certificate.section6Index.symm index
  have hsection : certificate.section6Index literalIndex = index :=
    certificate.section6Index.apply_symm_apply index
  have hpublicLine : WZ1PaperTubeInLineClass
      (certificate.publicFamily.tube index) :=
    certificate.publicFamily_line_class literal.target_line_class index
  have hliteralLine : WZ1PaperTubeInLineClass
      (literal.targetFamily.tube literalIndex) :=
    literal.target_line_class literalIndex
  have hpublicAxis :
      tubeAxisLine (certificate.publicFamily.tube index) =
        tubeAxisLine (literal.targetFamily.tube literalIndex) := by
    rw [← hsection]
    exact certificate.same_axis literalIndex
  have hpublicDirection :
      wz1PaperDirection (certificate.publicFamily.tube index) =
        wz1PaperDirection (literal.targetFamily.tube literalIndex) :=
    paperDirection_eq_of_same_axis hpublicLine hliteralLine hpublicAxis
  have hsourceLine : WZ1PaperTubeInLineClass
      (input.fiberFamily.family.tube (literal.sourceIndex literalIndex)) :=
    cover.fine_line_class.subfamily input.fiberFamily
      (literal.sourceIndex literalIndex)
  have hcovered : WZ1PaperTubeCovers
      (input.fiberFamily.family.tube (literal.sourceIndex literalIndex))
      (coarse.tube input.parent) := by
    rw [input.fiberFamily.tube_eq]
    apply (mem_wz2PaperFullFiberIndices_iff input.parent
      (input.fiberFamily.embedding (literal.sourceIndex literalIndex))).mp
    exact Finset.orderEmbOfFin_mem _ _ _
  have hliteralVertical : Real.sqrt 3 / 2 ≤
      wz1PaperDirection (literal.targetFamily.tube literalIndex)
        (2 : Fin 3) :=
    literal_target_paperDirection_vertical_ge_sqrt_three_half
      hrho hrhoOne hsourceLine hcovered hliteralLine
      (literal.target_axis literalIndex)
  change Real.sqrt 3 / 2 ≤
    wz1PaperDirection
      (transportTube selection.chartLabel.chart.isometry
        (certificate.publicFamily.tube index)) 2
  rw [selection.chartLabel.chart.paperDirection_transportTube,
    selection.chartLabel.chart.isometry_preserves_coord2, hpublicDirection]
  exact hliteralVertical

/-- Cropped extremality and its nearby-scale CWA are transported together
with the whole public configuration. -/
lemma normalizedExtremal
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss) :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      (selection.normalizedFamily rescaled)
      (selection.normalizedShading rescaled) := by
  simpa [normalizedFamily, normalizedShading,
      Proposition63ChartRescaledData.publicShading] using
    selection.chartLabel.chart.transportPaperCroppedExtremal
      rescaled.extremal

/-- The exact actual nearby witness selected at requested scale `Delta`,
together with the global-slice AD estimate at that actual radius. -/
structure Proposition63NearbyCoverData
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta) where
  nearby : WZ2PaperPureNearbyScaleCoverData
    (selection.normalizedFamily rescaled)
    (selection.requestedDelta hrhoDelta)
    (Kakeya.realRpowENN (delta / rho) (-outputLoss))
  global_ad : ∀ height : ℝ,
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (slopes.slope (100 * height)))
        (horizontalSlice
          (selection.chartLabel.chart.transportPaperShading
            rescaled.publicShading).union height))
      nearby.rho (1 - sigma)
      ((2 * (Nat.ceil
          (proposition63ExactSliceError delta rho Delta coefficient / Delta) +
        1) : ENNReal) ^ 2 *
          (204 * (1 + proposition63SlabADConstant delta localLoss)))

namespace Proposition63NearbyCoverData

/-- The actual cover radius is no smaller than the requested `Delta`. -/
lemma Delta_le_actual
    {selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio}
    {outputLoss : ℝ}
    {rescaled : Proposition63ChartRescaledData selection outputLoss}
    {slopes : Proposition63SlopeData selection}
    {hrhoDelta : rho = Delta}
    (nearbyData : Proposition63NearbyCoverData
      selection rescaled slopes hrhoDelta) :
    Delta ≤ nearbyData.nearby.rho := by
  simpa [requestedDelta] using nearbyData.nearby.requested_le

/-- The actual radius is positive, without identifying it with `Delta`. -/
lemma actual_pos
    {selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio}
    {outputLoss : ℝ}
    {rescaled : Proposition63ChartRescaledData selection outputLoss}
    {slopes : Proposition63SlopeData selection}
    {hrhoDelta : rho = Delta}
    (nearbyData : Proposition63NearbyCoverData
      selection rescaled slopes hrhoDelta) :
    0 < nearbyData.nearby.rho :=
  nearbyData.nearby.scaleData.rho_pos

end Proposition63NearbyCoverData

/-- Select the literal nearby witness supplied by Definition 2.12 and
coarsen the minimum scale of the exact-slice AD estimate to its actual
radius. -/
theorem proposition63_nearby_cover
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63NearbyCoverData
      selection rescaled slopes hrhoDelta) := by
  let nearby : WZ2PaperPureNearbyScaleCoverData
      (selection.normalizedFamily rescaled)
      (selection.requestedDelta hrhoDelta)
      (Kakeya.realRpowENN (delta / rho) (-outputLoss)) :=
    (selection.normalizedExtremal rescaled).cwa_nearby_scales.chosenNearby
      (selection.requestedDelta hrhoDelta)
  have hglobal : ∀ height : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (slopes.slope (100 * height)))
          (horizontalSlice
            (selection.chartLabel.chart.transportPaperShading
              rescaled.publicShading).union height))
        nearby.rho (1 - sigma)
        ((2 * (Nat.ceil
            (proposition63ExactSliceError delta rho Delta coefficient / Delta) +
          1) : ENNReal) ^ 2 *
            (204 * (1 + proposition63SlabADConstant delta localLoss))) := by
    intro height
    have hAD := selection.normalized_public_horizontal_slice_ad
      rescaled slopes hrhoDelta hsigma hsigmaOne height
    exact paper_ad_coarsen_minimum_scale hAD nearby.requested_le
  exact ⟨{ nearby := nearby, global_ad := hglobal }⟩

end Proposition63ChartSelectionData

end Kakeya.Assouad.PureWZ2

end

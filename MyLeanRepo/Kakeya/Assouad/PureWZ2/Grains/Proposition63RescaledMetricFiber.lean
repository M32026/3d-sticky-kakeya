import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MetricFiberInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RescaledSubfiberTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageCarrier

/-!
# Rescale the retained Proposition 6.3 metric fibre

Refresh the literal cubical image shading on the frozen Node 3 target family
and reuse its public rescaling certificate.  The selected source-fibre density
and one explicit power absorption produce the rescaled extremal pair.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The refreshed rescaled shading and its cropped extremality. -/
structure Proposition63RescaledMetricFiberData
    {delta rho sigma stickyLoss localLoss targetLoss coefficient : ℝ}
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
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) where
  literalImage : WZ2PaperLiteralUnitRescaledShadingData
    input.frozenRescaled.familyData input.selectedFiber
  publicShading : WZ1PaperTubeShading
    input.frozenRescaled.rescalingCertificate.publicFamily :=
    input.frozenRescaled.rescalingCertificate.publicShading
      literalImage.targetShading
  extremal : WZ2PaperCroppedIsExtremal sigma targetLoss
    input.frozenRescaled.rescalingCertificate.publicFamily publicShading

/-- Refresh the literal cubical image of any further shading refinement on
the same selected metric fibre, without changing the frozen target family or
the frozen public rescaling certificate. -/
theorem proposition63_literal_unit_rescaled_shading
    {delta rho sigma stickyLoss localLoss coefficient : ℝ}
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
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho)
    (selected : WZ1PaperTubeShading input.fiberFamily.family)
    (hrhoOne : rho ≤ 1)
    (hscaleSmall : delta / rho ≤ 1 / 24) :
    Nonempty (WZ2PaperLiteralUnitRescaledShadingData
      input.frozenRescaled.familyData selected) := by
  have hsourceLine : WZ1PaperIsLineClass input.fiberFamily.family :=
    cover.fine_line_class.subfamily input.fiberFamily
  have hanchorLine : WZ1PaperTubeInLineClass (coarse.tube input.parent) :=
    cover.coarse_line_class input.parent
  have hcovered : ∀ source : Fin input.fiberFamily.family.card,
      WZ1PaperTubeCovers (input.fiberFamily.family.tube source)
        (coarse.tube input.parent) := by
    intro source
    rw [input.fiberFamily.tube_eq source]
    apply (mem_wz2PaperFullFiberIndices_iff input.parent
      (input.fiberFamily.embedding source)).mp
    change (Finset.orderEmbOfFin
      (wz2PaperFullFiberIndices fine coarse input.parent) rfl source) ∈
        wz2PaperFullFiberIndices fine coarse input.parent
    exact Finset.orderEmbOfFin_mem
      (wz2PaperFullFiberIndices fine coarse input.parent) rfl source
  exact wz2_paper_literal_unit_rescaled_shading
    wz2_paper_literal_image_carrier hdelta hrho hrhoOne hscaleSmall
    hsourceLine hanchorLine hcovered input.frozenRescaled.familyData selected

/-- Build the refreshed literal image and recover extremality from the
selected source-fibre density. -/
theorem proposition63_rescaled_metric_fiber
    {delta rho sigma stickyLoss localLoss targetLoss coefficient : ℝ}
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
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho)
    (sourceDensity : ENNReal)
    (hsourceDensity : sourceDensity * input.fiberFamily.family.enncard *
        Kakeya.realRpowENN delta 2 ≤ input.selectedFiber.mass)
    (hloss : stickyLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho ≤ 1)
    (hscaleSmall : delta / rho ≤ 1 / 24)
    (hdensityAbsorb :
      Kakeya.realRpowENN (delta / rho) targetLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity) :
    Nonempty (Proposition63RescaledMetricFiberData
      (targetLoss := targetLoss) input) := by
  rcases proposition63_literal_unit_rescaled_shading input
      input.selectedFiber hrhoOne hscaleSmall with
    ⟨literalImage⟩
  have hextremal := rescaledSubfiber_extremal_of_source_density
    input.frozenRescaled input.source_subshading literalImage
    sourceDensity hsourceDensity hloss htargetLoss hscaleSmall
    hdensityAbsorb
  exact ⟨{ literalImage := literalImage, extremal := hextremal }⟩

end Kakeya.Assouad.PureWZ2

end

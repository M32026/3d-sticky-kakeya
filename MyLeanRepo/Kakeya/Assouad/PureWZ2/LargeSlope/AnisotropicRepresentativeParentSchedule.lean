import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperCleanupSourceRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicTubeParameterForward
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RepresentativeParentCover

/-!
# Representative-parent schedule for the exact Proposition 6.5 map

After the centered target cleanup and the second source regularization, the
source and target families have the same index type.  At each source nearby
scale we choose one synchronized target representative over every complete
source fiber and enlarge its canonical centered segment by the exact amount
needed for strict containment.

This is still preliminary data: the parent axes are separated simultaneously
by `PureWZ2FiniteRepresentativeParentScheduleData.simultaneouslySeparate`
before public Definition 2.12 covers are formed.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Absolute target parent radius attached to a source parent scale. -/
def anisotropicRepresentativeParentScale
    (targetDelta sourceRho : ℝ) : ℝ :=
  3600000 * sourceRho + targetDelta

/-- Exact source-fiber line-distance budget for the triangular map. -/
def anisotropicRepresentativeLineBound (sourceRho : ℝ) : ℝ :=
  2400000 * sourceRho

/-- One source public scale produces one preliminary exact-triangular target
parent cover on the synchronized target family. -/
noncomputable def anisotropicRepresentativeParentData
    {sourceDelta sourceRho targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {cleanupConstant sourceNearbyConstant scheduleConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw cleanupConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant scheduleConstant sourceNormalization levelCount)
    {sourceScaleConstant : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData
      data.selected.family sourceRho sourceScaleConstant)
    (hg : g.IsNormalized)
    (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hmOne : m ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    (hsourceLine : WZ1PaperIsLineClass data.selected.family)
    (hsourceBase : ∀ source,
      ‖(data.selected.family.tube source).base‖ ≤ 5) :
    PureWZ2RepresentativeParentCoverData
      (targetRho :=
        anisotropicRepresentativeParentScale targetDelta sourceRho)
      (lineBound := anisotropicRepresentativeLineBound sourceRho)
      sourceScale
      (PureWZ2ExternalWeightRegularizationData.anisotropicCleanupTargetSubfamily
        data).family
      (Equiv.refl (Fin data.selected.family.card)) := by
  let targetFine :=
    (PureWZ2ExternalWeightRegularizationData.anisotropicCleanupTargetSubfamily
      data).family
  refine
    { source_nonempty := data.selected_nonempty
      target_delta_pos := htargetDelta
      target_rho_pos := ?_
      target_line_class := data.anisotropicCleanupTarget_line_class
      target_ordinary_distinct := data.anisotropicCleanupTarget_distinct
      target_midpoint_local := data.anisotropicCleanupTarget_midpoint_local
      target_packing_distinct := by
        have hpacking :=
          data.anisotropicCleanupTarget_centeredPacking_paper_distinct
            htargetDelta
        intro first second hne
        have hraw := hpacking first second hne
        change (2 / 3 : ℝ) * targetDelta <
          wz1PaperLineDistance
            (wz2PaperRelabelTube (targetFine.tube first))
            (wz2PaperRelabelTube (targetFine.tube second))
        change (2 / 3 : ℝ) * targetDelta <
          wz1PaperLineDistance
            (wz2PaperRelabelTube
              (pureWZ2PaperCenteredTube (targetFine.tube first)))
            (wz2PaperRelabelTube
              (pureWZ2PaperCenteredTube (targetFine.tube second))) at hraw
        rw [wz2PaperRelabelTube_lineDistance_both] at hraw ⊢
        rw [pureWZ2PaperCenteredTube_lineDistance _ _
          (data.anisotropicCleanupTarget_line_class first)
          (data.anisotropicCleanupTarget_line_class second)] at hraw
        exact hraw
      target_carrier_subset_relabel := by
        intro rho hrho first second hbudget
        have hcontain := pureWZ2_centered_carrier_subset_relabel_of_lineDistance
          htargetDelta hrho (targetFine.tube first) (targetFine.tube second)
          hbudget
        rw [data.anisotropicCleanupTarget_centered first,
          data.anisotropicCleanupTarget_centered second] at hcontain
        exact hcontain
      common_source_parent_lineDistance := ?_
      containment_budget := ?_ }
  · unfold anisotropicRepresentativeParentScale
    nlinarith [sourceScale.rho_pos]
  · intro first second hparent
    change wz1PaperLineDistance
        (targetFine.tube first) (targetFine.tube second) ≤
      anisotropicRepresentativeLineBound sourceRho
    unfold anisotropicRepresentativeLineBound
    exact anisotropic_recentered_lineDistance_le_of_same_source_fiber
      (targetDelta := targetDelta) g c d m center hg hcd hdc hsub hm hmOne
      sourceScale hsourceDeltaRho
      (targetFine := targetFine) (Equiv.refl _) hsourceLine hsourceBase
      data.anisotropicCleanupTarget_line_class
      data.anisotropicCleanupTarget_axis_source first second hparent
  · unfold anisotropicRepresentativeParentScale
      anisotropicRepresentativeLineBound
    linarith

/-- Package every finite source nearby-scale witness as a preliminary
representative-axis target cover. -/
noncomputable def anisotropicRepresentativeParentSchedule
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {cleanupConstant sourceNearbyConstant scheduleConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw cleanupConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant scheduleConstant sourceNormalization levelCount)
    (hg : g.IsNormalized)
    (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hmOne : m ≤ 1)
    (htargetDelta : 0 < targetDelta)
    {sourceScaleConstant parentScheduleConstant : ENNReal}
    {parentLevelCount : ℕ}
    (sourceSchedule : PureWZ2FiniteNearbyScheduleData
      (family := data.selected.family) sourceScaleConstant
        parentScheduleConstant parentLevelCount)
    (hsourceLine : WZ1PaperIsLineClass data.selected.family)
    (hsourceBase : ∀ source,
      ‖(data.selected.family.tube source).base‖ ≤ 5) :
    PureWZ2FiniteRepresentativeParentScheduleData
      (PureWZ2ExternalWeightRegularizationData.anisotropicCleanupTargetSubfamily
        data).family
      (Equiv.refl (Fin data.selected.family.card))
      sourceScaleConstant sourceSchedule.scaleCount where
  sourceRho coordinate :=
    (sourceSchedule.witness coordinate).rho
  targetRho coordinate :=
    anisotropicRepresentativeParentScale targetDelta
      (sourceSchedule.witness coordinate).rho
  lineBound coordinate :=
    anisotropicRepresentativeLineBound
      (sourceSchedule.witness coordinate).rho
  sourceScale coordinate :=
    (sourceSchedule.witness coordinate).scaleData
  parentData coordinate :=
    anisotropicRepresentativeParentData data
      (sourceSchedule.witness coordinate).scaleData
      hg hdc hsub hmOne htargetDelta
      ((sourceSchedule.requested coordinate).2.1.trans
        (sourceSchedule.witness coordinate).requested_le)
      hsourceLine hsourceBase

end Kakeya.Assouad

end

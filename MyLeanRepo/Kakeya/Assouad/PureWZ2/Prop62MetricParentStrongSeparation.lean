import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperSchedule

/-!
# Proposition 6.2 final metric-parent strong separation

The proxy residue selection separates distinct occupied line-parameter cells
before the final quotient cleanup.  This module records the resulting
`1600 * rho` line separation on the exact final coarse family.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62ProxySelectedMeshCells

/--
The selected proxy mesh is separated beyond the literal doubled-fiber
threshold when its residue stride has the corresponding factor-six margin.
-/
theorem coarse_strongly_separated
    {delta scale proxyScale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {proxyTube : Fin oldData.coarse.card → Kakeya.DeltaTube proxyScale}
    {width : ℝ}
    (mesh :
      PureWZ2Prop62ProxySelectedMeshCells
        (rho := rho) oldData proxyTube width)
    (proxyLine :
      ∀ parent, WZ1PaperTubeInLineClass (proxyTube parent))
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (proxyTube first) =
          pureWZ2Prop62LineColor width stride
            (proxyTube second))
    (strongSeparation :
      9600 * rho < ((stride : ℝ) - 1) * width) :
    ∀ first second, first ≠ second →
      1600 * rho <
        wz1PaperLineDistance
          (mesh.coarse.tube first) (mesh.coarse.tube second) := by
  intro first second distinct
  let firstCell := (mesh.cellEquiv first).1
  let secondCell := (mesh.cellEquiv second).1
  have firstCellMem : firstCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv first).2
  have secondCellMem : secondCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv second).2
  have firstRepresentative :=
    mesh.representative_mem firstCell firstCellMem
  have secondRepresentative :=
    mesh.representative_mem secondCell secondCellMem
  have cellNe : firstCell ≠ secondCell := by
    intro equality
    apply distinct
    apply mesh.cellEquiv.injective
    exact Subtype.ext equality
  have colorEq :=
    sameColor
      (mesh.representative firstCell)
      (mesh.representative secondCell)
      firstRepresentative.1 secondRepresentative.1
  have representativeSeparated :=
    pureWZ2_prop62_sameLineColor_distinctCell_separated
      widthPos
      (proxyTube (mesh.representative firstCell))
      (proxyTube (mesh.representative secondCell))
      (proxyLine _) (proxyLine _) colorEq <| by
        rw [firstRepresentative.2, secondRepresentative.2]
        exact cellNe
  change
    1600 * rho <
      wz1PaperLineDistance
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (proxyTube (mesh.representative firstCell)))
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (proxyTube (mesh.representative secondCell)))
  rw [wz1PaperLineDistance_centeredLineTube_both
    (proxyLine _) (proxyLine _)]
  nlinarith

end PureWZ2Prop62ProxySelectedMeshCells

namespace PureWZ2Prop62ProxyQuotientMetricCoreOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

/--
The exact final coarse family retains the strong separation of the selected
proxy mesh.
-/
theorem finalMetricParents_strongly_separated
    (fineLine : WZ1PaperIsLineClass fine)
    (widthPos : 0 < width)
    (strongSeparation :
      9600 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width) :
    ∀ first second, first ≠ second →
      1600 * rho <
        wz1PaperLineDistance
          (output.restriction.coarseSelected.family.tube first)
          (output.restriction.coarseSelected.family.tube second) := by
  have sameColor :
      ∀ first second,
        first ∈ output.metric.mesh.selectedParents →
        second ∈ output.metric.mesh.selectedParents →
        pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate first) =
          pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate second) := by
    intro first second firstMem secondMem
    rw [output.metric.mesh_selectedParents_eq,
      output.metric.selectedParents_eq] at firstMem secondMem
    rcases Finset.mem_image.mp firstMem with
      ⟨firstSource, firstSourceMem, firstEq⟩
    rcases Finset.mem_image.mp secondMem with
      ⟨secondSource, secondSourceMem, secondEq⟩
    have firstResidue :=
      output.metric.selection.selected_residue
        firstSource firstSourceMem
    have secondResidue :=
      output.metric.selection.selected_residue
        secondSource secondSourceMem
    simpa only [firstEq, secondEq] using
      firstResidue.trans secondResidue.symm
  have metricStronglySeparated :
      ∀ first second, first ≠ second →
        1600 * rho <
          wz1PaperLineDistance
            (output.metric.metricParents.tube first)
            (output.metric.metricParents.tube second) := by
    change
      ∀ first second, first ≠ second →
        1600 * rho <
          wz1PaperLineDistance
            (output.metric.metricInput.coarse.tube first)
            (output.metric.metricInput.coarse.tube second)
    rw [output.metric.metric_coarse_eq]
    exact
      output.metric.mesh.coarse_strongly_separated
        (schedule.coordinateProxyTube_lineClass
          fineNonempty fineLine packetCoordinate)
        widthPos (strideBase + 1) sameColor strongSeparation
  intro first second distinct
  have ambientDistinct :
      output.restriction.coarseSelected.embedding first ≠
        output.restriction.coarseSelected.embedding second :=
    output.restriction.coarseSelected.embedding.injective.ne distinct
  simpa only [
    output.restriction.coarseSelected.tube_eq
  ] using
    metricStronglySeparated
      (output.restriction.coarseSelected.embedding first)
      (output.restriction.coarseSelected.embedding second)
      ambientDistinct

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalHeightLift
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalOneScaleAssembly

/-!
# Same-extremizer assembly from the source height lift

The weighted graph argument supplies mass only through the auxiliary rich
spatial shading.  `PureWZ2SourceAlternativeAHeightLift` contains that shading
but is defined solely by rich heights on complete source `delta`-cells.  This
module applies the Node-4 refinement to that height-only source shading and
assembles all final fields on the resulting single dependent configuration.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

theorem PureWZ2SourceAlternativeAHeightLift.toOneScaleOfGrainProducer
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready outputLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    {richTrapezoid :
      PureWZ2SourceAlternativeARichTrapezoid richShading}
    (heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralOutput : structuralLoss ≤ outputLoss)
    (grainProducer :
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        ∀ shading : WZ1PaperTubeShading family,
          WZ1PaperIsLineClass family →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss family shading →
            Nonempty
              (PureWZ2GrainRefinementData
                shading sigma outputLoss))
    (hdenseBudget :
      (54 * (wz1Lemma23SnappedHeights graph.residue.cells).card : ENNReal) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
          twoScale.coarse.balanced.incidenceMass) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source outputLoss richTrapezoid.scale) := by
  let factor : ENNReal :=
    54 * (wz1Lemma23SnappedHeights graph.residue.cells).card
  have hheightsNonempty :
      (wz1Lemma23SnappedHeights graph.residue.cells).Nonempty := by
    rcases richCells.graphCells_nonempty with ⟨cell, hcell⟩
    exact ⟨cell.2.2, Finset.mem_image.mpr
      ⟨cell, richCells.graphCells_subset hcell, rfl⟩⟩
  have hfactorZero : factor ≠ 0 := by
    apply ne_of_gt
    dsimp only [factor]
    positivity
  have hfactorTop : factor ≠ ⊤ := by
    dsimp only [factor]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hrichDense :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        richShading.shading.mass := by
    apply (ENNReal.mul_le_mul_iff_right hfactorZero hfactorTop).mp
    calc
      factor * (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
          ((rich.heightIndices.card * graph.residue.cells.card : ℕ) :
            ENNReal) * twoScale.coarse.balanced.incidenceMass := by
        simpa [factor, mul_comm, mul_left_comm, mul_assoc] using hdenseBudget
      _ ≤ factor * richShading.shading.mass := by
        simpa [factor, mul_comm, mul_left_comm, mul_assoc] using
          richShading.graph_weighted_mass_lower
  have hliftDense :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        heightLift.shading.mass :=
    hrichDense.trans heightLift.mass_lower
  have hsourceStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hliftStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family heightLift.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := heightLift.whole_cells
      dense := hliftDense
      volume_upper :=
        (measure_mono heightLift.subshading.union_subset).trans
          hsourceStructural.volume_upper }
  rcases grainProducer source.family heightLift.shading
      source.line_class hliftStructural with ⟨refined⟩
  have hsub :
      PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro index point hpoint
    exact heightLift.subshading index
      (refined.subshading index hpoint)
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one
      (hinputStructural.trans hstructuralOutput)
  have hconstantTop :
      Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    hsub hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict
    hsub hconstant hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ refined.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, hsub.union_subset point.property⟩
  let trapezoids : Finset WZ1VerticalTrapezoid :=
    {richTrapezoid.trapezoid}
  have hdeltaScale : delta ≤ richTrapezoid.scale := by
    calc
      delta ≤ prep.graphScale := prep.sourceScale_le_graphScale
      _ ≤ 5 * prep.graphScale := by nlinarith [prep.graphScale_pos]
      _ = richTrapezoid.scale := richTrapezoid.scale_eq.symm
  exact ⟨{
    rho_pos := richTrapezoid.scale_pos
    delta_le_rho := hdeltaScale
    rho_le_one := richTrapezoid.scale_le_one
    shading := refined.shading
    subshading := hsub
    whole_cells := refined.cubical
    extremal := refined.extremal
    volume_lower := refined.volume_lower
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    globalGrains := globalGrains
    slope_eq := rfl
    trapezoids := trapezoids
    trapezoids_nonempty := by simp [trapezoids]
    height_eq := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact richTrapezoid.height_eq
    slope_bound := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact richTrapezoid.length_bounds
    separated_cores := by
      intro first hfirst second hsecond hne
      simp only [trapezoids, Finset.mem_singleton] at hfirst hsecond
      exact False.elim (hne (hfirst.trans hsecond.symm))
    slope_approximation := by
      intro trapezoid htrapezoid z _hz hslice
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      apply heightLift.slope_approximation z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
    active_height_coverage := by
      intro z _hz hslice
      refine ⟨richTrapezoid.trapezoid, by simp [trapezoids], ?_⟩
      apply heightLift.active_height_coverage z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
  }⟩

end Kakeya.Assouad

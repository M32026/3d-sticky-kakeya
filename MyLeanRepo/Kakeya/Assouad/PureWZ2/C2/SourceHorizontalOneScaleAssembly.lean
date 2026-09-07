import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRichTrapezoid

/-!
# Same-configuration Pure one-scale assembly from a rich source shading
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

theorem PureWZ2SourceAlternativeARichTrapezoid.toOneScale
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
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
    (richTrapezoid :
      PureWZ2SourceAlternativeARichTrapezoid richShading)
    (hloss : inputLoss ≤ outputLoss)
    (hdense :
      Kakeya.realRpowENN delta outputLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        richShading.shading.mass)
    (hvolume :
      Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        MeasureTheory.volume richShading.shading.union) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source outputLoss richTrapezoid.scale) := by
  have hsourceOutput :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss source.family source.shading :=
    source.extremal.mono_loss hloss
  have hextremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss source.family richShading.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceOutput.cwa_nearby_scales
      cubical := richShading.whole_cells
      dense := hdense
      volume_upper := by
        exact (measure_mono richShading.subshading.union_subset).trans
          hsourceOutput.volume_upper }
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hloss
  have hconstantTop :
      Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    richShading.subshading hconstant hconstantTop
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      richShading.subshading hconstant hconstantTop
  let globalGrains :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  have hvertical :
      ∀ point : {point : Point3 // point ∈ richShading.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, richShading.subshading.union_subset point.property⟩
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
    shading := richShading.shading
    subshading := richShading.subshading
    whole_cells := richShading.whole_cells
    extremal := hextremal
    volume_lower := hvolume
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
      intro trapezoid htrapezoid z hz hslice
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact richTrapezoid.slope_approximation z hz hslice
    active_height_coverage := by
      intro z _hz hslice
      exact ⟨richTrapezoid.trapezoid, by simp [trapezoids],
        richTrapezoid.active_height_coverage z hslice⟩
  }⟩

/--
Cancel the common weighted-height factor and assemble the final one-scale
output.  These are the exact two inequalities that the outer small-scale
schedule must prove; no unweighted rich-height count is substituted for
whole-cell mass.
-/
theorem PureWZ2SourceAlternativeARichTrapezoid.toOneScaleOfWeightedBudgets
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
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
    (richTrapezoid :
      PureWZ2SourceAlternativeARichTrapezoid richShading)
    (hloss : inputLoss ≤ outputLoss)
    (hdenseBudget :
      (54 * (wz1Lemma23SnappedHeights graph.residue.cells).card : ENNReal) *
          (Kakeya.realRpowENN delta outputLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
          twoScale.coarse.balanced.incidenceMass)
    (hvolumeBudget :
      (54 * (wz1Lemma23SnappedHeights graph.residue.cells).card : ENNReal) *
          Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
          twoScale.coarse.balanced.cellMass) :
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
  have hdense :
      Kakeya.realRpowENN delta outputLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        richShading.shading.mass := by
    apply (ENNReal.mul_le_mul_iff_right hfactorZero hfactorTop).mp
    calc
      factor * (Kakeya.realRpowENN delta outputLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
          ((rich.heightIndices.card * graph.residue.cells.card : ℕ) :
            ENNReal) * twoScale.coarse.balanced.incidenceMass := by
        simpa [factor, mul_comm, mul_left_comm, mul_assoc] using hdenseBudget
      _ ≤ factor * richShading.shading.mass := by
        simpa [factor, mul_comm, mul_left_comm, mul_assoc] using
          richShading.graph_weighted_mass_lower
  have hvolume :
      Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        MeasureTheory.volume richShading.shading.union := by
    apply (ENNReal.mul_le_mul_iff_right hfactorZero hfactorTop).mp
    calc
      factor * Kakeya.realRpowENN delta (sigma + outputLoss) ≤
          ((rich.heightIndices.card * graph.residue.cells.card : ℕ) :
            ENNReal) * twoScale.coarse.balanced.cellMass := by
        simpa [factor, mul_comm, mul_left_comm, mul_assoc] using hvolumeBudget
      _ ≤ factor * MeasureTheory.volume richShading.shading.union := by
        simpa [factor, mul_comm, mul_left_comm, mul_assoc] using
          richShading.graph_weighted_volume_lower
  exact richTrapezoid.toOneScale hloss hdense hvolume

/--
Restrict the rich one-trapezoid certificate to a same-family grain refinement.

The final volume lower bound and extremality come from the dependent Node-4
refinement.  The local and global grain data are restricted directly from the
original source, so the final slope is definitionally the source slope; no
unrelated grain carrier or independently selected slope is substituted.
-/
theorem PureWZ2SourceAlternativeARichTrapezoid.toOneScaleOfGrainRefinement
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
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
    (richTrapezoid :
      PureWZ2SourceAlternativeARichTrapezoid richShading)
    (refined :
      PureWZ2GrainRefinementData
        richShading.shading sigma outputLoss)
    (hloss : inputLoss ≤ outputLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source outputLoss richTrapezoid.scale) := by
  have hsub :
      PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro index point hpoint
    exact richShading.subshading index
      (refined.subshading index hpoint)
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hloss
  have hconstantTop :
      Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    hsub hconstant hconstantTop
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      hsub hconstant hconstantTop
  let globalGrains :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
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
      intro trapezoid htrapezoid z hz hslice
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      apply richTrapezoid.slope_approximation z hz
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
    active_height_coverage := by
      intro z _hz hslice
      refine ⟨richTrapezoid.trapezoid, by simp [trapezoids], ?_⟩
      apply richTrapezoid.active_height_coverage z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
  }⟩

/--
Paper-faithful Lemma-24 exit.  Weighted graph counting first makes the rich
whole-cell shading extremal at the structural loss selected by Node 4.  The
same-extremizer Node-4 producer then returns a dependent subshading with the
final volume lower bound; the one-trapezoid certificate is restricted to that
same final shading.
-/
theorem PureWZ2SourceAlternativeARichTrapezoid.toOneScaleOfGrainProducer
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
    (richTrapezoid :
      PureWZ2SourceAlternativeARichTrapezoid richShading)
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
          twoScale.coarse.balanced.incidenceMass)
    :
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
  have hdense :
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
  have hsourceStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hrichStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family richShading.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := richShading.whole_cells
      dense := hdense
      volume_upper :=
        (measure_mono richShading.subshading.union_subset).trans
          hsourceStructural.volume_upper }
  rcases grainProducer source.family richShading.shading
      source.line_class hrichStructural with ⟨refined⟩
  exact richTrapezoid.toOneScaleOfGrainRefinement refined
    (hinputStructural.trans hstructuralOutput)

end Kakeya.Assouad

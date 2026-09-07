import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactWeightedTrapezoid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements

/-!
# Same-configuration terminal one-scale assembly

The weighted whole-cell shading is first certified as a structural extremizer
using its genuine indexed mass.  The supplied Node-4 same-extremizer producer
then returns the final dependent refinement.  All grain data, extremality,
volume, and CWA fields therefore belong to that one final shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

theorem PureWZ2TerminalExactWeightedTrapezoid.toOneScaleOfGrainProducer
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    {prep : PureWZ2TerminalExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    {rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss}
    {weighted : PureWZ2TerminalExactRichHeightCellData rich}
    (trapezoid : PureWZ2TerminalExactWeightedTrapezoid weighted)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralOutput : structuralLoss ≤ outputLoss)
    (hdenseBudget :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        (rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData
                targetShading sigma outputLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source outputLoss trapezoid.scale) := by
  have hsourceStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hdense : weighted.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
    exact hdenseBudget.trans
      (weighted.volume_lower.trans weighted.mass_lower)
  have hweightedStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family weighted.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := weighted.whole_cells
      dense := hdense
      volume_upper := by
        have hsubSource : PureWZ2PaperIsSubshading
            weighted.shading source.shading := by
          intro index point hpoint
          exact retained.subshading index
            (weighted.subshading index hpoint)
        exact (measure_mono hsubSource.union_subset).trans
          hsourceStructural.volume_upper }
  rcases grainProducer source.family weighted.shading source.line_class
      hweightedStructural with ⟨refined⟩
  have hsub :
      PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro sourceIndex point hpoint
    exact retained.subshading sourceIndex
      (weighted.subshading sourceIndex
        (refined.subshading sourceIndex hpoint))
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
  let trapezoids : Finset WZ1VerticalTrapezoid := {trapezoid.trapezoid}
  exact ⟨{
    rho_pos := trapezoid.scale_pos
    delta_le_rho := by
      rw [trapezoid.scale_eq]
      nlinarith [source.extremal.delta_pos]
    rho_le_one := trapezoid.scale_le_one
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
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact trapezoid.height_eq
    slope_bound := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact trapezoid.slope_bound
    length_bounds := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact trapezoid.length_bounds
    separated_cores := by
      intro firstCandidate hfirst secondCandidate hsecond hne
      simp only [trapezoids, Finset.mem_singleton] at hfirst hsecond
      exact False.elim (hne (hfirst.trans hsecond.symm))
    slope_approximation := by
      intro candidate hcandidate z hz hslice
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      apply trapezoid.slope_approximation z hz
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
    active_height_coverage := by
      intro z _hz hslice
      refine ⟨trapezoid.trapezoid, by simp [trapezoids], ?_⟩
      apply trapezoid.active_height_coverage z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩ }⟩

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderRichGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalHeightLiftOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalMultiWindowAssembly

/-!
# One-scale output from the paper-ordered ordinary graph

The preceding module has already returned the selected `Z_lin` heights to an
original-family paper shading.  Consequently the final density hypothesis can
be stated directly against that proved source-mass lower bound; no graph-cell
incidence surrogate or second coarse/source pullback is introduced here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Refine the paper-ordered `Z_lin` height lift on the same original family. -/
theorem PureWZ2OrdinaryPaperOrderRichGraphData.toOneScaleOfMassBudget
    {sigma inputLoss delta rho middleLoss stickyLoss outputLoss normalEta
      theoremEta structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := outputLoss) (theoremEta := theoremEta) graphData)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralOutput : structuralLoss ≤ outputLoss)
    (grainProducer :
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        ∀ shading : WZ1PaperTubeShading family,
          WZ1PaperIsLineClass family →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss family shading →
            Nonempty
              (PureWZ2GrainRefinementData shading sigma outputLoss))
    (hdenseBudget :
      3 * (Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass) ≤
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((data.rich.heightIndices.card : ENNReal) *
            carriers.outerPopular.popular.layerMass)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source outputLoss data.richTrapezoid.scale) := by
  have hscaled :
      3 * (Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass) ≤
        3 * data.heightLift.shading.mass :=
    hdenseBudget.trans data.source_mass_lower
  have hliftDense :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        data.heightLift.shading.mass :=
    (ENNReal.mul_le_mul_iff_left
      (show (3 : ENNReal) ≠ 0 by norm_num)
      (show (3 : ENNReal) ≠ ⊤ by norm_num)).mp (by
        simpa [mul_comm] using hscaled)
  have hsourceStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hliftStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family data.heightLift.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := data.heightLift.whole_cells
      dense := hliftDense
      volume_upper :=
        (measure_mono data.heightLift.subshading.union_subset).trans
          hsourceStructural.volume_upper }
  rcases grainProducer source.family data.heightLift.shading
      source.line_class hliftStructural with ⟨refined⟩
  have hsub :
      PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro index point hpoint
    exact data.heightLift.subshading index
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
    {data.richTrapezoid.trapezoid}
  have hdeltaScale : delta ≤ data.richTrapezoid.scale := by
    calc
      delta ≤ prepared.prep.graphScale := prepared.prep.sourceScale_le_graphScale
      _ ≤ 5 * prepared.prep.graphScale := by
        nlinarith [prepared.prep.graphScale_pos]
      _ = data.richTrapezoid.scale := data.richTrapezoid.scale_eq.symm
  exact ⟨{
    rho_pos := data.richTrapezoid.scale_pos
    delta_le_rho := hdeltaScale
    rho_le_one := data.richTrapezoid.scale_le_one
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
      exact data.richTrapezoid.height_eq
    slope_bound := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact data.richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact data.richTrapezoid.length_bounds
    separated_cores := by
      intro first hfirst second hsecond hne
      simp only [trapezoids, Finset.mem_singleton] at hfirst hsecond
      exact False.elim (hne (hfirst.trans hsecond.symm))
    slope_approximation := by
      intro trapezoid htrapezoid z _hz hslice
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      apply data.heightLift.slope_approximation z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
    active_height_coverage := by
      intro z _hz hslice
      refine ⟨data.richTrapezoid.trapezoid, by simp [trapezoids], ?_⟩
      apply data.heightLift.active_height_coverage z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
  }⟩

/-- Public-scale form of `toOneScaleOfMassBudget`. The exact graph
normalization gives `5 * (256 * rho) = 1280 * rho`. -/
theorem PureWZ2OrdinaryPaperOrderRichGraphData.toOneScale
    {sigma inputLoss delta rho middleLoss stickyLoss outputLoss normalEta
      theoremEta structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := outputLoss) (theoremEta := theoremEta) graphData)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralOutput : structuralLoss ≤ outputLoss)
    (grainProducer :
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        ∀ shading : WZ1PaperTubeShading family,
          WZ1PaperIsLineClass family →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss family shading →
            Nonempty
              (PureWZ2GrainRefinementData shading sigma outputLoss))
    (hdenseBudget :
      3 * (Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass) ≤
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((data.rich.heightIndices.card : ENNReal) *
            carriers.outerPopular.popular.layerMass)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source outputLoss (pureWZ2SourceHorizontalFinalScale rho)) := by
  have hscale : data.richTrapezoid.scale =
      pureWZ2SourceHorizontalFinalScale rho := by
    rw [data.richTrapezoid.scale_eq, prepared.prep.graphScale_eq]
    simp [pureWZ2SourceHorizontalFinalScale]
    ring
  rw [← hscale]
  exact data.toOneScaleOfMassBudget hinputStructural hstructuralOutput
    grainProducer hdenseBudget

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineRichTrapezoid

/-!
# Same-configuration one-scale output on the first-sticky coarse grain base

The Node-5 conclusion is existential.  We therefore take the actual grain
refinement of the first sticky coarse extremizer as the hierarchy base.  All
slopes and plane maps below are restrictions of that base; no original-source
slope is substituted for it.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

theorem PureWZ2HorizontalAlternativeARichTrapezoid.toOneScaleOfGrainProducer
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2HorizontalFixedLineSharpGeometry graph}
    {ready : PureWZ2HorizontalFixedLineReadyGraph
      (eta := eta) (theoremEta := theoremEta)
      (graphParents := graphParents) (sources := sources)
      (fullGrains := fullGrains) sharp}
    {rich : PureWZ2HorizontalAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2HorizontalAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2HorizontalAlternativeARichShading richCells}
    (richTrapezoid : PureWZ2HorizontalAlternativeARichTrapezoid richShading)
    (hmiddleStructural : middleLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily :
          Kakeya.Streamlined.TubeFamily twoScale.rhoRequested.1,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData
                targetShading sigma finalLoss))
    (hdense :
      Kakeya.realRpowENN twoScale.rhoRequested.1 structuralLoss *
          (wz1PaperBodyFamily twoScale.coarse.coarse).mass ≤
        richShading.shading.mass) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      (twoScale.coarseGrains.toQuantitativeGrainConfiguration
        twoScale.coarseGrains_slope_bound)
      finalLoss richTrapezoid.scale) := by
  let base := twoScale.coarseGrains.toQuantitativeGrainConfiguration
    twoScale.coarseGrains_slope_bound
  have hbaseStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss base.family base.shading :=
    base.extremal.mono_loss hmiddleStructural
  have hrichStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss base.family richShading.shading :=
    { delta_pos := hbaseStructural.delta_pos
      delta_le_one := hbaseStructural.delta_le_one
      nonempty := hbaseStructural.nonempty
      cwa_nearby_scales := hbaseStructural.cwa_nearby_scales
      cubical := richShading.whole_cells
      dense := by
        simpa [Kakeya.Streamlined.Shading.IsLambdaDense, base,
          PureWZ2GrainRefinementData.toQuantitativeGrainConfiguration]
          using hdense
      volume_upper :=
        (measure_mono richShading.subshading.union_subset).trans
          hbaseStructural.volume_upper }
  rcases grainProducer base.family richShading.shading base.line_class
      hrichStructural with ⟨refined⟩
  have hsub : PureWZ2PaperIsSubshading refined.shading base.shading := by
    intro index point hpoint
    exact richShading.subshading index (refined.subshading index hpoint)
  have hconstant :
      Kakeya.realRpowENN twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1 (-finalLoss) :=
    pureWZ2_grain_constant_mono base.extremal.delta_pos
      base.extremal.delta_le_one
      (hmiddleStructural.trans hstructuralFinal)
  have hconstantTop :
      Kakeya.realRpowENN twoScale.rhoRequested.1 (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := base.localGrains.restrictWithConstant hsub hconstant hconstantTop
  let globalGrains := base.globalGrains.restrict hsub hconstant hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ refined.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact base.planeMap_vertical_bound
      ⟨point, hsub.union_subset point.property⟩
  let trapezoids : Finset WZ1VerticalTrapezoid :=
    {richTrapezoid.trapezoid}
  have hstoredScale :
      twoScale.rhoRequested.1 ≤ richTrapezoid.scale := by
    calc
      twoScale.rhoRequested.1 ≤ prep.graphScale := by
        rw [prep.graphScale_eq]
        nlinarith [base.extremal.delta_pos]
      _ ≤ 5 * prep.graphScale := by nlinarith [prep.graphScale_pos]
      _ = richTrapezoid.scale := richTrapezoid.scale_eq.symm
  exact ⟨{
    rho_pos := richTrapezoid.scale_pos
    delta_le_rho := hstoredScale
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

end Kakeya.Assouad

end

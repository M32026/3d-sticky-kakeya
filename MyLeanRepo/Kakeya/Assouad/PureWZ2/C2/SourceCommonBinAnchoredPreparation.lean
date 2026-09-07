import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredTwoScaleInput

/-!
# Source carrier preparation for anchored CommonBin

This is the full-grain-free analogue of `PureWZ2SourceCarrierPreparation`.
Both grain structures are restricted from the literal supplied source.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2AnchoredSourceCarrierPreparation
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    (selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily selected.shading source.extremal.delta_pos) :=
    pureWZ2ActiveCellShading selected.shading source.extremal.delta_pos
  shadow_union : shadow.union = selected.shading.union
  localPaper : PureWZ2LocalGrainData selected.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper : PureWZ2BoundedLipschitzGlobalGrainData selected.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper_slope_eq : globalPaper.slope = source.globalGrains.slope
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ selected.shading.union},
      localGrains.planeMap point = localPaper.planeMap point
  planeMap_vertical_bound :
    ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  exactAD_delta :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        rhoRequested.1 (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))

theorem PureWZ2AnchoredSourceRelativeFineSelection.prepareSourceCarrier
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    (selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2AnchoredSourceCarrierPreparation selected) := by
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by simp [C, Kakeya.realRpowENN]
  let localPaper := source.localGrains.restrictWithConstant
    selected.subshading le_rfl hCtop
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      selected.subshading le_rfl hCtop
  let globalPaper :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  let shadow := pureWZ2ActiveCellShading
    selected.shading source.extremal.delta_pos
  have hunion : shadow.union = selected.shading.union :=
    pureWZ2ActiveCellShading_union selected.shading
      source.extremal.delta_pos selected.whole_cells
  let localGrains := localPaper.toActiveCellShadow
    source.extremal.delta_pos selected.whole_cells hbridge
  have hplane :
      ∀ point : {point : Point3 // point ∈ selected.shading.union},
        localGrains.planeMap point = localPaper.planeMap point := by
    intro point
    exact (Classical.choose_spec localPaper.exists_ambient_extension).2 point
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ selected.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, selected.subshading.union_subset point.property⟩
  have hvertical :
      ∀ point ∈ shadow.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toActiveCellShadow_vertical_bound
      source.extremal.delta_pos selected.whole_cells hbridge hverticalPaper
  have hdeltaRho : delta ≤ rhoRequested.1 := rhoRequested.property.1
  have hrho : 0 < rhoRequested.1 :=
    source.extremal.delta_pos.trans_le hdeltaRho
  have hexactDelta :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma) (10 * C) := by
    intro z hz
    have h := globalPaper.activeCellShadow_exactAD
      source.extremal.delta_pos selected.whole_cells hbridge
      globalPaper.slope_bound z hz
    rwa [show globalPaper.slope = source.globalGrains.slope by rfl] at h
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          rhoRequested.1 (1 - sigma) (10 * C) := by
    intro z hz
    exact (hexactDelta z hz).coarsen_scale hrho hdeltaRho
      rhoRequested.property.2
  exact ⟨{
    shadow := shadow
    shadow_union := hunion
    localPaper := localPaper
    globalPaper := globalPaper
    globalPaper_slope_eq := rfl
    localGrains := localGrains
    planeMap_eq_on_paper := hplane
    planeMap_vertical_bound := hvertical
    exactAD_delta := by simpa [C] using hexactDelta
    exactAD := by simpa [C] using hexact
  }⟩

end Kakeya.Assouad

end

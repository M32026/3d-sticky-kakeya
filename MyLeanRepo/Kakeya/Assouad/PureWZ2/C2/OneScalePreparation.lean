import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.HeightWindowPigeonhole
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry

/-!
# Same-configuration Pure WZ2 Lemma-23 preparation

This record locks the paper shading, its equal-union ordinary active-cell
shadow, local grains, and the exact-slice global package together before the
fixed-line and heavy-source selections.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2Lemma23PreparedSource
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (rho : ℝ) where
  rho_pos : 0 < rho
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily source.shading source.extremal.delta_pos) :=
    pureWZ2ActiveCellShading source.shading source.extremal.delta_pos
  shadow_union : shadow.union = source.shading.union
  localGrains :
    WZ1LocalGrainData shadow sigma
      (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_vertical_bound :
    ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  global :
    WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma)
      shadow (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : global.sourceSlope = source.globalGrains.slope
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))

structure PureWZ2Lemma23WindowedSource
    {sigma inputLoss delta rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (prepared : PureWZ2Lemma23PreparedSource source rho) where
  left : ℝ
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily source.shading source.extremal.delta_pos)
  subshading : IsSubshading shading prepared.shadow
  localGrains :
    WZ1LocalGrainData shading sigma
      (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_vertical_bound :
    ∀ point ∈ shading.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed :
    WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma)
      shading (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  volume_lower :
    MeasureTheory.volume prepared.shadow.union *
          ENNReal.ofReal (Real.sqrt rho) /
        ENNReal.ofReal (2 + rho + Real.sqrt rho) ≤
      MeasureTheory.volume shading.union

/-- Select one complete-cell paper height window on the prepared shadow. -/
theorem PureWZ2Lemma23PreparedSource.selectHeightWindow
    {sigma inputLoss delta rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (prepared : PureWZ2Lemma23PreparedSource source rho) :
    Nonempty (PureWZ2Lemma23WindowedSource prepared) := by
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hsource : point ∈ source.shading.union := by
      simpa [prepared.shadow_union] using hpoint
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hheight :
      ∀ point ∈ prepared.shadow.union, |point (2 : Fin 3)| ≤ 1 := by
    intro point hpoint
    have hsource : point ∈ source.shading.union := by
      simpa [prepared.shadow_union] using hpoint
    have hbox := shading_union_subset_axisBox hsource
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  rcases
      height_window_pigeonhole_tight_of_paper_window
        prepared.shadow prepared.rho_pos prepared.rho_le_one
        hball hheight with
    ⟨left, hvolume⟩
  have hcoord :
      ∀ point ∈ prepared.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource : point ∈ source.shading.union := by
      simpa [prepared.shadow_union] using hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hglobal :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice prepared.shadow.union z))
          delta (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    exact prepared.exactAD
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases
      wz1_lemma23_windowed_global_slice_package_of_exact_paper_window
        prepared.shadow prepared.rho_pos prepared.delta_le_rho
        prepared.rho_le_one hball hcoord
        source.globalGrains.slope source.globalGrains.slope_lipschitz
        source.globalGrains.slope_bound
        (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop
        hglobal left with
    ⟨shading, windowed, hshadingEq, hsub, hslope⟩
  let localGrains :
      WZ1LocalGrainData shading sigma
        (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    restrictAndWeakenLocalGrains hsub (by rfl) prepared.localGrains
  have hunionSub : shading.union ⊆ prepared.shadow.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩
  have hvertical :
      ∀ point ∈ shading.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point hpoint
    exact prepared.planeMap_vertical_bound point (hunionSub hpoint)
  have hunionEq :
      shading.union =
        prepared.shadow.union ∩
          wz1Lemma23CellHeightWindowSet rho prepared.rho_pos left := by
    rw [hshadingEq]
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
    · rintro ⟨⟨index, hpoint⟩, hwindow⟩
      exact ⟨index, hpoint, hwindow⟩
  have hvolume' :
      MeasureTheory.volume prepared.shadow.union *
            ENNReal.ofReal (Real.sqrt rho) /
          ENNReal.ofReal (2 + rho + Real.sqrt rho) ≤
        MeasureTheory.volume shading.union := by
    rw [hunionEq]
    exact hvolume
  exact
    ⟨{ left := left
       shading := shading
       subshading := hsub
       localGrains := localGrains
       planeMap_vertical_bound := hvertical
       windowed := windowed
       sourceSlope_eq := hslope
       volume_lower := hvolume' }⟩

/-- Construct the exact-slice shadow package directly from the pure source. -/
theorem PureWZ2QuantitativeGrainConfiguration.toLemma23PreparedSource
    {sigma inputLoss delta rho : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hrho : 0 < rho) (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1) :
    Nonempty (PureWZ2Lemma23PreparedSource source rho) := by
  let hdelta := source.extremal.delta_pos
  let shadow := pureWZ2ActiveCellShading source.shading hdelta
  have hunion : shadow.union = source.shading.union :=
    pureWZ2ActiveCellShading_union source.shading hdelta source.cubical
  let localGrains :=
    source.localGrains.toActiveCellShadow hdelta source.cubical hbridge
  have hvertical :
      ∀ point ∈ shadow.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    exact source.localGrains.toActiveCellShadow_vertical_bound
      hdelta source.cubical hbridge source.planeMap_vertical_bound
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hsource : point ∈ source.shading.union := by simpa [hunion] using hpoint
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource : point ∈ source.shading.union := by simpa [hunion] using hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hglobal :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    exact source.globalGrains.activeCellShadow_exactAD
      hdelta source.cubical hbridge source.globalGrains.slope_bound
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases
      wz1_lemma23_global_slice_package_of_exact_paper_window
        shadow hrho hdelta_rho hrho_one hball hcoord
        source.globalGrains.slope source.globalGrains.slope_lipschitz
        source.globalGrains.slope_bound
        (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop hglobal with
    ⟨global, hslope⟩
  exact
    ⟨{ rho_pos := hrho
       delta_le_rho := hdelta_rho
       rho_le_one := hrho_one
       shadow := shadow
       shadow_union := hunion
       localGrains := localGrains
       planeMap_vertical_bound := hvertical
       global := global
       sourceSlope_eq := hslope
       exactAD := hglobal }⟩

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScalePreparedSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage

/-!
# Exact-slice preparation at the terminal tube scale

The graph scale is the source tube radius `delta`.  The ordinary active-cell
shadow is an equal-union view of the selected terminal paper shading, so its
global slope and local plane map come from the same restricted Pure source.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2TerminalLemma23Prepared
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent}
    (prepared : PureWZ2TerminalPreparedSource source terminal) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily prepared.shading
      prepared.delta_pos) :=
    pureWZ2ActiveCellShading prepared.shading prepared.delta_pos
  shadow_union : shadow.union = prepared.shading.union
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_vertical_bound :
    ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  global : WZ1Lemma23GlobalSlicePackage
    (delta := delta) (rho := delta) (sigma := sigma) shadow
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : global.sourceSlope = source.globalGrains.slope
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))

theorem PureWZ2TerminalPreparedSource.toLemma23Prepared
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent}
    (prepared : PureWZ2TerminalPreparedSource source terminal)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalLemma23Prepared prepared) := by
  let hdelta := prepared.delta_pos
  let shadow := pureWZ2ActiveCellShading prepared.shading hdelta
  have hunion : shadow.union = prepared.shading.union :=
    pureWZ2ActiveCellShading_union prepared.shading hdelta prepared.cubical
  let localGrains := prepared.localGrains.toActiveCellShadow
    hdelta prepared.cubical hbridge
  have hvertical :
      ∀ point ∈ shadow.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    prepared.localGrains.toActiveCellShadow_vertical_bound
      hdelta prepared.cubical hbridge prepared.planeMap_vertical_bound
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ prepared.shading.union := by simpa [hunion] using hpoint
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ prepared.shading.union := by simpa [hunion] using hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    intro z hz
    have h := prepared.globalGrains.activeCellShadow_exactAD
      hdelta prepared.cubical hbridge prepared.globalGrains.slope_bound z hz
    rwa [prepared.global_slope_eq] at h
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hdelta le_rfl prepared.delta_le_one hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound
      (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop hexact with
    ⟨global, hslope⟩
  exact ⟨{
    shadow := shadow
    shadow_union := hunion
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    global := global
    sourceSlope_eq := hslope
    exactAD := hexact
  }⟩

end Kakeya.Assouad

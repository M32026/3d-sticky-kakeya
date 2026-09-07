import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleTwoScaleSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TwoScaleVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.HeightWindowPigeonhole
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry

/-!
# Lemma-23 exact-slice preparation on the genuine coarse grain refinement

The first sticky output is refined by the grain-facing Node-4 producer before
the second sticky application.  This module converts that actual `rho`-scale
paper shading and its global grains into the ordinary exact-slice package used
by the closed Lemma-23 graph infrastructure.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Minimal global input actually consumed by Lemma-23 coarse preparation.
It is independent of local grains and can be filled directly from the
supplied current slope plus an exact AD receipt on the selected fine union. -/
structure PureWZ2AnchoredCoarseGlobalInput
    {rho sigma middleLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    (fineShading : WZ1PaperTubeShading family) where
  rho_pos : 0 < rho
  rho_le_one : rho ≤ 1
  cubical : WZ1PaperIsCubicalShading fineShading
  slope : ℝ → ℝ
  slope_lipschitz :
    LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1)
  slope_bound : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 → |slope z| ≤ 3
  global_ad :
    ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice fineShading.union z))
        rho (1 - sigma)
        (Kakeya.realRpowENN rho (-middleLoss))

structure PureWZ2AnchoredLemma23PreparedCoarse
    {rho sigma middleLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading family}
    (input : PureWZ2AnchoredCoarseGlobalInput
      (sigma := sigma) (middleLoss := middleLoss) fineShading) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily fineShading input.rho_pos) :=
    pureWZ2ActiveCellShading fineShading input.rho_pos
  shadow_union : shadow.union = fineShading.union
  global :
    WZ1Lemma23GlobalSlicePackage
      (delta := rho) (rho := rho) (sigma := sigma) shadow
      (10 * Kakeya.realRpowENN rho (-middleLoss))
  sourceSlope_eq : global.sourceSlope = input.slope
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (input.slope z))
          (horizontalSlice shadow.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))

/-- Prepare the exact fine shadow from the anchored global receipt. -/
theorem PureWZ2AnchoredCoarseGlobalInput.toLemma23PreparedCoarse
    {rho sigma middleLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading family}
    (input : PureWZ2AnchoredCoarseGlobalInput
      (sigma := sigma) (middleLoss := middleLoss) fineShading)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2AnchoredLemma23PreparedCoarse input) := by
  let shadow := pureWZ2ActiveCellShading fineShading input.rho_pos
  have hunion : shadow.union = fineShading.union :=
    pureWZ2ActiveCellShading_union fineShading input.rho_pos
      input.cubical
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hfine : point ∈ fineShading.union := by simpa [hunion] using hpoint
    have hnorm := norm_le_two_of_mem_paperShading hfine
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hfine : point ∈ fineShading.union := by simpa [hunion] using hpoint
    have hbox := shading_union_subset_axisBox hfine
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection (globalGrainDirection (input.slope z))
            (horizontalSlice shadow.union z))
          rho (1 - sigma)
          (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
    intro z hz
    rw [hunion]
    exact hbridge.1
      (scalarProjection (globalGrainDirection (input.slope z))
        (horizontalSlice fineShading.union z))
      rho (1 - sigma)
      (Kakeya.realRpowENN rho (-middleLoss))
      (show
        scalarProjection (globalGrainDirection (input.slope z))
            (horizontalSlice fineShading.union z) ⊆
          Set.Icc (-4 : ℝ) 4 from by
        rintro value ⟨point, hpoint, rfl⟩
        have hbox := shading_union_subset_axisBox hpoint.1
        simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
        have hslope := input.slope_bound z hz
        have hformula :
            inner ℝ point (globalGrainDirection (input.slope z)) =
              point 0 + input.slope z * point 1 := by
          simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        change inner ℝ point (globalGrainDirection (input.slope z)) ∈
          Set.Icc (-4 : ℝ) 4
        rw [hformula]
        have habs : |point 0 + input.slope z * point 1| ≤ 4 := by
          calc
            |point 0 + input.slope z * point 1| ≤
                |point 0| + |input.slope z| * |point 1| := by
              calc
                _ ≤ |point 0| + |input.slope z * point 1| := abs_add_le _ _
                _ = _ := by rw [abs_mul]
            _ ≤ 1 + 3 * 1 := by
              have hpoint0 : |point 0| ≤ 1 := by
                norm_num at hbox ⊢
                exact hbox.1
              have hpoint1 : |point 1| ≤ 1 := by
                norm_num at hbox ⊢
                exact hbox.2.1
              exact add_le_add hpoint0
                (mul_le_mul hslope hpoint1 (abs_nonneg _) (by norm_num))
            _ = 4 := by norm_num
        exact abs_le.mp habs)
      (input.global_ad z hz)
  have hCtop :
      (10 * Kakeya.realRpowENN rho (-middleLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow input.rho_pos le_rfl input.rho_le_one hball hcoord
      input.slope input.slope_lipschitz input.slope_bound
      (10 * Kakeya.realRpowENN rho (-middleLoss)) hCtop hexact with
    ⟨global, hslope⟩
  exact ⟨{
    shadow := shadow
    shadow_union := hunion
    global := global
    sourceSlope_eq := hslope
    exactAD := hexact
  }⟩

structure PureWZ2Lemma23PreparedCoarse
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily
      twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos) :=
    pureWZ2ActiveCellShading
      twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos
  shadow_union : shadow.union = twoScale.fine.refined.union
  global :
    WZ1Lemma23GlobalSlicePackage
      (delta := twoScale.rhoRequested.1)
      (rho := twoScale.rhoRequested.1) (sigma := sigma)
      shadow
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
  sourceSlope_eq :
    global.sourceSlope = twoScale.coarseGrains.globalGrains.slope
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection
            (twoScale.coarseGrains.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        twoScale.rhoRequested.1 (1 - sigma)
        (10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss))

structure PureWZ2Lemma23WindowedCoarse
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) where
  left : ℝ
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily
      twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos)
  subshading : IsSubshading shading prepared.shadow
  windowed :
    WZ1Lemma23WindowedGlobalSlicePackage
      (delta := twoScale.rhoRequested.1)
      (rho := twoScale.rhoRequested.1) (sigma := sigma)
      shading
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
  sourceSlope_eq :
    windowed.global.sourceSlope =
      twoScale.coarseGrains.globalGrains.slope
  volumeSupply : ENNReal
  volumeSupply_pos : 0 < volumeSupply
  volumeSupply_ne_top : volumeSupply ≠ ⊤
  union_height_window :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        (left - twoScale.rhoRequested.1)
        (left + Real.sqrt twoScale.rhoRequested.1 +
          twoScale.rhoRequested.1)
  volume_lower : volumeSupply ≤ MeasureTheory.volume shading.union

/-- Build the exact-slice ordinary shadow of the actual coarse grain output. -/
theorem PureWZ2OneScaleTwoScaleStickyData.toLemma23PreparedCoarse
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2Lemma23PreparedCoarse twoScale) := by
  let hscale := twoScale.coarseGrains.extremal.delta_pos
  let shadow :=
    pureWZ2ActiveCellShading twoScale.fine.refined hscale
  have hunion : shadow.union = twoScale.fine.refined.union :=
    pureWZ2ActiveCellShading_union
      twoScale.fine.refined hscale
      twoScale.fine.refined_cubical
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      simpa [hunion] using hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource :
        point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hfine : point ∈ twoScale.fine.refined.union := by
      simpa [hunion] using hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource :
        point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection
              (twoScale.coarseGrains.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          twoScale.rhoRequested.1 (1 - sigma)
          (10 * Kakeya.realRpowENN
            twoScale.rhoRequested.1 (-middleLoss)) := by
    intro z hz
    rw [hunion]
    have hfineSub :
        twoScale.fine.refined.union ⊆
          twoScale.coarseGrains.shading.union := by
      rintro point ⟨index, hindex⟩
      exact ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    exact hbridge.1 _ twoScale.rhoRequested.1 (1 - sigma)
      (Kakeya.realRpowENN twoScale.rhoRequested.1 (-middleLoss))
      (by
        rintro value ⟨point, hpoint, rfl⟩
        have hbox := shading_union_subset_axisBox (hfineSub hpoint.1)
        simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
        have hslope :=
          twoScale.coarseGrains_slope_bound z hz
        have hformula :
            inner ℝ point
                (globalGrainDirection
                  (twoScale.coarseGrains.globalGrains.slope z)) =
              point 0 +
                twoScale.coarseGrains.globalGrains.slope z * point 1 := by
          simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        change inner ℝ point
            (globalGrainDirection
              (twoScale.coarseGrains.globalGrains.slope z)) ∈
          Set.Icc (-4 : ℝ) 4
        rw [hformula]
        have habs :
            |point 0 +
                twoScale.coarseGrains.globalGrains.slope z * point 1| ≤
              4 := by
          calc
            |point 0 +
                twoScale.coarseGrains.globalGrains.slope z * point 1|
                ≤ |point 0| +
                    |twoScale.coarseGrains.globalGrains.slope z| *
                      |point 1| := by
                  calc
                    _ ≤ |point 0| +
                        |twoScale.coarseGrains.globalGrains.slope z *
                          point 1| := abs_add_le _ _
                    _ = _ := by rw [abs_mul]
            _ ≤ 1 + 3 * 1 := by
              have hpoint0 : |point 0| ≤ 1 := by
                norm_num at hbox ⊢
                exact hbox.1
              have hpoint1 : |point 1| ≤ 1 := by
                norm_num at hbox ⊢
                exact hbox.2.1
              exact add_le_add hpoint0
                (mul_le_mul hslope hpoint1 (abs_nonneg _) (by norm_num))
            _ = 4 := by norm_num
        exact abs_le.mp habs)
      ((twoScale.coarseGrains.globalGrains.global_ad z hz).mono
        (by
          rintro value ⟨point, hpoint, rfl⟩
          exact ⟨point, ⟨hfineSub hpoint.1, hpoint.2⟩, rfl⟩))
  have hCtop :
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases
      wz1_lemma23_global_slice_package_of_exact_paper_window
        shadow hscale le_rfl twoScale.rhoRequested.property.2
        hball hcoord
        twoScale.coarseGrains.globalGrains.slope
        twoScale.coarseGrains.globalGrains.slope_lipschitz
        twoScale.coarseGrains_slope_bound
        (10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss)) hCtop
        hexact with
    ⟨global, hslope⟩
  exact
    ⟨{ shadow := shadow
       shadow_union := hunion
       global := global
       sourceSlope_eq := hslope
       exactAD := hexact }⟩

/-- The retained coarse carrier has the second-sticky power volume floor. -/
theorem PureWZ2Lemma23PreparedCoarse.power_volume_lower
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hetaAbsorb :
      Kakeya.realRpowENN twoScale.rhoRequested.1 eta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent) :
    Kakeya.realRpowENN twoScale.rhoRequested.1
        (1 + sigma / 2 + middleLoss + outputLoss / 2 + eta) ≤
      MeasureTheory.volume prepared.shadow.union := by
  rw [prepared.shadow_union]
  exact twoScale.second_refined_volume_power hrhoSmall hetaAbsorb

/-- Package any positive complete-cell subshading in one `sqrt rho` height
window.  This is the local constructor used by the Lemma-24 slab iteration. -/
theorem PureWZ2Lemma23PreparedCoarse.ofSubshading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (left : ℝ)
    (shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily
        twoScale.fine.refined
        twoScale.coarseGrains.extremal.delta_pos))
    (hsub : IsSubshading shading prepared.shadow)
    (hactive :
      ∀ cell ∈ wz1Lemma23ActiveCells shading
          twoScale.rhoRequested.1
          twoScale.coarseGrains.extremal.delta_pos,
        (wz1Lemma23SnappedPoint twoScale.rhoRequested.1 cell)
            (2 : Fin 3) ∈
          Set.Icc left
            (left + Real.sqrt twoScale.rhoRequested.1))
    (volumeSupply : ENNReal)
    (hvolumeSupply : 0 < volumeSupply)
    (hvolumeSupplyTop : volumeSupply ≠ ⊤)
    (hvolume : volumeSupply ≤ MeasureTheory.volume shading.union) :
    ∃ window : PureWZ2Lemma23WindowedCoarse prepared,
      window.left = left ∧ window.shading = shading ∧
        window.volumeSupply = volumeSupply := by
  have hscale : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  have hscaleOne : twoScale.rhoRequested.1 ≤ 1 :=
    twoScale.rhoRequested.property.2
  have hunionSub : shading.union ⊆ prepared.shadow.union :=
    hsub.union_subset
  have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := hunionSub hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      rwa [prepared.shadow_union] at hprepared
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hprepared := hunionSub hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      rwa [prepared.shadow_union] at hprepared
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection
              (twoScale.coarseGrains.globalGrains.slope z))
            (horizontalSlice shading.union z))
          twoScale.rhoRequested.1 (1 - sigma)
          (10 * Kakeya.realRpowENN
            twoScale.rhoRequested.1 (-middleLoss)) := by
    intro z hz
    exact (prepared.exactAD z hz).mono (by
      rintro value ⟨point, hpoint, rfl⟩
      exact ⟨point, ⟨hunionSub hpoint.1, hpoint.2⟩, rfl⟩)
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shading hscale le_rfl hscaleOne hball hcoord
      twoScale.coarseGrains.globalGrains.slope
      twoScale.coarseGrains.globalGrains.slope_lipschitz
      twoScale.coarseGrains_slope_bound
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss)) hCtop hexact with
    ⟨global, hslope⟩
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := twoScale.rhoRequested.1)
      (rho := twoScale.rhoRequested.1) (sigma := sigma) shading
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss)) :=
    { global := global
      active_height_window := ⟨left, hactive⟩ }
  have hunionHeight :
      ∀ point ∈ shading.union,
        point (2 : Fin 3) ∈ Set.Ico
          (left - twoScale.rhoRequested.1)
          (left + Real.sqrt twoScale.rhoRequested.1 +
            twoScale.rhoRequested.1) := by
    intro point hpoint
    have hactiveCell :=
      wz1Lemma23_index_mem_active_two hscale hball hpoint
    have hcenterWindow := hactive _ hactiveCell
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry
        twoScale.rhoRequested.1 hscale hscaleOne).2.1
        (wz1Lemma23CellIndex twoScale.rhoRequested.1 point)
        point rfl).1 (2 : Fin 3)
    rw [abs_le] at hpointCenter
    exact ⟨by linarith [hcenterWindow.1, hpointCenter.2],
      by linarith [hcenterWindow.2, hpointCenter.1]⟩
  let result : PureWZ2Lemma23WindowedCoarse prepared := {
    left := left
    shading := shading
    subshading := hsub
    windowed := windowed
    sourceSlope_eq := by simpa [windowed] using hslope
    volumeSupply := volumeSupply
    volumeSupply_pos := hvolumeSupply
    volumeSupply_ne_top := hvolumeSupplyTop
    union_height_window := hunionHeight
    volume_lower := hvolume
  }
  exact ⟨result, rfl, rfl, rfl⟩

/-- Select one complete-cell height window on the coarse grain shadow. -/
theorem PureWZ2Lemma23PreparedCoarse.selectHeightWindow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    Nonempty (PureWZ2Lemma23WindowedCoarse prepared) := by
  have hrho : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : twoScale.rhoRequested.1 ≤ 1 :=
    twoScale.rhoRequested.property.2
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      simpa [prepared.shadow_union] using hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hheight :
      ∀ point : Point3, point ∈ prepared.shadow.union →
        |point (2 : Fin 3)| ≤ 1 := by
    intro point hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      simpa [prepared.shadow_union] using hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hbox := shading_union_subset_axisBox hsource
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  rcases
      height_window_pigeonhole_tight_of_paper_window
        prepared.shadow hrho hrhoOne hball hheight with
    ⟨left, hvolume⟩
  have hcoord :
      ∀ point ∈ prepared.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hfine : point ∈ twoScale.fine.refined.union := by
      simpa [prepared.shadow_union] using hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases
      wz1_lemma23_windowed_global_slice_package_of_exact_paper_window
        prepared.shadow hrho le_rfl hrhoOne hball hcoord
        twoScale.coarseGrains.globalGrains.slope
        twoScale.coarseGrains.globalGrains.slope_lipschitz
      twoScale.coarseGrains_slope_bound
        (10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss)) hCtop
        prepared.exactAD left with
    ⟨shading, windowed, _hshading, hsub, hslope⟩
  let volumeSupply :=
    MeasureTheory.volume prepared.shadow.union *
        ENNReal.ofReal (Real.sqrt twoScale.rhoRequested.1) /
      ENNReal.ofReal
        (2 + twoScale.rhoRequested.1 +
          Real.sqrt twoScale.rhoRequested.1)
  have hshadowVolumePos :
      0 < MeasureTheory.volume prepared.shadow.union := by
    rw [prepared.shadow_union]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos twoScale.coarseGrains.extremal.delta_pos _)).trans_le
        twoScale.fine.refined_volume_lower
  have hsqrtPos :
      0 < ENNReal.ofReal (Real.sqrt twoScale.rhoRequested.1) :=
    ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hrho)
  have hdenomPos :
      0 < ENNReal.ofReal
        (2 + twoScale.rhoRequested.1 +
          Real.sqrt twoScale.rhoRequested.1) := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hsupplyPos : 0 < volumeSupply := by
    dsimp only [volumeSupply]
    exact ENNReal.div_pos
      (ENNReal.mul_pos hshadowVolumePos.ne' hsqrtPos.ne').ne'
      ENNReal.ofReal_ne_top
  have hsupplyTop : volumeSupply ≠ ⊤ := by
    dsimp only [volumeSupply]
    apply ENNReal.div_ne_top
    exact ENNReal.mul_ne_top
      (ne_top_of_le_ne_top
        Metric.isBounded_closedBall.measure_lt_top.ne
        (MeasureTheory.measure_mono hball))
      ENNReal.ofReal_ne_top
    exact hdenomPos.ne'
  have hunionHeight :
      ∀ point ∈ shading.union,
        point (2 : Fin 3) ∈ Set.Ico
          (left - twoScale.rhoRequested.1)
          (left + Real.sqrt twoScale.rhoRequested.1 +
            twoScale.rhoRequested.1) := by
    intro point hpoint
    have hwindow :
        point ∈ wz1Lemma23CellHeightWindowSet
          twoScale.rhoRequested.1 hrho left := by
      rw [_hshading] at hpoint
      rcases hpoint with ⟨_index, _hsource, hwindow⟩
      exact hwindow
    rcases Set.mem_iUnion₂.mp hwindow with
      ⟨cell, hcell, hpointCell⟩
    have hcenterWindow := (Finset.mem_filter.mp hcell).2
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry
        twoScale.rhoRequested.1 hrho hrhoOne).2.1
        cell point hpointCell).1 (2 : Fin 3)
    rw [abs_le] at hpointCenter
    exact ⟨by linarith [hcenterWindow.1, hpointCenter.2],
      by linarith [hcenterWindow.2, hpointCenter.1]⟩
  exact
    ⟨{ left := left
       shading := shading
       subshading := hsub
       windowed := windowed
       sourceSlope_eq := hslope
       volumeSupply := volumeSupply
       volumeSupply_pos := hsupplyPos
       volumeSupply_ne_top := hsupplyTop
       union_height_window := hunionHeight
       volume_lower := by
         rw [_hshading]
         have hunionRestricted :
             (wz1Lemma23RestrictShadingToCellHeightWindow
                prepared.shadow hrho left).union =
               prepared.shadow.union ∩
                 wz1Lemma23CellHeightWindowSet
                   twoScale.rhoRequested.1 hrho left := by
           ext point
           constructor
           · rintro ⟨index, hpoint⟩
             exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
           · rintro ⟨⟨index, hpoint⟩, hwindow⟩
             exact ⟨index, hpoint, hwindow⟩
         rw [hunionRestricted]
         simpa [volumeSupply] using hvolume }⟩

end Kakeya.Assouad

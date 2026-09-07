import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineResiduePreparation
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalProjectionHeavyFiberInSource
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeavyFiberThreshold
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainNormalBound

/-!
# Full local grains on the same fixed-line residue shadow
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- A half-open interval containment in a closed interval includes both endpoints. -/
private lemma pureWZ2_Ico_containment_closure
    {a b left right : ℝ} (hab : a < b)
    (hsub : Set.Ico a b ⊆ Set.Icc left right) :
    Set.Icc a b ⊆ Set.Icc left right := by
  rw [← closure_Ico hab.ne]
  exact closure_minimal hsub isClosed_Icc

structure PureWZ2HorizontalFixedLineResidueFullGrainFamily
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading) where
  fiberFor :
    ∀ parent (hparent : parent ∈ residue.selected),
      WZ1Lemma23LocalProjectionHeavyFiberInSource
        (rho := prep.graphScale) prep.shadow
          (10 * Kakeya.realRpowENN
            twoScale.rhoRequested.1 (-middleLoss))
          prep.localGrains (sources.sourceFor parent hparent).anchor
          (sources.sourceFor parent hparent).coarseSource
  fullInput :
    ∀ parent (hparent : parent ∈ residue.selected),
      WZ1Lemma23FullLocalGrainInputGeneralized
        prep.graphScale sigma eta
          (10 * Kakeya.realRpowENN
            twoScale.rhoRequested.1 (-middleLoss))
          prep.windowed.global.sourceSlope
  fullInput_center :
    ∀ parent (hparent : parent ∈ residue.selected),
      (fullInput parent hparent).center =
        (sources.sourceFor parent hparent).anchor
  fullInput_normal :
    ∀ parent (hparent : parent ∈ residue.selected),
      (fullInput parent hparent).normal =
        prep.localGrains.planeMap
          (sources.sourceFor parent hparent).anchor
  fullInput_projected :
    ∀ parent (hparent : parent ∈ residue.selected),
      ∀ z,
        (fullInput parent hparent).projected z =
          scalarProjection
            (globalGrainDirection
              (prep.windowed.global.sourceSlope z))
            (horizontalSlice prep.shadow.union z)
  coarse_source_volume :
    ∀ parent (hparent : parent ∈ residue.selected),
      Kakeya.realRpowENN prep.graphScale
          (3 / 2 + sigma / 2 + eta) ≤
        volume (sources.sourceFor parent hparent).coarseSource
  grain_in_source :
    ∀ parent (hparent : parent ∈ residue.selected),
      (fullInput parent hparent).grain ⊆
        (sources.sourceFor parent hparent).coarseSource

theorem PureWZ2HorizontalFixedLineResidueSourceFamily.fullGrains
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading)
    (hsourceAbsorb :
      (512 : ENNReal) *
          Kakeya.realRpowENN prep.graphScale
            (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hconstantPower :
      10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN prep.graphScale (-eta)) :
    Nonempty
      (PureWZ2HorizontalFixedLineResidueFullGrainFamily
        (eta := eta) sources prep) := by
  let C := 10 * Kakeya.realRpowENN
    twoScale.rhoRequested.1 (-middleLoss)
  have hCtop : C ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hCOne : 1 ≤ C := by
    have hlocal := prep.localGrains.local_ad
      prep.graphScale prep.base_le_graphScale prep.graphScale_one
    rcases residue.selected_nonempty with ⟨parent, hparent⟩
    exact (hlocal (sources.sourceFor parent hparent).anchor
      (by
        rw [prep.shadow_union]
        exact sources.anchor_mem parent hparent)).2.2.2.1
  have hfiberExists :
      ∀ parent (hparent : parent ∈ residue.selected),
        Nonempty
          (WZ1Lemma23LocalProjectionHeavyFiberInSource
            (rho := prep.graphScale) prep.shadow C prep.localGrains
            (sources.sourceFor parent hparent).anchor
            (sources.sourceFor parent hparent).coarseSource) := by
    intro parent hparent
    apply wz1_lemma23_local_projection_heavy_fiber_in_source
    · rw [prep.shadow_union]
      exact sources.anchor_mem parent hparent
    · exact (sources.sourceFor parent hparent).coarseSource_measurable
    · exact (sources.sourceFor parent hparent).coarseSource_nonempty
    · intro point hpoint
      have hsource := sources.coarse_source_subset parent hparent hpoint
      rw [prep.shadow_union]
      refine ⟨hsource.1, ?_⟩
      have hsmall := hsource.2
      rw [Metric.mem_closedBall] at hsmall ⊢
      exact hsmall.trans (by
        rw [prep.graphScale_sqrt]
        nlinarith [twoScale.fine.coarse_extremal.delta_pos])
    · exact prep.graphScale_pos
    · exact prep.base_le_graphScale
    · exact prep.graphScale_one
    · exact hCtop
  let fiberFor :
      ∀ parent (hparent : parent ∈ residue.selected),
        WZ1Lemma23LocalProjectionHeavyFiberInSource
          (rho := prep.graphScale) prep.shadow C prep.localGrains
          (sources.sourceFor parent hparent).anchor
          (sources.sourceFor parent hparent).coarseSource := fun parent hparent =>
    Classical.choice (hfiberExists parent hparent)
  have hsourceLower :
      ∀ parent (hparent : parent ∈ residue.selected),
        Kakeya.realRpowENN prep.graphScale
            (3 / 2 + sigma / 2 + eta) ≤
          volume (sources.sourceFor parent hparent).coarseSource := by
    intro parent hparent
    exact (sources.sourceFor parent hparent).volume_lower_target
      (Kakeya.realRpowENN prep.graphScale
        (3 / 2 + sigma / 2 + eta)) hsourceAbsorb
  let fullInput :
      ∀ parent (hparent : parent ∈ residue.selected),
        WZ1Lemma23FullLocalGrainInputGeneralized
          prep.graphScale sigma eta C prep.windowed.global.sourceSlope :=
    fun parent hparent =>
      let data := sources.sourceFor parent hparent
      let fiber := fiberFor parent hparent
      let graphLeft :=
        max (-1 : ℝ)
          (data.heightLeft + twoScale.sqrtRequested.1 -
            Real.sqrt prep.graphScale)
      { grain := fiber.grain
        grain_measurable := fiber.grain_measurable
        grain_finite := fiber.grain_finite
        heightLeft := graphLeft
        grain_height := by
          intro point hpoint
          have hheight := data.source_height point (fiber.grain_in_source hpoint)
          have hroot := twoScale.fine.coarse_extremal.delta_pos
          have hgraphRoot : twoScale.sqrtRequested.1 ≤
              Real.sqrt prep.graphScale := by
            rw [prep.graphScale_sqrt]
            nlinarith
          have hwindowClosed :
              Set.Icc data.heightLeft
                  (data.heightLeft + twoScale.sqrtRequested.1) ⊆
                Set.Icc (-1 : ℝ) 1 :=
            pureWZ2_Ico_containment_closure
              (by linarith [hroot]) data.height_window
          have hminusOne : (-1 : ℝ) ≤ data.heightLeft :=
            (hwindowClosed ⟨le_rfl, by linarith [hroot]⟩).1
          have hsecond :
              data.heightLeft + twoScale.sqrtRequested.1 -
                  Real.sqrt prep.graphScale ≤ data.heightLeft := by
            linarith
          have hgraphLeft : graphLeft ≤ data.heightLeft :=
            max_le hminusOne hsecond
          constructor
          · exact hgraphLeft.trans hheight.1
          · have hright :
                data.heightLeft + twoScale.sqrtRequested.1 ≤
                  graphLeft + Real.sqrt prep.graphScale := by
              have := le_max_right (-1 : ℝ)
                (data.heightLeft + twoScale.sqrtRequested.1 -
                  Real.sqrt prep.graphScale)
              linarith
            exact hheight.2.trans_le hright
        grain_volume := fiber.grain_volume_of_source_lower
          prep.graphScale_pos hCOne hconstantPower (hsourceLower parent hparent)
        center := data.anchor
        normal := prep.localGrains.planeMap data.anchor
        localProjectionCenter := fiber.center
        normal_unit := prep.localGrains.unit data.anchor (by
          rw [prep.shadow_union]
          exact sources.anchor_mem parent hparent)
        normal_vertical := prep.planeMap_vertical_bound data.anchor (by
          rw [prep.shadow_union]
          exact sources.anchor_mem parent hparent)
        grain_square := fiber.grain_square
        grain_local_strip := fiber.grain_local_strip
        slope_small := by
          intro z hz
          rw [prep.sourceSlope_eq]
          exact twoScale.coarseGrains_slope_bound z
            (by
              have hleft : (-1 : ℝ) ≤ graphLeft := le_max_left _ _
              have hgraphOneSqrt : Real.sqrt prep.graphScale ≤ 1 :=
                Real.sqrt_le_one.mpr prep.graphScale_one
              have hright : graphLeft + Real.sqrt prep.graphScale ≤ 1 := by
                dsimp only [graphLeft]
                by_cases hcase : (-1 : ℝ) ≥
                    data.heightLeft + twoScale.sqrtRequested.1 -
                      Real.sqrt prep.graphScale
                · rw [max_eq_left hcase]
                  linarith
                · rw [max_eq_right (le_of_not_ge hcase)]
                  have hdataRight :
                      data.heightLeft + twoScale.sqrtRequested.1 ≤ 1 := by
                    exact (pureWZ2_Ico_containment_closure
                      (by linarith [twoScale.fine.coarse_extremal.delta_pos])
                      data.height_window
                      ⟨by linarith [twoScale.fine.coarse_extremal.delta_pos],
                        le_rfl⟩).2
                  linarith
              exact ⟨hleft.trans hz.1, hz.2.le.trans hright⟩)
        projected := fun z =>
          scalarProjection
            (globalGrainDirection (prep.windowed.global.sourceSlope z))
            (horizontalSlice prep.shadow.union z)
        globalAD := by
          intro z hz
          have hzIcc : z ∈ Set.Icc (-1 : ℝ) 1 := by
            have hleft : (-1 : ℝ) ≤ graphLeft := le_max_left _ _
            have hright : graphLeft + Real.sqrt prep.graphScale ≤ 1 := by
              dsimp only [graphLeft]
              by_cases hcase : (-1 : ℝ) ≥
                  data.heightLeft + twoScale.sqrtRequested.1 -
                    Real.sqrt prep.graphScale
              · rw [max_eq_left hcase]
                have hsqrtOne := Real.sqrt_le_one.mpr prep.graphScale_one
                linarith
              · rw [max_eq_right (le_of_not_ge hcase)]
                have hnonempty := data.coarseSource_nonempty
                have hdataRight :
                    data.heightLeft + twoScale.sqrtRequested.1 ≤ 1 :=
                  (pureWZ2_Ico_containment_closure
                    (by linarith [twoScale.fine.coarse_extremal.delta_pos])
                    data.height_window
                    ⟨by linarith [twoScale.fine.coarse_extremal.delta_pos],
                      le_rfl⟩).2
                linarith
            exact ⟨hleft.trans hz.1, hz.2.le.trans hright⟩
          exact prep.exactAD z hzIcc
        global_projection_sub := by
          intro z _
          rintro value ⟨point, hpoint, rfl⟩
          have hlift : point3 (point 0) (point 1) z ∈ fiber.grain :=
            wz1Lemma23_mem_planarSlice_iff.mp hpoint
          have hshadow := fiber.grain_in_shading hlift
          refine ⟨point3 (point 0) (point 1) z,
            ⟨hshadow, by simp [point3]⟩, ?_⟩
          change inner ℝ (point3 (point 0) (point 1) z)
              (globalGrainDirection (prep.windowed.global.sourceSlope z)) =
            point 0 + prep.windowed.global.sourceSlope z * point 1
          rw [PiLp.inner_apply]
          simp [Fin.sum_univ_succ, globalGrainDirection, point3] }
  exact
    ⟨{ fiberFor := fiberFor
       fullInput := fullInput
       fullInput_center := by
         intro parent hparent
         rfl
       fullInput_normal := by
         intro parent hparent
         rfl
       fullInput_projected := by
         intro parent hparent z
         rfl
       coarse_source_volume := hsourceLower
       grain_in_source := by
         intro parent hparent
         exact (fiberFor parent hparent).grain_in_source }⟩

end Kakeya.Assouad

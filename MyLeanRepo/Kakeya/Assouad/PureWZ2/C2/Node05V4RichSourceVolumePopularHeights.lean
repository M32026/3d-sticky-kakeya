import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedAllSlabs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HeightVolumePopularity

/-!
# Source-volume regularization inside the paper's `Z_S`

Before the auxiliary Theorem-5.2 graph is formed, first construct the
paper-literal continuous set `Z_S` by source slice mass.  Its source
restriction is then regularized by genuine union volume in graph-height
slabs.  The dyadic band is auxiliary bookkeeping inside `Z_S`; it is not
itself identified with the paper's `Z_S`.

No graph cell, saturated carrier, or independently selected family occurs in
either selection.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The source-volume-popular height band attached to one exact heavy slab. -/
structure PureWZ2Node05V4RichSourceVolumePopularHeightData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) where
  continuous : pullback.SourcePopularHeightData heightIndex.1
  sourcePopularShading : WZ1PaperTubeShading current.grain.family
  sourcePopularShading_carrier : ∀ index,
    sourcePopularShading.carrier index =
      (pullback.standardSqrtSlabSourceShading heightIndex.1.1).carrier index ∩
        {point | point (2 : Fin 3) ∈ continuous.popularHeights}
  sourcePopularShading_union :
    sourcePopularShading.union = continuous.popularRegion
  sourcePopularShading_sub_slab :
    PureWZ2PaperIsSubshading sourcePopularShading
      (pullback.standardSqrtSlabSourceShading heightIndex.1.1)
  popular : PureWZ2HeightVolumePopularData
    sourcePopularShading (256 * rho)

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

/-- Regularize source volume inside an already selected paper `Z_S`.  This
variant is used after the fixed line has been chosen: it preserves that exact
continuous height witness instead of invoking `sourcePopularHeightData` a
second time. -/
theorem sourceVolumePopularHeightDataOfContinuous
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (continuous : pullback.SourcePopularHeightData heightIndex.1) :
    Nonempty
      (PureWZ2Node05V4RichSourceVolumePopularHeightData
        pullback heightIndex) := by
  let slabShading :=
    pullback.standardSqrtSlabSourceShading heightIndex.1.1
  have hheightMeas : MeasurableSet
      {point : Point3 | point (2 : Fin 3) ∈ continuous.popularHeights} :=
    continuous.popularHeights_measurable.preimage (by fun_prop)
  let sourceShading : WZ1PaperTubeShading current.grain.family :=
    { carrier := fun index =>
        slabShading.carrier index ∩
          {point | point (2 : Fin 3) ∈ continuous.popularHeights}
      measurable_carrier := fun index =>
        (slabShading.measurable_carrier index).inter hheightMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (slabShading.subset_body index) }
  have hsourceUnion :
      sourceShading.union = continuous.popularRegion := by
    rw [continuous.popularRegion_eq]
    unfold PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularRegion
    rw [← continuous.popularHeights_eq]
    rw [← pullback.standardSqrtSlabSourceShading_union heightIndex.1.1]
    ext point
    constructor
    · rintro ⟨index, hslab, hheight⟩
      exact ⟨⟨index, hslab⟩, hheight⟩
    · rintro ⟨⟨index, hslab⟩, hheight⟩
      exact ⟨index, hslab, hheight⟩
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hsourcePos : 0 < volume sourceShading.union := by
    rw [hsourceUnion]
    have hslabPos :=
      pullback.standardSqrtSlabSourceRegion_volume_pos heightIndex.1.2
    have hhalfPos :
        0 <
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 :=
      ENNReal.div_pos hslabPos.ne' (by norm_num)
    exact hhalfPos.trans_le continuous.popularRegion_half_volume
  have hsourceBall :
      sourceShading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    rw [hsourceUnion] at hpoint
    rw [continuous.popularRegion_eq,
      PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularRegion] at hpoint
    have hsource :
        point ∈ current.grain.shading.union :=
      (pullback.standardSqrtSlabSourceShading_sub_source
        heightIndex.1.1).union_subset (by
          rw [pullback.standardSqrtSlabSourceShading_union]
          exact hpoint.1)
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsourceTop : volume sourceShading.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hsourceBall)
  rcases pureWZ2_heightVolumePopularity sourceShading (256 * rho)
      (by positivity) hsourceBall hsourcePos hsourceTop with
    ⟨popular⟩
  exact ⟨{
    continuous := continuous
    sourcePopularShading := sourceShading
    sourcePopularShading_carrier := fun _ => rfl
    sourcePopularShading_union := hsourceUnion
    sourcePopularShading_sub_slab := fun _ => Set.inter_subset_left
    popular := popular
  }⟩

/-- Select the paper's continuous `Z_S`, then its weighted graph-height band,
before any graph or line output. -/
theorem sourceVolumePopularHeightData
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    Nonempty
      (PureWZ2Node05V4RichSourceVolumePopularHeightData
        pullback heightIndex) := by
  rcases pullback.sourcePopularHeightData heightIndex.1 with ⟨continuous⟩
  exact pullback.sourceVolumePopularHeightDataOfContinuous
    heightIndex continuous

end PureWZ2Node05V4RichTwoScaleCellPullbackData

namespace PureWZ2Node05V4RichSourceVolumePopularHeightData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (data :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)

/-- A volume-popular graph-height band inside one side-`sqrt rho` source slab
has the paper's single half-power cardinality. -/
theorem heightIndices_card_le_four_sqrt_inv :
    (data.popular.heightIndices.card : ENNReal) ≤
      4 * Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  let width := gridSide ((256 * rho) / 2)
  have hwidth : 0 < width := by
    dsimp only [width, gridSide]
    positivity
  let slabLeft := (heightIndex.1.1 : ℝ) * Real.sqrt rho
  let slabRight := slabLeft + Real.sqrt rho
  let lower : ℤ := Int.floor (slabLeft / width) - 1
  let upper : ℤ := Int.floor (slabRight / width)
  have hsubset :
      data.popular.heightIndices ⊆ Finset.Icc lower upper := by
    intro selectedHeight hselectedHeight
    have hlayerPos :
        0 < volume (data.sourcePopularShading.union ∩
          wz1Lemma23HeightSlab (256 * rho) selectedHeight) :=
      data.popular.layerMass_pos.trans_le
        (data.popular.layer_volume_band
          selectedHeight hselectedHeight).1
    rcases nonempty_of_measure_ne_zero hlayerPos.ne' with
      ⟨point, hsource, hpointHeight⟩
    have hslabSource :
        point ∈ pullback.standardSqrtSlabSourceRegion heightIndex.1.1 := by
      have hsource' :=
        data.sourcePopularShading_sub_slab.union_subset hsource
      rwa [pullback.standardSqrtSlabSourceShading_union] at hsource'
    have hsourceHeight :=
      pullback.standardSqrtSlabSourceRegion_height hslabSource
    change point (2 : Fin 3) ∈
      wz1Lemma23HeightInterval (256 * rho) selectedHeight at hpointHeight
    have hwidthEq :
        gridSide ((256 * rho) / 2) = width := rfl
    rw [wz1Lemma23HeightInterval, hwidthEq] at hpointHeight
    have hlowerReal :
        slabLeft / width < (selectedHeight : ℝ) + 1 := by
      rw [div_lt_iff₀ hwidth]
      dsimp only [slabLeft]
      linarith [hsourceHeight.1, hpointHeight.2]
    have hupperReal :
        (selectedHeight : ℝ) < slabRight / width := by
      rw [lt_div_iff₀ hwidth]
      dsimp only [slabRight, slabLeft]
      linarith [hsourceHeight.2, hpointHeight.1]
    rw [Finset.mem_Icc]
    constructor
    · dsimp only [lower]
      have hfloor :=
        Int.floor_mono hlowerReal.le
      rw [Int.floor_intCast_add] at hfloor
      norm_num at hfloor
      omega
    · dsimp only [upper]
      have hfloor := Int.floor_mono hupperReal.le
      simpa using hfloor
  have hlowerUpper : lower ≤ upper + 1 := by
    rcases data.popular.heightIndices_nonempty with
      ⟨selectedHeight, hselectedHeight⟩
    have hmem := hsubset hselectedHeight
    rw [Finset.mem_Icc] at hmem
    omega
  have hcardInt :
      ((Finset.Icc lower upper).card : ℤ) = upper + 1 - lower :=
    Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal :
      (data.popular.heightIndices.card : ℝ) ≤
        (upper : ℝ) + 1 - lower := by
    have hcast :
        (data.popular.heightIndices.card : ℤ) ≤
          (Finset.Icc lower upper).card := by
      exact_mod_cast Finset.card_le_card hsubset
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupperFloor : (upper : ℝ) ≤ slabRight / width := by
    exact Int.floor_le _
  have hlowerFloor : slabLeft / width < (Int.floor
      (slabLeft / width) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hcardBound :
      (data.popular.heightIndices.card : ℝ) ≤
        Real.sqrt rho / width + 3 := by
    dsimp only [upper, lower] at hcardReal hupperFloor ⊢
    norm_num only [Int.cast_sub, Int.cast_one] at hcardReal
    have hquotient :
        slabRight / width - slabLeft / width =
          Real.sqrt rho / width := by
      dsimp only [slabRight]
      ring
    rw [← hquotient]
    linarith
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg (3 : ℝ)]
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hrootOne : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
  have hsqrtThreePos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hratio :
      Real.sqrt rho / width ≤ 1 / Real.sqrt rho := by
    have hrootSq : Real.sqrt rho * Real.sqrt rho = rho := by
      nlinarith [Real.sq_sqrt hrho.le]
    have hratioEq :
        Real.sqrt rho / width =
          Real.sqrt 3 / (256 * Real.sqrt rho) := by
      dsimp only [width, gridSide]
      field_simp [hrho.ne', hroot.ne', hsqrtThreePos.ne']
      nlinarith
    rw [hratioEq]
    rw [div_le_iff₀ (mul_pos (by norm_num) hroot),
      one_div]
    rw [show (Real.sqrt rho)⁻¹ * (256 * Real.sqrt rho) = 256 by
      field_simp [hroot.ne']]
    nlinarith
  have hreal :
      (data.popular.heightIndices.card : ℝ) ≤
        4 / Real.sqrt rho := by
    calc
      _ ≤ Real.sqrt rho / width + 3 := hcardBound
      _ ≤ 1 / Real.sqrt rho + 3 := by gcongr
      _ ≤ 4 / Real.sqrt rho := by
        rw [show 4 / Real.sqrt rho =
          1 / Real.sqrt rho + 3 / Real.sqrt rho by ring]
        gcongr
        exact (le_div_iff₀ hroot).2 (by nlinarith)
  have henn := ENNReal.ofReal_mono hreal
  have hrpow :
      ENNReal.ofReal (1 / Real.sqrt rho) =
        Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) := by
    rw [Kakeya.realRpowENN]
    congr 1
    calc
      1 / Real.sqrt rho = (Real.sqrt rho)⁻¹ := one_div _
      _ = (Real.rpow rho (1 / 2 : ℝ))⁻¹ := by
        congr 1
        exact Real.sqrt_eq_rpow rho
      _ = Real.rpow rho (-(1 / 2 : ℝ)) :=
        (Real.rpow_neg hrho.le (1 / 2 : ℝ)).symm
  have hfour :
      ENNReal.ofReal (4 / Real.sqrt rho) =
        4 * ENNReal.ofReal (1 / Real.sqrt rho) := by
    rw [show 4 / Real.sqrt rho = 4 * (1 / Real.sqrt rho) by ring,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hfour, hrpow] at henn
  simpa using henn

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end

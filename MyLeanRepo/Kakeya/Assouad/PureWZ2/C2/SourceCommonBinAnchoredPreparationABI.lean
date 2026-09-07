import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredSeparated
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseGlobalPreparation
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GeometricInput

/-!
# Construction-independent anchored graph preparation
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2AnchoredRhoShadowData
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
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    {weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block}
    (separated : PureWZ2AnchoredSeparatedShadingData weighted) where
  shading : WZ1PaperTubeShading coarse.coarse
  carrier_eq : ∀ index,
    shading.carrier index =
      coarse.croppedCoarseShading.carrier index ∩
        separated.pullback.shading.union
  union_eq : shading.union = separated.pullback.shading.union

theorem PureWZ2AnchoredSeparatedShadingData.toRhoShadow
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
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    {weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block}
    (separated : PureWZ2AnchoredSeparatedShadingData weighted) :
    Nonempty (PureWZ2AnchoredRhoShadowData separated) := by
  let shading : WZ1PaperTubeShading coarse.coarse := {
    carrier := fun index =>
      coarse.croppedCoarseShading.carrier index ∩
        separated.pullback.shading.union
    measurable_carrier := fun index =>
      (coarse.croppedCoarseShading.measurable_carrier index).inter
        separated.pullback.shading.union_measurable
    subset_body := fun index =>
      Set.inter_subset_left.trans
        (coarse.croppedCoarseShading.subset_body index)
  }
  have hsourceSub :
      separated.pullback.shading.union ⊆
        coarse.croppedCoarseShading.union := by
    intro point hpoint
    rcases hpoint with ⟨sourceIndex, hsourcePoint⟩
    rw [separated.pullback.carrier_eq sourceIndex] at hsourcePoint
    rcases selected.zeroExtension.carrier_support
        sourceIndex point hsourcePoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    rcases coarse.data.cover.covers selectedIndex with ⟨parent, hcover⟩
    exact ⟨parent,
      coarse.balanced.point_compatibility selectedIndex parent hcover point
        hselected⟩
  have hunion : shading.union = separated.pullback.shading.union := by
    ext point
    constructor
    · rintro ⟨index, _hcoarse, hsource⟩
      exact hsource
    · intro hsource
      rcases hsourceSub hsource with ⟨index, hcoarse⟩
      exact ⟨index, hcoarse, hsource⟩
  exact ⟨{
    shading := shading
    carrier_eq := fun _ => rfl
    union_eq := hunion
  }⟩

namespace PureWZ2AnchoredRhoShadowData

variable
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
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    {weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block}
    {separated : PureWZ2AnchoredSeparatedShadingData weighted}
    (rhoShadow : PureWZ2AnchoredRhoShadowData separated)

def shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily rhoShadow.shading
      coarse.coarse_extremal.delta_pos) :=
  pureWZ2PartialActiveCellShading rhoShadow.shading
    coarse.coarse_extremal.delta_pos

theorem shadow_union :
    rhoShadow.shadow.union = separated.pullback.shading.union := by
  rw [shadow, pureWZ2PartialActiveCellShading_union, rhoShadow.union_eq]

end PureWZ2AnchoredRhoShadowData

/-- The global analytic input is independent of any grain package. -/
structure PureWZ2AnchoredGraphGlobalInput
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shadow : Kakeya.Streamlined.TubeShading family) (C : ENNReal) where
  rho_pos : 0 < rho
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  sourceSlope : ℝ → ℝ
  sourceSlope_lipschitz :
    LipschitzOnWith 1 sourceSlope (Set.Icc (-1 : ℝ) 1)
  sourceSlope_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1, |sourceSlope z| ≤ 3
  constant_ne_top : C ≠ ⊤
  shadow_ball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2
  shadow_coordinate :
    ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma) C

noncomputable def PureWZ2AnchoredRhoShadowData.toGlobalInput
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
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    {weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block}
    {separated : PureWZ2AnchoredSeparatedShadingData weighted}
    (rhoShadow : PureWZ2AnchoredRhoShadowData separated)
    (C : ENNReal)
    (hsourceAbsorb : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN rhoRequested.1 (-coarseLoss))
    (hCAbsorb : Kakeya.realRpowENN rhoRequested.1 (-coarseLoss) ≤ C)
    (hCTop : C ≠ ⊤)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rhoRequested.1 ≤ 1) :
    PureWZ2AnchoredGraphGlobalInput
      (rho := 256 * rhoRequested.1) (sigma := sigma)
      rhoShadow.shadow (10 * C) := by
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  have hcoord : ∀ point ∈ rhoShadow.shadow.union,
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    rw [rhoShadow.shadow_union] at hpoint
    have hsource := separated.pullback.subshading.union_subset hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  refine {
    rho_pos := mul_pos (by norm_num) hrho
    delta_le_rho := by nlinarith
    rho_le_one := hgraphOne
    sourceSlope := source.globalGrains.slope
    sourceSlope_lipschitz := source.globalGrains.slope_lipschitz
    sourceSlope_bound := source.globalGrains.slope_bound
    constant_ne_top := ENNReal.mul_ne_top (by norm_num) hCTop
    shadow_ball := ?_
    shadow_coordinate := hcoord
    exactAD := ?_
  }
  · intro point hpoint
    rw [rhoShadow.shadow_union] at hpoint
    have hnorm := norm_le_two_of_mem_paperShading
      (separated.pullback.subshading.union_subset hpoint)
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  · intro z hz
    have hsubset :
        scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice rhoShadow.shadow.union z) ⊆
          scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice selected.shading.union z) := by
      rintro value ⟨point, hpoint, rfl⟩
      refine ⟨point, ⟨?_, hpoint.2⟩, rfl⟩
      have hunion := hpoint.1
      rw [rhoShadow.shadow_union, separated.pullback.union_eq] at hunion
      rw [selected.union_eq]
      refine ⟨hunion.1, ?_⟩
      rw [separated.pullback.region_eq] at hunion
      rw [selected.selectedRegion_eq]
      rcases Set.mem_iUnion₂.mp hunion.2 with ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr ⟨cell,
        data.cells_subset_selected
          (block.envelope.cells_subset
            (weighted.selectedCells_subset hcell)),
        hpointCell⟩
    have hpaper := (selected.global_ad hsourceAbsorb z hz).mono hsubset
    have hpaperC := hpaper.mono_const hCAbsorb hCTop
    have hbound :
        scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice rhoShadow.shadow.union z) ⊆
          Set.Icc (-4 : ℝ) 4 := by
      rintro value ⟨point, hpoint, rfl⟩
      have hslope := source.globalGrains.slope_bound z hz
      have hp0 := hcoord point hpoint.1 (0 : Fin 3)
      have hp1 := hcoord point hpoint.1 (1 : Fin 3)
      have hformula :
          inner ℝ point
              (globalGrainDirection (source.globalGrains.slope z)) =
            point 0 + source.globalGrains.slope z * point 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      have habs :
          |point 0 + source.globalGrains.slope z * point 1| ≤ 4 := by
        calc
          _ ≤ |point 0| +
              |source.globalGrains.slope z| * |point 1| := by
            simpa [abs_mul] using
              abs_add_le (point 0) (source.globalGrains.slope z * point 1)
          _ ≤ 1 + 3 * 1 := by gcongr
          _ = 4 := by norm_num
      change -4 ≤ inner ℝ point
          (globalGrainDirection (source.globalGrains.slope z)) ∧
        inner ℝ point
          (globalGrainDirection (source.globalGrains.slope z)) ≤ 4
      rw [hformula]
      exact abs_le.mp habs
    exact hbridge.1 _ rhoRequested.1 (1 - sigma) C hbound hpaperC

/-- Window/localization ABI consumed by all later WZ1 graph stages. -/
structure PureWZ2AnchoredGraphPreparationData
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    (globalInput : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C) where
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := rho) (sigma := sigma) shadow C
  sourceSlope_eq : windowed.global.sourceSlope = globalInput.sourceSlope
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (windowed.global.sourceSlope z))
          (horizontalSlice shadow.union z))
        rho (1 - sigma) C
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global
  shadow_coordinate :
    ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1

theorem pureWZ2_anchoredGraphPreparation
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    (input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C)
    (heightWindow : ∀ global :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) shadow C,
      global.sourceSlope = input.sourceSlope →
        WZ1Lemma23ActiveCellHeightWindow shadow global.rho_pos)
    (localization : ∀ global :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) shadow C,
      global.sourceSlope = input.sourceSlope →
        WZ1Lemma23GlobalLocalizationInput global) :
    Nonempty (PureWZ2AnchoredGraphPreparationData input) := by
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow input.rho_pos input.delta_le_rho input.rho_le_one
      input.shadow_ball input.shadow_coordinate
      input.sourceSlope input.sourceSlope_lipschitz input.sourceSlope_bound
      C input.constant_ne_top input.exactAD with
    ⟨global, hslope⟩
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shadow C := {
    global := global
    active_height_window := heightWindow global hslope
  }
  have hlocal : WZ1Lemma23GlobalLocalizationInput windowed.global :=
    localization global hslope
  exact ⟨{
    windowed := windowed
    sourceSlope_eq := hslope
    exactAD := by
      intro z hz
      rw [hslope]
      exact (input.exactAD z hz).coarsen_scale input.rho_pos
        input.delta_le_rho input.rho_le_one
    localization := hlocal
    shadow_coordinate := input.shadow_coordinate
  }⟩

end Kakeya.Assouad

end

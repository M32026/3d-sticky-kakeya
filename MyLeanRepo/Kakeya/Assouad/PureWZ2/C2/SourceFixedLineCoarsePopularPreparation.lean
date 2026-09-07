import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePopularCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePreparation

/-!
# Lemma-23 preparation on the outer-popular genuine coarse carrier

This is the synchronized replacement for the full genuine-coarse preparation.
Its graph shadow is the first-sticky coarse carrier restricted to the source
outer-popular height region.  Exact-slice AD is inherited by restriction from
the original-slope coarse certificate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceFixedBinPopularCoarsePreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    (popularCoarse : PureWZ2SourceFixedBinPopularCoarseCarrierData
      outerPopular retained carrier) : Type where
  graphScale : ℝ := 256 * rho
  graphScale_eq : graphScale = 256 * rho
  graphScale_pos : 0 < graphScale
  graphScale_one : graphScale ≤ 1
  graphScale_sqrt :
    Real.sqrt graphScale = 16 * twoScale.sqrtRequested.1
  graphScale_two_root_bound :
    graphScale + 2 * twoScale.sqrtRequested.1 ≤
      16 * twoScale.sqrtRequested.1
  rho_le_graphScale : rho ≤ graphScale
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily carrier.shading
      twoScale.coarseGrains.extremal.delta_pos) := popularCoarse.shading
  shadow_eq : shadow = popularCoarse.shading
  shadow_union : shadow.union =
    carrier.shading.union ∩ outerPopular.popular.heightRegion
  shadow_union_subset : shadow.union ⊆ carrier.shading.union
  shadow_height_region : shadow.union ⊆
    outerPopular.popular.heightRegion
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := twoScale.rhoRequested.1) (rho := graphScale)
    (sigma := sigma) shadow
    (10 * Kakeya.realRpowENN rho (-middleLoss))
  sourceSlope_eq :
    windowed.global.sourceSlope = source.globalGrains.slope
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (windowed.global.sourceSlope z))
          (horizontalSlice shadow.union z))
        graphScale (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))
  fixed_line_localization :
    ∀ point ∈ shadow.union,
      |inner ℝ point
          (globalGrainDirection
            (windowed.global.sourceSlope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global

/-- Forget the construction-specific outer-popular fields and expose the
common genuine-coarse preparation interface consumed by Lemma 23. -/
def PureWZ2SourceFixedBinPopularCoarsePreparationData.toCoarsePreparation
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses :
      PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {popularCoarse : PureWZ2SourceFixedBinPopularCoarseCarrierData
      outerPopular retained carrier}
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses)
    (data : PureWZ2SourceFixedBinPopularCoarsePreparationData popularCoarse) :
    PureWZ2SourceFixedBinCoarsePreparationData original where
  graphScale := data.graphScale
  graphScale_eq := data.graphScale_eq
  graphScale_pos := data.graphScale_pos
  graphScale_one := data.graphScale_one
  graphScale_sqrt := data.graphScale_sqrt
  graphScale_two_root_bound := data.graphScale_two_root_bound
  rho_le_graphScale := data.rho_le_graphScale
  shadow := data.shadow
  shadow_union_subset := data.shadow_union_subset
  windowed := data.windowed
  sourceSlope_eq := data.sourceSlope_eq
  exactAD := data.exactAD
  fixed_line_localization := data.fixed_line_localization
  localization := data.localization

theorem PureWZ2SourceFixedBinPopularCoarseCarrierData.union_subset_coarse
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    (popularCoarse : PureWZ2SourceFixedBinPopularCoarseCarrierData
      outerPopular retained carrier) :
    popularCoarse.shading.union ⊆ carrier.shading.union := by
  rw [popularCoarse.union_eq]
  exact Set.inter_subset_left

/-- Prepare the synchronized genuine-coarse graph without reintroducing
discarded source heights.  Positivity is intentionally not needed here; it is
the separate all-bin quantitative obligation. -/
theorem PureWZ2SourceFixedBinPopularCoarseCarrierData.prepareFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses :
      PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    (popularCoarse : PureWZ2SourceFixedBinPopularCoarseCarrierData
      outerPopular retained carrier)
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceFixedBinPopularCoarsePreparationData
      popularCoarse) := by
  let graphScale := 256 * rho
  let C : ENNReal := 10 * Kakeya.realRpowENN rho (-middleLoss)
  have hrho : 0 < rho := line.rho_pos
  have hroot : 0 < twoScale.sqrtRequested.1 :=
    twoScale.fine.coarse_extremal.delta_pos
  have hgraph : 0 < graphScale := by positivity
  have hrhoGraph : rho ≤ graphScale := by
    dsimp only [graphScale]
    nlinarith
  have hsqrtRho : twoScale.sqrtRequested.1 = Real.sqrt rho :=
    twoScale.sqrtRequested_eq
  have hsqrtGraph : Real.sqrt graphScale =
      16 * twoScale.sqrtRequested.1 := by
    rw [show graphScale = 256 * rho by rfl,
      Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (256 : ℝ) = 16 by norm_num, ← hsqrtRho]
  have hshadowSub : popularCoarse.shading.union ⊆
      carrier.shading.union := popularCoarse.union_subset_coarse
  have hball : popularCoarse.shading.union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcoarse := carrier.subshading.union_subset (hshadowSub hpoint)
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ popularCoarse.shading.union,
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset (hshadowSub hpoint))
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexactBase :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice popularCoarse.shading.union z))
          twoScale.rhoRequested.1 (1 - sigma) C := by
    intro z hz
    have hmono :
        scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice popularCoarse.shading.union z) ⊆
          scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice carrier.shading.union z) := by
      rintro value ⟨point, hpoint, rfl⟩
      exact ⟨point, ⟨hshadowSub hpoint.1, hpoint.2⟩, rfl⟩
    have h := (original.original_slope_exactADFixedBin z hz).mono hmono
    simpa only [twoScale.rhoRequested_eq, C] using h
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      popularCoarse.shading hgraph
      (by simpa [twoScale.rhoRequested_eq] using hrhoGraph)
      hgraphOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound C hCtop hexactBase with
    ⟨global, hsourceSlope⟩
  let left := (carrier.commonParentHeight : ℝ) *
    twoScale.sqrtRequested.1 - graphScale / 2
  have hactiveWindow : WZ1Lemma23ActiveCellHeightWindow
      popularCoarse.shading global.rho_pos := by
    refine ⟨left, ?_⟩
    intro cell hcell
    have hactive := (wz1Lemma23_mem_active_iff
      popularCoarse.shading hgraph cell).mp hcell
    rcases hactive.2 with ⟨point, hpoint, hpointCell⟩
    have hheight := carrier.union_height point (hshadowSub hpoint)
    have hcenter := ((wz1_lemma23_snapped_cell_geometry
      graphScale hgraph hgraphOne).2.1 cell point hpointCell).1
        (2 : Fin 3)
    rw [abs_le] at hcenter
    constructor
    · dsimp only [left]
      linarith [hheight.1, hcenter.2]
    · dsimp only [left]
      rw [hsqrtGraph]
      have hshort : graphScale + twoScale.sqrtRequested.1 ≤
          16 * twoScale.sqrtRequested.1 := by
        linarith [hheightAbsorb]
      linarith [hheight.2, hcenter.1]
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := twoScale.rhoRequested.1) (rho := graphScale)
      (sigma := sigma) popularCoarse.shading C :=
    { global := global
      active_height_window := hactiveWindow }
  have hexactGraph :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (global.sourceSlope z))
            (horizontalSlice popularCoarse.shading.union z))
          graphScale (1 - sigma) C := by
    intro z hz
    rw [hsourceSlope]
    exact (hexactBase z hz).coarsen_scale hgraph
      (by simpa [twoScale.rhoRequested_eq] using hrhoGraph) hgraphOne
  have hfixedLine :
      ∀ point ∈ popularCoarse.shading.union,
        |inner ℝ point
            (globalGrainDirection
              (global.sourceSlope (point (2 : Fin 3)))) -
          line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1 := by
    intro point hpoint
    rw [hsourceSlope]
    exact carrier.fixed_line_localizationFixedBin point (hshadowSub hpoint)
  have hlocalization : WZ1Lemma23GlobalLocalizationInput windowed.global := by
    refine ⟨fun _ => line.lineLevel, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hbound := hfixedLine point hpoint.1
    rw [hpoint.2] at hbound
    rw [Metric.mem_closedBall, Real.dist_eq, hsqrtGraph]
    exact hbound.trans (by nlinarith [hroot])
  exact ⟨{
    graphScale := graphScale
    graphScale_eq := rfl
    graphScale_pos := hgraph
    graphScale_one := hgraphOne
    graphScale_sqrt := hsqrtGraph
    graphScale_two_root_bound := by
      simpa [graphScale] using hheightAbsorb
    rho_le_graphScale := hrhoGraph
    shadow := popularCoarse.shading
    shadow_eq := rfl
    shadow_union := popularCoarse.union_eq
    shadow_union_subset := hshadowSub
    shadow_height_region := popularCoarse.height_region
    windowed := windowed
    sourceSlope_eq := hsourceSlope
    exactAD := hexactGraph
    fixed_line_localization := hfixedLine
    localization := hlocalization
  }⟩

/-- Prepare the whole-cell outer-popular envelope.  The returned equality is
kept explicit so later aggregate volume selection uses this exact shadow. -/
theorem PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData.prepareFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    (envelope : PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      outerPopular retained carrier)
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    ∃ prep : PureWZ2SourceFixedBinCoarsePreparationData original,
      prep.shadow = envelope.shading := by
  exact original.prepareSubshadowFixedBin envelope.shading
    envelope.union_subset_coarse hgraphOne hheightAbsorb

end Kakeya.Assouad

end

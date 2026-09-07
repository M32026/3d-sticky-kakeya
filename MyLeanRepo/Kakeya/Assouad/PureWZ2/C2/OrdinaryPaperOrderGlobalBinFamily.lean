import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPopularPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGraphParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalFineWitnesses
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseCarrier

/-!
# All global-bin preparations in one ordinary source block

The ordinary Lemma-24 construction first chooses a source-volume-popular
height set and one exact horizontal slice.  This module then retains every
nonempty global-bin fibre of that common slice.  Each fibre carries its own
genuine second-sticky parents, separated y-residue, original-family shading,
outer-popular graph shadow, graph preparation, and original fine witnesses.

No ready-graph volume lower bound is asserted here: it is false in general
for every individual bin.  The exact slice-cardinality partition is retained
for the subsequent aggregate argument.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- All source-horizontal global-bin preparations associated with one
paper-ordered source block. -/
structure PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow) where
  /-- The slice is selected from the whole-cell envelope of the outer-popular
  height set.  It is intentionally distinct from the legacy maximal-bin line
  selected from the exact partial-height shading. -/
  line : PureWZ2SourceHorizontalFixedLineData carriers.outerPopular.windowed
  core : ∀ bin : {bin // bin ∈ line.globalBins},
    PureWZ2SourceHorizontalFixedBinData carriers.outerPopular.windowed
  lineBin_eq : ∀ bin, (core bin).lineBin = bin.1
  heavyCells_eq : ∀ bin, (core bin).heavyCells =
    pureWZ2SourceHorizontalGlobalBinCells line bin.1
  parents : ∀ bin, PureWZ2SourceHorizontalFixedBinParentData (core bin)
  selection : ∀ bin, PureWZ2SourceHorizontalFixedBinYSelection (parents bin)
  residue : ∀ bin,
    PureWZ2SourceHorizontalFixedBinYResidueData (selection bin)
  sourceRetained : ∀ bin,
    PureWZ2SourceHorizontalFixedBinResidueShadingData (residue bin)
  sourceRetained_shadow_union : ∀ bin,
    (sourceRetained bin).graphShadow.union =
      (sourceRetained bin).shading.union
  /-- The genuine first-sticky carrier over the same selected second-sticky
  parents.  This is the paper's local-Lemma-23 spatial carrier. -/
  coarseCarrier : ∀ bin,
    PureWZ2SourceFixedBinCoarseCarrierData (residue bin)
  popularSourceCarrier : ∀ bin,
    PureWZ2SourceHorizontalFixedBinPopularCarrierData
      carriers.outerPopular (sourceRetained bin)
  graphRetained : ∀ bin,
    PureWZ2SourceHorizontalFixedBinResidueShadingData (residue bin) :=
      fun bin => (sourceRetained bin).withPopularGraphFixedBin
        (popularSourceCarrier bin)
  graphRetained_eq : ∀ bin, graphRetained bin =
    (sourceRetained bin).withPopularGraphFixedBin (popularSourceCarrier bin)
  prep : ∀ bin,
    PureWZ2SourceHorizontalFixedBinResiduePreparation (graphRetained bin)
  graphParents : ∀ bin,
    PureWZ2SourceHorizontalFixedBinGraphParentData (prep bin)
  fineWitnesses : ∀ bin,
    PureWZ2SourceHorizontalFixedBinFineWitnessData (graphRetained bin)
  original_slope_eq : ∀ bin,
    (prep bin).windowed.global.sourceSlope = source.globalGrains.slope
  graph_point_near_height_region : ∀ bin point,
    point ∈ (prep bin).shadow.union →
      ∃ anchor ∈ carriers.outerPopular.popular.heightRegion,
        dist point anchor < 2 * delta
  slice_card : line.sliceCells.card =
    ∑ bin : {bin // bin ∈ line.globalBins},
      (core bin).heavyCells.card

/-- Construct every nonempty global-bin preparation on the same exact source
slice.  This is the ordinary analogue of the terminal all-bin parent and
prepared-family constructors, with the pre-graph outer-popular restriction
kept explicit. -/
theorem PureWZ2OrdinaryPaperOrderCarrierAtWindowData.prepareAllGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers) := by
  have henvelopeVolume : 0 <
      volume carriers.outerPopular.windowed.shading.union :=
    carriers.outerPopular.windowed.volumeSupply_pos.trans_le
      carriers.outerPopular.windowed.volume_lower
  let line : PureWZ2SourceHorizontalFixedLineData
      carriers.outerPopular.windowed :=
    Classical.choice
      (carriers.outerPopular.windowed.selectHorizontalFixedLine henvelopeVolume)
  let core : ∀ bin : {bin // bin ∈ line.globalBins},
      PureWZ2SourceHorizontalFixedBinData
        carriers.outerPopular.windowed := fun bin =>
    Classical.choose (line.coreAtGlobalBin bin.1 bin.2)
  let parents : ∀ bin,
      PureWZ2SourceHorizontalFixedBinParentData (core bin) := fun bin =>
    Classical.choice ((core bin).toParents)
  let selection : ∀ bin,
      PureWZ2SourceHorizontalFixedBinYSelection (parents bin) := fun bin =>
    Classical.choice ((parents bin).selectOnePerYFixedBin)
  let residue : ∀ bin,
      PureWZ2SourceHorizontalFixedBinYResidueData (selection bin) := fun bin =>
    Classical.choice ((selection bin).selectResidueFixedBin)
  let sourceRetained : ∀ bin,
      PureWZ2SourceHorizontalFixedBinResidueShadingData (residue bin) :=
    fun bin => Classical.choose ((residue bin).retainSourceShadingFixedBin)
  let coarseCarrier : ∀ bin,
      PureWZ2SourceFixedBinCoarseCarrierData (residue bin) := fun bin =>
    Classical.choice ((residue bin).retainCoarseCarrierFixedBin)
  let popularSourceCarrier : ∀ bin,
      PureWZ2SourceHorizontalFixedBinPopularCarrierData
        carriers.outerPopular (sourceRetained bin) := fun bin =>
    Classical.choice
      ((sourceRetained bin).restrictToOuterPopularFixedBin
        carriers.outerPopular)
  let graphRetained : ∀ bin,
      PureWZ2SourceHorizontalFixedBinResidueShadingData (residue bin) :=
    fun bin => (sourceRetained bin).withPopularGraphFixedBin
      (popularSourceCarrier bin)
  let base : ∀ bin,
      PureWZ2SourceHorizontalFixedBinResiduePreparation
        (sourceRetained bin) := fun bin =>
    Classical.choice ((sourceRetained bin).prepareFixedBin
      hbridge hgraphOne hheightAbsorb)
  let prep : ∀ bin,
      PureWZ2SourceHorizontalFixedBinResiduePreparation
        (graphRetained bin) := fun bin =>
    Classical.choice
      ((popularSourceCarrier bin).installInPreparationFixedBin
        (base bin) hbridge)
  let graphParents : ∀ bin,
      PureWZ2SourceHorizontalFixedBinGraphParentData (prep bin) := fun bin =>
    Classical.choice ((prep bin).graphParentsFixedBin)
  let fineWitnesses : ∀ bin,
      PureWZ2SourceHorizontalFixedBinFineWitnessData
        (graphRetained bin) := fun bin =>
    Classical.choice ((graphRetained bin).fineWitnessesFixedBin)
  have hlineBin : ∀ bin, (core bin).lineBin = bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (line.coreAtGlobalBin bin.1 bin.2)).1
  have hheavy : ∀ bin, (core bin).heavyCells =
      pureWZ2SourceHorizontalGlobalBinCells line bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (line.coreAtGlobalBin bin.1 bin.2)).2
  have hsourceRetainedUnion : ∀ bin,
      (sourceRetained bin).graphShadow.union =
        (sourceRetained bin).shading.union := by
    intro bin
    exact (Classical.choose_spec
      ((residue bin).retainSourceShadingFixedBin))
  have hnear : ∀ bin point,
      point ∈ (prep bin).shadow.union →
        ∃ anchor ∈ carriers.outerPopular.popular.heightRegion,
          dist point anchor < 2 * delta := by
    intro bin point hpoint
    have hgraph : point ∈
        (popularSourceCarrier bin).graphShadow.union := by
      rw [(prep bin).shadow_eq] at hpoint
      exact hpoint
    exact (popularSourceCarrier bin).graphShadow_point_near_height_region
      point hgraph
  have hslice : line.sliceCells.card =
      ∑ bin : {bin // bin ∈ line.globalBins},
        (core bin).heavyCells.card := by
    calc
      line.sliceCells.card =
          ∑ bin ∈ line.globalBins,
            (pureWZ2SourceHorizontalGlobalBinCells
              line bin).card :=
        line.card_eq_sum_globalBinCells
      _ = ∑ bin : {bin // bin ∈ line.globalBins},
          (pureWZ2SourceHorizontalGlobalBinCells
            line bin.1).card := by
        exact Finset.sum_subtype line.globalBins (fun _ => Iff.rfl) _
      _ = ∑ bin : {bin // bin ∈ line.globalBins},
          (core bin).heavyCells.card := by
        apply Finset.sum_congr rfl
        intro bin _hbin
        rw [hheavy bin]
  exact ⟨{
    line := line
    core := core
    lineBin_eq := hlineBin
    heavyCells_eq := hheavy
    parents := parents
    selection := selection
    residue := residue
    sourceRetained := sourceRetained
    sourceRetained_shadow_union := hsourceRetainedUnion
    coarseCarrier := coarseCarrier
    popularSourceCarrier := popularSourceCarrier
    graphRetained := graphRetained
    graphRetained_eq := fun _ => rfl
    prep := prep
    graphParents := graphParents
    fineWitnesses := fineWitnesses
    original_slope_eq := fun bin => (prep bin).sourceSlope_eq
    graph_point_near_height_region := hnear
    slice_card := hslice
  }⟩

end Kakeya.Assouad

end

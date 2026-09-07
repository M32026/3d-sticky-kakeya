import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPopularCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalFineWitnesses
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseCarrier

/-!
# Paper-order carriers for the ordinary Lemma-24 step

The ordinary construction first selects source-volume-popular heights in one
`sqrt rho` window.  Only then does it choose the exact source slice and the
fixed line in direction `f(z₀)`.  The resulting spatial residue is represented
in two ways which must not be identified:

* a genuine first-sticky `rho`-scale coarse carrier, used for the coarse
  volume supply;
* an original-family carrier restricted to the already selected popular
  heights, carrying the original global slope and local-plane witnesses.

This record freezes that order and the common provenance before the finite
Lemma-23 graph is built.  In particular, it makes no equality claim between
the first-sticky coarse slope and the original source slope.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The paper-ordered carrier boundary immediately before the ordinary
Lemma-23 graph. -/
structure PureWZ2OrdinaryPaperOrderCarrierData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) where
  pullback : PureWZ2TwoScaleCellPullbackData twoScale
  prepared : PureWZ2SourceCarrierPreparation pullback
  sourceWindow : PureWZ2SourceCarrierWindow prepared
  /-- This is selected before `line`; it is the paper's pre-graph `Z_S`. -/
  outerPopular : PureWZ2SourceWindowHeightPopularData
    sourceWindow (256 * rho)
  /-- The fixed line is selected from the already popular source window and
  therefore uses the original source slope literally. -/
  line : PureWZ2SourceHorizontalFixedLineData outerPopular.popularWindow
  parents : PureWZ2SourceHorizontalParentData line
  selection : PureWZ2SourceHorizontalYSelection parents
  residue : PureWZ2SourceHorizontalYResidueData selection
  sourceRetained : PureWZ2SourceHorizontalResidueShadingData residue
  sourceRetained_shadow_union :
    sourceRetained.graphShadow.union = sourceRetained.shading.union
  /-- The original-family graph carrier after imposing the complete
  source-cell envelope of the already selected outer-popular region. -/
  popularSourceCarrier :
    PureWZ2SourceHorizontalPopularCarrierData outerPopular sourceRetained
  /-- Genuine first-sticky carrier on the same selected side-`sqrt rho`
  parents. -/
  coarseCarrier : PureWZ2SourceFixedLineCoarseCarrierData residue
  /-- Original source points and original `V`-normals attached to the selected
  first-sticky cells. -/
  fineWitnesses : PureWZ2SourceHorizontalFineWitnessData sourceRetained
  original_slope_eq :
    outerPopular.popularWindow.windowed.global.sourceSlope =
      source.globalGrains.slope
  source_volume_retention :
    volume sourceWindow.shading.union ≤
      (2 * outerPopular.popular.bins : ℕ) *
        outerPopular.popularWindow.volumeSupply
  popular_graph_point_near_height_region :
    ∀ point ∈ popularSourceCarrier.graphShadow.union,
      ∃ anchor ∈ outerPopular.popular.heightRegion,
        dist point anchor < 2 * delta
  popular_graph_union :
    popularSourceCarrier.graphShadow.union =
      popularSourceCarrier.shading.union
  coarse_fixed_line_localization :
    ∀ point ∈ coarseCarrier.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1
  coarse_volume_supply :
    outerPopular.popularWindow.volumeSupply *
        twoScale.fine.balanced.cellMass ≤
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        volume coarseCarrier.shading.union
  original_normal_eq :
    ∀ parent (hparent : parent ∈ residue.selected),
      fineWitnesses.normal parent = source.localGrains.planeMap
        ⟨fineWitnesses.witness parent,
          fineWitnesses.witness_mem_source parent hparent⟩

/-- The paper-ordered carrier boundary indexed by the caller's chosen source
window.  Keeping the window as a type index preserves its provenance when the
construction is applied to every retained `sqrt rho` slab. -/
structure PureWZ2OrdinaryPaperOrderCarrierAtWindowData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (sourceWindow : PureWZ2SourceCarrierWindow prepared) where
  /-- This is selected before `line`; it is the paper's pre-graph `Z_S`. -/
  outerPopular : PureWZ2SourceWindowHeightPopularData
    sourceWindow (256 * rho)
  /-- The fixed line is selected from the already popular source window and
  therefore uses the original source slope literally. -/
  line : PureWZ2SourceHorizontalFixedLineData outerPopular.popularWindow
  parents : PureWZ2SourceHorizontalParentData line
  selection : PureWZ2SourceHorizontalYSelection parents
  residue : PureWZ2SourceHorizontalYResidueData selection
  sourceRetained : PureWZ2SourceHorizontalResidueShadingData residue
  sourceRetained_shadow_union :
    sourceRetained.graphShadow.union = sourceRetained.shading.union
  popularSourceCarrier :
    PureWZ2SourceHorizontalPopularCarrierData outerPopular sourceRetained
  coarseCarrier : PureWZ2SourceFixedLineCoarseCarrierData residue
  fineWitnesses : PureWZ2SourceHorizontalFineWitnessData sourceRetained
  original_slope_eq :
    outerPopular.popularWindow.windowed.global.sourceSlope =
      source.globalGrains.slope
  source_volume_retention :
    volume sourceWindow.shading.union ≤
      (2 * outerPopular.popular.bins : ℕ) *
        outerPopular.popularWindow.volumeSupply
  popular_graph_point_near_height_region :
    ∀ point ∈ popularSourceCarrier.graphShadow.union,
      ∃ anchor ∈ outerPopular.popular.heightRegion,
        dist point anchor < 2 * delta
  coarse_fixed_line_localization :
    ∀ point ∈ coarseCarrier.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1
  coarse_volume_supply :
    outerPopular.popularWindow.volumeSupply *
        twoScale.fine.balanced.cellMass ≤
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        volume coarseCarrier.shading.union
  original_normal_eq :
    ∀ parent (hparent : parent ∈ residue.selected),
      fineWitnesses.normal parent = source.localGrains.planeMap
        ⟨fineWitnesses.witness parent,
          fineWitnesses.witness_mem_source parent hparent⟩

/-- Forget the external window index and recover the existing single-window
carrier interface. -/
def PureWZ2OrdinaryPaperOrderCarrierAtWindowData.toCarrierData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (carriers :
      PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow) :
    PureWZ2OrdinaryPaperOrderCarrierData twoScale where
  pullback := pullback
  prepared := prepared
  sourceWindow := sourceWindow
  outerPopular := carriers.outerPopular
  line := carriers.line
  parents := carriers.parents
  selection := carriers.selection
  residue := carriers.residue
  sourceRetained := carriers.sourceRetained
  sourceRetained_shadow_union := carriers.sourceRetained_shadow_union
  popularSourceCarrier := carriers.popularSourceCarrier
  coarseCarrier := carriers.coarseCarrier
  fineWitnesses := carriers.fineWitnesses
  original_slope_eq := carriers.original_slope_eq
  source_volume_retention := carriers.source_volume_retention
  popular_graph_point_near_height_region :=
    carriers.popular_graph_point_near_height_region
  popular_graph_union := carriers.popularSourceCarrier.graphShadow_union_eq
  coarse_fixed_line_localization := carriers.coarse_fixed_line_localization
  coarse_volume_supply := carriers.coarse_volume_supply
  original_normal_eq := carriers.original_normal_eq

/-- Assemble the two carrier views from one supplied source window in the
literal Lemma-24 order. -/
theorem PureWZ2SourceCarrierWindow.ordinaryPaperOrderCarriers
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (sourceWindow : PureWZ2SourceCarrierWindow prepared) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact source.extremal.delta_pos.trans_le
      twoScale.rhoRequested.property.1
  rcases sourceWindow.heightPopularWholeCells (256 * rho) (by positivity) with
    ⟨outerPopular⟩
  have hpopularVolume :
      0 < volume outerPopular.popularWindow.shading.union :=
    outerPopular.popularWindow.volumeSupply_pos.trans_le
      outerPopular.popularWindow.volume_lower
  rcases outerPopular.popularWindow.selectHorizontalFixedLine hpopularVolume with
    ⟨line⟩
  rcases line.toParents with ⟨parents⟩
  rcases parents.selectOnePerY with ⟨selection⟩
  rcases selection.selectResidue with ⟨residue⟩
  rcases residue.retainSourceShading with
    ⟨sourceRetained, hsourceRetainedShadow⟩
  rcases sourceRetained.restrictToOuterPopular outerPopular with
    ⟨popularSourceCarrier⟩
  rcases residue.retainCoarseCarrier with ⟨coarseCarrier⟩
  rcases sourceRetained.fineWitnesses with ⟨fineWitnesses⟩
  exact ⟨{
    outerPopular := outerPopular
    line := line
    parents := parents
    selection := selection
    residue := residue
    sourceRetained := sourceRetained
    sourceRetained_shadow_union := hsourceRetainedShadow
    popularSourceCarrier := popularSourceCarrier
    coarseCarrier := coarseCarrier
    fineWitnesses := fineWitnesses
    original_slope_eq := outerPopular.popularWindow.sourceSlope_eq
    source_volume_retention := outerPopular.source_volume_retention
    popular_graph_point_near_height_region :=
      popularSourceCarrier.graphShadow_point_near_height_region
    coarse_fixed_line_localization :=
      coarseCarrier.fixed_line_localization
    coarse_volume_supply := coarseCarrier.volume_supply_le
    original_normal_eq := fineWitnesses.normal_eq
  }⟩

/-- Select one source window and assemble the two carrier views in the literal
Lemma-24 order. -/
theorem PureWZ2OneScaleTwoScaleStickyData.ordinaryPaperOrderCarriers
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2OrdinaryPaperOrderCarrierData twoScale) := by
  rcases twoScale.pullbackSelectedCells with ⟨pullback⟩
  rcases pullback.prepareSourceCarrier hbridge with ⟨prepared⟩
  rcases prepared.selectWindow with ⟨sourceWindow⟩
  rcases sourceWindow.ordinaryPaperOrderCarriers with ⟨carriers⟩
  exact ⟨carriers.toCarrierData⟩

/-- The first two quantitative steps of the paper-order construction on one
window.  The source-volume popularity loss is paid before the fixed-line
Fubini estimate, and the result lands on the genuine first-sticky coarse
carrier selected by that line.  No claim about the later height-restricted
original-family graph shadow is made here. -/
theorem PureWZ2OrdinaryPaperOrderCarrierData.source_to_coarse_volume_supply
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale) :
    volume carriers.sourceWindow.shading.union *
          twoScale.fine.balanced.cellMass ≤
      (2 * carriers.outerPopular.popular.bins : ℕ) *
        (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          volume carriers.coarseCarrier.shading.union) := by
  calc
    volume carriers.sourceWindow.shading.union *
          twoScale.fine.balanced.cellMass ≤
        ((2 * carriers.outerPopular.popular.bins : ℕ) *
          carriers.outerPopular.popularWindow.volumeSupply) *
            twoScale.fine.balanced.cellMass := by
      gcongr
      exact carriers.source_volume_retention
    _ = (2 * carriers.outerPopular.popular.bins : ℕ) *
        (carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass) := by ring
    _ ≤ (2 * carriers.outerPopular.popular.bins : ℕ) *
        (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          volume carriers.coarseCarrier.shading.union) := by
      exact mul_le_mul_left' carriers.coarse_volume_supply _

end Kakeya.Assouad

end

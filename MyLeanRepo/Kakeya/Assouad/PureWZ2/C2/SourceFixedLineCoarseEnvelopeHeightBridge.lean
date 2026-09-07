import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseHeightLift
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePopularCarrier

/-!
# Bounded-neighbour height provenance for the genuine coarse envelope

The whole-cell outer-popular envelope is not pointwise contained in the
outer-popular height region.  It is, however, within an absolute multiple of
the first-sticky scale.  Since the Lemma-23 graph height slabs have width
`gridSide ((256 * rho) / 2)`, this metric proximity forces every rich graph
height to be at integer distance at most one from an outer-popular height.

This result is only the height-provenance half of the genuine-coarse bridge.
It does not assert the still-missing graph-ready volume lower bound on this
same dependent carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

private lemma floor_sub_abs_le_one {x y : ℝ} (h : |x - y| ≤ 1) :
    |(Int.floor x : ℤ) - (Int.floor y : ℤ)| ≤ (1 : ℤ) := by
  have hxy : x - y ≤ 1 := (abs_le.mp h).2
  have hyx : y - x ≤ 1 := by
    have := (abs_le.mp h).1
    linarith
  have hforward : (Int.floor x : ℤ) - Int.floor y ≤ 1 := by
    by_contra hnot
    have hlower : (2 : ℤ) ≤ (Int.floor x : ℤ) - Int.floor y := by omega
    have hlowerReal : (2 : ℝ) ≤
        (Int.floor x : ℝ) - Int.floor y := by exact_mod_cast hlower
    have hfloorX : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have hyFloor : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
    linarith
  have hbackward : (Int.floor y : ℤ) - Int.floor x ≤ 1 := by
    by_contra hnot
    have hlower : (2 : ℤ) ≤ (Int.floor y : ℤ) - Int.floor x := by omega
    have hlowerReal : (2 : ℝ) ≤
        (Int.floor y : ℝ) - Int.floor x := by exact_mod_cast hlower
    have hfloorY : (Int.floor y : ℝ) ≤ y := Int.floor_le y
    have hxFloor : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
    linarith
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- Moving within one source `delta` cell does not leave the rich-height
refill band when the reference graph height is adjacent to the popular one. -/
lemma source_cell_near_adjacent_graph_height
    {delta rho graphScale : ℝ} {heightIndex popularHeight : ℤ}
    {point other : Point3}
    (hrho : 0 < rho) (hdeltaRho : delta ≤ rho)
    (hscale : graphScale = 256 * rho)
    (hpointSlab : point ∈ wz1Lemma23HeightSlab graphScale popularHeight)
    (hotherPoint : |other (2 : Fin 3) - point (2 : Fin 3)| ≤ delta)
    (hnear : |heightIndex - popularHeight| ≤ (1 : ℤ)) :
    |other (2 : Fin 3) -
        wz1Lemma23SnappedBaseHeight graphScale heightIndex| ≤ graphScale := by
  let width := gridSide (graphScale / 2)
  have hgraph : 0 < graphScale := by rw [hscale]; positivity
  have hwidth : 0 < width := by
    dsimp only [width, gridSide]
    positivity
  have hsqrtThreePos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtThreeLower : (5 / 3 : ℝ) ≤ Real.sqrt 3 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hsqrtNonneg := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hwidthEq : width = graphScale / Real.sqrt 3 := by
    dsimp only [width, gridSide]
    ring
  have hwidthBound : 3 * width / 2 + delta ≤ graphScale := by
    rw [hwidthEq, hscale]
    have hdelta : delta ≤ 256 * rho / 10 := by linarith
    have hdiv : 256 * rho / Real.sqrt 3 ≤ 3 * (256 * rho) / 5 := by
      rw [div_le_iff₀ hsqrtThreePos]
      nlinarith
    nlinarith
  have hslab : point (2 : Fin 3) ∈
      Set.Ico ((popularHeight : ℝ) * width)
        (((popularHeight : ℝ) + 1) * width) := by
    simpa [wz1Lemma23HeightSlab, wz1Lemma23HeightInterval, width] using
      hpointSlab
  have hnearBounds := abs_le.mp hnear
  have hlowerInt : heightIndex - 1 ≤ popularHeight := by omega
  have hupperInt : popularHeight ≤ heightIndex + 1 := by omega
  have hlowerReal : (heightIndex : ℝ) - 1 ≤ (popularHeight : ℝ) := by
    exact_mod_cast hlowerInt
  have hupperReal : (popularHeight : ℝ) ≤ (heightIndex : ℝ) + 1 := by
    exact_mod_cast hupperInt
  rw [wz1Lemma23SnappedBaseHeight]
  change |other 2 - (((heightIndex : ℝ) + 1 / 2) * width)| ≤ graphScale
  rw [abs_le]
  rw [abs_le] at hotherPoint
  constructor <;> nlinarith [hslab.1, hslab.2.le]

/-- Every Alternative-A height selected from a graph built on the complete-cell
outer-popular envelope has an outer-popular height in one of the three adjacent
integer slots. -/
theorem PureWZ2SourceFixedBinCoarseAlternativeAHeightData.heightIndices_near_outerPopular
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss)
    (hgraphNear : ∀ point ∈ prep.shadow.union,
      ∃ anchor ∈ outerPopular.popular.heightRegion,
        dist point anchor < 2 * rho + 2 * delta) :
    ∀ heightIndex ∈ rich.heightIndices,
      ∃ popularHeight ∈ outerPopular.popular.heightIndices,
        |heightIndex - popularHeight| ≤ (1 : ℤ) := by
  intro heightIndex hheightIndex
  rw [rich.heightIndices_eq] at hheightIndex
  rcases Finset.mem_image.mp hheightIndex with
    ⟨point, hpoint, hheightEq⟩
  let cell := (rich.pathFor point).2.1
  have hcellGraph : cell ∈ preparedGraph.graph.residue.cells :=
    rich.cell_mem point hpoint
  have hcellGlobal : cell ∈ prep.windowed.global.cells :=
    preparedGraph.graph.residue.cells_subset hcellGraph
  have hrepresentative :
      graphParents.representative cell ∈ prep.shadow.union :=
    graphParents.representative_mem cell hcellGlobal
  rcases hgraphNear (graphParents.representative cell) hrepresentative with
    ⟨anchor, hanchor, hnear⟩
  rw [outerPopular.popular.heightRegion_eq] at hanchor
  rcases Set.mem_iUnion₂.mp hanchor with
    ⟨popularHeight, hpopularHeight, hanchorSlab⟩
  refine ⟨popularHeight, hpopularHeight, ?_⟩
  have hfloorPopular := (wz1Lemma23_mem_heightSlab_iff
    outerPopular.popular.graphScale_pos popularHeight anchor).mp hanchorSlab
  have hcellHeight := congrArg
    (fun index : ℤ × ℤ × ℤ => index.2.2)
    (graphParents.representative_index cell hcellGlobal)
  have hfloorCell :
      Int.floor
          (graphParents.representative cell (2 : Fin 3) /
            gridSide ((256 * rho) / 2)) = cell.2.2 := by
    rw [← prep.graphScale_eq]
    simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using hcellHeight
  have hheightCell : rich.heightIndex point = cell.2.2 :=
    rich.heightIndex_eq point hpoint
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hsqrtThreePos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtThreeLe : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  let width := gridSide ((256 * rho) / 2)
  have hwidth : 0 < width := by
    dsimp only [width, gridSide]
    positivity
  have hnearWidth : 2 * rho + 2 * delta ≤ width := by
    change 2 * rho + 2 * delta ≤ 2 * ((256 * rho) / 2) / Real.sqrt 3
    rw [le_div_iff₀ hsqrtThreePos]
    nlinarith
  have hcoordinate :
      |graphParents.representative cell (2 : Fin 3) - anchor (2 : Fin 3)| <
        2 * rho + 2 * delta := by
    have hcoordinateLe := PiLp.dist_apply_le
      (graphParents.representative cell) anchor (2 : Fin 3)
    have hcoordinateLe' :
        |graphParents.representative cell (2 : Fin 3) -
            anchor (2 : Fin 3)| ≤
          dist (graphParents.representative cell) anchor := by
      simpa [Real.dist_eq] using hcoordinateLe
    exact hcoordinateLe'.trans_lt hnear
  have hscaled :
      |graphParents.representative cell (2 : Fin 3) / width -
          anchor (2 : Fin 3) / width| ≤ 1 := by
    rw [show graphParents.representative cell (2 : Fin 3) / width -
        anchor (2 : Fin 3) / width =
          (graphParents.representative cell (2 : Fin 3) -
            anchor (2 : Fin 3)) / width by ring]
    rw [abs_div, abs_of_pos hwidth]
    calc
      |graphParents.representative cell (2 : Fin 3) -
            anchor (2 : Fin 3)| / width ≤ width / width := by
        gcongr
        exact hcoordinate.le.trans hnearWidth
      _ = 1 := div_self hwidth.ne'
  have hfloor := floor_sub_abs_le_one hscaled
  have hfloorHeight :
      Int.floor
          (graphParents.representative cell (2 : Fin 3) / width) =
        heightIndex := by
    exact hfloorCell.trans (hheightCell.symm.trans hheightEq)
  have hfloorPopular' : Int.floor (anchor (2 : Fin 3) / width) =
      popularHeight := by
    simpa [width] using hfloorPopular
  simpa [hfloorHeight, hfloorPopular'] using hfloor

/-- A choice of an outer-popular neighbour for every rich envelope height.
The fiber bound is the exact combinatorial content of the absolute loss: an
integer has only three neighbours at distance at most one. -/
structure PureWZ2SourceFixedBinCoarseEnvelopeHeightAssignmentData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho))
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss) where
  assigned : ℤ → ℤ
  assigned_mem : ∀ heightIndex ∈ rich.heightIndices,
    assigned heightIndex ∈ outerPopular.popular.heightIndices
  assigned_near : ∀ heightIndex ∈ rich.heightIndices,
    |heightIndex - assigned heightIndex| ≤ (1 : ℤ)
  assigned_fiber_card : ∀ popularHeight : ℤ,
    (rich.heightIndices.filter fun heightIndex =>
      assigned heightIndex = popularHeight).card ≤ 3

/-- Package any proved adjacent outer-popular assignment. This separates the
finite-fiber argument from the construction-specific provenance proof. -/
theorem PureWZ2SourceFixedBinCoarseAlternativeAHeightData.envelopeHeightAssignment_of_near
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho))
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss)
    (hnear : ∀ heightIndex ∈ rich.heightIndices,
      ∃ popularHeight ∈ outerPopular.popular.heightIndices,
        |heightIndex - popularHeight| ≤ (1 : ℤ)) :
    Nonempty (PureWZ2SourceFixedBinCoarseEnvelopeHeightAssignmentData
      outerPopular rich) := by
  let assigned : ℤ → ℤ := fun heightIndex =>
    if hheight : heightIndex ∈ rich.heightIndices then
      Classical.choose (hnear heightIndex hheight)
    else 0
  have hmem : ∀ heightIndex ∈ rich.heightIndices,
      assigned heightIndex ∈ outerPopular.popular.heightIndices := by
    intro heightIndex hheight
    simp only [assigned, dif_pos hheight]
    exact (Classical.choose_spec (hnear heightIndex hheight)).1
  have hclose : ∀ heightIndex ∈ rich.heightIndices,
      |heightIndex - assigned heightIndex| ≤ (1 : ℤ) := by
    intro heightIndex hheight
    simp only [assigned, dif_pos hheight]
    exact (Classical.choose_spec (hnear heightIndex hheight)).2
  refine ⟨{
    assigned := assigned
    assigned_mem := hmem
    assigned_near := hclose
    assigned_fiber_card := ?_
  }⟩
  intro popularHeight
  apply (Finset.card_le_card (t := Finset.Icc
    (popularHeight - 1) (popularHeight + 1)) ?_).trans_eq
  · rw [Int.card_Icc]
    omega
  intro heightIndex hheight
  rw [Finset.mem_filter] at hheight
  rw [Finset.mem_Icc]
  have hbound := hclose heightIndex hheight.1
  rw [hheight.2] at hbound
  have hb := abs_le.mp hbound
  omega

/-- Package the bounded-neighbour relation into a single assignment whose
fibers have cardinality at most three. -/
theorem PureWZ2SourceFixedBinCoarseAlternativeAHeightData.envelopeHeightAssignment
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
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
    {envelope : PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      outerPopular retained carrier}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss)
    (hprep : prep.shadow = envelope.shading) :
    Nonempty (PureWZ2SourceFixedBinCoarseEnvelopeHeightAssignmentData
      outerPopular rich) := by
  have hnear := rich.heightIndices_near_outerPopular fun point hpoint =>
    envelope.point_near_height_region point (by
      rw [← hprep]
      exact hpoint)
  let assigned : ℤ → ℤ := fun heightIndex =>
    if hheight : heightIndex ∈ rich.heightIndices then
      Classical.choose (hnear heightIndex hheight)
    else 0
  have hassignedMem : ∀ heightIndex ∈ rich.heightIndices,
      assigned heightIndex ∈ outerPopular.popular.heightIndices := by
    intro heightIndex hheight
    simp only [assigned, dif_pos hheight]
    exact (Classical.choose_spec (hnear heightIndex hheight)).1
  have hassignedNear : ∀ heightIndex ∈ rich.heightIndices,
      |heightIndex - assigned heightIndex| ≤ (1 : ℤ) := by
    intro heightIndex hheight
    simp only [assigned, dif_pos hheight]
    exact (Classical.choose_spec (hnear heightIndex hheight)).2
  refine ⟨{
    assigned := assigned
    assigned_mem := hassignedMem
    assigned_near := hassignedNear
    assigned_fiber_card := ?_
  }⟩
  intro popularHeight
  have hsubset :
      rich.heightIndices.filter (fun heightIndex =>
          assigned heightIndex = popularHeight) ⊆
        Finset.Icc (popularHeight - 1) (popularHeight + 1) := by
    intro heightIndex hheight
    rw [Finset.mem_filter] at hheight
    rw [Finset.mem_Icc]
    have hnearAssigned := hassignedNear heightIndex hheight.1
    rw [hheight.2] at hnearAssigned
    have hb := abs_le.mp hnearAssigned
    omega
  have hcard : (Finset.Icc
      (popularHeight - 1) (popularHeight + 1)).card = 3 := by
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsubset).trans_eq hcard

namespace PureWZ2SourceFixedBinCoarseEnvelopeHeightAssignmentData

/-- Every assigned height remains in the original outer-popular set. -/
theorem assigned_image_subset
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    (assignment : PureWZ2SourceFixedBinCoarseEnvelopeHeightAssignmentData
      outerPopular rich) :
    rich.heightIndices.image assignment.assigned ⊆
      outerPopular.popular.heightIndices := by
  intro popularHeight hheight
  rcases Finset.mem_image.mp hheight with ⟨heightIndex, hheightIndex, rfl⟩
  exact assignment.assigned_mem heightIndex hheightIndex

/-- The bounded fibers lose at most the absolute factor three in height
cardinality. -/
theorem rich_card_le_three_mul_assigned_card
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    (assignment : PureWZ2SourceFixedBinCoarseEnvelopeHeightAssignmentData
      outerPopular rich) :
    rich.heightIndices.card ≤
      3 * (rich.heightIndices.image assignment.assigned).card := by
  rw [Finset.card_eq_sum_card_image assignment.assigned rich.heightIndices]
  calc
    (∑ popularHeight ∈ rich.heightIndices.image assignment.assigned,
        (rich.heightIndices.filter fun heightIndex =>
          assignment.assigned heightIndex = popularHeight).card) ≤
      ∑ _popularHeight ∈ rich.heightIndices.image assignment.assigned, 3 := by
        exact Finset.sum_le_sum fun popularHeight _ =>
          assignment.assigned_fiber_card popularHeight
    _ = 3 * (rich.heightIndices.image assignment.assigned).card := by
      simp [Finset.sum_const, Nat.mul_comm]

end PureWZ2SourceFixedBinCoarseEnvelopeHeightAssignmentData

end Kakeya.Assouad

end

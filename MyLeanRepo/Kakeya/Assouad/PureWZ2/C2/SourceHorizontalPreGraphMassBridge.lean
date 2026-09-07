import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRichHeightVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceWindowHeightPopularity

/-!
# Pre-graph source-volume retention for the ordinary WZ step

In WZ Lemma 5.5 the height popularity is imposed on the original source
window before the auxiliary fixed-line graph is chosen.  The graph is formed
on the complete source-cell envelope of those heights and chooses only the
final rich heights.  The nearby-height assignment below returns them to the
full source window and converts its union-volume lower bound to indexed mass
using the first sticky multiplicity band.

The complete final height lift itself is not claimed to have constant
multiplicity.  Instead we construct the common spatial restriction of the
first sticky zero extension inside it and use that smaller shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private lemma source_floor_sub_abs_le_one {x y : ℝ} (h : |x - y| ≤ 1) :
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

private lemma source_cell_near_adjacent_graph_height
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

/-- Every Alternative-A height selected from the complete source-cell
outer-popular envelope is adjacent to a genuinely volume-popular height. -/
theorem PureWZ2SourceAlternativeAHeightData.heightIndices_near_outerPopular_of_envelope
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceAlternativeAHeightData ready finalLoss)
    (hscale : prep.graphScale = 256 * rho)
    (hcarrier : ∀ point ∈ prep.shadow.union,
      ∃ anchor ∈ outerPopular.popular.heightRegion,
        dist point anchor < 2 * delta) :
    ∀ heightIndex ∈ rich.heightIndices,
      ∃ popularHeight ∈ outerPopular.popular.heightIndices,
        |heightIndex - popularHeight| ≤ (1 : ℤ) := by
  intro heightIndex hheightIndex
  rw [rich.heightIndices_eq] at hheightIndex
  rcases Finset.mem_image.mp hheightIndex with
    ⟨point, hpoint, hheightEq⟩
  let cell := (rich.pathFor point).2.1
  have hcellGraph : cell ∈ graph.residue.cells := rich.cell_mem point hpoint
  have hcellGlobal : cell ∈ prep.windowed.global.cells :=
    graph.residue.cells_subset hcellGraph
  have hrepresentative : graphParents.representative cell ∈ prep.shadow.union :=
    graphParents.representative_mem cell hcellGlobal
  rcases hcarrier (graphParents.representative cell) hrepresentative with
    ⟨anchor, hanchor, hnear⟩
  rw [outerPopular.popular.heightRegion_eq] at hanchor
  rcases Set.mem_iUnion₂.mp hanchor with
    ⟨popularHeight, hpopularHeight, hslab⟩
  refine ⟨popularHeight, hpopularHeight, ?_⟩
  have hfloorPopular := (wz1Lemma23_mem_heightSlab_iff
    outerPopular.popular.graphScale_pos popularHeight anchor).mp hslab
  have hcellHeight := congrArg
    (fun index : ℤ × ℤ × ℤ => index.2.2)
    (graphParents.representative_index cell hcellGlobal)
  have hfloorCell :
      Int.floor
          (graphParents.representative cell (2 : Fin 3) /
            gridSide ((256 * rho) / 2)) = cell.2.2 := by
    rw [← hscale]
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
  let width := gridSide ((256 * rho) / 2)
  have hwidth : 0 < width := by
    dsimp only [width, gridSide]
    positivity
  have hnearWidth : 2 * delta ≤ width := by
    change 2 * delta ≤ 2 * ((256 * rho) / 2) / Real.sqrt 3
    rw [le_div_iff₀ hsqrtThreePos]
    have hsqrtThreeLe : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith
  have hcoordinate :
      |graphParents.representative cell (2 : Fin 3) -
          anchor (2 : Fin 3)| < 2 * delta := by
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
  have hfloor := source_floor_sub_abs_le_one hscaled
  have hfloorHeight :
      Int.floor
          (graphParents.representative cell (2 : Fin 3) / width) =
        heightIndex := by
    exact hfloorCell.trans (hheightCell.symm.trans hheightEq)
  have hfloorPopular' :
      Int.floor (anchor (2 : Fin 3) / width) = popularHeight := by
    simpa [width] using hfloorPopular
  simpa [hfloorHeight, hfloorPopular'] using hfloor

/-- A bounded-fiber choice of a genuinely outer-popular neighbour for each
rich source-envelope height. -/
structure PureWZ2SourceEnvelopeHeightAssignmentData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceAlternativeAHeightData ready finalLoss) where
  assigned : ℤ → ℤ
  assigned_mem : ∀ heightIndex ∈ rich.heightIndices,
    assigned heightIndex ∈ outerPopular.popular.heightIndices
  assigned_near : ∀ heightIndex ∈ rich.heightIndices,
    |heightIndex - assigned heightIndex| ≤ (1 : ℤ)
  assigned_fiber_card : ∀ popularHeight : ℤ,
    (rich.heightIndices.filter fun heightIndex =>
      assigned heightIndex = popularHeight).card ≤ 3

/-- Package nearby height provenance into an assignment with fibers of size
at most three. -/
theorem PureWZ2SourceAlternativeAHeightData.envelopeHeightAssignment
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceAlternativeAHeightData ready finalLoss)
    (hscale : prep.graphScale = 256 * rho)
    (hcarrier : ∀ point ∈ prep.shadow.union,
      ∃ anchor ∈ outerPopular.popular.heightRegion,
        dist point anchor < 2 * delta) :
    Nonempty (PureWZ2SourceEnvelopeHeightAssignmentData
      outerPopular rich) := by
  have hnear := rich.heightIndices_near_outerPopular_of_envelope
    (graphParents := graphParents) hscale hcarrier
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

namespace PureWZ2SourceEnvelopeHeightAssignmentData

theorem assigned_image_subset
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    (assignment : PureWZ2SourceEnvelopeHeightAssignmentData
      outerPopular rich) :
    rich.heightIndices.image assignment.assigned ⊆
      outerPopular.popular.heightIndices := by
  intro popularHeight hheight
  rcases Finset.mem_image.mp hheight with ⟨heightIndex, hheightIndex, rfl⟩
  exact assignment.assigned_mem heightIndex hheightIndex

theorem rich_card_le_three_mul_assigned_card
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    (assignment : PureWZ2SourceEnvelopeHeightAssignmentData
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

end PureWZ2SourceEnvelopeHeightAssignmentData

theorem PureWZ2SourceAlternativeAHeightLift.mass_lower_of_window_layers
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    {richTrapezoid : PureWZ2SourceAlternativeARichTrapezoid richShading}
    (heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid)
    (layerMass : ENNReal)
    (hlayer : ∀ heightIndex ∈ rich.heightIndices,
      layerMass ≤ volume (window.shading.union ∩
        wz1Lemma23HeightSlab prep.graphScale heightIndex)) :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        ((rich.heightIndices.card : ENNReal) * layerMass) ≤
      heightLift.shading.mass := by
  let richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  have hregionMeasurable : MeasurableSet richRegion :=
    MeasurableSet.biUnion rich.heightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let region : Set Point3 := window.shading.union ∩ richRegion
  have hregionMeasurable' : MeasurableSet region :=
    (measurableSet_shading_union window.shading).inter hregionMeasurable
  let paperRich : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        pullback.zeroExtension.ambientShading.carrier index ∩ region
      measurable_carrier := fun index =>
        (pullback.zeroExtension.ambientShading.measurable_carrier index).inter
          hregionMeasurable'
      subset_body := fun index => Set.inter_subset_left.trans
        (pullback.zeroExtension.ambientShading.subset_body index) }
  have hwindowAmbient : window.shading.union ⊆
      pullback.zeroExtension.ambientShading.union := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      window.subshading.union_subset hpoint
    have hpullback : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    rcases hpullback with ⟨index, hindex⟩
    rw [pullback.carrier_eq] at hindex
    exact ⟨index, hindex.1⟩
  have hunion : paperRich.union = region := by
    apply Set.Subset.antisymm
    · rintro point ⟨_index, _hambient, hregion⟩
      exact hregion
    · intro point hpoint
      rcases hwindowAmbient hpoint.1 with ⟨index, hindex⟩
      exact ⟨index, hindex, hpoint⟩
  have hconstant : paperRich.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
    have hambient := pullback.zeroExtension.constantMultiplicity
      twoScale.coarse.refined_multiplicity_band
    intro point hpoint
    have hpointAmbient : point ∈
        pullback.zeroExtension.ambientShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩
    have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
      (fun index => show paperRich.carrier index =
        pullback.zeroExtension.ambientShading.carrier index ∩ region from rfl)
      hpoint
    rw [hmultiplicity]
    exact hambient point hpointAmbient
  have hpaperSub : PureWZ2PaperIsSubshading
      paperRich heightLift.shading := by
    intro index point hpoint
    have hregion : point ∈ region := hpoint.2
    have hwindow : point ∈ window.shading.union := hregion.1
    have hrichRegion : point ∈ richRegion := hregion.2
    rcases Set.mem_iUnion₂.mp hrichRegion with
      ⟨heightIndex, hheightIndex, hpointSlab⟩
    rcases pullback.zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, hindex, hselected⟩
    have hsource : point ∈ source.shading.carrier index := by
      subst index
      exact twoScale.coarse.subshading selectedIndex hselected
    have hsourceUnion : point ∈ source.shading.union := ⟨index, hsource⟩
    rw [source.cubical.union_eq_activeCells source.extremal.delta_pos]
      at hsourceUnion
    rcases Set.mem_iUnion₂.mp hsourceUnion with
      ⟨cell, hcell, hpointCell⟩
    have hpointClose : |point 2 -
        wz1Lemma23SnappedBaseHeight prep.graphScale heightIndex| ≤
          prep.graphScale / 2 := by
      change point 2 ∈ wz1Lemma23HeightInterval
        prep.graphScale heightIndex at hpointSlab
      have hside : gridSide (prep.graphScale / 2) =
          prep.graphScale / Real.sqrt 3 := by
        simp [gridSide]
        ring
      rw [wz1Lemma23HeightInterval, hside] at hpointSlab
      rw [wz1Lemma23SnappedBaseHeight, hside]
      rw [abs_le]
      constructor
      · have hhalf : prep.graphScale / (2 * Real.sqrt 3) ≤
            prep.graphScale / 2 := by
          have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg (3 : ℝ)]
          exact div_le_div_of_nonneg_left prep.graphScale_pos.le
            (by norm_num) hden
        have hcenter : ((heightIndex : ℝ) + 1 / 2) *
              (prep.graphScale / Real.sqrt 3) -
            (heightIndex : ℝ) * (prep.graphScale / Real.sqrt 3) =
              prep.graphScale / (2 * Real.sqrt 3) := by ring
        linarith [hpointSlab.1, hhalf, hcenter]
      · have hhalf : prep.graphScale / (2 * Real.sqrt 3) ≤
            prep.graphScale / 2 := by
          have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg (3 : ℝ)]
          exact div_le_div_of_nonneg_left prep.graphScale_pos.le
            (by norm_num) hden
        have hcenterUpper :
            ((heightIndex : ℝ) + 1) *
                (prep.graphScale / Real.sqrt 3) -
              ((heightIndex : ℝ) + 1 / 2) *
                (prep.graphScale / Real.sqrt 3) =
              prep.graphScale / (2 * Real.sqrt 3) := by ring
        linarith [hpointSlab.2, hhalf, hcenterUpper]
    have hcellCondition : ∀ other ∈ wz1PaperGridCube delta cell,
        other 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ selectedHeight ∈ rich.heightIndices,
            |other 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale selectedHeight| ≤ prep.graphScale := by
      intro other hother
      have hotherClose : |other 2 - point 2| ≤ delta := by
        have hpointBounds := hpointCell
        have hotherBounds := hother
        rw [wz1PaperGridCube_eq_Ico source.extremal.delta_pos cell]
          at hpointBounds hotherBounds
        rw [abs_le]
        constructor <;>
          linarith [hpointBounds.2.2.2.2.1, hpointBounds.2.2.2.2.2,
            hotherBounds.2.2.2.2.1, hotherBounds.2.2.2.2.2]
      have hdeltaRho : delta ≤ rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.1
      have hrhoGraph : rho ≤ prep.graphScale / 2 := by
        rw [prep.graphScale_eq]
        nlinarith [line.rho_pos]
      have hcellEq : cell = wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
      refine ⟨richTrapezoid.window_cell_height_coverage
          point hwindow other (by rwa [← hcellEq]),
        heightIndex, hheightIndex, ?_⟩
      calc
        |other 2 - wz1Lemma23SnappedBaseHeight
            prep.graphScale heightIndex| ≤
          |other 2 - point 2| +
            |point 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| := abs_sub_le _ _ _
        _ ≤ delta + prep.graphScale / 2 := by gcongr
        _ ≤ prep.graphScale := by linarith
    have hheightCell : cell ∈ heightLift.heightCells := by
      rw [heightLift.heightCells_eq]
      exact Finset.mem_filter.mpr ⟨hcell, hcellCondition⟩
    rw [heightLift.carrier_eq]
    refine ⟨hsource, ?_⟩
    rw [heightLift.region_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hheightCell, hpointCell⟩
  have hvolume : (rich.heightIndices.card : ENNReal) * layerMass ≤
      volume paperRich.union := by
    rw [hunion]
    have hpartition : region =
        ⋃ heightIndex ∈ rich.heightIndices,
          window.shading.union ∩
            wz1Lemma23HeightSlab prep.graphScale heightIndex := by
      ext point
      simp [region, richRegion]
    rw [hpartition]
    rw [MeasureTheory.measure_biUnion_finset]
    · calc
        (rich.heightIndices.card : ENNReal) * layerMass =
            ∑ _heightIndex ∈ rich.heightIndices, layerMass := by
          simp [Finset.sum_const]
        _ ≤ ∑ heightIndex ∈ rich.heightIndices,
            volume (window.shading.union ∩
              wz1Lemma23HeightSlab prep.graphScale heightIndex) :=
          Finset.sum_le_sum hlayer
    · intro first _ second _ hne
      exact (wz1Lemma23_heightSlab_disjoint prep.graphScale_pos hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro heightIndex _
      exact (measurableSet_shading_union window.shading).inter (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  calc
    (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((rich.heightIndices.card : ENNReal) * layerMass) ≤
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          volume paperRich.union := by gcongr
    _ ≤ paperRich.mass :=
      (constant_multiplicity_mass_volume_generic hconstant).1
    _ ≤ heightLift.shading.mass := by
      apply Finset.sum_le_sum
      intro index _
      exact measure_mono (hpaperSub index)

/-- Paper-order specialization: when the local graph was built on a
source-volume-popular window, its rich-height count controls an actual
original-family subshading.  No multiplicity assertion is made about the
larger height lift. -/
theorem PureWZ2SourceAlternativeAHeightLift.mass_lower_of_outer_popular
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    {richTrapezoid : PureWZ2SourceAlternativeARichTrapezoid richShading}
    (heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid)
    (hwindow : window.shading.union = outerPopular.popular.shading.union)
    (hscale : prep.graphScale = 256 * rho)
    (hheightSubset : rich.heightIndices ⊆
      outerPopular.popular.heightIndices) :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        ((rich.heightIndices.card : ENNReal) *
          outerPopular.popular.layerMass) ≤ heightLift.shading.mass := by
  apply heightLift.mass_lower_of_window_layers outerPopular.popular.layerMass
  intro heightIndex hheightIndex
  have hband := outerPopular.popular.layer_volume_band heightIndex
    (hheightSubset hheightIndex)
  have hsliceEq :
      outerPopular.popular.shading.union ∩
          wz1Lemma23HeightSlab (256 * rho) heightIndex =
        sourceWindow.shading.union ∩
          wz1Lemma23HeightSlab (256 * rho) heightIndex := by
    rw [outerPopular.popular.union_eq]
    apply Set.Subset.antisymm
    · exact fun _ hpoint => ⟨hpoint.1.1, hpoint.2⟩
    · intro point hpoint
      refine ⟨⟨hpoint.1, ?_⟩, hpoint.2⟩
      rw [outerPopular.popular.heightRegion_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨heightIndex, hheightSubset hheightIndex, hpoint.2⟩
  rw [hwindow, hscale]
  rw [hsliceEq]
  exact hband.1

/-- Source layers at the assigned genuinely popular heights embed in the
original-family height lift.  Adjacency is absorbed by the lift's one
graph-scale refill band. -/
theorem PureWZ2SourceAlternativeAHeightLift.mass_lower_of_assigned_outer_popular
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    {richTrapezoid : PureWZ2SourceAlternativeARichTrapezoid richShading}
    (heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid)
    (assignment : PureWZ2SourceEnvelopeHeightAssignmentData
      outerPopular rich)
    (hwindow : window.shading.union =
      outerPopular.popular.shading.union) :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        (((rich.heightIndices.image assignment.assigned).card : ENNReal) *
          outerPopular.popular.layerMass) ≤ heightLift.shading.mass := by
  let assignedHeights := rich.heightIndices.image assignment.assigned
  let assignedRegion : Set Point3 :=
    ⋃ heightIndex ∈ assignedHeights,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  have hregionMeasurable : MeasurableSet assignedRegion :=
    MeasurableSet.biUnion assignedHeights.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let region : Set Point3 := window.shading.union ∩ assignedRegion
  have hregionMeasurable' : MeasurableSet region :=
    (measurableSet_shading_union window.shading).inter hregionMeasurable
  let paperAssigned : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        pullback.zeroExtension.ambientShading.carrier index ∩ region
      measurable_carrier := fun index =>
        (pullback.zeroExtension.ambientShading.measurable_carrier index).inter
          hregionMeasurable'
      subset_body := fun index => Set.inter_subset_left.trans
        (pullback.zeroExtension.ambientShading.subset_body index) }
  have hwindowAmbient : window.shading.union ⊆
      pullback.zeroExtension.ambientShading.union := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      window.subshading.union_subset hpoint
    have hpullback : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    rcases hpullback with ⟨index, hindex⟩
    rw [pullback.carrier_eq] at hindex
    exact ⟨index, hindex.1⟩
  have hunion : paperAssigned.union = region := by
    apply Set.Subset.antisymm
    · rintro point ⟨_index, _hambient, hregion⟩
      exact hregion
    · intro point hpoint
      rcases hwindowAmbient hpoint.1 with ⟨index, hindex⟩
      exact ⟨index, hindex, hpoint⟩
  have hconstant : paperAssigned.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
    have hambient := pullback.zeroExtension.constantMultiplicity
      twoScale.coarse.refined_multiplicity_band
    intro point hpoint
    have hpointAmbient : point ∈
        pullback.zeroExtension.ambientShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩
    have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
      (fun index => show paperAssigned.carrier index =
        pullback.zeroExtension.ambientShading.carrier index ∩ region from rfl)
      hpoint
    rw [hmultiplicity]
    exact hambient point hpointAmbient
  have hpaperSub : PureWZ2PaperIsSubshading
      paperAssigned heightLift.shading := by
    intro index point hpoint
    have hregion : point ∈ region := hpoint.2
    have hwindowPoint : point ∈ window.shading.union := hregion.1
    have hassignedRegion : point ∈ assignedRegion := hregion.2
    rcases Set.mem_iUnion₂.mp hassignedRegion with
      ⟨popularHeight, hpopularImage, hpointSlab⟩
    rcases Finset.mem_image.mp hpopularImage with
      ⟨heightIndex, hheightIndex, hassignedEq⟩
    rcases pullback.zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, hindex, hselected⟩
    have hsource : point ∈ source.shading.carrier index := by
      subst index
      exact twoScale.coarse.subshading selectedIndex hselected
    have hsourceUnion : point ∈ source.shading.union := ⟨index, hsource⟩
    rw [source.cubical.union_eq_activeCells source.extremal.delta_pos]
      at hsourceUnion
    rcases Set.mem_iUnion₂.mp hsourceUnion with
      ⟨cell, hcell, hpointCell⟩
    have hcellCondition : ∀ other ∈ wz1PaperGridCube delta cell,
        other 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ selectedHeight ∈ rich.heightIndices,
            |other 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale selectedHeight| ≤ prep.graphScale := by
      intro other hother
      have hotherClose : |other 2 - point 2| ≤ delta := by
        have hpointBounds := hpointCell
        have hotherBounds := hother
        rw [wz1PaperGridCube_eq_Ico source.extremal.delta_pos cell]
          at hpointBounds hotherBounds
        rw [abs_le]
        constructor <;>
          linarith [hpointBounds.2.2.2.2.1, hpointBounds.2.2.2.2.2,
            hotherBounds.2.2.2.2.1, hotherBounds.2.2.2.2.2]
      have hdeltaRho : delta ≤ rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.1
      have hrho : 0 < rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos
      have hcellEq : cell = wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
      refine ⟨richTrapezoid.window_cell_height_coverage
          point hwindowPoint other (by rwa [← hcellEq]),
        heightIndex, hheightIndex, ?_⟩
      apply source_cell_near_adjacent_graph_height
        hrho hdeltaRho prep.graphScale_eq
      · simpa only [hassignedEq] using hpointSlab
      · exact hotherClose
      · have hnear := assignment.assigned_near heightIndex hheightIndex
        rw [hassignedEq] at hnear
        exact hnear
    have hheightCell : cell ∈ heightLift.heightCells := by
      rw [heightLift.heightCells_eq]
      exact Finset.mem_filter.mpr ⟨hcell, hcellCondition⟩
    rw [heightLift.carrier_eq]
    refine ⟨hsource, ?_⟩
    rw [heightLift.region_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hheightCell, hpointCell⟩
  have hvolume :
      ((assignedHeights.card : ENNReal) *
          outerPopular.popular.layerMass) ≤ volume paperAssigned.union := by
    rw [hunion]
    have hpartition : region =
        ⋃ heightIndex ∈ assignedHeights,
          window.shading.union ∩
            wz1Lemma23HeightSlab prep.graphScale heightIndex := by
      ext point
      simp [region, assignedRegion]
    rw [hpartition]
    rw [MeasureTheory.measure_biUnion_finset]
    · calc
        (assignedHeights.card : ENNReal) *
              outerPopular.popular.layerMass =
            ∑ _heightIndex ∈ assignedHeights,
              outerPopular.popular.layerMass := by
                simp [Finset.sum_const]
        _ ≤ ∑ heightIndex ∈ assignedHeights,
            volume (window.shading.union ∩
              wz1Lemma23HeightSlab prep.graphScale heightIndex) := by
          apply Finset.sum_le_sum
          intro heightIndex hheightIndex
          have hpopular : heightIndex ∈
              outerPopular.popular.heightIndices :=
            assignment.assigned_image_subset hheightIndex
          have hband := outerPopular.popular.layer_volume_band
            heightIndex hpopular
          have hsliceEq :
              outerPopular.popular.shading.union ∩
                  wz1Lemma23HeightSlab (256 * rho) heightIndex =
                sourceWindow.shading.union ∩
                  wz1Lemma23HeightSlab (256 * rho) heightIndex := by
            rw [outerPopular.popular.union_eq]
            apply Set.Subset.antisymm
            · exact fun _ hpoint => ⟨hpoint.1.1, hpoint.2⟩
            · intro selectedPoint hselectedPoint
              refine ⟨⟨hselectedPoint.1, ?_⟩, hselectedPoint.2⟩
              rw [outerPopular.popular.heightRegion_eq]
              exact Set.mem_iUnion₂.mpr
                ⟨heightIndex, hpopular, hselectedPoint.2⟩
          rw [hwindow, prep.graphScale_eq, hsliceEq]
          exact hband.1
    · intro first _ second _ hne
      exact (wz1Lemma23_heightSlab_disjoint prep.graphScale_pos hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro heightIndex _
      exact (measurableSet_shading_union window.shading).inter (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  change (twoScale.coarse.fineMultiplicity : ENNReal) *
      ((assignedHeights.card : ENNReal) *
        outerPopular.popular.layerMass) ≤ heightLift.shading.mass
  calc
    (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((assignedHeights.card : ENNReal) *
            outerPopular.popular.layerMass) ≤
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          volume paperAssigned.union := by gcongr
    _ ≤ paperAssigned.mass :=
      (constant_multiplicity_mass_volume_generic hconstant).1
    _ ≤ heightLift.shading.mass := by
      apply Finset.sum_le_sum
      intro index _
      exact measure_mono (hpaperSub index)

/-- Final nearby-height source refill.  The only loss relative to exact height
containment is the cardinality-three assignment fiber. -/
theorem PureWZ2SourceAlternativeAHeightLift.mass_lower_of_nearby_outer_popular
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
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
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    {richTrapezoid : PureWZ2SourceAlternativeARichTrapezoid richShading}
    (heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid)
    (assignment : PureWZ2SourceEnvelopeHeightAssignmentData
      outerPopular rich)
    (hwindow : window.shading.union =
      outerPopular.popular.shading.union) :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        ((rich.heightIndices.card : ENNReal) *
          outerPopular.popular.layerMass) ≤
      3 * heightLift.shading.mass := by
  have hcardNat := assignment.rich_card_le_three_mul_assigned_card
  have hcard : (rich.heightIndices.card : ENNReal) ≤
      3 * ((rich.heightIndices.image assignment.assigned).card : ENNReal) := by
    exact_mod_cast hcardNat
  have hmass := heightLift.mass_lower_of_assigned_outer_popular
    assignment hwindow
  calc
    (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((rich.heightIndices.card : ENNReal) *
            outerPopular.popular.layerMass) ≤
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((3 * ((rich.heightIndices.image assignment.assigned).card : ENNReal)) *
            outerPopular.popular.layerMass) := by gcongr
    _ = 3 * ((twoScale.coarse.fineMultiplicity : ENNReal) *
          (((rich.heightIndices.image assignment.assigned).card : ENNReal) *
            outerPopular.popular.layerMass)) := by ring
    _ ≤ 3 * heightLift.shading.mass := by gcongr

end Kakeya.Assouad

end

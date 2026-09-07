import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryFinalMetricCardinalityBin
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryUpperGeometry

/-!
# Proposition 6.2: upper fibers from the final metric-parent partition

At one old coordinate above `rho`, the final old packet is exactly partitioned
by the final metric parents whose frozen upper ancestor is that old parent.
The pre-core `D_-` band and the one-pass density estimate then give the
factor-two upper bound, the scaled lower bound, and uniformity of every upper
cover fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

noncomputable abbrev finalUpperCoverData
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :=
  output.finalUpperMonochromaticCover
    coordinates rhoPos widthPos packetScaleLeRho
    sixWidthLe allAncestryCoordinatesUpper coordinate

noncomputable def finalUpperChildrenFiber
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    Finset
      (Fin output.finalMetricRestriction.coarseSelected.family.card) :=
  wz2PaperOrdinaryFullFiberIndices
    output.finalMetricRestriction.coarseSelected.family
    (output.finalUpperCoverData
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
      |>.selectedParents.family)
    parent

noncomputable def finalUpperOldParentIndex
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    Fin (output.finalOldScaleData coordinate.1).coarse.card :=
  ⟨(output.finalUpperCoverData
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
      |>.selectedParents.embedding parent).1,
    (output.finalUpperCoverData
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
      |>.selectedParents.embedding parent).2⟩

noncomputable def finalUpperOldLeafFiber
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    Finset
      (Fin output.finalMetricRestriction.fineSelected.family.card) :=
  wz2PaperOrdinaryFullFiberIndices
    output.finalMetricRestriction.fineSelected.family
    (output.finalOldScaleData coordinate.1).coarse
    (output.finalUpperOldParentIndex
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate parent)

theorem finalUpperChild_owner_eq
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card))
    (child : Fin output.finalMetricRestriction.coarseSelected.family.card) :
    child ∈
        output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent ↔
      finalUpperAncestor (output := output) coordinate child =
        output.finalUpperOldParentIndex
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent := by
  have fiberEq :=
    (output.finalUpperCoverData
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
      |>.fullFiberIndices_eq_owner parent)
  have memberEq :=
    Finset.ext_iff.mp fiberEq child
  constructor
  · intro childMem
    have ownerMem :=
      memberEq.mp childMem
    have ownerEq :=
      (Finset.mem_filter.mp ownerMem).2
    apply Fin.ext
    exact congrArg Fin.val ownerEq
  · intro ownerEq
    apply memberEq.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ child, ?_⟩
    apply Fin.ext
    exact congrArg Fin.val ownerEq

theorem finalMetricFiberIndices_eq_lineParent
    (child :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family child =
      Finset.univ.filter fun leaf =>
        output.finalMetricRestriction.lineCover.parent leaf = child := by
  ext leaf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_wz2PaperFullFiberIndices_iff]
  constructor
  · intro covered
    exact
      (output.finalMetricRestriction.lineCover.parent_unique
        leaf child covered).symm
  · intro parentEq
    rw [← parentEq]
    exact
      output.finalMetricRestriction.lineCover.parent_covers leaf

theorem finalUpperOldLeaf_mem_iff_lineParent_mem
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card))
    (leaf : Fin output.finalMetricRestriction.fineSelected.family.card) :
    leaf ∈
        output.finalUpperOldLeafFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent ↔
      output.finalMetricRestriction.lineCover.parent leaf ∈
        output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent := by
  let child :=
    output.finalMetricRestriction.lineCover.parent leaf
  have leafMetric :
      leaf ∈
        wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family child := by
    rw [output.finalMetricFiberIndices_eq_lineParent child]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ leaf, rfl⟩
  have oldParent :=
    output.finalUpperAncestor_source
      rhoPos widthPos packetScaleLeRho sixWidthLe
      allAncestryCoordinatesUpper coordinate child leaf leafMetric
  rw [finalUpperOldLeafFiber,
    (output.finalOldScaleData coordinate.1).cover.mem_fullFiber_iff_parent_eq
      (output.finalOldScaleData coordinate.1).rho_pos.le]
  rw [output.finalUpperChild_owner_eq
    coordinates rhoPos widthPos packetScaleLeRho
    sixWidthLe allAncestryCoordinatesUpper coordinate parent child]
  exact oldParent ▸ Iff.rfl

theorem finalUpperOldLeafFiber_filter_eq_metricFiber
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card))
    (child :
      Fin output.finalMetricRestriction.coarseSelected.family.card)
    (childMem :
      child ∈
        output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent) :
    (output.finalUpperOldLeafFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent).filter
          (fun leaf =>
            output.finalMetricRestriction.lineCover.parent leaf = child) =
      wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family child := by
  ext leaf
  simp only [Finset.mem_filter]
  rw [output.finalMetricFiberIndices_eq_lineParent child]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro parentEq
    exact
      ⟨(output.finalUpperOldLeaf_mem_iff_lineParent_mem
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent leaf).mpr
          (by rwa [parentEq]),
        parentEq⟩

theorem finalUpperOldLeafFiber_sum_metricFibers
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    (∑ child ∈
        output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent,
        (wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family child).card) =
      (output.finalUpperOldLeafFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent).card := by
  let leaves :=
    output.finalUpperOldLeafFiber
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate parent
  let children :=
    output.finalUpperChildrenFiber
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate parent
  let owner :=
    output.finalMetricRestriction.lineCover.parent
  have sumFiber :=
    Finset.sum_card_fiberwise_eq_card_filter leaves children owner
  have allLeaves : leaves.filter (fun leaf => owner leaf ∈ children) =
      leaves := by
    apply Finset.filter_true_of_mem
    intro leaf leafMem
    exact
      (output.finalUpperOldLeaf_mem_iff_lineParent_mem
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent leaf).mp
        leafMem
  rw [allLeaves] at sumFiber
  calc
    (∑ child ∈ children,
        (wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family child).card) =
        ∑ child ∈ children,
          (leaves.filter fun leaf => owner leaf = child).card := by
      apply Finset.sum_congr rfl
      intro child childMem
      rw [output.finalUpperOldLeafFiber_filter_eq_metricFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent
        child childMem]
    _ = leaves.card := sumFiber

theorem finalUpperOldLeafFiber_card_le
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    (output.finalUpperOldLeafFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent).card ≤
      2 * output.metricFiberCardinalityBin.fiberFloor *
        (output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent).card := by
  rw [← output.finalUpperOldLeafFiber_sum_metricFibers
    coordinates rhoPos widthPos packetScaleLeRho
    sixWidthLe allAncestryCoordinatesUpper coordinate parent]
  calc
    (∑ child ∈
        output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent,
        (wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family child).card) ≤
        ∑ _child ∈
          output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate parent,
          2 * output.metricFiberCardinalityBin.fiberFloor := by
      exact Finset.sum_le_sum fun child _ =>
        Nat.le_of_lt
          (output.finalMetricFiber_card_lt_two_fiberFloor child)
    _ =
        2 * output.metricFiberCardinalityBin.fiberFloor *
          (output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate parent).card := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem finalUpperFiber_scaled_lower
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        (output.finalUpperCoverData
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.selectedParents.family.card)) :
    (output.metricFiberCardinalityBin.fiberFloor : ENNReal) *
        ((output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent).card :
          ENNReal) ≤
      output.ancestryDensityLoss *
        ((output.finalUpperOldLeafFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent).card :
          ENNReal) := by
  have fiberSumENN :
      (∑ child ∈
          output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate parent,
          ((wz2PaperFullFiberIndices
            output.finalMetricRestriction.fineSelected.family
            output.finalMetricRestriction.coarseSelected.family child).card :
            ENNReal)) =
        ((output.finalUpperOldLeafFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent).card :
          ENNReal) := by
    exact_mod_cast
      output.finalUpperOldLeafFiber_sum_metricFibers
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate parent
  calc
    (output.metricFiberCardinalityBin.fiberFloor : ENNReal) *
        ((output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate parent).card :
          ENNReal) =
        ∑ _child ∈
          output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate parent,
          (output.metricFiberCardinalityBin.fiberFloor : ENNReal) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤
        ∑ child ∈
          output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate parent,
          output.ancestryDensityLoss *
            ((wz2PaperFullFiberIndices
              output.finalMetricRestriction.fineSelected.family
              output.finalMetricRestriction.coarseSelected.family child).card :
              ENNReal) := by
      exact Finset.sum_le_sum fun child _ =>
        output.fiberFloor_le_ancestryDensityLoss_finalMetricFiber
          rhoPos widthPos packetScaleLeRho sixWidthLe
          schedule.parent_covers allAncestryCoordinatesUpper child
    _ =
        output.ancestryDensityLoss *
          ∑ child ∈
            output.finalUpperChildrenFiber
              coordinates rhoPos widthPos packetScaleLeRho
              sixWidthLe allAncestryCoordinatesUpper coordinate parent,
            ((wz2PaperFullFiberIndices
              output.finalMetricRestriction.fineSelected.family
              output.finalMetricRestriction.coarseSelected.family child).card :
              ENNReal) := by
      exact
        (Finset.mul_sum
          (output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate parent)
          (fun child =>
            ((wz2PaperFullFiberIndices
              output.finalMetricRestriction.fineSelected.family
              output.finalMetricRestriction.coarseSelected.family child).card :
              ENNReal))
          output.ancestryDensityLoss).symm
    _ =
        output.ancestryDensityLoss *
          ((output.finalUpperOldLeafFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate parent).card :
            ENNReal) := by
      rw [fiberSumENN]

def finalUpperFiberUniformConstant : ENNReal :=
  output.ancestryDensityLoss * output.finalCoreConstant * 2

theorem finalUpperFullFiber_uniform
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ ancestryCoordinate :
          schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate ancestryCoordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :
    WZ2PaperPureFullFibersAreCUniform
      output.finalMetricRestriction.coarseSelected.family
      (output.finalUpperCoverData
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate
        |>.selectedParents.family)
      output.finalUpperFiberUniformConstant := by
  intro first second
  change
    ((output.finalUpperChildrenFiber
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate first).card :
      ENNReal) ≤
    output.finalUpperFiberUniformConstant *
      ((output.finalUpperChildrenFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate second).card :
        ENNReal)
  let firstOld :=
    output.finalUpperOldParentIndex
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate first
  let secondOld :=
    output.finalUpperOldParentIndex
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate second
  have firstLower :=
    output.finalUpperFiber_scaled_lower
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate first
  have oldUniform :=
    (output.finalOldScaleData coordinate.1).full_fiber_uniform
      firstOld secondOld
  have secondUpperNat :=
    output.finalUpperOldLeafFiber_card_le
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate second
  have secondUpper :
      ((output.finalUpperOldLeafFiber
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate second).card :
        ENNReal) ≤
      (2 : ENNReal) *
        (output.metricFiberCardinalityBin.fiberFloor : ENNReal) *
        ((output.finalUpperChildrenFiber
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate second).card :
          ENNReal) := by
    exact_mod_cast secondUpperNat
  have scaled :
      (output.metricFiberCardinalityBin.fiberFloor : ENNReal) *
          ((output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate first).card :
            ENNReal) ≤
        (output.finalUpperFiberUniformConstant *
          ((output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate second).card :
            ENNReal)) *
          (output.metricFiberCardinalityBin.fiberFloor : ENNReal) := by
    calc
      (output.metricFiberCardinalityBin.fiberFloor : ENNReal) *
          ((output.finalUpperChildrenFiber
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate first).card :
            ENNReal) ≤
          output.ancestryDensityLoss *
            ((output.finalUpperOldLeafFiber
              coordinates rhoPos widthPos packetScaleLeRho
              sixWidthLe allAncestryCoordinatesUpper coordinate first).card :
              ENNReal) :=
        firstLower
      _ ≤
          output.ancestryDensityLoss *
            (output.finalCoreConstant *
              ((output.finalUpperOldLeafFiber
                coordinates rhoPos widthPos packetScaleLeRho
                sixWidthLe allAncestryCoordinatesUpper coordinate second).card :
                ENNReal)) := by
        gcongr
        exact oldUniform
      _ ≤
          output.ancestryDensityLoss *
            (output.finalCoreConstant *
              ((2 : ENNReal) *
                (output.metricFiberCardinalityBin.fiberFloor : ENNReal) *
                ((output.finalUpperChildrenFiber
                  coordinates rhoPos widthPos packetScaleLeRho
                  sixWidthLe allAncestryCoordinatesUpper coordinate second).card :
                  ENNReal))) := by
        gcongr
      _ =
          (output.finalUpperFiberUniformConstant *
            ((output.finalUpperChildrenFiber
              coordinates rhoPos widthPos packetScaleLeRho
              sixWidthLe allAncestryCoordinatesUpper coordinate second).card :
              ENNReal)) *
            (output.metricFiberCardinalityBin.fiberFloor : ENNReal) := by
        simp only [finalUpperFiberUniformConstant]
        ring
  have floorPos :
      0 <
        (output.metricFiberCardinalityBin.fiberFloor : ENNReal) := by
    exact_mod_cast
      output.metricFiberCardinalityBin.fiberFloor_pos
  have floorTop :
      (output.metricFiberCardinalityBin.fiberFloor : ENNReal) ≠ ⊤ := by
    simp
  exact
    (ENNReal.mul_le_mul_iff_right floorPos.ne' floorTop).mp <| by
      simpa [mul_comm, mul_assoc] using scaled

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end

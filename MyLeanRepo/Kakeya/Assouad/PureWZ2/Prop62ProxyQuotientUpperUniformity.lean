import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PerParentSourceColorLeafBin
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPrefixBridge

/-!
# Proposition 6.2 quotient-prefix upper-fiber uniformity

This module isolates the finite counting argument for the strict fibers of an
upper quotient-center cover.  The actual-copy packing bound, the old-scale
packet uniformity constant, and the normalized one-pass cleanup density are
all explicit inputs.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62ProxyQuotientAuxiliaryLevel

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)

/--
Actual Definition 2.12 parents at one upper coordinate whose canonical
representatives lie in the chosen quotient-prefix node.
-/
def prefixActualParents
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card) :
    Finset
      (Fin (schedule.scaleData coordinate.1).coarse.card) :=
  Finset.univ.filter fun parent =>
    schedule.parentRepresentative
        fineNonempty coordinate.1 parent ∈
      auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor

theorem prefixEquivalent_of_coordinateParent_eq
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (first second : Fin fine.card)
    (parentEq :
      (schedule.scaleData coordinate.1).cover.parent first =
        (schedule.scaleData coordinate.1).cover.parent second) :
    schedule.proxyUpperCenterPrefixEquivalent
      fineNonempty quotient rho packetCoordinate
      (coordinate.1.1 + 1) first second := by
  intro earlier earlierLt
  unfold
    PureWZ2Prop62LaminarPureSchedule.proxyUpperCenterAncestry
    PureWZ2Prop62ProxyQuotientScheduleData.leafCenter
  congr 1
  have earlierLe : earlier.1.1 ≤ coordinate.1.1 :=
    Nat.lt_succ_iff.mp earlierLt
  exact
    schedule.parent_eq_of_coordinate_le
      earlier.1
      coordinate.1 earlierLe first second parentEq

theorem prefixActualParents_subset_centerActualParents
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card) :
    auxiliary.prefixActualParents coordinate anchor ⊆
      quotient.centerActualParents coordinate.1
        (quotient.leafCenter coordinate.1 anchor) := by
  intro parent parentMem
  have representativePrefix :
      schedule.parentRepresentative
          fineNonempty coordinate.1 parent ∈
        auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor :=
    (Finset.mem_filter.mp parentMem).2
  have prefixEquivalent :
      schedule.proxyUpperCenterPrefixEquivalent
        fineNonempty quotient rho packetCoordinate
        (coordinate.1.1 + 1)
        (schedule.parentRepresentative
          fineNonempty coordinate.1 parent)
        anchor := by
    simpa only [
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
      Finset.mem_filter, Finset.mem_univ, true_and
    ] using representativePrefix
  have currentCenterEq :=
    prefixEquivalent coordinate (Nat.lt_succ_self coordinate.1.1)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ parent, ?_⟩
  change
    quotient.actualCenter coordinate.1 parent =
      quotient.leafCenter coordinate.1 anchor
  simpa only [
    PureWZ2Prop62LaminarPureSchedule.proxyUpperCenterAncestry,
    PureWZ2Prop62ProxyQuotientScheduleData.leafCenter,
    schedule.parentRepresentative_parent
  ] using currentCenterEq

theorem prefixActualParents_card_le
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (Bcopy : ENNReal)
    (centerCopyBound :
      ∀ center,
        ((quotient.centerActualParents
          coordinate.1 center).card : ENNReal) ≤ Bcopy) :
    ((auxiliary.prefixActualParents
      coordinate anchor).card : ENNReal) ≤ Bcopy := by
  exact
    (by
      exact_mod_cast
        Finset.card_le_card
          (auxiliary.prefixActualParents_subset_centerActualParents
            coordinate anchor) :
      ((auxiliary.prefixActualParents
        coordinate anchor).card : ENNReal) ≤
        ((quotient.centerActualParents coordinate.1
          (quotient.leafCenter coordinate.1 anchor)).card :
          ENNReal)).trans
      (centerCopyBound
        (quotient.leafCenter coordinate.1 anchor))

theorem prefixNodeAt_eq_actualParent_biUnion
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card) :
    auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor =
      (auxiliary.prefixActualParents coordinate anchor).biUnion
        (wz2PaperOrdinaryFullFiberIndices
          fine (schedule.scaleData coordinate.1).coarse) := by
  ext source
  constructor
  · intro sourcePrefix
    let parent :=
      (schedule.scaleData coordinate.1).cover.parent source
    have representativeParent :
        (schedule.scaleData coordinate.1).cover.parent
            (schedule.parentRepresentative
              fineNonempty coordinate.1 parent) =
          parent :=
      schedule.parentRepresentative_parent
        fineNonempty coordinate.1 parent
    have representativeSourcePrefix :
        schedule.proxyUpperCenterPrefixEquivalent
          fineNonempty quotient rho packetCoordinate
          (coordinate.1.1 + 1)
          (schedule.parentRepresentative
            fineNonempty coordinate.1 parent)
          source :=
      prefixEquivalent_of_coordinateParent_eq
        (schedule := schedule) (fineNonempty := fineNonempty)
        (quotient := quotient) coordinate _ _ <| by
          rw [representativeParent]
    have sourceAnchorPrefix :
        schedule.proxyUpperCenterPrefixEquivalent
          fineNonempty quotient rho packetCoordinate
          (coordinate.1.1 + 1) source anchor := by
      simpa only [
        PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
        Finset.mem_filter, Finset.mem_univ, true_and
      ] using sourcePrefix
    have representativePrefix :
        schedule.parentRepresentative
            fineNonempty coordinate.1 parent ∈
          auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor := by
      simp only [
        PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
        Finset.mem_filter, Finset.mem_univ, true_and
      ]
      exact
        schedule.proxyUpperCenterPrefixEquivalent_trans
          fineNonempty quotient rho packetCoordinate
          representativeSourcePrefix sourceAnchorPrefix
    exact
      Finset.mem_biUnion.mpr
        ⟨parent,
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ parent, representativePrefix⟩,
          (schedule.scaleData coordinate.1).cover
            |>.parent_mem_fullFiber source⟩
  · intro sourceUnion
    rcases Finset.mem_biUnion.mp sourceUnion with
      ⟨parent, parentMem, sourceFiber⟩
    have representativePrefix :
        schedule.parentRepresentative
            fineNonempty coordinate.1 parent ∈
          auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor :=
      (Finset.mem_filter.mp parentMem).2
    have representativeAnchorPrefix :
        schedule.proxyUpperCenterPrefixEquivalent
          fineNonempty quotient rho packetCoordinate
          (coordinate.1.1 + 1)
          (schedule.parentRepresentative
            fineNonempty coordinate.1 parent)
          anchor := by
      simpa only [
        PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
        Finset.mem_filter, Finset.mem_univ, true_and
      ] using representativePrefix
    have sourceParent :
        (schedule.scaleData coordinate.1).cover.parent source =
          parent :=
      ((schedule.scaleData coordinate.1).cover
        |>.mem_fullFiber_iff_parent_eq
          (schedule.scaleData coordinate.1).rho_pos.le
          parent source).mp sourceFiber
    have representativeParent :=
      schedule.parentRepresentative_parent
        fineNonempty coordinate.1 parent
    have sourceRepresentativePrefix :
        schedule.proxyUpperCenterPrefixEquivalent
          fineNonempty quotient rho packetCoordinate
          (coordinate.1.1 + 1) source
          (schedule.parentRepresentative
            fineNonempty coordinate.1 parent) :=
      prefixEquivalent_of_coordinateParent_eq
        (schedule := schedule) (fineNonempty := fineNonempty)
        (quotient := quotient) coordinate _ _ <| by
          rw [sourceParent, representativeParent]
    simp only [
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
      Finset.mem_filter, Finset.mem_univ, true_and
    ]
    exact
      schedule.proxyUpperCenterPrefixEquivalent_trans
        fineNonempty quotient rho packetCoordinate
        sourceRepresentativePrefix representativeAnchorPrefix

theorem actualFiber_subset_prefixNodeAt
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (anchor : Fin fine.card)
    (parent :
      Fin (schedule.scaleData coordinate.1).coarse.card)
    (parentMem :
      parent ∈ auxiliary.prefixActualParents coordinate anchor) :
    wz2PaperOrdinaryFullFiberIndices
        fine (schedule.scaleData coordinate.1).coarse parent ⊆
      auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor := by
  rw [auxiliary.prefixNodeAt_eq_actualParent_biUnion
    coordinate anchor]
  exact
    Finset.subset_biUnion_of_mem
      (wz2PaperOrdinaryFullFiberIndices
        fine (schedule.scaleData coordinate.1).coarse)
      parentMem

theorem prefixNodeAt_card_le_copy_mul_ambient
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (firstAnchor secondAnchor : Fin fine.card)
    (Bcopy Cold : ENNReal)
    (centerCopyBound :
      ∀ center,
        ((quotient.centerActualParents
          coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      WZ2PaperPureFullFibersAreCUniform
        fine (schedule.scaleData coordinate.1).coarse Cold) :
    ((auxiliary.prefixNodeAt
      (coordinate.1.1 + 1) firstAnchor).card : ENNReal) ≤
      Bcopy * Cold *
        ((auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) secondAnchor).card : ENNReal) := by
  let secondParent :=
    (schedule.scaleData coordinate.1).cover.parent secondAnchor
  have secondFiberSubset :
      wz2PaperOrdinaryFullFiberIndices
          fine (schedule.scaleData coordinate.1).coarse secondParent ⊆
        auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) secondAnchor := by
    intro source sourceMem
    have sourceParent :
        (schedule.scaleData coordinate.1).cover.parent source =
          secondParent :=
      ((schedule.scaleData coordinate.1).cover
        |>.mem_fullFiber_iff_parent_eq
          (schedule.scaleData coordinate.1).rho_pos.le
          secondParent source).mp sourceMem
    simp only [
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
      Finset.mem_filter, Finset.mem_univ, true_and
    ]
    exact
      prefixEquivalent_of_coordinateParent_eq
        (schedule := schedule) (fineNonempty := fineNonempty)
        (quotient := quotient)
        coordinate source secondAnchor sourceParent
  have secondFiberCardLe :
      ((wz2PaperOrdinaryFullFiberIndices
        fine (schedule.scaleData coordinate.1).coarse
        secondParent).card : ENNReal) ≤
      ((auxiliary.prefixNodeAt
        (coordinate.1.1 + 1) secondAnchor).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card secondFiberSubset
  have unionCardLe :
      (((auxiliary.prefixActualParents coordinate firstAnchor).biUnion
        (wz2PaperOrdinaryFullFiberIndices
          fine (schedule.scaleData coordinate.1).coarse)).card :
          ENNReal) ≤
        ∑ parent ∈
          auxiliary.prefixActualParents coordinate firstAnchor,
          ((wz2PaperOrdinaryFullFiberIndices
            fine (schedule.scaleData coordinate.1).coarse parent).card :
            ENNReal) := by
    exact_mod_cast
      (Finset.card_biUnion_le :
        ((auxiliary.prefixActualParents coordinate firstAnchor).biUnion
          (wz2PaperOrdinaryFullFiberIndices
            fine (schedule.scaleData coordinate.1).coarse)).card ≤
          ∑ parent ∈
            auxiliary.prefixActualParents coordinate firstAnchor,
            (wz2PaperOrdinaryFullFiberIndices
              fine (schedule.scaleData coordinate.1).coarse parent).card)
  rw [auxiliary.prefixNodeAt_eq_actualParent_biUnion
    coordinate firstAnchor]
  calc
    (((auxiliary.prefixActualParents coordinate firstAnchor).biUnion
      (wz2PaperOrdinaryFullFiberIndices
        fine (schedule.scaleData coordinate.1).coarse)).card :
        ENNReal) ≤
      ∑ parent ∈
        auxiliary.prefixActualParents coordinate firstAnchor,
        ((wz2PaperOrdinaryFullFiberIndices
          fine (schedule.scaleData coordinate.1).coarse parent).card :
          ENNReal) :=
      unionCardLe
    _ ≤
      ∑ _parent ∈
        auxiliary.prefixActualParents coordinate firstAnchor,
        Cold *
          ((wz2PaperOrdinaryFullFiberIndices
            fine (schedule.scaleData coordinate.1).coarse
            secondParent).card : ENNReal) := by
      apply Finset.sum_le_sum
      intro parent _parentMem
      simpa only [wz2PaperOrdinaryFullFiberCount] using
        ambientUniform parent secondParent
    _ =
      ((auxiliary.prefixActualParents
        coordinate firstAnchor).card : ENNReal) *
        (Cold *
          ((wz2PaperOrdinaryFullFiberIndices
            fine (schedule.scaleData coordinate.1).coarse
            secondParent).card : ENNReal)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤
      Bcopy *
        (Cold *
          ((wz2PaperOrdinaryFullFiberIndices
            fine (schedule.scaleData coordinate.1).coarse
            secondParent).card : ENNReal)) := by
      gcongr
      exact
        auxiliary.prefixActualParents_card_le
          coordinate firstAnchor Bcopy centerCopyBound
    _ ≤
      Bcopy * Cold *
        ((auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) secondAnchor).card : ENNReal) := by
      calc
        Bcopy *
            (Cold *
              ((wz2PaperOrdinaryFullFiberIndices
                fine (schedule.scaleData coordinate.1).coarse
                secondParent).card : ENNReal)) ≤
          Bcopy *
            (Cold *
              ((auxiliary.prefixNodeAt
                (coordinate.1.1 + 1) secondAnchor).card :
                ENNReal)) := by
          gcongr
        _ = _ := by ring

end PureWZ2Prop62ProxyQuotientAuxiliaryLevel

/--
Restrict one fixed strong quotient-center coloring to the selected upper
envelope family.  This is deterministic and does not invoke
`upperEnvelopeColoring` or make a second coloring choice.
-/
def PureWZ2Prop62UpperEnvelopeCenterColoringData.toUpperEnvelopeColoring
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (output :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    (output.upperEnvelopeScaleInput
      fineLine fineBase rhoPos coordinate).ColoringData where
  color := fun center =>
    coloring.color coordinate
      ((output.upperCenters coordinate).embedding center)
  proper := by
    intro first second indexNe overlap
    apply coloring.proper coordinate
    · exact
        (output.upperCenters coordinate).embedding.injective.ne
          indexNe
    · rw [wz1PaperLineDistance_symm]
      exact
        output.upperEnvelope_conflict_centerDistance_le
          fineLine rhoPos coordinate overlap

@[simp]
theorem PureWZ2Prop62UpperEnvelopeCenterColoringData.toUpperEnvelopeColoring_childColor
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (output :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin output.metricParents.card) :
    (output.upperEnvelopeScaleInput
      fineLine fineBase rhoPos coordinate).childColor
        (coloring.toUpperEnvelopeColoring
          output fineLine fineBase rhoPos coordinate)
        parent =
      coloring.metricParentColor output coordinate parent := by
  change
    coloring.color coordinate
        ((output.upperCenters coordinate).embedding
          (output.upperEnvelopeOwner coordinate parent)) =
      coloring.color coordinate
        (output.upperQuotientCenter coordinate parent)
  rw [output.upperEnvelopeOwner_ambient]

/-- Leaves in one complete metric-parent fiber before the final cleanup. -/
def pureWZ2Prop62WholeMetricFiber
    {Leaf Parent : Type*}
    [DecidableEq Leaf]
    (wholeLeaves : Finset Leaf)
    (metricParent : Leaf → Parent)
    (parent : Parent) :
    Finset Leaf :=
  wholeLeaves.filter fun leaf => metricParent leaf = parent

@[simp]
theorem mem_pureWZ2Prop62WholeMetricFiber
    {Leaf Parent : Type*}
    [DecidableEq Leaf]
    {wholeLeaves : Finset Leaf}
    {metricParent : Leaf → Parent}
    {parent : Parent}
    {leaf : Leaf} :
    leaf ∈
        pureWZ2Prop62WholeMetricFiber
          wholeLeaves metricParent parent ↔
      leaf ∈ wholeLeaves ∧ metricParent leaf = parent := by
  simp [pureWZ2Prop62WholeMetricFiber]

/-- Metric parents still hit after the final cleanup. -/
def pureWZ2Prop62SurvivingMetricParents
    {Leaf Parent : Type*}
    [DecidableEq Parent]
    (core : Finset Leaf)
    (metricParent : Leaf → Parent) :
    Finset Parent :=
  core.image metricParent

@[simp]
theorem mem_pureWZ2Prop62SurvivingMetricParents
    {Leaf Parent : Type*}
    [DecidableEq Parent]
    {core : Finset Leaf}
    {metricParent : Leaf → Parent}
    {parent : Parent} :
    parent ∈
        pureWZ2Prop62SurvivingMetricParents core metricParent ↔
      ∃ leaf ∈ core, metricParent leaf = parent := by
  simp [pureWZ2Prop62SurvivingMetricParents]

/--
The upper strict fiber through an anchor: surviving metric parents whose
upper quotient center agrees with the anchor's upper center.
-/
def pureWZ2Prop62UpperStrictFiberAt
    {Leaf Parent Center : Type*}
    [DecidableEq Parent] [DecidableEq Center]
    (core : Finset Leaf)
    (metricParent : Leaf → Parent)
    (upperCenter : Parent → Center)
    (anchor : Leaf) :
    Finset Parent :=
  (pureWZ2Prop62SurvivingMetricParents core metricParent).filter
    fun parent =>
      upperCenter parent = upperCenter (metricParent anchor)

/--
Finite counting core for upper strict-fiber uniformity.  The prefix comparison
and cleanup-density estimate are explicit inputs.  The only remaining loss is
the factor-two whole-metric-fiber band, so the resulting constant is exactly
`2 * Bcopy * Cold * Λ`.
-/
theorem pureWZ2_prop62_upperStrictFiberAt_uniform_of_prefix
    {Leaf Parent Center : Type*}
    [DecidableEq Leaf] [DecidableEq Parent] [DecidableEq Center]
    (wholeLeaves core : Finset Leaf)
    (metricParent : Leaf → Parent)
    (upperCenter : Parent → Center)
    (prefixFiber : Leaf → Finset Leaf)
    (DMinus : ℕ)
    (Bcopy Cold Λ : ENNReal)
    (DMinus_pos : 0 < DMinus)
    (core_subset : core ⊆ wholeLeaves)
    (prefix_mem_iff :
      ∀ anchor ∈ core, ∀ leaf ∈ wholeLeaves,
        leaf ∈ prefixFiber anchor ↔
          upperCenter (metricParent leaf) =
            upperCenter (metricParent anchor))
    (wholeMetricFiber_band :
      ∀ parent ∈ wholeLeaves.image metricParent,
        DMinus ≤
            (pureWZ2Prop62WholeMetricFiber
              wholeLeaves metricParent parent).card ∧
          (pureWZ2Prop62WholeMetricFiber
            wholeLeaves metricParent parent).card ≤
            2 * DMinus)
    (prefix_comparison :
      ∀ first second,
        ((prefixFiber first).card : ENNReal) ≤
          Bcopy * Cold * ((prefixFiber second).card : ENNReal))
    (receipt_density :
      ∀ anchor ∈ core,
        ((prefixFiber anchor).card : ENNReal) ≤
          Λ * ((core ∩ prefixFiber anchor).card : ENNReal))
    (firstAnchor secondAnchor : Leaf)
    (firstAnchor_mem : firstAnchor ∈ core)
    (secondAnchor_mem : secondAnchor ∈ core) :
    ((pureWZ2Prop62UpperStrictFiberAt
      core metricParent upperCenter firstAnchor).card : ENNReal) ≤
      (2 * Bcopy * Cold * Λ) *
        ((pureWZ2Prop62UpperStrictFiberAt
          core metricParent upperCenter secondAnchor).card :
          ENNReal) := by
  let firstParents :=
    pureWZ2Prop62UpperStrictFiberAt
      core metricParent upperCenter firstAnchor
  let secondParents :=
    pureWZ2Prop62UpperStrictFiberAt
      core metricParent upperCenter secondAnchor
  let parentFiber := pureWZ2Prop62WholeMetricFiber
    wholeLeaves metricParent
  have survivingParentWhole :
      ∀ parent ∈ pureWZ2Prop62SurvivingMetricParents core metricParent,
        parent ∈ wholeLeaves.image metricParent := by
    intro parent parentMem
    rcases Finset.mem_image.mp parentMem with
      ⟨leaf, leafCore, rfl⟩
    exact Finset.mem_image.mpr
      ⟨leaf, core_subset leafCore, rfl⟩
  have parentFibersDisjoint :
      ∀ parents : Finset Parent,
        (↑parents : Set Parent).PairwiseDisjoint parentFiber := by
    intro parents
    rw [Finset.pairwiseDisjoint_iff]
    intro first firstMem second secondMem overlap
    rcases overlap with ⟨leaf, leafMem⟩
    have firstEq :
        metricParent leaf = first :=
      (mem_pureWZ2Prop62WholeMetricFiber.mp
        (Finset.mem_inter.mp leafMem).1).2
    have secondEq :
        metricParent leaf = second :=
      (mem_pureWZ2Prop62WholeMetricFiber.mp
        (Finset.mem_inter.mp leafMem).2).2
    exact firstEq.symm.trans secondEq
  have firstUnionSubset :
      firstParents.biUnion parentFiber ⊆ prefixFiber firstAnchor := by
    intro leaf leafMem
    rcases Finset.mem_biUnion.mp leafMem with
      ⟨parent, parentMem, leafFiber⟩
    have parentData := Finset.mem_filter.mp parentMem
    have leafWhole :=
      (mem_pureWZ2Prop62WholeMetricFiber.mp leafFiber).1
    have leafParent :=
      (mem_pureWZ2Prop62WholeMetricFiber.mp leafFiber).2
    apply
      (prefix_mem_iff
        firstAnchor firstAnchor_mem leaf leafWhole).2
    rw [leafParent]
    exact parentData.2
  have firstScaledLowerNat :
      DMinus * firstParents.card ≤
        (prefixFiber firstAnchor).card := by
    calc
      DMinus * firstParents.card =
          ∑ _parent ∈ firstParents, DMinus := by
        simp [Finset.sum_const, mul_comm]
      _ ≤
          ∑ parent ∈ firstParents,
            (parentFiber parent).card := by
        apply Finset.sum_le_sum
        intro parent parentMem
        exact
          (wholeMetricFiber_band parent <|
            survivingParentWhole
              parent ((Finset.mem_filter.mp parentMem).1)).1
      _ =
          (firstParents.biUnion parentFiber).card := by
        exact
          (Finset.card_biUnion
            (parentFibersDisjoint firstParents)).symm
      _ ≤ (prefixFiber firstAnchor).card :=
        Finset.card_le_card firstUnionSubset
  have firstScaledLower :
      (DMinus : ENNReal) *
          (firstParents.card : ENNReal) ≤
        ((prefixFiber firstAnchor).card : ENNReal) := by
    exact_mod_cast firstScaledLowerNat
  have secondCorePrefixSubset :
      core ∩ prefixFiber secondAnchor ⊆
        secondParents.biUnion parentFiber := by
    intro leaf leafMem
    have leafCore := (Finset.mem_inter.mp leafMem).1
    have leafPrefix := (Finset.mem_inter.mp leafMem).2
    have leafWhole := core_subset leafCore
    let parent := metricParent leaf
    have parentSurvives :
        parent ∈
          pureWZ2Prop62SurvivingMetricParents core metricParent :=
      Finset.mem_image.mpr ⟨leaf, leafCore, rfl⟩
    have centerEq :=
      (prefix_mem_iff
        secondAnchor secondAnchor_mem leaf leafWhole).1 leafPrefix
    have parentStrict : parent ∈ secondParents :=
      Finset.mem_filter.mpr ⟨parentSurvives, centerEq⟩
    exact
      Finset.mem_biUnion.mpr
        ⟨parent, parentStrict,
          mem_pureWZ2Prop62WholeMetricFiber.mpr
            ⟨leafWhole, rfl⟩⟩
  have secondCorePrefixUpperNat :
      (core ∩ prefixFiber secondAnchor).card ≤
        2 * DMinus * secondParents.card := by
    calc
      (core ∩ prefixFiber secondAnchor).card ≤
          (secondParents.biUnion parentFiber).card :=
        Finset.card_le_card secondCorePrefixSubset
      _ =
          ∑ parent ∈ secondParents,
            (parentFiber parent).card :=
        Finset.card_biUnion
          (parentFibersDisjoint secondParents)
      _ ≤
          ∑ _parent ∈ secondParents, 2 * DMinus := by
        apply Finset.sum_le_sum
        intro parent parentMem
        exact
          (wholeMetricFiber_band parent <|
            survivingParentWhole
              parent ((Finset.mem_filter.mp parentMem).1)).2
      _ = 2 * DMinus * secondParents.card := by
        simp [Finset.sum_const, mul_comm]
  have secondCorePrefixUpper :
      ((core ∩ prefixFiber secondAnchor).card : ENNReal) ≤
        (2 : ENNReal) * DMinus *
          (secondParents.card : ENNReal) := by
    exact_mod_cast secondCorePrefixUpperNat
  have scaled :
      (DMinus : ENNReal) *
          (firstParents.card : ENNReal) ≤
        ((2 * Bcopy * Cold * Λ) *
          (secondParents.card : ENNReal)) *
            (DMinus : ENNReal) := by
    calc
      (DMinus : ENNReal) *
          (firstParents.card : ENNReal) ≤
        ((prefixFiber firstAnchor).card : ENNReal) :=
      firstScaledLower
      _ ≤
          Bcopy * Cold *
            ((prefixFiber secondAnchor).card : ENNReal) :=
        prefix_comparison firstAnchor secondAnchor
      _ ≤
          Bcopy * Cold *
            (Λ *
              ((core ∩ prefixFiber secondAnchor).card : ENNReal)) := by
        gcongr
        exact receipt_density secondAnchor secondAnchor_mem
      _ ≤
          Bcopy * Cold *
            (Λ *
              ((2 : ENNReal) * DMinus *
                (secondParents.card : ENNReal))) := by
        gcongr
      _ =
          ((2 * Bcopy * Cold * Λ) *
            (secondParents.card : ENNReal)) *
              (DMinus : ENNReal) := by
        ring
  have DMinus_ne_zero : (DMinus : ENNReal) ≠ 0 := by
    exact_mod_cast DMinus_pos.ne'
  have DMinus_ne_top : (DMinus : ENNReal) ≠ ⊤ := by
    simp
  exact
    (ENNReal.mul_le_mul_iff_right
      DMinus_ne_zero DMinus_ne_top).mp <| by
        simpa [mul_comm, mul_assoc] using scaled

/--
Quotient-prefix specialization.  Global monochromaticity is deliberately an
explicit parent-level hypothesis; it is not inferred from the older per-cell
ancestry selection.
-/
theorem pureWZ2_prop62_proxyQuotient_upperStrictFiber_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)
    (output :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    (wholeLeaves : Finset (Fin fine.card))
    (metricParent :
      Fin fine.card → Fin output.metricParents.card)
    (sourceColor : Fin fine.card → SourceColor)
    (total : ENNReal)
    (selection :
      PureWZ2Prop62PerParentSourceColorLeafBinData
        (Fin fine.card) (Fin output.metricParents.card) SourceColor
        wholeLeaves metricParent sourceColor weight total)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        auxiliary.tree selection.selected)
    (coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (selectedUpperColor :
      ∀ _coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
    (selectedParents_monochromatic :
      ∀ parent ∈ wholeLeaves.image metricParent,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          (output.upperEnvelopeScaleInput
            fineLine fineBase rhoPos coordinate).childColor
              (coloring.toUpperEnvelopeColoring
                output fineLine fineBase rhoPos coordinate)
              parent =
            selectedUpperColor coordinate)
    (leafCenter_eq_upperCenter :
      ∀ leaf ∈ wholeLeaves,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          quotient.leafCenter coordinate.1 leaf =
            output.upperQuotientCenter coordinate
              (metricParent leaf))
    (DMinus : ℕ)
    (DMinus_pos : 0 < DMinus)
    (wholeMetricFiber_band :
      ∀ parent ∈ wholeLeaves.image metricParent,
        DMinus ≤
            (pureWZ2Prop62WholeMetricFiber
              wholeLeaves metricParent parent).card ∧
          (pureWZ2Prop62WholeMetricFiber
            wholeLeaves metricParent parent).card ≤
            2 * DMinus)
    (Bcopy Cold Λ : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (receipt_density :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ anchor ∈ receipt.core,
          ((auxiliary.prefixNodeAt
            (coordinate.1.1 + 1) anchor).card : ENNReal) ≤
            Λ *
              ((receipt.core ∩
                auxiliary.prefixNodeAt
                  (coordinate.1.1 + 1) anchor).card : ENNReal))
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (firstAnchor secondAnchor : Fin fine.card)
    (firstAnchor_mem : firstAnchor ∈ receipt.core)
    (secondAnchor_mem : secondAnchor ∈ receipt.core) :
    ((pureWZ2Prop62UpperStrictFiberAt
      receipt.core metricParent
        (output.upperQuotientCenter coordinate)
        firstAnchor).card : ENNReal) ≤
      (2 * Bcopy * Cold * Λ) *
        ((pureWZ2Prop62UpperStrictFiberAt
          receipt.core metricParent
            (output.upperQuotientCenter coordinate)
            secondAnchor).card : ENNReal) := by
  have coreSubsetWhole : receipt.core ⊆ wholeLeaves :=
    receipt.core_subset.trans
      selection.selected_subset_wholeLeaves
  have leafMonochromatic :
      ∀ leaf ∈ wholeLeaves,
        ∀ current :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor current leaf =
            selectedUpperColor current := by
    intro leaf leafMem current
    unfold
      PureWZ2Prop62UpperEnvelopeCenterColoringData.leafColor
    rw [leafCenter_eq_upperCenter leaf leafMem current]
    change
      coloring.metricParentColor output current (metricParent leaf) =
        selectedUpperColor current
    simpa only [
      PureWZ2Prop62UpperEnvelopeCenterColoringData.toUpperEnvelopeColoring_childColor
    ] using
      selectedParents_monochromatic
        (metricParent leaf)
        (Finset.mem_image.mpr ⟨leaf, leafMem, rfl⟩)
        current
  have prefixMembership :
      ∀ anchor ∈ receipt.core, ∀ leaf ∈ wholeLeaves,
        leaf ∈
            auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) anchor ↔
          output.upperQuotientCenter coordinate (metricParent leaf) =
            output.upperQuotientCenter coordinate
              (metricParent anchor) := by
    intro anchor anchorCore leaf leafWhole
    have anchorWhole := coreSubsetWhole anchorCore
    have bridge :=
      coloring.monochromatic_centerPacket_inter_prefixNode
        fineLine fineBase wholeLeaves selectedUpperColor
        leafMonochromatic auxiliary anchor anchorWhole coordinate
    have membership :=
      Finset.ext_iff.mp bridge leaf
    simp only [
      Finset.mem_inter, leafWhole, true_and,
      PureWZ2Prop62ProxyQuotientScheduleData.centerPacketIndices,
      Finset.mem_filter, Finset.mem_univ
    ] at membership
    rw [
      leafCenter_eq_upperCenter leaf leafWhole coordinate,
      leafCenter_eq_upperCenter anchor anchorWhole coordinate
    ] at membership
    exact membership.symm
  exact
    pureWZ2_prop62_upperStrictFiberAt_uniform_of_prefix
      wholeLeaves receipt.core metricParent
      (output.upperQuotientCenter coordinate)
      (fun anchor =>
        auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) anchor)
      DMinus Bcopy Cold Λ DMinus_pos coreSubsetWhole
      prefixMembership wholeMetricFiber_band
      (fun first second =>
        auxiliary.prefixNodeAt_card_le_copy_mul_ambient
          coordinate first second Bcopy Cold
          (centerCopyBound coordinate)
          (ambientUniform coordinate))
      (receipt_density coordinate)
      firstAnchor secondAnchor firstAnchor_mem secondAnchor_mem

end Kakeya.Assouad

end

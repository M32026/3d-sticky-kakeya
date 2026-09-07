import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ReferenceTreeCharge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeRanges
import Mathlib.Algebra.Order.Floor.Div

/-!
# Proposition 6.2: assembly of the terminal four-degree core

This module performs no new geometric choice.  It starts from the three
ordered dyadic bins, uses ceiling divisions as the integer versions of the
paper thresholds

`K / A0`, `d / A0`, `n / A0`, `D / A0`,

and runs the four degree deletions together with all reference-tree
deletions in one finite peeling process.

The asymptotic choice of `A0 = C_L J^4` is isolated in one scalar gate saying
that the total coordinate and tree charges are at most half of the binned
edge pool.  Under that gate the terminal core is nonempty and retains at
least half of the binned edges.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)

def parentThreshold (A0 : ℕ) : ℕ :=
  parentDegree.K ⌈/⌉ A0

def fineCellThreshold
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (A0 : ℕ) : ℕ :=
  2 ^ bins.fineCellBin.level ⌈/⌉ A0

def parentCoarseThreshold
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (A0 : ℕ) : ℕ :=
  2 ^ bins.parentCoarseBin.level ⌈/⌉ A0

def coarseCellThreshold
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (A0 : ℕ) : ℕ :=
  2 ^ bins.coarseCellBin.level ⌈/⌉ A0

def commonBinCount
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges) : ℕ :=
  1 + bins.fineCellBin.binCount +
    bins.parentCoarseBin.binCount +
    bins.coarseCellBin.binCount

def canonicalPeelingA0
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges) : ℕ :=
  8 * (schedule.levelCount + 2) *
    (input.commonBinCount
      multiplicity parentClass treeCleanup exactification bins) ^ 4

theorem mul_ceilDiv_sub_one_le
    (base A0 : ℕ)
    (A0_pos : 0 < A0) :
    A0 * (base ⌈/⌉ A0 - 1) ≤ base := by
  by_cases quotientZero : base ⌈/⌉ A0 = 0
  · simp [quotientZero]
  · have quotientPos : 0 < base ⌈/⌉ A0 :=
      Nat.pos_of_ne_zero quotientZero
    have predecessorLt :
        base ⌈/⌉ A0 - 1 < base ⌈/⌉ A0 := by
      omega
    have notBaseLe :
        ¬base ≤ A0 * (base ⌈/⌉ A0 - 1) := by
      intro baseLe
      have quotientLe :
          base ⌈/⌉ A0 ≤ base ⌈/⌉ A0 - 1 :=
        (ceilDiv_le_iff_le_mul A0_pos).2 baseLe
      omega
    omega

theorem fourDegreeCapacity_scaled_le
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (A0 : ℕ)
    (A0_pos : 0 < A0) :
    A0 *
        exactification.incidence.fourDegreeCapacity
          (input.parentThreshold
            multiplicity parentClass treeCleanup
            exactification parentDegree A0)
          (input.fineCellThreshold
            multiplicity parentClass treeCleanup
            exactification bins A0)
          (input.parentCoarseThreshold
            multiplicity parentClass treeCleanup
            exactification bins A0)
          (input.coarseCellThreshold
            multiplicity parentClass treeCleanup
            exactification bins A0)
          bins.finalEdges ≤
      4 * exactification.incidence.allEdges.card := by
  have parentSupportSubset :
      exactification.incidence.activeParents bins.finalEdges ⊆
        exactification.incidence.activeParents
          exactification.incidence.allEdges :=
    by
      intro parent parentMem
      rcases Finset.mem_image.mp parentMem with
        ⟨edge, edgeMem, rfl⟩
      exact Finset.mem_image.mpr
        ⟨edge,
          PureWZ2Prop62FourDegreeIncidenceData.ThreeDegreeBinningData.finalEdges_subset_initial
            exactification.incidence bins edgeMem,
          rfl⟩
  have parentBase :
      (exactification.incidence.activeParents bins.finalEdges).card *
          parentDegree.K ≤
        exactification.incidence.allEdges.card := by
    calc
      (exactification.incidence.activeParents bins.finalEdges).card *
          parentDegree.K ≤
          (exactification.incidence.activeParents
              exactification.incidence.allEdges).card *
            parentDegree.K := by
        exact Nat.mul_le_mul_right parentDegree.K
          (Finset.card_le_card parentSupportSubset)
      _ =
          treeCleanup.referenceParents.card *
            parentDegree.K := by
        rw [input.referenceParents_eq_activeParents
          multiplicity parentClass treeCleanup exactification]
      _ ≤ exactification.incidence.allEdges.card :=
        input.referenceParents_card_mul_K_le_allEdges_card
          multiplicity parentClass treeCleanup exactification
            parentDegree
  have fineCellBase :
      (exactification.incidence.activeFineCells bins.finalEdges).card *
          2 ^ bins.fineCellBin.level ≤
        exactification.incidence.allEdges.card := by
    simpa [PureWZ2Prop62FourDegreeIncidenceData.activeFineCells] using
      PureWZ2Prop62FourDegreeIncidenceData.DegreeBinData.active_card_mul_lower_le_card
        exactification.incidence bins.fineCellBin
        bins.finalEdges_subset_fineCell
  have parentCoarseBase :
      (exactification.incidence.activeParentCoarsePairs
          bins.finalEdges).card *
          2 ^ bins.parentCoarseBin.level ≤
        exactification.incidence.allEdges.card := by
    have selectedBound :
        bins.fineCellBin.selectedEdges.card ≤
          exactification.incidence.allEdges.card :=
      Finset.card_le_card bins.fineCellBin.selectedEdges_subset
    have baseBound :
        (exactification.incidence.activeParentCoarsePairs
            bins.finalEdges).card *
            2 ^ bins.parentCoarseBin.level ≤
          bins.fineCellBin.selectedEdges.card := by
      simpa [
        PureWZ2Prop62FourDegreeIncidenceData.activeParentCoarsePairs
      ] using
        PureWZ2Prop62FourDegreeIncidenceData.DegreeBinData.active_card_mul_lower_le_card
          exactification.incidence bins.parentCoarseBin
          bins.finalEdges_subset_parentCoarse
    exact baseBound.trans selectedBound
  have coarseCellBase :
      (exactification.incidence.activeCoarseCells bins.finalEdges).card *
          2 ^ bins.coarseCellBin.level ≤
        exactification.incidence.allEdges.card := by
    have selectedBound :
        bins.parentCoarseBin.selectedEdges.card ≤
          exactification.incidence.allEdges.card :=
      Finset.card_le_card <|
        bins.parentCoarseBin.selectedEdges_subset.trans
          bins.fineCellBin.selectedEdges_subset
    have baseBound :
        (exactification.incidence.activeCoarseCells
            bins.finalEdges).card *
            2 ^ bins.coarseCellBin.level ≤
          bins.parentCoarseBin.selectedEdges.card := by
      change
        (bins.coarseCellBin.selectedEdges.image
            exactification.incidence.edgeCoarseCell).card *
            2 ^ bins.coarseCellBin.level ≤
          bins.parentCoarseBin.selectedEdges.card
      exact
        PureWZ2Prop62FourDegreeIncidenceData.DegreeBinData.active_card_mul_lower_le_card
          exactification.incidence bins.coarseCellBin
          (fun _ edgeMem => edgeMem)
    exact baseBound.trans selectedBound
  have parentCharge :
      A0 *
          ((exactification.incidence.activeParents bins.finalEdges).card *
            (input.parentThreshold
                multiplicity parentClass treeCleanup
                exactification parentDegree A0 - 1)) ≤
        exactification.incidence.allEdges.card := by
    calc
      A0 *
          ((exactification.incidence.activeParents bins.finalEdges).card *
            (input.parentThreshold
                multiplicity parentClass treeCleanup
                exactification parentDegree A0 - 1)) =
          (exactification.incidence.activeParents bins.finalEdges).card *
            (A0 *
              (parentDegree.K ⌈/⌉ A0 - 1)) := by
        simp only [parentThreshold]
        ring
      _ ≤
          (exactification.incidence.activeParents bins.finalEdges).card *
            parentDegree.K := by
        exact Nat.mul_le_mul_left _
          (mul_ceilDiv_sub_one_le parentDegree.K A0 A0_pos)
      _ ≤ exactification.incidence.allEdges.card :=
        parentBase
  have fineCellCharge :
      A0 *
          ((exactification.incidence.activeFineCells bins.finalEdges).card *
            (input.fineCellThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0 - 1)) ≤
        exactification.incidence.allEdges.card := by
    calc
      A0 *
          ((exactification.incidence.activeFineCells bins.finalEdges).card *
            (input.fineCellThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0 - 1)) =
          (exactification.incidence.activeFineCells bins.finalEdges).card *
            (A0 *
              (2 ^ bins.fineCellBin.level ⌈/⌉ A0 - 1)) := by
        simp only [fineCellThreshold]
        ring
      _ ≤
          (exactification.incidence.activeFineCells bins.finalEdges).card *
            2 ^ bins.fineCellBin.level := by
        exact Nat.mul_le_mul_left _
          (mul_ceilDiv_sub_one_le
            (2 ^ bins.fineCellBin.level) A0 A0_pos)
      _ ≤ exactification.incidence.allEdges.card :=
        fineCellBase
  have parentCoarseCharge :
      A0 *
          ((exactification.incidence.activeParentCoarsePairs
              bins.finalEdges).card *
            (input.parentCoarseThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0 - 1)) ≤
        exactification.incidence.allEdges.card := by
    calc
      A0 *
          ((exactification.incidence.activeParentCoarsePairs
              bins.finalEdges).card *
            (input.parentCoarseThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0 - 1)) =
          (exactification.incidence.activeParentCoarsePairs
              bins.finalEdges).card *
            (A0 *
              (2 ^ bins.parentCoarseBin.level ⌈/⌉ A0 - 1)) := by
        simp only [parentCoarseThreshold]
        ring
      _ ≤
          (exactification.incidence.activeParentCoarsePairs
              bins.finalEdges).card *
            2 ^ bins.parentCoarseBin.level := by
        exact Nat.mul_le_mul_left _
          (mul_ceilDiv_sub_one_le
            (2 ^ bins.parentCoarseBin.level) A0 A0_pos)
      _ ≤ exactification.incidence.allEdges.card :=
        parentCoarseBase
  have coarseCellCharge :
      A0 *
          ((exactification.incidence.activeCoarseCells
              bins.finalEdges).card *
            (input.coarseCellThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0 - 1)) ≤
        exactification.incidence.allEdges.card := by
    calc
      A0 *
          ((exactification.incidence.activeCoarseCells
              bins.finalEdges).card *
            (input.coarseCellThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0 - 1)) =
          (exactification.incidence.activeCoarseCells
              bins.finalEdges).card *
            (A0 *
              (2 ^ bins.coarseCellBin.level ⌈/⌉ A0 - 1)) := by
        simp only [coarseCellThreshold]
        ring
      _ ≤
          (exactification.incidence.activeCoarseCells
              bins.finalEdges).card *
            2 ^ bins.coarseCellBin.level := by
        exact Nat.mul_le_mul_left _
          (mul_ceilDiv_sub_one_le
            (2 ^ bins.coarseCellBin.level) A0 A0_pos)
      _ ≤ exactification.incidence.allEdges.card :=
        coarseCellBase
  rw [
    exactification.incidence.fourDegreeCapacity_eq,
    Nat.mul_add, Nat.mul_add, Nat.mul_add
  ]
  omega

theorem commonBinCount_pos
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges) :
    0 <
      input.commonBinCount
        multiplicity parentClass treeCleanup exactification bins := by
  unfold commonBinCount
  omega

theorem allEdges_card_le_commonBinCube_finalEdges
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges) :
    exactification.incidence.allEdges.card ≤
      (input.commonBinCount
          multiplicity parentClass treeCleanup exactification bins) ^ 3 *
        bins.finalEdges.card := by
  apply bins.common_log_retention
  · unfold commonBinCount
    omega
  · unfold commonBinCount
    omega
  · unfold commonBinCount
    omega

theorem totalCharge_scaled_le
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (A0 : ℕ)
    (A0_pos : 0 < A0) :
    A0 *
        (exactification.incidence.fourDegreeCapacity
            (input.parentThreshold
              multiplicity parentClass treeCleanup
              exactification parentDegree A0)
            (input.fineCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            (input.parentCoarseThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            (input.coarseCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            bins.finalEdges +
          ∑ label ∈
              input.referenceTreeLabels
                multiplicity parentClass treeCleanup,
            input.referenceTreeCharge
              multiplicity parentClass treeCleanup exactification
                parentDegree A0 label) ≤
      4 * (schedule.levelCount + 2) *
        exactification.incidence.allEdges.card := by
  have coordinateCharge :=
    input.fourDegreeCapacity_scaled_le
      multiplicity parentClass treeCleanup exactification
        parentDegree bins A0 A0_pos
  have treeCharge :=
    input.referenceTreeCharge_sum_scaled_le
      multiplicity parentClass treeCleanup exactification
        parentDegree A0
  rw [Nat.mul_add]
  calc
    A0 *
          exactification.incidence.fourDegreeCapacity
            (input.parentThreshold
              multiplicity parentClass treeCleanup
              exactification parentDegree A0)
            (input.fineCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            (input.parentCoarseThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            (input.coarseCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            bins.finalEdges +
        A0 *
          ∑ label ∈
              input.referenceTreeLabels
                multiplicity parentClass treeCleanup,
            input.referenceTreeCharge
              multiplicity parentClass treeCleanup exactification
                parentDegree A0 label ≤
        4 * exactification.incidence.allEdges.card +
          4 * (schedule.levelCount + 1) *
            exactification.incidence.allEdges.card :=
      Nat.add_le_add coordinateCharge treeCharge
    _ =
        4 * (schedule.levelCount + 2) *
          exactification.incidence.allEdges.card := by
      ring

theorem canonicalPeelingA0_pos
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges) :
    0 <
      input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins := by
  unfold canonicalPeelingA0
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num) (by omega))
    (pow_pos
      (input.commonBinCount_pos
        multiplicity parentClass treeCleanup exactification bins) 4)

theorem canonical_halfCharge
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges) :
    2 *
        (exactification.incidence.fourDegreeCapacity
            (input.parentThreshold
              multiplicity parentClass treeCleanup
              exactification parentDegree
              (input.canonicalPeelingA0
                multiplicity parentClass treeCleanup
                  exactification bins))
            (input.fineCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins
              (input.canonicalPeelingA0
                multiplicity parentClass treeCleanup
                  exactification bins))
            (input.parentCoarseThreshold
              multiplicity parentClass treeCleanup
              exactification bins
              (input.canonicalPeelingA0
                multiplicity parentClass treeCleanup
                  exactification bins))
            (input.coarseCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins
              (input.canonicalPeelingA0
                multiplicity parentClass treeCleanup
                  exactification bins))
            bins.finalEdges +
          ∑ label ∈
              input.referenceTreeLabels
                multiplicity parentClass treeCleanup,
            input.referenceTreeCharge
              multiplicity parentClass treeCleanup exactification
                parentDegree
                (input.canonicalPeelingA0
                  multiplicity parentClass treeCleanup
                    exactification bins)
                label) ≤
      bins.finalEdges.card := by
  let J :=
    input.commonBinCount
      multiplicity parentClass treeCleanup exactification bins
  let A0 :=
    input.canonicalPeelingA0
      multiplicity parentClass treeCleanup exactification bins
  let totalCharge :=
    exactification.incidence.fourDegreeCapacity
        (input.parentThreshold
          multiplicity parentClass treeCleanup
          exactification parentDegree A0)
        (input.fineCellThreshold
          multiplicity parentClass treeCleanup
          exactification bins A0)
        (input.parentCoarseThreshold
          multiplicity parentClass treeCleanup
          exactification bins A0)
        (input.coarseCellThreshold
          multiplicity parentClass treeCleanup
          exactification bins A0)
        bins.finalEdges +
      ∑ label ∈
          input.referenceTreeLabels
            multiplicity parentClass treeCleanup,
        input.referenceTreeCharge
          multiplicity parentClass treeCleanup exactification
            parentDegree A0 label
  have JPos : 0 < J := by
    exact
      input.commonBinCount_pos
        multiplicity parentClass treeCleanup exactification bins
  have A0Pos : 0 < A0 := by
    exact
      input.canonicalPeelingA0_pos
        multiplicity parentClass treeCleanup exactification bins
  have scaledCharge :
      A0 * totalCharge ≤
        4 * (schedule.levelCount + 2) *
          exactification.incidence.allEdges.card := by
    exact
      input.totalCharge_scaled_le
        multiplicity parentClass treeCleanup exactification
          parentDegree bins A0 A0Pos
  have retention :
      exactification.incidence.allEdges.card ≤
        J ^ 3 * bins.finalEdges.card := by
    exact
      input.allEdges_card_le_commonBinCube_finalEdges
        multiplicity parentClass treeCleanup exactification bins
  have cubeLeFourth : J ^ 3 ≤ J ^ 4 := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right (J ^ 3) JPos
  have scaledHalf :
      A0 * (2 * totalCharge) ≤
        A0 * bins.finalEdges.card := by
    calc
      A0 * (2 * totalCharge) =
          2 * (A0 * totalCharge) := by ring
      _ ≤
          2 *
            (4 * (schedule.levelCount + 2) *
              exactification.incidence.allEdges.card) := by
        exact Nat.mul_le_mul_left 2 scaledCharge
      _ ≤
          2 *
            (4 * (schedule.levelCount + 2) *
              (J ^ 3 * bins.finalEdges.card)) := by
        exact Nat.mul_le_mul_left 2 <|
          Nat.mul_le_mul_left (4 * (schedule.levelCount + 2)) retention
      _ ≤
          8 * (schedule.levelCount + 2) *
            J ^ 4 * bins.finalEdges.card := by
        calc
          2 *
              (4 * (schedule.levelCount + 2) *
                (J ^ 3 * bins.finalEdges.card)) =
              8 * (schedule.levelCount + 2) *
                (J ^ 3 * bins.finalEdges.card) := by ring
          _ ≤
              8 * (schedule.levelCount + 2) *
                (J ^ 4 * bins.finalEdges.card) := by
            exact Nat.mul_le_mul_left _ <|
              Nat.mul_le_mul_right bins.finalEdges.card cubeLeFourth
          _ =
              8 * (schedule.levelCount + 2) *
                J ^ 4 * bins.finalEdges.card := by ring
      _ = A0 * bins.finalEdges.card := by
        rfl
  change 2 * totalCharge ≤ bins.finalEdges.card
  exact Nat.le_of_mul_le_mul_left scaledHalf A0Pos

structure FourDegreeCoreAssemblyData
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (A0 : ℕ) where
  A0_pos : 0 < A0
  peeling :
    exactification.incidence.SimultaneousPeelingCoreData
      bins.finalEdges
      (input.parentThreshold
        multiplicity parentClass treeCleanup
        exactification parentDegree A0)
      (input.fineCellThreshold
        multiplicity parentClass treeCleanup
        exactification bins A0)
      (input.parentCoarseThreshold
        multiplicity parentClass treeCleanup
        exactification bins A0)
      (input.coarseCellThreshold
        multiplicity parentClass treeCleanup
        exactification bins A0)
      (input.referenceTreeLabels
        multiplicity parentClass treeCleanup)
      (input.referenceTreeBad
        multiplicity parentClass treeCleanup exactification A0)
      (input.referenceTreeCharge
        multiplicity parentClass treeCleanup
        exactification parentDegree A0)
  half_charge :
    2 *
        (exactification.incidence.fourDegreeCapacity
            (input.parentThreshold
              multiplicity parentClass treeCleanup
              exactification parentDegree A0)
            (input.fineCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            (input.parentCoarseThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            (input.coarseCellThreshold
              multiplicity parentClass treeCleanup
              exactification bins A0)
            bins.finalEdges +
          ∑ label ∈
              input.referenceTreeLabels
                multiplicity parentClass treeCleanup,
            input.referenceTreeCharge
              multiplicity parentClass treeCleanup
              exactification parentDegree A0 label) ≤
      bins.finalEdges.card
  core_nonempty : peeling.core.Nonempty
  half_retention :
    bins.finalEdges.card ≤ 2 * peeling.core.card
  ranges :
    exactification.incidence.FourDegreeRangeData
      bins
      (input.parentThreshold
        multiplicity parentClass treeCleanup
        exactification parentDegree A0)
      (input.fineCellThreshold
        multiplicity parentClass treeCleanup
        exactification bins A0)
      (input.parentCoarseThreshold
        multiplicity parentClass treeCleanup
        exactification bins A0)
      (input.coarseCellThreshold
        multiplicity parentClass treeCleanup
        exactification bins A0)
      (input.referenceTreeLabels
        multiplicity parentClass treeCleanup)
      (input.referenceTreeBad
        multiplicity parentClass treeCleanup exactification A0)
      (input.referenceTreeCharge
        multiplicity parentClass treeCleanup
        exactification parentDegree A0)
  ranges_peeling_eq :
    ranges.peeling = peeling
  parent_degree_strict :
    ∀ parent,
      0 <
          exactification.incidence.parentDegree
            peeling.core parent →
        exactification.incidence.parentDegree
            peeling.core parent <
          4 * parentDegree.K

namespace FourDegreeCoreAssemblyData

variable
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)

theorem parent_range
    (parent : Fin coarse.card)
    (degree_pos :
      0 <
        exactification.incidence.parentDegree
          core.peeling.core parent) :
    input.parentThreshold
          multiplicity parentClass treeCleanup
          exactification parentDegree A0 ≤
        exactification.incidence.parentDegree
          core.peeling.core parent ∧
      exactification.incidence.parentDegree
          core.peeling.core parent <
        4 * parentDegree.K := by
  exact
    ⟨PureWZ2Prop62FourDegreeIncidenceData.SimultaneousPeelingCoreData.parent_degree_lower
      exactification.incidence core.peeling parent degree_pos,
      core.parent_degree_strict parent degree_pos⟩

theorem tree_stable
    (label :
      input.ReferenceTreeLabel)
    (labelMem :
      label ∈
        input.referenceTreeLabels
          multiplicity parentClass treeCleanup) :
    ¬input.referenceTreeBad
      multiplicity parentClass treeCleanup exactification
      A0 core.peeling.core label :=
  core.peeling.tree_stable label labelMem

end FourDegreeCoreAssemblyData

theorem pureWZ2_prop62_four_degree_core_assembly
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges)
    (A0 : ℕ)
    (A0_pos : 0 < A0)
    (halfCharge :
      2 *
          (exactification.incidence.fourDegreeCapacity
              (input.parentThreshold
                multiplicity parentClass treeCleanup
                exactification parentDegree A0)
              (input.fineCellThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0)
              (input.parentCoarseThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0)
              (input.coarseCellThreshold
                multiplicity parentClass treeCleanup
                exactification bins A0)
              bins.finalEdges +
            ∑ label ∈
                input.referenceTreeLabels
                  multiplicity parentClass treeCleanup,
              input.referenceTreeCharge
                multiplicity parentClass treeCleanup
                exactification parentDegree A0 label) ≤
        bins.finalEdges.card) :
    Nonempty
      (input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0) := by
  rcases
      exactification.incidence
        |>.pureWZ2_prop62_simultaneous_peeling_core
          bins.finalEdges
          (input.parentThreshold
            multiplicity parentClass treeCleanup
            exactification parentDegree A0)
          (input.fineCellThreshold
            multiplicity parentClass treeCleanup
            exactification bins A0)
          (input.parentCoarseThreshold
            multiplicity parentClass treeCleanup
            exactification bins A0)
          (input.coarseCellThreshold
            multiplicity parentClass treeCleanup
            exactification bins A0)
          (input.referenceTreeLabels
            multiplicity parentClass treeCleanup)
          (input.referenceTreeBlock
            multiplicity parentClass treeCleanup exactification)
          (input.referenceTreeBad
            multiplicity parentClass treeCleanup exactification A0)
          (input.referenceTreeCharge
            multiplicity parentClass treeCleanup
            exactification parentDegree A0)
          (fun edges label bad =>
            input.referenceTreeBad_nonempty
              multiplicity parentClass treeCleanup exactification
              A0 edges label bad)
          (fun edges label bad =>
            input.referenceTreeBad_card_le_charge
              multiplicity parentClass treeCleanup exactification
              parentDegree A0 A0_pos edges label bad)
    with ⟨peeling⟩
  have coreNonempty :
      peeling.core.Nonempty :=
    PureWZ2Prop62FourDegreeIncidenceData.SimultaneousPeelingCoreData.core_nonempty
      exactification.incidence peeling
      bins.finalEdges_nonempty halfCharge
  have halfRetention :
      bins.finalEdges.card ≤ 2 * peeling.core.card :=
    PureWZ2Prop62FourDegreeIncidenceData.SimultaneousPeelingCoreData.half_retention
      exactification.incidence peeling halfCharge
  have parentUpper :
      ∀ parent,
        exactification.incidence.parentDegree
            peeling.core parent ≤
          4 * parentDegree.K := by
    intro parent
    have coreSubsetAll :
        peeling.core ⊆ exactification.incidence.allEdges :=
      peeling.core_subset.trans
        bins.finalEdges_subset_initial
    have degreeMono :
        exactification.incidence.parentDegree
            peeling.core parent ≤
          exactification.incidence.parentDegree
            exactification.incidence.allEdges parent := by
      apply Finset.card_le_card
      intro edge edgeMem
      have edgeData := Finset.mem_filter.mp edgeMem
      exact
        Finset.mem_filter.mpr
          ⟨coreSubsetAll edgeData.1, edgeData.2⟩
    by_cases degreeZero :
        exactification.incidence.parentDegree
            peeling.core parent = 0
    · simp [degreeZero]
    · have ambientPos :
          0 <
            exactification.incidence.parentDegree
              exactification.incidence.allEdges parent :=
        lt_of_lt_of_le (Nat.pos_of_ne_zero degreeZero) degreeMono
      have parentActive :
          parent ∈
            exactification.incidence.activeParents
              exactification.incidence.allEdges := by
        rw [exactification.incidence.mem_activeParents_iff]
        exact ambientPos
      exact degreeMono.trans
        (parentDegree.incidence_degree_band
          parent parentActive).2.le
  let ranges :
      exactification.incidence.FourDegreeRangeData
        bins
        (input.parentThreshold
          multiplicity parentClass treeCleanup
          exactification parentDegree A0)
        (input.fineCellThreshold
          multiplicity parentClass treeCleanup
          exactification bins A0)
        (input.parentCoarseThreshold
          multiplicity parentClass treeCleanup
          exactification bins A0)
        (input.coarseCellThreshold
          multiplicity parentClass treeCleanup
          exactification bins A0)
        (input.referenceTreeLabels
          multiplicity parentClass treeCleanup)
        (input.referenceTreeBad
          multiplicity parentClass treeCleanup exactification A0)
        (input.referenceTreeCharge
          multiplicity parentClass treeCleanup
          exactification parentDegree A0) :=
    {
      peeling := peeling
      parentUpper := 4 * parentDegree.K
      parent_upper := parentUpper
    }
  have parentStrict :
      ∀ parent,
        0 <
            exactification.incidence.parentDegree
              peeling.core parent →
          exactification.incidence.parentDegree
              peeling.core parent <
            4 * parentDegree.K := by
    intro parent degreePos
    have coreSubsetAll :
        peeling.core ⊆ exactification.incidence.allEdges :=
      peeling.core_subset.trans
        bins.finalEdges_subset_initial
    have degreeMono :
        exactification.incidence.parentDegree
            peeling.core parent ≤
          exactification.incidence.parentDegree
            exactification.incidence.allEdges parent := by
      apply Finset.card_le_card
      intro edge edgeMem
      have edgeData := Finset.mem_filter.mp edgeMem
      exact
        Finset.mem_filter.mpr
          ⟨coreSubsetAll edgeData.1, edgeData.2⟩
    have ambientPos :
        0 <
          exactification.incidence.parentDegree
            exactification.incidence.allEdges parent :=
      degreePos.trans_le degreeMono
    have parentActive :
        parent ∈
          exactification.incidence.activeParents
            exactification.incidence.allEdges := by
      rw [exactification.incidence.mem_activeParents_iff]
      exact ambientPos
    exact degreeMono.trans_lt
      (parentDegree.incidence_degree_band
        parent parentActive).2
  exact
    ⟨{
      A0_pos := A0_pos
      peeling := peeling
      half_charge := halfCharge
      core_nonempty := coreNonempty
      half_retention := halfRetention
      ranges := ranges
      ranges_peeling_eq := rfl
      parent_degree_strict := parentStrict
    }⟩

theorem pureWZ2_prop62_canonical_four_degree_core_assembly
    (bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges) :
    Nonempty
      (input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification
          parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins)) := by
  exact
    input.pureWZ2_prop62_four_degree_core_assembly
      multiplicity parentClass treeCleanup exactification parentDegree
      bins
      (input.canonicalPeelingA0
        multiplicity parentClass treeCleanup exactification bins)
      (input.canonicalPeelingA0_pos
        multiplicity parentClass treeCleanup exactification bins)
      (input.canonical_halfCharge
        multiplicity parentClass treeCleanup exactification
          parentDegree bins)

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end

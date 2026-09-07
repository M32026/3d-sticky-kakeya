import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeCoreAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62BalancingLowerTail

/-!
# Proposition 6.2: canonical exact-balancing sample

The terminal four-degree ranges imply the fixed-quota selection rate

`N(Q) ≤ 4 * A0^2 * W`

for every active coarse cell.  Combining this deterministic estimate with
the hypergeometric lower-tail theorem leaves one explicit finite scalar gate:
the sum of the parent exponential tails is less than one.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped BigOperators

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
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)

namespace FourDegreeCoreAssemblyData

def balancingRateLoss
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0) : ℕ :=
  4 * A0 ^ 2

def balancingDegreeLoss
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0) : ℕ :=
  2 * _core.balancingRateLoss
    input multiplicity parentClass treeCleanup
      exactification parentDegree

theorem balancingRateLoss_pos :
    0 <
      core.balancingRateLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree := by
  unfold balancingRateLoss
  exact Nat.mul_pos (by norm_num) (pow_pos core.A0_pos 2)

theorem balancingDegreeLoss_pos :
    0 <
      core.balancingDegreeLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree := by
  unfold balancingDegreeLoss
  exact Nat.mul_pos (by norm_num) <|
    core.balancingRateLoss_pos
      input multiplicity parentClass treeCleanup
        exactification parentDegree

theorem balancing_selection_rate
    (coarseCell : core.ranges.ActiveCoarseCell) :
    (core.ranges.availableFineCells coarseCell).card ≤
      core.balancingRateLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree *
        core.ranges.commonFineCellCount := by
  let fineBase : ℕ := 2 ^ bins.fineCellBin.level
  let coarseBase : ℕ := 2 ^ bins.coarseCellBin.level
  let fineCount : ℕ :=
    core.ranges.activeFineCount coarseCell.1
  let W : ℕ := core.ranges.commonFineCellCount
  have coarsePos :=
    core.ranges.activeCoarseCell_degree_pos coarseCell
  have fineLowerBound :
      input.fineCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 *
          fineCount ≤
        exactification.incidence.coarseDegree
          core.ranges.terminalEdges coarseCell.1 := by
    simpa [fineCount] using
      core.ranges.fineLower_mul_activeFineCount_le_coarseDegree
        coarsePos
  have coarseDegreeUpper :
      exactification.incidence.coarseDegree
            core.ranges.terminalEdges coarseCell.1 <
        2 * coarseBase := by
    have upper :=
      (core.ranges.coarse_degree_range coarsePos).2
    simpa [
      PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.coarseUpper,
      coarseBase,
      pow_succ,
      Nat.mul_comm
    ] using upper
  have fineBaseLeThreshold :
      fineBase ≤
        A0 *
          input.fineCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 := by
    simpa [
      fineBase,
      PureWZ2Prop62PacketCellInput.fineCellThreshold
    ] using
      (le_smul_ceilDiv core.A0_pos :
        2 ^ bins.fineCellBin.level ≤
          A0 * (2 ^ bins.fineCellBin.level ⌈/⌉ A0))
  have coarseBaseLeThreshold :
      coarseBase ≤
        A0 *
          input.coarseCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 := by
    simpa [
      coarseBase,
      PureWZ2Prop62PacketCellInput.coarseCellThreshold
    ] using
      (le_smul_ceilDiv core.A0_pos :
        2 ^ bins.coarseCellBin.level ≤
          A0 * (2 ^ bins.coarseCellBin.level ⌈/⌉ A0))
  have coarseThresholdLe :
      input.coarseCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 ≤
        core.ranges.fineUpper * W := by
    have raw :=
      le_smul_ceilDiv
        (show 0 < core.ranges.fineUpper by
          simp [
            PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineUpper
          ])
        (b :=
          input.coarseCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0)
    exact raw.trans <|
      Nat.mul_le_mul_left core.ranges.fineUpper
        (le_max_right _ _)
  have scaledUpper :
      2 * coarseBase ≤
        (4 * A0 ^ 2 * W) *
          input.fineCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 := by
    calc
      2 * coarseBase ≤
          2 *
            (A0 *
              input.coarseCellThreshold
                multiplicity parentClass treeCleanup
                  exactification bins A0) :=
        Nat.mul_le_mul_left 2 coarseBaseLeThreshold
      _ ≤
          2 * (A0 * (core.ranges.fineUpper * W)) := by
        gcongr
      _ = 4 * A0 * fineBase * W := by
        simp [
          PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineUpper,
          fineBase,
          pow_succ
        ]
        ring
      _ ≤
          4 * A0 *
              (A0 *
                input.fineCellThreshold
                  multiplicity parentClass treeCleanup
                    exactification bins A0) *
            W := by
        gcongr
      _ =
          (4 * A0 ^ 2 * W) *
            input.fineCellThreshold
              multiplicity parentClass treeCleanup
                exactification bins A0 := by
        ring
  have multiplied :
      input.fineCellThreshold
              multiplicity parentClass treeCleanup
                exactification bins A0 *
            fineCount <
        (4 * A0 ^ 2 * W) *
          input.fineCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 :=
    fineLowerBound.trans_lt <|
      coarseDegreeUpper.trans_le scaledUpper
  have fineThresholdPos :
      0 <
        input.fineCellThreshold
          multiplicity parentClass treeCleanup
            exactification bins A0 := by
    by_contra thresholdNotPos
    have thresholdZero :
        input.fineCellThreshold
          multiplicity parentClass treeCleanup
            exactification bins A0 = 0 := by
      omega
    simp [thresholdZero] at fineBaseLeThreshold
    have fineBasePos : 0 < fineBase := by
      simp [fineBase]
    omega
  have countLt :
      fineCount < 4 * A0 ^ 2 * W := by
    apply (Nat.mul_lt_mul_left fineThresholdPos).mp
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      multiplied
  simpa [
    fineCount,
    W,
    balancingRateLoss,
    core.ranges.availableFineCells_card coarseCell
  ] using countLt.le

structure BalancingTailSmallData : Prop where
  tail_sum_lt_one :
    (∑ parent ∈ core.ranges.terminalParents,
        Real.exp
          (-(1 /
              (10 *
                core.balancingRateLoss
                  input multiplicity parentClass treeCleanup
                    exactification parentDegree) : ℝ) *
            exactification.incidence.parentDegree
              core.ranges.terminalEdges parent)) < 1

structure BalancingNumericalSmallData : Prop where
  scalar :
    (core.ranges.terminalParents.card : ℝ) *
        Real.exp
          (-(1 /
              (10 *
                core.balancingRateLoss
                  input multiplicity parentClass treeCleanup
                    exactification parentDegree) : ℝ) *
            input.parentThreshold
              multiplicity parentClass treeCleanup
                exactification parentDegree A0) < 1

theorem terminalParents_card_le_coarse_card :
    core.ranges.terminalParents.card ≤ coarse.card := by
  calc
    core.ranges.terminalParents.card ≤
        (Finset.univ : Finset (Fin coarse.card)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = coarse.card := by simp

structure BalancingAmbientLogSmallData : Prop where
  log_card_lt :
    Real.log (coarse.card : ℝ) <
      (input.parentThreshold
        multiplicity parentClass treeCleanup
          exactification parentDegree A0 : ℝ) /
        (10 *
          core.balancingRateLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree)

theorem balancingAmbientLogSmallData_of_scaled_referenceDegree
    (scaled :
      (40 : ℝ) * (A0 : ℝ) ^ 3 *
          Real.log (coarse.card : ℝ) <
        (parentDegree.K : ℝ)) :
    core.BalancingAmbientLogSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree := by
  have thresholdBound :
      parentDegree.K ≤
        A0 *
          input.parentThreshold
            multiplicity parentClass treeCleanup
              exactification parentDegree A0 := by
    simpa [
      PureWZ2Prop62PacketCellInput.parentThreshold,
      Nat.mul_comm
    ] using
      (le_smul_ceilDiv core.A0_pos :
        parentDegree.K ≤
          A0 * (parentDegree.K ⌈/⌉ A0))
  have thresholdBoundReal :
      (parentDegree.K : ℝ) ≤
        (A0 : ℝ) *
          (input.parentThreshold
            multiplicity parentClass treeCleanup
              exactification parentDegree A0 : ℝ) := by
    exact_mod_cast thresholdBound
  have denominatorPos :
      (0 : ℝ) <
        10 *
          core.balancingRateLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree := by
    have ratePos :
        (0 : ℝ) <
          (core.balancingRateLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree : ℕ) := by
      exact_mod_cast
        core.balancingRateLoss_pos
          input multiplicity parentClass treeCleanup
            exactification parentDegree
    positivity
  constructor
  apply (lt_div_iff₀ denominatorPos).2
  have A0PosReal : (0 : ℝ) < A0 := by
    exact_mod_cast core.A0_pos
  have divided :
      (40 : ℝ) * (A0 : ℝ) ^ 2 *
          Real.log (coarse.card : ℝ) <
        (input.parentThreshold
          multiplicity parentClass treeCleanup
            exactification parentDegree A0 : ℝ) := by
    nlinarith
  calc
    Real.log (coarse.card : ℝ) *
          (10 *
            (core.balancingRateLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree : ℕ)) =
        (40 : ℝ) * (A0 : ℝ) ^ 2 *
          Real.log (coarse.card : ℝ) := by
      simp [
        FourDegreeCoreAssemblyData.balancingRateLoss,
        Nat.cast_mul, Nat.cast_pow
      ]
      ring
    _ <
        (input.parentThreshold
          multiplicity parentClass treeCleanup
            exactification parentDegree A0 : ℝ) :=
      divided

theorem balancingNumericalSmallData_of_ambientLog
    (logSmall : core.BalancingAmbientLogSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree) :
    core.BalancingNumericalSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree := by
  constructor
  let exponent : ℝ :=
    (input.parentThreshold
      multiplicity parentClass treeCleanup
        exactification parentDegree A0 : ℝ) /
      (10 *
        core.balancingRateLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree)
  have coarseCardPosReal : (0 : ℝ) < coarse.card := by
    rcases
        PureWZ2Prop62PacketCellInput.FourDegreeCoreAssemblyData.core_nonempty
          core
      with ⟨edge, edgeMem⟩
    exact_mod_cast
      Nat.zero_lt_of_lt
        (exactification.incidence.edgeParent edge).isLt
  have terminalCardCast :
      (core.ranges.terminalParents.card : ℝ) ≤
        (coarse.card : ℝ) := by
    exact_mod_cast
      core.terminalParents_card_le_coarse_card
        input multiplicity parentClass treeCleanup
          exactification parentDegree
  have tailExponentEq :
      -(1 /
          (10 *
            core.balancingRateLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree) : ℝ) *
          input.parentThreshold
            multiplicity parentClass treeCleanup
              exactification parentDegree A0 =
        -exponent := by
    dsimp only [exponent]
    rw [div_eq_mul_inv]
    ring
  calc
    (core.ranges.terminalParents.card : ℝ) *
          Real.exp
            (-(1 /
                (10 *
                  core.balancingRateLoss
                    input multiplicity parentClass treeCleanup
                      exactification parentDegree) : ℝ) *
              input.parentThreshold
                multiplicity parentClass treeCleanup
                  exactification parentDegree A0) ≤
        (coarse.card : ℝ) * Real.exp (-exponent) := by
      rw [tailExponentEq]
      exact
        mul_le_mul_of_nonneg_right
          terminalCardCast (Real.exp_nonneg _)
    _ = Real.exp (Real.log (coarse.card : ℝ) - exponent) := by
      calc
        (coarse.card : ℝ) * Real.exp (-exponent) =
            Real.exp (Real.log (coarse.card : ℝ)) *
              Real.exp (-exponent) := by
          rw [Real.exp_log coarseCardPosReal]
        _ = Real.exp
              (Real.log (coarse.card : ℝ) + (-exponent)) := by
          rw [Real.exp_add]
        _ = Real.exp
              (Real.log (coarse.card : ℝ) - exponent) := by
          congr 1
    _ < Real.exp 0 := by
      apply Real.exp_lt_exp.mpr
      dsimp only [exponent]
      linarith [logSmall.log_card_lt]
    _ = 1 := by simp

theorem balancingTailSmallData_of_numerical
    (numerical : core.BalancingNumericalSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree) :
    core.BalancingTailSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree := by
  constructor
  calc
    (∑ parent ∈ core.ranges.terminalParents,
        Real.exp
          (-(1 /
              (10 *
                core.balancingRateLoss
                  input multiplicity parentClass treeCleanup
                    exactification parentDegree) : ℝ) *
            exactification.incidence.parentDegree
              core.ranges.terminalEdges parent)) ≤
        ∑ _parent ∈ core.ranges.terminalParents,
          Real.exp
            (-(1 /
                (10 *
                  core.balancingRateLoss
                    input multiplicity parentClass treeCleanup
                      exactification parentDegree) : ℝ) *
              input.parentThreshold
                multiplicity parentClass treeCleanup
                  exactification parentDegree A0) := by
      apply Finset.sum_le_sum
      intro parent parentMem
      apply Real.exp_le_exp.mpr
      have degreePos :=
        core.ranges.terminalParent_degree_pos parentMem
      have thresholdLe :=
        (PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.parent_range
          exactification.incidence core.ranges parent degreePos).1
      have coefficientNonneg :
          0 ≤
            (1 /
              (10 *
                core.balancingRateLoss
                  input multiplicity parentClass treeCleanup
                    exactification parentDegree) : ℝ) := by
        positivity
      have castThreshold :
          (input.parentThreshold
              multiplicity parentClass treeCleanup
                exactification parentDegree A0 : ℝ) ≤
            exactification.incidence.parentDegree
              core.ranges.terminalEdges parent := by
        exact_mod_cast thresholdLe
      nlinarith [mul_le_mul_of_nonneg_left
        castThreshold coefficientNonneg]
    _ =
        (core.ranges.terminalParents.card : ℝ) *
          Real.exp
            (-(1 /
                (10 *
                  core.balancingRateLoss
                    input multiplicity parentClass treeCleanup
                      exactification parentDegree) : ℝ) *
              input.parentThreshold
                multiplicity parentClass treeCleanup
                  exactification parentDegree A0) := by
      simp
    _ < 1 :=
      numerical.scalar

noncomputable def balancingLowerTailCertificate
    (tailSmall : core.BalancingTailSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree) :
    core.ranges.ParentLowerTailCertificate
      (core.balancingDegreeLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree) := by
  unfold balancingDegreeLoss
  exact
    core.ranges.parentLowerTailCertificate_of_exp_sum_lt_one
      (core.balancingRateLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree)
      (core.balancingRateLoss_pos
        input multiplicity parentClass treeCleanup
          exactification parentDegree)
      (core.balancing_selection_rate
        input multiplicity parentClass treeCleanup
          exactification parentDegree)
      tailSmall.tail_sum_lt_one

noncomputable def balancingLowerTailCertificate_of_numerical
    (numerical : core.BalancingNumericalSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree) :
    core.ranges.ParentLowerTailCertificate
      (core.balancingDegreeLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree) :=
  core.balancingLowerTailCertificate
    input multiplicity parentClass treeCleanup
      exactification parentDegree <|
    core.balancingTailSmallData_of_numerical
      input multiplicity parentClass treeCleanup
        exactification parentDegree numerical

theorem exists_canonical_good_balancing_sample
    (tailSmall : core.BalancingTailSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree) :
    Nonempty
      (core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree)) :=
  core.ranges.exists_good_balancing_sample <|
    core.balancingLowerTailCertificate
      input multiplicity parentClass treeCleanup
        exactification parentDegree tailSmall

theorem exists_canonical_good_balancing_sample_of_numerical
    (numerical : core.BalancingNumericalSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree) :
    Nonempty
      (core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree)) :=
  core.ranges.exists_good_balancing_sample <|
    core.balancingLowerTailCertificate_of_numerical
      input multiplicity parentClass treeCleanup
        exactification parentDegree numerical

theorem exists_canonical_good_balancing_sample_of_ambientLog
    (logSmall : core.BalancingAmbientLogSmallData
      input multiplicity parentClass treeCleanup
        exactification parentDegree) :
    Nonempty
      (core.ranges.GoodBalancingSampleData
        (core.balancingDegreeLoss
          input multiplicity parentClass treeCleanup
            exactification parentDegree)) :=
  core.exists_canonical_good_balancing_sample_of_numerical
    input multiplicity parentClass treeCleanup
      exactification parentDegree <|
    core.balancingNumericalSmallData_of_ambientLog
      input multiplicity parentClass treeCleanup
        exactification parentDegree logSmall

end FourDegreeCoreAssemblyData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end

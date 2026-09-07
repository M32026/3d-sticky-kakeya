import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedQuotaConcentration

/-!
# Proposition 6.2: lower tail for the exact-balancing product sample

Each active coarse cell contributes one uniform fixed-cardinality coordinate.
The estimates below multiply the coordinate hypergeometric moment bounds
without imposing independence on the individual fine cells inside one
coordinate.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62FourDegreeIncidenceData
namespace FourDegreeRangeData

variable
    {Parent FineCell CoarseCell : Type*}
    [DecidableEq Parent]
    [DecidableEq FineCell]
    [DecidableEq CoarseCell]
    {data :
      PureWZ2Prop62FourDegreeIncidenceData
        Parent FineCell CoarseCell}
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    {initialEdges : Finset data.Edge}
    {bins : data.ThreeDegreeBinningData initialEdges}
    {parentLower fineLower parentCoarseLower coarseLower : ℕ}
    {treeLabels : Finset TreeLabel}
    {treeBad : Finset data.Edge → TreeLabel → Prop}
    {treeCharge : TreeLabel → ℕ}
    (ranges :
      data.FourDegreeRangeData
        bins parentLower fineLower
        parentCoarseLower coarseLower
        treeLabels treeBad treeCharge)

theorem availableFineCells_card
    (coarseCell : ranges.ActiveCoarseCell) :
    (ranges.availableFineCells coarseCell).card =
      ranges.activeFineCount coarseCell.1 :=
  rfl

theorem availableFineCells_card_pos
    (coarseCell : ranges.ActiveCoarseCell) :
    0 < (ranges.availableFineCells coarseCell).card := by
  rw [ranges.availableFineCells_card coarseCell]
  exact
    (ranges.activeFineCellsAt_nonempty
      (ranges.activeCoarseCell_degree_pos coarseCell)).card_pos

theorem coordinateChoices_card
    (coarseCell : ranges.ActiveCoarseCell) :
    (ranges.coordinateChoices coarseCell).card =
      Nat.choose
        (ranges.availableFineCells coarseCell).card
        ranges.commonFineCellCount := by
  exact Finset.card_powersetCard _ _

theorem coordinateChoiceFintype_card
    (coarseCell : ranges.ActiveCoarseCell) :
    Fintype.card
        {selected : Finset FineCell //
          selected ∈ ranges.coordinateChoices coarseCell} =
      Nat.choose
        (ranges.availableFineCells coarseCell).card
        ranges.commonFineCellCount := by
  rw [Fintype.card_coe]
  exact ranges.coordinateChoices_card coarseCell

theorem balancingSample_card :
    Fintype.card ranges.BalancingSample =
      ∏ coarseCell : ranges.ActiveCoarseCell,
        Nat.choose
          (ranges.availableFineCells coarseCell).card
          ranges.commonFineCellCount := by
  change
    Fintype.card
        (∀ coarseCell : ranges.ActiveCoarseCell,
          {selected : Finset FineCell //
            selected ∈ ranges.coordinateChoices coarseCell}) =
      _
  calc
    Fintype.card
        (∀ coarseCell : ranges.ActiveCoarseCell,
          {selected : Finset FineCell //
            selected ∈ ranges.coordinateChoices coarseCell}) =
        ∏ coarseCell : ranges.ActiveCoarseCell,
          Fintype.card
            {selected : Finset FineCell //
              selected ∈ ranges.coordinateChoices coarseCell} :=
      Fintype.card_pi
    _ =
        ∏ coarseCell : ranges.ActiveCoarseCell,
          Nat.choose
            (ranges.availableFineCells coarseCell).card
            ranges.commonFineCellCount := by
      apply Finset.prod_congr rfl
      intro coarseCell coarseMem
      exact ranges.coordinateChoiceFintype_card coarseCell

theorem coordinate_exp_neg_sum_le
    (parent : Parent)
    (coarseCell : ranges.ActiveCoarseCell) :
    (∑ choice :
        {selected : Finset FineCell //
          selected ∈ ranges.coordinateChoices coarseCell},
        Real.exp
          (-(((choice.1 ∩
            ranges.parentFineCellsAt parent coarseCell).card : ℝ)))) ≤
      (Nat.choose
          (ranges.availableFineCells coarseCell).card
          ranges.commonFineCellCount : ℝ) *
        Real.exp
          (-(3 / 5 : ℝ) *
            ((ranges.commonFineCellCount : ℝ) /
              (ranges.availableFineCells coarseCell).card) *
            (ranges.parentFineCellsAt parent coarseCell).card) := by
  calc
    (∑ choice :
        {selected : Finset FineCell //
          selected ∈ ranges.coordinateChoices coarseCell},
        Real.exp
          (-(((choice.1 ∩
            ranges.parentFineCellsAt parent coarseCell).card : ℝ)))) =
        ∑ selected ∈ ranges.coordinateChoices coarseCell,
          Real.exp
            (-(((selected ∩
              ranges.parentFineCellsAt parent coarseCell).card : ℝ))) := by
      exact
        (Finset.sum_subtype
          (ranges.coordinateChoices coarseCell)
          (fun _ => Iff.rfl)
          (fun selected =>
            Real.exp
              (-(((selected ∩
                ranges.parentFineCellsAt parent coarseCell).card : ℝ))))).symm
    _ ≤
        (Nat.choose
            (ranges.availableFineCells coarseCell).card
            ranges.commonFineCellCount : ℝ) *
          Real.exp
            (-(3 / 5 : ℝ) *
              ((ranges.commonFineCellCount : ℝ) /
                (ranges.availableFineCells coarseCell).card) *
              (ranges.parentFineCellsAt parent coarseCell).card) :=
      fixedQuota_exp_neg_sum_le
        (ranges.availableFineCells coarseCell)
        (ranges.parentFineCellsAt parent coarseCell)
        ranges.commonFineCellCount
        (ranges.parentFineCellsAt_subset_available
          parent coarseCell)
        (ranges.commonFineCellCount_le_activeFineCount
          (ranges.activeCoarseCell_degree_pos coarseCell))
        (ranges.availableFineCells_card_pos coarseCell)

theorem coordinate_exp_neg_sum_le_of_rate
    (parent : Parent)
    (coarseCell : ranges.ActiveCoarseCell)
    (rateLoss : ℕ)
    (rateLoss_pos : 0 < rateLoss)
    (rate :
      (ranges.availableFineCells coarseCell).card ≤
        rateLoss * ranges.commonFineCellCount) :
    (∑ choice :
        {selected : Finset FineCell //
          selected ∈ ranges.coordinateChoices coarseCell},
        Real.exp
          (-(((choice.1 ∩
            ranges.parentFineCellsAt parent coarseCell).card : ℝ)))) ≤
      (Nat.choose
          (ranges.availableFineCells coarseCell).card
          ranges.commonFineCellCount : ℝ) *
        Real.exp
          (-(3 / (5 * rateLoss) : ℝ) *
            (ranges.parentFineCellsAt parent coarseCell).card) := by
  have availablePos :=
    ranges.availableFineCells_card_pos coarseCell
  have ratioLower :
      (1 : ℝ) / rateLoss ≤
        (ranges.commonFineCellCount : ℝ) /
          (ranges.availableFineCells coarseCell).card := by
    rw [div_le_div_iff₀
      (by exact_mod_cast rateLoss_pos)
      (by exact_mod_cast availablePos)]
    norm_num
    exact_mod_cast (by simpa [Nat.mul_comm] using rate)
  have exponentLe :
      -(3 / 5 : ℝ) *
            ((ranges.commonFineCellCount : ℝ) /
              (ranges.availableFineCells coarseCell).card) *
            (ranges.parentFineCellsAt parent coarseCell).card ≤
        -(3 / (5 * rateLoss) : ℝ) *
          (ranges.parentFineCellsAt parent coarseCell).card := by
    have coefficientLower :
        (3 / (5 * rateLoss) : ℝ) ≤
          (3 / 5 : ℝ) *
            ((ranges.commonFineCellCount : ℝ) /
              (ranges.availableFineCells coarseCell).card) := by
      calc
        (3 / (5 * rateLoss) : ℝ) =
            (3 / 5 : ℝ) * ((1 : ℝ) / rateLoss) := by
          field_simp
        _ ≤
            (3 / 5 : ℝ) *
              ((ranges.commonFineCellCount : ℝ) /
                (ranges.availableFineCells coarseCell).card) := by
          gcongr
    have markedNonneg :
        0 ≤
          ((ranges.parentFineCellsAt
            parent coarseCell).card : ℝ) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_right
      coefficientLower markedNonneg]
  calc
    (∑ choice :
        {selected : Finset FineCell //
          selected ∈ ranges.coordinateChoices coarseCell},
        Real.exp
          (-(((choice.1 ∩
            ranges.parentFineCellsAt parent coarseCell).card : ℝ)))) ≤
        (Nat.choose
            (ranges.availableFineCells coarseCell).card
            ranges.commonFineCellCount : ℝ) *
          Real.exp
            (-(3 / 5 : ℝ) *
              ((ranges.commonFineCellCount : ℝ) /
                (ranges.availableFineCells coarseCell).card) *
              (ranges.parentFineCellsAt parent coarseCell).card) :=
      ranges.coordinate_exp_neg_sum_le parent coarseCell
    _ ≤
        (Nat.choose
            (ranges.availableFineCells coarseCell).card
            ranges.commonFineCellCount : ℝ) *
          Real.exp
            (-(3 / (5 * rateLoss) : ℝ) *
              (ranges.parentFineCellsAt parent coarseCell).card) := by
      gcongr

theorem parent_exp_neg_sum_eq_prod
    (parent : Parent) :
    (∑ sample : ranges.BalancingSample,
        Real.exp
          (-(ranges.selectedParentDegree sample parent : ℝ))) =
      ∏ coarseCell : ranges.ActiveCoarseCell,
        ∑ choice :
            {selected : Finset FineCell //
              selected ∈ ranges.coordinateChoices coarseCell},
          Real.exp
            (-(((choice.1 ∩
              ranges.parentFineCellsAt parent coarseCell).card : ℝ))) := by
  calc
    (∑ sample : ranges.BalancingSample,
        Real.exp
          (-(ranges.selectedParentDegree sample parent : ℝ))) =
        ∑ sample : ranges.BalancingSample,
          ∏ coarseCell : ranges.ActiveCoarseCell,
            Real.exp
              (-((((sample coarseCell).1 ∩
                ranges.parentFineCellsAt parent coarseCell).card : ℝ))) := by
      apply Finset.sum_congr rfl
      intro sample sampleMem
      rw [selectedParentDegree,
        ranges.selectedParentDegree_eq_sum_inter sample parent,
        ← Real.exp_sum]
      congr 1
      push_cast
      rw [Finset.sum_neg_distrib]
    _ =
        ∏ coarseCell : ranges.ActiveCoarseCell,
          ∑ choice :
              {selected : Finset FineCell //
                selected ∈ ranges.coordinateChoices coarseCell},
            Real.exp
              (-(((choice.1 ∩
                ranges.parentFineCellsAt parent coarseCell).card : ℝ))) := by
      exact
        (Fintype.prod_sum fun
          coarseCell
          (choice :
            {selected : Finset FineCell //
              selected ∈ ranges.coordinateChoices coarseCell}) =>
            Real.exp
              (-(((choice.1 ∩
                ranges.parentFineCellsAt parent coarseCell).card : ℝ)))).symm

theorem parent_exp_neg_sum_le
    (parent : Parent)
    (rateLoss : ℕ)
    (rateLoss_pos : 0 < rateLoss)
    (rate :
      ∀ coarseCell : ranges.ActiveCoarseCell,
        (ranges.availableFineCells coarseCell).card ≤
          rateLoss * ranges.commonFineCellCount) :
    (∑ sample : ranges.BalancingSample,
        Real.exp
          (-(ranges.selectedParentDegree sample parent : ℝ))) ≤
      (Fintype.card ranges.BalancingSample : ℝ) *
        Real.exp
          (-(3 / (5 * rateLoss) : ℝ) *
            data.parentDegree ranges.terminalEdges parent) := by
  rw [ranges.parent_exp_neg_sum_eq_prod parent]
  calc
    (∏ coarseCell : ranges.ActiveCoarseCell,
        ∑ choice :
            {selected : Finset FineCell //
              selected ∈ ranges.coordinateChoices coarseCell},
          Real.exp
            (-(((choice.1 ∩
              ranges.parentFineCellsAt parent coarseCell).card : ℝ)))) ≤
        ∏ coarseCell : ranges.ActiveCoarseCell,
          ((Nat.choose
              (ranges.availableFineCells coarseCell).card
              ranges.commonFineCellCount : ℝ) *
            Real.exp
              (-(3 / (5 * rateLoss) : ℝ) *
                (ranges.parentFineCellsAt
                  parent coarseCell).card)) := by
      apply Finset.prod_le_prod
      · intro coarseCell coarseMem
        positivity
      · intro coarseCell coarseMem
        exact
          ranges.coordinate_exp_neg_sum_le_of_rate
            parent coarseCell rateLoss rateLoss_pos
              (rate coarseCell)
    _ =
        (∏ coarseCell : ranges.ActiveCoarseCell,
            (Nat.choose
              (ranges.availableFineCells coarseCell).card
              ranges.commonFineCellCount : ℝ)) *
          ∏ coarseCell : ranges.ActiveCoarseCell,
            Real.exp
              (-(3 / (5 * rateLoss) : ℝ) *
                (ranges.parentFineCellsAt
                  parent coarseCell).card) := by
      rw [Finset.prod_mul_distrib]
    _ =
        (Fintype.card ranges.BalancingSample : ℝ) *
          Real.exp
            (-(3 / (5 * rateLoss) : ℝ) *
              data.parentDegree ranges.terminalEdges parent) := by
      congr 1
      · norm_cast
        exact ranges.balancingSample_card.symm
      · rw [← Real.exp_sum,
          ranges.parentDegree_eq_sum_parentFineCellsAt parent]
        congr 1
        push_cast
        rw [Finset.mul_sum]

theorem parentBadSamples_card_real_le
    (parent : Parent)
    (rateLoss : ℕ)
    (rateLoss_pos : 0 < rateLoss)
    (rate :
      ∀ coarseCell : ranges.ActiveCoarseCell,
        (ranges.availableFineCells coarseCell).card ≤
          rateLoss * ranges.commonFineCellCount) :
    ((ranges.parentBadSamples (2 * rateLoss) parent).card : ℝ) ≤
      (Fintype.card ranges.BalancingSample : ℝ) *
        Real.exp
          (-(1 / (10 * rateLoss) : ℝ) *
            data.parentDegree ranges.terminalEdges parent) := by
  let threshold : ℝ :=
    (data.parentDegree ranges.terminalEdges parent : ℝ) /
      (2 * rateLoss)
  have thresholdExpPos :
      0 < Real.exp (-threshold) :=
    Real.exp_pos _
  have badTermLower :
      ∀ sample ∈ ranges.parentBadSamples (2 * rateLoss) parent,
        Real.exp (-threshold) ≤
          Real.exp
            (-(ranges.selectedParentDegree sample parent : ℝ)) := by
    intro sample sampleBad
    have badNat :
        (2 * rateLoss) *
              ranges.selectedParentDegree sample parent <
            data.parentDegree ranges.terminalEdges parent :=
      (ranges.mem_parentBadSamples_iff
        (2 * rateLoss) parent sample).mp sampleBad
    have badReal :
        ((2 * rateLoss : ℕ) : ℝ) *
              ranges.selectedParentDegree sample parent <
            data.parentDegree ranges.terminalEdges parent := by
      exact_mod_cast badNat
    have denominatorPos :
        (0 : ℝ) < (2 * rateLoss : ℕ) := by
      positivity
    have selectedLt :
        (ranges.selectedParentDegree sample parent : ℝ) <
          threshold := by
      rw [show threshold =
          (data.parentDegree ranges.terminalEdges parent : ℝ) /
            ((2 * rateLoss : ℕ) : ℝ) by
              simp [threshold]]
      exact (lt_div_iff₀ denominatorPos).2 (by
        simpa [mul_comm] using badReal)
    exact Real.exp_le_exp.mpr (by linarith)
  have badWeightedLower :
      ((ranges.parentBadSamples
          (2 * rateLoss) parent).card : ℝ) *
            Real.exp (-threshold) ≤
        ∑ sample ∈
            ranges.parentBadSamples (2 * rateLoss) parent,
          Real.exp
            (-(ranges.selectedParentDegree sample parent : ℝ)) := by
    calc
      ((ranges.parentBadSamples
          (2 * rateLoss) parent).card : ℝ) *
            Real.exp (-threshold) =
          ∑ _sample ∈
              ranges.parentBadSamples (2 * rateLoss) parent,
            Real.exp (-threshold) := by
        simp
      _ ≤
          ∑ sample ∈
              ranges.parentBadSamples (2 * rateLoss) parent,
            Real.exp
              (-(ranges.selectedParentDegree sample parent : ℝ)) :=
        Finset.sum_le_sum badTermLower
  have badWeightedUpper :
      ((ranges.parentBadSamples
          (2 * rateLoss) parent).card : ℝ) *
            Real.exp (-threshold) ≤
        (Fintype.card ranges.BalancingSample : ℝ) *
          Real.exp
            (-(3 / (5 * rateLoss) : ℝ) *
              data.parentDegree ranges.terminalEdges parent) := by
    calc
      ((ranges.parentBadSamples
          (2 * rateLoss) parent).card : ℝ) *
            Real.exp (-threshold) ≤
          ∑ sample ∈
              ranges.parentBadSamples (2 * rateLoss) parent,
            Real.exp
              (-(ranges.selectedParentDegree sample parent : ℝ)) :=
        badWeightedLower
      _ ≤
          ∑ sample : ranges.BalancingSample,
            Real.exp
              (-(ranges.selectedParentDegree sample parent : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ _
        · intro _ _ _
          positivity
      _ ≤
          (Fintype.card ranges.BalancingSample : ℝ) *
            Real.exp
              (-(3 / (5 * rateLoss) : ℝ) *
                data.parentDegree ranges.terminalEdges parent) :=
        ranges.parent_exp_neg_sum_le
          parent rateLoss rateLoss_pos rate
  calc
    ((ranges.parentBadSamples
        (2 * rateLoss) parent).card : ℝ) ≤
        ((Fintype.card ranges.BalancingSample : ℝ) *
            Real.exp
              (-(3 / (5 * rateLoss) : ℝ) *
                data.parentDegree ranges.terminalEdges parent)) /
          Real.exp (-threshold) := by
      exact
        (le_div_iff₀ thresholdExpPos).2
          badWeightedUpper
    _ =
        (Fintype.card ranges.BalancingSample : ℝ) *
          Real.exp
            (-(1 / (10 * rateLoss) : ℝ) *
              data.parentDegree ranges.terminalEdges parent) := by
      have expRatio :
          Real.exp
                (-(3 / (5 * rateLoss) : ℝ) *
                  data.parentDegree ranges.terminalEdges parent) /
              Real.exp (-threshold) =
            Real.exp
              (-(1 / (10 * rateLoss) : ℝ) *
                data.parentDegree ranges.terminalEdges parent) := by
        rw [div_eq_mul_inv, ← Real.exp_neg,
          ← Real.exp_add]
        congr 1
        dsimp only [threshold]
        have rateLossNe :
            (rateLoss : ℝ) ≠ 0 := by
          exact_mod_cast rateLoss_pos.ne'
        field_simp [rateLossNe]
        ring
      rw [mul_div_assoc, expRatio]

noncomputable def parentLowerTailCertificate_of_exp_sum_lt_one
    (rateLoss : ℕ)
    (rateLoss_pos : 0 < rateLoss)
    (rate :
      ∀ coarseCell : ranges.ActiveCoarseCell,
        (ranges.availableFineCells coarseCell).card ≤
          rateLoss * ranges.commonFineCellCount)
    (tailSum :
      (∑ parent ∈ ranges.terminalParents,
          Real.exp
            (-(1 / (10 * rateLoss) : ℝ) *
              data.parentDegree
                ranges.terminalEdges parent)) < 1) :
    ranges.ParentLowerTailCertificate (2 * rateLoss) := by
  let sampleCount : ℕ :=
    Fintype.card ranges.BalancingSample
  have sampleCountPos : 0 < sampleCount := by
    dsimp only [sampleCount]
    exact
      Fintype.card_pos_iff.mpr
        ranges.balancingSample_nonempty
  have summedBadReal :
      ((∑ parent ∈ ranges.terminalParents,
          (ranges.parentBadSamples
            (2 * rateLoss) parent).card : ℕ) : ℝ) ≤
        (sampleCount : ℝ) *
          ∑ parent ∈ ranges.terminalParents,
            Real.exp
              (-(1 / (10 * rateLoss) : ℝ) *
                data.parentDegree
                  ranges.terminalEdges parent) := by
    push_cast
    rw [Finset.mul_sum]
    exact
      Finset.sum_le_sum fun parent parentMem =>
        ranges.parentBadSamples_card_real_le
          parent rateLoss rateLoss_pos rate
  have summedBadLt :
      (∑ parent ∈ ranges.terminalParents,
          (ranges.parentBadSamples
            (2 * rateLoss) parent).card) <
        sampleCount := by
    have sampleCountRealPos :
        (0 : ℝ) < sampleCount := by
      exact_mod_cast sampleCountPos
    have strictReal :
        ((∑ parent ∈ ranges.terminalParents,
            (ranges.parentBadSamples
              (2 * rateLoss) parent).card : ℕ) : ℝ) <
          (sampleCount : ℝ) := by
      calc
        ((∑ parent ∈ ranges.terminalParents,
            (ranges.parentBadSamples
              (2 * rateLoss) parent).card : ℕ) : ℝ) ≤
            (sampleCount : ℝ) *
              ∑ parent ∈ ranges.terminalParents,
                Real.exp
                  (-(1 / (10 * rateLoss) : ℝ) *
                    data.parentDegree
                      ranges.terminalEdges parent) :=
          summedBadReal
        _ < (sampleCount : ℝ) * 1 := by
          exact
            mul_lt_mul_of_pos_left
              tailSum sampleCountRealPos
        _ = sampleCount := by ring
    exact_mod_cast strictReal
  exact
    {
      failureBudget := fun parent =>
        (ranges.parentBadSamples
          (2 * rateLoss) parent).card
      bad_card_le := by
        intro parent parentMem
        exact le_rfl
      total_failure_lt := by
        simpa [sampleCount] using summedBadLt
    }

end FourDegreeRangeData
end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end

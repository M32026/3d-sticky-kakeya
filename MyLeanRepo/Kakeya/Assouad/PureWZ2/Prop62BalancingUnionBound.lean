import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ExactBalancingSample

/-!
# Proposition 6.2: finite union bound for the exact-balancing sample

The sample space is already the product of uniform fixed-cardinality choices.
This module is purely finite and measure-free:

* define the selected degree of each parent;
* define its lower-tail bad-event;
* assume a cardinality bound for each bad-event;
* use a finite union bound to choose one sample outside all bad-events.

The only missing probabilistic leaf is therefore the per-parent cardinality
bound for uniform fixed-size sampling.  No Bernoulli replacement and no
post-balancing tube-family selection are introduced.
-/

noncomputable section

namespace Kakeya.Assouad

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

def selectedParentDegree
    (sample : ranges.BalancingSample)
    (parent : Parent) : ℕ :=
  data.parentDegree (ranges.selectedEdges sample) parent

def terminalParents : Finset Parent :=
  data.activeParents ranges.terminalEdges

theorem terminalParent_degree_pos
    {parent : Parent}
    (parentMem : parent ∈ ranges.terminalParents) :
    0 < data.parentDegree ranges.terminalEdges parent := by
  exact
    (data.mem_activeParents_iff
      ranges.terminalEdges parent).mp parentMem

/-- A sample is bad for `parent` if it retains less than
`1 / degreeLoss` of the terminal parent degree. -/
def parentBadSamples
    (degreeLoss : ℕ)
    (parent : Parent) :
    Finset ranges.BalancingSample :=
  Finset.univ.filter fun sample =>
    degreeLoss * ranges.selectedParentDegree sample parent <
      data.parentDegree ranges.terminalEdges parent

@[simp]
theorem mem_parentBadSamples_iff
    (degreeLoss : ℕ)
    (parent : Parent)
    (sample : ranges.BalancingSample) :
    sample ∈ ranges.parentBadSamples degreeLoss parent ↔
      degreeLoss * ranges.selectedParentDegree sample parent <
        data.parentDegree ranges.terminalEdges parent := by
  simp [parentBadSamples]

structure ParentLowerTailCertificate
    (degreeLoss : ℕ) where
  failureBudget : Parent → ℕ
  bad_card_le :
    ∀ parent ∈ ranges.terminalParents,
      (ranges.parentBadSamples degreeLoss parent).card ≤
        failureBudget parent
  total_failure_lt :
    (∑ parent ∈ ranges.terminalParents,
        failureBudget parent) <
      Fintype.card ranges.BalancingSample

/-- The union of all parent lower-tail bad-events. -/
def allBadSamples
    (degreeLoss : ℕ) :
    Finset ranges.BalancingSample :=
  ranges.terminalParents.biUnion fun parent =>
    ranges.parentBadSamples degreeLoss parent

theorem allBadSamples_card_le_sum
    (degreeLoss : ℕ) :
    (ranges.allBadSamples degreeLoss).card ≤
      ∑ parent ∈ ranges.terminalParents,
        (ranges.parentBadSamples degreeLoss parent).card := by
  exact Finset.card_biUnion_le

theorem allBadSamples_card_lt_univ
    {degreeLoss : ℕ}
    (certificate :
      ranges.ParentLowerTailCertificate degreeLoss) :
    (ranges.allBadSamples degreeLoss).card <
      (Finset.univ : Finset ranges.BalancingSample).card := by
  calc
    (ranges.allBadSamples degreeLoss).card ≤
        ∑ parent ∈ ranges.terminalParents,
          (ranges.parentBadSamples degreeLoss parent).card :=
      ranges.allBadSamples_card_le_sum degreeLoss
    _ ≤
        ∑ parent ∈ ranges.terminalParents,
          certificate.failureBudget parent := by
      exact Finset.sum_le_sum fun parent parentMem =>
        certificate.bad_card_le parent parentMem
    _ <
        Fintype.card ranges.BalancingSample :=
      certificate.total_failure_lt
    _ =
        (Finset.univ : Finset ranges.BalancingSample).card := by
      simp

structure GoodBalancingSampleData
    (degreeLoss : ℕ) where
  sample : ranges.BalancingSample
  parent_degree_retention :
    ∀ parent ∈ ranges.terminalParents,
      data.parentDegree ranges.terminalEdges parent ≤
        degreeLoss * ranges.selectedParentDegree sample parent
  selectedEdges_subset :
    ranges.selectedEdges sample ⊆ ranges.terminalEdges
  exact_fine_cell_count :
    ∀ coarseCell : ranges.ActiveCoarseCell,
      (ranges.selectedFineCellsAt sample coarseCell.1).card =
        ranges.commonFineCellCount

theorem exists_good_balancing_sample
    {degreeLoss : ℕ}
    (certificate :
      ranges.ParentLowerTailCertificate degreeLoss) :
    Nonempty (ranges.GoodBalancingSampleData degreeLoss) := by
  have badCardLt :=
    ranges.allBadSamples_card_lt_univ certificate
  have notSubset :
      ¬(Finset.univ : Finset ranges.BalancingSample) ⊆
        ranges.allBadSamples degreeLoss := by
    intro subset
    have cardLe := Finset.card_le_card subset
    omega
  rcases Finset.not_subset.mp notSubset with
    ⟨sample, _sampleUniv, sampleNotBad⟩
  have sampleGood :
      ∀ parent ∈ ranges.terminalParents,
        data.parentDegree ranges.terminalEdges parent ≤
          degreeLoss *
            ranges.selectedParentDegree sample parent := by
    intro parent parentMem
    by_contra notRetained
    have strict :
        degreeLoss *
            ranges.selectedParentDegree sample parent <
          data.parentDegree ranges.terminalEdges parent := by
      omega
    have sampleParentBad :
        sample ∈ ranges.parentBadSamples degreeLoss parent :=
      (ranges.mem_parentBadSamples_iff
        degreeLoss parent sample).mpr strict
    have sampleAllBad :
        sample ∈ ranges.allBadSamples degreeLoss :=
      Finset.mem_biUnion.mpr
        ⟨parent, parentMem, sampleParentBad⟩
    exact sampleNotBad sampleAllBad
  exact
    ⟨{
      sample := sample
      parent_degree_retention := sampleGood
      selectedEdges_subset :=
        ranges.selectedEdges_subset sample
      exact_fine_cell_count :=
        ranges.selectedFineCellsAt_card sample
    }⟩

end FourDegreeRangeData
end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ParentClassSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CleanupReceipt
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62IndependentPureSchedule

/-!
# Proposition 6.2: weighted cleanup of the metric-parent tree

The tree in this module is a finite pure schedule on the metric parent
family itself.  It is not the earlier fine-tube schedule used to construct
those metric parents.

The selected parent cardinality class has incidence weights in one dyadic
band.  Applying the existing one-pass tree core therefore retains a fixed
fraction of the parent weight and records the locally dense reference
subtree used by the later simultaneous four-degree peeling.
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
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow)

structure ParentTreeCleanupData where
  referenceParents : Finset (Fin coarse.card)
  referenceParents_nonempty : referenceParents.Nonempty
  referenceParents_subset :
    referenceParents ⊆ parentClass.selectedParents
  weight_retention :
    (∑ parent ∈ parentClass.selectedParents,
        (input.parentIncidenceWeight multiplicity parent : ENNReal)) ≤
      (2 ^ (schedule.levelCount + 1) : ENNReal) *
        ∑ parent ∈ referenceParents,
          (input.parentIncidenceWeight multiplicity parent : ENNReal)
  node_density :
    ∀ level, level ≤ schedule.levelCount →
      ∀ node : Finset (Fin coarse.card),
        (referenceParents ∩
          schedule.tree.fiber level node).Nonempty →
          parentClass.selectedParents.card *
              (schedule.tree.fiber level node).card ≤
            2 ^ schedule.levelCount *
              (referenceParents ∩
                schedule.tree.fiber level node).card *
              coarse.card
  reference_weight_band :
    ∀ parent ∈ referenceParents,
      parentClass.weightFloor ≤
          input.parentIncidenceWeight multiplicity parent ∧
        input.parentIncidenceWeight multiplicity parent <
          2 * parentClass.weightFloor
  reference_fiber_card_band :
    ∀ parent ∈ referenceParents,
      parentClass.fiberFloor ≤ input.parentFiberCard parent ∧
        input.parentFiberCard parent <
          2 * parentClass.fiberFloor

namespace ParentTreeCleanupData

variable
    (cleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)

def referenceCount
    (level : ℕ)
    (node : Finset (Fin coarse.card)) : ℕ :=
  (cleanup.referenceParents ∩
    schedule.tree.fiber level node).card

def selectedCount
    (level : ℕ)
    (node : Finset (Fin coarse.card)) : ℕ :=
  (parentClass.selectedParents ∩
    schedule.tree.fiber level node).card

theorem referenceCount_le_selectedCount
    (level : ℕ)
    (node : Finset (Fin coarse.card)) :
    ParentTreeCleanupData.referenceCount
        input multiplicity parentClass schedule cleanup
        level node ≤
      ParentTreeCleanupData.selectedCount
        input multiplicity parentClass schedule
        level node := by
  apply Finset.card_le_card
  exact Finset.inter_subset_inter cleanup.referenceParents_subset
    Finset.Subset.rfl

theorem referenceCount_pos_iff
    (level : ℕ)
    (node : Finset (Fin coarse.card)) :
    0 <
        ParentTreeCleanupData.referenceCount
          input multiplicity parentClass schedule cleanup
          level node ↔
      (cleanup.referenceParents ∩
        schedule.tree.fiber level node).Nonempty := by
  exact Finset.card_pos

theorem local_reference_fraction
    {level : ℕ}
    (level_le : level ≤ schedule.levelCount)
    (node : Finset (Fin coarse.card))
    (reference_pos :
      0 <
        ParentTreeCleanupData.referenceCount
          input multiplicity parentClass schedule cleanup
          level node) :
    parentClass.selectedParents.card *
        (schedule.tree.fiber level node).card ≤
      2 ^ schedule.levelCount *
        ParentTreeCleanupData.referenceCount
          input multiplicity parentClass schedule cleanup
          level node *
        coarse.card := by
  exact
    (ParentTreeCleanupData.node_density cleanup)
      level level_le node <|
    (ParentTreeCleanupData.referenceCount_pos_iff
      input multiplicity parentClass schedule cleanup
      level node).mp reference_pos

theorem reference_parent_weight_pos
    {parent : Fin coarse.card}
    (parentMem : parent ∈ cleanup.referenceParents) :
    0 < input.parentIncidenceWeight multiplicity parent := by
  exact
    ParentClassData.selectedParent_weight_pos
      input multiplicity parentClass
      (cleanup.referenceParents_subset parentMem)

theorem reference_parent_has_selected_pair
    {parent : Fin coarse.card}
    (parentMem : parent ∈ cleanup.referenceParents) :
    (input.selectedPairsAt multiplicity parent).Nonempty := by
  apply input.selectedPairsAt_nonempty multiplicity
  exact
    parentClass.weightClass_subset <|
      parentClass.selectedParents_subset <|
        cleanup.referenceParents_subset parentMem

end ParentTreeCleanupData

theorem pureWZ2_prop62_parent_tree_cleanup :
    Nonempty
      (input.ParentTreeCleanupData
        multiplicity parentClass schedule) := by
  let receipt :=
    pureWZ2Prop62CleanupReceipt
      schedule.tree parentClass.selectedParents
  have referenceNonempty : receipt.core.Nonempty := by
    apply Finset.card_pos.mp
    by_contra coreCardNotPos
    have coreCardZero : receipt.core.card = 0 :=
      Nat.eq_zero_of_not_pos coreCardNotPos
    have selectedCardPos :
        0 < parentClass.selectedParents.card :=
      Finset.card_pos.mpr parentClass.selectedParents_nonempty
    have globalRetention := receipt.global_retention
    rw [coreCardZero] at globalRetention
    simp only [mul_zero] at globalRetention
    omega
  let parentWeight : Fin coarse.card → ENNReal :=
    fun parent =>
      input.parentIncidenceWeight multiplicity parent
  have weightRetention :
      (∑ parent ∈ parentClass.selectedParents,
          parentWeight parent) ≤
        (2 ^ (schedule.levelCount + 1) : ENNReal) *
          ∑ parent ∈ receipt.core,
            parentWeight parent := by
    exact
      receipt.weighted_retention parentWeight
        (parentClass.weightFloor : ENNReal)
        (fun parent parentMem => by
          change
            (parentClass.weightFloor : ENNReal) ≤
              (input.parentIncidenceWeight
                multiplicity parent : ENNReal)
          exact_mod_cast
            (parentClass.weight_band parent
              (parentClass.selectedParents_subset parentMem)).1)
        (fun parent parentMem => by
          have upper :=
            (parentClass.weight_band parent
              (parentClass.selectedParents_subset parentMem)).2.le
          change
            (input.parentIncidenceWeight
                multiplicity parent : ENNReal) ≤
              2 * (parentClass.weightFloor : ENNReal)
          exact_mod_cast upper)
  exact
    ⟨{
      referenceParents := receipt.core
      referenceParents_nonempty := referenceNonempty
      referenceParents_subset := receipt.core_subset
      weight_retention := weightRetention
      node_density := by
        intro level levelLe node nodeNonempty
        simpa only [Fintype.card_fin] using
          receipt.node_density level levelLe node nodeNonempty
      reference_weight_band := by
        intro parent parentMem
        exact
          parentClass.weight_band parent <|
            parentClass.selectedParents_subset <|
              receipt.core_subset parentMem
      reference_fiber_card_band := by
        intro parent parentMem
        exact
          parentClass.fiber_card_band parent <|
            receipt.core_subset parentMem
    }⟩

/--
Build the parent-tree cleanup package from one externally supplied cleanup
receipt.  This is the route used by the paper-audit targets: the receipt is
obtained from the preceding one-pass cleanup lemma rather than recomputed.
-/
theorem pureWZ2_prop62_parent_tree_cleanup_of_receipt
    (receipt :
      PureWZ2Prop62CleanupReceipt
        schedule.tree parentClass.selectedParents) :
    Nonempty
      (input.ParentTreeCleanupData
        multiplicity parentClass schedule) := by
  have referenceNonempty : receipt.core.Nonempty := by
    apply Finset.card_pos.mp
    by_contra coreCardNotPos
    have coreCardZero : receipt.core.card = 0 :=
      Nat.eq_zero_of_not_pos coreCardNotPos
    have selectedCardPos :
        0 < parentClass.selectedParents.card :=
      Finset.card_pos.mpr parentClass.selectedParents_nonempty
    have globalRetention := receipt.global_retention
    rw [coreCardZero] at globalRetention
    simp only [mul_zero] at globalRetention
    omega
  exact
    ⟨{
      referenceParents := receipt.core
      referenceParents_nonempty := referenceNonempty
      referenceParents_subset := receipt.core_subset
      weight_retention := by
        exact
          receipt.weighted_retention
            (fun parent =>
              (input.parentIncidenceWeight multiplicity parent : ENNReal))
            (parentClass.weightFloor : ENNReal)
            (fun parent parentMem => by
              exact_mod_cast
                (parentClass.weight_band parent
                  (parentClass.selectedParents_subset parentMem)).1)
            (fun parent parentMem => by
              exact_mod_cast
                (parentClass.weight_band parent
                  (parentClass.selectedParents_subset parentMem)).2.le)
      node_density := by
        intro level levelLe node nodeNonempty
        simpa only [Fintype.card_fin] using
          receipt.node_density level levelLe node nodeNonempty
      reference_weight_band := by
        intro parent parentMem
        exact
          parentClass.weight_band parent <|
            parentClass.selectedParents_subset <|
              receipt.core_subset parentMem
      reference_fiber_card_band := by
        intro parent parentMem
        exact
          parentClass.fiber_card_band parent <|
            receipt.core_subset parentMem
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end

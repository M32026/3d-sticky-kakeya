import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreRestriction

/-!
# Proposition 6.2 metric parents: one auxiliary laminar level

The metric-parent proof inserts one auxiliary partition between two adjacent
levels of the old pure schedule.  The auxiliary mesh/ancestry classes refine
the old level above them, while the old level below them refines the
auxiliary classes.  The resulting augmented tree is pruned exactly once.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62AuxiliaryLevel
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)
    (Aux : Type)
    [Fintype Aux] [DecidableEq Aux] where
  insertionLevel : ℕ
  insertion_lt : insertionLevel < schedule.levelCount
  label : Fin fine.card → Aux
  label_refines_previous :
    ∀ first second,
      label first = label second →
        schedule.nodeAt insertionLevel first =
          schedule.nodeAt insertionLevel second
  next_refines_label :
    ∀ first second,
      schedule.nodeAt (insertionLevel + 1) first =
          schedule.nodeAt (insertionLevel + 1) second →
        label first = label second

namespace PureWZ2Prop62AuxiliaryLevel

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel schedule Aux)

def liftLevel (oldLevel : ℕ) : ℕ :=
  if oldLevel ≤ auxiliary.insertionLevel then
    oldLevel
  else
    oldLevel + 1

def nodeAt (level : ℕ) (leaf : Fin fine.card) :
    Finset (Fin fine.card) :=
  if level ≤ auxiliary.insertionLevel then
    schedule.nodeAt level leaf
  else if level = auxiliary.insertionLevel + 1 then
    Finset.univ.filter fun source =>
      auxiliary.label source = auxiliary.label leaf
  else
    schedule.nodeAt (level - 1) leaf

@[simp] theorem nodeAt_coarse
    {level : ℕ}
    (hlevel : level ≤ auxiliary.insertionLevel)
    (leaf : Fin fine.card) :
    auxiliary.nodeAt level leaf =
      schedule.nodeAt level leaf := by
  simp [nodeAt, hlevel]

theorem nodeAt_aux
    (leaf : Fin fine.card) :
    auxiliary.nodeAt (auxiliary.insertionLevel + 1) leaf =
      Finset.univ.filter fun source =>
        auxiliary.label source = auxiliary.label leaf := by
  simp [nodeAt]

theorem nodeAt_fine
    {level : ℕ}
    (hlevel : auxiliary.insertionLevel + 1 < level)
    (leaf : Fin fine.card) :
    auxiliary.nodeAt level leaf =
      schedule.nodeAt (level - 1) leaf := by
  simp [nodeAt,
    show ¬level ≤ auxiliary.insertionLevel by omega,
    show level ≠ auxiliary.insertionLevel + 1 by omega]

theorem nodeAt_liftLevel
    {oldLevel : ℕ}
    (holdLevel : oldLevel ≤ schedule.levelCount)
    (leaf : Fin fine.card) :
    auxiliary.nodeAt (auxiliary.liftLevel oldLevel) leaf =
      schedule.nodeAt oldLevel leaf := by
  by_cases hcoarse : oldLevel ≤ auxiliary.insertionLevel
  · rw [show auxiliary.liftLevel oldLevel = oldLevel by
      simp [liftLevel, hcoarse]]
    exact auxiliary.nodeAt_coarse hcoarse leaf
  · have hfine :
        auxiliary.insertionLevel + 1 < oldLevel + 1 := by
      omega
    rw [show auxiliary.liftLevel oldLevel = oldLevel + 1 by
      simp [liftLevel, hcoarse]]
    rw [auxiliary.nodeAt_fine hfine]
    simp

def tree :
    PureWZ2Prop62FiniteTree
      (Fin fine.card) (Finset (Fin fine.card))
      (schedule.levelCount + 1) where
  nodeAt := auxiliary.nodeAt
  root_constant first second := by
    rw [auxiliary.nodeAt_coarse (Nat.zero_le _),
      auxiliary.nodeAt_coarse (Nat.zero_le _)]
    exact schedule.tree.root_constant first second
  nested level hlevel first second heq := by
    by_cases hbefore : level < auxiliary.insertionLevel
    · rw [auxiliary.nodeAt_coarse (by omega),
        auxiliary.nodeAt_coarse (by omega)] at heq
      rw [auxiliary.nodeAt_coarse (by omega),
        auxiliary.nodeAt_coarse (by omega)]
      exact
        schedule.tree.nested level
          (hbefore.trans auxiliary.insertion_lt)
          first second heq
    · by_cases hat : level = auxiliary.insertionLevel
      · subst level
        have hfirstMem :
            first ∈
              auxiliary.nodeAt
                (auxiliary.insertionLevel + 1) first := by
          rw [auxiliary.nodeAt_aux]
          simp
        rw [heq] at hfirstMem
        have hlabel :
            auxiliary.label first = auxiliary.label second := by
          simpa only [auxiliary.nodeAt_aux,
            Finset.mem_filter, Finset.mem_univ, true_and] using
              hfirstMem
        rw [auxiliary.nodeAt_coarse le_rfl,
          auxiliary.nodeAt_coarse le_rfl]
        exact auxiliary.label_refines_previous first second hlabel
      · by_cases htransition :
          level = auxiliary.insertionLevel + 1
        · subst level
          have hnext :
              auxiliary.insertionLevel + 1 <
                auxiliary.insertionLevel + 2 := by
            omega
          rw [auxiliary.nodeAt_fine hnext,
            auxiliary.nodeAt_fine hnext] at heq
          have hlabel :=
            auxiliary.next_refines_label first second heq
          rw [auxiliary.nodeAt_aux, auxiliary.nodeAt_aux]
          ext source
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hlabel]
        · have hafter :
              auxiliary.insertionLevel + 1 < level := by
            omega
          have hafterNext :
              auxiliary.insertionLevel + 1 < level + 1 := by
            omega
          rw [auxiliary.nodeAt_fine hafterNext,
            auxiliary.nodeAt_fine hafterNext] at heq
          rw [auxiliary.nodeAt_fine hafter,
            auxiliary.nodeAt_fine hafter]
          have hpred : level - 1 < schedule.levelCount := by
            omega
          have hsucc : level - 1 + 1 = level := by
            omega
          exact
            schedule.tree.nested (level - 1) hpred
              first second <| by
                change
                  schedule.nodeAt level first =
                    schedule.nodeAt level second at heq
                change
                  schedule.nodeAt (level - 1 + 1) first =
                    schedule.nodeAt (level - 1 + 1) second
                rw [hsucc]
                exact heq

def auxiliaryFiber (label : Aux) : Finset (Fin fine.card) :=
  Finset.univ.filter fun leaf => auxiliary.label leaf = label

theorem tree_fiber_aux_eq
    (leaf : Fin fine.card) :
    auxiliary.tree.fiber
        (auxiliary.insertionLevel + 1)
        (auxiliary.nodeAt (auxiliary.insertionLevel + 1) leaf) =
      auxiliary.auxiliaryFiber (auxiliary.label leaf) := by
  ext source
  constructor
  · intro hsource
    have hnode :
        auxiliary.nodeAt (auxiliary.insertionLevel + 1) source =
          auxiliary.nodeAt (auxiliary.insertionLevel + 1) leaf :=
      (Finset.mem_filter.mp hsource).2
    have hsourceMem :
        source ∈
          auxiliary.nodeAt
            (auxiliary.insertionLevel + 1) source := by
      rw [auxiliary.nodeAt_aux]
      simp
    rw [hnode, auxiliary.nodeAt_aux] at hsourceMem
    exact hsourceMem
  · intro hsource
    have hlabel :
        auxiliary.label source = auxiliary.label leaf :=
      (Finset.mem_filter.mp hsource).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    change
      auxiliary.nodeAt (auxiliary.insertionLevel + 1) source =
        auxiliary.nodeAt (auxiliary.insertionLevel + 1) leaf
    rw [auxiliary.nodeAt_aux, auxiliary.nodeAt_aux]
    ext candidate
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hlabel]

structure CoreOutput (selected : Finset (Fin fine.card)) where
  core : Finset (Fin fine.card)
  core_eq :
    core = (auxiliary.tree.coreOutput selected).core
  core_subset : core ⊆ selected
  global_retention :
    selected.card ≤
      2 ^ (schedule.levelCount + 1) * core.card
  old_node_density :
    ∀ coordinate : Fin schedule.levelCount,
      ∀ node : Finset (Fin fine.card),
        (core ∩
          schedule.tree.fiber (coordinate.1 + 1) node).Nonempty →
          selected.card *
              (schedule.tree.fiber
                (coordinate.1 + 1) node).card ≤
            2 ^ (schedule.levelCount + 1) *
              (core ∩
                schedule.tree.fiber
                  (coordinate.1 + 1) node).card *
              fine.card
  auxiliary_density :
    ∀ label,
      (core ∩ auxiliary.auxiliaryFiber label).Nonempty →
        selected.card *
            (auxiliary.auxiliaryFiber label).card ≤
          2 ^ (schedule.levelCount + 1) *
            (core ∩ auxiliary.auxiliaryFiber label).card *
            fine.card

noncomputable def coreOutput
    (selected : Finset (Fin fine.card)) :
    auxiliary.CoreOutput selected where
  core := (auxiliary.tree.coreOutput selected).core
  core_eq := rfl
  core_subset :=
    (auxiliary.tree.coreOutput selected).core_subset
  global_retention :=
    (auxiliary.tree.coreOutput selected).global_retention
  old_node_density := by
    intro coordinate node hnonempty
    let oldLevel := coordinate.1 + 1
    let liftedLevel := auxiliary.liftLevel oldLevel
    have holdLevel : oldLevel ≤ schedule.levelCount := by
      omega
    have hlifted :
        liftedLevel ≤ schedule.levelCount + 1 := by
      dsimp only [liftedLevel]
      unfold liftLevel
      split_ifs <;> omega
    have hfiber :
        auxiliary.tree.fiber liftedLevel node =
          schedule.tree.fiber oldLevel node := by
      ext leaf
      simp only [PureWZ2Prop62FiniteTree.fiber,
        Finset.mem_filter, Finset.mem_univ, true_and]
      change
        auxiliary.nodeAt liftedLevel leaf = node ↔
          schedule.nodeAt oldLevel leaf = node
      rw [auxiliary.nodeAt_liftLevel holdLevel]
    have hnode :=
      (auxiliary.tree.coreOutput selected).node_density
        liftedLevel hlifted node
    rw [hfiber] at hnode
    simpa only [Fintype.card_fin] using hnode hnonempty
  auxiliary_density := by
    intro label hnonempty
    rcases Finset.nonempty_def.mp hnonempty with
      ⟨leaf, hleaf⟩
    have hlabel :
        auxiliary.label leaf = label :=
      (Finset.mem_filter.mp
        (Finset.mem_inter.mp hleaf).2).2
    have htreeFiber :=
      auxiliary.tree_fiber_aux_eq leaf
    rw [hlabel] at htreeFiber
    have hnode :=
      (auxiliary.tree.coreOutput selected).node_density
        (auxiliary.insertionLevel + 1)
        (Nat.succ_le_succ
          (Nat.le_of_lt auxiliary.insertion_lt))
        (auxiliary.nodeAt (auxiliary.insertionLevel + 1) leaf)
    rw [htreeFiber] at hnode
    simpa only [Fintype.card_fin] using hnode hnonempty

end PureWZ2Prop62AuxiliaryLevel

end Kakeya.Assouad

end

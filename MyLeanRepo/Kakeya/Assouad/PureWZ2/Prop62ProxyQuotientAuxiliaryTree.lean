import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyAncestryMetricOutput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CleanupReceipt

/-!
# Proposition 6.2 quotient-ancestry auxiliary tree

The paper records affine-line ancestry, not copies of ordinary finite
segments.  Accordingly, every old level in this tree is labelled by the
prefix of quotient-center ancestors.  The inserted level records the packet
cell together with the complete quotient-center ancestry above it.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62LaminarPureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)

abbrev ProxyUpperCenterAncestry :=
  ∀ coordinate : schedule.ProxyUpperCoordinate rho packetCoordinate,
    Fin (quotient.level coordinate.1).centerFamily.card

def proxyUpperCenterAncestry
    (source : Fin fine.card) :
    schedule.ProxyUpperCenterAncestry
      fineNonempty quotient rho packetCoordinate :=
  fun coordinate =>
    quotient.leafCenter coordinate.1 source

def proxyUpperCenterPrefixEquivalent
    (level : ℕ)
    (first second : Fin fine.card) : Prop :=
  ∀ coordinate : schedule.ProxyUpperCoordinate rho packetCoordinate,
    coordinate.1.1 < level →
      schedule.proxyUpperCenterAncestry
          fineNonempty quotient rho packetCoordinate first coordinate =
        schedule.proxyUpperCenterAncestry
          fineNonempty quotient rho packetCoordinate second coordinate

theorem proxyUpperCenterPrefixEquivalent_refl
    (level : ℕ)
    (source : Fin fine.card) :
    schedule.proxyUpperCenterPrefixEquivalent
      fineNonempty quotient rho packetCoordinate level source source :=
  fun _ _ => rfl

theorem proxyUpperCenterPrefixEquivalent_symm
    {level : ℕ}
    {first second : Fin fine.card}
    (equivalent :
      schedule.proxyUpperCenterPrefixEquivalent
        fineNonempty quotient rho packetCoordinate level first second) :
    schedule.proxyUpperCenterPrefixEquivalent
      fineNonempty quotient rho packetCoordinate level second first :=
  fun coordinate coordinateLt => (equivalent coordinate coordinateLt).symm

theorem proxyUpperCenterPrefixEquivalent_trans
    {level : ℕ}
    {first second third : Fin fine.card}
    (firstSecond :
      schedule.proxyUpperCenterPrefixEquivalent
        fineNonempty quotient rho packetCoordinate level first second)
    (secondThird :
      schedule.proxyUpperCenterPrefixEquivalent
        fineNonempty quotient rho packetCoordinate level second third) :
    schedule.proxyUpperCenterPrefixEquivalent
      fineNonempty quotient rho packetCoordinate level first third :=
  fun coordinate coordinateLt =>
    (firstSecond coordinate coordinateLt).trans
      (secondThird coordinate coordinateLt)

theorem proxyUpperCenterPrefixEquivalent_mono
    {first second : Fin fine.card}
    {firstLevel secondLevel : ℕ}
    (levelLe : firstLevel ≤ secondLevel)
    (equivalent :
      schedule.proxyUpperCenterPrefixEquivalent
        fineNonempty quotient rho packetCoordinate secondLevel first second) :
    schedule.proxyUpperCenterPrefixEquivalent
      fineNonempty quotient rho packetCoordinate firstLevel first second :=
  fun coordinate coordinateLt =>
    equivalent coordinate (coordinateLt.trans_le levelLe)

end PureWZ2Prop62LaminarPureSchedule

abbrev PureWZ2Prop62ProxyQuotientAuxiliaryLabel
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho : ℝ)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :=
  schedule.ProxyPacketCell
      (schedule.proxyPacketLineCell
        fineNonempty packetCoordinate width) ×
    schedule.ProxyUpperCenterAncestry
      fineNonempty quotient rho packetCoordinate

def pureWZ2Prop62ProxyQuotientAuxiliaryLabel
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho : ℝ)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    PureWZ2Prop62ProxyQuotientAuxiliaryLabel
      schedule fineNonempty quotient rho width packetCoordinate :=
  ⟨schedule.proxyPacketCell
      (schedule.proxyPacketLineCell
        fineNonempty packetCoordinate width)
      source,
    schedule.proxyUpperCenterAncestry
      fineNonempty quotient rho packetCoordinate source⟩

structure PureWZ2Prop62ProxyQuotientAuxiliaryLevel
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho : ℝ)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount) where
  label :
    Fin fine.card →
      PureWZ2Prop62ProxyQuotientAuxiliaryLabel
        schedule fineNonempty quotient rho width packetCoordinate
  label_eq :
    label =
      pureWZ2Prop62ProxyQuotientAuxiliaryLabel
        schedule fineNonempty quotient rho width packetCoordinate

noncomputable def pureWZ2Prop62ProxyQuotientAuxiliaryLevel
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho : ℝ)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount) :
    PureWZ2Prop62ProxyQuotientAuxiliaryLevel
      schedule fineNonempty quotient rho width packetCoordinate where
  label :=
    pureWZ2Prop62ProxyQuotientAuxiliaryLabel
      schedule fineNonempty quotient rho width packetCoordinate
  label_eq := rfl

namespace PureWZ2Prop62ProxyQuotientAuxiliaryLevel

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {rho width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)

def prefixNodeAt
    (level : ℕ)
    (leaf : Fin fine.card) :
    Finset (Fin fine.card) :=
  let _ := auxiliary
  Finset.univ.filter fun source =>
    schedule.proxyUpperCenterPrefixEquivalent
      fineNonempty quotient rho packetCoordinate level source leaf

theorem prefixNodeAt_eq_of_equivalent
    (level : ℕ)
    (first second : Fin fine.card)
    (equivalent :
      schedule.proxyUpperCenterPrefixEquivalent
        fineNonempty quotient rho packetCoordinate level first second) :
    auxiliary.prefixNodeAt level first =
      auxiliary.prefixNodeAt level second := by
  ext source
  simp only [prefixNodeAt, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro sourceFirst coordinate coordinateLt
    exact
      (sourceFirst coordinate coordinateLt).trans
        (equivalent coordinate coordinateLt)
  · intro sourceSecond coordinate coordinateLt
    exact
      (sourceSecond coordinate coordinateLt).trans
        (equivalent coordinate coordinateLt).symm

def nodeAt
    (level : ℕ)
    (leaf : Fin fine.card) :
    Finset (Fin fine.card) :=
  if level ≤ packetCoordinate.1 then
    auxiliary.prefixNodeAt level leaf
  else if level = packetCoordinate.1 + 1 then
    Finset.univ.filter fun source =>
      auxiliary.label source = auxiliary.label leaf
  else
    schedule.nodeAt (level - 1) leaf

theorem nodeAt_prefix
    {level : ℕ}
    (levelLe : level ≤ packetCoordinate.1)
    (leaf : Fin fine.card) :
    auxiliary.nodeAt level leaf =
      auxiliary.prefixNodeAt level leaf := by
  simp [nodeAt, levelLe]

theorem nodeAt_aux
    (leaf : Fin fine.card) :
    auxiliary.nodeAt (packetCoordinate.1 + 1) leaf =
      Finset.univ.filter fun source =>
        auxiliary.label source = auxiliary.label leaf := by
  simp [nodeAt]

theorem nodeAt_fine
    {level : ℕ}
    (afterAuxiliary : packetCoordinate.1 + 1 < level)
    (leaf : Fin fine.card) :
    auxiliary.nodeAt level leaf =
      schedule.nodeAt (level - 1) leaf := by
  simp [nodeAt,
    show ¬level ≤ packetCoordinate.1 by omega,
    show level ≠ packetCoordinate.1 + 1 by omega]

theorem label_refines_prefix
    (first second : Fin fine.card)
    (labelEq : auxiliary.label first = auxiliary.label second) :
    schedule.proxyUpperCenterPrefixEquivalent
      fineNonempty quotient rho packetCoordinate packetCoordinate.1 first second := by
  rw [auxiliary.label_eq] at labelEq
  have ancestryEq :
      schedule.proxyUpperCenterAncestry
          fineNonempty quotient rho packetCoordinate first =
        schedule.proxyUpperCenterAncestry
          fineNonempty quotient rho packetCoordinate second := by
    simpa only [pureWZ2Prop62ProxyQuotientAuxiliaryLabel] using
      congrArg Prod.snd labelEq
  intro coordinate _coordinateLt
  exact congrFun ancestryEq coordinate

theorem packet_parent_refines_label
    (first second : Fin fine.card)
    (parentEq :
      (schedule.scaleData packetCoordinate).cover.parent first =
        (schedule.scaleData packetCoordinate).cover.parent second) :
    auxiliary.label first = auxiliary.label second := by
  rw [auxiliary.label_eq]
  apply Prod.ext
  · apply Subtype.ext
    exact
      schedule.proxyPacketLineCell_parent_invariant
        fineNonempty packetCoordinate width first second parentEq
  · funext coordinate
    change
      quotient.leafCenter coordinate.1 first =
        quotient.leafCenter coordinate.1 second
    unfold PureWZ2Prop62ProxyQuotientScheduleData.leafCenter
    congr 1
    exact
      schedule.parent_eq_of_coordinate_le
        coordinate.1
        packetCoordinate
        (Nat.le_of_lt coordinate.2.2)
        first second parentEq

def auxiliaryFiber
    (label :
      PureWZ2Prop62ProxyQuotientAuxiliaryLabel
        schedule fineNonempty quotient rho width packetCoordinate) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    auxiliary.label source = label

def tree :
    PureWZ2Prop62FiniteTree
      (Fin fine.card) (Finset (Fin fine.card))
      (schedule.levelCount + 1) where
  nodeAt := auxiliary.nodeAt
  root_constant first second := by
    rw [auxiliary.nodeAt_prefix (Nat.zero_le _),
      auxiliary.nodeAt_prefix (Nat.zero_le _)]
    exact auxiliary.prefixNodeAt_eq_of_equivalent 0 first second <|
      fun coordinate coordinateLt =>
        False.elim (Nat.not_lt_zero coordinate.1 coordinateLt)
  nested level levelLt first second nodeEq := by
    by_cases beforeAuxiliary : level < packetCoordinate.1
    · rw [auxiliary.nodeAt_prefix (by omega),
        auxiliary.nodeAt_prefix (by omega)] at nodeEq
      have firstMem :
          first ∈ auxiliary.prefixNodeAt (level + 1) first := by
        simp [prefixNodeAt,
          schedule.proxyUpperCenterPrefixEquivalent_refl
            fineNonempty quotient rho packetCoordinate]
      rw [nodeEq] at firstMem
      have nextEquivalent :
          schedule.proxyUpperCenterPrefixEquivalent
            fineNonempty quotient rho packetCoordinate
            (level + 1) first second := by
        simpa only [prefixNodeAt, Finset.mem_filter,
          Finset.mem_univ, true_and] using firstMem
      rw [auxiliary.nodeAt_prefix (by omega),
        auxiliary.nodeAt_prefix (by omega)]
      exact
        auxiliary.prefixNodeAt_eq_of_equivalent level first second <|
          schedule.proxyUpperCenterPrefixEquivalent_mono
            fineNonempty quotient rho packetCoordinate
            (Nat.le_succ level) nextEquivalent
    · by_cases atAuxiliary : level = packetCoordinate.1
      · subst level
        have firstMem :
            first ∈
              auxiliary.nodeAt
                (packetCoordinate.1 + 1) first := by
          rw [auxiliary.nodeAt_aux]
          simp
        rw [nodeEq] at firstMem
        have labelEq :
            auxiliary.label first = auxiliary.label second := by
          simpa only [auxiliary.nodeAt_aux,
            Finset.mem_filter, Finset.mem_univ, true_and] using
              firstMem
        rw [auxiliary.nodeAt_prefix le_rfl,
          auxiliary.nodeAt_prefix le_rfl]
        exact auxiliary.prefixNodeAt_eq_of_equivalent
          packetCoordinate.1 first second
          (auxiliary.label_refines_prefix first second labelEq)
      · by_cases afterAuxiliary :
          level = packetCoordinate.1 + 1
        · subst level
          have nextAfter :
              packetCoordinate.1 + 1 <
                packetCoordinate.1 + 2 := by omega
          rw [auxiliary.nodeAt_fine nextAfter,
            auxiliary.nodeAt_fine nextAfter] at nodeEq
          have nodeEq' :
              schedule.nodeAt (packetCoordinate.1 + 1) first =
                schedule.nodeAt (packetCoordinate.1 + 1) second := by
            convert nodeEq <;> omega
          have packetParentEq :
              (schedule.scaleData packetCoordinate).cover.parent first =
                (schedule.scaleData packetCoordinate).cover.parent second := by
            have firstMem :
                first ∈
                  schedule.nodeAt
                    (packetCoordinate.1 + 1) first := by
              rw [schedule.nodeAt_succ packetCoordinate.2]
              simp
            rw [nodeEq'] at firstMem
            simpa only [schedule.nodeAt_succ packetCoordinate.2,
              Finset.mem_filter, Finset.mem_univ, true_and] using
                firstMem
          have labelEq :=
            auxiliary.packet_parent_refines_label
              first second packetParentEq
          rw [auxiliary.nodeAt_aux, auxiliary.nodeAt_aux]
          ext source
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [labelEq]
        · have after :
              packetCoordinate.1 + 1 < level := by omega
          have nextAfter :
              packetCoordinate.1 + 1 < level + 1 := by omega
          rw [auxiliary.nodeAt_fine nextAfter,
            auxiliary.nodeAt_fine nextAfter] at nodeEq
          rw [auxiliary.nodeAt_fine after,
            auxiliary.nodeAt_fine after]
          have predecessorLt :
              level - 1 < schedule.levelCount := by omega
          have successor : level - 1 + 1 = level := by omega
          exact
            schedule.tree.nested (level - 1) predecessorLt
              first second <| by
                change
                  schedule.nodeAt level first =
                    schedule.nodeAt level second at nodeEq
                change
                  schedule.nodeAt (level - 1 + 1) first =
                    schedule.nodeAt (level - 1 + 1) second
                rw [successor]
                exact nodeEq

theorem tree_fiber_aux_eq
    (leaf : Fin fine.card) :
    auxiliary.tree.fiber (packetCoordinate.1 + 1)
        (auxiliary.nodeAt (packetCoordinate.1 + 1) leaf) =
      auxiliary.auxiliaryFiber (auxiliary.label leaf) := by
  ext source
  simp only [PureWZ2Prop62FiniteTree.fiber, tree, auxiliaryFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [auxiliary.nodeAt_aux, auxiliary.nodeAt_aux]
  constructor
  · intro nodeEq
    have sourceMem :
        source ∈
          Finset.univ.filter fun candidate =>
            auxiliary.label candidate = auxiliary.label source := by
      simp
    rw [nodeEq] at sourceMem
    simpa using sourceMem
  · intro labelEq
    ext candidate
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [labelEq]

noncomputable def coreOutput
    (selected : Finset (Fin fine.card)) :
    auxiliary.tree.CoreOutput selected :=
  auxiliary.tree.coreOutput selected

end PureWZ2Prop62ProxyQuotientAuxiliaryLevel

structure PureWZ2Prop62ProxyQuotientOnePassCleanupData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal) where
  selection :
    PureWZ2Prop62GlobalResiduePerCellSelectionData
      (Fin fine.card)
      (schedule.ProxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (Fin 4 → ZMod (strideBase + 1))
      (schedule.ProxyUpperColorVector rho packetCoordinate)
      (schedule.proxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (fun source =>
        pureWZ2Prop62LineColor width (strideBase + 1)
          (schedule.coordinateProxyTube
            fineNonempty packetCoordinate
            ((schedule.scaleData packetCoordinate).cover.parent source)))
      (quotient.proxyUpperColorVector rho packetCoordinate)
      weight
  selection_eq :
    selection =
      quotient.selectProxyResidueUpperAncestryPerCell
        rho width packetCoordinate strideBase weight
  preliminary : Finset (Fin fine.card)
  preliminary_nonempty : preliminary.Nonempty
  preliminary_subset_selection :
    preliminary ⊆ selection.selected
  auxiliary :
    PureWZ2Prop62ProxyQuotientAuxiliaryLevel
      schedule fineNonempty quotient rho width packetCoordinate
  core :
    PureWZ2Prop62CleanupReceipt auxiliary.tree preliminary

noncomputable def pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary) :
    PureWZ2Prop62ProxyQuotientOnePassCleanupData
      schedule fineNonempty quotient rho width
        packetCoordinate strideBase weight := by
  let selection :=
    quotient.selectProxyResidueUpperAncestryPerCell
      rho width packetCoordinate strideBase weight
  let auxiliary :=
    pureWZ2Prop62ProxyQuotientAuxiliaryLevel
      schedule fineNonempty quotient rho width packetCoordinate
  exact
    {
      selection := selection
      selection_eq := rfl
      preliminary := preliminary
      preliminary_nonempty := preliminaryNonempty
      preliminary_subset_selection := preliminarySubsetSelection
      auxiliary := auxiliary
      core := receipt
    }

@[simp] theorem pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt_core
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary) :
    (pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt
      schedule fineNonempty quotient rho width packetCoordinate
        strideBase weight preliminary preliminaryNonempty
        preliminarySubsetSelection receipt).core =
      receipt :=
  rfl

noncomputable def pureWZ2Prop62ProxyQuotientOnePassCleanup
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected) :
    PureWZ2Prop62ProxyQuotientOnePassCleanupData
      schedule fineNonempty quotient rho width
        packetCoordinate strideBase weight :=
  pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt
    schedule fineNonempty quotient rho width packetCoordinate
      strideBase weight preliminary preliminaryNonempty
      preliminarySubsetSelection
      (pureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary)

namespace PureWZ2Prop62ProxyQuotientOnePassCleanupData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {rho width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyQuotientOnePassCleanupData
        schedule fineNonempty quotient rho width
          packetCoordinate strideBase weight)

theorem core_subset_selection :
    output.core.core ⊆ output.selection.selected :=
  fun _ sourceMem =>
    output.preliminary_subset_selection
      (output.core.core_subset sourceMem)

theorem preliminary_card_le_core :
    output.preliminary.card ≤
      2 ^ (schedule.levelCount + 1) *
        output.core.core.card :=
  output.core.global_retention

theorem selection_mem_iff_of_auxiliary_label_eq
    (first second : Fin fine.card)
    (labelEq :
      output.auxiliary.label first =
        output.auxiliary.label second) :
    first ∈ output.selection.selected ↔
      second ∈ output.selection.selected := by
  rw [output.auxiliary.label_eq] at labelEq
  have packetCellEq :
      schedule.proxyPacketCell
            (schedule.proxyPacketLineCell
              fineNonempty packetCoordinate width) first =
        schedule.proxyPacketCell
            (schedule.proxyPacketLineCell
              fineNonempty packetCoordinate width) second :=
    congrArg Prod.fst labelEq
  have rawCellEq :
      schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width first =
        schedule.proxyPacketLineCell
            fineNonempty packetCoordinate width second :=
    congrArg Subtype.val packetCellEq
  have residueEq :
      pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate
              ((schedule.scaleData packetCoordinate).cover.parent first)) =
        pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate
              ((schedule.scaleData packetCoordinate).cover.parent second)) := by
    unfold pureWZ2Prop62LineColor
    exact congrArg
      (fun cell : Fin 4 → ℤ =>
        fun coordinate => (cell coordinate : ZMod (strideBase + 1)))
      rawCellEq
  have ancestryEq :
      schedule.proxyUpperCenterAncestry
            fineNonempty quotient rho packetCoordinate first =
        schedule.proxyUpperCenterAncestry
            fineNonempty quotient rho packetCoordinate second :=
    congrArg Prod.snd labelEq
  have colorEq :
      quotient.proxyUpperColorVector rho packetCoordinate first =
        quotient.proxyUpperColorVector rho packetCoordinate second := by
    funext coordinate
    unfold
      PureWZ2Prop62ProxyQuotientScheduleData.proxyUpperColorVector
      PureWZ2Prop62ProxyQuotientScheduleData.leafCenterColor
    congr 1
    simpa only [
      PureWZ2Prop62LaminarPureSchedule.proxyUpperCenterAncestry
    ] using congrFun ancestryEq coordinate
  rw [output.selection.selected_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [residueEq, packetCellEq, colorEq]

theorem auxiliary_density
    (label :
      PureWZ2Prop62ProxyQuotientAuxiliaryLabel
        schedule fineNonempty quotient rho width packetCoordinate)
    (nonempty :
      (output.core.core ∩
        output.auxiliary.auxiliaryFiber label).Nonempty) :
    output.preliminary.card *
          (output.auxiliary.auxiliaryFiber label).card ≤
      2 ^ (schedule.levelCount + 1) *
        (output.core.core ∩
          output.auxiliary.auxiliaryFiber label).card *
        fine.card := by
  rcases Finset.nonempty_def.mp nonempty with
    ⟨leaf, leafMem⟩
  have labelEq :
      output.auxiliary.label leaf = label :=
    (Finset.mem_filter.mp
      (Finset.mem_inter.mp leafMem).2).2
  have fiberEq :=
    output.auxiliary.tree_fiber_aux_eq leaf
  rw [labelEq] at fiberEq
  have density :=
    output.core.node_density
      (packetCoordinate.1 + 1)
      (Nat.succ_le_succ (Nat.le_of_lt packetCoordinate.2))
      (output.auxiliary.nodeAt
        (packetCoordinate.1 + 1) leaf)
  rw [fiberEq] at density
  simpa only [Fintype.card_fin] using density nonempty

theorem core_nonempty
    : output.core.core.Nonempty := by
  by_contra coreEmpty
  have coreEq : output.core.core = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp coreEmpty
  have selectedZero :
      output.preliminary.card ≤ 0 := by
    simpa [coreEq] using output.preliminary_card_le_core
  have selectedPos :
      0 < output.preliminary.card :=
    Finset.card_pos.mpr output.preliminary_nonempty
  omega

end PureWZ2Prop62ProxyQuotientOnePassCleanupData

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperScaleGeometry

/-!
# Proposition 6.2 metric parents: upper-parent counting

This is the counting core of equation `prop62-upper-parent-cwa`.  A child
whose carrier lies in a convex region contributes its entire packet of fine
leaves to that region.  A common packet-cardinality floor therefore converts
the child count into a fine-leaf count before the ambient CWA is applied.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem pureWZ2_prop62_upper_parent_counting
    {Leaf Child : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Child] [DecidableEq Child]
    (owner : Leaf → Child)
    (selectedLeaves : Finset Leaf)
    (activeChildren containedChildren : Finset Child)
    (containedLeaves : Finset Leaf)
    (degreeFloor : ℕ)
    (contained_subset :
      containedChildren ⊆ activeChildren)
    (fiber_floor :
      ∀ child ∈ activeChildren,
        degreeFloor ≤
          (selectedLeaves.filter fun leaf =>
            owner leaf = child).card)
    (packet_containment :
      ∀ leaf ∈ selectedLeaves,
        owner leaf ∈ containedChildren →
          leaf ∈ containedLeaves) :
    degreeFloor * containedChildren.card ≤
      containedLeaves.card := by
  let selectedInContained : Finset Leaf :=
    selectedLeaves.filter fun leaf =>
      owner leaf ∈ containedChildren
  have selectedInContained_subset :
      selectedInContained ⊆ containedLeaves := by
    intro leaf hleaf
    have hdata := Finset.mem_filter.mp hleaf
    exact packet_containment leaf hdata.1 hdata.2
  have fiberSum :
      ∑ child ∈ containedChildren,
          (selectedLeaves.filter fun leaf =>
            owner leaf = child).card =
        selectedInContained.card := by
    simpa only [selectedInContained] using
      Finset.sum_card_fiberwise_eq_card_filter
        selectedLeaves containedChildren owner
  calc
    degreeFloor * containedChildren.card =
        ∑ _child ∈ containedChildren, degreeFloor := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤
        ∑ child ∈ containedChildren,
          (selectedLeaves.filter fun leaf =>
            owner leaf = child).card := by
      exact Finset.sum_le_sum fun child hchild =>
        fiber_floor child (contained_subset hchild)
    _ = selectedInContained.card := fiberSum
    _ ≤ containedLeaves.card :=
      Finset.card_le_card selectedInContained_subset

theorem pureWZ2_prop62_upper_parent_cwa_cross
    {Leaf Child : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Child] [DecidableEq Child]
    (owner : Leaf → Child)
    (selectedLeaves : Finset Leaf)
    (activeChildren containedChildren : Finset Child)
    (containedLeaves : Finset Leaf)
    (degreeFloor : ℕ)
    (contained_subset :
      containedChildren ⊆ activeChildren)
    (fiber_floor :
      ∀ child ∈ activeChildren,
        degreeFloor ≤
          (selectedLeaves.filter fun leaf =>
            owner leaf = child).card)
    (packet_containment :
      ∀ leaf ∈ selectedLeaves,
        owner leaf ∈ containedChildren →
          leaf ∈ containedLeaves)
    (C volumeFactor ambientCard : ENNReal)
    (ambient_cwa :
      (containedLeaves.card : ENNReal) ≤
        C * volumeFactor * ambientCard) :
    (degreeFloor : ENNReal) *
        (containedChildren.card : ENNReal) ≤
      C * volumeFactor * ambientCard := by
  have hcount :=
    pureWZ2_prop62_upper_parent_counting
      owner selectedLeaves activeChildren containedChildren
      containedLeaves degreeFloor contained_subset
      fiber_floor packet_containment
  exact
    (show
      (degreeFloor : ENNReal) *
          (containedChildren.card : ENNReal) ≤
        (containedLeaves.card : ENNReal) by
      exact_mod_cast hcount).trans ambient_cwa

/--
Cancel the common packet-cardinality floor in
`prop62-upper-parent-cwa`.

The three comparison factors have the literal paper meanings:

* `ambientToSelected` transfers the old ambient leaf packet to the final core;
* `degreeRatio` compares the upper and lower metric-packet cardinalities;
* `sourceConstant` is the old ancestor's normalized CWA constant.
-/
theorem pureWZ2_prop62_upper_parent_cwa_cancel
    (degreeFloor containedChildren ambientLeaves selectedLeaves
      activeChildren ambientToSelected degreeRatio sourceConstant
      volumeFactor : ENNReal)
    (degreeFloor_pos : 0 < degreeFloor)
    (degreeFloor_ne_top : degreeFloor ≠ ⊤)
    (cross_bound :
      degreeFloor * containedChildren ≤
        sourceConstant * volumeFactor * ambientLeaves)
    (ambient_to_selected :
      ambientLeaves ≤ ambientToSelected * selectedLeaves)
    (selected_upper :
      selectedLeaves ≤
        degreeRatio * degreeFloor * activeChildren) :
    containedChildren ≤
      (sourceConstant * ambientToSelected * degreeRatio) *
        volumeFactor * activeChildren := by
  have scaled :
      containedChildren * degreeFloor ≤
        ((sourceConstant * ambientToSelected * degreeRatio) *
          volumeFactor * activeChildren) * degreeFloor := by
    calc
      containedChildren * degreeFloor =
          degreeFloor * containedChildren := by ring
      _ ≤ sourceConstant * volumeFactor * ambientLeaves :=
        cross_bound
      _ ≤
          sourceConstant * volumeFactor *
            (ambientToSelected * selectedLeaves) := by
        gcongr
      _ ≤
          sourceConstant * volumeFactor *
            (ambientToSelected *
              (degreeRatio * degreeFloor * activeChildren)) := by
        gcongr
      _ =
          ((sourceConstant * ambientToSelected * degreeRatio) *
            volumeFactor * activeChildren) * degreeFloor := by
        ring
  exact
    (ENNReal.mul_le_mul_iff_left
      degreeFloor_pos.ne' degreeFloor_ne_top).mp scaled

/--
Nat-cardinality form of the complete upper-parent CWA calculation.

It combines the packet-counting injection with the final-core and
factor-two packet-cardinality comparisons, but leaves all geometric set
definitions to the caller.
-/
theorem pureWZ2_prop62_upper_parent_cwa
    {Leaf Child : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Child] [DecidableEq Child]
    (owner : Leaf → Child)
    (selectedLeaves : Finset Leaf)
    (activeChildren containedChildren : Finset Child)
    (containedLeaves : Finset Leaf)
    (degreeFloor : ℕ)
    (degreeFloor_pos : 0 < degreeFloor)
    (contained_subset :
      containedChildren ⊆ activeChildren)
    (fiber_floor :
      ∀ child ∈ activeChildren,
        degreeFloor ≤
          (selectedLeaves.filter fun leaf =>
            owner leaf = child).card)
    (packet_containment :
      ∀ leaf ∈ selectedLeaves,
        owner leaf ∈ containedChildren →
          leaf ∈ containedLeaves)
    (ambientLeaves ambientToSelected degreeRatio sourceConstant
      volumeFactor : ENNReal)
    (containedLeaves_cwa :
      (containedLeaves.card : ENNReal) ≤
        sourceConstant * volumeFactor * ambientLeaves)
    (ambient_to_selected :
      ambientLeaves ≤
        ambientToSelected * (selectedLeaves.card : ENNReal))
    (selected_upper :
      (selectedLeaves.card : ENNReal) ≤
        degreeRatio * (degreeFloor : ENNReal) *
          (activeChildren.card : ENNReal)) :
    (containedChildren.card : ENNReal) ≤
      (sourceConstant * ambientToSelected * degreeRatio) *
        volumeFactor * (activeChildren.card : ENNReal) := by
  have cross :=
    pureWZ2_prop62_upper_parent_cwa_cross
      owner selectedLeaves activeChildren containedChildren
      containedLeaves degreeFloor contained_subset fiber_floor
      packet_containment sourceConstant volumeFactor ambientLeaves
      containedLeaves_cwa
  exact
    pureWZ2_prop62_upper_parent_cwa_cancel
      (degreeFloor : ENNReal)
      (containedChildren.card : ENNReal)
      ambientLeaves
      (selectedLeaves.card : ENNReal)
      (activeChildren.card : ENNReal)
      ambientToSelected degreeRatio sourceConstant volumeFactor
      (by exact_mod_cast degreeFloor_pos)
      (by simp)
      cross ambient_to_selected selected_upper

/--
Upper-parent counting when the common cardinality floor is available only
after an explicit core-density loss:

`degreeFloor ≤ floorScale * #fiber`.

This is the literal form needed after the Proposition 6.2 augmented-tree
cleanup, where `degreeFloor = D_-` and `floorScale = θ⁻¹`.
-/
theorem pureWZ2_prop62_upper_parent_cwa_scaled_floor
    {Leaf Child : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Child] [DecidableEq Child]
    (owner : Leaf → Child)
    (selectedLeaves : Finset Leaf)
    (activeChildren containedChildren : Finset Child)
    (containedLeaves : Finset Leaf)
    (degreeFloor : ℕ)
    (degreeFloor_pos : 0 < degreeFloor)
    (floorScale : ENNReal)
    (contained_subset :
      containedChildren ⊆ activeChildren)
    (fiber_floor :
      ∀ child ∈ activeChildren,
        (degreeFloor : ENNReal) ≤
          floorScale *
            ((selectedLeaves.filter fun leaf =>
              owner leaf = child).card : ENNReal))
    (packet_containment :
      ∀ leaf ∈ selectedLeaves,
        owner leaf ∈ containedChildren →
          leaf ∈ containedLeaves)
    (ambientLeaves ambientToSelected degreeRatio sourceConstant
      volumeFactor : ENNReal)
    (containedLeaves_cwa :
      (containedLeaves.card : ENNReal) ≤
        sourceConstant * volumeFactor * ambientLeaves)
    (ambient_to_selected :
      ambientLeaves ≤
        ambientToSelected * (selectedLeaves.card : ENNReal))
    (selected_upper :
      (selectedLeaves.card : ENNReal) ≤
        degreeRatio * (degreeFloor : ENNReal) *
          (activeChildren.card : ENNReal)) :
    (containedChildren.card : ENNReal) ≤
      ((floorScale * sourceConstant) *
          ambientToSelected * degreeRatio) *
        volumeFactor * (activeChildren.card : ENNReal) := by
  let selectedInContained : Finset Leaf :=
    selectedLeaves.filter fun leaf =>
      owner leaf ∈ containedChildren
  have selectedInContained_subset :
      selectedInContained ⊆ containedLeaves := by
    intro leaf leafMem
    have leafData := Finset.mem_filter.mp leafMem
    exact packet_containment leaf leafData.1 leafData.2
  have fiberSum :
      ∑ child ∈ containedChildren,
          ((selectedLeaves.filter fun leaf =>
            owner leaf = child).card : ENNReal) =
        (selectedInContained.card : ENNReal) := by
    have natural :=
      Finset.sum_card_fiberwise_eq_card_filter
        selectedLeaves containedChildren owner
    exact_mod_cast natural
  have cross :
      (degreeFloor : ENNReal) *
          (containedChildren.card : ENNReal) ≤
        (floorScale * sourceConstant) *
          volumeFactor * ambientLeaves := by
    calc
      (degreeFloor : ENNReal) *
          (containedChildren.card : ENNReal) =
          ∑ _child ∈ containedChildren,
            (degreeFloor : ENNReal) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤
          ∑ child ∈ containedChildren,
            floorScale *
              ((selectedLeaves.filter fun leaf =>
                owner leaf = child).card : ENNReal) := by
        exact Finset.sum_le_sum fun child childMem =>
          fiber_floor child (contained_subset childMem)
      _ =
          floorScale * (selectedInContained.card : ENNReal) := by
        rw [← fiberSum]
        exact
          (Finset.mul_sum containedChildren
            (fun child =>
              ((selectedLeaves.filter fun leaf =>
                owner leaf = child).card : ENNReal))
            floorScale).symm
      _ ≤ floorScale * (containedLeaves.card : ENNReal) := by
        exact mul_le_mul_left' (by
          exact_mod_cast
            Finset.card_le_card selectedInContained_subset) _
      _ ≤
          floorScale *
            (sourceConstant * volumeFactor * ambientLeaves) := by
        gcongr
      _ =
          (floorScale * sourceConstant) *
            volumeFactor * ambientLeaves := by
        ring
  exact
    pureWZ2_prop62_upper_parent_cwa_cancel
      (degreeFloor : ENNReal)
      (containedChildren.card : ENNReal)
      ambientLeaves
      (selectedLeaves.card : ENNReal)
      (activeChildren.card : ENNReal)
      ambientToSelected degreeRatio
      (floorScale * sourceConstant) volumeFactor
      (by exact_mod_cast degreeFloor_pos)
      (by simp)
      cross ambient_to_selected selected_upper

end Kakeya.Assouad

end

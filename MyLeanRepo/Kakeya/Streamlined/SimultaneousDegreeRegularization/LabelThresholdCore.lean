import MyLeanRepo.Kakeya.Streamlined.SimultaneousDegreeRegularization.TCore

/-!
# Label-dependent cores for finite multipartite systems

The ordinary `TCore` uses one threshold per coordinate.  The common
parent/component selector needs a different threshold for every label, since
each original fiber must retain a fixed fraction of its own cardinality.

This module proves the corresponding finite deletion theorem.  Repeatedly
delete a nonempty fiber whose size is below its label-dependent threshold.
The total number of deleted vertices is bounded by

```text
sum coordinate, sum active label, threshold coordinate label.
```
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Every nonempty coordinate fiber of a label-threshold core meets the
threshold assigned to that exact label. -/
def IsLabelThresholdCore
    {I : Type*} [DecidableEq I]
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {Label : Coordinate → Type*}
    [∀ coordinate, DecidableEq (Label coordinate)]
    (parent : ∀ coordinate, I → Label coordinate)
    (threshold : ∀ coordinate, Label coordinate → ℕ)
    (selected : Finset I) : Prop :=
  ∀ (coordinate : Coordinate) (label : Label coordinate),
    0 < (selected.filter
      (fun vertex => parent coordinate vertex = label)).card →
      threshold coordinate label ≤
        (selected.filter
          (fun vertex => parent coordinate vertex = label)).card

/-- Sum of the thresholds of all labels active in a finite vertex set. -/
def labelThresholdCapacity
    {I : Type*} [DecidableEq I]
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {Label : Coordinate → Type*}
    [∀ coordinate, DecidableEq (Label coordinate)]
    (parent : ∀ coordinate, I → Label coordinate)
    (threshold : ∀ coordinate, Label coordinate → ℕ)
    (vertices : Finset I) : ℕ :=
  ∑ coordinate : Coordinate,
    ∑ label ∈ vertices.image (parent coordinate),
      threshold coordinate label

private lemma labelThresholdCapacity_decrease
    {I : Type*} [DecidableEq I]
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {Label : Coordinate → Type*}
    [∀ coordinate, DecidableEq (Label coordinate)]
    (parent : ∀ coordinate, I → Label coordinate)
    (threshold : ∀ coordinate, Label coordinate → ℕ)
    (vertices : Finset I)
    (coordinate : Coordinate)
    (label : Label coordinate)
    (hlabel :
      label ∈ vertices.image (parent coordinate)) :
    let fiber :=
      vertices.filter
        (fun vertex => parent coordinate vertex = label)
    let remaining := vertices \ fiber
    labelThresholdCapacity parent threshold remaining +
        threshold coordinate label ≤
      labelThresholdCapacity parent threshold vertices := by
  classical
  let fiber :=
    vertices.filter
      (fun vertex => parent coordinate vertex = label)
  let remaining := vertices \ fiber
  have himage_coordinate :
      remaining.image (parent coordinate) =
        vertices.image (parent coordinate) \ {label} := by
    ext current
    simp only
      [remaining, fiber, Finset.mem_image, Finset.mem_sdiff,
        Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨vertex, ⟨hvertex, hnotFiber⟩, rfl⟩
      refine ⟨⟨vertex, hvertex, rfl⟩, ?_⟩
      intro heq
      apply hnotFiber
      exact ⟨hvertex, heq⟩
    · rintro ⟨⟨vertex, hvertex, hparent⟩, hne⟩
      refine ⟨vertex, ⟨hvertex, ?_⟩, hparent⟩
      intro hfiber
      exact hne (hparent.symm.trans hfiber.2)
  have himage_subset :
      ∀ current : Coordinate,
        remaining.image (parent current) ⊆
          vertices.image (parent current) := by
    intro current value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨vertex, hvertex, rfl⟩
    have hvertex' : vertex ∈ vertices :=
      (Finset.mem_sdiff.mp hvertex).1
    exact Finset.mem_image.mpr ⟨vertex, hvertex', rfl⟩
  let capacityAt :
      Coordinate → Finset I → ℕ :=
    fun current set =>
      ∑ value ∈ set.image (parent current),
        threshold current value
  have hcoordinate :
      capacityAt coordinate remaining +
          threshold coordinate label =
        capacityAt coordinate vertices := by
    dsimp only [capacityAt]
    rw [himage_coordinate]
    have hsingleton :
        ({label} : Finset (Label coordinate)) ⊆
          vertices.image (parent coordinate) := by
      simpa using hlabel
    simpa using
      (Finset.sum_sdiff
        (f := threshold coordinate) hsingleton)
  have hother :
      ∀ current : Coordinate,
        capacityAt current remaining ≤
          capacityAt current vertices := by
    intro current
    dsimp only [capacityAt]
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (himage_subset current)
        (fun _ _ _ => Nat.zero_le _)
  have hsum_remaining :
      (∑ current : Coordinate, capacityAt current remaining) =
        (∑ current ∈
            (Finset.univ : Finset Coordinate).erase coordinate,
            capacityAt current remaining) +
          capacityAt coordinate remaining := by
    symm
    exact
      Finset.sum_erase_add
        (Finset.univ : Finset Coordinate)
        (fun current => capacityAt current remaining)
        (Finset.mem_univ coordinate)
  have hsum_vertices :
      (∑ current : Coordinate, capacityAt current vertices) =
        (∑ current ∈
            (Finset.univ : Finset Coordinate).erase coordinate,
            capacityAt current vertices) +
          capacityAt coordinate vertices := by
    symm
    exact
      Finset.sum_erase_add
        (Finset.univ : Finset Coordinate)
        (fun current => capacityAt current vertices)
        (Finset.mem_univ coordinate)
  have hotherSum :
      (∑ current ∈
          (Finset.univ : Finset Coordinate).erase coordinate,
          capacityAt current remaining) ≤
        ∑ current ∈
          (Finset.univ : Finset Coordinate).erase coordinate,
          capacityAt current vertices := by
    exact Finset.sum_le_sum fun current _ => hother current
  change
    (∑ current : Coordinate, capacityAt current remaining) +
        threshold coordinate label ≤
      ∑ current : Coordinate, capacityAt current vertices
  rw [hsum_remaining, hsum_vertices]
  calc
    (∑ current ∈
          (Finset.univ : Finset Coordinate).erase coordinate,
          capacityAt current remaining) +
          capacityAt coordinate remaining +
        threshold coordinate label =
      (∑ current ∈
          (Finset.univ : Finset Coordinate).erase coordinate,
          capacityAt current remaining) +
        (capacityAt coordinate remaining +
          threshold coordinate label) := by omega
    _ =
      (∑ current ∈
          (Finset.univ : Finset Coordinate).erase coordinate,
          capacityAt current remaining) +
        capacityAt coordinate vertices := by
          rw [hcoordinate]
    _ ≤
      (∑ current ∈
          (Finset.univ : Finset Coordinate).erase coordinate,
          capacityAt current vertices) +
        capacityAt coordinate vertices := by
          gcongr

/--
Every finite multipartite vertex set has a label-threshold core.  The number
of removed vertices is bounded by the exact initial threshold capacity.
-/
theorem label_threshold_core_existence
    {I : Type*} [DecidableEq I]
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {Label : Coordinate → Type*}
    [∀ coordinate, DecidableEq (Label coordinate)]
    (parent : ∀ coordinate, I → Label coordinate)
    (threshold : ∀ coordinate, Label coordinate → ℕ)
    (vertices : Finset I) :
    ∃ core : Finset I,
      core ⊆ vertices ∧
      IsLabelThresholdCore parent threshold core ∧
      (vertices \ core).card ≤
        labelThresholdCapacity parent threshold vertices := by
  classical
  let property : ℕ → Prop :=
    fun size =>
      ∀ current : Finset I, current.card ≤ size →
        ∃ core : Finset I,
          core ⊆ current ∧
          IsLabelThresholdCore parent threshold core ∧
          (current \ core).card ≤
            labelThresholdCapacity parent threshold current
  have hstep :
      ∀ size : ℕ,
        (∀ smaller : ℕ, smaller < size → property smaller) →
          property size := by
    intro size inductionHypothesis current hcurrent
    by_cases hcore :
        IsLabelThresholdCore parent threshold current
    · exact ⟨current, by simp, hcore, by simp⟩
    · have hbad :
          ∃ (coordinate : Coordinate)
            (label : Label coordinate),
            0 <
              (current.filter
                (fun vertex =>
                  parent coordinate vertex = label)).card ∧
            (current.filter
                (fun vertex =>
                  parent coordinate vertex = label)).card <
              threshold coordinate label := by
        simpa [IsLabelThresholdCore] using hcore
      rcases hbad with
        ⟨coordinate, label, hfiberPositive, hfiberSmall⟩
      let fiber :=
        current.filter
          (fun vertex => parent coordinate vertex = label)
      let remaining := current \ fiber
      have hfiberSubset : fiber ⊆ current :=
        Finset.filter_subset _ _
      have hremainingCard :
          remaining.card = current.card - fiber.card := by
        rw [show remaining = current \ fiber from rfl]
        rw [Finset.card_sdiff]
        have hinter : fiber ∩ current = fiber := by
          exact Finset.inter_eq_left.mpr hfiberSubset
        rw [hinter]
      have hremainingLt :
          remaining.card < current.card := by
        rw [hremainingCard]
        exact Nat.sub_lt
          (lt_of_lt_of_le hfiberPositive
            (Finset.card_le_card hfiberSubset))
          hfiberPositive
      have hremainingLtSize :
          remaining.card < size :=
        hremainingLt.trans_le hcurrent
      rcases
          inductionHypothesis remaining.card
            hremainingLtSize remaining le_rfl with
        ⟨core, hcoreSubsetRemaining, hcoreProperty,
          hremovedRemaining⟩
      have hremainingSubsetCurrent :
          remaining ⊆ current :=
        Finset.sdiff_subset
      have hcoreSubsetCurrent :
          core ⊆ current :=
        hcoreSubsetRemaining.trans hremainingSubsetCurrent
      have hlabelImage :
          label ∈ current.image (parent coordinate) := by
        rcases Finset.card_pos.mp hfiberPositive with
          ⟨vertex, hvertex⟩
        exact Finset.mem_image.mpr
          ⟨vertex, (Finset.mem_filter.mp hvertex).1,
            (Finset.mem_filter.mp hvertex).2⟩
      have hcapacityDecrease :
          labelThresholdCapacity parent threshold remaining +
              threshold coordinate label ≤
            labelThresholdCapacity parent threshold current :=
        labelThresholdCapacity_decrease
          parent threshold current coordinate label hlabelImage
      have hfiberRemovedDisjoint :
          Disjoint fiber (remaining \ core) := by
        rw [Finset.disjoint_left]
        intro vertex hvertexFiber hvertexRemaining
        have hremaining :
            vertex ∈ remaining :=
          (Finset.mem_sdiff.mp hvertexRemaining).1
        exact (Finset.mem_sdiff.mp hremaining).2 hvertexFiber
      have hremovedUnion :
          current \ core =
            fiber ∪ (remaining \ core) := by
        ext vertex
        simp only
          [remaining, Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro hvertex
          by_cases hvertexFiber : vertex ∈ fiber
          · exact Or.inl hvertexFiber
          · exact Or.inr
              ⟨⟨hvertex.1, hvertexFiber⟩, hvertex.2⟩
        · rintro (hvertexFiber |
            ⟨⟨hvertexCurrent, _⟩, hvertexCore⟩)
          · have hnotCore : vertex ∉ core := by
              intro hvertexCore
              have hvertexRemaining :
                  vertex ∈ remaining :=
                hcoreSubsetRemaining hvertexCore
              exact
                (Finset.mem_sdiff.mp hvertexRemaining).2
                  hvertexFiber
            exact ⟨hfiberSubset hvertexFiber, hnotCore⟩
          · exact ⟨hvertexCurrent, hvertexCore⟩
      have hremovedCard :
          (current \ core).card =
            fiber.card + (remaining \ core).card := by
        rw [hremovedUnion,
          Finset.card_union_of_disjoint
            hfiberRemovedDisjoint]
      have hfiberBound :
          fiber.card ≤ threshold coordinate label := by
        have h :
            fiber.card < threshold coordinate label := by
          simpa [fiber] using hfiberSmall
        exact h.le
      have hremovedBound :
          (current \ core).card ≤
            labelThresholdCapacity parent threshold current := by
        rw [hremovedCard]
        calc
          fiber.card + (remaining \ core).card
              ≤ threshold coordinate label +
                  (remaining \ core).card := by
                    gcongr
          _ ≤ threshold coordinate label +
                labelThresholdCapacity
                  parent threshold remaining := by
              gcongr
          _ =
              labelThresholdCapacity
                  parent threshold remaining +
                threshold coordinate label := by omega
          _ ≤
              labelThresholdCapacity
                parent threshold current :=
            hcapacityDecrease
      exact
        ⟨core, hcoreSubsetCurrent, hcoreProperty,
          hremovedBound⟩
  have hall :
      ∀ size : ℕ, property size :=
    fun size => Nat.strong_induction_on size hstep
  exact hall vertices.card vertices le_rfl

/-- A strict capacity bound forces the selected core to be nonempty. -/
theorem nonempty_label_threshold_core_existence
    {I : Type*} [DecidableEq I]
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {Label : Coordinate → Type*}
    [∀ coordinate, DecidableEq (Label coordinate)]
    (parent : ∀ coordinate, I → Label coordinate)
    (threshold : ∀ coordinate, Label coordinate → ℕ)
    (vertices : Finset I)
    (hcapacity :
      labelThresholdCapacity parent threshold vertices <
        vertices.card) :
    ∃ core : Finset I,
      core.Nonempty ∧
      core ⊆ vertices ∧
      IsLabelThresholdCore parent threshold core ∧
      (vertices \ core).card ≤
        labelThresholdCapacity parent threshold vertices := by
  rcases
      label_threshold_core_existence
        parent threshold vertices with
    ⟨core, hcoreSubset, hcore, hremoved⟩
  have hcoreNonempty : core.Nonempty := by
    by_contra hempty
    have hcoreEmpty : core = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hremovedAll :
        (vertices \ core).card = vertices.card := by
      rw [hcoreEmpty]
      simp
    rw [hremovedAll] at hremoved
    exact (not_le_of_gt hcapacity) hremoved
  exact
    ⟨core, hcoreNonempty, hcoreSubset, hcore, hremoved⟩

end Kakeya.Streamlined

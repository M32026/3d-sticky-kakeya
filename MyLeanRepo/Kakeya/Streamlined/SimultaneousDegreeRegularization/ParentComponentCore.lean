import MyLeanRepo.Kakeya.Streamlined.SimultaneousDegreeRegularization.LabelThresholdCore
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.ConflictColoring

/-!
# A common core for parent and component labels

At each coordinate every vertex has a parent label and a finer component
label.  First choose one common vector of dyadic parent/component bins.  Then
run one label-dependent core on both label systems.  The output keeps one
common selected vertex set, a fixed fraction of every active original label
fiber, and a fixed fraction of a weight whose values were already placed in
one dyadic interval.
-/

noncomputable section

namespace Kakeya.Streamlined

universe u

/-- Number of joint parent/component bin vectors. -/
def parentComponentColorCount (m B : ℕ) : ℕ :=
  B ^ (2 * m)

/-- Denominator used for every label-dependent retained-fraction threshold. -/
def parentComponentCoreDenominator (m B : ℕ) : ℕ :=
  16 * m * parentComponentColorCount m B

private lemma finset_sum_div_le_div_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (denominator : ℕ) :
    ∑ x ∈ s, f x / denominator ≤
      (∑ x ∈ s, f x) / denominator := by
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      calc
        f x / denominator + ∑ y ∈ s, f y / denominator
            ≤ f x / denominator +
                (∑ y ∈ s, f y) / denominator := by
              gcongr
        _ ≤ (f x + ∑ y ∈ s, f y) / denominator :=
          Nat.add_div_le_add_div _ _ _

private lemma sum_original_fiber_cards_le
    {I Label : Type*} [Fintype Label]
    [DecidableEq I] [DecidableEq Label]
    (vertices : Finset I) (label : I → Label)
    (active : Finset Label) :
    ∑ value ∈ active,
        (vertices.filter fun vertex => label vertex = value).card ≤
      vertices.card := by
  calc
    ∑ value ∈ active,
        (vertices.filter fun vertex => label vertex = value).card
        ≤ ∑ value : Label,
            (vertices.filter fun vertex => label vertex = value).card := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ active) (fun _ _ _ => Nat.zero_le _)
    _ = vertices.card := by
      simpa using
        (Finset.sum_fiberwise'
          vertices label (fun _ => (1 : ℕ)))

/--
Choose one common parent/component profile cell and prune it to a
label-dependent core.

The hypotheses on `weight` say that the input `vertices` have already been
placed in one positive dyadic weight bin.  This turns the cardinality loss of
the core into a weight loss without another selection.
-/
lemma simultaneous_parent_component_core
    {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (hm : 0 < m)
    (Parent Component : Fin m → Type u)
    [∀ k, Fintype (Parent k)] [∀ k, DecidableEq (Parent k)]
    [∀ k, Fintype (Component k)] [∀ k, DecidableEq (Component k)]
    (parent : ∀ k, I → Parent k)
    (component : ∀ k, I → Component k)
    (B : ℕ) (hB : 0 < B)
    (parentBin : ∀ k, Parent k → Fin B)
    (componentBin : ∀ k, Component k → Fin B)
    (vertices : Finset I) (hvertices : vertices.Nonempty)
    (weight : I → ENNReal) (c : ENNReal) (hc : 0 < c)
    (hweight :
      ∀ i ∈ vertices, c ≤ weight i ∧ weight i ≤ 2 * c) :
    ∃ selected : Finset I,
      selected.Nonempty ∧
      selected ⊆ vertices ∧
      (∑ i ∈ vertices, weight i) ≤
        (8 * parentComponentColorCount m B : ℕ) *
          ∑ i ∈ selected, weight i ∧
      (∀ k, ∀ i ∈ selected, ∀ i' ∈ selected,
        parentBin k (parent k i) = parentBin k (parent k i')) ∧
      (∀ k, ∀ i ∈ selected, ∀ i' ∈ selected,
        componentBin k (component k i) =
          componentBin k (component k i')) ∧
      (∀ k, ∀ label : Parent k,
        0 < (selected.filter fun i => parent k i = label).card →
          (vertices.filter fun i => parent k i = label).card ≤
            parentComponentCoreDenominator m B *
              ((selected.filter fun i => parent k i = label).card + 1)) ∧
      ∀ k, ∀ label : Component k,
        0 < (selected.filter fun i => component k i = label).card →
          (vertices.filter fun i => component k i = label).card ≤
            parentComponentCoreDenominator m B *
              ((selected.filter fun i => component k i = label).card + 1) := by
  classical
  let ColorVector := (k : Fin m) → Fin B × Fin B
  let colorCount := parentComponentColorCount m B
  have hColorVectorCard : Fintype.card ColorVector = colorCount := by
    simp only [ColorVector, Fintype.card_pi, Fintype.card_prod,
      Fintype.card_fin, colorCount, parentComponentColorCount]
    calc
      ∏ _ : Fin m, B * B = (B * B) ^ m := by simp
      _ = B ^ (2 * m) := by ring
  have hcolorCount : 0 < colorCount := by
    simp only [colorCount, parentComponentColorCount]
    positivity
  let colorEquiv : ColorVector ≃ Fin colorCount := by
    simpa [hColorVectorCard] using Fintype.equivFin ColorVector
  let color : I → Fin colorCount := fun i =>
    colorEquiv fun k =>
      (parentBin k (parent k i), componentBin k (component k i))
  rcases
      exists_heavy_color_class vertices colorCount hcolorCount color
        (fun _ => (1 : ENNReal)) with
    ⟨chosenColor, hcolorHeavy⟩
  let cell := vertices.filter fun i => color i = chosenColor
  have hverticesCard :
      vertices.card ≤ colorCount * cell.card := by
    have hcast :
        (vertices.card : ENNReal) ≤
          (colorCount : ENNReal) * (cell.card : ENNReal) := by
      simpa [cell] using hcolorHeavy
    exact_mod_cast hcast
  have hcell : cell.Nonempty := by
    by_contra hempty
    have hcellEmpty : cell = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hcellEmpty] at hverticesCard
    simp at hverticesCard
    exact hvertices.ne_empty hverticesCard
  have hcellSubset : cell ⊆ vertices :=
    Finset.filter_subset _ _
  have hparentBin :
      ∀ k, ∀ i ∈ cell, ∀ i' ∈ cell,
        parentBin k (parent k i) = parentBin k (parent k i') := by
    intro k i hi i' hi'
    have hcolorI : color i = chosenColor :=
      (Finset.mem_filter.mp hi).2
    have hcolorI' : color i' = chosenColor :=
      (Finset.mem_filter.mp hi').2
    have hvector :
        (fun k =>
          (parentBin k (parent k i),
            componentBin k (component k i))) =
        fun k =>
          (parentBin k (parent k i'),
            componentBin k (component k i')) := by
      apply colorEquiv.injective
      exact hcolorI.trans hcolorI'.symm
    exact congrArg Prod.fst (congrFun hvector k)
  have hcomponentBin :
      ∀ k, ∀ i ∈ cell, ∀ i' ∈ cell,
        componentBin k (component k i) =
          componentBin k (component k i') := by
    intro k i hi i' hi'
    have hcolorI : color i = chosenColor :=
      (Finset.mem_filter.mp hi).2
    have hcolorI' : color i' = chosenColor :=
      (Finset.mem_filter.mp hi').2
    have hvector :
        (fun k =>
          (parentBin k (parent k i),
            componentBin k (component k i))) =
        fun k =>
          (parentBin k (parent k i'),
            componentBin k (component k i')) := by
      apply colorEquiv.injective
      exact hcolorI.trans hcolorI'.symm
    exact congrArg Prod.snd (congrFun hvector k)
  let Coordinate := Fin m ⊕ Fin m
  let Label : Coordinate → Type _ := fun coordinate =>
    match coordinate with
    | Sum.inl k => Parent k
    | Sum.inr k => Component k
  letI : ∀ coordinate, Fintype (Label coordinate) := fun coordinate =>
    match coordinate with
    | Sum.inl _ => inferInstance
    | Sum.inr _ => inferInstance
  letI : ∀ coordinate, DecidableEq (Label coordinate) := fun coordinate =>
    match coordinate with
    | Sum.inl _ => inferInstance
    | Sum.inr _ => inferInstance
  let label : ∀ coordinate, I → Label coordinate := fun coordinate =>
    match coordinate with
    | Sum.inl k => parent k
    | Sum.inr k => component k
  let denominator := parentComponentCoreDenominator m B
  have hdenominator : 0 < denominator := by
    simp only [denominator, parentComponentCoreDenominator]
    positivity
  let originalFiberCard :
      ∀ coordinate, Label coordinate → ℕ := fun coordinate value =>
    (vertices.filter fun i => label coordinate i = value).card
  let threshold : ∀ coordinate, Label coordinate → ℕ :=
    fun coordinate value => originalFiberCard coordinate value / denominator
  have hcapacityCoordinate :
      ∀ coordinate : Coordinate,
        (∑ value ∈ cell.image (label coordinate),
          threshold coordinate value) ≤
            vertices.card / denominator := by
    intro coordinate
    calc
      (∑ value ∈ cell.image (label coordinate),
          threshold coordinate value)
          ≤ (∑ value ∈ cell.image (label coordinate),
              originalFiberCard coordinate value) / denominator := by
            exact finset_sum_div_le_div_sum
              (cell.image (label coordinate))
              (originalFiberCard coordinate) denominator
      _ ≤ vertices.card / denominator := by
        gcongr
        exact sum_original_fiber_cards_le
          vertices (label coordinate) (cell.image (label coordinate))
  have hcapacity :
      labelThresholdCapacity label threshold cell ≤
        (2 * m) * (vertices.card / denominator) := by
    change
      (∑ coordinate : Coordinate,
        ∑ value ∈ cell.image (label coordinate),
          threshold coordinate value) ≤ _
    calc
      (∑ coordinate : Coordinate,
          ∑ value ∈ cell.image (label coordinate),
            threshold coordinate value)
          ≤ ∑ _coordinate : Coordinate,
              vertices.card / denominator := by
            exact Finset.sum_le_sum fun coordinate _ =>
              hcapacityCoordinate coordinate
      _ = (2 * m) * (vertices.card / denominator) := by
        rw [Finset.sum_const]
        change Fintype.card Coordinate *
            (vertices.card / denominator) =
          (2 * m) * (vertices.card / denominator)
        congr 1
        simp [Coordinate, Fintype.card_sum]
        omega
  have hcapacityEight :
      8 * colorCount * labelThresholdCapacity label threshold cell ≤
        vertices.card := by
    calc
      8 * colorCount * labelThresholdCapacity label threshold cell
          ≤ 8 * colorCount *
              ((2 * m) * (vertices.card / denominator)) := by
            gcongr
      _ = denominator * (vertices.card / denominator) := by
        simp only [denominator, parentComponentCoreDenominator]
        ring
      _ ≤ vertices.card := by
        simpa [mul_comm] using Nat.div_mul_le_self vertices.card denominator
  have hcapacityLt :
      labelThresholdCapacity label threshold cell < cell.card := by
    have hcapacityLeCell :
        8 * labelThresholdCapacity label threshold cell ≤ cell.card := by
      have hpositiveColor : 0 < colorCount := hcolorCount
      have hmain :
          colorCount *
              (8 * labelThresholdCapacity label threshold cell) ≤
            colorCount * cell.card := by
        calc
          colorCount *
                (8 * labelThresholdCapacity label threshold cell)
              = 8 * colorCount *
                  labelThresholdCapacity label threshold cell := by ring
          _ ≤ vertices.card := hcapacityEight
          _ ≤ colorCount * cell.card := hverticesCard
      exact Nat.le_of_mul_le_mul_left hmain hpositiveColor
    have hcellCard : 0 < cell.card := hcell.card_pos
    omega
  rcases
      nonempty_label_threshold_core_existence
        label threshold cell hcapacityLt with
    ⟨selected, hselected, hselectedSubsetCell, hselectedCore, hremoved⟩
  have hselectedSubset : selected ⊆ vertices :=
    hselectedSubsetCell.trans hcellSubset
  have hcellCardDecomposition :
      (cell \ selected).card + selected.card = cell.card := by
    exact Finset.card_sdiff_add_card_eq_card hselectedSubsetCell
  have hremovedLeEighth :
      8 * (cell \ selected).card ≤ cell.card := by
    calc
      8 * (cell \ selected).card
          ≤ 8 * labelThresholdCapacity label threshold cell := by
            gcongr
      _ ≤ cell.card := by
        have hpositiveColor : 0 < colorCount := hcolorCount
        exact Nat.le_of_mul_le_mul_left
          (show colorCount *
              (8 * labelThresholdCapacity label threshold cell) ≤
              colorCount * cell.card by
            calc
              colorCount *
                    (8 * labelThresholdCapacity label threshold cell)
                  = 8 * colorCount *
                      labelThresholdCapacity label threshold cell := by ring
              _ ≤ vertices.card := hcapacityEight
              _ ≤ colorCount * cell.card := hverticesCard)
          hpositiveColor
  have hcellCardLe :
      cell.card ≤ 2 * selected.card := by
    omega
  have hverticesWeightUpper :
      (∑ i ∈ vertices, weight i) ≤
        (vertices.card : ENNReal) * (2 * c) := by
    calc
      (∑ i ∈ vertices, weight i)
          ≤ ∑ _i ∈ vertices, 2 * c :=
        Finset.sum_le_sum fun i hi => (hweight i hi).2
      _ = (vertices.card : ENNReal) * (2 * c) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hselectedWeightLower :
      (selected.card : ENNReal) * c ≤
        ∑ i ∈ selected, weight i := by
    calc
      (selected.card : ENNReal) * c
          = ∑ _i ∈ selected, c := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ selected, weight i :=
        Finset.sum_le_sum fun i hi =>
          (hweight i (hselectedSubset hi)).1
  have hweightTotal :
      (∑ i ∈ vertices, weight i) ≤
        (8 * colorCount : ℕ) *
          ∑ i ∈ selected, weight i := by
    calc
      (∑ i ∈ vertices, weight i)
          ≤ (vertices.card : ENNReal) * (2 * c) :=
        hverticesWeightUpper
      _ ≤ ((colorCount * cell.card : ℕ) : ENNReal) * (2 * c) := by
        gcongr
      _ ≤ ((colorCount * (2 * selected.card) : ℕ) : ENNReal) *
            (2 * c) := by
        gcongr
      _ = ((4 * colorCount : ℕ) : ENNReal) *
            ((selected.card : ENNReal) * c) := by
        push_cast
        ring
      _ ≤ ((4 * colorCount : ℕ) : ENNReal) *
            ∑ i ∈ selected, weight i := by
        gcongr
      _ ≤ ((8 * colorCount : ℕ) : ENNReal) *
            ∑ i ∈ selected, weight i := by
        gcongr
        norm_num
  have hlabelRetention :
      ∀ coordinate, ∀ value : Label coordinate,
        0 < (selected.filter fun i => label coordinate i = value).card →
          originalFiberCard coordinate value ≤
            denominator *
              ((selected.filter fun i =>
                label coordinate i = value).card + 1) := by
    intro coordinate value hactive
    have hthreshold :
        threshold coordinate value ≤
          (selected.filter fun i =>
            label coordinate i = value).card :=
      hselectedCore coordinate value hactive
    have hdiv :
        originalFiberCard coordinate value / denominator ≤
          (selected.filter fun i =>
            label coordinate i = value).card := by
      exact hthreshold
    have hbound :
        originalFiberCard coordinate value <
          denominator *
            ((selected.filter fun i =>
              label coordinate i = value).card + 1) := by
      calc
        originalFiberCard coordinate value
            < denominator *
                (originalFiberCard coordinate value / denominator + 1) :=
          Nat.lt_mul_div_succ _ hdenominator
        _ ≤ denominator *
              ((selected.filter fun i =>
                label coordinate i = value).card + 1) := by
          gcongr
    exact hbound.le
  refine
    ⟨selected, hselected, hselectedSubset, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [colorCount] using hweightTotal
  · intro k i hi i' hi'
    exact hparentBin k i (hselectedSubsetCell hi)
      i' (hselectedSubsetCell hi')
  · intro k i hi i' hi'
    exact hcomponentBin k i (hselectedSubsetCell hi)
      i' (hselectedSubsetCell hi')
  · intro k value hactive
    simpa [label] using hlabelRetention (Sum.inl k) value hactive
  · intro k value hactive
    simpa [label] using hlabelRetention (Sum.inr k) value hactive

end Kakeya.Streamlined

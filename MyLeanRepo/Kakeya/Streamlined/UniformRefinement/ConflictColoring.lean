import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Weighted conflict coloring

An explicit finite coloring of a conflict relation has a color class that is
conflict-free and retains at least the reciprocal number of colors of any
nonnegative weight.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/--
One color class of a finite coloring carries at least the average total
`ENNReal` weight.
-/
lemma exists_heavy_color_class
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (q : ℕ) (hq : 0 < q)
    (color : α → Fin q) (weight : α → ENNReal) :
    ∃ c : Fin q,
      (∑ i ∈ indices, weight i) ≤
        (q : ENNReal) *
          ∑ i ∈ indices.filter (fun i => color i = c), weight i := by
  classical
  let fiber (c : Fin q) : Finset α :=
    indices.filter fun i => color i = c
  let mass (c : Fin q) : ENNReal :=
    ∑ i ∈ fiber c, weight i

  have h_disjoint :
      ∀ c₁ ∈ (Finset.univ : Finset (Fin q)),
        ∀ c₂ ∈ (Finset.univ : Finset (Fin q)), c₁ ≠ c₂ →
          Disjoint (fiber c₁) (fiber c₂) := by
    intro c₁ _ c₂ _ hne
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    have hc₁ : color i = c₁ := (Finset.mem_filter.mp hi₁).2
    have hc₂ : color i = c₂ := (Finset.mem_filter.mp hi₂).2
    exact hne (hc₁.symm.trans hc₂)

  have h_union :
      (Finset.univ : Finset (Fin q)).biUnion fiber = indices := by
    ext i
    simp [fiber]

  have h_partition :
      ∑ c : Fin q, mass c = ∑ i ∈ indices, weight i := by
    have h_sum :
        ∑ c ∈ (Finset.univ : Finset (Fin q)),
            ∑ i ∈ fiber c, weight i =
          ∑ i ∈ (Finset.univ : Finset (Fin q)).biUnion fiber, weight i :=
      (Finset.sum_biUnion h_disjoint).symm
    simpa [mass, h_union] using h_sum

  have hcolors : (Finset.univ : Finset (Fin q)).Nonempty := by
    exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  rcases Finset.exists_max_image
      (Finset.univ : Finset (Fin q)) mass hcolors with
    ⟨c, _, hmax⟩

  have h_sum_le : ∑ d : Fin q, mass d ≤ ∑ _d : Fin q, mass c := by
    apply Finset.sum_le_sum
    intro d _
    exact hmax d (Finset.mem_univ d)
  have h_count : ∑ _d : Fin q, mass c = (q : ENNReal) * mass c := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  refine ⟨c, ?_⟩
  change (∑ i ∈ indices, weight i) ≤ (q : ENNReal) * mass c
  rw [← h_partition, ← h_count]
  exact h_sum_le

/--
If equal colors never conflict, one color class is conflict-free and retains
at least a `1 / q` fraction of the total weight, expressed without division.
-/
lemma exists_heavy_conflict_free_color_class
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (q : ℕ) (hq : 0 < q)
    (color : α → Fin q) (weight : α → ENNReal)
    (conflict : α → α → Prop)
    (hproper :
      ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
        conflict i j → color i ≠ color j) :
    ∃ c : Fin q,
      let selected := indices.filter fun i => color i = c
      selected ⊆ indices ∧
      (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬ conflict i j) ∧
      (∑ i ∈ indices, weight i) ≤
        (q : ENNReal) * ∑ i ∈ selected, weight i := by
  classical
  rcases exists_heavy_color_class indices q hq color weight with
    ⟨c, hmass⟩
  refine ⟨c, Finset.filter_subset _ _, ?_, hmass⟩
  intro i hi j hj hij hconflict
  have hi' : i ∈ indices := (Finset.mem_filter.mp hi).1
  have hj' : j ∈ indices := (Finset.mem_filter.mp hj).1
  have hci : color i = c := (Finset.mem_filter.mp hi).2
  have hcj : color j = c := (Finset.mem_filter.mp hj).2
  exact hproper i hi' j hj' hij hconflict (hci.trans hcj.symm)

/--
A symmetric conflict relation of degree at most `D` on a finite set admits a
proper coloring with `D + 1` colors.
-/
lemma exists_bounded_conflict_coloring
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (D : ℕ)
    (conflict : α → α → Prop) [DecidableRel conflict]
    (hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i)
    (hdegree :
      ∀ i ∈ indices,
        (indices.filter fun j => j ≠ i ∧ conflict i j).card ≤ D) :
    ∃ color : α → Fin (D + 1),
      ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
        conflict i j → color i ≠ color j := by
  classical
  induction indices using Finset.induction with
  | empty =>
      exact ⟨fun _ => ⟨0, Nat.succ_pos D⟩, by simp⟩
  | @insert a indices ha ih =>
      have hdegree_indices :
          ∀ i ∈ indices,
            (indices.filter fun j => j ≠ i ∧ conflict i j).card ≤ D := by
        intro i hi
        apply le_trans (Finset.card_le_card ?_) (hdegree i (Finset.mem_insert_of_mem hi))
        intro j hj
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_insert_of_mem hj.1, hj.2⟩
      rcases ih hdegree_indices with ⟨color, hproper⟩

      let neighbors := indices.filter fun j => conflict a j
      let used := neighbors.image color
      have hneighbors_card : neighbors.card ≤ D := by
        apply le_trans (Finset.card_le_card ?_) (hdegree a (Finset.mem_insert_self a indices))
        intro j hj
        have hj_indices : j ∈ indices := (Finset.mem_filter.mp hj).1
        have hja : j ≠ a := fun hja => ha (hja ▸ hj_indices)
        simp only [Finset.mem_filter]
        exact ⟨Finset.mem_insert_of_mem hj_indices, hja, (Finset.mem_filter.mp hj).2⟩
      have hused_card : used.card ≤ D :=
        (Finset.card_image_le.trans hneighbors_card)
      have hused_lt : used.card < (Finset.univ : Finset (Fin (D + 1))).card := by
        simpa using Nat.lt_succ_of_le hused_card
      rcases Finset.sdiff_nonempty_of_card_lt_card hused_lt with ⟨c, hc⟩
      have hc_unused : c ∉ used := (Finset.mem_sdiff.mp hc).2

      let newColor : α → Fin (D + 1) := fun i => if i = a then c else color i
      refine ⟨newColor, ?_⟩
      intro i hi j hj hij hconflict
      have hi_cases : i = a ∨ i ∈ indices := (Finset.mem_insert.mp hi)
      have hj_cases : j = a ∨ j ∈ indices := (Finset.mem_insert.mp hj)
      rcases hi_cases with rfl | hi_indices
      · have hj_indices : j ∈ indices := hj_cases.resolve_left hij.symm
        have hj_neighbor : j ∈ neighbors := by
          simp only [neighbors, Finset.mem_filter]
          exact ⟨hj_indices, hconflict⟩
        have hcolor_used : color j ∈ used := by
          exact Finset.mem_image.mpr ⟨j, hj_neighbor, rfl⟩
        simp only [newColor, if_pos, if_neg hij.symm]
        exact fun h => hc_unused (h ▸ hcolor_used)
      · rcases hj_cases with rfl | hj_indices
        · have hi_neighbor : i ∈ neighbors := by
            simp only [neighbors, Finset.mem_filter]
            exact ⟨hi_indices, hsymm hconflict⟩
          have hcolor_used : color i ∈ used := by
            exact Finset.mem_image.mpr ⟨i, hi_neighbor, rfl⟩
          simp only [newColor, if_neg hij, if_pos]
          exact fun h => hc_unused (h.symm ▸ hcolor_used)
        · simp only [newColor, if_neg (ne_of_mem_of_not_mem hi_indices ha),
            if_neg (ne_of_mem_of_not_mem hj_indices ha)]
          exact hproper i hi_indices j hj_indices hij hconflict

/--
From a symmetric degree-`D` conflict relation, select a conflict-free class
that retains at least a `1 / (D + 1)` fraction of the total `ENNReal` weight.
-/
lemma exists_heavy_bounded_conflict_free_class
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (D : ℕ)
    (weight : α → ENNReal) (conflict : α → α → Prop) [DecidableRel conflict]
    (hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i)
    (hdegree :
      ∀ i ∈ indices,
        (indices.filter fun j => j ≠ i ∧ conflict i j).card ≤ D) :
    ∃ selected : Finset α,
      selected ⊆ indices ∧
      (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬ conflict i j) ∧
      (∑ i ∈ indices, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) * ∑ i ∈ selected, weight i := by
  classical
  rcases exists_bounded_conflict_coloring indices D conflict hsymm hdegree with
    ⟨color, hproper⟩
  rcases exists_heavy_conflict_free_color_class
      indices (D + 1) (Nat.succ_pos D) color weight conflict hproper with
    ⟨c, hsubset, hfree, hmass⟩
  exact ⟨indices.filter fun i => color i = c, hsubset, hfree, hmass⟩

/--
A bounded-degree conflict relation has one conflict-free class that
simultaneously retains both cardinality and arbitrary `ENNReal` weight up to
the factor `D + 1`.

Start with a heavy color class and extend it to a maximal conflict-free
superset.  Weight can only increase, while maximality makes the selected set
dominating; its closed conflict neighborhoods cover all indices.
-/
lemma exists_bicriteria_bounded_conflict_free_class
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (D : ℕ)
    (weight : α → ENNReal) (conflict : α → α → Prop) [DecidableRel conflict]
    (hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i)
    (hdegree :
      ∀ i ∈ indices,
        (indices.filter fun j => j ≠ i ∧ conflict i j).card ≤ D) :
    ∃ selected : Finset α,
      selected ⊆ indices ∧
      (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬ conflict i j) ∧
      indices.card ≤ (D + 1) * selected.card ∧
      (∑ i ∈ indices, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) * ∑ i ∈ selected, weight i := by
  classical
  rcases exists_heavy_bounded_conflict_free_class
      indices D weight conflict hsymm hdegree with
    ⟨initial, hinitial_subset, hinitial_free, hinitial_mass⟩
  let IsFree : Finset α → Prop := fun selected =>
    ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬ conflict i j
  let candidates : Finset (Finset α) :=
    indices.powerset.filter fun selected =>
      initial ⊆ selected ∧ IsFree selected
  have hinitial_candidate : initial ∈ candidates := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hinitial_subset,
      Finset.Subset.rfl, hinitial_free⟩
  have hcandidates_nonempty : candidates.Nonempty :=
    ⟨initial, hinitial_candidate⟩
  rcases Finset.exists_max_image candidates Finset.card hcandidates_nonempty with
    ⟨selected, hselected_candidate, hselected_max⟩
  have hselected_data := Finset.mem_filter.mp hselected_candidate
  have hselected_subset : selected ⊆ indices :=
    Finset.mem_powerset.mp hselected_data.1
  have hinitial_selected : initial ⊆ selected := hselected_data.2.1
  have hselected_free : IsFree selected := hselected_data.2.2
  have hmaximal :
      ∀ i ∈ indices, i ∉ selected →
        ∃ j ∈ selected, i ≠ j ∧ conflict i j := by
    intro i hi_indices hi_not_selected
    by_contra h
    have hno_conflict :
        ∀ j ∈ selected, i ≠ j → ¬ conflict i j := by
      simpa only [not_exists, not_and] using h
    have hinsert_subset : insert i selected ⊆ indices := by
      intro j hj
      rw [Finset.mem_insert] at hj
      exact hj.elim (fun hji => hji ▸ hi_indices) (fun hj' => hselected_subset hj')
    have hinsert_free : IsFree (insert i selected) := by
      intro j hj k hk hjk hconflict
      rw [Finset.mem_insert] at hj hk
      rcases hj with rfl | hj_selected
      · have hk_selected : k ∈ selected := hk.resolve_left hjk.symm
        exact hno_conflict k hk_selected hjk hconflict
      · rcases hk with rfl | hk_selected
        · exact hno_conflict j hj_selected hjk.symm (hsymm hconflict)
        · exact hselected_free j hj_selected k hk_selected hjk hconflict
    have hinsert_candidate : insert i selected ∈ candidates := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr hinsert_subset, ?_, hinsert_free⟩
      exact hinitial_selected.trans (Finset.subset_insert i selected)
    have hcard_le : (insert i selected).card ≤ selected.card :=
      hselected_max (insert i selected) hinsert_candidate
    rw [Finset.card_insert_of_notMem hi_not_selected] at hcard_le
    omega
  let closedNeighborhood (j : α) : Finset α :=
    insert j (indices.filter fun i => i ≠ j ∧ conflict j i)
  have hclosed_card :
      ∀ j ∈ selected, (closedNeighborhood j).card ≤ D + 1 := by
    intro j hj
    have hj_indices : j ∈ indices := hselected_subset hj
    calc
      (closedNeighborhood j).card
          ≤ (indices.filter fun i => i ≠ j ∧ conflict j i).card + 1 := by
            simpa [closedNeighborhood, add_comm] using
              Finset.card_insert_le j
                (indices.filter fun i => i ≠ j ∧ conflict j i)
      _ ≤ D + 1 := Nat.add_le_add_right (hdegree j hj_indices) 1
  have hcover : indices ⊆ selected.biUnion closedNeighborhood := by
    intro i hi
    by_cases hi_selected : i ∈ selected
    · exact Finset.mem_biUnion.mpr
        ⟨i, hi_selected, Finset.mem_insert_self i _⟩
    · rcases hmaximal i hi hi_selected with ⟨j, hj, hij, hconflict⟩
      refine Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩
      rw [Finset.mem_insert]
      right
      rw [Finset.mem_filter]
      exact ⟨hi, hij, hsymm hconflict⟩
  have hcard :
      indices.card ≤ (D + 1) * selected.card := by
    calc
      indices.card ≤ (selected.biUnion closedNeighborhood).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ j ∈ selected, (closedNeighborhood j).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ selected, (D + 1) :=
        Finset.sum_le_sum hclosed_card
      _ = (D + 1) * selected.card := by
        simp [Finset.sum_const, mul_comm]
  have hweight_mono :
      (∑ i ∈ initial, weight i) ≤ ∑ i ∈ selected, weight i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hinitial_selected
    intro _ _ _
    positivity
  have hmass :
      (∑ i ∈ indices, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) * ∑ i ∈ selected, weight i := by
    exact hinitial_mass.trans (mul_le_mul_left' hweight_mono _)
  exact ⟨selected, hselected_subset, hselected_free, hcard, hmass⟩

/-- Complete output of a bicriteria maximal conflict-free selection.

The `dominates` field retains the maximality certificate used internally by
`exists_bicriteria_bounded_conflict_free_class`: every input index is either
selected or conflicts with a selected representative. -/
structure DominatingBicriteriaConflictFreePackage
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (D : ℕ)
    (weight : α → ENNReal) (conflict : α → α → Prop) where
  selected : Finset α
  selected_subset : selected ⊆ indices
  conflictFree :
    ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬ conflict i j
  cardinalityRetention :
    indices.card ≤ (D + 1) * selected.card
  weightRetention :
    (∑ i ∈ indices, weight i) ≤
      ((D + 1 : ℕ) : ENNReal) * ∑ i ∈ selected, weight i
  closedNeighborhood : α → Finset α
  closedNeighborhood_card :
    ∀ j ∈ selected, (closedNeighborhood j).card ≤ D + 1
  closedNeighborhood_spec :
    ∀ j ∈ selected,
      ∀ i ∈ closedNeighborhood j,
        i = j ∨ (i ∈ indices ∧ i ≠ j ∧ conflict j i)
  closedNeighborhood_cover :
    indices ⊆ selected.biUnion closedNeighborhood
  dominates :
    ∀ i ∈ indices,
      i ∈ selected ∨
        ∃ j ∈ selected, i ≠ j ∧ conflict i j

/-- A bounded-degree symmetric conflict relation admits one bicriteria
conflict-free selection together with its domination certificate. -/
theorem exists_dominating_bicriteria_bounded_conflict_free_class
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (D : ℕ)
    (weight : α → ENNReal) (conflict : α → α → Prop)
    [DecidableRel conflict]
    (hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i)
    (hdegree :
      ∀ i ∈ indices,
        (indices.filter fun j => j ≠ i ∧ conflict i j).card ≤ D) :
    Nonempty
      (DominatingBicriteriaConflictFreePackage
        indices D weight conflict) := by
  classical
  rcases exists_heavy_bounded_conflict_free_class
      indices D weight conflict hsymm hdegree with
    ⟨initial, hinitial_subset, hinitial_free, hinitial_mass⟩
  let IsFree : Finset α → Prop := fun selected =>
    ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬ conflict i j
  let candidates : Finset (Finset α) :=
    indices.powerset.filter fun selected =>
      initial ⊆ selected ∧ IsFree selected
  have hinitial_candidate : initial ∈ candidates := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hinitial_subset,
      Finset.Subset.rfl, hinitial_free⟩
  have hcandidates_nonempty : candidates.Nonempty :=
    ⟨initial, hinitial_candidate⟩
  rcases
      Finset.exists_max_image candidates Finset.card hcandidates_nonempty with
    ⟨selected, hselected_candidate, hselected_max⟩
  have hselected_data := Finset.mem_filter.mp hselected_candidate
  have hselected_subset : selected ⊆ indices :=
    Finset.mem_powerset.mp hselected_data.1
  have hinitial_selected : initial ⊆ selected := hselected_data.2.1
  have hselected_free : IsFree selected := hselected_data.2.2
  have hmaximal :
      ∀ i ∈ indices, i ∉ selected →
        ∃ j ∈ selected, i ≠ j ∧ conflict i j := by
    intro i hi_indices hi_not_selected
    by_contra h
    have hno_conflict :
        ∀ j ∈ selected, i ≠ j → ¬ conflict i j := by
      simpa only [not_exists, not_and] using h
    have hinsert_subset : insert i selected ⊆ indices := by
      intro j hj
      rw [Finset.mem_insert] at hj
      exact hj.elim
        (fun hji => hji ▸ hi_indices)
        (fun hj' => hselected_subset hj')
    have hinsert_free : IsFree (insert i selected) := by
      intro j hj k hk hjk hconflict
      rw [Finset.mem_insert] at hj hk
      rcases hj with rfl | hj_selected
      · have hk_selected : k ∈ selected := hk.resolve_left hjk.symm
        exact hno_conflict k hk_selected hjk hconflict
      · rcases hk with rfl | hk_selected
        · exact hno_conflict j hj_selected hjk.symm (hsymm hconflict)
        · exact hselected_free j hj_selected k hk_selected hjk hconflict
    have hinsert_candidate : insert i selected ∈ candidates := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr hinsert_subset, ?_, hinsert_free⟩
      exact hinitial_selected.trans (Finset.subset_insert i selected)
    have hcard_le : (insert i selected).card ≤ selected.card :=
      hselected_max (insert i selected) hinsert_candidate
    rw [Finset.card_insert_of_notMem hi_not_selected] at hcard_le
    omega
  let closedNeighborhood (j : α) : Finset α :=
    insert j (indices.filter fun i => i ≠ j ∧ conflict j i)
  have hclosed_card :
      ∀ j ∈ selected, (closedNeighborhood j).card ≤ D + 1 := by
    intro j hj
    have hj_indices : j ∈ indices := hselected_subset hj
    calc
      (closedNeighborhood j).card
          ≤ (indices.filter fun i => i ≠ j ∧ conflict j i).card + 1 := by
            simpa [closedNeighborhood, add_comm] using
              Finset.card_insert_le j
                (indices.filter fun i => i ≠ j ∧ conflict j i)
      _ ≤ D + 1 := Nat.add_le_add_right (hdegree j hj_indices) 1
  have hcover : indices ⊆ selected.biUnion closedNeighborhood := by
    intro i hi
    by_cases hi_selected : i ∈ selected
    · exact Finset.mem_biUnion.mpr
        ⟨i, hi_selected, Finset.mem_insert_self i _⟩
    · rcases hmaximal i hi hi_selected with ⟨j, hj, hij, hconflict⟩
      refine Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩
      rw [Finset.mem_insert]
      right
      rw [Finset.mem_filter]
      exact ⟨hi, hij, hsymm hconflict⟩
  have hcard :
      indices.card ≤ (D + 1) * selected.card := by
    calc
      indices.card ≤ (selected.biUnion closedNeighborhood).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ j ∈ selected, (closedNeighborhood j).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ selected, (D + 1) :=
        Finset.sum_le_sum hclosed_card
      _ = (D + 1) * selected.card := by
        simp [Finset.sum_const, mul_comm]
  have hweight_mono :
      (∑ i ∈ initial, weight i) ≤ ∑ i ∈ selected, weight i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hinitial_selected
    intro _ _ _
    positivity
  have hmass :
      (∑ i ∈ indices, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) * ∑ i ∈ selected, weight i :=
    hinitial_mass.trans (mul_le_mul_left' hweight_mono _)
  exact
    ⟨{
      selected := selected
      selected_subset := hselected_subset
      conflictFree := hselected_free
      cardinalityRetention := hcard
      weightRetention := hmass
      closedNeighborhood := closedNeighborhood
      closedNeighborhood_card := hclosed_card
      closedNeighborhood_spec := by
        intro j hj i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact Or.inl rfl
        · exact Or.inr (Finset.mem_filter.mp hi)
      closedNeighborhood_cover := hcover
      dominates := by
        intro i hi
        by_cases hisel : i ∈ selected
        · exact Or.inl hisel
        · exact Or.inr (hmaximal i hi hisel)
    }⟩

/--
If the conflict neighbors of each index admit an injective local code in a
fixed finite type, their number is bounded by the cardinality of that type.
-/
lemma local_conflict_degree_le_card
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (indices : Finset α) (conflict : α → α → Prop) [DecidableRel conflict]
    (localCode : α → α → β)
    (hcode :
      ∀ i ∈ indices,
        ∀ j ∈ indices, j ≠ i → conflict i j →
        ∀ k ∈ indices, k ≠ i → conflict i k →
          localCode i j = localCode i k → j = k) :
    ∀ i ∈ indices,
      (indices.filter fun j => j ≠ i ∧ conflict i j).card ≤ Fintype.card β := by
  classical
  intro i hi
  let neighbors := indices.filter fun j => j ≠ i ∧ conflict i j
  have hinjective : Set.InjOn (localCode i) neighbors := by
    intro j hj k hk heq
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    exact hcode i hi j hj'.1 hj'.2.1 hj'.2.2
      k hk'.1 hk'.2.1 hk'.2.2 heq
  calc
    neighbors.card = (neighbors.image (localCode i)).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ (Finset.univ : Finset β).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card β := Finset.card_univ

/--
An injective finite local code for every conflict neighborhood yields a
conflict-free class retaining at least the reciprocal code-space cardinality
plus one of the total weight.
-/
lemma exists_heavy_locally_encoded_conflict_free_class
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (indices : Finset α) (weight : α → ENNReal)
    (conflict : α → α → Prop) [DecidableRel conflict]
    (hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i)
    (localCode : α → α → β)
    (hcode :
      ∀ i ∈ indices,
        ∀ j ∈ indices, j ≠ i → conflict i j →
        ∀ k ∈ indices, k ≠ i → conflict i k →
          localCode i j = localCode i k → j = k) :
    ∃ selected : Finset α,
      selected ⊆ indices ∧
      (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬ conflict i j) ∧
      (∑ i ∈ indices, weight i) ≤
        ((Fintype.card β + 1 : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i := by
  apply exists_heavy_bounded_conflict_free_class
      indices (Fintype.card β) weight conflict hsymm
  exact local_conflict_degree_le_card indices conflict localCode hcode

end Kakeya.Streamlined

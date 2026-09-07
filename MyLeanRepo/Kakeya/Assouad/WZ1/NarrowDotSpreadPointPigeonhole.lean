import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadCountingHelpers

/-!
# Point-multiplicity pigeonhole for the narrow branch

Unlike `real_separated_or_concentrated`, this lemma partitions source points,
not only their image values.  It therefore retains multiplicity when many
different graph vertices have the same or nearby dot value.
-/

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

lemma point_separated_or_concentrated
    {α : Type*} [DecidableEq α]
    {source : Finset α} {value : α → ℝ}
    {delta lower upper K : ℝ}
    (hdelta : 0 < delta)
    (hbound : ∀ point ∈ source,
      lower ≤ value point ∧ value point ≤ upper)
    (hK : 0 < K)
    (hnonempty : source.Nonempty) :
    (∃ center : ℝ,
      K ≤
        (source.filter fun point =>
          |value point - center| ≤ delta).card) ∨
      ∃ selected : Finset α,
        selected ⊆ source ∧
        (∀ first ∈ selected, ∀ second ∈ selected,
          first ≠ second →
            2 * delta < |value first - value second|) ∧
        (source.card : ℝ) / (3 * K) ≤
          (selected.card : ℝ) := by
  classical
  let cellOf : α → ℕ :=
    fun point => Nat.floor ((value point - lower) / delta)
  let cellPoints : ℕ → Finset α :=
    fun index => source.filter (fun point => cellOf point = index)
  let nonemptyCells : Finset ℕ :=
    Finset.image cellOf source
  have hnonnegative :
      ∀ point ∈ source,
        0 ≤ (value point - lower) / delta := by
    intro point hpoint
    exact div_nonneg
      (sub_nonneg.mpr (hbound point hpoint).1) hdelta.le
  have hcell_bounds :
      ∀ point ∈ source,
        (cellOf point : ℝ) * delta ≤ value point - lower ∧
          value point - lower <
            ((cellOf point : ℝ) + 1) * delta := by
    intro point hpoint
    constructor
    · have hfloor :
          (cellOf point : ℝ) ≤
            (value point - lower) / delta :=
        Nat.floor_le (hnonnegative point hpoint)
      calc
        (cellOf point : ℝ) * delta
            ≤ ((value point - lower) / delta) * delta := by
          gcongr
        _ = value point - lower := by
          field_simp [hdelta.ne']
    · have hfloor :
          (value point - lower) / delta <
            (cellOf point : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      calc
        value point - lower =
            ((value point - lower) / delta) * delta := by
          field_simp [hdelta.ne']
        _ < ((cellOf point : ℝ) + 1) * delta := by
          gcongr
  have hcell_nonempty :
      ∀ index ∈ nonemptyCells,
        (cellPoints index).Nonempty := by
    intro index hindex
    rcases Finset.mem_image.mp hindex with
      ⟨point, hpoint, rfl⟩
    exact
      ⟨point, Finset.mem_filter.mpr ⟨hpoint, rfl⟩⟩
  have hdisjoint :
      Set.PairwiseDisjoint
        (nonemptyCells : Set ℕ) cellPoints := by
    intro first _ second _ hne
    simp only [Finset.disjoint_left]
    intro point hfirst hsecond
    have hfirst_cell :
        cellOf point = first :=
      (Finset.mem_filter.mp hfirst).2
    have hsecond_cell :
        cellOf point = second :=
      (Finset.mem_filter.mp hsecond).2
    exact hne (hfirst_cell.symm.trans hsecond_cell)
  have hpartition :
      source.card =
        ∑ index ∈ nonemptyCells,
          (cellPoints index).card := by
    have hunion :
        source = nonemptyCells.biUnion cellPoints := by
      ext point
      simp only [nonemptyCells, cellPoints,
        Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
      constructor
      · intro hpoint
        exact
          ⟨cellOf point, ⟨point, hpoint, rfl⟩,
            hpoint, rfl⟩
      · rintro ⟨_, ⟨_, _, _⟩, hpoint, _⟩
        exact hpoint
    rw [hunion, Finset.card_biUnion hdisjoint]
  by_cases hconcentrated :
      ∃ index ∈ nonemptyCells,
        K ≤ (cellPoints index).card
  · rcases hconcentrated with
      ⟨index, _, hcardinality⟩
    let center : ℝ :=
      lower + (index : ℝ) * delta + delta / 2
    have hsubset :
        cellPoints index ⊆
          source.filter fun point =>
            |value point - center| ≤ delta := by
      intro point hpoint
      have hpoint_source :=
        (Finset.mem_filter.mp hpoint).1
      have hindex :
          cellOf point = index :=
        (Finset.mem_filter.mp hpoint).2
      have hb := hcell_bounds point hpoint_source
      rw [hindex] at hb
      have hdistance :
          |value point - center| ≤ delta := by
        have heq :
            value point - center =
              (value point - lower) -
                (index : ℝ) * delta - delta / 2 := by
          dsimp only [center]
          ring
        rw [heq]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact
        Finset.mem_filter.mpr
          ⟨hpoint_source, hdistance⟩
    exact Or.inl
      ⟨center,
        hcardinality.trans
          (by
            exact_mod_cast
              Finset.card_le_card hsubset)⟩
  · have hsmall :
        ∀ index ∈ nonemptyCells,
          ((cellPoints index).card : ℝ) < K := by
      intro index hindex
      by_contra hnot
      exact hconcentrated
        ⟨index, hindex, by linarith⟩
    have hcells_nonempty : nonemptyCells.Nonempty :=
      Finset.Nonempty.image hnonempty cellOf
    have hsum :
        (source.card : ℝ) <
          (nonemptyCells.card : ℝ) * K := by
      have hsum_lt :
          (∑ index ∈ nonemptyCells,
              (cellPoints index).card : ℝ) <
            ∑ _index ∈ nonemptyCells, K := by
        apply Finset.sum_lt_sum_of_nonempty hcells_nonempty
        intro index hindex
        exact hsmall index hindex
      have hcard_eq :
          (source.card : ℝ) =
            (∑ index ∈ nonemptyCells,
              (cellPoints index).card : ℝ) := by
        exact_mod_cast hpartition
      simpa [hcard_eq, Finset.sum_const, mul_comm] using hsum_lt
    let residueCells : ℕ → Finset ℕ :=
      fun residue =>
        nonemptyCells.filter fun index =>
          index % 3 = residue
    have hresidue_disjoint :
        ∀ first second : ℕ, first ≠ second →
          Disjoint (residueCells first) (residueCells second) := by
      intro first second hne
      simp [residueCells, Finset.disjoint_left]
      omega
    have hresidue_union :
        nonemptyCells =
          residueCells 0 ∪ residueCells 1 ∪ residueCells 2 := by
      ext index
      simp only [residueCells, Finset.mem_filter, Finset.mem_union]
      have hmod :
          index % 3 = 0 ∨ index % 3 = 1 ∨ index % 3 = 2 := by
        have hlt : index % 3 < 3 :=
          Nat.mod_lt index (by norm_num)
        interval_cases hvalue : index % 3 <;> tauto
      tauto
    have hresidue_card :
        nonemptyCells.card =
          (residueCells 0).card +
            (residueCells 1).card +
            (residueCells 2).card := by
      rw [hresidue_union]
      have h01 :
          Disjoint (residueCells 0) (residueCells 1) :=
        hresidue_disjoint 0 1 (by norm_num)
      have h02 :
          Disjoint (residueCells 0) (residueCells 2) :=
        hresidue_disjoint 0 2 (by norm_num)
      have h12 :
          Disjoint (residueCells 1) (residueCells 2) :=
        hresidue_disjoint 1 2 (by norm_num)
      rw [Finset.card_union_of_disjoint
        (by
          simpa [Finset.disjoint_union_left] using
            And.intro h02 h12)]
      rw [Finset.card_union_of_disjoint h01]
    have hlarge_residue :
        ∃ residue : ℕ, residue < 3 ∧
          (nonemptyCells.card : ℝ) ≤
            3 * (residueCells residue).card := by
      by_cases hzero :
          (nonemptyCells.card : ℝ) ≤
            3 * (residueCells 0).card
      · exact ⟨0, by norm_num, hzero⟩
      · by_cases hone :
            (nonemptyCells.card : ℝ) ≤
              3 * (residueCells 1).card
        · exact ⟨1, by norm_num, hone⟩
        · by_cases htwo :
              (nonemptyCells.card : ℝ) ≤
                3 * (residueCells 2).card
          · exact ⟨2, by norm_num, htwo⟩
          · have hcard_eq :
                (nonemptyCells.card : ℝ) =
                  ((residueCells 0).card +
                    (residueCells 1).card +
                    (residueCells 2).card : ℝ) := by
              exact_mod_cast hresidue_card
            rw [hcard_eq] at hzero hone htwo
            push Not at hzero hone htwo
            linarith
    rcases hlarge_residue with
      ⟨residue, _, hresidue_bound⟩
    let selectedCells := residueCells residue
    have hselected_cells :
        selectedCells ⊆ nonemptyCells := by
      intro index hindex
      exact (Finset.mem_filter.mp hindex).1
    let pickPoint (index : ℕ) : α :=
      if h : index ∈ nonemptyCells then
        Classical.choose (hcell_nonempty index h)
      else Classical.choose hnonempty
    let selected : Finset α :=
      selectedCells.image pickPoint
    have hpick :
        ∀ index ∈ selectedCells,
          pickPoint index ∈ cellPoints index := by
      intro index hindex
      have hcell : index ∈ nonemptyCells :=
        hselected_cells hindex
      have heq :
          pickPoint index =
            Classical.choose (hcell_nonempty index hcell) := by
        dsimp only [pickPoint]
        rw [dif_pos hcell]
      rw [heq]
      exact Classical.choose_spec (hcell_nonempty index hcell)
    have hselected_source : selected ⊆ source := by
      intro point hpoint
      rcases Finset.mem_image.mp hpoint with
        ⟨index, hindex, rfl⟩
      exact (Finset.mem_filter.mp (hpick index hindex)).1
    have hcell_separation :
        ∀ first ∈ selectedCells,
          ∀ second ∈ selectedCells,
            first ≠ second →
              2 * delta <
                |value (pickPoint first) -
                  value (pickPoint second)| := by
      intro first hfirst second hsecond hne
      have hfirst_source :
          pickPoint first ∈ source :=
        (Finset.mem_filter.mp (hpick first hfirst)).1
      have hsecond_source :
          pickPoint second ∈ source :=
        (Finset.mem_filter.mp (hpick second hsecond)).1
      have hfirst_index :
          cellOf (pickPoint first) = first :=
        (Finset.mem_filter.mp (hpick first hfirst)).2
      have hsecond_index :
          cellOf (pickPoint second) = second :=
        (Finset.mem_filter.mp (hpick second hsecond)).2
      have hfirst_bounds :=
        hcell_bounds (pickPoint first) hfirst_source
      have hsecond_bounds :=
        hcell_bounds (pickPoint second) hsecond_source
      rw [hfirst_index] at hfirst_bounds
      rw [hsecond_index] at hsecond_bounds
      by_cases horder : first < second
      · have hgap : second ≥ first + 3 := by
          have hfirst_mod :
              first % 3 = residue :=
            (Finset.mem_filter.mp hfirst).2
          have hsecond_mod :
              second % 3 = residue :=
            (Finset.mem_filter.mp hsecond).2
          omega
        have hgap_real :
            (second : ℝ) ≥ (first : ℝ) + 3 := by
          exact_mod_cast hgap
        have hdifference :
            value (pickPoint second) -
                value (pickPoint first) >
              2 * delta := by
          nlinarith [hfirst_bounds.2, hsecond_bounds.1]
        rw [show
          value (pickPoint first) -
              value (pickPoint second) =
            -(value (pickPoint second) -
              value (pickPoint first)) by ring]
        rw [abs_neg, abs_of_pos (by linarith)]
        exact hdifference
      · have horder' : second < first := by omega
        have hgap : first ≥ second + 3 := by
          have hfirst_mod :
              first % 3 = residue :=
            (Finset.mem_filter.mp hfirst).2
          have hsecond_mod :
              second % 3 = residue :=
            (Finset.mem_filter.mp hsecond).2
          omega
        have hgap_real :
            (first : ℝ) ≥ (second : ℝ) + 3 := by
          exact_mod_cast hgap
        have hdifference :
            value (pickPoint first) -
                value (pickPoint second) >
              2 * delta := by
          nlinarith [hfirst_bounds.1, hsecond_bounds.2]
        rw [abs_of_pos (by linarith)]
        exact hdifference
    have hinjective :
        Set.InjOn pickPoint (selectedCells : Set ℕ) := by
      intro first hfirst second hsecond heq
      by_contra hne
      have hsep :=
        hcell_separation first hfirst second hsecond hne
      rw [heq] at hsep
      simp only [sub_self, abs_zero] at hsep
      linarith
    have hselected_card :
        selected.card = selectedCells.card :=
      Finset.card_image_of_injOn hinjective
    have hseparated :
        ∀ first ∈ selected, ∀ second ∈ selected,
          first ≠ second →
            2 * delta < |value first - value second| := by
      intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with
        ⟨firstIndex, hfirstIndex, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondIndex, hsecondIndex, rfl⟩
      apply hcell_separation firstIndex hfirstIndex
        secondIndex hsecondIndex
      intro heq
      exact hne (congrArg pickPoint heq)
    have hcardinality :
        (source.card : ℝ) / (3 * K) ≤
          (selected.card : ℝ) := by
      rw [hselected_card]
      have hcells_lower :
          (source.card : ℝ) / K ≤
            (nonemptyCells.card : ℝ) := by
        by_contra hnot
        have hstrict :
            (nonemptyCells.card : ℝ) <
              (source.card : ℝ) / K := by
          linarith
        have hproduct :
            (nonemptyCells.card : ℝ) * K <
              (source.card : ℝ) := by
          calc
            (nonemptyCells.card : ℝ) * K
                < ((source.card : ℝ) / K) * K := by
              gcongr
            _ = source.card := div_mul_cancel₀ _ hK.ne'
        linarith
      calc
        (source.card : ℝ) / (3 * K) =
            ((source.card : ℝ) / K) / 3 := by ring
        _ ≤ (nonemptyCells.card : ℝ) / 3 := by
          gcongr
        _ ≤ (selectedCells.card : ℝ) := by
          exact
            (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
              (by simpa [mul_comm] using hresidue_bound)
    exact
      Or.inr
        ⟨selected, hselected_source,
          hseparated, hcardinality⟩

end Kakeya.Assouad

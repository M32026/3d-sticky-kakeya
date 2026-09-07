import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadGeometricLemmas
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9NarrowSplitStatements

/-!
# Counting helpers for the narrow branch of WZ1 Proposition 8.9

This module contains the finite counting input for the remaining coupled
narrow-dot-spread argument: Frostman cardinality lower bounds, second- and
third-coordinate fiber bounds, a real separated-or-concentrated dichotomy,
and monotonicity of the two possible outputs.
-/

namespace Kakeya.Assouad

open scoped ENNReal

noncomputable section

/-- Frostman at scale `delta` and nonemptiness force a cardinality lower bound. -/
lemma frostman_delta_separated_card_lower
    {A : DiscreteSet 2} {delta C : ℝ}
    (_hsep : A.IsDeltaSeparated delta)
    (hfrost : A.IsFrostman delta 1 (ENNReal.ofReal C))
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (_hC : 0 < C)
    (hnonempty : A.Nonempty) :
    (1 : ENNReal) ≤
      ENNReal.ofReal C * ENNReal.ofReal delta * A.enncard := by
  rcases hnonempty with ⟨point, hpoint⟩
  have hpoint_ball :
      point ∈ A.filter fun candidate : Point2 =>
        dist candidate point ≤ delta := by
    simp only [Finset.mem_filter, hpoint, true_and, dist_self]
    linarith
  have hball_nonempty :
      (A.filter fun candidate : Point2 =>
        dist candidate point ≤ delta).Nonempty :=
    ⟨point, hpoint_ball⟩
  have hone : (1 : ENNReal) ≤ A.ballCount point delta := by
    simp [DiscreteSet.ballCount, hball_nonempty]
  have hfrost_bound :
      A.ballCount point delta ≤
        ENNReal.ofReal C *
          Kakeya.realRpowENN delta 1 * A.enncard :=
    hfrost point delta le_rfl hdelta1
  have hrpow :
      Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
    simp [Kakeya.realRpowENN]
  rw [hrpow] at hfrost_bound
  exact hone.trans hfrost_bound

/-- Uniform density gives the second-coordinate fiber lower bound. -/
lemma fiber_size_lower_bound
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density : ENNReal}
    (hdensity : WZ1UniformTripleDensity density F G₁ G₂ H)
    {first second third : Point2}
    (hedge : (first, second, third) ∈ H) :
    ((kaufmanSecondFiber H first third).card : ENNReal) ≥
      density * G₁.enncard :=
  uniform_density_second_fiber_bound
    hdensity (first, second, third) hedge

/--
Membership in the projected second-coordinate fiber retains an actual source
edge with the fixed first and third coordinates.
-/
lemma kaufmanSecondFiber_actual_edge
    {H : Finset (Point2 × Point2 × Point2)}
    {first second third : Point2}
    (hsecond : second ∈ kaufmanSecondFiber H first third) :
    (first, second, third) ∈ H := by
  rcases Finset.mem_image.mp hsecond with
    ⟨edge, hedge, hedgeSecond⟩
  have hedgeH : edge ∈ H :=
    (Finset.mem_filter.mp hedge).1
  have hedgeFirst : edge.1 = first :=
    (Finset.mem_filter.mp hedge).2.1
  have hedgeThird : edge.2.2 = third :=
    (Finset.mem_filter.mp hedge).2.2
  have hedgeTuple :
      edge = (first, second, third) := by
    exact Prod.ext hedgeFirst
      (Prod.ext hedgeSecond hedgeThird)
  rw [← hedgeTuple]
  exact hedgeH

/-- The dot-difference value of an edge belongs to its graph's dot set. -/
lemma dot_value_mem
    {H : Finset (Point2 × Point2 × Point2)}
    {first second third : Point2}
    (hedge : (first, second, third) ∈ H) :
    inner ℝ first (second - third) ∈ wz1DotDifferenceSet H := by
  simp only [wz1DotDifferenceSet, Finset.mem_coe, Finset.mem_image]
  exact ⟨(first, second, third), hedge, rfl⟩

/--
For finite real values in one interval, either one radius-`delta` interval
contains at least `K` values, or a `2 * delta`-separated subset retains at
least `values.card / (3 * K)` values.
-/
lemma real_separated_or_concentrated
    {values : Finset ℝ} {delta lower upper K : ℝ}
    (hdelta : 0 < delta)
    (hbound : ∀ value ∈ values, lower ≤ value ∧ value ≤ upper)
    (hK : 0 < K)
    (hnonempty : values.Nonempty) :
    (∃ center : ℝ,
      K ≤
        (values.filter fun value =>
          |value - center| ≤ delta).card) ∨
      ∃ selected : Finset ℝ,
        selected ⊆ values ∧
        (∀ first ∈ selected, ∀ second ∈ selected,
          first ≠ second →
            2 * delta < |first - second|) ∧
        (values.card : ℝ) / (3 * K) ≤
          (selected.card : ℝ) := by
  classical
  let cellOf : ℝ → ℕ :=
    fun value => Nat.floor ((value - lower) / delta)
  let cellPoints : ℕ → Finset ℝ :=
    fun index => values.filter (fun value => cellOf value = index)
  let nonemptyCells : Finset ℕ := Finset.image cellOf values
  have hnonnegative :
      ∀ value ∈ values, 0 ≤ (value - lower) / delta := by
    intro value hvalue
    exact div_nonneg (sub_nonneg.mpr (hbound value hvalue).1) hdelta.le
  have hcell_bounds :
      ∀ value ∈ values,
        (cellOf value : ℝ) * delta ≤ value - lower ∧
          value - lower <
            ((cellOf value : ℝ) + 1) * delta := by
    intro value hvalue
    constructor
    · have hfloor :
          (cellOf value : ℝ) ≤
            (value - lower) / delta :=
        Nat.floor_le (hnonnegative value hvalue)
      calc
        (cellOf value : ℝ) * delta
            ≤ ((value - lower) / delta) * delta := by
          gcongr
        _ = value - lower := by
          field_simp [hdelta.ne']
    · have hfloor :
          (value - lower) / delta <
            (cellOf value : ℝ) + 1 :=
        Nat.lt_floor_add_one ((value - lower) / delta)
      calc
        value - lower =
            ((value - lower) / delta) * delta := by
          field_simp [hdelta.ne']
        _ < ((cellOf value : ℝ) + 1) * delta := by
          gcongr
  have hcell_nonempty :
      ∀ index ∈ nonemptyCells, (cellPoints index).Nonempty := by
    intro index hindex
    rcases Finset.mem_image.mp hindex with
      ⟨value, hvalue, rfl⟩
    exact
      ⟨value, Finset.mem_filter.mpr ⟨hvalue, rfl⟩⟩
  have hdisjoint :
      Set.PairwiseDisjoint
        (nonemptyCells : Set ℕ) cellPoints := by
    intro first _ second _ hne
    simp only [Finset.disjoint_left]
    intro value hfirst hsecond
    have hfirst_cell :
        cellOf value = first :=
      (Finset.mem_filter.mp hfirst).2
    have hsecond_cell :
        cellOf value = second :=
      (Finset.mem_filter.mp hsecond).2
    exact hne (hfirst_cell.symm.trans hsecond_cell)
  have hpartition :
      values.card =
        ∑ index ∈ nonemptyCells, (cellPoints index).card := by
    have hunion :
        values = nonemptyCells.biUnion cellPoints := by
      ext value
      simp only [nonemptyCells, cellPoints, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image]
      constructor
      · intro hvalue
        exact ⟨cellOf value, ⟨value, hvalue, rfl⟩, hvalue, rfl⟩
      · rintro ⟨_, ⟨_, _, _⟩, hvalue, _⟩
        exact hvalue
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
          values.filter fun value =>
            |value - center| ≤ delta := by
      intro value hvalue
      have hvalue_mem :
          value ∈ values :=
        (Finset.mem_filter.mp hvalue).1
      have hindex :
          cellOf value = index :=
        (Finset.mem_filter.mp hvalue).2
      have hb := hcell_bounds value hvalue_mem
      rw [hindex] at hb
      have hdistance :
          |value - center| ≤ delta := by
        have heq :
            value - center =
              (value - lower) -
                (index : ℝ) * delta - delta / 2 := by
          dsimp only [center]
          ring
        rw [heq]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact
        Finset.mem_filter.mpr
          ⟨hvalue_mem, hdistance⟩
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
        (values.card : ℝ) <
          (nonemptyCells.card : ℝ) * K := by
      have hsum_lt :
          (∑ index ∈ nonemptyCells,
              (cellPoints index).card : ℝ) <
            ∑ _index ∈ nonemptyCells, K := by
        apply Finset.sum_lt_sum_of_nonempty hcells_nonempty
        intro index hindex
        exact hsmall index hindex
      have hcard_eq :
          (values.card : ℝ) =
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
          index % 3 = 0 ∨
            index % 3 = 1 ∨
            index % 3 = 2 := by
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
        (by simpa [Finset.disjoint_union_left] using And.intro h02 h12)]
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
    let pickPoint (index : ℕ) : ℝ :=
      if h : index ∈ nonemptyCells then
        (cellPoints index).min' (hcell_nonempty index h)
      else 0
    let selected : Finset ℝ :=
      selectedCells.image pickPoint
    have hpick :
        ∀ index ∈ selectedCells,
          pickPoint index ∈ cellPoints index := by
      intro index hindex
      have hcell : index ∈ nonemptyCells :=
        hselected_cells hindex
      dsimp only [pickPoint]
      rw [dif_pos hcell]
      exact
        Finset.min'_mem
          (cellPoints index) (hcell_nonempty index hcell)
    have hselected_values : selected ⊆ values := by
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with
        ⟨index, hindex, rfl⟩
      exact (Finset.mem_filter.mp (hpick index hindex)).1
    have hcell_separation :
        ∀ first ∈ selectedCells,
          ∀ second ∈ selectedCells,
            first ≠ second →
              2 * delta <
                |pickPoint first - pickPoint second| := by
      intro first hfirst second hsecond hne
      have hfirst_mem :
          pickPoint first ∈ values :=
        (Finset.mem_filter.mp (hpick first hfirst)).1
      have hsecond_mem :
          pickPoint second ∈ values :=
        (Finset.mem_filter.mp (hpick second hsecond)).1
      have hfirst_index :
          cellOf (pickPoint first) = first :=
        (Finset.mem_filter.mp (hpick first hfirst)).2
      have hsecond_index :
          cellOf (pickPoint second) = second :=
        (Finset.mem_filter.mp (hpick second hsecond)).2
      have hfirst_bounds :=
        hcell_bounds (pickPoint first) hfirst_mem
      have hsecond_bounds :=
        hcell_bounds (pickPoint second) hsecond_mem
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
            pickPoint second - pickPoint first >
              2 * delta := by
          nlinarith [hfirst_bounds.2, hsecond_bounds.1]
        rw [show
          pickPoint first - pickPoint second =
            -(pickPoint second - pickPoint first) by ring]
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
            pickPoint first - pickPoint second >
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
            2 * delta < |first - second| := by
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
        (values.card : ℝ) / (3 * K) ≤
          (selected.card : ℝ) := by
      rw [hselected_card]
      have hcells_lower :
          (values.card : ℝ) / K ≤
            (nonemptyCells.card : ℝ) := by
        by_contra hnot
        have hstrict :
            (nonemptyCells.card : ℝ) <
              (values.card : ℝ) / K := by
          linarith
        have hproduct :
            (nonemptyCells.card : ℝ) * K <
              (values.card : ℝ) := by
          calc
            (nonemptyCells.card : ℝ) * K
                < ((values.card : ℝ) / K) * K := by
              gcongr
            _ = values.card := div_mul_cancel₀ _ hK.ne'
        linarith
      calc
        (values.card : ℝ) / (3 * K) =
            ((values.card : ℝ) / K) / 3 := by ring
        _ ≤ (nonemptyCells.card : ℝ) / 3 := by
          gcongr
        _ ≤ (selectedCells.card : ℝ) := by
          exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
            (by simpa [mul_comm] using hresidue_bound)
    exact
      Or.inr
        ⟨selected, hselected_values,
          hseparated, hcardinality⟩

/-- Frostman with constant `delta⁻workingLambda` gives polynomial cardinality. -/
lemma frostman_workinglambda_lower_bound
    {A : DiscreteSet 2} {delta workingLambda : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (_hworking_pos : 0 < workingLambda)
    (_hworking_one : workingLambda < 1)
    (hsep : A.IsDeltaSeparated delta)
    (hfrost : A.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-workingLambda)))
    (hnonempty : A.Nonempty) :
    A.enncard ≥
      Kakeya.realRpowENN delta (workingLambda - 1) := by
  let C : ℝ := Real.rpow delta (-workingLambda)
  have hC : 0 < C := Real.rpow_pos_of_pos hdelta _
  have hone :
      (1 : ENNReal) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal delta * A.enncard :=
    frostman_delta_separated_card_lower
      hsep hfrost hdelta hdelta1 hC hnonempty
  have hC_eq :
      ENNReal.ofReal C =
        Kakeya.realRpowENN delta (-workingLambda) := rfl
  have hdelta_eq :
      ENNReal.ofReal delta =
        Kakeya.realRpowENN delta 1 := by
    simp [Kakeya.realRpowENN]
  rw [hC_eq, hdelta_eq] at hone
  have hrpow_mul :
      Kakeya.realRpowENN delta (-workingLambda) *
          Kakeya.realRpowENN delta 1 =
        Kakeya.realRpowENN delta (1 - workingLambda) := by
    simp only [Kakeya.realRpowENN]
    have hreal :
        Real.rpow delta (-workingLambda) *
            Real.rpow delta 1 =
          Real.rpow delta (1 - workingLambda) := by
      have h :=
        Real.rpow_add hdelta (-workingLambda) 1
      have hexponent :
          (-workingLambda) + 1 =
            1 - workingLambda := by ring
      rw [hexponent] at h
      exact h.symm
    have hnonnegative :
        0 ≤ Real.rpow delta (-workingLambda) := by
      positivity
    rw [← ENNReal.ofReal_mul hnonnegative, hreal]
  rw [hrpow_mul] at hone
  let factor : ENNReal :=
    Kakeya.realRpowENN delta (1 - workingLambda)
  have hdivide :
      (1 : ENNReal) / factor ≤ A.enncard :=
    ENNReal.div_le_of_le_mul' hone
  have hfactor_inv :
      (1 : ENNReal) / factor =
        Kakeya.realRpowENN delta (workingLambda - 1) := by
    have hpositive :
        0 < Real.rpow delta (1 - workingLambda) :=
      Real.rpow_pos_of_pos hdelta _
    have hinverse :
        (Real.rpow delta (1 - workingLambda))⁻¹ =
          Real.rpow delta (workingLambda - 1) := by
      have hproduct :
          Real.rpow delta (1 - workingLambda) *
              Real.rpow delta (workingLambda - 1) =
            1 := by
        have hadd :=
          Real.rpow_add hdelta
            (1 - workingLambda)
            (workingLambda - 1)
        have hsum :
            (1 - workingLambda) +
                (workingLambda - 1) =
              0 := by ring
        rw [hsum] at hadd
        simpa using hadd.symm
      exact inv_eq_of_mul_eq_one_right hproduct
    simp only [factor, Kakeya.realRpowENN, one_div]
    rw [← ENNReal.ofReal_inv_of_pos hpositive, hinverse]
  rw [hfactor_inv] at hdivide
  exact hdivide

/-- The third-coordinate fiber over fixed first and second coordinates. -/
def kaufmanThirdFiber
    (H : Finset (Point2 × Point2 × Point2))
    (first second : Point2) : Finset Point2 :=
  (H.filter fun edge =>
      edge.1 = first ∧ edge.2.1 = second).image
    fun edge => edge.2.2

/-- Uniform density gives the third-coordinate fiber lower bound. -/
lemma uniform_density_third_fiber_bound
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density : ENNReal}
    (hdensity : WZ1UniformTripleDensity density F G₁ G₂ H)
    (edge : Point2 × Point2 × Point2) (hedge : edge ∈ H) :
    ((kaufmanThirdFiber H edge.1 edge.2.1).card : ENNReal) ≥
      density * G₂.enncard := by
  let encoded : Fin 3 → Point2 := wz1TripleCoordinate edge
  have hencoded : encoded ∈ wz1EncodeTriples H :=
    Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  let fixed : Finset (Fin 3) := {0, 1}
  have hfiber := hdensity.2.2 encoded hencoded fixed
  have hcomplement :
      (Finset.univ : Finset (Fin 3)) \ fixed = {2} := by
    decide
  have hproduct :
      wz1VertexCardProduct
          (wz1TripleVertexClasses F G₁ G₂) ({2} : Finset (Fin 3)) =
        G₂.enncard := by
    simp [wz1VertexCardProduct, wz1TripleVertexClasses] <;> rfl
  rw [hcomplement, hproduct] at hfiber
  let hypergraphFiber :=
    wz1HypergraphFiber (wz1EncodeTriples H) fixed encoded
  let projectThird : (Fin 3 → Point2) → Point2 :=
    fun current => current 2
  have hmaps :
      ∀ current ∈ hypergraphFiber,
        projectThird current ∈
          kaufmanThirdFiber H edge.1 edge.2.1 := by
    intro current hcurrent
    have hgraph :
        current ∈ wz1EncodeTriples H :=
      (Finset.mem_filter.mp hcurrent).1
    have hfixed :
        ∀ index ∈ fixed,
          current index = encoded index :=
      (Finset.mem_filter.mp hcurrent).2
    rcases Finset.mem_image.mp hgraph with
      ⟨source, hsource, rfl⟩
    have hfirst : source.1 = edge.1 :=
      hfixed 0 (by simp [fixed])
    have hsecond : source.2.1 = edge.2.1 :=
      hfixed 1 (by simp [fixed])
    exact
      Finset.mem_image.mpr
        ⟨source,
          Finset.mem_filter.mpr
            ⟨hsource, hfirst, hsecond⟩,
          rfl⟩
  have hinjective :
      Set.InjOn projectThird
        (hypergraphFiber : Set (Fin 3 → Point2)) := by
    intro first hfirst second hsecond heq
    have hfirst_fixed :
        ∀ index ∈ fixed,
          first index = encoded index :=
      (Finset.mem_filter.mp hfirst).2
    have hsecond_fixed :
        ∀ index ∈ fixed,
          second index = encoded index :=
      (Finset.mem_filter.mp hsecond).2
    funext index
    fin_cases index
    · exact
        (hfirst_fixed 0 (by simp [fixed])).trans
          (hsecond_fixed 0 (by simp [fixed])).symm
    · exact
        (hfirst_fixed 1 (by simp [fixed])).trans
          (hsecond_fixed 1 (by simp [fixed])).symm
    · exact heq
  have himage :
      hypergraphFiber.image projectThird ⊆
        kaufmanThirdFiber H edge.1 edge.2.1 := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨current, hcurrent, rfl⟩
    exact hmaps current hcurrent
  have hcard :
      hypergraphFiber.card ≤
        (kaufmanThirdFiber H edge.1 edge.2.1).card := by
    rw [← Finset.card_image_of_injOn hinjective]
    exact Finset.card_le_card himage
  exact hfiber.trans (by exact_mod_cast hcard)

/--
Membership in the projected third-coordinate fiber retains an actual source
edge with the fixed first and second coordinates.
-/
lemma kaufmanThirdFiber_actual_edge
    {H : Finset (Point2 × Point2 × Point2)}
    {first second third : Point2}
    (hthird : third ∈ kaufmanThirdFiber H first second) :
    (first, second, third) ∈ H := by
  rcases Finset.mem_image.mp hthird with
    ⟨edge, hedge, hedgeThird⟩
  have hedgeH : edge ∈ H :=
    (Finset.mem_filter.mp hedge).1
  have hedgeFirst : edge.1 = first :=
    (Finset.mem_filter.mp hedge).2.1
  have hedgeSecond : edge.2.1 = second :=
    (Finset.mem_filter.mp hedge).2.2
  have hedgeTuple :
      edge = (first, second, third) := by
    exact Prod.ext hedgeFirst
      (Prod.ext hedgeSecond hedgeThird)
  rw [← hedgeTuple]
  exact hedgeH

/-- Alternative A is monotone under enlarging all three vertex classes. -/
lemma alternative_a_mono
    {delta epsilon : ℝ}
    {F F' G₁ G₁' G₂ G₂' : DiscreteSet 2}
    (h : WZ1Proposition8_9AlternativeA delta epsilon F' G₁' G₂')
    (hF : F' ⊆ F) (hG₁ : G₁' ⊆ G₁) (hG₂ : G₂' ⊆ G₂) :
    WZ1Proposition8_9AlternativeA delta epsilon F G₁ G₂ := by
  rcases h with
    ⟨base, direction, hdirection, hF_count, hG₁_count, hG₂_count⟩
  have hF_mono :
      wz1DiscreteLineCount F' 0 (wz1Perp2 direction) delta ≤
        wz1DiscreteLineCount F 0 (wz1Perp2 direction) delta := by
    simp [wz1DiscreteLineCount]
    gcongr
  have hG₁_mono :
      wz1DiscreteLineCount G₁' base direction delta ≤
        wz1DiscreteLineCount G₁ base direction delta := by
    simp [wz1DiscreteLineCount]
    gcongr
  have hG₂_mono :
      wz1DiscreteLineCount G₂' base direction delta ≤
        wz1DiscreteLineCount G₂ base direction delta := by
    simp [wz1DiscreteLineCount]
    gcongr
  exact
    ⟨base, direction, hdirection,
      hF_count.trans hF_mono,
      hG₁_count.trans hG₁_mono,
      hG₂_count.trans hG₂_mono⟩

/-- Dot-spread evidence is monotone under enlarging the source graph. -/
def dot_spread_data_mono
    {delta epsilon eta : ℝ}
    {H H' : Finset (Point2 × Point2 × Point2)}
    (hH : H' ⊆ H)
    (data : WZ1Proposition8_9NarrowDotSpreadData
      delta epsilon eta H') :
    WZ1Proposition8_9NarrowDotSpreadData
      delta epsilon eta H := by
  have hdot :
      wz1DotDifferenceSet H' ⊆ wz1DotDifferenceSet H := by
    intro value hvalue
    exact_mod_cast
      Finset.image_mono
        (fun edge => inner ℝ edge.1 (edge.2.1 - edge.2.2))
        hH hvalue
  exact
    ⟨data.values, data.lower, data.upper,
      data.lower_mem, data.upper_mem, data.separated,
      data.values_dot.trans hdot, data.between,
      data.cardinality⟩

end

end Kakeya.Assouad

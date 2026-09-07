import MyLeanRepo.Kakeya.Assouad.PropStickyNestedWeightedLowerRegularizationStatements
import MyLeanRepo.Kakeya.Assouad.MultiscaleUniformRefinement
import Mathlib.Data.ENNReal.BigOperators

/-! # Nested weighted lower regularization -/

noncomputable section

namespace Kakeya.Assouad

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

private lemma weighted_lower_single_level
    {indexType : Type} [DecidableEq indexType]
    (current : Finset indexType)
    (weight : indexType → ENNReal)
    (cells : Finset (Finset indexType))
    (hdisjoint :
      ∀ first ∈ cells, ∀ second ∈ cells,
        first ≠ second → Disjoint first second)
    (hcover : current ⊆ Finset.biUnion cells id)
    (hfinite : (∑ index ∈ current, weight index) ≠ ⊤) :
    ∃ selected kept,
      kept ⊆ cells ∧
      selected =
        (Finset.biUnion kept fun cell => current ∩ cell) ∧
      selected ⊆ current ∧
      (∑ index ∈ current, weight index) ≤
        (2 : ENNReal) * ∑ index ∈ selected, weight index ∧
      ∀ cell ∈ cells,
        (selected ∩ cell).Nonempty →
          (1 / 2 : ENNReal) *
                (∑ index ∈ selected, weight index) ≤
            (cells.card : ENNReal) *
              ∑ index ∈ selected ∩ cell, weight index := by
  by_cases hcurrent : current = ∅
  · refine ⟨∅, ∅, Finset.empty_subset _, ?_, ?_, ?_, ?_⟩
    · simp [hcurrent]
    · simp [hcurrent]
    · simp [hcurrent]
    · intro cell _ hnonempty
      simpa [hcurrent] using hnonempty
  have hcurrentNonempty : current.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hcurrent
  have hcellsNonempty : cells.Nonempty := by
    rcases hcurrentNonempty with ⟨index, hindex⟩
    rcases Finset.mem_biUnion.mp (hcover hindex) with
      ⟨cell, hcell, _⟩
    exact ⟨cell, hcell⟩
  let total : ENNReal := ∑ index ∈ current, weight index
  let count : ENNReal := cells.card
  let cellWeight : Finset indexType → ENNReal := fun cell =>
    ∑ index ∈ current ∩ cell, weight index
  let threshold : ENNReal := (1 / 2 : ENNReal) * total * count⁻¹
  let kept : Finset (Finset indexType) :=
    cells.filter fun cell => threshold ≤ cellWeight cell
  let discarded : Finset (Finset indexType) := cells \ kept
  let selected : Finset indexType :=
    Finset.biUnion kept fun cell => current ∩ cell
  have hcountZero : count ≠ 0 := by
    dsimp only [count]
    exact_mod_cast hcellsNonempty.card_pos.ne'
  have hcountTop : count ≠ ⊤ := by
    dsimp only [count]
    exact ENNReal.natCast_ne_top _
  have hpairwise :
      (cells : Set (Finset indexType)).PairwiseDisjoint
        (fun cell => current ∩ cell) := by
    intro first hfirst second hsecond hne
    exact
      (hdisjoint first hfirst second hsecond hne).mono
        (Finset.inter_subset_right)
        (Finset.inter_subset_right)
  have hcurrentUnion :
      current =
        Finset.biUnion cells (fun cell => current ∩ cell) := by
    ext index
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hindex
      rcases Finset.mem_biUnion.mp (hcover hindex) with
        ⟨cell, hcell, hindexCell⟩
      exact ⟨cell, hcell, hindex, hindexCell⟩
    · rintro ⟨cell, _, hindex, _⟩
      exact hindex
  have htotal :
      ∑ cell ∈ cells, cellWeight cell = total := by
    calc
      ∑ cell ∈ cells, cellWeight cell =
          ∑ index ∈
              Finset.biUnion cells (fun cell => current ∩ cell),
            weight index := by
        exact (Finset.sum_biUnion hpairwise).symm
      _ = ∑ index ∈ current, weight index := by
        rw [← hcurrentUnion]
      _ = total := rfl
  have hkeptSubset : kept ⊆ cells :=
    Finset.filter_subset _ _
  have hdiscardedSubset : discarded ⊆ cells :=
    Finset.sdiff_subset
  have hkeptDiscarded : Disjoint kept discarded :=
    Finset.disjoint_sdiff
  have hkeptUnion : kept ∪ discarded = cells := by
    exact Finset.union_sdiff_of_subset hkeptSubset
  have hdiscardedPointwise :
      ∀ cell ∈ discarded, cellWeight cell ≤ threshold := by
    intro cell hcell
    have hnotKept : cell ∉ kept :=
      (Finset.mem_sdiff.mp hcell).2
    have hnotLower : ¬threshold ≤ cellWeight cell := by
      intro hlower
      exact hnotKept
        (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp hcell).1, hlower⟩)
    exact (lt_of_not_ge hnotLower).le
  have hdiscardedMass :
      ∑ cell ∈ discarded, cellWeight cell ≤
        (1 / 2 : ENNReal) * total := by
    calc
      ∑ cell ∈ discarded, cellWeight cell ≤
          ∑ _cell ∈ discarded, threshold := by
        exact Finset.sum_le_sum hdiscardedPointwise
      _ = (discarded.card : ENNReal) * threshold := by
        simp [Finset.sum_const]
      _ ≤ count * threshold := by
        gcongr
        change
          (discarded.card : ENNReal) ≤
            (cells.card : ENNReal)
        exact_mod_cast Finset.card_le_card hdiscardedSubset
      _ = (1 / 2 : ENNReal) * total := by
        dsimp only [threshold]
        calc
          count * ((1 / 2 : ENNReal) * total * count⁻¹) =
              (count * count⁻¹) * ((1 / 2 : ENNReal) * total) := by
            ring
          _ = (1 / 2 : ENNReal) * total := by
            rw [ENNReal.mul_inv_cancel hcountZero hcountTop, one_mul]
  have hpartitionWeight :
      total =
        (∑ cell ∈ kept, cellWeight cell) +
          ∑ cell ∈ discarded, cellWeight cell := by
    calc
      total = ∑ cell ∈ cells, cellWeight cell := htotal.symm
      _ = ∑ cell ∈ kept ∪ discarded, cellWeight cell := by
        rw [hkeptUnion]
      _ =
          (∑ cell ∈ kept, cellWeight cell) +
            ∑ cell ∈ discarded, cellWeight cell :=
        Finset.sum_union hkeptDiscarded
  have hkeptPairwise :
      (kept : Set (Finset indexType)).PairwiseDisjoint
        (fun cell => current ∩ cell) := by
    intro first hfirst second hsecond hne
    exact
      hpairwise
        (hkeptSubset hfirst) (hkeptSubset hsecond) hne
  have hselectedWeight :
      ∑ index ∈ selected, weight index =
        ∑ cell ∈ kept, cellWeight cell := by
    dsimp only [selected]
    exact Finset.sum_biUnion hkeptPairwise
  have hhalfFinite :
      (1 / 2 : ENNReal) * total ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) hfinite
  have hhalfDouble :
      (1 / 2 : ENNReal) * total +
          (1 / 2 : ENNReal) * total =
        total := by
    have hcancel :
        (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
      simpa [div_eq_mul_inv] using
        ENNReal.mul_inv_cancel
          (show (2 : ENNReal) ≠ 0 by norm_num)
          (show (2 : ENNReal) ≠ ⊤ by norm_num)
    calc
      (1 / 2 : ENNReal) * total +
          (1 / 2 : ENNReal) * total =
          (2 : ENNReal) * ((1 / 2 : ENNReal) * total) := by
        simp [two_mul]
      _ = total := by
        rw [← mul_assoc, hcancel, one_mul]
  have hhalfRetained :
      (1 / 2 : ENNReal) * total ≤
        ∑ cell ∈ kept, cellWeight cell := by
    have hmain :
        total ≤
          (∑ cell ∈ kept, cellWeight cell) +
            (1 / 2 : ENNReal) * total := by
      calc
        total =
            (∑ cell ∈ kept, cellWeight cell) +
              ∑ cell ∈ discarded, cellWeight cell :=
          hpartitionWeight
        _ ≤
            (∑ cell ∈ kept, cellWeight cell) +
              (1 / 2 : ENNReal) * total :=
          add_le_add_right hdiscardedMass _
    have hadd :
        (1 / 2 : ENNReal) * total +
            (1 / 2 : ENNReal) * total ≤
          (∑ cell ∈ kept, cellWeight cell) +
            (1 / 2 : ENNReal) * total := by
      rwa [hhalfDouble]
    exact
      (ENNReal.add_le_add_iff_right hhalfFinite).mp hadd
  have hretained :
      total ≤
        (2 : ENNReal) * ∑ index ∈ selected, weight index := by
    rw [hselectedWeight]
    calc
      total =
          (1 / 2 : ENNReal) * total +
            (1 / 2 : ENNReal) * total := hhalfDouble.symm
      _ ≤
          (∑ cell ∈ kept, cellWeight cell) +
            ∑ cell ∈ kept, cellWeight cell :=
        add_le_add hhalfRetained hhalfRetained
      _ =
          (2 : ENNReal) *
            ∑ cell ∈ kept, cellWeight cell := by
        simp [two_mul]
  have hselectedSubset : selected ⊆ current := by
    intro index hindex
    rcases Finset.mem_biUnion.mp hindex with
      ⟨cell, _, hindex⟩
    exact (Finset.mem_inter.mp hindex).1
  have hselectedTotalLe :
      (∑ index ∈ selected, weight index) ≤ total := by
    dsimp only [total]
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        hselectedSubset (fun _ _ _ => bot_le)
  have hselectedInterKept :
      ∀ cell ∈ kept, selected ∩ cell = current ∩ cell := by
    intro cell hcell
    have hcurrentCellSubset : current ∩ cell ⊆ selected := by
      intro index hindex
      exact Finset.mem_biUnion.mpr ⟨cell, hcell, hindex⟩
    ext index
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hindexSelected, hindexCell⟩
      exact ⟨hselectedSubset hindexSelected, hindexCell⟩
    · rintro ⟨hindexCurrent, hindexCell⟩
      exact
        ⟨hcurrentCellSubset
          (Finset.mem_inter.mpr ⟨hindexCurrent, hindexCell⟩),
          hindexCell⟩
  have hselectedInterNotKept :
      ∀ cell ∈ cells, cell ∉ kept →
        selected ∩ cell = ∅ := by
    intro cell hcell hnotKept
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    rcases hnonempty with ⟨index, hindex⟩
    rcases Finset.mem_inter.mp hindex with
      ⟨hindexSelected, hindexCell⟩
    rcases Finset.mem_biUnion.mp hindexSelected with
      ⟨other, hotherKept, hindexOther⟩
    have hindexOtherCell : index ∈ other :=
      (Finset.mem_inter.mp hindexOther).2
    have hotherCell : other ∈ cells :=
      hkeptSubset hotherKept
    have hne : other ≠ cell := by
      intro heq
      exact hnotKept (heq ▸ hotherKept)
    have hdisj := hdisjoint other hotherCell cell hcell hne
    exact
      Finset.disjoint_left.mp hdisj
        hindexOtherCell hindexCell
  have hlower :
      ∀ cell ∈ cells,
        (selected ∩ cell).Nonempty →
          (1 / 2 : ENNReal) *
                (∑ index ∈ selected, weight index) ≤
            (cells.card : ENNReal) *
              ∑ index ∈ selected ∩ cell, weight index := by
    intro cell hcell hnonempty
    have hcellKept : cell ∈ kept := by
      by_contra hnot
      rw [hselectedInterNotKept cell hcell hnot] at hnonempty
      exact Finset.not_nonempty_empty hnonempty
    have hthreshold :
        threshold ≤ cellWeight cell :=
      (Finset.mem_filter.mp hcellKept).2
    have hcellEq :
        selected ∩ cell = current ∩ cell :=
      hselectedInterKept cell hcellKept
    calc
      (1 / 2 : ENNReal) *
            (∑ index ∈ selected, weight index) ≤
          (1 / 2 : ENNReal) * total := by
        gcongr
      _ = count * threshold := by
        dsimp only [threshold]
        calc
          (1 / 2 : ENNReal) * total =
              (count * count⁻¹) *
                ((1 / 2 : ENNReal) * total) := by
            rw [ENNReal.mul_inv_cancel hcountZero hcountTop, one_mul]
          _ =
              count *
                ((1 / 2 : ENNReal) * total * count⁻¹) := by
            ring
      _ ≤ count * cellWeight cell := by
        gcongr
      _ =
          (cells.card : ENNReal) *
            ∑ index ∈ selected ∩ cell, weight index := by
        rw [hcellEq]
  exact
    ⟨selected, kept, hkeptSubset, rfl, hselectedSubset,
      by simpa [total] using hretained, hlower⟩

private lemma nested_weighted_lower_induction
    {indexType : Type} [DecidableEq indexType]
    (ambient : Finset indexType)
    (weight : indexType → ENNReal)
    (levelCount : ℕ)
    (partition : ℕ → Finset (Finset indexType))
    (hpartition :
      ∀ level < levelCount,
        (∀ cell ∈ partition level, cell ⊆ ambient) ∧
        (∀ first ∈ partition level,
          ∀ second ∈ partition level,
            first ≠ second → Disjoint first second) ∧
        ambient ⊆ Finset.biUnion (partition level) id)
    (hrefine :
      ∀ level, level + 1 < levelCount →
        ∀ child ∈ partition (level + 1),
          ∃ parent ∈ partition level, child ⊆ parent)
    (hfinite : (∑ index ∈ ambient, weight index) ≠ ⊤) :
    ∀ processed : ℕ, processed ≤ levelCount →
      ∃ selected : Finset indexType,
        selected ⊆ ambient ∧
        (∑ index ∈ ambient, weight index) ≤
          (2 : ENNReal) ^ processed *
            ∑ index ∈ selected, weight index ∧
        ∀ level,
          levelCount - processed ≤ level →
          level < levelCount →
            ∀ cell ∈ partition level,
              (selected ∩ cell).Nonempty →
                (1 / 2 : ENNReal) *
                      (∑ index ∈ selected, weight index) ≤
                  ((partition level).card : ENNReal) *
                    ∑ index ∈ selected ∩ cell, weight index := by
  intro processed hprocessed
  induction processed with
  | zero =>
      refine ⟨ambient, Finset.Subset.rfl, ?_, ?_⟩
      · simp
      · intro level hlevel _
        exfalso
        omega
  | succ processed inductionHypothesis =>
      have hprocessedLe : processed ≤ levelCount := by
        omega
      rcases inductionHypothesis hprocessedLe with
        ⟨current, hcurrentSubset, hcurrentRetained,
          hcurrentLower⟩
      let level := levelCount - (processed + 1)
      have hlevel : level < levelCount := by
        omega
      have hcurrentCover :
          current ⊆
            Finset.biUnion (partition level) id :=
        hcurrentSubset.trans (hpartition level hlevel).2.2
      have hcurrentFinite :
          (∑ index ∈ current, weight index) ≠ ⊤ := by
        apply ne_top_of_le_ne_top hfinite
        exact
          Finset.sum_le_sum_of_subset_of_nonneg
            hcurrentSubset (fun _ _ _ => bot_le)
      rcases
          weighted_lower_single_level current weight
            (partition level)
            (hpartition level hlevel).2.1
            hcurrentCover hcurrentFinite with
        ⟨selected, kept, hkeptSubset, hselectedEq,
          hselectedSubsetCurrent, hstepRetained, hlevelLower⟩
      have hselectedSubset :
          selected ⊆ ambient :=
        hselectedSubsetCurrent.trans hcurrentSubset
      have hselectedRetained :
          (∑ index ∈ ambient, weight index) ≤
            (2 : ENNReal) ^ (processed + 1) *
              ∑ index ∈ selected, weight index := by
        calc
          (∑ index ∈ ambient, weight index) ≤
              (2 : ENNReal) ^ processed *
                ∑ index ∈ current, weight index :=
            hcurrentRetained
          _ ≤
              (2 : ENNReal) ^ processed *
                ((2 : ENNReal) *
                  ∑ index ∈ selected, weight index) := by
            gcongr
          _ =
              (2 : ENNReal) ^ (processed + 1) *
                ∑ index ∈ selected, weight index := by
            rw [pow_succ]
            ring
      have hselectedWeightLe :
          (∑ index ∈ selected, weight index) ≤
            ∑ index ∈ current, weight index := by
        exact
          Finset.sum_le_sum_of_subset_of_nonneg
            hselectedSubsetCurrent (fun _ _ _ => bot_le)
      have hancestor :
          ∀ finer,
            level ≤ finer →
            finer < levelCount →
              ∀ cell ∈ partition finer,
                ∃ parent ∈ partition level, cell ⊆ parent :=
        fun finer hlevelFiner hfiner =>
          find_ancestor levelCount partition hrefine
            hlevelFiner hfiner
      have hpreserved :
          ∀ finer,
            level < finer →
            finer < levelCount →
              ∀ cell ∈ partition finer,
                (selected ∩ cell).Nonempty →
                  selected ∩ cell = current ∩ cell := by
        intro finer hlevelFiner hfiner cell hcell hnonempty
        rcases hancestor finer hlevelFiner.le hfiner cell hcell with
          ⟨parent, hparent, hcellParent⟩
        have hparentKept : parent ∈ kept := by
          by_contra hnotKept
          rcases hnonempty with ⟨index, hindex⟩
          have hindexSelected : index ∈ selected :=
            (Finset.mem_inter.mp hindex).1
          have hindexCell : index ∈ cell :=
            (Finset.mem_inter.mp hindex).2
          have hindexParent : index ∈ parent :=
            hcellParent hindexCell
          rw [hselectedEq] at hindexSelected
          rcases Finset.mem_biUnion.mp hindexSelected with
            ⟨other, hotherKept, hindexOther⟩
          have hindexOtherCell : index ∈ other :=
            (Finset.mem_inter.mp hindexOther).2
          have hother : other ∈ partition level :=
            hkeptSubset hotherKept
          have hne : other ≠ parent := by
            intro heq
            exact hnotKept (heq ▸ hotherKept)
          exact
            Finset.disjoint_left.mp
              ((hpartition level hlevel).2.1
                other hother parent hparent hne)
              hindexOtherCell hindexParent
        have hcurrentCellSubset : current ∩ cell ⊆ selected := by
          intro index hindex
          have hindexParent : index ∈ parent :=
            hcellParent (Finset.mem_inter.mp hindex).2
          rw [hselectedEq]
          exact
            Finset.mem_biUnion.mpr
              ⟨parent, hparentKept,
                Finset.mem_inter.mpr
                  ⟨(Finset.mem_inter.mp hindex).1,
                    hindexParent⟩⟩
        ext index
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hindexSelected, hindexCell⟩
          exact
            ⟨hselectedSubsetCurrent hindexSelected,
              hindexCell⟩
        · rintro ⟨hindexCurrent, hindexCell⟩
          exact
            ⟨hcurrentCellSubset
                (Finset.mem_inter.mpr
                  ⟨hindexCurrent, hindexCell⟩),
              hindexCell⟩
      refine
        ⟨selected, hselectedSubset, hselectedRetained, ?_⟩
      intro finer hfinerLower hfinerUpper cell hcell hnonempty
      by_cases heq : finer = level
      · subst finer
        exact hlevelLower cell hcell hnonempty
      have hlevelFiner : level < finer := by
        dsimp only [level] at *
        omega
      have hcurrentLevelLower :
          levelCount - processed ≤ finer := by
        dsimp only [level] at *
        omega
      have hcurrent :=
        hcurrentLower finer hcurrentLevelLower hfinerUpper
          cell hcell
      have hcellEq :=
        hpreserved finer hlevelFiner hfinerUpper
          cell hcell hnonempty
      have hcurrentNonempty :
          (current ∩ cell).Nonempty := by
        rwa [← hcellEq]
      calc
        (1 / 2 : ENNReal) *
              (∑ index ∈ selected, weight index) ≤
            (1 / 2 : ENNReal) *
              ∑ index ∈ current, weight index := by
          gcongr
        _ ≤
            ((partition finer).card : ENNReal) *
              ∑ index ∈ current ∩ cell, weight index :=
          hcurrent hcurrentNonempty
        _ =
            ((partition finer).card : ENNReal) *
              ∑ index ∈ selected ∩ cell, weight index := by
          rw [hcellEq]

theorem wz2_prop_sticky_nested_weighted_lower_regularization :
    WZ2PropStickyNestedWeightedLowerRegularizationStatement := by
  intro indexType _ ambient weight levelCount partition
    hpartition hrefine hfinite
  rcases
      nested_weighted_lower_induction
        ambient weight levelCount partition
        hpartition hrefine hfinite
        levelCount le_rfl with
    ⟨selected, hselected, hretained, hlower⟩
  refine ⟨selected, hselected, hretained, ?_⟩
  intro level hlevel
  exact hlower level (by simp) hlevel

end Kakeya.Assouad

end

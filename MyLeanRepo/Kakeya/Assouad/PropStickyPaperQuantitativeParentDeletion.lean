import MyLeanRepo.Kakeya.Assouad.WZ1.IterativeDeletion

/-!
# Quantitative whole-cell parent deletion

The existing termination theorem shows that the stabilized cell family is
nonempty when the deletion budget is smaller than the initial mass.  The
paper-level refinement also needs the quantitative charging estimate: the
total mass of all deleted cells is at most that same deletion budget.
-/

noncomputable section

open Finset

namespace Kakeya.Assouad

lemma iterative_deletion_quantitative
    {n coarseCard : ℕ}
    (cells : Finset (Fin n))
    (activeParents : Fin n → Finset (Fin coarseCard))
    (fiberMass : Fin coarseCard → ENNReal)
    (fiberCellMass : ENNReal)
    (cellMass : Fin n → ENNReal)
    (degreeCap : ℕ)
    (threshold : ENNReal)
    (hDegree :
      ∀ cell ∈ cells,
        (activeParents cell).card ≤ 2 * degreeCap)
    (hCellMass :
      ∀ cell ∈ cells,
        cellMass cell ≤
          2 * (degreeCap : ENNReal) * fiberCellMass) :
    ∃ goodCells : Finset (Fin n),
      goodCells ⊆ cells ∧
      (∀ cell ∈ goodCells,
        ∀ parent ∈ activeParents cell,
          threshold * fiberMass parent ≤
            ∑ other ∈ goodCells,
              if parent ∈ activeParents other then
                fiberCellMass
              else 0) ∧
      (∑ cell ∈ cells \ goodCells, cellMass cell) ≤
        2 * (degreeCap : ENNReal) * threshold *
          ∑ parent : Fin coarseCard, fiberMass parent := by
  classical
  let parentMass
      (selected : Finset (Fin n))
      (parent : Fin coarseCard) : ENNReal :=
    ∑ cell ∈ selected,
      if parent ∈ activeParents cell then fiberCellMass else 0
  let badParents
      (selected : Finset (Fin n)) :
      Finset (Fin coarseCard) :=
    Finset.univ.filter fun parent =>
      parentMass selected parent < threshold * fiberMass parent
  let step (selected : Finset (Fin n)) : Finset (Fin n) :=
    deletionStep activeParents fiberMass fiberCellMass threshold selected
  have step_eq :
      ∀ selected,
        step selected =
          selected.filter fun cell =>
            Disjoint (activeParents cell) (badParents selected) := by
    intro selected
    rfl
  have step_subset :
      ∀ selected : Finset (Fin n),
        step selected ⊆ selected := by
    intro selected
    exact Finset.filter_subset _ _
  let iter : ℕ → Finset (Fin n) :=
    deletionIter cells activeParents fiberMass fiberCellMass threshold
  have iter_decreasing :
      ∀ stage : ℕ, iter (stage + 1) ⊆ iter stage := by
    intro stage
    exact step_subset (iter stage)
  have iter_subset :
      ∀ stage : ℕ, iter stage ⊆ cells := by
    intro stage
    induction stage with
    | zero =>
        simp [iter, deletionIter]
    | succ stage ih =>
        exact (iter_decreasing stage).trans ih
  have plateau :
      ∃ stage ≤ cells.card,
        iter (stage + 1) = iter stage := by
    let size : ℕ → ℕ := fun stage => (iter stage).card
    by_contra h
    push Not at h
    have strict :
        ∀ stage ≤ cells.card,
          size (stage + 1) < size stage := by
      intro stage hstage
      have hne :
          iter (stage + 1) ≠ iter stage :=
        h stage hstage
      have hproper :
          iter (stage + 1) ⊂ iter stage :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨iter_decreasing stage, hne⟩
      exact Finset.card_lt_card hproper
    have bound :
        ∀ stage,
          stage ≤ cells.card + 1 →
            size stage + stage ≤ size 0 := by
      intro stage hstage
      induction stage with
      | zero =>
          simp
      | succ stage ih =>
          have hstage' : stage ≤ cells.card := by omega
          have hlt :
              size (stage + 1) < size stage :=
            strict stage hstage'
          have hih :
              size stage + stage ≤ size 0 :=
            ih (by omega)
          omega
    have contradiction :=
      bound (cells.card + 1) (by omega)
    have size_zero : size 0 = cells.card := by
      simp [size, iter, deletionIter]
    rw [size_zero] at contradiction
    omega
  rcases plateau with ⟨stableStage, hstableStage, stable⟩
  have constant_after :
      ∀ stage ≥ stableStage,
        iter stage = iter stableStage := by
    intro stage hstage
    induction' hstage with stage hstage ih
    · rfl
    · have iter_succ :
          iter (stage + 1) = step (iter stage) := by
        simp [iter, deletionIter, deletionStep]
        rfl
      have fixed :
          step (iter stableStage) = iter stableStage := by
        have stable_succ :
            iter (stableStage + 1) =
              step (iter stableStage) := by
          simp [iter, deletionIter, deletionStep]
          rfl
        rw [stable_succ] at stable
        exact stable
      calc
        iter (stage + 1) = step (iter stage) := iter_succ
        _ = step (iter stableStage) := by rw [ih]
        _ = iter stableStage := fixed
  let goodCells := iter cells.card
  have good_subset : goodCells ⊆ cells :=
    iter_subset cells.card
  have final_eq :
      iter cells.card = iter stableStage :=
    constant_after cells.card (by omega)
  have final_fixed :
      step goodCells = goodCells := by
    have next_eq :
        iter (cells.card + 1) = iter stableStage :=
      constant_after (cells.card + 1) (by omega)
    have next_step :
        iter (cells.card + 1) =
          step (iter cells.card) := by
      simp [iter, deletionIter, deletionStep]
      rfl
    rw [next_step, final_eq] at next_eq
    simpa [goodCells, final_eq] using next_eq
  have good_condition :
      ∀ cell ∈ goodCells,
        ∀ parent ∈ activeParents cell,
          threshold * fiberMass parent ≤
            parentMass goodCells parent := by
    intro cell hcell parent hparent
    have cell_step : cell ∈ step goodCells := by
      rw [final_fixed]
      exact hcell
    have disjoint :
        Disjoint
          (activeParents cell)
          (badParents goodCells) := by
      rw [step_eq goodCells] at cell_step
      exact (Finset.mem_filter.mp cell_step).2
    have parent_not_bad :
        parent ∉ badParents goodCells :=
      Finset.disjoint_left.mp disjoint hparent
    have not_less :
        ¬parentMass goodCells parent <
          threshold * fiberMass parent := by
      simpa [badParents] using parent_not_bad
    exact le_of_not_gt not_less
  let deletedCells := cells \ goodCells
  by_cases deleted_empty : deletedCells = ∅
  · refine ⟨goodCells, good_subset, ?_, ?_⟩
    · intro cell hcell parent hparent
      exact good_condition cell hcell parent hparent
    · simpa [deletedCells, deleted_empty]
  have deleted_nonempty : deletedCells.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr deleted_empty
  have deleted_subset :
      deletedCells ⊆ cells :=
    Finset.sdiff_subset
  have deleted_not_good :
      ∀ cell ∈ deletedCells,
        cell ∉ goodCells := by
    intro cell hcell
    exact (Finset.mem_sdiff.mp hcell).2
  have eventually_deleted :
      ∀ cell ∈ deletedCells,
        ∃ stage : ℕ, cell ∉ iter (stage + 1) := by
    intro cell hcell
    have not_good := deleted_not_good cell hcell
    have next_subset :
        iter (cells.card + 1) ⊆ goodCells :=
      iter_decreasing cells.card
    exact
      ⟨cells.card, fun hnext =>
        not_good (next_subset hnext)⟩
  let deletionStage
      (cell : Fin n)
      (hcell : cell ∈ deletedCells) : ℕ :=
    Nat.find (eventually_deleted cell hcell)
  have deletionStage_spec :
      ∀ cell hcell,
        cell ∉ iter (deletionStage cell hcell + 1) := by
    intro cell hcell
    exact Nat.find_spec (eventually_deleted cell hcell)
  have present_before :
      ∀ cell hcell,
        ∀ stage ≤ deletionStage cell hcell,
          cell ∈ iter stage := by
    intro cell hcell stage hstage
    by_contra hmissing
    by_cases hzero : stage = 0
    · rw [hzero] at hmissing
      have hcell_cells := deleted_subset hcell
      simpa [iter, deletionIter] using hmissing hcell_cells
    · have predecessor : stage - 1 + 1 = stage := by omega
      have missing_predecessor :
          cell ∉ iter ((stage - 1) + 1) := by
        rw [predecessor]
        exact hmissing
      have minimal :
          deletionStage cell hcell ≤ stage - 1 :=
        Nat.find_min'
          (eventually_deleted cell hcell)
          missing_predecessor
      omega
  have present_at_deletion :
      ∀ cell hcell,
        cell ∈ iter (deletionStage cell hcell) := by
    intro cell hcell
    exact present_before cell hcell _ (by omega)
  have witness_exists :
      ∀ cell hcell,
        ∃ parent ∈ activeParents cell,
          parentMass
                (iter (deletionStage cell hcell))
                parent <
            threshold * fiberMass parent := by
    intro cell hcell
    have present :=
      present_at_deletion cell hcell
    have missing_step :
        cell ∉
          step (iter (deletionStage cell hcell)) := by
      have next_eq :
          iter (deletionStage cell hcell + 1) =
            step (iter (deletionStage cell hcell)) := by
        simp [iter, deletionIter, deletionStep]
        rfl
      rw [← next_eq]
      exact deletionStage_spec cell hcell
    rw [step_eq (iter (deletionStage cell hcell))] at missing_step
    have not_disjoint :
        ¬Disjoint
          (activeParents cell)
          (badParents
            (iter (deletionStage cell hcell))) := by
      intro hdisjoint
      exact
        missing_step
          (Finset.mem_filter.mpr ⟨present, hdisjoint⟩)
    rcases
        (by
          simpa [Finset.disjoint_left] using not_disjoint)
      with ⟨parent, hparent, hbad⟩
    have bad_inequality :
        parentMass
              (iter (deletionStage cell hcell))
              parent <
          threshold * fiberMass parent := by
      simpa [badParents] using hbad
    exact ⟨parent, hparent, bad_inequality⟩
  let witness
      (cell : Fin n)
      (hcell : cell ∈ deletedCells) :
      Fin coarseCard :=
    Classical.choose (witness_exists cell hcell)
  have witness_spec :
      ∀ cell hcell,
        witness cell hcell ∈ activeParents cell ∧
        parentMass
              (iter (deletionStage cell hcell))
              (witness cell hcell) <
          threshold * fiberMass (witness cell hcell) := by
    intro cell hcell
    exact Classical.choose_spec (witness_exists cell hcell)
  rcases deleted_nonempty with ⟨defaultCell, hdefaultCell⟩
  let defaultParent : Fin coarseCard :=
    witness defaultCell hdefaultCell
  let witnessTotal (cell : Fin n) : Fin coarseCard :=
    if hcell : cell ∈ deletedCells then
      witness cell hcell
    else defaultParent
  let chargedCells
      (parent : Fin coarseCard) : Finset (Fin n) :=
    deletedCells.filter fun cell =>
      witnessTotal cell = parent
  have same_deletion_stage :
      ∀ first second hfirst hsecond,
        witness first hfirst = witness second hsecond →
          deletionStage first hfirst =
            deletionStage second hsecond := by
    intro first second hfirst hsecond hwitness
    by_cases hlt :
        deletionStage first hfirst <
          deletionStage second hsecond
    · let parent := witness first hfirst
      have parent_bad :
          parent ∈
            badParents
              (iter (deletionStage first hfirst)) := by
        simpa [badParents] using
          (witness_spec first hfirst).2
      have parent_active :
          parent ∈ activeParents second := by
        have h :
            witness second hsecond = parent :=
          hwitness.symm
        rw [← h]
        exact (witness_spec second hsecond).1
      have second_present :
          second ∈ iter (deletionStage first hfirst) :=
        present_before second hsecond _ (by omega)
      have second_removed :
          second ∉ iter (deletionStage first hfirst + 1) := by
        have removed_from_step :
            second ∉
              step
                (iter (deletionStage first hfirst)) := by
          rw [step_eq]
          intro hmem
          have hdisjoint :=
            (Finset.mem_filter.mp hmem).2
          exact
            (Finset.disjoint_left.mp hdisjoint)
              parent_active parent_bad
        have next_eq :
            iter (deletionStage first hfirst + 1) =
              step
                (iter (deletionStage first hfirst)) := by
          simp [iter, deletionIter, deletionStep]
          rfl
        rwa [next_eq]
      have second_still_present :
          second ∈ iter (deletionStage first hfirst + 1) :=
        present_before second hsecond _ (by omega)
      exact (second_removed second_still_present).elim
    · by_cases hgt :
          deletionStage second hsecond <
            deletionStage first hfirst
      · let parent := witness second hsecond
        have parent_bad :
            parent ∈
              badParents
                (iter (deletionStage second hsecond)) := by
          simpa [badParents] using
            (witness_spec second hsecond).2
        have parent_active :
            parent ∈ activeParents first := by
          have h :
              witness first hfirst = parent :=
            hwitness
          rw [← h]
          exact (witness_spec first hfirst).1
        have first_present :
            first ∈ iter (deletionStage second hsecond) :=
          present_before first hfirst _ (by omega)
        have first_removed :
            first ∉ iter (deletionStage second hsecond + 1) := by
          have removed_from_step :
              first ∉
                step
                  (iter (deletionStage second hsecond)) := by
            rw [step_eq]
            intro hmem
            have hdisjoint :=
              (Finset.mem_filter.mp hmem).2
            exact
              (Finset.disjoint_left.mp hdisjoint)
                parent_active parent_bad
          have next_eq :
              iter (deletionStage second hsecond + 1) =
                step
                  (iter (deletionStage second hsecond)) := by
            simp [iter, deletionIter, deletionStep]
            rfl
          rwa [next_eq]
        have first_still_present :
            first ∈ iter (deletionStage second hsecond + 1) :=
          present_before first hfirst _ (by omega)
        exact (first_removed first_still_present).elim
      · omega
  have charged_bound :
      ∀ parent : Fin coarseCard,
        ∑ cell ∈ chargedCells parent, cellMass cell ≤
          2 * (degreeCap : ENNReal) *
            threshold * fiberMass parent := by
    intro parent
    by_cases hempty : chargedCells parent = ∅
    · rw [hempty]
      simp
    · rcases
          Finset.nonempty_iff_ne_empty.mpr hempty
        with ⟨reference, hreference⟩
      have reference_deleted :
          reference ∈ deletedCells :=
        (Finset.mem_filter.mp hreference).1
      have reference_witness :
          witness reference reference_deleted = parent := by
        have h :=
          (Finset.mem_filter.mp hreference).2
        simpa [witnessTotal, dif_pos reference_deleted] using h
      let stage := deletionStage reference reference_deleted
      have charged_subset :
          chargedCells parent ⊆
            (iter stage).filter fun cell =>
              parent ∈ activeParents cell := by
        intro cell hcell
        have cell_deleted :
            cell ∈ deletedCells :=
          (Finset.mem_filter.mp hcell).1
        have cell_witness_total :
            witnessTotal cell = parent :=
          (Finset.mem_filter.mp hcell).2
        have cell_witness :
            witness cell cell_deleted = parent := by
          simpa [witnessTotal, dif_pos cell_deleted] using
            cell_witness_total
        have same_stage :
            deletionStage cell cell_deleted = stage :=
          same_deletion_stage
            cell reference cell_deleted reference_deleted
            (by rw [cell_witness, reference_witness])
        have cell_present :
            cell ∈ iter stage := by
          rw [← same_stage]
          exact present_at_deletion cell cell_deleted
        have parent_active :
            parent ∈ activeParents cell := by
          rw [← cell_witness]
          exact (witness_spec cell cell_deleted).1
        exact Finset.mem_filter.mpr
          ⟨cell_present, parent_active⟩
      have parent_bad :
          parentMass (iter stage) parent <
            threshold * fiberMass parent := by
        have h :=
          (witness_spec reference reference_deleted).2
        simpa [stage, reference_witness] using h
      calc
        ∑ cell ∈ chargedCells parent, cellMass cell ≤
            ∑ cell ∈
                (iter stage).filter fun cell =>
                  parent ∈ activeParents cell,
              cellMass cell :=
          Finset.sum_le_sum_of_subset_of_nonneg
            charged_subset
            (fun _ _ _ => by positivity)
        _ ≤
            ∑ cell ∈
                (iter stage).filter fun cell =>
                  parent ∈ activeParents cell,
              2 * (degreeCap : ENNReal) *
                fiberCellMass := by
          apply Finset.sum_le_sum
          intro cell hcell
          exact
            hCellMass cell
              (iter_subset stage
                (Finset.mem_filter.mp hcell).1)
        _ =
            2 * (degreeCap : ENNReal) *
              parentMass (iter stage) parent := by
          have hmass :
              parentMass (iter stage) parent =
                ∑ cell ∈
                    (iter stage).filter fun cell =>
                      parent ∈ activeParents cell,
                  fiberCellMass := by
            simp [parentMass, Finset.sum_ite]
          rw [hmass, Finset.mul_sum]
        _ ≤
            2 * (degreeCap : ENNReal) *
              (threshold * fiberMass parent) := by
          exact
            mul_le_mul_of_nonneg_left
              (le_of_lt parent_bad) (by positivity)
        _ =
            2 * (degreeCap : ENNReal) *
              threshold * fiberMass parent := by
          ring
  have partition :
      ∑ cell ∈ deletedCells, cellMass cell =
        ∑ parent : Fin coarseCard,
          ∑ cell ∈ chargedCells parent, cellMass cell := by
    have single :
        ∀ cell ∈ deletedCells,
          (∑ parent : Fin coarseCard,
              if witnessTotal cell = parent then
                cellMass cell
              else 0) =
            cellMass cell := by
      intro cell hcell
      have hsum :
          (∑ parent : Fin coarseCard,
              if witnessTotal cell = parent then
                cellMass cell
              else 0) =
            (if
                witnessTotal cell = witnessTotal cell
              then cellMass cell
              else 0) := by
        apply Finset.sum_eq_single_of_mem
          (witnessTotal cell) (Finset.mem_univ _)
        intro parent _ hne
        have hcondition :
            ¬witnessTotal cell = parent := by
          intro heq
          exact hne heq.symm
        rw [if_neg hcondition]
      rw [hsum, if_pos rfl]
    calc
      ∑ cell ∈ deletedCells, cellMass cell =
          ∑ cell ∈ deletedCells,
            ∑ parent : Fin coarseCard,
              if witnessTotal cell = parent then
                cellMass cell
              else 0 := by
        apply Finset.sum_congr rfl
        intro cell hcell
        exact (single cell hcell).symm
      _ =
          ∑ parent : Fin coarseCard,
            ∑ cell ∈ deletedCells,
              if witnessTotal cell = parent then
                cellMass cell
              else 0 := by
        rw [Finset.sum_comm]
      _ =
          ∑ parent : Fin coarseCard,
            ∑ cell ∈ chargedCells parent,
              cellMass cell := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [Finset.sum_ite]
        simp [chargedCells]
  refine ⟨goodCells, good_subset, ?_, ?_⟩
  · intro cell hcell parent hparent
    exact good_condition cell hcell parent hparent
  · change
      (∑ cell ∈ deletedCells, cellMass cell) ≤
        2 * (degreeCap : ENNReal) * threshold *
          ∑ parent : Fin coarseCard, fiberMass parent
    rw [partition]
    calc
      ∑ parent : Fin coarseCard,
          ∑ cell ∈ chargedCells parent, cellMass cell ≤
          ∑ parent : Fin coarseCard,
            2 * (degreeCap : ENNReal) *
              threshold * fiberMass parent := by
        apply Finset.sum_le_sum
        intro parent _
        exact charged_bound parent
      _ =
          2 * (degreeCap : ENNReal) * threshold *
            ∑ parent : Fin coarseCard, fiberMass parent := by
        rw [Finset.mul_sum]

lemma iterative_deletion_quantitative_nonempty
    {n coarseCard : ℕ}
    (cells : Finset (Fin n))
    (activeParents : Fin n → Finset (Fin coarseCard))
    (fiberMass : Fin coarseCard → ENNReal)
    (fiberCellMass : ENNReal)
    (cellMass : Fin n → ENNReal)
    (degreeCap : ℕ)
    (threshold : ENNReal)
    (hDegree :
      ∀ cell ∈ cells,
        (activeParents cell).card ≤ 2 * degreeCap)
    (hCellMass :
      ∀ cell ∈ cells,
        cellMass cell ≤
          2 * (degreeCap : ENNReal) * fiberCellMass)
    (hTotal :
      2 * (degreeCap : ENNReal) * threshold *
            ∑ parent : Fin coarseCard, fiberMass parent <
        ∑ cell ∈ cells, cellMass cell) :
    ∃ goodCells : Finset (Fin n),
      goodCells ⊆ cells ∧
      goodCells.Nonempty ∧
      (∀ cell ∈ goodCells,
        ∀ parent ∈ activeParents cell,
          threshold * fiberMass parent ≤
            ∑ other ∈ goodCells,
              if parent ∈ activeParents other then
                fiberCellMass
              else 0) ∧
      (∑ cell ∈ cells \ goodCells, cellMass cell) ≤
        2 * (degreeCap : ENNReal) * threshold *
          ∑ parent : Fin coarseCard, fiberMass parent := by
  rcases
      iterative_deletion_quantitative
        cells activeParents fiberMass fiberCellMass
        cellMass degreeCap threshold hDegree hCellMass
    with ⟨goodCells, goodSubset, goodCondition, deletedMass⟩
  have goodNonempty : goodCells.Nonempty := by
    by_contra hempty
    have goodEmpty : goodCells = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hempty
    have allDeleted : cells \ goodCells = cells := by
      rw [goodEmpty]
      simp
    rw [allDeleted] at deletedMass
    exact (not_le_of_gt hTotal) deletedMass
  exact
    ⟨goodCells, goodSubset, goodNonempty,
      goodCondition, deletedMass⟩

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# Iterative deletion for active parent density

Delete whole cells meeting a parent whose surviving mass is below threshold.
The global charging argument proves that the stabilized family is nonempty.
-/

noncomputable section

open MeasureTheory Metric Set Finset

namespace Kakeya.Assouad

/-- One simultaneous whole-cell deletion step. -/
def deletionStep {n coarseCard : ℕ}
    (activeParents : Fin n → Finset (Fin coarseCard))
    (fiberMass : Fin coarseCard → ENNReal)
    (fiberCellMass : ENNReal)
    (threshold : ENNReal)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  let parentMass (S : Finset (Fin n)) (j : Fin coarseCard) : ENNReal :=
    ∑ c ∈ S, if j ∈ activeParents c then fiberCellMass else 0
  let badParents : Finset (Fin coarseCard) :=
    Finset.univ.filter (fun j => parentMass S j < threshold * fiberMass j)
  S.filter (fun c => Disjoint (activeParents c) badParents)

/-- Iterate the whole-cell deletion step. -/
def deletionIter {n coarseCard : ℕ}
    (cells : Finset (Fin n))
    (activeParents : Fin n → Finset (Fin coarseCard))
    (fiberMass : Fin coarseCard → ENNReal)
    (fiberCellMass : ENNReal)
    (threshold : ENNReal)
    (k : ℕ) : Finset (Fin n) :=
  Nat.recOn k cells (fun _ previous =>
    deletionStep activeParents fiberMass fiberCellMass threshold previous)

/--
The whole-cell deletion process stabilizes at a nonempty family on which every
active parent has the prescribed surviving mass.
-/
lemma iterative_deletion_terminates
    {n coarseCard : ℕ}
    (cells : Finset (Fin n))
    (activeParents : Fin n → Finset (Fin coarseCard))
    (fiberMass : Fin coarseCard → ENNReal)
    (fiberCellMass : ENNReal)
    (cellMass : Fin n → ENNReal)
    (C : ℕ)
    (threshold : ENNReal)
    (h1 : ∀ c ∈ cells, (activeParents c).card ≤ 2 * C)
    (h2 : ∀ c ∈ cells, cellMass c ≤ 2 * (C : ENNReal) * fiberCellMass)
    (h_total :
      2 * (C : ENNReal) * threshold *
          ∑ j : Fin coarseCard, fiberMass j <
        ∑ c ∈ cells, cellMass c) :
    ∃ (goodCells : Finset (Fin n)),
      goodCells ⊆ cells ∧
      goodCells.Nonempty ∧
      (∀ c ∈ goodCells, ∀ j ∈ activeParents c,
        threshold * fiberMass j ≤
          ∑ c' ∈ goodCells,
            if j ∈ activeParents c' then fiberCellMass else 0) := by
  classical
  let parentMass (S : Finset (Fin n)) (j : Fin coarseCard) : ENNReal :=
    ∑ c ∈ S, if j ∈ activeParents c then fiberCellMass else 0
  let badParents (S : Finset (Fin n)) : Finset (Fin coarseCard) :=
    Finset.univ.filter
      (fun j => parentMass S j < threshold * fiberMass j)
  let step (S : Finset (Fin n)) : Finset (Fin n) :=
    deletionStep activeParents fiberMass fiberCellMass threshold S
  have h_step_eq : ∀ S,
      step S =
        S.filter
          (fun c => Disjoint (activeParents c) (badParents S)) := by
    intro S
    rfl
  have h_step_sub : ∀ S : Finset (Fin n), step S ⊆ S := by
    intro S
    exact Finset.filter_subset _ _
  let iter : ℕ → Finset (Fin n) :=
    deletionIter cells activeParents fiberMass fiberCellMass threshold
  have h_iter_decr : ∀ k : ℕ, iter (k + 1) ⊆ iter k := by
    intro k
    exact h_step_sub (iter k)
  have h_iter_cells : ∀ k : ℕ, iter k ⊆ cells := by
    intro k
    induction k with
    | zero => simp [iter, deletionIter]
    | succ k ih => exact (h_iter_decr k).trans ih
  have h_plateau : ∃ k ≤ cells.card, iter (k + 1) = iter k := by
    let f : ℕ → ℕ := fun k => (iter k).card
    by_contra h
    push Not at h
    have h_strict : ∀ k ≤ cells.card, f (k + 1) < f k := by
      intro k hk
      have h_ne : iter (k + 1) ≠ iter k := h k (by linarith)
      have h_ss : iter (k + 1) ⊂ iter k :=
        Finset.ssubset_iff_subset_ne.mpr ⟨h_iter_decr k, h_ne⟩
      exact Finset.card_lt_card h_ss
    have h_bound : ∀ k, k ≤ cells.card + 1 → f k + k ≤ f 0 := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
          have h_k_le : k ≤ cells.card := by omega
          have h_lt : f (k + 1) < f k := h_strict k h_k_le
          have h_ih : f k + k ≤ f 0 := ih (by omega)
          omega
    have h_contra := h_bound (cells.card + 1) (by omega)
    have h_zero : f 0 = cells.card := by
      simp [f, iter, deletionIter]
    rw [h_zero] at h_contra
    omega
  rcases h_plateau with ⟨k, hk, h_eq⟩
  have h_const : ∀ m ≥ k, iter m = iter k := by
    intro m hm
    induction' hm with m hm ih
    · rfl
    · have h1 : iter (m + 1) = step (iter m) := by
        simp [iter, deletionIter, deletionStep]
        rfl
      have h2 : step (iter k) = iter k := by
        have h3 : iter (k + 1) = step (iter k) := by
          simp [iter, deletionIter, deletionStep]
          rfl
        rw [h3] at h_eq
        exact h_eq
      calc
        iter (m + 1) = step (iter m) := h1
        _ = step (iter k) := by rw [ih]
        _ = iter k := h2
  let goodCells := iter cells.card
  have h_goodCells_sub : goodCells ⊆ cells := h_iter_cells cells.card
  have h_eq_card : iter cells.card = iter k :=
    h_const cells.card (by linarith)
  have h_fp : step goodCells = goodCells := by
    have h1 : iter (cells.card + 1) = iter k :=
      h_const (cells.card + 1) (by linarith)
    have h2 : iter (cells.card + 1) = step (iter cells.card) := by
      simp [iter, deletionIter, deletionStep]
      rfl
    have h3 : step (iter cells.card) = iter k := by rw [← h2, h1]
    have h4 : step (iter cells.card) = iter cells.card := by
      rw [h3, ← h_eq_card]
    exact h4
  have h_good_condition :
      ∀ c ∈ goodCells, ∀ j ∈ activeParents c,
        threshold * fiberMass j ≤ parentMass goodCells j := by
    intro c hc j hj
    have h_c_in_step : c ∈ step goodCells := by
      rw [h_fp]
      exact hc
    have h_disj :
        Disjoint (activeParents c) (badParents goodCells) := by
      rw [h_step_eq goodCells] at h_c_in_step
      exact (Finset.mem_filter.mp h_c_in_step).2
    have h_j_not_bad : j ∉ badParents goodCells :=
      Finset.disjoint_left.mp h_disj hj
    have h_ge :
        ¬parentMass goodCells j < threshold * fiberMass j := by
      simpa [badParents] using h_j_not_bad
    exact le_of_not_gt h_ge
  by_cases h_empty : goodCells = ∅
  · have h_all_del : ∀ c ∈ cells, c ∉ goodCells := by
      intro c hc
      rw [h_empty]
      simp
    have h_exists_del :
        ∀ c ∈ cells, ∃ m : ℕ, c ∉ iter (m + 1) := by
      intro c hc
      have h1 : c ∉ goodCells := h_all_del c hc
      have h2 : iter (cells.card + 1) ⊆ goodCells :=
        h_iter_decr cells.card
      exact ⟨cells.card, fun h3 => h1 (h2 h3)⟩
    let delIter (c : Fin n) (hc : c ∈ cells) : ℕ :=
      Nat.find (h_exists_del c hc)
    have h_delIter_prop :
        ∀ c hc, c ∉ iter (delIter c hc + 1) := by
      intro c hc
      exact Nat.find_spec (h_exists_del c hc)
    have h_present_before :
        ∀ c hc, ∀ m ≤ delIter c hc, c ∈ iter m := by
      intro c hc m hm
      by_contra h
      by_cases h0 : m = 0
      · rw [h0] at h
        simpa [iter, deletionIter] using h hc
      · have h_k : m - 1 + 1 = m := by omega
        have h2 : c ∉ iter ((m - 1) + 1) := by
          rw [h_k]
          exact h
        have h3 : delIter c hc ≤ m - 1 :=
          Nat.find_min' (h_exists_del c hc) h2
        omega
    have h_delIter_in : ∀ c hc, c ∈ iter (delIter c hc) := by
      intro c hc
      exact h_present_before c hc (delIter c hc) (by omega)
    have h_deleted_if_bad :
        ∀ (S : Finset (Fin n)) (c : Fin n) (j : Fin coarseCard),
          c ∈ S →
          j ∈ badParents S →
          j ∈ activeParents c →
          c ∉ step S := by
      intro S c j hc hbad hactive
      rw [h_step_eq S]
      intro hcin
      have h_disj :
          Disjoint (activeParents c) (badParents S) :=
        (Finset.mem_filter.mp hcin).2
      exact Finset.disjoint_left.mp h_disj hactive hbad
    have h_witness_exists :
        ∀ c hc, ∃ j ∈ activeParents c,
          parentMass (iter (delIter c hc)) j <
            threshold * fiberMass j := by
      intro c hc
      have h1 : c ∈ iter (delIter c hc) := h_delIter_in c hc
      have h2 : c ∉ step (iter (delIter c hc)) := by
        have h4 :
            iter (delIter c hc + 1) =
              step (iter (delIter c hc)) := by
          simp [iter, deletionIter, deletionStep]
          rfl
        rw [← h4]
        exact h_delIter_prop c hc
      rw [h_step_eq (iter (delIter c hc))] at h2
      have h3 :
          ¬Disjoint (activeParents c)
            (badParents (iter (delIter c hc))) := by
        intro h_disj
        exact h2 (Finset.mem_filter.mpr ⟨h1, h_disj⟩)
      rcases (by
        simpa [Finset.disjoint_left] using h3) with
        ⟨j, hj_active, hj_bad⟩
      have h6 :
          parentMass (iter (delIter c hc)) j <
            threshold * fiberMass j := by
        simpa [badParents] using hj_bad
      exact ⟨j, hj_active, h6⟩
    let witness (c : Fin n) (hc : c ∈ cells) : Fin coarseCard :=
      Classical.choose (h_witness_exists c hc)
    have h_witness_prop :
        ∀ c hc,
          witness c hc ∈ activeParents c ∧
          parentMass (iter (delIter c hc)) (witness c hc) <
            threshold * fiberMass (witness c hc) := by
      intro c hc
      exact Classical.choose_spec (h_witness_exists c hc)
    have h_coarseCard_pos : 0 < coarseCard := by
      by_contra h
      have h0 : coarseCard = 0 := by omega
      have h_bad_empty : ∀ S, badParents S = ∅ := by
        intro S
        subst h0
        simp [badParents]
      have h_step_id : ∀ S, step S = S := by
        intro S
        rw [h_step_eq S, h_bad_empty S]
        simp
      have h_iter_id : ∀ m, iter m = cells := by
        intro m
        induction m with
        | zero => simp [iter, deletionIter]
        | succ m ih =>
            have hm : iter (m + 1) = step (iter m) := by
              simp [iter, deletionIter]
              rfl
            rw [hm, h_step_id, ih]
      have h3 : goodCells = cells := by
        simpa [goodCells] using h_iter_id cells.card
      rw [h3] at h_empty
      rw [h_empty] at h_total
      simp at h_total
    let defaultParent : Fin coarseCard := ⟨0, h_coarseCard_pos⟩
    let witnessTotal (c : Fin n) : Fin coarseCard :=
      if hc : c ∈ cells then witness c hc else defaultParent
    let D (j : Fin coarseCard) : Finset (Fin n) :=
      cells.filter (fun c => witnessTotal c = j)
    have h_same_iter :
        ∀ (c c' : Fin n) (hc hc'),
          witness c hc = witness c' hc' →
            delIter c hc = delIter c' hc' := by
      intro c c' hc hc' hj
      by_cases h_lt : delIter c hc < delIter c' hc'
      · let j := witness c hc
        have h_j_bad : j ∈ badParents (iter (delIter c hc)) := by
          simpa [badParents] using (h_witness_prop c hc).2
        have h_j_active : j ∈ activeParents c' := by
          have h : witness c' hc' = j := hj.symm
          rw [← h]
          exact (h_witness_prop c' hc').1
        have h_c'_in : c' ∈ iter (delIter c hc) :=
          h_present_before c' hc' (delIter c hc) (by omega)
        have h_c'_out : c' ∉ iter (delIter c hc + 1) :=
          h_deleted_if_bad (iter (delIter c hc)) c' j
            h_c'_in h_j_bad h_j_active
        have h_c'_in2 : c' ∈ iter (delIter c hc + 1) :=
          h_present_before c' hc' (delIter c hc + 1) (by omega)
        exact False.elim (h_c'_out h_c'_in2)
      · by_cases h_gt : delIter c' hc' < delIter c hc
        · let j := witness c' hc'
          have h_j_bad :
              j ∈ badParents (iter (delIter c' hc')) := by
            simpa [badParents] using (h_witness_prop c' hc').2
          have h_j_active : j ∈ activeParents c := by
            have h : witness c hc = j := hj
            rw [← h]
            exact (h_witness_prop c hc).1
          have h_c_in : c ∈ iter (delIter c' hc') :=
            h_present_before c hc (delIter c' hc') (by omega)
          have h_c_out : c ∉ iter (delIter c' hc' + 1) :=
            h_deleted_if_bad (iter (delIter c' hc')) c j
              h_c_in h_j_bad h_j_active
          have h_c_in2 : c ∈ iter (delIter c' hc' + 1) :=
            h_present_before c hc (delIter c' hc' + 1) (by omega)
          exact False.elim (h_c_out h_c_in2)
        · omega
    have h_D_j_bound :
        ∀ j : Fin coarseCard,
          ∑ c ∈ D j, cellMass c ≤
            2 * (C : ENNReal) * threshold * fiberMass j := by
      intro j
      by_cases hDj : D j = ∅
      · rw [hDj]
        simp
      · rcases Finset.nonempty_iff_ne_empty.mpr hDj with ⟨c0, hc0⟩
        have hc0_in : c0 ∈ cells := (Finset.mem_filter.mp hc0).1
        have hwit0 : witnessTotal c0 = j :=
          (Finset.mem_filter.mp hc0).2
        have hwit0' : witness c0 hc0_in = j := by
          simpa [witnessTotal, dif_pos hc0_in] using hwit0
        let k_j := delIter c0 hc0_in
        have h_D_j_sub :
            D j ⊆ (iter k_j).filter (fun c => j ∈ activeParents c) := by
          intro c hc
          have hc_in : c ∈ cells := (Finset.mem_filter.mp hc).1
          have hwit : witnessTotal c = j :=
            (Finset.mem_filter.mp hc).2
          have hwit' : witness c hc_in = j := by
            simpa [witnessTotal, dif_pos hc_in] using hwit
          have h_same : delIter c hc_in = k_j :=
            h_same_iter c c0 hc_in hc0_in (by rw [hwit', hwit0'])
          have h_c_in_iter : c ∈ iter k_j := by
            rw [← h_same]
            exact h_delIter_in c hc_in
          have h_j_active : j ∈ activeParents c := by
            rw [← hwit']
            exact (h_witness_prop c hc_in).1
          exact Finset.mem_filter.mpr ⟨h_c_in_iter, h_j_active⟩
        have h_j_bad :
            parentMass (iter k_j) j <
              threshold * fiberMass j := by
          have h := (h_witness_prop c0 hc0_in).2
          simpa [k_j, hwit0'] using h
        calc
          ∑ c ∈ D j, cellMass c
              ≤ ∑ c ∈ (iter k_j).filter
                  (fun c => j ∈ activeParents c), cellMass c :=
            Finset.sum_le_sum_of_subset_of_nonneg h_D_j_sub
              (fun _ _ _ => by positivity)
          _ ≤ ∑ c ∈ (iter k_j).filter
                  (fun c => j ∈ activeParents c),
                2 * (C : ENNReal) * fiberCellMass := by
            apply Finset.sum_le_sum
            intro c hc
            have hc' : c ∈ cells :=
              h_iter_cells k_j (Finset.mem_filter.mp hc).1
            exact h2 c hc'
          _ = 2 * (C : ENNReal) * parentMass (iter k_j) j := by
            have h_eq :
                parentMass (iter k_j) j =
                  ∑ c ∈ (iter k_j).filter
                    (fun c => j ∈ activeParents c), fiberCellMass := by
              simp [parentMass, Finset.sum_ite]
            rw [h_eq, Finset.mul_sum]
          _ ≤ 2 * (C : ENNReal) * (threshold * fiberMass j) := by
            exact mul_le_mul_of_nonneg_left
              (le_of_lt h_j_bad) (by positivity)
          _ = 2 * (C : ENNReal) * threshold * fiberMass j := by ring
    have h_partition :
        ∑ c ∈ cells, cellMass c =
          ∑ j : Fin coarseCard, ∑ c ∈ D j, cellMass c := by
      have h1 : ∀ c ∈ cells,
          (∑ j : Fin coarseCard,
            if witnessTotal c = j then cellMass c else 0) =
              cellMass c := by
        intro c hc
        have hsum :
            ∑ j : Fin coarseCard,
                (if witnessTotal c = j then cellMass c else 0) =
              (if witnessTotal c = witnessTotal c then cellMass c else 0) := by
          apply Finset.sum_eq_single_of_mem
            (witnessTotal c) (Finset.mem_univ _)
          intro j _ hne
          have h_cond : ¬witnessTotal c = j := by
            intro h_eq
            exact hne h_eq.symm
          rw [if_neg h_cond]
        rw [hsum, if_pos rfl]
      have h3 :
          ∑ c ∈ cells, cellMass c =
            ∑ c ∈ cells, ∑ j : Fin coarseCard,
              if witnessTotal c = j then cellMass c else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (h1 c hc).symm
      rw [h3, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_ite]
      simp [D]
    have h_final :
        ∑ c ∈ cells, cellMass c ≤
          2 * (C : ENNReal) * threshold *
            ∑ j : Fin coarseCard, fiberMass j := by
      rw [h_partition]
      calc
        ∑ j : Fin coarseCard, ∑ c ∈ D j, cellMass c
            ≤ ∑ j : Fin coarseCard,
                2 * (C : ENNReal) * threshold * fiberMass j := by
          apply Finset.sum_le_sum
          intro j _
          exact h_D_j_bound j
        _ = 2 * (C : ENNReal) * threshold *
              ∑ j : Fin coarseCard, fiberMass j := by
          rw [Finset.mul_sum]
    exact False.elim (not_le.mpr h_total h_final)
  · have h_nonempty : goodCells.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr h_empty
    exact ⟨goodCells, h_goodCells_sub, h_nonempty, h_good_condition⟩

end Kakeya.Assouad

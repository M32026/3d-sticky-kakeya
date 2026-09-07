module

public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Fine Phase Cross-Point Pigeonholing

Lemmas for uniformizing slope-cell counts across points in the fine phase
of the induction on scales (OS Proposition 5.1, Phase B).

## Main results

1. `cell_count_pigeonhole`: select a subset of points whose occupied slope-cell
   counts all lie in a dyadic band [S, 2S), with |P| ≤ (log N + 2) * |P'|.
2. `select_uniform_cell_family`: from a tube family with ≥ S occupied slope
   cells, select exactly S cells and one representative tube per cell.
3. `cross_point_uniform_cells`: combined theorem for cross-point uniformization.

## Whiteprint node
`fine_phase_pigeonhole` under `InductionOnScales/FinePhase/`.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

-- ============================================================================
-- Helper: dyadic level bound (reproduced from Pigeonhole private lemma)
-- ============================================================================

lemma dyadicLevel_bound {w N : ℕ} (hw : w ≤ N) (hN : 0 < N) :
    dyadicLevel w < numDyadicLevels N := by
  have h : dyadicLevel w ≤ Nat.log 2 N + 1 := by
    simp only [dyadicLevel]
    split_ifs with h0
    · simp [numDyadicLevels] <;> omega
    · have h1 : Nat.log 2 w ≤ Nat.log 2 N := by
          gcongr
      simp [numDyadicLevels] at * <;> omega
  simp [numDyadicLevels] at h ⊢ <;> omega

-- ============================================================================
-- Helper: real-valued cardinality pigeonhole
-- ============================================================================

/-- Given a finite set `s` partitioned into `L` level sets by `level : α → ℕ`
with `level x < L` for all `x ∈ s`, find a level `j` whose level set is
nonempty and satisfies `|s| ≤ L * |levelSet j|` (as real numbers). -/
lemma largest_partition_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (L : ℕ) (hL_pos : 0 < L)
    (hs_nonempty : s.Nonempty)
    (level : α → ℕ) (h_level_bound : ∀ x ∈ s, level x < L) :
    ∃ (j : ℕ), (s.filter (fun x => level x = j)).Nonempty ∧
      (s.card : ℝ) ≤ (L : ℝ) * ((s.filter (fun x => level x = j)).card : ℝ) := by
  let levelSet := fun j : ℕ => s.filter (fun x => level x = j)
  have h_disj : (Finset.range L : Set ℕ).PairwiseDisjoint levelSet := by
    intro j _ k _ hjk
    simp only [Finset.disjoint_left, levelSet, Finset.mem_filter]
    intro x hx1 hx2
    have h1 : level x = j := hx1.2
    have h2 : level x = k := hx2.2
    rw [h1] at h2
    exact hjk h2
  have h_union : (Finset.range L).biUnion levelSet = s := by
    ext x
    simp only [Finset.mem_biUnion, levelSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨j, _, hx, _⟩
      exact hx
    · intro hx
      exact ⟨level x, h_level_bound x hx, hx, rfl⟩
  have h_sum : ∑ j ∈ Finset.range L, (levelSet j).card = s.card := by
    rw [←Finset.card_biUnion h_disj, h_union]
  have h_sum_real : ∑ j ∈ Finset.range L, ((levelSet j).card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast h_sum
  have h_range_nonempty : (Finset.range L).Nonempty :=
    Finset.nonempty_range_iff.mpr hL_pos.ne'
  have h_exists : ∃ j ∈ Finset.range L,
      ∀ k ∈ Finset.range L, (levelSet k).card ≤ (levelSet j).card :=
    Finset.exists_max_image (Finset.range L) (fun j => (levelSet j).card) h_range_nonempty
  rcases h_exists with ⟨j, hj_in, h_max⟩
  have h_j_nonempty : (levelSet j).Nonempty := by
    by_contra h_empty
    have h_all_empty : ∀ k ∈ Finset.range L, levelSet k = ∅ := by
      intro k hk
      have h_le : (levelSet k).card ≤ (levelSet j).card := h_max k hk
      have h_j_card : (levelSet j).card = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp h_empty] <;> simp
      rw [h_j_card] at h_le
      have h_k_card : (levelSet k).card = 0 := by omega
      exact Finset.card_eq_zero.mp h_k_card
    have h_union_empty : (Finset.range L).biUnion levelSet = ∅ := by
      have h : ∀ j ∈ Finset.range L, levelSet j = ∅ := h_all_empty
      have h2 : (Finset.range L).biUnion levelSet = (Finset.range L).biUnion (fun _ => ∅) := by
        apply Finset.biUnion_congr rfl
        intro j hj
        exact h j hj
      rw [h2]
      ext x
      simp
    rw [h_union_empty] at h_union
    have h_contra : s = ∅ := h_union.symm
    exact hs_nonempty.ne_empty h_contra
  have h_card_bound : ∀ k ∈ Finset.range L, ((levelSet k).card : ℝ) ≤ ((levelSet j).card : ℝ) := by
    intro k hk
    exact_mod_cast h_max k hk
  have h_main : (s.card : ℝ) ≤ (L : ℝ) * ((levelSet j).card : ℝ) := by
    calc (s.card : ℝ)
      = ∑ k ∈ Finset.range L, ((levelSet k).card : ℝ) := h_sum_real.symm
    _ ≤ ∑ k ∈ Finset.range L, ((levelSet j).card : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact h_card_bound k hk
    _ = (L : ℝ) * ((levelSet j).card : ℝ) := by
      simp [Finset.sum_const] <;> ring
  exact ⟨j, h_j_nonempty, h_main⟩

-- ============================================================================
-- 1. Cross-point cell-count pigeonhole
-- ============================================================================

/-- **Cell count pigeonhole**: Given a finite set of points `P`, each with
a number of occupied slope cells `c(p) ≤ N`, find a dyadic band `[S, 2S)`
such that the subset of points whose cell count lies in the band satisfies
`|P| ≤ (Nat.log 2 N + 2) * |P'|`. -/
lemma cell_count_pigeonhole {α : Type*} [DecidableEq α]
    (P : Finset α) (N : ℕ) (hN : 0 < N)
    (c : α → ℕ) (hc_bound : ∀ p ∈ P, c p ≤ N)
    (hc_pos : ∀ p ∈ P, 0 < c p) :
    ∃ (S : ℕ) (P' : Finset α),
      P' ⊆ P ∧
      (∀ p ∈ P', S ≤ c p ∧ c p < 2 * S) ∧
      (P.card : ℝ) ≤ ((Nat.log 2 N + 2 : ℕ) : ℝ) * (P'.card : ℝ) := by
  let L := numDyadicLevels N
  have hL_pos : 0 < L := by simp [L, numDyadicLevels] <;> omega
  let level : α → ℕ := fun p => dyadicLevel (c p)
  have h_level_bound : ∀ p ∈ P, level p < L := by
    intro p hp
    have h1 : c p ≤ N := hc_bound p hp
    exact dyadicLevel_bound h1 hN
  by_cases hP_empty : P = ∅
  · subst hP_empty
    refine ⟨1, ∅, by simp, by simp, by simp⟩
  · have hP_nonempty : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP_empty
    rcases largest_partition_bound P L hL_pos hP_nonempty level h_level_bound with
      ⟨j0, h_nonempty, h_bound⟩
    let P' := P.filter (fun p => level p = j0)
    have hP'_nonempty : P'.Nonempty := h_nonempty
    have h_j0_pos : 1 ≤ j0 := by
      rcases hP'_nonempty with ⟨p, hp⟩
      have h_cpos : 0 < c p := hc_pos p (Finset.mem_filter.mp hp).1
      have h2 : c p ≠ 0 := by omega
      have h1 : 1 ≤ dyadicLevel (c p) := by
        simp [dyadicLevel, h2] <;> omega
      have hlev : level p = j0 := (Finset.mem_filter.mp hp).2
      have h_eq : dyadicLevel (c p) = j0 := by simpa [level] using hlev
      rw [h_eq] at h1
      exact h1
    let j := j0 - 1
    let S : ℕ := 2 ^ j
    have h_band : ∀ p ∈ P', S ≤ c p ∧ c p < 2 * S := by
      intro p hp
      have hlev : level p = j0 := (Finset.mem_filter.mp hp).2
      have h_cpos : 0 < c p := hc_pos p (Finset.mem_filter.mp hp).1
      have h_ne_zero : c p ≠ 0 := by omega
      have hlog_eq : dyadicLevel (c p) = j0 := by simpa [level] using hlev
      have hlog : Nat.log 2 (c p) + 1 = j0 := by
        have h : dyadicLevel (c p) = Nat.log 2 (c p) + 1 := by
          simp [dyadicLevel, h_ne_zero]
        rw [h] at hlog_eq
        exact hlog_eq
      have hlog2 : Nat.log 2 (c p) = j0 - 1 := by omega
      have h1 : 2^(j0 - 1) ≤ c p := by
        have h3 : 2 ^ Nat.log 2 (c p) ≤ c p := Nat.pow_log_le_self 2 h_ne_zero
        rw [hlog2] at h3
        exact h3
      have h2 : c p < 2 ^ j0 := by
        have h3 : c p < 2 ^ (Nat.log 2 (c p) + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num) (c p)
        rw [hlog] at h3
        exact h3
      have hS1 : S ≤ c p := by
        have h : 2^(j0 - 1) = S := by
          have h5 : j0 - 1 = j := by omega
          rw [h5] <;> rfl
        rw [←h]
        exact h1
      have hS2 : c p < 2 * S := by
        have h : 2^j0 = 2 * S := by
          have h6 : j0 = j + 1 := by omega
          rw [h6] <;> ring
        rw [←h]
        exact h2
      exact ⟨hS1, hS2⟩
    have h_final : (P.card : ℝ) ≤ ((Nat.log 2 N + 2 : ℕ) : ℝ) * (P'.card : ℝ) := by
      have hL_eq : (L : ℝ) = ((Nat.log 2 N + 2 : ℕ) : ℝ) := by
        simp [L, numDyadicLevels] <;> norm_cast
      rw [hL_eq] at h_bound
      exact h_bound
    exact ⟨S, P', Finset.filter_subset _ _, h_band, h_final⟩

-- ============================================================================
-- 2. Selecting S cells and one representative tube per cell
-- ============================================================================

/-- The set of occupied slope cells of a tube family at scale m. -/
def occupiedCells (m : ℕ) {n : ℕ} (F : Finset (DyadicTube n)) : Finset ℤ :=
  F.image (fun (T : DyadicTube n) => localSlopeCellIndex m T.a)

/-- **Select S slope cells** from a tube family that has at least S occupied
cells. Returns a finset of cell indices of cardinality exactly S. -/
lemma select_s_cells (m n : ℕ) (F : Finset (DyadicTube n))
    (S : ℕ) (hS : S ≤ (occupiedCells m F).card) :
    ∃ (cells : Finset ℤ),
      cells ⊆ occupiedCells m F ∧ cells.card = S :=
  Finset.exists_subset_card_eq hS

/-- **Select one representative tube per cell**. -/
lemma select_tube_per_cell (m n : ℕ)
    (F : Finset (DyadicTube n))
    (cells : Finset ℤ)
    (hcells : cells ⊆ occupiedCells m F) :
    ∃ (G : Finset (DyadicTube n)),
      G ⊆ F ∧
      G.card = cells.card ∧
      occupiedCells m G = cells ∧
      Set.InjOn (fun (T : DyadicTube n) => localSlopeCellIndex m T.a) G := by
  have h_choose : ∀ (a : ℤ), a ∈ cells →
      ∃ (T : DyadicTube n), T ∈ F ∧ localSlopeCellIndex m T.a = a := by
    intro a ha
    have h1 : a ∈ occupiedCells m F := hcells ha
    rcases Finset.mem_image.mp h1 with ⟨T, hT, rfl⟩
    exact ⟨T, hT, rfl⟩
  classical
  choose T hT_in hT_cell using h_choose
  -- T : ∀ (a : ℤ), a ∈ cells → DyadicTube n
  -- Define a total function by providing a dummy for a ∉ cells
  let f : ℤ → DyadicTube n := fun a =>
    if h : a ∈ cells then T a h else ⟨0, 0⟩
  let G : Finset (DyadicTube n) := cells.image f
  have hG_sub : G ⊆ F := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨a, ha, rfl⟩
    have h_f_eq : f a = T a ha := by
      simp [f, ha]
    rw [h_f_eq]
    exact hT_in a ha
  have h_f_eq : ∀ a ha, f a = T a ha := by
    intro a ha
    simp [f, ha]
    <;> rfl
  have h_inj : Set.InjOn f cells := by
    intro a1 ha1 a2 ha2 h
    have h_f1 : f a1 = T a1 ha1 := h_f_eq a1 ha1
    have h_f2 : f a2 = T a2 ha2 := h_f_eq a2 ha2
    have h_eq : T a1 ha1 = T a2 ha2 := by
      rw [←h_f1, ←h_f2, h]
    have h1 : localSlopeCellIndex m (T a1 ha1).a = a1 := hT_cell a1 ha1
    have h2 : localSlopeCellIndex m (T a2 ha2).a = a2 := hT_cell a2 ha2
    have h3 : localSlopeCellIndex m (T a1 ha1).a = localSlopeCellIndex m (T a2 ha2).a := by
      rw [h_eq]
    rw [h1, h2] at h3
    exact h3
  have hG_card : G.card = cells.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have hG_cells : occupiedCells m G = cells := by
    have h1 : occupiedCells m G = cells.image (fun a => localSlopeCellIndex m (f a).a) := by
      simp [occupiedCells, G, Finset.image_image] <;> rfl
    rw [h1]
    have h2 : cells.image (fun a => localSlopeCellIndex m (f a).a) = cells.image (fun a => a) := by
      apply Finset.image_congr
      intro a ha
      have hfe : f a = T a ha := h_f_eq a ha
      have h4 : localSlopeCellIndex m (f a).a = a := by
        rw [hfe]
        exact hT_cell a ha
      exact h4
    rw [h2]
    simp
  have hG_inj : Set.InjOn (fun (T : DyadicTube n) => localSlopeCellIndex m T.a) G := by
    intro T1 hT1 T2 hT2 h
    rcases Finset.mem_image.mp hT1 with ⟨a1, ha1, rfl⟩
    rcases Finset.mem_image.mp hT2 with ⟨a2, ha2, rfl⟩
    have h_f1 : f a1 = T a1 ha1 := h_f_eq a1 ha1
    have h_f2 : f a2 = T a2 ha2 := h_f_eq a2 ha2
    have h1 : localSlopeCellIndex m (f a1).a = localSlopeCellIndex m (f a2).a := h
    have h1' : localSlopeCellIndex m (T a1 ha1).a = localSlopeCellIndex m (T a2 ha2).a := by
      rw [←h_f1, ←h_f2]
      exact h1
    have h3 : localSlopeCellIndex m (T a1 ha1).a = a1 := hT_cell a1 ha1
    have h4 : localSlopeCellIndex m (T a2 ha2).a = a2 := hT_cell a2 ha2
    rw [h3, h4] at h1'
    have h5 : a1 = a2 := h1'
    rw [h5]
  exact ⟨G, hG_sub, hG_card, hG_cells, hG_inj⟩

/-- **Combined: select S cells and one tube per cell** from a family with
at least S occupied slope cells. -/
lemma select_uniform_cell_family (m n : ℕ)
    (F : Finset (DyadicTube n)) (S : ℕ)
    (hS : S ≤ (occupiedCells m F).card) :
    ∃ (G : Finset (DyadicTube n)),
      G ⊆ F ∧
      G.card = S ∧
      (occupiedCells m G).card = S ∧
      Set.InjOn (fun (T : DyadicTube n) => localSlopeCellIndex m T.a) G := by
  rcases select_s_cells m n F S hS with ⟨cells, hcells_sub, hcells_card⟩
  rcases select_tube_per_cell m n F cells hcells_sub with
    ⟨G, hG_sub, hG_card, hG_cells, hG_inj⟩
  have h1 : G.card = S := by
    rw [hG_card, hcells_card]
  have h2 : (occupiedCells m G).card = S := by
    rw [hG_cells, hcells_card]
  exact ⟨G, hG_sub, h1, h2, hG_inj⟩

-- ============================================================================
-- 3. Cross-point uniform cell count theorem
-- ============================================================================

/-- **Cross-point uniformization**: Given points P each with a tube family,
find a subset P' and a uniform cell count S such that:
- Every p ∈ P' has ≥ S occupied slope cells
- |P| ≤ (log N + 2) * |P'|
- For each p ∈ P', we can select a subfamily G_p of size S with distinct
  slope cells (one tube per cell) -/
theorem cross_point_uniform_cells {n m : ℕ} {α : Type*} [DecidableEq α]
    (P : Finset α) (N : ℕ) (hN : 0 < N)
    (fam : α → Finset (DyadicTube n))
    (h_bound : ∀ p ∈ P, (fam p).card ≤ N)
    (hF_nonempty : ∀ p ∈ P, (fam p).Nonempty) :
    ∃ (S : ℕ) (hS_pos : 0 < S) (P' : Finset α)
      (hP'_sub : P' ⊆ P)
      (selected : ∀ (p : α), p ∈ P' → Finset (DyadicTube n)),
      (P.card : ℝ) ≤ ((Nat.log 2 N + 2 : ℕ) : ℝ) * (P'.card : ℝ) ∧
      (∀ p hp, (selected p hp) ⊆ fam p) ∧
      (∀ p hp, (selected p hp).card = S) ∧
      (∀ p hp, Set.InjOn (fun (T : DyadicTube n) => localSlopeCellIndex m T.a) (selected p hp)) := by
  let c : α → ℕ := fun p => (occupiedCells m (fam p)).card
  have hc_bound : ∀ p ∈ P, c p ≤ N := by
    intro p hp
    have h1 : c p ≤ (fam p).card := by
      dsimp only [c]
      exact Finset.card_image_le
    have h2 : (fam p).card ≤ N := h_bound p hp
    exact le_trans h1 h2
  by_cases hP_empty : P = ∅
  · subst hP_empty
    refine ⟨1, by norm_num, ∅, by simp, fun _ _ => ∅, by simp, by simp, by simp, by simp⟩
  · have hc_pos : ∀ p ∈ P, 0 < c p := by
      intro p hp
      have hF_nonempty' : (fam p).Nonempty := hF_nonempty p hp
      have h_img_nonempty : (occupiedCells m (fam p)).Nonempty :=
        Finset.Nonempty.image hF_nonempty' _
      dsimp only [c]
      exact h_img_nonempty.card_pos
    have hP_nonempty : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP_empty
    rcases cell_count_pigeonhole P N hN c hc_bound hc_pos with
      ⟨S, P', hP'_sub, h_band, h_card⟩
    have hS_le : ∀ p ∈ P', S ≤ (occupiedCells m (fam p)).card := by
      intro p hp
      exact (h_band p hp).1
    let selected : ∀ (p : α), p ∈ P' → Finset (DyadicTube n) := fun p hp =>
      Classical.choose (select_uniform_cell_family m n (fam p) S (hS_le p hp))
    have h_selected_spec : ∀ (p : α) (hp : p ∈ P'),
        (selected p hp) ⊆ fam p ∧
        (selected p hp).card = S ∧
        (occupiedCells m (selected p hp)).card = S ∧
        Set.InjOn (fun (T : DyadicTube n) => localSlopeCellIndex m T.a) (selected p hp) := by
      intro p hp
      exact Classical.choose_spec (select_uniform_cell_family m n (fam p) S (hS_le p hp))
    have hP'_nonempty : P'.Nonempty := by
      by_contra h
      have h_empty : P' = ∅ := by simpa using h
      rw [h_empty] at h_card
      have hP_pos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
      have h_card0 : (P.card : ℝ) ≤ 0 := by
        simpa [Finset.card_empty] using h_card
      exact not_le.mpr hP_pos h_card0
    have hS_pos : 0 < S := by
      rcases hP'_nonempty with ⟨p, hp⟩
      have h_band_p : S ≤ c p ∧ c p < 2 * S := h_band p hp
      by_contra hS0
      have hS0' : S = 0 := by omega
      rw [hS0'] at h_band_p
      have h3 : c p < 0 := h_band_p.2
      exact Nat.not_lt_zero (c p) h3
    refine ⟨S, hS_pos, P', hP'_sub, selected, h_card, ?_⟩
    constructor
    · intro p hp
      exact (h_selected_spec p hp).1
    · constructor
      · intro p hp
        exact (h_selected_spec p hp).2.1
      · intro p hp
        exact (h_selected_spec p hp).2.2.2

end InductionOnScales

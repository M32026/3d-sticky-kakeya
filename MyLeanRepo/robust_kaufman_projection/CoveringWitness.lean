module

public import MyLeanRepo.robust_kaufman_projection.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Covering witness for bounded sets in ℝ

Given a bounded set `A ⊂ ℝ` and `δ > 0`, constructs a strictly `2δ`-separated
subset `R ⊆ A` whose cardinality equals the `δ`-external covering number of `A`.

Uses a greedy infimum sequence from left to right, then backward perturbation
to extract points in A with strict 2δ-separation and exact covering cardinality.

Whiteprint node: covering_witness
Dependencies: base
-/

noncomputable section

open scoped ENNReal NNReal
open Metric Set Finset Classical

lemma ncover_witness_subset {A : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hA_bounded : Bornology.IsBounded A) (hA_nonempty : A.Nonempty) :
    ∃ (R : Finset ℝ), (R : Set ℝ) ⊆ A ∧
      (∀ x ∈ R, ∀ y ∈ R, x ≠ y → 2 * δ < |x - y|) ∧
      (R.card : ENNReal) = Ncover δ A := by
  classical

  -- Bounds
  have hA_bdd_below : BddBelow A := hA_bounded.bddBelow
  have hA_bdd_above : BddAbove A := hA_bounded.bddAbove
  let L : ℝ := sInf A
  let U : ℝ := sSup A
  have hL : ∀ x ∈ A, L ≤ x := fun x hx => csInf_le hA_bdd_below hx
  have hU : ∀ x ∈ A, x ≤ U := fun x hx => le_csSup hA_bdd_above hx
  have hLU : L ≤ U := by
    let x := Classical.choose hA_nonempty
    have hx : x ∈ A := Classical.choose_spec hA_nonempty
    exact le_trans (hL x hx) (hU x hx)

  -- Greedy sequence of left endpoints
  let a : ℕ → ℝ := fun n => Nat.recOn n L fun k prev => sInf {x ∈ A | x > prev + 2 * δ}
  let S : ℕ → Set ℝ := fun k => match k with | 0 => A | k+1 => {x ∈ A | x > a k + 2 * δ}
  have ha_eq : ∀ k, a k = sInf (S k) := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => simp [a, S, ih] <;> rfl
  have hS_sub : ∀ k, S k ⊆ A := by intro k; cases k <;> simp [S] <;> tauto
  have hS_bdd : ∀ k, BddBelow (S k) := fun k => BddBelow.mono (hS_sub k) hA_bdd_below
  let active : ℕ → Prop := fun k => (S k).Nonempty

  have h_active0 : active 0 := hA_nonempty

  -- If active k, then a k ≤ U
  have h_a_le_U : ∀ k, active k → a k ≤ U := by
    intro k hak
    rcases hak with ⟨x, hx⟩
    have h_xA : x ∈ A := hS_sub k hx
    have h1 : a k ≤ x := by
      rw [ha_eq k]
      exact csInf_le (hS_bdd k) hx
    have h2 : x ≤ U := hU x h_xA
    linarith

  -- If active (k+1), then a (k+1) ≥ a k + 2δ
  have h_step : ∀ k, active (k+1) → a (k+1) ≥ a k + 2 * δ := by
    intro k hak
    rw [ha_eq (k+1)]
    have h_bound : ∀ y ∈ S (k+1), a k + 2 * δ ≤ y := by
      intro y hy
      have h_lt : a k + 2 * δ < y := by simpa [S] using hy.2
      exact le_of_lt h_lt
    exact le_csInf hak h_bound

  -- Growth: a (k+n) ≥ a k + 2*n*δ when all intermediate are active
  have h_growth_ind : ∀ (k n : ℕ), (∀ j, k ≤ j → j ≤ k+n → active j) →
      a (k+n) ≥ a k + 2 * (n : ℝ) * δ := by
    intro k n hall
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have h_act : active (k+n+1) := hall (k+n+1) (by omega) (by omega)
      have h_ih' : a (k+n) ≥ a k + 2 * (n : ℝ) * δ :=
        ih (fun j h1 h2 => hall j h1 (by omega))
      have h4 : a (k+n+1) ≥ a (k+n) + 2 * δ := h_step (k+n) h_act
      have h_goal : a (k+n+1) ≥ a k + 2 * ((n + 1 : ℕ) : ℝ) * δ := by
        calc a (k+n+1) ≥ a (k+n) + 2 * δ := h4
          _ ≥ a k + 2 * (n : ℝ) * δ + 2 * δ := by linarith
          _ = a k + 2 * ((n + 1 : ℕ) : ℝ) * δ := by
            simp [Nat.cast_add] <;> ring
      exact h_goal

  -- Existence of stopping time M
  have h_exists_stop : ∃ M, ¬active M := by
    by_contra h
    push Not at h
    have h_all : ∀ k, active k := h
    have h1 : ∀ k, a k ≥ L + 2 * (k : ℝ) * δ := by
      intro k
      have h := h_growth_ind 0 k (fun j _ _ => h_all j)
      simpa [a] using h
    have h2 : ∀ k, a k ≤ U := fun k => h_a_le_U k (h_all k)
    obtain ⟨K, hK⟩ := exists_nat_gt ((U - L) / (2 * δ))
    have h3 : a K ≥ L + 2 * (K : ℝ) * δ := h1 K
    have h4 : a K ≤ U := h2 K
    have h5 : 2 * (K : ℝ) * δ > U - L := by
      have h6 : (K : ℝ) > (U - L) / (2 * δ) := hK
      have h7 : 0 < 2 * δ := by positivity
      calc 2 * (K : ℝ) * δ = (K : ℝ) * (2 * δ) := by ring
        _ > ((U - L) / (2 * δ)) * (2 * δ) := by gcongr
        _ = U - L := by field_simp [h7.ne'] <;> ring
    linarith

  let M : ℕ := Nat.find h_exists_stop
  have hM_not : ¬active M := Nat.find_spec h_exists_stop
  have hM_pos : 0 < M := by
    by_cases h : M = 0
    · rw [h] at hM_not
      exact False.elim (hM_not h_active0)
    · omega
  have h_active_lt : ∀ k < M, active k := by
    intro k hk; by_contra h; exact Nat.find_min h_exists_stop hk h

  -- Growth between arbitrary indices below M
  have h_growth2 : ∀ (k l : ℕ), k < l → l < M → a l ≥ a k + 2 * ((l : ℝ) - (k : ℝ)) * δ := by
    intro k l hkl hlt
    have h_all : ∀ j, k ≤ j → j ≤ l → active j := fun j _ hj => h_active_lt j (by omega)
    have h := h_growth_ind k (l - k) (fun j h1 h2 =>
      have h3 : j ≤ l := by omega
      h_all j h1 h3)
    have h6 : k + (l - k) = l := by omega
    rw [h6] at h
    have h7 : ((l - k : ℕ) : ℝ) = (l : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub (show k ≤ l from by omega)] <;> simp
    rw [h7] at h
    exact h

  -- Coverage: A ⊆ ⋃_{k < M} [a k, a k + 2δ]
  have h_cover : ∀ x ∈ A, ∃ k : ℕ, k < M ∧ a k ≤ x ∧ x ≤ a k + 2 * δ := by
    intro x hx
    classical
    have h_last : x ≤ a (M-1) + 2 * δ := by
      by_contra h
      have h_gt : x > a (M-1) + 2 * δ := by linarith
      have hM_ne_zero : M ≠ 0 := by omega
      have hSM_eq : S M = {y ∈ A | y > a (M-1) + 2 * δ} := by
        rcases Nat.exists_eq_succ_of_ne_zero hM_ne_zero with ⟨M', hM'⟩
        rw [hM']
        simp [S] <;> rfl
      have h_xS : x ∈ S M := by
        rw [hSM_eq]
        exact ⟨hx, h_gt⟩
      exact hM_not ⟨x, h_xS⟩
    let Kfin : Finset ℕ := by
      letI : DecidablePred (fun k : ℕ => a k ≤ x) := Classical.decPred _
      exact Finset.filter (fun k => a k ≤ x) (Finset.range M)
    have hK_mem_iff : ∀ (k : ℕ), k ∈ Kfin ↔ k ∈ Finset.range M ∧ a k ≤ x := by
      intro k
      simp [Kfin, Finset.mem_filter]
      <;> tauto
    have hK_nonempty : Kfin.Nonempty := by
      refine ⟨0, ?_⟩
      have h0 : a 0 ≤ x := by simpa [a] using hL x hx
      have h0_in : 0 ∈ Kfin := (hK_mem_iff 0).mpr ⟨Finset.mem_range.mpr (by omega), h0⟩
      exact h0_in
    let k := Kfin.max' hK_nonempty
    have hk_mem : k ∈ Kfin := Finset.max'_mem Kfin hK_nonempty
    have hk_filter : k ∈ Finset.range M ∧ a k ≤ x := (hK_mem_iff k).mp hk_mem
    have hk_lt_M : k < M := Finset.mem_range.mp hk_filter.1
    have hk_ale : a k ≤ x := hk_filter.2
    have hk_max : ∀ l ∈ Kfin, l ≤ k := fun l hl => Finset.le_max' Kfin l hl
    have h_x_le : x ≤ a k + 2 * δ := by
      by_contra h
      have h_gt : a k + 2 * δ < x := by linarith
      have h_xS : x ∈ S (k+1) := by
        simp [S, hx, h_gt] <;> tauto
      by_cases h_k1 : k+1 < M
      · have h_ak1 : a (k+1) ≤ x := by
          rw [ha_eq (k+1)]
          exact csInf_le (hS_bdd (k+1)) h_xS
        have h_k1_in : k+1 ∈ Kfin := (hK_mem_iff (k+1)).mpr ⟨Finset.mem_range.mpr h_k1, h_ak1⟩
        have h_cont : k+1 ≤ k := hk_max (k+1) h_k1_in
        omega
      · have h_k1_eq : k+1 = M := by omega
        rw [h_k1_eq] at h_xS
        exact hM_not ⟨x, h_xS⟩
    exact ⟨k, hk_lt_M, hk_ale, h_x_le⟩

  -- Upper bound: Ncover δ A ≤ M
  let centers : Finset ℕ := Finset.range M
  let C : Finset ℝ := Finset.image (fun k : ℕ => a k + δ) centers
  have hC_inj : Set.InjOn (fun k : ℕ => a k + δ) (centers : Set ℕ) := by
    intro k hk l hl h
    have hk' : k < M := Finset.mem_range.mp hk
    have hl' : l < M := Finset.mem_range.mp hl
    by_cases hkl : k < l
    · have h_g : a l ≥ a k + 2 * ((l : ℝ) - (k : ℝ)) * δ := h_growth2 k l hkl hl'
      have h7 : a l + δ > a k + δ := by
        have h8 : (l : ℝ) - (k : ℝ) ≥ 1 := by
          have h9 : k + 1 ≤ l := by omega
          have h10 : (l : ℝ) ≥ (k : ℝ) + 1 := by exact_mod_cast h9
          linarith
        nlinarith
      linarith
    · by_cases hlk : l < k
      · have h_g : a k ≥ a l + 2 * ((k : ℝ) - (l : ℝ)) * δ := h_growth2 l k hlk hk'
        have h7 : a k + δ > a l + δ := by
          have h8 : (k : ℝ) - (l : ℝ) ≥ 1 := by
            have h9 : l + 1 ≤ k := by omega
            have h10 : (k : ℝ) ≥ (l : ℝ) + 1 := by exact_mod_cast h9
            linarith
          nlinarith
        linarith
      · have h_eq : k = l := by omega
        exact h_eq
  have hC_card : C.card = M := by
    rw [Finset.card_image_of_injOn hC_inj, Finset.card_range]
  have hC_cover : Metric.IsCover δ.toNNReal A (C : Set ℝ) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    intro x hx
    rcases h_cover x hx with ⟨k, hk_lt_M, hk_ale, hk_xle⟩
    have h_rad : (δ.toNNReal : ℝ) = δ := by rw [Real.coe_toNNReal δ] <;> linarith
    have h_dist : dist x (a k + δ) ≤ (δ.toNNReal : ℝ) := by
      rw [h_rad, Real.dist_eq]
      have h2 : |x - (a k + δ)| ≤ δ := by rw [abs_le] <;> constructor <;> linarith
      exact h2
    have h1 : x ∈ closedBall (a k + δ) δ.toNNReal := h_dist
    have h3 : a k + δ ∈ (C : Set ℝ) := by
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk_lt_M)
    exact Set.mem_iUnion₂.mpr ⟨a k + δ, h3, h1⟩
  have h_upper : Ncover δ A ≤ (M : ENNReal) := by
    have h4 := Metric.IsCover.externalCoveringNumber_le_encard hC_cover
    have h5 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤ ((C.card : ENat) : ENNReal) := by
      exact_mod_cast h4
    rw [hC_card] at h5
    simpa [Ncover] using h5

  -- Near-infimum property: for active k and ε > 0, ∃ x ∈ S k with a k ≤ x < a k + ε
  have h_near : ∀ k, active k → ∀ ε : ℝ, 0 < ε → ∃ (x : ℝ), x ∈ S k ∧ a k ≤ x ∧ x < a k + ε := by
    intro k hak ε hε
    have h_active_k : active k := hak
    rcases hak with ⟨y, hy⟩
    have h1 : a k ≤ y := by
      rw [ha_eq k]
      exact csInf_le (hS_bdd k) hy
    by_cases h : y < a k + ε
    · exact ⟨y, hy, h1, h⟩
    · have h' : a k + ε ≤ y := by linarith
      have h_exists : ∃ (x : ℝ), x ∈ S k ∧ x < a k + ε := by
        by_contra h2
        push Not at h2
        have h3 : ∀ x ∈ S k, a k + ε ≤ x := by
          intro x hx
          exact h2 x hx
        have h4 : a k + ε ≤ a k := by
          have h5 : ∀ b ∈ S k, sInf (S k) + ε ≤ b := by
            intro b hb
            have h6 : a k + ε ≤ b := h3 b hb
            have h7 : a k = sInf (S k) := by rw [ha_eq k]
            rw [h7] at h6
            exact h6
          have h8 : sInf (S k) + ε ≤ sInf (S k) := le_csInf h_active_k h5
          have h9 : a k = sInf (S k) := by rw [ha_eq k]
          rw [h9]
          exact h8
        linarith
      rcases h_exists with ⟨x, hxS, hx_lt⟩
      have h5 : a k ≤ x := by
        rw [ha_eq k]
        exact csInf_le (hS_bdd k) hxS
      exact ⟨x, hxS, h5, hx_lt⟩

  -- Backward construction of points in A
  let P : ℕ → ℝ → Prop := fun j x =>
    x ∈ S (M-1-j) ∧ a (M-1-j) ≤ x

  have h_base : ∃ (x : ℝ), P 0 x := by
    have h_act : active (M-1) := h_active_lt (M-1) (by omega)
    rcases h_near (M-1) h_act 1 (by norm_num) with ⟨x, hxS, hx_ge, _⟩
    exact ⟨x, hxS, hx_ge⟩
  let f0 : ℝ := Classical.choose h_base
  have hf0 : P 0 f0 := Classical.choose_spec h_base

  have h_step_exists : ∀ (j : ℕ), j < M-1 → ∀ (prev : ℝ), P j prev →
      ∃ (x : ℝ), P (j+1) x ∧ prev - x > 2 * δ := by
    intro j hj prev hprev
    let k : ℕ := M-2-j
    have h_k_lt_M : k < M := by omega
    have h_act_k : active k := h_active_lt k h_k_lt_M
    have h_k1_eq : k + 1 = M - 1 - j := by omega
    have h_prev_in_S : prev ∈ S (k+1) := by
      rw [h_k1_eq]
      exact hprev.1
    have h_prev_gt : prev > a k + 2 * δ := by
      have h : S (k+1) = {y ∈ A | y > a k + 2 * δ} := by simp [S] <;> rfl
      rw [h] at h_prev_in_S
      exact h_prev_in_S.2
    set ε : ℝ := prev - (a k + 2 * δ) with hε_def
    have hε_pos : 0 < ε := by linarith
    rcases h_near k h_act_k (ε / 2) (by linarith) with ⟨x, hxS, hx_ge, hx_lt⟩
    have h_px : prev - x > 2 * δ := by
      linarith [hε_def, hx_lt]
    have h_target_eq : M - 1 - (j + 1) = k := by omega
    have hP_x : P (j+1) x := by
      constructor
      · rw [h_target_eq] <;> exact hxS
      · rw [h_target_eq] <;> exact hx_ge
    exact ⟨x, hP_x, h_px⟩

  let step_fun (j : ℕ) (prev : ℝ) : ℝ := by
    classical
    exact if hj : j < M-1 then
      if hP : P j prev then
        Classical.choose (h_step_exists j hj prev hP)
      else 0
    else 0
  let f : ℕ → ℝ := fun j => Nat.recOn j f0 step_fun

  have hP_f : ∀ j, j < M → P j (f j) := by
    intro j hj
    induction j with
    | zero => exact hf0
    | succ j ih =>
      have h_j_lt : j < M-1 := by omega
      have hP_j : P j (f j) := ih (by omega)
      have h_f_succ : f (j+1) = step_fun j (f j) := by rfl
      have h_step_eq : step_fun j (f j) = Classical.choose (h_step_exists j h_j_lt (f j) hP_j) := by
        unfold step_fun
        rw [dif_pos h_j_lt, dif_pos hP_j]
      rw [h_f_succ, h_step_eq]
      exact (Classical.choose_spec (h_step_exists j h_j_lt (f j) hP_j)).1

  have h_sep_step : ∀ j, j < M-1 → f j - f (j+1) > 2 * δ := by
    intro j hj
    have hP_j : P j (f j) := hP_f j (by omega)
    have h_f_succ : f (j+1) = step_fun j (f j) := by rfl
    have h_step_eq : step_fun j (f j) = Classical.choose (h_step_exists j hj (f j) hP_j) := by
      unfold step_fun
      rw [dif_pos hj, dif_pos hP_j]
    rw [h_f_succ, h_step_eq]
    exact (Classical.choose_spec (h_step_exists j hj (f j) hP_j)).2

  have h_helper : ∀ (i n : ℕ), 0 < n → i + n < M → f i - f (i+n) > 2 * (n : ℝ) * δ := by
    intro i n hn h_lt
    induction n with
    | zero => exfalso; linarith
    | succ n ih =>
      by_cases h_n0 : n = 0
      · subst h_n0
        have h' : i < M-1 := by omega
        have h : f i - f (i+1) > 2 * δ := h_sep_step i h'
        simpa using h
      · have h_n_pos : 0 < n := by omega
        have h_ih' : f i - f (i+n) > 2 * (n : ℝ) * δ := ih h_n_pos (by omega)
        have h_step' : i + n < M-1 := by omega
        have h2 : f (i+n) - f (i+n+1) > 2 * δ := h_sep_step (i+n) h_step'
        have h_goal : f i - f (i+n+1) > 2 * ((n + 1 : ℕ) : ℝ) * δ := by
          calc f i - f (i+n+1) = (f i - f (i+n)) + (f (i+n) - f (i+n+1)) := by ring
            _ > 2 * (n : ℝ) * δ + 2 * δ := by linarith
            _ = 2 * ((n + 1 : ℕ) : ℝ) * δ := by simp [Nat.cast_add] <;> ring
        exact h_goal

  have h_sep_cumul : ∀ (i j : ℕ), i < j → j < M → f i - f j > 2 * ((j : ℝ) - (i : ℝ)) * δ := by
    intro i j h_ij h_jlt
    let n := j - i
    have h_n_pos : 0 < n := by omega
    have h_j_eq : j = i + n := by omega
    have h_lt : i + n < M := by rw [←h_j_eq] <;> exact h_jlt
    have h := h_helper i n h_n_pos h_lt
    have h9 : (n : ℝ) = (j : ℝ) - (i : ℝ) := by
      have h10 : n = j - i := by rfl
      rw [h10, Nat.cast_sub (show i ≤ j from by omega)] <;> simp
    have h11 : i + n = j := by omega
    rw [h11] at h
    rw [h9] at h
    exact h

  have h_f_inj : Set.InjOn f (Finset.range M : Set ℕ) := by
    intro i hi j hj h_eq
    have h_i_lt_M : i < M := Finset.mem_range.mp hi
    have h_j_lt_M : j < M := Finset.mem_range.mp hj
    by_cases h : i < j
    · have h_diff_pos : 0 < (j : ℝ) - (i : ℝ) := by
        have h10 : (i : ℝ) < (j : ℝ) := by exact_mod_cast h
        linarith
      have h'' : f i - f j > 2 * ((j : ℝ) - (i : ℝ)) * δ := h_sep_cumul i j h h_j_lt_M
      have h_pos2 : 0 < 2 * ((j : ℝ) - (i : ℝ)) * δ := by positivity
      have h' : f i - f j > 0 := by linarith
      have h_ne : f i ≠ f j := by linarith
      exact False.elim (h_ne h_eq)
    · by_cases h2 : j < i
      · have h_diff_pos : 0 < (i : ℝ) - (j : ℝ) := by
          have h10 : (j : ℝ) < (i : ℝ) := by exact_mod_cast h2
          linarith
        have h'' : f j - f i > 2 * ((i : ℝ) - (j : ℝ)) * δ := h_sep_cumul j i h2 h_i_lt_M
        have h_pos2 : 0 < 2 * ((i : ℝ) - (j : ℝ)) * δ := by positivity
        have h' : f j - f i > 0 := by linarith
        have h_ne : f j ≠ f i := by linarith
        exact False.elim (h_ne h_eq.symm)
      · have h_eq2 : i = j := by omega
        exact h_eq2

  let R : Finset ℝ := Finset.image f (Finset.range M)
  have hR_card : R.card = M := by
    rw [Finset.card_image_of_injOn h_f_inj, Finset.card_range]

  have hR_sub : (R : Set ℝ) ⊆ A := by
    intro x hx
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨j, hj, rfl⟩
    have h_j_lt_M : j < M := Finset.mem_range.mp hj
    have hP : P j (f j) := hP_f j h_j_lt_M
    have h_in_S : f j ∈ S (M-1-j) := hP.1
    exact hS_sub (M-1-j) h_in_S

  have hR_sep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 2 * δ < |x - y| := by
    intro x hx y hy hne
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨j, hj, rfl⟩
    have h_i_lt_M : i < M := Finset.mem_range.mp hi
    have h_j_lt_M : j < M := Finset.mem_range.mp hj
    by_cases h_ij : i < j
    · have h_diff_ge1 : (j : ℝ) - (i : ℝ) ≥ 1 := by
        have h10 : i + 1 ≤ j := by omega
        have h11 : ((i + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h10
        simp [Nat.cast_add] at h11
        linarith
      have h' : f i - f j > 2 * ((j : ℝ) - (i : ℝ)) * δ := h_sep_cumul i j h_ij h_j_lt_M
      have h : f i - f j > 2 * δ := by
        calc f i - f j > 2 * ((j : ℝ) - (i : ℝ)) * δ := h'
          _ ≥ 2 * 1 * δ := by gcongr
          _ = 2 * δ := by ring
      have h_pos : 0 < f i - f j := by linarith
      have h_abs : |f i - f j| = f i - f j := by rw [abs_of_pos h_pos]
      rw [h_abs] <;> linarith
    · by_cases h_ji : j < i
      · have h_diff_ge1 : (i : ℝ) - (j : ℝ) ≥ 1 := by
          have h10 : j + 1 ≤ i := by omega
          have h11 : ((j + 1 : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast h10
          simp [Nat.cast_add] at h11
          linarith
        have h' : f j - f i > 2 * ((i : ℝ) - (j : ℝ)) * δ := h_sep_cumul j i h_ji h_i_lt_M
        have h : f j - f i > 2 * δ := by
          calc f j - f i > 2 * ((i : ℝ) - (j : ℝ)) * δ := h'
            _ ≥ 2 * 1 * δ := by gcongr
            _ = 2 * δ := by ring
        have h_pos : 0 < f j - f i := by linarith
        have h_abs : |f j - f i| = f j - f i := by rw [abs_of_pos h_pos]
        have h_comm : |f i - f j| = |f j - f i| := by rw [abs_sub_comm]
        rw [h_comm, h_abs] <;> linarith
      · have h_eq : i = j := by omega
        exfalso
        exact hne (by congr)

  -- Lower bound: M ≤ Ncover δ A via packing-covering inequality
  let ε : NNReal := δ.toNNReal
  have hε : (ε : ℝ) = δ := by
    rw [Real.coe_toNNReal δ] <;> linarith
  have hR_is_sep : IsSeparated (2 * ε) (R : Set ℝ) := by
    intro x hx y hy hne
    have h : 2 * δ < |x - y| := hR_sep x hx y hy hne
    have h_edist : edist x y = ENNReal.ofReal |x - y| := by
      rw [edist_dist, Real.dist_eq]
    rw [h_edist]
    have h_abs_pos : 0 < |x - y| := by linarith [h, hδ]
    have h_coe : (2 * (↑ε : ENNReal)) = ENNReal.ofReal (2 * δ) := by
      have h9 : (2 * (↑ε : ENNReal)) = ↑(2 * ε) := by simp
      rw [h9]
      simp [ε, hε] <;> norm_cast
    rw [h_coe]
    exact (ENNReal.ofReal_lt_ofReal_iff h_abs_pos).mpr h
  have h1 : (R : Set ℝ).encard ≤ packingNumber (2 * ε) A :=
    IsSeparated.encard_le_packingNumber hR_sub hR_is_sep
  have h2 : packingNumber (2 * ε) A ≤ externalCoveringNumber ε A :=
    packingNumber_two_mul_le_externalCoveringNumber ε A
  have h3 : (R : Set ℝ).encard ≤ externalCoveringNumber ε A := le_trans h1 h2
  have h4 : (R : Set ℝ).encard = ↑R.card := by simp
  rw [h4] at h3
  have h_lower : (R.card : ENNReal) ≤ Ncover δ A := by
    have h5 : (externalCoveringNumber ε A : ENNReal) = Ncover δ A := by
      simp [Ncover, ε, hε] <;> rfl
    have h6 : (↑R.card : ENNReal) ≤ (externalCoveringNumber ε A : ENNReal) := by
      exact_mod_cast h3
    rw [h5] at h6
    exact h6

  have h_eq : (R.card : ENNReal) = Ncover δ A :=
    le_antisymm h_lower (by rw [hR_card] <;> exact h_upper)

  exact ⟨R, hR_sub, hR_sep, h_eq⟩

end

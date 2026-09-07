module

/-
# Full Discretized Plünnecke-Ruzsa Inequality

Extends `DiscretizedPluennecke.lean` (which gives Ruzsa triangle) to the full
Plünnecke-Ruzsa inequality for dyadic covering numbers.

## Main results

Given `N(A+B, δ) ≤ K · N(A, δ)`:
1. `discretized_pluennecke_nfold_sum`: `N(nB, δ) ≤ n · (2K)^n · N(A, δ)`
2. `discretized_pluennecke_nfold_diff`: `N(mB - nB, δ) ≤ (m+n) · (2K)^(m+n) · N(A, δ)`

## Proof route

1. Associate bounded sets to finite cube index sets `I(S) : Finset ℤ`.
2. Show `I(A)+I(B) ⊆ I(A+B) + {-1,0}`, so `|I(A)+I(B)| ≤ 2·|I(A+B)|`.
3. Apply Mathlib's finite Plünnecke-Ruzsa to the index sets.
4. Show iterated index inclusions:
   `I(nB) ⊆ n•I(B) + {0,...,n-1}`
   `I(mB - nB) ⊆ m•I(B) - n•I(B) + {-n,...,m-1}`
5. Combine and convert back to covering numbers.

## Whiteprint node
`WeakTwoEnds/OSW/DiscretizedPluenneckeFull`
-/

public import MyLeanRepo.DiscretizedPluennecke
public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence

open ProductLikeIncidence (realCubeIndexSet realCubeIndexSet_finite
  realCoveringNumber_eq_card sum_index_inclusion sum_index_inclusion_rev
  bounded_image2_add bounded_image2_sub
  finset_pointwise_add_card_le)

/-! ## Iterated sumset -/

/-- n-fold iterated sumset: `0 • B = {0}`, `(n+1) • B = B + n • B`. -/
def nfoldSum : ℕ → Set ℝ → Set ℝ
  | 0, _ => {0}
  | n + 1, B => Set.image2 (· + ·) B (nfoldSum n B)

lemma nfoldSum_bounded {n : ℕ} {B : Set ℝ} (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (nfoldSum n B) := by
  induction n with
  | zero => exact Set.finite_singleton 0 |>.isBounded
  | succ n ih => exact bounded_image2_add hB ih

lemma nfoldSum_one {B : Set ℝ} : nfoldSum 1 B = B := by
  simp [nfoldSum] <;> ext x <;> simp [Set.mem_image2] <;>
    constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> simp_all

/-! ## Generalized difference index inclusion -/

/-- If k indexes a cube meeting X - Y, then `k = i - j + e` with
    `i ∈ I(X)`, `j ∈ I(Y)`, `e ∈ {-1, 0}`. -/
lemma diff_index_inclusion {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ} :
    realCubeIndexSet δ (Set.image2 (· - ·) X Y) ⊆
      (realCubeIndexSet δ X - realCubeIndexSet δ Y) + ({-1, 0} : Set ℤ) := by
  intro k hk
  simp only [realCubeIndexSet, Set.mem_setOf_eq] at hk
  rcases hk with ⟨w, ⟨hw1, hw2⟩, ⟨x, hxX, y, hyY, rfl⟩⟩
  let i : ℤ := Int.floor (x / δ)
  let j : ℤ := Int.floor (y / δ)
  have hi1 : δ * (i : ℝ) ≤ x := by
    have h : (i : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h' : δ * (i : ℝ) ≤ δ * (x / δ) := by gcongr
    have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hi2 : x < δ * ((i : ℝ) + 1) := by
    have h : x / δ < (i : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h' : δ * (x / δ) < δ * ((i : ℝ) + 1) := by gcongr
    have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hj1 : δ * (j : ℝ) ≤ y := by
    have h : (j : ℝ) ≤ y / δ := Int.floor_le (y / δ)
    have h' : δ * (j : ℝ) ≤ δ * (y / δ) := by gcongr
    have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hj2 : y < δ * ((j : ℝ) + 1) := by
    have h : y / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
    have h' : δ * (y / δ) < δ * ((j : ℝ) + 1) := by gcongr
    have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hiX : i ∈ realCubeIndexSet δ X := by
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    exact ⟨x, ⟨hi1, hi2⟩, hxX⟩
  have hjY : j ∈ realCubeIndexSet δ Y := by
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    exact ⟨y, ⟨hj1, hj2⟩, hyY⟩
  have h1 : δ * (k : ℝ) ≤ x - y := hw1
  have h2 : x - y < δ * (((i - j : ℤ) : ℝ) + 1) := by
    have h_eq : δ * ((i : ℝ) + 1) - δ * (j : ℝ) = δ * (((i - j : ℤ) : ℝ) + 1) := by
      simp [sub_eq_add_neg] <;> ring
    have h : x - y < δ * ((i : ℝ) + 1) - δ * (j : ℝ) := by linarith
    rw [h_eq] at h; exact h
  have h3 : δ * (k : ℝ) < δ * (((i - j : ℤ) : ℝ) + 1) := lt_of_le_of_lt h1 h2
  have h4 : (k : ℝ) < ((i - j : ℤ) : ℝ) + 1 := by
    have h5 : δ * (k : ℝ) < δ * (((i - j : ℤ) : ℝ) + 1) := h3
    nlinarith
  have h5 : k < i - j + 1 := by exact_mod_cast h4
  have h_k_upper : k ≤ i - j := by omega
  have h6 : δ * (i : ℝ) - δ * ((j : ℝ) + 1) < x - y := by linarith
  have h7 : δ * (((i - j - 1 : ℤ) : ℝ)) < x - y := by
    have h_eq : δ * (i : ℝ) - δ * ((j : ℝ) + 1) = δ * (((i - j - 1 : ℤ) : ℝ)) := by
      simp [sub_eq_add_neg] <;> ring
    rw [h_eq] at h6; exact h6
  have h8 : δ * (((i - j - 1 : ℤ) : ℝ)) < δ * ((k : ℝ) + 1) := lt_trans h7 hw2
  have h9 : ((i - j - 1 : ℤ) : ℝ) < (k : ℝ) + 1 := by nlinarith
  have h10 : i - j - 1 < k + 1 := by exact_mod_cast h9
  have h_k_lower : i - j - 1 ≤ k := by linarith
  have h_e3 : k - (i - j) ∈ ({-1, 0} : Set ℤ) := by
    have h6 : k - (i - j) ≤ 0 := by omega
    have h7 : -1 ≤ k - (i - j) := by omega
    have h8 : k - (i - j) = -1 ∨ k - (i - j) = 0 := by omega
    rcases h8 with (h8 | h8) <;> rw [h8] <;> simp
  have h_ij : i - j ∈ (realCubeIndexSet δ X - realCubeIndexSet δ Y) := by
    exact ⟨i, hiX, j, hjY, rfl⟩
  have h_eq : (i - j) + (k - (i - j)) = k := by omega
  have h_goal : k ∈ (realCubeIndexSet δ X - realCubeIndexSet δ Y) + ({-1, 0} : Set ℤ) := by
    have h : (i - j) + (k - (i - j)) ∈ (realCubeIndexSet δ X - realCubeIndexSet δ Y) + ({-1, 0} : Set ℤ) := by
      exact ⟨i - j, h_ij, k - (i - j), h_e3, rfl⟩
    rw [h_eq] at h; exact h
  exact h_goal

/-! ## Iterated sum index inclusion -/

/-- Helper: `{0, ..., n-1}` as `Finset ℤ`. -/
noncomputable def rangeInt (n : ℕ) : Finset ℤ := Finset.Ico 0 (n : ℤ)

lemma rangeInt_card (n : ℕ) : (rangeInt n).card = n := by
  simp [rangeInt, Finset.Ico_eq_empty_of_le] <;> omega

/-- Coercion commutes with nsmul for finsets. -/
lemma finset_coe_nsmul {α : Type*} [AddCommMonoid α] (s : Finset α) (n : ℕ) :
    (↑(n • s) : Set α) = n • (↑s : Set α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (↑((n + 1) • s) : Set α)
        = ↑(n • s + s) := by rw [succ_nsmul]
      _ = ↑(n • s) + ↑s := by rw [Finset.coe_add]
      _ = n • (↑s : Set α) + ↑s := by rw [ih]
      _ = (n + 1) • (↑s : Set α) := by
        have h : (n + 1) • (↑s : Set α) = n • (↑s : Set α) + ↑s := by
          rw [add_smul, one_smul]
        exact h.symm

/-- Auxiliary version taking IB as explicit argument. -/
lemma nfold_sum_index_inclusion_aux {δ : ℝ} (hδ : 0 < δ) {B : Set ℝ}
    (hB : Bornology.IsBounded B) (IB : Finset ℤ)
    (hIB : (IB : Set ℤ) = realCubeIndexSet δ B) (n : ℕ) (hn : 0 < n) :
    realCubeIndexSet δ (nfoldSum n B) ⊆ (↑(n • IB) + rangeInt n : Set ℤ) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hn0 : n = 0
    · -- Base case n = 0, so n+1 = 1
      subst hn0
      intro k hk
      have h1 : nfoldSum 1 B = B := nfoldSum_one
      rw [h1] at hk
      have hk' : k ∈ IB := by
        have h : k ∈ (IB : Set ℤ) := by rw [hIB]; exact hk
        exact Finset.mem_coe.mp h
      have h10 : (0 : ℤ) ∈ rangeInt 1 := by
        simp [rangeInt] <;> omega
      have h_goal : k ∈ (↑(1 • IB) + rangeInt 1 : Set ℤ) := by
        have h9 : (1 : ℕ) • IB = IB := by simp
        rw [h9]
        exact ⟨k, hk', 0, h10, by simp⟩
      exact h_goal
    · -- Inductive step n ≥ 1
      have hn' : 0 < n := by omega
      have h1 : realCubeIndexSet δ (nfoldSum (n + 1) B) ⊆
          realCubeIndexSet δ B + realCubeIndexSet δ (nfoldSum n B) + ({0, 1} : Set ℤ) :=
        sum_index_inclusion_rev hδ
      intro z hz
      rcases h1 hz with ⟨s, ⟨i, hi, j, hj, rfl⟩, e, he, rfl⟩
      have h_ih : j ∈ (↑(n • IB) + rangeInt n : Set ℤ) := ih hn' hj
      rcases h_ih with ⟨j1, hj1, j2, hj2, rfl⟩
      have hj1' : j1 ∈ n • IB := Finset.mem_coe.mp hj1
      have h_i : i ∈ IB := by
        have h : i ∈ (IB : Set ℤ) := by rw [hIB]; exact hi
        exact Finset.mem_coe.mp h
      have h_e : e = 0 ∨ e = 1 := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he <;> tauto
      have h_j2_bounds : 0 ≤ j2 ∧ j2 < (n : ℤ) := by
        simpa [rangeInt, Finset.mem_Ico] using hj2
      rcases h_e with (rfl | rfl)
      · -- e = 0
        have h_j2' : j2 ∈ rangeInt (n + 1) := by
          simp only [rangeInt, Finset.mem_Ico] <;> omega
        have h_sum : i + j1 ∈ (n + 1) • IB := by
          have h10 : (n + 1) • IB = IB + n • IB := by
            simp [succ_nsmul, add_comm]
          rw [h10]
          exact Finset.add_mem_add h_i hj1'
        have h_sum' : i + j1 ∈ (↑((n + 1) • IB) : Set ℤ) := Finset.mem_coe.mpr h_sum
        exact ⟨i + j1, h_sum', j2, h_j2', by ring⟩
      · -- e = 1
        have h_j2' : j2 + 1 ∈ rangeInt (n + 1) := by
          simp only [rangeInt, Finset.mem_Ico] <;> omega
        have h_sum : i + j1 ∈ (n + 1) • IB := by
          have h10 : (n + 1) • IB = IB + n • IB := by
            simp [succ_nsmul, add_comm]
          rw [h10]
          exact Finset.add_mem_add h_i hj1'
        have h_sum' : i + j1 ∈ (↑((n + 1) • IB) : Set ℤ) := Finset.mem_coe.mpr h_sum
        exact ⟨i + j1, h_sum', j2 + 1, h_j2', by ring⟩

/-- For n ≥ 1, `I(nB) ⊆ n•I(B) + {0, ..., n-1}`. -/
lemma nfold_sum_index_inclusion {δ : ℝ} (hδ : 0 < δ) {B : Set ℝ}
    (hB : Bornology.IsBounded B) (n : ℕ) (hn : 0 < n) :
    realCubeIndexSet δ (nfoldSum n B) ⊆
      (↑(n • (realCubeIndexSet_finite hδ hB).toFinset) + rangeInt n : Set ℤ) := by
  let IB := (realCubeIndexSet_finite hδ hB).toFinset
  have hIB : (IB : Set ℤ) = realCubeIndexSet δ B := Set.Finite.coe_toFinset _
  exact nfold_sum_index_inclusion_aux hδ hB IB hIB n hn

/-! ## Iterated difference index inclusion -/

/-- For m, n ≥ 1, `I(mB - nB) ⊆ m•I(B) - n•I(B) + {-n, ..., m-1}`. -/
lemma nfold_diff_index_inclusion {δ : ℝ} (hδ : 0 < δ) {B : Set ℝ}
    (hB : Bornology.IsBounded B) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    realCubeIndexSet δ (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B)) ⊆
      ((↑(m • (realCubeIndexSet_finite hδ hB).toFinset)) -
       (↑(n • (realCubeIndexSet_finite hδ hB).toFinset)) +
       Finset.Ico (-n : ℤ) m : Set ℤ) := by
  have h1 : realCubeIndexSet δ (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B)) ⊆
      realCubeIndexSet δ (nfoldSum m B) - realCubeIndexSet δ (nfoldSum n B) + ({-1, 0} : Set ℤ) :=
    diff_index_inclusion hδ
  intro z hz
  rcases h1 hz with ⟨d, ⟨i, hi, j, hj, rfl⟩, e, he, rfl⟩
  let IB := (realCubeIndexSet_finite hδ hB).toFinset
  have h_im : i ∈ (↑(m • IB) + rangeInt m : Set ℤ) :=
    nfold_sum_index_inclusion hδ hB m hm hi
  have h_jn : j ∈ (↑(n • IB) + rangeInt n : Set ℤ) :=
    nfold_sum_index_inclusion hδ hB n hn hj
  rcases h_im with ⟨i1, hi1, i2, hi2, rfl⟩
  rcases h_jn with ⟨j1, hj1, j2, hj2, rfl⟩
  have h_e : e = -1 ∨ e = 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he <;> tauto
  have hi2_bounds : 0 ≤ i2 ∧ i2 < (m : ℤ) := by
    simpa [rangeInt, Finset.mem_Ico] using hi2
  have hj2_bounds : 0 ≤ j2 ∧ j2 < (n : ℤ) := by
    simpa [rangeInt, Finset.mem_Ico] using hj2
  have hi1' : i1 ∈ m • IB := Finset.mem_coe.mp hi1
  have hj1' : j1 ∈ n • IB := Finset.mem_coe.mp hj1
  have hi1_set : i1 ∈ (↑(m • IB) : Set ℤ) := Finset.mem_coe.mpr hi1'
  have hj1_set : j1 ∈ (↑(n • IB) : Set ℤ) := Finset.mem_coe.mpr hj1'
  have h_sub : i1 - j1 ∈ (↑(m • IB) : Set ℤ) - (↑(n • IB) : Set ℤ) :=
    ⟨i1, hi1_set, j1, hj1_set, rfl⟩
  rcases h_e with (rfl | rfl)
  · have h_err1 : -(n : ℤ) ≤ i2 - j2 - 1 := by linarith
    have h_err2 : i2 - j2 - 1 < (m : ℤ) := by linarith
    have h_err : i2 - j2 - 1 ∈ Finset.Ico (-n : ℤ) m := by
      simp only [Finset.mem_Ico] <;> exact ⟨h_err1, h_err2⟩
    exact ⟨i1 - j1, h_sub, i2 - j2 - 1, h_err, by simp [sub_eq_add_neg] <;> ring⟩
  · have h_err1 : -(n : ℤ) ≤ i2 - j2 := by linarith
    have h_err2 : i2 - j2 < (m : ℤ) := by linarith
    have h_err : i2 - j2 ∈ Finset.Ico (-n : ℤ) m := by
      simp only [Finset.mem_Ico] <;> exact ⟨h_err1, h_err2⟩
    exact ⟨i1 - j1, h_sub, i2 - j2, h_err, by simp [sub_eq_add_neg] <;> ring⟩

/-! ## Finite Plünnecke-Ruzsa helpers -/

/-- Finite Plünnecke for pure iterated sum. -/
lemma finite_pluennecke_nsmul {IA IB : Finset ℤ} (hIA : IA.Nonempty)
    (K' : ℚ≥0) (hK' : (IA + IB).card ≤ K' * IA.card) (n : ℕ) :
    (n • IB).card ≤ K'^n * IA.card := by
  have h_main := Finset.pluennecke_ruzsa_inequality_nsmul_add hIA IB n
  have h_pos : (0 : ℚ≥0) < (IA.card : ℚ≥0) := by exact_mod_cast hIA.card_pos
  have h_ratio : ((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0) ≤ K' := by
    have h : ((IA + IB).card : ℚ≥0) ≤ K' * (IA.card : ℚ≥0) := by exact_mod_cast hK'
    calc
      ((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)
        ≤ (K' * (IA.card : ℚ≥0)) / (IA.card : ℚ≥0) := by gcongr
      _ = K' := by field_simp [h_pos.ne'] <;> ring
  have h_mono : (((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)) ^ n ≤ K'^n := by gcongr
  have h_final : ((n • IB).card : ℚ≥0) ≤ K'^n * (IA.card : ℚ≥0) := by
    calc ((n • IB).card : ℚ≥0)
        ≤ (((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)) ^ n * (IA.card : ℚ≥0) := h_main
      _ ≤ K'^n * (IA.card : ℚ≥0) := by gcongr
  exact_mod_cast h_final

/-- Finite Plünnecke for difference. -/
lemma finite_pluennecke_diff {IA IB : Finset ℤ} (hIA : IA.Nonempty)
    (K' : ℚ≥0) (hK' : (IA + IB).card ≤ K' * IA.card) (m n : ℕ) :
    ((m • IB) - (n • IB)).card ≤ K'^(m + n) * IA.card := by
  have h_main := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hIA IB m n
  have h_pos : (0 : ℚ≥0) < (IA.card : ℚ≥0) := by exact_mod_cast hIA.card_pos
  have h_ratio : ((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0) ≤ K' := by
    have h : ((IA + IB).card : ℚ≥0) ≤ K' * (IA.card : ℚ≥0) := by exact_mod_cast hK'
    calc
      ((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)
        ≤ (K' * (IA.card : ℚ≥0)) / (IA.card : ℚ≥0) := by gcongr
      _ = K' := by field_simp [h_pos.ne'] <;> ring
  have h_mono : (((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)) ^ (m + n) ≤ K'^(m + n) := by gcongr
  have h_final : (((m • IB) - (n • IB)).card : ℚ≥0) ≤ K'^(m + n) * (IA.card : ℚ≥0) := by
    calc (((m • IB) - (n • IB)).card : ℚ≥0)
        ≤ (((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)) ^ (m + n) * (IA.card : ℚ≥0) := h_main
      _ ≤ K'^(m + n) * (IA.card : ℚ≥0) := by gcongr
  exact_mod_cast h_final

/-- If A is nonempty and bounded, its cube index finset is nonempty. -/
lemma cube_index_nonempty {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA : Bornology.IsBounded A) (hA_nonempty : A.Nonempty) :
    (realCubeIndexSet_finite hδ hA).toFinset.Nonempty := by
  rcases hA_nonempty with ⟨x, hx⟩
  let k : ℤ := Int.floor (x / δ)
  have hk : k ∈ realCubeIndexSet δ A := by
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    have h1 : δ * (k : ℝ) ≤ x := by
      have h : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h' : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have h2 : x < δ * ((k : ℝ) + 1) := by
      have h : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
      have h' : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    exact ⟨x, ⟨h1, h2⟩, hx⟩
  let F := (realCubeIndexSet_finite hδ hA).toFinset
  have hF : (F : Set ℤ) = realCubeIndexSet δ A := Set.Finite.coe_toFinset _
  have h_k_in_F : k ∈ F := by
    have h : k ∈ (F : Set ℤ) := by
      rw [hF]; exact hk
    simpa [Finset.mem_coe] using h
  exact ⟨k, h_k_in_F⟩

/-! ## Main covering number theorems -/

noncomputable abbrev Nreal' (δ : ℝ) (A : Set ℝ) : ENNReal :=
  ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A))

/-- Common setup: convert covering number hypothesis to finset cardinality bound. -/
lemma covering_hyp_to_card {δ : ℝ} (hδ : 0 < δ) {A B : Set ℝ}
    (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B)
    {K : ℝ} (hK_nonneg : 0 ≤ K)
    (h : Nreal' δ (Set.image2 (· + ·) A B) ≤ ENNReal.ofReal K * Nreal' δ A) :
    let IA := (realCubeIndexSet_finite hδ hA).toFinset
    let IAB := (realCubeIndexSet_finite hδ (bounded_image2_add hA hB)).toFinset
    IAB.card ≤ K * IA.card := by
  let IA := (realCubeIndexSet_finite hδ hA).toFinset
  let IAB := (realCubeIndexSet_finite hδ (bounded_image2_add hA hB)).toFinset
  have hNAB := realCoveringNumber_eq_card hδ (bounded_image2_add hA hB)
  have hNA := realCoveringNumber_eq_card hδ hA
  have h_encard_IAB : (realCubeIndexSet δ (Set.image2 (· + ·) A B)).encard = IAB.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (bounded_image2_add hA hB))] <;> rfl
  have h_encard_IA : (realCubeIndexSet δ A).encard = IA.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hA)] <;> rfl
  have h' : Nreal' δ (Set.image2 (· + ·) A B) = (IAB.card : ENNReal) := by
    dsimp only [Nreal']
    have h_eq1 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) A B))) =
        ENat.toENNReal (realCubeIndexSet δ (Set.image2 (· + ·) A B)).encard := by
      have h : dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) A B)) =
          (realCubeIndexSet δ (Set.image2 (· + ·) A B)).encard := hNAB
      rw [h]
    rw [h_eq1, h_encard_IAB]
    <;> simp
  have h'' : Nreal' δ A = (IA.card : ENNReal) := by
    dsimp only [Nreal']
    have h_eq2 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) =
        ENat.toENNReal (realCubeIndexSet δ A).encard := by
      have h : dyadicCoveringNumber δ (productLikeRealLineCopy A) =
          (realCubeIndexSet δ A).encard := hNA
      rw [h]
    rw [h_eq2, h_encard_IA] <;> simp
  rw [h', h''] at h
  have h_final : (IAB.card : ℝ) ≤ K * (IA.card : ℝ) := by
    have hK_nonneg' : 0 ≤ K * (IA.card : ℝ) := by positivity
    have h_eq : ENNReal.ofReal K * (IA.card : ENNReal) = ENNReal.ofReal (K * (IA.card : ℝ)) := by
      rw [ENNReal.ofReal_mul hK_nonneg] <;> norm_cast
    rw [h_eq] at h
    have h_card_eq : (IAB.card : ENNReal) = ENNReal.ofReal (IAB.card : ℝ) := by
      simp
    rw [h_card_eq] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  dsimp only
  exact h_final

/-- Bound |IA + IB| ≤ 2 * |IAB|. -/
lemma sum_index_card_bound {δ : ℝ} (hδ : 0 < δ) {A B : Set ℝ}
    (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B) :
    let IA := (realCubeIndexSet_finite hδ hA).toFinset
    let IB := (realCubeIndexSet_finite hδ hB).toFinset
    let IAB := (realCubeIndexSet_finite hδ (bounded_image2_add hA hB)).toFinset
    (IA + IB).card ≤ 2 * IAB.card := by
  let IA := (realCubeIndexSet_finite hδ hA).toFinset
  let IB := (realCubeIndexSet_finite hδ hB).toFinset
  let IAB := (realCubeIndexSet_finite hδ (bounded_image2_add hA hB)).toFinset
  have hIA : (IA : Set ℤ) = realCubeIndexSet δ A := Set.Finite.coe_toFinset _
  have hIB : (IB : Set ℤ) = realCubeIndexSet δ B := Set.Finite.coe_toFinset _
  have hIAB : (IAB : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) A B) :=
    Set.Finite.coe_toFinset _
  have h_sum_incl : (IA + IB : Finset ℤ) ⊆ IAB + ({-1, 0} : Finset ℤ) := by
    have h2 : ((IA + IB : Finset ℤ) : Set ℤ) ⊆
        ((IAB + ({-1, 0} : Finset ℤ)) : Set ℤ) := by
      calc ((IA + IB : Finset ℤ) : Set ℤ)
          = realCubeIndexSet δ A + realCubeIndexSet δ B := by simp [hIA, hIB] <;> rfl
        _ ⊆ realCubeIndexSet δ (Set.image2 (· + ·) A B) + ({-1, 0} : Set ℤ) :=
          sum_index_inclusion hδ
        _ = (IAB : Set ℤ) + ({-1, 0} : Set ℤ) := by rw [←hIAB]
        _ = ((IAB + ({-1, 0} : Finset ℤ)) : Set ℤ) := by simp
    exact_mod_cast h2
  have h3 : (IA + IB).card ≤ (IAB + ({-1, 0} : Finset ℤ)).card :=
    Finset.card_le_card h_sum_incl
  have h4 : (IAB + ({-1, 0} : Finset ℤ)).card ≤ IAB.card * 2 := by
    have h5 := finset_pointwise_add_card_le (A := IAB) (B := ({-1, 0} : Finset ℤ))
    simpa using h5
  calc (IA + IB).card ≤ (IAB + ({-1, 0} : Finset ℤ)).card := h3
    _ ≤ IAB.card * 2 := h4
    _ = 2 * IAB.card := by ring

/-- **Full discretized Plünnecke-Ruzsa**: pure iterated sum.

If `N(A+B, δ) ≤ K · N(A, δ)`, then for all `n ≥ 1`,
`N(nB, δ) ≤ n · (2K)^n · N(A, δ)`. -/
lemma discretized_pluennecke_nfold_sum
    {δ : ℝ} (hδ : 0 < δ) {A B : Set ℝ}
    (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B)
    (hA_nonempty : A.Nonempty)
    {K : ℝ} (hK_nonneg : 0 ≤ K)
    (h : Nreal' δ (Set.image2 (· + ·) A B) ≤ ENNReal.ofReal K * Nreal' δ A)
    {n : ℕ} (hn : 0 < n) :
    Nreal' δ (nfoldSum n B) ≤
      ENNReal.ofReal ((n : ℝ) * (2 * K) ^ n) * Nreal' δ A := by
  let IA := (realCubeIndexSet_finite hδ hA).toFinset
  let IB := (realCubeIndexSet_finite hδ hB).toFinset
  let IAB := (realCubeIndexSet_finite hδ (bounded_image2_add hA hB)).toFinset
  have hIA_nonempty : IA.Nonempty := cube_index_nonempty hδ hA hA_nonempty
  have h_card_hyp : IAB.card ≤ K * IA.card := covering_hyp_to_card hδ hA hB hK_nonneg h
  have h_card_sum : (IA + IB).card ≤ 2 * IAB.card := sum_index_card_bound hδ hA hB
  have h_card_sum2 : ((IA + IB).card : ℝ) ≤ 2 * K * (IA.card : ℝ) := by
    calc ((IA + IB).card : ℝ)
        ≤ 2 * (IAB.card : ℝ) := by exact_mod_cast h_card_sum
      _ ≤ 2 * (K * (IA.card : ℝ)) := by gcongr
      _ = 2 * K * (IA.card : ℝ) := by ring
  let r : ℚ≥0 := ((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)
  have h_pos : (0 : ℚ≥0) < (IA.card : ℚ≥0) := by exact_mod_cast hIA_nonempty.card_pos
  have hr : (IA + IB).card ≤ r * IA.card := by
    have h_pos' : (IA.card : ℚ≥0) ≠ 0 := h_pos.ne'
    have h_pos'' : (IA.card : ℚ) ≠ 0 := by exact_mod_cast h_pos'
    have h_eq : r * (IA.card : ℚ≥0) = ((IA + IB).card : ℚ≥0) := by
      apply NNRat.coe_injective
      simp [r, NNRat.coe_mul, NNRat.coe_div, h_pos''] <;> field_simp [h_pos''] <;> ring
    exact_mod_cast h_eq.symm.le
  have hr_le : (r : ℝ) ≤ 2 * K := by
    have h_pos' : (0 : ℝ) < (IA.card : ℝ) := by exact_mod_cast hIA_nonempty.card_pos
    have h1 : (r : ℝ) = ((IA + IB).card : ℝ) / (IA.card : ℝ) := by
      simp [r, NNRat.cast_div, NNRat.cast_mul] <;> field_simp [h_pos'.ne'] <;> ring
    rw [h1]
    have h2 : ((IA + IB).card : ℝ) ≤ 2 * K * (IA.card : ℝ) := by exact_mod_cast h_card_sum2
    calc ((IA + IB).card : ℝ) / (IA.card : ℝ)
        ≤ (2 * K * (IA.card : ℝ)) / (IA.card : ℝ) := by gcongr
      _ = 2 * K := by field_simp [h_pos'.ne'] <;> ring
  have h_pluennecke : (n • IB).card ≤ r ^ n * IA.card :=
    finite_pluennecke_nsmul hIA_nonempty r hr n
  have hInB_finite : (realCubeIndexSet δ (nfoldSum n B)).Finite :=
    realCubeIndexSet_finite hδ (nfoldSum_bounded hB)
  let InB := hInB_finite.toFinset
  have hInB : (InB : Set ℤ) = realCubeIndexSet δ (nfoldSum n B) := Set.Finite.coe_toFinset _
  have h_incl : InB ⊆ (n • IB) + rangeInt n := by
    apply Finset.coe_subset.mp
    have h6 : (↑((n • IB) + rangeInt n) : Set ℤ) = (↑(n • IB) + rangeInt n : Set ℤ) := by
      rw [Finset.coe_add] <;> rfl
    rw [h6, hInB]
    exact nfold_sum_index_inclusion hδ hB n hn
  have h_card_nB : InB.card ≤ n * (n • IB).card := by
    have h6 : InB.card ≤ ((n • IB) + rangeInt n).card := Finset.card_le_card h_incl
    have h7 : ((n • IB) + rangeInt n).card ≤ (n • IB).card * (rangeInt n).card :=
      finset_pointwise_add_card_le
    have h8 : (rangeInt n).card = n := rangeInt_card n
    calc InB.card ≤ ((n • IB) + rangeInt n).card := h6
      _ ≤ (n • IB).card * (rangeInt n).card := h7
      _ = (n • IB).card * n := by rw [h8] <;> ring
      _ = n * (n • IB).card := by ring
  have h_final_card : (InB.card : ℝ) ≤ (n : ℝ) * (2 * K) ^ n * (IA.card : ℝ) := by
    have h9 : (InB.card : ℝ) ≤ (n : ℝ) * ((n • IB).card : ℝ) := by exact_mod_cast h_card_nB
    have h10 : ((n • IB).card : ℝ) ≤ (r : ℝ) ^ n * (IA.card : ℝ) := by exact_mod_cast h_pluennecke
    have h11 : (r : ℝ) ^ n ≤ (2 * K) ^ n := by gcongr <;> linarith
    calc (InB.card : ℝ)
        ≤ (n : ℝ) * ((n • IB).card : ℝ) := h9
      _ ≤ (n : ℝ) * ((r : ℝ) ^ n * (IA.card : ℝ)) := by gcongr
      _ ≤ (n : ℝ) * ((2 * K) ^ n * (IA.card : ℝ)) := by gcongr
      _ = (n : ℝ) * (2 * K) ^ n * (IA.card : ℝ) := by ring
  have hNnB := realCoveringNumber_eq_card (S := nfoldSum n B) hδ (nfoldSum_bounded hB)
  have hNA := realCoveringNumber_eq_card hδ hA
  have h_encard_InB : (realCubeIndexSet δ (nfoldSum n B)).encard = InB.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite (S := nfoldSum n B) hδ (nfoldSum_bounded hB))] <;> rfl
  have h_encard_IA : (realCubeIndexSet δ A).encard = IA.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hA)] <;> rfl
  have h_ofReal_card : ∀ (c : ℕ), ENNReal.ofReal (c : ℝ) = (c : ENNReal) := by
    intro c; simp
  have h_ennreal : (InB.card : ENNReal) ≤
      ENNReal.ofReal ((n : ℝ) * (2 * K) ^ n) * (IA.card : ENNReal) := by
    have h_mul : ENNReal.ofReal ((n : ℝ) * (2 * K) ^ n * (IA.card : ℝ)) =
        ENNReal.ofReal ((n : ℝ) * (2 * K) ^ n) * (IA.card : ENNReal) := by
      rw [ENNReal.ofReal_mul, h_ofReal_card IA.card] <;> ring_nf <;> positivity
    have h5 : (InB.card : ENNReal) = ENNReal.ofReal (InB.card : ℝ) := by
      rw [h_ofReal_card]
    rw [h5, ←h_mul]
    exact ENNReal.ofReal_le_ofReal h_final_card
  have h_goal : Nreal' δ (nfoldSum n B) ≤
      ENNReal.ofReal ((n : ℝ) * (2 * K) ^ n) * Nreal' δ A := by
    dsimp only [Nreal']
    have h1 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (nfoldSum n B))) =
        (InB.card : ENNReal) := by
      rw [hNnB, h_encard_InB] <;> simp
    have h2 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) =
        (IA.card : ENNReal) := by
      rw [hNA, h_encard_IA] <;> simp
    rw [h1, h2]
    exact h_ennreal
  exact h_goal

/-- **Full discretized Plünnecke-Ruzsa**: difference version.

If `N(A+B, δ) ≤ K · N(A, δ)`, then for all `m, n ≥ 1`,
`N(mB - nB, δ) ≤ (m+n) · (2K)^(m+n) · N(A, δ)`. -/
lemma discretized_pluennecke_nfold_diff
    {δ : ℝ} (hδ : 0 < δ) {A B : Set ℝ}
    (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B)
    (hA_nonempty : A.Nonempty)
    {K : ℝ} (hK_nonneg : 0 ≤ K)
    (h : Nreal' δ (Set.image2 (· + ·) A B) ≤ ENNReal.ofReal K * Nreal' δ A)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nreal' δ (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B)) ≤
      ENNReal.ofReal (((m + n : ℕ) : ℝ) * (2 * K) ^ (m + n)) * Nreal' δ A := by
  let IA := (realCubeIndexSet_finite hδ hA).toFinset
  let IB := (realCubeIndexSet_finite hδ hB).toFinset
  let IAB := (realCubeIndexSet_finite hδ (bounded_image2_add hA hB)).toFinset
  have hIA_nonempty : IA.Nonempty := cube_index_nonempty hδ hA hA_nonempty
  have h_card_hyp : IAB.card ≤ K * IA.card := covering_hyp_to_card hδ hA hB hK_nonneg h
  have h_card_sum : (IA + IB).card ≤ 2 * IAB.card := sum_index_card_bound hδ hA hB
  have h_card_sum2 : ((IA + IB).card : ℝ) ≤ 2 * K * (IA.card : ℝ) := by
    calc ((IA + IB).card : ℝ)
        ≤ 2 * (IAB.card : ℝ) := by exact_mod_cast h_card_sum
      _ ≤ 2 * (K * (IA.card : ℝ)) := by gcongr
      _ = 2 * K * (IA.card : ℝ) := by ring
  let r : ℚ≥0 := ((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)
  have h_pos : (0 : ℚ≥0) < (IA.card : ℚ≥0) := by exact_mod_cast hIA_nonempty.card_pos
  have hr : (IA + IB).card ≤ r * IA.card := by
    have h_pos' : (IA.card : ℚ≥0) ≠ 0 := h_pos.ne'
    have h_pos'' : (IA.card : ℚ) ≠ 0 := by exact_mod_cast h_pos'
    have h_eq : r * (IA.card : ℚ≥0) = ((IA + IB).card : ℚ≥0) := by
      apply NNRat.coe_injective
      simp [r, NNRat.coe_mul, NNRat.coe_div, h_pos''] <;> field_simp [h_pos''] <;> ring
    exact_mod_cast h_eq.symm.le
  have hr_le : (r : ℝ) ≤ 2 * K := by
    have h_pos' : (0 : ℝ) < (IA.card : ℝ) := by exact_mod_cast hIA_nonempty.card_pos
    have h1 : (r : ℝ) = ((IA + IB).card : ℝ) / (IA.card : ℝ) := by
      simp [r, NNRat.cast_div, NNRat.cast_mul] <;> field_simp [h_pos'.ne'] <;> ring
    rw [h1]
    have h2 : ((IA + IB).card : ℝ) ≤ 2 * K * (IA.card : ℝ) := by exact_mod_cast h_card_sum2
    calc ((IA + IB).card : ℝ) / (IA.card : ℝ)
        ≤ (2 * K * (IA.card : ℝ)) / (IA.card : ℝ) := by gcongr
      _ = 2 * K := by field_simp [h_pos'.ne'] <;> ring
  have h_pluennecke : ((m • IB) - (n • IB)).card ≤ r ^ (m + n) * IA.card :=
    finite_pluennecke_diff hIA_nonempty r hr m n
  let hBdiff_bdd : Bornology.IsBounded (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B)) :=
    bounded_image2_sub (nfoldSum_bounded hB) (nfoldSum_bounded hB)
  let errSet := Finset.Ico (-n : ℤ) m
  have h_err_card : errSet.card = m + n := by
    simp [errSet, Finset.Ico_eq_empty_of_le] <;> omega
  have hImBnB_finite : (realCubeIndexSet δ (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B))).Finite :=
    realCubeIndexSet_finite hδ hBdiff_bdd
  let ImBnB := hImBnB_finite.toFinset
  have hImBnB : (ImBnB : Set ℤ) =
      realCubeIndexSet δ (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B)) :=
    Set.Finite.coe_toFinset _
  have h_incl : ImBnB ⊆ ((m • IB) - (n • IB)) + errSet := by
    apply Finset.coe_subset.mp
    have h6 : (↑(((m • IB) - (n • IB)) + errSet) : Set ℤ) =
        (↑(m • IB) - ↑(n • IB) + errSet : Set ℤ) := by
      rw [Finset.coe_add, Finset.coe_sub] <;> rfl
    rw [h6, hImBnB]
    exact nfold_diff_index_inclusion hδ hB m n hm hn
  have h_card : ImBnB.card ≤ (m + n) * ((m • IB) - (n • IB)).card := by
    have h6 : ImBnB.card ≤ (((m • IB) - (n • IB)) + errSet).card :=
      Finset.card_le_card h_incl
    have h7 : (((m • IB) - (n • IB)) + errSet).card ≤
        ((m • IB) - (n • IB)).card * errSet.card := finset_pointwise_add_card_le
    calc ImBnB.card ≤ (((m • IB) - (n • IB)) + errSet).card := h6
      _ ≤ ((m • IB) - (n • IB)).card * errSet.card := h7
      _ = ((m • IB) - (n • IB)).card * (m + n) := by rw [h_err_card] <;> ring
      _ = (m + n) * ((m • IB) - (n • IB)).card := by ring
  have h_final_card : (ImBnB.card : ℝ) ≤
      ((m + n : ℕ) : ℝ) * (2 * K) ^ (m + n) * (IA.card : ℝ) := by
    have h9 : (ImBnB.card : ℝ) ≤ ((m + n : ℕ) : ℝ) * (((m • IB) - (n • IB)).card : ℝ) := by
      exact_mod_cast h_card
    have h10 : (((m • IB) - (n • IB)).card : ℝ) ≤ (r : ℝ) ^ (m + n) * (IA.card : ℝ) := by
      exact_mod_cast h_pluennecke
    have h11 : (r : ℝ) ^ (m + n) ≤ (2 * K) ^ (m + n) := by gcongr <;> linarith
    calc (ImBnB.card : ℝ)
        ≤ ((m + n : ℕ) : ℝ) * (((m • IB) - (n • IB)).card : ℝ) := h9
      _ ≤ ((m + n : ℕ) : ℝ) * ((r : ℝ) ^ (m + n) * (IA.card : ℝ)) := by gcongr
      _ ≤ ((m + n : ℕ) : ℝ) * ((2 * K) ^ (m + n) * (IA.card : ℝ)) := by gcongr
      _ = ((m + n : ℕ) : ℝ) * (2 * K) ^ (m + n) * (IA.card : ℝ) := by ring
  have hN := realCoveringNumber_eq_card hδ hBdiff_bdd
  have hNA := realCoveringNumber_eq_card hδ hA
  have h_encard : (realCubeIndexSet δ (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B))).encard =
      ImBnB.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hBdiff_bdd)] <;> rfl
  have h_encard_IA : (realCubeIndexSet δ A).encard = IA.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hA)] <;> rfl
  have h_ofReal_card : ∀ (c : ℕ), ENNReal.ofReal (c : ℝ) = (c : ENNReal) := by
    intro c; simp
  have h_ennreal : (ImBnB.card : ENNReal) ≤
      ENNReal.ofReal (((m + n : ℕ) : ℝ) * (2 * K) ^ (m + n)) * (IA.card : ENNReal) := by
    have h_mul : ENNReal.ofReal (((m + n : ℕ) : ℝ) * (2 * K) ^ (m + n) * (IA.card : ℝ)) =
        ENNReal.ofReal (((m + n : ℕ) : ℝ) * (2 * K) ^ (m + n)) * (IA.card : ENNReal) := by
      rw [ENNReal.ofReal_mul, h_ofReal_card IA.card] <;> ring_nf <;> positivity
    have h5 : (ImBnB.card : ENNReal) = ENNReal.ofReal (ImBnB.card : ℝ) := by
      rw [h_ofReal_card]
    rw [h5, ←h_mul]
    exact ENNReal.ofReal_le_ofReal h_final_card
  dsimp only [Nreal']
  have h1 : ENat.toENNReal (dyadicCoveringNumber δ
        (productLikeRealLineCopy (Set.image2 (· - ·) (nfoldSum m B) (nfoldSum n B)))) =
      (ImBnB.card : ENNReal) := by
    rw [hN, h_encard] <;> simp
  have h2 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) =
      (IA.card : ENNReal) := by
    rw [hNA, h_encard_IA] <;> simp
  rw [h1, h2]
  exact h_ennreal

/-- **General discretized Ruzsa triangle** (sub-add-add form):

`N(X-Z, δ) · N(Y, δ) ≤ 8 · N(X+Y, δ) · N(Z+Y, δ)`.

The factor 8 comes from two discretization errors of size 2 (for the two sum
inclusions) and one for the difference inclusion. -/
lemma discretized_ruzsa_triangle_sub_add_add
    {δ : ℝ} (hδ : 0 < δ) {X Y Z : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hZ : Bornology.IsBounded Z) (hY_nonempty : Y.Nonempty) :
    Nreal' δ (Set.image2 (· - ·) X Z) * Nreal' δ Y ≤
      8 * Nreal' δ (Set.image2 (· + ·) X Y) * Nreal' δ (Set.image2 (· + ·) Z Y) := by
  let IX := (realCubeIndexSet_finite hδ hX).toFinset
  let IY := (realCubeIndexSet_finite hδ hY).toFinset
  let IZ := (realCubeIndexSet_finite hδ hZ).toFinset
  have hIY_nonempty : IY.Nonempty := cube_index_nonempty hδ hY hY_nonempty
  let E1 : Finset ℤ := {-1, 0}
  have hE1_card : E1.card = 2 := by decide
  have hE1_set : (E1 : Set ℤ) = ({-1, 0} : Set ℤ) := by
    ext x <;> simp [E1] <;> omega
  let IXmZ := (realCubeIndexSet_finite hδ (bounded_image2_sub hX hZ)).toFinset
  let IXpY := (realCubeIndexSet_finite hδ (bounded_image2_add hX hY)).toFinset
  let IZpY := (realCubeIndexSet_finite hδ (bounded_image2_add hZ hY)).toFinset
  have hIX : (IX : Set ℤ) = realCubeIndexSet δ X := Set.Finite.coe_toFinset _
  have hIY : (IY : Set ℤ) = realCubeIndexSet δ Y := Set.Finite.coe_toFinset _
  have hIZ : (IZ : Set ℤ) = realCubeIndexSet δ Z := Set.Finite.coe_toFinset _
  have hIXmZ : (IXmZ : Set ℤ) = realCubeIndexSet δ (Set.image2 (· - ·) X Z) := Set.Finite.coe_toFinset _
  have hIXpY : (IXpY : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X Y) := Set.Finite.coe_toFinset _
  have hIZpY : (IZpY : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) Z Y) := Set.Finite.coe_toFinset _
  have h1 : IXmZ ⊆ (IX - IZ) + E1 := by
    apply Finset.coe_subset.mp
    have h6 : (↑(((IX - IZ) + E1)) : Set ℤ) = (↑IX - ↑IZ + (E1 : Set ℤ)) := by
      rw [Finset.coe_add, Finset.coe_sub] <;> rfl
    rw [h6, hIXmZ, hIX, hIZ, hE1_set]
    exact diff_index_inclusion (X := X) (Y := Z) hδ
  have h2 : (IX + IY) ⊆ IXpY + E1 := by
    apply Finset.coe_subset.mp
    have h6 : (↑(IXpY + E1) : Set ℤ) = (↑IXpY + (E1 : Set ℤ)) := by
      rw [Finset.coe_add] <;> rfl
    rw [h6, Finset.coe_add, hIX, hIY, hIXpY, hE1_set]
    exact sum_index_inclusion (X := X) (Y := Y) hδ
  have h3 : (IZ + IY) ⊆ IZpY + E1 := by
    apply Finset.coe_subset.mp
    have h6 : (↑(IZpY + E1) : Set ℤ) = (↑IZpY + (E1 : Set ℤ)) := by
      rw [Finset.coe_add] <;> rfl
    rw [h6, Finset.coe_add, hIZ, hIY, hIZpY, hE1_set]
    exact sum_index_inclusion (X := Z) (Y := Y) hδ
  have h_card1 : IXmZ.card ≤ 2 * (IX - IZ).card := by
    have h4 : IXmZ ⊆ (IX - IZ) + E1 := h1
    have h5 : ((IX - IZ) + E1).card ≤ (IX - IZ).card * E1.card := finset_pointwise_add_card_le
    calc IXmZ.card ≤ ((IX - IZ) + E1).card := Finset.card_le_card h4
      _ ≤ (IX - IZ).card * E1.card := h5
      _ = (IX - IZ).card * 2 := by rw [hE1_card] <;> ring
      _ = 2 * (IX - IZ).card := by ring
  have h_card2 : (IX + IY).card ≤ 2 * IXpY.card := by
    have h4 : (IX + IY) ⊆ IXpY + E1 := h2
    have h5 : (IXpY + E1).card ≤ IXpY.card * E1.card := finset_pointwise_add_card_le
    calc (IX + IY).card ≤ (IXpY + E1).card := Finset.card_le_card h4
      _ ≤ IXpY.card * E1.card := h5
      _ = IXpY.card * 2 := by rw [hE1_card] <;> ring
      _ = 2 * IXpY.card := by ring
  have h_card3 : (IZ + IY).card ≤ 2 * IZpY.card := by
    have h4 : (IZ + IY) ⊆ IZpY + E1 := h3
    have h5 : (IZpY + E1).card ≤ IZpY.card * E1.card := finset_pointwise_add_card_le
    calc (IZ + IY).card ≤ (IZpY + E1).card := Finset.card_le_card h4
      _ ≤ IZpY.card * E1.card := h5
      _ = IZpY.card * 2 := by rw [hE1_card] <;> ring
      _ = 2 * IZpY.card := by ring
  have h_ruzsa : (IX - IZ).card * IY.card ≤ (IX + IY).card * (IZ + IY).card :=
    Finset.ruzsa_triangle_inequality_sub_add_add IX IY IZ
  have h_main : IXmZ.card * IY.card ≤ 8 * IXpY.card * IZpY.card := by
    calc IXmZ.card * IY.card
        ≤ (2 * (IX - IZ).card) * IY.card := by gcongr
      _ = 2 * ((IX - IZ).card * IY.card) := by ring
      _ ≤ 2 * ((IX + IY).card * (IZ + IY).card) := by gcongr
      _ ≤ 2 * ((2 * IXpY.card) * (2 * IZpY.card)) := by gcongr
      _ = 8 * IXpY.card * IZpY.card := by ring
  have hN_XmZ := realCoveringNumber_eq_card hδ (bounded_image2_sub hX hZ)
  have hN_Y := realCoveringNumber_eq_card hδ hY
  have hN_XpY := realCoveringNumber_eq_card hδ (bounded_image2_add hX hY)
  have hN_ZpY := realCoveringNumber_eq_card hδ (bounded_image2_add hZ hY)
  dsimp only [Nreal']
  rw [hN_XmZ, hN_Y, hN_XpY, hN_ZpY]
  have h_encard_XmZ : (realCubeIndexSet δ (Set.image2 (· - ·) X Z)).encard = IXmZ.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (bounded_image2_sub hX hZ))] <;> rfl
  have h_encard_Y : (realCubeIndexSet δ Y).encard = IY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hY)] <;> rfl
  have h_encard_XpY : (realCubeIndexSet δ (Set.image2 (· + ·) X Y)).encard = IXpY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (bounded_image2_add hX hY))] <;> rfl
  have h_encard_ZpY : (realCubeIndexSet δ (Set.image2 (· + ·) Z Y)).encard = IZpY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (bounded_image2_add hZ hY))] <;> rfl
  rw [h_encard_XmZ, h_encard_Y, h_encard_XpY, h_encard_ZpY]
  norm_cast
  <;> exact_mod_cast h_main

/-- **Convert sumset bound to difference set bound**:

`N(A-B, δ) · N(A, δ) · N(B, δ) ≤ 72 · N(A+B, δ)^3`.

Combines the general discretized Ruzsa triangle with the sumset Ruzsa triangle. -/
lemma discretized_sum_to_diff
    {δ : ℝ} (hδ : 0 < δ) {A B : Set ℝ}
    (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) :
    Nreal' δ (Set.image2 (· - ·) A B) * Nreal' δ A * Nreal' δ B ≤
      72 * Nreal' δ (Set.image2 (· + ·) A B) ^ 3 := by
  have h1 : Nreal' δ (Set.image2 (· - ·) A B) * Nreal' δ A ≤
      8 * Nreal' δ (Set.image2 (· + ·) A A) * Nreal' δ (Set.image2 (· + ·) B A) :=
    discretized_ruzsa_triangle_sub_add_add hδ hA hA hB hA_nonempty
  have hBA_eq_AB : Set.image2 (· + ·) B A = Set.image2 (· + ·) A B := by
    ext z
    simp [Set.mem_image2, add_comm]
    <;> tauto
  have h2 : Nreal' δ (Set.image2 (· + ·) B A) = Nreal' δ (Set.image2 (· + ·) A B) := by
    rw [hBA_eq_AB]
  rw [h2] at h1
  have h3 : Nreal' δ (Set.image2 (· + ·) A A) * Nreal' δ B ≤
      9 * Nreal' δ (Set.image2 (· + ·) A B) ^ 2 := by
    have h_raw := discretized_pluennecke_ruzsa_sum hδ hA hB hB_nonempty
    simp only [Nreal'] at h_raw ⊢
    have h4 : 9 * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) A B))) *
          ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) A B))) =
        9 * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) A B))) ^ 2 := by
      ring
    rw [h4] at h_raw
    exact h_raw
  calc Nreal' δ (Set.image2 (· - ·) A B) * Nreal' δ A * Nreal' δ B
      = (Nreal' δ (Set.image2 (· - ·) A B) * Nreal' δ A) * Nreal' δ B := by ring
    _ ≤ (8 * Nreal' δ (Set.image2 (· + ·) A A) * Nreal' δ (Set.image2 (· + ·) A B)) * Nreal' δ B := by gcongr
    _ = 8 * Nreal' δ (Set.image2 (· + ·) A B) * (Nreal' δ (Set.image2 (· + ·) A A) * Nreal' δ B) := by ring
    _ ≤ 8 * Nreal' δ (Set.image2 (· + ·) A B) * (9 * Nreal' δ (Set.image2 (· + ·) A B) ^ 2) := by gcongr
    _ = 72 * Nreal' δ (Set.image2 (· + ·) A B) ^ 3 := by ring

end ProductLikeIncidence

module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Retention-based Point Selection

Selects a subset of points whose retained tube families are sufficiently large.

Given a global average retention bound, uses a Markov-type argument to select
points satisfying `M ≤ K_ret * |retained p|`, while losing at most a factor
`K_ret` in point cardinality.

## Main result

`select_points_by_retention` — select P' with uniform retention guarantee.

## Proof sketch

1. Set threshold = M / (2 * K_cpd).
2. P' = {p ∈ P : |retained p| ≥ threshold}.
3. For p ∈ P', M ≤ 2*K_cpd * |retained p|, so K_ret = 2*K_cpd.
4. Upper bound |retained p| ≤ M and global average imply |P| ≤ K_ret * |P'|.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace InductionOnScales

/-- Select points with sufficiently large retained tube families.

Given:
- `h_ret_upper`: each retained family has at most M tubes
- `h_global_retention`: average retention ≥ M / K_cpd

Returns P' and K_ret = 2*K_cpd such that:
- Every p ∈ P' satisfies M ≤ K_ret * |retained p|
- |P| ≤ K_ret * |P'|
-/
lemma select_points_by_retention
    {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (retained : DyadicSquare n → Finset (DyadicTube n))
    (M : ℕ) (hM : 0 < M)
    (K_cpd : ℝ) (hK_cpd : 1 ≤ K_cpd)
    (hP_nonempty : P.Nonempty)
    (h_ret_upper : ∀ p ∈ P, (retained p).card ≤ M)
    (h_global_retention : (∑ p ∈ P, (retained p).card : ℝ) ≥
      (P.card : ℝ) * (M : ℝ) / K_cpd) :
    ∃ (P' : Finset (DyadicSquare n)) (K_ret : ℝ),
      P' ⊆ P ∧
      (1 ≤ K_ret) ∧
      (K_ret = 2 * K_cpd) ∧
      P'.Nonempty ∧
      (∀ p ∈ P', (M : ℝ) ≤ K_ret * ((retained p).card : ℝ)) ∧
      ((P.card : ℝ) ≤ K_ret * (P'.card : ℝ)) := by
  let threshold : ℝ := (M : ℝ) / (2 * K_cpd)
  let P' : Finset (DyadicSquare n) :=
    P.filter (fun p => threshold ≤ ((retained p).card : ℝ))
  let P_bad : Finset (DyadicSquare n) :=
    P.filter (fun p => ¬(threshold ≤ ((retained p).card : ℝ)))
  let K_ret : ℝ := 2 * K_cpd

  have hK_pos : 0 < K_cpd := by linarith
  have hK_ret_one : 1 ≤ K_ret := by
    dsimp only [K_ret]
    nlinarith

  have hP'_sub : P' ⊆ P := Finset.filter_subset _ _

  -- Size bound for selected points
  have h_size : ∀ p ∈ P', (M : ℝ) ≤ K_ret * ((retained p).card : ℝ) := by
    intro p hp
    have h2 : threshold ≤ ((retained p).card : ℝ) := (Finset.mem_filter.mp hp).2
    dsimp only [threshold, K_ret] at h2 ⊢
    have h3 : (M : ℝ) = 2 * K_cpd * ((M : ℝ) / (2 * K_cpd)) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h3]
    gcongr

  have h_disj : Disjoint P' P_bad := by
    simp [P', P_bad, Finset.disjoint_left]
    <;> tauto

  have h_union : P = P' ∪ P_bad := by
    ext p
    simp only [P', P_bad, Finset.mem_union, Finset.mem_filter]
    <;> by_cases h : threshold ≤ ((retained p).card : ℝ) <;> simp [h] <;> tauto

  have h_card_P : (P.card : ℝ) = (P'.card : ℝ) + (P_bad.card : ℝ) := by
    rw [h_union, Finset.card_union_of_disjoint h_disj] <;> norm_cast

  -- Upper bound on sum over good points
  have hS_good : (∑ p ∈ P', (retained p).card : ℝ) ≤
      (P'.card : ℝ) * (M : ℝ) := by
    have h : ∀ p ∈ P', (retained p).card ≤ M := by
      intro p hp
      exact h_ret_upper p (hP'_sub hp)
    calc (∑ p ∈ P', (retained p).card : ℝ)
      = ∑ p ∈ P', ((retained p).card : ℝ) := by norm_cast
    _ ≤ ∑ p ∈ P', (M : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact_mod_cast h p hp
    _ = (P'.card : ℝ) * (M : ℝ) := by
      simp [Finset.sum_const] <;> ring

  -- Upper bound on sum over bad points
  have hS_bad : (∑ p ∈ P_bad, (retained p).card : ℝ) ≤
      (P_bad.card : ℝ) * threshold := by
    calc (∑ p ∈ P_bad, (retained p).card : ℝ)
      = ∑ p ∈ P_bad, ((retained p).card : ℝ) := by norm_cast
    _ ≤ ∑ p ∈ P_bad, threshold := by
      apply Finset.sum_le_sum
      intro p hp
      have h2 : ¬(threshold ≤ ((retained p).card : ℝ)) := (Finset.mem_filter.mp hp).2
      exact le_of_lt (not_le.mp h2)
    _ = (P_bad.card : ℝ) * threshold := by
      simp [Finset.sum_const] <;> ring

  have h_sum : (∑ p ∈ P, (retained p).card : ℝ) =
      (∑ p ∈ P', (retained p).card : ℝ) + (∑ p ∈ P_bad, (retained p).card : ℝ) := by
    rw [← Finset.sum_union h_disj, h_union] <;> norm_cast

  -- Cardinality bound: |P| ≤ K_ret * |P'|
  set a : ℝ := (P'.card : ℝ) with ha_def
  set b : ℝ := (P_bad.card : ℝ) with hb_def
  have hM_pos : (M : ℝ) > 0 := by exact_mod_cast hM
  have h_card_ab : (P.card : ℝ) = a + b := by
    simpa [ha_def, hb_def] using h_card_P
  have h_sum' : (∑ p ∈ P, (retained p).card : ℝ) ≤ a * (M : ℝ) + b * threshold := by
    rw [h_sum]
    have h2 : (∑ p ∈ P', (retained p).card : ℝ) ≤ a * (M : ℝ) := by
      simpa [ha_def] using hS_good
    have h3 : (∑ p ∈ P_bad, (retained p).card : ℝ) ≤ b * threshold := by
      simpa [hb_def] using hS_bad
    linarith
  have h3 : (a + b) * (M : ℝ) / K_cpd ≤ a * (M : ℝ) + b * threshold := by
    have h1 : (P.card : ℝ) * (M : ℝ) / K_cpd ≤ (∑ p ∈ P, (retained p).card : ℝ) := h_global_retention
    rw [h_card_ab] at h1
    linarith [h_sum']
  have h4 : (a + b) / K_cpd ≤ a + b / (2 * K_cpd) := by
    have h5 : (a + b) * (M : ℝ) / K_cpd ≤ a * (M : ℝ) + b * ((M : ℝ) / (2 * K_cpd)) := by
      simpa [threshold] using h3
    have h6 : 0 < (M : ℝ) := hM_pos
    calc (a + b) / K_cpd
      = ((a + b) * (M : ℝ) / K_cpd) / (M : ℝ) := by field_simp [h6.ne'] <;> ring
    _ ≤ (a * (M : ℝ) + b * ((M : ℝ) / (2 * K_cpd))) / (M : ℝ) := by gcongr
    _ = a + b / (2 * K_cpd) := by field_simp [h6.ne'] <;> ring
  have h9 : 0 < K_cpd := hK_pos
  have h10 : 2 * (a + b) ≤ 2 * K_cpd * a + b := by
    calc 2 * (a + b)
      = 2 * K_cpd * ((a + b) / K_cpd) := by field_simp [h9.ne'] <;> ring
    _ ≤ 2 * K_cpd * (a + b / (2 * K_cpd)) := by gcongr
    _ = 2 * K_cpd * a + b := by field_simp [h9.ne'] <;> ring
  have h8 : b ≤ 2 * (K_cpd - 1) * a := by linarith
  have h_a_nonneg : 0 ≤ a := by
    have h : 0 ≤ (P'.card : ℝ) := Nat.cast_nonneg _
    simpa [ha_def] using h
  have h_main : (P.card : ℝ) ≤ K_ret * (P'.card : ℝ) := by
    have h11 : (P.card : ℝ) = a + b := h_card_ab
    rw [h11]
    dsimp only [K_ret]
    have h12 : a + b ≤ (2 * K_cpd - 1) * a := by linarith
    have h13 : (2 * K_cpd - 1) * a ≤ 2 * K_cpd * a := by
      nlinarith
    linarith

  have hP'_nonempty : P'.Nonempty := by
    by_contra h
    have h4 : P' = ∅ := by simpa using h
    have h5 : (P'.card : ℝ) = 0 := by
      rw [h4]
      <;> simp
    have h6 : (P.card : ℝ) ≤ 0 := by
      rw [h5] at h_main
      <;> simpa using h_main
    have h7 : P.card = 0 := by
      have h71 : (P.card : ℝ) ≤ 0 := h6
      have h72 : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
      exact_mod_cast le_antisymm h71 h72
    have h8 : P = ∅ := Finset.card_eq_zero.mp h7
    exact hP_nonempty.ne_empty h8

  have hK_ret_eq : K_ret = 2 * K_cpd := by rfl
  exact ⟨P', K_ret, hP'_sub, hK_ret_one, hK_ret_eq, hP'_nonempty, h_size, h_main⟩

end InductionOnScales

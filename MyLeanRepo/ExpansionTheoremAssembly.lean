module

/-
# Expansion Theorem (Theorem 1)

Given an all-scale (κ,C)-Frostman measure μ supported on [-C,C],
there exists N (depending on κ,C) such that the iterated difference
N·K^(N) - N·K^(N) has positive Lebesgue measure, where K = supp(μ).

## Proof route (paper lines 549-569)

1. Let n = least integer with nκ > 1.
2. ν = μ^×n is all-scale (nκ, C^n)-Frostman on ℝ^n.
3. By FrostmanEnergy, I_1(ν) ≤ 1 + C^n/(nκ-1) < ∞.
4. By Marstrand's projection theorem, ∃ v ∈ [1/2,1]^n with
   volume(v_1·K + ... + v_n·K) > 0.
5. Apply Expansion Lemma (Lemma 3.2) n-1 times to eliminate each weight v_j,
   at each step replacing K by N_i·K^(2) - N_i·K^(2).
6. Conclude volume(N·K^(N) - N·K^(N)) > 0.

## Dependencies
- FrostmanEnergy (proved ✓)
- Marstrand arbitrary-dim projection (pending)
- Expansion Lemma Lemma 3.2 (bacon, in progress)
- n-dim Blichfeldt (pending)
-/

public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.FrostmanEnergy
public import MyLeanRepo.ExpansionLemma
public import MyLeanRepo.MarstrandArbitraryDim
public import MyLeanRepo.IterativeElimination
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric Classical BigOperators
open scoped BigOperators Pointwise

namespace WeakTwoEndsSumProduct

/-! ## Iterative elimination helper lemmas -/

/-- `productSet A (n+1) = image2 (*) A (productSet A n)`. -/
lemma productSet_succ {A : Set ℝ} {n : ℕ} :
    ExpansionLemma.productSet A (n + 1) =
      Set.image2 (· * ·) A (ExpansionLemma.productSet A n) := by
  ext z
  simp only [ExpansionLemma.productSet, Set.mem_image2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    let g : Fin n → ℝ := fun i => f i.succ
    have hg : ∀ i, g i ∈ A := fun i => hf i.succ
    have hb : (∏ i : Fin n, g i) ∈ ExpansionLemma.productSet A n := ⟨g, hg, rfl⟩
    have h_eq : f 0 * (∏ i : Fin n, g i) = (∏ i : Fin (n + 1), f i) := by
      rw [Fin.prod_univ_succ]
      <;> apply Finset.prod_congr rfl
      <;> intro i _ <;> rfl
    exact ⟨f 0, hf 0, (∏ i : Fin n, g i), hb, h_eq⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases hb with ⟨g, hg, hbg⟩
    let f : Fin (n + 1) → ℝ := fun i =>
      if h : i.val = 0 then a else g ⟨i.val - 1, by omega⟩
    have hf : ∀ i, f i ∈ A := by
      intro i
      by_cases h : i.val = 0
      · have h_i0 : i = 0 := by
          apply Fin.ext
          simpa using h
        rw [h_i0]
        simp [f] <;> exact ha
      · have h_i_pos : i.val ≠ 0 := h
        have h_fi : f i = g ⟨i.val - 1, by omega⟩ := by
          unfold f
          rw [dif_neg h_i_pos]
        rw [h_fi]
        exact hg ⟨i.val - 1, by omega⟩
    have h_f0 : f 0 = a := by simp [f]
    have h_fsucc : ∀ (i : Fin n), f i.succ = g i := by
      intro i
      have h_val : (i.succ : Fin (n + 1)).val ≠ 0 := by simp
      simp [f, h_val] <;> congr <;> omega
    have h_eq : (∏ i : Fin (n + 1), f i) = a * b := by
      have h1 : (∏ i : Fin (n + 1), f i) = f 0 * ∏ i : Fin n, f i.succ := Fin.prod_univ_succ f
      rw [h1, h_f0]
      have h2 : (∏ i : Fin n, f i.succ) = ∏ i : Fin n, g i := by
        apply Finset.prod_congr rfl
        intro i _
        exact h_fsucc i
      rw [h2, hbg] <;> ring
    exact ⟨f, hf, h_eq.symm⟩

/-- Product of elements from `productSet K d` and `productSet K e`
lies in `productSet K (d + e)`. -/
lemma productSet_mul {K : Set ℝ} {d e : ℕ} {x y : ℝ}
    (hx : x ∈ ExpansionLemma.productSet K d)
    (hy : y ∈ ExpansionLemma.productSet K e) :
    x * y ∈ ExpansionLemma.productSet K (d + e) := by
  have h_main : ∀ (e' : ℕ) (y' : ℝ), y' ∈ ExpansionLemma.productSet K e' →
      x * y' ∈ ExpansionLemma.productSet K (d + e') := by
    intro e'
    induction e' with
    | zero =>
      intro y' hy'
      have hy1 : y' = 1 := by
        rcases hy' with ⟨f, _, h_eq⟩
        simpa using h_eq
      rw [hy1] <;> simpa [add_zero] using hx
    | succ e' ih =>
      intro y' hy'
      rw [productSet_succ] at hy'
      rcases hy' with ⟨y1, hy1, y2, hy2, rfl⟩
      have h1 : x * y2 ∈ ExpansionLemma.productSet K (d + e') := ih y2 hy2
      have h2 : y1 * (x * y2) ∈ ExpansionLemma.productSet K (d + e' + 1) := by
        rw [productSet_succ]
        exact ⟨y1, hy1, x * y2, h1, rfl⟩
      have h3 : x * (y1 * y2) = y1 * (x * y2) := by ring
      rw [h3]
      exact h2
  exact h_main e y hy

/-- Multiply a `productSet` element by an `iteratedSumset` of productSets. -/
lemma mul_iteratedSumset_productSet {K : Set ℝ} {d e N : ℕ} {a y : ℝ}
    (ha : a ∈ ExpansionLemma.productSet K d)
    (hy : y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K e) N) :
    a * y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) N := by
  have hy' : y ∈ ExpansionLemma.iteratedSumsetFin (ExpansionLemma.productSet K e) N := by
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact hy
  rcases hy' with ⟨g, hg, rfl⟩
  let h : Fin N → ℝ := fun i => a * g i
  have hh : ∀ i, h i ∈ ExpansionLemma.productSet K (d + e) := by
    intro i
    exact productSet_mul ha (hg i)
  have h_sum : a * (∑ i : Fin N, g i) = ∑ i : Fin N, h i := by
    have h : ∑ i : Fin N, h i = ∑ i : Fin N, (a * g i) := by rfl
    rw [h, Finset.mul_sum] <;> rfl
  rw [h_sum]
  have h_main : ∑ i : Fin N, h i ∈ ExpansionLemma.iteratedSumsetFin (ExpansionLemma.productSet K (d + e)) N :=
    ⟨h, hh, rfl⟩
  rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_main
  exact h_main

/-- If `x ∈ iteratedSumset (productSet K d) M` and
`y ∈ iteratedSumset (productSet K e) N`, then
`x * y ∈ iteratedSumset (productSet K (d + e)) (M * N)`. -/
lemma iteratedSumset_product {K : Set ℝ} {d e M N : ℕ} {x y : ℝ}
    (hx : x ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K d) M)
    (hy : y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K e) N) :
    x * y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M * N) := by
  have h_main : ∀ (M' : ℕ) (x' : ℝ),
      x' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K d) M' →
        x' * y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M' * N) := by
    intro M'
    induction M' with
    | zero =>
      intro x' hx'
      have hx0 : x' = 0 := by
        simpa [ExpansionLemma.iteratedSumset] using hx'
      rw [hx0]
      simp [ExpansionLemma.iteratedSumset]
    | succ M' ih =>
      intro x' hx'
      have hx'fin : x' ∈ ExpansionLemma.iteratedSumsetFin (ExpansionLemma.productSet K d) (M' + 1) := by
        rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact hx'
      rcases hx'fin with ⟨f, hf, h_eq⟩
      have h_f0 : f 0 ∈ ExpansionLemma.productSet K d := hf 0
      have h_rest_sum : ∑ i : Fin M', f i.succ ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K d) M' := by
        have h_goal : ∑ i : Fin M', f i.succ ∈ ExpansionLemma.iteratedSumsetFin (ExpansionLemma.productSet K d) M' :=
          ⟨fun i => f i.succ, fun i => hf i.succ, rfl⟩
        rw [←ExpansionLemma.iteratedSumsetFin_eq_recursive]
        exact h_goal
      have h1 : (f 0) * y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) N :=
        mul_iteratedSumset_productSet h_f0 hy
      have h2 : (∑ i : Fin M', f i.succ) * y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M' * N) :=
        ih (∑ i : Fin M', f i.succ) h_rest_sum
      have h_x'_eq : x' = f 0 + ∑ i : Fin M', f i.succ := by
        rw [h_eq.symm, Fin.sum_univ_succ] <;> rfl
      rw [h_x'_eq]
      have h3 : (f 0 + ∑ i : Fin M', f i.succ) * y = (f 0) * y + (∑ i : Fin M', f i.succ) * y := by ring
      rw [h3]
      have h4 := ExpansionLemma.iteratedSumsetFin_add
        (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h1)
        (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h2)
      rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h4
      have h5 : N + M' * N = (M' + 1) * N := by ring
      rw [h5] at h4
      exact h4
  exact h_main M x hx

/-- Sum of N elements, each in `iteratedSumset T P`, lies in `iteratedSumset T (N*P)`. -/
lemma sum_of_iteratedSumset {T : Set ℝ} {P N : ℕ} {a : Fin N → ℝ}
    (ha : ∀ i, a i ∈ ExpansionLemma.iteratedSumset T P) :
    ∑ i : Fin N, a i ∈ ExpansionLemma.iteratedSumset T (N * P) := by
  induction N with
  | zero =>
    simp [ExpansionLemma.iteratedSumset]
  | succ N ih =>
    have h1 : a 0 ∈ ExpansionLemma.iteratedSumset T P := ha 0
    have h2 : ∑ i : Fin N, a i.succ ∈ ExpansionLemma.iteratedSumset T (N * P) :=
      ih (fun i => ha i.succ)
    have h3 : a 0 + ∑ i : Fin N, a i.succ ∈ ExpansionLemma.iteratedSumset T (P + N * P) := by
      have h4 := ExpansionLemma.iteratedSumsetFin_add
        (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h1)
        (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h2)
      rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h4
      exact h4
    have h5 : P + N * P = (N + 1) * P := by ring
    rw [h5] at h3
    have h6 : ∑ i : Fin (N + 1), a i = a 0 + ∑ i : Fin N, a i.succ := by
      rw [Fin.sum_univ_succ] <;> rfl
    rw [h6]
    exact h3

/-- If `S ⊆ iteratedDifference T P`, then
`iteratedSumset S N ⊆ iteratedDifference T (N * P)`. -/
lemma sumset_of_difference {S T : Set ℝ} {P N : ℕ}
    (h : S ⊆ ExpansionLemma.iteratedDifference T P) :
    ExpansionLemma.iteratedSumset S N ⊆
      ExpansionLemma.iteratedDifference T (N * P) := by
  intro z hz
  have hz' : z ∈ ExpansionLemma.iteratedSumsetFin S N := by
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact hz
  rcases hz' with ⟨f, hf, rfl⟩
  have h_i : ∀ i : Fin N, ∃ (a b : ℝ),
      a ∈ ExpansionLemma.iteratedSumset T P ∧
      b ∈ ExpansionLemma.iteratedSumset T P ∧ f i = a - b := by
    intro i
    have h_mem : f i ∈ ExpansionLemma.iteratedDifference T P := by
      exact h (hf i)
    have h_iff : (f i ∈ ExpansionLemma.iteratedDifference T P) ↔
        ∃ (a b : ℝ), a ∈ ExpansionLemma.iteratedSumset T P ∧
          b ∈ ExpansionLemma.iteratedSumset T P ∧ f i = a - b := by
      constructor
      · intro h
        rcases h with ⟨a, ha, b, hb, h_eq⟩
        exact ⟨a, b, ha, hb, h_eq.symm⟩
      · rintro ⟨a, b, ha, hb, h_eq⟩
        exact ⟨a, ha, b, hb, h_eq.symm⟩
    exact h_iff.mp h_mem
  choose a b ha hb h_eq using h_i
  have hA : ∑ i : Fin N, a i ∈ ExpansionLemma.iteratedSumset T (N * P) :=
    sum_of_iteratedSumset (T := T) (P := P) ha
  have hB : ∑ i : Fin N, b i ∈ ExpansionLemma.iteratedSumset T (N * P) :=
    sum_of_iteratedSumset (T := T) (P := P) hb
  have h_eq2 : ∑ i : Fin N, f i = (∑ i : Fin N, a i) - (∑ i : Fin N, b i) := by
    have h : ∀ i, f i = a i - b i := by intro i; exact h_eq i
    have h_sum : ∑ i : Fin N, f i = ∑ i : Fin N, (a i - b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact h i
    rw [h_sum, Finset.sum_sub_distrib]
  rw [h_eq2]
  exact ⟨∑ i : Fin N, a i, hA, ∑ i : Fin N, b i, hB, rfl⟩

/-- If `S ⊆ iteratedDifference T P` and `S.Nonempty`, then
`iteratedDifference S N ⊆ iteratedDifference T (2 * N * P)`. -/
lemma difference_of_difference {S T : Set ℝ} {P N : ℕ}
    (h : S ⊆ ExpansionLemma.iteratedDifference T P)
    (hS : S.Nonempty) :
    ExpansionLemma.iteratedDifference S N ⊆
      ExpansionLemma.iteratedDifference T (2 * N * P) := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  have hx' : x ∈ ExpansionLemma.iteratedDifference T (N * P) :=
    sumset_of_difference h hx
  have hy' : y ∈ ExpansionLemma.iteratedDifference T (N * P) :=
    sumset_of_difference h hy
  rcases hx' with ⟨a, ha, b, hb, rfl⟩
  rcases hy' with ⟨c, hc, d, hd, rfl⟩
  have h1 : a + d ∈ ExpansionLemma.iteratedSumset T (N * P + N * P) := by
    have h_add := ExpansionLemma.iteratedSumsetFin_add
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact ha)
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact hd)
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_add
    exact h_add
  have h2 : b + c ∈ ExpansionLemma.iteratedSumset T (N * P + N * P) := by
    have h_add := ExpansionLemma.iteratedSumsetFin_add
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact hb)
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact hc)
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_add
    exact h_add
  have h3 : N * P + N * P = 2 * N * P := by ring
  have h1' : a + d ∈ ExpansionLemma.iteratedSumset T (2 * N * P) := by
    convert h1 using 1
    <;> ring_nf
  have h2' : b + c ∈ ExpansionLemma.iteratedSumset T (2 * N * P) := by
    convert h2 using 1
    <;> ring_nf
  have h4 : (a - b) - (c - d) = (a + d) - (b + c) := by ring
  have h_goal : (a - b) - (c - d) ∈ ExpansionLemma.iteratedDifference T (2 * N * P) := by
    have h5 : (a - b) - (c - d) = (a + d) - (b + c) := h4
    rw [h5]
    exact ⟨a + d, h1', b + c, h2', rfl⟩
  exact h_goal

/-- If `A ⊆ iteratedDifference (productSet K d) M`, then
`productSet A 2 ⊆ iteratedDifference (productSet K (2 * d)) (2 * M * M)`. -/
lemma productSet_of_contained_difference {K A : Set ℝ} {d M : ℕ}
    (h : A ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K d) M) :
    ExpansionLemma.productSet A 2 ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (2 * d)) (2 * M * M) := by
  intro z hz
  rcases hz with ⟨f, hf, hz_eq⟩
  have hx : (f 0) ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K d) M := h (hf 0)
  have hy : (f 1) ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K d) M := h (hf 1)
  rcases hx with ⟨u, hu, v, hv, hx_eq⟩
  rcases hy with ⟨w, hw, z', hz', hy_eq⟩
  have hz2 : z = (u - v) * (w - z') := by
    have h_prod : ∏ i : Fin 2, f i = f 0 * f 1 := by
      simp [Fin.prod_univ_two]
    have h_step1 : z = f 0 * f 1 := by
      rw [hz_eq, h_prod]
    rw [h_step1]
    have h_step2 : f 0 * f 1 = (u - v) * (w - z') := by
      have h1 : f 0 = u - v := hx_eq.symm
      have h2 : f 1 = w - z' := hy_eq.symm
      rw [h1, h2] <;> ring
    exact h_step2
  have h_dd : d + d = 2 * d := by ring
  have h1 : u * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (M * M) := by
    have h1_raw := iteratedSumset_product hu hw
    rw [h_dd] at h1_raw
    exact h1_raw
  have h2 : v * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (M * M) := by
    have h2_raw := iteratedSumset_product hv hz'
    rw [h_dd] at h2_raw
    exact h2_raw
  have h3 : u * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (M * M) := by
    have h3_raw := iteratedSumset_product hu hz'
    rw [h_dd] at h3_raw
    exact h3_raw
  have h4 : v * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (M * M) := by
    have h4_raw := iteratedSumset_product hv hw
    rw [h_dd] at h4_raw
    exact h4_raw
  have h_pos : u * w + v * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (M * M + M * M) := by
    have h_add := ExpansionLemma.iteratedSumsetFin_add
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h1)
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h2)
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_add
    exact h_add
  have h_neg : u * z' + v * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (M * M + M * M) := by
    have h_add := ExpansionLemma.iteratedSumsetFin_add
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h3)
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h4)
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_add
    exact h_add
  have h5 : M * M + M * M = 2 * M * M := by ring
  have h_pos' : u * w + v * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (2 * M * M) := by
    convert h_pos using 1 <;> ring_nf
  have h_neg' : u * z' + v * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (2 * d)) (2 * M * M) := by
    convert h_neg using 1 <;> ring_nf
  have h_eq : (u - v) * (w - z') = (u * w + v * z') - (u * z' + v * w) := by ring
  have h_goal : (u - v) * (w - z') ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (2 * d)) (2 * M * M) := by
    rw [h_eq]
    exact ⟨u * w + v * z', h_pos', u * z' + v * w, h_neg', rfl⟩
  rw [hz2]
  exact h_goal

/-- **Iterative containment**.

If `A ⊆ iteratedDifference (productSet K d) M`, then
`iteratedDifference (productSet A 2) N ⊆ iteratedDifference (productSet K (2*d)) (4*N*M*M)`. -/
lemma iterative_containment {K A : Set ℝ} {d M N : ℕ}
    (hA_nonempty : A.Nonempty)
    (h : A ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K d) M) :
    ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (2 * d)) (4 * N * M * M) := by
  have h1 : ExpansionLemma.productSet A 2 ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (2 * d)) (2 * M * M) :=
    productSet_of_contained_difference h
  have h2 : (ExpansionLemma.productSet A 2).Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    have h_elem : a * a ∈ ExpansionLemma.productSet A 2 := by
      refine ⟨fun _ => a, fun _ => ha, ?_⟩
      have h : ∏ i : Fin 2, (fun _ : Fin 2 => a) i = a * a := by
        rw [Fin.prod_univ_two]
        <;> simp
      exact h.symm
    exact ⟨a * a, h_elem⟩
  have h3 : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (2 * d)) (2 * N * (2 * M * M)) :=
    difference_of_difference h1 h2
  have h4 : 2 * N * (2 * M * M) = 4 * N * M * M := by ring
  have h5 : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (2 * d)) (4 * N * M * M) := by
    convert h3 using 2
    <;> ring
  exact h5

/-! ## Product of differences -/

/-- If `x ∈ iteratedDifference (productSet K d) M` and
`y ∈ iteratedDifference (productSet K e) N`, then
`x * y ∈ iteratedDifference (productSet K (d+e)) (2*M*N)`. -/
lemma product_of_differences {K : Set ℝ} {d e M N : ℕ} {x y : ℝ}
    (hx : x ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K d) M)
    (hy : y ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K e) N) :
    x * y ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (d + e)) (2 * M * N) := by
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  rcases hy with ⟨c, hc, z, hz, rfl⟩
  have h1 : a * c ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M * N) :=
    iteratedSumset_product ha hc
  have h2 : b * z ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M * N) :=
    iteratedSumset_product hb hz
  have h3 : a * z ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M * N) :=
    iteratedSumset_product ha hz
  have h4 : b * c ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M * N) :=
    iteratedSumset_product hb hc
  have h_pos : a * c + b * z ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M * N + M * N) := by
    have h_add := ExpansionLemma.iteratedSumsetFin_add
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h1)
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h2)
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_add
    exact h_add
  have h_neg : a * z + b * c ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (M * N + M * N) := by
    have h_add := ExpansionLemma.iteratedSumsetFin_add
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h3)
      (by rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact h4)
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_add
    exact h_add
  have h_pos' : a * c + b * z ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (2 * M * N) := by
    convert h_pos using 1 <;> ring_nf
  have h_neg' : a * z + b * c ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K (d + e)) (2 * M * N) := by
    convert h_neg using 1 <;> ring_nf
  have h_eq : (a - b) * (c - z) = (a * c + b * z) - (a * z + b * c) := by ring
  rw [h_eq]
  exact ⟨a * c + b * z, h_pos', a * z + b * c, h_neg', rfl⟩

/-! ## Iterated containment for product sets -/

/-- If `A' ⊆ iteratedDifference (productSet K d) M`, then
`productSet A' (e+1) ⊆ iteratedDifference (productSet K (d*(e+1))) (M^(e+1) * 2^e)`. -/
lemma productSet_of_iteratedDifference {K A' : Set ℝ} {d M : ℕ} (e : ℕ)
    (h : A' ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K d) M) :
    ExpansionLemma.productSet A' (e + 1) ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (d * (e + 1))) (M ^ (e + 1) * 2 ^ e) := by
  induction e with
  | zero =>
    have h_ps1 : ExpansionLemma.productSet A' 1 = A' := by
      ext x
      simp only [ExpansionLemma.productSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨f, hf, h_eq⟩
        have h : ∏ i : Fin 1, f i = f 0 := by simp
        rw [h] at h_eq
        rw [h_eq] <;> exact hf 0
      · intro hx
        refine ⟨fun _ => x, fun _ => hx, ?_⟩
        simp
    rw [h_ps1]
    simpa [mul_one, pow_one, pow_zero] using h
  | succ e ih =>
    intro z hz
    have h_split : z ∈ Set.image2 (· * ·) A' (ExpansionLemma.productSet A' (e + 1)) := by
      rw [productSet_succ] at hz
      exact hz
    rcases h_split with ⟨y, hy, x, hx, h_eq⟩
    have hx' : x ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (d * (e + 1))) (M ^ (e + 1) * 2 ^ e) := ih hx
    have hy' : y ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K d) M := h hy
    have h_goal : x * y ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K (d * (e + 1) + d)) (2 * (M ^ (e + 1) * 2 ^ e) * M) :=
      product_of_differences hx' hy'
    have h_z_eq : z = x * y := by
      calc z = y * x := h_eq.symm
           _ = x * y := by ring
    rw [h_z_eq]
    have h6 : d * (e + 1) + d = d * (e + 2) := by ring
    have h7 : 2 * (M ^ (e + 1) * 2 ^ e) * M = M ^ (e + 2) * 2 ^ (e + 1) := by ring
    rw [h6, h7] at h_goal
    exact h_goal

/-! ## Monotonicity and scaling of iteratedDifference -/

/-- Adding `k` copies of `s` to an element of `iteratedSumset S M`
gives an element of `iteratedSumset S (M+k)`. -/
lemma iteratedSumset_add_const {S : Set ℝ} {M : ℕ} {x : ℝ} (s : ℝ) (hs : s ∈ S)
    (hx : x ∈ ExpansionLemma.iteratedSumset S M) (k : ℕ) :
    x + (k : ℝ) * s ∈ ExpansionLemma.iteratedSumset S (M + k) := by
  induction k with
  | zero =>
    simpa using hx
  | succ k ih =>
    have h1 : x + (k : ℝ) * s ∈ ExpansionLemma.iteratedSumset S (M + k) := ih
    have h2 : (x + (k : ℝ) * s) + s ∈ ExpansionLemma.iteratedSumset S (M + k + 1) := by
      have h_def : ExpansionLemma.iteratedSumset S (M + k + 1) =
          Set.image2 (· + ·) S (ExpansionLemma.iteratedSumset S (M + k)) := by rfl
      rw [h_def]
      exact ⟨s, hs, x + (k : ℝ) * s, h1, by ring⟩
    have h3 : (x + (k : ℝ) * s) + s = x + ((k + 1 : ℕ) : ℝ) * s := by
      simp [Nat.cast_add, Nat.cast_one] <;> ring
    rw [h3] at h2
    convert h2 using 1 <;> ring_nf

/-- If `S.Nonempty` and `M ≤ N`, then
`iteratedDifference S M ⊆ iteratedDifference S N`. -/
lemma iteratedDifference_mono {S : Set ℝ} {M N : ℕ} (hS : S.Nonempty) (h : M ≤ N) :
    ExpansionLemma.iteratedDifference S M ⊆ ExpansionLemma.iteratedDifference S N := by
  rcases hS with ⟨s, hs⟩
  let k := N - M
  have hN : N = M + k := by omega
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  have hx' : x + (k : ℝ) * s ∈ ExpansionLemma.iteratedSumset S (M + k) :=
    iteratedSumset_add_const s hs hx k
  have hy' : y + (k : ℝ) * s ∈ ExpansionLemma.iteratedSumset S (M + k) :=
    iteratedSumset_add_const s hs hy k
  have h4 : (x + (k : ℝ) * s) - (y + (k : ℝ) * s) = x - y := by ring
  have h5 : (x + (k : ℝ) * s) - (y + (k : ℝ) * s) ∈ ExpansionLemma.iteratedDifference S (M + k) :=
    ⟨x + (k : ℝ) * s, hx', y + (k : ℝ) * s, hy', rfl⟩
  rw [h4] at h5
  rw [hN]
  exact h5

/-- If `x ∈ productSet A d` and `a ∈ A`, then
`x * a^k ∈ productSet A (d+k)`. -/
lemma productSet_mul_pow {A : Set ℝ} {d k : ℕ} {x : ℝ} {a : ℝ}
    (hx : x ∈ ExpansionLemma.productSet A d) (ha : a ∈ A) :
    x * a ^ k ∈ ExpansionLemma.productSet A (d + k) := by
  induction k with
  | zero =>
    simpa using hx
  | succ k ih =>
    have h1 : x * a ^ k ∈ ExpansionLemma.productSet A (d + k) := ih
    have h2 : a ∈ ExpansionLemma.productSet A 1 := by
      refine ⟨fun _ => a, fun _ => ha, ?_⟩
      simp
    have h3 : (x * a ^ k) * a ∈ ExpansionLemma.productSet A (d + k + 1) :=
      productSet_mul h1 h2
    have h4 : (x * a ^ k) * a = x * a ^ (k + 1) := by ring
    rw [h4] at h3
    convert h3 using 1 <;> ring_nf

/-- Scaling containment: if `a ∈ A`, `a ≠ 0`, then multiplication by `a^k` maps
`iteratedDifference (productSet A d) M` into `iteratedDifference (productSet A (d+k)) M`. -/
lemma iteratedDifference_productSet_scale {A : Set ℝ} {d M k : ℕ} {a : ℝ}
    (ha : a ∈ A) (ha_ne_zero : a ≠ 0) :
    (fun x : ℝ => x * a ^ k) '' ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d + k)) M := by
  intro w hw
  rcases hw with ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  have h1 : ∀ (w' : ℝ), w' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A d) M →
      w' * a ^ k ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A (d + k)) M := by
    intro w' hw'
    have hw'' : w' ∈ ExpansionLemma.iteratedSumsetFin (ExpansionLemma.productSet A d) M := by
      rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] <;> exact hw'
    rcases hw'' with ⟨f, hf, rfl⟩
    let g : Fin M → ℝ := fun i => f i * a ^ k
    have hg : ∀ i, g i ∈ ExpansionLemma.productSet A (d + k) := by
      intro i
      exact productSet_mul_pow (hf i) ha
    have h_sum : (∑ i : Fin M, f i) * a ^ k = ∑ i : Fin M, g i := by
      have h : ∑ i : Fin M, g i = ∑ i : Fin M, (f i * a ^ k) := by rfl
      rw [h, Finset.sum_mul] <;> rfl
    rw [h_sum]
    have h_main : ∑ i : Fin M, g i ∈ ExpansionLemma.iteratedSumsetFin (ExpansionLemma.productSet A (d + k)) M :=
      ⟨g, hg, rfl⟩
    rw [ExpansionLemma.iteratedSumsetFin_eq_recursive] at h_main
    exact h_main
  have hx' := h1 x hx
  have hy' := h1 y hy
  have h4 : (x - y) * a ^ k = x * a ^ k - y * a ^ k := by ring
  have h5 : (fun x : ℝ => x * a ^ k) (x - y) = (x - y) * a ^ k := by rfl
  rw [h5, h4]
  exact ⟨x * a ^ k, hx', y * a ^ k, hy', rfl⟩

/-- Positive volume is preserved under multiplication by a nonzero constant. -/
lemma volume_pos_image_mul_const {S : Set ℝ} {c : ℝ} (hc : c ≠ 0)
    (hvol : 0 < volume S) :
    0 < volume ((fun x : ℝ => x * c) '' S) := by
  have h_image_eq : (fun x : ℝ => x * c) '' S = (fun y : ℝ => y / c) ⁻¹' S := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hc] using hx
    · intro hz
      refine ⟨z / c, hz, ?_⟩
      field_simp [hc] <;> ring
  rw [h_image_eq]
  have h_preimage : volume ((fun y : ℝ => y / c) ⁻¹' S) =
      ENNReal.ofReal (|c|) * volume S := by
    have h_div : (fun y : ℝ => y / c) = fun y : ℝ => y * (c⁻¹) := by
      funext y; field_simp [hc]
    rw [h_div]
    rw [Real.volume_preimage_mul_right (inv_ne_zero hc) S]
    have h_abs : |(c⁻¹)⁻¹| = |c| := by
      rw [inv_inv c]
    rw [h_abs]
  rw [h_preimage]
  have hc_pos : 0 < ENNReal.ofReal (|c|) := by
    apply ENNReal.ofReal_pos.mpr
    exact abs_pos.mpr hc
  positivity

/-! ## Format conversion: make productSet and iteratedDifference indices equal -/

/-- Given positive volume of `iteratedDifference (productSet A d) M` with `d ≥ 1`,
produce positive volume of `iteratedDifference (productSet A N) N` for some `N`. -/
lemma convert_to_same_N {A : Set ℝ} {d M : ℕ}
    (hA_nonempty : A.Nonempty) (hA_has_nonzero : ∃ (a : ℝ), a ∈ A ∧ a ≠ 0)
    (hd_pos : 1 ≤ d)
    (hvol : 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M)) :
    ∃ (N : ℕ), 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) N) := by
  rcases hA_has_nonzero with ⟨a, ha, ha_ne⟩
  let N := max d M
  have h_d_le : d ≤ N := le_max_left d M
  have h_M_le : M ≤ N := le_max_right d M
  let k := N - d
  have hN_d : N = d + k := by omega
  let S := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M
  let f : ℝ → ℝ := fun x => x * a ^ k
  have hk_ne : a ^ k ≠ 0 := pow_ne_zero k ha_ne
  have h_image_vol : 0 < volume (f '' S) := volume_pos_image_mul_const hk_ne hvol
  have h_image_subset : f '' S ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M := by
    rw [hN_d]
    exact iteratedDifference_productSet_scale ha ha_ne
  have h_vol1 : 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M) :=
    lt_of_lt_of_le h_image_vol (measure_mono h_image_subset)
  have hPS_nonempty : (ExpansionLemma.productSet A N).Nonempty := by
    rcases hA_nonempty with ⟨x, hx⟩
    refine ⟨x ^ N, ?_⟩
    refine ⟨fun _ => x, fun _ => hx, ?_⟩
    have h : ∏ i : Fin N, (fun _ : Fin N => x) i = x ^ N := by
      simp [Finset.prod_const] <;> ring
    exact h.symm
  have h_mono : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) N :=
    iteratedDifference_mono hPS_nonempty h_M_le
  have h_vol2 : 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) N) :=
    lt_of_lt_of_le h_vol1 (measure_mono h_mono)
  exact ⟨N, h_vol2⟩

/-! ## Main iterative elimination induction -/

/-- **Iterative elimination induction**.

Given compact nonempty `A` with `diam(A) > 0`, weights `v : Fin n → ℝ` in `[1/2,1]`,
and positive volume of `scaledSumset v A`, there exist `d, M` with `d ≥ 1` such that
`volume(iteratedDifference (productSet A d) M) > 0`. -/
lemma iterative_elimination_induction :
    ∀ (n : ℕ), ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
      ∀ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
        0 < volume (ExpansionLemma.scaledSumset v A) →
          ∃ (d M : ℕ), 1 ≤ d ∧
            0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M) := by
  intro n
  induction n with
  | zero =>
    intro A hA hA_nonempty h_diam v hv hvol
    have h0 : ExpansionLemma.scaledSumset v A = {0} := by
      ext x
      simp [ExpansionLemma.scaledSumset]
      <;> constructor <;> intro h <;> simpa using h
    rw [h0] at hvol
    simp at hvol
  | succ n ih =>
    intro A hA hA_nonempty h_diam v hv hvol
    by_cases h_n : n = 0
    · -- Base case: 1 weight
      subst h_n
      have h_v0_pos : 0 < v 0 := by
        have h : v 0 ∈ Set.Icc (1 / 2 : ℝ) 1 := hv 0
        have h1 : 1 / 2 ≤ v 0 := h.1
        have h2 : (0 : ℝ) < 1 / 2 := by norm_num
        linarith
      have h_v0_ne_zero : v 0 ≠ 0 := h_v0_pos.ne'
      have h_ss : ExpansionLemma.scaledSumset v A = (fun x : ℝ => v 0 * x) '' A := by
        ext y
        simp only [ExpansionLemma.scaledSumset, Set.mem_setOf_eq, Set.mem_image]
        constructor
        · rintro ⟨a, ha, h_eq⟩
          have h_sum : ∑ i : Fin 1, v i * a i = v 0 * a 0 := by
            rw [Fin.sum_univ_one] <;> rfl
          have h_y : y = v 0 * a 0 := by
            rw [h_sum] at h_eq; exact h_eq
          exact ⟨a 0, ha 0, h_y.symm⟩
        · rintro ⟨x, hx, h_eq⟩
          let a : Fin 1 → ℝ := fun _ => x
          have ha : ∀ i : Fin 1, a i ∈ A := by
            intro i; simpa [a] using hx
          have h_sum : ∑ i : Fin 1, v i * a i = v 0 * x := by
            rw [Fin.sum_univ_one] <;> simp [a] <;> ring
          have h_y : y = ∑ i : Fin 1, v i * a i := by
            rw [h_sum, h_eq]
          exact ⟨a, ha, h_y⟩
      rw [h_ss] at hvol
      have h_volA : 0 < volume A := by
        have h_pos_image : 0 < volume ((fun x : ℝ => v 0 * x) '' A) := hvol
        let c := (v 0)⁻¹
        have hc_ne : c ≠ 0 := inv_ne_zero h_v0_ne_zero
        have h_image2 : (fun x : ℝ => x * c) '' ((fun x : ℝ => v 0 * x) '' A) = A := by
          ext z
          simp only [c, Set.mem_image, Set.mem_setOf_eq]
          constructor
          · rintro ⟨_, ⟨x, hx, rfl⟩, hz⟩
            have h5 : (v 0 * x) * c = x := by
              dsimp only [c]
              field_simp [h_v0_ne_zero] <;> ring
            have h_z : z = x := by
              rw [h5] at hz
              exact hz.symm
            rw [h_z]
            exact hx
          · intro hz
            refine ⟨v 0 * z, ⟨z, hz, by ring⟩, ?_⟩
            field_simp [h_v0_ne_zero] <;> ring
        have h_vol2 : 0 < volume ((fun x : ℝ => x * c) '' ((fun x : ℝ => v 0 * x) '' A)) :=
          volume_pos_image_mul_const hc_ne h_pos_image
        rw [h_image2] at h_vol2
        exact h_vol2
      rcases hA_nonempty with ⟨a, ha⟩
      have h_translate : (fun x => x - a) '' A ⊆ ExpansionLemma.iteratedDifference A 1 := by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        simp [ExpansionLemma.iteratedDifference, ExpansionLemma.iteratedSumset]
        <;> exact ⟨x, hx, a, ha, by ring⟩
      have h_vol_translate : 0 < volume ((fun x : ℝ => x - a) '' A) := by
        have h_image_eq : (fun x : ℝ => x - a) '' A = (fun y : ℝ => y + a) ⁻¹' A := by
          ext z
          simp only [Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨x, hx, rfl⟩
            simpa using hx
          · intro hz
            refine ⟨z + a, hz, ?_⟩
            ring
        rw [h_image_eq]
        have h_preimage : volume ((fun y : ℝ => y + a) ⁻¹' A) = volume A := by
          simpa using Real.volume_preimage_add a A
        rw [h_preimage]
        exact h_volA
      have h_vol_diff : 0 < volume (ExpansionLemma.iteratedDifference A 1) :=
        lt_of_lt_of_le h_vol_translate (measure_mono h_translate)
      have h_productSet1 : ExpansionLemma.productSet A 1 = A := by
        ext x
        simp only [ExpansionLemma.productSet, Set.mem_setOf_eq, Fin.prod_univ_one]
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ha 0
        · intro hx
          refine ⟨fun _ => x, fun _ => hx, ?_⟩
          simp
      rw [←h_productSet1] at h_vol_diff
      exact ⟨1, 1, by norm_num, h_vol_diff⟩
    · -- Inductive step: n ≥ 1, so n + 1 ≥ 2
      have h_n_pos : 0 < n := by omega
      have h_hn : 2 ≤ n + 1 := by omega
      have h_exp := ExpansionLemma.expansion_lemma hA hA_nonempty h_hn hv hvol
      let N : ℕ := Classical.choose h_exp
      have hN_spec := Classical.choose_spec h_exp
      have hN_pos : 0 < N := hN_spec.1
      have h_j := hN_spec.2
      let j : Fin (n + 1) := Classical.choose h_j
      have h_vol_bound := Classical.choose_spec h_j
      -- Construct R from compactness of scaledSumset
      let S := ExpansionLemma.scaledSumset v A
      have hS_compact : IsCompact S := ExpansionLemma.scaledSumset_compact hA
      have hS_bdd : Bornology.IsBounded S := hS_compact.isBounded
      have h_ball : ∃ (r : ℝ), S ⊆ Metric.ball (0 : ℝ) r :=
        (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hS_bdd
      rcases h_ball with ⟨r, hr⟩
      let R : ℝ := max r 1
      have hR_nonneg : 0 ≤ R := by positivity
      have hR1 : 1 ≤ R := by
        simp [R] <;> omega
      have hS_sub_R : S ⊆ Set.Icc (-R) R := by
        intro x hx
        have h2 : x ∈ Metric.ball (0 : ℝ) r := hr hx
        have h3 : dist x 0 < r := h2
        have h4 : |x| < r := by simpa [dist_eq_norm, Real.norm_eq_abs] using h3
        have h5 : -r < x ∧ x < r := by
          exact abs_lt.mp h4
        have h6 : -R ≤ x := by
          have h7 : -r ≤ x := by linarith
          have hRr : r ≤ R := le_max_left r 1
          have h_neg : -R ≤ -r := by linarith
          linarith
        have h8 : x ≤ R := by
          have h9 : x ≤ r := by linarith
          have hRr : r ≤ R := le_max_left r 1
          linarith
        exact ⟨h6, h8⟩
      let A' := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N
      have hA'_compact : IsCompact A' :=
        iteratedDifference_compact (productSet_compact hA)
      have h_volA' : 0 < volume (ExpansionLemma.scaledSumsetExcept v j A') := by
        have h_diam_pos' : 0 < ENNReal.ofReal (diam A) := ENNReal.ofReal_pos.mpr h_diam
        have h_pos : 0 < ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A) := by
          positivity
        exact lt_of_lt_of_le h_pos h_vol_bound
      have hA'_nonempty : A'.Nonempty := by
        by_contra h
        have h_empty : A' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        have h_ss_empty : ExpansionLemma.scaledSumsetExcept v j A' = ∅ := by
          rw [h_empty]
          ext y
          simp only [ExpansionLemma.scaledSumsetExcept, ExpansionLemma.scaledSumset, Set.mem_empty_iff_false, Set.mem_setOf_eq, iff_false]
          intro h
          rcases h with ⟨a, ha, _⟩
          have h_card : 0 < Fintype.card {i : Fin (n + 1) // i ≠ j} := by
            simp [Fintype.card_subtype_compl] <;> omega
          have h_nonempty : Nonempty {i : Fin (n + 1) // i ≠ j} := Fintype.card_pos_iff.mp h_card
          let i : {i : Fin (n + 1) // i ≠ j} := Classical.choice h_nonempty
          have h_contra : a i ∈ (∅ : Set ℝ) := ha i
          simpa using h_contra
        rw [h_ss_empty] at h_volA'
        simp at h_volA'
      have h_diamA'_pos : 0 < diam A' := by
        by_contra h
        have h_le : diam A' ≤ 0 := by exact Std.not_lt.mp h
        have h0 : diam A' = 0 := le_antisymm h_le diam_nonneg
        rcases hA'_nonempty with ⟨x, hx⟩
        have h_sub : A' ⊆ {x} := by
          intro y hy
          have h1 : dist y x ≤ diam A' := dist_le_diam_of_mem hA'_compact.isBounded hy hx
          rw [h0] at h1
          have h2 : dist y x = 0 := le_antisymm h1 dist_nonneg
          have h3 : y = x := by simpa [dist_eq_zero] using h2
          simpa using h3
        have h_singleton : A' = {x} := by
          apply Set.Subset.antisymm h_sub
          simpa using hx
        let ι := {i : Fin (n + 1) // i ≠ j}
        let w : ι → ℝ := fun i => v i
        have h_ss_singleton : ExpansionLemma.scaledSumset w A' = {∑ i : ι, w i * x} := by
          ext y
          simp only [ExpansionLemma.scaledSumset, Set.mem_singleton_iff, Set.mem_setOf_eq]
          constructor
          · rintro ⟨a, ha, rfl⟩
            have h_all : ∀ i : ι, a i = x := by
              intro i
              have h : a i ∈ A' := ha i
              rw [h_singleton] at h
              simpa using h
            have h_sum : ∑ i : ι, w i * a i = ∑ i : ι, w i * x := by
              apply Finset.sum_congr rfl
              intro i _
              rw [h_all i]
            rw [h_sum]
          · rintro rfl
            refine ⟨fun _ => x, fun _ => by rw [h_singleton] <;> simp, ?_⟩
            <;> rfl
        have h_eq : ExpansionLemma.scaledSumsetExcept v j A' = ExpansionLemma.scaledSumset w A' := by
          rfl
        rw [h_eq, h_ss_singleton] at h_volA'
        simp at h_volA'
      let ι := {i : Fin (n + 1) // i ≠ j}
      let w : ι → ℝ := fun i => v i
      have hw : ∀ i : ι, w i ∈ Set.Icc (1 / 2 : ℝ) 1 := fun i => hv i
      have h_card : Fintype.card ι = n := by
        simp [ι, Fintype.card_subtype_compl]
        <;> omega
      let e2 : Fin (Fintype.card ι) ≃ Fin n :=
        { toFun := Fin.cast h_card
          invFun := Fin.cast h_card.symm
          left_inv := by intro x; simp
          right_inv := by intro x; simp }
      let e : ι ≃ Fin n :=
        (Fintype.equivFin ι).trans e2
      let v' : Fin n → ℝ := fun k => w (e.symm k)
      have hv' : ∀ k : Fin n, v' k ∈ Set.Icc (1 / 2 : ℝ) 1 := fun k => hw (e.symm k)
      have h_eq_ss : ExpansionLemma.scaledSumset v' A' = ExpansionLemma.scaledSumset w A' :=
        scaledSumset_equiv e.symm (v := w)
      have h_vol_v' : 0 < volume (ExpansionLemma.scaledSumset v' A') := by
        rw [h_eq_ss]
        exact h_volA'
      have h_ih := ih A' hA'_compact hA'_nonempty h_diamA'_pos v' hv' h_vol_v'
      rcases h_ih with ⟨d, M', hd_pos, h_vol_result⟩
      have h_contain : A' ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N :=
        subset_refl A'
      let e_idx := d - 1
      have h_d_eq : d = e_idx + 1 := by omega
      have h_productSet_contain : ExpansionLemma.productSet A' d ⊆
          ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (2 * d)) (N ^ d * 2 ^ (d - 1)) := by
        rw [h_d_eq]
        exact productSet_of_iteratedDifference e_idx h_contain
      let B := N ^ d * 2 ^ (d - 1)
      have hPS_nonempty : (ExpansionLemma.productSet A' d).Nonempty := by
        rcases hA'_nonempty with ⟨x, hx⟩
        refine ⟨x ^ d, ?_⟩
        refine ⟨fun _ => x, fun _ => hx, ?_⟩
        have h : ∏ i : Fin d, (fun _ : Fin d => x) i = x ^ d := by
          simp [Finset.prod_const] <;> ring
        exact h.symm
      have h_diff_contain : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A' d) M' ⊆
          ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (2 * d)) (2 * M' * B) :=
        difference_of_difference h_productSet_contain hPS_nonempty
      have h_final : 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (2 * d)) (2 * M' * B)) :=
        lt_of_lt_of_le h_vol_result (measure_mono h_diff_contain)
      exact ⟨2 * d, 2 * M' * B, by omega, h_final⟩

theorem expansion_theorem
    {κ C : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hC_pos : 0 < C)
    {μ : Measure ℝ} (hμ : IsAllScaleFrostman κ C μ)
    (hμ_supp : μ.support ⊆ Set.Icc (-C) C) :
    ∃ (N : ℕ) (c : ℝ), 0 < c ∧
      ENNReal.ofReal c ≤ volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet μ.support N) N) := by
  -- Step 1: Choose n = least integer with nκ > 1
  have h_exists_n : ∃ (n : ℕ), 1 < (n : ℝ) * κ := by
    have h : ∃ (n : ℕ), 1 / κ < (n : ℝ) := exists_nat_gt (1 / κ)
    rcases h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc (n : ℝ) * κ > (1 / κ) * κ := by gcongr
      _ = 1 := by field_simp [hκ_pos.ne'] <;> ring
  let n : ℕ := Nat.find h_exists_n
  have hn : 1 < (n : ℝ) * κ := Nat.find_spec h_exists_n
  have hn_pos : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hn
    norm_num at hn
    <;> linarith

  -- Step 2: Product measure ν = μ^×n is (nκ, C^n)-Frostman
  let ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    ProductMeasureEnergy.productMeasure (n := n) μ
  have hν_frost : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ν (Metric.ball x r) ≤ ENNReal.ofReal ((C ^ n) * r ^ ((n : ℝ) * κ)) := by
    intro x r hr
    exact hμ.product_ball_bound (n := n) (x := x) (r := r) (hr := hr)
  have hν_prob : ν Set.univ = 1 :=
    ProductMeasureEnergy.product_measure_univ hμ.1

  -- Step 3: Energy bound I_1(ν) < ∞
  have h_energy : robust_projection_main.rieszEnergy (α := 1) (δ := 1) (hδ := by norm_num) ν < ⊤ := by
    have h_bound : robust_projection_main.rieszEnergy (α := 1) (δ := 1) (hδ := by norm_num) ν ≤
        ENNReal.ofReal (1 + C ^ n / ((n : ℝ) * κ - 1)) :=
      hμ.product_riesz_energy_bound (n := n) hn (δ := 1) (hδ := by norm_num)
    have h_lt : ENNReal.ofReal (1 + C ^ n / ((n : ℝ) * κ - 1)) < ⊤ := ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt h_bound h_lt

  -- Step 4: Marstrand projection theorem with cone restriction
  -- We use the open cone of directions whose coordinates are all positive
  -- and pairwise within factor 2. After normalization by the max coordinate,
  -- any direction in the closure gives weights in [1/2,1].
  have h_marstrand : ∃ (v : Fin n → ℝ),
      (∀ i : Fin n, v i ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
      0 < volume (ExpansionLemma.scaledSumset v μ.support) := by
    -- n ≥ 2 since nκ > 1 and κ < 1
    have hn_ge2 : 2 ≤ n := by
      by_contra h
      have h1 : n ≤ 1 := by omega
      have h2 : n = 1 := by omega
      have h2' : (n : ℝ) = 1 := by exact_mod_cast h2
      rw [h2'] at hn
      have h_contra : 1 < κ := by simpa using hn
      linarith [hκ_lt_one]
    letI : IsProbabilityMeasure ν := ⟨hν_prob⟩
    let B : ℝ := 1 + C ^ n / ((n : ℝ) * κ - 1)
    have hB_pos : 0 < B := by positivity
    have hI_uniform : ∀ (ε : ℝ) (hε : 0 < ε),
        robust_projection_main.rieszEnergy (α := 1) (hδ := hε) ν ≤ ENNReal.ofReal B := by
      intro ε hε
      exact hμ.product_riesz_energy_bound hn hε
    -- Use ratioCapOpen cone
    let U : Set (ProductLikeIncidence.Sphere n) := ProductLikeIncidence.ratioCapOpen n
    have hU_open : IsOpen U := ProductLikeIncidence.ratioCapOpen_isOpen
    have hn_pos : 0 < n := by linarith
    have hU_meas : MeasurableSet U := hU_open.measurableSet
    have hU_pos : 0 < ProductLikeIncidence.sphereProbabilityMeasure n U :=
      ProductLikeIncidence.ratioCapOpen_positiveMeasure hn_pos
    -- Compact support of ν
    let K : Set ℝ := μ.support
    have hK_compact : IsCompact K := by
      have h1 : IsCompact (Set.Icc (-C) C) := isCompact_Icc
      exact h1.of_isClosed_subset Measure.isClosed_support hμ_supp
    let Kn : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, x i ∈ K}
    have hKn_closed : IsClosed Kn := by
      have h_eq : Kn = ⋂ i : Fin n, {x : EuclideanSpace ℝ (Fin n) | x i ∈ K} := by
        ext x; simp [Kn] <;> tauto
      rw [h_eq]
      apply isClosed_iInter
      intro i
      exact hK_compact.isClosed.preimage (by fun_prop)
    have hKn_bounded : Bornology.IsBounded Kn := by
      have h1 : Kn ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (n : ℝ) * C) := by
        intro x hx
        have h2 : ∀ i, |x i| ≤ C := fun i => abs_le.mpr (hμ_supp (hx i))
        simp only [Metric.mem_closedBall, dist_zero_right]
        rw [PiLp.norm_eq_of_L2]
        have h_sum : ∑ i : Fin n, |x i| ^ 2 ≤ (n : ℝ) * C ^ 2 := by
          have h3 : ∑ i : Fin n, |x i| ^ 2 ≤ ∑ i : Fin n, C ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have h4 : |x i| ≤ C := h2 i
            have h5 : |x i| ^ 2 ≤ C ^ 2 := by gcongr
            exact h5
          have h6 : ∑ i : Fin n, C ^ 2 = (n : ℝ) * C ^ 2 := by
            simp [Finset.sum_const] <;> ring
          rw [h6] at h3; exact h3
        have h4 : Real.sqrt (∑ i : Fin n, |x i| ^ 2) ≤ Real.sqrt ((n : ℝ) * C ^ 2) := by
          apply Real.sqrt_le_sqrt <;> linarith
        have h5 : Real.sqrt ((n : ℝ) * C ^ 2) = Real.sqrt (n : ℝ) * C := by
          rw [Real.sqrt_mul (by positivity)] <;> rw [Real.sqrt_sq (by linarith)]
        rw [h5] at h4; exact h4
      have h_ball_bdd : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (n : ℝ) * C)) := by exact isBounded_closedBall
      exact h_ball_bdd.subset h1
    have hKn_compact : IsCompact Kn := Metric.isCompact_of_isClosed_isBounded hKn_closed hKn_bounded
    -- ν(Knᶜ) = 0
    let e_eq := EuclideanSpace.equiv (Fin n) ℝ
    letI : IsProbabilityMeasure μ := ⟨hμ.1⟩
    have h_main : ∀ (i : Fin n), ν {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} = 0 := by
      intro i
      have hK_compl_zero : μ Kᶜ = 0 := by exact Measure.measure_compl_support
      have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
      have hK_compl_meas : MeasurableSet Kᶜ := hK_meas.compl
      have h_coord_meas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) := by fun_prop
      have h_meas_set2 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} :=
        h_coord_meas hK_compl_meas
      have h_meas_symm : Measurable e_eq.symm := e_eq.symm.continuous.measurable
      have h1 : ν = Measure.map e_eq.symm (Measure.pi (fun (_ : Fin n) => μ)) := by rfl
      let S : Set (Fin n → ℝ) := Set.pi Set.univ (fun j => if j = i then Kᶜ else Set.univ)
      have h_preimage : e_eq.symm ⁻¹' {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} = S := by
        ext f
        simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi]
        have h_eq2 : (e_eq.symm f) i = f i := by simp [e_eq] <;> rfl
        rw [h_eq2]
        constructor
        · intro h
          intro j
          by_cases hji : j = i
          · subst hji
            simpa using h
          · rw [if_neg hji] <;> trivial
        · intro h
          have h_i : f i ∈ (if i = i then Kᶜ else Set.univ) := h i
          simpa using h_i
      have h2 : ν {x | x i ∉ K} = (Measure.pi (fun (_ : Fin n) => μ)) S := by
        calc ν {x | x i ∉ K}
          = (Measure.map e_eq.symm (Measure.pi (fun (_ : Fin n) => μ))) {x | x i ∉ K} := by rw [h1]
        _ = (Measure.pi (fun (_ : Fin n) => μ)) (e_eq.symm ⁻¹' {x | x i ∉ K}) := by
          rw [Measure.map_apply h_meas_symm h_meas_set2]
        _ = (Measure.pi (fun (_ : Fin n) => μ)) S := by rw [h_preimage]
      rw [h2]
      have h_pi : (Measure.pi (fun (_ : Fin n) => μ)) S = ∏ j : Fin n, μ (if j = i then Kᶜ else Set.univ) := by
        exact Measure.pi_pi (fun x => μ) fun j => if j = i then Kᶜ else univ
      rw [h_pi]
      have h_prod : ∏ j : Fin n, μ (if j = i then Kᶜ else Set.univ) = μ Kᶜ := by
        have h2 : (∏ j : Fin n, μ (if j = i then Kᶜ else Set.univ)) =
            ∏ j ∈ Finset.univ, μ (if j = i then Kᶜ else Set.univ) := by simp
        rw [h2]
        have h_eq : ∏ j ∈ Finset.univ, μ (if j = i then Kᶜ else Set.univ) =
            μ (if i = i then Kᶜ else Set.univ) :=
          Finset.prod_eq_single_of_mem i (Finset.mem_univ i) (fun j _ hji => by
            have h10 : (if j = i then Kᶜ else Set.univ) = Set.univ := by simp [hji]
            rw [h10, measure_univ])
        rw [h_eq] <;> simp
      rw [h_prod, hK_compl_zero]
    have h_union : Knᶜ = ⋃ i ∈ Finset.univ, {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} := by
      ext x; simp [Kn, Set.mem_univ] <;> tauto
    have h_meas_set : ∀ i : Fin n, MeasurableSet {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} := by
      intro i
      have h_meas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) := by fun_prop
      exact h_meas (hK_compact.isClosed.measurableSet.compl)
    have h_null_union : ν (⋃ i ∈ Finset.univ, {x : EuclideanSpace ℝ (Fin n) | x i ∉ K}) = 0 := by
      have h : ∀ (s : Finset (Fin n)), ν (⋃ k ∈ s, {x : EuclideanSpace ℝ (Fin n) | x k ∉ K}) = 0 := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | @insert i s hi ih =>
          rw [Finset.set_biUnion_insert i s (fun k : Fin n => {x : EuclideanSpace ℝ (Fin n) | x k ∉ K})]
          have h_union : ν (({x : EuclideanSpace ℝ (Fin n) | x i ∉ K} ∪ ⋃ k ∈ s, {x | x k ∉ K})) ≤
              ν {x | x i ∉ K} + ν (⋃ k ∈ s, {x | x k ∉ K}) :=
            measure_union_le _ _
          have h_le : ν (({x : EuclideanSpace ℝ (Fin n) | x i ∉ K} ∪ ⋃ k ∈ s, {x | x k ∉ K})) ≤ 0 := by
            rw [h_main i, ih] at h_union
            <;> simpa using h_union
          exact le_antisymm h_le (by positivity)
      exact h Finset.univ
    have hν_Kn_compl : ν Knᶜ = 0 := by
      rw [h_union]
      exact h_null_union
    have h_ae : Kn ∈ MeasureTheory.ae ν := by
      exact mem_ae_iff.mpr hν_Kn_compl
    have hν_supp_sub : ν.support ⊆ Kn :=
      MeasureTheory.Measure.support_subset_of_isClosed hKn_closed h_ae
    have hν_supp_compact : IsCompact ν.support :=
      hKn_compact.of_isClosed_subset Measure.isClosed_support hν_supp_sub
    -- Apply cone Marstrand theorem
    rcases ProductLikeIncidence.marstrand_cone_positive_volume hn_ge2 hB_pos ν hI_uniform U hU_meas hU_pos hν_supp_compact
      with ⟨θ, hθ_closure, hθ_vol_bound⟩
    have hθ_vol : 0 < volume (ProductLikeIncidence.linearProjection θ.val '' ν.support) := by
      have h_c_pos : 0 < (ProductLikeIncidence.sphereProbabilityMeasure n U).toReal / (ProductLikeIncidence.marstrandSphereConstant n * B) := by
        have hα_pos : 0 < (ProductLikeIncidence.sphereProbabilityMeasure n U).toReal := by
          have h_ne : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≠ 0 := hU_pos.ne'
          have h_bdd : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≤ 1 := by
            letI : IsProbabilityMeasure (ProductLikeIncidence.sphereProbabilityMeasure n) :=
              ProductLikeIncidence.sphereProbabilityMeasure_isProbability (by linarith)
            have h3 : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≤ (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) := measure_mono (subset_univ U)
            have h4 : (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) = 1 := measure_univ
            rw [h4] at h3; exact h3
          have h_top : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≠ ⊤ :=
            ne_top_of_le_ne_top (by simp) h_bdd
          exact ENNReal.toReal_pos h_ne h_top
        have hC_pos : 0 < ProductLikeIncidence.marstrandSphereConstant n := by
          dsimp only [ProductLikeIncidence.marstrandSphereConstant]
          have h_d_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by linarith)
          exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
        positivity
      have h1 : 0 < ENNReal.ofReal ((ProductLikeIncidence.sphereProbabilityMeasure n U).toReal / (ProductLikeIncidence.marstrandSphereConstant n * B)) :=
        ENNReal.ofReal_pos.mpr h_c_pos
      exact lt_of_lt_of_le h1 hθ_vol_bound
    -- Derive properties from θ ∈ closure U
    have hθ_nonneg : ∀ i : Fin n, 0 ≤ θ.val i := by
      intro i
      have h_cont : Continuous (fun φ : ProductLikeIncidence.Sphere n => φ.val i) := by fun_prop
      have h_closed : IsClosed {φ : ProductLikeIncidence.Sphere n | 0 ≤ φ.val i} :=
        isClosed_Ici.preimage h_cont
      have h_sub : U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ φ.val i} := by
        intro φ hφ
        have h6 : ∀ i, 0 < φ.val i := hφ.1
        have h7 : 0 ≤ φ.val i := le_of_lt (h6 i)
        exact h7
      have h7 : closure U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ φ.val i} :=
        closure_minimal h_sub h_closed
      exact h7 hθ_closure
    have hθ_ratio : ∀ i j : Fin n, θ.val i ≤ 2 * θ.val j := by
      intro i j
      have h_cont : Continuous (fun φ : ProductLikeIncidence.Sphere n => 2 * φ.val j - φ.val i) := by fun_prop
      have h_closed : IsClosed {φ : ProductLikeIncidence.Sphere n | 0 ≤ 2 * φ.val j - φ.val i} :=
        isClosed_Ici.preimage h_cont
      have h_sub : U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ 2 * φ.val j - φ.val i} := by
        intro φ hφ
        have h6 : ∀ (i j : Fin n), φ.val i < 2 * φ.val j := hφ.2
        have h7 : φ.val i < 2 * φ.val j := h6 i j
        have h8 : 0 ≤ 2 * φ.val j - φ.val i := by linarith
        exact h8
      have h7 : closure U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ 2 * φ.val j - φ.val i} :=
        closure_minimal h_sub h_closed
      have h8 : 0 ≤ 2 * θ.val j - θ.val i := h7 hθ_closure
      linarith
    -- All θ.val i > 0
    have hθ_pos : ∀ i : Fin n, 0 < θ.val i := by
      intro i
      by_contra h
      have h0 : θ.val i = 0 := by linarith [hθ_nonneg i]
      have h1 : ∀ j : Fin n, θ.val j = 0 := by
        intro j
        have h2 : θ.val j ≤ 2 * θ.val i := hθ_ratio j i
        rw [h0] at h2
        linarith [hθ_nonneg j]
      have h3 : θ.val = 0 := by
        ext j
        exact h1 j
      have h4 : ‖θ.val‖ = 0 := by rw [h3] <;> simp
      have h5 : ‖θ.val‖ = 1 := by
        have h_sphere : θ.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := θ.property
        simpa [Metric.mem_sphere, dist_zero_right] using h_sphere
      rw [h4] at h5 <;> norm_num at h5
    -- Normalize by maximum coordinate
    have h_univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
      refine ⟨⟨0, by linarith⟩, Finset.mem_univ _⟩
    have h_exists_max : ∃ (j : Fin n), j ∈ Finset.univ ∧ ∀ (i : Fin n), i ∈ Finset.univ → θ.val i ≤ θ.val j :=
      Finset.exists_max_image Finset.univ (fun i : Fin n => θ.val i) h_univ_nonempty
    rcases h_exists_max with ⟨j, _, hj_max⟩
    let m : ℝ := θ.val j
    have hm_pos : 0 < m := hθ_pos j
    have h_le_max : ∀ i : Fin n, θ.val i ≤ m := fun i => hj_max i (Finset.mem_univ i)
    have h_half_max : ∀ i : Fin n, m ≤ 2 * θ.val i := by
      intro i
      exact hθ_ratio j i
    let v : Fin n → ℝ := fun i => θ.val i / m
    have hv1 : ∀ i, v i ≤ 1 := by
      intro i
      dsimp only [v]
      have h : θ.val i ≤ m := h_le_max i
      have hpos : 0 < m := hm_pos
      have hdiv : θ.val i / m ≤ 1 := by
        calc θ.val i / m ≤ m / m := by gcongr
          _ = 1 := by
            field_simp [hpos.ne'] <;> ring
      exact hdiv
    have hv2 : ∀ i, 1 / 2 ≤ v i := by
      intro i
      dsimp only [v]
      have h9 : m ≤ 2 * θ.val i := h_half_max i
      have h10 : m / 2 ≤ θ.val i := by linarith
      have h11 : 0 < m := hm_pos
      have h12 : (1 / 2 : ℝ) ≤ θ.val i / m := by
        have h13 : m / 2 ≤ θ.val i := h10
        have h14 : (m / 2) / m ≤ θ.val i / m := by
          apply div_le_div_of_nonneg_right h13 (by linarith)
        have h15 : (m / 2) / m = (1 / 2 : ℝ) := by
          field_simp [h11.ne'] <;> ring
        rw [h15] at h14
        exact h14
      exact h12
    have hv_in_Icc : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1 := fun i => ⟨hv2 i, hv1 i⟩
    -- Projection of Kn equals scaledSumset
    have h_inner : ∀ (x : EuclideanSpace ℝ (Fin n)),
        ProductLikeIncidence.linearProjection θ.val x = ∑ i : Fin n, θ.val i * x i := by
      intro x
      have h : ProductLikeIncidence.linearProjection θ.val x = ∑ i : Fin n, x i * θ.val i := by
        simp [ProductLikeIncidence.linearProjection, PiLp.inner_apply]
        <;> ring
      rw [h]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h_proj_eq : ProductLikeIncidence.linearProjection θ.val '' Kn =
        ExpansionLemma.scaledSumset θ.val K := by
      ext y
      simp only [Set.mem_image, Kn, ExpansionLemma.scaledSumset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨fun i => x i, hx, ?_⟩
        rw [h_inner x]
      · rintro ⟨a, ha, rfl⟩
        let x : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm a
        have h_eq2 : ∀ i, x i = a i := by intro i; rfl
        have hx : x ∈ Kn := by
          have h : ∀ i, x i ∈ K := by
            intro i
            rw [h_eq2 i]
            exact ha i
          simpa [Kn] using h
        refine ⟨x, hx, ?_⟩
        have h_eq : (∑ i : Fin n, θ.val i * a i) = (∑ i : Fin n, θ.val i * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h_eq2 i]
        rw [h_inner x, h_eq]
    -- Positive volume of projection of support implies positive volume of scaled sumset
    have h_supp_proj_sub : ProductLikeIncidence.linearProjection θ.val '' ν.support ⊆
        ProductLikeIncidence.linearProjection θ.val '' Kn :=
      Set.image_mono hν_supp_sub
    have h_vol_scaled : 0 < volume (ExpansionLemma.scaledSumset θ.val K) := by
      calc 0 < volume (ProductLikeIncidence.linearProjection θ.val '' ν.support) := hθ_vol
        _ ≤ volume (ProductLikeIncidence.linearProjection θ.val '' Kn) := measure_mono h_supp_proj_sub
        _ = volume (ExpansionLemma.scaledSumset θ.val K) := by rw [h_proj_eq]
    -- Relate scaledSumset θ.val K to scaledSumset v K via scaling factor m
    have hθ_eq : θ.val = fun i => m * v i := by
      funext i
      dsimp only [v]
      <;> field_simp [hm_pos.ne'] <;> ring
    have h_scaled_eq : ExpansionLemma.scaledSumset θ.val K = m • ExpansionLemma.scaledSumset v K := by
      rw [hθ_eq]
      ext y
      simp only [ExpansionLemma.scaledSumset, Set.mem_setOf_eq, Set.mem_smul_set]
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨∑ i : Fin n, v i * a i, ⟨a, ha, rfl⟩, ?_⟩
        have h_sum : ∑ i : Fin n, (m * v i) * a i = m * (∑ i : Fin n, v i * a i) := by
          have h_assoc : ∀ i, (m * v i) * a i = m * (v i * a i) := by intro i; ring
          calc ∑ i : Fin n, (m * v i) * a i
            = ∑ i : Fin n, m * (v i * a i) := by apply Finset.sum_congr rfl; intro i _; exact h_assoc i
          _ = m * (∑ i : Fin n, v i * a i) := by rw [Finset.mul_sum]
        have h_smul : m • (∑ i : Fin n, v i * a i) = m * (∑ i : Fin n, v i * a i) := by simp
        rw [h_smul]
        exact h_sum.symm
      · rintro ⟨_, ⟨a, ha, rfl⟩, hz⟩
        refine ⟨a, ha, ?_⟩
        have h_sum : ∑ i : Fin n, (m * v i) * a i = m * (∑ i : Fin n, v i * a i) := by
          have h_assoc : ∀ i, (m * v i) * a i = m * (v i * a i) := by intro i; ring
          calc ∑ i : Fin n, (m * v i) * a i
            = ∑ i : Fin n, m * (v i * a i) := by apply Finset.sum_congr rfl; intro i _; exact h_assoc i
          _ = m * (∑ i : Fin n, v i * a i) := by rw [Finset.mul_sum]
        have h_smul : m • (∑ i : Fin n, v i * a i) = m * (∑ i : Fin n, v i * a i) := by simp [smul_eq_mul]
        have hz' : m * (∑ i : Fin n, v i * a i) = y := by
          rw [h_smul] at hz
          exact hz
        exact (h_sum.trans hz').symm
    have h_vol_v : 0 < volume (ExpansionLemma.scaledSumset v K) := by
      rw [h_scaled_eq] at h_vol_scaled
      have h10 : m⁻¹ ≠ 0 := by positivity
      have h_preimage_eq : (fun x : ℝ => m⁻¹ * x) ⁻¹' (ExpansionLemma.scaledSumset v K) =
          m • ExpansionLemma.scaledSumset v K := by
        ext y
        have hm_ne : m ≠ 0 := hm_pos.ne'
        simp only [Set.mem_preimage, Set.mem_smul_set, smul_eq_mul]
        constructor
        · intro h
          refine ⟨m⁻¹ * y, h, ?_⟩
          have h_mul : m * (m⁻¹ * y) = y := mul_inv_cancel_left₀ hm_ne y
          exact h_mul
        · rintro ⟨a, ha, h_eq⟩
          have h_mul : m⁻¹ * y = a := by
            rw [←h_eq, inv_mul_cancel_left₀ hm_ne]
          rw [h_mul]
          exact ha
      have h9 : volume (m • ExpansionLemma.scaledSumset v K) =
          ENNReal.ofReal (|m|) * volume (ExpansionLemma.scaledSumset v K) := by
        have h11 := Real.volume_preimage_mul_left h10 (ExpansionLemma.scaledSumset v K)
        rw [h_preimage_eq] at h11
        have h12 : |(m⁻¹)⁻¹| = |m| := by
          have h13 : (m⁻¹)⁻¹ = m := by
            field_simp [hm_pos.ne']
          rw [h13]
        rw [h12] at h11
        exact h11
      rw [h9] at h_vol_scaled
      have h13 : 0 < ENNReal.ofReal (|m|) := by
        exact ENNReal.ofReal_pos.mpr (abs_pos.mpr hm_pos.ne')
      exact (ENNReal.mul_pos_iff).mp h_vol_scaled |>.2
    exact ⟨v, hv_in_Icc, h_vol_v⟩

  rcases h_marstrand with ⟨v, hv, hvol_pos⟩

  -- Step 5: Apply Expansion Lemma iteratively to eliminate weights
  -- We need n-1 applications.
  -- Base: we have volume(scaledSumset v K) > 0
  -- Each application eliminates one weight and replaces K by
  -- N_i · K^(2) - N_i · K^(2).
  -- After n-1 steps, we get a single remaining weight, which means
  -- we have volume of a scaled copy of N·K^(N) - N·K^(N).

  -- The remaining block carries out the iterative argument.
  -- The Expansion Lemma (Lemma 3.2) states:
  -- Given compact A, weights v ∈ [1/2,1]^n, positive volume scaled sumset,
  -- ∃ N > 0, ∃ j, such that volume(scaledSumsetExcept v j
  --   (iteratedDifference (productSet A 2) N)) ≥ diam(A) * volume(scaledSumset v A)

  -- We need:
  -- 1. K = supp(μ) is compact (follows from bounded support + closed support)
  -- 2. diam(K) > 0 (follows from Frostman non-concentration)
  -- 3. Iterate the lemma n-1 times

  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hK_compact : IsCompact μ.support := by
    have h1 : IsCompact (Set.Icc (-C) C) := isCompact_Icc
    exact h1.of_isClosed_subset MeasureTheory.Measure.isClosed_support hμ_supp
  have hK_nonempty : μ.support.Nonempty := by
    by_contra h
    have h_empty : μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_zero : μ = 0 := by exact Measure.support_eq_empty_iff.mp h_empty
    rw [h_zero] at hμ_univ
    simp at hμ_univ
  have hK_diam_pos : 0 < diam μ.support := by
    by_contra h
    have h_le : diam μ.support ≤ 0 := by exact Std.not_lt.mp h
    have h0 : diam μ.support = 0 := le_antisymm h_le diam_nonneg
    rcases hK_nonempty with ⟨x, hx⟩
    have h_sub : μ.support ⊆ {x} := by
      intro y hy
      have h1 : dist y x ≤ diam μ.support := dist_le_diam_of_mem hK_compact.isBounded hy hx
      rw [h0] at h1
      have h2 : 0 ≤ dist y x := dist_nonneg
      have h3 : dist y x = 0 := le_antisymm h1 h2
      have h4 : y = x := by
        simpa [dist_eq_zero] using h3
      simpa using h4
    have h_singleton : μ.support = {x} := by
      apply Set.Subset.antisymm h_sub
      simpa using hx
    have h_frost := hμ.2.2.2
    let r : ℝ := (1 / (2 * C)) ^ (1 / κ)
    have hr_pos : 0 < r := by positivity
    have h_supp_sub : μ.support ⊆ Set.Icc (x - r) (x + r) := by
      rw [h_singleton]
      simp only [Set.singleton_subset_iff, Set.mem_Icc]
      constructor <;> linarith [hr_pos]
    have h_meas1 : μ (Set.Icc (x - r) (x + r)) = 1 := by
      have h_compl : (Set.Icc (x - r) (x + r))ᶜ ⊆ (μ.support)ᶜ := Set.compl_subset_compl.mpr h_supp_sub
      have h2 : μ ((Set.Icc (x - r) (x + r))ᶜ) = 0 :=
        measure_mono_null h_compl Measure.measure_compl_support
      have h3 : μ (Set.Icc (x - r) (x + r)) + μ ((Set.Icc (x - r) (x + r))ᶜ) = μ Set.univ := by
        rw [← measure_union (disjoint_compl_right) measurableSet_Icc.compl] <;> simp
      have h4 : μ (Set.Icc (x - r) (x + r)) = μ Set.univ := by
        rw [h2] at h3 <;> simpa using h3
      rw [h4, hμ_univ]
    have h4 := h_frost x r hr_pos
    rw [h_meas1] at h4
    have h_pos2 : 0 ≤ 1 / (2 * C) := by positivity
    have h6 : r ^ κ = 1 / (2 * C) := by
      have h7 : r = (1 / (2 * C)) ^ (1 / κ) := rfl
      calc r ^ κ
        = ((1 / (2 * C)) ^ (1 / κ)) ^ κ := by rw [h7]
      _ = (1 / (2 * C)) ^ ((1 / κ) * κ) := by exact Eq.symm (Real.rpow_mul h_pos2 (1 / κ) κ)
      _ = (1 / (2 * C)) ^ (1 : ℝ) := by
        have h9 : (1 / κ : ℝ) * κ = 1 := by field_simp [hκ_pos.ne'] <;> ring
        rw [h9]
      _ = 1 / (2 * C) := by simp
    have h5 : C * r ^ κ = 1 / 2 := by
      rw [h6]
      field_simp [hC_pos.ne'] <;> ring
    rw [h5] at h4
    <;> norm_num at h4

  -- Iterative elimination: apply Expansion Lemma n-1 times

  have hA_has_nonzero : ∃ (a : ℝ), a ∈ μ.support ∧ a ≠ 0 := by
    by_contra h
    push Not at h
    have h_sub : μ.support ⊆ {0} := by
      intro x hx
      have h0 : x = 0 := h x hx
      simpa using h0
    have h_singleton : μ.support = {0} := by
      apply Set.Subset.antisymm h_sub
      rcases hK_nonempty with ⟨x, hx⟩
      have h0 : x = 0 := h x hx
      rw [h0] at hx
      simpa using hx
    rw [h_singleton] at hK_diam_pos
    simp at hK_diam_pos <;> linarith

  have h_ind := iterative_elimination_induction n μ.support hK_compact hK_nonempty hK_diam_pos v hv hvol_pos
  rcases h_ind with ⟨d, M, hd_pos, h_vol_dM⟩

  have h_conv := convert_to_same_N hK_nonempty hA_has_nonzero hd_pos h_vol_dM
  rcases h_conv with ⟨N, h_vol_N⟩

  have h_exists_c : ∃ (c : ℝ), 0 < c ∧
      ENNReal.ofReal c ≤ volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet μ.support N) N) := by
    have h_pos : 0 < volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet μ.support N) N) := h_vol_N
    by_cases h_top : volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet μ.support N) N) = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      rw [h_top] <;> simp
    · let r := ENNReal.toReal (volume (ExpansionLemma.iteratedDifference
          (ExpansionLemma.productSet μ.support N) N))
      have hr_pos : 0 < r := ENNReal.toReal_pos h_pos.ne' h_top
      refine ⟨r / 2, by linarith, ?_⟩
      have h_le : ENNReal.ofReal (r / 2) ≤ ENNReal.ofReal r := by
        gcongr <;> linarith
      have h_eq : ENNReal.ofReal r = volume (ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet μ.support N) N) := by
        rw [ENNReal.ofReal_toReal h_top]
      have h_final : ENNReal.ofReal (r / 2) ≤ volume (ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet μ.support N) N) := by
        calc ENNReal.ofReal (r / 2)
          ≤ ENNReal.ofReal r := h_le
          _ = volume (ExpansionLemma.iteratedDifference
              (ExpansionLemma.productSet μ.support N) N) := h_eq
      exact h_final

  exact ⟨N, h_exists_c⟩

/-! ## Uniform expansion theorem -/

/-- Lower bound on diameter from positive scaled sumset volume.
If `volume(scaledSumset v A) ≥ V` and all `v_i ∈ [1/2,1]`, then `diam A ≥ V / (2n)`. -/
lemma diam_lower_from_scaledSumset_volume {n : ℕ} {V : ℝ} {v : Fin n → ℝ} {A : Set ℝ}
    (hA_nonempty : A.Nonempty) (hA_bdd : Bornology.IsBounded A)
    (hv : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hV : ENNReal.ofReal V ≤ volume (ExpansionLemma.scaledSumset v A))
    (hV_pos : 0 < V) (hn_pos : 0 < n) :
    ENNReal.ofReal (V / (2 * (n : ℝ))) ≤ ENNReal.ofReal (diam A) := by
  rcases hA_nonempty with ⟨a0, ha0⟩
  have h1 : ExpansionLemma.scaledSumset v A ⊆
      Set.Icc ((∑ i : Fin n, v i) * a0 - (n : ℝ) * diam A)
        ((∑ i : Fin n, v i) * a0 + (n : ℝ) * diam A) := by
    intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    have h2 : ∀ i : Fin n, |a i - a0| ≤ diam A := by
      intro i
      exact dist_le_diam_of_mem hA_bdd (ha i) ha0
    have h3 : |∑ i : Fin n, v i * a i - (∑ i : Fin n, v i) * a0| ≤ (n : ℝ) * diam A := by
      have h4 : ∑ i : Fin n, v i * a i - (∑ i : Fin n, v i) * a0 =
          ∑ i : Fin n, v i * (a i - a0) := by
        have h41 : (∑ i : Fin n, v i) * a0 = ∑ i : Fin n, v i * a0 := by
          rw [Finset.sum_mul]
        rw [h41]
        have h42 : ∑ i : Fin n, v i * a i - ∑ i : Fin n, v i * a0 =
            ∑ i : Fin n, (v i * a i - v i * a0) := by
          rw [Finset.sum_sub_distrib]
        rw [h42]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h4]
      have h5 : |∑ i : Fin n, v i * (a i - a0)| ≤ ∑ i : Fin n, |v i * (a i - a0)| := by
        exact Finset.abs_sum_le_sum_abs (fun i => v i * (a i - a0)) Finset.univ
      have h6 : ∑ i : Fin n, |v i * (a i - a0)| = ∑ i : Fin n, v i * |a i - a0| := by
        apply Finset.sum_congr rfl
        intro i _
        have hvi_nonneg : 0 ≤ v i := by have h := (hv i).1; linarith
        rw [abs_mul, abs_of_nonneg hvi_nonneg]
      rw [h6] at h5
      have h7 : ∑ i : Fin n, v i * |a i - a0| ≤ ∑ i : Fin n, v i * diam A := by
        apply Finset.sum_le_sum
        intro i _
        have hvi_nonneg : 0 ≤ v i := by have h := (hv i).1; linarith
        have h8 : |a i - a0| ≤ diam A := h2 i
        gcongr
      have h9 : ∑ i : Fin n, v i * diam A = (∑ i : Fin n, v i) * diam A := by
        rw [Finset.sum_mul]
      have h10 : (∑ i : Fin n, v i) * diam A ≤ (n : ℝ) * diam A := by
        have h11 : ∑ i : Fin n, v i ≤ (n : ℝ) := by
          have h12 : ∀ i : Fin n, v i ≤ 1 := fun i => (hv i).2
          have h13 : ∑ i : Fin n, v i ≤ ∑ i : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro i _; exact h12 i
          simpa using h13
        gcongr <;> exact diam_nonneg
      calc |∑ i : Fin n, v i * (a i - a0)|
        ≤ ∑ i : Fin n, v i * |a i - a0| := h5
      _ ≤ (∑ i : Fin n, v i) * diam A := le_trans h7 h9.le
      _ ≤ (n : ℝ) * diam A := h10
    have h4 : -(n : ℝ) * diam A ≤ ∑ i : Fin n, v i * a i - (∑ i : Fin n, v i) * a0 := by
      linarith [abs_le.mp h3]
    have h5 : ∑ i : Fin n, v i * a i - (∑ i : Fin n, v i) * a0 ≤ (n : ℝ) * diam A := by
      linarith [abs_le.mp h3]
    exact ⟨by linarith, by linarith⟩
  have h_vol : volume (ExpansionLemma.scaledSumset v A) ≤
      ENNReal.ofReal (2 * (n : ℝ) * diam A) := by
    have h6 : volume (Set.Icc ((∑ i : Fin n, v i) * a0 - (n : ℝ) * diam A) ((∑ i : Fin n, v i) * a0 + (n : ℝ) * diam A)) =
        ENNReal.ofReal (2 * (n : ℝ) * diam A) := by
      rw [Real.volume_Icc] <;> ring_nf
    have h7 : volume (ExpansionLemma.scaledSumset v A) ≤ ENNReal.ofReal (2 * (n : ℝ) * diam A) := by
      have h71 : volume (ExpansionLemma.scaledSumset v A) ≤
          volume (Set.Icc ((∑ i : Fin n, v i) * a0 - (n : ℝ) * diam A) ((∑ i : Fin n, v i) * a0 + (n : ℝ) * diam A)) :=
        by exact OuterMeasureClass.measure_mono volume h1
      rw [h6] at h71
      exact h71
    exact h7
  have h8 : ENNReal.ofReal V ≤ ENNReal.ofReal (2 * (n : ℝ) * diam A) := le_trans hV h_vol
  have h9 : V ≤ 2 * (n : ℝ) * diam A :=
    ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h8
  have h10 : V / (2 * (n : ℝ)) ≤ diam A := by
    have h11 : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have h12 : 0 < 2 * (n : ℝ) := by positivity
    calc V / (2 * (n : ℝ))
      ≤ (2 * (n : ℝ) * diam A) / (2 * (n : ℝ)) := by gcongr
    _ = diam A := by field_simp [h12.ne'] <;> ring
  exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h10

/-- Uniform quantitative Marstrand bound.

Given a Frostman measure μ on ℝ with support in [-C,C] and nκ > 1,
there exist weights v ∈ [1/2,1]^n such that
`volume(scaledSumset v μ.support) ≥ V_min`,
where `V_min` depends only on κ, C, n (not on μ).

The bound comes from `marstrand_cone_positive_volume`: the projection volume
is at least `σ(U)/(marstrandSphereConstant(n) * B)`, and after normalizing
the direction θ by its maximum coordinate m ≤ 2/√n, the scaled sumset volume
is at least `σ(U)/(marstrandSphereConstant(n) * B) * √n / 2`. -/
lemma marstrand_uniform_lower_bound
    {κ C : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hC_pos : 0 < C)
    {n : ℕ} (hn_pos : 0 < n) (hnκ : 1 < (n : ℝ) * κ)
    (μ : Measure ℝ) (hμ : IsAllScaleFrostman κ C μ)
    (hμ_supp : μ.support ⊆ Set.Icc (-C) C) :
    ∃ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
      ENNReal.ofReal ((ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n)).toReal /
        (ProductLikeIncidence.marstrandSphereConstant n *
          (1 + C ^ n / ((n : ℝ) * κ - 1))) * Real.sqrt n / 2) ≤
      volume (ExpansionLemma.scaledSumset v μ.support) := by
  have hn_ge2 : 2 ≤ n := by
    by_contra h
    have h1 : n ≤ 1 := by omega
    have h2 : n = 1 := by omega
    have h2' : (n : ℝ) = 1 := by exact_mod_cast h2
    rw [h2'] at hnκ
    have h_contra : 1 < κ := by simpa using hnκ
    linarith [hκ_lt_one]
  let B : ℝ := 1 + C ^ n / ((n : ℝ) * κ - 1)
  have hB_pos : 0 < B := by positivity
  letI : IsProbabilityMeasure μ := ⟨hμ.1⟩
  let ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    ProductMeasureEnergy.productMeasure (n := n) μ
  have hν_prob : ν Set.univ = 1 :=
    ProductMeasureEnergy.product_measure_univ hμ.1
  letI : IsProbabilityMeasure ν := ⟨hν_prob⟩
  have hI_uniform : ∀ (ε : ℝ) (hε : 0 < ε),
      robust_projection_main.rieszEnergy (α := 1) (hδ := hε) ν ≤ ENNReal.ofReal B := by
    intro ε hε
    exact hμ.product_riesz_energy_bound hnκ hε
  let U : Set (ProductLikeIncidence.Sphere n) := ProductLikeIncidence.ratioCapOpen n
  have hU_open : IsOpen U := ProductLikeIncidence.ratioCapOpen_isOpen
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hU_pos : 0 < ProductLikeIncidence.sphereProbabilityMeasure n U :=
    ProductLikeIncidence.ratioCapOpen_positiveMeasure hn_pos
  let K : Set ℝ := μ.support
  have hK_compact : IsCompact K := by
    have h1 : IsCompact (Set.Icc (-C) C) := isCompact_Icc
    exact h1.of_isClosed_subset Measure.isClosed_support hμ_supp
  let Kn : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, x i ∈ K}
  have hKn_closed : IsClosed Kn := by
    have h_eq : Kn = ⋂ i : Fin n, {x : EuclideanSpace ℝ (Fin n) | x i ∈ K} := by
      ext x; simp [Kn] <;> tauto
    rw [h_eq]
    apply isClosed_iInter
    intro i
    exact hK_compact.isClosed.preimage (by fun_prop)
  have hKn_bounded : Bornology.IsBounded Kn := by
    have h1 : Kn ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (n : ℝ) * C) := by
      intro x hx
      have h2 : ∀ i, |x i| ≤ C := fun i => abs_le.mpr (hμ_supp (hx i))
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [PiLp.norm_eq_of_L2]
      have h_sum : ∑ i : Fin n, |x i| ^ 2 ≤ (n : ℝ) * C ^ 2 := by
        have h3 : ∑ i : Fin n, |x i| ^ 2 ≤ ∑ i : Fin n, C ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have h4 : |x i| ≤ C := h2 i
          have h5 : |x i| ^ 2 ≤ C ^ 2 := by gcongr
          exact h5
        have h6 : ∑ i : Fin n, C ^ 2 = (n : ℝ) * C ^ 2 := by
          simp [Finset.sum_const] <;> ring
        rw [h6] at h3; exact h3
      have h4 : Real.sqrt (∑ i : Fin n, |x i| ^ 2) ≤ Real.sqrt ((n : ℝ) * C ^ 2) := by
        apply Real.sqrt_le_sqrt <;> linarith
      have h5 : Real.sqrt ((n : ℝ) * C ^ 2) = Real.sqrt (n : ℝ) * C := by
        rw [Real.sqrt_mul (by positivity)] <;> rw [Real.sqrt_sq (by linarith)]
      rw [h5] at h4; exact h4
    have h_ball_bdd : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (n : ℝ) * C)) := by exact isBounded_closedBall
    exact h_ball_bdd.subset h1
  have hKn_compact : IsCompact Kn := Metric.isCompact_of_isClosed_isBounded hKn_closed hKn_bounded
  let e_eq := EuclideanSpace.equiv (Fin n) ℝ
  have h_main : ∀ (i : Fin n), ν {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} = 0 := by
    intro i
    have hK_compl_zero : μ Kᶜ = 0 := by exact Measure.measure_compl_support
    have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
    have hK_compl_meas : MeasurableSet Kᶜ := hK_meas.compl
    have h_coord_meas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) := by fun_prop
    have h_meas_set2 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} :=
      h_coord_meas hK_compl_meas
    have h_meas_symm : Measurable e_eq.symm := e_eq.symm.continuous.measurable
    have h1 : ν = Measure.map e_eq.symm (Measure.pi (fun (_ : Fin n) => μ)) := by rfl
    let S : Set (Fin n → ℝ) := Set.pi Set.univ (fun j => if j = i then Kᶜ else Set.univ)
    have h_preimage : e_eq.symm ⁻¹' {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} = S := by
      ext f
      simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi]
      have h_eq2 : (e_eq.symm f) i = f i := by simp [e_eq] <;> rfl
      rw [h_eq2]
      constructor
      · intro h
        intro j
        by_cases hji : j = i
        · subst hji
          simpa using h
        · rw [if_neg hji] <;> trivial
      · intro h
        have h_i : f i ∈ (if i = i then Kᶜ else Set.univ) := h i
        simpa using h_i
    have h2 : ν {x | x i ∉ K} = (Measure.pi (fun (_ : Fin n) => μ)) S := by
      calc ν {x | x i ∉ K}
        = (Measure.map e_eq.symm (Measure.pi (fun (_ : Fin n) => μ))) {x | x i ∉ K} := by rw [h1]
      _ = (Measure.pi (fun (_ : Fin n) => μ)) (e_eq.symm ⁻¹' {x | x i ∉ K}) := by
        rw [Measure.map_apply h_meas_symm h_meas_set2]
      _ = (Measure.pi (fun (_ : Fin n) => μ)) S := by rw [h_preimage]
    rw [h2]
    have h_pi : (Measure.pi (fun (_ : Fin n) => μ)) S = ∏ j : Fin n, μ (if j = i then Kᶜ else Set.univ) := by
      exact Measure.pi_pi (fun x => μ) fun j => if j = i then Kᶜ else univ
    rw [h_pi]
    have h_prod : ∏ j : Fin n, μ (if j = i then Kᶜ else Set.univ) = μ Kᶜ := by
      have h2 : (∏ j : Fin n, μ (if j = i then Kᶜ else Set.univ)) =
          ∏ j ∈ Finset.univ, μ (if j = i then Kᶜ else Set.univ) := by simp
      rw [h2]
      have h_eq : ∏ j ∈ Finset.univ, μ (if j = i then Kᶜ else Set.univ) =
          μ (if i = i then Kᶜ else Set.univ) :=
        Finset.prod_eq_single_of_mem i (Finset.mem_univ i) (fun j _ hji => by
          have h10 : (if j = i then Kᶜ else Set.univ) = Set.univ := by simp [hji]
          rw [h10, measure_univ])
      rw [h_eq] <;> simp
    rw [h_prod, hK_compl_zero]
  have h_union : Knᶜ = ⋃ i ∈ Finset.univ, {x : EuclideanSpace ℝ (Fin n) | x i ∉ K} := by
    ext x; simp [Kn, Set.mem_univ] <;> tauto
  have h_null_union : ν (⋃ i ∈ Finset.univ, {x : EuclideanSpace ℝ (Fin n) | x i ∉ K}) = 0 := by
    have h : ∀ (s : Finset (Fin n)), ν (⋃ k ∈ s, {x : EuclideanSpace ℝ (Fin n) | x k ∉ K}) = 0 := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.set_biUnion_insert i s (fun k : Fin n => {x : EuclideanSpace ℝ (Fin n) | x k ∉ K})]
        have h_union : ν (({x : EuclideanSpace ℝ (Fin n) | x i ∉ K} ∪ ⋃ k ∈ s, {x | x k ∉ K})) ≤
            ν {x | x i ∉ K} + ν (⋃ k ∈ s, {x | x k ∉ K}) :=
          measure_union_le _ _
        have h_le : ν (({x : EuclideanSpace ℝ (Fin n) | x i ∉ K} ∪ ⋃ k ∈ s, {x | x k ∉ K})) ≤ 0 := by
          rw [h_main i, ih] at h_union <;> simpa using h_union
        exact le_antisymm h_le (by positivity)
    exact h Finset.univ
  have hν_Kn_compl : ν Knᶜ = 0 := by
    rw [h_union]
    exact h_null_union
  have h_ae : Kn ∈ MeasureTheory.ae ν := by
    have h : ν Knᶜ = 0 := hν_Kn_compl
    simpa [MeasureTheory.mem_ae_iff] using h
  have hν_supp_sub : ν.support ⊆ Kn :=
    MeasureTheory.Measure.support_subset_of_isClosed hKn_closed h_ae
  have hν_supp_compact : IsCompact ν.support :=
    hKn_compact.of_isClosed_subset Measure.isClosed_support hν_supp_sub
  let V_n : ℝ := (ProductLikeIncidence.sphereProbabilityMeasure n U).toReal /
      (ProductLikeIncidence.marstrandSphereConstant n * B)
  have hV_n_pos : 0 < V_n := by
    dsimp only [V_n]
    have hα_pos : 0 < (ProductLikeIncidence.sphereProbabilityMeasure n U).toReal := by
      have h_ne : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≠ 0 := hU_pos.ne'
      have h_bdd : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≤ 1 := by
        letI : IsProbabilityMeasure (ProductLikeIncidence.sphereProbabilityMeasure n) :=
          ProductLikeIncidence.sphereProbabilityMeasure_isProbability (by linarith)
        have h3 : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≤ (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) := measure_mono (subset_univ U)
        have h4 : (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) = 1 := measure_univ
        rw [h4] at h3; exact h3
      have h_top : (ProductLikeIncidence.sphereProbabilityMeasure n U) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp) h_bdd
      exact ENNReal.toReal_pos h_ne h_top
    have hC_pos : 0 < ProductLikeIncidence.marstrandSphereConstant n := by
      dsimp only [ProductLikeIncidence.marstrandSphereConstant]
      have h_d_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by linarith)
      exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
    positivity
  rcases ProductLikeIncidence.marstrand_cone_positive_volume hn_ge2 hB_pos ν hI_uniform U hU_meas hU_pos hν_supp_compact
    with ⟨θ, hθ_closure, hθ_vol_bound⟩
  have hθ_nonneg : ∀ i : Fin n, 0 ≤ θ.val i := by
    intro i
    have h_cont : Continuous (fun φ : ProductLikeIncidence.Sphere n => φ.val i) := by fun_prop
    have h_closed : IsClosed {φ : ProductLikeIncidence.Sphere n | 0 ≤ φ.val i} :=
      isClosed_Ici.preimage h_cont
    have h_sub : U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ φ.val i} := by
      intro φ hφ
      have h6 : ∀ i, 0 < φ.val i := hφ.1
      have h7 : 0 ≤ φ.val i := le_of_lt (h6 i)
      exact h7
    have h7 : closure U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ φ.val i} :=
      closure_minimal h_sub h_closed
    exact h7 hθ_closure
  have hθ_ratio : ∀ i j : Fin n, θ.val i ≤ 2 * θ.val j := by
    intro i j
    have h_cont : Continuous (fun φ : ProductLikeIncidence.Sphere n => 2 * φ.val j - φ.val i) := by fun_prop
    have h_closed : IsClosed {φ : ProductLikeIncidence.Sphere n | 0 ≤ 2 * φ.val j - φ.val i} :=
      isClosed_Ici.preimage h_cont
    have h_sub : U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ 2 * φ.val j - φ.val i} := by
      intro φ hφ
      have h6 : ∀ (i j : Fin n), φ.val i < 2 * φ.val j := hφ.2
      have h7 : φ.val i < 2 * φ.val j := h6 i j
      have h8 : 0 ≤ 2 * φ.val j - φ.val i := by linarith
      exact h8
    have h7 : closure U ⊆ {φ : ProductLikeIncidence.Sphere n | 0 ≤ 2 * φ.val j - φ.val i} :=
      closure_minimal h_sub h_closed
    have h8 : 0 ≤ 2 * θ.val j - θ.val i := h7 hθ_closure
    linarith
  have hθ_pos : ∀ i : Fin n, 0 < θ.val i := by
    intro i
    by_contra h
    have h0 : θ.val i = 0 := by linarith [hθ_nonneg i]
    have h1 : ∀ j : Fin n, θ.val j = 0 := by
      intro j
      have h2 : θ.val j ≤ 2 * θ.val i := hθ_ratio j i
      rw [h0] at h2
      linarith [hθ_nonneg j]
    have h3 : θ.val = 0 := by
      ext j
      exact h1 j
    have h4 : ‖θ.val‖ = 0 := by rw [h3] <;> simp
    have h5 : ‖θ.val‖ = 1 := by
      have h_sphere : θ.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := θ.property
      simpa [Metric.mem_sphere, dist_zero_right] using h_sphere
    rw [h4] at h5 <;> norm_num at h5
  have h_univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
    refine ⟨⟨0, by linarith⟩, Finset.mem_univ _⟩
  have h_exists_max : ∃ (j : Fin n), j ∈ Finset.univ ∧ ∀ (i : Fin n), i ∈ Finset.univ → θ.val i ≤ θ.val j :=
    Finset.exists_max_image Finset.univ (fun i : Fin n => θ.val i) h_univ_nonempty
  rcases h_exists_max with ⟨j, _, hj_max⟩
  let m : ℝ := θ.val j
  have hm_pos : 0 < m := hθ_pos j
  have h_le_max : ∀ i : Fin n, θ.val i ≤ m := fun i => hj_max i (Finset.mem_univ i)
  have h_half_max : ∀ i : Fin n, m ≤ 2 * θ.val i := by
    intro i
    exact hθ_ratio j i
  let v : Fin n → ℝ := fun i => θ.val i / m
  have hv1 : ∀ i, v i ≤ 1 := by
    intro i
    dsimp only [v]
    have h : θ.val i ≤ m := h_le_max i
    have hpos : 0 < m := hm_pos
    have hdiv : θ.val i / m ≤ 1 := by
      calc θ.val i / m ≤ m / m := by gcongr
        _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact hdiv
  have hv2 : ∀ i, 1 / 2 ≤ v i := by
    intro i
    dsimp only [v]
    have h9 : m ≤ 2 * θ.val i := h_half_max i
    have h10 : m / 2 ≤ θ.val i := by linarith
    have h11 : 0 < m := hm_pos
    have h12 : (1 / 2 : ℝ) ≤ θ.val i / m := by
      have h13 : m / 2 ≤ θ.val i := h10
      have h14 : (m / 2) / m ≤ θ.val i / m := by
        apply div_le_div_of_nonneg_right h13 (by linarith)
      have h15 : (m / 2) / m = (1 / 2 : ℝ) := by
        field_simp [h11.ne'] <;> ring
      rw [h15] at h14
      exact h14
    exact h12
  have hv_in_Icc : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1 := fun i => ⟨hv2 i, hv1 i⟩
  have h_norm_sq : ∑ i : Fin n, (θ.val i) ^ 2 = 1 := by
    have h_sphere : θ.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := θ.property
    have h : ‖θ.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using h_sphere
    have h2 : ‖θ.val‖ ^ 2 = ∑ i : Fin n, (θ.val i) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      <;> apply Finset.sum_congr rfl
      <;> intro i _ <;> simp [Real.norm_eq_abs] <;> ring
    have h3 : ‖θ.val‖ ^ 2 = 1 := by rw [h] <;> norm_num
    rw [h2] at h3
    exact h3
  have h_m_le : m ≤ 2 / Real.sqrt (n : ℝ) := by
    have h1 : ∀ i : Fin n, m / 2 ≤ θ.val i := by
      intro i
      have h2 : m ≤ 2 * θ.val i := h_half_max i
      linarith
    have h3 : ∑ i : Fin n, (θ.val i) ^ 2 ≥ ∑ i : Fin n, (m / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h4 : m / 2 ≤ θ.val i := h1 i
      have h5 : 0 ≤ m / 2 := by positivity
      nlinarith
    have h6 : ∑ i : Fin n, (m / 2) ^ 2 = (n : ℝ) * (m / 2) ^ 2 := by
      simp [Finset.sum_const] <;> ring
    rw [h6] at h3
    have h7 : (n : ℝ) * (m / 2) ^ 2 ≤ 1 := by linarith [h_norm_sq]
    have h8 : (n : ℝ) * m ^ 2 ≤ 4 := by
      have h9 : (n : ℝ) * (m / 2) ^ 2 = (n : ℝ) * m ^ 2 / 4 := by ring
      rw [h9] at h7
      linarith
    have h10 : (n : ℝ) > 0 := by exact_mod_cast hn_pos
    have h11 : m ^ 2 ≤ 4 / (n : ℝ) := by
      calc m ^ 2
        = ((n : ℝ) * m ^ 2) / (n : ℝ) := by field_simp [h10.ne'] <;> ring
      _ ≤ 4 / (n : ℝ) := by gcongr
    have h10 : 0 < Real.sqrt (n : ℝ) := by positivity
    have h11 : m ≤ Real.sqrt (4 / (n : ℝ)) := by
      have h12 : 0 ≤ m := by linarith
      have h13 : 0 ≤ 4 / (n : ℝ) := by positivity
      exact (Real.le_sqrt' (hθ_pos j)).mpr h11
    have h13 : Real.sqrt (4 / (n : ℝ)) = 2 / Real.sqrt (n : ℝ) := by
      have h14 : Real.sqrt (4 / (n : ℝ)) = Real.sqrt 4 / Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_div (by positivity)]
      rw [h14]
      have h15 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h15] <;> ring
    rw [h13] at h11
    exact h11
  have h_inner : ∀ (x : EuclideanSpace ℝ (Fin n)),
      ProductLikeIncidence.linearProjection θ.val x = ∑ i : Fin n, θ.val i * x i := by
    intro x
    have h : ProductLikeIncidence.linearProjection θ.val x = ∑ i : Fin n, x i * θ.val i := by
      simp [ProductLikeIncidence.linearProjection, PiLp.inner_apply] <;> ring
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_proj_eq : ProductLikeIncidence.linearProjection θ.val '' Kn =
      ExpansionLemma.scaledSumset θ.val K := by
    ext y
    simp only [Set.mem_image, Kn, ExpansionLemma.scaledSumset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun i => x i, hx, ?_⟩
      rw [h_inner x]
    · rintro ⟨a, ha, rfl⟩
      let x : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm a
      have h_eq2 : ∀ i, x i = a i := by intro i; rfl
      have hx : x ∈ Kn := by
        have h : ∀ i, x i ∈ K := by
          intro i
          rw [h_eq2 i]
          exact ha i
        simpa [Kn] using h
      refine ⟨x, hx, ?_⟩
      have h_eq : (∑ i : Fin n, θ.val i * a i) = (∑ i : Fin n, θ.val i * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h_eq2 i]
      rw [h_inner x, h_eq]
  have h_supp_proj_sub : ProductLikeIncidence.linearProjection θ.val '' ν.support ⊆
      ProductLikeIncidence.linearProjection θ.val '' Kn :=
    Set.image_mono hν_supp_sub
  have h_vol_scaled : ENNReal.ofReal V_n ≤ volume (ExpansionLemma.scaledSumset θ.val K) := by
    calc ENNReal.ofReal V_n
      ≤ volume (ProductLikeIncidence.linearProjection θ.val '' ν.support) := hθ_vol_bound
    _ ≤ volume (ProductLikeIncidence.linearProjection θ.val '' Kn) := measure_mono h_supp_proj_sub
    _ = volume (ExpansionLemma.scaledSumset θ.val K) := by rw [h_proj_eq]
  have hθ_eq : θ.val = fun i => m * v i := by
    funext i
    dsimp only [v]
    <;> field_simp [hm_pos.ne'] <;> ring
  have h_scaled_eq : ExpansionLemma.scaledSumset θ.val K = m • ExpansionLemma.scaledSumset v K := by
    rw [hθ_eq]
    ext y
    simp only [ExpansionLemma.scaledSumset, Set.mem_setOf_eq, Set.mem_smul_set]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨∑ i : Fin n, v i * a i, ⟨a, ha, rfl⟩, ?_⟩
      have h_sum : ∑ i : Fin n, (m * v i) * a i = m * (∑ i : Fin n, v i * a i) := by
        have h_assoc : ∀ i, (m * v i) * a i = m * (v i * a i) := by intro i; ring
        calc ∑ i : Fin n, (m * v i) * a i
          = ∑ i : Fin n, m * (v i * a i) := by apply Finset.sum_congr rfl; intro i _; exact h_assoc i
        _ = m * (∑ i : Fin n, v i * a i) := by rw [Finset.mul_sum]
      have h_smul : m • (∑ i : Fin n, v i * a i) = m * (∑ i : Fin n, v i * a i) := by
        simp [smul_eq_mul]
      rw [h_smul]
      exact h_sum.symm
    · rintro ⟨x, hx, hz⟩
      rcases hx with ⟨a, ha, rfl⟩
      refine ⟨a, ha, ?_⟩
      have h_smul : m • (∑ i : Fin n, v i * a i) = m * (∑ i : Fin n, v i * a i) := by
        exact smul_eq_mul m (∑ i, v i * a i)
      have hz' : m * (∑ i : Fin n, v i * a i) = y := by
        rw [←h_smul, hz]
      have h_sum : ∑ i : Fin n, (m * v i) * a i = m * (∑ i : Fin n, v i * a i) := by
        have h_assoc : ∀ i, (m * v i) * a i = m * (v i * a i) := by intro i; ring
        calc ∑ i : Fin n, (m * v i) * a i
          = ∑ i : Fin n, m * (v i * a i) := by apply Finset.sum_congr rfl; intro i _; exact h_assoc i
        _ = m * (∑ i : Fin n, v i * a i) := by rw [Finset.mul_sum]
      exact (h_sum.trans hz').symm
  have h10 : m⁻¹ ≠ 0 := by positivity
  have h_preimage_eq : (fun x : ℝ => m⁻¹ * x) ⁻¹' (ExpansionLemma.scaledSumset v K) =
      m • ExpansionLemma.scaledSumset v K := by
    ext y
    have hm_ne : m ≠ 0 := hm_pos.ne'
    simp only [Set.mem_preimage, Set.mem_smul_set, smul_eq_mul]
    constructor
    · intro h
      refine ⟨m⁻¹ * y, h, ?_⟩
      have h_mul : m * (m⁻¹ * y) = y := mul_inv_cancel_left₀ hm_ne y
      exact h_mul
    · rintro ⟨a, ha, h_eq⟩
      have h_mul : m⁻¹ * y = a := by
        rw [←h_eq, inv_mul_cancel_left₀ hm_ne]
      rw [h_mul]
      exact ha
  have h9 : volume (m • ExpansionLemma.scaledSumset v K) =
      ENNReal.ofReal (|m|) * volume (ExpansionLemma.scaledSumset v K) := by
    have h11 := Real.volume_preimage_mul_left h10 (ExpansionLemma.scaledSumset v K)
    rw [h_preimage_eq] at h11
    have h12 : |(m⁻¹)⁻¹| = |m| := by
      have h13 : (m⁻¹)⁻¹ = m := by field_simp [hm_pos.ne']
      rw [h13]
    rw [h12] at h11
    exact h11
  have h_abs_m : |m| = m := abs_of_pos hm_pos
  rw [h_scaled_eq] at h_vol_scaled
  rw [h9, h_abs_m] at h_vol_scaled
  have h_final : ENNReal.ofReal (V_n * Real.sqrt (n : ℝ) / 2) ≤ volume (ExpansionLemma.scaledSumset v K) := by
    by_cases h_top : volume (ExpansionLemma.scaledSumset v K) = ⊤
    · rw [h_top] <;> simp
    · have h_ne_top : volume (ExpansionLemma.scaledSumset v K) ≠ ⊤ := h_top
      set r : ℝ := ENNReal.toReal (volume (ExpansionLemma.scaledSumset v K)) with hr_def
      have h_eq : ENNReal.ofReal r = volume (ExpansionLemma.scaledSumset v K) :=
        ENNReal.ofReal_toReal h_ne_top
      have h_mul : ENNReal.ofReal m * volume (ExpansionLemma.scaledSumset v K) = ENNReal.ofReal (m * r) := by
        rw [←h_eq]
        have h : ENNReal.ofReal m * ENNReal.ofReal r = ENNReal.ofReal (m * r) := by
          exact (ENNReal.ofReal_mul (show 0 ≤ m by linarith)).symm
        exact h
      have h_ineq : V_n ≤ m * r := by
        have h : ENNReal.ofReal V_n ≤ ENNReal.ofReal (m * r) := by
          rw [←h_mul]; exact h_vol_scaled
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
      have h1 : V_n / m ≤ r := by
        calc V_n / m ≤ (m * r) / m := by gcongr
          _ = r := by field_simp [hm_pos.ne'] <;> ring
      have h2 : V_n * Real.sqrt (n : ℝ) / 2 ≤ V_n / m := by
        have h3 : V_n * Real.sqrt (n : ℝ) / 2 = V_n / (2 / Real.sqrt (n : ℝ)) := by
          have h4 : 0 < Real.sqrt (n : ℝ) := by positivity
          field_simp [h4.ne'] <;> ring
        rw [h3]
        have h5 : m ≤ 2 / Real.sqrt (n : ℝ) := h_m_le
        have h6 : 0 < V_n := hV_n_pos
        gcongr
      have h_goal : V_n * Real.sqrt (n : ℝ) / 2 ≤ r := by linarith
      have h_main : ENNReal.ofReal (V_n * Real.sqrt (n : ℝ) / 2) ≤ ENNReal.ofReal r :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h_goal
      rw [h_eq] at h_main
      exact h_main
  exact ⟨v, hv_in_Icc, h_final⟩

/-- Upper bound on iterated sumset of a bounded set. -/
lemma iteratedSumset_bounded {S : Set ℝ} {N : ℕ} {R : ℝ} (hR_nonneg : 0 ≤ R)
    (hS : S ⊆ Set.Icc (-R) R) :
    ExpansionLemma.iteratedSumset S N ⊆ Set.Icc (-(N : ℝ) * R) ((N : ℝ) * R) := by
  induction N with
  | zero =>
    intro z hz
    simp [ExpansionLemma.iteratedSumset] at hz
    rw [hz]
    <;> simp [hR_nonneg] <;> linarith
  | succ N ih =>
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hx' : x ∈ Set.Icc (-R) R := hS hx
    have hy' : y ∈ Set.Icc (-(N : ℝ) * R) ((N : ℝ) * R) := ih hy
    have h1 : -((N.succ : ℝ)) * R ≤ x + y := by
      simp [Nat.cast_add, Nat.cast_one] at * <;> linarith
    have h2 : x + y ≤ (N.succ : ℝ) * R := by
      simp [Nat.cast_add, Nat.cast_one] at * <;> linarith
    exact ⟨h1, h2⟩

/-- Upper bound on diameter of iterated difference of product set. -/
lemma diam_upper_iteratedDifference_productSet {A : Set ℝ} {N R : ℕ}
    (hA : A ⊆ Set.Icc (-R : ℝ) R) :
    ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N ⊆
      Set.Icc (-(2 * (N : ℝ) * (R : ℝ)^2)) (2 * (N : ℝ) * (R : ℝ)^2) := by
  have hR_nonneg : 0 ≤ (R : ℝ) := by positivity
  have h1 : ExpansionLemma.productSet A 2 ⊆ Set.Icc (-(R : ℝ)^2) ((R : ℝ)^2) := by
    intro z hz
    have h_exists : ∃ (a : Fin 2 → ℝ), (∀ i, a i ∈ A) ∧ z = ∏ i : Fin 2, a i := by
      simpa [ExpansionLemma.productSet] using hz
    rcases h_exists with ⟨a, ha, h_eq⟩
    have h3 : a 0 ∈ Set.Icc (-(R : ℝ)) (R : ℝ) := hA (ha 0)
    have h4 : a 1 ∈ Set.Icc (-(R : ℝ)) (R : ℝ) := hA (ha 1)
    have h5 : -(R : ℝ)^2 ≤ a 0 * a 1 := by
      nlinarith [h3.1, h3.2, h4.1, h4.2]
    have h6 : a 0 * a 1 ≤ (R : ℝ)^2 := by
      nlinarith [h3.1, h3.2, h4.1, h4.2]
    have h_prod : (∏ i : Fin 2, a i) = a 0 * a 1 := by
      simp [Fin.prod_univ_two] <;> ring
    rw [h_eq, h_prod]
    exact ⟨h5, h6⟩
  have hR2_nonneg : 0 ≤ (R : ℝ)^2 := by positivity
  have h2 : ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) N ⊆
      Set.Icc (-(N : ℝ) * (R : ℝ)^2) ((N : ℝ) * (R : ℝ)^2) :=
    iteratedSumset_bounded (N := N) hR2_nonneg h1
  intro z hz
  rcases hz with ⟨x, hx, y, hy, h_eq⟩
  have hx' : x ∈ Set.Icc (-(N : ℝ) * (R : ℝ)^2) ((N : ℝ) * (R : ℝ)^2) := h2 hx
  have hy' : y ∈ Set.Icc (-(N : ℝ) * (R : ℝ)^2) ((N : ℝ) * (R : ℝ)^2) := h2 hy
  have h_z1 : -(2 * (N : ℝ) * (R : ℝ)^2) ≤ x - y := by
    nlinarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have h_z2 : x - y ≤ 2 * (N : ℝ) * (R : ℝ)^2 := by
    nlinarith [hx'.1, hx'.2, hy'.1, hy'.2]
  exact h_eq ▸ ⟨h_z1, h_z2⟩

/-! ## Uniform Expansion Theorem

N depends only on κ,C, not on μ.  This wires together:
1. Uniform Expansion Lemma (bacon: `expansion_lemma_uniform(n, d_max, V_min)`)
2. Uniform Iterative Elimination (granite: common N for all A)
3. Quantitative Marstrand (uniform volume lower bound V_min)

### Diameter growth plan

To instantiate bacon's bounded uniform lemma, we need `d_max` covering all
intermediate sets in the iterative elimination.

Given initial `d_0 = 2*C` (from `μ.support ⊆ [-C,C]`), the diameter grows as:
`d_{k+1} ≤ N_bound(d_k) * d_k^2`
where `N_bound(d)` is the explicit N bound from the expansion lemma for a set
of diameter `d`.  After `n-1` steps, `d_max = d_{n-1}`.

The lower bound `diam(A) ≥ C^{-1/κ}` from Frostman ensures `N_bound(d)` is
bounded above uniformly for all `d ≥ C^{-1/κ}`.

TODO: plug in bacon's explicit `N_bound` formula once exposed.
-/

/-- Iterated diameter growth bound: `d_{k+1} = N_bound(d_k) * d_k^2`. -/
def diamGrowthIter (N_bound : ℝ → ℕ) (d : ℝ) : ℝ :=
  (N_bound d : ℝ) * d^2

/-- Compute `d_max` after `k` iterations starting from `d0`. -/
def diamGrowthBound (N_bound : ℝ → ℕ) (d0 : ℝ) (k : ℕ) : ℝ :=
  Nat.recOn k d0 fun _ prev => diamGrowthIter N_bound prev

/-- Quantitative volume recurrence from the paper:
`V_{i+1} = V_i^2 / (n - i)`.
At stage `i`, there are `n-i` remaining weights, and the diameter lower bound
is `V_i / (n-i)`, so the expansion lemma gives `V_{i+1} ≥ diam(A) * V_i ≥ V_i^2 / (n-i)`. -/
def volumeRecurrence (n : ℕ) (V0 : ℝ) : ℕ → ℝ
  | 0 => V0
  | k + 1 => (volumeRecurrence n V0 k)^2 / ((n - k : ℝ))

/-- The recurrence preserves positivity: if `V0 > 0` and `k < n`, then `volumeRecurrence n V0 k > 0`. -/
lemma volumeRecurrence_pos {n : ℕ} (hn : 2 ≤ n) {V0 : ℝ} (hV0 : 0 < V0) {k : ℕ} (hk : k < n) :
    0 < volumeRecurrence n V0 k := by
  induction k with
  | zero => exact hV0
  | succ k ih =>
    have h_k_lt_n : k < n := by omega
    have h_ih_pos : 0 < volumeRecurrence n V0 k := ih h_k_lt_n
    have h_n_minus_k_pos : 0 < (n : ℝ) - (k : ℝ) := by
      have h : (k : ℝ) < (n : ℝ) := by exact_mod_cast h_k_lt_n
      linarith
    dsimp only [volumeRecurrence]
    apply div_pos
    · exact sq_pos_of_pos h_ih_pos
    · exact h_n_minus_k_pos

/-- Uniform Expansion Theorem skeleton.

Given a uniform expansion lemma (fixed `N_max`), a quantitative Marstrand
result (uniform lower bound `V_min` on projection volume), and a uniform
iterative elimination theorem, produces a common `N` such that for **all**
Frostman measures μ, `N·K^(N) - N·K^(N)` has positive volume.

The hypotheses `h_expansion_uniform`, `h_marstrand_uniform`, and
`h_uniform_elim` are the three missing pieces to be filled in.
-/
theorem expansion_theorem_uniform
    {κ C : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hC_pos : 0 < C)
    {n : ℕ} (hn_pos : 0 < n) (hnκ : 1 < (n : ℝ) * κ)
    -- Uniform expansion lemma with fixed N_max
    (N_max : ℕ) (hN_max_pos : 0 < N_max)
    (h_expansion_uniform : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N_max)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B))
    -- Uniform iterative elimination with quantitative bound.
    -- Takes V_min explicitly to avoid metavariable issues.
    (h_uniform_elim : ∀ (V_min : ℝ), 0 < V_min →
      ∃ (N : ℕ) (V_final : ℝ), 0 < V_final ∧
        ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
          ∀ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
            ENNReal.ofReal V_min ≤ volume (ExpansionLemma.scaledSumset v A) →
            ENNReal.ofReal V_final ≤ volume (ExpansionLemma.iteratedDifference
              (ExpansionLemma.productSet A N) N))
    -- Quantitative Marstrand: uniform lower bound V_min
    (V_min : ℝ) (hV_min_pos : 0 < V_min)
    (h_marstrand_uniform : ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
      μ.support ⊆ Set.Icc (-C) C →
      ∃ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
        ENNReal.ofReal V_min ≤ volume (ExpansionLemma.scaledSumset v μ.support)) :
    ∃ (N : ℕ) (V_final : ℝ), 0 < V_final ∧
      ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
      μ.support ⊆ Set.Icc (-C) C →
        ENNReal.ofReal V_final ≤ volume (ExpansionLemma.iteratedDifference
          (ExpansionLemma.productSet μ.support N) N) := by
  rcases h_uniform_elim V_min hV_min_pos with ⟨N, V_final, hV_final_pos, hN⟩
  refine ⟨N, V_final, hV_final_pos, ?_⟩
  intro μ hμ hμ_supp
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hK_compact : IsCompact μ.support := by
    have h1 : IsCompact (Set.Icc (-C) C) := isCompact_Icc
    exact h1.of_isClosed_subset MeasureTheory.Measure.isClosed_support hμ_supp
  have hK_nonempty : μ.support.Nonempty := by
    by_contra h
    have h_empty : μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_zero : μ = 0 := by exact Measure.support_eq_empty_iff.mp h_empty
    rw [h_zero] at hμ_univ
    simp at hμ_univ
  have hK_diam_pos : 0 < diam μ.support := by
    by_contra h
    have h_le : diam μ.support ≤ 0 := by exact Std.not_lt.mp h
    have h0 : diam μ.support = 0 := le_antisymm h_le diam_nonneg
    rcases hK_nonempty with ⟨x, hx⟩
    have h_sub : μ.support ⊆ {x} := by
      intro y hy
      have h1 : dist y x ≤ diam μ.support := dist_le_diam_of_mem hK_compact.isBounded hy hx
      rw [h0] at h1
      have h2 : 0 ≤ dist y x := dist_nonneg
      have h3 : dist y x = 0 := le_antisymm h1 h2
      have h4 : y = x := by simpa [dist_eq_zero] using h3
      simpa using h4
    have h_singleton : μ.support = {x} := by
      apply Set.Subset.antisymm h_sub
      simpa using hx
    have h_frost := hμ.2.2.2
    let r : ℝ := (1 / (2 * C)) ^ (1 / κ)
    have hr_pos : 0 < r := by positivity
    have h_supp_sub : μ.support ⊆ Set.Icc (x - r) (x + r) := by
      rw [h_singleton]
      simp only [Set.singleton_subset_iff, Set.mem_Icc]
      constructor <;> linarith [hr_pos]
    have h_meas1 : μ (Set.Icc (x - r) (x + r)) = 1 := by
      have h_compl : (Set.Icc (x - r) (x + r))ᶜ ⊆ (μ.support)ᶜ := Set.compl_subset_compl.mpr h_supp_sub
      have h2 : μ ((Set.Icc (x - r) (x + r))ᶜ) = 0 :=
        measure_mono_null h_compl Measure.measure_compl_support
      have h3 : μ (Set.Icc (x - r) (x + r)) + μ ((Set.Icc (x - r) (x + r))ᶜ) = μ Set.univ := by
        rw [← measure_union (disjoint_compl_right) measurableSet_Icc.compl] <;> simp
      have h4 : μ (Set.Icc (x - r) (x + r)) = μ Set.univ := by
        rw [h2] at h3 <;> simpa using h3
      rw [h4, hμ_univ]
    have h4 := h_frost x r hr_pos
    rw [h_meas1] at h4
    have h_pos2 : 0 ≤ 1 / (2 * C) := by positivity
    have h6 : r ^ κ = 1 / (2 * C) := by
      have h7 : r = (1 / (2 * C)) ^ (1 / κ) := rfl
      calc r ^ κ
        = ((1 / (2 * C)) ^ (1 / κ)) ^ κ := by rw [h7]
      _ = (1 / (2 * C)) ^ ((1 / κ) * κ) := by exact Eq.symm (Real.rpow_mul h_pos2 (1 / κ) κ)
      _ = (1 / (2 * C)) ^ (1 : ℝ) := by
        have h9 : (1 / κ : ℝ) * κ = 1 := by field_simp [hκ_pos.ne'] <;> ring
        rw [h9]
      _ = 1 / (2 * C) := by simp
    have h5 : C * r ^ κ = 1 / 2 := by
      rw [h6]
      field_simp [hC_pos.ne'] <;> ring
    rw [h5] at h4 <;> norm_num at h4
  rcases h_marstrand_uniform μ hμ hμ_supp with ⟨v, hv, hvol_ge⟩
  exact hN μ.support hK_compact hK_nonempty hK_diam_pos v hv hvol_ge

/-- Expansion theorem with Marstrand bound supplied.

This wraps `expansion_theorem_uniform`, supplying `h_marstrand_uniform` from
`marstrand_uniform_lower_bound`. The uniform expansion lemma and iterative
elimination remain as parameters (to be supplied by the recursive schedule). -/
theorem expansion_theorem_with_marstrand
    {κ C : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hC_pos : 0 < C)
    {n : ℕ} (hn_pos : 0 < n) (hnκ : 1 < (n : ℝ) * κ)
    (N_max : ℕ) (hN_max_pos : 0 < N_max)
    (h_expansion_uniform : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N_max)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B))
    (h_uniform_elim : ∀ (V_min : ℝ), 0 < V_min →
      ∃ (N : ℕ) (V_final : ℝ), 0 < V_final ∧
        ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
          ∀ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
            ENNReal.ofReal V_min ≤ volume (ExpansionLemma.scaledSumset v A) →
            ENNReal.ofReal V_final ≤ volume (ExpansionLemma.iteratedDifference
              (ExpansionLemma.productSet A N) N)) :
    ∃ (N : ℕ) (V_final : ℝ), 0 < V_final ∧
      ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
        μ.support ⊆ Set.Icc (-C) C →
          ENNReal.ofReal V_final ≤ volume (ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet μ.support N) N) := by
  let B_val : ℝ := 1 + C ^ n / ((n : ℝ) * κ - 1)
  let V_min : ℝ := (ProductLikeIncidence.sphereProbabilityMeasure n
      (ProductLikeIncidence.ratioCapOpen n)).toReal /
    (ProductLikeIncidence.marstrandSphereConstant n * B_val) * Real.sqrt n / 2
  have hB_val_pos : 0 < B_val := by positivity
  have hV_min_pos : 0 < V_min := by
    dsimp only [V_min, B_val]
    have hα_pos : 0 < (ProductLikeIncidence.sphereProbabilityMeasure n
        (ProductLikeIncidence.ratioCapOpen n)).toReal := by
      have hU_pos : 0 < ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n) :=
        ProductLikeIncidence.ratioCapOpen_positiveMeasure hn_pos
      have h_ne : (ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n)) ≠ 0 := hU_pos.ne'
      letI : IsProbabilityMeasure (ProductLikeIncidence.sphereProbabilityMeasure n) :=
        ProductLikeIncidence.sphereProbabilityMeasure_isProbability (by linarith)
      have h_bdd : (ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n)) ≤ 1 := by
        have h3 : (ProductLikeIncidence.sphereProbabilityMeasure n
            (ProductLikeIncidence.ratioCapOpen n)) ≤
            (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) :=
          measure_mono (subset_univ (ProductLikeIncidence.ratioCapOpen n))
        have h4 : (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) = 1 := measure_univ
        rw [h4] at h3; exact h3
      have h_top : _ ≠ ⊤ := ne_top_of_le_ne_top (by simp) h_bdd
      exact ENNReal.toReal_pos h_ne h_top
    have hC_pos' : 0 < ProductLikeIncidence.marstrandSphereConstant n := by
      dsimp only [ProductLikeIncidence.marstrandSphereConstant]
      have h_d_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by linarith)
      exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
    have h_sqrt_pos : 0 < Real.sqrt (n : ℝ) := by positivity
    positivity
  let h_marstrand_uniform : ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
      μ.support ⊆ Set.Icc (-C) C →
      ∃ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
        ENNReal.ofReal V_min ≤ volume (ExpansionLemma.scaledSumset v μ.support) :=
    fun μ hμ hμ_supp =>
      marstrand_uniform_lower_bound hκ_pos hκ_lt_one hC_pos hn_pos hnκ μ hμ hμ_supp
  exact expansion_theorem_uniform hκ_pos hκ_lt_one hC_pos hn_pos hnκ
    N_max hN_max_pos h_expansion_uniform h_uniform_elim V_min hV_min_pos h_marstrand_uniform

-- NOTE: `expansion_theorem_almost_complete` was removed because its
-- `h_expansion_uniform` hypothesis was a false universal strengthening
-- (fixed N_max for all diameters and projection volumes). Use
-- `expansion_theorem_recursive` in ExpansionTheoremRecursive.lean instead,
-- which consumes the bounded factory interface.

end WeakTwoEndsSumProduct

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma 4: Lower bound on weighted sum S

This module proves the lower bound on `∑_{i≠j} S^{ij}` using a perfect
square identity and a diagonal bound.

The block structure is abstract: `G i l a b` represents
`∑_{|s|=l} orderFun(A_s^i, a, b)`.
-/

namespace MarcusTardos.WeightedLowerBound

open BigOperators Finset

variable {α : Type*} [DecidableEq α]

/-- Weighted sum S^{ij} in terms of abstract block sums `G`. -/
noncomputable def S (k : ℕ) (w : ℕ → ℝ) (alphabet : Finset α)
    (G : ℕ → ℕ → α → α → ℝ) (i j : ℕ) : ℝ :=
  ∑ l ∈ Icc 1 k, w l *
    ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, G i l a b * G j l a b

/-- Helper: commute triple sum i,j,l to l,i,j. -/
private lemma commute_ijl_to_lij {m k : ℕ} {f : ℕ → ℕ → ℕ → ℝ} :
    ∑ i ∈ range m, ∑ j ∈ range m, ∑ l ∈ Icc 1 k, f i j l =
    ∑ l ∈ Icc 1 k, ∑ i ∈ range m, ∑ j ∈ range m, f i j l := by
  have h1 : ∑ i ∈ range m, ∑ j ∈ range m, ∑ l ∈ Icc 1 k, f i j l =
      ∑ j ∈ range m, ∑ i ∈ range m, ∑ l ∈ Icc 1 k, f i j l := by
    rw [Finset.sum_comm]
  rw [h1]
  have h2 : ∑ j ∈ range m, ∑ i ∈ range m, ∑ l ∈ Icc 1 k, f i j l =
      ∑ j ∈ range m, ∑ l ∈ Icc 1 k, ∑ i ∈ range m, f i j l := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [h2]
  have h3 : ∑ j ∈ range m, ∑ l ∈ Icc 1 k, ∑ i ∈ range m, f i j l =
      ∑ l ∈ Icc 1 k, ∑ j ∈ range m, ∑ i ∈ range m, f i j l := by
    rw [Finset.sum_comm]
  rw [h3]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

/-- Helper: for fixed l, the double sum over i,j factors into a product. -/
private lemma inner_product_sum (m : ℕ) (w : ℕ → ℝ) (alphabet : Finset α)
    (G : ℕ → ℕ → α → α → ℝ) (l : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range m,
      (w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, G i l a b * G j l a b) =
    w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
      (∑ i ∈ range m, G i l a b) * (∑ j ∈ range m, G j l a b) := by
  let X (i j : ℕ) : ℝ := ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, G i l a b * G j l a b
  have h1 : ∑ i ∈ range m, ∑ j ∈ range m, (w l * X i j) =
      w l * ∑ i ∈ range m, ∑ j ∈ range m, X i j := by
    rw [Finset.mul_sum]
    <;> apply Finset.sum_congr rfl
    <;> intro i _
    <;> rw [Finset.mul_sum]
  rw [h1]
  have h2 : ∑ i ∈ range m, ∑ j ∈ range m, X i j =
      ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        ∑ i ∈ range m, ∑ j ∈ range m, (G i l a b * G j l a b) := by
    dsimp only [X]
    let g (i j : ℕ) (a b : α) : ℝ := G i l a b * G j l a b
    -- Step 1: commute j with (a,b)
    have h_s1 : ∑ i ∈ range m, ∑ j ∈ range m, ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, g i j a b =
        ∑ i ∈ range m, ∑ a ∈ alphabet, ∑ j ∈ range m, ∑ b ∈ alphabet.erase a, g i j a b := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    -- Step 2: commute i with a
    have h_s2 : ∑ i ∈ range m, ∑ a ∈ alphabet, ∑ j ∈ range m, ∑ b ∈ alphabet.erase a, g i j a b =
        ∑ a ∈ alphabet, ∑ i ∈ range m, ∑ j ∈ range m, ∑ b ∈ alphabet.erase a, g i j a b := by
      rw [Finset.sum_comm]
    -- Step 3: commute j with b
    have h_s3 : ∑ a ∈ alphabet, ∑ i ∈ range m, ∑ j ∈ range m, ∑ b ∈ alphabet.erase a, g i j a b =
        ∑ a ∈ alphabet, ∑ i ∈ range m, ∑ b ∈ alphabet.erase a, ∑ j ∈ range m, g i j a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    -- Step 4: commute i with b
    have h_s4 : ∑ a ∈ alphabet, ∑ i ∈ range m, ∑ b ∈ alphabet.erase a, ∑ j ∈ range m, g i j a b =
        ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, ∑ i ∈ range m, ∑ j ∈ range m, g i j a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    rw [h_s1, h_s2, h_s3, h_s4]
  rw [h2]
  have h3 : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        ∑ i ∈ range m, ∑ j ∈ range m, (G i l a b * G j l a b) =
      ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (∑ i ∈ range m, G i l a b) * (∑ j ∈ range m, G j l a b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul_sum]
  rw [h3]
  <;> ring

/-- Perfect square identity: `∑_{i,j} S^{ij} ≥ 0`. -/
lemma total_sum_nonneg (m k : ℕ) (w : ℕ → ℝ) (alphabet : Finset α)
    (G : ℕ → ℕ → α → α → ℝ)
    (hw_nonneg : ∀ l ∈ Icc 1 k, 0 ≤ w l) :
    ∑ i ∈ range m, ∑ j ∈ range m, S k w alphabet G i j ≥ 0 := by
  let f (i j l : ℕ) : ℝ :=
    w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, G i l a b * G j l a b
  have hS : ∀ i j, S k w alphabet G i j = ∑ l ∈ Icc 1 k, f i j l := by
    intro i j
    rfl
  have h_expand : ∑ i ∈ range m, ∑ j ∈ range m, S k w alphabet G i j =
      ∑ i ∈ range m, ∑ j ∈ range m, ∑ l ∈ Icc 1 k, f i j l := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hS i j
  rw [h_expand]
  rw [commute_ijl_to_lij (f := f)]
  have h_main : ∑ l ∈ Icc 1 k, ∑ i ∈ range m, ∑ j ∈ range m, f i j l =
      ∑ l ∈ Icc 1 k, w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (∑ i ∈ range m, G i l a b)^2 := by
    apply Finset.sum_congr rfl
    intro l hl
    dsimp only [f]
    have h_inner := inner_product_sum m w alphabet G l
    rw [h_inner]
    have h_sq : w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
          (∑ i ∈ range m, G i l a b) * (∑ j ∈ range m, G j l a b) =
        w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (∑ i ∈ range m, G i l a b)^2 := by
      apply congr_arg (fun x => w l * x)
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    exact h_sq
  rw [h_main]
  apply sum_nonneg
  intro l hl
  have h₂ : 0 ≤ w l := hw_nonneg l hl
  have h₃ : 0 ≤ ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (∑ i ∈ range m, G i l a b)^2 := by
    apply sum_nonneg
    intro a _
    apply sum_nonneg
    intro b _
    exact sq_nonneg _
  exact mul_nonneg h₂ h₃

/-- Diagonal bound. -/
lemma diagonal_bound (m k d : ℕ) (w : ℕ → ℝ) (alphabet : Finset α)
    (G : ℕ → ℕ → α → α → ℝ)
    (hw_nonneg : ∀ l ∈ Icc 1 k, 0 ≤ w l)
    (i : ℕ)
    (hG_bound : ∀ l ∈ Icc 1 k,
      ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G i l a b)^2 ≤ (d : ℝ)^2 / (2 : ℝ)^l) :
    S k w alphabet G i i ≤ ∑ l ∈ Icc 1 k, w l * (d : ℝ)^2 / (2 : ℝ)^l := by
  have h₁ : S k w alphabet G i i =
      ∑ l ∈ Icc 1 k, w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G i l a b)^2 := by
    simp only [S]
    apply Finset.sum_congr rfl
    intro l _
    apply congr_arg (fun x => w l * x)
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [h₁]
  have h₂ : ∑ l ∈ Icc 1 k, w l * ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G i l a b)^2 ≤
      ∑ l ∈ Icc 1 k, w l * ((d : ℝ)^2 / (2 : ℝ)^l) := by
    apply sum_le_sum
    intro l hl
    have h₃ : 0 ≤ w l := hw_nonneg l hl
    have h₄ := hG_bound l hl
    exact mul_le_mul_of_nonneg_left h₄ h₃
  have h₅ : ∑ l ∈ Icc 1 k, w l * ((d : ℝ)^2 / (2 : ℝ)^l) =
      ∑ l ∈ Icc 1 k, w l * (d : ℝ)^2 / (2 : ℝ)^l := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h₅] at h₂
  exact h₂

/-- Main lower bound (Lemma 4). -/
lemma weighted_lower_bound (m k d : ℕ) (w : ℕ → ℝ) (alphabet : Finset α)
    (G : ℕ → ℕ → α → α → ℝ)
    (hw_nonneg : ∀ l ∈ Icc 1 k, 0 ≤ w l)
    (hG_bound : ∀ i ∈ range m, ∀ l ∈ Icc 1 k,
      ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G i l a b)^2 ≤ (d : ℝ)^2 / (2 : ℝ)^l) :
    ∑ i ∈ range m, ∑ j ∈ (range m).erase i, S k w alphabet G i j ≥
      - (m : ℝ) * (d : ℝ)^2 * ∑ l ∈ Icc 1 k, w l / (2 : ℝ)^l := by
  have h_total : ∑ i ∈ range m, ∑ j ∈ range m, S k w alphabet G i j ≥ 0 :=
    total_sum_nonneg m k w alphabet G hw_nonneg
  have h_diag : ∀ i ∈ range m, S k w alphabet G i i ≤
      ∑ l ∈ Icc 1 k, w l * (d : ℝ)^2 / (2 : ℝ)^l := by
    intro i hi
    exact diagonal_bound m k d w alphabet G hw_nonneg i (fun l hl => hG_bound i hi l hl)
  have h_sum_diag : ∑ i ∈ range m, S k w alphabet G i i ≤
      (m : ℝ) * ∑ l ∈ Icc 1 k, w l * (d : ℝ)^2 / (2 : ℝ)^l := by
    calc
      ∑ i ∈ range m, S k w alphabet G i i
        ≤ ∑ i ∈ range m, (∑ l ∈ Icc 1 k, w l * (d : ℝ)^2 / (2 : ℝ)^l) := by
          apply sum_le_sum
          intro i hi
          exact h_diag i hi
      _ = (m : ℝ) * ∑ l ∈ Icc 1 k, w l * (d : ℝ)^2 / (2 : ℝ)^l := by
        simp [sum_const]
        <;> ring
  have h_erase : ∀ i ∈ range m, ∑ j ∈ (range m).erase i, S k w alphabet G i j =
      (∑ j ∈ range m, S k w alphabet G i j) - S k w alphabet G i i := by
    intro i hi
    have h₂ : (range m).erase i = (range m) \ {i} := by
      ext x
      simp [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
      <;> tauto
    rw [h₂]
    have h₄ : ∑ j ∈ (range m) \ {i}, S k w alphabet G i j + ∑ j ∈ ({i} : Finset ℕ), S k w alphabet G i j =
        ∑ j ∈ range m, S k w alphabet G i j := by
      rw [← Finset.sum_sdiff (show ({i} : Finset ℕ) ⊆ range m from by simp [hi])]
      <;> ring
    have h₃ : ∑ j ∈ (range m) \ {i}, S k w alphabet G i j =
        (∑ j ∈ range m, S k w alphabet G i j) - ∑ j ∈ ({i} : Finset ℕ), S k w alphabet G i j := by
      linarith
    rw [h₃]
    simp
    <;> ring
  have h_main : ∑ i ∈ range m, ∑ j ∈ (range m).erase i, S k w alphabet G i j =
      (∑ i ∈ range m, ∑ j ∈ range m, S k w alphabet G i j) -
      ∑ i ∈ range m, S k w alphabet G i i := by
    calc
      ∑ i ∈ range m, ∑ j ∈ (range m).erase i, S k w alphabet G i j
        = ∑ i ∈ range m, ((∑ j ∈ range m, S k w alphabet G i j) - S k w alphabet G i i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact h_erase i hi
      _ = (∑ i ∈ range m, ∑ j ∈ range m, S k w alphabet G i j) -
            ∑ i ∈ range m, S k w alphabet G i i := by
          rw [Finset.sum_sub_distrib]
  rw [h_main]
  have h₄ : ∑ i ∈ range m, S k w alphabet G i i ≤
      (m : ℝ) * (d : ℝ)^2 * ∑ l ∈ Icc 1 k, w l / (2 : ℝ)^l := by
    have h₅ : ∑ l ∈ Icc 1 k, w l * (d : ℝ)^2 / (2 : ℝ)^l =
        (d : ℝ)^2 * ∑ l ∈ Icc 1 k, w l / (2 : ℝ)^l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [h₅] at h_sum_diag
    have h₆ : (m : ℝ) * ((d : ℝ)^2 * ∑ l ∈ Icc 1 k, w l / (2 : ℝ)^l) =
        (m : ℝ) * (d : ℝ)^2 * ∑ l ∈ Icc 1 k, w l / (2 : ℝ)^l := by ring
    rw [h₆] at h_sum_diag
    exact h_sum_diag
  linarith

end MarcusTardos.WeightedLowerBound

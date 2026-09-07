module

/-
# Energy and Cauchy-Schwarz Helpers

Generic helper lemmas for the incidence energy lower bound in the key lemma.

## Main results

- `cauchy_schwarz_nat`: (Σ a_i)² ≤ |s| · Σ a_i² for natural numbers
- `double_counting`: Σ_i |{j ∈ t | R i j}| = Σ_j |{i ∈ s | R i j}|
- `cauchy_schwarz_ennreal_of_nat`: ENNReal Cauchy-Schwarz from nat-valued function
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open Finset ENNReal

namespace ProductLikeIncidence.ProductReduction

attribute [local instance] Classical.propDecidable

/-- Cauchy-Schwarz for natural numbers: (Σ a_i)² ≤ |s| · Σ a_i². -/
lemma cauchy_schwarz_nat {α : Type*} {s : Finset α} {f : α → ℕ} :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  let g : α → ℝ := fun i => (f i : ℝ)
  have h_sum1 : (∑ i ∈ s, g i * (1 : ℝ)) = ∑ i ∈ s, g i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_sum2 : (∑ i ∈ s, (1 : ℝ) ^ 2) = (s.card : ℝ) := by
    simp
  have h_cs : (∑ i ∈ s, g i) ^ 2 ≤ (∑ i ∈ s, (g i) ^ 2) * (s.card : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s g (fun _ => (1 : ℝ))
    rw [h_sum1, h_sum2] at h
    exact h
  have h_cs' : (∑ i ∈ s, g i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (g i) ^ 2 := by
    rw [mul_comm] at h_cs
    exact h_cs
  have h_g_sum : (∑ i ∈ s, g i) = ↑(∑ i ∈ s, f i) := by
    simp [g, Finset.sum_apply]
    <;> norm_cast
  have h_g_sum2 : (∑ i ∈ s, (g i) ^ 2) = ↑(∑ i ∈ s, (f i) ^ 2) := by
    simp [g, Finset.sum_apply]
    <;> norm_cast
  rw [h_g_sum, h_g_sum2] at h_cs'
  exact_mod_cast h_cs'

/-- Double counting identity: sum of fiber cardinalities equals sum of
cofiber cardinalities for a relation R between two finite sets. -/
lemma double_counting {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (R : α → β → Prop) [∀ i j, Decidable (R i j)] :
    ∑ i ∈ s, (t.filter (fun j => R i j)).card =
    ∑ j ∈ t, (s.filter (fun i => R i j)).card := by
  let f : α → β → ℕ := fun i j => if R i j then 1 else 0
  have h1 : ∀ i ∈ s, (t.filter (fun j => R i j)).card = ∑ j ∈ t, f i j := by
    intro i _
    rw [Finset.card_filter]
    <;> rfl
  have h2 : ∀ j ∈ t, (s.filter (fun i => R i j)).card = ∑ i ∈ s, f i j := by
    intro j _
    rw [Finset.card_filter]
    <;> rfl
  calc
    ∑ i ∈ s, (t.filter (fun j => R i j)).card
      = ∑ i ∈ s, ∑ j ∈ t, f i j := by
        apply Finset.sum_congr rfl; intro i hi; exact h1 i hi
    _ = ∑ j ∈ t, ∑ i ∈ s, f i j := by rw [Finset.sum_comm]
    _ = ∑ j ∈ t, (s.filter (fun i => R i j)).card := by
        apply Finset.sum_congr rfl; intro j hj; exact (h2 j hj).symm

/-- Cauchy-Schwarz for ENNReal values coming from natural numbers:
(Σ (f i : ENNReal))² ≤ |s| · Σ (f i : ENNReal)². -/
lemma cauchy_schwarz_ennreal_of_nat {α : Type*} {s : Finset α} {f : α → ℕ} :
    (∑ i ∈ s, (f i : ENNReal)) ^ 2 ≤
    (s.card : ENNReal) * ∑ i ∈ s, ((f i : ENNReal) ^ 2) := by
  have h4 : (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 :=
    cauchy_schwarz_nat (s := s) (f := f)
  have h5 : (( (∑ i ∈ s, f i) ^ 2 : ℕ) : ENNReal) ≤
      ((s.card * ∑ i ∈ s, (f i) ^ 2 : ℕ) : ENNReal) := by
    exact_mod_cast h4
  have h6 : (( (∑ i ∈ s, f i) ^ 2 : ℕ) : ENNReal) =
      (∑ i ∈ s, (f i : ENNReal)) ^ 2 := by
    simp [Nat.cast_sum, Nat.cast_pow]
    <;> rfl
  have h7 : ((s.card * ∑ i ∈ s, (f i) ^ 2 : ℕ) : ENNReal) =
      (s.card : ENNReal) * ∑ i ∈ s, ((f i : ENNReal) ^ 2) := by
    simp [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul]
    <;> rfl
  rw [h6, h7] at h5
  exact h5

end ProductLikeIncidence.ProductReduction

module

public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Uniform SSet subset and dyadic pigeonhole corollary (Bacon)

Two lemmas needed for constructing coarse tube families:
1. `sset_uniform_subset`: subset with uniform size ratio gets SSet constant K*C
2. `dyadic_pigeonhole_uniform`: select subfamily with sizes in a dyadic interval
-/

open scoped BigOperators

noncomputable section

namespace InductionOnScales

/-- A subset `TQ ⊆ TΔ` with `|TΔ| ≤ K * |TQ|` is SSet with constant `K * C`.

Combines `subset_scaled` (constant scales by |TΔ|/|TQ|) with
`monotone_const` (since |TΔ|/|TQ| ≤ K). -/
lemma sset_uniform_subset {n : ℕ} {s C K : ℝ}
    {TΔ TQ : Finset (DyadicTube n)}
    (hTQ : TQ ⊆ TΔ)
    (hSSet : IsFiniteTubeSSet s C TΔ)
    (h_size : (TΔ.card : ℝ) ≤ K * (TQ.card : ℝ))
    (hK : 1 ≤ K) :
    IsFiniteTubeSSet s (K * C) TQ := by
  by_cases h_empty : TQ = ∅
  · have hTΔ_empty : TΔ = ∅ := by
      have h1 : TΔ.card = 0 := by
        rw [h_empty] at h_size
        simp at h_size ⊢ <;> omega
      exact Finset.card_eq_zero.mp h1
    rcases hSSet with ⟨h_nonempty, _, _, _, _⟩
    rw [hTΔ_empty] at h_nonempty
    simp at h_nonempty
  · have hQne : TQ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; exact h_empty
    have hQpos : (TQ.card : ℝ) > 0 := by exact_mod_cast hQne.card_pos
    have hC_one : 1 ≤ C := hSSet.2.1
    have h_factor1 : (TΔ.card : ℝ) / (TQ.card : ℝ) ≤ K := by
      have h1 : (TΔ.card : ℝ) ≤ K * (TQ.card : ℝ) := h_size
      have h2 : (TΔ.card : ℝ) / (TQ.card : ℝ) ≤ (K * (TQ.card : ℝ)) / (TQ.card : ℝ) :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have h3 : (K * (TQ.card : ℝ)) / (TQ.card : ℝ) = K := by
        field_simp [hQpos.ne'] <;> ring
      rw [h3] at h2
      exact h2
    have h_factor2 : C * (TΔ.card : ℝ) / (TQ.card : ℝ) ≤ K * C := by
      have h4 : C * (TΔ.card : ℝ) / (TQ.card : ℝ) = C * ((TΔ.card : ℝ) / (TQ.card : ℝ)) := by
        field_simp [hQpos.ne'] <;> ring
      rw [h4]
      have h5 : C ≥ 0 := by linarith
      nlinarith
    have h_scaled := IsFiniteTubeSSet.subset_scaled hQne hTQ hSSet
    exact IsFiniteTubeSSet.monotone_const h_factor2 h_scaled

/-- Alias for `sset_uniform_subset`: if F is SSet(C) and G ⊆ F with
|F| ≤ K·|G|, then G is SSet(K·C). -/
lemma sset_monotone_card {n : ℕ} {s C K : ℝ}
    {F G : Finset (DyadicTube n)}
    (hG : G ⊆ F)
    (hSSet : IsFiniteTubeSSet s C F)
    (h_size : (F.card : ℝ) ≤ K * (G.card : ℝ))
    (hK : 1 ≤ K) :
    IsFiniteTubeSSet s (K * C) G :=
  sset_uniform_subset hG hSSet h_size hK

/-- Dyadic pigeonhole: given a function `f : α → ℕ` bounded by `N` and positive
on `s`, there exists a level `j` and a subset `s' ⊆ s` such that
`2^j ≤ f i < 2^(j+1)` for all `i ∈ s'`, and
`|s'| ≥ |s| / (Nat.log 2 N + 2)`.

Uses `uniformize_positive_by_dyadic_level` and shifts the level index by 1. -/
theorem dyadic_pigeonhole_uniform {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ i ∈ s, f i ≤ N) (h_pos : ∀ i ∈ s, 0 < f i) :
    ∃ (j : ℕ) (s' : Finset α), s' ⊆ s ∧
      (∀ i ∈ s', 2 ^ j ≤ f i ∧ f i < 2 ^ (j + 1)) ∧
      s'.card ≥ s.card / (Nat.log 2 N + 2) := by
  rcases uniformize_positive_by_dyadic_level s f hN h_bound h_pos with
    ⟨s', j0, h_sub, hj1, hj_le, h_range, h_card⟩
  -- j0 ≥ 1, and 2^(j0-1) ≤ f i < 2^j0
  -- Set j = j0 - 1, then 2^j ≤ f i < 2^(j+1)
  let j := j0 - 1
  have h_j0_pos : 1 ≤ j0 := hj1
  have h_j0_eq : j0 = j + 1 := by
    omega
  refine ⟨j, s', h_sub, ?_, h_card⟩
  intro i hi
  have h1 : 2 ^ (j0 - 1) ≤ f i := (h_range i hi).1
  have h2 : f i < 2 ^ j0 := (h_range i hi).2
  have h3 : 2 ^ (j0 - 1) = 2 ^ j := by
    have h4 : j0 - 1 = j := by omega
    rw [h4]
  have h5 : 2 ^ j0 = 2 ^ (j + 1) := by
    have h6 : j0 = j + 1 := by omega
    rw [h6] <;> ring
  rw [h3] at h1
  rw [h5] at h2
  exact ⟨h1, h2⟩

end InductionOnScales

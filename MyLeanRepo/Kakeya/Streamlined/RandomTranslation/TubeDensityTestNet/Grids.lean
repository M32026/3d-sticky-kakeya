import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PositionGrid
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Dimension and center grids for the tube density test net

## Dimension grid

`dimGrid δ` is the dyadic sequence `δ, 2δ, 4δ, ..., 2^k*δ` where `2^k*δ ≥ 40`.
Cardinality is `O(log(1/δ))`.

## Center grid

`centerGrid δ` is a finite set of points covering `closedBall 0 20` with
spacing `δ/10`, obtained from `position_grid`. Cardinality is `O(δ^{-3})`.
-/

noncomputable section

open Metric Finset
open Kakeya.Streamlined.GeometricLemmas

namespace Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet

/-! ### Dimension grid -/

/-- Smallest natural `k` such that `2^k * δ ≥ 40`. -/
def dimGridK (δ : ℝ) (hδ : 0 < δ) : ℕ :=
  Nat.ceil (Real.log (250 / δ) / Real.log 2)

lemma dimGridK_spec (δ : ℝ) (hδ : 0 < δ) :
    (2 : ℝ) ^ (dimGridK δ hδ) * δ ≥ 250 := by
  set k : ℕ := dimGridK δ hδ with hk
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (k : ℝ) ≥ Real.log (250 / δ) / Real.log 2 := Nat.le_ceil _
  have h2 : (k : ℝ) * Real.log 2 ≥ Real.log (250 / δ) := by
    calc (k : ℝ) * Real.log 2
      ≥ (Real.log (250 / δ) / Real.log 2) * Real.log 2 := by gcongr
      _ = Real.log (250 / δ) := by
        field_simp [hlog2_pos.ne'] <;> ring
  have h3 : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have h4 : Real.log ((2 : ℝ) ^ k) ≥ Real.log (250 / δ) := by linarith
  have hpos1 : 0 < (2 : ℝ) ^ k := by positivity
  have hpos2 : 0 < (250 / δ) := by positivity
  have h5 : (250 / δ) ≤ (2 : ℝ) ^ k :=
    (Real.log_le_log_iff hpos2 hpos1).mp h4
  calc (2 : ℝ) ^ k * δ
    ≥ (250 / δ) * δ := by gcongr
    _ = 250 := by field_simp [hδ.ne'] <;> ring

/-- Dyadic dimension grid: `δ, 2δ, 4δ, ..., 2^k*δ` where `2^k*δ ≥ 40`. -/
def dimGrid (δ : ℝ) (hδ : 0 < δ) : Finset ℝ :=
  Finset.image (fun n : ℕ => (2 : ℝ) ^ n * δ) (Finset.range (dimGridK δ hδ + 1))

lemma dimGrid_contains_delta (δ : ℝ) (hδ : 0 < δ) :
    δ ∈ dimGrid δ hδ := by
  have h : (0 : ℕ) ∈ Finset.range (dimGridK δ hδ + 1) := by simp
  exact Finset.mem_image.mpr ⟨0, h, by ring⟩

lemma dimGrid_contains_large (δ : ℝ) (hδ : 0 < δ) :
    ∃ x ∈ dimGrid δ hδ, x ≥ 250 := by
  let k := dimGridK δ hδ
  have hk_in : k ∈ Finset.range (k + 1) := by simp
  refine ⟨(2 : ℝ) ^ k * δ, Finset.mem_image.mpr ⟨k, hk_in, rfl⟩, dimGridK_spec δ hδ⟩

/-- Round any `x ∈ [δ, 250]` up to next dyadic grid value, with factor ≤ 2. -/
lemma dimGrid_round_up (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (hx1 : δ ≤ x) (hx2 : x ≤ 250) :
    ∃ (x' : ℝ), x' ∈ dimGrid δ hδ ∧ x ≤ x' ∧ x' ≤ 2 * x := by
  have h_exists : ∃ (n : ℕ), (2:ℝ)^n * δ ≥ x := by
    refine ⟨dimGridK δ hδ, ?_⟩
    have h : (2:ℝ)^(dimGridK δ hδ) * δ ≥ 250 := dimGridK_spec δ hδ
    linarith
  let k : ℕ := Nat.find h_exists
  have hk1 : (2:ℝ)^k * δ ≥ x := Nat.find_spec h_exists
  have hk2 : k ≤ dimGridK δ hδ := by
    by_contra h
    have h' : k > dimGridK δ hδ := by omega
    have h'' : (2:ℝ)^(dimGridK δ hδ) * δ ≥ x := by
      have h : (2:ℝ)^(dimGridK δ hδ) * δ ≥ 250 := dimGridK_spec δ hδ
      linarith
    have h_not : ¬((2:ℝ)^(dimGridK δ hδ) * δ ≥ x) :=
      Nat.find_min h_exists (show dimGridK δ hδ < k from by omega)
    exact h_not h''
  have hk3 : (2:ℝ)^k * δ ≤ 2 * x := by
    by_cases hk0 : k = 0
    · rw [hk0]; norm_num at * <;> linarith
    · have h_pos : 0 < k := by omega
      have h_prev : (2:ℝ)^(k - 1) * δ < x := by
        have h := Nat.find_min h_exists (show k - 1 < k from by omega)
        exact lt_of_not_ge h
      have h4 : (2:ℝ)^k * δ = 2 * ((2:ℝ)^(k - 1) * δ) := by
        have h5 : k = (k - 1) + 1 := by omega
        rw [h5]
        simp [pow_succ] <;> ring
      rw [h4]; linarith
  refine ⟨(2:ℝ)^k * δ, ?_, hk1, hk3⟩
  have h5 : k ∈ Finset.range (dimGridK δ hδ + 1) := by
    simp only [Finset.mem_range] <;> omega
  exact Finset.mem_image.mpr ⟨k, h5, rfl⟩

/-- Round `x ∈ [δ,250]` up to the minimal dyadic grid value, with factor ≤ 2. -/
lemma dimGrid_round_up_min (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (hx1 : δ ≤ x) (hx2 : x ≤ 250) :
    ∃ (x' : ℝ), x' ∈ dimGrid δ hδ ∧ x ≤ x' ∧ x' ≤ 2 * x ∧
      ∀ (n : ℕ), (2:ℝ)^n * δ ≥ x → x' ≤ (2:ℝ)^n * δ := by
  have h_exists : ∃ (n : ℕ), (2:ℝ)^n * δ ≥ x := by
    refine ⟨dimGridK δ hδ, ?_⟩
    have h : (2:ℝ)^(dimGridK δ hδ) * δ ≥ 250 := dimGridK_spec δ hδ
    linarith
  let k : ℕ := Nat.find h_exists
  have hk1 : (2:ℝ)^k * δ ≥ x := Nat.find_spec h_exists
  have hk2 : k ≤ dimGridK δ hδ := by
    by_contra h
    have h' : k > dimGridK δ hδ := by omega
    have h'' : (2:ℝ)^(dimGridK δ hδ) * δ ≥ x := by
      have h : (2:ℝ)^(dimGridK δ hδ) * δ ≥ 250 := dimGridK_spec δ hδ
      linarith
    have h_not : ¬((2:ℝ)^(dimGridK δ hδ) * δ ≥ x) :=
      Nat.find_min h_exists (show dimGridK δ hδ < k from by omega)
    exact h_not h''
  have hk3 : (2:ℝ)^k * δ ≤ 2 * x := by
    by_cases hk0 : k = 0
    · rw [hk0]
      have h_xpos : 0 < x := by linarith [hδ, hx1]
      linarith
    · have h_pos : 0 < k := by omega
      have h_prev : (2:ℝ)^(k - 1) * δ < x := by
        have h := Nat.find_min h_exists (show k - 1 < k from by omega)
        exact lt_of_not_ge h
      have h4 : (2:ℝ)^k * δ = 2 * ((2:ℝ)^(k - 1) * δ) := by
        have h5 : k = (k - 1) + 1 := by omega
        rw [h5]; simp [pow_succ] <;> ring
      rw [h4]; linarith
  have hk4 : ∀ (n : ℕ), (2:ℝ)^n * δ ≥ x → (2:ℝ)^k * δ ≤ (2:ℝ)^n * δ := by
    intro n hn
    have h_ineq : k ≤ n := by
      by_contra h
      have h' : n < k := by omega
      exact Nat.find_min h_exists h' hn
    have h_pow : (2:ℝ)^k ≤ (2:ℝ)^n :=
      pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) h_ineq
    exact mul_le_mul_of_nonneg_right h_pow (by linarith [hδ])
  have h5 : k ∈ Finset.range (dimGridK δ hδ + 1) := by
    simp only [Finset.mem_range] <;> omega
  exact ⟨(2:ℝ)^k * δ, Finset.mem_image.mpr ⟨k, h5, rfl⟩, hk1, hk3, hk4⟩

lemma dimGrid_all_pos (δ : ℝ) (hδ : 0 < δ) :
    ∀ x ∈ dimGrid δ hδ, 0 < x := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨n, _, rfl⟩
  positivity

lemma dimGrid_card_le (δ : ℝ) (hδ : 0 < δ) :
    (dimGrid δ hδ).card ≤ dimGridK δ hδ + 1 := by
  have h : (dimGrid δ hδ).card ≤ (Finset.range (dimGridK δ hδ + 1)).card :=
    Finset.card_image_le
  simpa using h

/-! ### Ordered dimension triples -/

/-- All ordered triples `(a,b,c)` from `dimGrid` with `a ≤ b ≤ c`. -/
def dimTriples (δ : ℝ) (hδ : 0 < δ) : Finset (ℝ × ℝ × ℝ) :=
  let G := dimGrid δ hδ
  (G ×ˢ G ×ˢ G).filter (fun p : ℝ × ℝ × ℝ => p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2)

lemma dimTriples_all_pos (δ : ℝ) (hδ : 0 < δ) :
    ∀ p ∈ dimTriples δ hδ, 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by
  intro p hp
  have h1 : p ∈ (dimGrid δ hδ ×ˢ dimGrid δ hδ ×ˢ dimGrid δ hδ) :=
    (Finset.mem_filter.mp hp).1
  have h2 : p.1 ∈ dimGrid δ hδ := by
    simp [Finset.mem_product] at h1 <;> tauto
  have h3 : p.2.1 ∈ dimGrid δ hδ := by
    simp [Finset.mem_product] at h1 <;> tauto
  have h4 : p.2.2 ∈ dimGrid δ hδ := by
    simp [Finset.mem_product] at h1 <;> tauto
  exact ⟨dimGrid_all_pos δ hδ p.1 h2,
    dimGrid_all_pos δ hδ p.2.1 h3,
    dimGrid_all_pos δ hδ p.2.2 h4⟩

lemma dimTriples_ordered (δ : ℝ) (hδ : 0 < δ) :
    ∀ p ∈ dimTriples δ hδ, p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-! ### Center grid -/

/-- Finite set of centers covering `closedBall 0 20` with spacing `δ/10`. -/
def centerGrid (δ : ℝ) (hδ : 0 < δ) : Finset Point3 :=
  Classical.choose (position_grid (δ / 10) (by positivity) (25 : ℝ) (by norm_num))

lemma centerGrid_cover (δ : ℝ) (hδ : 0 < δ) :
    ∀ (m : Point3), ‖m‖ ≤ 20 →
      ∃ p ∈ centerGrid δ hδ, ‖m - p‖ ≤ Real.sqrt 3 / 2 * (δ / 10) := by
  have h_main := (Classical.choose_spec
    (position_grid (δ / 10) (by positivity) (25 : ℝ) (by norm_num))).1
  intro m hm
  have h25 : ‖m‖ ≤ 25 := by linarith
  exact h_main m h25

lemma centerGrid_separation (δ : ℝ) (hδ : 0 < δ) :
    ∀ p1 ∈ centerGrid δ hδ, ∀ p2 ∈ centerGrid δ hδ,
      p1 ≠ p2 → ‖p1 - p2‖ ≥ δ / 10 :=
  (Classical.choose_spec (position_grid (δ / 10) (by positivity) (25 : ℝ) (by norm_num))).2.1

lemma centerGrid_card (δ : ℝ) (hδ : 0 < δ) :
    ((centerGrid δ hδ).card : ℝ) ≤ 64 * (25 + δ / 10)^3 / (δ / 10)^3 :=
  (Classical.choose_spec (position_grid (δ / 10) (by positivity) (25 : ℝ) (by norm_num))).2.2

end Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet

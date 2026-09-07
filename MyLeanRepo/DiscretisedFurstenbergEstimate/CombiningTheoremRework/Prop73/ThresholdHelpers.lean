module

/-
  ThresholdHelpers.lean

  Reusable threshold-construction lemmas for CombiningInductionWithBound.
  Encapsulates the standard "exponential dominates polynomial" argument using
  `isLittleO_rpow_exp_pos_mul_atTop`, natural-threshold extraction from real
  `atTop` eventualities, and the dyadicDelta exponential identity.

  Main results:
  - `exp_dominates_poly_threshold`: ∃ K : ℕ, ∀ k ≥ K, C * k^s < exp(b*k)
  - `exp_absorbs_poly_threshold`: ∃ K : ℕ, ∀ k ≥ K, k^s * exp(-b*k) < 1/C
  - `nat_threshold_from_real`: convert real atTop property to ℕ threshold
  - `exp_log2_to_dyadicDelta`: exp(c * log 2 * k) = (2^(-k))^(-c)
  - `pos_min4`, `pos_min3`: positivity of nested mins
  - `exists_nat_ge_one`: natural threshold ≥ X and ≥ 1
  - `exp_dominates_poly_threshold_with_lower_bound`: combined threshold with lower bound
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

/-- Absorption helper: from `p * exp(-b*k) < 1/C` derive `C*p < exp(b*k)`. -/
lemma exp_absorb_helper' {p b C : ℝ} (k : ℝ) (hp : 0 < p) (hb : 0 < b) (hC : 0 < C)
    (h : p * Real.exp (-b * k) < 1 / C) :
    C * p < Real.exp (b * k) := by
  have h1 : 0 < Real.exp (b * k) := Real.exp_pos (b * k)
  have h2 : Real.exp (-b * k) * Real.exp (b * k) = 1 := by
    rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  have h3 : C * (p * Real.exp (-b * k)) < 1 := by
    calc C * (p * Real.exp (-b * k))
      < C * (1 / C) := by gcongr
    _ = 1 := by field_simp [hC.ne'] <;> ring
  calc C * p
    = C * p * (Real.exp (-b * k) * Real.exp (b * k)) := by rw [h2] <;> ring
  _ = (C * (p * Real.exp (-b * k))) * Real.exp (b * k) := by ring
  _ < 1 * Real.exp (b * k) := by gcongr
  _ = Real.exp (b * k) := by ring

/-- Given polynomial exponent `s`, exponential rate `b > 0`, and constant `C > 0`,
there exists a natural threshold `K ≥ 1` such that for all `k ≥ K`:
  `C * k^s < Real.exp (b * k)`.
This is the standard "exponential dominates polynomial" threshold, derived from
`isLittleO_rpow_exp_pos_mul_atTop`. -/
lemma exp_dominates_poly_threshold (s b C : ℝ) (hb : 0 < b) (hC : 0 < C) :
    ∃ (K : ℕ), K ≥ 1 ∧ ∀ (k : ℕ), k ≥ K →
      C * (k : ℝ)^s < Real.exp (b * (k : ℝ)) := by
  have h_olo : Asymptotics.IsLittleO Filter.atTop
        (fun x : ℝ => x^s) (fun x : ℝ => Real.exp (b * x)) :=
    isLittleO_rpow_exp_pos_mul_atTop s (b := b) hb
  have h_tendsto : Filter.Tendsto
        (fun x : ℝ => x^s / Real.exp (b * x)) Filter.atTop (nhds 0) :=
    h_olo.tendsto_div_nhds_zero
  have h_pos_inv : 0 < 1 / C := by positivity
  have h_Iio : Set.Iio (1 / C) ∈ nhds (0 : ℝ) := by
    apply Iio_mem_nhds
    exact h_pos_inv
  have h_eventually : ∀ᶠ (x : ℝ) in Filter.atTop,
        x^s / Real.exp (b * x) < 1 / C :=
    h_tendsto h_Iio
  rcases Filter.eventually_atTop.mp h_eventually with ⟨K_real, hK_real⟩
  let K0 : ℕ := Nat.ceil K_real
  let K : ℕ := max 1 K0
  have hK_ge1 : K ≥ 1 := Nat.le_max_left 1 K0
  refine ⟨K, hK_ge1, fun k hk => ?_⟩
  have h_k_ge : (K_real : ℝ) ≤ (k : ℝ) := by
    have h1 : (K_real : ℝ) ≤ (K0 : ℝ) := Nat.le_ceil K_real
    have h2 : (K0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.le_max_right _ _
    have h3 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact le_trans (le_trans h1 h2) h3
  have h_k_pos : 0 < (k : ℝ) := by
    have h4 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans hK_ge1 hk)
    linarith
  have h4 : (k : ℝ)^s / Real.exp (b * (k : ℝ)) < 1 / C := hK_real (k : ℝ) h_k_ge
  have h5 : 0 < (k : ℝ)^s := by positivity
  have h7 : (k : ℝ)^s * Real.exp (-b * (k : ℝ)) < 1 / C := by
    have h_inv : (Real.exp (b * (k : ℝ)))⁻¹ = Real.exp (-b * (k : ℝ)) := by
      have h_eq : -b * (k : ℝ) = -(b * (k : ℝ)) := by ring
      have h : Real.exp (-b * (k : ℝ)) = (Real.exp (b * (k : ℝ)))⁻¹ := by
        rw [h_eq]
        exact Real.exp_neg (b * (k : ℝ))
      exact h.symm
    have h_eq : (k : ℝ)^s / Real.exp (b * (k : ℝ)) =
        (k : ℝ)^s * Real.exp (-b * (k : ℝ)) := by
      rw [div_eq_mul_inv, h_inv] <;> ring
    rw [h_eq] at h4
    exact h4
  exact exp_absorb_helper' (k : ℝ) h5 hb hC h7

/-- Equivalent absorption form: there exists `K ≥ 1` such that for all `k ≥ K`:
  `k^s * Real.exp (-b * k) < 1 / C`. -/
lemma exp_absorbs_poly_threshold (s b C : ℝ) (hb : 0 < b) (hC : 0 < C) :
    ∃ (K : ℕ), K ≥ 1 ∧ ∀ (k : ℕ), k ≥ K →
      (k : ℝ)^s * Real.exp (-b * (k : ℝ)) < 1 / C := by
  rcases exp_dominates_poly_threshold s b C hb hC with ⟨K, hK1, hK⟩
  refine ⟨K, hK1, fun k hk => ?_⟩
  have h_core : C * (k : ℝ)^s < Real.exp (b * (k : ℝ)) := hK k hk
  have h_k_pos : 0 < (k : ℝ) := by
    have h4 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans hK1 hk)
    linarith
  have h5 : 0 < (k : ℝ)^s := by positivity
  have h6 : 0 < Real.exp (b * (k : ℝ)) := Real.exp_pos _
  have h7 : 0 < C := hC
  have h8 : (k : ℝ)^s * Real.exp (-b * (k : ℝ)) < 1 / C := by
    have h9 : C * ((k : ℝ)^s * Real.exp (-b * (k : ℝ))) < 1 := by
      have h10 : Real.exp (-b * (k : ℝ)) * Real.exp (b * (k : ℝ)) = 1 := by
        rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
      calc
        C * ((k : ℝ)^s * Real.exp (-b * (k : ℝ)))
          = (C * (k : ℝ)^s) * Real.exp (-b * (k : ℝ)) := by ring
        _ < Real.exp (b * (k : ℝ)) * Real.exp (-b * (k : ℝ)) := by gcongr
        _ = 1 := by rw [mul_comm, h10]
    have h12 : (k : ℝ)^s * Real.exp (-b * (k : ℝ)) < 1 / C := by
      calc
        (k : ℝ)^s * Real.exp (-b * (k : ℝ))
          = (C * ((k : ℝ)^s * Real.exp (-b * (k : ℝ)))) / C := by
            field_simp [h7.ne'] <;> ring
        _ < 1 / C := by gcongr
    exact h12
  exact h8

/-- Convert a real `atTop` eventual property into a natural-number threshold.
Given `h : ∀ x ≥ K_real, P x`, produce `∃ K : ℕ, ∀ k ≥ K, P (k : ℝ)`. -/
lemma nat_threshold_from_real {P : ℝ → Prop} {K_real : ℝ}
    (h : ∀ (x : ℝ), x ≥ K_real → P x) :
    ∃ (K : ℕ), ∀ (k : ℕ), k ≥ K → P (k : ℝ) := by
  let K : ℕ := Nat.ceil K_real
  refine ⟨K, fun k hk => ?_⟩
  have h1 : (K_real : ℝ) ≤ (K : ℝ) := Nat.le_ceil K_real
  have h2 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact h (k : ℝ) (le_trans h1 h2)

/-- Exponential-dyadic identity:
  `Real.exp (c * Real.log 2 * k) = (Real.rpow 2 (-k))^(-c)`.
This converts the exponential threshold into a dyadic-delta power.
If `dyadicDelta k = Real.rpow 2 (-(k : ℝ))`, then RHS is `(dyadicDelta k)^(-c)`. -/
lemma exp_log2_to_dyadicDelta {c : ℝ} (k : ℕ) :
    Real.exp (c * Real.log 2 * (k : ℝ)) =
    Real.rpow (Real.rpow 2 (-(k : ℝ))) (-c) := by
  have h2 : Real.rpow (Real.rpow 2 (-(k : ℝ))) (-c) =
      Real.rpow 2 ((-(k : ℝ)) * (-c)) := by
    have h_rpow : ∀ (x : ℝ), 0 ≤ x → ∀ (y z : ℝ),
        Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) := by
      intro x hx y z
      exact (Real.rpow_mul hx y z).symm
    exact h_rpow 2 (by norm_num) (-(k : ℝ)) (-c)
  rw [h2]
  have h3 : (-(k : ℝ)) * (-c) = c * (k : ℝ) := by ring
  rw [h3]
  have h4 : Real.rpow 2 (c * (k : ℝ)) = Real.exp ((c * (k : ℝ)) * Real.log 2) := by
    have h5 : 0 < Real.rpow 2 (c * (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h6 : Real.log (Real.rpow 2 (c * (k : ℝ))) = (c * (k : ℝ)) * Real.log 2 := by
      have h7 : Real.log ((2 : ℝ) ^ (c * (k : ℝ))) = (c * (k : ℝ)) * Real.log 2 :=
        Real.log_rpow (by norm_num : (0 : ℝ) < 2) (c * (k : ℝ))
      simpa using h7
    rw [← Real.exp_log h5, h6]
  rw [h4] <;> ring_nf

/-- Positivity of a four-way nested min. -/
lemma pos_min4 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < min (min (min a b) c) d := by
  positivity

/-- Positivity of a three-way nested min. -/
lemma pos_min3 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < min (min a b) c := by
  positivity

/-- Given a real lower bound `X`, produce a natural `K ≥ X` with `K ≥ 1`. -/
lemma exists_nat_ge_one (X : ℝ) : ∃ (K : ℕ), (K : ℝ) ≥ X ∧ K ≥ 1 := by
  rcases exists_nat_ge X with ⟨K0, hK0⟩
  let K : ℕ := max 1 K0
  refine ⟨K, ?_, Nat.le_max_left 1 K0⟩
  have h1 : (K0 : ℝ) ≥ X := by exact_mod_cast hK0
  have h2 : (K : ℝ) ≥ (K0 : ℝ) := by exact_mod_cast Nat.le_max_right _ _
  exact le_trans h1 h2

/-- Combined threshold: produce `K : ℕ` satisfying both an exponential-dominance
condition and a lower bound `K ≥ B`. -/
lemma exp_dominates_poly_threshold_with_lower_bound
    (s b C : ℝ) (hb : 0 < b) (hC : 0 < C) (B : ℕ) :
    ∃ (K : ℕ), K ≥ B ∧ ∀ (k : ℕ), k ≥ K →
      C * (k : ℝ)^s < Real.exp (b * (k : ℝ)) := by
  rcases exp_dominates_poly_threshold s b C hb hC with ⟨K0, _, hK0⟩
  let K : ℕ := max B K0
  refine ⟨K, Nat.le_max_left B K0, fun k hk => ?_⟩
  have h_k_ge_K0 : k ≥ K0 := by
    have h1 : K0 ≤ K := Nat.le_max_right B K0
    exact le_trans h1 hk
  exact hK0 k h_k_ge_K0

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

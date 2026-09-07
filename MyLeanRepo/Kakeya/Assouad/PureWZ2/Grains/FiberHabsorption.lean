import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperAbsorptionArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fiber-specific h_absorb arithmetic with constant multiplicity

This module formalizes the h_absorb condition for the rescaled fiber in the
`outputLoss ≤ 1` case of the grain proposition.

## Fiber h_absorb derivation

The standard fiber h_absorb (from `paper_h_absorb_fiber_core`) is:
  `4·M²·C²·K³ ≤ Q·τ·mass²`
where `K` bounds `ε²·N` (fiber packing).

With **constant multiplicity** μ₀:
- `M ≤ 2·μ₀` (multiplicity upper bound)
- `mass ≥ μ₀·vol` (mass lower bound)

Substituting:
  `4·(2μ₀)²·C²·K³ ≤ Q·τ·(μ₀·vol)²`
  `16·μ₀²·C²·K³ ≤ Q·τ·μ₀²·vol²`

Cancel `μ₀² > 0`:
  `16·C²·K³ ≤ Q·τ·vol²`

## Loose incidence verification

On the fiber:
- `K ≤ C_K·ε²` (N bounded by packing constant)
- `τ ≥ κ·ε^(σ/2)` (loose incidence lower bound)
- `vol ≥ c·ε²` (at least one tube's volume)

Then:
- LHS ≤ `16·C²·C_K³·ε⁶`
- RHS ≥ `κ·ε^(σ/2)·c²·ε⁴ = κ·c²·ε^(σ/2+4)`

Need: `16·C²·C_K³·ε⁶ ≤ κ·c²·ε^(σ/2+4)`
i.e.: `16·C²·C_K³·ε^(2-σ/2) ≤ κ·c²`

Since `2-σ/2 > 0` (for σ < 1), `ε^(2-σ/2) → 0` as ε → 0.
Thus the condition holds for sufficiently small ε.

## Main results

- `fiber_h_absorb_mu_cancellation`: cancel μ₀ from the full fiber h_absorb
- `fiber_h_absorb_arithmetic_core`: verify `16C²K³ ≤ Qτvol²` with loose incidence
- `fiber_h_absorb_exists`: existence of a sufficiently small ε₀
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- μ cancellation for the fiber h_absorb.

Given `M ≤ 2·μ₀` and `mass ≥ μ₀·vol`, proving
  `16·C²·K³ ≤ Q·τ·vol²`
implies the full fiber h_absorb:
  `4·M²·C²·K³ ≤ Q·τ·mass²` -/
lemma fiber_h_absorb_mu_cancellation
    (C K mu0 mass vol tau : ℝ)
    (M : ℝ)
    (Q : ℕ)
    (_hC_nonneg : 0 ≤ C)
    (hK_nonneg : 0 ≤ K)
    (hmu0_pos : 0 < mu0)
    (_hvol_nonneg : 0 ≤ vol)
    (_hmass_nonneg : 0 ≤ mass)
    (htau_nonneg : 0 ≤ tau)
    (hM_nonneg : 0 ≤ M)
    (hM_le : M ≤ 2 * mu0)
    (hmass_ge : mu0 * vol ≤ mass)
    (h_reduced : 16 * C^2 * K^3 ≤ (Q : ℝ) * tau * vol^2) :
    4 * M^2 * C^2 * K^3 ≤ (Q : ℝ) * tau * mass^2 := by
  have h1 : 4 * M^2 * C^2 * K^3 ≤ 4 * (2 * mu0)^2 * C^2 * K^3 := by
    gcongr
  have h2 : 4 * (2 * mu0)^2 * C^2 * K^3 = mu0^2 * (16 * C^2 * K^3) := by ring
  rw [h2] at h1
  have h3 : mu0^2 * (16 * C^2 * K^3) ≤ mu0^2 * ((Q : ℝ) * tau * vol^2) := by
    gcongr
  have h4 : mu0^2 * ((Q : ℝ) * tau * vol^2) = (Q : ℝ) * tau * (mu0 * vol)^2 := by ring
  rw [h4] at h3
  calc
    4 * M^2 * C^2 * K^3
      ≤ mu0^2 * (16 * C^2 * K^3) := h1
    _ ≤ (Q : ℝ) * tau * (mu0 * vol)^2 := h3
    _ ≤ (Q : ℝ) * tau * mass^2 := by
      gcongr

/-- Core arithmetic for the fiber h_absorb with loose incidence.

Given:
- `K ≤ C_K·ε²` (fiber packing bound)
- `τ ≥ κ·ε^(σ/2)` (loose incidence lower bound)
- `vol ≥ c·ε²` (volume lower bound)
- `Q ≥ 1`
- `ε` sufficiently small

Proves: `16·C²·K³ ≤ Q·τ·vol²`

The key exponent is `2 - σ/2 > 0`, so `ε^(2-σ/2) → 0` as ε → 0. -/
lemma fiber_h_absorb_arithmetic_core
    (epsilon sigma C C_K c K kappa tau vol : ℝ)
    (Q : ℕ)
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (_hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hC_pos : 0 < C)
    (hC_K_pos : 0 < C_K)
    (hc_pos : 0 < c)
    (hK_nonneg : 0 ≤ K)
    (hkappa_pos : 0 < kappa)
    (htau_nonneg : 0 ≤ tau)
    (_hvol_nonneg : 0 ≤ vol)
    (hQ_pos : 0 < Q)
    (hK_bound : K ≤ C_K * epsilon^2)
    (htau_bound : kappa * epsilon^(sigma / 2) ≤ tau)
    (hvol_bound : c * epsilon^2 ≤ vol)
    (hepsilon_small : epsilon ≤
        (kappa * c^2 / (16 * C^2 * C_K^3)) ^ (1 / (2 - sigma / 2))) :
    16 * C^2 * K^3 ≤ (Q : ℝ) * tau * vol^2 := by
  have halpha_pos : 0 < 2 - sigma / 2 := by linarith
  have h1 : 0 < kappa * c^2 / (16 * C^2 * C_K^3) := by positivity
  have h2 : 0 ≤ epsilon := by linarith

  -- ε^(2-σ/2) ≤ κc²/(16C²C_K³) from smallness
  have h3 : epsilon^(2 - sigma / 2) ≤ kappa * c^2 / (16 * C^2 * C_K^3) := by
    have h4 : epsilon^(2 - sigma / 2) ≤
        ((kappa * c^2 / (16 * C^2 * C_K^3)) ^ (1 / (2 - sigma / 2)))^(2 - sigma / 2) :=
      Real.rpow_le_rpow h2 hepsilon_small (by linarith)
    have h5 : ((kappa * c^2 / (16 * C^2 * C_K^3)) ^ (1 / (2 - sigma / 2)))^(2 - sigma / 2) =
        kappa * c^2 / (16 * C^2 * C_K^3) := by
      rw [← Real.rpow_mul (by positivity)]
      have h6 : (1 / (2 - sigma / 2)) * (2 - sigma / 2) = 1 :=
        one_div_mul_cancel halpha_pos.ne'
      rw [h6]
      simp
    rw [h5] at h4
    exact h4

  -- Multiply: 16C²C_K³·ε^(2-σ/2) ≤ κc²
  have h7 : 16 * C^2 * C_K^3 * epsilon^(2 - sigma / 2) ≤ kappa * c^2 := by
    have h8 : 16 * C^2 * C_K^3 * epsilon^(2 - sigma / 2) ≤
        16 * C^2 * C_K^3 * (kappa * c^2 / (16 * C^2 * C_K^3)) := by
      gcongr
    have h9 : 16 * C^2 * C_K^3 * (kappa * c^2 / (16 * C^2 * C_K^3)) = kappa * c^2 := by
      field_simp [show (16 * C^2 * C_K^3 : ℝ) ≠ 0 by positivity]
    rw [h9] at h8
    exact h8

  -- LHS ≤ 16C²C_K³·ε⁶
  have h10 : 16 * C^2 * K^3 ≤ 16 * C^2 * C_K^3 * epsilon^6 := by
    have h11 : K^3 ≤ (C_K * epsilon^2)^3 := by gcongr
    have h12 : (C_K * epsilon^2)^3 = C_K^3 * epsilon^6 := by ring
    rw [h12] at h11
    nlinarith

  -- RHS ≥ κc²·ε^(σ/2+4)
  have h13 : (Q : ℝ) * tau * vol^2 ≥ kappa * c^2 * epsilon^(sigma / 2 + 4) := by
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ_pos
    have h14 : (Q : ℝ) * tau * vol^2 ≥ 1 * tau * vol^2 := by
      gcongr
    have h15 : tau * vol^2 ≥ (kappa * epsilon^(sigma / 2)) * (c * epsilon^2)^2 := by
      gcongr
    have h161 : (c * epsilon^2)^2 = c^2 * epsilon^4 := by ring
    have h162 : epsilon^(sigma / 2) * epsilon^(4 : ℝ) = epsilon^(sigma / 2 + 4) :=
      (Real.rpow_add hepsilon_pos (sigma / 2) (4 : ℝ)).symm
    have h16 : (kappa * epsilon^(sigma / 2)) * (c * epsilon^2)^2 =
        kappa * c^2 * epsilon^(sigma / 2 + 4) := by
      have h_expand : (c * epsilon^2)^2 = c^2 * epsilon^4 := by ring
      have h4cast : (epsilon ^ 4 : ℝ) = epsilon^(4 : ℝ) := by norm_cast
      have h_b : epsilon^(sigma / 2) * (c^2 * epsilon^(4 : ℝ)) =
          c^2 * (epsilon^(sigma / 2) * epsilon^(4 : ℝ)) := by
        have h1 : epsilon^(sigma / 2) * (c^2 * epsilon^(4 : ℝ)) =
            (epsilon^(sigma / 2) * c^2) * epsilon^(4 : ℝ) := by rw [mul_assoc]
        have h2 : epsilon^(sigma / 2) * c^2 = c^2 * epsilon^(sigma / 2) :=
          mul_comm (epsilon^(sigma / 2)) (c^2)
        rw [h1, h2, mul_assoc]
      have h_rearrange : (kappa * epsilon^(sigma / 2)) * (c^2 * epsilon^4) =
          kappa * c^2 * (epsilon^(sigma / 2) * epsilon^(4 : ℝ)) := by
        calc
          (kappa * epsilon^(sigma / 2)) * (c^2 * epsilon^4)
            = (kappa * epsilon^(sigma / 2)) * (c^2 * epsilon^(4 : ℝ)) := by rw [h4cast]
          _ = kappa * (epsilon^(sigma / 2) * (c^2 * epsilon^(4 : ℝ))) := by rw [mul_assoc]
          _ = kappa * (c^2 * (epsilon^(sigma / 2) * epsilon^(4 : ℝ))) := by rw [h_b]
          _ = kappa * c^2 * (epsilon^(sigma / 2) * epsilon^(4 : ℝ)) := by rw [mul_assoc]
      have h_step1 : (kappa * epsilon^(sigma / 2)) * (c * epsilon^2)^2 =
          kappa * c^2 * (epsilon^(sigma / 2) * epsilon^(4 : ℝ)) := by
        rw [h_expand]
        exact h_rearrange
      have h_step2 : kappa * c^2 * (epsilon^(sigma / 2) * epsilon^(4 : ℝ)) =
          kappa * c^2 * epsilon^(sigma / 2 + 4) := by
        apply congr_arg (fun x : ℝ => kappa * c^2 * x)
        exact h162
      exact Eq.trans h_step1 h_step2
    rw [h16] at h15
    linarith

  -- Connect: 16C²C_K³·ε⁶ ≤ κc²·ε^(σ/2+4)
  have h17 : 16 * C^2 * C_K^3 * epsilon^6 ≤ kappa * c^2 * epsilon^(sigma / 2 + 4) := by
    have h18 : epsilon^(sigma / 2 + 4) * epsilon^(2 - sigma / 2) = epsilon^6 := by
      have h181 := Real.rpow_add hepsilon_pos (sigma / 2 + 4) (2 - sigma / 2)
      have h182 : (sigma / 2 + 4) + (2 - sigma / 2) = (6 : ℝ) := by ring
      rw [h182] at h181
      have h183 : epsilon ^ (6 : ℝ) = epsilon ^ 6 := by norm_cast
      exact Eq.trans h181.symm h183
    have h19 : 0 ≤ epsilon^(sigma / 2 + 4) := by positivity
    have h20 : 16 * C^2 * C_K^3 * epsilon^6 ≤ kappa * c^2 * epsilon^(sigma / 2 + 4) := by
      rw [← h18]
      have h21 : 16 * C^2 * C_K^3 * (epsilon^(sigma / 2 + 4) * epsilon^(2 - sigma / 2)) ≤
          kappa * c^2 * epsilon^(sigma / 2 + 4) := by
        have h22 : 16 * C^2 * C_K^3 * epsilon^(2 - sigma / 2) ≤ kappa * c^2 := h7
        calc
          16 * C^2 * C_K^3 * (epsilon^(sigma / 2 + 4) * epsilon^(2 - sigma / 2))
            = epsilon^(sigma / 2 + 4) * (16 * C^2 * C_K^3 * epsilon^(2 - sigma / 2)) := by ring
          _ ≤ epsilon^(sigma / 2 + 4) * (kappa * c^2) := by gcongr
          _ = kappa * c^2 * epsilon^(sigma / 2 + 4) := by ring
      exact h21
    exact h20

  calc
    16 * C^2 * K^3
      ≤ 16 * C^2 * C_K^3 * epsilon^6 := h10
    _ ≤ kappa * c^2 * epsilon^(sigma / 2 + 4) := h17
    _ ≤ (Q : ℝ) * tau * vol^2 := h13

/-- Existence of a threshold ε₀ such that the fiber h_absorb holds
    for all `0 < ε < ε₀`. -/
lemma fiber_h_absorb_exists
    (sigma C C_K c kappa : ℝ)
    (_hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hC_pos : 0 < C)
    (hC_K_pos : 0 < C_K)
    (hc_pos : 0 < c)
    (hkappa_pos : 0 < kappa) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ (epsilon : ℝ), 0 < epsilon → epsilon < epsilon₀ →
        ∀ (K tau vol : ℝ) (Q : ℕ),
          0 ≤ K → 0 ≤ tau → 0 ≤ vol → 0 < Q →
          K ≤ C_K * epsilon^2 →
          kappa * epsilon^(sigma / 2) ≤ tau →
          c * epsilon^2 ≤ vol →
          16 * C^2 * K^3 ≤ (Q : ℝ) * tau * vol^2 := by
  have halpha_pos : 0 < 2 - sigma / 2 := by linarith
  set threshold : ℝ :=
      (kappa * c^2 / (16 * C^2 * C_K^3)) ^ (1 / (2 - sigma / 2))
    with hthreshold_def
  have hthreshold_pos : 0 < threshold := by positivity
  let epsilon₀ := min threshold 1
  have hepsilon₀_pos : 0 < epsilon₀ := by positivity
  refine ⟨epsilon₀, hepsilon₀_pos, fun epsilon hepsilon_pos hepsilon_lt => ?_⟩
  have hepsilon_lt_threshold : epsilon < threshold := by
    calc epsilon < epsilon₀ := hepsilon_lt
         _ ≤ threshold := by exact min_le_left threshold 1
  have hepsilon_lt_one : epsilon < 1 := by
    calc epsilon < epsilon₀ := hepsilon_lt
         _ ≤ 1 := by exact min_le_right threshold 1
  intro K tau vol Q hK_nonneg htau_nonneg hvol_nonneg hQ_pos hK_bound htau_bound hvol_bound
  exact fiber_h_absorb_arithmetic_core
    epsilon sigma C C_K c K kappa tau vol Q
    hepsilon_pos hepsilon_lt_one _hsigma_pos hsigma_lt_one hC_pos hC_K_pos hc_pos
    hK_nonneg hkappa_pos htau_nonneg hvol_nonneg hQ_pos
    hK_bound htau_bound hvol_bound
    (by linarith)

/-- **General Q-existence for the fiber h_absorb (direct analysis).**

For ANY finite packing bound `K` (including `K ~ 1`, i.e. `N ~ ε^(-2)`),
we can choose `Q` large enough to satisfy
`16·C²·K³ ≤ Q·τ·vol²`, provided `τ > 0` and `vol > 0`.

This is bacon's direct analysis: unlike `fiber_h_absorb_arithmetic_core`,
this does NOT require `K ≤ C_K·ε²`. The CV term `(ε²·N)^(3/2)` is bounded
by `K^(3/2)` (a constant when `N ~ ε^(-2)`), and `Q` absorbs the deficit.

The cost is that `Q` may be large (depending on `K`, `τ`, `vol`), which
feeds into the multiplicity growth condition. The conditional weak planiness
(`weak_planiness_wiring_half_conditional`) only requires growth on the
narrow set, where multiplicity is automatically high enough. -/
lemma fiber_h_absorb_general_Q_exists
    (C K tau vol : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hK_nonneg : 0 ≤ K)
    (htau_pos : 0 < tau)
    (hvol_pos : 0 < vol) :
    ∃ (Q : ℕ), 16 * C^2 * K^3 ≤ (Q : ℝ) * tau * vol^2 := by
  let rhs_per_Q : ℝ := tau * vol^2
  have hrhs_pos : 0 < rhs_per_Q := by positivity
  let target : ℝ := 16 * C^2 * K^3
  have htarget_nonneg : 0 ≤ target := by positivity
  by_cases h : target ≤ 0
  · -- target = 0, Q = 1 works
    refine ⟨1, ?_⟩
    have h0 : 16 * C^2 * K^3 = 0 := by
      have h1 : target = 0 := by linarith
      simpa [target] using h1
    rw [h0]
    <;> positivity
  · -- target > 0, choose Q = ceil(target / rhs_per_Q)
    have htarget_pos : 0 < target := by linarith
    let Q0 : ℕ := Nat.ceil (target / rhs_per_Q)
    have hQ0 : (Q0 : ℝ) ≥ target / rhs_per_Q := Nat.le_ceil _
    refine ⟨Q0, ?_⟩
    have h_main : (Q0 : ℝ) * (tau * vol^2) ≥ 16 * C^2 * K^3 := by
      calc
        (Q0 : ℝ) * (tau * vol^2)
          ≥ (target / rhs_per_Q) * (tau * vol^2) := by gcongr
        _ = (target / rhs_per_Q) * rhs_per_Q := by rfl
        _ = target := by field_simp [hrhs_pos.ne'] <;> ring
        _ = 16 * C^2 * K^3 := by rfl
    have h_final : 16 * C^2 * K^3 ≤ (Q0 : ℝ) * tau * vol^2 := by
      have h_eq : (Q0 : ℝ) * tau * vol^2 = (Q0 : ℝ) * (tau * vol^2) := by ring
      rw [h_eq]
      exact h_main
    exact h_final

/-- **General h_absorb Q-existence (direct real form).**

Given multiplicity upper bound `M`, CV constant `C`, packing bound `K`,
loose incidence `tau`, and mass lower bound `mass`, there exists `Q : ℕ`
such that:

`2·M·C·K^(3/2) ≤ √(Q·τ)·mass`

This is the direct real-number form needed by `paper_h_absorb_ennreal_bridge`.
Unlike `fiber_h_absorb_arithmetic_core`, no small-ε assumption is needed:
`Q` simply absorbs any constant deficit. -/
lemma general_h_absorb_Q_exists
    (M C K tau mass : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hC_nonneg : 0 ≤ C)
    (hK_nonneg : 0 ≤ K)
    (htau_pos : 0 < tau)
    (hmass_pos : 0 < mass) :
    ∃ (Q : ℕ),
      2 * M * C * K^(3 / 2 : ℝ) ≤ Real.sqrt ((Q : ℝ) * tau) * mass := by
  by_cases hK : K = 0
  · -- K = 0, LHS = 0, Q = 1 works
    refine ⟨1, ?_⟩
    have h1 : K^(3 / 2 : ℝ) = 0 := by
      rw [hK]
      simp [Real.zero_rpow] <;> norm_num
    rw [h1]
    <;> ring_nf <;> positivity
  · -- K > 0
    have hK_pos : 0 < K := by
      by_contra h
      have : K = 0 := by linarith
      exact hK this
    by_cases hMC : M = 0 ∨ C = 0
    · -- M = 0 or C = 0, LHS = 0
      refine ⟨1, ?_⟩
      rcases hMC with (rfl | rfl) <;> ring_nf <;> positivity
    · -- M > 0 and C > 0
      have hM_pos : 0 < M :=
        lt_of_le_of_ne hM_nonneg (fun h => hMC (Or.inl h.symm))
      have hC_pos : 0 < C :=
        lt_of_le_of_ne hC_nonneg (fun h => hMC (Or.inr h.symm))
      let lhs_sq : ℝ := 4 * M^2 * C^2 * K^3
      have hlhs_sq_pos : 0 < lhs_sq := by positivity
      let rhs_per_Q : ℝ := tau * mass^2
      have hrhs_pos : 0 < rhs_per_Q := by positivity
      let Q0 : ℕ := Nat.ceil (lhs_sq / rhs_per_Q)
      have hQ0 : (Q0 : ℝ) ≥ lhs_sq / rhs_per_Q := Nat.le_ceil _
      have h_main : (Q0 : ℝ) * rhs_per_Q ≥ lhs_sq := by
        calc
          (Q0 : ℝ) * rhs_per_Q ≥ (lhs_sq / rhs_per_Q) * rhs_per_Q := by gcongr
          _ = lhs_sq := by field_simp [hrhs_pos.ne'] <;> ring
      have h10 : 4 * M^2 * C^2 * K^3 ≤ (Q0 : ℝ) * tau * mass^2 := by
        have h11 : (Q0 : ℝ) * rhs_per_Q = (Q0 : ℝ) * tau * mass^2 := by
          simp [rhs_per_Q] <;> ring
        rw [h11] at h_main
        exact h_main
      have hK_pow : (K^(3 / 2 : ℝ))^2 = K^3 := by
        have h1 : (K^(3 / 2 : ℝ))^2 = K^(3 / 2 : ℝ) * K^(3 / 2 : ℝ) := by ring
        rw [h1]
        have h2 : K^((3 / 2 : ℝ) + (3 / 2 : ℝ)) = K^(3 / 2 : ℝ) * K^(3 / 2 : ℝ) :=
          Real.rpow_add hK_pos (3 / 2 : ℝ) (3 / 2 : ℝ)
        exact h2.symm ▸ by norm_num
      have h12 : 0 ≤ (2 * M * C * K^(3 / 2 : ℝ)) / mass := by positivity
      have h13 : ((2 * M * C * K^(3 / 2 : ℝ)) / mass)^2 ≤ (Q0 : ℝ) * tau := by
        calc
          ((2 * M * C * K^(3 / 2 : ℝ)) / mass)^2
            = (4 * M^2 * C^2 * (K^(3 / 2 : ℝ))^2) / mass^2 := by
              field_simp [hmass_pos.ne'] <;> ring
          _ = (4 * M^2 * C^2 * K^3) / mass^2 := by rw [hK_pow]
          _ ≤ ((Q0 : ℝ) * tau * mass^2) / mass^2 := by gcongr
          _ = (Q0 : ℝ) * tau := by field_simp [hmass_pos.ne'] <;> ring
      have h14 : (2 * M * C * K^(3 / 2 : ℝ)) / mass ≤ Real.sqrt ((Q0 : ℝ) * tau) := by
        rw [← Real.sqrt_sq h12]
        exact Real.sqrt_le_sqrt h13
      refine ⟨Q0, ?_⟩
      calc
        2 * M * C * K^(3 / 2 : ℝ)
          = ((2 * M * C * K^(3 / 2 : ℝ)) / mass) * mass := by
            field_simp [hmass_pos.ne'] <;> ring
        _ ≤ Real.sqrt ((Q0 : ℝ) * tau) * mass := by gcongr

/-- Complete ENNReal bridge for the fiber h_absorb.

Given the real fiber bounds and constant multiplicity, produce the ENNReal
h_absorb condition required by `paper_broad_mass_budget_main` and
`weak_planiness_wiring`.

This chains together:
1. Fiber arithmetic: `16C²K³ ≤ Qτvol²`
2. Square root: `4C·K^(3/2) ≤ √(Qτ)·vol`
3. Packing: `(ε²·N)^(3/2) ≤ K^(3/2)`
4. μ cancellation: `2M·C·(ε²·N)^(3/2) ≤ √(Qτ)·mass`
5. ENNReal lift via `paper_h_absorb_ennreal_bridge` -/
lemma fiber_h_absorb_ennreal
    (epsilon sigma C K kappa tau vol mu0 mass : ℝ)
    (M : ℝ)
    (N : ℕ)
    (Q : ℕ)
    (C_enn M_enn S_mass F_enncard : ENNReal)
    (hepsilon_pos : 0 < epsilon)
    (hsigma_lt_one : sigma < 1)
    (hC_pos : 0 < C)
    (hK_nonneg : 0 ≤ K)
    (hkappa_pos : 0 < kappa)
    (htau_pos : 0 < tau)
    (hvol_pos : 0 < vol)
    (hmu0_pos : 0 < mu0)
    (hmass_pos : 0 < mass)
    (hM_nonneg : 0 ≤ M)
    (hN_pos : 0 < N)
    (hQ_pos : 0 < Q)
    (hM_le : M ≤ 2 * mu0)
    (hmass_ge : mu0 * vol ≤ mass)
    (hN_bound : epsilon^2 * (N : ℝ) ≤ K)
    (h_arithmetic : 16 * C^2 * K^3 ≤ (Q : ℝ) * tau * vol^2)
    (hC_enn : C_enn ≤ ENNReal.ofReal C)
    (hM_enn : M_enn ≤ ENNReal.ofReal M)
    (hcard : F_enncard ≤ (N : ENNReal))
    (hmass_enn : ENNReal.ofReal mass ≤ S_mass) :
    (2 : ENNReal) * M_enn * C_enn *
        (ENNReal.ofReal (epsilon^2) * F_enncard)^(3 / 2 : ℝ) ≤
      (((Q : ENNReal) * ENNReal.ofReal tau)^(1 / 2 : ℝ)) * S_mass := by
  -- Step 1: Square root of arithmetic
  have h1 : 0 ≤ 16 * C^2 * K^3 := by positivity
  have h2 : 0 ≤ (Q : ℝ) * tau * vol^2 := by positivity
  have h3 : Real.sqrt (16 * C^2 * K^3) ≤ Real.sqrt ((Q : ℝ) * tau * vol^2) :=
    Real.sqrt_le_sqrt h_arithmetic
  have h4 : Real.sqrt (16 * C^2 * K^3) = 4 * C * K^(3 / 2 : ℝ) := by
    have h41 : 0 ≤ 4 * C := by positivity
    have h42 : 0 ≤ K^(3 / 2 : ℝ) := by positivity
    have h : Real.sqrt (16 * C^2 * K^3) = Real.sqrt (16 * C^2) * Real.sqrt (K^3) := by
      rw [Real.sqrt_mul] <;> positivity
    rw [h]
    have h5 : Real.sqrt (16 * C^2) = 4 * C := by
      have h51 : (4 * C)^2 = 16 * C^2 := by ring
      rw [← h51]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg] <;> positivity
    have h6 : Real.sqrt (K^3) = K^(3 / 2 : ℝ) := by
      have h7 : K^3 = K^(3 : ℝ) := by norm_cast
      rw [h7]
      have h8 : Real.sqrt (K^(3 : ℝ)) = (K^(3 : ℝ))^(1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h8]
      have h9 : (K^(3 : ℝ))^(1 / 2 : ℝ) = K^((3 : ℝ) * (1 / 2 : ℝ)) :=
        Eq.symm (Real.rpow_mul hK_nonneg (3 : ℝ) (1 / 2 : ℝ))
      rw [h9]
      have h10 : (3 : ℝ) * (1 / 2 : ℝ) = (3 / 2 : ℝ) := by norm_num
      rw [h10]
    rw [h5, h6] <;> ring
  have h5 : Real.sqrt ((Q : ℝ) * tau * vol^2) = Real.sqrt ((Q : ℝ) * tau) * vol := by
    have h51 : Real.sqrt ((Q : ℝ) * tau * vol^2) =
        Real.sqrt ((Q : ℝ) * tau) * Real.sqrt (vol^2) := by
      rw [Real.sqrt_mul] <;> positivity
    rw [h51]
    have h52 : Real.sqrt (vol^2) = vol := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hvol_pos]
    rw [h52] <;> ring
  rw [h4, h5] at h3

  -- Step 2: Packing bound
  have h6 : (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ) ≤ K^(3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hN_bound (by norm_num)

  -- Step 3: Reduced h_absorb
  have h7 : 4 * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
      Real.sqrt ((Q : ℝ) * tau) * vol := by
    calc
      4 * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ)
        ≤ 4 * C * K^(3 / 2 : ℝ) := by gcongr
      _ ≤ Real.sqrt ((Q : ℝ) * tau) * vol := h3

  -- Step 4: μ cancellation (unsquared)
  have h8 : 2 * M * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
      Real.sqrt ((Q : ℝ) * tau) * mass := by
    have h81 : 2 * M * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
        2 * (2 * mu0) * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ) := by gcongr
    have h82 : 2 * (2 * mu0) * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ) =
        mu0 * (4 * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ)) := by ring
    rw [h82] at h81
    have h83 : mu0 * (4 * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ)) ≤
        mu0 * (Real.sqrt ((Q : ℝ) * tau) * vol) := by gcongr
    have h84 : mu0 * (Real.sqrt ((Q : ℝ) * tau) * vol) =
        Real.sqrt ((Q : ℝ) * tau) * (mu0 * vol) := by ring
    rw [h84] at h83
    calc
      2 * M * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ)
        ≤ mu0 * (4 * C * (epsilon^2 * (N : ℝ))^(3 / 2 : ℝ)) := h81
      _ ≤ Real.sqrt ((Q : ℝ) * tau) * (mu0 * vol) := h83
      _ ≤ Real.sqrt ((Q : ℝ) * tau) * mass := by gcongr

  -- Step 5: ENNReal bridge
  exact paper_h_absorb_ennreal_bridge
    (epsilon^2) N C M mass tau Q
    C_enn M_enn S_mass F_enncard
    (by positivity) (by linarith) hM_nonneg (by linarith) htau_pos hN_pos
    h8 hC_enn hM_enn hcard hmass_enn

end Kakeya.Assouad

end

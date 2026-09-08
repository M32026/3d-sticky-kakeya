/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exponent bookkeeping of the bilinear broad--narrow cap induction

steps **A1** (, §5 row A1; existing here , mathematics identical).

Pure real arithmetic. Nothing here is geometry; these are the budget identities the informal
proof of the Cap Lemma uses, so that the *accounting* is compiler-checked before the geometry
(steps A2--A6) is written.

* `Kakeya.ML2Cap.Arith.broad_level` — the broad case at one level. At scale `δ` with `N ≤ δ⁻¹`
  tubes, angular scale `θ = δ^c` and fullness `λ`, the bilinear two-tube bound gives
  `μ ≤ C₃ N δ / (θ λ²)`, and that is `≤ C₃ N^γ δ^{γ-c} λ^{-2}` whenever `c ≤ γ ≤ 1`. So the loss
  against the target `N^γ` is `δ^{γ-c} λ^{-2}`: a **positive** power of the level's scale. This is
  where the cardinality-weighted target `μ ≤ δ^{-ε}|𝕋|^γ` pays the angular loss, and it is exactly
  what fails at `γ = 0` (the plain Kakeya maximal target), since `c ≤ γ` is then impossible.
* `Kakeya.ML2Cap.Arith.exists_depth` — the induction has finite depth `k*` for every accuracy.
* `Kakeya.ML2Cap.Arith.bottom_trivial` — at the bottom level the trivial bound `μ ≤ N` already
  fits inside `δ^{-ε/2}`.
* `Kakeya.ML2Cap.Arith.drift` — a Katz--Tao (or fullness) hypothesis at the fine scale `δ`, read
  at the coarser level scale `δ^a`, is still a hypothesis of the same shape, provided
  `η ≤ a·η_D`; so a single `η := (ε/2)·η_D` serves every level.
* `Kakeya.ML2Cap.Arith.total_loss` — a constant loss per level over `k` levels is absorbed by
  `δ^{-ε/2}` for all `δ ≤ C^{-2k/ε}`.
* `Kakeya.ML2Cap.Arith.recursion_bound` — the downward induction itself: `F k ≤ max A (C·F(k+1))`
  below the bottom, `F K ≤ A`, gives `F 0 ≤ C^K A`.
* `Kakeya.ML2Cap.Arith.gain_is_positive_power` — the sign statement behind `broad_level`: with
  `c ≤ γ` the factor `δ^{γ-c}` is a gain, not a loss.

No `axiom`, `opaque` or `native_decide`; no in-tree import, hence no possible dependence on the
abandoned Wang--Zahl route.
-/

@[expose] public section

open Real Filter Topology

namespace Kakeya.ML2Cap.Arith

/-- **Broad case at one level.** Scale `δ`, `N ≤ δ⁻¹` tubes, angular scale `θ = δ^c`, fullness
`λ`. The bilinear bound gives `μ ≤ C₃ N δ / (θ λ²)`; this is `≤ C₃ N^γ δ^(γ-c) λ⁻²` whenever
`c ≤ γ ≤ 1`. So the loss against the target `N^γ` is `δ^(γ-c) λ⁻²`, a *positive* power of the
level's scale (times the fullness), not a negative one. -/
theorem broad_level {N δ γ c l : ℝ} (hN1 : 1 ≤ N) (hNδ : N ≤ δ⁻¹) (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hc0 : 0 ≤ c) (_hcγ : c ≤ γ) (hγ1 : γ ≤ 1) (hl : 0 < l) :
    N * δ / (δ ^ c * l ^ 2) ≤ N ^ γ * δ ^ (γ - c) * (l ^ 2)⁻¹ := by
  have hNpos : 0 < N := by linarith
  have hsplit : N = N ^ γ * N ^ (1 - γ) := by
    rw [← rpow_add hNpos]; simp
  have h2 : N ^ (1 - γ) ≤ δ⁻¹ ^ (1 - γ) := rpow_le_rpow hNpos.le hNδ (by linarith)
  have h3 : δ⁻¹ ^ (1 - γ) = δ ^ (-(1 - γ)) := by
    rw [inv_rpow hδ0.le, rpow_neg hδ0.le]
  have hδc : 0 < δ ^ c := rpow_pos_of_pos hδ0 c
  have hl2 : 0 < l ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc N * δ = N ^ γ * N ^ (1 - γ) * δ := by rw [← hsplit]
    _ ≤ N ^ γ * δ ^ (-(1 - γ)) * δ := by
        have h4 : N ^ (1 - γ) ≤ δ ^ (-(1 - γ)) := h3 ▸ h2
        gcongr
    _ = N ^ γ * δ ^ (γ - c) * δ ^ c := by
        rw [mul_assoc, mul_assoc, ← rpow_add_one hδ0.ne', ← rpow_add hδ0]
        congr 2; ring
    _ = N ^ γ * δ ^ (γ - c) * (l ^ 2)⁻¹ * (δ ^ c * l ^ 2) := by
        field_simp

/-- **Depth of the induction.** For `0 < c < 1` and any target `ε > 0` there is a depth `k` with
`(1-c)^k ≤ ε`; the scale after `k` cap-rescalings is `δ^((1-c)^k) ≥ δ^ε`. -/
theorem exists_depth {c ε : ℝ} (hc0 : 0 < c) (_hc1 : c < 1) (hε : 0 < ε) :
    ∃ k : ℕ, (1 - c) ^ k ≤ ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (show 1 - c < 1 by linarith)
  exact ⟨k, hk.le⟩

/-- **The bottom level.** If `(1-c)^k ≤ ε/2` and `N < (δ^((1-c)^k))⁻¹`, the trivial bound `μ ≤ N`
is `≤ δ^(-ε/2)`. -/
theorem bottom_trivial {N δ a ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (_ha0 : 0 ≤ a) (ha : a ≤ ε / 2)
    (hN : N < (δ ^ a)⁻¹) : N ≤ δ ^ (-(ε / 2)) := by
  have h1 : (δ ^ a)⁻¹ = δ ^ (-a) := (rpow_neg hδ0.le a).symm
  have h2 : δ ^ (-a) ≤ δ ^ (-(ε / 2)) :=
    rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  linarith [h1 ▸ hN]

/-- **Katz--Tao / fullness drift.** A hypothesis `Δ_max ≤ δ^(-η)` read at the coarser scale
`δ_k = δ^a` (`a = (1-c)^k ≥ ε/2`) is `Δ_max ≤ δ_k^(-η/a) ≤ δ_k^(-η_D)` once `η ≤ a η_D`; so
`η := (ε/2) η_D` serves every level. -/
theorem drift {δ a η ηD : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (_ha0 : 0 < a) (hη : η ≤ a * ηD) :
    δ ^ (-η) ≤ (δ ^ a) ^ (-ηD) := by
  rw [← rpow_mul hδ0.le]
  apply rpow_le_rpow_of_exponent_ge hδ0 hδ1
  nlinarith

/-- **Total loss.** With a constant loss `C ≥ 1` per level over `k` levels and a per-leaf bound
`δ^(-ε/2) N^γ`, the assembled bound `C^k δ^(-ε/2) N^γ` is `≤ δ^(-ε) N^γ` for all
`δ ≤ C^(-2k/ε)`. -/
theorem total_loss {C ε δ : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) (k : ℕ) (hδ0 : 0 < δ)
    (hδ : δ ≤ C ^ (-(2 * (k : ℝ) / ε))) :
    C ^ (k : ℝ) * δ ^ (-(ε / 2)) ≤ δ ^ (-ε) := by
  have hCpos : 0 < C := by linarith
  have hδ1 : δ ≤ 1 := by
    refine hδ.trans ?_
    calc C ^ (-(2 * (k : ℝ) / ε)) ≤ C ^ (0 : ℝ) :=
          rpow_le_rpow_of_exponent_le hC (by
            have : 0 ≤ 2 * (k : ℝ) / ε := by positivity
            linarith)
      _ = 1 := rpow_zero C
  -- δ^(ε/2) ≤ C^(-k), i.e. C^k ≤ δ^(-ε/2)
  have hstep : δ ^ (ε / 2) ≤ C ^ (-(k : ℝ)) := by
    calc δ ^ (ε / 2) ≤ (C ^ (-(2 * (k : ℝ) / ε))) ^ (ε / 2) :=
          rpow_le_rpow hδ0.le hδ (by positivity)
      _ = C ^ (-(k : ℝ)) := by
          rw [← rpow_mul hCpos.le]; congr 1; field_simp
  have hCk : C ^ (k : ℝ) ≤ δ ^ (-(ε / 2)) := by
    have hδe : 0 < δ ^ (ε / 2) := rpow_pos_of_pos hδ0 _
    rw [rpow_neg hδ0.le]
    rw [rpow_neg hCpos.le] at hstep
    have := (le_inv_comm₀ hδe (by positivity)).mp hstep
    simpa using this
  calc C ^ (k : ℝ) * δ ^ (-(ε / 2)) ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := by
        gcongr
    _ = δ ^ (-ε) := by rw [← rpow_add hδ0]; ring_nf

/-- **The recursion.** If the level-`k` bound `F k` satisfies `F k ≤ max A (C * F (k+1))` below
the bottom `K` and `F K ≤ A`, with `C ≥ 1`, `A ≥ 0`, then `F 0 ≤ C^K * A`. -/
theorem recursion_bound (F : ℕ → ℝ) (A C : ℝ) (K : ℕ) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hstep : ∀ k < K, F k ≤ max A (C * F (k + 1))) (hbot : F K ≤ A) :
    F 0 ≤ C ^ K * A := by
  -- prove `F k ≤ C^(K-k) * A` by downward induction
  have key : ∀ j, ∀ k, k + j = K → F k ≤ C ^ j * A := by
    intro j
    induction j with
    | zero =>
      intro k hk
      obtain rfl : k = K := by omega
      simpa using hbot
    | succ j ih =>
      intro k hk
      have hkK : k < K := by omega
      have hnext : F (k + 1) ≤ C ^ j * A := ih (k + 1) (by omega)
      have hCj : (1 : ℝ) ≤ C ^ j := one_le_pow₀ hC
      calc F k ≤ max A (C * F (k + 1)) := hstep k hkK
        _ ≤ C ^ (j + 1) * A := by
          apply max_le
          · calc A = 1 * A := (one_mul A).symm
              _ ≤ C ^ (j + 1) * A := by gcongr; exact one_le_pow₀ hC
          · calc C * F (k + 1) ≤ C * (C ^ j * A) := by gcongr
              _ = C ^ (j + 1) * A := by ring
  exact key K 0 (by simp)

/-- The sign statement behind `Kakeya.ML2Cap.Arith.broad_level`: the hypothesis `c ≤ γ` is what
makes the `δ^(γ-c)` factor a *gain* rather than a loss.  (The inequality of `broad_level` is
monotone in the exponents, so it has no strict numerical counterexample at `γ < c`; what fails
there is the accounting, not the inequality.) -/
theorem gain_is_positive_power {δ γ c : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hcγ : c ≤ γ) :
    δ ^ (γ - c) ≤ 1 := by
  have := rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show 0 ≤ γ - c by linarith)
  simpa using this

end Kakeya.ML2Cap.Arith

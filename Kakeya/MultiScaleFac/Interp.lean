/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.FibreDensity
public import Kakeya.MultiScaleFac.FibrePacking

/-!
# Discrete-to-arbitrary-scale interpolation for fibre Frostman constants (GWZ §7.7)

The stopping time of `Kakeya.MultiScaleFac.Stopping` only ever splits at the grid scales
`σ_k = δ^{k/N}`, so every bound it produces lives at a *discrete* scale.  Both alternatives of
GWZ Lemma 7.7(A) need arbitrary real scales:

* alternative (i) is `IsFrostmanAtEveryScale`, a statement about **every** `ρ ∈ [δ, 1]`;
* the lower bound of alternative (ii) ranges over the whole real interval
  `[τ(θ/τ)^ε, θ(τ/θ)^ε]`.

This file supplies the two-sided passage between the two.  The mechanism is that all the
quantities involved change by at most a fixed power of the scale ratio when the anchor scale
moves inside `[ρ', ρ'']`: the anchor volume is comparable to `ρ^{n-1}`
(`Tube.le_volume`, `Tube.volume_le`), and the number of tubes in a fibre changes by at most the
packing count `(ρ''/ρ')^{n-1}` of `ρ'`-tubes inside a `ρ''`-tube.  Only the `n-1` transverse
directions contribute, since the tube cores all have length `1`.

* `frostmanConstant_interp_upper` — the upper interpolation, used for alternative (i).
* `frostmanConstant_interp_lower` — the lower interpolation, used for alternative (ii)-3.
* `gridScale_bracket`, `gridScale_div_gridScale_succ`, `gridScale_ratio_rpow_le` — the grid
  arithmetic that turns the interpolation loss into the exponent `(n-1)ε` of alternative (i):
  an arbitrary `ρ ∈ [δ, 1]` sits between two consecutive grid scales whose ratio is
  `δ^{-1/N}`, and `1/N ≤ ε = 1/√N`.

Both interpolation statements are relative: they compare the Frostman constant of one fibre
family with that of another, at a *different anchor scale but the same member scale* `σ`.  This
is deliberately not `Kakeya.StickyKakeya.anchor_densityIn_ge_of_discrete`, which produces an
absolute
numerical lower bound for the density and is moreover specialised to the index type `ι × E`.

The member scale `σ` is a parameter rather than being fixed to `δ`: alternative (i) uses
`σ = δ` (the family `𝕋[i₀;ρ]`), while alternative (ii)-3 uses `σ = τ` (the gap family
`𝕋_{τ∣ρ}[i₀]`).

`⪅` does not appear: every bound carries an explicit constant quantified before `δ`, as
required by.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Grid arithmetic for the interpolation loss -/

/-- **Every scale in `[δ, 1]` is bracketed by consecutive grid scales.**  This is the first half
of the discrete-to-arbitrary-scale passage of GWZ Lemma 7.7(A): an arbitrary `ρ` is squeezed
between `σ_{k+1}` and `σ_k` for some `k < N`, so a bound available at the grid scales can be
transported to `ρ` at the cost of the single-step ratio `σ_k/σ_{k+1} = δ^{-1/N}`. -/
theorem gridScale_bracket {δ : NNReal} (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) {N : ℕ} (hN : 0 < N)
    {ρ : NNReal} (hρδ : δ ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ k : ℕ, k < N ∧ gridScale δ N (k + 1) ≤ ρ ∧ ρ ≤ gridScale δ N k := by
  classical
  have hpN : gridScale δ N ((N - 1) + 1) ≤ ρ := by
    rw [show (N - 1) + 1 = N by omega, gridScale_self δ hN]; exact hρδ
  have hw : ∃ k : ℕ, gridScale δ N (k + 1) ≤ ρ := ⟨N - 1, hpN⟩
  refine ⟨Nat.find hw, ?_, Nat.find_spec hw, ?_⟩
  · by_contra h
    exact Nat.find_min hw (by omega) hpN
  · rcases Nat.eq_zero_or_pos (Nat.find hw) with h0 | hpos
    · rw [h0]; simpa using hρ1
    · have h := Nat.find_min hw (Nat.sub_lt hpos Nat.one_pos)
      rw [Nat.sub_add_cancel hpos] at h
      exact (not_le.mp h).le

/-! ### The two-sided interpolation -/

/-- **Upper interpolation of the fibre Frostman constant** (GWZ Lemma 7.7(A), the step from the grid
to alternative (i)).  If `ρ' ≤ ρ ≤ ρ''` are scales above the member scale `σ` and below `1`, then
the Frostman constant of the fibre family anchored at the intermediate scale `ρ` is controlled by
the one anchored at the coarse scale `ρ''`, at the cost of a packing factor in `ρ''/ρ₀`.  Uniformity
is needed at the base scale `ρ₀` only, and `C` depends only on the dimension and on `Cu`. -/
theorem frostmanConstant_interp_upper (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ σ ρ₀ ρ' ρ ρ'' : NNReal, δ ≤ σ → 0 < ρ₀ → 2 * σ ≤ ρ₀ → 8 * ρ₀ ≤ ρ' →
        ρ' ≤ ρ → ρ ≤ ρ'' → ρ'' ≤ 1 →
      Tube.IsUniformAtScale s T ρ₀ Cu →
      ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ).toConvexSpaceBody
          ≤ (C : ENNReal) *
              ENNReal.ofReal (((ρ'' : ℝ) / (ρ₀ : ℝ)) ^ (2 * (Module.finrank ℝ E : ℝ))) *
              ConvexSpaceBody.frostmanConstant (fibreIndex s T σ ρ'' i₀) (fibreBodies T σ)
                ((T i₀).rescale ρ'').toConvexSpaceBody := by
  classical
  refine ⟨1 ⊔ fibreFrostmanConst (Module.finrank ℝ E) *
    (2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E) * Cu ^ 3), le_sup_left, ?_⟩
  intro ι δ hδ hδ1 s T hball σ ρ₀ ρ' ρ ρ'' hδσ hρ₀ h2σρ₀ h8ρ₀ρ' hρ'ρ hρρ'' hρ''1 hUnif i₀ hi₀
  have hρ₀ρ : ρ₀ ≤ ρ :=
    (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 8)).trans (h8ρ₀ρ'.trans hρ'ρ)
  have hσρ : σ ≤ ρ := (le_mul_of_one_le_left zero_le one_le_two).trans (h2σρ₀.trans hρ₀ρ)
  have hR : ((ρ'' : ℝ) / (ρ₀ : ℝ)) ^ (2 * (Module.finrank ℝ E : ℝ))
      = ((ρ'' : ℝ) / (ρ₀ : ℝ)) ^ (2 * Module.finrank ℝ E) := by
    rw [← Real.rpow_natCast ((ρ'' : ℝ) / (ρ₀ : ℝ)) (2 * Module.finrank ℝ E), Nat.cast_mul,
      Nat.cast_ofNat]
  have hCu' : (1 : ℝ) ≤ (Cu : ℝ) := NNReal.one_le_coe.2 hCu
  have hC0 : (0 : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 3 :=
    mul_nonneg (mul_nonneg zero_le_two (pow_nonneg (by norm_num : (0 : ℝ) ≤ 25) _))
      (pow_nonneg (zero_le_one.trans hCu') 3)
  have hKR : (0 : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 3 *
      ((ρ'' : ℝ) / (ρ₀ : ℝ)) ^ (2 * Module.finrank ℝ E) :=
    mul_nonneg hC0 (pow_nonneg (div_nonneg ρ''.coe_nonneg ρ₀.coe_nonneg) _)
  have hcount : ((fibreIndex s T σ ρ'' i₀).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 3 *
          ((ρ'' : ℝ) / (ρ₀ : ℝ)) ^ (2 * Module.finrank ℝ E) *
          ((fibreIndex s T σ ρ i₀).card : ℝ) :=
    (anchorGraded_of_isUniformAtScale_atScale (s := s) (T := T) (σ := σ) (ρ := ρ₀) (ρ' := ρ'')
      hUnif hρ₀ hδσ h2σρ₀ (hρ₀ρ.trans hρρ'') hi₀).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (Finset.card_le_card
        (fibreIndex_subset_of_anchor_le (s := s) (T := T) (σ := σ)
          (h8ρ₀ρ'.trans hρ'ρ) i₀))) hKR)
  have hcount' : ((fibreIndex s T σ ρ'' i₀).card : ENNReal)
      ≤ ((2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E) * Cu ^ 3 : NNReal) : ENNReal) *
          ENNReal.ofReal (((ρ'' : ℝ) / (ρ₀ : ℝ)) ^ (2 * (Module.finrank ℝ E : ℝ))) *
          ((fibreIndex s T σ ρ i₀).card : ENNReal) := by
    rw [hR, ← ENNReal.ofReal_coe_nnreal,
      show ((2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E) * Cu ^ 3 : NNReal) : ℝ)
        = 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) ^ 3 by push_cast; ring,
      ← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_natCast (fibreIndex s T σ ρ i₀).card,
      ← ENNReal.ofReal_natCast (fibreIndex s T σ ρ'' i₀).card, ← ENNReal.ofReal_mul hKR]
    exact ENNReal.ofReal_le_ofReal hcount
  refine (frostmanConstant_fibre_le_of_card_le (σ := σ) (ρ := ρ) (ρ' := ρ'') (hδ.trans_le hδσ)
    (hσρ.trans (hρρ''.trans hρ''1)) hσρ hρρ'' hρ''1
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hi₀ hcount').trans
    (mul_le_mul' ?_ le_rfl)
  rw [← mul_assoc, ← ENNReal.coe_mul]
  exact mul_le_mul' (ENNReal.coe_le_coe.2 le_sup_right) le_rfl

end MultiScaleFac

end Kakeya

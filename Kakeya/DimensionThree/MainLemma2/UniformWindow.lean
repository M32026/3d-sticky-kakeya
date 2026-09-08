/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.KTWindowThresholds

/-!
# The `β`-uniform window pair, hoisted above the configuration

`Kakeya.WindowFour` (`KTWindowThresholds.lean`) is the windowed Katz--Tao multiplicity bound at
window radius `4` with both of its thresholds named.  This file adds the two monotonicity
properties that let *one* threshold pair serve a whole interval of Katz--Tao exponents, the
predicate `Kakeya.UniformWindowPair` saying that a pair does so, and the Skolemisation
`Kakeya.windowPairData` of that predicate together with the three facts about it that hold
**unconditionally**.

## Why this file sits where it does

`Kakeya.VeryNotSticky` carries the window pair as a field (`Kakeya.CoarseKTData`), so the
predicate and the Skolem constant have to be stated *above* `VeryNotSticky.lean`.  They can be:
`KTWindowThresholds.lean` imports `Kakeya.PartialEstimatesWindowed` and nothing else, and its
`namespace VeryNotSticky` is a namespace, **not** a dependency — the import closure was measured,
not guessed.

What is deliberately **not** here is `Kakeya.exists_uniformWindowPair`, the theorem that the
predicate is inhabited.  That rests on `Kakeya.VNSUniform.estimateSet_shape`, which lives far
downstream, and it is not needed to *state* anything: `Kakeya.windowPairData_fst_pos`,
`Kakeya.windowPairData_snd_pos` and `Kakeya.windowPairData_snd_le_half` hold in **both** branches
of the `dite`, so the configuration's clauses are statable — and satisfiable — before the
existence proof is in scope.  That separation is the whole reason the field can be an *input* to
a producer rather than an obligation on it.
-/

@[expose] public section

universe u

open MeasureTheory Metric Set ShadedBody Filter Topology
open scoped ENNReal NNReal

namespace Kakeya

/-- **The windowed Katz–Tao bound transports upward in the exponent, at the same thresholds.**

If `Kakeya.WindowFour E β ε ηKT ρ₀` holds and `β ≤ β' ≤ 1`, then `WindowFour E β' ε ηKT ρ₀`
holds — *with the same `ηKT` and the same `ρ₀`*.

The whole content is `Kakeya.maxDensity_le_card`: writing `Δ = Δ_max(s, W)` and `N = |s|`, the
conclusion's right-hand factor is `Δ^{1-β} N^{β} = Δ · (N/Δ)^{β}` and `Δ ≤ N`, so it is
nondecreasing in `β`.  Nothing about `Kakeya.KatzTaoEstimate` is used, and no threshold moves.

This is what makes a *single* pair of thresholds serve a whole window `[β₀, 1]`; see
`Kakeya.windowFour_uniform_of_katzTao`. -/
theorem WindowFour.mono_beta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {β β' ε ηKT : ℝ} {ρ₀ : NNReal} (hββ' : β ≤ β') (hβ'1 : β' ≤ 1)
    (h : WindowFour.{u} E β ε ηKT ρ₀) : WindowFour.{u} E β' ε ηKT ρ₀ := by
  intro ρ hρ0 hρ₀ τ hτ0 hτρ ι s T hball hfull
  refine le_trans (h ρ hρ0 hρ₀ τ hτ0 hτρ s T hball hfull) ?_
  set D : ENNReal := maxDensity s (fun i ↦ (T i).toConvexSpaceBody) with hD
  set N : ENNReal := (s.card : ENNReal) with hN
  have hDN : D ≤ N := by rw [hD, hN]; exact maxDensity_le_card s _
  have hDtop : D ≠ ⊤ := by rw [hD]; exact maxDensity_ne_top s _
  have hNtop : N ≠ ⊤ := by rw [hN]; exact ENNReal.natCast_ne_top _
  have key : D ^ (1 - β) * N ^ β ≤ D ^ (1 - β') * N ^ β' := by
    rcases eq_or_lt_of_le hββ' with heq | hlt
    · subst heq; exact le_rfl
    have hβ1 : β < 1 := lt_of_lt_of_le hlt hβ'1
    rcases eq_or_ne D 0 with hD0 | hD0
    · rw [hD0, ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < 1 - β)]
      simp
    rcases eq_or_ne N 0 with hN0 | hN0
    · exact absurd (le_antisymm (hN0 ▸ hDN) zero_le) hD0
    have hsplit : D ^ (1 - β) = D ^ (1 - β') * D ^ (β' - β) := by
      rw [← ENNReal.rpow_add _ _ hD0 hDtop]
      congr 1
      ring
    have hjoin : N ^ (β' - β) * N ^ β = N ^ β' := by
      rw [← ENNReal.rpow_add _ _ hN0 hNtop]
      congr 1
      ring
    calc D ^ (1 - β) * N ^ β = D ^ (1 - β') * D ^ (β' - β) * N ^ β := by rw [hsplit]
      _ ≤ D ^ (1 - β') * N ^ (β' - β) * N ^ β := by gcongr
      _ = D ^ (1 - β') * (N ^ (β' - β) * N ^ β) := by rw [mul_assoc]
      _ = D ^ (1 - β') * N ^ β' := by rw [hjoin]
  calc (τ : ENNReal) ^ (-ε) * D ^ (1 - β) * N ^ β
      = (τ : ENNReal) ^ (-ε) * (D ^ (1 - β) * N ^ β) := by rw [mul_assoc]
    _ ≤ (τ : ENNReal) ^ (-ε) * (D ^ (1 - β') * N ^ β') := by gcongr
    _ = (τ : ENNReal) ^ (-ε) * D ^ (1 - β') * N ^ β' := by rw [mul_assoc]


/-- **The windowed bound transports upward in the loss exponent.**  `τ ≤ ρ₀ ≤ 1` makes
`τ^{-ε}` nondecreasing in `ε`, so a bound at loss `ε` is a bound at every larger loss `ε'`.

Together with `Kakeya.WindowFour.mono_beta` this is what lets a *single* pair, chosen at the
bottom of a window and at the smallest loss exponent the window uses, serve every `(β, ν)` the
case split reads. -/
theorem WindowFour.mono_eps {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {β ε ε' ηKT : ℝ} {ρ₀ : NNReal} (hρ₀ : ρ₀ ≤ 1) (hεε' : ε ≤ ε')
    (h : WindowFour.{u} E β ε ηKT ρ₀) : WindowFour.{u} E β ε' ηKT ρ₀ := by
  intro ρ hρ0 hρ₀' τ hτ0 hτρ ι s T hball hfull
  refine le_trans (h ρ hρ0 hρ₀' τ hτ0 hτρ s T hball hfull) ?_
  have hτ1 : (τ : ENNReal) ≤ 1 := by
    have : τ ≤ 1 := le_trans hτρ (le_trans hρ₀' hρ₀)
    exact_mod_cast this
  refine mul_le_mul_right' (mul_le_mul_right' ?_ _) _
  exact ENNReal.rpow_le_rpow_of_exponent_ge hτ1 (by linarith)


/-- **A threshold pair that serves a whole window.**

`p.1` is a fullness exponent and `p.2` a radius threshold such that the windowed Katz--Tao bound
at loss `ε` holds at **every** `β ∈ [β₀, 1]` at which both partial estimates hold.  The two
positivity clauses and `p.2 ≤ 1/2` are what the consumer
`Kakeya.VeryNotSticky.coarseKatzTaoBound_general_at` asks of its thresholds. -/
def UniformWindowPair (β₀ ε : ℝ) (p : ℝ × NNReal) : Prop :=
  0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧
    ∀ β ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) β ε p.1 p.2

open Classical in
/-- **The Skolemized uniform pair.**  A named `(ηKT, ρ₀)` depending only on the window bottom
`β₀` and the loss exponent `ε` — and, unlike `Kakeya.VeryNotSticky.coarseKTEta`, **not** on the
exponent `β` at which it is used.  That `β`-independence is the whole point: the clause
`2η ≤ exscal · (windowPairData β₀ ε).1` mentions no `β`, so
`Kakeya.VNSUniform.CaseParams.mono_beta` carries it without any monotonicity in `β`, which is
the step that defeated the `Kakeya.VeryNotSticky.coarseKTEta` formulation. -/
noncomputable def windowPairData (β₀ ε : ℝ) : ℝ × NNReal :=
  if h : ∃ p : ℝ × NNReal, UniformWindowPair.{u} β₀ ε p then h.choose else (1, 1 / 2)

/-- The fullness exponent is positive in **both** branches, hence unconditionally.  This is what
lets the parameter package bound `η` by it at a point where no Katz--Tao hypothesis is in scope,
exactly as `Kakeya.VeryNotSticky.coarseKTEta_pos'` does for the pointwise threshold. -/
theorem windowPairData_fst_pos (β₀ ε : ℝ) : 0 < (windowPairData.{u} β₀ ε).1 := by
  classical
  rw [windowPairData]
  split
  · rename_i h; exact h.choose_spec.1
  · norm_num

/-- The radius threshold is positive in both branches, hence unconditionally. -/
theorem windowPairData_snd_pos (β₀ ε : ℝ) : 0 < (windowPairData.{u} β₀ ε).2 := by
  classical
  rw [windowPairData]
  split
  · rename_i h; exact h.choose_spec.2.1
  · norm_num

/-- The radius threshold is at most `1/2` in both branches, hence unconditionally. -/
theorem windowPairData_snd_le_half (β₀ ε : ℝ) : (windowPairData.{u} β₀ ε).2 ≤ 1 / 2 := by
  classical
  rw [windowPairData]
  split
  · rename_i h; exact h.choose_spec.2.2.1
  · norm_num

/-- **A hypothesis that sits inside the innermost binder may be assumed outside all of them**, at
GWZ Lemma 9.1's binder shape.

`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` chooses `ν` and `η` *before* its
`KatzTaoEstimate β →`, which is why an upper bound on `η` involving a quantity produced by
`K_KT(β)` looks unarrangeable.  It is arrangeable: the hypothesis is a `Prop`, so `Classical.em`
splits on it outside the existentials — if it fails every instance is vacuous and any witnesses
serve, and if it holds its proof is in scope before the witnesses are chosen.  **No statement is
weakened**: the conclusion is the unweakened one.

(`Kakeya.VeryNotSticky.coarseKTEta_pos'` sidesteps the same obstruction differently, by making
the threshold positive in both branches of its `Classical.choose`.  The two are complementary:
that one gives positivity without `K_KT`, this one gives the *specification* without reordering
the statement.) -/
theorem lemma91_shape_of_imp {P : Prop} {R : ℝ → ℝ → ℝ → ℝ → Prop}
    (h : P → ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ), R ϖ ζ ν η) :
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ), P → R ϖ ζ ν η := by
  by_cases hP : P
  · obtain ⟨ϖ, hϖ, hrest⟩ := h hP
    refine ⟨ϖ, hϖ, fun ζ hζ ↦ ?_⟩
    obtain ⟨ν, hν, η, hη, hR⟩ := hrest ζ hζ
    exact ⟨ν, hν, η, hη, fun _ ↦ hR⟩
  · exact ⟨1, one_pos, fun _ _ ↦ ⟨1, one_pos, 1, one_pos, fun hp ↦ absurd hp hP⟩⟩


end Kakeya

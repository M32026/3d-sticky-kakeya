/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterUniformity
public import Kakeya.Tube.CardEssentiallyDistinct

/-!
# The packing ceiling for essentially distinct tubes, and the exponent bound it forces

condition of record:.  The tree states count **lower** bounds
`ρ^{-2-ζ'} ≤ #t` in every count clause it carries and had no **upper** companion, so nothing in it
contradicted an arbitrarily large `ζ'` — and a regime `ζ' > 72` was read as available when it is
not.  This leaf supplies the missing side.

## What is provable here, and what is not

The ceiling is `Kakeya.Tube.card_le_of_EssDistinct` (existing, axiom-clean), which counts a pairwise
essentially distinct family of `δ`-tubes inside `B̄(0,r)` by
`card_le_of_EssDistinct.C n · (r/δ)^{2n}` — in `ℝ³`, **exponent `6`**.

That is *not* the sharp exponent, and the difference matters for what may be claimed.  A unit-core
`ρ`-tube in the unit ball is fixed by four parameters — two for the direction, two for the
perpendicular foot — so the geometric count is `≍ ρ^{-4}`, and the existing lemma's own docstring says
as much ("the geometrically expected count grows like `(r/δ)^n`, whereas this estimate gives the
much larger exponent `2n`").  Deriving `ρ^{-4}` would be a **new packing theorem**, not a
citation.  So the ceiling below is stated at the exponent the tree actually proves, and the
exponent bound it forces is `ζ' ≤ 4` rather than `ζ' ≤ 2`.  That is weaker than the sharp bound and
it is *derived*, which is what §AA asks for; it forecloses the collision either way.

## The collision it forecloses

`Kakeya.ML2Reduction.spineRung_gainBudget_sharp` and its neighbours read a count clause at an
exponent `ζ'` that the rung ledger is free to make large.  With `exists_threshold_exponent_le_four`
no such reading survives below the threshold: a family that satisfies the count clause at any
`ζ' > 4` cannot be essentially distinct inside the unit ball at a small enough scale.  In
particular `ζ' > 72` is impossible, and the regime is closed by the compiler rather than by a
reader's judgement.

## Main declarations

* `Kakeya.VeryNotSticky.edPackingCeilingConstant` — the absolute constant, **derived** from
  `Tube.card_le_of_EssDistinct.C 3` and not chosen; `_eq` gives its value `78^6 + 1`.
* `Kakeya.VeryNotSticky.card_le_edPackingCeiling` — the ceiling, at the unit ball.
* `Kakeya.VeryNotSticky.exists_threshold_exponent_le_four` — the exponent bound: below an explicit
  threshold, a count clause at `ζ'` over an essentially distinct family in the unit ball forces
  `ζ' ≤ 4`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

/-- **The packing ceiling's constant**, derived from `Kakeya.Tube.card_le_of_EssDistinct.C` at the
ambient dimension `3` — not chosen.  Its value is `78^6 + 1` (`edPackingCeilingConstant_eq`). -/
noncomputable def edPackingCeilingConstant : ℝ := Tube.card_le_of_EssDistinct.C 3

theorem edPackingCeilingConstant_eq : edPackingCeilingConstant = 78 ^ 6 + 1 := by
  unfold edPackingCeilingConstant Tube.card_le_of_EssDistinct.C
  norm_num

theorem one_le_edPackingCeilingConstant : (1 : ℝ) ≤ edPackingCeilingConstant := by
  rw [edPackingCeilingConstant_eq]; norm_num

theorem edPackingCeilingConstant_pos : (0 : ℝ) < edPackingCeilingConstant :=
  lt_of_lt_of_le zero_lt_one one_le_edPackingCeilingConstant

/-- **The packing ceiling.**  A pairwise essentially distinct family of `ρ`-tubes whose carriers
all lie in the **unit ball** has at most `edPackingCeilingConstant · ρ^{-6}` members.

This is `Kakeya.Tube.card_le_of_EssDistinct` at `r = 1` and `n = 3`, with the `(1/ρ)^6` written as
the `rpow` the count clauses use.  The exponent is the existing lemma's `2n`, not the sharp `n + 1`
that the four line parameters of a unit-core tube in `ℝ³` would give; see the module docstring. -/
theorem card_le_edPackingCeiling {ρ : NNReal} (hρ0 : 0 < ρ)
    {ι : Type*} (s : Finset ι) (T : ι → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hED : (s : Set ι).Pairwise
      fun i j ↦ _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    (s.card : ℝ) ≤ edPackingCeilingConstant * (ρ : ℝ) ^ (-(6 : ℝ)) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρr : (0 : ℝ) < (ρ : ℝ) := hρ0
  have h := Tube.card_le_of_EssDistinct (E := EuclideanSpace ℝ (Fin 3)) hρ0 1 s T hball hED
  rw [hfr] at h
  refine h.trans (le_of_eq ?_)
  have hpow : ((1 : ℝ) / (ρ : ℝ)) ^ (2 * 3) = (ρ : ℝ) ^ (-(6 : ℝ)) := by
    rw [Real.rpow_neg hρr.le, show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div, ← inv_pow]
  rw [hpow]
  rfl

/-- **The exponent bound the ceiling forces**.

Below an explicit threshold, no essentially distinct family in the unit ball can satisfy a count
clause `ρ^{-2-ζ'} ≤ #s` with `ζ' > 4`: the clause would need more tubes than fit.  The threshold is
the standard absolute-constant-as-threshold device
(`Kakeya.ML2Reduction.exists_threshold_const_le_rpow_neg`), and it depends only on `ζ'` and on the
absolute `edPackingCeilingConstant`.

The bound is `ζ' ≤ 4` because the existing ceiling's exponent is `6 = 2n`; the sharp ceiling
`ρ^{-4}` would give `ζ' ≤ 2`.  Either way `ζ' > 72` is foreclosed. -/
theorem exists_threshold_exponent_le_four (ζ' : ℝ) :
    ∃ ρ₀ : NNReal, 0 < ρ₀ ∧ ∀ ρ : NNReal, 0 < ρ → ρ ≤ ρ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        ((s : Set ι).Pairwise
          fun i j ↦ _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (ρ : ℝ) ^ (-2 - ζ') ≤ (s.card : ℝ) →
        ζ' ≤ 4 := by
  by_cases hζ : ζ' ≤ 4
  · exact ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ ↦ hζ⟩
  rw [not_le] at hζ
  set K : NNReal := ⟨edPackingCeilingConstant, edPackingCeilingConstant_pos.le⟩ + 1 with hK
  have hK1 : (1 : NNReal) ≤ K := by
    rw [hK]; exact le_add_self
  obtain ⟨ρ₀, hρ₀0, hthr⟩ :=
    Kakeya.ML2Reduction.exists_threshold_const_le_rpow_neg hK1 (by linarith : (0 : ℝ) < ζ' - 4)
  refine ⟨ρ₀, hρ₀0, ?_⟩
  intro ρ hρ0 hρle ι s T hball hED hcount
  exfalso
  have hρr : (0 : ℝ) < (ρ : ℝ) := hρ0
  have hceil := card_le_edPackingCeiling hρ0 s T hball hED
  -- `ρ^{-2-ζ'} ≤ K₀ · ρ^{-6}`, so `ρ^{4-ζ'} ≤ K₀`
  have hcomb : (ρ : ℝ) ^ (-2 - ζ') ≤ edPackingCeilingConstant * (ρ : ℝ) ^ (-(6 : ℝ)) :=
    hcount.trans hceil
  have hsplit : (ρ : ℝ) ^ (-2 - ζ') = (ρ : ℝ) ^ (4 - ζ') * (ρ : ℝ) ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_add hρr]
    congr 1
    ring
  have hpow6 : (0 : ℝ) < (ρ : ℝ) ^ (-(6 : ℝ)) := Real.rpow_pos_of_pos hρr _
  have hle : (ρ : ℝ) ^ (4 - ζ') ≤ edPackingCeilingConstant := by
    rw [hsplit] at hcomb
    exact le_of_mul_le_mul_right (by linarith [hcomb]) hpow6
  -- the threshold says the same quantity is at least `K = ceiling + 1`
  have hge := hthr ρ hρ0 hρle
  have hgeR : (K : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - 4)) := by
    have h1 : ((K : NNReal) : ℝ) ≤ ((ρ ^ (-(ζ' - 4)) : NNReal) : ℝ) := by exact_mod_cast hge
    rwa [NNReal.coe_rpow] at h1
  have hKR : (K : ℝ) = edPackingCeilingConstant + 1 := by
    rw [hK, NNReal.coe_add, NNReal.coe_one]
    rfl
  have hneg : (-(ζ' - 4)) = 4 - ζ' := by ring
  rw [hneg, hKR] at hgeR
  linarith

end Kakeya.VeryNotSticky

end

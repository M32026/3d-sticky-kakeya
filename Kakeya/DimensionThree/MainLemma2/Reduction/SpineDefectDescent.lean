/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.ENNReal

/-!
# The abstract defect descent 

The refined source runs its Main-Lemma-2 argument as a **loop**, not as a single shot.  One
*trial* (`lem:defect-one-trial`, l.5793–5851 of
`prof_ma_refined/260115_kakeyadetailedproofv3_revised_detailed.tex`) consumes a shaded family and
returns one of two alternatives,

* `(G)`  a terminal bound `μ(𝕊,Z) ≤ Λ δ^{-ω} δ^{ν₀} (#𝕊)^β`, or
* `(B)`  a nonempty subfamily `𝕊* ⊆ 𝕊` with a sub-shading `Z*` such that
  `μ(𝕊,Z) ≤ Λ μ(𝕊*,Z*)`, `λ(𝕊*,Z*) ≥ Λ⁻¹ λ(𝕊,Z)` and `Φ_h(𝕊*) ≤ Φ_h(𝕊) − 1`,

and the outer induction (l.5949–5975) runs on the ceiling `P = 0,…,P_max` of the potential:

```
 Φ_h(𝕊) ≤ P  and  λ(𝕊,Z) ≥ Λ^{P−P_max} δ^{η₀}
   ⟹  μ(𝕊,Z) ≤ Λ^{P+1} δ^{-ω} δ^{ν₀} (#𝕊)^β.
```

This file is that induction and **nothing else**: the potential `Φ`, its ceiling `P`, the loss
`Λ`, the fullness `lam`, the mass `μ` and the two terminal right-hand sides `A`, `B` are all
*parameters*.  No tube, no cover, no shading occurs anywhere in the statements, so the file
compiles against `Kakeya.Mathlib.ENNReal` alone and is independent of the geometric potential of
`Kakeya.ML2Core.potential` (`SpineDefectPotential.lean`) — which is the point: the descent may be
checked before the potential exists, and the potential may be replaced without touching the
descent.

Two terminal right-hand sides rather than one, because the tree's
`Kakeya.ML2Assembly.Dichotomy` is a disjunction: `A` carries the sticky exit
`δ^{-ε₀}·vol(⋃)` and `B` the gain exit `δ^{g}·(#𝕊)^{β}·vol(⋃)`.  Both must be **monotone along
the descent** (`A y ≤ A x`), which they are: `𝕊* ⊆ 𝕊` and `Z*(T) ⊆ Z(T)` shrink both the
cardinality and the volume of the union.

## The fullness ladder, and why it is stated multiplicatively

The source writes the induction hypothesis as `λ ≥ Λ^{P−P_max} δ^{η₀}` with a *negative* power of
`Λ`.  In `ℝ≥0∞` that is `lam0 ≤ Λ^(P − Φ x) * lam x` with truncated subtraction and no division,
which is the form used here.  A descent step consumes exactly one power: from
`lam x ≤ Λ * lam y` and `Φ y + 1 ≤ Φ x` one gets the ladder at `y`, because
`P − Φ y ≥ (P − Φ x) + 1`.

## Contents

* `Kakeya.ML2Core.gain_of_trialDescent` — the strong induction on `Φ`;
* `Kakeya.ML2Core.gain_of_trialDescent_top` — its top-level form, with the accumulated factor
  flattened to `Λ ^ P`;
* `Kakeya.ML2Core.gain_of_trialDescent_single` — the degenerate case `Φ ≡ 0`, which is the
  existing single-shot route (compatibility `T-D3`).
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## The descent -/

section Descent

variable {σ : Type*}

/-- **The abstract defect descent** (refined source l.5949–5975).

`htrial` is one trial: on an admissible state whose fullness is on the ladder, either a terminal
bound holds (`μ x ≤ A x` or `μ x ≤ B x`), or there is a *child* `y` — admissible, of strictly
smaller potential — paying one factor `Λ` in the mass and one in the fullness, and not increasing
either terminal right-hand side.

The conclusion accumulates exactly `Λ ^ Φ x`, so the ceiling `P` is spent only through the
ladder.  Note that no separate base case is assumed: at `Φ x = 0` the alternative `(B)` is
*unavailable* because `Φ y + 1 ≤ 0` is impossible in `ℕ`, which is the source's "(B) is impossible
at `P = 0`" (l.5964–5966). -/
theorem gain_of_trialDescent {Adm : σ → Prop} {Φ : σ → ℕ} {P : ℕ}
    {lam μ A B : σ → ℝ≥0∞} {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ)
    (hΦP : ∀ x, Adm x → Φ x ≤ P)
    (htrial : ∀ x, Adm x → lam0 ≤ Λ ^ (P - Φ x) * lam x →
      (μ x ≤ A x ∨ μ x ≤ B x) ∨
        ∃ y, Adm y ∧ Φ y + 1 ≤ Φ x ∧ μ x ≤ Λ * μ y ∧ lam x ≤ Λ * lam y ∧
          A y ≤ A x ∧ B y ≤ B x) :
    ∀ x, Adm x → lam0 ≤ Λ ^ (P - Φ x) * lam x →
      μ x ≤ Λ ^ Φ x * A x ∨ μ x ≤ Λ ^ Φ x * B x := by
  have hterm : ∀ x : σ, (μ x ≤ A x ∨ μ x ≤ B x) →
      μ x ≤ Λ ^ Φ x * A x ∨ μ x ≤ Λ ^ Φ x * B x := by
    intro x hx
    have hone : (1 : ℝ≥0∞) ≤ Λ ^ Φ x := one_le_pow_of_one_le' hΛ _
    rcases hx with h | h
    · exact Or.inl (h.trans (le_mul_of_one_le_left' hone))
    · exact Or.inr (h.trans (le_mul_of_one_le_left' hone))
  -- induction on a fuel bounding the potential: the source's `P = 0,…,P_max`
  suffices H : ∀ n : ℕ, ∀ x, Φ x ≤ n → Adm x → lam0 ≤ Λ ^ (P - Φ x) * lam x →
      μ x ≤ Λ ^ Φ x * A x ∨ μ x ≤ Λ ^ Φ x * B x by
    exact fun x hx hlad => H (Φ x) x le_rfl hx hlad
  intro n
  induction n with
  | zero =>
    intro x hxn hx hlad
    rcases htrial x hx hlad with h | ⟨y, _, hstep, _⟩
    · exact hterm x h
    · omega
  | succ n ih =>
    intro x hxn hx hlad
    rcases htrial x hx hlad with h | ⟨y, hy, hstep, hmass, hfull, hA, hB⟩
    · exact hterm x h
    · -- the ladder transports to the child: one power of `Λ` buys one unit of potential
      have hPx : Φ x ≤ P := hΦP x hx
      have hPy : (P - Φ x) + 1 ≤ P - Φ y := by omega
      have hlady : lam0 ≤ Λ ^ (P - Φ y) * lam y := by
        refine hlad.trans ?_
        calc Λ ^ (P - Φ x) * lam x ≤ Λ ^ (P - Φ x) * (Λ * lam y) := mul_le_mul' le_rfl hfull
          _ = Λ ^ ((P - Φ x) + 1) * lam y := by ring
          _ ≤ Λ ^ (P - Φ y) * lam y := mul_le_mul' (pow_le_pow_right' hΛ hPy) le_rfl
      have hres := ih y (by omega) hy hlady
      have hpow : Λ ^ (Φ y + 1) ≤ Λ ^ Φ x := pow_le_pow_right' hΛ hstep
      rcases hres with h | h
      · refine Or.inl (hmass.trans ?_)
        calc Λ * μ y ≤ Λ * (Λ ^ Φ y * A y) := mul_le_mul' le_rfl h
          _ = Λ ^ (Φ y + 1) * A y := by ring
          _ ≤ Λ ^ Φ x * A x := mul_le_mul' hpow hA
      · refine Or.inr (hmass.trans ?_)
        calc Λ * μ y ≤ Λ * (Λ ^ Φ y * B y) := mul_le_mul' le_rfl h
          _ = Λ ^ (Φ y + 1) * B y := by ring
          _ ≤ Λ ^ Φ x * B x := mul_le_mul' hpow hB

/-- **The descent, read at the top of the ladder.**

At the top the fullness hypothesis is the plain floor `lam0 ≤ lam x` (the source's
`λ(𝕋,Y) ≥ δ^{η₀}`, l.5969–5971) and the accumulated factor is flattened to `Λ ^ P`, which is the
`Λ^{P_max+1} ≤ δ^{-a₀}` the loop's ledger absorbs (l.5944–5948). -/
theorem gain_of_trialDescent_top {Adm : σ → Prop} {Φ : σ → ℕ} {P : ℕ}
    {lam μ A B : σ → ℝ≥0∞} {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ)
    (hΦP : ∀ x, Adm x → Φ x ≤ P)
    (htrial : ∀ x, Adm x → lam0 ≤ Λ ^ (P - Φ x) * lam x →
      (μ x ≤ A x ∨ μ x ≤ B x) ∨
        ∃ y, Adm y ∧ Φ y + 1 ≤ Φ x ∧ μ x ≤ Λ * μ y ∧ lam x ≤ Λ * lam y ∧
          A y ≤ A x ∧ B y ≤ B x) :
    ∀ x, Adm x → lam0 ≤ lam x → μ x ≤ Λ ^ P * A x ∨ μ x ≤ Λ ^ P * B x := by
  intro x hx hlam
  have hlad : lam0 ≤ Λ ^ (P - Φ x) * lam x :=
    hlam.trans (le_mul_of_one_le_left' (one_le_pow_of_one_le' hΛ _))
  have hpow : Λ ^ Φ x ≤ Λ ^ P := pow_le_pow_right' hΛ (hΦP x hx)
  rcases gain_of_trialDescent hΛ hΦP htrial x hx hlad with h | h
  · exact Or.inl (h.trans (mul_le_mul' hpow le_rfl))
  · exact Or.inr (h.trans (mul_le_mul' hpow le_rfl))

/-- **compatibility `T-D3`: at potential `0` the wrapper *is* the existing single-shot route.**

With `Φ ≡ 0` and `P = 0` the trial's `(B)` alternative is vacuous and the conclusion is the
terminal bound with no accumulated loss at all.  If this ever stops being provable, the descent's
shape has drifted from the single-shot statement it is meant to generalise. -/
theorem gain_of_trialDescent_single {Adm : σ → Prop} {lam μ A B : σ → ℝ≥0∞} {Λ lam0 : ℝ≥0∞}
    (hΛ : 1 ≤ Λ)
    (htrial : ∀ x, Adm x → lam0 ≤ lam x → μ x ≤ A x ∨ μ x ≤ B x) :
    ∀ x, Adm x → lam0 ≤ lam x → μ x ≤ A x ∨ μ x ≤ B x := by
  intro x hx hlam
  have := gain_of_trialDescent (Adm := Adm) (Φ := fun _ ↦ 0) (P := 0) (lam := lam) (μ := μ)
    (A := A) (B := B) (Λ := Λ) (lam0 := lam0) hΛ (fun _ _ ↦ le_rfl)
    (fun z hz hl ↦ Or.inl (htrial z hz (by simpa using hl))) x hx (by simpa using hlam)
  simpa using this

end Descent

end Kakeya.ML2Core

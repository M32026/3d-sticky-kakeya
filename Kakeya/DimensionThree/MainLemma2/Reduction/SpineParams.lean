/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The parameter spine of the proof of GWZ Main Lemma 2

This module carries the *parameter-selection step* of the blueprint proof of Main Lemma 2
(`blueprint/src/GWZAdapted/section9.tex`, the block "Proof of Main Lemma~\ref{lemmain2}"), and
nothing else: every declaration below is a statement about real numbers and natural numbers.
There is no tube, no shading, no plank and no measure.

## What the blueprint asks for

Fix `β ∈ (0, 1]`.  The proof names, in dependency order,

* `ε₁`, the Katz--Tao exponent produced by Theorem 7.3(B)
  (`katzTaoAtEveryScaleImpliesMultSmall`) at some accuracy;
* `ϖ = ϖ(β) > 0`, the scale-window exponent of Lemma 9.1 (`lemmain2vns`, in Lean
  `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`), together with the two exponents
  `ν(β, ζ) > 0` and `η(β, ζ) > 0` that Lemma 9.1 produces at each `ζ > 0`;
* `ε₂ = ε₂(ε₁, ϖ, β)`, subject to `ε₂ ≤ ε₁/5` and `ε₂ ≤ ϖ/2`;
* `N = ⌈25/ε₂²⌉` and the dividing-scales exponent `e = 1/√N` of Lemma
  `dividingScalesLemmaB` (`section7.tex`, which *sets* `ε = 1/√N`).  The Lean form of that
  lemma, `StickyKakeya.dividingScalesKatzTao`, additionally demands `4096 ≤ N`; see
  the section "The `4096` threshold" below;
* a chain `η = η₀ ≤ η₁ ≤ … ≤ η_N ≤ e`, each rung "very small depending on `η_{j+1}`, `ε₂`
  and `β`";
* the gain `ν` of Main Lemma 2 itself, "selected small compared to `η₁`".

The constraints the proof imposes on the chain, collected from the text, are

1. `ε₂ ≤ ε₁/5` — so that conclusion (i) of the dividing-scales lemma is `δ^{-ε₁}` Katz--Tao at
   every scale and Theorem 7.3(B) applies;
2. `ε₂ ≤ ϖ/2` — so that after rescaling `T_b` to `B₁` the window `[(δ')^{1-ϖ}, (δ')^{ϖ}]` of
   Lemma 9.1 sits inside the window `[δ̃^{1-ε₂}, δ̃^{ε₂}]` on which the count bound is known.
   The arithmetic content of that inclusion is `ε₂ (1 + ϖ) ≤ ϖ`, which is the field
   `IsSpine.window_fits`;
3. with `η'_{j-1} := 12 η_{j-1}/(e β)` (the blueprint's eccentricity threshold, written there
   with `ε₂` in the denominator; see the note on denominators below), the separation
   `η'_{j-1} ≤ e η_j / 4`.  The blueprint asks only `η'_{j-1} ≤ η_j ε₂`, which is what forces
   `b ≥ δ̃^{ε₂}` by contradiction with `Δ_max(𝕋̃_ρ) ≥ ρ^{-η_j}`; the sharper `/4` is what the
   count hypothesis of Lemma 9.1 needs, since `δ̃^{2 η'_{j-1}} ≥ σ^{η_j/2}` for
   `σ ≤ δ̃^{e}` requires `2 η'_{j-1} ≤ e η_j / 2`;
4. the eccentric case is pure exponent arithmetic and imposes *no* constraint: by the very
   definition of `η'_{j-1}`,
   `-2 η_{j-1}/e + β η'_{j-1} = 10 η_{j-1}/e`, which is `IsSpine.eccentric_exponent`;
5. `ν(β, η_j/2) - 2 η'_{j-1} ≥ 10 η_{j-1}/e` in the non-eccentric case
   (`IsSpine.gain_budget`);
6. `η_{j-1}/e ≤ η(β, η_j/2)/2`, which is what makes `Δ_max(𝕋̃[T_b]) ≤ δ̃^{-η'}` hold for the
   density exponent `η'` of Lemma 9.1 at `ζ = η_j/2`, with room to spare for the passage from
   `δ̃` to `δ' = δ̃/b ≤ δ̃^{1-ε₂}` (`IsSpine.dens_budget`);
7. `ν ≤ η₁`;
8. `4096 ≤ N` (`IsSpine.four_thousand_le_stepCount`), which is not in the blueprint text but is
   a hypothesis of the Lean statement of the dividing-scales lemma — see the next section.

## The `4096` threshold

`StickyKakeya.dividingScalesKatzTao`, this development's GWZ Lemma 7.7(B), carries the
hypothesis `hN : 4096 ≤ N`.  The blueprint hides that constant inside "let `N` be large
enough", but in Lean it is a real side condition, and a spine that cannot supply it cannot be
fed to the dichotomy at all: `stepCount_eq` together with a cap `ε₂ ≤ 1/2` yields only
`N = ⌈25/ε₂²⌉ ≥ 100`.  So `4096 ≤ N` is a field of `IsSpine`, and the witness `spineEps₂` is
capped at `1/64` rather than `1/2`, which gives `N ≥ 25 · 64² = 102400`
(`Kakeya.ML2Spine.hundredThousand_le_spineCount`).  Tightening the cap costs nothing: `ε₂` is
free to be as small as one likes, every constraint on it is an upper bound, and the derived
quantities only improve (`e = 1/√N ≤ ε₂/5 ≤ 1/320`).

## `ε₂` versus `e = 1/√N`: a repair, not a change of numerals

The blueprint writes `ε₂` in the denominator of every exponent of the middle scale, and also
writes `δ̃ ≤ δ^{ε₂}`.  Those two are not simultaneously available: Lemma
`dividingScalesLemmaB` is applied with *its* exponent `ε = 1/√N`, and what it returns is
`τ ≤ δ^{1/√N} θ`, i.e. `δ̃ ≤ δ^{e}` with `e = 1/√N ≤ ε₂/5`, which is *weaker* than
`δ̃ ≤ δ^{ε₂}`.  Since `e ≤ ε₂`, replacing `ε₂` by `e` in every denominator makes each
constraint strictly *harder*, and the resulting parameters therefore satisfy the blueprint's
`ε₂`-form as well.  Both forms are recorded: the fields of `IsSpine` are stated with `e`, and
`IsSpine.sep_eps₂`, `IsSpine.gain_budget_eps₂`, `IsSpine.dens_budget_eps₂` derive the
`ε₂`-form from them.  Likewise the window of the dividing-scales lemma is
`[δ̃^{1-e}, δ̃^{e}] ⊇ [δ̃^{1-ε₂}, δ̃^{ε₂}]`, so a hypothesis known on the `ε₂`-window is known
on the `e`-window only in the easy direction; every clause below is stated so that the
consumer may use whichever of the two it holds.

## `ν` does not depend on `ε` (Prof. Hong Wang, 2026-08-30)

The published proof reads `ε₁` as the output of Theorem 7.3(B) *at the outer accuracy `ε`*,
which would make `ε₂`, `N`, the chain and `ν` all depend on `ε`; the parenthesis "since `ε₁`
and `ϖ` depend only on `β`, `ε₂` depends only on `β`" is then false, and the statement of Main
Lemma 2, whose `ν = ν(β)` is fixed before `ε`, cannot be reached.  The correction is that
Theorem 7.3(B) is applied at an **absolute** accuracy `ε₀`, here `Kakeya.ML2Spine.absAccuracy β
= β/2`, a function of `β` alone.

Two declarations make this a theorem rather than a comment.

* `Kakeya.ML2Spine.spineNu` is a definition whose argument list *does not contain `ε`*, and
  `Kakeya.ML2Spine.exists_ml2SpineParams` binds `ν` **outside** the `∀ ε > 0`.  The `∀ ε` is
  not idle: its body carries the closing inequality of the every-scale branch,
  `absAccuracy β ≤ ε + (β - ν)`, which is what turns the branch bound `μ ≤ δ^{-ε₀}` into the
  goal `μ ≤ δ^{-ε} |𝕋|^{β-ν}` in the presence of `|𝕋| ≥ δ^{-1}`.
* `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` shows the naive reading is *impossible*: if
  the spine is built from `E ε` rather than from `E ε₀`, and `E` takes arbitrarily small
  positive values — which it must, since a Katz--Tao exponent bounded below would give
  `μ ≲ δ^{-o(1)}` outright — then no positive `ν` can be chosen before `ε`.

## Shape of the chain

The chain is a bare `η : ℕ → ℝ` with a global `Monotone η`, not a `Fin (N+1) → ℝ`.  The
consumer receives the index `j` from `dividingScalesLemmaB` as a natural number with
`1 ≤ j ≤ N` and then uses `η (j-1)` and `η j`; with `Fin (N+1)` every one of those uses would
carry a coercion and a `j - 1 < N + 1` obligation, while the recursion that builds the chain
would have to be written on `Fin`.  Extending the chain to all of `ℕ` by the constant value
`e` above the top rung costs nothing — the budget fields are guarded by `k < N` — and buys a
single unconditional `Monotone η`, from which `η i ≤ η j` for any `i ≤ j` and `η k ≤ e` for
*every* `k` follow with no arithmetic side conditions.
-/

@[expose] public section

namespace Kakeya.ML2Spine

/-! ### The specification -/

/-- **The parameter spine of the proof of Main Lemma 2.**

`IsSpine β ϖ ε₁ gain dens ε₂ e N η` says that `(ε₂, e, N, η)` satisfies every constraint the
blueprint proof of Main Lemma 2 imposes, given

* the exponent `β ∈ (0,1]` of the hypotheses `K_KT(β)`, `K_F(β)`;
* the scale-window exponent `ϖ = ϖ(β)` of Lemma 9.1;
* the Katz--Tao exponent `ε₁` of Theorem 7.3(B) — read at an **absolute** accuracy, see the
  module docstring;
* the two exponent functions `gain = ν(β, ·)` and `dens = η(β, ·)` of Lemma 9.1.

`e` is the dividing-scales exponent `1/√N` of `dividingScalesLemmaB`; it is a field rather
than a derived quantity because that lemma quantifies over `N` and *defines* its own `ε` to be
`1/√N`, so the consumer needs the two side by side. -/
structure IsSpine (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ) : Prop where
  /-- `ε₂` is a positive exponent. -/
  eps₂_pos : 0 < ε₂
  /-- `ε₂ ≤ ε₁/5`: conclusion (i) of the dividing-scales lemma is then `δ^{-ε₁}` Katz--Tao at
  every scale, so Theorem 7.3(B) applies in the first branch. -/
  eps₂_le_everyScale : ε₂ ≤ ε₁ / 5
  /-- `ε₂ ≤ ϖ/2`: the rescaled count hypothesis lands inside the window
  `[(δ')^{1-ϖ}, (δ')^{ϖ}]` of Lemma 9.1. -/
  eps₂_le_vnsWindow : ε₂ ≤ ϖ / 2
  /-- `ε₂ ≤ 1/2`.  Kept in this weak form because that is all any consumer spends (it is used
  to turn `δ' ≤ δ̃^{1-ε₂}` into `δ' ≤ δ̃^{1/2}` in `dens_budget`, and to bound `e β ≤ 1`).  The
  sharp cap is a *consequence* of the two fields `stepCount_eq` and
  `four_thousand_le_stepCount` — see `Kakeya.ML2Spine.IsSpine.eps₂_lt_twelfth` — and the
  concrete witness `Kakeya.ML2Spine.spineEps₂` satisfies `ε₂ ≤ 1/64`. -/
  eps₂_le_half : ε₂ ≤ 1 / 2
  /-- The arithmetic content of the window inclusion of `eps₂_le_vnsWindow`: for
  `δ' = δ̃/b ≤ δ̃^{1-ε₂}` and `b ≥ δ̃^{ε₂}`, the image of `[(δ')^{1-ϖ}, (δ')^{ϖ}]` under
  `σ' ↦ σ' b` lies in `[δ̃^{1-ε₂}, δ̃^{ε₂}]` exactly when `ε₂ (1 + ϖ) ≤ ϖ`. -/
  window_fits : ε₂ * (1 + ϖ) ≤ ϖ
  /-- `N = ⌈25/ε₂²⌉`, the number of dividing scales. -/
  stepCount_eq : N = ⌈25 / ε₂ ^ 2⌉₊
  /-- `N ≥ 1`, as `dividingScalesLemmaB` demands. -/
  one_le_stepCount : 1 ≤ N
  /-- `N ≥ 4096`.

  This is the running threshold of the *Lean* form of the dividing-scales lemma:
  `StickyKakeya.dividingScalesKatzTao` (GWZ Lemma 7.7(B)) carries the hypothesis
  `hN : 4096 ≤ N`, and without this field no spine can be fed to it — `stepCount_eq`
  together with `eps₂_le_half` gives only `N = ⌈25/ε₂²⌉ ≥ 100`.  It is not an extra demand
  on the blueprint: `ε₂` is chosen "small enough" there, and `ε₂ ≤ 1/64` already forces
  `25/ε₂² ≥ 102400`.  The witness `Kakeya.ML2Spine.spineEps₂` is capped at `1/64` for
  exactly this reason. -/
  four_thousand_le_stepCount : 4096 ≤ N
  /-- `e = 1/√N` is the exponent `dividingScalesLemmaB` builds from `N`. -/
  div_eq : e = 1 / Real.sqrt (N : ℝ)
  /-- `e` is positive. -/
  div_pos : 0 < e
  /-- `e ≤ ε₂/5`, the consequence of `N ≥ 25/ε₂²`. -/
  div_le : e ≤ ε₂ / 5
  /-- Every rung is positive. -/
  rung_pos : ∀ k, 0 < η k
  /-- The chain is nondecreasing.  Above the top rung it is constant, so this holds on all of
  `ℕ`. -/
  rung_mono : Monotone η
  /-- The top rung is `e`: this is `η_N ≤ ε` of `dividingScalesLemmaB` at its sharpest. -/
  rung_top : η N = e
  /-- Consequently every rung is at most `e` (and hence at most `ε₂/5`). -/
  rung_le_div : ∀ k, η k ≤ e
  /-- **Separation.**  With `η'_{k} = 12 η_k/(e β)` the blueprint's eccentricity threshold,
  `η'_{k} ≤ e η_{k+1}/4`.  The weaker `η'_k ≤ e η_{k+1}` is what forces `b ≥ δ̃^{ε₂}`; the
  factor `4` is what the count hypothesis of Lemma 9.1 needs. -/
  sep_le : ∀ k < N, 12 * η k / (e * β) ≤ e * η (k + 1) / 4
  /-- **The gain budget of the non-eccentric case**: `ν(β, η_{k+1}/2) - 2 η'_k ≥ 10 η_k/e`. -/
  gain_budget : ∀ k < N, 10 * η k / e + 2 * (12 * η k / (e * β)) ≤ gain (η (k + 1) / 2)
  /-- **The density budget**: `Δ_max(𝕋̃[T_b]) ≤ δ̃^{-η_k/e}` must be at most `(δ')^{-η'}` for
  the density exponent `η' = η(β, η_{k+1}/2)` of Lemma 9.1, and `δ' ≤ δ̃^{1-ε₂}` with
  `ε₂ ≤ 1/2`, so `η_k/e ≤ η(β, η_{k+1}/2)/2` suffices. -/
  dens_budget : ∀ k < N, η k / e ≤ dens (η (k + 1) / 2) / 2

namespace IsSpine

variable {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}

/-- `e ≤ ε₂`; immediate from `e ≤ ε₂/5`. -/
theorem div_le_eps₂ (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) : e ≤ ε₂ := by
  have := h.div_le
  have := h.eps₂_pos
  linarith

/-- Every rung is at most `ε₂`, which is the blueprint's `η_N ≤ ε₂`. -/
theorem rung_le_eps₂ (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) (k : ℕ) : η k ≤ ε₂ :=
  (h.rung_le_div k).trans h.div_le_eps₂

/-- The blueprint's chain condition `η = η₀ ≤ η₁ ≤ … ≤ η_N ≤ ε₂`, in one line. -/
theorem chain (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) :
    (∀ k, η k ≤ η (k + 1)) ∧ η N ≤ ε₂ :=
  ⟨fun k ↦ h.rung_mono (Nat.le_succ k), h.rung_le_eps₂ N⟩

/-- **The eccentric case is an identity, not a constraint.**  With `η'_k = 12 η_k/(e β)` and
`a/b ≤ δ̃^{η'_k}`, the eccentric bound reads
`δ̃^{-2 η_k/e} (a/b)^β ≤ δ̃^{-2 η_k/e + β η'_k} = δ̃^{10 η_k/e}`, and the exponent identity
holds by the very definition of `η'_k`. -/
theorem eccentric_exponent (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ : 0 < β) (k : ℕ) :
    -(2 * η k / e) + β * (12 * η k / (e * β)) = 10 * η k / e := by
  have he : e ≠ 0 := ne_of_gt h.div_pos
  field_simp
  ring

/-- The weak form of `sep_le` that the blueprint states: `η'_k ≤ ε₂ η_{k+1}`, which is what
contradicts `Δ_max(𝕋̃_ρ) ≥ ρ^{-η_{k+1}}` unless `b ≥ δ̃^{ε₂}`. -/
theorem sep_le_weak (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N) :
    12 * η k / (e * β) ≤ ε₂ * η (k + 1) := by
  have h1 := h.sep_le k hk
  have hr : 0 < η (k + 1) := h.rung_pos (k + 1)
  have hd : e ≤ ε₂ := h.div_le_eps₂
  have hprod : e * η (k + 1) ≤ ε₂ * η (k + 1) := mul_le_mul_of_nonneg_right hd hr.le
  have hnn : 0 ≤ ε₂ * η (k + 1) := (mul_pos h.eps₂_pos hr).le
  linarith

/-- The `ε₂`-form of `sep_le`: since `e ≤ ε₂`, the `e`-form is the stronger one. -/
theorem sep_eps₂ (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ : 0 < β) {k : ℕ} (hk : k < N) :
    12 * η k / (ε₂ * β) ≤ ε₂ * η (k + 1) / 4 := by
  have hd : e ≤ ε₂ := h.div_le_eps₂
  have he : 0 < e := h.div_pos
  have hr : 0 < η (k + 1) := h.rung_pos (k + 1)
  have hk0 : 0 < η k := h.rung_pos k
  have step1 : 12 * η k / (ε₂ * β) ≤ 12 * η k / (e * β) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos he hβ)
      (mul_le_mul_of_nonneg_right hd hβ.le)
  have step2 : e * η (k + 1) / 4 ≤ ε₂ * η (k + 1) / 4 := by
    have : e * η (k + 1) ≤ ε₂ * η (k + 1) := mul_le_mul_of_nonneg_right hd hr.le
    linarith
  exact step1.trans ((h.sep_le k hk).trans step2)

/-- The `ε₂`-form of `gain_budget`. -/
theorem gain_budget_eps₂ (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ : 0 < β) {k : ℕ}
    (hk : k < N) :
    10 * η k / ε₂ + 2 * (12 * η k / (ε₂ * β)) ≤ gain (η (k + 1) / 2) := by
  have hd : e ≤ ε₂ := h.div_le_eps₂
  have he : 0 < e := h.div_pos
  have hk0 : 0 < η k := h.rung_pos k
  have s1 : 10 * η k / ε₂ ≤ 10 * η k / e :=
    div_le_div_of_nonneg_left (by positivity) he hd
  have s2 : 12 * η k / (ε₂ * β) ≤ 12 * η k / (e * β) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos he hβ)
      (mul_le_mul_of_nonneg_right hd hβ.le)
  have := h.gain_budget k hk
  linarith

/-- The `ε₂`-form of `dens_budget`. -/
theorem dens_budget_eps₂ (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N) :
    η k / ε₂ ≤ dens (η (k + 1) / 2) / 2 := by
  have hd : e ≤ ε₂ := h.div_le_eps₂
  have he : 0 < e := h.div_pos
  have hk0 : 0 < η k := h.rung_pos k
  have s1 : η k / ε₂ ≤ η k / e := div_le_div_of_nonneg_left hk0.le he hd
  exact s1.trans (h.dens_budget k hk)

/-- `e ≤ ε₁/25`: conclusion (i) of the dividing-scales lemma is `δ^{-e}` Katz--Tao at every
scale, and `e ≤ ε₁/25` leaves the factor `25` of room the blueprint's `≲` absorbs. -/
theorem div_le_everyScale (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) : e ≤ ε₁ / 25 := by
  have h1 := h.div_le
  have h2 := h.eps₂_le_everyScale
  linarith

/-- **`eps₂_le_half` is not the operative cap.**  `stepCount_eq` and
`four_thousand_le_stepCount` say `⌈25/ε₂²⌉ ≥ 4096`, hence `25/ε₂² > 4095` and `ε₂ < 1/12`.
Recorded so that the weak field `eps₂_le_half`, which is all any consumer spends, is visibly
not the strongest thing the structure knows about `ε₂`. -/
theorem eps₂_lt_twelfth (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) : ε₂ < 1 / 12 := by
  have hpos : 0 < ε₂ := h.eps₂_pos
  have hN : 4095 < ⌈25 / ε₂ ^ 2⌉₊ := by
    have := h.four_thousand_le_stepCount
    rw [h.stepCount_eq] at this
    omega
  have hR : (4095 : ℝ) < 25 / ε₂ ^ 2 := by exact_mod_cast Nat.lt_ceil.mp hN
  rw [lt_div_iff₀ (by positivity)] at hR
  nlinarith [hR, hpos]

/-- `e ≤ 1/64`: the `e`-side of the `4096` threshold, from `div_eq` and
`four_thousand_le_stepCount`.  This is the exact converse of
`Kakeya.ML2Reduction.four_thousand_le_of_div_eq`, so the two sides of the threshold agree.

Note that it does *not* follow from `eps₂_lt_twelfth` via `div_le : e ≤ ε₂/5`, which gives only
`e < 1/60`: the ceiling in `stepCount_eq` loses just enough that `ε₂ < 5/64` is unavailable
(`⌈25/ε₂²⌉ ≥ 4096` only forces `ε₂ < 5/√4095`).  It has to be read off `N` directly. -/
theorem div_le_inv64 (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) : e ≤ 1 / 64 := by
  have hN : (4096 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h.four_thousand_le_stepCount
  have h4096 : Real.sqrt (4096 : ℝ) = 64 := by
    rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 64)]
  have h64 : (64 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have := Real.sqrt_le_sqrt hN
    rwa [h4096] at this
  rw [h.div_eq]
  exact one_div_le_one_div_of_le (by norm_num) h64

end IsSpine

/-! ### The construction -/

/-- `ε₂ = min (ε₁/5) (ϖ/2) (1/64)`, the largest choice the two blueprint constraints allow,
capped at `1/64` so that `N = ⌈25/ε₂²⌉ ≥ 25 · 64² = 102400 ≥ 4096`.

The cap used to be `1/2`, which gives only `N ≥ 100`.  That was not enough:
`StickyKakeya.dividingScalesKatzTao` (GWZ Lemma 7.7(B)) refuses to run below
`4096` stopping steps, so no spine could instantiate the dichotomy at all.  See the field
`Kakeya.ML2Spine.IsSpine.four_thousand_le_stepCount`.  Nothing else in the blueprint proof
constrains the cap from below — it is a free "choose `ε₂` small enough" — so tightening it
weakens no conclusion. -/
noncomputable def spineEps₂ (ϖ ε₁ : ℝ) : ℝ := min (min (ε₁ / 5) (ϖ / 2)) (1 / 64)

/-- `N = ⌈25/ε₂²⌉`, the number of dividing scales. -/
noncomputable def spineCount (ϖ ε₁ : ℝ) : ℕ := ⌈25 / spineEps₂ ϖ ε₁ ^ 2⌉₊

/-- `e = 1/√N`, the exponent `dividingScalesLemmaB` builds from `N`. -/
noncomputable def spineDiv (ϖ ε₁ : ℝ) : ℝ := 1 / Real.sqrt (spineCount ϖ ε₁ : ℝ)

/-- One step down the chain: `η_k = step (η_{k+1})`, where the three entries of the minimum are
exactly the three budgets of `IsSpine`.

* `e² β x / 1024` is the refined source's `ν_c ≤ (β/16)·η̄_{k+1}` (l.4270-4274, l.4310) read at the
  saturated eccentric cap `η̄_{k+1} = e² η_{k+1}/64` (l.4011): `β·(e² x/64)/16 = e² β x/1024`.  It
  also pays the separation `12 η_k/(e β) ≤ e η_{k+1}/4` — now with room to spare rather than with
  equality, since `12 (e² β x/1024)/(e β) = e x/85.33`;
* `e β · gain (x/2) / 34` pays the gain budget, since
  `10 β/34 + 24/34 ≤ 1` for `β ≤ 1`;
* `e · dens (x/2) / 2` pays the density budget, again with equality.

The first entry also makes the step a contraction (`e² β/1024 ≤ 1`), which is what gives the
chain its monotonicity. -/
noncomputable def spineStep (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (x : ℝ) : ℝ :=
  min (min (spineDiv ϖ ε₁ ^ 2 * β * x / 1024) (spineDiv ϖ ε₁ * β * gain (x / 2) / 34))
    (spineDiv ϖ ε₁ * dens (x / 2) / 2)

/-- The chain read *downwards* from the top: `spineAux β ϖ ε₁ gain dens m` is `η_{N-m}`. -/
noncomputable def spineAux (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) : ℕ → ℝ
  | 0 => spineDiv ϖ ε₁
  | m + 1 => spineStep β ϖ ε₁ gain dens (spineAux β ϖ ε₁ gain dens m)

/-- **The chain `η : ℕ → ℝ`.**  `η_N = e` and `η_k = step (η_{k+1})` for `k < N`; above `N` it
is constant at `e`. -/
noncomputable def spineRung (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (k : ℕ) : ℝ :=
  spineAux β ϖ ε₁ gain dens (spineCount ϖ ε₁ - k)

/-- **The gain of Main Lemma 2**, `ν = η₀`, the bottom rung of the chain.

Note the argument list: `β`, the two `β`-only exponent functions of Lemma 9.1, the `β`-only
window exponent `ϖ`, and the Katz--Tao exponent `ε₁`.  There is **no `ε`**. -/
noncomputable def spineNu (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) : ℝ :=
  spineRung β ϖ ε₁ gain dens 0

/-- The **absolute** accuracy at which Theorem 7.3(B) is read: `ε₀ = β/2`, a function of `β`
alone.  Prof. Hong Wang's clarification of 2026-08-30: the outer `ε` must not be used here. -/
noncomputable def absAccuracy (β : ℝ) : ℝ := β / 2

theorem absAccuracy_pos {β : ℝ} (hβ : 0 < β) : 0 < absAccuracy β := by
  unfold absAccuracy; linarith

/-! ### Properties of the construction -/

variable {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}

theorem spineEps₂_pos (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) : 0 < spineEps₂ ϖ ε₁ :=
  lt_min (lt_min (by linarith) (by linarith)) (by norm_num)

theorem spineEps₂_le_everyScale : spineEps₂ ϖ ε₁ ≤ ε₁ / 5 :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem spineEps₂_le_vnsWindow : spineEps₂ ϖ ε₁ ≤ ϖ / 2 :=
  (min_le_left _ _).trans (min_le_right _ _)

/-- `ε₂ ≤ 1/64`: the cap that makes `N ≥ 4096`, which is what GWZ Lemma 7.7(B) needs. -/
theorem spineEps₂_le_inv64 : spineEps₂ ϖ ε₁ ≤ 1 / 64 := min_le_right _ _

theorem spineEps₂_le_half : spineEps₂ ϖ ε₁ ≤ 1 / 2 :=
  spineEps₂_le_inv64.trans (by norm_num)

theorem spineEps₂_window_fits (hϖ : 0 < ϖ) : spineEps₂ ϖ ε₁ * (1 + ϖ) ≤ ϖ := by
  have h1 : spineEps₂ ϖ ε₁ ≤ ϖ / 2 := spineEps₂_le_vnsWindow
  have h2 : spineEps₂ ϖ ε₁ ≤ 1 / 2 := spineEps₂_le_half
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - spineEps₂ ϖ ε₁) hϖ.le]

/-- **`N ≥ 102400`**, from the cap `ε₂ ≤ 1/64`: `25/ε₂² ≥ 25 · 64² = 102400`.

The sharp form; `Kakeya.ML2Spine.four_thousand_le_spineCount` and
`Kakeya.ML2Spine.hundred_le_spineCount` are the two thresholds actually consumed. -/
theorem hundredThousand_le_spineCount (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) :
    102400 ≤ spineCount ϖ ε₁ := by
  have hpos : 0 < spineEps₂ ϖ ε₁ := spineEps₂_pos hϖ hε₁
  have h64 : spineEps₂ ϖ ε₁ ≤ 1 / 64 := spineEps₂_le_inv64
  have hR : (102400 : ℝ) ≤ 25 / spineEps₂ ϖ ε₁ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have := hR.trans (Nat.le_ceil (25 / spineEps₂ ϖ ε₁ ^ 2))
  exact_mod_cast this

/-- **`N ≥ 4096`**, the threshold of `StickyKakeya.dividingScalesKatzTao`. -/
theorem four_thousand_le_spineCount (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) : 4096 ≤ spineCount ϖ ε₁ :=
  le_trans (by norm_num) (hundredThousand_le_spineCount hϖ hε₁)

theorem hundred_le_spineCount (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) : 100 ≤ spineCount ϖ ε₁ :=
  le_trans (by norm_num) (four_thousand_le_spineCount hϖ hε₁)

theorem one_le_spineCount (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) : 1 ≤ spineCount ϖ ε₁ :=
  le_trans (by norm_num) (hundred_le_spineCount hϖ hε₁)

theorem spineDiv_pos (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) : 0 < spineDiv ϖ ε₁ := by
  have hN : 1 ≤ spineCount ϖ ε₁ := one_le_spineCount hϖ hε₁
  have hNR : (0 : ℝ) < (spineCount ϖ ε₁ : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have : 0 < Real.sqrt (spineCount ϖ ε₁ : ℝ) := Real.sqrt_pos.mpr hNR
  unfold spineDiv
  positivity

theorem spineDiv_le (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) : spineDiv ϖ ε₁ ≤ spineEps₂ ϖ ε₁ / 5 := by
  have hpos : 0 < spineEps₂ ϖ ε₁ := spineEps₂_pos hϖ hε₁
  have hN : 1 ≤ spineCount ϖ ε₁ := one_le_spineCount hϖ hε₁
  have hNR : (0 : ℝ) < (spineCount ϖ ε₁ : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hceil : 25 / spineEps₂ ϖ ε₁ ^ 2 ≤ (spineCount ϖ ε₁ : ℝ) := Nat.le_ceil _
  have hsq : (5 / spineEps₂ ϖ ε₁) ^ 2 ≤ (spineCount ϖ ε₁ : ℝ) := by
    have : (5 / spineEps₂ ϖ ε₁) ^ 2 = 25 / spineEps₂ ϖ ε₁ ^ 2 := by
      field_simp
      norm_num
    rw [this]; exact hceil
  have hsqrt : 5 / spineEps₂ ϖ ε₁ ≤ Real.sqrt (spineCount ϖ ε₁ : ℝ) :=
    Real.le_sqrt_of_sq_le hsq
  have hfive : 0 < 5 / spineEps₂ ϖ ε₁ := by positivity
  unfold spineDiv
  calc 1 / Real.sqrt (spineCount ϖ ε₁ : ℝ) ≤ 1 / (5 / spineEps₂ ϖ ε₁) :=
        one_div_le_one_div_of_le hfive hsqrt
    _ = spineEps₂ ϖ ε₁ / 5 := by
        rw [one_div_div]

theorem spineDiv_le_one (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) : spineDiv ϖ ε₁ ≤ 1 / 10 := by
  have h1 := spineDiv_le hϖ hε₁
  have h2 : spineEps₂ ϖ ε₁ ≤ 1 / 2 := spineEps₂_le_half
  linarith

/-- The step is positive whenever the rung it starts from is. -/
theorem spineStep_pos (hβ : 0 < β) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) {x : ℝ} (hx : 0 < x) :
    0 < spineStep β ϖ ε₁ gain dens x := by
  have he : 0 < spineDiv ϖ ε₁ := spineDiv_pos hϖ hε₁
  have hg : 0 < gain (x / 2) := hgain _ (by linarith)
  have hd : 0 < dens (x / 2) := hdens _ (by linarith)
  unfold spineStep
  exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)

set_option linter.unusedVariables false in
/-- The step is a contraction: `step x ≤ e² β x/1024 ≤ x`.

`hβ : 0 < β` is carried for uniformity with the rest of the construction bundle even though the
inequality survives `β ≤ 0` (the step is then nonpositive). -/
@[nolint unusedArguments]
theorem spineStep_le_self (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) {x : ℝ}
    (hx : 0 ≤ x) : spineStep β ϖ ε₁ gain dens x ≤ x := by
  have he : 0 < spineDiv ϖ ε₁ := spineDiv_pos hϖ hε₁
  have he10 : spineDiv ϖ ε₁ ≤ 1 / 10 := spineDiv_le_one hϖ hε₁
  have hfirst : spineStep β ϖ ε₁ gain dens x ≤ spineDiv ϖ ε₁ ^ 2 * β * x / 1024 :=
    (min_le_left _ _).trans (min_le_left _ _)
  refine hfirst.trans ?_
  have he2 : spineDiv ϖ ε₁ ^ 2 ≤ 1 / 100 := by nlinarith [he.le, he10]
  have hsq : spineDiv ϖ ε₁ ^ 2 * β ≤ 1024 := by
    nlinarith [he2, hβ1, hβ.le, sq_nonneg (spineDiv ϖ ε₁)]
  nlinarith [hsq, hx, mul_nonneg (mul_nonneg (sq_nonneg (spineDiv ϖ ε₁)) hβ.le) hx]

/-- **The pre- first-entry bound**, `step x ≤ e² β x / 48`, kept for the existing
consumers that re-derive it from the step; it is implied by the re-anchored entry `e² β x / 1024`
since `e² β x ≥ 0`. -/
theorem spineStep_le_div_48 (hβ : 0 < β) {x : ℝ} (hx : 0 ≤ x) :
    spineStep β ϖ ε₁ gain dens x ≤ spineDiv ϖ ε₁ ^ 2 * β * x / 48 := by
  refine ((min_le_left _ _).trans (min_le_left _ _)).trans ?_
  have hX : 0 ≤ spineDiv ϖ ε₁ ^ 2 * β * x := by positivity
  exact div_le_div_of_nonneg_left hX (by norm_num) (by norm_num)

theorem spineAux_pos (hβ : 0 < β) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∀ m, 0 < spineAux β ϖ ε₁ gain dens m := by
  intro m
  induction m with
  | zero => exact spineDiv_pos hϖ hε₁
  | succ m ih =>
      rw [spineAux]
      exact spineStep_pos hβ hϖ hε₁ hgain hdens ih

theorem spineAux_antitone (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    Antitone (spineAux β ϖ ε₁ gain dens) := by
  refine antitone_nat_of_succ_le ?_
  intro m
  rw [spineAux]
  exact spineStep_le_self hβ hβ1 hϖ hε₁ (spineAux_pos hβ hϖ hε₁ hgain hdens m).le

/-- The recursion, read on `spineRung`: for `k < N`, `η_k = step (η_{k+1})`. -/
theorem spineRung_eq_step {k : ℕ} (hk : k < spineCount ϖ ε₁) :
    spineRung β ϖ ε₁ gain dens k
      = spineStep β ϖ ε₁ gain dens (spineRung β ϖ ε₁ gain dens (k + 1)) := by
  unfold spineRung
  have h : spineCount ϖ ε₁ - k = (spineCount ϖ ε₁ - (k + 1)) + 1 := by omega
  rw [h, spineAux]

theorem spineRung_top : spineRung β ϖ ε₁ gain dens (spineCount ϖ ε₁) = spineDiv ϖ ε₁ := by
  unfold spineRung
  simp [spineAux]

/-! ### The spine is a spine -/

/-- **The construction satisfies every constraint of `IsSpine`.** -/
theorem spineRung_isSpine (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    IsSpine β ϖ ε₁ gain dens (spineEps₂ ϖ ε₁) (spineDiv ϖ ε₁) (spineCount ϖ ε₁)
      (spineRung β ϖ ε₁ gain dens) := by
  have he : 0 < spineDiv ϖ ε₁ := spineDiv_pos hϖ hε₁
  have hanti : Antitone (spineAux β ϖ ε₁ gain dens) :=
    spineAux_antitone hβ hβ1 hϖ hε₁ hgain hdens
  have hauxpos : ∀ m, 0 < spineAux β ϖ ε₁ gain dens m := spineAux_pos hβ hϖ hε₁ hgain hdens
  have hrungpos : ∀ k, 0 < spineRung β ϖ ε₁ gain dens k := fun k ↦ hauxpos _
  refine
    { eps₂_pos := spineEps₂_pos hϖ hε₁
      eps₂_le_everyScale := spineEps₂_le_everyScale
      eps₂_le_vnsWindow := spineEps₂_le_vnsWindow
      eps₂_le_half := spineEps₂_le_half
      window_fits := spineEps₂_window_fits hϖ
      stepCount_eq := rfl
      one_le_stepCount := one_le_spineCount hϖ hε₁
      four_thousand_le_stepCount := four_thousand_le_spineCount hϖ hε₁
      div_eq := rfl
      div_pos := he
      div_le := spineDiv_le hϖ hε₁
      rung_pos := hrungpos
      rung_mono := ?_
      rung_top := spineRung_top
      rung_le_div := ?_
      sep_le := ?_
      gain_budget := ?_
      dens_budget := ?_ }
  · -- monotone
    intro i j hij
    exact hanti (by omega : spineCount ϖ ε₁ - j ≤ spineCount ϖ ε₁ - i)
  · -- every rung ≤ e
    intro k
    have : spineAux β ϖ ε₁ gain dens (spineCount ϖ ε₁ - k) ≤ spineAux β ϖ ε₁ gain dens 0 :=
      hanti (Nat.zero_le _)
    simpa [spineRung, spineAux] using this
  · -- separation
    intro k hk
    have hstep := spineRung_eq_step (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain) (dens := dens) hk
    have hx : 0 < spineRung β ϖ ε₁ gain dens (k + 1) := hrungpos (k + 1)
    have h1 : spineRung β ϖ ε₁ gain dens k
        ≤ spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ gain dens (k + 1) / 1024 := by
      rw [hstep]
      exact (min_le_left _ _).trans (min_le_left _ _)
    rw [div_le_iff₀ (mul_pos he hβ)]
    have hM : 0 ≤ spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ gain dens (k + 1) := by positivity
    have heq : spineDiv ϖ ε₁ * spineRung β ϖ ε₁ gain dens (k + 1) / 4 * (spineDiv ϖ ε₁ * β)
        = spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ gain dens (k + 1) / 4 := by ring
    rw [heq]
    linarith [h1, hM]
  · -- gain budget
    intro k hk
    have hstep := spineRung_eq_step (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain) (dens := dens) hk
    have hx : 0 < spineRung β ϖ ε₁ gain dens (k + 1) := hrungpos (k + 1)
    have hg : 0 < gain (spineRung β ϖ ε₁ gain dens (k + 1) / 2) := hgain _ (by linarith)
    have hk0 : 0 < spineRung β ϖ ε₁ gain dens k := hrungpos k
    have h2 : spineRung β ϖ ε₁ gain dens k
        ≤ spineDiv ϖ ε₁ * β * gain (spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 34 := by
      rw [hstep]
      exact (min_le_left _ _).trans (min_le_right _ _)
    have he' : spineDiv ϖ ε₁ ≠ 0 := ne_of_gt he
    have hβ' : β ≠ 0 := ne_of_gt hβ
    have hcollect : 10 * spineRung β ϖ ε₁ gain dens k / spineDiv ϖ ε₁
          + 2 * (12 * spineRung β ϖ ε₁ gain dens k / (spineDiv ϖ ε₁ * β))
        = (10 * β + 24) * spineRung β ϖ ε₁ gain dens k / (spineDiv ϖ ε₁ * β) := by
      field_simp
      ring
    rw [hcollect, div_le_iff₀ (mul_pos he hβ)]
    nlinarith [h2, hk0, hg, he, hβ, hβ1,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 10 - 10 * β) hk0.le]
  · -- density budget
    intro k hk
    have hstep := spineRung_eq_step (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain) (dens := dens) hk
    have hx : 0 < spineRung β ϖ ε₁ gain dens (k + 1) := hrungpos (k + 1)
    have h3 : spineRung β ϖ ε₁ gain dens k
        ≤ spineDiv ϖ ε₁ * dens (spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 2 := by
      rw [hstep]
      exact min_le_right _ _
    rw [div_le_iff₀ he]
    nlinarith [h3, he]

/-! ### The gain -/

theorem spineNu_pos (hβ : 0 < β) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    0 < spineNu β ϖ ε₁ gain dens :=
  spineAux_pos hβ hϖ hε₁ hgain hdens _

/-- `ν ≤ η₁`: the gain of Main Lemma 2 is below the first rung.  In fact `ν = η₀`. -/
theorem spineNu_le_rung_one (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    spineNu β ϖ ε₁ gain dens ≤ spineRung β ϖ ε₁ gain dens 1 := by
  have hanti : Antitone (spineAux β ϖ ε₁ gain dens) :=
    spineAux_antitone hβ hβ1 hϖ hε₁ hgain hdens
  unfold spineNu spineRung
  exact hanti (by omega : spineCount ϖ ε₁ - 1 ≤ spineCount ϖ ε₁ - 0)

/-- `2 ν ≤ β`: the every-scale branch closes at the absolute accuracy `ε₀ = β/2`, because
`ε₀ ≤ ε + (β - ν)` for every `ε > 0`.  In fact `ν ≤ β/48000`. -/
theorem two_spineNu_le (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    2 * spineNu β ϖ ε₁ gain dens ≤ β := by
  have he : 0 < spineDiv ϖ ε₁ := spineDiv_pos hϖ hε₁
  have he10 : spineDiv ϖ ε₁ ≤ 1 / 10 := spineDiv_le_one hϖ hε₁
  have hanti : Antitone (spineAux β ϖ ε₁ gain dens) :=
    spineAux_antitone hβ hβ1 hϖ hε₁ hgain hdens
  have hN : 1 ≤ spineCount ϖ ε₁ := one_le_spineCount hϖ hε₁
  have hstep : spineNu β ϖ ε₁ gain dens ≤ spineAux β ϖ ε₁ gain dens 1 := by
    unfold spineNu spineRung
    rw [Nat.sub_zero]
    exact hanti hN
  have hone : spineAux β ϖ ε₁ gain dens 1
      ≤ spineDiv ϖ ε₁ ^ 2 * β * spineDiv ϖ ε₁ / 1024 := by
    rw [spineAux, spineAux]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have he2 : spineDiv ϖ ε₁ ^ 2 ≤ 1 / 100 := by nlinarith [he.le, he10]
  have hcube : spineDiv ϖ ε₁ ^ 2 * spineDiv ϖ ε₁ ≤ 1 / 1000 := by
    nlinarith [he2, he.le, he10, sq_nonneg (spineDiv ϖ ε₁)]
  have hfin : spineDiv ϖ ε₁ ^ 2 * β * spineDiv ϖ ε₁ / 1024 ≤ β / 2 := by
    nlinarith [hcube, hβ.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 1000 - spineDiv ϖ ε₁ ^ 2 * spineDiv ϖ ε₁) hβ.le]
  linarith [hstep, hone, hfin]

/-! ### The headline: `ν` is fixed before `ε` -/

/-- **Parameter selection for the proof of GWZ Main Lemma 2.**

Given `β ∈ (0, 1]`, the `β`-only data of Lemma 9.1 (`ϖ`, and the two exponent functions
`gain = ν(β, ·)` and `dens = η(β, ·)`), and the exponent map `E` of Theorem 7.3(B)
(`accuracy ↦ Katz--Tao exponent`), there is a gain `ν > 0` such that for **every** accuracy
`ε > 0` the whole parameter spine exists with that same `ν`.

The quantifier order is the content: `ν` is bound outside `∀ ε > 0`.  Theorem 7.3(B) is read
at `absAccuracy β = β/2`, an absolute accuracy in the sense of Prof. Hong Wang's clarification
— it is a function of `β` alone and in particular is not the outer `ε`.  The last conjunct of
the body is the only clause that mentions `ε` at all, and it is what the every-scale branch
needs: the branch gives `μ(𝕋, Y) ≤ δ^{-ε₀}`, and `ε₀ ≤ ε + (β - ν)` turns this into
`μ(𝕋, Y) ≤ δ^{-ε} |𝕋|^{β-ν}` once `|𝕋| ≥ δ^{-1}`.

`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` shows this conclusion is *unavailable* if `E`
is read at the outer `ε` instead. -/
theorem exists_ml2SpineParams (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {E : ℝ → ℝ} (hE : ∀ a, 0 < a → 0 < E a) :
    ∃ ν : ℝ, 0 < ν ∧ 2 * ν ≤ β ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
          IsSpine β ϖ (E (absAccuracy β)) gain dens ε₂ e N η ∧
            ν = η 0 ∧ ν ≤ η 1 ∧ absAccuracy β ≤ ε + (β - ν) := by
  have hε₁ : 0 < E (absAccuracy β) := hE _ (absAccuracy_pos hβ)
  refine ⟨spineNu β ϖ (E (absAccuracy β)) gain dens, spineNu_pos hβ hϖ hε₁ hgain hdens,
    two_spineNu_le hβ hβ1 hϖ hε₁ hgain hdens, ?_⟩
  intro ε hε
  refine ⟨spineEps₂ ϖ (E (absAccuracy β)), spineDiv ϖ (E (absAccuracy β)),
    spineCount ϖ (E (absAccuracy β)), spineRung β ϖ (E (absAccuracy β)) gain dens,
    spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens, rfl,
    spineNu_le_rung_one hβ hβ1 hϖ hε₁ hgain hdens, ?_⟩
  have h2 := two_spineNu_le hβ hβ1 hϖ hε₁ hgain hdens
  simp only [absAccuracy] at h2 ⊢
  linarith

/-! ### The obstruction: reading Theorem 7.3(B) at the outer `ε` kills the gain -/

/-- **Reading Theorem 7.3(B) at the outer accuracy makes an `ε`-free gain impossible.**

Suppose one insists on the published dependency `ε ↦ ε₁ = E ε ↦ ε₂ ↦ (N, η) ↦ ν` while still
demanding a single `ν > 0` valid for every `ε`.  The chain of the spine gives
`ν ≤ η₁ ≤ e ≤ ε₂/5 ≤ E ε/25`, so `ν` is bounded by `E ε/25` for every `ε > 0`.  If `E` takes
arbitrarily small positive values — which it must, since a Katz--Tao exponent bounded below by
some `η♭ > 0` at every accuracy would say that any family which is `δ^{-η♭}` Katz--Tao at every
scale has multiplicity `δ^{-ε}` for *every* `ε`, i.e. multiplicity `δ^{-o(1)}` — then `ν ≤ 0`,
a contradiction.

This is exactly why Theorem 7.3(B) must be applied at an absolute accuracy: the typo in the
published proof is not cosmetic, it is the difference between a theorem and a falsehood. -/
theorem not_epsFree_of_outerAccuracy {E : ℝ → ℝ}
    (hsmall : ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ E ε < c) {ν : ℝ} (hν : 0 < ν)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
        IsSpine β ϖ (E ε) gain dens ε₂ e N η ∧ ν ≤ η 1) : False := by
  obtain ⟨ε, hε, hEε⟩ := hsmall (25 * ν) (by linarith)
  obtain ⟨ε₂, e, N, η, hspine, hν1⟩ := h ε hε
  have h1 : η 1 ≤ e := hspine.rung_le_div 1
  have h2 : e ≤ E ε / 25 := hspine.div_le_everyScale
  linarith

/-- The same obstruction under the concrete normalisation `E a ≤ a`, which is how the
every-scale exponent is actually built (one always takes the minimum with the accuracy). -/
theorem not_epsFree_of_outerAccuracy' {E : ℝ → ℝ} (hE : ∀ a : ℝ, 0 < a → E a ≤ a) {ν : ℝ}
    (hν : 0 < ν)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
        IsSpine β ϖ (E ε) gain dens ε₂ e N η ∧ ν ≤ η 1) : False := by
  refine not_epsFree_of_outerAccuracy (β := β) (ϖ := ϖ) (gain := gain) (dens := dens)
    (E := E) ?_ hν h
  intro c hc
  exact ⟨c / 2, by linarith, by have := hE (c / 2) (by linarith); linarith⟩

/-! ### Non-vacuity

`spineRung_isSpine` and `exists_ml2SpineParams` are conditional: they carry hypotheses on
`β`, `ϖ`, `gain`, `dens` and `E`.  A conditional theorem whose hypotheses are unsatisfiable
proves nothing, so the two certificates below discharge every one of those hypotheses at
concrete data (`β = ϖ = 1`, `gain = dens = E = id`), leaving an unconditional existential.
-/

/-- **`IsSpine` is inhabited, with no hypotheses left standing.**  Concrete instance of
`Kakeya.ML2Spine.spineRung_isSpine`; in particular the `4096 ≤ N` field is satisfiable
alongside all the others. -/
theorem exists_isSpine_at_one :
    ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
      IsSpine 1 1 1 (fun x => x) (fun x => x) ε₂ e N η :=
  ⟨_, _, _, _,
    spineRung_isSpine (β := 1) (ϖ := 1) (ε₁ := 1) (gain := fun x => x) (dens := fun x => x)
      one_pos le_rfl one_pos one_pos (fun _ h => h) (fun _ h => h)⟩

/-- **The obstruction `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` is not vacuous either.**

That theorem derives `False` from a *uniform* `ν` together with a spine at `ε₁ = E ε` for every
`ε`.  One could worry that it derives `False` merely because its `IsSpine` clause is
unsatisfiable — which would make it say nothing about the published proof.  It is not: at every
positive `ε₁` whatsoever, in particular at `ε₁ = E ε`, the spine exists and its first rung is
positive.  So the only thing `not_epsFree_of_outerAccuracy` rules out is the uniformity of `ν`,
which is exactly the defect Prof. Hong Wang's clarification identifies. -/
theorem exists_isSpine_of_pos (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
      IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧ 0 < η 1 :=
  ⟨_, _, _, _, spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens,
    spineAux_pos hβ hϖ hε₁ hgain hdens _⟩

/-- **`exists_ml2SpineParams` is not vacuous.**  Its six hypotheses are simultaneously
satisfiable, so the `ν` it produces is a real number and not a consequence of `False`. -/
theorem exists_ml2SpineParams_at_one :
    ∃ ν : ℝ, 0 < ν ∧ 2 * ν ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
          IsSpine 1 1 (absAccuracy 1) (fun x => x) (fun x => x) ε₂ e N η ∧
            ν = η 0 ∧ ν ≤ η 1 ∧ absAccuracy 1 ≤ ε + (1 - ν) :=
  exists_ml2SpineParams (β := 1) (ϖ := 1) (gain := fun x => x) (dens := fun x => x)
    (E := fun x => x) one_pos le_rfl one_pos (fun _ h => h) (fun _ h => h) (fun _ h => h)

end Kakeya.ML2Spine

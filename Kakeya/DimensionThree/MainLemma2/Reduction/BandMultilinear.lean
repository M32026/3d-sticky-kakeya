/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardBand

/-!
# Scoping the multilinear input of the Main Lemma 2 cardinality band

`Kakeya.ML2Band` (`Reduction/SpineCardBand.lean`) reduces the last open branch of the Main Lemma 2
assembly to `Kakeya.ML2Band.BandDichotomy`, equivalently to `Kakeya.ML2Band.BandKakeya`, on the
cardinality band `δ^{-ε/(2(β-γ))} < |𝕋| < δ^{-1}`, and proves that none of the three inequalities
the assembly holds is strong enough there.  The route named by Prof. Hong Wang is broad--narrow,
whose broad half needs a **multilinear Kakeya inequality in ℝ³**.

This file is the *scoping* of that input. It states the multilinear ingredient precisely, states
the exponent budget that any broad--narrow route through it must meet, and — the reason the file
exists — **shows by compiler-checked arithmetic that the broad--narrow sketch recorded  does not meet that budget**. Nothing here is assumed: every declaration is
either a `def... : Prop` that nothing uses, or a theorem proved outright.

**Two different Bourgain--Guth constants appear below and must not be conflated.**  `b` in
`Kakeya.ML2BandML.Budget` is the *broad extraction* exponent, from `m ≤ K^{b}(m₁m₂m₃)^{1/3}`; the
crude extraction gives `b = 2`, from `∑_τ m_τ = m` over `≈ K²` caps.  `b` in
`Kakeya.ML2BandML.narrowLossExponent` is the *narrow threshold* exponent, `Λ = K^{b}`.  They are
independent, and the two sections below are about the two of them separately.  (In the Lean
statements they are of course separate binders; the shared letter is only in this prose.)

## The budget

Assemble the broad half exactly as the sketch does: the pointwise Bourgain--Guth broad bound
`m ≤ K^b (m₁m₂m₃)^{1/3}`, a multilinear Kakeya inequality of loss `δ^{-A₀}`, Hölder with exponents
`(3/2, 3)`, the fullness lower bound `λ ≥ δ^{η}`, and the band hypothesis `δ²|𝕋| < δ`.  Writing
`K = δ^{-κ}`, the broad alternative closes to `μ ≲ δ^{1 - 3bκ - 2A₀ - 2η}`, so it delivers
`μ ≤ δ^{-ε}` exactly when

  `3·b·κ + 2·A₀ + 2·η ≤ 1 + ε`.                                        (`Kakeya.ML2BandML.Budget`)

`Kakeya.ML2BandML.broad_closes_of_budget` is that implication as an `rpow` inequality, and
`Kakeya.ML2BandML.le_pow_three_of_le_rpow_mul` is the one nonlinear step of the derivation
(`μ ≤ B·μ^{2/3} → μ ≤ B³`, which is where "the broad case closes" happens).  Read the other way,
the budget *is* the `δ¹` of surplus the band enjoys: `Kakeya.ML2BandML.exists_budget_of_lt_half`
says every loss `2A₀ < 1 + ε` — in particular every `A₀ < 1/2` — meets it, and
`Kakeya.ML2BandML.not_budget_of_half_lt` says that threshold is sharp.  So the broad half tolerates
a multilinear loss of almost `δ^{-1/2}`, and the sketch's claim that the broad case is easy here,
with a whole factor `δ¹` of surplus, is **confirmed**.

## Loomis--Whitney is not a substitute for Bennett--Carbery--Tao

The only thing in Mathlib's Brascamp--Lieb corner is the axis-parallel "grid-lines" lemma
`MeasureTheory.lintegral_prod_lintegral_pow_le` (`Mathlib/Analysis/FunctionalSpaces/
SobolevInequality.lean`).  Applied to tubes whose directions lie in a cap of width `1/K`, it gives
loss exponent `A₀ = 3/2 - κ`: a `δ`-tube whose direction lies in a `1/K`-cap has a projection of
area `≈ δ·(1/K)`, not `δ²`, and the transversality of a Bourgain--Guth broad triple is only
`ν ≈ 1/K`.  With the Bourgain--Guth constant `b ≥ 2` the budget then forces `2 ≤ ε`
(`Kakeya.ML2BandML.loomisWhitney_budget_forces_two_le`): it misses by two full powers of `δ`.
Even at the best conceivable transversality `ν ≈ 1` the loss is `A₀ = 3(1-κ)/2` and the budget
still forces `2 ≤ ε` for every `b ≥ 2`
(`Kakeya.ML2BandML.loomisWhitney_transverse_budget_forces_two_le`).  Genuine
Bennett--Carbery--Tao/Guth — loss `δ^{-ε'}` for **every** `ε' > 0` — is required.

## The sketch's narrow accounting, and what repairing it costs

 argues that the narrow half terminates after `n = O(log(1/a)/κ)` rescalings
with accumulated loss `K^{bn} = δ^{-bκn}`, "`≤ δ^{-ε}` provided `κ` is chosen small compared to
`ε/n` — self-consistent, since `n` depends only on `κ` and `a`".  It is not self-consistent: `n`
grows like `1/κ`, so `κ·n ≈ log(1/a)` does not depend on `κ` at all.

Account charitably for the shrinking of the scale — step `j` runs at `δ^{(1-κ)^j}`, so its loss is
`δ^{-bκ(1-κ)^j}`, the *smallest* reading of the claim — and the accumulated loss exponent is
`b(1 - (1-κ)^n)` (`Kakeya.ML2BandML.narrowLossExponent_eq`), while termination of the induction is
exactly `(1-κ)^n ≤ a`, `a` being the cardinality exponent the band starts at.  So the accumulated
loss exponent is at least `b(1-a)` **whatever `κ` is**
(`Kakeya.ML2BandML.le_narrowLossExponent_of_terminates`, `Kakeya.ML2BandML.not_sketchNarrowBudget`).
`Kakeya.ML2BandML.narrowLossExponent_le_mul` records that this refutes the literal reading `bκn`
as well, since `b(1-(1-κ)^n) ≤ b·κ·n`.

**So `κ` is not the free parameter; `b` is** (`Kakeya.ML2BandML.narrow_forces_small_step_loss`:
the route needs `b ≤ ε/(1-a)`).  And `b` is not free either, for a reason that is the real content
of this file.  Write `Λ = K^{b}` for the Bourgain--Guth threshold, so that "narrow at `x`" means
some cap carries at least `m(x)/Λ`.  In the broad complement no cap carries `m/Λ`, while the caps
carrying at least `m/(2K²)` already carry half of `m`; hence more than `Λ/2` caps are heavy.  To
extract *three `Ω(1)`-transverse* heavy caps one needs more heavy caps than fit in a neighbourhood
of a great circle, and at cap width `1/K` a great circle carries `≈ K` caps.  A broad/narrow
**dichotomy** — no planar case — therefore forces `Λ ≳ K`, i.e. `b ≥ 1`, and then `b(1-a) ≥ 1-a`,
a fixed power of `δ`, and the accounting fails.  Taking instead `Λ = K^{ε'}` with `ε'` small *does*
make the accounting close, but leaves the broad complement possibly planar.

**The two defects are one defect.**  Broad--narrow in `ℝ³` is a *trichotomy*, and the sketch's
dichotomy silently prices the planar case into the narrow loss, where it costs a fixed power of
`δ`.  The compiler-checked statements above are what pins that: whatever `κ` and `n` are, the
narrow half costs `b(1-a)`, so either `b ≥ 1` and the route fails, or `b < 1` and the planar case
is owed.

## What is deliberately *not* here

There is no `theorem bandDichotomy_of_trilinearKakeya`.  Stating one would be the shell game the
brief forbids: by the findings above, `Kakeya.ML2BandML.TrilinearKakeya` does **not** suffice for
`Kakeya.ML2Band.BandDichotomy` through the sketch, and what is missing is not bookkeeping.  The
missing case is the **planar** one — all heavy caps inside a small neighbourhood of a great circle
— which is neither multilinear nor a rescaling; it is the `SL₂`/slab regime, the case the whole
`VeryNotSticky` apparatus of Section 9 exists to handle.  `GWZAdapted/section9.tex` mentions none
of this.

The one statement known to discharge the band is `Kakeya.ML2Band.BandKakeya`, already proved
sufficient in `Reduction/SpineCardBand.lean` (`Kakeya.ML2Band.smallCard_of_bandKakeya`,
`Kakeya.ML2Band.bandDichotomy_of_bandKakeya`).  The tripwires in the `Target` section pin that,
verbatim, so no later edit can quietly change what this file is scoping.
-/

@[expose] public section

open MeasureTheory Topology Filter

namespace Kakeya.ML2BandML

universe u

/-- The ambient space of Main Lemma 2, as in `Kakeya.ML2Band.Space3`. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-! ## Target

Verbatim tripwires against drift in the statement this file scopes.  If
`Kakeya.ML2Band.BandKakeya` or `Kakeya.ML2Band.BandDichotomy` changes — a binder moved, a
hypothesis added or dropped — the `rfl` and the two `example`s below stop compiling. -/

section Target

/-- A verbatim copy of `Kakeya.ML2Band.BandKakeya`.  The `rfl` in
`Kakeya.ML2BandML.bandTarget_eq` is the compatibility. -/
def BandTarget : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade)

/-- **Fidelity compatibility.**  The obligation this file scopes is exactly
`Kakeya.ML2Band.BandKakeya`. -/
theorem bandTarget_eq : BandTarget.{u} = Kakeya.ML2Band.BandKakeya.{u} := rfl

/-- **Fidelity compatibility.**  The target discharges the assembly's `SmallCard`; `γ = 0` is enough to
pin the interface. -/
example : Kakeya.ML2Band.BandKakeya.{u} → Kakeya.ML2Assembly.SmallCard.{u} 0 :=
  Kakeya.ML2Band.smallCard_of_bandKakeya le_rfl

/-- **Fidelity compatibility.**  The target discharges `Kakeya.ML2Band.BandDichotomy`, the form the
assembly consumes at the budget `c ≤ g`. -/
example {β g : ℝ} : Kakeya.ML2Band.BandKakeya.{u} → Kakeya.ML2Band.BandDichotomy.{u} β g :=
  Kakeya.ML2Band.bandDichotomy_of_bandKakeya

end Target

/-! ## The multilinear ingredient

`Kakeya.ML2BandML.TrilinearKakeya` is the Bennett--Carbery--Tao/Guth inequality in the shape the
broad half of broad--narrow consumes.  It is a `def`, used by nothing; this file asserts nothing
about it. -/

section Multilinear

/-- **Quantitative `ν`-transversality of three directions in `ℝ³`.**  Every vector is controlled by
its three inner products, with constant `ν⁻¹`.  For unit vectors this is comparable to
`|det (d₁, d₂, d₃)| ≥ ν`, and it is the form the constant of a multilinear Kakeya inequality
actually depends on.

Stated coordinate-free on purpose: a coordinate reading of "transverse" is the standard way such a
predicate silently becomes vacuous.  Both halves of non-vacuity are checked below
(`Kakeya.ML2BandML.transverse_single`, `Kakeya.ML2BandML.not_transverse_const`). -/
def Transverse (ν : ℝ) (d₁ d₂ d₃ : Space3) : Prop :=
  ∀ x : Space3, ‖x‖ ≤ ν⁻¹ * (|inner ℝ d₁ x| + |inner ℝ d₂ x| + |inner ℝ d₃ x|)

/-- `a² + b² + c² ≤ (|a| + |b| + |c|)²`, the arithmetic behind
`Kakeya.ML2BandML.transverse_single`. -/
private lemma sum_sq_le_sq_abs_sum (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≤ (|a| + |b| + |c|) ^ 2 := by
  nlinarith [sq_abs a, sq_abs b, sq_abs c, abs_nonneg a, abs_nonneg b, abs_nonneg c,
    mul_nonneg (abs_nonneg a) (abs_nonneg b), mul_nonneg (abs_nonneg a) (abs_nonneg c),
    mul_nonneg (abs_nonneg b) (abs_nonneg c)]

/-- **Non-vacuity, positive half.**  The standard basis of `ℝ³` is `1`-transverse, so
`Kakeya.ML2BandML.Transverse` is satisfiable at the best possible constant. -/
theorem transverse_single :
    Transverse 1 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 2 1) := by
  intro x
  have hi : ∀ i : Fin 3, inner ℝ (EuclideanSpace.single i (1 : ℝ)) x = x i := by
    intro i
    rw [EuclideanSpace.inner_single_left]
    simp
  rw [EuclideanSpace.norm_eq x, hi 0, hi 1, hi 2, inv_one, one_mul]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ (|x 0| + |x 1| + |x 2|) ^ 2 := by
    rw [Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    exact sum_sq_le_sq_abs_sum _ _ _
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2)
      ≤ Real.sqrt ((|x 0| + |x 1| + |x 2|) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = |x 0| + |x 1| + |x 2| := Real.sqrt_sq (by positivity)

/-- **Non-vacuity, negative half.**  Three copies of one unit direction are `ν`-transverse for no
`ν`: the predicate is not satisfied by everything, so a `Kakeya.ML2BandML.TrilinearKakeya`
hypothesis cannot be discharged by feeding it degenerate triples. -/
theorem not_transverse_const (ν : ℝ) :
    ¬ Transverse ν (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 0 1) := by
  intro h
  have hx := h (EuclideanSpace.single 1 (1 : ℝ))
  have h1 : inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : Space3) = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp
  have hn : ‖(EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : Space3)‖ = 1 := by simp
  rw [hn, h1] at hx
  norm_num at hx

/-- **The multilinear (trilinear) Kakeya inequality in `ℝ³`, at loss exponent `A₀`.**

Bennett--Carbery--Tao (with Guth's endpoint) in the shape the broad half of broad--narrow consumes:
for three families of `δ`-tubes whose directions are pairwise `ν`-transverse across the families,

  `∫ ∏_{k=1}^{3} (∑_{T ∈ 𝕋_k} 1_T)^{1/2} ≤ (C/ν) · δ^{-A₀} · ∏_{k=1}^{3} (δ²·|𝕋_k|)^{1/2}`.

`A₀` is the loss exponent: BCT/Guth is the assertion that this holds for **every** `A₀ > 0`, and
`Kakeya.ML2BandML.exists_budget_of_lt_half` shows the band's broad half is content with any
`A₀ < 1/2`.  The `ν`-dependence is taken as `ν^{-1}`, which is weaker than the true `ν^{-1/2}` and
therefore keeps the `def` as weak as it can honestly be made.

**This is a `def`.  It is not proved here, it is not assumed here, and nothing in the tree depends
on it.**  See the module docstring for why no implication into `Kakeya.ML2Band.BandDichotomy` is
claimed. -/
def TrilinearKakeya (A₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type u} (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
      ∀ (s₁ s₂ s₃ : Finset ι) (T : ι → Tube δ Space3),
        (∀ i₁ ∈ s₁, ∀ i₂ ∈ s₂, ∀ i₃ ∈ s₃,
            Transverse ν (T i₁).direction (T i₂).direction (T i₃).direction) →
        (∫⁻ x, (∑ i ∈ s₁, (T i).carrier.indicator (1 : Space3 → ENNReal) x) ^ ((1 : ℝ) / 2)
                 * (∑ i ∈ s₂, (T i).carrier.indicator (1 : Space3 → ENNReal) x) ^ ((1 : ℝ) / 2)
                 * (∑ i ∈ s₃, (T i).carrier.indicator (1 : Space3 → ENNReal) x) ^ ((1 : ℝ) / 2))
          ≤ ENNReal.ofReal (C / ν) * (δ : ENNReal) ^ (-A₀)
              * ((δ : ENNReal) ^ (2 : ℝ) * (s₁.card : ENNReal)) ^ ((1 : ℝ) / 2)
              * ((δ : ENNReal) ^ (2 : ℝ) * (s₂.card : ENNReal)) ^ ((1 : ℝ) / 2)
              * ((δ : ENNReal) ^ (2 : ℝ) * (s₃.card : ENNReal)) ^ ((1 : ℝ) / 2)

end Multilinear

/-! ## The broad budget

The exponent bookkeeping of the broad half, and the surplus the band enjoys. -/

section Broad

/-- **The closing step of the broad case.**  `μ ≤ B·μ^{2/3}` forces `μ ≤ B³`.  This is the one
nonlinear step in the broad derivation: after Hölder and the fullness bound the broad alternative
reads `μ ≤ B·μ^{2/3}` with `B = 2·K^{b}·L^{2/3}·(δ²|𝕋|)^{1/3}·λ^{-2/3}`, and cubing it is what
turns the multilinear estimate into a bound on `μ`. -/
theorem le_pow_three_of_le_rpow_mul {μ B : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B)
    (h : μ ≤ B * μ ^ ((2 : ℝ) / 3)) : μ ≤ B ^ 3 := by
  set t : ℝ := μ ^ ((1 : ℝ) / 3) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hμ _
  have h3 : t ^ 3 = μ := by
    rw [ht, ← Real.rpow_natCast (μ ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hμ.le]
    norm_num
  have h2 : t ^ 2 = μ ^ ((2 : ℝ) / 3) := by
    rw [ht, ← Real.rpow_natCast (μ ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hμ.le]
    norm_num
  have hkey : t ^ 3 ≤ B * t ^ 2 := by rw [h3, h2]; exact h
  have htB : t ≤ B := by nlinarith [sq_nonneg t]
  calc μ = t ^ 3 := h3.symm
    _ ≤ B ^ 3 := by gcongr

/-- **The broad budget.**

With `K = δ^{-κ}` the Bourgain--Guth cap parameter, `b` the exponent of `K` lost in the pointwise
broad bound `m ≤ K^{b}(m₁m₂m₃)^{1/3}`, `A₀` the loss exponent of the multilinear Kakeya inequality
(`Kakeya.ML2BandML.TrilinearKakeya`), and `η` the exponent in the fullness hypothesis `λ ≥ δ^{η}`,
the broad alternative of broad--narrow closes to

  `μ ≲ δ^{1 - 3bκ - 2A₀ - 2η}`

on the band `|𝕋| < δ^{-1}` (where `δ²|𝕋| < δ` — this is the `δ¹` of surplus), so it delivers
`μ ≤ δ^{-ε}` exactly under this inequality. -/
def Budget (b κ A₀ η ε : ℝ) : Prop := 3 * b * κ + 2 * A₀ + 2 * η ≤ 1 + ε

/-- **The budget is what makes the broad alternative close.** -/
theorem broad_closes_of_budget {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {b κ A₀ η ε : ℝ}
    (h : Budget b κ A₀ η ε) :
    δ ^ (1 - 3 * b * κ - 2 * A₀ - 2 * η) ≤ δ ^ (-ε) :=
  Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by unfold Budget at h; linarith)

/-- **The band's `δ¹` of surplus, quantified: any multilinear loss with `2A₀ < 1 + ε` is
affordable.**  In particular every `A₀ < 1/2` is affordable at every `ε ≥ 0`, and every `A₀ ≤ 0`
— the Bennett--Carbery--Tao/Guth regime — trivially so.  The Bourgain--Guth constant `b` is free:
the cap parameter `κ` is chosen after it. -/
theorem exists_budget_of_lt_half {b A₀ ε : ℝ} (hb : 0 ≤ b) (h : 2 * A₀ < 1 + ε) :
    ∃ κ > (0 : ℝ), ∃ η > (0 : ℝ), Budget b κ A₀ η ε := by
  set s : ℝ := 1 + ε - 2 * A₀ with hs
  have hs0 : 0 < s := by simp only [hs]; linarith
  refine ⟨s / (24 * (b + 1)), by positivity, s / 8, by positivity, ?_⟩
  unfold Budget
  have hb1 : (0 : ℝ) < b + 1 := by linarith
  have hkey : 3 * b * (s / (24 * (b + 1))) ≤ s / 8 := by
    have e1 : 3 * b * (s / (24 * (b + 1))) = (b / (b + 1)) * (s / 8) := by
      field_simp
      ring
    have e2 : b / (b + 1) ≤ 1 := by
      rw [div_le_one hb1]
      linarith
    calc 3 * b * (s / (24 * (b + 1))) = (b / (b + 1)) * (s / 8) := e1
      _ ≤ 1 * (s / 8) := mul_le_mul_of_nonneg_right e2 (by positivity)
      _ = s / 8 := one_mul _
  linarith

/-- **The `1/2` threshold is sharp.**  A multilinear loss exponent above `(1+ε)/2` cannot be paid
for by the broad half at any cap parameter and any fullness exponent. -/
theorem not_budget_of_half_lt {b κ A₀ η ε : ℝ} (hbκ : 0 ≤ 3 * b * κ) (hη : 0 ≤ η)
    (hA₀ : (1 + ε) / 2 < A₀) : ¬ Budget b κ A₀ η ε := by
  unfold Budget
  linarith

/-- **Loomis--Whitney is not enough, at the transversality a Bourgain--Guth broad triple has.**

Mathlib's grid-lines/Loomis--Whitney inequality, applied to `δ`-tubes whose directions lie in a cap
of width `1/K = δ^{κ}`, majorises each tube by its projection, of area `≈ δ·(1/K)` rather than
`δ²`, and pays `ν^{-1/2}` for the transversality `ν ≈ 1/K` of the broad triple.  That is the loss
exponent `A₀ = 3/2 - κ`.  With any Bourgain--Guth constant `b ≥ 2` the budget then forces `2 ≤ ε`:
the route misses by two full powers of `δ`, so no choice of `κ` or `η` rescues it. -/
theorem loomisWhitney_budget_forces_two_le {b κ A₀ η ε : ℝ} (hb : 2 ≤ b) (hκ : 0 ≤ κ)
    (hη : 0 ≤ η) (hA₀ : A₀ = 3 / 2 - κ) (h : Budget b κ A₀ η ε) : 2 ≤ ε := by
  unfold Budget at h
  subst hA₀
  nlinarith

/-- **Loomis--Whitney is not enough even at perfect transversality.**  Grant the broad triple the
best conceivable transversality `ν ≈ 1`, so the only loss is the `1/K`-cap projection: then
`A₀ = 3(1-κ)/2`, and the budget still forces `2 ≤ ε` for every Bourgain--Guth constant `b ≥ 2`. -/
theorem loomisWhitney_transverse_budget_forces_two_le {b κ A₀ η ε : ℝ} (hb : 2 ≤ b) (hκ : 0 ≤ κ)
    (hη : 0 ≤ η) (hA₀ : A₀ = 3 * (1 - κ) / 2) (h : Budget b κ A₀ η ε) : 2 ≤ ε := by
  unfold Budget at h
  subst hA₀
  nlinarith

end Broad

/-! ## The narrow accounting, refuted -/

section Narrow

/-- **The exponent of the loss accumulated by `n` narrow steps of the sketch's recursion.**

The sketch pigeonholes a single cap of width `1/K = δ^{-κ}`… i.e. `K = δ^{-κ}` … localises to the
`1/K`-tubes in that direction and rescales, so step `j` runs at scale `δ_j = δ^{(1-κ)^j}` with cap
parameter `K_j = δ_j^{-κ} = δ^{-κ(1-κ)^j}` and loses `K_j^{b} = δ^{-bκ(1-κ)^j}`.  This is the
*charitable* reading: accounting instead with the initial `K` at every step gives the larger
`b·κ·n` (`Kakeya.ML2BandML.narrowLossExponent_le_mul`). -/
noncomputable def narrowLossExponent (b κ : ℝ) (n : ℕ) : ℝ :=
  b * ∑ j ∈ Finset.range n, κ * (1 - κ) ^ j

/-- The geometric sum in closed form: the accumulated narrow loss exponent is `b(1 - (1-κ)^n)`. -/
theorem narrowLossExponent_eq (b : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (n : ℕ) :
    narrowLossExponent b κ n = b * (1 - (1 - κ) ^ n) := by
  have hne : (1 - κ) ≠ 1 := by
    intro hcon
    exact hκ (by linarith [sub_eq_iff_eq_add.mp hcon])
  have hsum : ∑ j ∈ Finset.range n, κ * (1 - κ) ^ j = 1 - (1 - κ) ^ n := by
    rw [← Finset.mul_sum, geom_sum_eq hne n]
    field_simp
    ring
  rw [narrowLossExponent, hsum]

/-- **The refined accounting is the smaller one**: `b(1-(1-κ)^n) ≤ b·κ·n`, so refuting the refined
reading refutes the literal `K^{bn} = δ^{-bκn}` of the sketch as well. -/
theorem narrowLossExponent_le_mul {b κ : ℝ} (hb : 0 ≤ b) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (n : ℕ) :
    narrowLossExponent b κ n ≤ b * (κ * n) := by
  rcases eq_or_lt_of_le hκ0 with h | h
  · simp [narrowLossExponent, ← h]
  rw [narrowLossExponent_eq b (ne_of_gt h) n]
  have hbern : 1 + (n : ℝ) * (-κ) ≤ (1 + (-κ)) ^ n := one_add_mul_le_pow (by linarith) n
  have hb2 : (1 : ℝ) - (n : ℝ) * κ ≤ (1 - κ) ^ n := by
    simpa [sub_eq_add_neg, mul_neg] using hbern
  nlinarith

/-- **`κ` cancels.**  The narrow induction terminates when the cardinality exponent has been pushed
from `a` up to `1`, i.e. when `(1-κ)^n ≤ a`; and at that moment the accumulated loss exponent is at
least `b(1-a)`, *independently of `κ`*.  This is the defect : the number of
steps `n` grows like `1/κ`, so `κ·n` does not shrink with `κ`.  The free parameter is `b`, the
per-step Bourgain--Guth loss exponent — and see `Kakeya.ML2BandML.narrow_forces_small_step_loss`
for what a small `b` costs elsewhere. -/
theorem le_narrowLossExponent_of_terminates {b κ a : ℝ} (hb : 0 ≤ b) (hκ0 : 0 < κ) {n : ℕ}
    (hterm : (1 - κ) ^ n ≤ a) : b * (1 - a) ≤ narrowLossExponent b κ n := by
  rw [narrowLossExponent_eq b (ne_of_gt hκ0) n]
  have : 1 - a ≤ 1 - (1 - κ) ^ n := by linarith
  nlinarith

/-- **The sketch's self-consistency claim.**  For every accuracy `ε` there is a cap parameter `κ`
and a number of narrow steps `n` that both terminates the induction (`(1-κ)^n ≤ a`, i.e. the
cardinality exponent has reached `1`) and keeps the accumulated loss inside `δ^{-ε}`. -/
def SketchNarrowBudget (b a : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ, 0 < κ ∧ κ < 1 ∧ ∃ n : ℕ, (1 - κ) ^ n ≤ a ∧ narrowLossExponent b κ n ≤ ε

/-- **Refutation.**  `Kakeya.ML2BandML.SketchNarrowBudget` — "at a fixed per-step loss exponent `b`,
choosing `κ` small enough keeps the accumulated narrow loss inside any `ε`" — is false for every
`b > 0` and every cardinality exponent `a < 1`, i.e. everywhere strictly inside the band.  Choosing
`κ` small is exactly the move  makes, and it does nothing. -/
theorem not_sketchNarrowBudget {b a : ℝ} (hb : 0 < b) (ha : a < 1) : ¬ SketchNarrowBudget b a := by
  intro h
  obtain ⟨κ, hκ0, _, n, hterm, hle⟩ := h (b * (1 - a) / 2) (by positivity)
  have := le_narrowLossExponent_of_terminates hb.le hκ0 hterm
  nlinarith

/-- **What the narrow half would need.**  If some `κ` and `n` do terminate the induction from
cardinality exponent `a < 1` inside a loss `δ^{-ε}`, then the *per-step* Bourgain--Guth threshold
exponent `b` (the loss is `K^{b}` per step) is already at most `ε/(1-a)`.

This is the precise fork, and it is the point of the file.  A broad/narrow **dichotomy** — one that
owes no planar case — needs its threshold `Λ = K^{b}` large enough that the broad complement's
`> Λ/2` heavy caps cannot all sit in a neighbourhood of a great circle; at cap width `1/K` a great
circle carries `≈ K` caps, so it needs `b ≥ 1`, whence `b(1-a) ≥ 1-a` and the route needs
`ε ≥ 1-a`, while the band needs `ε` arbitrarily small.  A **trichotomy** may take `b` as small as
one likes and satisfies this inequality comfortably — at the price of owing the planar case, which
is the open one. -/
theorem narrow_forces_small_step_loss {b a ε κ : ℝ} (hb : 0 ≤ b) (hκ0 : 0 < κ) (ha : a < 1)
    {n : ℕ} (hterm : (1 - κ) ^ n ≤ a) (hle : narrowLossExponent b κ n ≤ ε) :
    b ≤ ε / (1 - a) := by
  have hkey := le_narrowLossExponent_of_terminates hb hκ0 hterm
  rw [le_div_iff₀ (by linarith)]
  linarith

end Narrow

end Kakeya.ML2BandML

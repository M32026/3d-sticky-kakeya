/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleGuardrails
public import Kakeya.DimensionThree.MainLemma2.UniformWindow
public import Kakeya.DimensionThree.MainLemma2.CoarseKTArrangeable

/-!
# Rewiring `coarseKatzTaoBound`'s consumer, and the `β`-monotonicity that prices its residual

Its proved replacement
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget_atThresholds` and the pricing of the three
hypotheses that replacement adds are in
`Kakeya.DimensionThree.MainLemma2.KTWindowThresholds` and
`Kakeya.DimensionThree.MainLemma2.CoarseKTArrangeable`. This file supplies the two things that
pricing left open.

## 1. The rewired consumer, compiled

`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` (`AScaleInterface.lean`) is the **only**
consumer of the refuted statement.  `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale_atThresholds`
below has that consumer's conclusion **verbatim** and is proved from the repaired estimate, with
the three added hypotheses in the shape the two branch call sites can meet.  Two `example`s pin
both routes into the same `Prop`, so drift in either breaks the build.

Everything the rewire needs at the call site is proved here too:

* `Kakeya.VeryNotSticky.coarseBudgets_of_gain` — the budget clause `3η(1-β) ≤ exscal·(ν/180)`
  from the single gain budget `540 η ≤ exscal · ν`, which is a strengthening of the interface's
  existing binder `hνη : 90 η ≤ ν`;
* `Kakeya.VeryNotSticky.coarseRadius_of_grid` — the node radius from the nominal radius, paying
  the one grid step `δ^{-η}`;
* `Kakeya.VeryNotSticky.thickRadius_le_six_rpow_exscal` and
  `Kakeya.VeryNotSticky.transverseFillRadius_le_six_rpow_exscal` — the nominal radius bound
  `r ≤ 6 δ^{exscal}` at the two branches.  The transverse one needs **no** `CaseScale` clause,
  unlike `Kakeya.VeryNotSticky.transverseFillRadius_le_one`, which establishes it internally and
  discards it.

## 2. Where the thread stops, and why the residual is *not* irreducible

`Kakeya.VNSUniform.UniformCoarseKTEta` is recorded in
`Kakeya.DimensionThree.MainLemma2.CoarseKTArrangeable` as the price of deleting the refuted
statement, on the ground that `Kakeya.VeryNotSticky.coarseKTEta` is a `Classical.choose` value
so *"no such bound is derivable"*.  **That reading is too pessimistic, and this file shows why
by construction.**

`Kakeya.WindowFour.mono_beta`: the windowed Katz–Tao bound at exponent `β` implies the same bound,
**at the same two thresholds**, at every exponent `β' ∈ [β, 1]`.  The mechanism is
`Kakeya.maxDensity_le_card` — `Δ_max(s, W) ≤ |s|` — which makes `Δ_max^{1-β}|s|^{β}` monotone
increasing in `β`.  Consequently one pair `(ηKT, ρ₀)` obtained at the *bottom* of a window serves
the whole window, and the uniform floor is not a new analytic assumption but a consequence of
`K_KT` at the bottom exponent (`Kakeya.windowFour_uniform_of_katzTao`).

What the residual really is, then, is the **open-threshold** configuration: if
`A := {β | K_KT β}` has no least element, there is no bottom exponent to read the pair at.  That
is exactly the configuration in which `Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold`
already shows the protected Main Lemma 2 to be **refuted**, and in which
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_least` shows that a *closed* `A` needs no uniformity at
all.  So `UniformCoarseKTEta` is not an independent obligation; it is the fourth case of the
trichotomy the tree has already isolated.

## What is deliberately *not* done here

Removing
it means threading two binders — the strengthened gain budget and the fullness threshold
`2η ≤ exscal · coarseKTEta β ν` — from `rScaleParentData_of_gridScale` up through
`exists_aScaleInputs`, `exists_aScaleData_of_le_one`, `exists_aScaleData`, the six-step thick
chain, the transverse chain, `exists_goalMult`, and both of `vnsBody_of_params` and
`multiplicity_le_of_card_isEssDistinct_ge`. The second binder is an upper bound on `η` and can
only be met where `η` is chosen; on the non-uniform route
`Kakeya.VeryNotSticky.exists_eta_coarseKT_caseParams` meets it for free, but on the `β`-uniform
route it needs one `η` for a continuum of `β`, and **`Kakeya.VNSUniform.CaseParams.mono_beta`
cannot carry it**, `coarseKTEta` having no monotonicity in `β`.

No statement is weakened below, no hypothesis is introduced that no call site can supply, and
every declaration is proved outright.
-/

@[expose] public section

universe u

open MeasureTheory Metric Set ShadedBody Filter Topology
open scoped ENNReal NNReal

namespace Kakeya

/-- **One pair of thresholds serves a whole window `[β₀, 1]`.**

`K_KT(β₀)` produces a pair `(ηKT, ρ₀)` at the bottom exponent, and
`Kakeya.WindowFour.mono_beta` carries it to every `β ∈ [β₀, 1]`.  So the `β`-uniform lower bound
on the fullness exponent that the deletion of `Kakeya.VeryNotSticky.coarseKatzTaoBound` needs is
**not** an independent analytic assumption: it follows from the Katz–Tao estimate at the bottom
of the window.  What is genuinely missing is a *bottom* — see the module docstring. -/
theorem windowFour_uniform_of_katzTao {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] {β₀ : ℝ} (hβ₀0 : 0 ≤ β₀) (hβ₀1 : β₀ ≤ 1)
    (h : KatzTaoEstimate.{u} E β₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × NNReal, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧
      ∀ β ∈ Set.Icc β₀ 1, WindowFour.{u} E β ε p.1 p.2 := by
  obtain ⟨p, hp1, hp2, hp3, hwin⟩ := exists_windowFour hβ₀0 hβ₀1 h hε
  exact ⟨p, hp1, hp2, hp3, fun β hβ ↦ WindowFour.mono_beta hβ.1 hβ.2 hwin⟩

/-- **The uniform threshold pair exists whenever the Katz–Tao set has a least element in the
window.**

Let `A := {β | K_KT β}`, which is up-closed by `Kakeya.KatzTaoEstimate.mono`.  If `A ∩ [β₀,1]`
has a least element `m`, then the pair produced at `m` serves **every** `β ∈ [β₀,1]` at which
the estimate holds: `Kakeya.WindowFour.mono_beta` carries it up from `m`, and minimality puts
every such `β` above `m`.

This is the reduction the residual `Kakeya.VNSUniform.UniformCoarseKTEta` actually needs.  It is
*not* an independent analytic assumption about a `Classical.choose` value: it is the statement
that `A ∩ [β₀,1]` is empty or closed at its infimum — the same trichotomy
`Kakeya.VNSUniform.katzTaoEstimate_sub_of_trichotomy` already runs, whose fourth case
`Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` shows to **refute** the protected Main
Lemma 2 outright. -/
theorem windowFour_uniform_of_least {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] {β₀ : ℝ} (hβ₀0 : 0 ≤ β₀) {ε : ℝ} (hε : 0 < ε)
    (hleast : ∃ m ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} E m ∧
      ∀ b ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} E b → m ≤ b) :
    ∃ p : ℝ × NNReal, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧
      ∀ β ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} E β → WindowFour.{u} E β ε p.1 p.2 := by
  obtain ⟨m, hm, hKTm, hmin⟩ := hleast
  obtain ⟨p, hp1, hp2, hp3, hwin⟩ :=
    exists_windowFour (le_trans hβ₀0 hm.1) hm.2 hKTm hε
  exact ⟨p, hp1, hp2, hp3, fun β hβ hKTβ ↦ WindowFour.mono_beta (hmin β hβ hKTβ) hβ.2 hwin⟩

/-- **The empty case.**  If the estimate holds nowhere in the window the requirement is vacuous,
so any pair serves.  Together with `Kakeya.windowFour_uniform_of_least` this covers every case of
the trichotomy except the open threshold. -/
theorem windowFour_uniform_of_none {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {β₀ ε : ℝ} (hnone : ∀ β ∈ Set.Icc β₀ 1, ¬ KatzTaoEstimate.{u} E β) :
    ∃ p : ℝ × NNReal, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧
      ∀ β ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} E β → WindowFour.{u} E β ε p.1 p.2 :=
  ⟨(1, 1 / 2), one_pos, by norm_num, le_rfl, fun β hβ hKT ↦ absurd hKT (hnone β hβ)⟩

/-- **The reduction, in one statement.**  The `β`-uniform threshold pair that retiring
`Kakeya.VeryNotSticky.coarseKatzTaoBound` needs exists as soon as the Katz–Tao set is empty or
closed at its infimum on the window.  So the residual
`Kakeya.VNSUniform.UniformCoarseKTEta` is *not* irreducible: it is the fourth case of the
trichotomy, and no new analytic input is required in the other three. -/
theorem windowFour_uniform_of_not_open_threshold {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] {β₀ : ℝ} (hβ₀0 : 0 ≤ β₀) {ε : ℝ} (hε : 0 < ε)
    (h : (∀ β ∈ Set.Icc β₀ 1, ¬ KatzTaoEstimate.{u} E β) ∨
      ∃ m ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} E m ∧
        ∀ b ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} E b → m ≤ b) :
    ∃ p : ℝ × NNReal, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧
      ∀ β ∈ Set.Icc β₀ 1, KatzTaoEstimate.{u} E β → WindowFour.{u} E β ε p.1 p.2 := by
  rcases h with hnone | hleast
  · exact windowFour_uniform_of_none hnone
  · exact windowFour_uniform_of_least hβ₀0 hε hleast

/-! ## The `β`-uniform threshold pair, discharged by the trichotomy

`Kakeya.VNSUniform.UniformCoarseKTEta` is recorded in
`Kakeya.DimensionThree.MainLemma2.CoarseKTArrangeable` as the price of retiring
`Kakeya.VeryNotSticky.coarseKatzTaoBound`.  **It is the wrong object, and that is why it looked
unpayable.**  It asserts a positive lower bound on `Kakeya.VeryNotSticky.coarseKTEta`, which is
`Classical.choose` applied to an existential: knowing that a *good* pair exists says nothing
about the pair the choice function returns, so no amount of mathematics can bound it below.  The
statement is not hard, it is *about the wrong thing*.

What the retirement actually needs is a **pair**, not a bound on a choice: one
`(ηKT, ρ₀)` satisfying `Kakeya.WindowFour` at every exponent of the window at which the partial
estimates hold.  That is `Kakeya.UniformWindowPair`, and it is **proved outright** below —
`Kakeya.exists_uniformWindowPair` — with no residual, from
`Kakeya.VNSUniform.estimateSet_shape`, which is itself proved and which is where the
open-threshold case is eliminated.
-/

/-! ### The open-threshold branch, closed twice over

The reason `Kakeya.exists_uniformWindowPair` has only **two** cases and not three is that the
open-threshold configuration — an infimum `m` of the estimate set that is not attained — cannot
occur.  The two theorems below put both halves of that on the record as proof terms rather than
prose: the configuration is *impossible* (`Kakeya.openThreshold_impossible`, from the closedness
of the two estimate sets — the same fact `Kakeya.VNSUniform.estimateSet_shape` is built on) and,
independently, it would *refute the protected conclusion* if it did occur (`Kakeya.openThreshold_refutes_monotone_drop`, from
`Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold`).  Either alone closes the branch;
together they are why no residual is left. -/

/-- **The open-threshold configuration cannot occur.**

If both partial estimates hold at every exponent strictly above `m` in `(m,1]`, they hold at `m`
— that is the closedness of the two estimate sets,
`Kakeya.VNSUniform.katzTaoEstimate_of_forall_gt` and
`Kakeya.VNSUniform.frostmanEstimate_of_forall_gt`.  So an unattained infimum is impossible, and
`Kakeya.exists_uniformWindowPair` needs only the two cases
`Kakeya.VNSUniform.estimateSet_shape` provides.  No hypothesis below the threshold is used. -/
theorem openThreshold_impossible {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (hnot : ¬ (KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m ∧
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) m))
    (habove : ∀ β : ℝ, m < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β ∧
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) : False :=
  hnot ⟨VNSUniform.katzTaoEstimate_of_forall_gt hm0 hm1
      (fun β hβ hβ1 ↦ (habove β hβ hβ1).1),
    VNSUniform.frostmanEstimate_of_forall_gt hm0 hm1
      (fun β hβ hβ1 ↦ (habove β hβ hβ1).2)⟩

/-- **And if it did occur, it would refute the protected conclusion.**  This is
`Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` read at the Katz--Tao predicate, and it
is the independent second reason the branch is closed. -/
theorem openThreshold_refutes_monotone_drop {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (hbelow : ∀ x : ℝ, x < m → ¬ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) x)
    {ν : ℝ → ℝ} (hmono : MonotoneOn ν (Set.Ioc (0 : ℝ) 1))
    (hpos : ∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β)
    (hstep : ∀ β : ℝ, m < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β)) : False :=
  VNSUniform.no_monotoneOn_drop_of_open_threshold hm0 hm1 hbelow hmono hpos hstep

/-- **The defining property**, available unconditionally because
`Kakeya.exists_uniformWindowPair` is. -/
theorem windowPairData_spec {β₀ : ℝ} (hβ₀0 : 0 < β₀) (hβ₀1 : β₀ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    UniformWindowPair.{u} β₀ ε (windowPairData.{u} β₀ ε) := by
  classical
  have hex : ∃ p : ℝ × NNReal, UniformWindowPair.{u} β₀ ε p :=
    exists_uniformWindowPair hβ₀0 hβ₀1 hε
  have hval : windowPairData.{u} β₀ ε = hex.choose := by rw [windowPairData, dif_pos hex]
  rw [hval]
  exact hex.choose_spec

/-- **The pair, delivered at the exponent and loss a consumer actually uses.**

From the window datum at `(β₀, ε)` and the two comparisons `β₀ ≤ β` and `ε ≤ ε'`, the windowed
bound holds at `(β, ε')` at the *same* thresholds.  This is the only fact a consumer needs, and
it is what makes the pair threadable through the case split as two `β`-free numbers. -/
theorem windowFour_of_windowPair {β₀ : ℝ} (hβ₀0 : 0 < β₀) (hβ₀1 : β₀ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {β : ℝ} (hβ : β ∈ Set.Icc β₀ 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    {ε' : ℝ} (hεε' : ε ≤ ε') :
    WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) β ε'
      (windowPairData.{u} β₀ ε).1 (windowPairData.{u} β₀ ε).2 :=
  WindowFour.mono_eps (le_trans (windowPairData_snd_le_half β₀ ε) (by norm_num)) hεε'
    ((windowPairData_spec hβ₀0 hβ₀1 hε).2.2.2 β hβ hKT hF)

namespace VeryNotSticky

/-! ## What the rewired consumer needs at its call sites -/

/-- **The budget clause of `coarseKatzTaoBound_of_etaBudget_atThresholds`, from one gain budget.**

`540 η ≤ exscal · ν` gives `3η(1-β) ≤ exscal·(ν/180)`, using only `β ≤ 1` and `0 < exscal`.  It
is the strengthening of the interface's existing binder `hνη : 90 cfg.η ≤ ν` that the repair
costs, and it is a bound on `η` alone once `ν`, `β` and `exscal` are fixed — with `η` chosen
last, exactly as `Kakeya.VeryNotSticky.exists_eta_coarseKT_caseParams` chooses it. -/
theorem coarseBudgets_of_gain (cfg : VeryNotSticky.{u}) {ν : ℝ}
    (hbud : 540 * cfg.η ≤ cfg.exscal * ν) :
    3 * cfg.η * (1 - cfg.β) ≤ cfg.exscal * (ν / 180) := by
  have hexs : 0 < cfg.exscal := cfg.hexscal
  have hη : 0 < cfg.η := cfg.hη
  have hβ1 : cfg.β ≤ 1 := cfg.hβ1
  have hβ0 : 0 < cfg.β := cfg.hβ
  nlinarith

/-- **Pin: `Kakeya.VeryNotSticky.CoarseKatzTaoStatement` is false.**

`Kakeya.VeryNotSticky.coarseKatzTao_refutes_config` derives `False` from that `Prop` together
with any configuration in the regime `cfg.δ < 1`, `cfg.β < 1/2`; this is that theorem read as a
negation.  It is the replacement for the tripwire
`example : CoarseKatzTaoStatement := @coarseKatzTaoBound` of
`Kakeya.DimensionThree.MainLemma2.AScaleGuardrails`, which cannot survive the removal of the
refuted declaration, and it says strictly more than that tripwire said. -/
theorem statement_of_universal_coarseKatzTao_false (cfg : VeryNotSticky.{u})
    (hδlt : cfg.δ < 1) (hβ : cfg.β < 1 / 2) : ¬ CoarseKatzTaoStatement.{u} :=
  fun H => coarseKatzTao_refutes_config H cfg hδlt hβ

/-- The conclusion of `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale`, verbatim, as a
`Prop` in its own right, so that both routes can be pinned into it. -/
def RScaleParentDataConclusion (cfg : VeryNotSticky.{u}) (ν : ℝ) (r : NNReal)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι) : Prop :=
  ∃ volT volTa Δ Na Nf : ENNReal,
    Na ≠ 0 ∧ Na ≠ ⊤ ∧ Nf ≠ ⊤ ∧
    ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier = volT * (cfg.s.card : ENNReal) ∧
    (cfg.δ : ENNReal) ^ (2 * cfg.η) * (Na * volTa) ≤
      (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β *
        volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ∧
    Δ * (Nf * (cfg.δ : ENNReal) ^ 2) ≤
      (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 ∧
    (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT) ≤
      (cfg.δ : ENNReal) ^ 2 * volTa ∧
    (cfg.s.card : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 2 * (Na * Nf)

/-! ## The rewired consumer, compiled

`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` (`AScaleInterface.lean:277`) is the **only**
consumer of the refuted `coarseKatzTaoBound`.  The theorem below has its conclusion **verbatim**
and is proved from the *repaired*
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget_atThresholds`, with the three added
hypotheses in the shape the branch call sites can meet:

* `hbud : 540 cfg.η ≤ cfg.exscal · ν` — a strengthening of the existing binder
  `hνη : 90 cfg.η ≤ ν`, which yields the budget clause by `coarseBudgets_of_gain`;
* `hηKT : 2 cfg.η ≤ cfg.exscal · coarseKTEta cfg.β ν` — the fullness threshold, an upper bound
  on `cfg.η` that `Kakeya.VeryNotSticky.exists_eta_coarseKT_caseParams` meets for free where
  `η` is chosen;
* `hrsmall : r ≤ 6 δ^{exscal}` together with
  `hδrad : 6 δ^{exscal-η} ≤ coarseKTRadius cfg.β ν` — the radius threshold, reduced from the
  node radius to the nominal radius by `coarseRadius_of_grid` and thence to a smallness
  condition on `δ` that `Kakeya.VeryNotSticky.eventually_rpow_le_coarseKTRadius` supplies inside
  the `∀ᶠ δ` the case split already carries.

Two interior differences from the original, both forced by the density slot moving from
`δ^{ν/45}` to `δ^{2η}`, and both invisible in the signature because `Δ` is existentially
quantified: the witness `Δ` is `δ^{2η}(δ^{η} Δ_max)`, and the two-scale step is
`Kakeya.VeryNotSticky.rpow_two_eta_mul_sq_le_sq_of_gridStep` rather than
`Kakeya.VeryNotSticky.rpow_mul_sq_le_sq_of_gridStep` — whose own proof passes through
`2η ≤ ν/45` and discards the surplus.

Everything else is reproduced unchanged.  **This is the compiled evidence that step 3 of the
retirement thread is sound**; what stops the thread is step 4 on the `β`-uniform route, not
this. -/
set_option linter.unusedVariables false in
theorem rScaleParentData_of_gridScale_atPair (cfg : VeryNotSticky.{u}) {ν ε₀ ηKT : ℝ}
    {ρ₀ : NNReal} (hν : 0 < ν)
    (hνη : 90 * cfg.η ≤ ν) (hbud : 540 * cfg.η ≤ cfg.exscal * ν)
    (hε₀ν : ε₀ ≤ ν / 180)
    (hηKTpos : 0 < ηKT) (hρ₀half : ρ₀ ≤ 1 / 2)
    (hW : WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) cfg.β ε₀ ηKT ρ₀)
    (hηKT : 2 * cfg.η ≤ cfg.exscal * ηKT)
    (hδrad : 6 * cfg.δ ^ (cfg.exscal - cfg.η) ≤ ρ₀)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {r ρ : NNReal}
    (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (har : cfg.a ≤ r) (hr1 : r ≤ 1) (hrρ : r ≤ ρ) (hρr : ρ ≤ cfg.δ ^ (-cfg.η) * r)
    (hρ1 : ρ ≤ 1) (hrsmall : r ≤ 6 * cfg.δ ^ cfg.exscal)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    ∃ volT volTa Δ Na Nf : ENNReal,
      Na ≠ 0 ∧ Na ≠ ⊤ ∧ Nf ≠ ⊤ ∧
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier = volT * (cfg.s.card : ENNReal) ∧
      (cfg.δ : ENNReal) ^ (2 * cfg.η) * (Na * volTa) ≤
        (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ∧
      Δ * (Nf * (cfg.δ : ENNReal) ^ 2) ≤
        (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 ∧
      (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT) ≤
        (cfg.δ : ENNReal) ^ 2 * volTa ∧
      (cfg.s.card : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 2 * (Na * Nf) := by
  classical
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨j, hj⟩ := activeTubeNodes_nonempty cfg 𝒰 hk (s_nonempty cfg)
  have hjIdx : j ∈ 𝒰.cover.indexSet k := mem_indexSet_of_mem_activeTubeNodes cfg 𝒰 hj
  let volT : ENNReal := cfg.meanTubeVolume
  let volTa : ENNReal := (Tube.le_volume.c 3 : ENNReal) * (ρ : ENNReal) ^ 2
  let Na : ENNReal := (G.outerSet.card : ENNReal)
  let Nf : ENNReal := ((cfg.tubeFibre 𝒰 k j).card : ENNReal)
  let md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j' => (𝒰.cover.tube k j').toConvexSpaceBody)
  let Delta : ENNReal := (cfg.δ : ENNReal) ^ (2 * cfg.η) *
    ((cfg.δ : ENNReal) ^ cfg.η * md)
  have hVol : ∀ j0 ∈ G.outerSet, volTa ≤ volume (G.outerBody j0).carrier := by
    intro j0 hj0
    have hlb : (Tube.le_volume.c 3 : ENNReal) * (ρ : ENNReal) ^ 2 ≤
        volume (𝒰.cover.tube k j0).carrier := by
      simpa [hfin, hgrid] using (Tube.le_volume (𝒰.cover.tube k j0))
    have hcar1 : (G.outerBody j0).carrier = (𝒰.cover.tube k j0).carrier :=
      congrArg ConvexSpaceBody.carrier (houterBody j0 hj0)
    dsimp [volTa]
    rw [hcar1]
    exact hlb
  have hKT : ShadedBody.multiplicity G.outerSet G.outerBody ≤
      (cfg.a : ENNReal) ^ (-(ν / 90)) * Delta ^ (1 - cfg.β) *
        (G.outerSet.card : ENNReal) ^ cfg.β := by
    simpa [Delta, md] using
      (coarseKatzTaoBound_of_etaBudget_atPair cfg (by linarith)
        (by
          have h1 := coarseBudgets_of_gain cfg hbud
          have hexs : (0 : ℝ) < cfg.exscal := cfg.hexscal
          have h2 : ν / 180 ≤ ν / 90 - ε₀ := by linarith
          have h3 := mul_le_mul_of_nonneg_left h2 hexs.le
          linarith)
        hηKTpos hρ₀half hW 𝒰 hk hgrid ⟨le_trans har hrρ, hρ1⟩
        (le_trans (coarseRadius_of_grid cfg hρr hrsmall) hδrad) hηKT G houterSet houterBody hfull)
  have hMass : (cfg.δ : ENNReal) ^ (2 * cfg.η) * ((G.outerSet.card : ENNReal) * volTa) ≤
      (cfg.δ : ENNReal) ^ (-(ν / 90)) * Delta ^ (1 - cfg.β) *
        (G.outerSet.card : ENNReal) ^ cfg.β *
        volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := by
    exact coarseMassBound cfg hν (le_trans har hr1) cfg.hdims.1 hfull hVol hKT
  have hstep : (cfg.δ : ENNReal) ^ (2 * cfg.η) * (ρ : ENNReal) ^ 2 ≤ (r : ENNReal) ^ 2 :=
    rpow_two_eta_mul_sq_le_sq_of_gridStep (cfg := cfg) (hρ := hρr)
  have hMax : md * Nf * (cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ 2 ≤
      (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (ρ : ENNReal) ^ 2 := by
    simpa [md, Nf] using (maxDensity_activeTubeNodes_le cfg cfg.hC₀ 𝒰 hk cfg.hD₀ hjIdx hgrid hρ1)
  refine ⟨volT, volTa, Delta, Na, Nf, ?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8⟩
  · have hNon : G.outerSet.Nonempty := by
      rw [houterSet]
      exact activeTubeNodes_nonempty cfg 𝒰 hk (s_nonempty cfg)
    have hpos : 0 < G.outerSet.card := Finset.card_pos.mpr hNon
    dsimp [Na]
    exact_mod_cast (ne_of_gt hpos)
  · dsimp [Na]
    exact ENNReal.natCast_ne_top _
  · dsimp [Nf]
    exact ENNReal.natCast_ne_top _
  · dsimp [volT]
    exact sum_volume_eq cfg
  · simpa [Na] using hMass
  · calc
      Delta * (Nf * (cfg.δ : ENNReal) ^ 2)
          = (cfg.δ : ENNReal) ^ (2 * cfg.η) *
              (md * Nf * (cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ 2) := by
            dsimp [Delta]
            ring
      _ ≤ (cfg.δ : ENNReal) ^ (2 * cfg.η) *
            ((deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (ρ : ENNReal) ^ 2) := by
            gcongr
      _ = (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) *
            ((cfg.δ : ENNReal) ^ (2 * cfg.η) * (ρ : ENNReal) ^ 2) := by
            ring
      _ ≤ (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 := by
            gcongr
  · dsimp [volT, volTa]
    exact tubeVolumeRatio_of_le hrρ (meanTubeVolume_le cfg)
  · have hcnt : (cfg.s.card : NNReal) ≤
        cfg.C₀ ^ 2 * (((cfg.activeTubeNodes 𝒰 k).card : NNReal) *
          ((cfg.tubeFibre 𝒰 k j).card : NNReal)) :=
      (card_le_card_activeTubeNodes_mul cfg 𝒰 hk cfg.hD₀ hjIdx).1
    dsimp [Na, Nf]
    rw [houterSet]
    exact_mod_cast hcnt

/-! ### The two instantiations

`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale_atPair` is stated at an arbitrary threshold
pair.  The two routes through the case split instantiate it differently, and that is the whole
architectural point:

* the **pointwise** route uses the Skolem pair of `Kakeya.DimensionThree.MainLemma2.KTWindowThresholds`,
  which is what `Kakeya.VeryNotSticky.exists_eta_coarseKT_caseParams` already bounds `η` against;
* the **`β`-uniform** route uses `Kakeya.windowPairData`, whose two components do **not** move
  with `β`.  That is what `Kakeya.VNSUniform.CaseParams.mono_beta` can carry and
  `Kakeya.VeryNotSticky.coarseKTEta` cannot, and it is why the residual
  `Kakeya.VNSUniform.UniformCoarseKTEta` is not needed. -/

set_option linter.unusedVariables false in
/-- **Pointwise instantiation.**  The consumer's conclusion from the Skolem thresholds — the form
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` would take on the non-uniform route. -/
theorem rScaleParentData_of_gridScale_atThresholds (cfg : VeryNotSticky.{u}) {ν : ℝ} (hν : 0 < ν)
    (hνη : 90 * cfg.η ≤ ν) (hbud : 540 * cfg.η ≤ cfg.exscal * ν)
    (hηKT : 2 * cfg.η ≤ cfg.exscal * coarseKTEta.{u} cfg.β ν)
    (hδrad : 6 * cfg.δ ^ (cfg.exscal - cfg.η) ≤ coarseKTRadius.{u} cfg.β ν)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {r ρ : NNReal}
    (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (har : cfg.a ≤ r) (hr1 : r ≤ 1) (hrρ : r ≤ ρ) (hρr : ρ ≤ cfg.δ ^ (-cfg.η) * r)
    (hρ1 : ρ ≤ 1) (hrsmall : r ≤ 6 * cfg.δ ^ cfg.exscal)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    RScaleParentDataConclusion.{u} cfg ν r G :=
  rScaleParentData_of_gridScale_atPair cfg hν hνη hbud le_rfl
    (coarseKTEta_pos cfg.hβ.le cfg.hβ1 cfg.ktEstimate hν) (coarseKTRadius_le_half cfg.β ν)
    (coarseKT_windowFour cfg.hβ.le cfg.hβ1 cfg.ktEstimate hν) hηKT hδrad
    𝒰 hk hgrid har hr1 hrρ hρr hρ1 hrsmall G houterSet houterBody hfull

set_option linter.unusedVariables false in
/-- **`β`-uniform instantiation — the one the residual was blocking.**

Every threshold is read from `Kakeya.windowPairData β₀ ε₀`, a pair of numbers depending on the
window bottom and the loss exponent alone.  The configuration supplies `cfg.ktEstimate` and
`cfg.fEstimate`, and `Kakeya.windowFour_of_windowPair` converts them into the windowed bound at
`(cfg.β, ν/180)`.  Nothing here is assumed: `Kakeya.exists_uniformWindowPair` is proved from
`Kakeya.VNSUniform.estimateSet_shape`. -/
theorem rScaleParentData_of_gridScale_atWindowPair (cfg : VeryNotSticky.{u}) {ν β₀ ε₀ : ℝ}
    (hν : 0 < ν) (hνη : 90 * cfg.η ≤ ν) (hbud : 540 * cfg.η ≤ cfg.exscal * ν)
    (hβ₀0 : 0 < β₀) (hβ₀1 : β₀ ≤ 1) (hε₀ : 0 < ε₀) (hε₀ν : ε₀ ≤ ν / 180)
    (hβwin : cfg.β ∈ Set.Icc β₀ 1)
    (hηKT : 2 * cfg.η ≤ cfg.exscal * (windowPairData.{u} β₀ ε₀).1)
    (hδrad : 6 * cfg.δ ^ (cfg.exscal - cfg.η) ≤ (windowPairData.{u} β₀ ε₀).2)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {r ρ : NNReal}
    (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (har : cfg.a ≤ r) (hr1 : r ≤ 1) (hrρ : r ≤ ρ) (hρr : ρ ≤ cfg.δ ^ (-cfg.η) * r)
    (hρ1 : ρ ≤ 1) (hrsmall : r ≤ 6 * cfg.δ ^ cfg.exscal)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    RScaleParentDataConclusion.{u} cfg ν r G :=
  rScaleParentData_of_gridScale_atPair cfg hν hνη hbud hε₀ν
    (windowPairData_fst_pos β₀ ε₀) (windowPairData_snd_le_half β₀ ε₀)
    (windowFour_of_windowPair hβ₀0 hβ₀1 hε₀ hβwin cfg.ktEstimate cfg.fEstimate le_rfl)
    hηKT hδrad 𝒰 hk hgrid har hr1 hrρ hρr hρ1 hrsmall G houterSet houterBody hfull

end VeryNotSticky

end Kakeya

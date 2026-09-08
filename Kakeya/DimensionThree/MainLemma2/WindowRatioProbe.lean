/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyUniform

/-!
# The loss-to-fullness ratio of the Katz–Tao window: what the tree's input does and does not give

 Consider the inequality on `Kakeya.CoarseKTWindow`'s own two exponents,

```
c * we ≤ 2 ^ 18 * wη
```

(the *loss-to-fullness ratio*), as the one thing the tangential branch's fullness half needs and
cannot pay: `frev49_fullness_forces_window_ratio` derives it from the transported enclosure
requirement, `frev49_window_ratio_not_derivable` exhibits admissible numerals violating it, and
`frev49_window_ratio_satisfiable` exhibits admissible numerals meeting it — so it is a decision,
not a dead end.   The scalar condition of Option R *is* that ratio
(`optionR_is_the_window_ratio`) and that `Kakeya.exists_uniformWindowPair` supplies no clause
relating its input `ε` to its output `p.1`.

This file answers the next question — **is the ratio provable as a strengthening of
`Kakeya.exists_uniformWindowPair`'s conclusion?** — and the answer is *no*, for a reason sharper
than "no clause relates them".  Nothing here is read by the tree; every declaration is a new
theorem, and no statement anywhere is cut.

## What is established

**(A) The two transports the tree has, and their direction.**  `Kakeya.WindowFour` is *monotone*
in the loss exponent (`Kakeya.WindowFour.mono_eps`, existing) and, proved here, *antitone* in the
fullness exponent (`Kakeya.WindowFour.mono_etaKT`): the pair may always be moved to a larger loss
or to a smaller threshold.  Both moves are lifted to `Kakeya.UniformWindowPair`
(`Kakeya.UniformWindowPair.mono_eps`, `Kakeya.UniformWindowPair.anti_eta`).

**(B) Both transports run away from the ratio.**  `Kakeya.uniformWindowPair_ratio_not_gained`:
from a pair at which `c * we ≤ K * wη` fails, *every* pair reachable by the two available moves
still fails.  So no application of the tree's own window monotonicity lemmas can manufacture the
ratio.

**(C) The ratio is independent of the Katz–Tao quantifier shape.**  `Kakeya.KTWindowShape`
bundles exactly the three structural facts the tree's window producer is known to have —
monotone in the loss, antitone in the threshold, inhabited at every positive loss.  It is not a
strawman: `Kakeya.uniformWindowShape` is an instance built from `Kakeya.exists_uniformWindowPair`
and (A).  And the ratio is independent of it: `Kakeya.ratioFailingShape` is a shape at which the
ratio fails at *every* admissible pair, `Kakeya.ratioSatisfyingShape` one at which it holds.
`Kakeya.no_ratio_producer_from_shape_even_with_free_loss` is the sharp form — even granting the
producer the freedom to *choose* the loss exponent anywhere below `Kakeya.CoarseKTWindow.hwe`'s
ceiling, the shape does not yield the ratio.

**(D) Along the tree's own producer chain the loss exponent cancels identically, and the ratio
becomes an accuracy-independent floor on GWZ Definition 3.4's threshold function.**  The chain
`Kakeya.exists_uniformWindowPair → Kakeya.exists_windowFour →
Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window →
Kakeya.KatzTaoEstimate.multiplicity_bound_generalize → Kakeya.KatzTaoEstimate` returns, at loss
`ε` and from a raw Katz–Tao threshold `η₀`, the fullness exponent `ε * η₀ / (4 * (4 + η₀))` in
`EuclideanSpace ℝ (Fin 3)`.  `Kakeya.windowChain_ratio_iff_thresholdFloor` says the ratio at that
value is *equivalent* to `16 * c ≤ (K - 4 * c) * η₀` — in which `ε` does not appear.  GWZ's own
Remark 3.6 construction `η(β,ϵ) = ϵ η₁(β,ϵ) / 100` gives the same shape
(`Kakeya.gwzRemark36_ratio_iff_thresholdFloor`).

**(E) The parameter-order fact.**  `Kakeya.ratio_free_for_noninput_parameter`: a loss parameter
that is *not* an input of the producer — GWZ's `η_bias`, bounded only from above — always meets
the ratio, because it may be chosen after the threshold.  Contrast (C): the producer's *input*
cannot.  That difference of order, not any difference of strength, is the whole gap.

## What is NOT established here

No refutation of `Kakeya.KatzTaoEstimate` itself.  (C) refutes derivability from the quantifier
shape together with the monotonicities the tree has; a genuine counter-instance of
`Kakeya.KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β` would be a statement about Kakeya sets in
`ℝ³` that nobody has.  The identification in (D) of the produced fullness exponent with
`ε * η₀ / (4 * (4 + η₀))` is read off the two proof scripts
(`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, which sets `η := ε * η₁ / M` with
`M = finrank + η₁ + 1`, and `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`, which
calls it at `ε / 2` and returns `η₁ / 2`); the *arithmetic consequence* is what is compiled here,
The formula describes that construction; the arithmetic consequence is the theorem established here.
-/

@[expose] public section

universe u

open Set Filter Topology
open scoped NNReal

namespace Kakeya

/-! ### (A) The two transports, and the one that was missing -/

/-- **The windowed bound transports downward in the fullness exponent.**

Companion of `Kakeya.WindowFour.mono_eps`, and the second of the only two transports the tree
has for a window pair.  The content is one line: the auxiliary scale satisfies `τ ≤ ρ ≤ ρ₀ ≤ 1`,
so `τ ^ ηKT` is *non-increasing* in `ηKT`; lowering the exponent therefore strengthens the
fullness hypothesis, and a statement proved under the weaker hypothesis holds under the stronger
one.

Direction matters, and it is the point of this file: the pair can always be moved to a
**smaller** threshold, never to a larger one. -/
theorem WindowFour.mono_etaKT {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {β ε ηKT ηKT' : ℝ} {ρ₀ : NNReal} (hρ₀ : ρ₀ ≤ 1) (hle : ηKT' ≤ ηKT)
    (h : WindowFour.{u} E β ε ηKT ρ₀) : WindowFour.{u} E β ε ηKT' ρ₀ := by
  intro ρ hρ0 hρρ₀ τ hτ0 hτρ ι s T hball hfull
  refine h ρ hρ0 hρρ₀ τ hτ0 hτρ s T hball ?_
  refine le_trans ?_ hfull
  have hτ1 : τ ≤ 1 := le_trans hτρ (le_trans hρρ₀ hρ₀)
  exact NNReal.rpow_le_rpow_of_exponent_ge hτ0 hτ1 hle

/-- **A uniform window pair transports upward in the loss exponent.**  `Kakeya.WindowFour.mono_eps`
at the level of `Kakeya.UniformWindowPair`; the radius threshold is unchanged, and `p.2 ≤ 1/2`
supplies that lemma's `ρ₀ ≤ 1`. -/
theorem UniformWindowPair.mono_eps {β₀ ε ε' : ℝ} {p : ℝ × NNReal} (hεε' : ε ≤ ε')
    (h : UniformWindowPair.{u} β₀ ε p) : UniformWindowPair.{u} β₀ ε' p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun β hβ hKT hF ↦ ?_⟩
  exact WindowFour.mono_eps (le_trans h3 (by norm_num)) hεε' (h4 β hβ hKT hF)

/-- **A uniform window pair transports downward in the fullness exponent.**
`Kakeya.WindowFour.mono_etaKT` at the level of `Kakeya.UniformWindowPair`. -/
theorem UniformWindowPair.anti_eta {β₀ ε η η' : ℝ} {ρ : NNReal} (hη'0 : 0 < η')
    (hle : η' ≤ η) (h : UniformWindowPair.{u} β₀ ε (η, ρ)) :
    UniformWindowPair.{u} β₀ ε (η', ρ) := by
  obtain ⟨_, h2, h3, h4⟩ := h
  exact ⟨hη'0, h2, h3, fun β hβ hKT hF ↦
    WindowFour.mono_etaKT (le_trans h3 (by norm_num)) hle (h4 β hβ hKT hF)⟩

/-! ### (B) Both transports run away from the ratio -/

/-- **The loss-to-fullness ratio clause of **, at a general pair of constants.
`WindowRatio c K we wη` is that the `c * we ≤ 2 ^ 18 * wη` at `K = 2 ^ 18`. -/
def WindowRatio (c K we wη : ℝ) : Prop := c * we ≤ K * wη

/-- Raising the loss exponent — the direction `Kakeya.WindowFour.mono_eps` allows — cannot
create the ratio. -/
theorem windowRatio_not_gained_by_mono_eps {c K we we' wη : ℝ} (hc : 0 ≤ c) (hle : we ≤ we')
    (h : ¬ WindowRatio c K we wη) : ¬ WindowRatio c K we' wη := fun hcon ↦
  h (le_trans (mul_le_mul_of_nonneg_left hle hc) hcon)

/-- Lowering the fullness exponent — the direction `Kakeya.WindowFour.mono_etaKT` allows —
cannot create the ratio. -/
theorem windowRatio_not_gained_by_anti_eta {c K we wη wη' : ℝ} (hK : 0 ≤ K) (hle : wη' ≤ wη)
    (h : ¬ WindowRatio c K we wη) : ¬ WindowRatio c K we wη' := fun hcon ↦
  h (le_trans hcon (mul_le_mul_of_nonneg_left hle hK))

/-- **The closure of a ratio-failing pair under the tree's own transports still fails.**

Given a uniform window pair at which the  clause fails, every pair reachable from
it by `Kakeya.UniformWindowPair.mono_eps` and `Kakeya.UniformWindowPair.anti_eta` — the only two
moves the tree has — is again a uniform window pair at which the clause fails.  So the ratio
cannot be produced by transporting a pair the producer already returned; it has to come from the
Katz–Tao input itself. -/
theorem uniformWindowPair_ratio_not_gained {β₀ we we' wη wη' : ℝ} {ρ : NNReal} {c K : ℝ}
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hwe : we ≤ we') (hwη : wη' ≤ wη) (hwη'0 : 0 < wη')
    (hp : UniformWindowPair.{u} β₀ we (wη, ρ)) (hfail : ¬ WindowRatio c K we wη) :
    UniformWindowPair.{u} β₀ we' (wη', ρ) ∧ ¬ WindowRatio c K we' wη' :=
  ⟨UniformWindowPair.mono_eps hwe (UniformWindowPair.anti_eta hwη'0 hwη hp),
    windowRatio_not_gained_by_anti_eta hK hwη
      (windowRatio_not_gained_by_mono_eps hc hwe hfail)⟩

/-! ### (C) The ratio is independent of the Katz–Tao quantifier shape -/

/-- **The structural content of the tree's window producer.**

`Holds ε η` is to be read as "`η` is an admissible fullness exponent at loss `ε`".  The three
fields are exactly the three facts the tree *proves* about
`fun ε η ↦ ∃ ρ, Kakeya.UniformWindowPair β₀ ε (η, ρ)`, and nothing more:

* `mono_loss` — `Kakeya.UniformWindowPair.mono_eps`;
* `anti_threshold` — `Kakeya.UniformWindowPair.anti_eta`;
* `exists_threshold` — `Kakeya.exists_uniformWindowPair`, whose conclusion, as
   measured, relates its input to its output by nothing at all.

`Kakeya.uniformWindowShape` below is the instance, so this bundle is a faithful abstraction and
not a weakened one. -/
structure KTWindowShape where
  /-- `Holds ε η`: the threshold `η` is admissible at loss `ε`. -/
  Holds : ℝ → ℝ → Prop
  /-- The bound transports upward in the loss exponent. -/
  mono_loss : ∀ {ε ε' η : ℝ}, ε ≤ ε' → Holds ε η → Holds ε' η
  /-- The bound transports downward in the fullness exponent. -/
  anti_threshold : ∀ {ε η η' : ℝ}, 0 < η' → η' ≤ η → Holds ε η → Holds ε η'
  /-- Some positive threshold is admissible at every positive loss. -/
  exists_threshold : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), Holds ε η

/-- **The tree's window producer is an instance of the shape.**  This is the control that
`Kakeya.KTWindowShape` is not a strawman: everything the abstraction assumes, the tree has. -/
noncomputable def uniformWindowShape {β₀ : ℝ} (hβ₀0 : 0 < β₀) (hβ₀1 : β₀ ≤ 1) :
    KTWindowShape where
  Holds ε η := ∃ ρ : NNReal, UniformWindowPair.{u} β₀ ε (η, ρ)
  mono_loss := fun hεε' ⟨ρ, hρ⟩ ↦ ⟨ρ, UniformWindowPair.mono_eps hεε' hρ⟩
  anti_threshold := fun hη'0 hle ⟨ρ, hρ⟩ ↦ ⟨ρ, UniformWindowPair.anti_eta hη'0 hle hρ⟩
  exists_threshold := fun ε hε ↦ by
    obtain ⟨p, hp⟩ := exists_uniformWindowPair.{u} hβ₀0 hβ₀1 hε
    exact ⟨p.1, hp.1, p.2, hp⟩

/-- **A shape at which the ratio fails at every admissible pair.**  Admissible thresholds at loss
`ε` are exactly those below `c * ε / (K + 1)`; the shape's three fields all hold, and
`K * η ≤ K c ε / (K + 1) < c ε` for every one of them. -/
def ratioFailingShape (c K : ℝ) (hc : 0 < c) (hK : 0 < K) : KTWindowShape where
  Holds ε η := 0 < ε ∧ (K + 1) * η ≤ c * ε
  mono_loss := fun hεε' ⟨hε, hη⟩ ↦
    ⟨lt_of_lt_of_le hε hεε', le_trans hη (mul_le_mul_of_nonneg_left hεε' hc.le)⟩
  anti_threshold := fun _ hle ⟨hε, hη⟩ ↦
    ⟨hε, le_trans (mul_le_mul_of_nonneg_left hle (by linarith)) hη⟩
  exists_threshold := fun ε hε ↦ by
    have hK1 : (0 : ℝ) < K + 1 := by linarith
    exact ⟨c * ε / (K + 1), by positivity, hε, le_of_eq (by field_simp)⟩

/-- **The failing shape really fails, at every admissible pair and every positive loss.** -/
theorem ratioFailingShape_refutes {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ∀ ε > (0 : ℝ), ∀ η : ℝ, (ratioFailingShape c K hc hK).Holds ε η →
      ¬ WindowRatio c K ε η := by
  intro ε hε η hη hcon
  have h1 : (K + 1) * η ≤ c * ε := hη.2
  have h2 : c * ε ≤ K * η := hcon
  have hη0 : η ≤ 0 := by nlinarith
  nlinarith [mul_pos hc hε]

/-- **A shape at which the ratio holds.**  The firing control for
`Kakeya.ratioFailingShape_refutes`: the shape's three fields do not *refute* the ratio either, so
the ratio is genuinely independent of them rather than false. -/
def ratioSatisfyingShape : KTWindowShape where
  Holds ε η := 0 < ε ∧ 0 < η ∧ η ≤ ε
  mono_loss := fun hεε' ⟨hε, hη0, hη⟩ ↦ ⟨lt_of_lt_of_le hε hεε', hη0, le_trans hη hεε'⟩
  anti_threshold := fun hη'0 hle ⟨hε, _, hη⟩ ↦ ⟨hε, hη'0, le_trans hle hη⟩
  exists_threshold := fun ε hε ↦ ⟨ε, hε, hε, hε, le_rfl⟩

/-- The satisfying shape satisfies the ratio, at every positive loss, whenever `c ≤ K`. -/
theorem ratioSatisfyingShape_satisfies {c K : ℝ} (hcK : c ≤ K) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ratioSatisfyingShape.Holds ε η ∧ WindowRatio c K ε η :=
  fun ε hε ↦ ⟨ε, hε, ⟨hε, hε, le_rfl⟩, mul_le_mul_of_nonneg_right hcK hε.le⟩

/-- **The ratio is independent of the Katz–Tao quantifier shape.**  Both a shape refuting it at
every admissible pair and a shape satisfying it at every loss exist. -/
theorem windowRatio_independent_of_shape {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hcK : c ≤ K) :
    (∃ S : KTWindowShape, ∀ ε > (0 : ℝ), ∀ η : ℝ, S.Holds ε η → ¬ WindowRatio c K ε η) ∧
      (∃ S : KTWindowShape, ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), S.Holds ε η ∧ WindowRatio c K ε η) :=
  ⟨⟨ratioFailingShape c K hc hK, ratioFailingShape_refutes hc hK⟩,
    ⟨ratioSatisfyingShape, ratioSatisfyingShape_satisfies hcK⟩⟩

/-- **No producer of the ratio follows from the shape.**  This is the negative answer to "is
`c * we ≤ 2 ^ 18 * wη` provable as a strengthening of `Kakeya.exists_uniformWindowPair`'s
conclusion?", relative to everything the tree proves about that producer. -/
theorem no_ratio_producer_from_shape {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ¬ ∀ (S : KTWindowShape) (ε : ℝ), 0 < ε →
        ∃ η > (0 : ℝ), S.Holds ε η ∧ WindowRatio c K ε η := by
  intro hall
  obtain ⟨η, -, hHolds, hratio⟩ := hall (ratioFailingShape c K hc hK) 1 one_pos
  exact ratioFailingShape_refutes hc hK 1 one_pos η hHolds hratio

/-- **…and the freedom to choose the loss exponent does not buy it either.**

`Kakeya.CoarseKTWindow.we` is a *field*: its only constraint is the upper bound
`Kakeya.CoarseKTWindow.hwe`, so a producer may pick it anywhere in `(0, εmax]` and only then call
the window producer.  That extra freedom is granted here in full, and the ratio still does not
follow.  This is the form that matters for conjunct 3's general branch. -/
theorem no_ratio_producer_from_shape_even_with_free_loss {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ¬ ∀ (S : KTWindowShape) (εmax : ℝ), 0 < εmax →
        ∃ ε, 0 < ε ∧ ε ≤ εmax ∧ ∃ η > (0 : ℝ), S.Holds ε η ∧ WindowRatio c K ε η := by
  intro hall
  obtain ⟨ε, hε, -, η, -, hHolds, hratio⟩ := hall (ratioFailingShape c K hc hK) 1 one_pos
  exact ratioFailingShape_refutes hc hK ε hε η hHolds hratio

/-! ### (D) Along the tree's producer chain the loss exponent cancels -/

/-- **The loss exponent cancels identically from the ratio.**

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` returns the threshold `ε * η₀ / M` with
`M = Module.finrank ℝ E + η₀ + 1`, and
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` calls it at `ε / 2` and returns
half of what it gets; in `EuclideanSpace ℝ (Fin 3)` that composite is
`ε * η₀ / (4 * (4 + η₀))`, where `η₀` is GWZ Definition 3.4's own threshold `η(ϵ, β)` at the
accuracy `ε / 2`.  At that value the  clause is **equivalent** to a condition in
which `ε` does not occur — an absolute floor on Definition 3.4's threshold function.

So no choice of `Kakeya.CoarseKTWindow.we` can buy the ratio along this chain: shrinking the loss
shrinks the delivered threshold in exact proportion. -/
theorem windowChain_ratio_iff_thresholdFloor {c K ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    WindowRatio c K ε (ε * η₀ / (4 * (4 + η₀))) ↔ 16 * c ≤ (K - 4 * c) * η₀ := by
  have hden : (0 : ℝ) < 4 * (4 + η₀) := by linarith
  rw [WindowRatio, mul_div_assoc', le_div_iff₀ hden]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- The floor at the constants  measures (`c = 2` at H.3's split, `K = 2 ^ 18`):
GWZ Definition 3.4's threshold must exceed `32 / 262136 ≈ 1.2207 · 10⁻⁴`, at some accuracy, for
the tangential branch's fullness half to close. -/
theorem windowChain_ratio_iff_thresholdFloor_two {ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    WindowRatio 2 (2 ^ 18) ε (ε * η₀ / (4 * (4 + η₀))) ↔ (32 : ℝ) / 262136 ≤ η₀ := by
  rw [windowChain_ratio_iff_thresholdFloor hε hη₀,
    div_le_iff₀ (by norm_num : (0:ℝ) < 262136)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Below the floor, the ratio fails at every loss exponent.**  The quantifier `∀ ε > 0` is the
point: the producer's freedom in `Kakeya.CoarseKTWindow.we` is exhausted without effect. -/
theorem windowChain_ratio_fails_at_every_loss {c K η₀ : ℝ} (hη₀ : 0 < η₀)
    (hsmall : (K - 4 * c) * η₀ < 16 * c) :
    ∀ ε > (0 : ℝ), ¬ WindowRatio c K ε (ε * η₀ / (4 * (4 + η₀))) := by
  intro ε hε hcon
  exact absurd ((windowChain_ratio_iff_thresholdFloor hε hη₀).mp hcon) (not_le.mpr hsmall)

/-- **GWZ's own Remark 3.6 construction gives the same shape.**  Remark 3.6 defines the general
threshold as `η(β,ϵ) = ϵ · η₁(β,ϵ) / 100`; at that value the ratio again loses all dependence on
the accuracy and becomes a floor on the raw Katz–Tao threshold `η₁`.  So the obstruction is not
an artefact of the tree's constants. -/
theorem gwzRemark36_ratio_iff_thresholdFloor {c K ε η₁ : ℝ} (hε : 0 < ε) :
    WindowRatio c K ε (ε * η₁ / 100) ↔ 100 * c ≤ K * η₁ := by
  rw [WindowRatio, mul_div_assoc', le_div_iff₀ (by norm_num : (0:ℝ) < 100)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ### (D′) …and the linear degradation is forced, not incidental -/

/-- **The Remark 3.6 transport cannot deliver more than `η₀ / t`.**

GWZ Remark 3.6 (and its formal counterpart
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`) converts a hypothesis stated at an
*auxiliary* scale `τ ≤ δ` into `Kakeya.KatzTaoEstimate`'s hypothesis at `δ`.  Both of that
definition's clauses — `Δmax ≤ δ ^ (-η₀)` and `λ ≥ δ ^ η₀` — are usable from the corresponding
clauses at `τ` exactly when `δ ^ η₀ ≤ τ ^ η`.  Writing `τ = δ ^ t`, covering auxiliary scales
down to depth `t` therefore forces `t * η ≤ η₀`: the transported threshold is at most `η₀ / t`.

This is not a remark about one proof script.  It is the semantic content of the transport, and it
is why the delivered fullness exponent is *linear in the accuracy*: the depth `t` a proof must
cover is itself inversely proportional to the accuracy (`Kakeya.remark36_depth_forces_ratio`). -/
theorem remark36_transport_forces_linear {η η₀ t : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 → δ ^ η₀ ≤ (δ ^ t) ^ η) : t * η ≤ η₀ := by
  have hδ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hδ1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hkey : ((1:ℝ)/2) ^ η₀ ≤ ((1:ℝ)/2) ^ (t * η) := by
    rw [Real.rpow_mul hδ0.le]
    exact h (1/2) hδ0 hδ1
  exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ0 hδ1).mp hkey

/-- **The transport depth is `M / ε`, so the delivered threshold is linear in the accuracy.**

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` splits at `τ = δ ^ (M / ε)` with
`M = Module.finrank ℝ E + η₀ + 1`, because below that scale the trivial cardinality bound pays
for itself; above it, the transport of the previous lemma must hold.  So the threshold it can
deliver is at most `ε * η₀ / M`. -/
theorem remark36_depth_forces_ratio {ε η η₀ M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 → δ ^ η₀ ≤ (δ ^ (M / ε)) ^ η) : η ≤ ε * η₀ / M := by
  have hdepth : M / ε * η ≤ η₀ := remark36_transport_forces_linear h
  rw [le_div_iff₀ hM]
  have : M / ε * η * ε ≤ η₀ * ε := mul_le_mul_of_nonneg_right hdepth hε.le
  calc η * M = M / ε * η * ε := by field_simp
    _ ≤ η₀ * ε := this
    _ = ε * η₀ := by ring

/-- **Below the floor, no accuracy at all gives the ratio — even granting the transport its
best possible threshold.**

The hypothesis `hbound` is the *upper* bound the transport can deliver
(`Kakeya.remark36_depth_forces_ratio`), so this covers every proof of that shape, not just the
existing one; and the conclusion holds at every accuracy `ε`, so the producer's freedom in
`Kakeya.CoarseKTWindow.we` is exhausted without effect. -/
theorem remark36_ratio_fails_at_every_accuracy {c K ε η η₀ M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (hK : 0 < K) (hbound : η ≤ ε * η₀ / M) (hfloor : K * η₀ < c * M) :
    ¬ WindowRatio c K ε η := by
  intro hcon
  have h1 : K * η ≤ K * (ε * η₀ / M) := mul_le_mul_of_nonneg_left hbound hK.le
  have h2 : K * (ε * η₀ / M) < c * ε := by
    rw [mul_div_assoc', div_lt_iff₀ hM]
    nlinarith
  exact absurd (lt_of_le_of_lt (le_trans hcon h1) h2) (lt_irrefl _)

/-- Satisfiability control for `Kakeya.remark36_transport_forces_linear`: its hypothesis is met,
with equality, at exactly the threshold the transport delivers.  So the bound is sharp and the
binder is not vacuous. -/
example {ε η₀ M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    ∀ δ : ℝ, 0 < δ → δ < 1 → δ ^ η₀ ≤ (δ ^ (M / ε)) ^ (ε * η₀ / M) := by
  intro δ hδ0 _
  rw [← Real.rpow_mul hδ0.le, show M / ε * (ε * η₀ / M) = η₀ by field_simp]

/-! ### (E) The parameter-order fact -/

/-- **A loss parameter that is not an input of the producer always meets the ratio.**

GWZ apply `K_KT(β)` at an accuracy of their choosing and only afterwards fix `η_bias`, `τ` and
`τ'`, each of which is constrained from *above* alone; the transported enclosure cost is then
charged to `η_bias` against the already-known threshold.  Formally: given any shape, any
positive `εmax` at which the producer is consulted, and any ceiling `ϱmax` on the second
parameter, a positive `ϱ ≤ ϱmax` meeting `c * ϱ ≤ K * η` exists.

Compare `Kakeya.no_ratio_producer_from_shape_even_with_free_loss`: the *same* freedom in the
producer's own input does **not** give the ratio.  The difference is only the order in which the
two are fixed, and that is what `Kakeya.CoarseKTWindow` would have to encode — `wη` before the
parameter that pays for the transport, rather than after `we`. -/
theorem ratio_free_for_noninput_parameter (S : KTWindowShape) {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    {ε ϱmax : ℝ} (hε : 0 < ε) (hϱmax : 0 < ϱmax) :
    ∃ η > (0 : ℝ), S.Holds ε η ∧ ∃ ϱ, 0 < ϱ ∧ ϱ ≤ ϱmax ∧ WindowRatio c K ϱ η := by
  obtain ⟨η, hη, hHolds⟩ := S.exists_threshold ε hε
  refine ⟨η, hη, hHolds, min ϱmax (K * η / c), lt_min hϱmax (by positivity),
    min_le_left _ _, ?_⟩
  have h : min ϱmax (K * η / c) ≤ K * η / c := min_le_right _ _
  rw [WindowRatio, ← le_div_iff₀' hc]
  exact h

/-! ### Satisfiability controls

Each binder bundle used above is inhabited; a vacuous hypothesis set would make the negative
results empty.  These are the sharp-binder checks. -/

/-- The failing shape's admissibility predicate is inhabited. -/
example : (ratioFailingShape 2 (2 ^ 18) (by norm_num) (by norm_num)).Holds 1
    (2 / (2 ^ 18 + 1)) := ⟨one_pos, by norm_num⟩

/-- The failing shape's clause is a genuine constraint: some positive threshold violates it. -/
example : ¬ (ratioFailingShape 2 (2 ^ 18) (by norm_num) (by norm_num)).Holds 1 1 := by
  rintro ⟨-, h⟩; norm_num at h

/-- The satisfying shape's admissibility predicate is inhabited. -/
example : ratioSatisfyingShape.Holds 1 1 := ⟨one_pos, one_pos, le_rfl⟩

/-- The floor of `Kakeya.windowChain_ratio_iff_thresholdFloor_two` is met by some positive
threshold — the equivalence is not vacuously false. -/
example : WindowRatio 2 (2 ^ 18) 1 (1 * (1 / 100) / (4 * (4 + 1 / 100))) :=
  (windowChain_ratio_iff_thresholdFloor_two one_pos (by norm_num)).mpr (by norm_num)

/-- …and it is violated by some positive threshold — the equivalence is not vacuously true. -/
example : ¬ WindowRatio 2 (2 ^ 18) 1 (1 * (1 / 10 ^ 6) / (4 * (4 + 1 / 10 ^ 6))) := by
  intro h
  have := (windowChain_ratio_iff_thresholdFloor_two one_pos (by norm_num)).mp h
  norm_num at this

end Kakeya

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle

/-!
# The `ρ`-tube count of Configuration `hyp:ml2setup`, repaired

`Kakeya.VeryNotSticky.rho_count` renders the third bullet of blueprint `lemmain2vns`

> for each `ρ ∈ [δ^{1-ϖ}, δ^{ϖ}]`, `|𝕋_ρ| ≥ ρ^{-2-ζ}`

as a statement about **every** essentially distinct family of `ρ`-tubes covering the
configuration's own family `cfg.s`, with the multiplicative constant taken to be `1`.  Two
separate things are wrong with that rendering, and this file separates them, states the
repaired clause, and proves it from exactly the binders of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`.

**Defect 1 — the missing constant, at the *binder*.**  GWZ's `|𝕋_ρ|` is the *canonical parent
family* of the uniformity Definition `uniformSetOfTubes`, not an arbitrary cover.  Passing from
"the canonical parent family is large" to "every essentially distinct cover is large" costs the
bounded-overlap constant `D` of Definition `uniformSetOfTubes`(ii): the map sending a parent
tube to a cover element containing one of its children is at most `D`-to-one, so an arbitrary
cover only obeys `|t| ≥ D^{-1}|𝕋_ρ|`.  That constant is the one the `⪆` of §9 hides on the
count, and it is affordable: `Kakeya.ML2Spine.spine_tube_card_lower`, which supplies the
binder, carries its threshold with the strictly positive gap `κ = 2 e η_j` of
`Kakeya.ML2Spine.spine_countGap`, so its hypothesis `hsmall` survives multiplication of the
left-hand side by any fixed constant — indeed by any `δ̃^{-θ}` with `θ < κ`.  The constant is
carried here by `Ccount`.

**Defect 2 — and it is *not* a constant.**  In GWZ the setup pigeonholes of subsection
*proofoverview* refine only the **shading** `Y` (and the per-ball segment families `𝕋_B`); the
tube family `𝕋` itself is never refined, so the count hypothesis survives verbatim.  The Lean
configuration instead carries the *refined* family `cfg.s ⊆ s` — it must, because
`Kakeya.VeryNotSticky.shading_lb`, `shading_ub` and `lam_ge` are per-tube demands that an
aggregate binder cannot meet without discarding tubes.  Covering families for `cfg.s` are a
**strictly larger** class than covering families for `s`, so the field is strictly stronger
than the binder; `rhoCountOn_mono_index` below is that implication, and it points the wrong
way.  No constant closes the gap: `not_rhoCountOn_empty` shows the field is *false* at the
extreme legal refinement `cfg.s = ∅` for **every** constant `Ccount`.

The repair is therefore not a constant but a *datum*: the configuration has to remember the
parent family.  `RhoCountParent` is the repaired clause — "the configuration's family sits
inside a family that satisfies Lemma 9.1's containment, `Δ_max` and count hypotheses" — and
`rhoCountParent_of_binders` discharges it from the binders of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` in one line, at `Ccount = 1`, with `sPar := s`.
`rhoCountParent_of_veryNotSticky` shows the repaired clause is *weaker* than the present field,
so the change is a weakening of `Kakeya.VeryNotSticky` and every consumer must be rechecked;
there is exactly one, `Kakeya.VeryNotSticky.rho2_range`, restated here as
`rho2_range_parent`.

**The price of the repair,** and it is the standard `⪆`: the count is spent, in the blueprint,
as the fibre bound `|𝕋[T_{ρ₂}]| ≤ ρ₂^{2+ζ}|𝕋|`, and reading it off the parent family costs the
ratio `|sPar|/|s|`.  `card_parent_le_of_isCRefinement` prices that ratio at `(c·λ)^{-1}`, which
at the setup's own constants `c ≥ δ^η` and `λ ≥ δ^η` is `δ^{-2η}` — subpolynomial, hence
absorbed exactly like every other `⪆` of the section. The absorption is explicit: this `δ^{-2η}` is one of the summands of the `18η` of
`Kakeya.VeryNotSticky.SplitInputs.countConstant`, measured by the producer
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

universe u

open MeasureTheory Metric Set ShadedBody

/-! ## The clause, as a standalone `Prop`, and the identification of the refutation

`RhoCountOn` and `RhoCountParent` now live **above** the structure, in
`Kakeya.DimensionThree.MainLemma2.VeryNotSticky`, next to the field's present form
`Kakeya.VeryNotSticky.RhoParentData`; using them from here would be an
import cycle. What stays here is everything about them that is not needed to state the
structure.

The old field form is preserved below as a standalone `Prop`,
`RhoCountFieldOldStatement`, so that the refutation `not_rhoCountFieldOldStatement_empty`
survives the field change and keeps compiling. This is the
`Kakeya.ThinCase.Refute.statement_of_universal_loc` device: a plain tripwire `example` about a
*field* cannot survive that field changing, so the statement under test is hoisted out of the
declaration into a `Prop` of its own, and two theorems pin it in both directions —
`rhoCountFieldOldStatement_iff_rhoCountOn_one` says the hoisted `Prop` is the old text, and
`rhoCount_field_is_parentData` says the field is now the repaired one (`RhoParentData`;
`rhoCount_field_is_parent` records that the intermediate form `RhoCountParent` still follows). If
any of them drifts, one of them stops elaborating.
-/

/-- **The form the field `Kakeya.VeryNotSticky.rho_count` used to carry, verbatim, as a
standalone `Prop`.**

Character for character the old field body, with the structure's `δ, ζ, exscalb, s, T` turned
into binders. Nothing reads it: its only purpose is to keep the refutation
`not_rhoCountFieldOldStatement_empty` alive after the field itself changed, and to make a silent
return of the old form impossible — restoring it would break
`rhoCount_field_is_parent`. -/
def RhoCountFieldOldStatement (δ : NNReal) (ζ exscalb : ℝ) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscalb)) (δ ^ exscalb) →
    ∀ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
      (tρ : Set κ).Pairwise
        (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
      (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)

/-- **The hoisted old form is `RhoCountOn … 1`.**

Half of the identification: it certifies that `RhoCountFieldOldStatement` really is the constant-`1`
instance of the family the refutations below are about, so refuting one refutes the other. -/
theorem rhoCountFieldOldStatement_iff_rhoCountOn_one {δ : NNReal} {ζ exscalb : ℝ}
    {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} :
    RhoCountFieldOldStatement δ ζ exscalb s T ↔ RhoCountOn δ ζ exscalb s T 1 := by
  constructor
  · intro h ρ hρ κ tρ Tρ hcover hdisj
    simpa using h ρ hρ κ tρ Tρ hcover hdisj
  · intro h ρ hρ κ tρ Tρ hcover hdisj
    simpa using h ρ hρ κ tρ Tρ hcover hdisj

/-- **The other half of the identification: the field is now `RhoParentData`**: the count on the family's own parent with the parent's bounded uniform hierarchy and the
retention `δ^{2η}|sPar| ≤ |s|`.

The replacement for the old tripwire `rhoCountOn_one_of_veryNotSticky`, which asserted that the
field was `RhoCountOn … 1` and which the repair had to kill. If the field drifts by one symbol —
in particular if it is restored to `RhoCountFieldOldStatement` or to `RhoCountParent` — this
`exact` stops elaborating. -/
theorem rhoCount_field_is_parentData (cfg : VeryNotSticky.{u}) :
    RhoParentData cfg.δ cfg.ζ cfg.exscalb cfg.η cfg.s cfg.T :=
  cfg.rho_count

/-- **The previous field form is a consequence of the field**, at the constant
`max C₀ (Tube.coverCountLoss 3)` (`Kakeya.VeryNotSticky.rhoCountParent_of_rhoParentData`); no
consumer of `RhoCountParent` is lost by the F12b retyping. -/
theorem rhoCount_field_is_parent (cfg : VeryNotSticky.{u}) :
    RhoCountParent cfg.δ cfg.ζ cfg.exscalb cfg.η cfg.s cfg.T
      (max cfg.C₀ (Tube.coverCountLoss 3)) :=
  rhoCountParent_of_rhoParentData cfg.hδ cfg.hδ1 cfg.hexscalb.le (le_max_right _ _)
    cfg.rho_count

/-- Enlarging the constant only weakens the clause. -/
theorem RhoCountOn.mono_const {δ : NNReal} {ζ exscalb : ℝ} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {C C' : NNReal} (hC : C ≤ C')
    (h : RhoCountOn δ ζ exscalb s T C) : RhoCountOn δ ζ exscalb s T C' := by
  intro ρ hρ κ tρ Tρ hcover hdisj
  refine (h ρ hρ κ tρ Tρ hcover hdisj).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (Nat.cast_nonneg _)

/-! ## Defect 2: the clause is monotone in the index set, and the gap is not a constant -/

/-- **The clause is *monotone* in the index set: a smaller family is a *stronger* demand.**

Every family of `ρ`-tubes covering `s` also covers a subfamily `s' ⊆ s`, so the covers of `s'`
are a superset of the covers of `s` and a lower bound over all of them is a stronger statement.
This is the hazard, in one line: the binder `hcount` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` is `RhoCountOn … s …`, the field it must
produce is `RhoCountOn … cfg.s …` with `cfg.s ⊆ s`, and this implication runs the other way. -/
theorem rhoCountOn_mono_index {δ : NNReal} {ζ exscalb : ℝ} {ι : Type u} {s s' : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {C : NNReal} (hsub : s' ⊆ s)
    (h : RhoCountOn δ ζ exscalb s' T C) : RhoCountOn δ ζ exscalb s T C := by
  intro ρ hρ κ tρ Tρ hcover hdisj
  exact h ρ hρ κ tρ Tρ (fun i hi ↦ hcover i (hsub hi)) hdisj

/-- **The field change is a weakening: the old form implies the repaired one**, at `sPar := s`
and any `Ccount ≥ 1`.

So no producer of a configuration is made harder by the change, and only the field's consumers
had to be rechecked — there was exactly one,
`Kakeya.VeryNotSticky.rho2_range`. Together with
`not_rhoCountFieldOldStatement_empty` this is the whole check of the direction of the change:
strictly weaker, and the thing dropped was false. -/
theorem rhoCountParent_of_rhoCountFieldOldStatement {δ : NNReal} {ζ exscalb η : ℝ}
    {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {C : NNReal} (hC : 1 ≤ C)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    (h : RhoCountFieldOldStatement δ ζ exscalb s T) :
    RhoCountParent δ ζ exscalb η s T C :=
  ⟨s, Finset.Subset.refl _, hball, hmax,
    RhoCountOn.mono_const hC (rhoCountFieldOldStatement_iff_rhoCountOn_one.1 h)⟩

/-- **The window is nonempty exactly when `exscalb ≤ 1/2`.** -/
theorem rho_window_nonempty {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {exscalb : ℝ}
    (hex : exscalb ≤ 1 / 2) :
    (δ ^ (1 - exscalb)) ∈ Set.Icc (δ ^ (1 - exscalb)) (δ ^ exscalb) :=
  ⟨le_rfl, NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)⟩

/-- **No constant repairs the clause: it is *false* at the empty refinement.**

`∅ ⊆ s` is a legal subfamily, the empty family of `ρ`-tubes covers it vacuously and is
pairwise essentially distinct vacuously, and the clause then demands `ρ^{-2-ζ} ≤ Ccount · 0`.
Since `ρ > 0` the left side is positive, so the demand fails for **every** `Ccount`.

This is the compiler-checked reason why the `⪆`-with-a-constant repair — the repair that fixed
`Kakeya.VeryNotSticky.lam_ge` — cannot fix `rho_count`: the gap between the binder and the
field is a *class of covers*, not a factor. -/
theorem not_rhoCountOn_empty {δ : NNReal} {ζ exscalb : ℝ} {ι : Type u}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {C : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hex : exscalb ≤ 1 / 2) :
    ¬ RhoCountOn δ ζ exscalb (∅ : Finset ι) T C := by
  intro h
  have hmem := rho_window_nonempty hδ hδ1 (exscalb := exscalb) hex
  have hpos : (0 : ℝ) < ((δ ^ (1 - exscalb) : NNReal) : ℝ) := by
    have : (0 : NNReal) < δ ^ (1 - exscalb) := NNReal.rpow_pos hδ
    exact_mod_cast this
  have hkey := h (δ ^ (1 - exscalb)) hmem (ULift.{u} Empty) (∅ : Finset (ULift.{u} Empty))
    (fun x ↦ x.down.elim) (by simp) (by simp)
  have hlt : (0 : ℝ) < ((δ ^ (1 - exscalb) : NNReal) : ℝ) ^ (-2 - ζ) :=
    Real.rpow_pos_of_pos hpos _
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at hkey
  exact absurd hkey (not_le.2 hlt)

/-- **The refutation, identified on the hoisted old form.**

This is the declaration that must keep compiling: it says that the *exact text* the field
`Kakeya.VeryNotSticky.rho_count` used to carry is false at the legal refinement `s = ∅`, with no
constant anywhere in it to blame. It is stated against
`RhoCountFieldOldStatement` rather than against the field, so that it is immune to the field
change — which is the whole point of hoisting the statement. -/
theorem not_rhoCountFieldOldStatement_empty {δ : NNReal} {ζ exscalb : ℝ} {ι : Type u}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hex : exscalb ≤ 1 / 2) :
    ¬ RhoCountFieldOldStatement δ ζ exscalb (∅ : Finset ι) T := by
  intro h
  exact not_rhoCountOn_empty (C := 1) hδ hδ1 hex
    (rhoCountFieldOldStatement_iff_rhoCountOn_one.1 h)

/-! ## The repaired clause: its producer, and the one consumer

`RhoCountParent` itself is stated in `Kakeya.DimensionThree.MainLemma2.VeryNotSticky`, above the
structure, because the field is it.
-/

/-- **The producing lemma.**

From exactly the binders `hball`, `hmax`, `hcount` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`, and the fact that the configuration's family
is a subfamily of the given one, the repaired clause holds — with `Ccount = 1`, hence with any
`Ccount ≥ 1`, and with no arithmetic.

Contrast `rhoCountOn_mono_index`: the *present* field is not obtainable from the same binders
at any constant (`not_rhoCountOn_empty`). -/
theorem rhoCountParent_of_binders {δ : NNReal} {ζ exscal η : ℝ} {ι : Type u}
    {s s' : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Ccount : NNReal}
    (hC : 1 ≤ Ccount) (hsub : s' ⊆ s)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∀ {κ : Type u} (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    RhoCountParent δ ζ exscal η s' T Ccount := by
  refine ⟨s, hsub, hball, hmax, ?_⟩
  intro ρ hρ κ tρ Tρ hcover hdisj
  refine (hcount ρ hρ tρ Tρ hcover hdisj).trans ?_
  have h1 : (1 : ℝ) ≤ (Ccount : ℝ) := by exact_mod_cast hC
  nlinarith [Nat.cast_nonneg (α := ℝ) tρ.card]

/-- **The derived form of the field, at any constant `≥ Tube.coverCountLoss 3`.**

The field is `RhoParentData`, whose count is the `∃`-form; the
`∀`-over-covers form `RhoCountParent` follows at any constant absorbing the cover-comparison loss
`Tube.coverCountLoss 3` (`Kakeya.VeryNotSticky.rhoCountParent_of_rhoParentData`). This is the
shape the non-slab branch reads, where the constant is already free. -/
theorem rhoCountParent_of_veryNotSticky (cfg : VeryNotSticky.{u}) {C : NNReal}
    (hC : Tube.coverCountLoss 3 ≤ C) :
    RhoCountParent cfg.δ cfg.ζ cfg.exscalb cfg.η cfg.s cfg.T C :=
  rhoCountParent_of_rhoParentData cfg.hδ cfg.hδ1 cfg.hexscalb.le hC cfg.rho_count

/-! ## The one consumer

`Kakeya.VeryNotSticky.rho2_range` (`Kakeya.DimensionThree.MainLemma2.NonSlabAngle`) is the only
consumer of the field, and it is restated there against the repaired clause: it returns the
parent family in its conclusion. It had, and still has, no term-level users — the count is spent
through the carried field `Kakeya.VeryNotSticky.SplitInputs.fibreScaleCount`, whose constant is, the carried `Ccnt` of
`Kakeya.VeryNotSticky.SplitInputs.countConstant` at `Ccnt ≤ δ^{-18η}` and **not** the δ-free
`(2 C_{lem:ml2bodyAngle}(C₀))²` this paragraph used to name. So a constant on the count does not
cost the non-slab branch nothing for free: it is paid, together with the `δ^{-2η}` of the parent
form and the `ρ_k/ρ₂` rounding, out of the `18η` of `countConstant`, whose downstream price is
the `m`-slot `19` of `Kakeya.VeryNotSticky.tangentialSlabMultAbsorb` — `22` of `2^17` budget
units, and the absorb's conclusion is `m`-free ( (b)-(c)).
-/

/-! ## Defect 1: the constant the `⪆` hides is the bounded-overlap constant `D` -/

/-- **The parent family injects into any cover, `D`-to-one.**

The combinatorial skeleton of "GWZ's `|𝕋_ρ|` is the canonical parent family, not an arbitrary
cover".  Read `P` as the parent family `𝕋_ρ` of Definition `uniformSetOfTubes`, `t` as an
arbitrary family of `ρ`-tubes covering `𝕋`, and `fib j` as the set of parent tubes one of whose
children lies in the cover element `j`.  Clause (ii) of that definition — *for every `ρ`-tube
`V`, at most `D` parent tubes meet `V` through `𝕋`* — is exactly `hD`, and `hcov` is that every
parent has a child, which the cover then places in some element of `t`.  The conclusion
`|𝕋_ρ| ≤ D |t|` is the missing constant: the blueprint's `|𝕋_ρ| ≥ ρ^{-2-ζ}` yields, for an
arbitrary cover, only `|t| ≥ D^{-1} ρ^{-2-ζ}`.

That constant is affordable.  `Kakeya.ML2Spine.spine_tube_card_lower`, which supplies Lemma
9.1's count binder at `ζ = η_j/2`, reaches its threshold through
`Kakeya.ML2Spine.spine_countThreshold`, whose remaining hypothesis is
`L · CF₀ · C_up ≤ c_lo · δ̃^{-2 e η_j}` with `2 e η_j > 0`
(`Kakeya.ML2Spine.spine_countGap_pos`).  Multiplying the left-hand side by a fixed `D` — or
indeed by `δ̃^{-θ}` for any `θ < 2 e η_j` — leaves that hypothesis true for all small `δ̃`.  The
slack is there because GWZ applies the lemma at `ζ = η_j/2` while
`TTSigmaBigCardinalityV1` supplies the exponent `η_j`: half the count exponent is spare, and it
is spare *by design*. -/
theorem card_parent_le_mul_card_cover {π κ : Type*}
    {P : Finset π} {t : Finset κ} {D : ℕ} (fib : κ → Finset π)
    (hcov : ∀ p ∈ P, ∃ j ∈ t, p ∈ fib j) (hD : ∀ j ∈ t, (fib j).card ≤ D) :
    P.card ≤ D * t.card := by
  classical
  have hsub : P ⊆ t.biUnion fib := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := hcov p hp
    exact Finset.mem_biUnion.2 ⟨j, hj, hpj⟩
  calc P.card ≤ (t.biUnion fib).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ t, (fib j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ t, D := Finset.sum_le_sum hD
    _ = D * t.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]


open scoped Classical in
/-- **The uniformity constant is the constant: any cover of `𝕋` has at least `C^{-1}|𝕋_ρ|`
members.**

`card_parent_le_mul_card_cover` instantiated against the real Definition 2.1: `𝕋_ρ` is the node
family of the hierarchy at the grid index `k`, presented as the image of the assignment (so
that no surjectivity hypothesis is needed), and the bounded-overlap clause
`Tube.UniformTubeSet.boundedOverlap` supplies the `D`-to-one bound at `D = C`.

This is the precise price of the Lean rendering: GWZ's third bullet of `lemmain2vns` asserts
`|𝕋_ρ| ≥ ρ^{-2-ζ}` for the *canonical* parent family, and
`Kakeya.VeryNotSticky.rho_count` asserts `|t| ≥ ρ^{-2-ζ}` for *every* essentially distinct
covering family `t`.  The two differ by the factor `C`, and by nothing else: this lemma is the
implication `|𝕋_ρ| ≥ X ⟹ |t| ≥ C^{-1} X`, valid for every cover, essentially distinct or not
(essential distinctness is not used).

`C` is subpolynomial in the setup — `Kakeya.VeryNotSticky.aScaleData_absorb` forces
`C₀ ≤ δ^{-η}` (`Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`) — so the factor is a `δ^{-η}` and
is absorbed exactly like every other `⪆` of the section. -/
theorem card_image_assign_le_mul_card_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    {κ : Type*} {tρ : Finset κ} {Tρ : κ → Tube (Tube.gridScale δ N k) E}
    (hcover : ∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) :
    (((s.image (𝒰.cover.assign k)).card : ℕ) : NNReal) ≤ C * (tρ.card : NNReal) := by
  set fib : κ → Finset ι := fun j =>
    (𝒰.cover.indexSet k).filter (fun p => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k p).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) with hfibdef
  have hsub : s.image (𝒰.cover.assign k) ⊆ tρ.biUnion fib := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, hj, hij⟩ := hcover i hi
    refine Finset.mem_biUnion.2 ⟨j, hj, ?_⟩
    exact Finset.mem_filter.2 ⟨𝒰.cover.assign_mem k hk i hi,
      ⟨i, hi, 𝒰.cover.le_tube_assign k hk i hi, hij⟩⟩
  have hD : ∀ j ∈ tρ, ((fib j).card : NNReal) ≤ C := fun j _ ↦ 𝒰.boundedOverlap k hk (Tρ j)
  have hcard : (s.image (𝒰.cover.assign k)).card ≤ ∑ j ∈ tρ, (fib j).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc (((s.image (𝒰.cover.assign k)).card : ℕ) : NNReal)
      ≤ ((∑ j ∈ tρ, (fib j).card : ℕ) : NNReal) := by exact_mod_cast hcard
    _ = ∑ j ∈ tρ, ((fib j).card : NNReal) := by push_cast; rfl
    _ ≤ ∑ _j ∈ tρ, C := Finset.sum_le_sum hD
    _ = C * (tρ.card : NNReal) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## The price of the repair -/

/-- **The parent family exceeds the refined one by at most `(c · λ)^{-1}`.**

The count is spent, in the blueprint, as the fibre bound `|𝕋[T_ρ]| ≤ ρ^{2+ζ}|𝕋|`; reading it
off the parent family instead of the configuration's own family multiplies it by
`|sPar| / |cfg.s|`, and this lemma prices that ratio.

If `(𝕋', Y')` is a `c`-refinement of `(𝕋, Y)`, the carriers all have the common volume `v`, and
`(𝕋, Y)` has aggregate fullness at least `a`, then `c · a · |𝕋| ≤ |𝕋'|`.  At the setup's own
constants — `c ≥ δ^η`, the conjunct `(δ:ENNReal)^η ≤ c` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`, and `a = δ^η`, the binder `hfull` — the ratio
is `δ^{-2η}`: subpolynomial, hence absorbed exactly like every other `⪆` of the section.

The equal-carrier-volume hypothesis is the one the repository's pigeonholes already ask for;
for a family of `Kakeya.ShadedTube δ` it is `Tube.volume_carrier_eq_volume_carrier`, so
it costs a producer nothing.  It is left as a hypothesis rather than imported, to keep the
interface honest and the import surface minimal. -/
theorem card_parent_le_of_isCRefinement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
    {ι : Type*} {s s' : Finset ι} {V V' : ι → ShadedBody E} {c a : NNReal} {v : ENNReal}
    (href : ShadedBody.IsCRefinement s' V' s V c)
    (hfull : a ≤ ShadedBody.fullness s V)
    (hvol : ∀ i ∈ s, volume (V i).carrier = v) (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) :
    (c : ENNReal) * (a : ENNReal) * (s.card : ENNReal) ≤ (s'.card : ENNReal) := by
  obtain ⟨⟨hss, hcar⟩, hmass⟩ := href
  -- the shade mass of the parent family is at least `a · |𝕋| · v`
  have hlow : (a : ENNReal) * ((s.card : ENNReal) * v) ≤ ∑ i ∈ s, volume (V i).shade :=
    ShadedBody.coe_fullness_mul_le_sum_volume_shade s V hfull
      (fun i hi ↦ (hvol i hi).ge)
  -- the shade mass of the refinement is at most `|𝕋'| · v`
  have hupp : ∑ i ∈ s', volume (V' i).shade ≤ (s'.card : ENNReal) * v := by
    refine (Finset.sum_le_card_nsmul s' _ v ?_).trans_eq ?_
    · intro i hi
      have hc : (V' i).carrier = (V i).carrier := congrArg ConvexSpaceBody.carrier (hcar i hi).1
      calc volume (V' i).shade ≤ volume (V' i).carrier := measure_mono (V' i).shade_subset
        _ = volume (V i).carrier := by rw [hc]
        _ = v := hvol i (hss hi)
    · simp [nsmul_eq_mul]
  -- chain, and cancel the common carrier volume
  have hstep : (c : ENNReal) * ((a : ENNReal) * ((s.card : ENNReal) * v))
      ≤ (c : ENNReal) * ∑ i ∈ s, volume (V i).shade := by gcongr
  have hchain : ((c : ENNReal) * (a : ENNReal) * (s.card : ENNReal)) * v
      ≤ (s'.card : ENNReal) * v := by
    have h := hstep.trans (hmass.trans hupp)
    calc ((c : ENNReal) * (a : ENNReal) * (s.card : ENNReal)) * v
        = (c : ENNReal) * ((a : ENNReal) * ((s.card : ENNReal) * v)) := by ring
      _ ≤ (s'.card : ENNReal) * v := h
  exact (ENNReal.mul_le_mul_iff_left hv0 hvtop).mp hchain

end Kakeya.VeryNotSticky

end

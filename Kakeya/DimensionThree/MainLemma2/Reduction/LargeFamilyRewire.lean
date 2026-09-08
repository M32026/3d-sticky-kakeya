/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.KKTResidualProps
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# The large-family Main Lemma 2 from the geometric core — wiring, no `SmallCard`

Nothing here is new
mathematics: every theorem composes two or three tree facts, and no statement in the tree changes.

## What is recorded

* **§4(a) — with the cardinality clause on the conclusion side there is no band.**  Main Lemma 2
  stated as `K_KT(β) ∧ K_F(β) ⇒ K_KT^{≥}(β − c)` — `Kakeya.KKTResidual.KatzTaoEstimateStrict`,
  GWZ Definition 3.4 restricted to families with `δ^{-2} ≤ |𝕋|` — follows from the geometric core
  `Kakeya.ML2Assembly.GeometricCoreAt` alone, with **no** small-cardinality input: the slot
  `Kakeya.ML2Assembly.SmallCardHyp` is not needed at all.
  `Kakeya.ML2Large.strict_drop_of_geometricCoreAt` composes
  `Kakeya.ML2Assembly.pointwiseCore_of_geometricCoreAt` with
  `Kakeya.KKTResidual.strict_sub_of_dichotomy`; `Kakeya.ML2Large.slack_drop_of_geometricCoreAt`
  is the same with the slack clause `δ^{-2+η} ≤ |𝕋|` (`Kakeya.KKTResidual.KatzTaoEstimateSlack`).
* **§4(b) — the padding lemma is the small-family theorem.**  The bridge `K_KT^{≥}(γ) → K_KT(γ)`
  that a conclusion-side Main Lemma 2 would need at the internal sites of the Kakeya bootstrap is,
  verbatim, `Strict γ → Small γ 2` (`Kakeya.ML2Large.padding_iff_small`), and in `ℝ³`
  `Small γ 2 ↔ K_KT γ` (`Kakeya.KKTResidual.small_iff_katzTaoEstimate`, the tree's affine
  squeeze).  Under such a padding lemma the large-family drop yields the protected Main Lemma 2
  outright (`Kakeya.ML2Large.mainLemma2Statement_of_geometricCoreAt_of_padding`), so the padding
  lemma is exactly what the conclusion-side design leaves open.
* **Monotonicity in the exponent** of the two clause-bearing estimates,
  `Kakeya.KKTResidual.KatzTaoEstimateStrict.mono` and
  `Kakeya.KKTResidual.KatzTaoEstimateSlack.mono`, copies of `Kakeya.KatzTaoEstimate.mono` with
  the cardinality clause passed through.

## What this makes a fact, and what it does not

In the axiom sets of those theorems the
`sorryAx` enters only through `Kakeya.ML2Assembly.exists_lemma91ParamsAt`, i.e. through GWZ Lemma
9.1 (`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`) and its own Section-9 leaf; the theorems
that do not touch Lemma 9.1 (`padding_iff_small` and the two `.mono`) are axiom-clean.

The import closure of this file contains no module of the abandoned route: in particular
`Kakeya.DimensionThree.MainLemma2Rewire` is **not** imported (it reaches that route through
`Kakeya.DimensionThree.MainLemma2Ptw` and `Kakeya.DimensionThree.MainLemma2`), and nothing here
needs it.

Source: GWZ §9, the proof of Main Lemma 2 from Lemma 9.1 (transcript l.1786–1960).  Branch (i) of
that proof (l.1800–1803, Lemma 7.7(B) conclusion (i) followed by Theorem 7.3(B)) is read here at the
absolute accuracy `β/2` per Prof. Hong Wang's clarification, so the every-scale case needs
`|𝕋| ≥ δ^{-1}` — which the conclusion-side clause supplies and Definition 3.4 does not.
-/

@[expose] public section

open MeasureTheory Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.KKTResidual

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The strict large-family estimate is monotone in `β`: a smaller exponent gives a stronger
bound, so `K_KT^{≥}(β)` for `β ≤ β'` implies `K_KT^{≥}(β')`.  A copy of
`Kakeya.KatzTaoEstimate.mono` with the clause `δ^{-2} ≤ |𝕋|` passed through. -/
theorem KatzTaoEstimateStrict.mono {β β' : ℝ} (hββ' : β ≤ β')
    (h : KatzTaoEstimateStrict.{u} E β) : KatzTaoEstimateStrict.{u} E β' := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh] with δ hh_δ
  intro ι s T hball hKT hfull hcard
  by_cases hcard0 : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard0
    subst hs; simp
  refine (hh_δ s T hball hKT hfull hcard).trans ?_
  have hone : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard0
  gcongr

/-- The slack large-family estimate is monotone in `β`.  A copy of `Kakeya.KatzTaoEstimate.mono`
with the clause `δ^{-2+η} ≤ |𝕋|` passed through. -/
theorem KatzTaoEstimateSlack.mono {β β' : ℝ} (hββ' : β ≤ β')
    (h : KatzTaoEstimateSlack.{u} E β) : KatzTaoEstimateSlack.{u} E β' := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh] with δ hh_δ
  intro ι s T hball hKT hfull hcard
  by_cases hcard0 : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard0
    subst hs; simp
  refine (hh_δ s T hball hKT hfull hcard).trans ?_
  have hone : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard0
  gcongr

end Kakeya.KKTResidual

namespace Kakeya.ML2Large

universe u

/-- **One-step large-family Main Lemma 2 from the geometric core, no `SmallCard`**
((a)).  Pointwise form: at every `β ∈ (0,1]` where `K_KT β` and `K_F β` hold there
is an `ε`-free drop `c` with `2c ≤ β` such that the strict large-family estimate `K_KT^{≥}(β - c)`
(`Kakeya.KKTResidual.KatzTaoEstimateStrict`, clause `δ^{-2} ≤ |𝕋|`) holds.  The geometric core
`Kakeya.ML2Assembly.GeometricCoreAt` is the explicit hypothesis; it has no producer in the tree. -/
theorem strict_drop_of_geometricCoreAt (hcore : ML2Assembly.GeometricCoreAt.{u}) :
    ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ c : ℝ, 0 < c ∧ 2 * c ≤ β ∧
        KKTResidual.KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  intro β hβ hβ1 hKT hKF
  obtain ⟨c, hc, hcβ, η, hη0, hη1, hdich⟩ :=
    ML2Assembly.pointwiseCore_of_geometricCoreAt hcore β hβ hβ1 hKT hKF
  exact ⟨c, hc, hcβ, KKTResidual.strict_sub_of_dichotomy hc hcβ hη0 hη1 le_rfl hdich⟩

/-- The same with the slack clause `δ^{-2+η} ≤ |𝕋|` (`Kakeya.KKTResidual.KatzTaoEstimateSlack`;
(a)). -/
theorem slack_drop_of_geometricCoreAt (hcore : ML2Assembly.GeometricCoreAt.{u}) :
    ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ c : ℝ, 0 < c ∧ 2 * c ≤ β ∧
        KKTResidual.KatzTaoEstimateSlack.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  intro β hβ hβ1 hKT hKF
  obtain ⟨c, hc, hcβ, η, hη0, hη1, hdich⟩ :=
    ML2Assembly.pointwiseCore_of_geometricCoreAt hcore β hβ hβ1 hKT hKF
  exact ⟨c, hc, hcβ, KKTResidual.slack_sub_of_dichotomy hc hcβ hη0 hη1 le_rfl hdich⟩

/-- **The padding lemma `K_KT^{≥}(γ) → K_KT(γ)` is exactly `Strict → Small 2`** ((b)), and `Small 2` is `K_KT` itself in `ℝ³` (`Kakeya.KKTResidual.small_iff_katzTaoEstimate`).
So the padding lemma is the full small-family theorem, not a monotonicity fact. -/
theorem padding_iff_small {γ : ℝ} (hγ : 0 ≤ γ) :
    (KKTResidual.KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) γ →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ) ↔
    (KKTResidual.KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) γ →
      KKTResidual.KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) γ 2) := by
  constructor
  · intro h hs
    exact KKTResidual.small_of_katzTaoEstimate 2 (h hs)
  · intro h hs
    exact (KKTResidual.small_iff_katzTaoEstimate hγ two_pos).mp (h hs)

/-- Under the padding lemma (at every exponent), the one-step large-family Main Lemma 2 gives the
full protected Main Lemma 2 (`Kakeya.VNSUniform.MainLemma2Statement`, via
`Kakeya.VNSUniform.mainLemma2Statement_of_pointwise_drop`) — i.e. the padding lemma is the whole
of what the conclusion-side design leaves open ((b)). -/
theorem mainLemma2Statement_of_geometricCoreAt_of_padding
    (hcore : ML2Assembly.GeometricCoreAt.{u})
    (hpad : ∀ γ : ℝ, 0 ≤ γ →
      KKTResidual.KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) γ →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ) :
    VNSUniform.MainLemma2Statement.{u} := by
  apply VNSUniform.mainLemma2Statement_of_pointwise_drop
  intro β hβ hβ1 hKT hKF
  obtain ⟨c, hc, hcβ, hstrict⟩ := strict_drop_of_geometricCoreAt hcore β hβ hβ1 hKT hKF
  exact ⟨c, hc, hpad (β - c) (by linarith) hstrict⟩

/-- compatibility: the `hpad` binder of `mainLemma2Statement_of_geometricCoreAt_of_padding` is, at each
`γ ≥ 0`, the left-hand side of `padding_iff_small`, hence small-family `K_KT` at `γ` under
`K_KT^{≥}(γ)`.  If either statement drifts, this stops compiling. -/
example (hpad : ∀ γ : ℝ, 0 ≤ γ →
      KKTResidual.KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) γ →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ) {γ : ℝ} (hγ : 0 ≤ γ) :
    KKTResidual.KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) γ →
      KKTResidual.KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) γ 2 :=
  (padding_iff_small hγ).mp (hpad γ hγ)

end Kakeya.ML2Large

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.Scheme
public import Kakeya.DimensionThree.MainLemma2.Reduction.LargeFamilyRewire

/-!
# Band item A7's wiring: from the geometric core to Main Lemma 2, through the Cap Lemma

 row A7. Three things are wired here, on top of the Cap Lemma
`Kakeya.ML2Cap.katzTaoEstimate_of_largeOne_of_seam` of `Cap/Scheme.lean`:

* `Kakeya.ML2Cap.katzTaoEstimate_sub_of_dichotomy'` — the `hsmall`-free form of
  `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`.  Band item A0 already recorded the shape
  as `Kakeya.ML2Cap.katzTaoEstimate_sub_of_dichotomy_of_capLemma`, with the Cap Lemma as an
  explicit binder; here the binder is discharged from the seam.
* `Kakeya.ML2Cap.pointwiseDrop_of_geometricCoreAt` — `Kakeya.ML2Assembly.PointwiseDrop` from
  `Kakeya.ML2Assembly.GeometricCoreAt` **alone** (plus the seam), with **no** appeal to
  `Kakeya.ML2Assembly.SmallCardHyp`.
* `Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt` — the route to
  `Kakeya.VNSUniform.MainLemma2Statement`, i.e. to the conclusion of the protected Main Lemma 2,
  through `Kakeya.VNSUniform.mainLemma2Statement_of_pointwise_drop`.

## No protected statement moves, and none has to

The conclusion reached is `Kakeya.VNSUniform.MainLemma2Statement`, which is a **pre-existing**
`Prop` already pinned to the protected declaration by the tripwires of
`Kakeya/DimensionThree/MainLemma2Ptw.lean`.  So the route is
`GeometricCoreAt + seam ⟹ MainLemma2Statement` with no new text on the protected side, and in
particular the large-family variants `Kakeya.ML2Large.strict_drop_of_geometricCoreAt` and
`Kakeya.ML2Large.mainLemma2Statement_of_geometricCoreAt_of_padding` are **not** needed: the Cap
Lemma discharges their `hpad` binder.  Nothing here adds a cardinality clause to
`Kakeya.KatzTaoEstimate`; the large-family restriction stays where band item A0 put it, in
`Kakeya.ML2Cap.KatzTaoEstimateLargeOne`, conclusion-side.

## ⚠ `Kakeya.ML2Assembly.SmallCardHyp` is NOT derivable this way, and is not needed

 row A7 asks for `smallCardHyp_of_geometricCoreAt`.  That statement
is **stronger than anything the band delivers, and the difference is not bookkeeping**:
`Kakeya.ML2Assembly.SmallCardHyp` demands `Kakeya.ML2Assembly.SmallCard γ` — equivalently, by
`Kakeya.ML2Squeeze.smallCard_iff_katzTaoEstimate`, `K_KT γ` — for **every** `γ ∈ [β/2, β)`, while
the geometric core supplies a **single** drop `c` with `2c ≤ β`, hence `K_KT(β - c)` and, by
`Kakeya.KatzTaoEstimate.mono`, `K_KT γ` only for `γ ≥ β - c`.  Since
`Kakeya.ML2Assembly.Dichotomy` is monotone in its gain, the drop may be shrunk but never
enlarged, so `β - c` is a floor: exponents in `[β/2, β - c)` are out of reach, and reaching them
is a strictly stronger estimate, not a rearrangement.

What is delivered instead is `Kakeya.ML2Cap.smallCard_of_geometricCoreAt` — the same statement
restricted to `γ ≥ β - c` — together with the observation that the reduction never needs more:
`Kakeya.ML2Assembly.pointwiseDrop_of_pointwiseCore` calls `SmallCardHyp` at `γ = β - c` and
nowhere else, and `Kakeya.ML2Cap.pointwiseDrop_of_geometricCoreAt` bypasses the slot altogether.

## The one hypothesis on `β - c ≤ 1`

`Kakeya.ML2Cap.katzTaoEstimate_sub_of_dichotomy'` carries `hβ1 : β - c ≤ 1` because the Cap Lemma
does (A6's `hγ1`, which the induction's bottom level and `Kakeya.ML2Cap.capBottom_cond` both
read).  It is **not** a hypothesis added to make anything typecheck: at the only call site the
reduction has, `Kakeya.ML2Assembly.PointwiseCore` is quantified over `β ≤ 1` and `0 < c`, so
`β - c ≤ 1` is free — `Kakeya.ML2Cap.pointwiseDrop_of_geometricCoreAt` supplies it by `linarith`
and takes no such binder itself.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Cap

universe u

/-- **The seam at every exponent** — the form the wiring consumes.

The drop `c` is chosen by `Kakeya.ML2Assembly.GeometricCoreAt`, and the Cap Lemma is then read at
`γ = β - c`, an exponent not known in advance; so the seam has to be available at every
`γ ∈ (0,1]`.  The three absolute constants are the ones band items A4/A5 fix:
`K_c = 16` (`Kakeya.CapRescale.capScale_of_angular`), `C₁ = Kakeya.CapRescale.capLoss` and
`c₁ = (8 · Kakeya.CapBroadNarrow.capPackingConst · 18 · capLoss)⁻¹`. -/
def CapSeamAll (Kc C₁ c₁ : NNReal) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    CapSeamOn.{u} (EuclideanSpace ℝ (Fin 3)) γ (γ / 4) Kc C₁ c₁

/-- `1 < finrank ℝ ℝ³`, the nondegeneracy hypothesis of the Cap Lemma. -/
theorem one_lt_finrank_space3 : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  simp

/-- **The Cap Lemma in `ℝ³`, modulo the seam.** -/
theorem katzTaoEstimate_of_largeOne_three {γ : ℝ} {Kc C₁ c₁ : NNReal}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamOn.{u} (EuclideanSpace ℝ (Fin 3)) γ (γ / 4) Kc C₁ c₁)
    (hL : KatzTaoEstimateLargeOne.{u} (EuclideanSpace ℝ (Fin 3)) γ) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ :=
  katzTaoEstimate_of_largeOne_of_seam one_lt_finrank_space3 hγ0 hγ1 hKc hC₁ hc₁0 hc₁1 hseam hL

/-! ## The `hsmall`-free reduction -/

/-- **`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` with `hsmall` deleted.**

Band item A0's `Kakeya.ML2Cap.largeOne_of_dichotomy` gives `L(β - c)` from the dichotomy alone;
the Cap Lemma turns it into `K_KT(β - c)`.  So the small-cardinality branch of the tree's version
is not merely unused here — it is *discharged*, by the cap induction. -/
theorem katzTaoEstimate_sub_of_dichotomy' {β g η c : ℝ} {Kc C₁ c₁ : NNReal}
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hβ1 : β - c ≤ 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hseam : CapSeamOn.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) ((β - c) / 4) Kc C₁ c₁)
    (hdich : ML2Assembly.Dichotomy.{u} β (β / 2) g η) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
  katzTaoEstimate_sub_of_dichotomy_of_capLemma
    (katzTaoEstimate_of_largeOne_three (by linarith) hβ1 hKc hC₁ hc₁0 hc₁1 hseam)
    hc hcβ hη0 hη1 hg hdich

/-! ## From the geometric core -/

/-- **The pointwise drop from the geometric core alone.**

`Kakeya.ML2Assembly.pointwiseCore_of_geometricCoreAt` supplies the drop `c` and the dichotomy
(GWZ Lemma 9.1 being consumed as a term inside it, through
`Kakeya.ML2Assembly.exists_lemma91ParamsAt`); band item A0 turns the dichotomy into `L(β - c)`;
the Cap Lemma turns that into `K_KT(β - c)`.  `Kakeya.ML2Assembly.SmallCardHyp` is not a
hypothesis. -/
theorem pointwiseDrop_of_geometricCoreAt {Kc C₁ c₁ : NNReal}
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamAll.{u} Kc C₁ c₁)
    (hcore : ML2Assembly.GeometricCoreAt.{u}) : ML2Assembly.PointwiseDrop.{u} := by
  intro β hβ hβ1 hKT hKF
  obtain ⟨c, hc, hcβ, η, hη0, hη1, hdich⟩ :=
    ML2Assembly.pointwiseCore_of_geometricCoreAt hcore β hβ hβ1 hKT hKF
  refine ⟨c, hc, ?_⟩
  exact katzTaoEstimate_sub_of_dichotomy' hKc hC₁ hc₁0 hc₁1 hc hcβ (by linarith) hη0 hη1
    le_rfl (hseam (β - c) (by linarith) (by linarith)) hdich

/-- **The small-cardinality case, as far as the band reaches it.**

The honest replacement for  row A7's
`smallCardHyp_of_geometricCoreAt`: the drop `c` is the geometric core's, and
`Kakeya.ML2Assembly.SmallCard γ` follows for every `γ ≥ β - c`, by
`Kakeya.KatzTaoEstimate.mono` and band item A0's
`Kakeya.ML2Cap.smallCard_of_katzTaoEstimate`.  Exponents in `[β/2, β - c)` are **not** reached;
see this module's docstring for why that is a strictly stronger estimate and not a
rearrangement. -/
theorem smallCard_of_geometricCoreAt {Kc C₁ c₁ : NNReal}
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamAll.{u} Kc C₁ c₁)
    (hcore : ML2Assembly.GeometricCoreAt.{u}) :
    ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ c : ℝ, 0 < c ∧ 2 * c ≤ β ∧ ∀ γ : ℝ, β - c ≤ γ → ML2Assembly.SmallCard.{u} γ := by
  intro β hβ hβ1 hKT hKF
  obtain ⟨c, hc, hcβ, η, hη0, hη1, hdich⟩ :=
    ML2Assembly.pointwiseCore_of_geometricCoreAt hcore β hβ hβ1 hKT hKF
  refine ⟨c, hc, hcβ, ?_⟩
  have hKTsub : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
    katzTaoEstimate_sub_of_dichotomy' hKc hC₁ hc₁0 hc₁1 hc hcβ (by linarith) hη0 hη1
      le_rfl (hseam (β - c) (by linarith) (by linarith)) hdich
  intro γ hγ
  exact smallCard_of_katzTaoEstimate (KatzTaoEstimate.mono hγ hKTsub)

/-- **The conclusion of the protected Main Lemma 2, from the geometric core and the seam.**

The conclusion is the pre-existing `Kakeya.VNSUniform.MainLemma2Statement`, which
`Kakeya/DimensionThree/MainLemma2Ptw.lean` pins to the protected declaration; **no protected text
is touched, and no cardinality clause is added anywhere.**  The `MonotoneOn ν` clause comes, as in
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_pointwiseCore`, from
`Kakeya.VNSUniform.estimateSet_shape` and not from any uniformity of GWZ Lemma 9.1.

This is **not** a proof of Main Lemma 2: `Kakeya.ML2Assembly.GeometricCoreAt` has no producer, and
`Kakeya.ML2Cap.CapSeamAll` is assumed. -/
theorem mainLemma2Statement_of_geometricCoreAt {Kc C₁ c₁ : NNReal}
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamAll.{u} Kc C₁ c₁)
    (hcore : ML2Assembly.GeometricCoreAt.{u}) : VNSUniform.MainLemma2Statement.{u} :=
  VNSUniform.mainLemma2Statement_of_pointwise_drop.{u}
    (pointwiseDrop_of_geometricCoreAt hKc hC₁ hc₁0 hc₁1 hseam hcore)

/-- **Fidelity tripwire.**  The conclusion of
`Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt` is, verbatim, the statement of the
protected `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`.  If either drifts,
this stops compiling — and it is stated as an `example` so that it records the fit without adding
a declaration to the tree. -/
example {Kc C₁ c₁ : NNReal} (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamAll.{u} Kc C₁ c₁) (hcore : ML2Assembly.GeometricCoreAt.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  mainLemma2Statement_of_geometricCoreAt hKc hC₁ hc₁0 hc₁1 hseam hcore

/-- **The padding lemma, at the threshold the band actually reaches.**

`Kakeya.ML2Large.padding_iff_small` shows the padding lemma *is* the small-family theorem; what
the cap induction supplies is that theorem **at the `δ^{-1}` threshold**, i.e. exactly
`Kakeya.ML2Cap.KatzTaoEstimateLargeOne γ → Kakeya.KatzTaoEstimate γ`, which is this alias.

It is worth recording what is **not** obtained.  The `hpad` binder of
`Kakeya.ML2Large.mainLemma2Statement_of_geometricCoreAt_of_padding` is stated at the `δ^{-2}`
threshold (`Kakeya.KKTResidual.KatzTaoEstimateStrict`), and that form is **strictly stronger as a
hypothesis to discharge**: `Kakeya.ML2Cap.strict_of_largeOne` runs `L(γ) → K_KT^{≥}(γ)` and there
is no converse, so a `Strict` hypothesis does not feed the cap induction, whose case (a) reads
`L(γ)` at every level scale.  That route is not needed —
`Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt` goes through
`Kakeya.ML2Assembly.PointwiseDrop` instead — and it is **not** discharged here. -/
theorem largeOne_padding_of_seam {γ : ℝ} {Kc C₁ c₁ : NNReal}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamOn.{u} (EuclideanSpace ℝ (Fin 3)) γ (γ / 4) Kc C₁ c₁) :
    KatzTaoEstimateLargeOne.{u} (EuclideanSpace ℝ (Fin 3)) γ →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ :=
  katzTaoEstimate_of_largeOne_three hγ0 hγ1 hKc hC₁ hc₁0 hc₁1 hseam

end Kakeya.ML2Cap

end

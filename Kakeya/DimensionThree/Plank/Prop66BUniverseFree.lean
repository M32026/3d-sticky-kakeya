/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.MasterScaleLemma61
public import Kakeya.DimensionThree.IsometryTransport

/-!
# GWZ Proposition 6.6(B) over the Part-(B) datum, at the caller's universe

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` is stated with
`Kakeya.KatzTaoEstimate.{0}`, because the two master-scale readings of GWZ Lemma 6.1 it discharges
internally (`Kakeya.KatzTaoEstimate.plankEstimateAtMasterScale` and
`Kakeya.KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity`) introduce representative index types
in `Type 0`.

The project statement of Proposition 6.6(B),
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Factorization.lean`), instead carries a **universe-polymorphic**
`Kakeya.KatzTaoEstimate`, whose universe is a parameter of that theorem and is therefore not
available as `0` inside its own proof.  That mismatch was recorded as the open chore "A6" of the
Part-(B) gap list.

This file closes it, in one line, with `Kakeya.KatzTaoEstimate.toTypeZero`
(`Kakeya/DimensionThree/IsometryTransport.lean`), which reindexes a `Type 0` family along
`Equiv.ulift` and is already proved.  Nothing else changes: the datum, the hypotheses and the
conclusion below are those of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`
verbatim.

Consequently the two master-scale Lemma-6.1 hypotheses are **not** part of the residual gap between
the Part-(B) chain and the project statement of Proposition 6.6(B): they are dischargeable from that
statement's own `Kakeya.KatzTaoEstimate` hypothesis at whatever universe the caller supplies.  What
remains of that gap is the datum conversion, essential distinctness of the outer representatives,
and the inner-scale threshold `δ ≤ s₀ * a` (derivable); the leaf-scale essential distinctness of
the fine family is, since, a hypothesis of the project statement itself; see the
docstring of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped ENNReal NNReal

noncomputable section

universe u

namespace Kakeya

/-- **GWZ Proposition 6.6(B) over the Part-(B) datum, with the Katz--Tao hypothesis at the caller's
universe.**

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` with `Kakeya.KatzTaoEstimate.{0}`
relaxed to `Kakeya.KatzTaoEstimate.{u}`, which is the shape the project statement
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` supplies.  The proof is
`Kakeya.KatzTaoEstimate.toTypeZero`. -/
theorem tubeMultiplicityOfGlobalPlankFactorisation_of_partBData_univ
    (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), ∃ s₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
          {κ : Type*} (r : Finset κ)
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
          C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
          δ ≤ ρ → ρ ≤ a → δ ≤ s₀ * a →
          ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
          D.Remark53Prop51 Cprop →
          (D.factor.cells : Set D.factor.Cell).Pairwise
            (fun x y => _root_.IsEssentiallyDistinct
              (D.factor.repr x).carrier (D.factor.repr y).carrier) →
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β :=
  tubeMultiplicityOfGlobalPlankFactorisation_of_partBData Cprop hCprop hβpos hβle
    hKKT.toTypeZero hKF

/-- **The two master-scale readings of GWZ Lemma 6.1 are free at the project statement's
universe.**

Stated separately so that the fact is citable without the datum: from exactly the four hypotheses
of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, both
`Kakeya.PlankEstimateAtMasterScale.{0}` and `Kakeya.PlankEstimateAtMasterScaleWithDensity.{0}`
follow. -/
theorem plankEstimatesAtMasterScale_of_katzTaoEstimate
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    PlankEstimateAtMasterScale.{0} β ∧ PlankEstimateAtMasterScaleWithDensity.{0} β :=
  ⟨KatzTaoEstimate.plankEstimateAtMasterScale hβpos hβle hKKT.toTypeZero,
    KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity hβpos hβle hKKT.toTypeZero⟩

end Kakeya

end

end

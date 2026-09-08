/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.SeamDischarge
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreFinal

/-!
# the estimate: the tripwire the axiom check runs on

`Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt_free` turns a producer of
`Kakeya.ML2Assembly.GeometricCoreAt` into `Kakeya.VNSUniform.MainLemma2Statement`.  the estimate asks for
that composition to be a **named** declaration, so that `#print axioms` — or
`Lean.collectAxioms`, which is what the gate actually runs — can measure the whole route rather
than a fragment.

This file cannot live under `Reduction/`: every `Cap/` module that reaches
`mainLemma2Statement_of_geometricCoreAt_free` imports `Reduction/`, so naming the composition
there would close an import cycle.  It is therefore a `Cap/` leaf whose only content is the
composition and the definitional pin it rests on.

**What the check shows today.**  The composition below is *conditional*: its hypothesis is the
per-exponent dichotomy statement, which has no producer, because the middle factor of GWZ's
three-factor split (`Reduction/SpineCoreFinal.lean`,
`Kakeya.ML2Core.multiplicity_le_of_three_factors`) has none — the estimate and the estimate, the rescaled datum
and the plank factoring, were never built.  So what the axiom gate measures here is the axiom cost
of the *plumbing*, and that is the point: if the plumbing were to carry `sorryAx`, no producer
could ever repair it.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Cap

universe u

/-- **the estimate.**  The named composition
`mainLemma2Statement_of_geometricCoreAt_free ∘ geometricCoreAt_of_pointwise`, so that the axiom
gate has a single declaration to check.  Both halves are definitional packaging: the content is
entirely in the hypothesis. -/
theorem mainLemma2Statement_of_pointwiseDichotomy
    (h : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
        ML2Assembly.Dichotomy.{u} β (β / 2)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) η) :
    VNSUniform.MainLemma2Statement.{u} :=
  mainLemma2Statement_of_geometricCoreAt_free (ML2Core.geometricCoreAt_of_pointwise h)

/-- **the estimate at the single remaining obligation.**  The same composition, taken through
`Kakeya.ML2Core.geometricCoreAt_of_windowGain`, so that the axiom gate measures the route a
producer of the window-branch gain will actually travel. -/
theorem mainLemma2Statement_of_windowGain
    (hright : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
            ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) →
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
            ≥ δ ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) →
          (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
          ¬ ML2Shading.DichotomyLeft (β / 2) s T →
          ∑ i ∈ s, MeasureTheory.volume (T i).shade
            ≤ (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
                * (s.card : ENNReal) ^ β
                * MeasureTheory.volume (⋃ i ∈ s, (T i).shade)) :
    VNSUniform.MainLemma2Statement.{u} :=
  mainLemma2Statement_of_geometricCoreAt_free (ML2Core.geometricCoreAt_of_windowGain hright)

end Kakeya.ML2Cap

end

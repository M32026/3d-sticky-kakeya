/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Prop66BChainResidueProof

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

universe u v w

namespace Kakeya.ML2Core

open Classical in
/-- GWZ 6.6(B) on an actual assigned coarse decomposition. The coarse scale
window pays the residue's inner-scale cutoff. All datum clauses are retained. -/
theorem source_prop66B_of_assigned_coarse_data {beta eps2 : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hKT : KatzTaoEstimate.{w} (EuclideanSpace ℝ (Fin 3)) beta)
    (heps2 : 0 < eps2) (heps21 : eps2 ≤ 1) :
    ∀ eps > (0 : ℝ), ∃ eta66 > (0 : ℝ), ∃ sigma0 > (0 : ℝ≥0), sigma0 ≤ 1 ∧
      ∀ {ι : Type u} (q : Finset ι) {sigma : ℝ≥0} (_hsigma0 : 0 < sigma)
        (U : ι → ShadedTube sigma (EuclideanSpace ℝ (Fin 3))),
        sigma ≤ sigma0 →
        (∀ i ∈ q, (U i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (U i).carrier (U j).carrier) →
        sigma ^ eta66 ≤ ShadedBody.fullness q (fun i => (U i).toShadedBody) →
        ∀ (rho Ahat Bhat : ℝ≥0) (hAB : Ahat ≤ Bhat) (hB1 : Bhat ≤ 1)
          {κ : Type v} (r : Finset κ)
          (R : κ → Tube rho (EuclideanSpace ℝ (Fin 3))) (n Cfib CF C0 Kdim : ℝ≥0),
          C0 ≤ sigma ^ (-eta66) → CF ≤ sigma ^ (-eta66) →
          Cfib ≤ sigma ^ (-eta66) → Kdim ≤ sigma ^ (-eta66) →
          sigma ^ (1 - eps2) ≤ rho → rho ≤ Ahat →
          ∀ (D6 : Section6PartBData Ahat Bhat hAB hB1 q U r R n Cfib CF C0),
          (∀ x ∈ D6.factor.cells, (D6.factor.coarseFibre x).Nonempty) →
          (∀ x ∈ D6.factor.cells,
            IsPlankOfDimensions Kdim Ahat Bhat (D6.factor.body x)) →
          (∀ x ∈ D6.factor.cells,
            maxDensity r (fun k => (R k).toConvexSpaceBody) ≤
              (C0 : ENNReal) * densityIn (D6.factor.coarseFibre x)
                (fun k => (R k).toConvexSpaceBody) (D6.factor.body x)) →
          ShadedBody.multiplicity q (fun i => (U i).toShadedBody) ≤
            (sigma : ENNReal) ^ (-eps) *
              (maxDensity q (fun i => (U i).toConvexSpaceBody)) ^ (1 - beta) *
              ((Ahat : ENNReal) / (Bhat : ENNReal)) ^ beta * (q.card : ENNReal) ^ beta := by
  intro eps heps
  obtain ⟨eta66, heta66, sigma66, hsigma66, s66, hs66, hcall⟩ :=
    Kakeya.prop66BPartBChainConstructed_of_katzTaoEstimate.{u, v, w}
      hbeta hbeta1 hKT eps heps
  refine ⟨eta66, heta66, min sigma66 (min 1 (s66 ^ (1 / eps2))),
    lt_min hsigma66 (lt_min zero_lt_one (NNReal.rpow_pos hs66)),
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro iota q sigma hsigma U hsmall hball hED hfull rho Ahat Bhat hAB hB1
    kappa r R n Cfib CF C0 Kdim hC0 hCF hCfib hKdim hrho hA D6 hnonempty hdim hcapture
  have hsigma1 : sigma ≤ 1 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsigmaRho : sigma ≤ rho := by
    calc
      sigma = sigma ^ (1 : ℝ) := (NNReal.rpow_one _).symm
      _ ≤ sigma ^ (1 - eps2) :=
        NNReal.rpow_le_rpow_of_exponent_ge hsigma hsigma1 (by linarith only [heps2])
      _ ≤ rho := hrho
  have hsigmaA : sigma ≤ s66 * Ahat :=
    Prop66BScale.le_mul_of_plankScale_le hsigma heps2
      (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))) hrho hA
  exact hcall q hsigma U (hsmall.trans (min_le_left _ _)) hball hED hfull
    rho Ahat Bhat hAB hB1 r R n Cfib CF C0 Kdim hC0 hCF hCfib hKdim
    hsigmaRho hA hsigmaA D6 hnonempty hdim hcapture

end Kakeya.ML2Core

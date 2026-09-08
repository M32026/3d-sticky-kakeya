/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreSupplyProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

theorem source_exists_shaded_uniform_on_given_hierarchy
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {V : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))} {N : Nat} {C : NNReal}
    (U : UniformTubeSet S (fun i => (V i).toTube) N C) (hN : 0 < N)
    (clamp : Nat) (hclamp : ∀ s : Finset iota, s <= S -> Nat.log 2 s.card <= clamp) :
    ∃ W : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)),
      (∀ i, (W i).toTube = (V i).toTube) /\
      (∀ i, (W i).shade <= (V i).shade) /\
      ShadedBody.fullness' S (fun i => (V i).toShadedBody) <=
        ((clamp + 1 : Nat) : ENNReal) ^ (2 * N + 2) *
          ShadedBody.fullness' S (fun i => (W i).toShadedBody) /\
      ∃ VU : ShadedUniformTubeSet S W N (max C 4),
        VU.tubeUniform.cover.indexSet = U.cover.indexSet /\
        VU.tubeUniform.cover.assign = U.cover.assign /\
        VU.tubeUniform.cover.tube = U.cover.tube /\
        VU.tubeUniform.branchingN = U.branchingN := by
  exact ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet U hN clamp hclamp

theorem source_exists_strong_everyScale_dichotomy (Cu : NNReal) (N : Nat)
    (hN : 4096 <= N) {e eps1 : Real} (he : e = 1 / Real.sqrt (N : Real))
    (heps1 : 0 < eps1) (hdiv : e <= eps1 / 25) :
    ∃ (C delta0 : NNReal) (K cl : Nat), 1 <= C /\ 0 < delta0 /\ delta0 <= 1 /\
      ∀ {iota : Type u} {delta : NNReal}, 0 < delta -> delta <= delta0 ->
      ∀ q : Nat -> Real, 0 <= q 0 -> (∀ m, m < N -> q m <= e * q (m + 1)) ->
      q N <= e -> ∀ (S : Finset iota) (V : iota -> Tube delta (EuclideanSpace Real (Fin 3))),
      (∀ i ∈ S, (V i).carrier <= Metric.closedBall 0 1) ->
      (S : Set iota).Pairwise
        (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ->
      UniformTubeSet S V (ssfGridLen delta) Cu ->
      Kakeya.maxDensity S (fun i => (V i).toConvexSpaceBody) <=
        ENNReal.ofReal ((delta : Real) ^ (-q 0)) ->
      ∃ S', S' <= S /\
        (S.card : ENNReal) <= StickyKakeya.totalLoss C K cl delta * (S'.card : ENNReal) /\
        ∃ U' : UniformTubeSet S' V (ssfGridLen delta) C,
          U'.IsKatzTaoAtEveryScale (ENNReal.ofReal ((delta : Real) ^ (-eps1))) \/
          ∃ a b m : Nat, ML2Reduction.IsKatzTaoDividingWindowLevels U'
            ((C : ENNReal) * StickyKakeya.totalLoss C K cl delta) q e N a b m := by
  exact ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_params (by simp) Cu N hN
    he heps1 hdiv

theorem source_exists_one_joint_pass {iota : Type u} {delta Cu : NNReal}
    (hdelta : 0 < delta) (hCu : 2 <= Cu) {S : Finset iota}
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (U : UniformTubeSet S (fun i => (Z i).toTube) (ssfGridLen delta) Cu)
    (hS : S.Nonempty) {massFloor : ENNReal} (hmass0 : massFloor ≠ 0)
    (hmass : ∀ i ∈ S, massFloor <= volume (Z i).shade)
    {Cstar : ENNReal} (hCstar : 2 <= Cstar) :
    ∃ (S' : Finset iota) (J : Nat) (hS' : S' <= S) (hhom : IsClassHomogeneousOn U S'),
      IsShadedRefinementOf U
        (((J + 1 : ENNReal) ^ (2 * ssfGridLen delta + 4)) ^ (ssfGridLen delta + 1)) S Z S' Z /\
      ∃ Phi : Nat -> Nat -> ENNReal, ∀ a, a <= ssfGridLen delta ->
        ∀ b, b <= ssfGridLen delta ->
        ∀ j ∈ (refinedHierarchy U hS' hhom rfl).cover.indexSet a,
          Phi a b <= Kakeya.maxDensity ((refinedHierarchy U hS' hhom rfl).assignFibre b a j)
            (fun k => ((refinedHierarchy U hS' hhom rfl).cover.tube b k).toConvexSpaceBody) /\
          Kakeya.maxDensity ((refinedHierarchy U hS' hhom rfl).assignFibre b a j)
            (fun k => ((refinedHierarchy U hS' hhom rfl).cover.tube b k).toConvexSpaceBody) <=
            Cstar * Phi a b := by
  exact exists_oneJointPass hdelta hCu Z U hS hmass0 hmass hCstar

end Kakeya.ML2Core

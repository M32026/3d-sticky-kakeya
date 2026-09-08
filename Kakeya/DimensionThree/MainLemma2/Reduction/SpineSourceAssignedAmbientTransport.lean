/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceChosenTowerRealization

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

open scoped Classical in
/-- Pull back one named normalized retained family through the actual canonical surjection. -/
noncomputable def sourceNormalizedLift {iota : Type u}
    (S : Finset iota) (pi : iota -> iota) (R : Finset iota) : Finset iota :=
  S.filter (fun i => pi i ∈ R)

section Comparison

variable {iota : Type u} {delta d Cu : NNReal} {ambient sourceFamily : Finset iota}
  {T : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
  {Y : iota -> Tube d (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- A required comparison for an actual finite level embedding and its paid errors.
Source logarithms use d, ambient logarithms use delta; neither denominator is replaced. -/
structure SourceAssignedAmbientComparison
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (Q : SourceThreadedTower sourceFamily Y M C) (S support : Finset iota) (pi : iota -> iota)
    (sample : Fin (M + 1) ↪o Fin (ssfGridLen delta + 1))
    (radiusError profileError : Real) : Prop where
  original_subset : S <= ambient
  source_subset : support <= sourceFamily
  radius_error_nonneg : 0 <= radiusError
  profile_error_nonneg : 0 <= profileError
  bottom_level : sample (Fin.last M) = Fin.last (ssfGridLen delta)
  radius_lower : ∀ k : Fin (M + 1),
    delta ^ radiusError * gridScale delta (ssfGridLen delta) (sample k) <= sourceTowerRadius d M k
  radius_upper : ∀ k : Fin (M + 1),
    sourceTowerRadius d M k <= delta ^ (-radiusError) * gridScale delta (ssfGridLen delta) (sample k)
  profile_lower : ∀ R : Finset iota, R <= support -> ∀ a b : Fin (M + 1), a < b ->
    profileExp delta (pairProfile U (sourceNormalizedLift S pi R) (sample a) (sample b)) <=
      Q.assignedProfileExp R a b + profileError
  profile_upper : ∀ R : Finset iota, R <= support -> ∀ a b : Fin (M + 1), a < b ->
    Q.assignedProfileExp R a b <=
      profileExp delta (pairProfile U (sourceNormalizedLift S pi R) (sample a) (sample b)) + profileError

/-- The actual source margin is two h. Usable quantized reflection is a separate
required conclusion, never inferred solely from radius or real error bounds. -/
def SourceAssignedAmbientDropReflection
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (Q : SourceThreadedTower sourceFamily Y M C) (S support : Finset iota) (pi : iota -> iota)
    (sample : Fin (M + 1) ↪o Fin (ssfGridLen delta + 1)) (hSrc : Real) : Prop :=
  ∀ R R' : Finset iota, R' <= R -> R <= support ->
    ∀ a b : Fin (M + 1), a < b ->
      Q.assignedProfileExp R' a b + 2 * hSrc <= Q.assignedProfileExp R a b ->
      Nat.ceil (profileExp delta
        (pairProfile U (sourceNormalizedLift S pi R') (sample a) (sample b)) / hSrc) <
      Nat.ceil (profileExp delta
        (pairProfile U (sourceNormalizedLift S pi R) (sample a) (sample b)) / hSrc)

/-- The corrected assigned-source drop reaches the same protected ambient potential.
Its actual existence premise is reflection, not a renamed geometric source profile. -/
theorem source_potential_drop_of_assigned_reflection
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (Q : SourceThreadedTower sourceFamily Y M C) (S support : Finset iota) (pi : iota -> iota)
    (sample : Fin (M + 1) ↪o Fin (ssfGridLen delta + 1)) {hSrc : Real}
    (hreflect : SourceAssignedAmbientDropReflection U Q S support pi sample hSrc)
    (hh : 0 < hSrc) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    {R R' : Finset iota} (hR' : R' <= R) (hR : R <= support)
    {a b : Fin (M + 1)} (hab : a < b)
    (hdrop : Q.assignedProfileExp R' a b + 2 * hSrc <= Q.assignedProfileExp R a b) :
    potential hSrc U (sourceNormalizedLift S pi R') <
      potential hSrc U (sourceNormalizedLift S pi R) := by
  classical
  have hlift : sourceNormalizedLift S pi R' <= sourceNormalizedLift S pi R := by
    intro i hi
    simp only [sourceNormalizedLift, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hR' hi.2⟩
  have hmono : ∀ k l, Nat.ceil
      (profileExp delta (pairProfile U (sourceNormalizedLift S pi R') k l) / hSrc) <=
      Nat.ceil (profileExp delta (pairProfile U (sourceNormalizedLift S pi R) k l) / hSrc) := by
    intro k l
    refine Nat.ceil_le_ceil (div_le_div_of_nonneg_right ?_ hh.le)
    exact profileExp_mono hdelta0 hdelta1 (pairProfile_ne_top U _ k l)
      (pairProfile_mono_family U hlift k l)
  unfold potential
  refine Finset.sum_lt_sum (fun p _ => hmono p.1 p.2) ?_
  refine ⟨((sample a).val, (sample b).val), ?_, hreflect R R' hR' hR a b hab hdrop⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨(sample a).isLt, (sample b).isLt⟩, sample.strictMono hab⟩

/-- Full strong-window transport on the same original U, with the actual lift and J-1 index.
This names a construction requirement; the source and runtime predicates are not identified. -/
def SourceAssignedWindowTransport
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (Q : SourceThreadedTower sourceFamily Y M C) (S : Finset iota) (pi : iota -> iota)
    (hlift : sourceNormalizedLift S pi sourceFamily <= ambient)
    (hhom : IsClassHomogeneousOn U (sourceNormalizedLift S pi sourceFamily))
    (sample : Fin (M + 1) ↪o Fin (ssfGridLen delta + 1))
    (A0 A1 N : Nat) (eta : Nat -> Real) (e : Real) (Cstar : ENNReal) : Prop :=
  ∀ a b : Fin (M + 1), ∀ J : Nat, SourceTowerDividingWindow Q A0 A1 N eta e a b J ->
    ML2Reduction.IsKatzTaoDividingWindowLevels (U.restrictOccupied hlift hhom)
      Cstar (fun m => eta (m + 1)) e N (sample a) (sample b) (J - 1)

end Comparison

/-- Full actual TrialSupplier/IsTrialAtGain input, without added source centring or ED. -/
structure SourceActualTrialState {iota : Type u} {delta Cu : NNReal}
    {ambient : Finset iota} {T : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    (Cu0 : NNReal) (etaIn : Real)
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (S : Finset iota) (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (lam : NNReal) : Prop where
  uniform_constant : Cu <= Cu0
  subset : S <= ambient
  nonempty : S.Nonempty
  tubes : ∀ i, (Z i).toTube = (T i).toTube
  shades : ∀ i, (Z i).shade <= (T i).shade
  homogeneous : IsClassHomogeneousOn U S
  ball : ∀ i ∈ S, (Z i).carrier <= Metric.closedBall 0 1
  max_density : Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) <= (delta : ENNReal) ^ (-etaIn)
  dense : ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody)
  comparable : ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody)
  lambda_floor : delta ^ etaIn / 2 <= lam
  ambient_card : (ambient.card : NNReal) <= delta ^ (-(4 : Real))

/-- Complete existence goal for a usable comparison on the SAME normalization/preparation witness.
This construction is an explicit additional hypothesis, separate from the chosen-tower theorem.
The final two fixed-polylog rows are extra required conclusions: the displayed raw centring charge
does not imply them. Their existence is part of the missing runtime bridge. -/
def SourceUniversalRuntimeBridgeGoal (M N K : Nat) (eta : Nat -> Real)
    (e eta0 etaIn hSrc radiusAllowance profileAllowance : Real) (Cu0 : NNReal) : Prop :=
  ∀ᶠ delta : NNReal in 𝓝[>] 0,
    ∀ {iota : Type u} (ambient : Finset iota)
      (T : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) (Cu : NNReal)
      (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
      (S : Finset iota) (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) (lam : NNReal),
      SourceActualTrialState Cu0 etaIn U S Z lam ->
    ∃ (I : Finset iota) (Y : iota -> ShadedTube (delta / 2) (EuclideanSpace Real (Fin 3)))
      (pi : iota -> iota), SourceCanonicalNormalization S I Z Y pi (2 * etaIn) /\
    ∃ (R0 R1 : Finset iota)
      (Q0 : SourceThreadedTower R0 (fun i => (Y i).toTube) M sourceThreadConstant)
      (Q1 : SourceThreadedTower R1 (fun i => (Y i).toTube) M sourceThreadConstant),
      R0 <= I /\ SourceFixedTowerInput Q0 sourceBottomED sourceLevelED eta0 /\
      (∑ i ∈ I, volume (Y i).shade) <=
        sourceTowerSelectionLoss M I.card * ∑ i ∈ R0, volume (Y i).shade /\
      SourceTowerRestriction Q0 Q1 /\ SourceFixedTowerInput Q1 sourceBottomED sourceLevelED eta0 /\
      SourceTowerStatistics Q1 Y /\
      SourceFixedPreparationLedger Q0 R0 R1 Y eta0 hSrc (sourceFixedPreparationLoss K (delta / 2)) /\
    ∃ (sample : Fin (M + 1) ↪o Fin (ssfGridLen delta + 1)) (radiusError profileError : Real)
      (hlift : sourceNormalizedLift S pi R1 <= ambient)
      (hhom : IsClassHomogeneousOn U (sourceNormalizedLift S pi R1)) (Cstar : ENNReal),
      radiusError <= radiusAllowance /\ profileError <= profileAllowance /\
      SourceAssignedAmbientComparison U Q0 S R1 pi sample radiusError profileError /\
      SourceAssignedAmbientDropReflection U Q0 S R1 pi sample hSrc /\
      SourceAssignedWindowTransport U Q1 S pi hlift hhom sample sourceBottomED sourceLevelED N eta e Cstar /\
      1 <= Cstar /\ Cstar <= sourceFixedPreparationLoss K (delta / 2) /\
      IsShadedRefinementOf U
        (sourceCentringCost delta (2 * etaIn) * sourceTowerSelectionLoss M I.card *
          sourceFixedPreparationLoss K (delta / 2)) S Z (sourceNormalizedLift S pi R1) Z /\
      IsShadedRefinementOf U (polylogLoss K delta) S Z (sourceNormalizedLift S pi R1) Z /\
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
        polylogLoss K delta *
          ShadedBody.fullness' (sourceNormalizedLift S pi R1) (fun i => (Z i).toShadedBody)

/-- The exact finite source Katz--Tao array good alternative, S:2688-2692. -/
def SourceFixedKTArrayGood {iota : Type u} {d : NNReal} {R : Finset iota}
    {Y : iota -> Tube d (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower R Y M C) (B : NNReal) (N : Nat) (e : Real) : Prop :=
  ∀ l : Nat, 1 <= l -> l <= M ->
    Q.assignedProfile R 0 l <= (B : ENNReal) ^ (N + 1) * (d : ENNReal) ^ (-(5 * e))

/-- Separate exact existential obligation to turn the fixed source good array into the
actual Sticky input on the original ambient hierarchy, with its own stated loss.
It is not supplied by fixed-M vector binning or assumed in source_exists_fixedTower_preparation. -/
def SourceAssignedStickyRealizationGoal {iota : Type u} {delta d Cu : NNReal}
    {ambient R : Finset iota}
    {T : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {Y : iota -> Tube d (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (U : UniformTubeSet ambient (fun i => (T i).toTube) (ssfGridLen delta) Cu)
    (Q : SourceThreadedTower R Y M C) (S : Finset iota) (pi : iota -> iota)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (B : NNReal) (N : Nat) (e etaS epsSt : Real) (loss : ENNReal) : Prop :=
  SourceFixedKTArrayGood Q B N e ->
    ∃ (L : Finset iota) (W : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (hL : L <= ambient) (hhom : IsClassHomogeneousOn U L)
      (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)),
      IsShadedRefinementOf U loss (sourceNormalizedLift S pi R) Z L W /\
      ShadedBody.fullness' (sourceNormalizedLift S pi R) (fun i => (Z i).toShadedBody) <=
        loss * ShadedBody.fullness' L (fun i => (W i).toShadedBody) /\
      (∀ i ∈ L, (W i).carrier <= Metric.closedBall 0 1) /\
      ENNReal.ofReal ((delta : Real) ^ etaS) <= ShadedBody.fullness' L (fun i => (W i).toShadedBody) /\
      Kakeya.maxDensity L (fun i => (W i).toConvexSpaceBody) <=
        ENNReal.ofReal ((delta : Real) ^ (-etaS)) /\
      ∃ Csh : NNReal, ∃ VU : ShadedUniformTubeSet L W (ssfGridLen delta) Csh,
        VU.tubeUniform.cover.indexSet = (refinedHierarchy U hL hhom hW).cover.indexSet /\
        VU.tubeUniform.cover.assign = (refinedHierarchy U hL hhom hW).cover.assign /\
        VU.tubeUniform.cover.tube = (refinedHierarchy U hL hhom hW).cover.tube /\
        VU.tubeUniform.branchingN = (refinedHierarchy U hL hhom hW).branchingN /\
        (refinedHierarchy U hL hhom hW).IsKatzTaoAtEveryScale
          (ENNReal.ofReal ((delta : Real) ^ (-epsSt)))

end Kakeya.ML2Core

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceBudget
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFactors
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineNewParentFactor

/-!
# Actual factor ceilings and their complete analytic applications

The returned input exponents and tube-scale thresholds are fixed before
the common input exponent, the source rung, and all runtime families.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Kakeya.ML2Assembly

universe u v

variable (E : Type v) [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The full eventual fine-factor estimate at its own scale. -/
def SourceFineFactorBody (beta charge input : Real) : Prop :=
  ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
    forall {iota : Type u} (f : Finset iota) (Y : iota -> ShadedTube delta E),
      (forall i, i ∈ f -> (Y i).carrier ⊆ Metric.closedBall (0 : E) 1) ->
      Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) <=
        (delta : ENNReal) ^ (-input) ->
      delta ^ input <= ShadedBody.fullness f (fun i => (Y i).toShadedBody) ->
      ShadedBody.multiplicity f (fun i => (Y i).toShadedBody) <=
        (delta : ENNReal) ^ (-charge) * (f.card : ENNReal) ^ beta

open Classical in
/-- The full actual translated new-parent fibre body at a fixed parent parameter. -/
def SourceParentFactorAtBody (beta charge input : Real) (thetaParent : NNReal)
    (etaPrime : Real) : Prop :=
  forall {delta Cu : NNReal} {iota : Type u} {family : Finset iota}
    {T : iota -> Tube delta E} {L a p : Nat}
    {U : Tube.UniformTubeSet family T L Cu} {tp : Finset iota}
    {Yp : iota -> ShadedTube (Tube.gridScale delta L p) E} {shift : E} {j : iota},
    0 < delta -> delta <= 1 -> a <= p -> p <= L ->
    Tube.gridScale delta L p <= thetaParent ->
    tp ⊆ ML2Reduction.activeNodes U.cover.toChain p ->
    (forall k, (Yp k).toTube = (U.cover.tube p k).translate shift) ->
    (forall k, k ∈ ({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} :
        Finset iota) -> (Yp k).carrier ⊆ Metric.closedBall (0 : E) 1) ->
    delta ^ input <= ShadedBody.fullness
      ({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} : Finset iota)
      (fun k => (Yp k).toShadedBody) ->
    Kakeya.maxDensity (U.nodesUnder p a j)
      (fun k => (U.cover.tube p k).toConvexSpaceBody) <=
        (delta : ENNReal) ^ (-(2 * etaPrime)) ->
    ShadedBody.multiplicity
      ({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} : Finset iota)
      (fun k => (Yp k).toShadedBody) <=
        (delta : ENNReal) ^ (-charge) *
          ((({k ∈ tp | ML2Reduction.coarseNode U.cover.toChain a p k = j} :
            Finset iota).card : ENNReal)) ^ beta

/-- The complete outer estimate with ambient fullness and density scales decoupled. -/
def SourceOuterFactorAtBody (beta charge input : Real) (thetaOuter : NNReal)
    (densityExponent : Real) : Prop :=
  forall {theta : NNReal}, 0 < theta -> theta <= thetaOuter ->
    forall dt : NNReal, 0 < dt -> dt <= theta ->
    forall {iota : Type u} (t : Finset iota) (Y : iota -> ShadedTube theta E),
      (forall k, k ∈ t -> (Y k).carrier ⊆ Metric.closedBall (0 : E) 1) ->
      dt ^ input <= ShadedBody.fullness t (fun k => (Y k).toShadedBody) ->
      Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) <=
        (dt : ENNReal) ^ (-densityExponent) ->
      ShadedBody.multiplicity t (fun k => (Y k).toShadedBody) <=
        (dt : ENNReal) ^ (-charge) * (t.card : ENNReal) ^ beta

/-- Actual estimator outputs: three exponents and two distinct tube-scale thresholds. -/
structure SourceFactorCeilingData where
  fineInput : Real
  parentInput : Real
  outerInput : Real
  parentThreshold : NNReal
  outerThreshold : NNReal

open Classical in
/-- Only returned ambient exponent ceilings enter the later finite minimum. -/
noncomputable def sourceFactorCeilingSet (x : SourceFactorCeilingData) : Finset Real :=
  {x.fineInput, x.parentInput, x.outerInput}

/-- All returned signs, thresholds, and complete bodies before any input or rung choice. -/
structure SourceFactorCores (beta epsFine epsParent epsOuter : Real)
    (x : SourceFactorCeilingData) : Prop where
  fine_input_pos : 0 < x.fineInput
  parent_input_pos : 0 < x.parentInput
  outer_input_pos : 0 < x.outerInput
  parent_threshold_pos : 0 < x.parentThreshold
  parent_threshold_le_one : x.parentThreshold <= 1
  outer_threshold_pos : 0 < x.outerThreshold
  outer_threshold_le_one : x.outerThreshold <= 1
  ceilings_pos : forall h : Real, h ∈ sourceFactorCeilingSet x -> 0 < h
  fine : SourceFineFactorBody.{u} E beta epsFine x.fineInput
  parent : forall etaPrime : Real, 0 <= etaPrime ->
    SourceParentFactorAtBody.{u} E beta (epsParent + 2 * etaPrime)
      x.parentInput x.parentThreshold etaPrime
  outer : forall k : Real, 0 <= k ->
    SourceOuterFactorAtBody.{u} E beta (epsOuter + k) x.outerInput x.outerThreshold k

/-- A1: the fine ceiling and full body come from the actual Katz-Tao estimate. -/
theorem source_exists_fine_factor {beta epsFine : Real}
    (hbeta : 0 <= beta) (hKT : KatzTaoEstimate.{u} E beta) (heps : 0 < epsFine) :
    exists Hf : Real, 0 < Hf /\ SourceFineFactorBody.{u} E beta epsFine Hf := by
  exact ML2Core.exists_fine_factor (E := E) hbeta hKT heps

/-- A2: the actual parent call precedes every nonnegative parent-density parameter. -/
theorem source_exists_parent_factor {beta epsParent : Real}
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} E beta) (heps : 0 < epsParent) :
    exists Hp : Real, 0 < Hp /\ exists thetaParent : NNReal,
      0 < thetaParent /\ thetaParent <= 1 /\
      forall etaPrime : Real, 0 <= etaPrime ->
        SourceParentFactorAtBody.{u} E beta (epsParent + 2 * etaPrime)
          Hp thetaParent etaPrime := by
  obtain ⟨H, hH, theta, htheta0, htheta1, hcore⟩ :=
    ML2Core.exists_newParent_factor_at (E := E) hbeta0 hbeta1 hKT heps
  refine ⟨H, hH, theta, htheta0, htheta1, ?_⟩
  intro etaPrime heta delta Cu iota family T L a p U tp Yp shift j
    hdelta0 hdelta1 hap hpL hscale htp hYp hball hfull hdens
  exact hcore hdelta0 hdelta1 hap hpL hscale heta htp hYp hball hfull hdens

/-- A3: the actual outer call precedes every nonnegative density exponent. -/
theorem source_exists_outer_factor {beta epsOuter : Real}
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} E beta) (heps : 0 < epsOuter) :
    exists Hc : Real, 0 < Hc /\ exists thetaOuter : NNReal,
      0 < thetaOuter /\ thetaOuter <= 1 /\
      forall k : Real, 0 <= k ->
        SourceOuterFactorAtBody.{u} E beta (epsOuter + k) Hc thetaOuter k := by
  obtain ⟨H, hH, theta0, htheta0, htheta1, hcore⟩ :=
    ML2Core.exists_coarse_factor (E := E) hbeta0 hbeta1 hKT heps
  refine ⟨H, hH, theta0, htheta0, htheta1, ?_⟩
  intro k hk theta htheta hscale dt hdt0 hdttheta iota t Y hball hfull hdens
  exact hcore htheta hscale dt hdt0 hdttheta hk t Y hball hfull hdens

/-- A4: all three real producer calls are fixed together before later input ceilings. -/
theorem source_exists_factor_cores {beta epsFine epsParent epsOuter : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} E beta)
    (hf : 0 < epsFine) (hp : 0 < epsParent) (hc : 0 < epsOuter) :
    exists x : SourceFactorCeilingData,
      SourceFactorCores.{u} E beta epsFine epsParent epsOuter x := by
  obtain ⟨Hf, hHf, hFine⟩ := source_exists_fine_factor E hbeta0.le hKT hf
  obtain ⟨Hp, hHp, thetaP, hthetaP0, hthetaP1, hParent⟩ :=
    source_exists_parent_factor E hbeta0.le hbeta1 hKT hp
  obtain ⟨Hc, hHc, thetaC, hthetaC0, hthetaC1, hOuter⟩ :=
    source_exists_outer_factor E hbeta0.le hbeta1 hKT hc
  let x : SourceFactorCeilingData := ⟨Hf, Hp, Hc, thetaP, thetaC⟩
  refine ⟨x, {
    fine_input_pos := hHf
    parent_input_pos := hHp
    outer_input_pos := hHc
    parent_threshold_pos := hthetaP0
    parent_threshold_le_one := hthetaP1
    outer_threshold_pos := hthetaC0
    outer_threshold_le_one := hthetaC1
    ceilings_pos := ?_
    fine := hFine
    parent := hParent
    outer := hOuter }⟩
  intro h hh
  simp only [sourceFactorCeilingSet, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl
  · exact hHf
  · exact hHp
  · exact hHc

/-- A5: lower the common fine input exponent on a tail of positive scales below one. -/
theorem sourceFineFactorBody_mono_input {beta charge H etaL : Real}
    (hbody : SourceFineFactorBody.{u} E beta charge H)
    (hetaL : 0 < etaL) (hcap : etaL <= H) :
    SourceFineFactorBody.{u} E beta charge etaL := by
  filter_upwards [hbody, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta hdelta hdelta1
  intro iota f Y hball hdens hfull
  apply hdelta f Y hball
  · exact hdens.trans (ENNReal.rpow_le_rpow_of_exponent_ge
      (by exact_mod_cast hdelta1.2.le) (neg_le_neg hcap))
  · exact (NNReal.rpow_le_rpow_of_exponent_ge hdelta1.1 hdelta1.2.le hcap).trans hfull

/-- A6: lower parent fullness input, preserving every actual fibre and density row. -/
theorem sourceParentFactorAtBody_mono_input
    {beta charge H etaL etaPrime : Real} {thetaParent : NNReal}
    (hbody : SourceParentFactorAtBody.{u} E beta charge H thetaParent etaPrime)
    (hetaL : 0 < etaL) (hcap : etaL <= H) :
    SourceParentFactorAtBody.{u} E beta charge etaL thetaParent etaPrime := by
  intro delta Cu iota family T L a p U tp Yp shift j
    hdelta0 hdelta1 hap hpL hscale htp hYp hball hfull hdens
  exact hbody hdelta0 hdelta1 hap hpL hscale htp hYp hball
    ((NNReal.rpow_le_rpow_of_exponent_ge hdelta0 hdelta1 hcap).trans hfull) hdens

/-- A7: lower outer fullness input at every auxiliary scale below the actual threshold. -/
theorem sourceOuterFactorAtBody_mono_input
    {beta charge H etaL k : Real} {thetaOuter : NNReal}
    (hbody : SourceOuterFactorAtBody.{u} E beta charge H thetaOuter k)
    (htheta : thetaOuter <= 1) (hetaL : 0 < etaL) (hcap : etaL <= H) :
    SourceOuterFactorAtBody.{u} E beta charge etaL thetaOuter k := by
  intro theta htheta0 hscale dt hdt0 hdttheta iota t Y hball hfull hdens
  exact hbody htheta0 hscale dt hdt0 hdttheta t Y hball
    ((NNReal.rpow_le_rpow_of_exponent_ge hdt0
      (hdttheta.trans (hscale.trans htheta)) hcap).trans hfull) hdens

/-- Actual scheduled charges and density parameters, uniformly over every source rung. -/
structure SourceScheduledFactorBodies (beta varpi eps1 : Real)
    (rawGain rawDens : Real -> Real) (a : SourceLocalAccuracyData)
    (etaL : Real) (x : SourceFactorCeilingData) : Prop where
  parent_parameter_nonneg : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    0 <= sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16))
      (rawDens (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16))
  outer_density_nonneg : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    0 <= a.kappaC + ML2Spine.spineRung beta varpi eps1
      (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m
  fine : ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
    forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
      forall {iota : Type u} (f : Finset iota) (Y : iota -> ShadedTube delta E),
        (forall i, i ∈ f -> (Y i).carrier ⊆ Metric.closedBall (0 : E) 1) ->
        Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) <=
          (delta : ENNReal) ^ (-etaL) ->
        delta ^ etaL <= ShadedBody.fullness f (fun i => (Y i).toShadedBody) ->
        ShadedBody.multiplicity f (fun i => (Y i).toShadedBody) <=
          (delta : ENNReal) ^ (-(a.epsf m)) * (f.card : ENNReal) ^ beta
  parent : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceParentFactorAtBody.{u} E beta (a.epsp m) etaL x.parentThreshold
      (sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
        (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
        (rawGain (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16))
        (rawDens (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16)))
  outer : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceOuterFactorAtBody.{u} E beta
      (a.epsc m + ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m)
      etaL x.outerThreshold
      (a.kappaC + ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m)

/-- A8: produce the actual finite ceiling set before every common input and actual rung. -/
theorem sourceSpine_exists_factor_ceilings_at_budget {beta varpi eps1 s : Real}
    {rawGain rawDens : Real -> Real} {a : SourceLocalAccuracyData}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens)
    (hKT : KatzTaoEstimate.{u} E beta)
    (hbudget : SourceLocalBudget beta varpi eps1 rawGain rawDens s a) :
    exists x : SourceFactorCeilingData,
      SourceFactorCores.{u} E beta s s s x /\
      forall etaL : Real, 0 < etaL ->
        (forall H : Real, H ∈ sourceFactorCeilingSet x -> etaL <= H) ->
        SourceScheduledFactorBodies.{u} E beta varpi eps1 rawGain rawDens a etaL x := by
  obtain ⟨x, hcores⟩ := source_exists_factor_cores E hbeta0 hbeta1 hKT
    hbudget.accuracy_pos hbudget.accuracy_pos hbudget.accuracy_pos
  refine ⟨x, hcores, ?_⟩
  intro etaL hetaL hcap
  have hf : etaL <= x.fineInput := hcap _ (by simp [sourceFactorCeilingSet])
  have hpCap : etaL <= x.parentInput := hcap _ (by simp [sourceFactorCeilingSet])
  have hc : etaL <= x.outerInput := hcap _ (by simp [sourceFactorCeilingSet])
  let G := sourceChoiceGain beta rawGain rawDens
  let D := sourceChoiceDens beta rawDens
  let rung := ML2Spine.spineRung beta varpi eps1 G D
  let P := fun m => sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
    (rung (m + 1)) (rawGain (rung (m + 1) / 16)) (rawDens (rung (m + 1) / 16))
  have hP (m : Nat) (hm : m < ML2Spine.spineCount varpi eps1) : 0 <= P m :=
    (sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm).parent_pos.le
  have hk (m : Nat) (hm : m < ML2Spine.spineCount varpi eps1) :
      0 <= a.kappaC + rung m := by
    have hparent := sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm
    exact add_nonneg hbudget.coarse_density_pos.le
      (hparent.margin_pos.le.trans hparent.margin_le_rung)
  refine {
    parent_parameter_nonneg := hP
    outer_density_nonneg := hk
    fine := ?_
    parent := ?_
    outer := ?_ }
  · have hFine := sourceFineFactorBody_mono_input E hcores.fine hetaL hf
    filter_upwards [hFine] with delta hdelta
    intro m hm iota f Y hball hdens hfull
    rw [hbudget.fine_eq m]
    exact hdelta f Y hball hdens hfull
  · intro m hm
    rw [hbudget.parent_charge_eq m, hbudget.parent_accuracy_eq m]
    exact sourceParentFactorAtBody_mono_input E
      (hcores.parent (P m) (hP m hm)) hetaL hpCap
  · intro m hm
    rw [hbudget.coarse_charge_eq m, hbudget.outer_accuracy_eq m, add_assoc]
    exact sourceOuterFactorAtBody_mono_input E
      (hcores.outer (a.kappaC + rung m) (hk m hm)) hcores.outer_threshold_le_one hetaL hc

end Kakeya.ML2Assembly

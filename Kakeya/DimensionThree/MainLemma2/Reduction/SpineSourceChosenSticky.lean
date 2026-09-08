/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParameterChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceGridChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceIndex
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceLocalReserve
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectDichotomy
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- Source structural accuracy, fixed before the numerical grid. -/
noncomputable def sourceStickyChi (varpi : Real) : Real := min (varpi / 4) (1 / 2)

/-- The multiplicity call uses its own accuracy and its own input exponent. -/
noncomputable def sourceStickyAccuracy (beta varpi : Real) : Real :=
  min (sourceStickyChi varpi) (beta / 4)

/-- The complete actual Sticky estimate at one input exponent and one runtime scale. -/
def SourceStickyEstimateAt (delta : NNReal) (accuracy inputExponent : Real) : Prop :=
  ∀ {iota : Type u} {eta : Real}, eta <= inputExponent ->
  ∀ (s : Finset iota) (V : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
    (∀ i ∈ s, (V i).carrier <= Metric.closedBall 0 1) ->
    ∀ {C : NNReal} (VU : ShadedUniformTubeSet s V (ssfGridLen delta) C),
      ENNReal.ofReal ((delta : Real) ^ eta) <=
        ShadedBody.fullness' s (fun i => (V i).toShadedBody) ->
      Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) <=
        ENNReal.ofReal ((delta : Real) ^ (-eta)) ->
      VU.tubeUniform.IsKatzTaoAtEveryScale
        (ENNReal.ofReal ((delta : Real) ^ (-inputExponent))) ->
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody) <=
        ENNReal.ofReal ((delta : Real) ^ (-accuracy))

/-- The map carries its actual complete estimate body at every positive accuracy. -/
structure SourceStickyExponentMap (Eexp : Real -> Real) : Prop where
  positive : ∀ accuracy : Real, 0 < accuracy -> 0 < Eexp accuracy
  estimate : ∀ accuracy : Real, 0 < accuracy ->
    ∃ delta0 : Real, 0 < delta0 /\ delta0 <= 1 /\
      ∀ delta : NNReal, 0 < delta -> (delta : Real) <= delta0 ->
        SourceStickyEstimateAt.{u} delta accuracy (Eexp accuracy)

/-- Actual map acquisition from the existing Sticky theorem, at the same universe. -/
theorem source_exists_actual_sticky_map :
    StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace Real (Fin 3)) →
    ∃ Eexp : Real -> Real, SourceStickyExponentMap.{u} Eexp := by
  intro hSFE
  obtain ⟨Eexp, hpos, hestimate⟩ :=
    ML2Reduction.exists_everyScale_exponent.{0, u} (E := EuclideanSpace Real (Fin 3))
      finrank_euclideanSpace_fin hSFE
  refine ⟨Eexp, hpos, ?_⟩
  intro accuracy haccuracy
  obtain ⟨delta0, h0, h1, hdelta⟩ := hestimate haccuracy
  exact ⟨delta0, h0, h1, fun delta hdelta0 hle => hdelta hdelta0 hle⟩

/-- The two actual map values and G1 are fixed before any runtime scale or family. -/
theorem source_exists_chosen_sticky_grid {beta varpi : Real}
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace Real (Fin 3)))
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (hvarpi : 0 < varpi) :
    ∃ Eexp : Real -> Real, SourceStickyExponentMap.{u} Eexp /\
      ∃ etaA epsSt eps1 : Real,
        etaA = Eexp (sourceStickyChi varpi) /\
        epsSt = Eexp (sourceStickyAccuracy beta varpi) /\
        0 < sourceStickyChi varpi /\ 0 < sourceStickyAccuracy beta varpi /\
        0 < etaA /\ 0 < epsSt /\ 0 < eps1 /\
        ML2Spine.SourceGridChoiceBounds beta varpi etaA epsSt eps1 := by
  have hchi : 0 < sourceStickyChi varpi := lt_min (by positivity) (by norm_num)
  have hacc : 0 < sourceStickyAccuracy beta varpi := lt_min hchi (by positivity)
  obtain ⟨Eexp, hE⟩ := source_exists_actual_sticky_map.{u} hSFE
  have hetaA := hE.positive _ hchi
  have hepsSt := hE.positive _ hacc
  obtain ⟨eps1, heps1, hgrid⟩ :=
    ML2Spine.sourceSpine_exists_grid_choice hbeta0 hbeta1 hvarpi hetaA hepsSt
  exact ⟨Eexp, hE, Eexp (sourceStickyChi varpi), Eexp (sourceStickyAccuracy beta varpi),
    eps1, rfl, rfl, hchi, hacc, hetaA, hepsSt, heps1, hgrid⟩

/-- The two selected accuracy calls have a common positive threshold. -/
theorem source_chosen_sticky_common_threshold {beta varpi : Real}
    {Eexp : Real -> Real} (hbeta : 0 < beta) (hvarpi : 0 < varpi)
    (hE : SourceStickyExponentMap.{u} Eexp) :
    ∃ delta0 : Real, 0 < delta0 /\ delta0 <= 1 /\
      ∀ delta : NNReal, 0 < delta -> (delta : Real) <= delta0 ->
        SourceStickyEstimateAt.{u} delta (sourceStickyChi varpi)
          (Eexp (sourceStickyChi varpi)) /\
        SourceStickyEstimateAt.{u} delta (sourceStickyAccuracy beta varpi)
          (Eexp (sourceStickyAccuracy beta varpi)) := by
  have hchi : 0 < sourceStickyChi varpi := lt_min (by positivity) (by norm_num)
  have hacc : 0 < sourceStickyAccuracy beta varpi := lt_min hchi (by positivity)
  obtain ⟨d1, hd10, hd11, hd1⟩ := hE.estimate _ hchi
  obtain ⟨d2, hd20, hd21, hd2⟩ := hE.estimate _ hacc
  refine ⟨min d1 d2, lt_min hd10 hd20, (min_le_left _ _).trans hd11, ?_⟩
  intro delta hdelta0 hle
  exact ⟨hd1 delta hdelta0 (hle.trans (min_le_left _ _)),
    hd2 delta hdelta0 (hle.trans (min_le_right _ _))⟩

/-- The actual chosen VNS package provides the strict multiplicity budget. -/
theorem source_chosen_sticky_strict_budget {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : ML2Assembly.Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    0 < sourceStickyAccuracy beta varpi /\
      sourceStickyAccuracy beta varpi < beta / 2 - (defectMargin beta varpi eps1
          (ML2Assembly.sourceChoiceGain beta rawGain rawDens)
          (ML2Assembly.sourceChoiceDens beta rawDens)) := by
  have hvarpi := hp.window_pos
  have hchi : 0 < sourceStickyChi varpi := lt_min (by positivity) (by norm_num)
  refine ⟨lt_min hchi (by positivity), ?_⟩
  have hchoice := ML2Assembly.sourceParameterChoice hbeta0 hbeta1 hp
  have hmargin := ML2Inputs.spineNu_le_div_48000 hbeta0 hbeta1 hvarpi heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  have hacc : sourceStickyAccuracy beta varpi <= beta / 4 := min_le_right _ _
  change defectMargin beta varpi eps1 (ML2Assembly.sourceChoiceGain beta rawGain rawDens)
    (ML2Assembly.sourceChoiceDens beta rawDens) <= beta / 48000 at hmargin
  linarith only [hmargin, hacc, hbeta0]

/-- A fixed polylog power is spent only after the strict Sticky accuracy is fixed. -/
theorem source_eventually_chosen_sticky_budget {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real} (K : Nat)
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : ML2Assembly.Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      polylogLoss K delta * (delta : ENNReal) ^ (-sourceStickyAccuracy beta varpi) <=
        (delta : ENNReal) ^ (-(beta / 2 - defectMargin beta varpi eps1
          (ML2Assembly.sourceChoiceGain beta rawGain rawDens)
          (ML2Assembly.sourceChoiceDens beta rawDens))) := by
  let target := beta / 2 - defectMargin beta varpi eps1
    (ML2Assembly.sourceChoiceGain beta rawGain rawDens) (ML2Assembly.sourceChoiceDens beta rawDens)
  have hgap : 0 < target - sourceStickyAccuracy beta varpi :=
    sub_pos.mpr (source_chosen_sticky_strict_budget hbeta0 hbeta1 heps1 hp).2
  filter_upwards [eventually_polylogLoss_le K hgap,
    Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with delta hpoly hdelta
  have h0 : (delta : ENNReal) ≠ 0 := by simpa using hdelta.1.ne'
  calc polylogLoss K delta * (delta : ENNReal) ^ (-sourceStickyAccuracy beta varpi)
      <= (delta : ENNReal) ^ (-(target - sourceStickyAccuracy beta varpi)) *
          (delta : ENNReal) ^ (-sourceStickyAccuracy beta varpi) := mul_le_mul' hpoly le_rfl
    _ = (delta : ENNReal) ^ (-target) := by
      rw [← ENNReal.rpow_add _ _ h0 ENNReal.coe_ne_top]
      congr 1
      ring

/-- G1's input cap is used by monotonicity of the every-scale constant, not of Eexp. -/
theorem source_everyScale_mono_input {delta Cu : NNReal} {iota : Type u}
    {s : Finset iota} {V : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    (U : UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen delta) Cu)
    {eps1 epsSt : Real} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hle : eps1 <= epsSt)
    (hKT : U.IsKatzTaoAtEveryScale (ENNReal.ofReal ((delta : Real) ^ (-eps1)))) :
    U.IsKatzTaoAtEveryScale (ENNReal.ofReal ((delta : Real) ^ (-epsSt))) := by
  apply hKT.mono
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdelta0)
    (by exact_mod_cast hdelta1) (neg_le_neg hle)

end Kakeya.ML2Core

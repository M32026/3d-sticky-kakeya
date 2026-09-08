/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceIndex
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteWitnessProducer
public import Kakeya.DimensionThree.MainLemma2.Cap.SeamDischarge

/-!
# Chosen-source closure and the conditional scalar profile gap

The actual ambient TrialSupplier remains an explicit producer obligation.
These interfaces preserve the source anchor and the existing free-cap route.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

open Filter Topology ML2Core

/-- The source anchor pays the scalar gap once the actual window log bound is supplied. -/
theorem sourceAnchor_scalar_gap {c e tau Theta delta : Real}
    (hc : 0 < c) (hct : c <= tau)
    (hlog : e ^ 2 / 2 <= Real.log Theta / Real.log (1 / delta)) :
    2 * (c * e ^ 2 / 8) <= (tau / 2) * (Real.log Theta / Real.log (1 / delta)) := by
  have htau : 0 <= tau / 2 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hlog htau
  have hctprod := mul_le_mul_of_nonneg_right hct (sq_nonneg e)
  nlinarith

/-- A witness and actual trial at the chosen tuple yield the full family dichotomy. -/
theorem chosenDichotomy_of_witness_and_trial
    {beta varpi eps1 eta etaIn aL : Real} {rawGain rawDens : Real -> Real}
    {Cu0 : NNReal} {K' : Nat}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) (haL0 : 0 < aL)
    (hwit : ML2Core.SiteWitness.{u} eta etaIn
      (ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)) aL Cu0)
    (htrial : ML2Core.TrialSupplier.{u} beta varpi eps1 etaIn
      (sourceChoicePotential beta varpi eps1 rawGain rawDens)
      (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
      Cu0 (ML2Core.polylogLoss K')) :
    Dichotomy.{u} beta (beta / 2)
      (4 * ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)) eta := by
  let c := ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
  let h := sourceChoicePotential beta varpi eps1 rawGain rawDens
  have hh : 0 < h :=
    (sourceChoice_ladderAnchorBounds hbeta0 hbeta1 heps1 hp).source_anchor_pos
  have hloss := eventually_polylogLoss_pow_potentialCeil_le (h := h) K' haL0
  obtain ⟨delta0, hdelta00, -, hCuBound⟩ := exists_threshold_const_le_rpow_neg_one Cu0
  apply dichotomy_of_descentDisjuncts
  filter_upwards [hwit, htrial, hloss,
    Ioo_mem_nhdsGT (show (0 : NNReal) < min 1 delta0 from lt_min zero_lt_one hdelta00)]
    with delta hw ht hl hdelta
  have hd0 : 0 < delta := hdelta.1
  have hd1 : delta < 1 := lt_of_lt_of_le hdelta.2 (min_le_left _ _)
  have hdle : delta <= delta0 := (lt_of_lt_of_le hdelta.2 (min_le_right _ _)).le
  intro i s T hball hKT hfull hcard
  obtain ⟨s', hsub, Cu, U, lam, K, hCu0, hcards, hsne, hmax, hlam0, hdense,
    hlamlow, houter, hK⟩ := hw s T hball hKT hfull hcard
  have hcard' := card_le_of_subset_of_card_le hsub hcards
  have ht' : IsTrialAtGain (beta / 2 - c) (4 * c + c) beta h etaIn U
      (polylogLoss K' delta) := ht s' T Cu U hCu0 hcard'
  change K * (delta : ENNReal) ^ (c - aL) <= 1 at hK
  apply dichotomy_disjuncts_of_chain hsub U
    (h := h) (α := aL) (ε₀' := beta / 2 - c + aL)
    (g' := 4 * c + c - aL) hbeta0.le hd0 hd1 hh
    (one_le_polylogLoss K' delta) (polylogLoss_ne_top K' delta)
    hcard' (hCuBound hd0 hdle Cu hCu0) hsne (fun j hj => hball j (hsub hj))
    hmax hlam0 hdense (absorb_half_of_loss_le hd0 hl) hlamlow ht'
    ?_ ?_ houter ?_ ?_
  · have hleft := absorb_of_loss_le (x := -(beta / 2 - c)) hd0 hl
    convert hleft using 1
    congr 1
    ring
  · exact absorb_of_loss_le (x := 4 * c + c) hd0 hl
  · have hleft := absorbK_of_budget (x := -(beta / 2)) hd0 hK
    convert hleft using 1
    congr 1
    ring
  · have hright := absorbK_of_budget (x := 4 * c) hd0 hK
    convert hright using 1
    congr 1
    ring

/-- The still-open chosen-tuple actual producer, with all constants before runtime data. -/
def ChosenTrialSuppliers : Prop :=
  forall beta : Real, 0 < beta -> beta <= 1 ->
    KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta ->
    FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta ->
    exists varpi : Real, exists rawGain rawDens : Real -> Real,
      Lemma91ParamsAt.{u} beta varpi rawGain rawDens /\
      exists eps1 : Real, 0 < eps1 /\
        exists eta etaIn aL : Real, exists K' : Nat,
          0 < eta /\ eta <= 1 /\ 0 < aL /\ eta + aL <= etaIn /\
          eta + aL < ML2Spine.spineNu beta varpi eps1
            (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) /\
          ML2Core.TrialSupplier.{u} beta varpi eps1 etaIn
            (sourceChoicePotential beta varpi eps1 rawGain rawDens)
            (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
            (ShadedTube.ssfUniformConst 3) (ML2Core.polylogLoss K')

/-- Package the chosen actual trials using the existing unconditional scalar-site producer. -/
theorem pointwiseCore_of_chosen_trialSuppliers (hsup : ChosenTrialSuppliers.{u}) :
    PointwiseCore.{u} := by
  intro beta hbeta0 hbeta1 hKT hF
  obtain ⟨varpi, rawGain, rawDens, hp, eps1, heps1, eta, etaIn, aL, K',
    heta0, heta1, haL0, hladder, hbudget, htrial⟩ := hsup beta hbeta0 hbeta1 hKT hF
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  refine ⟨ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens),
    ML2Spine.spineNu_pos hbeta0 hp.window_pos heps1
      hchoice.params.gain_pos hchoice.params.dens_pos,
    ML2Spine.two_spineNu_le hbeta0 hbeta1 hp.window_pos heps1
      hchoice.params.gain_pos hchoice.params.dens_pos, eta, heta0, heta1, ?_⟩
  exact chosenDichotomy_of_witness_and_trial hbeta0 hbeta1 heps1 hp haL0
    (siteWitness_of_scalars heta1 haL0 hladder hbudget) htrial

/-- The free-cap theorem converts the existing pointwise core to a pointwise drop. -/
theorem pointwiseDrop_of_pointwiseCore_free (hcore : PointwiseCore.{u}) :
    PointwiseDrop.{u} := by
  intro beta hbeta0 hbeta1 hKT hF
  obtain ⟨c, hc, hcBeta, eta, heta0, heta1, hdich⟩ := hcore beta hbeta0 hbeta1 hKT hF
  exact ⟨c, hc, ML2Cap.katzTaoEstimate_sub_of_dichotomy_free hc hcBeta
    (by linarith) heta0 heta1 le_rfl hdich⟩

/-- The existing pointwise envelope gives the unchanged Main Lemma 2 proposition. -/
theorem mainLemma2Statement_of_pointwiseCore_free (hcore : PointwiseCore.{u}) :
    VNSUniform.MainLemma2Statement.{u} := by
  exact VNSUniform.mainLemma2Statement_of_pointwise_drop
    (pointwiseDrop_of_pointwiseCore_free hcore)

end Kakeya.ML2Assembly

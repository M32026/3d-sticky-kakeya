/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

/-- Scalar payment for an explicitly supplied raw-count charge. This supplies
no parent geometry. C1 proposes kappa=5 and denominator=48*300^9*C. -/
theorem source_direct_raw_count_payment
    (denominator kappa e tau etaParent : Real)
    (hdenominator : 0 < denominator) (hkappa : 0 <= kappa)
    (he : 0 < e) (htau : 0 < tau) (heta : 0 < etaParent)
    (hbudget : kappa * etaParent < e ^ 2 * tau / 8) :
    exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall Theta r : Real, 1 <= r -> r <= Theta ->
      e ^ 2 / 2 <= Real.log Theta / Real.log (1 / (delta : Real)) ->
      r ^ (4 * (tau / 16)) <=
        Theta ^ (tau / 2) * (delta : Real) ^ (kappa * etaParent) / denominator := by
  obtain ⟨delta0, hd0, hd1, hsmall⟩ :=
    Kakeya.ML2Shaded.exists_threshold_const_le_rpow_neg' denominator (sub_pos.mpr hbudget)
  refine ⟨delta0, hd0, hd1, ?_⟩
  intro delta hdelta hdd Theta r hr hrT hsep
  have hdR : (0 : Real) < delta := by exact_mod_cast hdelta
  have hdlt : delta < 1 := hdd.trans_le hd1
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hT0 : 0 < Theta := hr0.trans_le hrT
  have hlogpos := log_one_div_pos hdelta hdlt
  have hsep' := (le_div_iff₀ hlogpos).mp hsep
  rw [one_div, Real.log_inv] at hsep'
  have hdenlog := Real.log_le_log hdenominator (hsmall hdelta hdd.le)
  rw [Real.log_rpow hdR] at hdenlog
  have hrlog := mul_le_mul_of_nonneg_left (Real.log_le_log hr0 hrT)
    (show 0 <= tau / 4 by positivity)
  have hseplog := mul_le_mul_of_nonneg_left hsep' (show 0 <= tau / 4 by positivity)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hr0 _)
    (div_pos (mul_pos (Real.rpow_pos_of_pos hT0 _) (Real.rpow_pos_of_pos hdR _))
      hdenominator)).mp
  rw [Real.log_div (mul_pos (Real.rpow_pos_of_pos hT0 _)
    (Real.rpow_pos_of_pos hdR _)).ne' hdenominator.ne',
    Real.log_mul (Real.rpow_pos_of_pos hT0 _).ne' (Real.rpow_pos_of_pos hdR _).ne',
    Real.log_rpow hr0, Real.log_rpow hT0, Real.log_rpow hdR]
  nlinarith only [hdenlog, hrlog, hseplog]

end Kakeya.ML2Core

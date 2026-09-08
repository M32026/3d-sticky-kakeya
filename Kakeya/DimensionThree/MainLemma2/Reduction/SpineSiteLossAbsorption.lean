/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacProducer

/-!
# Uniform absorption of the three site splitting losses

The scalar input of the frozen B31 site consumers.
Source: the revised detailed GWZ proof, lines 4675-4681.
-/

@[expose] public section

open Topology Filter
open scoped NNReal

namespace Kakeya.ML2Core

/-- The zero-cardinality loss is bounded by the one-cardinality loss at the same scale. -/
theorem spineScaleLoss_zero_le_one (n : Nat) {sigma : NNReal}
    (hsigma : sigma <= 1) :
    ML2Reduction.spineScaleLoss n 0 sigma <=
      ML2Reduction.spineScaleLoss n 1 sigma := by
  have hupper : step1UpperBdAtScale n 0 = 0 := by
    apply ENNReal.coe_injective
    simp [coe_step1UpperBdAtScale]
  have hfiber :
      factoringStep1FiberPigeonholeConstant (step1LowerBdAtScale n sigma)
          (step1UpperBdAtScale n 0) <=
        factoringStep1FiberPigeonholeConstant (step1LowerBdAtScale n sigma)
          (step1UpperBdAtScale n 1) := by
    rw [hupper]
    have hzero : factoringStep1FiberPigeonholeConstant (step1LowerBdAtScale n sigma) 0 = 1 := by
      simp [factoringStep1FiberPigeonholeConstant]
    rw [hzero]
    exact one_le_factoringStep1FiberPigeonholeConstant
      (step1LowerBdAtScale_le_step1UpperBdAtScale n hsigma (by norm_num : 1 <= 1))
  unfold ML2Reduction.spineScaleLoss
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
    factoringStep1Step2AtScaleConstant factoringStep1AtScaleConstant
    factoringStep1PigeonholeConstant factoringStep3Constant
    factoringStep2PointwiseConstant MultiplicityFamily.scaleTripleConstant
    dyadicPigeonholeNatConstant ShadedBody.step5PackingRatio
  simp only [factoringStep2PigeonholeConstant_eq, Nat.log_zero_right, Nat.log_one_right,
    max_self, Nat.max_zero]
  gcongr

/-- A single small-scale threshold controls every cardinality, including zero,
and every intermediate scale between the small scale and one. -/
theorem eventually_spineScaleLoss_le_all (n : Nat) {kappa : Real}
    (hkappa : 0 < kappa) :
    Filter.Eventually
      (fun delta : NNReal =>
        forall N : Nat, (N : NNReal) <= delta ^ (-(4 : Real)) ->
        forall sigma : NNReal, delta <= sigma -> sigma <= 1 ->
          ML2Reduction.spineScaleLoss n N sigma <= delta ^ (-kappa))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  filter_upwards [eventually_spineScaleLoss_le n hkappa,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with delta hloss hdelta
  intro N hN sigma hds hs
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hone : ((1 : Nat) : NNReal) <= delta ^ (-(4 : Real)) := by
      simpa using NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos (z := -(4 : Real))
        hdelta.1 hdelta.2.le (by norm_num)
    exact (spineScaleLoss_zero_le_one n hs).trans
      (hloss 1 Nat.zero_lt_one hone sigma hds hs)
  · exact hloss N hNpos hN sigma hds hs

/-- A strict exponent gap absorbs the three splitting losses and the factor two,
uniformly over all three cardinalities and both intermediate scales. -/
theorem eventually_spineScaleLoss_prod3_mul_rpow_le_half
    {etaIn etaL : Real} (hgap : etaIn < etaL) :
    Filter.Eventually
      (fun delta : NNReal =>
        forall n1 n2 n3 : Nat,
          (n1 : NNReal) <= delta ^ (-(4 : Real)) ->
          (n2 : NNReal) <= delta ^ (-(4 : Real)) ->
          (n3 : NNReal) <= delta ^ (-(4 : Real)) ->
        forall sigma1 sigma2 : NNReal,
          delta <= sigma1 -> sigma1 <= 1 ->
          delta <= sigma2 -> sigma2 <= 1 ->
          ML2Reduction.spineScaleLoss 3 n1 delta *
            ML2Reduction.spineScaleLoss 3 n2 sigma1 *
            ML2Reduction.spineScaleLoss 3 n3 sigma2 *
            delta ^ etaL <= delta ^ etaIn / 2)
      (nhdsWithin 0 (Set.Ioi 0)) := by
  set kappa : Real := (etaL - etaIn) / 6 with hkappadef
  have hkappa : 0 < kappa := by rw [hkappadef]; linarith
  obtain ⟨delta0, hdelta0, htwo⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := 2) (by norm_num)
      (show (0 : Real) < (etaL - etaIn) / 2 by linarith)
  filter_upwards [eventually_spineScaleLoss_le_all 3 hkappa,
    Ioo_mem_nhdsGT (show (0 : NNReal) < min 1 delta0 from lt_min zero_lt_one hdelta0)]
    with delta hloss hdelta
  have hd0 : 0 < delta := hdelta.1
  have hd1 : delta <= 1 := hdelta.2.le.trans (min_le_left _ _)
  have hdsmall : delta <= delta0 := hdelta.2.le.trans (min_le_right _ _)
  have htwo' := htwo delta hd0 hdsmall
  intro n1 n2 n3 hn1 hn2 hn3 sigma1 sigma2 hds1 hs1 hds2 hs2
  have hfirst := hloss n1 hn1 delta le_rfl hd1
  have hsecond := hloss n2 hn2 sigma1 hds1 hs1
  have hthird := hloss n3 hn3 sigma2 hds2 hs2
  apply (le_div_iff₀ (show (0 : NNReal) < 2 by norm_num)).2
  calc
    ML2Reduction.spineScaleLoss 3 n1 delta *
        ML2Reduction.spineScaleLoss 3 n2 sigma1 *
        ML2Reduction.spineScaleLoss 3 n3 sigma2 * delta ^ etaL * 2
      <= delta ^ (-kappa) * delta ^ (-kappa) * delta ^ (-kappa) *
          delta ^ etaL * delta ^ (-((etaL - etaIn) / 2)) := by gcongr
    _ = delta ^ etaIn := by
      simp only [← NNReal.rpow_add hd0.ne']
      congr 1
      rw [hkappadef]
      ring

end Kakeya.ML2Core

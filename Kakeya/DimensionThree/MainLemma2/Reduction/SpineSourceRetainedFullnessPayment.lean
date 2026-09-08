/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceRetainedAnalyticData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceZeroDefectScalarDrop

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

theorem source_retained_fullness_payment {etaIn etaOut : Real}
    (hIn : 0 < etaIn) (hOut : 2 * etaIn <= etaOut) (K : Nat) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3))) (M C : Nat)
        (Q : SourceThreadedTower S T M C)
        (Z Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
        (R : Finset iota) (Q' : SourceThreadedTower R T M C),
      SourceParentRetainedState Q Z R Q' Z' (sourceFixedPreparationLoss K delta) ->
      delta ^ etaIn <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
      delta ^ etaOut <= ShadedBody.fullness R (fun i => (Z' i).toShadedBody) := by
  have hloss : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      sourceFixedPreparationLoss K delta <= (delta : ENNReal) ^ (-etaIn) := by
    simpa only [sourceFixedPreparationLoss, one_div, one_mul] using
      VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg
        (A := (2 : Real)) (B := (1 : Real)) (by norm_num) (by norm_num) K hIn
  filter_upwards [hloss, Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)]
    with delta hl hd
  intro iota S T M C Q Z Z' R Q' H hf
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hdt : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hfe : (delta : ENNReal) ^ etaIn <= ShadedBody.fullness' S
      (fun i => (Z i).toShadedBody) := by
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne', ShadedBody.coe_fullness] using
      (ENNReal.coe_le_coe.mpr hf)
  have hprod := (hfe.trans H.fullness).trans (mul_le_mul_right' hl _)
  have htwo : (delta : ENNReal) ^ (2 * etaIn) <=
      ShadedBody.fullness' R (fun i => (Z' i).toShadedBody) := by
    calc
      (delta : ENNReal) ^ (2 * etaIn) =
          (delta : ENNReal) ^ etaIn * (delta : ENNReal) ^ etaIn := by
        rw [← ENNReal.rpow_add _ _ hd0 hdt]
        congr 1
        ring
      _ <= (delta : ENNReal) ^ etaIn *
          ((delta : ENNReal) ^ (-etaIn) * ShadedBody.fullness' R (fun i => (Z' i).toShadedBody)) :=
        mul_le_mul_left' hprod _
      _ = ShadedBody.fullness' R (fun i => (Z' i).toShadedBody) := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 hdt, add_neg_cancel,
          ENNReal.rpow_zero, one_mul]
  have hout := (ENNReal.rpow_le_rpow_of_exponent_ge
    (show (delta : ENNReal) <= 1 by exact_mod_cast hd.2.le) hOut).trans htwo
  rw [← ShadedBody.coe_fullness] at hout
  apply ENNReal.coe_le_coe.mp
  simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hout


end Kakeya.ML2Core

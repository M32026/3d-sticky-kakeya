/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceScaleLossEnvelope
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQMiddleSelection

@[expose] public section

open Filter Topology
open Kakeya.ML2Core Kakeya.ML2Reduction
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

/-- Exact compatibility of the two existing source loss types, with positive finite
denominators on the source scale interval. -/
theorem sourceQSelectionLoss_preparation_compatibility (K : Nat) {delta : NNReal}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1) :
    (sourceQSelectionLoss K delta : ENNReal) = sourceFixedPreparationLoss K delta /\
      1 <= sourceQSelectionLoss K delta /\
      sourceQSelectionLoss K delta ≠ 0 /\
      sourceFixedPreparationLoss K delta < (⊤ : ENNReal) /\
      sourceFixedPreparationLoss K delta ≠ 0 := by
  have heq : (sourceQSelectionLoss K delta : ENNReal) =
      sourceFixedPreparationLoss K delta := rfl
  have hd : 0 < (delta : Real) := NNReal.coe_pos.mpr hdelta
  have hlog : 0 <= Real.logb 2 (1 / (delta : Real)) :=
    Real.logb_nonneg (by norm_num)
      ((le_div_iff₀ hd).mpr (by simpa using NNReal.coe_le_coe.mpr hdelta1))
  have hone : 1 <= sourceQSelectionLoss K delta := by
    change (1 : NNReal) <= Real.toNNReal _
    rw [← Real.toNNReal_one]
    exact Real.toNNReal_mono (one_le_pow₀ (by linarith))
  have hnz := ne_of_gt (zero_lt_one.trans_le hone)
  refine ⟨heq, hone, hnz, ?_, ?_⟩
  · rw [← heq]; exact ENNReal.coe_lt_top
  · rw [← heq]; exact_mod_cast hnz

/-- One common fixed K bounds the public one-scale loss in both source loss APIs. -/
theorem source_exists_spineScaleLoss_selection_envelope (A : NNReal) (B : Real)
    (hA : 0 < A) (hB : 0 <= B) :
    ∃ K : Nat, ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      forall (sigma : NNReal) (N : Nat),
        0 < delta -> delta <= sigma -> sigma <= 1 ->
        (N : NNReal) <= A * delta ^ (-B) ->
        spineScaleLoss 3 N sigma <= sourceQSelectionLoss K delta /\
          (spineScaleLoss 3 N sigma : ENNReal) <= sourceFixedPreparationLoss K delta := by
  obtain ⟨K, hK⟩ := source_exists_spineScaleLoss_polylog_envelope A B hA hB
  refine ⟨K, hK.mono ?_⟩
  intro delta hdelta sigma N hd hds hs hcard
  have h := hdelta sigma N hd hds hs hcard
  have heq := (sourceQSelectionLoss_preparation_compatibility K hd (hds.trans hs)).1
  refine ⟨h, ?_⟩
  rw [← heq]
  exact_mod_cast h

/-- The same fixed envelope pays all three actual one-scale calls; their input cardinalities
and radii are arbitrary runtime data satisfying the common polynomial ceiling. -/
theorem source_exists_spineScaleLoss_three_selection_envelope (A : NNReal) (B : Real)
    (hA : 0 < A) (hB : 0 <= B) :
    ∃ K : Nat, ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      forall (sigma : Fin 3 -> NNReal) (N : Fin 3 -> Nat),
        0 < delta -> (forall i, delta <= sigma i /\ sigma i <= 1) ->
        (forall i, (N i : NNReal) <= A * delta ^ (-B)) ->
        (forall i, spineScaleLoss 3 (N i) (sigma i) <= sourceQSelectionLoss K delta) /\
          (∏ i, spineScaleLoss 3 (N i) (sigma i)) <=
            sourceQSelectionLoss (3 * K) delta /\
          ((∏ i, spineScaleLoss 3 (N i) (sigma i) : NNReal) : ENNReal) <=
            sourceFixedPreparationLoss (3 * K) delta := by
  obtain ⟨K, hK⟩ := source_exists_spineScaleLoss_selection_envelope A B hA hB
  refine ⟨K, hK.mono ?_⟩
  intro delta hdelta sigma N hd hs hcard
  have hpoint : ∀ i, spineScaleLoss 3 (N i) (sigma i) <= sourceQSelectionLoss K delta :=
    fun i => (hdelta (sigma i) (N i) hd (hs i).1 (hs i).2 (hcard i)).1
  have hd1 : delta <= 1 := (hs 0).1.trans (hs 0).2
  have hbase : 0 <= 2 + Real.logb 2 (1 / (delta : Real)) := by
    have hlog := Real.logb_nonneg (by norm_num : (1 : Real) < 2)
      (show (1 : Real) <= 1 / (delta : Real) from
        (le_div_iff₀ (NNReal.coe_pos.mpr hd)).mpr
          (by simpa only [one_mul, NNReal.coe_one] using NNReal.coe_le_coe.mpr hd1))
    linarith
  have hpower : sourceQSelectionLoss K delta ^ 3 = sourceQSelectionLoss (3 * K) delta := by
    simp only [sourceQSelectionLoss, Real.toNNReal_pow hbase]
    rw [← pow_mul, Nat.mul_comm]
  have hprod : (∏ i, spineScaleLoss 3 (N i) (sigma i)) <= sourceQSelectionLoss (3 * K) delta := by
    calc
      _ <= ∏ _i : Fin 3, sourceQSelectionLoss K delta :=
        Finset.prod_le_prod' (fun i _ => hpoint i)
      _ = sourceQSelectionLoss K delta ^ 3 := by simp
      _ = _ := hpower
  refine ⟨hpoint, hprod, ?_⟩
  rw [← (sourceQSelectionLoss_preparation_compatibility (3 * K) hd hd1).1]
  exact_mod_cast hprod

end Kakeya.ML2Assembly

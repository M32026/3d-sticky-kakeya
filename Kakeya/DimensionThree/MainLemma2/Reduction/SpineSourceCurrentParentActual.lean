/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceCurrentParentData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The source-facing actual outcome uses current factors and paid histories.
All original-Q profile, final-Q statistics and F/P geometry are retained. -/
structure SourceCurrentParentOutcome (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (N J A0 A1 : Nat) (e : Real) (eta : Nat -> Real)
    (etaParent bias etaF : Real) (K : Nat) (cap : NNReal) (a b : Nat) : Prop where
  retained : SourceParentRetainedState Q Z R Q' Z (sourceFixedPreparationLoss K delta)
  input : SourceFixedTowerInput Q' A0 A1 etaF
  upper : SourceParentUpperWindow Q' A0 A1 N eta e a b J
  alternative :
    (exists k, SourceTowerWindow delta M e a b k /\
      SourceParentFailedConcentration Q R a k e (eta (J + 1)) /\
      Q.assignedPotential (eta 1 * e ^ 2 / 8) R + 1 <=
        Q.assignedPotential (eta 1 * e ^ 2 / 8) S) \/
    (exists B : SourceJointWindowFactors Q' e a b bias,
      Nonempty (SourceCurrentWindowHistory Q Z Q' B K) /\
      SourceParentRetainedConcentration Q' e (eta (J + 1)) a b /\
      (Nonempty (SourceParentEccentric Q' B etaParent) \/
        (exists P : SourceActualParent Q' B etaParent (eta (J + 1)) cap,
          Nonempty (SourceCurrentParentHistory Q Z Q' B P K))))

/-- This common terminal input exposes every current F/P field, with the paid
retained ledger, but does not ask an analytic consumer to reconstruct history. -/
structure SourceParentTerminalGeometry (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (R : Finset iota) (Q' : SourceThreadedTower R T M C)
    (N J A0 A1 : Nat) (e : Real) (eta : Nat -> Real)
    (etaParent bias etaF : Real) (K : Nat) (cap : NNReal) (a b : Nat) : Prop where
  retained : SourceParentRetainedState Q Z R Q' Z (sourceFixedPreparationLoss K delta)
  input : SourceFixedTowerInput Q' A0 A1 etaF
  upper : SourceParentUpperWindow Q' A0 A1 N eta e a b J
  alternative :
    (exists k, SourceTowerWindow delta M e a b k /\
      SourceParentFailedConcentration Q R a k e (eta (J + 1)) /\
      Q.assignedPotential (eta 1 * e ^ 2 / 8) R + 1 <=
        Q.assignedPotential (eta 1 * e ^ 2 / 8) S) \/
    (exists B : SourceJointWindowFactors Q' e a b bias,
      SourceParentRetainedConcentration Q' e (eta (J + 1)) a b /\
      (Nonempty (SourceParentEccentric Q' B etaParent) \/
        Nonempty (SourceActualParent Q' B etaParent (eta (J + 1)) cap)))

/-- The intersection diagram and its paid current-reference capture are genuine
consequences of an actual restriction; final parts need not be historical parts. -/
theorem source_current_historical_pieces
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {F G R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {a m : Nat} {j : iota} {bias : Real}
    (H : SourceImmediateBiasedParent Q Z F G a m j bias)
    (B : SourceParentBiasedFactors Q' a m j bias)
    (hrestriction : SourceTowerRestriction Q Q')
    (hRG : R <= G) (hj : j ∈ Q'.indexSet a) (hbias : 0 < bias) :
    Nonempty (SourceCurrentHistoricalPieces Q Z Q' H B) := by
  classical
  have hnodes : Q'.fibre a m j <= H.actual.selection.selected := by
    rw [hrestriction.full_retained_fibres, ← H.output_nodes]
    exact Finset.image_subset_image (Finset.filter_subset_filter _ hRG)
  have holdUnion : H.actual.selection.parts.biUnion id = H.actual.selection.selected := by
    rw [← Finset.sup_eq_biUnion, ← H.actual.selection.selected_eq]
  have hcurrentUnion := B.partition.biUnion_parts
  have holdMem {i : iota} (hi : i ∈ H.actual.selection.selected) :
      exists old, old ∈ H.actual.selection.parts /\ i ∈ old := by
    rw [← holdUnion] at hi
    exact Finset.mem_biUnion.mp hi
  let payment : ENNReal := (nonempty_biasedFactorization.C 3 bias : ENNReal) *
    ((max B.comparison H.comparison : NNReal) : ENNReal) ^ bias
  have hcomp : 0 < (max B.comparison H.comparison : NNReal) :=
    lt_of_lt_of_le (by norm_num) (B.comparison_one_le.trans (le_max_left _ _))
  have hconstant : 0 < (nonempty_biasedFactorization.C 3 bias : ENNReal) := by
    exact_mod_cast (show 0 < nonempty_biasedFactorization.C 3 bias by
      exact mul_pos (by norm_num) (NNReal.rpow_pos (Metric.volume_comparison.C_pos 3)))
  have hpaypos : 0 < payment := by
    exact ENNReal.mul_pos hconstant.ne'
      (ENNReal.rpow_pos (by exact_mod_cast hcomp) ENNReal.coe_ne_top).ne'
  have hpayfinite : payment < ⊤ := by
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hbias.le ENNReal.coe_ne_top)
  refine ⟨{
    retained_subset := hRG
    current_nodes_subset := hnodes
    current_piece_union := ?_
    historical_piece_union := ?_
    piece_disjoint := ?_
    piece_hull := ?_
    piece_hull_le_current := ?_
    piece_hull_le_historical := ?_
    whole_historical_hull := ?_
    reference_same_parent := by rw [hrestriction.tubes]
    referencePayment := payment
    payment_eq := rfl
    payment_positive := hpaypos
    payment_finite := hpayfinite
    current_capture_paid := ?_ }⟩
  · intro part hpart
    ext i
    constructor
    · intro hi
      obtain ⟨old, hold, hio⟩ := holdMem (hnodes (B.partition.subset hpart hi))
      exact Finset.mem_biUnion.mpr ⟨old, hold, Finset.mem_inter.mpr ⟨hi, hio⟩⟩
    · intro hi
      obtain ⟨old, hold, hio⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_inter.mp hio).1
  · intro old hold
    ext i
    constructor
    · intro hi
      obtain ⟨hio, hic⟩ := Finset.mem_inter.mp hi
      obtain ⟨part, hp, hip⟩ := B.partition.exists_mem hic
      exact Finset.mem_biUnion.mpr ⟨part, hp, Finset.mem_inter.mpr ⟨hip, hio⟩⟩
    · intro hi
      obtain ⟨part, hp, hip⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hip).2,
        B.partition.subset hp (Finset.mem_inter.mp hip).1⟩
  · intro part hpart old hold old' hold' hne
    exact (H.actual.selection.part_disjoint hold hold' hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  · intro part hpart old hold hne
    rw [hrestriction.tubes]
  · intro part hpart old hold hne
    apply (hne.convexHull_biUnion_le_iff _ _).mpr
    intro i hi
    exact Finset.le_convexHull_biUnion (fun i => (Q'.tube m i).toConvexSpaceBody)
      (Finset.mem_inter.mp hi).1
  · intro part hpart old hold hne
    rw [hrestriction.tubes]
    apply (hne.convexHull_biUnion_le_iff _ _).mpr
    intro i hi
    exact Finset.le_convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)
      (Finset.mem_inter.mp hi).2
  · intro old hold hwhole
    rw [hrestriction.tubes]
  · intro part hpart
    have hcoef : payment⁻¹ <= (nonempty_biasedFactorization.C 3 bias : ENNReal)⁻¹ *
        (B.comparison : ENNReal) ^ (-bias) := by
      dsimp only [payment]
      rw [ENNReal.mul_inv (Or.inl hconstant.ne') (Or.inl ENNReal.coe_ne_top), ENNReal.rpow_neg]
      apply mul_le_mul_right
      apply ENNReal.inv_le_inv.mpr
      exact ENNReal.rpow_le_rpow (by exact_mod_cast le_max_left B.comparison H.comparison) hbias.le
    exact (mul_le_mul_left (mul_le_mul_left hcoef _) _).trans (B.capture_paid part hpart)

/-- The displayed immediate-stage mass payments telescope on the original
shading, and the actual subset pays fullness and multiplicity with the same K. -/
theorem source_current_history_payment
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {R : Finset iota} {bias : Real} {K : Nat}
    (H : SourcePaidFactorHistory Q Z R bias K) :
    (∑ i ∈ S, volume (Z i).shade) <=
        sourceFixedPreparationLoss K delta * ∑ i ∈ R, volume (Z i).shade /\
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
        sourceFixedPreparationLoss K delta * ShadedBody.fullness' R (fun i => (Z i).toShadedBody) /\
      ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        sourceFixedPreparationLoss K delta *
          ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) := by
  classical
  have hmass (n : Nat) (hn : n <= H.trace.length) :
      (∑ i ∈ H.trace.state 0, volume (Z i).shade) <=
        (∏ k ∈ Finset.range n, H.trace.stepLoss k) *
          ∑ i ∈ H.trace.state n, volume (Z i).shade := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (∑ i ∈ H.trace.state 0, volume (Z i).shade) <=
            (∏ k ∈ Finset.range n, H.trace.stepLoss k) *
              ∑ i ∈ H.trace.state n, volume (Z i).shade := ih (by omega)
        _ <= (∏ k ∈ Finset.range n, H.trace.stepLoss k) *
              (H.trace.stepLoss n * ∑ i ∈ H.trace.state (n + 1), volume (Z i).shade) :=
          mul_le_mul_left' (H.trace.step_mass n (by omega)) _
        _ = (∏ k ∈ Finset.range (n + 1), H.trace.stepLoss k) *
              ∑ i ∈ H.trace.state (n + 1), volume (Z i).shade := by
          rw [Finset.prod_range_succ, mul_assoc]
  have hpaid : (∑ i ∈ S, volume (Z i).shade) <=
      sourceFixedPreparationLoss K delta * ∑ i ∈ R, volume (Z i).shade := by
    simpa only [H.trace.initial, H.trace.final] using
      (hmass H.trace.length le_rfl).trans (mul_le_mul_right' H.trace.total_loss _)
  have hRS : R <= S := by
    simpa only [H.trace.final] using H.trace.all_subset H.trace.length le_rfl
  refine ⟨hpaid, ?_, ?_⟩
  · exact ShadedBody.fullness'_le_of_subset_of_sum_shade_le S R
      (fun i => (Z i).toShadedBody) hRS hpaid
  · exact ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset S
      (fun i => (Z i).toShadedBody) R (fun i => (Z i).toShadedBody)
      (sourceFixedPreparationLoss K delta)
      (Set.iUnion₂_subset fun i hi => Set.subset_iUnion₂_of_subset i (hRS hi) Set.Subset.rfl)
      hpaid

end Kakeya.ML2Core

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricAssignedSelection

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- A D-parameterized geometric adapter keeps the exact existing factorization
and its constant. The new transverse reading constant is fixed solely by D. -/
theorem source_exists_global_plank_of_D_comparable_factors (D : NNReal) (hD : 1 <= D) :
    exists CD : NNReal, 1 <= CD /\
      forall {iota : Type u} {rho : NNReal} (_hrho : 0 < rho)
        (r : Finset iota) (R : iota -> Tube rho (EuclideanSpace Real (Fin 3)))
        (C0 aw bw cw : NNReal), r.Nonempty -> 0 < aw -> aw <= bw -> bw <= cw ->
      (forall i, i ∈ r -> (R i).carrier <= Metric.closedBall 0 1) ->
      forall F : ConvexSpaceBody.Factorization r (fun i => (R i).toConvexSpaceBody) C0,
      (forall part, part ∈ F.parts -> SourceZeroFactorDimensions D aw bw cw
        (part.convexHull_biUnion (fun i => (R i).toConvexSpaceBody))) ->
      exists (short middle Cw : NNReal) (hsm : short <= middle) (hm1 : middle <= 1),
        rho <= short /\ 1 <= Cw /\ Cw <= CD /\ short / middle <= CD * (aw / bw) /\
        exists Fz : Kakeya.GlobalPlankFactorization Cw short middle hsm hm1 r
            (fun i => (R i).toConvexSpaceBody) C0,
          Fz.toFactorization = F := by
  classical
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨64 * D ^ 2, by nlinarith [sq_nonneg (D - 1)], ?_⟩
  intro iota rho hrho r R C0 aw bw cw hr haw hab hbc hball F hdim
  let V := fun i => (R i).toConvexSpaceBody
  have hpne : forall part, part ∈ F.parts -> part.Nonempty :=
    fun _ hp => F.toFinpartition.nonempty_of_mem_parts hp
  have hpball : forall part, part ∈ F.parts ->
      part.convexHull_biUnion V <=
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) := by
    intro part hp
    apply ((hpne part hp).convexHull_biUnion_le_iff _ _).2
    intro i hi
    change (R i).carrier <= ConvexSpaceBody.closedUnitBall.carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hball i (F.toFinpartition.le hp hi)
  have hpball' : forall part, part ∈ F.parts ->
      (part.convexHull_biUnion V).carrier <= Metric.closedBall 0 1 := by
    intro part hp
    have h : (part.convexHull_biUnion V).carrier <=
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody (EuclideanSpace Real (Fin 3))).carrier :=
      hpball part hp
    simpa only [ConvexSpaceBody.closedUnitBall_carrier] using h
  have hupper : forall part, part ∈ F.parts -> forall n,
      ethickness Real (part.convexHull_biUnion V).carrier n <= 1 := by
    intro part hp n
    simpa using Metric.ethickness_le_of_subset_closedBall (𝕜 := Real) 1 (hpball' part hp) n
  obtain ⟨i0, hi0⟩ := hr
  obtain ⟨part0, hp0, hi0p⟩ := F.toFinpartition.exists_mem hi0
  have hbwD : bw / D <= 1 := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_div hD0.ne', ENNReal.coe_one]
    simpa only [div_eq_mul_inv, mul_comm] using
      (hdim part0 hp0).2.2.1.trans (hupper part0 hp0 1)
  let short : NNReal := min (D * aw) 1
  let middle : NNReal := min (D * bw) 1
  have hsm : short <= middle := min_le_min_right 1 (mul_le_mul_left' hab D)
  have hm1 : middle <= 1 := min_le_right _ _
  have hs1 : short <= 1 := min_le_right _ _
  have hbw : 0 < bw := haw.trans_le hab
  have hmidlower : bw / D <= middle := by
    refine le_min ?_ hbwD
    calc bw / D <= bw / 1 := by gcongr
      _ = bw := div_one _
      _ <= D * bw := by simpa only [one_mul] using mul_le_mul_right' hD bw
  have hmidpos : 0 < middle := (div_pos hbw hD0).trans_le hmidlower
  have hrho_thick : (rho : ENNReal) <=
      ethickness Real (part0.convexHull_biUnion V).carrier 2 := by
    have h := (R i0).le_ethickness_finrank_sub_one
    rw [show Module.finrank Real (EuclideanSpace Real (Fin 3)) - 1 = 2 by simp] at h
    exact h.trans (Metric.ethickness_monotone
      (Finset.le_convexHull_biUnion V hi0p) 2)
  have hrhos : rho <= short := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_min, ENNReal.coe_mul, ENNReal.coe_one]
    exact le_min (hrho_thick.trans (hdim part0 hp0).2.2.2.2.2)
      (hrho_thick.trans (hupper part0 hp0 2))
  have hcost : 1 <= 64 * D ^ 2 := by nlinarith [sq_nonneg (D - 1)]
  have haspect : short / middle <= (64 * D ^ 2) * (aw / bw) := by
    calc short / middle <= (D * aw) / (bw / D) := by
          gcongr
          exact min_le_left _ _
      _ = D ^ 2 * (aw / bw) := by
          rw [div_div_eq_mul_div]
          ring
      _ <= (64 * D ^ 2) * (aw / bw) := by gcongr; nlinarith
  refine ⟨short, middle, 64 * D ^ 2, hsm, hm1, hrhos, hcost, le_rfl, haspect, ?_⟩
  refine ⟨{ toFactorization := F, one_le_Cw := hcost, le_plank := ?_, wide := ?_ }, rfl⟩
  · intro part hp
    have hthin : ethickness Real (part.convexHull_biUnion V).carrier 2 <=
        (1 : NNReal) * (short : ENNReal) := by
      simp only [ENNReal.coe_one, one_mul]
      change _ <= ((min (D * aw) 1 : NNReal) : ENNReal)
      rw [ENNReal.coe_min, ENNReal.coe_mul, ENNReal.coe_one]
      exact le_min (hdim part hp).2.2.2.2.2 (hupper part hp 2)
    have hwide : ethickness Real (part.convexHull_biUnion V).carrier 1 <=
        (1 : NNReal) * (middle : ENNReal) := by
      simp only [ENNReal.coe_one, one_mul]
      change _ <= ((min (D * bw) 1 : NNReal) : ENNReal)
      rw [ENNReal.coe_min, ENNReal.coe_mul, ENNReal.coe_one]
      exact le_min (hdim part hp).2.2.2.1 (hupper part hp 1)
    have hshort : 1 * short <= 1 := by simpa using hs1
    have henv := Kakeya.comparablePlankEnvelope.body_le_bodyPlank
      hsm hshort hwide hthin (hpball part hp)
    let P0 := Kakeya.comparablePlankEnvelope.bodyPlank 1 short middle hsm hshort
      (part.convexHull_biUnion V)
    let P : Plank short middle hsm hm1 :=
      { toPrismNDim := P0.toPrismNDim
        thicknesses_eq := by
          simpa only [Kakeya.comparablePlankEnvelope.bodyThin,
            Kakeya.comparablePlankEnvelope.bodyWide, one_mul, min_eq_left hm1] using
            P0.thicknesses_eq }
    exact ⟨P, henv⟩
  · intro part hp
    obtain ⟨k, hk⟩ := hpne part hp
    have hsub : (R k).carrier <= (part.convexHull_biUnion V).carrier :=
      Finset.le_convexHull_biUnion V hk
    have hxm : (R k).x ∈ (R k).carrier := by
      rw [(R k).carrier_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨(R k).x, left_mem_segment Real _ _, Metric.mem_closedBall_self rho.coe_nonneg⟩
    have hym : (R k).y ∈ (R k).carrier := by
      rw [(R k).carrier_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨(R k).y, right_mem_segment Real _ _, Metric.mem_closedBall_self rho.coe_nonneg⟩
    have hwlow : ((bw / D : NNReal) : ENNReal) <=
        ethickness Real (part.convexHull_biUnion V).carrier 1 := by
      rw [ENNReal.coe_div hD0.ne']
      simpa only [div_eq_mul_inv, mul_comm] using (hdim part hp).2.2.1
    have hdisc := ML2Reduction.containsFlatDisc_of_le_ethickness_one
      (part.convexHull_biUnion V).isConvexSet.convex (hpball' part hp)
      (hsub hxm) (hsub hym) (R k).dist_eq_one (div_pos hbw hD0) hwlow
    apply hdisc.mono
    calc min middle (1 / 2) / (64 * D ^ 2) <= (D * bw) / (64 * D ^ 2) := by
          gcongr
          exact (min_le_left _ _).trans (min_le_left _ _)
      _ = (bw / D) / 64 := by
          apply NNReal.coe_injective
          push_cast
          field_simp

end Kakeya.ML2Core

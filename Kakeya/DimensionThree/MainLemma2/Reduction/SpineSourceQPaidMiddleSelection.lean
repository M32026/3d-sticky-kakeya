/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQMiddleSelection
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceOneScaleThickening
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceScaleLossEnvelope

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Kakeya.ML2Core Kakeya.ML2Reduction Kakeya.VeryNotSticky
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

set_option maxHeartbeats 8000000 in
/-- Auxiliary H0-H5 construction for S:4482-4500,4672-4685, pending exact
source review. Two induced-seed transfers explicitly cost original fullness
inverse squared. All witnesses and complete fibres use the original Q.
The fixed polylog exponent precedes delta, every family, and all indices. -/
theorem sourceQ_exists_paid_mass_coupled_middle (M A0 A1 C : Nat)
    (hM : 2 <= M) (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    (etaC : Real) (heta : 0 < etaC) (heta10 : 5 * etaC < 10) :
    exists K : Nat, 1 <= K /\
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceFixedTowerInput Q A0 A1 etaC -> SourceTowerStatistics Q Z ->
      delta ^ etaC <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
      (forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <=
        volume (Z i).shade) ->
      forall a p b : Nat, a <= p -> p < b -> b <= M ->
      exists X : SourceQMiddleSeam Q Z a p b
          ((sourceQSelectionLoss K delta)⁻¹ *
            ShadedBody.fullness S (fun i => (Z i).toShadedBody))
          (sourceFixedPreparationLoss K delta *
            (ShadedBody.fullness S (fun i => (Z i).toShadedBody) : ENNReal)⁻¹ ^ 2),
        sourceFixedPreparationLoss K delta = (sourceQSelectionLoss K delta : ENNReal) /\
        (X.stageLoss : ENNReal) ^ 3 <= sourceFixedPreparationLoss K delta /\
        delta ^ (5 * etaC) <= (sourceQSelectionLoss K delta)⁻¹ *
          ShadedBody.fullness S (fun i => (Z i).toShadedBody) /\
        0 < X.theta0 Q /\ X.theta0 Q <= 1 /\
        ((sourceQSelectionLoss K delta : Real)⁻¹ <= X.theta0 Q) /\
        (delta : Real) ^ (6 * etaC) <= X.theta0 Q /\
        sourceFixedPreparationLoss K delta *
          (ShadedBody.fullness S (fun i => (Z i).toShadedBody) : ENNReal)⁻¹ ^ 2 <=
            sourceFixedPreparationLoss K delta *
              ENNReal.ofReal ((delta : Real) ^ (-2 * etaC)) := by
  classical
  have hRaw {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
      (Q : SourceThreadedTower S T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (hst : SourceTowerStatistics Q Z) (hdelta : 0 < delta)
      {a p b : Nat} (hap : a <= p) (hpb : p < b) (hb : b <= M)
      (hscales : forall k, k <= M -> delta <= sourceTowerRadius delta M k /\
        sourceTowerRadius delta M k <= 1)
      (hmono : forall k l, k <= l -> l <= M ->
        sourceTowerRadius delta M l <= sourceTowerRadius delta M k)
      (hball : forall k, k <= M -> forall j, j ∈ Q.indexSet k ->
        (Q.tube k j).carrier <= Metric.closedBall 0 1)
      (hZball : forall i, i ∈ S -> (Z i).carrier <= Metric.closedBall 0 1)
      (hfull : 0 < ShadedBody.fullness S (fun i => (Z i).toShadedBody))
      (L H d q : NNReal) (hL1 : 1 <= L) (hd1 : 1 <= d) (hq1 : 1 <= q)
      (hdgeom : Tube.dilateFullness.C 3 <= d)
      (hqgeom : max 1 (Tube.volume_le.C 3 / Tube.le_volume.c 3) <= q)
      (hLfine : spineScaleLoss 3 S.card delta <= L)
      (hLcoarse : forall k, k <= M -> forall J : Finset iota, J <= Q.indexSet k ->
        spineScaleLoss 3 J.card (sourceTowerRadius delta M k) <= L)
      (hH : 1024 * d^3 * q^4 * L^7 <= H) :
      exists X : SourceQMiddleSeam Q Z a p b
        (H⁻¹ * ShadedBody.fullness S (fun i => (Z i).toShadedBody))
        ((H : ENNReal) *
          (ShadedBody.fullness S (fun i => (Z i).toShadedBody) : ENNReal)⁻¹^2),
        (X.stageLoss : ENNReal)^3 <= (H : ENNReal) /\
        (H : Real)⁻¹ <= X.theta0 Q := by
    have hgoodStage {ifine icoarse : Type u} {sigma rho : NNReal}
        (hsigma : 0 < sigma) (hscale : sigma <= rho) (hrho : rho <= 1)
        (s : Finset ifine) (t : Finset icoarse)
        (V : ifine -> ShadedTube sigma (EuclideanSpace Real (Fin 3)))
        (W : icoarse -> Tube rho (EuclideanSpace Real (Fin 3))) (parent : ifine -> icoarse)
        (hball : forall i, i ∈ s -> (V i).carrier <= Metric.closedBall 0 1)
        (hmaps : forall i, i ∈ s -> parent i ∈ t)
        (hcontain : forall i, i ∈ s -> (V i).toConvexSpaceBody <= (W (parent i)).toConvexSpaceBody)
        (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
        exists (t' G : Finset icoarse)
          (Zrho : icoarse -> ShadedTube rho (EuclideanSpace Real (Fin 3)))
          (Z' : ifine -> ShadedTube sigma (EuclideanSpace Real (Fin 3))),
          t' <= t /\ G <= t' /\ G.Nonempty /\
          (forall j, (Zrho j).toTube = W j) /\
          (forall i, (Z' i).toTube = (V i).toTube) /\
          (forall i, (Z' i).shade <= (V i).shade) /\
          (forall i, i ∈ s -> parent i ∈ t' -> (Z' i).shade <= (Zrho (parent i)).shade) /\
          (∑ i ∈ s, volume (V i).shade) <=
            (2 * spineScaleLoss 3 s.card sigma : NNReal) *
              ∑ i ∈ s.filter (fun i => parent i ∈ G), volume (Z' i).shade /\
          (forall j, j ∈ G ->
            (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) *
                (∑ i ∈ s.filter (fun i => parent i = j), volume (V i).carrier) <=
              (2 * spineScaleLoss 3 s.card sigma : NNReal) *
                ∑ i ∈ s.filter (fun i => parent i = j), volume (Z' i).shade) /\
          (forall j, j ∈ t' -> ShadedBody.multiplicity s (fun i => (V i).toShadedBody) <=
            (spineScaleLoss 3 s.card sigma : ENNReal) *
              ShadedBody.multiplicity t' (fun k => (Zrho k).toShadedBody) *
              ShadedBody.multiplicity (s.filter (fun i => parent i = j))
                (fun i => (Z' i).toShadedBody)) /\
          (forall j, j ∈ t' -> forall i, i ∈ s -> parent i = j ->
            (W j).carrier ∩ Metric.cthickening (2 * (rho : Real)) (Z' i).shade <=
              (Zrho j).shade) := by
      have hprune (J : Finset icoarse) (a m : icoarse -> ENNReal)
          {M0 C0 L : ENNReal} (hC0 : C0 ≠ 0) (hCt : C0 ≠ ⊤) (hMt : M0 ≠ ⊤)
          (ha : (∑ i ∈ J, a i) <= C0) (hm : M0 <= L * ∑ i ∈ J, m i) :
          M0 <= 2 * L * ∑ i ∈ J.filter (fun i => M0 * a i <= 2 * L * C0 * m i), m i := by
        let good : icoarse -> Prop := fun i => M0 * a i <= 2 * L * C0 * m i
        have hbad : (2 * L * C0) * (∑ i ∈ J.filter (fun i => ¬ good i), m i) <= M0 * C0 := by
          calc
            (2 * L * C0) * (∑ i ∈ J.filter (fun i => ¬ good i), m i) =
                ∑ i ∈ J.filter (fun i => ¬ good i), 2 * L * C0 * m i := Finset.mul_sum ..
            _ <= ∑ i ∈ J.filter (fun i => ¬ good i), M0 * a i :=
              Finset.sum_le_sum fun i hi => (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
            _ = M0 * ∑ i ∈ J.filter (fun i => ¬ good i), a i := (Finset.mul_sum ..).symm
            _ <= M0 * ∑ i ∈ J, a i :=
              mul_le_mul_right (Finset.sum_le_sum_of_subset (f := a)
                (Finset.filter_subset (fun i => ¬ good i) J)) M0
            _ <= M0 * C0 := mul_le_mul_right ha _
        have hsplit := Finset.sum_filter_add_sum_filter_not J good m
        have hscaled := mul_le_mul_right hm (2 * C0)
        rw [← hsplit] at hscaled
        change M0 <= 2 * L * ∑ i ∈ J.filter good, m i
        apply (ENNReal.mul_le_mul_iff_right hC0 hCt).mp
        apply (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top hCt hMt)).mp
        calc
          C0 * M0 + C0 * M0 = 2 * C0 * M0 := by ring
          _ <= 2 * C0 * (L * (∑ i ∈ J.filter good, m i +
              ∑ i ∈ J.filter (fun i => ¬ good i), m i)) := hscaled
          _ = C0 * (2 * L * ∑ i ∈ J.filter good, m i) +
              (2 * L * C0 * ∑ i ∈ J.filter (fun i => ¬ good i), m i) := by ring
          _ <= C0 * (2 * L * ∑ i ∈ J.filter good, m i) + C0 * M0 :=
            add_le_add_right (hbad.trans_eq (mul_comm _ _)) _
      obtain ⟨t', htt, Zrho, Z', hZrho, hZ', hsub, _hne, _hmassrho, hin, _hfull,
        href, hmult, hthick⟩ := source_exists_spineOneScale_thickening hsigma hscale hrho
          V W parent hball hmaps hcontain
      let L : NNReal := spineScaleLoss 3 s.card sigma
      let M0 : ENNReal := ∑ i ∈ s, volume (V i).shade
      let C0 : ENNReal := ∑ i ∈ s, volume (V i).carrier
      let a : icoarse -> ENNReal := fun j =>
        ∑ i ∈ s.filter (fun i => parent i = j), volume (V i).carrier
      let m : icoarse -> ENNReal := fun j =>
        ∑ i ∈ s.filter (fun i => parent i = j), volume (Z' i).shade
      let G := t'.filter (fun j => M0 * a j <= 2 * (L : ENNReal) * C0 * m j)
      have hG : G <= t' := Finset.filter_subset _ _
      have hC0 : C0 ≠ 0 := by
        exact ne_of_gt (hmass.trans_le (Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset))
      have hCt : C0 ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (V i).toConvexSpaceBody.3.measure_ne_top
      have hMt : M0 ≠ ⊤ := ne_top_of_le_ne_top hCt
        (Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset)
      have hpartition (J : Finset icoarse) (w : ifine -> ENNReal) :
          (∑ j ∈ J, ∑ i ∈ s.filter (fun i => parent i = j), w i) =
            ∑ i ∈ s.filter (fun i => parent i ∈ J), w i := by
        have hf (j : icoarse) (hj : j ∈ J) :
            (s.filter (fun i => parent i ∈ J)).filter (fun i => parent i = j) =
              s.filter (fun i => parent i = j) := by
          ext i
          simp only [Finset.mem_filter]
          exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hj⟩, h.2⟩⟩
        convert Finset.sum_fiberwise_of_maps_to
          (s := s.filter (fun i => parent i ∈ J)) (t := J) (g := parent)
          (fun i hi => (Finset.mem_filter.mp hi).2) w using 1
        exact Finset.sum_congr rfl fun j hj => congrArg (fun I : Finset ifine => ∑ i ∈ I, w i)
          (hf j hj).symm
      have hA : (∑ j ∈ t', a j) <= C0 := by
        change (∑ j ∈ t', ∑ i ∈ s.filter (fun i => parent i = j), volume (V i).carrier) <= C0
        rw [hpartition]
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have hL0 : L ≠ 0 := spineScaleLoss_ne_zero 3 s.card sigma
      have hraw : M0 <= (L : ENNReal) * ∑ j ∈ t', m j := by
        have hr : ((L⁻¹ : NNReal) : ENNReal) * M0 <=
            ∑ i ∈ s.filter (fun i => parent i ∈ t'), volume (Z' i).shade := by simpa [L] using href.2
        rw [ENNReal.coe_inv hL0] at hr
        have hh := (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hL0) ENNReal.coe_ne_top).mp hr
        simpa [m, hpartition] using hh
      have hgood : M0 <= 2 * (L : ENNReal) * ∑ j ∈ G, m j :=
        hprune t' a m hC0 hCt hMt hA hraw
      have hGne : G.Nonempty := by
        by_contra h
        have he := Finset.not_nonempty_iff_eq_empty.mp h
        rw [he, Finset.sum_empty, mul_zero] at hgood
        exact (not_le_of_gt hmass) hgood
      refine ⟨t', G, Zrho, Z', htt, hG, hGne, hZrho, hZ', hsub, hin, ?_, ?_, ?_, hthick⟩
      · simpa [M0, L, m, hpartition] using hgood
      · intro j hj
        have hh : M0 * a j <= 2 * (L : ENNReal) * C0 * m j := (Finset.mem_filter.mp hj).2
        have heq : M0 = (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) * C0 :=
          ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody)
        rw [heq] at hh
        apply (ENNReal.mul_le_mul_iff_right hC0 hCt).mp
        convert hh using 1 <;> simp only [L, a, m, ENNReal.coe_mul, ENNReal.coe_ofNat] <;> ring
      · simpa using hmult
    
    have hseedRef {ifine icoarse : Type u}
        (s : Finset ifine) (V : ifine -> ShadedBody (EuclideanSpace Real (Fin 3)))
        (F J : Finset icoarse) (hF : F <= J)
        (W : icoarse -> ShadedBody (EuclideanSpace Real (Fin 3)))
        (a m : icoarse -> ENNReal) (Ra Rk d r : NNReal)
        (hRa : Ra ≠ 0) (hRk : Rk ≠ 0) (hd : d ≠ 0)
        (hC0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0)
        (ha : forall i, i ∈ J -> forall j, j ∈ J -> a i <= (Ra : ENNReal) * a j)
        (hk : forall i, i ∈ J -> forall j, j ∈ J ->
          volume (W i).carrier <= (Rk : ENNReal) * volume (W j).carrier)
        (hblock : forall i, i ∈ J -> m i * volume (W i).carrier <=
          (d : ENNReal) * volume (W i).shade * a i)
        (hAsum : (∑ i ∈ J, a i) <= ∑ i ∈ s, volume (V i).carrier)
        (hretain : (r : ENNReal) * (∑ i ∈ s, volume (V i).shade) <= ∑ i ∈ F, m i) :
        ShadedBody.IsCRefinement F W J W (r * ShadedBody.fullness s V / (Ra * Rk * d)) := by
      have hCt : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr fun i _ => (V i).toConvexSpaceBody.3.measure_ne_top
      have hcross : (∑ i ∈ F, m i) * (∑ j ∈ J, volume (W j).carrier) <=
          ((Ra * Rk * d : NNReal) : ENNReal) *
            (∑ i ∈ F, volume (W i).shade) * (∑ j ∈ J, a j) := by
        have hpoint (i : icoarse) (hi : i ∈ F) (j : icoarse) (hj : j ∈ J) :
            m i * volume (W j).carrier <=
              (Ra : ENNReal) * Rk * d * volume (W i).shade * a j := by
          calc
            m i * volume (W j).carrier <= m i * ((Rk : ENNReal) * volume (W i).carrier) :=
              mul_le_mul_right (hk j hj i (hF hi)) _
            _ = (Rk : ENNReal) * (m i * volume (W i).carrier) := by ring
            _ <= (Rk : ENNReal) * ((d : ENNReal) * volume (W i).shade * a i) :=
              mul_le_mul_right (hblock i (hF hi)) _
            _ <= (Rk : ENNReal) * ((d : ENNReal) * volume (W i).shade * ((Ra : ENNReal) * a j)) :=
              mul_le_mul_right (mul_le_mul_right (ha i (hF hi) j hj) _) _
            _ = (Ra : ENNReal) * Rk * d * volume (W i).shade * a j := by ring
        calc
          (∑ i ∈ F, m i) * (∑ j ∈ J, volume (W j).carrier) =
              ∑ i ∈ F, ∑ j ∈ J, m i * volume (W j).carrier := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
          _ <= ∑ i ∈ F, ∑ j ∈ J, (Ra : ENNReal) * Rk * d * volume (W i).shade * a j :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpoint i hi j hj
          _ = ((Ra * Rk * d : NNReal) : ENNReal) *
              (∑ i ∈ F, volume (W i).shade) * (∑ j ∈ J, a j) := by
            simp only [ENNReal.coe_mul]
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
            rw [← Finset.mul_sum]
      have hseed : (r : ENNReal) * ShadedBody.fullness s V * (∑ j ∈ J, volume (W j).shade) <=
          ((Ra * Rk * d : NNReal) : ENNReal) * (∑ i ∈ F, volume (W i).shade) := by
        have hbound : ((r : ENNReal) * ShadedBody.fullness s V *
            (∑ j ∈ J, volume (W j).carrier)) * (∑ i ∈ s, volume (V i).carrier) <=
            (((Ra * Rk * d : NNReal) : ENNReal) * (∑ i ∈ F, volume (W i).shade)) *
              (∑ i ∈ s, volume (V i).carrier) := by
          calc
            _ = (r : ENNReal) * (∑ i ∈ s, volume (V i).shade) *
                (∑ j ∈ J, volume (W j).carrier) := by
              rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul s V]
              ring
            _ <= (∑ i ∈ F, m i) * (∑ j ∈ J, volume (W j).carrier) := mul_le_mul_left hretain _
            _ <= ((Ra * Rk * d : NNReal) : ENNReal) *
                (∑ i ∈ F, volume (W i).shade) * (∑ j ∈ J, a j) := hcross
            _ <= _ := mul_le_mul_right hAsum _
        exact (mul_le_mul_right
          (Finset.sum_le_sum fun i _ => measure_mono (W i).shade_subset) _).trans
          ((ENNReal.mul_le_mul_iff_left hC0 hCt).mp hbound)
      refine ⟨⟨hF, fun _ _ => ⟨rfl, Set.Subset.rfl⟩⟩, ?_⟩
      have hD : Ra * Rk * d ≠ 0 := mul_ne_zero (mul_ne_zero hRa hRk) hd
      rw [ENNReal.coe_div hD, ENNReal.coe_mul]
      have hh := (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hD) ENNReal.coe_ne_top).mpr hseed
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
    
    have hgeomBlock {iota : Type u} {sigma rho : NNReal} (hsigma : 0 < sigma)
        (hscale : sigma <= rho) (hrho : rho <= 1) (s : Finset iota)
        (V : iota -> ShadedTube sigma (EuclideanSpace Real (Fin 3)))
        (W : Tube rho (EuclideanSpace Real (Fin 3)))
        (O : Set (EuclideanSpace Real (Fin 3)))
        (hcontain : forall i, i ∈ s -> (V i).carrier <= W.carrier)
        (hthick : forall i, i ∈ s ->
          W.carrier ∩ Metric.cthickening (2 * (rho : Real)) (V i).shade <= O) :
        (∑ i ∈ s, volume (V i).shade) * volume W.carrier <=
          (Tube.dilateFullness.C 3 : ENNReal) * volume O * (∑ i ∈ s, volume (V i).carrier) := by
      have hW : (Tube.dilate W 1).carrier = W.carrier :=
        congrArg (fun B : ConvexSpaceBody (EuclideanSpace Real (Fin 3)) => B.carrier)
          (Tube.dilate_one W)
      have hpoint (i : iota) (hi : i ∈ s) :
          (volume (V i).shade / volume (V i).carrier) * volume W.carrier <=
            (Tube.dilateFullness.C 3 : ENNReal) * volume O := by
        have hv := Tube.volume_dilate_inter_cthickening_ge hsigma hscale hrho
          (le_refl (1 : Real)) (V i).toTube W
          (by rw [hW]; exact hcontain i hi) (V i).shade_subset
        have hv' : (volume (V i).shade / volume (V i).carrier) * volume W.carrier <=
            (Tube.dilateFullness.C 3 : ENNReal) *
              volume (W.carrier ∩ Metric.cthickening (2 * (rho : Real)) (V i).shade) := by
          simpa [hW] using hv
        exact hv'.trans (mul_le_mul_right (measure_mono (hthick i hi)) _)
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hvol0 : volume (V i).carrier ≠ 0 := by
        have hc := Tube.le_volume.c_pos 3
        have hv : (Tube.le_volume.c 3 : ENNReal) * (sigma : ENNReal)^2 <=
            volume (V i).carrier := by simpa using Tube.le_volume (V i).toTube
        exact ne_of_gt ((by positivity :
          0 < (Tube.le_volume.c 3 : ENNReal) * (sigma : ENNReal)^2).trans_le hv)
      have hvoltop : volume (V i).carrier ≠ ⊤ := (V i).toConvexSpaceBody.3.measure_ne_top
      calc
        volume (V i).shade * volume W.carrier =
            volume (V i).carrier * ((volume (V i).shade / volume (V i).carrier) * volume W.carrier) := by
          rw [← mul_assoc, mul_comm (volume (V i).carrier) (volume (V i).shade / volume (V i).carrier),
            ENNReal.div_mul_cancel hvol0 hvoltop]
        _ <= volume (V i).carrier * ((Tube.dilateFullness.C 3 : ENNReal) * volume O) :=
          mul_le_mul_right (hpoint i hi) _
        _ = (Tube.dilateFullness.C 3 : ENNReal) * volume O * volume (V i).carrier := by ring
    
    have hcarrierComp {iota : Type u} {sigma : NNReal} (hsigma : sigma <= 1)
        (F G : Finset iota) (V : iota -> Tube sigma (EuclideanSpace Real (Fin 3)))
        (C : NNReal) (hcard : (F.card : ENNReal) <= C * (G.card : ENNReal)) :
        (∑ i ∈ F, volume (V i).carrier) <=
          (C * max 1 (Tube.volume_le.C 3 / Tube.le_volume.c 3) : NNReal) *
            (∑ i ∈ G, volume (V i).carrier) := by
      let q : NNReal := max 1 (Tube.volume_le.C 3 / Tube.le_volume.c 3)
      have hq : Tube.volume_le.C 3 <= q * Tube.le_volume.c 3 :=
        (div_le_iff₀ (Tube.le_volume.c_pos 3)).mp (le_max_right _ _)
      calc
        (∑ i ∈ F, volume (V i).carrier) <=
            (F.card : ENNReal) * ((Tube.volume_le.C 3 : ENNReal) * (sigma : ENNReal)^2) := by
          simpa only [Finset.sum_const, nsmul_eq_mul] using
            Finset.sum_le_sum (fun i (_hi : i ∈ F) =>
              show volume (V i).carrier <= (Tube.volume_le.C 3 : ENNReal) * (sigma : ENNReal)^2
                from by simpa using Tube.volume_le hsigma (V i))
        _ <= ((C : ENNReal) * (G.card : ENNReal)) *
            ((q : ENNReal) * Tube.le_volume.c 3 * (sigma : ENNReal)^2) := by
          exact mul_le_mul' hcard (mul_le_mul_left (by exact_mod_cast hq) _)
        _ = ((C * q : NNReal) : ENNReal) *
            ((G.card : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * (sigma : ENNReal)^2)) := by
          push_cast
          ring
        _ <= ((C * q : NNReal) : ENNReal) * (∑ i ∈ G, volume (V i).carrier) := by
          apply mul_le_mul_right
          simpa only [Finset.sum_const, nsmul_eq_mul] using
            Finset.sum_le_sum (fun i (_hi : i ∈ G) =>
              show (Tube.le_volume.c 3 : ENNReal) * (sigma : ENNReal)^2 <= volume (V i).carrier
                from by simpa using Tube.le_volume (V i))
    
    have hshadeComp {iota : Type u} (J : Finset iota) (u : iota -> ENNReal)
        (hpair : forall i, i ∈ J -> forall j, j ∈ J -> u i <= 2 * u j)
        (j : iota) (hj : j ∈ J) :
        u j <= 2 * (∑ i ∈ J, u i) / (J.card : ENNReal) := by
      have hN0 : (J.card : ENNReal) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr ⟨j, hj⟩).ne'
      apply (ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl (by simp))).mpr
      calc
        u j * (J.card : ENNReal) = ∑ _i ∈ J, u j := by simp [mul_comm]
        _ <= ∑ i ∈ J, 2 * u i := Finset.sum_le_sum fun i hi => hpair j hj i hi
        _ = 2 * (∑ i ∈ J, u i) := (Finset.mul_sum ..).symm
    
    have hcountDense {N N' B B' gamma : NNReal} (hg : 0 < gamma)
        (hB : B <= N) (hN : N <= 2 * N') (hB' : gamma * N' <= B') :
        B <= (2 / gamma) * B' := by
      apply (mul_le_mul_iff_right₀ hg).mp
      calc
        gamma * B <= gamma * N := mul_le_mul_right hB _
        _ <= gamma * (2 * N') := mul_le_mul_right hN _
        _ = 2 * (gamma * N') := by ring
        _ <= 2 * B' := mul_le_mul_right hB' _
        _ = gamma * ((2 / gamma) * B') := by field_simp
    
    have hsparseCount {iota kappa : Type u} (B G : Finset iota) (P : Finset kappa)
        (parent : iota -> kappa) (hG : G <= B)
        (hmaps : forall i, i ∈ B -> parent i ∈ P) (gamma : NNReal) :
        let dense := P.filter (fun j => gamma * ((B.filter (fun i => parent i = j)).card : NNReal) <=
          ((G.filter (fun i => parent i = j)).card : NNReal))
        ((G.filter (fun i => parent i ∉ dense)).card : NNReal) <= gamma * (B.card : NNReal) := by
      intro dense
      let bad := G.filter (fun i => parent i ∉ dense)
      have hbadmaps : forall i, i ∈ bad -> parent i ∈ P :=
        fun i hi => hmaps i (hG (Finset.mem_filter.mp hi).1)
      have hsumBad : (∑ j ∈ P, ((bad.filter (fun i => parent i = j)).card : NNReal)) =
          (bad.card : NNReal) := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          Finset.sum_fiberwise_of_maps_to hbadmaps (fun _ => (1 : NNReal))
      have hsumB : (∑ j ∈ P, ((B.filter (fun i => parent i = j)).card : NNReal)) =
          (B.card : NNReal) := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : NNReal))
      have hpoint (j : kappa) (hj : j ∈ P) :
          ((bad.filter (fun i => parent i = j)).card : NNReal) <=
            gamma * ((B.filter (fun i => parent i = j)).card : NNReal) := by
        by_cases hd : j ∈ dense
        · have he : bad.filter (fun i => parent i = j) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro i hi
            obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
            exact (Finset.mem_filter.mp hi).2 (he ▸ hd)
          simp only [he, Finset.card_empty, Nat.cast_zero]
          positivity
        · have hnot : ¬ gamma * ((B.filter (fun i => parent i = j)).card : NNReal) <=
              ((G.filter (fun i => parent i = j)).card : NNReal) := by
            intro h
            exact hd (Finset.mem_filter.mpr ⟨hj, h⟩)
          have hsub : bad.filter (fun i => parent i = j) <= G.filter (fun i => parent i = j) := by
            intro i hi
            obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, he⟩
          exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (lt_of_not_ge hnot).le
      change (bad.card : NNReal) <= gamma * (B.card : NNReal)
      rw [← hsumBad, ← hsumB, Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    
    have hsparseMass {iota : Type u} (G B : Finset iota) (w : iota -> NNReal)
        (hG : G <= B) {gamma M N : NNReal} (hN : 0 < N)
        (hc : (G.card : NNReal) <= gamma * N)
        (hw : forall i, i ∈ B -> w i <= 2 * M / N) :
        (∑ i ∈ G, w i) <= 2 * gamma * M := by
      calc
        (∑ i ∈ G, w i) <= ∑ _i ∈ G, 2 * M / N :=
          Finset.sum_le_sum fun i hi => hw i (hG hi)
        _ = (G.card : NNReal) * (2 * M / N) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ <= (gamma * N) * (2 * M / N) := mul_le_mul_left hc _
        _ = 2 * gamma * M := by field_simp
    
    have hsparseMassE (G B : Finset iota) (w : iota -> ENNReal)
        (hG : G <= B) {gamma M0 N : ENNReal} (hN0 : N ≠ 0) (hNt : N ≠ ⊤)
        (hc : (G.card : ENNReal) <= gamma * N)
        (hw : forall i, i ∈ B -> w i <= 2 * M0 / N) :
        (∑ i ∈ G, w i) <= 2 * gamma * M0 := by
      calc
        (∑ i ∈ G, w i) <= ∑ _i ∈ G, 2 * M0 / N :=
          Finset.sum_le_sum fun i hi => hw i (hG hi)
        _ = (G.card : ENNReal) * (2 * M0 / N) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ <= (gamma * N) * (2 * M0 / N) := mul_le_mul_left hc _
        _ = gamma * (2 * M0 / N * N) := by ring
        _ = 2 * gamma * M0 := by rw [ENNReal.div_mul_cancel hN0 hNt]; ring
    have hpartition (J : Finset iota) (f : iota -> iota) (w : iota -> ENNReal) :
        (∑ j ∈ J, ∑ i ∈ S.filter (fun i => f i = j), w i) =
          ∑ i ∈ S.filter (fun i => f i ∈ J), w i := by
      have hf (j : iota) (hj : j ∈ J) :
          (S.filter (fun i => f i ∈ J)).filter (fun i => f i = j) =
            S.filter (fun i => f i = j) := by
        ext i
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hj⟩, h.2⟩⟩
      convert Finset.sum_fiberwise_of_maps_to
        (s := S.filter (fun i => f i ∈ J)) (t := J) (g := f)
        (fun i hi => (Finset.mem_filter.mp hi).2) w using 1
      exact Finset.sum_congr rfl fun j hj => congrArg (fun I : Finset iota => ∑ i ∈ I, w i)
        (hf j hj).symm
    let lam := ShadedBody.fullness S (fun i => (Z i).toShadedBody)
    let M0 : ENNReal := ∑ i ∈ S, volume (Z i).shade
    have hM0 : 0 < M0 := pos_iff_ne_zero.mpr
      (ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos S (fun i => (Z i).toShadedBody) hfull)
    have hMtop : M0 ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ =>
      ne_top_of_le_ne_top (Z i).toConvexSpaceBody.3.measure_ne_top
        (measure_mono (Z i).shade_subset)
    have hL0 : L ≠ 0 := ne_of_gt (zero_lt_one.trans_le hL1)
    have hd0 : d ≠ 0 := ne_of_gt (zero_lt_one.trans_le hd1)
    have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq1)
    have hpM : p <= M := (le_of_lt hpb).trans hb
    have haM : a <= M := hap.trans hpM
    have hbt : forall i, i ∈ S ->
        (Z i).toConvexSpaceBody <= (Q.tube b (Q.place b i)).toConvexSpaceBody := by
      intro i hi
      rw [show (Z i).toConvexSpaceBody = (T i).toConvexSpaceBody from
        congrArg (fun U : Tube delta (EuclideanSpace Real (Fin 3)) => U.toConvexSpaceBody)
          (hst.same_tubes i)]
      exact Q.leaf_containment b hb i hi
    obtain ⟨B1, Gb, Yb0, Z1, hB1, hGbB1, hGbne, hYb0, hZ1, hZ1sub,
      hZ1in, hGbmass0, hGbfull0, hmult1, hthick1⟩ :=
      hgoodStage hdelta (hscales b hb).1 (hscales b hb).2 S (Q.indexSet b)
        Z (Q.tube b) (Q.place b) hZball (Q.place_mem b hb) hbt hM0
    have hGbQ : Gb <= Q.indexSet b := hGbB1.trans hB1
    let g := sourceQAncestor Q p b
    have hanc := sourceQ_ancestor_fibre_identities Q (le_of_lt hpb) hb
    have hgmap : forall j, j ∈ Q.indexSet b -> g j ∈ Q.indexSet p := hanc.2.1
    let gamma : NNReal := (16 * L)⁻¹
    have hgamma0 : 0 < gamma := by dsimp [gamma]; positivity
    let Pdense := (Q.indexSet p).filter (fun j =>
      gamma * (((Q.indexSet b).filter (fun i => g i = j)).card : NNReal) <=
        ((Gb.filter (fun i => g i = j)).card : NNReal))
    let B := Gb.filter (fun j => g j ∈ Pdense)
    let Bbad := Gb.filter (fun j => g j ∉ Pdense)
    let mf : iota -> ENNReal := fun j => ∑ i ∈ Q.cell b j, volume (Z1 i).shade
    let uf : iota -> ENNReal := fun j => ∑ i ∈ Q.cell b j, volume (Z i).shade
    let af : iota -> ENNReal := fun j => ∑ i ∈ Q.cell b j, volume (Z i).carrier
    have hBGb : B <= Gb := Finset.filter_subset _ _
    have hBQ : B <= Q.indexSet b := hBGb.trans hGbQ
    have hBB1 : B <= B1 := hBGb.trans hGbB1
    have hN0 : ((Q.indexSet b).card : ENNReal) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (hGbne.mono hGbQ)).ne'
    have hsumuf : (∑ j ∈ Q.indexSet b, uf j) = M0 := by
      exact Finset.sum_fiberwise_of_maps_to (Q.place_mem b hb) (fun i => volume (Z i).shade)
    have hufupper (j : iota) (hj : j ∈ Q.indexSet b) :
        mf j <= 2 * M0 / ((Q.indexSet b).card : ENNReal) := by
      have hmfu : mf j <= uf j := Finset.sum_le_sum fun i _ => measure_mono (hZ1sub i)
      have hu := hshadeComp (Q.indexSet b) uf (hst.fibre_mass b hb) j hj
      rw [hsumuf] at hu
      exact hmfu.trans hu
    have hbadcard : (Bbad.card : ENNReal) <= (gamma : ENNReal) * ((Q.indexSet b).card : ENNReal) := by
      exact_mod_cast hsparseCount (Q.indexSet b) Gb (Q.indexSet p) g hGbQ hgmap gamma
    have hbadmass : (∑ j ∈ Bbad, mf j) <= 2 * (gamma : ENNReal) * M0 :=
      hsparseMassE Bbad (Q.indexSet b) mf ((Finset.filter_subset _ _).trans hGbQ)
        hN0 (by simp) hbadcard hufupper
    have hGbmass : M0 <= (2 * L : NNReal) * ∑ j ∈ Gb, mf j := by
      have hpart := hpartition Gb (Q.place b) (fun i => volume (Z1 i).shade)
      change (∑ j ∈ Gb, mf j) = _ at hpart
      rw [hpart]
      exact hGbmass0.trans (mul_le_mul_left (by exact_mod_cast (mul_le_mul_right hLfine 2)) _)
    have hsplit : (∑ j ∈ B, mf j) + (∑ j ∈ Bbad, mf j) = ∑ j ∈ Gb, mf j :=
      Finset.sum_filter_add_sum_filter_not Gb (fun j => g j ∈ Pdense) mf
    have hpay : ((4 * L : NNReal) : ENNReal) * (2 * (gamma : ENNReal)) <= 1 := by
      have hh : (4 * L) * (2 * gamma) <= (1 : NNReal) := by
        dsimp [gamma]
        field_simp
        norm_num
      exact_mod_cast hh
    have hbadpaid : ((4 * L : NNReal) : ENNReal) * (∑ j ∈ Bbad, mf j) <= M0 := by
      calc
        _ <= ((4 * L : NNReal) : ENNReal) * (2 * (gamma : ENNReal) * M0) :=
          mul_le_mul_right hbadmass _
        _ = (((4 * L : NNReal) : ENNReal) * (2 * (gamma : ENNReal))) * M0 := by ring
        _ <= 1 * M0 := mul_le_mul_left hpay _
        _ = M0 := one_mul _
    have hBmass : M0 <= ((4 * L : NNReal) : ENNReal) * ∑ j ∈ B, mf j := by
      apply (ENNReal.add_le_add_iff_right hMtop).mp
      calc
        M0 + M0 = 2 * M0 := by ring
        _ <= 2 * (((2 * L : NNReal) : ENNReal) * ∑ j ∈ Gb, mf j) := mul_le_mul_right hGbmass 2
        _ = ((4 * L : NNReal) : ENNReal) * (∑ j ∈ B, mf j) +
            ((4 * L : NNReal) : ENNReal) * (∑ j ∈ Bbad, mf j) := by rw [← hsplit]; push_cast; ring
        _ <= ((4 * L : NNReal) : ENNReal) * (∑ j ∈ B, mf j) + M0 :=
          add_le_add_right hbadpaid _
    have hBne : B.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [he, Finset.sum_empty, mul_zero] at hBmass
      exact (not_le_of_gt hM0) hBmass
    have hBfull (j : iota) (hj : j ∈ B) :
        (lam : ENNReal) * af j <= ((2 * L : NNReal) : ENNReal) * mf j :=
      (hGbfull0 j (hBGb hj)).trans (mul_le_mul_left (by exact_mod_cast
        (mul_le_mul_right hLfine 2)) _)
    have hcellne (k : Nat) (hk : k <= M) (j : iota) (hj : j ∈ Q.indexSet k) :
        (Q.cell k j).Nonempty := by
      obtain ⟨i, hi, he⟩ := Q.place_surjective k hk j hj
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩
    have hZ1carrier (i : iota) : (Z1 i).carrier = (Z i).carrier :=
      congrArg (fun U : Tube delta (EuclideanSpace Real (Fin 3)) => U.carrier) (hZ1 i)
    have hYb0carrier (j : iota) : (Yb0 j).carrier = (Q.tube b j).carrier :=
      congrArg (fun U : Tube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)) =>
        U.carrier) (hYb0 j)
    have hblock1 (j : iota) (hj : j ∈ B1) :
        mf j * volume (Yb0 j).carrier <= (d : ENNReal) * volume (Yb0 j).shade * af j := by
      have hh := hgeomBlock hdelta (hscales b hb).1 (hscales b hb).2 (Q.cell b j)
        Z1 (Q.tube b j) (Yb0 j).shade (fun i hi => by
          obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
          rw [hZ1carrier i]
          have hsub := hbt i hi
          rw [he] at hsub
          exact hsub) (fun i hi => by
            obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
            exact hthick1 j hj i hi he)
      have hcar : (∑ i ∈ Q.cell b j, volume (Z1 i).carrier) = af j :=
        Finset.sum_congr rfl fun i _ => congrArg volume (hZ1carrier i)
      rw [hcar, ← hYb0carrier j] at hh
      exact hh.trans (mul_le_mul_left (mul_le_mul_left (ENNReal.coe_le_coe.mpr hdgeom) _) _)
    have hcoarsePoint {lam0 A m0 K o : ENNReal} (hA0 : A ≠ 0) (hAt : A ≠ ⊤)
        (hden : lam0 * A <= ((2 * L : NNReal) : ENNReal) * m0)
        (hblk : m0 * K <= (d : ENNReal) * o * A) :
        lam0 * K <= ((2 * L * d : NNReal) : ENNReal) * o := by
      apply (ENNReal.mul_le_mul_iff_left hA0 hAt).mp
      calc
        (lam0 * K) * A = (lam0 * A) * K := by ring
        _ <= (((2 * L : NNReal) : ENNReal) * m0) * K := mul_le_mul_left hden _
        _ = ((2 * L : NNReal) : ENNReal) * (m0 * K) := by ring
        _ <= ((2 * L : NNReal) : ENNReal) * ((d : ENNReal) * o * A) := mul_le_mul_right hblk _
        _ = (((2 * L * d : NNReal) : ENNReal) * o) * A := by push_cast; ring
    have hBseedPoint (j : iota) (hj : j ∈ B) :
        (lam : ENNReal) * volume (Yb0 j).carrier <=
          ((2 * L * d : NNReal) : ENNReal) * volume (Yb0 j).shade := by
      obtain ⟨hAj0, hAjt⟩ := StickyKakeya.sum_volume_carrier_pos_ne_top hdelta
        (Q.cell b j) Z (hcellne b hb j (hBQ hj))
      exact hcoarsePoint hAj0.ne' hAjt (hBfull j hj) (hblock1 j (hBB1 hj))
    have hrhob : 0 < sourceTowerRadius delta M b := hdelta.trans_le (hscales b hb).1
    have hrhop : 0 < sourceTowerRadius delta M p := hdelta.trans_le (hscales p hpM).1
    have hrhoa : 0 < sourceTowerRadius delta M a := hdelta.trans_le (hscales a haM).1
    obtain ⟨hBcar0, hBcart⟩ := StickyKakeya.sum_volume_carrier_pos_ne_top hrhob B Yb0 hBne
    let lamB := ShadedBody.fullness B (fun j => (Yb0 j).toShadedBody)
    have h2Ld0 : 2 * L * d ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hL0) hd0
    have hlamB : lam / (2 * L * d) <= lamB := by
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_div h2Ld0]
      exact ShadedBody.le_fullness_of_forall_mul_volume_carrier_le
        (ENNReal.coe_ne_zero.mpr h2Ld0) ENNReal.coe_ne_top hBcar0.ne' hBcart hBseedPoint
    have hlamB0 : 0 < lamB := (div_pos hfull (pos_iff_ne_zero.mpr h2Ld0)).trans_le hlamB
    have hBseedmass : 0 < ∑ j ∈ B, volume (Yb0 j).shade := pos_iff_ne_zero.mpr
      (ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos B
        (fun j => (Yb0 j).toShadedBody) hlamB0)
    have hBball (j : iota) (hj : j ∈ B) : (Yb0 j).carrier <= Metric.closedBall 0 1 := by
      rw [hYb0carrier j]
      exact hball b hb j (hBQ hj)
    have hBmap (j : iota) (hj : j ∈ B) : g j ∈ Pdense := (Finset.mem_filter.mp hj).2
    have hBcontain (j : iota) (hj : j ∈ B) :
        (Yb0 j).toConvexSpaceBody <= (Q.tube p (g j)).toConvexSpaceBody := by
      change (Yb0 j).carrier <= (Q.tube p (g j)).carrier
      rw [hYb0carrier j]
      exact hanc.2.2.1 j (hBQ hj)
    obtain ⟨P1, P, Yp0, Yb, hP1, hPP1, hPne, hYp0, hYb, hYbsub,
      hYbin, hPmass0, hPfull0, hmult2, hthick2⟩ :=
      hgoodStage hrhob (hmono p b (le_of_lt hpb) hb) (hscales p hpM).2 B Pdense
        Yb0 (Q.tube p) g hBball hBmap hBcontain hBseedmass
    have hPQ : P <= Q.indexSet p := hPP1.trans (hP1.trans (Finset.filter_subset _ _))
    have hPPdense : P <= Pdense := hPP1.trans hP1
    have hLmiddle : spineScaleLoss 3 B.card (sourceTowerRadius delta M b) <= L :=
      hLcoarse b hb B hBQ
    let mp : iota -> ENNReal := fun j => ∑ i ∈ B.filter (fun i => g i = j), volume (Yb i).shade
    let ap : iota -> ENNReal := fun j => ∑ i ∈ B.filter (fun i => g i = j), volume (Yb0 i).carrier
    have hPfull (j : iota) (hj : j ∈ P) :
        (lamB : ENNReal) * ap j <= ((2 * L : NNReal) : ENNReal) * mp j :=
      (hPfull0 j hj).trans (mul_le_mul_left (by exact_mod_cast
        (mul_le_mul_right hLmiddle 2)) _)
    have hBfibre (j : iota) (hj : j ∈ Pdense) :
        B.filter (fun i => g i = j) = Gb.filter (fun i => g i = j) := by
      ext i
      simp only [B, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hj⟩, h.2⟩⟩
    have hBfibrene (j : iota) (hj : j ∈ Pdense) :
        (B.filter (fun i => g i = j)).Nonempty := by
      have hjQ := (Finset.mem_filter.mp hj).1
      have hne : (Q.fibre p b j).Nonempty := (hcellne p hpM j hjQ).image (Q.place b)
      have hNpos : (0 : NNReal) < (((Q.indexSet b).filter (fun i => g i = j)).card : NNReal) := by
        rw [← hanc.2.2.2 j hjQ]
        exact_mod_cast Finset.card_pos.mpr hne
      have hpos : (0 : NNReal) < ((Gb.filter (fun i => g i = j)).card : NNReal) :=
        (mul_pos hgamma0 hNpos).trans_le (Finset.mem_filter.mp hj).2
      rw [hBfibre j hj]
      exact Finset.card_pos.mp (by exact_mod_cast hpos)
    have hYbcarrier (j : iota) : (Yb j).carrier = (Yb0 j).carrier :=
      congrArg (fun U : Tube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)) =>
        U.carrier) (hYb j)
    have hYp0carrier (j : iota) : (Yp0 j).carrier = (Q.tube p j).carrier :=
      congrArg (fun U : Tube (sourceTowerRadius delta M p) (EuclideanSpace Real (Fin 3)) =>
        U.carrier) (hYp0 j)
    have hblock2 (j : iota) (hj : j ∈ P1) :
        mp j * volume (Yp0 j).carrier <= (d : ENNReal) * volume (Yp0 j).shade * ap j := by
      have hh := hgeomBlock hrhob (hmono p b (le_of_lt hpb) hb) (hscales p hpM).2
        (B.filter (fun i => g i = j)) Yb (Q.tube p j) (Yp0 j).shade (fun i hi => by
          obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
          rw [hYbcarrier i]
          have hsub := hBcontain i hi
          rw [he] at hsub
          exact hsub) (fun i hi => by
            obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
            exact hthick2 j hj i hi he)
      have hcar : (∑ i ∈ B.filter (fun i => g i = j), volume (Yb i).carrier) = ap j :=
        Finset.sum_congr rfl fun i _ => congrArg volume (hYbcarrier i)
      rw [hcar, ← hYp0carrier j] at hh
      exact hh.trans (mul_le_mul_left (mul_le_mul_left (ENNReal.coe_le_coe.mpr hdgeom) _) _)
    have hPseedPoint (j : iota) (hj : j ∈ P) :
        (lamB : ENNReal) * volume (Yp0 j).carrier <=
          ((2 * L * d : NNReal) : ENNReal) * volume (Yp0 j).shade := by
      obtain ⟨hAj0, hAjt⟩ := StickyKakeya.sum_volume_carrier_pos_ne_top hrhob
        (B.filter (fun i => g i = j)) Yb0 (hBfibrene j (hPPdense hj))
      exact hcoarsePoint hAj0.ne' hAjt (hPfull j hj) (hblock2 j (hPP1 hj))
    obtain ⟨hPcar0, hPcart⟩ := StickyKakeya.sum_volume_carrier_pos_ne_top hrhop P Yp0 hPne
    let lamP := ShadedBody.fullness P (fun j => (Yp0 j).toShadedBody)
    have hlamP : lamB / (2 * L * d) <= lamP := by
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_div h2Ld0]
      exact ShadedBody.le_fullness_of_forall_mul_volume_carrier_le
        (ENNReal.coe_ne_zero.mpr h2Ld0) ENNReal.coe_ne_top hPcar0.ne' hPcart hPseedPoint
    have hlamP0 : 0 < lamP := (div_pos hlamB0 (pos_iff_ne_zero.mpr h2Ld0)).trans_le hlamP
    have hPseedmass : 0 < ∑ j ∈ P, volume (Yp0 j).shade := pos_iff_ne_zero.mpr
      (ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos P
        (fun j => (Yp0 j).toShadedBody) hlamP0)
    let h := sourceQAncestor Q a p
    have hancAP := sourceQ_ancestor_fibre_identities Q hap hpM
    have hPball (j : iota) (hj : j ∈ P) : (Yp0 j).carrier <= Metric.closedBall 0 1 := by
      rw [hYp0carrier j]
      exact hball p hpM j (hPQ hj)
    have hPmap (j : iota) (hj : j ∈ P) : h j ∈ Q.indexSet a := hancAP.2.1 j (hPQ hj)
    have hPcontain (j : iota) (hj : j ∈ P) :
        (Yp0 j).toConvexSpaceBody <= (Q.tube a (h j)).toConvexSpaceBody := by
      change (Yp0 j).carrier <= (Q.tube a (h j)).carrier
      rw [hYp0carrier j]
      exact hancAP.2.2.1 j (hPQ hj)
    obtain ⟨A, hAQ, Ya, Yp, hYa, hYp, hYpsub, hAne0, _hAmass, hYpin,
      hAfull0, href3, hmult3, _hthick3⟩ :=
      source_exists_spineOneScale_thickening hrhop (hmono a p hap hpM) (hscales a haM).2
        Yp0 (Q.tube a) h hPball hPmap hPcontain
    have hAne : A.Nonempty := hAne0 hPseedmass
    have hLparent : spineScaleLoss 3 P.card (sourceTowerRadius delta M p) <= L :=
      hLcoarse p hpM P hPQ
    have hinvL3 : L⁻¹ <= (spineScaleLoss 3 P.card (sourceTowerRadius delta M p))⁻¹ :=
      inv_anti₀ (zero_lt_one.trans_le (one_le_spineScaleLoss _ _ _)) hLparent
    let PA := P.filter (fun j => h j ∈ A)
    have hPAfull : L⁻¹ * lamP <= ShadedBody.fullness PA (fun j => (Yp j).toShadedBody) := by
      have hh : (spineScaleLoss 3 P.card (sourceTowerRadius delta M p))⁻¹ * lamP <=
          ShadedBody.fullness PA (fun j => (Yp j).toShadedBody) := by
        have hh := href3.coe_mul_fullness_le
        simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
        exact_mod_cast hh
      exact (mul_le_mul_left hinvL3 lamP).trans hh
    have hPApos : 0 < ShadedBody.fullness PA (fun j => (Yp j).toShadedBody) :=
      (mul_pos (inv_pos.mpr (zero_lt_one.trans_le hL1)) hlamP0).trans_le hPAfull
    have hPAne : PA.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he, ShadedBody.fullness, ShadedBody.fullness', Finset.sum_empty,
        ENNReal.zero_div, ENNReal.toNNReal_zero] at hPApos
      exact lt_irrefl _ hPApos
    obtain ⟨hPAcar0, hPAcart⟩ := StickyKakeya.sum_volume_carrier_pos_ne_top hrhop PA Yp hPAne
    obtain ⟨ja, hja, hparentChoice⟩ := exists_fibre_fullness_le' PA
      (fun j => (Yp j).toShadedBody) A h (fun j hj => (Finset.mem_filter.mp hj).2)
        hAne hPAcar0.ne' hPAcart
    let parents := P.filter (fun j => h j = ja)
    have hparentsEq : PA.filter (fun j => h j = ja) = parents := by
      ext j
      simp only [PA, parents, Finset.mem_filter]
      exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2 ▸ hja⟩, hh.2⟩⟩
    rw [hparentsEq] at hparentChoice
    have hparentsFull : L⁻¹ * lamP <= ShadedBody.fullness parents (fun j => (Yp j).toShadedBody) :=
      hPAfull.trans hparentChoice
    have hparentsPos : 0 < ShadedBody.fullness parents (fun j => (Yp j).toShadedBody) :=
      hPApos.trans_le hparentChoice
    have hparentsNe : parents.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he, ShadedBody.fullness, ShadedBody.fullness', Finset.sum_empty,
        ENNReal.zero_div, ENNReal.toNNReal_zero] at hparentsPos
      exact lt_irrefl _ hparentsPos
    obtain ⟨jp, hjp⟩ := hparentsNe
    have hjpP : jp ∈ P := (Finset.mem_filter.mp hjp).1
    let middle := B.filter (fun j => g j = jp)
    have hmiddleNe : middle.Nonempty := hBfibrene jp (hPPdense hjpP)
    obtain ⟨jb, hjb⟩ := hmiddleNe
    have hjbB : jb ∈ B := (Finset.mem_filter.mp hjb).1
    have hqComp {sigma : NNReal} (hsigma : sigma <= 1)
        (F G : Finset iota) (V : iota -> Tube sigma (EuclideanSpace Real (Fin 3)))
        (c : NNReal) (hc : (F.card : ENNReal) <= c * (G.card : ENNReal)) :
        (∑ i ∈ F, volume (V i).carrier) <=
          ((c * q : NNReal) : ENNReal) * ∑ i ∈ G, volume (V i).carrier := by
      exact (hcarrierComp hsigma F G V c hc).trans
        (mul_le_mul_left (by exact_mod_cast mul_le_mul_right hqgeom c) _)
    have hpairB (i j : iota) : volume (Yb0 i).carrier <= (q : ENNReal) * volume (Yb0 j).carrier := by
      simpa only [Finset.sum_singleton, one_mul, hYb0carrier] using
        hqComp (hscales b hb).2 {i} {j} (Q.tube b) 1 (by simp)
    have hpairP (i j : iota) : volume (Yp0 i).carrier <= (q : ENNReal) * volume (Yp0 j).carrier := by
      simpa only [Finset.sum_singleton, one_mul, hYp0carrier] using
        hqComp (hscales p hpM).2 {i} {j} (Q.tube p) 1 (by simp)
    have hpairAf (i : iota) (hi : i ∈ B1) (j : iota) (hj : j ∈ B1) :
        af i <= ((2 * q : NNReal) : ENNReal) * af j :=
      hqComp ((hscales b hb).1.trans (hscales b hb).2) (Q.cell b i) (Q.cell b j)
        (fun k => (Z k).toTube) 2 (hst.descendant_count b hb i (hB1 hi) j (hB1 hj))
    have hAsum1 : (∑ j ∈ B1, af j) <= ∑ i ∈ S, volume (Z i).carrier := by
      change (∑ j ∈ B1, ∑ i ∈ S.filter (fun i => Q.place b i = j), volume (Z i).carrier) <= _
      rw [hpartition]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hretain1 : (((4 * L)⁻¹ : NNReal) : ENNReal) * M0 <= ∑ j ∈ B, mf j := by
      rw [ENNReal.coe_inv (by positivity)]
      exact (ENNReal.inv_mul_le_iff (by positivity) ENNReal.coe_ne_top).mpr hBmass
    have hScar0 : (∑ i ∈ S, volume (Z i).carrier) ≠ 0 :=
      ne_of_gt (hM0.trans_le (Finset.sum_le_sum fun i _ => measure_mono (Z i).shade_subset))
    let rb := lam / (8 * d * q^2 * L)
    have hrb0 : 0 < rb := by dsimp [rb]; positivity
    have hseedB : ShadedBody.IsCRefinement B (fun j => (Yb0 j).toShadedBody)
        B1 (fun j => (Yb0 j).toShadedBody) rb := by
      have hh := hseedRef S (fun i => (Z i).toShadedBody) B B1 hBB1
        (fun j => (Yb0 j).toShadedBody) af mf (2 * q) q d (4 * L)⁻¹
        (by positivity) hq0 hd0 hScar0 hpairAf
        (fun i _ j _ => hpairB i j) hblock1 hAsum1 hretain1
      convert hh using 1
      dsimp [rb]
      field_simp
      <;> ring
    have hpartitionB (J : Finset iota) (w : iota -> ENNReal) :
        (∑ j ∈ J, ∑ i ∈ B.filter (fun i => g i = j), w i) =
          ∑ i ∈ B.filter (fun i => g i ∈ J), w i := by
      have hf (j : iota) (hj : j ∈ J) :
          (B.filter (fun i => g i ∈ J)).filter (fun i => g i = j) =
            B.filter (fun i => g i = j) := by
        ext i
        simp only [Finset.mem_filter]
        exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2 ▸ hj⟩, hh.2⟩⟩
      convert Finset.sum_fiberwise_of_maps_to
        (s := B.filter (fun i => g i ∈ J)) (t := J) (g := g)
        (fun i hi => (Finset.mem_filter.mp hi).2) w using 1
      exact Finset.sum_congr rfl fun j hj => congrArg (fun I : Finset iota => ∑ i ∈ I, w i)
        (hf j hj).symm
    have hpairAp (i : iota) (hi : i ∈ P1) (j : iota) (hj : j ∈ P1) :
        ap i <= ((2 / gamma * q : NNReal) : ENNReal) * ap j := by
      have hiD := hP1 hi
      have hjD := hP1 hj
      have hcard : ((B.filter (fun k => g k = i)).card : NNReal) <=
          (2 / gamma) * ((B.filter (fun k => g k = j)).card : NNReal) := by
        apply hcountDense (N := ((Q.indexSet b).filter (fun k => g k = i)).card)
          (N' := ((Q.indexSet b).filter (fun k => g k = j)).card) hgamma0
        · exact_mod_cast Finset.card_le_card (show B.filter (fun k => g k = i) <=
              (Q.indexSet b).filter (fun k => g k = i) from
            fun k hk => Finset.mem_filter.mpr ⟨hBQ (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩)
        · have hh := hst.two_level_count p b hpb hb i (Finset.mem_filter.mp hiD).1
            j (Finset.mem_filter.mp hjD).1
          rw [hanc.2.2.2 i (Finset.mem_filter.mp hiD).1,
            hanc.2.2.2 j (Finset.mem_filter.mp hjD).1] at hh
          exact_mod_cast hh
        · rw [hBfibre j hjD]
          exact (Finset.mem_filter.mp hjD).2
      exact hqComp (hscales b hb).2 (B.filter (fun k => g k = i))
        (B.filter (fun k => g k = j)) (fun k => (Yb0 k).toTube) (2 / gamma)
        (by exact_mod_cast hcard)
    have hAsum2 : (∑ j ∈ P1, ap j) <= ∑ i ∈ B, volume (Yb0 i).carrier := by
      change (∑ j ∈ P1, ∑ i ∈ B.filter (fun i => g i = j), volume (Yb0 i).carrier) <= _
      rw [hpartitionB]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hretain2 : (((2 * L)⁻¹ : NNReal) : ENNReal) *
        (∑ i ∈ B, volume (Yb0 i).shade) <= ∑ j ∈ P, mp j := by
      rw [ENNReal.coe_inv (by positivity)]
      apply (ENNReal.inv_mul_le_iff (by positivity) ENNReal.coe_ne_top).mpr
      have hh : (∑ i ∈ B, volume (Yb0 i).shade) <=
          ((2 * L : NNReal) : ENNReal) * ∑ i ∈ B.filter (fun i => g i ∈ P), volume (Yb i).shade :=
        hPmass0.trans (mul_le_mul_left (by exact_mod_cast mul_le_mul_right hLmiddle 2) _)
      simpa only [mp, hpartitionB] using hh
    let rp := lam / (128 * d^2 * q^2 * L^3)
    have hrp0 : 0 < rp := by dsimp [rp]; positivity
    have hseedP : ShadedBody.IsCRefinement P (fun j => (Yp0 j).toShadedBody)
        P1 (fun j => (Yp0 j).toShadedBody) rp := by
      have hh := hseedRef B (fun i => (Yb0 i).toShadedBody) P P1 hPP1
        (fun j => (Yp0 j).toShadedBody) ap mp (2 / gamma * q) q d (2 * L)⁻¹
        (by positivity) hq0 hd0 hBcar0.ne' hpairAp
        (fun i _ j _ => hpairP i j) hblock2 hAsum2 hretain2
      apply ShadedBody.IsCRefinement.mono (c := (2 * L)⁻¹ * lamB / (2 / gamma * q * q * d)) ?_ hh
      calc
        rp = (2 * L)⁻¹ * (lam / (2 * L * d)) / (2 / gamma * q * q * d) := by
          dsimp [rp, gamma]
          field_simp
          <;> ring
        _ <= (2 * L)⁻¹ * lamB / (2 / gamma * q * q * d) := by gcongr
    have hmultB : ShadedBody.multiplicity B1 (fun j => (Yb0 j).toShadedBody) <=
        (rb⁻¹ : NNReal) * ShadedBody.multiplicity B (fun j => (Yb0 j).toShadedBody) := by
      rw [ENNReal.coe_inv hrb0.ne']
      apply (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr hrb0.ne') ENNReal.coe_ne_top).mp
      rw [← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hrb0.ne') ENNReal.coe_ne_top, one_mul]
      exact hseedB.mul_multiplicity_le
    have hmultP : ShadedBody.multiplicity P1 (fun j => (Yp0 j).toShadedBody) <=
        (rp⁻¹ : NNReal) * ShadedBody.multiplicity P (fun j => (Yp0 j).toShadedBody) := by
      rw [ENNReal.coe_inv hrp0.ne']
      apply (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr hrp0.ne') ENNReal.coe_ne_top).mp
      rw [← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hrp0.ne') ENNReal.coe_ne_top, one_mul]
      exact hseedP.mul_multiplicity_le
    have hmultFine : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        (L : ENNReal) * ((rb⁻¹ : NNReal) * ShadedBody.multiplicity B (fun j => (Yb0 j).toShadedBody)) *
          ShadedBody.multiplicity (Q.cell b jb) (fun i => (Z1 i).toShadedBody) := by
      exact (hmult1 jb (hBB1 hjbB)).trans
        (mul_le_mul_left (mul_le_mul' (by exact_mod_cast hLfine) hmultB) _)
    have hmultMiddle : ShadedBody.multiplicity B (fun j => (Yb0 j).toShadedBody) <=
        (L : ENNReal) * ((rp⁻¹ : NNReal) * ShadedBody.multiplicity P (fun j => (Yp0 j).toShadedBody)) *
          ShadedBody.multiplicity middle (fun j => (Yb j).toShadedBody) := by
      exact (hmult2 jp (hPP1 hjpP)).trans
        (mul_le_mul_left (mul_le_mul' (by exact_mod_cast hLmiddle) hmultP) _)
    have hmultParent : ShadedBody.multiplicity P (fun j => (Yp0 j).toShadedBody) <=
        (L : ENNReal) * ShadedBody.multiplicity A (fun j => (Ya j).toShadedBody) *
          ShadedBody.multiplicity parents (fun j => (Yp j).toShadedBody) := by
      have hh := hmult3 ja hja
      simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
      exact hh.trans (mul_le_mul_left (mul_le_mul_left (by exact_mod_cast hLparent) _) _)
    have hcoefficient : (L * rb⁻¹ * L * rp⁻¹ * L : NNReal) =
        1024 * d^3 * q^4 * L^7 * lam⁻¹^2 := by
      dsimp [rb, rp]
      field_simp
      <;> ring
    have hsplitPaid : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        ((H : ENNReal) * (lam : ENNReal)⁻¹^2) *
          ShadedBody.multiplicity (Q.cell b jb) (fun i => (Z1 i).toShadedBody) *
          ShadedBody.multiplicity middle (fun j => (Yb j).toShadedBody) *
          ShadedBody.multiplicity parents (fun j => (Yp j).toShadedBody) *
          ShadedBody.multiplicity A (fun j => (Ya j).toShadedBody) := by
      have hc : ((L * rb⁻¹ * L * rp⁻¹ * L : NNReal) : ENNReal) <=
          (H : ENNReal) * (lam : ENNReal)⁻¹^2 := by
        rw [hcoefficient, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv hfull.ne']
        exact mul_le_mul_left (by exact_mod_cast hH) _
      calc
        _ <= (L : ENNReal) * ((rb⁻¹ : NNReal) *
            ((L : ENNReal) * ((rp⁻¹ : NNReal) *
              ((L : ENNReal) * ShadedBody.multiplicity A (fun j => (Ya j).toShadedBody) *
                ShadedBody.multiplicity parents (fun j => (Yp j).toShadedBody))) *
              ShadedBody.multiplicity middle (fun j => (Yb j).toShadedBody))) *
            ShadedBody.multiplicity (Q.cell b jb) (fun i => (Z1 i).toShadedBody) := by
          apply hmultFine.trans
          gcongr
          apply hmultMiddle.trans
          gcongr
        _ = ((L * rb⁻¹ * L * rp⁻¹ * L : NNReal) : ENNReal) *
            ShadedBody.multiplicity (Q.cell b jb) (fun i => (Z1 i).toShadedBody) *
            ShadedBody.multiplicity middle (fun j => (Yb j).toShadedBody) *
            ShadedBody.multiplicity parents (fun j => (Yp j).toShadedBody) *
            ShadedBody.multiplicity A (fun j => (Ya j).toShadedBody) := by push_cast; ring
        _ <= _ := by gcongr
    have hfromMass (J : Finset iota) (V : iota -> ShadedBody (EuclideanSpace Real (Fin 3)))
        {x y : NNReal} (hy : 0 < y)
        (hc0 : (∑ i ∈ J, volume (V i).carrier) ≠ 0)
        (hm : (x : ENNReal) * (∑ i ∈ J, volume (V i).carrier) <=
          (y : ENNReal) * (∑ i ∈ J, volume (V i).shade)) :
        x / y <= ShadedBody.fullness J V := by
      have hct : (∑ i ∈ J, volume (V i).carrier) ≠ ⊤ := ENNReal.sum_ne_top.mpr
        fun i _ => (V i).toConvexSpaceBody.3.measure_ne_top
      rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul J V, ← mul_assoc] at hm
      have hh : x <= y * ShadedBody.fullness J V := by
        exact_mod_cast (ENNReal.mul_le_mul_iff_left hc0 hct).mp hm
      exact (div_le_iff₀ hy).mpr (by simpa only [mul_comm] using hh)
    have h2Lpos : 0 < 2 * L := by positivity
    have hfineBase : lam / (2 * L) <= ShadedBody.fullness (Q.cell b jb)
        (fun i => (Z1 i).toShadedBody) := by
      obtain ⟨hc0, _hct⟩ := StickyKakeya.sum_volume_carrier_pos_ne_top hdelta
        (Q.cell b jb) Z1 (hcellne b hb jb (hBQ hjbB))
      apply hfromMass _ _ h2Lpos hc0.ne'
      simpa only [hZ1carrier, mf, af] using hBfull jb hjbB
    have hmiddleBase : lamB / (2 * L) <= ShadedBody.fullness middle
        (fun j => (Yb j).toShadedBody) := by
      obtain ⟨hc0, _hct⟩ := StickyKakeya.sum_volume_carrier_pos_ne_top hrhob middle Yb ⟨jb, hjb⟩
      apply hfromMass _ _ h2Lpos hc0.ne'
      simpa only [middle, hYbcarrier, mp, ap] using hPfull jp hjpP
    have houterBase : L⁻¹ * lamP <= ShadedBody.fullness A (fun j => (Ya j).toShadedBody) := by
      have hh := hAfull0
      simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
      exact (mul_le_mul_left hinvL3 lamP).trans hh
    have hdom (c : NNReal) (hc : c <= 1024) (nd nq nL : Nat)
        (hdn : nd <= 3) (hqn : nq <= 4) (hLn : nL <= 7) :
        c * d^nd * q^nq * L^nL <= H :=
      (mul_le_mul' (mul_le_mul' (mul_le_mul' hc (pow_le_pow_right₀ hd1 hdn))
        (pow_le_pow_right₀ hq1 hqn)) (pow_le_pow_right₀ hL1 hLn)).trans hH
    have hHden : 4 * d^2 * L^3 <= H := by
      simpa only [pow_zero, mul_one] using hdom 4 (by norm_num) 2 0 3 (by omega) (by omega) (by omega)
    have hHtheta : 16 * L <= H := by
      simpa using hdom 16 (by norm_num) 0 0 1 (by omega) (by omega) (by omega)
    have hHstage : (4 * L)^3 <= H := by
      simpa only [pow_zero, mul_one, mul_pow, show (4 : NNReal)^3 = 64 from by norm_num] using
        hdom 64 (by norm_num) 0 0 3 (by omega) (by omega) (by omega)
    have hHpos : 0 < H := (by positivity : 0 < 16 * L).trans_le hHtheta
    have hbase : H⁻¹ * lam <= lam / (4 * d^2 * L^3) := by
      simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_left
        (inv_anti₀ (by positivity : 0 < 4 * d^2 * L^3) hHden) lam
    have hfineLower : H⁻¹ * lam <= ShadedBody.fullness (Q.cell b jb)
        (fun i => (Z1 i).toShadedBody) := by
      apply hbase.trans (le_trans ?_ hfineBase)
      have hh : 2 * L <= 4 * d^2 * L^3 := by
        calc
          2 * L = 2 * (1 : NNReal)^2 * L^1 := by ring
          _ <= 4 * d^2 * L^3 := by gcongr <;> norm_num
      exact div_le_div_of_nonneg_left zero_le h2Lpos hh
    have hmiddleLower : H⁻¹ * lam <= ShadedBody.fullness middle
        (fun i => (Yb i).toShadedBody) := by
      apply hbase.trans (le_trans ?_ hmiddleBase)
      calc
        lam / (4 * d^2 * L^3) <= lam / (4 * d * L^2) := by
          gcongr
          · simpa only [pow_one] using pow_le_pow_right₀ hd1 (show 1 <= 2 from by omega)
          · omega
        _ = (lam / (2 * L * d)) / (2 * L) := by field_simp; ring
        _ <= lamB / (2 * L) := by gcongr
    have hparentSeedBase : lam / (4 * d^2 * L^2) <= lamP := by
      calc
        lam / (4 * d^2 * L^2) = (lam / (2 * L * d)) / (2 * L * d) := by field_simp; ring
        _ <= lamB / (2 * L * d) := by gcongr
        _ <= lamP := hlamP
    have hparentOuterLower : H⁻¹ * lam <= L⁻¹ * lamP := by
      apply hbase.trans
      calc
        lam / (4 * d^2 * L^3) = L⁻¹ * (lam / (4 * d^2 * L^2)) := by field_simp <;> ring
        _ <= L⁻¹ * lamP := mul_le_mul_right hparentSeedBase _
    have hparentsSub : parents <= Q.fibre a p ja := by
      rw [hancAP.2.2.2 ja (hAQ hja)]
      intro j hj
      exact Finset.mem_filter.mpr ⟨hPQ (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
    have hmiddleSub : middle <= Q.fibre p b jp := by
      rw [hanc.2.2.2 jp (hPQ hjpP)]
      intro j hj
      exact Finset.mem_filter.mpr ⟨hBQ (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
    have hrefFine : ShadedBody.IsCRefinement (S.filter (fun i => Q.place b i ∈ B))
        (fun i => (Z1 i).toShadedBody) S (fun i => (Z i).toShadedBody) (4 * L)⁻¹ := by
      apply ShadedBody.isCRefinement_of_isRefinement_of_sum_le
      · refine ⟨Finset.filter_subset _ _, fun i _ => ⟨?_, hZ1sub i⟩⟩
        exact congrArg (fun U : Tube delta (EuclideanSpace Real (Fin 3)) => U.toConvexSpaceBody) (hZ1 i)
      · simpa only [mf, SourceThreadedTower.cell, hpartition] using hBmass
    have hrefMiddle : ShadedBody.IsCRefinement (B.filter (fun i => g i ∈ P))
        (fun i => (Yb i).toShadedBody) B (fun i => (Yb0 i).toShadedBody) (4 * L)⁻¹ := by
      apply ShadedBody.isCRefinement_of_isRefinement_of_sum_le
      · refine ⟨Finset.filter_subset _ _, fun i _ => ⟨?_, hYbsub i⟩⟩
        exact congrArg (fun U : Tube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)) =>
          U.toConvexSpaceBody) (hYb i)
      · apply hPmass0.trans
        apply mul_le_mul_left
        exact_mod_cast (show 2 * spineScaleLoss 3 B.card (sourceTowerRadius delta M b) <= 4 * L from
          (mul_le_mul_right hLmiddle 2).trans (by nlinarith))
    have hrefParent : ShadedBody.IsCRefinement PA
        (fun i => (Yp i).toShadedBody) P (fun i => (Yp0 i).toShadedBody) (4 * L)⁻¹ := by
      apply ShadedBody.IsCRefinement.mono ?_ href3
      simp only [finrank_euclideanSpace, Fintype.card_fin]
      apply inv_anti₀ (zero_lt_one.trans_le (one_le_spineScaleLoss _ _ _))
      exact hLparent.trans (by nlinarith)
    have hcardProduct {iota : Type u} {delta : NNReal} {S : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
        (Q : SourceThreadedTower S T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
        (hstats : SourceTowerStatistics Q Z)
        {a p b : Nat} (hap : a <= p) (hpb : p <= b) (hb : b <= M)
        {ja jp jb : iota} (hja : ja ∈ Q.indexSet a)
        (hjp : jp ∈ Q.indexSet p) (hjb : jb ∈ Q.indexSet b) :
        ((Q.cell b jb).card : ENNReal) * ((Q.fibre p b jp).card : ENNReal) *
          ((Q.fibre a p ja).card : ENNReal) * ((Q.indexSet a).card : ENNReal) <=
            8 * (S.card : ENNReal) := by
      classical
      have hsum (k : Nat) (hk : k <= M) :
          (∑ j ∈ Q.indexSet k, ((Q.cell k j).card : ENNReal)) = S.card := by
        simpa only [SourceThreadedTower.cell, Finset.sum_const, nsmul_eq_mul,
          mul_one] using Finset.sum_fiberwise_of_maps_to (Q.place_mem k hk)
            (fun _ => (1 : ENNReal))
      have hlocal (k l : Nat) (hkl : k <= l) (hl : l <= M)
          (j : iota) (hj : j ∈ Q.indexSet k) :
          (∑ v ∈ Q.fibre k l j, ((Q.cell l v).card : ENNReal)) = (Q.cell k j).card := by
        have ha := sourceQ_ancestor_fibre_identities Q hkl hl
        have hf : forall v, v ∈ Q.fibre k l j ->
            (Q.cell k j).filter (fun i => Q.place l i = v) = Q.cell l v := by
          intro v hv
          rw [ha.2.2.2 j hj] at hv
          obtain ⟨hv, hvj⟩ := Finset.mem_filter.mp hv
          ext i
          simp only [SourceThreadedTower.cell, Finset.mem_filter]
          constructor
          · exact fun h => ⟨h.1.1, h.2⟩
          · intro h
            refine ⟨⟨h.1, ?_⟩, h.2⟩
            rw [← ha.1 i h.1, h.2, hvj]
        have hm : forall i, i ∈ Q.cell k j -> Q.place l i ∈ Q.fibre k l j := by
          intro i hi
          exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
        have hs := Finset.sum_fiberwise_of_maps_to hm (fun _ => (1 : ENNReal))
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
        calc
          (∑ v ∈ Q.fibre k l j, ((Q.cell l v).card : ENNReal)) =
              ∑ v ∈ Q.fibre k l j, (((Q.cell k j).filter (fun i => Q.place l i = v)).card : ENNReal) := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [hf v hv]
          _ = (Q.cell k j).card := hs
      have hpair (k l : Nat) (hkl : k <= l) (hl : l <= M)
          (j v : iota) (hj : j ∈ Q.indexSet k) (hv : v ∈ Q.indexSet l) :
          ((Q.cell l v).card : ENNReal) * ((Q.fibre k l j).card : ENNReal) <=
            2 * ((Q.cell k j).card : ENNReal) := by
        calc
          ((Q.cell l v).card : ENNReal) * ((Q.fibre k l j).card : ENNReal) =
              ∑ w ∈ Q.fibre k l j, ((Q.cell l v).card : ENNReal) := by
                simp [mul_comm]
          _ <= ∑ w ∈ Q.fibre k l j, 2 * ((Q.cell l w).card : ENNReal) := by
            apply Finset.sum_le_sum
            intro w hw
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
            exact hstats.descendant_count l hl v hv _ (Q.place_mem l hl i (Finset.mem_filter.mp hi).1)
          _ = 2 * ((Q.cell k j).card : ENNReal) := by
            rw [← Finset.mul_sum, hlocal k l hkl hl j hj]
      have hlast : ((Q.cell a ja).card : ENNReal) * ((Q.indexSet a).card : ENNReal) <=
          2 * (S.card : ENNReal) := by
        calc
          ((Q.cell a ja).card : ENNReal) * ((Q.indexSet a).card : ENNReal) =
              ∑ j ∈ Q.indexSet a, ((Q.cell a ja).card : ENNReal) := by simp [mul_comm]
          _ <= ∑ j ∈ Q.indexSet a, 2 * ((Q.cell a j).card : ENNReal) := by
            exact Finset.sum_le_sum fun j hj => hstats.descendant_count a (by omega) ja hja j hj
          _ = 2 * (S.card : ENNReal) := by rw [← Finset.mul_sum, hsum a (by omega)]
      calc
        ((Q.cell b jb).card : ENNReal) * ((Q.fibre p b jp).card : ENNReal) *
            ((Q.fibre a p ja).card : ENNReal) * ((Q.indexSet a).card : ENNReal) <=
          (2 * ((Q.cell p jp).card : ENNReal)) * ((Q.fibre a p ja).card : ENNReal) *
            ((Q.indexSet a).card : ENNReal) := by
          exact mul_le_mul_right' (mul_le_mul_right' (hpair p b hpb hb jp jb hjp hjb) _) _
        _ = 2 * (((Q.cell p jp).card : ENNReal) * ((Q.fibre a p ja).card : ENNReal)) *
            ((Q.indexSet a).card : ENNReal) := by ring
        _ <= 2 * (2 * ((Q.cell a ja).card : ENNReal)) * ((Q.indexSet a).card : ENNReal) := by
          exact mul_le_mul_right' (mul_le_mul_left' (hpair a p hap (by omega) ja jp hja hjp) 2) _
        _ = 4 * (((Q.cell a ja).card : ENNReal) * ((Q.indexSet a).card : ENNReal)) := by ring
        _ <= 4 * (2 * (S.card : ENNReal)) := by gcongr
        _ = 8 * (S.card : ENNReal) := by ring
    have hcardFinal : ((Q.cell b jb).card : ENNReal) * (middle.card : ENNReal) *
        (parents.card : ENNReal) * (A.card : ENNReal) <= 16 * (S.card : ENNReal) := by
      have hh := hcardProduct Q Z hst hap (le_of_lt hpb) hb (hAQ hja) (hPQ hjpP) (hBQ hjbB)
      apply le_trans ?_ (hh.trans (mul_le_mul_left (by norm_num : (8 : ENNReal) <= 16) _))
      gcongr
      · exact hmiddleSub
      · exact hparentsSub
      · exact hAQ
    have hstagesPaid : (((4 * L : NNReal) : ENNReal))^3 <=
        (H : ENNReal) * (lam : ENNReal)⁻¹^2 := by
      apply (show (((4 * L : NNReal) : ENNReal))^3 <= (H : ENNReal) from by exact_mod_cast hHstage).trans
      rw [← ENNReal.coe_inv hfull.ne', ← ENNReal.coe_pow, ← ENNReal.coe_mul]
      exact_mod_cast (show H <= H * lam⁻¹^2 from le_mul_of_one_le_right zero_le
        (one_le_pow₀ ((one_le_inv₀ hfull).mpr (ShadedBody.fullness_le_one S _))))
    let X : SourceQMiddleSeam Q Z a p b (H⁻¹ * lam) ((H : ENNReal) * (lam : ENNReal)⁻¹^2) :=
      { coarse := A
        parents := parents
        middle := middle
        ja := ja
        jp := jp
        jb := jb
        fineShade := Z1
        middleShade := Yb
        parentShade := Yp
        outerShade := Ya
        coarse_subset := hAQ
        parents_subset := hparentsSub
        middle_subset := hmiddleSub
        coarse_member := hja
        parent_member := hjp
        middle_member := hjb
        fine_tubes := fun i => (hZ1 i).trans (hst.same_tubes i)
        middle_tubes := fun i => (hYb i).trans (hYb0 i)
        parent_tubes := fun i => (hYp i).trans (hYp0 i)
        outer_tubes := hYa
        fine_subshade := hZ1sub
        retainedMiddle := B
        retainedParents := P
        middleSeed := Yb0
        parentSeed := Yp0
        stageLoss := 4 * L
        stage_loss_one := by nlinarith
        stages_paid := hstagesPaid
        retained_middle_subset := hBQ
        retained_parents_subset := hPQ
        middle_fibre := rfl
        parent_fibre := rfl
        middle_seed_tubes := hYb0
        parent_seed_tubes := hYp0
        middle_refined := hYbsub
        parent_refined := hYpsub
        fine_in_middle_seed := fun i hi hj => hZ1in i hi (hBB1 hj)
        middle_in_parent_seed := fun i hi hj => hYbin i hi (hPP1 hj)
        parent_in_outer := hYpin
        fine_refinement := hrefFine
        middle_refinement := hrefMiddle
        parent_refinement := hrefParent
        refined_middle_mass := (hpartition middle (Q.place b) (fun i => volume (Z1 i).shade)).symm
        complete_middle_leaves := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_biUnion, SourceThreadedTower.cell]
          constructor
          · rintro ⟨hi, hj⟩
            exact ⟨Q.place b i, hj, hi, rfl⟩
          · rintro ⟨j, hj, hij⟩
            obtain ⟨hi, heq⟩ := hij
            exact ⟨hi, heq ▸ hj⟩
        complete_middle_mass := (hpartition middle (Q.place b) (fun i => volume (Z i).shade)).symm
        fine_fullness := hfineLower
        middle_fullness := hmiddleLower
        parent_fullness := hparentOuterLower.trans hparentsFull
        outer_fullness := hparentOuterLower.trans houterBase
        card_product := hcardFinal
        split := hsplitPaid }
    refine ⟨X, by exact_mod_cast hHstage, ?_⟩
    have hNpos : 0 < ((Q.fibre p b jp).card : Real) := by
      exact_mod_cast Finset.card_pos.mpr (show (Q.fibre p b jp).Nonempty from ⟨jb, hmiddleSub hjb⟩)
    have hgammaCard : (gamma : Real) * ((Q.fibre p b jp).card : Real) <= (middle.card : Real) := by
      have hh := (Finset.mem_filter.mp (hPPdense hjpP)).2
      rw [← hBfibre jp (hPPdense hjpP)] at hh
      rw [hanc.2.2.2 jp (hPQ hjpP)]
      exact_mod_cast hh
    have hgammaTheta : (gamma : Real) <= X.theta0 Q := (le_div_iff₀ hNpos).mpr hgammaCard
    apply le_trans ?_ hgammaTheta
    have hh : H⁻¹ <= gamma := inv_anti₀ (by positivity : 0 < 16 * L) hHtheta
    exact_mod_cast hh
  have hOccupied {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C A0 A1 : Nat}
      (Q : SourceThreadedTower S T M C) (hgeo : SourceTowerGeometry Q A0 A1)
      (hdelta : delta <= 1 / 40) (k : Nat) (hk : k <= M) :
      forall j, j ∈ Q.indexSet k ->
        (Q.tube k j).carrier <= Metric.closedBall 0 1 := by
    intro j hj
    obtain ⟨i, hi, hplace⟩ := Q.place_surjective k hk j hj
    have hrad : sourceTowerRadius delta M k <= 1 / 40 := by
      by_cases hkm : k < M
      · rw [sourceTowerRadius, if_pos hkm]
        have hd1 : delta <= 1 := hdelta.trans (by norm_num [div_le_iff₀])
        have he : (0 : Real) <= (k : Real) / (M : Real) := by positivity
        calc
          (1 / 40 : NNReal) * delta ^ ((k : Real) / (M : Real)) <= (1 / 40) * 1 := by
            gcongr
            exact NNReal.rpow_le_one hd1 he
          _ = 1 / 40 := by simp
      · simpa [sourceTowerRadius, hkm] using hdelta
    have hsub := Q.leaf_containment k hk i hi
    rw [hplace] at hsub
    have henlarge := Tube.le_rescale_of_subset (T i) (Q.tube k j) hsub
    intro x hx
    have hx' := henlarge hx
    change x ∈ ((T i).rescale (4 * sourceTowerRadius delta M k)).carrier at hx'
    rw [Tube.carrier_eq] at hx'
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx'
    have hyT : y ∈ (T i).carrier := by
      rw [(T i).carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨y, hy, Metric.mem_closedBall_self delta.coe_nonneg⟩
    have hy0 := hgeo.original_ball i hi hyT
    rw [Metric.mem_closedBall] at hxy hy0 ⊢
    have hrad' : (sourceTowerRadius delta M k : Real) <= 1 / 40 := by exact_mod_cast hrad
    push_cast at hxy
    calc
      dist x 0 <= dist x y + dist y 0 := dist_triangle _ _ _
      _ <= 1 := by linarith
  have hRadii (M : Nat) (hM : 2 <= M) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        0 < delta /\ delta <= 1 / 40 /\
        (forall k, k <= M -> delta <= sourceTowerRadius delta M k /\
          sourceTowerRadius delta M k <= 1) /\
        (forall k l, k <= l -> l <= M -> sourceTowerRadius delta M l <= sourceTowerRadius delta M k) := by
    filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : Real) < 1),
      Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1 / 40)] with delta hrad hd
    have hstep (k : Nat) (hk : k < M) : sourceTowerRadius delta M (k + 1) <= sourceTowerRadius delta M k :=
      (hrad.2.2.2.2.2 k hk).trans (div_le_self (by positivity) (by norm_num))
    have hmono (k l : Nat) (hkl : k <= l) :
        l <= M -> sourceTowerRadius delta M l <= sourceTowerRadius delta M k := by
      induction l, hkl using Nat.le_induction with
      | base => exact fun _ => le_refl _
      | succ l hkl ih =>
        intro hl
        exact (hstep l (by omega)).trans (ih (by omega))
    refine ⟨hrad.2.2.1, hd.2.le, ?_, hmono⟩
    intro k hk
    refine ⟨?_, (hmono 0 k (Nat.zero_le k) hk).trans hrad.2.2.2.1⟩
    by_cases hkm : k < M
    · have hh := hrad.2.2.2.2.1 k hkm
      nlinarith
    · have heq : k = M := by omega
      simp [heq, sourceTowerRadius]
  have hCards {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C A0 A1 : Nat}
      (Q : SourceThreadedTower S T M C) (eta : Real) (heta : eta <= 2)
      (hinput : SourceFixedTowerInput Q A0 A1 eta)
      (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      (hscales : forall k, k <= M -> delta <= sourceTowerRadius delta M k) :
      let A := max (Tube.card_le_of_densityIn_le.C 3) ((32 : NNReal)^(6 : Nat))
      (S.card : NNReal) <= A * delta ^ (-(6 : Real)) /\
        forall k, k <= M -> forall J : Finset iota, J <= Q.indexSet k ->
          (J.card : NNReal) <= A * delta ^ (-(6 : Real)) := by
    dsimp only
    let A := max (Tube.card_le_of_densityIn_le.C 3) ((32 : NNReal)^(6 : Nat))
    change (S.card : NNReal) <= A * delta ^ (-(6 : Real)) /\
      forall k, k <= M -> forall J : Finset iota, J <= Q.indexSet k ->
        (J.card : NNReal) <= A * delta ^ (-(6 : Real))
    have hball (i : iota) (hi : i ∈ S) : (T i).carrier <= Metric.closedBall 0 1 :=
      (hinput.geometry.original_ball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
    have hraw := Tube.card_le_of_densityIn_le hdelta.ne' hball
      ((Kakeya.le_maxDensity _ _ _).trans hinput.maximal_density)
    have hcardE : (S.card : ENNReal) <=
        (Tube.card_le_of_densityIn_le.C 3 : ENNReal) * (delta : ENNReal)^(-eta - 2) := by
      have hpow : (delta : ENNReal)^(-(2 : Int)) = (delta : ENNReal)^(-(2 : Real)) := by
        convert (ENNReal.rpow_intCast (delta : ENNReal) (-2 : Int)).symm using 1 <;> norm_num
      norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
        Int.reduceSub, Int.reduceNeg] at hraw
      rw [← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hdelta), ENNReal.ofReal_coe_nnreal,
        hpow, mul_assoc, ← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hdelta.ne') ENNReal.coe_ne_top] at hraw
      simpa only [sub_eq_add_neg] using hraw
    have hcard : (S.card : NNReal) <= A * delta ^ (-(6 : Real)) := by
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hdelta.ne']
      apply hcardE.trans
      apply mul_le_mul'
      · exact ENNReal.coe_le_coe.mpr (le_max_left _ _)
      · exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdelta1) (by linarith)
    refine ⟨hcard, ?_⟩
    intro k hk J hJ
    by_cases hkM : k < M
    · have hrhop : 0 < (sourceTowerRadius delta M k : Real) := by
        exact_mod_cast hdelta.trans_le (hscales k hk)
      have hdeltaR : 0 < (delta : Real) := by exact_mod_cast hdelta
      have hscalesR : (delta : Real) <= (sourceTowerRadius delta M k : Real) := by exact_mod_cast hscales k hk
      have hJcard : (J.card : Real) <= (32 / (sourceTowerRadius delta M k : Real))^6 :=
        (show (J.card : Real) <= ((Q.indexSet k).card : Real) from by exact_mod_cast Finset.card_le_card hJ).trans
          (hinput.geometry.coarse_card k hkM)
      have hbound : (32 / (sourceTowerRadius delta M k : Real))^6 <= (A : Real) * (delta : Real)^(-(6 : Real)) := by
        calc
          _ <= (32 / (delta : Real))^6 := by gcongr
          _ = (32 : Real)^6 * (delta : Real)^(-(6 : Real)) := by
            rw [div_pow, Real.rpow_neg hdeltaR.le, Real.rpow_ofNat, div_eq_mul_inv]
          _ <= _ := mul_le_mul_of_nonneg_right
            (by exact_mod_cast (show ((32 : NNReal)^(6 : Nat)) <= A from le_max_right _ _))
            (Real.rpow_nonneg hdeltaR.le _)
      exact_mod_cast hJcard.trans hbound
    · have hkEq : k = M := by omega
      rw [hkEq, Q.bottom_index] at hJ
      exact (show (J.card : NNReal) <= (S.card : NNReal) from by exact_mod_cast Finset.card_le_card hJ).trans hcard
  have hAbsorb (c : NNReal) (k0 : Nat) :
      exists K : Nat, 1 <= K /\ forall delta : NNReal, 0 < delta -> delta <= 1 ->
        c * (sourceQSelectionLoss k0 delta)^7 <= sourceQSelectionLoss K delta := by
    let N := Nat.ceil (c : Real)
    refine ⟨N + 7 * k0 + 1, by omega, ?_⟩
    intro delta hd hd1
    have hlog : 0 <= Real.logb 2 (1 / (delta : Real)) :=
      Real.logb_nonneg (by norm_num) (by
        rw [le_div_iff₀ (by exact_mod_cast hd)]
        simpa only [one_mul] using (show (delta : Real) <= 1 from by exact_mod_cast hd1))
    let x := Real.toNNReal (2 + Real.logb 2 (1 / (delta : Real)))
    have hx2 : 2 <= x := by
      have hh := Real.toNNReal_le_toNNReal (show (2 : Real) <= 2 + Real.logb 2 (1 / (delta : Real)) by linarith)
      simpa only [Real.toNNReal_ofNat] using hh
    have hx1 : 1 <= x := (by norm_num : (1 : NNReal) <= 2).trans hx2
    have hcN : c <= (N : NNReal) := by exact_mod_cast Nat.le_ceil (c : Real)
    have hNpow : (N : NNReal) <= (2 : NNReal)^N := by
      exact_mod_cast (show N <= 2^N from Nat.lt_two_pow_self.le)
    have hcx : c <= x^N := hcN.trans (hNpow.trans (pow_le_pow_left₀ (by positivity) hx2 _))
    have hloss (k : Nat) : sourceQSelectionLoss k delta = x^k := by
      exact Real.toNNReal_pow (by positivity) _
    rw [hloss, hloss]
    calc
      c * (x^k0)^7 <= x^N * (x^k0)^7 := mul_le_mul_left hcx _
      _ = x^(N + 7 * k0) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ <= x^(N + 7 * k0 + 1) := pow_le_pow_right₀ hx1 (by omega)
  have hLossBound (K : Nat) {eta : Real} (heta : 0 < eta) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        sourceFixedPreparationLoss K delta <= (delta : ENNReal) ^ (-eta) := by
    filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (2 : ENNReal)^K) (by finiteness) (by positivity : 0 < eta / 2),
      ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (by positivity : 0 < eta / 2) K,
      Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with delta hc hl hd
    have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
    have hdreal : (0 : Real) < delta := by exact_mod_cast hd.1
    have hdreal1 : (delta : Real) <= 1 := by exact_mod_cast hd.2.le
    have hlog : 0 <= Real.logb 2 (1 / (delta : Real)) :=
      Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hdreal]; linarith)
    calc sourceFixedPreparationLoss K delta <=
          ENNReal.ofReal ((2 * (1 + Real.logb 2 (1 / (delta : Real))))^K) := by
            apply ENNReal.ofReal_le_ofReal
            gcongr
            linarith
      _ = (2 : ENNReal)^K * ENNReal.ofReal (1 + Real.logb 2 (1 / (delta : Real)))^K := by
            rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num), mul_pow]
            norm_num
      _ <= (delta : ENNReal)^(-(eta / 2)) * (delta : ENNReal)^(-(eta / 2)) := mul_le_mul' hc hl
      _ = (delta : ENNReal)^(-eta) := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            congr 1
            ring
  have hBudget {delta H lam : NNReal} {eta : Real} (hd : 0 < delta) (hd1 : delta <= 1)
      (heta : 0 < eta) (hH0 : 0 < H) (hH : H <= delta ^ (-(4 * eta)))
      (hlam : delta ^ eta <= lam) :
      delta ^ (5 * eta) <= H⁻¹ * lam /\
        (delta : Real) ^ (6 * eta) <= (H : Real)⁻¹ /\
        (lam : ENNReal)⁻¹^2 <= ENNReal.ofReal ((delta : Real)^(-2 * eta)) := by
    have hpower0 : 0 < delta ^ (-(4 * eta)) := by positivity
    have hinv : delta ^ (4 * eta) <= H⁻¹ := by
      have hh := inv_anti₀ hH0 hH
      simpa only [NNReal.rpow_neg, inv_inv] using hh
    have hf : delta ^ (5 * eta) <= H⁻¹ * lam := by
      calc
        delta ^ (5 * eta) = delta ^ (4 * eta) * delta ^ eta := by
          rw [← NNReal.rpow_add hd.ne']
          congr 1
          ring
        _ <= H⁻¹ * lam := mul_le_mul' hinv hlam
    have ht : delta ^ (6 * eta) <= H⁻¹ :=
      (NNReal.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)).trans hinv
    have hlam0 : 0 < lam := (by positivity : 0 < delta ^ eta).trans_le hlam
    have hinvLam : lam⁻¹ <= delta ^ (-eta) := by
      simpa only [NNReal.rpow_neg] using inv_anti₀ (by positivity : 0 < delta ^ eta) hlam
    have hpay : lam⁻¹^2 <= delta ^ (-2 * eta) := by
      calc
        lam⁻¹^2 <= (delta ^ (-eta))^2 := pow_le_pow_left₀ (by positivity) hinvLam _
        _ = delta ^ (-2 * eta) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
          congr 1
          ring
    refine ⟨hf, by exact_mod_cast ht, ?_⟩
    rw [← ENNReal.coe_inv hlam0.ne', ← ENNReal.coe_pow,
      ← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hd), ENNReal.ofReal_coe_nnreal,
      ← ENNReal.coe_rpow_of_ne_zero hd.ne']
    exact ENNReal.coe_le_coe.mpr hpay
  have hEnvelope (A : NNReal) (B : Real) (hA : 0 < A) (hB : 0 <= B) :
      exists k : Nat, ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall (sigma : NNReal) (N : Nat), 0 < delta -> delta <= sigma -> sigma <= 1 ->
          (N : NNReal) <= A * delta ^ (-B) -> spineScaleLoss 3 N sigma <= sourceQSelectionLoss k delta := by
    exact source_exists_spineScaleLoss_polylog_envelope A B hA hB
  let A := max (Tube.card_le_of_densityIn_le.C 3) ((32 : NNReal)^(6 : Nat))
  have hApos : 0 < A := (by norm_num : (0 : NNReal) < 32^6).trans_le (le_max_right _ _)
  let d := max 1 (Tube.dilateFullness.C 3)
  let q := max 1 (Tube.volume_le.C 3 / Tube.le_volume.c 3)
  obtain ⟨k0, hk0⟩ := hEnvelope A 6 hApos (by norm_num)
  obtain ⟨K, hK, hKbound⟩ := hAbsorb (1024 * d^3 * q^4) k0
  refine ⟨K, hK, ?_⟩
  filter_upwards [hk0, hRadii M hM, hLossBound K (by positivity : 0 < 4 * etaC)] with delta hscale hrad hpower
  intro iota S T Q Z hinput hst hfull _hleaf a p b hap hpb hb
  obtain ⟨hd, hd40, hscales, hmono⟩ := hrad
  have hd1 : delta <= 1 := hd40.trans (by norm_num [div_le_iff₀])
  obtain ⟨hScard, hQcard⟩ := hCards Q etaC (by linarith) hinput hd hd1 (fun k hk => (hscales k hk).1)
  let L := sourceQSelectionLoss k0 delta
  let H := sourceQSelectionLoss K delta
  have hlossOne (k : Nat) : 1 <= sourceQSelectionLoss k delta := by
    have hlog : 0 <= Real.logb 2 (1 / (delta : Real)) :=
      Real.logb_nonneg (by norm_num) (by
        rw [le_div_iff₀ (by exact_mod_cast hd)]
        simpa only [one_mul] using (show (delta : Real) <= 1 from by exact_mod_cast hd1))
    rw [sourceQSelectionLoss, Real.toNNReal_pow (by positivity)]
    apply one_le_pow₀
    have hh := Real.toNNReal_le_toNNReal (show (1 : Real) <= 2 + Real.logb 2 (1 / (delta : Real)) by linarith)
    simpa only [Real.toNNReal_one] using hh
  have hZball (i : iota) (hi : i ∈ S) : (Z i).carrier <= Metric.closedBall 0 1 := by
    have hcar : (Z i).carrier = (T i).carrier :=
      congrArg (fun U : Tube delta (EuclideanSpace Real (Fin 3)) => U.carrier) (hst.same_tubes i)
    rw [hcar]
    exact (hinput.geometry.original_ball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hLfine : spineScaleLoss 3 S.card delta <= L := hscale delta S.card hd le_rfl hd1 hScard
  have hLcoarse (k : Nat) (hk : k <= M) (J : Finset iota) (hJ : J <= Q.indexSet k) :
      spineScaleLoss 3 J.card (sourceTowerRadius delta M k) <= L :=
    hscale _ _ hd (hscales k hk).1 (hscales k hk).2 (hQcard k hk J hJ)
  have hH : 1024 * d^3 * q^4 * L^7 <= H := hKbound delta hd hd1
  have hlam0 : 0 < ShadedBody.fullness S (fun i => (Z i).toShadedBody) :=
    (by positivity : 0 < delta ^ etaC).trans_le hfull
  obtain ⟨X, hstage, htheta⟩ := hRaw Q Z hst hd hap hpb hb hscales hmono
    (fun k hk => hOccupied Q hinput.geometry hd40 k hk) hZball hlam0
    L H d q (hlossOne k0) (le_max_left _ _) (le_max_left _ _)
    (le_max_right _ _) le_rfl hLfine hLcoarse hH
  have hcompat : sourceFixedPreparationLoss K delta = (H : ENNReal) := rfl
  have hHpos : 0 < H := zero_lt_one.trans_le (hlossOne K)
  have hHpow : H <= delta ^ (-(4 * etaC)) := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_rpow_of_ne_zero hd.ne']
    exact hcompat ▸ hpower
  obtain ⟨hlambda, hthetaPow, hinverse⟩ := hBudget hd hd1 heta hHpos hHpow hfull
  have hNpos : 0 < ((Q.fibre p b X.jp).card : Real) := by
    exact_mod_cast Finset.card_pos.mpr (show (Q.fibre p b X.jp).Nonempty from
      ⟨X.jb, X.middle_subset X.middle_member⟩)
  have hthetaOne : X.theta0 Q <= 1 := by
    apply (div_le_one hNpos).mpr
    exact_mod_cast Finset.card_le_card X.middle_subset
  have hthetaPos : 0 < X.theta0 Q := (inv_pos.mpr (by exact_mod_cast hHpos)).trans_le htheta
  refine ⟨X, hcompat, ?_, hlambda, hthetaPos, hthetaOne, htheta, hthetaPow.trans htheta, ?_⟩
  · exact hstage
  · exact mul_le_mul_right hinverse _

end Kakeya.ML2Assembly

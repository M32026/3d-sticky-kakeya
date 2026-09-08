/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricFactorTransportData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDComparablePlankAdapter

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

set_option maxHeartbeats 6000000 in
/-- The D-comparable raw factors, anisotropic normalization and partial-part
selection produce one actual GlobalPlankFactorization with a fixed polynomial
cost. This is a new geometry obligation; no constant-2 adapter is substituted. -/
theorem source_exists_eccentric_factor_transport
    (Rnorm : Real) (hR : 64 <= Rnorm) (Cgeom cParent D : NNReal)
    (hC : 1 <= Cgeom) (hc : 1 <= cParent) (hD : 1 <= D) :
    exists (A : NNReal) (p : Nat), Cgeom <= A /\ 1 <= A /\ 1 <= p /\
      forall {iota : Type u} {delta : NNReal} (_hdelta : 0 < delta) (_hdelta1 : delta <= 1)
        (S : Finset iota) (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (M C : Nat) (Q : SourceThreadedTower S T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
        (a m : Nat) (Lout : NNReal) (etaParent bias : Real) (aw bw cw : NNReal),
      0 < bias ->
      forall (O : SourceEccentricOuterSplit Q Z a Lout)
        (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
        (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
        (Lsel Ccount : NNReal), 1 <= Lsel ->
      forall P : SourceEccentricAssignedSelection Q O Nrm E Lsel Ccount,
        Nonempty (SourceEccentricFactorTransport Q P
          (sourceEccentricTransportCost A Lsel p delta bias)) := by
  classical
  have hCosts (G D c l : NNReal) (hG : 1 <= G) (hD : 1 <= D) (hc : 1 <= c) (hl : 1 <= l) :
      let k := c * l
      let lam := 2^50 * k
      let dd := 2 * G * D * lam
      let cz := 2^200 * G^2 * D^2 * k^4
      let A := 2^210 * G^2 * D^2
      1 <= dd ∧ 1 <= cz ∧ 256 * dd^2 <= cz ∧
        (384 * lam^3) * G * c <= cz ∧ G^2 * c * l <= cz ∧
        cz <= A * l^4 * c^4 ∧ G <= A ∧ 1 <= A := by
    dsimp only
    let k := c * l
    have hk : 1 <= k := one_le_mul_of_one_le_of_one_le hc hl
    have hck : c <= k := le_mul_of_one_le_right' hl
    have hk14 : k <= k^4 := by simpa using pow_le_pow_right₀ hk (by norm_num : 1 <= 4)
    have hk24 : k^2 <= k^4 := pow_le_pow_right₀ hk (by norm_num)
    have hG2 : G <= G^2 := by simpa using pow_le_pow_right₀ hG (by norm_num : 1 <= 2)
    have hD2 : 1 <= D^2 := one_le_pow₀ hD
    have hG21 : 1 <= G^2 := one_le_pow₀ hG
    have hk41 : 1 <= k^4 := one_le_pow₀ hk
    have hdd : 1 <= 2 * G * D * (2^50 * k) := by
      apply one_le_mul_of_one_le_of_one_le
      · exact one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by norm_num) hG) hD
      · exact one_le_mul_of_one_le_of_one_le (by norm_num) hk
    have hcz : 1 <= 2^200 * G^2 * D^2 * k^4 :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by norm_num) hG21) hD2) hk41
    have hA : G <= 2^210 * G^2 * D^2 := by
      calc G <= G^2 := hG2
        _ <= 2^210 * G^2 := le_mul_of_one_le_left' (by norm_num)
        _ <= _ := le_mul_of_one_le_right' hD2
    refine ⟨hdd, hcz, ?_, ?_, ?_, ?_, hA, hG.trans hA⟩
    · change 256 * (2 * G * D * (2^50 * k))^2 <= _
      calc 256 * (2 * G * D * (2^50 * k))^2 = 2^110 * G^2 * D^2 * k^2 := by ring
        _ <= 2^200 * G^2 * D^2 * k^4 := by gcongr <;> norm_num
    · change (384 * (2^50 * k)^3) * G * c <= _
      calc (384 * (2^50 * k)^3) * G * c <= (384 * (2^50 * k)^3) * G * k := by gcongr
        _ = (384 * 2^150) * G * k^4 := by ring
        _ <= 2^200 * G^2 * k^4 := by gcongr <;> norm_num
        _ <= (2^200 * G^2 * k^4) * D^2 := le_mul_of_one_le_right' hD2
        _ = _ := by dsimp [k]; ring
    · change G^2 * c * l <= _
      calc G^2 * c * l = G^2 * k := by dsimp [k]; ring
        _ <= 2^200 * G^2 * k^4 := by
          exact mul_le_mul' (le_mul_of_one_le_left' (by norm_num)) hk14
        _ <= (2^200 * G^2 * k^4) * D^2 := le_mul_of_one_le_right' hD2
        _ = _ := by dsimp [k]; ring
    · calc 2^200 * G^2 * D^2 * (c*l)^4 <= 2^210 * G^2 * D^2 * (c*l)^4 := by
            gcongr <;> norm_num
        _ = _ := by ring
  let A : NNReal := 2^210 * Cgeom^2 * D^2
  obtain ⟨_, _, _, _, _, _, hCA, hAone⟩ := hCosts Cgeom D 1 1 hC hD le_rfl le_rfl
  refine ⟨A, 4, hCA, hAone, by norm_num, ?_⟩
  intro iota delta hdelta hdelta1 S T M C Q Z a m Lout etaParent bias aw bw cw hbias O Nrm E Lsel Ccount hL P
  have hGeometry (hdelta : 0 < delta) (Q : SourceThreadedTower S T M C)
      {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
      {a m : Nat} {Lout : NNReal} (O : SourceEccentricOuterSplit Q Z a Lout)
      {Rnorm : Real} {Cgeom cParent : NNReal}
      (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
      {etaParent bias : Real} {D aw bw cw : NNReal}
      (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
      {Lsel Ccount : NNReal} (hL : 1 <= Lsel)
      (hC0 : 1 <= sourceZeroPlankConstant delta bias)
      (P : SourceEccentricAssignedSelection Q O Nrm E Lsel Ccount) :
      (forall part, part ∈ P.keptParts ->
        affineJacobian Nrm.affine * volume
          (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier <=
          (sourceZeroPlankConstant delta bias * Lsel : NNReal) * volume
            ((part ∩ P.parents).convexHull_biUnion (fun k => (Nrm.parent k).toConvexSpaceBody)).carrier) ∧
      (forall part, part ∈ P.keptParts ->
        volume ((part ∩ P.parents).convexHull_biUnion
          (fun k => (Nrm.parent k).toConvexSpaceBody)).carrier <=
          (Cgeom : ENNReal) * affineJacobian Nrm.affine * volume
            (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier) ∧
      (forall V : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
        exists W : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
          volume W.carrier <=
            ((384 * (2^50 * (sourceZeroPlankConstant delta bias * Lsel))^3 : NNReal) : ENNReal) /
              affineJacobian Nrm.affine * volume V.carrier ∧
          forall part, part ∈ P.keptParts ->
            (part ∩ P.parents).convexHull_biUnion (fun k => (Nrm.parent k).toConvexSpaceBody) <= V ->
            part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody) <= W) := by
    classical
    have hRetained {r : Finset iota}
        {V : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3))} {C0 L : NNReal}
        (F : ConvexSpaceBody.Factorization r V C0) {part q : Finset iota}
        (hpart : part ∈ F.parts) (hq : q <= part) (hqne : q.Nonempty)
        (hpositive : forall i, i ∈ part -> 0 < volume (V i).carrier)
        (hret : (∑ i ∈ part, volume (V i).carrier) <=
          (L : ENNReal) * ∑ i ∈ q, volume (V i).carrier) :
        volume (part.convexHull_biUnion V).carrier <=
          (C0 : ENNReal) * L * volume (q.convexHull_biUnion V).carrier := by
      classical
      let v := volume (part.convexHull_biUnion V).carrier
      let w := volume (q.convexHull_biUnion V).carrier
      let s := ∑ i ∈ part, volume (V i).carrier
      let t := ∑ i ∈ q, volume (V i).carrier
      have hvtop : v ≠ ⊤ := (part.convexHull_biUnion V).isCompact'.measure_lt_top.ne
      have hwtop : w ≠ ⊤ := (q.convexHull_biUnion V).isCompact'.measure_lt_top.ne
      have hstop : s ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (V i).isCompact'.measure_lt_top.ne
      have httop : t ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (V i).isCompact'.measure_lt_top.ne
      obtain ⟨i0, hi0⟩ := hqne
      have hi0p := hq hi0
      have hvpos : 0 < v := (hpositive i0 hi0p).trans_le
        (measure_mono (Finset.le_convexHull_biUnion V hi0p))
      have hwpos : 0 < w := (hpositive i0 hi0p).trans_le
        (measure_mono (Finset.le_convexHull_biUnion V hi0))
      have hspos : 0 < s := by
        refine (hpositive i0 hi0p).trans_le ?_
        dsimp [s]
        exact Finset.single_le_sum (f := fun i => volume (V i).carrier) (fun _ _ => bot_le) hi0p
      have hden : t / w <= (C0 : ENNReal) * (s / v) := by
        have hqR := hq.trans (F.toFinpartition.le hpart)
        have hbound := (le_maxDensity q V (q.convexHull_biUnion V)).trans
          ((maxDensity_mono V hqR).trans (F.maxDensity_le_mul part hpart))
        rw [densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi),
          densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi)] at hbound
        exact hbound
      have hrreal : s.toReal <= L * t.toReal := by
        have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top httop) hret
        simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using h
      have hdreal : t.toReal / w.toReal <= C0 * (s.toReal / v.toReal) := by
        have hden_top : (C0 : ENNReal) * (s / v) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.div_ne_top hstop hvpos.ne')
        have h := ENNReal.toReal_mono hden_top hden
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.coe_toReal] using h
      have hvreal : 0 < v.toReal := ENNReal.toReal_pos hvpos.ne' hvtop
      have hwreal : 0 < w.toReal := ENNReal.toReal_pos hwpos.ne' hwtop
      have hsreal : 0 < s.toReal := ENNReal.toReal_pos hspos.ne' hstop
      have hcross : t.toReal * v.toReal <= (C0 : Real) * s.toReal * w.toReal := by
        apply (div_le_iff₀ hwreal).mp at hdreal
        apply (mul_le_mul_iff_left₀ hvreal).2 at hdreal
        field_simp at hdreal
        nlinarith [hdreal]
      have hgoal : v.toReal <= (C0 : Real) * L * w.toReal := by
        have h1 := mul_le_mul_of_nonneg_right hrreal hvreal.le
        have h2 := mul_le_mul_of_nonneg_left hcross L.coe_nonneg
        nlinarith
      apply (ENNReal.toReal_le_toReal hvtop
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hwtop)).mp
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hgoal
    have hTest {jota : Type u} (q : Finset jota)
        (B O N : jota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
        (A : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3))
        (L : NNReal) (hL : 1 <= L)
        (hBpos : forall i, i ∈ q -> 0 < volume (B i).carrier)
        (hBO : forall i, i ∈ q -> B i <= O i)
        (hOBvol : forall i, i ∈ q -> volume (O i).carrier <= (L : ENNReal) * volume (B i).carrier)
        (hBN : forall i, i ∈ q -> (B i).mapAffine A <= N i) :
        forall V : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
          exists W : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
            volume W.carrier <= ((384 * (2^50 * L)^3 : NNReal) : ENNReal) /
              affineJacobian A * volume V.carrier ∧
            forall i, i ∈ q -> N i <= V -> O i <= W := by
      have hEnlarge (K : NNReal) (hK : 1 <= K)
          (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) (hM : 0 < volume M.carrier) :
          ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
            M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
            Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
        have hNormalized (K : NNReal) (hK : 1 <= K)
            (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
            (hMball : M.carrier <= Metric.closedBall 0 3)
            (hMvol : (6 : ENNReal)⁻¹ <= volume M.carrier) :
            ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
              M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
              Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
          have hMvol' : ENNReal.ofReal (1 / 6 : Real) <= volume M.carrier := by
            rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 6)]
            norm_num
            exact hMvol
          obtain ⟨z, hzM, hzball⟩ := exists_closedBall_subset_of_le_volume (by norm_num : 1 <= 3)
            (by norm_num : (0 : Real) < 3) M hMball (by norm_num : (0 : Real) < 1 / 6) hMvol'
          norm_num at hzball
          let r : NNReal := 1 / 1728
          have hball : Metric.closedBall z (r : Real) <= M.carrier := by
            simpa [r] using hzball
          have hMu : volume M.carrier <= 216 := by
            have h := volume_le_prod_ethickness M.carrier
            have hth : forall n, ethickness Real M.carrier n <= (3 : NNReal) :=
              fun n => ethickness_le_of_subset_closedBall (𝕜 := Real) 3 hMball n
            norm_num [Finset.prod_range_succ] at h
            calc volume M.carrier <=
                8 * (ethickness Real M.carrier 0 * ethickness Real M.carrier 1 *
                  ethickness Real M.carrier 2) := h
              _ <= 8 * ((3 : ENNReal) * 3 * 3) := by gcongr <;> exact hth _
              _ = 216 := by norm_num
          refine ⟨z, hzM, ?_⟩
          intro Q hMQ hQvol x hxQ
          have hQu : volume Q.carrier <= (216 : ENNReal) * K :=
            hQvol.trans (by simpa only [mul_comm] using mul_le_mul_left' hMu (K : ENNReal))
          have hr1 : (r : ENNReal) <= ethickness Real Q.carrier 1 :=
            (le_ethickness_closedBall (x := z) (n := 1) r (by norm_num)).trans
              (ethickness_monotone (hball.trans hMQ) 1)
          have hr2 : (r : ENNReal) <= ethickness Real Q.carrier 2 :=
            (le_ethickness_closedBall (x := z) (n := 2) r (by norm_num)).trans
              (ethickness_monotone (hball.trans hMQ) 2)
          have htfin : forall n, ethickness Real Q.carrier n ≠ ⊤ := by
            intro n
            change ethickness Real (Q : Set (EuclideanSpace Real (Fin 3))) n ≠ ⊤
            rw [ethickness_thickness' Q.isCompact.isBounded]
            exact ENNReal.ofReal_ne_top
          have hQr : (volume Q.carrier).toReal <= 216 * (K : Real) := by
            have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hQu
            simpa using this
          have hr1r : (r : Real) <= (ethickness Real Q.carrier 1).toReal := by
            simpa using ENNReal.toReal_mono (htfin 1) hr1
          have hr2r : (r : Real) <= (ethickness Real Q.carrier 2).toReal := by
            simpa using ENNReal.toReal_mono (htfin 2) hr2
          have hprod := Q.convex.ethickness_prod_le_volume
          norm_num [Finset.prod_range_succ, Metric.lt_volume_convexHull.c] at hprod
          have hprodr := ENNReal.toReal_mono Q.isCompact.measure_lt_top.ne hprod
          change ((6 : ENNReal)⁻¹ * (ethickness Real Q.carrier 0 * ethickness Real Q.carrier 1 *
            ethickness Real Q.carrier 2)).toReal <= (volume Q.carrier).toReal at hprodr
          simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hprodr
          have ht0 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 0)
          have ht1 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 1)
          have ht2 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 2)
          have hmul : (r : Real)^2 <= (ethickness Real Q.carrier 1).toReal *
              (ethickness Real Q.carrier 2).toReal := by
            nlinarith only [hr1r, hr2r, ht1, ht2, r.coe_nonneg,
              mul_nonneg (sub_nonneg.mpr hr1r) (sub_nonneg.mpr hr2r)]
          have ht0u : (ethickness Real Q.carrier 0).toReal <= 1296 * 1728^2 * (K : Real) := by
            have hmul0 := mul_le_mul_of_nonneg_left hmul ht0
            norm_num [r] at hmul0
            nlinarith only [hmul0, hprodr, hQr]
          have hdist := half_dist_le_ethickness_zero (𝕜 := Real) hxQ (hMQ hzM)
          have hdistr := ENNReal.toReal_mono (htfin 0) hdist
          rw [ENNReal.toReal_ofReal (by positivity)] at hdistr
          have hdistu : dist x z <= 2592 * 1728^2 * (K : Real) := by
            nlinarith only [hdistr, ht0u]
          have hK0 : (0 : Real) < K := by exact_mod_cast zero_lt_one.trans_le hK
          let lam : Real := (2 : Real)^50 * K
          have hlam : 0 < lam := by dsimp [lam]; positivity
          refine ⟨z + lam⁻¹ • (x - z), hball ?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_eq_norm]
            simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hlam), ← dist_eq_norm]
            apply (inv_mul_le_iff₀ hlam).2
            dsimp [r, lam]
            push_cast
            nlinarith only [hdistu, hK0]
          · change AffineMap.homothety z lam (z + lam⁻¹ • (x - z)) = x
            simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
              add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
            abel
        obtain ⟨c, b, len, hlen, hsub, hvol⟩ := M.convex.exists_boundingBox hM.ne'
          M.isCompact.measure_lt_top.ne (by simp : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3)
        let P := PrismNDim.mk' c b (fun i => (len i).toNNReal)
        have hMP : M.carrier <= P.carrier := by
          intro x hx
          rw [PrismNDim.mem_carrier_iff]
          intro i
          rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
            Real.coe_toNNReal _ (hlen i).le]
          simpa [vsub_eq_sub] using hsub x hx i
        have hPvol : volume P.carrier <= 48 * volume M.carrier := by
          rw [PrismNDim.volume_carrier, PrismNDim.thicknesses_mk']
          have hcoe : ∏ i, (((len i).toNNReal : NNReal) : ENNReal) =
              ENNReal.ofReal (∏ i, len i) := by
            rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hlen i).le)]
            exact Finset.prod_congr rfl fun i _ => rfl
          rw [hcoe]
          norm_num at hvol ⊢
          calc 8 * ENNReal.ofReal (∏ i, len i) <= 8 * (6 * volume M.carrier) :=
              mul_le_mul_left' hvol 8
            _ = 48 * volume M.carrier := by ring
        have hPv : 0 < volume P.carrier := hM.trans_le (measure_mono hMP)
        obtain ⟨A, hAcube, hAv⟩ := P.exists_affineEquiv_image_eq_cube hPv
        let N := M.mapAffine A
        have hNball : N.carrier <= Metric.closedBall 0 3 := by
          have hsub : N.carrier <= (PrismNDim.mk' 0 P.basis (fun _ => (1 : NNReal))).carrier := by
            change A '' M.carrier <= _
            rw [← hAcube]
            exact Set.image_mono hMP
          have hball := (PrismNDim.mk' (0 : EuclideanSpace Real (Fin 3)) P.basis
            (fun _ => (1 : NNReal))).carrier_subset_closedBall_euclidean
          norm_num [PrismNDim.center_mk', PrismNDim.thicknesses_mk'] at hball
          exact hsub.trans (hball.trans (Metric.closedBall_subset_closedBall (show Real.sqrt 3 <= (3 : Real) by
            rw [Real.sqrt_le_iff]
            norm_num)))
        have hNvol : (6 : ENNReal)⁻¹ <= volume N.carrier := by
          have hmfin : volume M.carrier ≠ ⊤ := M.isCompact.measure_lt_top.ne
          have hnfin : volume N.carrier ≠ ⊤ := N.isCompact.measure_lt_top.ne
          have hpfin : volume P.carrier ≠ ⊤ := P.toConvexSpaceBody.isCompact.measure_lt_top.ne
          have hpos := ENNReal.toReal_pos hM.ne' hmfin
          have hPn := hAv M.carrier
          change volume P.carrier * volume N.carrier = 2 ^ 3 * volume M.carrier at hPn
          have hPnr := congrArg ENNReal.toReal hPn
          norm_num only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hPnr
          norm_num at hPvol
          have hPvr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hmfin) hPvol
          change (volume P.carrier).toReal <= ((48 : ENNReal) * volume M.carrier).toReal at hPvr
          simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hPvr
          have hmul := mul_le_mul_of_nonneg_right hPvr (ENNReal.toReal_nonneg (a := volume N.carrier))
          apply (ENNReal.toReal_le_toReal (by simp) hnfin).mp
          norm_num only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
          nlinarith only [hpos, hPnr, hmul]
        obtain ⟨z, hzN, hz⟩ := hNormalized K hK N hNball hNvol
        have hzM : A.symm z ∈ M.carrier := by
          obtain ⟨w, hw, hwz⟩ := hzN
          simpa [← hwz] using hw
        refine ⟨A.symm z, hzM, ?_⟩
        intro Q hMQ hQv x hx
        have hNQ : N <= Q.mapAffine A := Set.image_mono hMQ
        have hQAv : volume (Q.mapAffine A).carrier <= (K : ENNReal) * volume N.carrier := by
          change volume (A '' Q.carrier) <= (K : ENNReal) * volume (A '' M.carrier)
          rw [volume_image_affineEquiv, volume_image_affineEquiv]
          simpa only [mul_assoc, mul_left_comm] using mul_le_mul_left' hQv (affineJacobian A)
        have hAx := hz (Q.mapAffine A) hNQ hQAv (Set.mem_image_of_mem A hx)
        obtain ⟨y, hyN, hyx⟩ := hAx
        obtain ⟨w, hw, hwy⟩ := hyN
        refine ⟨w, hw, A.injective ?_⟩
        rw [← hyx, ← hwy]
        simp only [AffineMap.homothety_apply]
        rw [A.map_vadd, map_smul]
        change (2 ^ 50 * (K : Real)) • A.toAffineMap.linear (w -ᵥ A.symm z) +ᵥ A (A.symm z) = _
        rw [A.toAffineMap.linearMap_vsub]
        simp
      let lam : NNReal := 2^50 * L
      have hlam : (1 : Real) <= lam := by
        have h : (1 : NNReal) <= lam := one_le_mul_of_one_le_of_one_le (by norm_num) hL
        exact_mod_cast h
      have hcost : (1 : ENNReal) <= ((384 * lam^3 : NNReal) : ENNReal) := by
        exact_mod_cast (show (1 : NNReal) <= 384 * lam^3 by
          apply one_le_mul_of_one_le_of_one_le (by norm_num)
          exact one_le_pow₀ (by exact_mod_cast hlam))
      have hJac0 := affineJacobian_ne_zero A
      have hJactop := affineJacobian_ne_top A
      have hpull (V : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) :
          affineJacobian A * volume (V.mapAffine A.symm).carrier = volume V.carrier := by
        rw [← volume_mapAffine, symm_mapAffine_mapAffine]
      intro V
      by_cases hex : ∃ i ∈ q, N i <= V
      · obtain ⟨i0, hi0, hiV⟩ := hex
        have hVpos : 0 < volume V.carrier := by
          have himg : 0 < volume ((B i0).mapAffine A).carrier := by
            rw [volume_mapAffine]
            exact ENNReal.mul_pos hJac0 (hBpos i0 hi0).ne'
          exact himg.trans_le (measure_mono ((hBN i0 hi0).trans hiV))
        obtain ⟨D, hVD, hhomD, hDvol⟩ := V.convex.exists_homothety_container hVpos.ne'
          V.isCompact.measure_lt_top.ne hlam
        refine ⟨D.toConvexSpaceBody.mapAffine A.symm, ?_, ?_⟩
        · apply (ENNReal.mul_le_mul_iff_right hJac0 hJactop).mp
          rw [hpull]
          have hcancel : affineJacobian A *
              (((384 * lam^3 : NNReal) : ENNReal) / affineJacobian A * volume V.carrier) =
              ((384 * lam^3 : NNReal) : ENNReal) * volume V.carrier := by
            rw [div_eq_mul_inv]
            calc _ = ((384 * lam^3 : NNReal) : ENNReal) *
                (affineJacobian A * (affineJacobian A)⁻¹) * volume V.carrier := by ring
              _ = _ := by rw [ENNReal.mul_inv_cancel hJac0 hJactop, mul_one]
          change volume D.carrier <= affineJacobian A *
            (((384 * lam^3 : NNReal) : ENNReal) / affineJacobian A * volume V.carrier)
          rw [hcancel]
          convert hDvol using 1 <;>
            norm_num [ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul,
              ENNReal.coe_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm]
          ring
        · intro i hi hiV x hx
          obtain ⟨z, hz, hOz⟩ := hEnlarge L hL (B i) (hBpos i hi)
          obtain ⟨y, hy, hyx⟩ := hOz (O i) (hBO i hi) (hOBvol i hi) hx
          have hzV : A z ∈ V.carrier := hiV (hBN i hi (Set.mem_image_of_mem A hz))
          have hyV : A y ∈ V.carrier := hiV (hBN i hi (Set.mem_image_of_mem A hy))
          have hAx : A x = (lam : Real) • (A y - A z) + A z := by
            rw [← hyx, AffineMap.homothety_apply, A.map_vadd, map_smul]
            change (2^50 * (L : Real)) • A.toAffineMap.linear (y -ᵥ z) +ᵥ A z = _
            rw [A.toAffineMap.linearMap_vsub]
            rfl
          exact ⟨A x, by rw [hAx]; exact hhomD _ hzV _ hyV, A.symm_apply_apply x⟩
      · refine ⟨V.mapAffine A.symm, ?_, ?_⟩
        · apply (ENNReal.mul_le_mul_iff_right hJac0 hJactop).mp
          rw [hpull]
          calc volume V.carrier <= ((384 * lam^3 : NNReal) : ENNReal) * volume V.carrier :=
              le_mul_of_one_le_left' hcost
            _ = _ := by
              change _ = affineJacobian A *
                (((384 * lam^3 : NNReal) : ENNReal) / affineJacobian A * volume V.carrier)
              rw [div_eq_mul_inv]
              calc _ = ((384 * lam^3 : NNReal) : ENNReal) *
                  (affineJacobian A * (affineJacobian A)⁻¹) * volume V.carrier := by
                    rw [ENNReal.mul_inv_cancel hJac0 hJactop, mul_one]
                _ = _ := by ring
        · intro i hi hiV
          exact (hex ⟨i, hi, hiV⟩).elim
    let F := E.factor O.chosen (O.outer_subset O.chosen_mem)
    let V0 := fun k => (Q.tube m k).toConvexSpaceBody
    let V1 := fun k => (Nrm.parent k).toConvexSpaceBody
    let H0 := fun part : Finset iota => part.convexHull_biUnion V0
    let Hr := fun part : Finset iota => (part ∩ P.parents).convexHull_biUnion V0
    let Hn := fun part : Finset iota => (part ∩ P.parents).convexHull_biUnion V1
    have htau : 0 < sourceTowerRadius delta M m := by
      unfold sourceTowerRadius
      split_ifs <;> positivity
    have hVpos : forall k, 0 < volume (V0 k).carrier := by
      intro k
      exact pos_iff_ne_zero.mpr (ML2Shaded.volume_carrier_ne_zero htau (Q.tube m k))
    have hparts : forall part, part ∈ P.keptParts -> part ∈ F.parts := P.kept_parts_subset
    have hpartsub : forall part, part ∈ P.keptParts -> part <= Q.fibre a m O.chosen :=
      fun part hp => F.toFinpartition.le (hparts part hp)
    have hrsub : forall part, part ∩ P.parents <= Q.fibre a m O.chosen :=
      fun part => Finset.inter_subset_right.trans P.parents_subset
    have hne : forall part, part ∈ P.keptParts -> (part ∩ P.parents).Nonempty :=
      P.kept_intersection_nonempty
    have hHrpos : forall part, part ∈ P.keptParts -> 0 < volume (Hr part).carrier := by
      intro part hp
      obtain ⟨k, hk⟩ := hne part hp
      exact (hVpos k).trans_le (measure_mono (Finset.le_convexHull_biUnion V0 hk))
    have hHrH0 : forall part, part ∈ P.keptParts -> Hr part <= H0 part := by
      intro part hp
      exact ((hne part hp).convexHull_biUnion_le_iff V0 _).mpr fun k hk =>
        Finset.le_convexHull_biUnion V0 (Finset.mem_inter.mp hk).1
    have hvolRet : forall part, part ∈ P.keptParts -> volume (H0 part).carrier <=
        (sourceZeroPlankConstant delta bias * Lsel : NNReal) * volume (Hr part).carrier := by
      intro part hp
      have hret : (∑ k ∈ part, volume (V0 k).carrier) <=
          (Lsel : ENNReal) * ∑ k ∈ part ∩ P.parents, volume (V0 k).carrier :=
        (P.part_volume_retention part hp).trans (by
          exact mul_le_mul_right' (ENNReal.coe_le_coe.mpr P.part_retention_bound) _)
      simpa only [ENNReal.coe_mul] using hRetained F (hparts part hp)
        Finset.inter_subset_left (hne part hp) (fun k _ => hVpos k) hret
    have hImage : forall part, part ∈ P.keptParts -> (Hr part).mapAffine Nrm.affine <= Hn part :=
      fun part hp => Nrm.part_image _ (hne part hp) (hrsub part)
    refine ⟨?_, ?_, hTest P.keptParts Hr H0 Hn Nrm.affine
      (sourceZeroPlankConstant delta bias * Lsel)
      (one_le_mul_of_one_le_of_one_le hC0 hL) hHrpos hHrH0 hvolRet hImage⟩
    · intro part hp
      have hnew : affineJacobian Nrm.affine * volume (Hr part).carrier <= volume (Hn part).carrier := by
        rw [← volume_mapAffine]
        exact measure_mono (hImage part hp)
      calc affineJacobian Nrm.affine * volume (H0 part).carrier <=
          affineJacobian Nrm.affine *
            ((sourceZeroPlankConstant delta bias * Lsel : NNReal) * volume (Hr part).carrier) :=
              mul_le_mul_left' (hvolRet part hp) _
        _ = ((sourceZeroPlankConstant delta bias * Lsel : NNReal) : ENNReal) *
            (affineJacobian Nrm.affine * volume (Hr part).carrier) := by ring
        _ <= _ := mul_le_mul_left' hnew _
    · intro part hp
      exact (Nrm.part_volume_upper _ (hne part hp) (hrsub part)).trans
        (mul_le_mul_left' (measure_mono (hHrH0 part hp)) _)
  have hRetained {iota : Type u} {r : Finset iota}
      {V : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3))} {C0 L : NNReal}
      (F : ConvexSpaceBody.Factorization r V C0) {part q : Finset iota}
      (hpart : part ∈ F.parts) (hq : q <= part) (hqne : q.Nonempty)
      (hpositive : forall i, i ∈ part -> 0 < volume (V i).carrier)
      (hret : (∑ i ∈ part, volume (V i).carrier) <=
        (L : ENNReal) * ∑ i ∈ q, volume (V i).carrier) :
      volume (part.convexHull_biUnion V).carrier <=
        (C0 : ENNReal) * L * volume (q.convexHull_biUnion V).carrier := by
    classical
    let v := volume (part.convexHull_biUnion V).carrier
    let w := volume (q.convexHull_biUnion V).carrier
    let s := ∑ i ∈ part, volume (V i).carrier
    let t := ∑ i ∈ q, volume (V i).carrier
    have hvtop : v ≠ ⊤ := (part.convexHull_biUnion V).isCompact'.measure_lt_top.ne
    have hwtop : w ≠ ⊤ := (q.convexHull_biUnion V).isCompact'.measure_lt_top.ne
    have hstop : s ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (V i).isCompact'.measure_lt_top.ne
    have httop : t ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (V i).isCompact'.measure_lt_top.ne
    obtain ⟨i0, hi0⟩ := hqne
    have hi0p := hq hi0
    have hvpos : 0 < v := (hpositive i0 hi0p).trans_le
      (measure_mono (Finset.le_convexHull_biUnion V hi0p))
    have hwpos : 0 < w := (hpositive i0 hi0p).trans_le
      (measure_mono (Finset.le_convexHull_biUnion V hi0))
    have hspos : 0 < s := by
      refine (hpositive i0 hi0p).trans_le ?_
      dsimp [s]
      exact Finset.single_le_sum (f := fun i => volume (V i).carrier) (fun _ _ => bot_le) hi0p
    have hden : t / w <= (C0 : ENNReal) * (s / v) := by
      have hqR := hq.trans (F.toFinpartition.le hpart)
      have hbound := (le_maxDensity q V (q.convexHull_biUnion V)).trans
        ((maxDensity_mono V hqR).trans (F.maxDensity_le_mul part hpart))
      rw [densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi),
        densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi)] at hbound
      exact hbound
    have hrreal : s.toReal <= L * t.toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top httop) hret
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using h
    have hdreal : t.toReal / w.toReal <= C0 * (s.toReal / v.toReal) := by
      have hden_top : (C0 : ENNReal) * (s / v) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.div_ne_top hstop hvpos.ne')
      have h := ENNReal.toReal_mono hden_top hden
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.coe_toReal] using h
    have hvreal : 0 < v.toReal := ENNReal.toReal_pos hvpos.ne' hvtop
    have hwreal : 0 < w.toReal := ENNReal.toReal_pos hwpos.ne' hwtop
    have hsreal : 0 < s.toReal := ENNReal.toReal_pos hspos.ne' hstop
    have hcross : t.toReal * v.toReal <= (C0 : Real) * s.toReal * w.toReal := by
      apply (div_le_iff₀ hwreal).mp at hdreal
      apply (mul_le_mul_iff_left₀ hvreal).2 at hdreal
      field_simp at hdreal
      nlinarith [hdreal]
    have hgoal : v.toReal <= (C0 : Real) * L * w.toReal := by
      have h1 := mul_le_mul_of_nonneg_right hrreal hvreal.le
      have h2 := mul_le_mul_of_nonneg_left hcross L.coe_nonneg
      nlinarith
    apply (ENNReal.toReal_le_toReal hvtop
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hwtop)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hgoal
  have hRetThickness (K B : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) (L : NNReal) (hL : 1 <= L)
      (hB : 0 < volume B.carrier) (hBK : B <= K)
      (hvol : volume K.carrier <= (L : ENNReal) * volume B.carrier) :
      forall j : Nat, ethickness Real K.carrier j <=
        ((2^50 * L : NNReal) : ENNReal) * ethickness Real B.carrier j := by
    have hEnlarge (K : NNReal) (hK : 1 <= K)
        (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) (hM : 0 < volume M.carrier) :
        ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
          M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
          Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
      have hNormalized (K : NNReal) (hK : 1 <= K)
          (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
          (hMball : M.carrier <= Metric.closedBall 0 3)
          (hMvol : (6 : ENNReal)⁻¹ <= volume M.carrier) :
          ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
            M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
            Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
        have hMvol' : ENNReal.ofReal (1 / 6 : Real) <= volume M.carrier := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 6)]
          norm_num
          exact hMvol
        obtain ⟨z, hzM, hzball⟩ := exists_closedBall_subset_of_le_volume (by norm_num : 1 <= 3)
          (by norm_num : (0 : Real) < 3) M hMball (by norm_num : (0 : Real) < 1 / 6) hMvol'
        norm_num at hzball
        let r : NNReal := 1 / 1728
        have hball : Metric.closedBall z (r : Real) <= M.carrier := by
          simpa [r] using hzball
        have hMu : volume M.carrier <= 216 := by
          have h := volume_le_prod_ethickness M.carrier
          have hth : forall n, ethickness Real M.carrier n <= (3 : NNReal) :=
            fun n => ethickness_le_of_subset_closedBall (𝕜 := Real) 3 hMball n
          norm_num [Finset.prod_range_succ] at h
          calc volume M.carrier <=
              8 * (ethickness Real M.carrier 0 * ethickness Real M.carrier 1 *
                ethickness Real M.carrier 2) := h
            _ <= 8 * ((3 : ENNReal) * 3 * 3) := by gcongr <;> exact hth _
            _ = 216 := by norm_num
        refine ⟨z, hzM, ?_⟩
        intro Q hMQ hQvol x hxQ
        have hQu : volume Q.carrier <= (216 : ENNReal) * K :=
          hQvol.trans (by simpa only [mul_comm] using mul_le_mul_left' hMu (K : ENNReal))
        have hr1 : (r : ENNReal) <= ethickness Real Q.carrier 1 :=
          (le_ethickness_closedBall (x := z) (n := 1) r (by norm_num)).trans
            (ethickness_monotone (hball.trans hMQ) 1)
        have hr2 : (r : ENNReal) <= ethickness Real Q.carrier 2 :=
          (le_ethickness_closedBall (x := z) (n := 2) r (by norm_num)).trans
            (ethickness_monotone (hball.trans hMQ) 2)
        have htfin : forall n, ethickness Real Q.carrier n ≠ ⊤ := by
          intro n
          change ethickness Real (Q : Set (EuclideanSpace Real (Fin 3))) n ≠ ⊤
          rw [ethickness_thickness' Q.isCompact.isBounded]
          exact ENNReal.ofReal_ne_top
        have hQr : (volume Q.carrier).toReal <= 216 * (K : Real) := by
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hQu
          simpa using this
        have hr1r : (r : Real) <= (ethickness Real Q.carrier 1).toReal := by
          simpa using ENNReal.toReal_mono (htfin 1) hr1
        have hr2r : (r : Real) <= (ethickness Real Q.carrier 2).toReal := by
          simpa using ENNReal.toReal_mono (htfin 2) hr2
        have hprod := Q.convex.ethickness_prod_le_volume
        norm_num [Finset.prod_range_succ, Metric.lt_volume_convexHull.c] at hprod
        have hprodr := ENNReal.toReal_mono Q.isCompact.measure_lt_top.ne hprod
        change ((6 : ENNReal)⁻¹ * (ethickness Real Q.carrier 0 * ethickness Real Q.carrier 1 *
          ethickness Real Q.carrier 2)).toReal <= (volume Q.carrier).toReal at hprodr
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hprodr
        have ht0 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 0)
        have ht1 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 1)
        have ht2 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 2)
        have hmul : (r : Real)^2 <= (ethickness Real Q.carrier 1).toReal *
            (ethickness Real Q.carrier 2).toReal := by
          nlinarith only [hr1r, hr2r, ht1, ht2, r.coe_nonneg,
            mul_nonneg (sub_nonneg.mpr hr1r) (sub_nonneg.mpr hr2r)]
        have ht0u : (ethickness Real Q.carrier 0).toReal <= 1296 * 1728^2 * (K : Real) := by
          have hmul0 := mul_le_mul_of_nonneg_left hmul ht0
          norm_num [r] at hmul0
          nlinarith only [hmul0, hprodr, hQr]
        have hdist := half_dist_le_ethickness_zero (𝕜 := Real) hxQ (hMQ hzM)
        have hdistr := ENNReal.toReal_mono (htfin 0) hdist
        rw [ENNReal.toReal_ofReal (by positivity)] at hdistr
        have hdistu : dist x z <= 2592 * 1728^2 * (K : Real) := by
          nlinarith only [hdistr, ht0u]
        have hK0 : (0 : Real) < K := by exact_mod_cast zero_lt_one.trans_le hK
        let lam : Real := (2 : Real)^50 * K
        have hlam : 0 < lam := by dsimp [lam]; positivity
        refine ⟨z + lam⁻¹ • (x - z), hball ?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hlam), ← dist_eq_norm]
          apply (inv_mul_le_iff₀ hlam).2
          dsimp [r, lam]
          push_cast
          nlinarith only [hdistu, hK0]
        · change AffineMap.homothety z lam (z + lam⁻¹ • (x - z)) = x
          simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
            add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
          abel
      obtain ⟨c, b, len, hlen, hsub, hvol⟩ := M.convex.exists_boundingBox hM.ne'
        M.isCompact.measure_lt_top.ne (by simp : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3)
      let P := PrismNDim.mk' c b (fun i => (len i).toNNReal)
      have hMP : M.carrier <= P.carrier := by
        intro x hx
        rw [PrismNDim.mem_carrier_iff]
        intro i
        rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
          Real.coe_toNNReal _ (hlen i).le]
        simpa [vsub_eq_sub] using hsub x hx i
      have hPvol : volume P.carrier <= 48 * volume M.carrier := by
        rw [PrismNDim.volume_carrier, PrismNDim.thicknesses_mk']
        have hcoe : ∏ i, (((len i).toNNReal : NNReal) : ENNReal) =
            ENNReal.ofReal (∏ i, len i) := by
          rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hlen i).le)]
          exact Finset.prod_congr rfl fun i _ => rfl
        rw [hcoe]
        norm_num at hvol ⊢
        calc 8 * ENNReal.ofReal (∏ i, len i) <= 8 * (6 * volume M.carrier) :=
            mul_le_mul_left' hvol 8
          _ = 48 * volume M.carrier := by ring
      have hPv : 0 < volume P.carrier := hM.trans_le (measure_mono hMP)
      obtain ⟨A, hAcube, hAv⟩ := P.exists_affineEquiv_image_eq_cube hPv
      let N := M.mapAffine A
      have hNball : N.carrier <= Metric.closedBall 0 3 := by
        have hsub : N.carrier <= (PrismNDim.mk' 0 P.basis (fun _ => (1 : NNReal))).carrier := by
          change A '' M.carrier <= _
          rw [← hAcube]
          exact Set.image_mono hMP
        have hball := (PrismNDim.mk' (0 : EuclideanSpace Real (Fin 3)) P.basis
          (fun _ => (1 : NNReal))).carrier_subset_closedBall_euclidean
        norm_num [PrismNDim.center_mk', PrismNDim.thicknesses_mk'] at hball
        exact hsub.trans (hball.trans (Metric.closedBall_subset_closedBall (show Real.sqrt 3 <= (3 : Real) by
          rw [Real.sqrt_le_iff]
          norm_num)))
      have hNvol : (6 : ENNReal)⁻¹ <= volume N.carrier := by
        have hmfin : volume M.carrier ≠ ⊤ := M.isCompact.measure_lt_top.ne
        have hnfin : volume N.carrier ≠ ⊤ := N.isCompact.measure_lt_top.ne
        have hpfin : volume P.carrier ≠ ⊤ := P.toConvexSpaceBody.isCompact.measure_lt_top.ne
        have hpos := ENNReal.toReal_pos hM.ne' hmfin
        have hPn := hAv M.carrier
        change volume P.carrier * volume N.carrier = 2 ^ 3 * volume M.carrier at hPn
        have hPnr := congrArg ENNReal.toReal hPn
        norm_num only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hPnr
        norm_num at hPvol
        have hPvr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hmfin) hPvol
        change (volume P.carrier).toReal <= ((48 : ENNReal) * volume M.carrier).toReal at hPvr
        simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hPvr
        have hmul := mul_le_mul_of_nonneg_right hPvr (ENNReal.toReal_nonneg (a := volume N.carrier))
        apply (ENNReal.toReal_le_toReal (by simp) hnfin).mp
        norm_num only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
        nlinarith only [hpos, hPnr, hmul]
      obtain ⟨z, hzN, hz⟩ := hNormalized K hK N hNball hNvol
      have hzM : A.symm z ∈ M.carrier := by
        obtain ⟨w, hw, hwz⟩ := hzN
        simpa [← hwz] using hw
      refine ⟨A.symm z, hzM, ?_⟩
      intro Q hMQ hQv x hx
      have hNQ : N <= Q.mapAffine A := Set.image_mono hMQ
      have hQAv : volume (Q.mapAffine A).carrier <= (K : ENNReal) * volume N.carrier := by
        change volume (A '' Q.carrier) <= (K : ENNReal) * volume (A '' M.carrier)
        rw [volume_image_affineEquiv, volume_image_affineEquiv]
        simpa only [mul_assoc, mul_left_comm] using mul_le_mul_left' hQv (affineJacobian A)
      have hAx := hz (Q.mapAffine A) hNQ hQAv (Set.mem_image_of_mem A hx)
      obtain ⟨y, hyN, hyx⟩ := hAx
      obtain ⟨w, hw, hwy⟩ := hyN
      refine ⟨w, hw, A.injective ?_⟩
      rw [← hyx, ← hwy]
      simp only [AffineMap.homothety_apply]
      rw [A.map_vadd, map_smul]
      change (2 ^ 50 * (K : Real)) • A.toAffineMap.linear (w -ᵥ A.symm z) +ᵥ A (A.symm z) = _
      rw [A.toAffineMap.linearMap_vsub]
      simp
    obtain ⟨z, hz, hgeom⟩ := hEnlarge L hL B hB
    have hn : ‖((2 : Real)^50 * L)‖₊ = (2^50 * L : NNReal) := by
      apply NNReal.coe_injective
      rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      push_cast
      rfl
    intro j
    calc ethickness Real K.carrier j <=
        ethickness Real (AffineMap.homothety z ((2 : Real)^50 * L) '' B.carrier) j :=
          ethickness_monotone (hgeom K hBK hvol) j
      _ <= _ := by
        have h := ethickness_homothety_image_le z ((2 : Real)^50 * L) B.carrier j
        change ethickness Real (AffineMap.homothety z ((2 : Real)^50 * L) '' B.carrier) j <=
          ((‖((2 : Real)^50 * L)‖₊ : NNReal) : ENNReal) * ethickness Real B.carrier j at h
        rw [hn] at h
        exact h
  have hDimensionTransport (K B N : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
      (G L D theta aw bw cw : NNReal) (hG : 1 <= G) (hL : 1 <= L) (hD : 1 <= D)
      (htheta : 0 < theta) (hraw : SourceZeroFactorDimensions D aw bw cw K)
      (hBK : B <= K)
      (hret : forall j : Nat, j = 1 ∨ j = 2 -> ethickness Real K.carrier j <=
        (L : ENNReal) * ethickness Real B.carrier j)
      (hlower : forall j : Nat, j = 1 ∨ j = 2 ->
        ethickness Real B.carrier j / ((G : ENNReal) * theta) <= ethickness Real N.carrier j)
      (hupper : forall j : Nat, j = 1 ∨ j = 2 ->
        ethickness Real N.carrier j <= (G : ENNReal) / theta * ethickness Real B.carrier j)
      (hzeroLower : (2 : ENNReal)⁻¹ <= ethickness Real N.carrier 0)
      (hzeroUpper : ethickness Real N.carrier 0 <= 1) :
      SourceZeroFactorDimensions (2 * G * D * L) (aw / theta) (bw / theta) 1 N := by
    let Cdim : NNReal := 2 * G * D * L
    have hG0 : G ≠ 0 := (zero_lt_one.trans_le hG).ne'
    have hD0 : D ≠ 0 := (zero_lt_one.trans_le hD).ne'
    have hL0 : L ≠ 0 := (zero_lt_one.trans_le hL).ne'
    have hCdim : 2 <= Cdim := by
      calc 2 = 2 * 1 * 1 * 1 := by norm_num
        _ <= 2 * G * D * L := by gcongr
    have hCdim0 : Cdim ≠ 0 := (by norm_num : (0 : NNReal) < 2).trans_le hCdim |>.ne'
    have hscalar (x a b n : ENNReal)
        (hxa : (D : ENNReal)⁻¹ * x <= a) (hab : a <= (L : ENNReal) * b)
        (hbn : b / ((G : ENNReal) * theta) <= n) :
        (Cdim : ENNReal)⁻¹ * (x / theta) <= n := by
      have hbn' := (ENNReal.div_le_iff
        (mul_ne_zero (ENNReal.coe_ne_zero.mpr hG0) (ENNReal.coe_ne_zero.mpr htheta.ne'))
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)).mp hbn
      have hdiv : x / (theta : ENNReal) / Cdim = x / ((theta : ENNReal) * Cdim) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr htheta.ne')) (Or.inl ENNReal.coe_ne_top)]
        ring
      rw [mul_comm (Cdim : ENNReal)⁻¹, ← div_eq_mul_inv, hdiv]
      apply (ENNReal.div_le_iff
        (mul_ne_zero (ENNReal.coe_ne_zero.mpr htheta.ne') (ENNReal.coe_ne_zero.mpr hCdim0))
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)).mpr
      calc x = (D : ENNReal) * ((D : ENNReal)⁻¹ * x) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hD0) ENNReal.coe_ne_top, one_mul]
        _ <= (D : ENNReal) * ((L : ENNReal) * (n * ((G : ENNReal) * theta))) := by
          exact mul_le_mul_left' (hxa.trans (hab.trans (mul_le_mul_left' hbn' _))) _
        _ <= 2 * ((D : ENNReal) * ((L : ENNReal) * (n * ((G : ENNReal) * theta)))) :=
          le_mul_of_one_le_left' (by norm_num)
        _ = _ := by simp only [Cdim, ENNReal.coe_mul, ENNReal.coe_ofNat]; ring
    have hupper' (x : NNReal) (j : Nat) (hj : j = 1 ∨ j = 2)
        (hx : ethickness Real K.carrier j <= (D : ENNReal) * x) :
        ethickness Real N.carrier j <= (Cdim : ENNReal) * (x / theta) := by
      have hGD : G * D <= Cdim := by
        calc G * D <= 2 * (G * D) := le_mul_of_one_le_left' (by norm_num)
          _ <= 2 * (G * D) * L := le_mul_of_one_le_right' hL
          _ = _ := by dsimp [Cdim]; ring
      calc ethickness Real N.carrier j <=
          (G : ENNReal) / theta * ((D : ENNReal) * x) :=
            (hupper j hj).trans (mul_le_mul_left'
              ((ethickness_monotone hBK j).trans hx) _)
        _ = ((G * D : NNReal) : ENNReal) * (x / theta) := by
          rw [ENNReal.coe_mul, div_eq_mul_inv, div_eq_mul_inv]
          ring
        _ <= _ := mul_le_mul_right' (ENNReal.coe_le_coe.mpr hGD) _
    have hlow' (x : NNReal) (j : Nat) (hj : j = 1 ∨ j = 2)
        (hx : (D : ENNReal)⁻¹ * x <= ethickness Real K.carrier j) :
        (Cdim : ENNReal)⁻¹ * ((x / theta : NNReal) : ENNReal) <= ethickness Real N.carrier j := by
      rw [ENNReal.coe_div htheta.ne']
      exact hscalar x _ _ _ hx (hret j hj) (hlower j hj)
    refine ⟨?_, ?_, hlow' bw 1 (Or.inl rfl) hraw.2.2.1, ?_,
      hlow' aw 2 (Or.inr rfl) hraw.2.2.2.2.1, ?_⟩
    · simp only [ENNReal.coe_one, mul_one]
      exact (ENNReal.inv_le_inv.mpr (by exact_mod_cast hCdim)).trans hzeroLower
    · simp only [ENNReal.coe_one, mul_one]
      exact hzeroUpper.trans (by exact_mod_cast (by norm_num : (1 : NNReal) <= 2).trans hCdim)
    · rw [ENNReal.coe_div htheta.ne']
      exact hupper' bw 1 (Or.inl rfl) hraw.2.2.2.1
    · rw [ENNReal.coe_div htheta.ne']
      exact hupper' aw 2 (Or.inr rfl) hraw.2.2.2.2.2
  have hSimilarity (K N : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
      (D aw bw cw : NNReal) (hD : 1 <= D)
      (hK : SourceZeroFactorDimensions D aw bw cw K)
      (hN : SourceZeroFactorDimensions D aw bw cw N) :
      ethickness Real K.carrier <= (D^2) • ethickness Real N.carrier := by
    have hD0 : (D : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hD).ne'
    have hscalar (a b x : ENNReal) (ha : a <= (D : ENNReal) * x)
        (hb : (D : ENNReal)⁻¹ * x <= b) : a <= ((D^2 : NNReal) : ENNReal) * b := by
      calc a <= (D : ENNReal) * x := ha
        _ = ((D^2 : NNReal) : ENNReal) * ((D : ENNReal)⁻¹ * x) := by
          rw [ENNReal.coe_pow, pow_two]
          calc _ = (D : ENNReal) * ((D : ENNReal) * (D : ENNReal)⁻¹) * x := by
                rw [ENNReal.mul_inv_cancel hD0 ENNReal.coe_ne_top, mul_one]
            _ = _ := by ring
        _ <= _ := mul_le_mul_left' hb _
    intro j
    change ethickness Real K.carrier j <= ((D^2 : NNReal) : ENNReal) * ethickness Real N.carrier j
    by_cases h0 : j = 0
    · subst j
      exact hscalar _ _ _ hK.2.1 hN.1
    by_cases h1 : j = 1
    · subst j
      exact hscalar _ _ _ hK.2.2.2.1 hN.2.2.1
    by_cases h2 : j = 2
    · subst j
      exact hscalar _ _ _ hK.2.2.2.2.2 hN.2.2.2.2.1
    have hj : Module.finrank Real (EuclideanSpace Real (Fin 3)) <= j := by simp; omega
    simp only [ethickness_eq_zero_of_finrank_le hj, mul_zero, le_rfl]
  have hDimensionMono (K : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
      (D D' aw bw cw : NNReal) (hDD' : D <= D')
      (hK : SourceZeroFactorDimensions D aw bw cw K) :
      SourceZeroFactorDimensions D' aw bw cw K := by
    have h : (D : ENNReal) <= D' := ENNReal.coe_le_coe.mpr hDD'
    have hi := ENNReal.inv_le_inv.mpr h
    exact ⟨(mul_le_mul_right' hi _).trans hK.1,
      hK.2.1.trans (mul_le_mul_right' h _),
      (mul_le_mul_right' hi _).trans hK.2.2.1,
      hK.2.2.2.1.trans (mul_le_mul_right' h _),
      (mul_le_mul_right' hi _).trans hK.2.2.2.2.1,
      hK.2.2.2.2.2.trans (mul_le_mul_right' h _)⟩
  have hAdapterDimensions (K : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
      (D aw bw : NNReal) (hD : 1 <= D)
      (hK : SourceZeroFactorDimensions D aw bw 1 K)
      (hlow : (2 : ENNReal)⁻¹ <= ethickness Real K.carrier 0)
      (hup : ethickness Real K.carrier 0 <= 1) :
      SourceZeroFactorDimensions (2*D) aw bw D K := by
    have hD0 : (D : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hD).ne'
    have hmul : (D : ENNReal) <= ((2*D : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (le_mul_of_one_le_left' (by norm_num))
    have hinv := ENNReal.inv_le_inv.mpr hmul
    refine ⟨?_, ?_, (mul_le_mul_right' hinv _).trans hK.2.2.1,
      hK.2.2.2.1.trans (mul_le_mul_right' hmul _),
      (mul_le_mul_right' hinv _).trans hK.2.2.2.2.1,
      hK.2.2.2.2.2.trans (mul_le_mul_right' hmul _)⟩
    · have heq : ((2*D : NNReal) : ENNReal)⁻¹ * D = (2 : ENNReal)⁻¹ := by
        rw [ENNReal.coe_mul]
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        rw [mul_assoc, ENNReal.inv_mul_cancel hD0 ENNReal.coe_ne_top, mul_one]
        norm_num
      rw [heq]
      exact hlow
    · apply hup.trans
      have hd : (1 : ENNReal) <= D := by exact_mod_cast hD
      have h2d : (1 : ENNReal) <= ((2*D : NNReal) : ENNReal) := hd.trans hmul
      exact one_le_mul_of_one_le_of_one_le h2d hd
  have hCapture {iota : Type u} {s : Finset iota}
      (V N : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
      (C0 Cgeom L : NNReal) (hCgeom : 1 <= Cgeom)
      (F : ConvexSpaceBody.Factorization s V C0)
      (A : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3))
      (r part q : Finset iota) (hr : r <= s) (hp : part ∈ F.parts)
      (hqp : q <= part) (hqr : q <= r) (hq : q.Nonempty)
      (hpositive : forall i, i ∈ part -> 0 < volume (V i).carrier)
      (hsub : forall i, i ∈ r -> (V i).mapAffine A <= N i)
      (hvol : forall i, i ∈ r -> volume (N i).carrier <= (Cgeom : ENNReal) * volume ((V i).mapAffine A).carrier)
      (hret : (∑ i ∈ part, volume (V i).carrier) <= (L : ENNReal) * ∑ i ∈ q, volume (V i).carrier)
      (hhull : volume (q.convexHull_biUnion N).carrier <= (Cgeom : ENNReal) * affineJacobian A *
        volume (part.convexHull_biUnion V).carrier) :
      maxDensity r N <= (Cgeom^2 * C0 * L : NNReal) *
        densityIn q N (q.convexHull_biUnion N) := by
    classical
    have hRatio {s t u v w J G L : ENNReal}
        (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) (hw0 : w ≠ 0) (hwtop : w ≠ ⊤)
        (hs : s <= L * t) (hu : J * t <= u) (hw : w <= G * J * v) :
        s / v <= G * L * (u / w) := by
      apply (ENNReal.div_le_iff hv0 hvtop).mpr
      apply (ENNReal.mul_le_mul_iff_left hw0 hwtop).mp
      calc s * w <= (L * t) * (G * J * v) := mul_le_mul' hs hw
        _ = G * L * (J * t) * v := by ring
        _ <= G * L * u * v := by gcongr
        _ = (G * L * (u / w) * v) * w := by
          rw [div_eq_mul_inv]
          calc _ = (G * L * u * v) * (w⁻¹ * w) := by rw [ENNReal.inv_mul_cancel hw0 hwtop, mul_one]
            _ = _ := by ring
    have hmax : maxDensity r N <= (Cgeom : ENNReal) * maxDensity s V := by
      apply (maxDensity_le_iff r N _).mpr
      intro K
      calc densityIn r N K <= (Cgeom : ENNReal) * densityIn r (fun i => (V i).mapAffine A) K :=
          Tube.densityIn_le_of_comparable hCgeom r (fun i => (V i).mapAffine A) N hsub hvol K
        _ <= (Cgeom : ENNReal) * maxDensity r (fun i => (V i).mapAffine A) :=
          mul_le_mul_left' (le_maxDensity r (fun i => (V i).mapAffine A) K) _
        _ = (Cgeom : ENNReal) * maxDensity r V := by rw [maxDensity_mapAffine]
        _ <= (Cgeom : ENNReal) * maxDensity s V := mul_le_mul_left' (maxDensity_mono V hr) _
    obtain ⟨i0, hi0⟩ := hq
    have hV0 : 0 < volume (part.convexHull_biUnion V).carrier :=
      (hpositive i0 (hqp hi0)).trans_le (measure_mono (Finset.le_convexHull_biUnion V (hqp hi0)))
    have hN0 : 0 < volume (q.convexHull_biUnion N).carrier := by
      have himg : 0 < volume ((V i0).mapAffine A).carrier := by
        rw [volume_mapAffine]
        exact ENNReal.mul_pos (affineJacobian_ne_zero A) (hpositive i0 (hqp hi0)).ne'
      exact himg.trans_le (measure_mono ((hsub i0 (hqr hi0)).trans
        (Finset.le_convexHull_biUnion N hi0)))
    have hsum : affineJacobian A * (∑ i ∈ q, volume (V i).carrier) <=
        ∑ i ∈ q, volume (N i).carrier := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [← volume_mapAffine]
      exact measure_mono (hsub i (hqr hi))
    have hden : densityIn part V (part.convexHull_biUnion V) <= (Cgeom : ENNReal) * L *
        densityIn q N (q.convexHull_biUnion N) := by
      rw [densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi),
        densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion N hi)]
      exact hRatio hV0.ne' (part.convexHull_biUnion V).isCompact.measure_lt_top.ne
        hN0.ne' (q.convexHull_biUnion N).isCompact.measure_lt_top.ne hret hsum hhull
    calc maxDensity r N <= (Cgeom : ENNReal) * maxDensity s V := hmax
      _ <= (Cgeom : ENNReal) * ((C0 : ENNReal) * densityIn part V (part.convexHull_biUnion V)) :=
        mul_le_mul_left' (F.maxDensity_le_mul part hp) _
      _ <= (Cgeom : ENNReal) * ((C0 : ENNReal) * ((Cgeom : ENNReal) * L *
          densityIn q N (q.convexHull_biUnion N))) := by gcongr
      _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_pow]; ring
  have hKTTransport {iota : Type u} (q : Finset iota)
      (O N : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
      (J : ENNReal) (hJ0 : J ≠ 0) (hJtop : J ≠ ⊤)
      (Cgeom Ctest C0 : NNReal)
      (hKT : IsKatzTao q O C0)
      (hvolume : forall i, i ∈ q -> volume (N i).carrier <= (Cgeom : ENNReal) * J * volume (O i).carrier)
      (hTest : forall V : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
        exists W : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
          volume W.carrier <= (Ctest : ENNReal) / J * volume V.carrier ∧
          forall i, i ∈ q -> N i <= V -> O i <= W) :
      IsKatzTao q N (Cgeom * Ctest * C0 : NNReal) := by
    classical
    rw [isKatzTao_iff]
    intro V
    obtain ⟨W, hWvol, hW⟩ := hTest V
    have hfilter : q.filter (fun i => N i <= V) <= q.filter (fun i => O i <= W) := by
      intro i hi
      obtain ⟨hiq, hiV⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hiq, hW i hiq hiV⟩
    calc (∑ i ∈ q with N i <= V, volume (N i).carrier) <=
        ∑ i ∈ q with N i <= V, (Cgeom : ENNReal) * J * volume (O i).carrier :=
          Finset.sum_le_sum fun i hi => hvolume i (Finset.mem_filter.mp hi).1
      _ = (Cgeom : ENNReal) * J * ∑ i ∈ q with N i <= V, volume (O i).carrier := by
        rw [Finset.mul_sum]
      _ <= (Cgeom : ENNReal) * J * ∑ i ∈ q with O i <= W, volume (O i).carrier :=
        mul_le_mul_left' (Finset.sum_le_sum_of_subset hfilter) _
      _ <= (Cgeom : ENNReal) * J * ((C0 : ENNReal) * volume W.carrier) :=
        mul_le_mul_left' ((isKatzTao_iff q O C0).mp hKT W) _
      _ <= (Cgeom : ENNReal) * J * ((C0 : ENNReal) * ((Ctest : ENNReal) / J * volume V.carrier)) := by
        gcongr
      _ = (Cgeom * Ctest * C0 : NNReal) * volume V.carrier := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, div_eq_mul_inv]
        calc _ = ((Cgeom : ENNReal) * Ctest * C0) * (J * J⁻¹) * volume V.carrier := by ring
          _ = _ := by rw [ENNReal.mul_inv_cancel hJ0 hJtop, mul_one]
  have hPartition {iota : Type u} {s : Finset iota} (F : Finpartition s)
      (p : Finset (Finset iota)) (r : Finset iota)
      (hp : p <= F.parts)
      (hne : forall part, part ∈ p -> (part ∩ r).Nonempty)
      (hcover : p.biUnion (fun part => part ∩ r) = r) :
      (Set.InjOn (fun part => part ∩ r) (p : Set (Finset iota))) ∧
      exists P : Finpartition r, P.parts = p.image (fun part => part ∩ r) := by
    classical
    have hinj : Set.InjOn (fun part => part ∩ r) (p : Set (Finset iota)) := by
      intro x hx y hy hxy
      change x ∩ r = y ∩ r at hxy
      by_contra hne'
      have hd := F.disjoint (hp hx) (hp hy) hne'
      obtain ⟨i, hi⟩ := hne x hx
      have hiy : i ∈ y ∩ r := by rwa [← hxy]
      exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hiy).1
    refine ⟨hinj, ⟨{ parts := p.image (fun part => part ∩ r), supIndep := ?_, sup_parts := ?_, bot_notMem := ?_ }, rfl⟩⟩
    · apply Finset.supIndep_iff_pairwiseDisjoint.mpr
      intro x hx y hy hxy
      obtain ⟨px, hpx, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨py, hpy, rfl⟩ := Finset.mem_image.mp hy
      exact (F.disjoint (hp hpx) (hp hpy) (fun h => hxy (h ▸ rfl))).mono
        Finset.inter_subset_left Finset.inter_subset_left
    · simpa [Finset.sup_image, Finset.sup_eq_biUnion] using hcover
    · intro hempty
      obtain ⟨part, hp', heq⟩ := Finset.mem_image.mp hempty
      exact (hne part hp').ne_empty heq
  have hAdapter (D : NNReal) (hD : 1 <= D) :
        forall {iota : Type u} {rho : NNReal} (_hrho : 0 < rho)
          (r : Finset iota) (R : iota -> Tube rho (EuclideanSpace Real (Fin 3)))
          (C0 aw bw cw : NNReal), r.Nonempty -> 0 < aw -> aw <= bw -> bw <= cw ->
        (forall i, i ∈ r -> (R i).carrier <= Metric.closedBall 0 1) ->
        forall F : ConvexSpaceBody.Factorization r (fun i => (R i).toConvexSpaceBody) C0,
        (forall part, part ∈ F.parts -> SourceZeroFactorDimensions D aw bw cw
          (part.convexHull_biUnion (fun i => (R i).toConvexSpaceBody))) ->
        exists (short middle Cw : NNReal) (hsm : short <= middle) (hm1 : middle <= 1),
          rho <= short /\ 1 <= Cw /\ Cw <= (64 * D ^ 2) /\ short / middle <= (64 * D ^ 2) * (aw / bw) /\
          exists Fz : Kakeya.GlobalPlankFactorization Cw short middle hsm hm1 r
              (fun i => (R i).toConvexSpaceBody) C0,
            Fz.toFactorization = F := by
    classical
    have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
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
  let C0 := sourceZeroPlankConstant delta bias
  let F := E.factor O.chosen (O.outer_subset O.chosen_mem)
  let V0 := fun k => (Q.tube m k).toConvexSpaceBody
  let V1 := fun k => (Nrm.parent k).toConvexSpaceBody
  let H0 := fun part : Finset iota => part.convexHull_biUnion V0
  let Hr := fun part : Finset iota => (part ∩ P.parents).convexHull_biUnion V0
  let Hn := fun part : Finset iota => (part ∩ P.parents).convexHull_biUnion V1
  have htau : 0 < sourceTowerRadius delta M m := by
    unfold sourceTowerRadius
    split_ifs <;> positivity
  have hVpos : forall k, 0 < volume (V0 k).carrier := by
    intro k
    exact pos_iff_ne_zero.mpr (ML2Shaded.volume_carrier_ne_zero htau (Q.tube m k))
  have hparts : forall part, part ∈ P.keptParts -> part ∈ F.parts := P.kept_parts_subset
  have hpartsub : forall part, part ∈ P.keptParts -> part <= Q.fibre a m O.chosen :=
    fun part hp => F.toFinpartition.le (hparts part hp)
  have hrsub : forall part, part ∩ P.parents <= Q.fibre a m O.chosen :=
    fun part => Finset.inter_subset_right.trans P.parents_subset
  have hne : forall part, part ∈ P.keptParts -> (part ∩ P.parents).Nonempty := P.kept_intersection_nonempty
  have hHrpos : forall part, part ∈ P.keptParts -> 0 < volume (Hr part).carrier := by
    intro part hp
    obtain ⟨k, hk⟩ := hne part hp
    exact (hVpos k).trans_le (measure_mono (Finset.le_convexHull_biUnion V0 hk))
  have hHrH0 : forall part, part ∈ P.keptParts -> Hr part <= H0 part := by
    intro part hp
    exact ((hne part hp).convexHull_biUnion_le_iff V0 _).mpr fun k hk =>
      Finset.le_convexHull_biUnion V0 (Finset.mem_inter.mp hk).1
  have hC0 : 1 <= C0 := by
    obtain ⟨part, hp⟩ := P.kept_parts_nonempty
    have hpos : 0 < volume (H0 part).carrier :=
      (hHrpos part hp).trans_le (measure_mono (hHrH0 part hp))
    have h := (one_le_maxDensity (s := F.parts) (W := H0) ⟨part, hparts part hp, hpos⟩).trans F.isKatzTao
    exact_mod_cast h
  let k := C0 * Lsel
  let lam : NNReal := 2^50 * k
  let DD : NNReal := 2 * Cgeom * D * lam
  let Ctest : NNReal := 384 * lam^3
  let Czero : NNReal := 2^200 * Cgeom^2 * D^2 * k^4
  let H := sourceEccentricTransportCost A Lsel 4 delta bias
  obtain ⟨hDD, hCzero, hWideCost, hKTCost, hCaptureCost, hCzeroH, _, _⟩ := hCosts Cgeom D C0 Lsel hC hD hC0 hL
  change 1 <= DD at hDD
  change 1 <= Czero at hCzero
  change 256 * DD^2 <= Czero at hWideCost
  change Ctest * Cgeom * C0 <= Czero at hKTCost
  change Cgeom^2 * C0 * Lsel <= Czero at hCaptureCost
  change Czero <= H at hCzeroH
  have hk : 1 <= k := one_le_mul_of_one_le_of_one_le hC0 hL
  have hlam : 1 <= lam := one_le_mul_of_one_le_of_one_le (by norm_num) hk
  have hDDsq : DD^2 <= Czero := (le_mul_of_one_le_left' (by norm_num : (1 : NNReal) <= 256)).trans hWideCost
  have hDDCzero : DD <= Czero := (show DD <= DD^2 by simpa using pow_le_pow_right₀ hDD (by norm_num : 1 <= 2)).trans hDDsq
  have hDDH : DD <= H := hDDCzero.trans hCzeroH
  have hH : 1 <= H := hCzero.trans hCzeroH
  obtain ⟨hOldVol, hNewVol, hTestBody⟩ := hGeometry hdelta Q O Nrm E hL hC0 P
  have hRetMass : forall part, part ∈ P.keptParts ->
      (∑ i ∈ part, volume (V0 i).carrier) <= (Lsel : ENNReal) * ∑ i ∈ part ∩ P.parents, volume (V0 i).carrier := by
    intro part hp
    exact (P.part_volume_retention part hp).trans
      (mul_le_mul_right' (ENNReal.coe_le_coe.mpr P.part_retention_bound) _)
  have hRetVol : forall part, part ∈ P.keptParts -> volume (H0 part).carrier <=
      (k : ENNReal) * volume (Hr part).carrier := by
    intro part hp
    simpa only [k, ENNReal.coe_mul] using hRetained F (hparts part hp) Finset.inter_subset_left
      (hne part hp) (fun k _ => hVpos k) (hRetMass part hp)
  have hThinRet : forall part, part ∈ P.keptParts -> forall j : Nat,
      ethickness Real (H0 part).carrier j <= (lam : ENNReal) * ethickness Real (Hr part).carrier j := by
    intro part hp
    exact hRetThickness (H0 part) (Hr part) k hk (hHrpos part hp) (hHrH0 part hp) (hRetVol part hp)
  have hBall : forall part, part ∈ P.keptParts -> (Hn part).carrier <= Metric.closedBall 0 1 := by
    intro part hp
    apply ((hne part hp).convexHull_biUnion_subset_iff V1 (convex_closedBall (0 : EuclideanSpace Real (Fin 3)) 1).isConvexSet).mpr
    intro i hi
    exact P.parent_ball i (Finset.mem_inter.mp hi).2
  have hUpper : forall part, part ∈ P.keptParts -> forall j, ethickness Real (Hn part).carrier j <= 1 := by
    intro part hp j
    simpa using ethickness_le_of_subset_closedBall (𝕜 := Real) 1 (hBall part hp) j
  have hZero : forall part, part ∈ P.keptParts -> (2 : ENNReal)⁻¹ <= ethickness Real (Hn part).carrier 0 := by
    intro part hp
    obtain ⟨i, hi⟩ := hne part hp
    change (2 : ENNReal)⁻¹ <= ethickness Real
      ((part ∩ P.parents).convexHull_biUnion V1 : Set (EuclideanSpace Real (Fin 3))) 0
    simpa only [one_div] using (Tube.le_ethickness_zero (Nrm.parent i)).trans
      (ethickness_monotone (Finset.le_convexHull_biUnion V1 hi) 0)
  have hDimensions : forall part, part ∈ P.keptParts ->
      SourceZeroFactorDimensions DD (aw / sourceTowerRadius delta M a) (bw / sourceTowerRadius delta M a) 1 (Hn part) := by
    intro part hp
    exact hDimensionTransport (H0 part) (Hr part) (Hn part) Cgeom lam D (sourceTowerRadius delta M a) aw bw cw
      hC hlam hD Nrm.ambient_pos (E.dimensions _ _ _ (hparts part hp)) (hHrH0 part hp)
      (fun j _ => hThinRet part hp j)
      (Nrm.part_thickness_lower _ (hne part hp) (hrsub part))
      (Nrm.part_thickness_upper _ (hne part hp) (hrsub part)) (hZero part hp) (hUpper part hp 0)
  obtain ⟨hinj, Fp, hFp⟩ := hPartition F.toFinpartition P.keptParts P.parents P.kept_parts_subset
    P.kept_intersection_nonempty P.kept_cover
  have hKTparts : IsKatzTao P.keptParts Hn Czero := by
    have hKT := hKTTransport P.keptParts H0 Hn (affineJacobian Nrm.affine)
      Nrm.jacobian_pos.ne' Nrm.jacobian_finite.ne Cgeom Ctest C0 (F.isKatzTao.subset P.kept_parts_subset)
      hNewVol hTestBody
    apply hKT.mono
    exact ENNReal.coe_le_coe.mpr (by simpa only [mul_comm Cgeom Ctest] using hKTCost)
  have hKTactual : IsKatzTao Fp.parts (fun part => part.convexHull_biUnion V1) Czero := by
    rw [isKatzTao_iff]
    intro V
    rw [hFp, Finset.filter_image, Finset.sum_image]
    · exact (isKatzTao_iff P.keptParts Hn Czero).mp hKTparts V
    · intro x hx y hy hxy
      exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  let Fnew : ConvexSpaceBody.Factorization P.parents V1 Czero :=
    { toFinpartition := Fp
      isKatzTao := hKTactual
      maxDensity_le_mul := by
        intro part hp
        rw [hFp] at hp
        obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hp
        have hcap := hCapture V0 V1 C0 Cgeom Lsel hC F Nrm.affine P.parents old (old ∩ P.parents)
          P.parents_subset (hparts old hold) Finset.inter_subset_left Finset.inter_subset_right
          (hne old hold) (fun i _ => hVpos i)
          (fun i hi => Nrm.parent_image i (P.parents_subset hi))
          (fun i hi => Nrm.parent_volume i (P.parents_subset hi))
          (hRetMass old hold) (hNewVol old hold)
        exact hcap.trans (mul_le_mul_right' (ENNReal.coe_le_coe.mpr hCaptureCost) _)
      simDims := by
        intro part hp part' hp'
        rw [hFp] at hp hp'
        obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨old', hold', rfl⟩ := Finset.mem_image.mp hp'
        have hs := hSimilarity (Hn old) (Hn old') DD (aw / sourceTowerRadius delta M a)
          (bw / sourceTowerRadius delta M a) 1 hDD (hDimensions old hold) (hDimensions old' hold')
        intro j
        exact (hs j).trans (mul_le_mul_right' (ENNReal.coe_le_coe.mpr hDDsq) _) }
  have hbw : bw / sourceTowerRadius delta M a <= DD := by
    obtain ⟨part, hp⟩ := P.kept_parts_nonempty
    have h := (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hDD).ne') ENNReal.coe_ne_top).mp
      ((hDimensions part hp).2.2.1.trans (hUpper part hp 1))
    simpa only [mul_one, ENNReal.coe_le_coe] using h
  have hDa : 1 <= 2*DD := hDD.trans (le_mul_of_one_le_left' (by norm_num))
  have hDimAdapter : forall part, part ∈ Fnew.parts -> SourceZeroFactorDimensions (2*DD)
      (aw / sourceTowerRadius delta M a) (bw / sourceTowerRadius delta M a) DD (part.convexHull_biUnion V1) := by
    intro part hp
    change part ∈ Fp.parts at hp
    rw [hFp] at hp
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hp
    exact hAdapterDimensions (Hn old) DD _ _ hDD (hDimensions old hold) (hZero old hold) (hUpper old hold 0)
  obtain ⟨short, middle, Cw, hsm, hm1, hRho, hCw, hCwCost, hAspect, Fz, hFz⟩ :=
    hAdapter (2*DD) hDa Nrm.parent_pos P.parents Nrm.parent Czero
      (aw / sourceTowerRadius delta M a) (bw / sourceTowerRadius delta M a) DD
      P.parents_nonempty (div_pos E.short_pos Nrm.ambient_pos)
      (div_le_div_of_nonneg_right E.short_le_middle Nrm.ambient_pos.le) hbw P.parent_ball Fnew hDimAdapter
  have hAdapterCost : 64 * (2*DD)^2 <= H := by
    have h : 64 * (2*DD)^2 <= Czero := by convert hWideCost using 1 <;> ring
    exact h.trans hCzeroH
  have hCwH : Cw <= H := hCwCost.trans hAdapterCost
  have hShortPos : 0 < short := Nrm.parent_pos.trans_le hRho
  have hPartsEq : Fz.parts = P.keptParts.image (fun part => part ∩ P.parents) := by
    have h := congrArg (fun G : ConvexSpaceBody.Factorization P.parents V1 Czero => G.parts) hFz
    exact h.trans hFp
  have hActual : forall part, part ∈ Fz.parts -> exists old, old ∈ P.keptParts ∧ part = old ∩ P.parents := by
    intro part hp
    rw [hPartsEq] at hp
    obtain ⟨old, hold, heq⟩ := Finset.mem_image.mp hp
    exact ⟨old, hold, heq.symm⟩
  refine ⟨{
    bound_one := hH, short := short, middle := middle, Cw := Cw, Czero := Czero,
    short_pos := hShortPos, short_le_middle := hsm, middle_le_one := hm1,
    parent_le_short := hRho, Cw_one := hCw, Czero_one := hCzero, Cw_bound := hCwH,
    Czero_bound := hCzeroH, factors := Fz, factors_nonempty := ?_, parts_eq := hPartsEq,
    actual_old_part := hActual, aspect := ?_, dimensions := ?_, old_hull_volume := ?_,
    new_hull_volume := ?_, original_test_body := ?_ }⟩
  · rw [hPartsEq]
    exact P.kept_parts_nonempty.image _
  · have hquot : (aw / sourceTowerRadius delta M a) / (bw / sourceTowerRadius delta M a) = aw / bw := by
      field_simp [Nrm.ambient_pos.ne', (E.short_pos.trans_le E.short_le_middle).ne']
    rw [hquot] at hAspect
    exact hAspect.trans (mul_le_mul_right' hAdapterCost _)
  · intro part hp
    obtain ⟨old, hold, rfl⟩ := hActual part hp
    exact hDimensionMono (Hn old) DD H _ _ 1 hDDH (hDimensions old hold)
  · intro part hp
    apply (hOldVol part hp).trans
    have hkH : k <= H := by
      calc k <= lam := le_mul_of_one_le_left' (by norm_num)
        _ <= DD := by dsimp [DD]; exact le_mul_of_one_le_left' (by
          exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hC) hD)
        _ <= H := hDDH
    exact mul_le_mul_right' (ENNReal.coe_le_coe.mpr hkH) _
  · intro part hp
    apply (hNewVol part hp).trans
    have hCH : Cgeom <= H := by
      calc Cgeom <= A := hCA
        _ <= H := by
          dsimp [H, sourceEccentricTransportCost]
          exact (le_mul_of_one_le_right' (one_le_pow₀ hL)).trans
            (le_mul_of_one_le_right' (one_le_pow₀ hC0))
    exact mul_le_mul_right' (mul_le_mul_right' (ENNReal.coe_le_coe.mpr hCH) _) _
  · intro V
    obtain ⟨W, hW, hWV⟩ := hTestBody V
    refine ⟨W, hW.trans ?_, hWV⟩
    have hCtH : Ctest <= H := by
      calc Ctest <= Ctest * Cgeom := le_mul_of_one_le_right' hC
        _ <= Ctest * Cgeom * C0 := le_mul_of_one_le_right' hC0
        _ <= Czero := hKTCost
        _ <= H := hCzeroH
    exact mul_le_mul_right' (ENNReal.div_le_div_right (ENNReal.coe_le_coe.mpr hCtH) (affineJacobian Nrm.affine)) _

end Kakeya.ML2Core

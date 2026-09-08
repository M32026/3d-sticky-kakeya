/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalPlankData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectPlankClosed

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

set_option maxHeartbeats 1600000 in
/-- Additive extraction of the completed outer split with exactly its
same-tube and a-count inputs. All geometric and quantitative outputs agree
with SourceEccentricOuterSplit and SourceEccentricOuterNormalization. -/
theorem source_exists_terminal_eccentric_outer_split (M : Nat) (hM : 2 <= M) :
    exists (Cgeom : NNReal) (K : Nat), 1 <= Cgeom /\ 1 <= K /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceTowerGeometry Q sourceBottomED sourceLevelED ->
        (forall i, (Z i).toTube = T i) ->
        (forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <=
          volume (Z i).shade) ->
        forall a : Nat, a < M -> SourceTerminalDescendantCounts Q a ->
        exists O : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss K delta),
          Nonempty (SourceEccentricOuterNormalization Q O Cgeom) := set_option maxHeartbeats 1600000 in
  by
    classical
    have hnormal : exists Cgeom : NNReal, 1 <= Cgeom /\
        forall {iota : Type u} {delta : NNReal} {S : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
          {Q : SourceThreadedTower S T M C}
          {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))} {a : Nat} {L : NNReal}
          (O : SourceEccentricOuterSplit Q Z a L),
          sourceTowerRadius delta M a <= 1 / 40 ->
          (forall i, i ∈ O.outer -> (Q.tube a i).carrier <= Metric.closedBall 0 3) ->
          Nonempty (SourceEccentricOuterNormalization Q O Cgeom) := by
      classical
      let c := Tube.le_volume.c 3
      let v := Tube.volume_le.C 3
      let Cgeom := max 1 (512 * v / c)
      have hc : 0 < c := Tube.le_volume.c_pos 3
      have hC : 1 <= Cgeom := le_max_left _ _
      have hCv : v <= Cgeom * (1 / 512) * c := by
        have h := (div_le_iff₀ hc).mp (show 512 * v / c <= Cgeom from le_max_right _ _)
        calc v <= Cgeom * c / 512 := (le_div_iff₀ (by norm_num)).mpr (by simpa [mul_comm] using h)
          _ = _ := by ring
      refine ⟨Cgeom, hC, ?_⟩
      intro iota delta S T M C Q Z a L O htheta hball
      let theta := sourceTowerRadius delta M a
      let A : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3) :=
        AffineEquiv.homothetyUnitsMulHom 0 (Units.mk0 (1 / 8 : Real) (by norm_num))
      have hA (x) : A x = (1 / 8 : Real) • x := by
        simp [A, AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply]
      have hAmap : (A : EuclideanSpace Real (Fin 3) -> EuclideanSpace Real (Fin 3)) =
          AffineMap.homothety 0 (1 / 8 : Real) := by
        funext x
        simp [hA, AffineMap.homothety_apply]
      have hdist (x y : EuclideanSpace Real (Fin 3)) : dist (A x) (A y) = (1 / 8 : Real) * dist x y := by
        rw [hA, hA, dist_smul₀]
        norm_num
      have hpq (i : iota) : A (Q.tube a i).x ≠ A (Q.tube a i).y := by
        apply A.injective.ne
        apply dist_ne_zero.mp
        rw [(Q.tube a i).dist_eq_one]
        norm_num
      let U : iota -> Tube (theta / 8) (EuclideanSpace Real (Fin 3)) :=
        fun i => Tube.centredExtension (theta / 8) (hpq i)
      have himage (i : iota) : A '' (Q.tube a i).carrier <= (U i).carrier := by
        have hh := Tube.cthickening_subset_centredExtension (s := theta / 8) (hpq i)
          (by rw [hdist, (Q.tube a i).dist_eq_one]; norm_num)
        rw [(Q.tube a i).carrier_eq_cthickening, hAmap,
          Metric.image_cthickening_homothety 0 (by norm_num : (0 : Real) < 1 / 8)
            theta.coe_nonneg, image_segment]
        simpa [U, hAmap, NNReal.coe_div, div_eq_mul_inv, mul_comm] using hh
      have hvolA (i : iota) : volume (A '' (Q.tube a i).carrier) =
          (1 / 512 : ENNReal) * volume (Q.tube a i).carrier := by
        rw [hAmap, MeasureTheory.Measure.addHaar_image_homothety]
        norm_num [ENNReal.ofReal_div_of_pos]
      have hvol (i : iota) : volume (U i).carrier <=
          (Cgeom : ENNReal) * volume (A '' (Q.tube a i).carrier) := by
        have hs : theta / 8 <= 1 := by dsimp [theta]; nlinarith only [htheta]
        have hthetas : theta / 8 <= theta := div_le_self (by positivity) (by norm_num)
        calc volume (U i).carrier <= (v : ENNReal) * ((theta / 8 : NNReal) : ENNReal) ^ (2 : Nat) := by
              simpa [v] using Tube.volume_le hs (U i)
          _ <= (v : ENNReal) * (theta : ENNReal) ^ (2 : Nat) := by gcongr
          _ <= ((Cgeom : ENNReal) * (1 / 512) * (c : ENNReal)) * (theta : ENNReal) ^ (2 : Nat) := by
              gcongr
              have h := ENNReal.coe_le_coe.mpr hCv
              have heq : ((1 / 512 : NNReal) : ENNReal) = 1 / 512 := by norm_num
              rw [ENNReal.coe_mul, ENNReal.coe_mul, heq] at h
              exact h
          _ = (Cgeom : ENNReal) * ((1 / 512) * ((c : ENNReal) * (theta : ENNReal) ^ (2 : Nat))) := by ring
          _ <= (Cgeom : ENNReal) * ((1 / 512) * volume (Q.tube a i).carrier) := by
              gcongr
              simpa [c, theta] using Tube.le_volume (Q.tube a i)
          _ = (Cgeom : ENNReal) * volume (A '' (Q.tube a i).carrier) := by rw [hvolA]
      have hUball (i : iota) (hi : i ∈ O.outer) : (U i).carrier <= Metric.closedBall 0 1 := by
        let p := A (Q.tube a i).x
        let q := A (Q.tube a i).y
        have hp : dist p 0 <= 3 / 8 := by
          have h := hball i hi ((Q.tube a i).mem_carrier_of_mem_segment (left_mem_segment ..))
          rw [Metric.mem_closedBall] at h
          dsimp [p]
          rw [show (0 : EuclideanSpace Real (Fin 3)) = A 0 by simp [hA], hdist]
          nlinarith only [h]
        have hq : dist q 0 <= 3 / 8 := by
          have h := hball i hi ((Q.tube a i).mem_carrier_of_mem_segment (right_mem_segment ..))
          rw [Metric.mem_closedBall] at h
          dsimp [q]
          rw [show (0 : EuclideanSpace Real (Fin 3)) = A 0 by simp [hA], hdist]
          nlinarith only [h]
        have hm : dist (_root_.midpoint Real p q) 0 <= 3 / 8 :=
          (convex_closedBall (0 : EuclideanSpace Real (Fin 3)) (3 / 8 : Real)).midpoint_mem hp hq
        have hcenter : (U i).center = _root_.midpoint Real p q :=
          Tube.center_centredExtension (s := theta / 8) (hpq i)
        have hx : dist (U i).x (U i).center = 1 / 2 := by
          rw [(U i).x_eq_center_sub, dist_eq_norm]
          simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, (U i).norm_direction]
          norm_num
        have hy : dist (U i).y (U i).center = 1 / 2 := by
          rw [(U i).y_eq_center_add, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, (U i).norm_direction]
          norm_num
        have hx0 : (U i).x ∈ Metric.closedBall 0 (7 / 8 : Real) := by
          rw [Metric.mem_closedBall]
          have h := dist_triangle (U i).x (U i).center 0
          rw [hx, hcenter] at h
          linarith only [h, hm]
        have hy0 : (U i).y ∈ Metric.closedBall 0 (7 / 8 : Real) := by
          rw [Metric.mem_closedBall]
          have h := dist_triangle (U i).y (U i).center 0
          rw [hy, hcenter] at h
          linarith only [h, hm]
        rw [(U i).carrier_eq_cthickening]
        apply (Metric.cthickening_subset_of_subset ((theta / 8 : NNReal) : Real)
          ((convex_closedBall _ _).segment_subset hx0 hy0)).trans
        rw [(isCompact_closedBall (0 : EuclideanSpace Real (Fin 3)) (7 / 8 : Real)).cthickening_eq_biUnion_closedBall (by positivity)]
        intro x hx
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
        rw [Metric.mem_closedBall] at hy hxy ⊢
        have htri := dist_triangle x y 0
        have h : (theta : Real) <= 1 / 40 := by exact_mod_cast htheta
        push_cast at hxy
        linarith only [h, hy, hxy, htri]
      let V : iota -> ShadedTube (theta / 8) (EuclideanSpace Real (Fin 3)) := fun i =>
        { toTube := U i
          shade := A '' (O.outerShade i).shade
          measurableSet_shade := Kakeya.measurableSet_affineEquiv_image A (O.outerShade i).measurableSet_shade
          shade_subset := by
            apply (Set.image_mono (O.outerShade i).shade_subset).trans
            have h := himage i
            change A '' (O.outerShade i).carrier <= (U i).carrier
            simpa only [← O.outer_tubes i] using h }
      refine ⟨{
        affine := A
        affine_eq := hA
        tubes := V
        shade_image := fun _ _ => rfl
        carrier_image := fun i _ => himage i
        volume_comparison := fun i _ => hvol i
        ball := hUball
        jacobian_pos := bot_lt_iff_ne_bot.mpr (affineJacobian_ne_zero A)
        jacobian_finite := lt_top_iff_ne_top.mpr (affineJacobian_ne_top A)
        mass_image := ?_
        union_image := ?_
        multiplicity := ?_
        fullness := ?_
        maximal_density := ?_ }⟩
      · dsimp [V]
        simp_rw [Kakeya.volume_image_affineEquiv]
        rw [Finset.mul_sum]
      · change volume (⋃ i ∈ O.outer, A '' (O.outerShade i).shade) = _
        rw [← Set.image_iUnion₂]
        exact Kakeya.volume_image_affineEquiv A _
      · rw [Tube.multiplicity_congr_of_shading_eq O.outer (ML2Reduction.spineFamily A O.outerShade)
          (fun i => (V i).toShadedBody) (fun _ _ => rfl)]
        exact ML2Reduction.spineFamily_multiplicity A O.outer O.outerShade
      · have h := Tube.le_fullness_of_volume_le hC O.outer (ML2Reduction.spineFamily A O.outerShade)
          (fun i => (V i).toShadedBody) (fun _ _ => rfl) (fun i _ => by
            have h := hvol i
            simpa only [V, ML2Reduction.spineFamily_apply, ML2Reduction.spineImage_carrier,
              ← O.outer_tubes i] using h)
        rw [ML2Reduction.spineFamily_fullness] at h
        simpa only [div_eq_mul_inv, mul_comm] using h
      · have h := ML2Reduction.maxDensity_le_of_comparable hC O.outer
          (fun i => (ML2Reduction.spineFamily A O.outerShade i).toConvexSpaceBody)
          (fun i => (V i).toConvexSpaceBody)
          (fun i _ => by
            change (ML2Reduction.spineFamily A O.outerShade i).carrier <= (V i).carrier
            simpa only [V, ML2Reduction.spineFamily_apply, ML2Reduction.spineImage_carrier,
              ← O.outer_tubes i] using himage i)
          (fun i _ => by
            simpa only [V, ML2Reduction.spineFamily_apply, ML2Reduction.spineImage_carrier,
              ← O.outer_tubes i] using hvol i)
        rw [ML2Reduction.spineFamily_maxDensity] at h
        have heq : (fun i => (O.outerShade i).toConvexSpaceBody) =
            (fun i => (Q.tube a i).toConvexSpaceBody) := by
          funext i
          exact congrArg Tube.toConvexSpaceBody (O.outer_tubes i)
        rw [heq] at h
        exact h.trans (mul_le_mul' le_rfl O.outer_density)
    have hcardinality {delta : NNReal} {iota : Type u} {S : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
        (Q : SourceThreadedTower S T M C)
        (hg : SourceTowerGeometry Q sourceBottomED sourceLevelED)
        (hd : 0 < delta) (hd1 : delta <= 1) :
        (S.card : Real) <= (sourceBottomED : Real) * (5 / (delta : Real)) ^ 6 := by
      classical
      have hdR : (0 : Real) < delta := by exact_mod_cast hd
      obtain ⟨G, hG, hsep, hcov⟩ := exists_maximal_separated_finset S
        (fun i j => ‖(T i).x - (T j).x‖ + ‖(T i).direction - (T j).direction‖)
        (ε := (delta : Real)) (fun i => by simpa using hdR)
        (fun i j => by rw [norm_sub_rev (T i).x, norm_sub_rev (T i).direction])
      have hGc : (G.card : Real) <= (5 / (delta : Real)) ^ 6 := by
        have h := Tube.card_le_of_L1_separated_in_box G (fun i => (T i).x)
          (fun i => (T i).direction) 0 0 (R := 1) hdR hsep
          (fun i hi => by
            have hb := hg.original_ball i (hG hi) (T i).x_mem_carrier
            rw [Metric.mem_closedBall, dist_zero_right] at hb
            simpa only [sub_zero] using hb.trans (by norm_num : (3 / 4 : Real) <= 1))
          (fun i hi => by simp only [sub_zero, Tube.norm_direction, le_refl])
        simp only [finrank_euclideanSpace_fin] at h
        apply h.trans
        apply pow_le_pow_left₀ (by positivity)
        have hd1R : (delta : Real) <= 1 := by exact_mod_cast hd1
        apply (div_le_div_iff₀ (by positivity : (0 : Real) < (delta : Real) / 4) hdR).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hd1R hdR.le]
      let F := fun j => S.filter (fun i => (T i).carrier <=
        Kakeya.VeryNotSticky.lineNbhd (T j).x (T j).direction (5 * (delta : Real)))
      have hcover : S <= G.biUnion F := by
        intro i hi
        obtain ⟨j, hj, hij⟩ := hcov i hi
        refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
        exact Kakeya.VeryNotSticky.carrier_subset_lineNbhd (T i)
          (εp := (delta : Real)) (εd := (delta : Real)) (r := 5 * (delta : Real))
          (left_mem_segment ..) (Or.inl rfl)
          (by linarith [norm_nonneg ((T i).direction - (T j).direction)])
          (by linarith [norm_nonneg ((T i).x - (T j).x)]) (by linarith)
      have hcard : S.card <= G.card * sourceBottomED := calc
        S.card <= (G.biUnion F).card := Finset.card_le_card hcover
        _ <= ∑ j ∈ G, (F j).card := Finset.card_biUnion_le
        _ <= ∑ j ∈ G, sourceBottomED := Finset.sum_le_sum (fun j hj =>
          hg.original_ed (T j).x (T j).direction (T j).norm_direction)
        _ = _ := by simp
      calc (S.card : Real) <= (G.card : Real) * sourceBottomED := by
            simpa only [Nat.cast_mul] using (Nat.cast_le (α := Real)).mpr hcard
        _ <= (5 / (delta : Real)) ^ 6 * sourceBottomED :=
          mul_le_mul_of_nonneg_right hGc (Nat.cast_nonneg sourceBottomED)
        _ = _ := by ring
    have hpolylog (B : Real) (hB : 1 <= B) :
        exists A : NNReal, 1 <= A /\ forall (delta : NNReal) (N : Nat),
          0 < delta -> delta <= 1 -> 0 < N ->
          (N : Real) <= B * (1 / (delta : Real)) ^ 6 ->
          ML2Reduction.spineScaleLoss 3 N delta <=
            A * (Real.toNNReal (2 + Real.logb 2 (1 / (delta : Real)))) ^ 6 := by
      let k : Real := 13 + Real.logb 2 (6 : Real) + Real.logb 2 (8 * B)
      have hlog6 : 0 <= Real.logb 2 (6 : Real) := Real.logb_nonneg one_lt_two (by norm_num)
      have hlogB : 0 <= Real.logb 2 (8 * B) := Real.logb_nonneg one_lt_two (by linarith)
      have hk : 1 <= k := by dsimp [k]; linarith only [hlog6, hlogB]
      let kn := Real.toNNReal k
      let A := max 1 (max (128 * kn ^ 6 * Kakeya.factoringStep5OverlapConstant 3 *
        ShadedBody.rhoTubesGeometricLoss 3) (ShadedBody.rhoTubesBallLoss 3))
      refine ⟨A, le_max_left _ _, ?_⟩
      intro delta N hd hd1 hN hcard
      have hdR : (0 : Real) < delta := by exact_mod_cast hd
      have hdinv : (1 : Real) <= 1 / (delta : Real) :=
        (le_div_iff₀ hdR).mpr (by simpa using (show (delta : Real) <= 1 by exact_mod_cast hd1))
      let l := Real.logb 2 (1 / (delta : Real))
      let X := Real.toNNReal (2 + l)
      have hl : 0 <= l := Real.logb_nonneg one_lt_two hdinv
      have hXcoe : (X : Real) = 2 + l := Real.coe_toNNReal _ (by positivity)
      have hX1 : 1 <= X := by rw [← NNReal.coe_le_coe, hXcoe]; norm_num; linarith only [hl]
      have hkn : (kn : Real) = k := Real.coe_toNNReal _ (zero_le_one.trans hk)
      have hFeq (n : Nat) (hn : 0 < n) :
          (Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale 3 delta)
            (Kakeya.step1UpperBdAtScale 3 n) : Real) =
          4 + Real.logb 2 (6 : Real) + Real.logb 2 (n : Real) + 3 * l := by
        have hr := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg 3
          (Nat.one_le_iff_ne_zero.mpr hn.ne') hd hd1
        have h := congrArg ENNReal.toReal
          (Kakeya.coe_factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale 3 delta)
            (Kakeya.step1UpperBdAtScale 3 n))
        rw [NNReal.coe_div] at hr
        rw [ENNReal.toReal_ofReal (by linarith : 0 <= 1 + Real.logb 2
          ((Kakeya.step1UpperBdAtScale 3 n : Real) / (Kakeya.step1LowerBdAtScale 3 delta : Real)))] at h
        simp only [ENNReal.coe_toReal] at h
        rw [h, ← NNReal.coe_div, Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale 3
          (Nat.one_le_iff_ne_zero.mpr hn.ne') hd]
        norm_num [l, Nat.factorial]
        ring
      have hlog (n : Nat) (hn : 0 < n)
          (hbound : (n : Real) <= (8 * B) * (1 / (delta : Real)) ^ 6) :
          Real.logb 2 (n : Real) <= Real.logb 2 (8 * B) + 6 * l := by
        have h := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
          (by exact_mod_cast hn : (0 : Real) < n) (by positivity)).mpr hbound
        rw [Real.logb_mul (by linarith : (8 * B : Real) ≠ 0) (by positivity), Real.logb_pow] at h
        exact h
      have hFN (n : Nat) (hn : 0 < n)
          (hbound : (n : Real) <= (8 * B) * (1 / (delta : Real)) ^ 6) :
          Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale 3 delta)
            (Kakeya.step1UpperBdAtScale 3 n) <= kn * X := by
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, hkn, hXcoe, hFeq n hn]
        have h := hlog n hn hbound
        dsimp [k]
        nlinarith only [h, hl, hlog6, hlogB, mul_nonneg hlog6 hl, mul_nonneg hlogB hl]
      have hcard' : (N : Real) <= (8 * B) * (1 / (delta : Real)) ^ 6 :=
        hcard.trans (by gcongr; linarith)
      have hcard8 : ((2 ^ 3 * N : Nat) : Real) <= (8 * B) * (1 / (delta : Real)) ^ 6 := by
        push_cast
        nlinarith only [hcard]
      have hlogNat : ((Nat.log 2 N + 1 : Nat) : NNReal) <= kn * X := by
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, hkn, hXcoe]
        push_cast
        have h := (Real.natLog_le_logb N 2).trans (hlog N hN hcard')
        dsimp [k]
        nlinarith only [h, hl, hlog6, hlogB, mul_nonneg hlog6 hl, mul_nonneg hlogB hl]
      have hratio : ShadedBody.step5PackingRatio 3 N delta =
          Kakeya.step1UpperBdAtScale 3 (2 ^ 3 * N) / Kakeya.step1LowerBdAtScale 3 delta := by
        unfold ShadedBody.step5PackingRatio
        rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hN.ne')]
        congr 1
        apply ENNReal.coe_injective
        rw [ENNReal.coe_mul, Kakeya.coe_step1UpperBdAtScale, Kakeya.coe_step1UpperBdAtScale]
        push_cast
        ring
      have hF5 : Kakeya.factoringStep1FiberPigeonholeConstant 1 (ShadedBody.step5PackingRatio 3 N delta) =
          Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale 3 delta)
            (Kakeya.step1UpperBdAtScale 3 (2 ^ 3 * N)) := by
        apply ENNReal.coe_injective
        rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant,
          Kakeya.coe_factoringStep1FiberPigeonholeConstant]
        congr 2
        rw [hratio]
        push_cast
        norm_num
      have h12 : Kakeya.factoringStep1Step2AtScaleConstant 3 N delta =
          2 * Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale 3 delta)
            (Kakeya.step1UpperBdAtScale 3 N) * ((Nat.log 2 N + 1 : Nat) : NNReal) ^ 3 := by
        rw [← NNReal.coe_inj]
        push_cast
        rw [Kakeya.coe_factoringStep1Step2AtScaleConstant 3
          (Nat.one_le_iff_ne_zero.mpr hN.ne') hd hd1, hFeq N hN]
        norm_num [Nat.factorial, l]
      have hLoss : 2 * Kakeya.factoringStep1Step2AtScaleConstant 3 N delta *
            (Kakeya.factoringStep3Constant N : NNReal) *
            ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
              (ShadedBody.step5PackingRatio 3 N delta) * ShadedBody.rhoTubesGeometricLoss 3 =
          128 * Kakeya.factoringStep1FiberPigeonholeConstant
            (Kakeya.step1LowerBdAtScale 3 delta) (Kakeya.step1UpperBdAtScale 3 N) *
            Kakeya.factoringStep1FiberPigeonholeConstant
              (Kakeya.step1LowerBdAtScale 3 delta) (Kakeya.step1UpperBdAtScale 3 (2 ^ 3 * N)) *
            ((Nat.log 2 N + 1 : Nat) : NNReal) ^ 4 *
            Kakeya.factoringStep5OverlapConstant 3 * ShadedBody.rhoTubesGeometricLoss 3 := by
        rw [h12, ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant, hF5,
          Kakeya.factoringStep3Constant]
        simp only [Kakeya.factoringStep2PointwiseConstant,
          Kakeya.MultiplicityFamily.scaleTripleConstant, Kakeya.dyadicPigeonholeNatConstant]
        push_cast
        ring
      have hmain : 128 * Kakeya.factoringStep1FiberPigeonholeConstant
            (Kakeya.step1LowerBdAtScale 3 delta) (Kakeya.step1UpperBdAtScale 3 N) *
            Kakeya.factoringStep1FiberPigeonholeConstant
              (Kakeya.step1LowerBdAtScale 3 delta) (Kakeya.step1UpperBdAtScale 3 (2 ^ 3 * N)) *
            ((Nat.log 2 N + 1 : Nat) : NNReal) ^ 4 *
            Kakeya.factoringStep5OverlapConstant 3 * ShadedBody.rhoTubesGeometricLoss 3 <=
          (128 * kn ^ 6 * Kakeya.factoringStep5OverlapConstant 3 * ShadedBody.rhoTubesGeometricLoss 3) *
            X ^ 6 := by
        calc _ <= 128 * (kn * X) * (kn * X) * (kn * X) ^ 4 *
              Kakeya.factoringStep5OverlapConstant 3 * ShadedBody.rhoTubesGeometricLoss 3 := by
                gcongr
                · exact hFN N hN hcard'
                · exact hFN _ (by positivity) hcard8
          _ = _ := by ring
      change ML2Reduction.spineScaleLoss 3 N delta <= A * X ^ 6
      rw [ML2Reduction.spineScaleLoss, ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C,
        one_pow, one_mul, hLoss]
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hX1)
      apply max_le
      · exact hmain.trans (mul_le_mul' ((le_max_left _ _).trans (le_max_right _ _)) le_rfl)
      · calc ShadedBody.rhoTubesBallLoss 3 <= A := (le_max_right _ _).trans (le_max_right _ _)
          _ <= A * X ^ 6 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hX1)
    have hsplit {iota : Type u} {delta : NNReal} {S : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C a : Nat}
        (Q : SourceThreadedTower S T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
        (hgeometry : SourceTowerGeometry Q sourceBottomED sourceLevelED)
        (hsame : forall i, (Z i).toTube = T i)
        (hcount : SourceTerminalDescendantCounts Q a) (ha : a <= M)
        (hdelta : 0 < delta) (hscale : delta <= sourceTowerRadius delta M a)
        (hscale1 : sourceTowerRadius delta M a <= 1)
        (hfull : 0 < ShadedBody.fullness S (fun i => (Z i).toShadedBody)) :
        let L := ML2Reduction.spineScaleLoss 3 S.card delta
        exists A : Finset iota, A <= Q.indexSet a /\ A.Nonempty /\
          exists (Za : iota -> ShadedTube (sourceTowerRadius delta M a)
              (EuclideanSpace Real (Fin 3)))
            (Zi : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
            (j : iota), j ∈ A /\
            (forall i, (Za i).toTube = Q.tube a i) /\
            (forall i, (Zi i).toTube = T i) /\
            (forall i, (Zi i).shade <= (Z i).shade) /\
            ShadedBody.IsCRefinement (S.filter (fun i => Q.place a i ∈ A))
              (fun i => (Zi i).toShadedBody) S (fun i => (Z i).toShadedBody) L⁻¹ /\
            (∑ i ∈ S, volume (Z i).shade) <=
              (L : ENNReal) * ∑ i ∈ S.filter (fun i => Q.place a i ∈ A), volume (Zi i).shade /\
            (forall i, i ∈ S -> Q.place a i ∈ A ->
              (Zi i).shade <= (Za (Q.place a i)).shade) /\
            ShadedBody.fullness S (fun i => (Z i).toShadedBody) / L <=
              ShadedBody.fullness A (fun i => (Za i).toShadedBody) /\
            ShadedBody.fullness S (fun i => (Z i).toShadedBody) / L <=
              ShadedBody.fullness (Q.cell a j) (fun i => (Zi i).toShadedBody) /\
            0 < ∑ i ∈ Q.cell a j, volume (Zi i).shade /\
            ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
              (L : ENNReal) * ShadedBody.multiplicity A (fun i => (Za i).toShadedBody) *
                ShadedBody.multiplicity (Q.cell a j) (fun i => (Zi i).toShadedBody) /\
            (A.card : ENNReal) * ((Q.cell a j).card : ENNReal) <= 2 * (S.card : ENNReal) /\
            maxDensity A (fun i => (Q.tube a i).toConvexSpaceBody) <=
              maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) := by
      classical
      dsimp only
      let L := ML2Reduction.spineScaleLoss 3 S.card delta
      have hL : 0 < L := lt_of_lt_of_le zero_lt_one (ML2Reduction.one_le_spineScaleLoss ..)
      have hball : forall i, i ∈ S -> (Z i).carrier <= Metric.closedBall 0 1 := by
        intro i hi
        have heq : (Z i).carrier = (T i).carrier :=
          congrArg (fun U : Tube delta (EuclideanSpace Real (Fin 3)) => U.carrier)
            (hsame i)
        rw [heq]
        exact (hgeometry.original_ball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
      obtain ⟨hvol, hvoltop⟩ :=
        Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hdelta S Z hgeometry.nonempty
      have hmass : 0 < ∑ i ∈ S, volume (Z i).shade := by
        rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul S (fun i => (Z i).toShadedBody)]
        exact ENNReal.mul_pos (ENNReal.coe_pos.mpr hfull).ne' hvol.ne'
      obtain ⟨A, hA, Za, Zi, hZa, hZi, hsub, hAne, hAmass, hcontain, hAfull, href, hmult⟩ :=
        ML2Reduction.exists_spineOneScale hdelta hscale hscale1 Z (Q.tube a) (Q.place a)
          hball (Q.place_mem a ha) (fun i hi => by
            have heq : (Z i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
              congrArg Tube.toConvexSpaceBody (hsame i)
            rw [heq]
            exact Q.leaf_containment a ha i hi)
      have hAne' := hAne hmass
      have href' : ShadedBody.IsCRefinement (S.filter (fun i => Q.place a i ∈ A))
          (fun i => (Zi i).toShadedBody) S (fun i => (Z i).toShadedBody) L⁻¹ := by
        simpa [L] using href
      have hrefFull := href'.mul_fullness_le _ _ _ _ hvol
      have hpaidPos : 0 < L⁻¹ * ShadedBody.fullness S (fun i => (Z i).toShadedBody) :=
        mul_pos (inv_pos.mpr hL) hfull
      have hrefPos : 0 < ShadedBody.fullness (S.filter (fun i => Q.place a i ∈ A))
          (fun i => (Zi i).toShadedBody) := hpaidPos.trans_le hrefFull
      have hrefNe : (S.filter (fun i => Q.place a i ∈ A)).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hrefPos
        simpa [ShadedBody.fullness, ShadedBody.fullness'] using hrefPos
      obtain ⟨hrefVol, hrefVolTop⟩ := Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top
        hdelta (S.filter (fun i => Q.place a i ∈ A)) Zi hrefNe
      obtain ⟨j, hj, hjfull⟩ := exists_fibre_fullness_le'
        (S.filter (fun i => Q.place a i ∈ A)) (fun i => (Zi i).toShadedBody) A (Q.place a)
        (fun i hi => (Finset.mem_filter.mp hi).2) hAne' hrefVol.ne' hrefVolTop
      have hfibre : (S.filter (fun i => Q.place a i ∈ A)).filter (fun i => Q.place a i = j) =
          Q.cell a j := by
        ext i
        simp only [SourceThreadedTower.cell, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hi, _⟩, heq⟩
          exact ⟨hi, heq⟩
        · rintro ⟨hi, heq⟩
          exact ⟨⟨hi, heq ▸ hj⟩, heq⟩
      rw [hfibre] at hjfull
      have hjpaid : L⁻¹ * ShadedBody.fullness S (fun i => (Z i).toShadedBody) <=
          ShadedBody.fullness (Q.cell a j) (fun i => (Zi i).toShadedBody) := hrefFull.trans hjfull
      have hjne : (Q.cell a j).Nonempty := by
        obtain ⟨i, hi, heq⟩ := Q.place_surjective a ha j (hA hj)
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
      obtain ⟨hjvol, _⟩ := Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hdelta _ Zi hjne
      have hjmass : 0 < ∑ i ∈ Q.cell a j, volume (Zi i).shade := by
        rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul (Q.cell a j)
          (fun i => (Zi i).toShadedBody)]
        exact ENNReal.mul_pos (ENNReal.coe_pos.mpr (hpaidPos.trans_le hjpaid)).ne' hjvol.ne'
      refine ⟨A, hA, hAne', Za, Zi, j, hj, hZa, (fun i => (hZi i).trans (hsame i)),
        hsub, href', ?_, hcontain, ?_, ?_, hjmass, ?_, ?_, maxDensity_mono _ hA⟩
      · have hm := href'.2
        rw [ENNReal.coe_inv hL.ne'] at hm
        exact (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hL.ne') ENNReal.coe_ne_top).mp hm
      · simpa only [L, div_eq_mul_inv, mul_comm, finrank_euclideanSpace_fin] using hAfull
      · simpa only [div_eq_mul_inv, mul_comm] using hjpaid
      · simpa only [L, SourceThreadedTower.cell, finrank_euclideanSpace_fin] using hmult j hj
      · have hsum : (∑ k ∈ Q.indexSet a, ((Q.cell a k).card : ENNReal)) = (S.card : ENNReal) := by
          have hnat := Finset.card_eq_sum_card_fiberwise (Q.place_mem a ha)
          exact_mod_cast hnat.symm
        calc
          (A.card : ENNReal) * ((Q.cell a j).card : ENNReal) <=
              ((Q.indexSet a).card : ENNReal) * ((Q.cell a j).card : ENNReal) :=
            mul_le_mul' (by exact_mod_cast Finset.card_le_card hA) le_rfl
          _ = ∑ k ∈ Q.indexSet a, ((Q.cell a j).card : ENNReal) := by simp
          _ <= ∑ k ∈ Q.indexSet a, 2 * ((Q.cell a k).card : ENNReal) :=
            Finset.sum_le_sum (fun k hk => hcount j (hA hj) k hk)
          _ = 2 * (S.card : ENNReal) := by rw [← Finset.mul_sum, hsum]
    obtain ⟨Cgeom, hCgeom, hnormal⟩ := hnormal
    let B : Real := (sourceBottomED : Real) * 5 ^ 6
    have hB : 1 <= B := by norm_num [B, sourceBottomED]
    obtain ⟨A, hA, hpolylog⟩ := hpolylog B hB
    let cutoff := Real.toNNReal (Real.exp (-(A : Real) * Real.log 2))
    have hcutoff : 0 < cutoff := Real.toNNReal_pos.mpr (Real.exp_pos _)
    refine ⟨Cgeom, 7, hCgeom, by norm_num, ?_⟩
    filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : Real) < 1),
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num), Ioo_mem_nhdsGT hcutoff]
      with delta hr hd1 hdcut
    intro iota S T Q Z hg hs hfloor a ha hcount
    have hd := hr.2.2.1
    have hdR : (0 : Real) < delta := by exact_mod_cast hd
    have hdle : delta <= 1 := hd1.2.le
    let X := Real.toNNReal (2 + Real.logb 2 (1 / (delta : Real)))
    have hlognonneg : 0 <= Real.logb 2 (1 / (delta : Real)) :=
      Real.logb_nonneg one_lt_two ((le_div_iff₀ hdR).mpr
        (by simpa only [one_mul] using (show (delta : Real) <= 1 by exact_mod_cast hdle)))
    have hX : (X : Real) = 2 + Real.logb 2 (1 / (delta : Real)) :=
      Real.coe_toNNReal _ (by positivity)
    have hAX : A <= X := by
      have hcut : (delta : Real) <= Real.exp (-(A : Real) * Real.log 2) := by
        have h := (NNReal.coe_le_coe).mpr hdcut.2.le
        simpa only [cutoff, Real.coe_toNNReal _ (Real.exp_pos _).le] using h
      have h := Real.log_le_log hdR hcut
      rw [Real.log_exp] at h
      rw [← NNReal.coe_le_coe, hX, Real.logb, one_div, Real.log_inv]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h' : (A : Real) <= -Real.log (delta : Real) / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr (by linarith only [h])
      linarith only [h']
    have hcard : (S.card : Real) <= B * (1 / (delta : Real)) ^ 6 := by
      have h := hcardinality Q hg hd hdle
      convert h using 1 <;> simp only [B] <;> ring
    have hLle : ML2Reduction.spineScaleLoss 3 S.card delta <= sourceEccentricLogLoss 7 delta := by
      calc ML2Reduction.spineScaleLoss 3 S.card delta <= A * X ^ 6 :=
            hpolylog delta S.card hd hdle (Finset.card_pos.mpr hg.nonempty) hcard
        _ <= X * X ^ 6 := mul_le_mul' hAX le_rfl
        _ = sourceEccentricLogLoss 7 delta := by
          rw [sourceEccentricLogLoss, Real.toNNReal_pow (by positivity)]
          change X * X ^ 6 = X ^ 7
          ring
    have hscale : delta <= sourceTowerRadius delta M a := by
      have h := hr.2.2.2.2.1 a ha
      nlinarith only [h]
    have htheta : sourceTowerRadius delta M a <= 1 / 40 := by
      rw [sourceTowerRadius, if_pos ha]
      exact mul_le_of_le_one_right (by positivity)
        (NNReal.rpow_le_one hdle (by positivity : (0 : Real) <= (a : Real) / M))
    have hscale1 : sourceTowerRadius delta M a <= 1 :=
      htheta.trans ((div_le_iff₀ (by norm_num : (0 : NNReal) < 40)).mpr (by norm_num))
    obtain ⟨hvol, hvoltop⟩ := Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hd S Z hg.nonempty
    have hmass : 0 < ∑ i ∈ S, volume (Z i).shade := by
      have hfloor' : (delta : ENNReal) ^ (10 : Real) * ∑ i ∈ S, volume (Z i).carrier <=
          ∑ i ∈ S, volume (Z i).shade := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have heq := congrArg (fun U : Tube delta (EuclideanSpace Real (Fin 3)) => U.carrier)
          (hs i)
        change (delta : ENNReal) ^ (10 : Real) * volume (Z i).carrier <= _
        rw [heq]
        exact hfloor i hi
      exact (ENNReal.mul_pos (by positivity : (delta : ENNReal) ^ (10 : Real) ≠ 0) hvol.ne').trans_le hfloor'
    have hfull : 0 < ShadedBody.fullness S (fun i => (Z i).toShadedBody) := by
      apply ENNReal.coe_pos.mp
      rw [ShadedBody.coe_fullness]
      exact ENNReal.div_pos hmass.ne' hvoltop
    obtain ⟨Aout, hAout, hAne, Za, Zi, j, hj, hZa, hZi, hsub, href, hmassRef,
      hcontain, hAfull, hjfull, hjmass, hmult, hcardProd, hD⟩ :=
      hsplit Q Z hg hs hcount ha.le hd hscale hscale1 hfull
    have hLpos : 0 < ML2Reduction.spineScaleLoss 3 S.card delta :=
      zero_lt_one.trans_le (ML2Reduction.one_le_spineScaleLoss ..)
    have href' := ShadedBody.IsCRefinement.mono
      (inv_anti₀ hLpos hLle) href
    have hjne : (Q.cell a j).Nonempty := by
      obtain ⟨i, hi, heq⟩ := Q.place_surjective a ha.le j (hAout hj)
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
    let O : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss 7 delta) := {
      outer := Aout
      outer_subset := hAout
      outer_nonempty := hAne
      outerShade := Za
      outer_tubes := hZa
      innerShade := Zi
      inner_tubes := hZi
      inner_subshade := hsub
      chosen := j
      chosen_mem := hj
      chosen_cell_nonempty := hjne
      refinedFine := S.filter (fun i => Q.place a i ∈ Aout)
      refined_fine_eq := rfl
      fine_refinement := href'
      refined_mass := hmassRef.trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hLle) le_rfl)
      fine_under_outer := fun i hi => hcontain i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
      outer_fullness := (div_le_div_of_nonneg_left (by positivity) hLpos hLle).trans hAfull
      inner_fullness := (div_le_div_of_nonneg_left (by positivity) hLpos hLle).trans hjfull
      inner_mass_pos := hjmass
      split_multiplicity := hmult.trans (mul_le_mul' (mul_le_mul' (ENNReal.coe_le_coe.mpr hLle) le_rfl) le_rfl)
      card_product := hcardProd
      outer_density := hD }
    exact ⟨O, hnormal O htheta (fun i hi => hg.coarse_ball a ha i (hAout hi))⟩

/-- Additive extraction of the actual assigned refinement. The only tower
statistics used by the completed proof are descendant counts at m; the
same fine ED selection, old-part retention and all costs remain outputs. -/
theorem source_exists_terminal_eccentric_assigned_refinement
    (M : Nat) (hM : 2 <= M) (Rnorm : Real) (hR : 64 <= Rnorm)
    (Cgeom cParent : NNReal) (hC : 1 <= Cgeom) (hc : 1 <= cParent)
    (D : NNReal) (hD : 1 <= D) (Kout : Nat) (hKout : 1 <= Kout) :
    exists (A : NNReal) (p K : Nat), Cgeom <= A /\ 1 <= A /\ 1 <= p /\ Kout <= K /\
      forall etaPlank zeta etaParent : Real, 0 < etaPlank -> etaPlank <= 1 ->
      0 < zeta -> 0 < etaParent ->
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall bias : Real, 0 < bias -> bias <= min (etaParent / 16) (etaPlank / 8) ->
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED etaPlank ->
        delta ^ etaPlank <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (a m : Nat) (aw bw cw : NNReal), m < M ->
        SourceTerminalDescendantCounts Q m ->
        forall (O : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss Kout delta))
          (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
          (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw),
        Nonempty (SourceEccentricAssignedSelection Q O Nrm E
          (sourceEccentricSelectionCost A p K delta etaPlank zeta)
          (A * delta ^ (-(p : Real) * zeta))) := by
  set_option maxHeartbeats 2000000 in
  classical
  have hbin {iota : Type u} {kappa : Type u} (s : Finset iota) (assign : iota -> kappa)
      (w : iota -> ENNReal) (hmass : 0 < ∑ i ∈ s, w i) :
      exists r : Finset kappa, r <= s.image assign /\ r.Nonempty /\
        (∑ i ∈ s, w i) <= ENNReal.ofReal (1 + Real.logb 2 (s.card : Real)) *
          ∑ i ∈ s.filter (fun i => assign i ∈ r), w i /\
        exists n : NNReal, 0 < n /\ forall k, k ∈ r ->
          n / 2 <= (((s.filter (fun i => assign i ∈ r)).filter
            (fun i => assign i = k)).card : NNReal) /\
          (((s.filter (fun i => assign i ∈ r)).filter
            (fun i => assign i = k)).card : NNReal) <= 2 * n := by
    classical
    let fibre := fun k => s.filter (fun i => assign i = k)
    have hne : s.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at hmass
    have hrange : forall k, k ∈ s.image assign ->
        ((fibre k).card : ENNReal) ∈ Set.Icc (1 : ENNReal) (s.card : ENNReal) := by
      intro k hk
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
      have hpos : 0 < (fibre k).card := Finset.card_pos.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hik⟩⟩
      constructor
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos.ne'
      · exact_mod_cast Finset.card_le_card (Finset.filter_subset _ s)
    obtain ⟨r, hrs, hrmass, hrcompare⟩ := ENNReal.dyadic_pigeonhole₁
      (s.image assign) (fun k => ∑ i ∈ fibre k, w i) (fun k => ((fibre k).card : ENNReal))
      (a := 1) (b := s.card) (by norm_num) (by exact_mod_cast hne.card_pos) (by
        simpa using hrange)
    have hsum : (∑ k ∈ s.image assign, ∑ i ∈ fibre k, w i) = ∑ i ∈ s, w i := by
      exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem assign hi) w
    have hselected : (∑ k ∈ r, ∑ i ∈ fibre k, w i) =
        ∑ i ∈ s.filter (fun i => assign i ∈ r), w i := by
      exact Finset.sum_fiberwise_eq_sum_filter s r assign w
    rw [hsum, hselected] at hrmass
    simp only [div_one] at hrmass
    have hrne : r.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.notMem_empty,
        Finset.filter_false, Finset.sum_empty, mul_zero] at hrmass
      exact (not_le_of_gt hmass) hrmass
    obtain ⟨k0, hk0⟩ := hrne
    refine ⟨r, hrs, ⟨k0, hk0⟩, hrmass, ((fibre k0).card : NNReal), ?_, ?_⟩
    · have h := (hrange k0 (hrs hk0)).1
      exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) h
    · intro k hk
      have heq : (s.filter (fun i => assign i ∈ r)).filter (fun i => assign i = k) =
          fibre k := by
        ext i
        simp only [Finset.mem_filter, fibre]
        aesop
      rw [heq]
      constructor
      · apply (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).mpr
        have h := hrcompare k0 hk0 k hk
        have hn : ((fibre k0).card : NNReal) <= 2 * ((fibre k).card : NNReal) := by
          exact_mod_cast h
        simpa only [mul_comm] using hn
      · exact_mod_cast hrcompare k hk k0 hk0
  have hcore {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
      (Q : SourceThreadedTower S T M C)
      {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
      {a m : Nat} {Lout : NNReal} (O : SourceEccentricOuterSplit Q Z a Lout)
      {Rnorm : Real} {Cgeom cParent : NNReal}
      (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
      {etaParent bias : Real} {D aw bw cw : NNReal}
      (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
      (hstats : SourceTerminalDescendantCounts Q m)
      (ed q0 : Finset iota) (heds : ed <= Q.cell a O.chosen) (hq0ed : q0 <= ed)
      (hed : (ed : Set iota).Pairwise (fun i j =>
        _root_.IsEssentiallyDistinct (Nrm.fine i).carrier (Nrm.fine j).carrier))
      (hedmass : (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).shade) <=
        (1 + Tube.refineToEssDistinctLeaves.C 3 *
          Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toConvexSpaceBody)) *
          ∑ i ∈ ed, volume (Nrm.fine i).shade)
      (n L Ccount : NNReal) (hn : 0 < n) (hL : 1 <= L) (hCcount : 2 <= Ccount)
      (hcounts : forall k, k ∈ q0.image (Q.place m) ->
        n / 2 <= ((q0.filter (fun i => Q.place m i = k)).card : NNReal) /\
        ((q0.filter (fun i => Q.place m i = k)).card : NNReal) <= 2 * n)
      (hbudget : 4 * (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).carrier) <=
        (L : ENNReal) * ∑ i ∈ q0, volume (Nrm.fine i).shade) :
      Nonempty (SourceEccentricAssignedSelection Q O Nrm E L Ccount) := by
    classical
    have hcross {iota : Type u} {kappa : Type u} (s q : Finset iota) (assign : iota -> kappa)
        (hqs : q <= s) (part : Finset kappa)
        (hcounts : forall k, k ∈ part -> forall l, l ∈ part ->
          ((s.filter (fun i => assign i = k)).card : ENNReal) <=
            2 * ((s.filter (fun i => assign i = l)).card : ENNReal)) :
        (part.card : ENNReal) * ((q.filter (fun i => assign i ∈ part)).card : ENNReal) <=
          2 * ((part ∩ q.image assign).card : ENNReal) *
            ((s.filter (fun i => assign i ∈ part)).card : ENNReal) := by
      classical
      let r := part ∩ q.image assign
      have hqsum : ((q.filter (fun i => assign i ∈ part)).card : ENNReal) =
          ∑ k ∈ r, ((q.filter (fun i => assign i = k)).card : ENNReal) := by
        have heq : q.filter (fun i => assign i ∈ part) = q.filter (fun i => assign i ∈ r) := by
          ext i
          simp only [Finset.mem_filter, r, Finset.mem_inter]
          constructor
          · rintro ⟨hi, hp⟩
            exact ⟨hi, hp, Finset.mem_image_of_mem _ hi⟩
          · rintro ⟨hi, hp, _⟩
            exact ⟨hi, hp⟩
        rw [heq]
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          (Finset.sum_fiberwise_eq_sum_filter q r assign (fun _ => (1 : ENNReal))).symm
      have hssum : ((s.filter (fun i => assign i ∈ part)).card : ENNReal) =
          ∑ k ∈ part, ((s.filter (fun i => assign i = k)).card : ENNReal) := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          (Finset.sum_fiberwise_eq_sum_filter s part assign (fun _ => (1 : ENNReal))).symm
      have hfibre : forall k, ((q.filter (fun i => assign i = k)).card : ENNReal) <=
          ((s.filter (fun i => assign i = k)).card : ENNReal) := by
        intro k
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hqs)
      rw [hqsum, hssum]
      calc
        (part.card : ENNReal) * ∑ k ∈ r, ((q.filter (fun i => assign i = k)).card : ENNReal) =
            ∑ l ∈ part, ∑ k ∈ r, ((q.filter (fun i => assign i = k)).card : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ l ∈ part, ∑ k ∈ r,
            2 * ((s.filter (fun i => assign i = l)).card : ENNReal) := by
          apply Finset.sum_le_sum
          intro l hl
          apply Finset.sum_le_sum
          intro k hk
          exact (hfibre k).trans (hcounts k (Finset.mem_inter.mp hk).1 l hl)
        _ = 2 * ((part ∩ q.image assign).card : ENNReal) *
            ∑ l ∈ part, ((s.filter (fun i => assign i = l)).card : ENNReal) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          change (r.card : ENNReal) * (2 * _) = 2 * (r.card : ENNReal) * _
          ring

    have hparts {iota : Type u} {kappa : Type u} [DecidableEq kappa]
        (q : Finset iota) (r : Finset kappa) (assign : iota -> kappa)
        (hassign : forall i, i ∈ q -> assign i ∈ r) (F : Finpartition r)
        (w : iota -> ENNReal) (v : kappa -> ENNReal) (t c : ENNReal)
        (hc : 0 < c) (hmass : 0 < ∑ i ∈ q, w i)
        (hfin : t * ∑ k ∈ r, v k ≠ ⊤)
        (hbudget : c * (∑ i ∈ q, w i) + t * ∑ k ∈ r, v k <= ∑ i ∈ q, w i) :
        exists g : Finset (Finset kappa), g <= F.parts /\ g.Nonempty /\
          c * (∑ i ∈ q, w i) <= ∑ i ∈ q.filter (fun i => assign i ∈ g.biUnion id), w i /\
          forall part, part ∈ g ->
            t * (∑ k ∈ part, v k) <=
              ∑ i ∈ (q.filter (fun i => assign i ∈ g.biUnion id)).filter
                (fun i => assign i ∈ part), w i := by
      classical
      let wp := fun part : Finset kappa => ∑ i ∈ q.filter (fun i => assign i ∈ part), w i
      let vp := fun part : Finset kappa => ∑ k ∈ part, v k
      let g := F.parts.filter (fun part => t * vp part <= wp part)
      have hgp : g <= F.parts := Finset.filter_subset _ _
      have hpSum (part : Finset kappa) : wp part =
          ∑ k ∈ part, ∑ i ∈ q.filter (fun i => assign i = k), w i :=
        (Finset.sum_fiberwise_eq_sum_filter q part assign w).symm
      have htotalW : (∑ part ∈ F.parts, wp part) = ∑ i ∈ q, w i := by
        simp_rw [hpSum]
        rw [← F.sum_eq_sum_parts_sum]
        exact Finset.sum_fiberwise_of_maps_to hassign w
      have htotalV : (∑ part ∈ F.parts, vp part) = ∑ k ∈ r, v k :=
        (F.sum_eq_sum_parts_sum v).symm
      have hselectedW : (∑ part ∈ g, wp part) =
          ∑ i ∈ q.filter (fun i => assign i ∈ g.biUnion id), w i := by
        simp_rw [hpSum]
        calc
          _ = ∑ k ∈ g.biUnion id, ∑ i ∈ q.filter (fun i => assign i = k), w i := by
            simpa using (Finset.sum_biUnion (F.disjoint.subset hgp)
              (f := fun k => ∑ i ∈ q.filter (fun i => assign i = k), w i)).symm
          _ = _ := Finset.sum_fiberwise_eq_sum_filter q (g.biUnion id) assign w
      have hsplit : (∑ part ∈ F.parts, wp part) <=
          (∑ part ∈ g, wp part) + t * ∑ part ∈ F.parts, vp part := by
        rw [← Finset.sum_filter_add_sum_filter_not F.parts (fun part => t * vp part <= wp part) wp]
        gcongr
        calc
          (∑ part ∈ F.parts.filter (fun part => ¬ t * vp part <= wp part), wp part) <=
              ∑ part ∈ F.parts.filter (fun part => ¬ t * vp part <= wp part), t * vp part := by
            exact Finset.sum_le_sum fun part hp =>
              le_of_lt (not_le.mp (Finset.mem_filter.mp hp).2)
          _ = t * ∑ part ∈ F.parts.filter (fun part => ¬ t * vp part <= wp part), vp part := by
            rw [Finset.mul_sum]
          _ <= t * ∑ part ∈ F.parts, vp part :=
            mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) t
      rw [htotalW, htotalV] at hsplit
      have hkeep : c * (∑ i ∈ q, w i) <= ∑ part ∈ g, wp part :=
        ENNReal.le_of_add_le_add_right hfin (hbudget.trans hsplit)
      have hgne : g.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hkeep
        exact (not_le_of_gt (ENNReal.mul_pos hc.ne' hmass.ne')) hkeep
      refine ⟨g, hgp, hgne, hselectedW ▸ hkeep, ?_⟩
      intro part hp
      have heq : (q.filter (fun i => assign i ∈ g.biUnion id)).filter
          (fun i => assign i ∈ part) = q.filter (fun i => assign i ∈ part) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hi, _⟩, hp⟩
          exact ⟨hi, hp⟩
        · rintro ⟨hi, hip⟩
          exact ⟨⟨hi, Finset.mem_biUnion.mpr ⟨part, hp, hip⟩⟩, hip⟩
      rw [heq]
      exact (Finset.mem_filter.mp hp).2

    have hpaid (A B P R t L : NNReal) (V mass : ENNReal)
        (hA : 0 < A) (hV : V ≠ 0) (hVfin : V ≠ ⊤)
        (hlow : (t : ENNReal) * (V * (A : ENNReal)) <= mass)
        (hupp : mass <= V * (B : ENNReal))
        (hcard : P * B <= 2 * R * A) (hLt : 2 <= L * t) : P <= L * R := by
      have hVA : V * (A : ENNReal) ≠ 0 :=
        mul_ne_zero hV (ENNReal.coe_ne_zero.mpr hA.ne')
      have hVAfin : V * (A : ENNReal) ≠ ⊤ :=
        ENNReal.mul_ne_top hVfin ENNReal.coe_ne_top
      have hscaled : ((t : ENNReal) * (P : ENNReal)) * (V * (A : ENNReal)) <=
          (2 * (R : ENNReal)) * (V * (A : ENNReal)) := by
        calc
          ((t : ENNReal) * (P : ENNReal)) * (V * (A : ENNReal)) =
              ((t : ENNReal) * (V * (A : ENNReal))) * (P : ENNReal) := by ring
          _ <= mass * (P : ENNReal) := mul_le_mul_left hlow _
          _ <= (V * (B : ENNReal)) * (P : ENNReal) := mul_le_mul_left hupp _
          _ = V * ((P : ENNReal) * (B : ENNReal)) := by ring
          _ <= V * (2 * (R : ENNReal) * (A : ENNReal)) :=
            mul_le_mul_right (by exact_mod_cast hcard) V
          _ = (2 * (R : ENNReal)) * (V * (A : ENNReal)) := by ring
      have hpaid : t * P <= 2 * R := by
        exact_mod_cast (ENNReal.mul_le_mul_iff_left hVA hVAfin).mp hscaled
      have hfinal : 2 * P <= 2 * (L * R) := by
        calc
          2 * P <= (L * t) * P := mul_le_mul_left hLt P
          _ = L * (t * P) := by ring
          _ <= L * (2 * R) := mul_le_mul_right hpaid L
          _ = 2 * (L * R) := by ring
      exact (mul_le_mul_iff_right₀ (by norm_num : (0 : NNReal) < 2)).mp hfinal
    let s := Q.cell a O.chosen
    let assign := Q.place m
    let r := Q.fibre a m O.chosen
    let F := (E.factor O.chosen (O.outer_subset O.chosen_mem)).toFinpartition
    let w := fun i => volume (Nrm.fine i).shade
    let v := fun k => ∑ i ∈ s.filter (fun i => assign i = k), volume (Nrm.fine i).carrier
    let t : NNReal := 2 / L
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
    have htpos : 0 < t := div_pos (by norm_num) hLpos
    have hLt : L * t = 2 := by
      dsimp [t]
      rw [← mul_div_assoc]
      exact (div_eq_iff hLpos.ne').mpr (mul_comm L 2)
    have hq0s : q0 <= s := hq0ed.trans heds
    have has : forall i, i ∈ s -> assign i ∈ r :=
      fun i hi => Finset.mem_image_of_mem _ hi
    have haq : forall i, i ∈ q0 -> assign i ∈ r := fun i hi => has i (hq0s hi)
    have hsumv : (∑ k ∈ r, v k) = ∑ i ∈ s, volume (Nrm.fine i).carrier :=
      Finset.sum_fiberwise_of_maps_to has _
    obtain ⟨i0, hi0⟩ := O.chosen_cell_nonempty
    have hsigma1 : sourceEccentricFineScale delta M a <= 1 := by
      exact_mod_cast Nrm.fine_situation.out_le_quarter.trans (by norm_num : (1 / 4 : Real) <= 1)
    let V := volume (Nrm.fine i0).carrier
    have hVpos : 0 < V :=
      (Tube.volume_pos_and_lt_top Nrm.fine_pos hsigma1 (Nrm.fine i0).toTube).1
    have hVfin : V ≠ ⊤ := (Nrm.fine i0).isCompact.measure_ne_top
    have hvol (i : iota) : volume (Nrm.fine i).carrier = V :=
      Tube.volume_carrier_eq_volume_carrier (Nrm.fine i).toTube (Nrm.fine i0).toTube
    have hcarrier : 0 < ∑ i ∈ s, volume (Nrm.fine i).carrier := by
      exact lt_of_lt_of_le (hvol i0 ▸ hVpos) (Finset.single_le_sum (fun _ _ => zero_le) hi0)
    have hcarfin : (∑ i ∈ s, volume (Nrm.fine i).carrier) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun i _ => (Nrm.fine i).isCompact.measure_ne_top
    have hqmass : 0 < ∑ i ∈ q0, w i := by
      by_contra h
      have hz := le_antisymm (le_of_not_gt h) zero_le
      change (∑ i ∈ q0, volume (Nrm.fine i).shade) = 0 at hz
      rw [hz, mul_zero] at hbudget
      exact (not_le_of_gt (ENNReal.mul_pos (by norm_num) hcarrier.ne')) hbudget
    have hhalfFour : (1 / 2 : ENNReal) * 4 = 2 := by
      rw [one_div, show (4 : ENNReal) = 2 * 2 by norm_num, ← mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    have hhalfAdd : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
      simpa only [one_div] using ENNReal.inv_two_add_inv_two
    have hsmall : (t : ENNReal) * ∑ k ∈ r, v k <= (1 / 2 : ENNReal) * ∑ i ∈ q0, w i := by
      rw [hsumv]
      have hL0 : (L : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hLpos.ne'
      apply (ENNReal.mul_le_mul_iff_right hL0 ENNReal.coe_ne_top).mp
      calc
        (L : ENNReal) * ((t : ENNReal) * ∑ i ∈ s, volume (Nrm.fine i).carrier) =
            2 * ∑ i ∈ s, volume (Nrm.fine i).carrier := by
          rw [← mul_assoc, ← ENNReal.coe_mul, hLt]
          norm_num
        _ = (1 / 2 : ENNReal) * (4 * ∑ i ∈ s, volume (Nrm.fine i).carrier) := by
          rw [← mul_assoc, hhalfFour]
        _ <= (1 / 2 : ENNReal) * ((L : ENNReal) * ∑ i ∈ q0, w i) :=
          mul_le_mul_right hbudget _
        _ = (L : ENNReal) * ((1 / 2 : ENNReal) * ∑ i ∈ q0, w i) := by ring
    have hhalf : (1 / 2 : ENNReal) * (∑ i ∈ q0, w i) +
        (t : ENNReal) * ∑ k ∈ r, v k <= ∑ i ∈ q0, w i := by
      calc
        _ <= (1 / 2 : ENNReal) * (∑ i ∈ q0, w i) +
            (1 / 2 : ENNReal) * (∑ i ∈ q0, w i) := add_le_add_right hsmall _
        _ = ∑ i ∈ q0, w i := by rw [← add_mul, hhalfAdd, one_mul]
    obtain ⟨g, hgp, hgne, hkeep, hgpart⟩ := hparts q0 r assign haq F w v
      (t : ENNReal) (1 / 2) (by norm_num) hqmass
      (by rw [hsumv]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top hcarfin) hhalf
    let q := q0.filter (fun i => assign i ∈ g.biUnion id)
    let parents := q.image assign
    have hqq0 : q <= q0 := Finset.filter_subset _ _
    have hqs : q <= s := hqq0.trans hq0s
    have hqmasspos : 0 < ∑ i ∈ q, w i :=
      (ENNReal.mul_pos (by norm_num) hqmass.ne').trans_le hkeep
    have hqne : q.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at hqmasspos
    have hparentne : parents.Nonempty := hqne.image _
    have hparentr : parents <= r := Finset.image_subset_iff.mpr fun i hi => has i (hqs hi)
    have hparent0 : parents <= q0.image assign := Finset.image_subset_image hqq0
    have hfibre (k : iota) (hk : k ∈ parents) :
        q.filter (fun i => assign i = k) = q0.filter (fun i => assign i = k) := by
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
      have hkg : k ∈ g.biUnion id := hjk ▸ (Finset.mem_filter.mp hj).2
      ext i
      simp only [q, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hi, _⟩, heq⟩
        exact ⟨hi, heq⟩
      · rintro ⟨hi, heq⟩
        exact ⟨⟨hi, heq ▸ hkg⟩, heq⟩
    have hmass : (∑ i ∈ s, volume (Nrm.fine i).shade) <=
        (L : ENNReal) * ∑ i ∈ q, volume (Nrm.fine i).shade := by
      calc
        _ <= ∑ i ∈ s, volume (Nrm.fine i).carrier :=
          Finset.sum_le_sum fun i _ => measure_mono (Nrm.fine i).shade_subset
        _ <= 2 * ∑ i ∈ s, volume (Nrm.fine i).carrier := by
          simpa only [one_mul] using mul_le_mul_left
            (by norm_num : (1 : ENNReal) <= 2) (∑ i ∈ s, volume (Nrm.fine i).carrier)
        _ = (1 / 2 : ENNReal) * (4 * ∑ i ∈ s, volume (Nrm.fine i).carrier) := by
          rw [← mul_assoc, hhalfFour]
        _ <= (1 / 2 : ENNReal) * ((L : ENNReal) * ∑ i ∈ q0, w i) :=
          mul_le_mul_right hbudget _
        _ = (L : ENNReal) * ((1 / 2 : ENNReal) * ∑ i ∈ q0, w i) := by ring
        _ <= (L : ENNReal) * ∑ i ∈ q, w i := mul_le_mul_right hkeep _
    have href : ShadedBody.IsCRefinement q (fun i => (Nrm.fine i).toShadedBody)
        s (fun i => (Nrm.fine i).toShadedBody) L⁻¹ :=
      ShadedBody.isCRefinement_of_isRefinement_of_sum_le _ _ _ _
        ⟨hqs, fun _ _ => ⟨rfl, le_rfl⟩⟩ hmass
    have hvpart (part : Finset iota) : (∑ k ∈ part, v k) =
        V * ((s.filter (fun i => assign i ∈ part)).card : ENNReal) := by
      dsimp [v]
      rw [Finset.sum_fiberwise_eq_sum_filter s part assign (fun i => volume (Nrm.fine i).carrier)]
      rw [Tube.sum_volume_carrier_eq_card_mul (fun i => (Nrm.fine i).toTube)
        (Nrm.fine i0).toTube]
      exact mul_comm _ _
    have hdescNe (part : Finset iota) (hp : part ∈ F.parts) :
        (s.filter (fun i => assign i ∈ part)).Nonempty := by
      obtain ⟨k, hk⟩ := F.nonempty_of_mem_parts hp
      have hkr : k ∈ r := F.subset hp hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hkr
      refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
      change Q.place m i ∈ part
      rw [heq]
      exact hk
    have hpartLower (part : Finset iota) (hp : part ∈ g) :
        (t : ENNReal) * (V * ((s.filter (fun i => assign i ∈ part)).card : ENNReal)) <=
          ∑ i ∈ q.filter (fun i => assign i ∈ part), w i := by
      simpa only [hvpart] using hgpart part hp
    have hpartUpper (part : Finset iota) : (∑ i ∈ q.filter (fun i => assign i ∈ part), w i) <=
        V * ((q.filter (fun i => assign i ∈ part)).card : ENNReal) := by
      calc
        _ <= ∑ i ∈ q.filter (fun i => assign i ∈ part), volume (Nrm.fine i).carrier :=
          Finset.sum_le_sum fun i _ => measure_mono (Nrm.fine i).shade_subset
        _ = V * ((q.filter (fun i => assign i ∈ part)).card : ENNReal) := by
          simp_rw [hvol]
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hpartsNe : forall part, part ∈ g -> (part ∩ parents).Nonempty := by
      intro part hp
      have hmasspart : 0 < ∑ i ∈ q.filter (fun i => assign i ∈ part), w i :=
        (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr htpos.ne')
          (mul_ne_zero hVpos.ne' (by exact_mod_cast (hdescNe part (hgp hp)).card_pos.ne'))).trans_le
            (hpartLower part hp)
      have hnonempty : (q.filter (fun i => assign i ∈ part)).Nonempty := by
        by_contra h
        simp [Finset.not_nonempty_iff_eq_empty.mp h] at hmasspart
      obtain ⟨i, hi⟩ := hnonempty
      exact ⟨assign i, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).2,
        Finset.mem_image_of_mem _ (Finset.mem_filter.mp hi).1⟩⟩
    have hancestor : forall b, a <= b -> b <= M -> forall i, i ∈ S -> forall j, j ∈ S ->
        Q.place b i = Q.place b j -> Q.place a i = Q.place a j := by
      intro b hab
      induction b, hab using Nat.le_induction with
      | base => intro _ i _ j _ heq; exact heq
      | succ b hab ih =>
        intro hb i hi j hj heq
        apply ih (Nat.le_of_succ_le hb) i hi j hj
        rw [Q.parent_composition b (Nat.lt_of_succ_le hb) i hi,
          Q.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
    have hwholecell (k : iota) (hk : k ∈ r) :
        s.filter (fun i => assign i = k) = Q.cell m k := by
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
      ext i
      simp only [s, SourceThreadedTower.cell, Finset.mem_filter, assign] at hj ⊢
      constructor
      · rintro ⟨⟨hi, _⟩, heq⟩
        exact ⟨hi, heq⟩
      · rintro ⟨hi, heq⟩
        refine ⟨⟨hi, ?_⟩, heq⟩
        exact (hancestor m E.coarse_lt_middle.le E.middle_bound i hi j hj.1
          (heq.trans hjk.symm)).trans hj.2
    have hindex (k : iota) (hk : k ∈ r) : k ∈ Q.indexSet m := by
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
      exact heq ▸ Q.place_mem m E.middle_bound i (Finset.mem_filter.mp hi).1
    have hpartCard : forall part, part ∈ g ->
        (part.card : NNReal) <= L * ((part ∩ parents).card : NNReal) := by
      intro part hp
      apply hpaid ((s.filter (fun i => assign i ∈ part)).card : NNReal)
        ((q.filter (fun i => assign i ∈ part)).card : NNReal)
        (part.card : NNReal) ((part ∩ parents).card : NNReal) t L V
        (∑ i ∈ q.filter (fun i => assign i ∈ part), w i)
        (by exact_mod_cast (hdescNe part (hgp hp)).card_pos) hVpos.ne' hVfin
        (by simpa using hpartLower part hp) (by simpa using hpartUpper part) ?_ hLt.symm.le
      have hcross' := hcross s q assign hqs part (by
        intro k hk l hl
        rw [hwholecell k (F.subset (hgp hp) hk), hwholecell l (F.subset (hgp hp) hl)]
        exact hstats k
          (hindex k (F.subset (hgp hp) hk)) l (hindex l (F.subset (hgp hp) hl)))
      exact_mod_cast hcross'
    have hpartMass : forall part, part ∈ g ->
        (∑ i ∈ s.filter (fun i => assign i ∈ part), volume (Nrm.fine i).shade) <=
          (L : ENNReal) * ∑ i ∈ q.filter (fun i => assign i ∈ part), volume (Nrm.fine i).shade := by
      intro part hp
      calc
        _ <= ∑ i ∈ s.filter (fun i => assign i ∈ part), volume (Nrm.fine i).carrier :=
          Finset.sum_le_sum fun i _ => measure_mono (Nrm.fine i).shade_subset
        _ = ∑ k ∈ part, v k :=
          (Finset.sum_fiberwise_eq_sum_filter s part assign (fun i => volume (Nrm.fine i).carrier)).symm
        _ <= 2 * ∑ k ∈ part, v k := by
          simpa only [one_mul] using mul_le_mul_left
            (by norm_num : (1 : ENNReal) <= 2) (∑ k ∈ part, v k)
        _ = (L : ENNReal) * ((t : ENNReal) * ∑ k ∈ part, v k) := by
          rw [← mul_assoc, ← ENNReal.coe_mul, hLt]
          norm_num
        _ <= (L : ENNReal) * ∑ i ∈ q.filter (fun i => assign i ∈ part), w i :=
          mul_le_mul_right (hgpart part hp) _
    refine ⟨{ edLeaves := ed
              ed_subset := heds
              ed_pairwise := hed
              ed_mass_price := hedmass
              leaves := q
              leaves_subset_ed := hqq0.trans hq0ed
              leaves_subset := hqs
              leaves_nonempty := hqne
              shading := Nrm.fine
              same_tubes := fun _ => rfl
              subshade := fun _ => le_rfl
              essentially_distinct := hed.mono (hqq0.trans hq0ed)
              refinement := href
              mass := hmass
              union_subset := ?_
              fullness := ?_
              multiplicity := ?_
              parents := parents
              parents_eq := rfl
              parents_subset := hparentr
              parents_nonempty := hparentne
              parent_ball := fun k hk => Nrm.parent_ball k (hparentr hk)
              n := n
              Cfib := 2
              n_positive := hn
              Cfib_one := by norm_num
              Cfib_bound := hCcount
              fibre_nonempty := ?_
              fibre_lower := ?_
              fibre_upper := ?_
              keptParts := g
              kept_parts_subset := hgp
              kept_parts_nonempty := hgne
              kept_intersection_nonempty := hpartsNe
              kept_cover := ?_
              partRetention := L
              part_retention_one := hL
              part_retention_bound := le_rfl
              part_card_retention := hpartCard
              part_volume_retention := ?_
              part_mass_retention := hpartMass }⟩
    · exact Set.iUnion₂_subset fun i hi => Set.subset_iUnion₂
        (s := fun i _ => (Nrm.fine i).shade) i (hqs hi)
    · simpa only [div_eq_mul_inv, mul_comm] using
        ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcarrier href
    · have hmul := ShadedBody.IsCRefinement.mul_multiplicity_le _ _ _ _ href
      rw [ENNReal.coe_inv hLpos.ne'] at hmul
      exact (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hLpos.ne') ENNReal.coe_ne_top).mp hmul
    · intro k hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
    · intro k hk
      rw [hfibre k hk]
      exact (hcounts k (hparent0 hk)).1
    · intro k hk
      rw [hfibre k hk]
      exact (hcounts k (hparent0 hk)).2
    · ext k
      simp only [Finset.mem_biUnion, Finset.mem_inter]
      constructor
      · rintro ⟨part, _, _, hk⟩
        exact hk
      · intro hk
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
        have hkg : k ∈ g.biUnion id := heq ▸ (Finset.mem_filter.mp hi).2
        obtain ⟨part, hp, hkp⟩ := Finset.mem_biUnion.mp hkg
        exact ⟨part, hp, hkp, Finset.mem_image.mpr ⟨i, hi, heq⟩⟩
    · intro part hp
      rw [Tube.sum_volume_carrier_eq_card_mul (Q.tube m) (Q.tube m i0),
        Tube.sum_volume_carrier_eq_card_mul (Q.tube m) (Q.tube m i0)]
      calc
        _ <= ((L : ENNReal) * ((part ∩ parents).card : ENNReal)) *
            volume (Q.tube m i0).carrier := by
          exact mul_le_mul_left (by exact_mod_cast hpartCard part hp) _
        _ = _ := by ring
  let A : NNReal := max Cgeom 2
  let edConstant : ENNReal := 1 + Tube.refineToEssDistinctLeaves.C 3 * (Cgeom : ENNReal)
  let paidConstant : ENNReal := 4 * (Cgeom : ENNReal) * edConstant
  have hA : 1 <= A := (by norm_num : (1 : NNReal) <= 2).trans (le_max_right _ _)
  have hAC : Cgeom <= A := le_max_left _ _
  have hA2 : 2 <= A := le_max_right _ _
  have hCpos : 0 < Cgeom := lt_of_lt_of_le (by norm_num) hC
  have hEDfinite : edConstant ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨by norm_num, ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top⟩
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
      (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
  have hPaidFinite : paidConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hEDfinite
  refine ⟨A, 4, Kout, hAC, hA, by norm_num, le_rfl, ?_⟩
  intro etaPlank zeta etaParent heta heta1 hzeta hParent
  have hcardEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      (Kakeya.Tube.card_le_of_densityIn_le.C 3 : ENNReal) <= (delta : ENNReal) ^ (-1 : Real) :=
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg ENNReal.coe_ne_top (by norm_num)
  have hPaidEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      paidConstant <= (delta : ENNReal) ^ (-zeta) :=
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg hPaidFinite hzeta
  have hLogEvent := Kakeya.VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg
    (A := 1) (B := 4) (by norm_num) (by norm_num) 1 hzeta
  have hUnitEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0, delta < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [hcardEvent, hPaidEvent, hLogEvent, self_mem_nhdsWithin,
    hUnitEvent] with
    delta hCardConstant hPaid hLog hdelta hdelta1
  intro bias hbias hBiasBound iota S T Q Z hQ hfull a m aw bw cw hm hstats O Nrm E
  have hdR : (0 : Real) < delta := hdelta
  have hd1R : (delta : Real) <= 1 := hdelta1.le
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hd1e : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1.le
  have hpow (x : Real) : ENNReal.ofReal ((delta : Real) ^ x) = (delta : ENNReal) ^ x := by
    rw [← ENNReal.ofReal_rpow_of_pos hdR]
    simp only [ENNReal.ofReal_coe_nnreal]
  have hone (x : Real) (hx : 0 <= x) : 1 <= (delta : ENNReal) ^ (-x) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne']
    exact_mod_cast NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (neg_nonpos.mpr hx)
  have hCard : (S.card : ENNReal) <= (delta : ENNReal) ^ (-4 : Real) := by
    have hc := Kakeya.Tube.card_le_of_densityIn_le hdelta.ne'
      (fun i hi => (hQ.geometry.original_ball i hi).trans
        (Metric.closedBall_subset_closedBall (by norm_num : (3 / 4 : Real) <= 1)))
      ((Kakeya.le_maxDensity S (fun i => (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall).trans hQ.maximal_density)
    have hc' : (S.card : ENNReal) <= (Kakeya.Tube.card_le_of_densityIn_le.C 3 : ENNReal) *
        (delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-2 : Real) := by
      rw [show (-2 : Real) = ((-2 : Int) : Real) by norm_num, ENNReal.rpow_intCast]
      simpa only [hpow, show Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 by simp,
        Nat.cast_ofNat, show -((3 : Int) - 1) = -2 by norm_num, ENNReal.rpow_intCast] using hc
    calc
      _ <= (delta : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ (-etaPlank) *
          (delta : ENNReal) ^ (-2 : Real) :=
        hc'.trans (mul_le_mul_left (mul_le_mul_left hCardConstant _) _)
      _ = (delta : ENNReal) ^ (-(etaPlank + 3)) := by
        rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        congr 1 <;> ring
      _ <= (delta : ENNReal) ^ (-4 : Real) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hd1e (by linarith)
  have hsigma1 : sourceEccentricFineScale delta M a <= 1 := by
    exact_mod_cast Nrm.fine_situation.out_le_quarter.trans (by norm_num : (1 / 4 : Real) <= 1)
  let s := Q.cell a O.chosen
  let mass := fun i => volume (Nrm.fine i).shade
  let carrier := fun i => volume (Nrm.fine i).carrier
  have hmasspos : 0 < ∑ i ∈ s, mass i := by
    rw [show (∑ i ∈ s, mass i) =
      affineJacobian Nrm.affine * ∑ i ∈ s, volume (O.innerShade i).shade from
        Nrm.mass_image s le_rfl]
    exact ENNReal.mul_pos Nrm.jacobian_pos.ne' O.inner_mass_pos.ne'
  have hdensity : Kakeya.maxDensity s (fun i => (Nrm.fine i).toConvexSpaceBody) <=
      (Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank) := by
    apply Nrm.maximal_density.trans
    apply mul_le_mul_right
    exact (Kakeya.maxDensity_mono _ (Finset.filter_subset _ _)).trans
      (by simpa only [hpow] using hQ.maximal_density)
  let cost := 1 + Tube.refineToEssDistinctLeaves.C 3 *
    Kakeya.maxDensity s (fun i => (Nrm.fine i).toConvexSpaceBody)
  have hcost : cost <= edConstant * (delta : ENNReal) ^ (-etaPlank) := by
    calc
      _ <= 1 + Tube.refineToEssDistinctLeaves.C 3 *
          ((Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) := by
        exact add_le_add_right (mul_le_mul_right hdensity _) 1
      _ <= (delta : ENNReal) ^ (-etaPlank) + Tube.refineToEssDistinctLeaves.C 3 *
          ((Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) :=
        add_le_add_left (hone etaPlank heta.le) _
      _ = edConstant * (delta : ENNReal) ^ (-etaPlank) := by dsimp [edConstant]; ring
  obtain ⟨ed, heds, hed, hedmass⟩ := Kakeya.exists_pairwise_essDistinct_subfamily_sum_shade_le
    Nrm.fine_pos hsigma1 s Nrm.fine le_rfl
  have hedmass' : (∑ i ∈ s, mass i) <= cost * ∑ i ∈ ed, mass i := by
    simpa [cost, show Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 by simp] using hedmass
  have hedpos : 0 < ∑ i ∈ ed, mass i := by
    by_contra h
    rw [le_antisymm (le_of_not_gt h) zero_le, mul_zero] at hedmass'
    exact (not_le_of_gt hmasspos) hedmass'
  obtain ⟨r, hrs, hrne, hrmass, n, hn, hcounts⟩ := hbin ed (Q.place m) mass hedpos
  let q0 := ed.filter (fun i => Q.place m i ∈ r)
  have hq0ed : q0 <= ed := Finset.filter_subset _ _
  have hq0r : q0.image (Q.place m) = r := by
    ext k
    constructor
    · rintro hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
      exact heq ▸ (Finset.mem_filter.mp hi).2
    · intro hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hrs hk)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, heq.symm ▸ hk⟩, heq⟩
  have hqcounts : forall k, k ∈ q0.image (Q.place m) ->
      n / 2 <= ((q0.filter (fun i => Q.place m i = k)).card : NNReal) /\
      ((q0.filter (fun i => Q.place m i = k)).card : NNReal) <= 2 * n := by
    simpa only [hq0r] using hcounts
  have hLo : 1 <= sourceEccentricLogLoss Kout delta := by
    apply Real.one_le_toNNReal.mpr
    have hinv : 1 <= (1 / (delta : Real)) := (one_le_div hdR).mpr hd1R
    have hl := Real.logb_nonneg (by norm_num : (1 : Real) < 2) hinv
    exact one_le_pow₀ (by linarith : (1 : Real) <= 2 + Real.logb 2 (1 / (delta : Real)))
  let L := sourceEccentricSelectionCost A 4 Kout delta etaPlank zeta
  have hL : 1 <= L := by
    have hp : 1 <= delta ^ (-(4 : Real) * (etaPlank + zeta)) :=
      NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by linarith)
    simpa only [L, sourceEccentricSelectionCost, Nat.cast_ofNat, mul_one] using
      mul_le_mul' (mul_le_mul' hA hLo) hp
  have hCount : 2 <= A * delta ^ (-(4 : Real) * zeta) := by
    apply hA2.trans
    have h : 1 <= delta ^ (-(4 : Real) * zeta) := by
      exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by linarith)
    simpa only [mul_one] using mul_le_mul_right h A
  apply hcore Q O Nrm E hstats ed q0 heds hq0ed hed hedmass' n L
    (A * delta ^ (-(4 : Real) * zeta)) hn hL hCount hqcounts
  have hedne : ed.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hedpos
  have hedCard : (ed.card : ENNReal) <= (delta : ENNReal) ^ (-4 : Real) := by
    have hh : (ed.card : ENNReal) <= S.card := by
      exact_mod_cast Finset.card_le_card (heds.trans (Finset.filter_subset _ _))
    exact hh.trans hCard
  have hedCardR : (ed.card : Real) <= (delta : Real) ^ (-4 : Real) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : Real) <= (delta : Real) ^ (-4 : Real))).mp
    simpa only [hpow, ENNReal.ofReal_natCast] using hedCard
  let binLoss := ENNReal.ofReal (1 + Real.logb 2 (ed.card : Real))
  have hbinLoss : binLoss <= (delta : ENNReal) ^ (-zeta) := by
    apply le_trans (b := ENNReal.ofReal (1 + 4 * Real.logb 2 ((delta : Real)⁻¹)))
    · apply ENNReal.ofReal_le_ofReal
      have hh := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2)
        (by exact_mod_cast hedne.card_pos : (0 : Real) < ed.card) hedCardR
      rw [Real.logb_rpow_eq_mul_logb_of_pos hdR] at hh
      rw [Real.logb_inv]
      linarith
    · simpa only [pow_one] using hLog
  have hLoc : 0 < sourceEccentricLogLoss Kout delta := lt_of_lt_of_le (by norm_num) hLo
  have hfullFine : delta ^ etaPlank / (sourceEccentricLogLoss Kout delta * Cgeom) <=
      ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) := by
    calc
      _ = (delta ^ etaPlank / sourceEccentricLogLoss Kout delta) / Cgeom := (div_div _ _ _).symm
      _ <= (ShadedBody.fullness S (fun i => (Z i).toShadedBody) /
          sourceEccentricLogLoss Kout delta) / Cgeom := by gcongr
      _ <= ShadedBody.fullness s (fun i => (O.innerShade i).toShadedBody) / Cgeom := by
        gcongr
        exact O.inner_fullness
      _ <= _ := Nrm.fullness
  let cFull : ENNReal :=
    (sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank)
  have hlc0 : ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal)) ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr hLoc.ne') (ENNReal.coe_ne_zero.mpr hCpos.ne')
  have hlcfin : (sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hfullFineE : (delta : ENNReal) ^ etaPlank /
      ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal)) <=
      (ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) : ENNReal) := by
    have hh := ENNReal.coe_le_coe.mpr hfullFine
    simpa only [ENNReal.coe_div (mul_pos hLoc hCpos).ne', ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hh
  have hcFull : 1 <= cFull *
      (ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) : ENNReal) := by
    calc
      1 = cFull * ((delta : ENNReal) ^ etaPlank /
          ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal))) := by
        dsimp [cFull]
        rw [div_eq_mul_inv]
        have heq : ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal) *
            (delta : ENNReal) ^ (-etaPlank)) *
            ((delta : ENNReal) ^ etaPlank *
              ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal))⁻¹) =
            (((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal)) *
              ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal))⁻¹) *
              ((delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ etaPlank) := by ring
        rw [heq, ENNReal.mul_inv_cancel hlc0 hlcfin,
          ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        simp
      _ <= _ := mul_le_mul_right hfullFineE _
  have hcarMass : (∑ i ∈ s, carrier i) <= cFull * ∑ i ∈ s, mass i := by
    calc
      _ = 1 * ∑ i ∈ s, carrier i := (one_mul _).symm
      _ <= (cFull * (ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) : ENNReal)) *
          ∑ i ∈ s, carrier i := mul_le_mul_left hcFull _
      _ = cFull * ∑ i ∈ s, mass i := by
        rw [mul_assoc, ← ShadedBody.sum_volumeReal_shade_eq_fullness_mul]
  have hcoeff : 4 * cFull * cost * binLoss <= (L : ENNReal) := by
    calc
      _ <= 4 * cFull * (edConstant * (delta : ENNReal) ^ (-etaPlank)) *
          (delta : ENNReal) ^ (-zeta) := by gcongr
      _ = paidConstant * (sourceEccentricLogLoss Kout delta : ENNReal) *
          ((delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-etaPlank)) *
          (delta : ENNReal) ^ (-zeta) := by dsimp [paidConstant, cFull]; ring
      _ <= (delta : ENNReal) ^ (-zeta) * (sourceEccentricLogLoss Kout delta : ENNReal) *
          ((delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-etaPlank)) *
          (delta : ENNReal) ^ (-zeta) := by gcongr
      _ = (sourceEccentricLogLoss Kout delta : ENNReal) *
          (delta : ENNReal) ^ (-(2 * etaPlank + 2 * zeta)) := by
        calc
          _ = (sourceEccentricLogLoss Kout delta : ENNReal) *
              (((delta : ENNReal) ^ (-zeta) * (delta : ENNReal) ^ (-etaPlank)) *
                (delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-zeta)) := by ring
          _ = _ := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
              ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
              ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            congr 2 <;> ring
      _ <= (A : ENNReal) * (sourceEccentricLogLoss Kout delta : ENNReal) *
          (delta : ENNReal) ^ (-(4 : Real) * (etaPlank + zeta)) := by
        have hexp := ENNReal.rpow_le_rpow_of_exponent_ge hd1e
          (show -(4 : Real) * (etaPlank + zeta) <= -(2 * etaPlank + 2 * zeta) by linarith)
        have hAA : (sourceEccentricLogLoss Kout delta : ENNReal) <=
            (A : ENNReal) * (sourceEccentricLogLoss Kout delta : ENNReal) := by
          simpa only [ENNReal.coe_one, one_mul] using mul_le_mul_left (ENNReal.coe_le_coe.mpr hA) _
        exact mul_le_mul' hAA hexp
      _ = (L : ENNReal) := by
        simp only [L, sourceEccentricSelectionCost, ENNReal.coe_mul,
          ENNReal.coe_rpow_of_ne_zero hdelta.ne', Nat.cast_ofNat]
  calc
    _ <= 4 * (cFull * ∑ i ∈ s, mass i) := mul_le_mul_right hcarMass _
    _ <= 4 * (cFull * (cost * ∑ i ∈ ed, mass i)) :=
      mul_le_mul_right (mul_le_mul_right hedmass' _) _
    _ <= 4 * (cFull * (cost * (binLoss * ∑ i ∈ q0, mass i))) :=
      mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hrmass _) _) _
    _ = (4 * cFull * cost * binLoss) * ∑ i ∈ q0, mass i := by ring
    _ <= (L : ENNReal) * ∑ i ∈ q0, mass i := mul_le_mul_left hcoeff _

set_option maxHeartbeats 4000000 in
/-- The complete assigned Part-B construction with the two level statistics.
All constants, factor identities, same-object witnesses and scale bounds
are exactly those of source_exists_direct_plank_construction. -/
theorem source_exists_terminal_plank_construction
    (N M J : Nat) (e : Real) (eta : Nat -> Real) (etaParent : Real)
    (hwindow : SourceZeroWindowSchedule N M J e eta etaParent)
    (D : NNReal) (hD : 1 <= D) :
    exists (Rnorm : Real) (Cgeom cParent A : NNReal) (p K : Nat),
      64 <= Rnorm /\ 1 <= Cgeom /\ 1 <= cParent /\ Cgeom <= A /\
      1 <= A /\ 1 <= p /\ 1 <= K /\
      forall etaPlank zeta : Real, 0 < etaPlank -> etaPlank <= 1 -> 0 < zeta ->
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall bias : Real, 0 < bias -> bias <= min (etaParent / 16) (etaPlank / 8) ->
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED etaPlank ->
        delta ^ etaPlank <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (a b m : Nat) (aw bw cw : NNReal),
        SourceTerminalPlankStatistics Q Z a m ->
        SourceParentUpperWindow Q sourceBottomED sourceLevelED N eta e a b J ->
        SourceTowerWindow delta M e a b m ->
        forall P : SourceDirectPlankFactors Q Z a m etaParent bias D aw bw cw,
        exists E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw,
          (forall j, forall hj : j ∈ Q.indexSet a,
            (E.factor j hj).parts = (P.factor j hj).parts) /\
          exists X : SourceEccentricAssignedConstruction Q Z E
            Rnorm Cgeom cParent A p K etaPlank zeta,
            SourceEccentricScaleBounds delta M e a b m cParent := by
  set_option maxHeartbeats 4000000 in
  classical
  have hN : (4 : Real) < N := by exact_mod_cast hwindow.count_bound
  have he : 0 < e := by
    rw [hwindow.window_exponent]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hehalf : e < 1 / 2 := by
    rw [hwindow.window_exponent]
    have h := Real.rpow_lt_rpow_of_neg (by norm_num : (0 : Real) < 4) hN
      (by norm_num : -(1 : Real) / 2 < 0)
    convert h using 1 <;> norm_num [Real.rpow_neg, Real.sqrt_eq_rpow]
  obtain ⟨Cout, Kout, hCout, hKout, hout⟩ :=
    source_exists_terminal_eccentric_outer_split M hwindow.level_bound
  obtain ⟨Rnorm, Cin, cParent, hR, hCin, hc, hnorm⟩ :=
    source_exists_eccentric_cell_normalization M hwindow.level_bound e he hehalf
  let Cgeom := max Cout Cin
  have hC : 1 <= Cgeom := hCout.trans (le_max_left _ _)
  have hCo : Cout <= Cgeom := le_max_left _ _
  have hCi : Cin <= Cgeom := le_max_right _ _
  obtain ⟨Asel, psel, K, hCAs, hAs, hps, hKs, hselect⟩ :=
    source_exists_terminal_eccentric_assigned_refinement M hwindow.level_bound
      Rnorm hR Cgeom cParent hC hc D hD Kout hKout
  obtain ⟨Afac, pfac, hCAf, hAf, hpf, hfactor⟩ :=
    source_exists_eccentric_factor_transport Rnorm hR Cgeom cParent D hC hc hD
  let A := max Asel Afac
  let p := max psel pfac
  have hAsA : Asel <= A := le_max_left _ _
  have hAfA : Afac <= A := le_max_right _ _
  have hpsp : psel <= p := le_max_left _ _
  have hpfp : pfac <= p := le_max_right _ _
  have hA : 1 <= A := hAs.trans hAsA
  have hp : 1 <= p := hps.trans hpsp
  have hK : 1 <= K := hKout.trans hKs
  refine ⟨Rnorm, Cgeom, cParent, A, p, K, hR, hC, hc,
    hCAs.trans hAsA, hA, hp, hK, ?_⟩
  intro etaPlank zeta heta heta1 hzeta
  filter_upwards [hout, hnorm,
    hselect etaPlank zeta etaParent heta heta1 hzeta hwindow.parent_positive,
    source_eccentric_normalized_scale_bounds M hwindow.level_bound e he hehalf
      cParent (lt_of_lt_of_le zero_lt_one hc),
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hout hnorm hselect hscale hd
  have hd0 := hd.1
  have hd1 := hd.2.le
  have hlogBase : (1 : Real) <= 2 + Real.logb 2 (1 / (delta : Real)) := by
    have hdReal : 0 < (delta : Real) := by exact_mod_cast hd0
    have h1 : (1 : Real) <= 1 / (delta : Real) :=
      (le_div_iff₀ hdReal).mpr (by simpa only [one_mul] using (show (delta : Real) <= 1 by exact_mod_cast hd1))
    have hlog := Real.logb_nonneg (by norm_num : (1 : Real) < 2) h1
    linarith
  have hLout : 1 <= sourceEccentricLogLoss Kout delta := by
    exact Real.one_le_toNNReal.mpr (one_le_pow₀ hlogBase)
  have hL : 1 <= sourceEccentricLogLoss K delta := by
    exact Real.one_le_toNNReal.mpr (one_le_pow₀ hlogBase)
  have hLmono : sourceEccentricLogLoss Kout delta <= sourceEccentricLogLoss K delta := by
    exact Real.toNNReal_mono (pow_le_pow_right₀ hlogBase hKs)
  let Lsel := sourceEccentricSelectionCost A p K delta etaPlank zeta
  let Lsmall := sourceEccentricSelectionCost Asel psel K delta etaPlank zeta
  have hselOne : 1 <= Lsel := by
    exact one_le_mul (one_le_mul hA hL)
      (NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
          (add_nonneg heta.le hzeta.le)))
  have hsmallOne : 1 <= Lsmall := by
    exact one_le_mul (one_le_mul hAs hL)
      (NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
          (add_nonneg heta.le hzeta.le)))
  have hselMono : Lsmall <= Lsel := by
    exact mul_le_mul' (mul_le_mul' hAsA le_rfl)
      (NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1
        (mul_le_mul_of_nonneg_right (neg_le_neg (by exact_mod_cast hpsp))
          (add_nonneg heta.le hzeta.le)))
  have hcountMono : Asel * delta ^ (-(psel : Real) * zeta) <=
      A * delta ^ (-(p : Real) * zeta) := by
    exact mul_le_mul' hAsA (NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1
      (mul_le_mul_of_nonneg_right (neg_le_neg (by exact_mod_cast hpsp)) hzeta.le))
  intro bias hbias hbiasBound iota S T Q Z hinput hfull a b m aw bw cw hstats hupper hwindowM Pdirect
  obtain ⟨hconstant, E, hparts⟩ := source_direct_plank_eccentric_data Q Z Pdirect
  refine ⟨E, hparts, ?_⟩
  have scales := hscale a b m hupper.fine_bound hupper.separation hwindowM
  have haM : a < M := scales.outer_lt_middle.trans (scales.middle_lt_inner.trans_le scales.inner_bound)
  have hmM : m < M := scales.middle_lt_inner.trans_le scales.inner_bound
  obtain ⟨O0, ⟨ON0⟩⟩ := hout S T Q Z hinput.geometry hstats.same_tubes E.shade_floor a haM hstats.outer_count
  obtain ⟨N0⟩ := hnorm S T Q Z hinput.geometry a b m
    (sourceEccentricLogLoss Kout delta) scales O0
  let Nrm0 : SourceEccentricCellNormalization Q O0 m Rnorm Cgeom cParent :=
    { N0 with
      comparison_one := hC
      outer_replacement_cost := N0.outer_replacement_cost.trans hCi
      fine_volume := fun i hi => (N0.fine_volume i hi).trans (by gcongr)
      parent_volume := fun k hk => (N0.parent_volume k hk).trans (by gcongr)
      fullness := (by gcongr : _ <= _).trans N0.fullness
      maximal_density := N0.maximal_density.trans (by gcongr)
      part_volume_upper := fun part hn hp => (N0.part_volume_upper part hn hp).trans (by gcongr)
      part_thickness_lower := fun part hn hp rank hr =>
        (by gcongr : _ <= _).trans (N0.part_thickness_lower part hn hp rank hr)
      part_thickness_upper := fun part hn hp rank hr =>
        (N0.part_thickness_upper part hn hp rank hr).trans (by gcongr) }
  obtain ⟨P0⟩ := hselect bias hbias hbiasBound S T Q Z hinput hfull
    a m aw bw cw hmM hstats.middle_count O0 Nrm0 E
  have hLoutPos : 0 < sourceEccentricLogLoss Kout delta := zero_lt_one.trans_le hLout
  have hSmallPos : 0 < Lsmall := zero_lt_one.trans_le hsmallOne
  let O : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss K delta) :=
    { O0 with
      fine_refinement := ShadedBody.IsCRefinement.mono (by gcongr) O0.fine_refinement
      refined_mass := O0.refined_mass.trans (by gcongr)
      outer_fullness := (by gcongr : _ <= _).trans O0.outer_fullness
      inner_fullness := (by gcongr : _ <= _).trans O0.inner_fullness
      split_multiplicity := O0.split_multiplicity.trans (by gcongr) }
  let ON : SourceEccentricOuterNormalization Q O Cgeom :=
    { ON0 with
      volume_comparison := fun i hi => (ON0.volume_comparison i hi).trans (by gcongr)
      fullness := (by gcongr : _ <= _).trans ON0.fullness
      maximal_density := ON0.maximal_density.trans (by gcongr) }
  let Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent :=
    { Nrm0 with affine := Nrm0.affine }
  let P : SourceEccentricAssignedSelection Q O Nrm E Lsel
      (A * delta ^ (-(p : Real) * zeta)) :=
    { P0 with
      refinement := ShadedBody.IsCRefinement.mono (by gcongr) P0.refinement
      mass := P0.mass.trans (by gcongr)
      fullness := (by gcongr : _ <= _).trans P0.fullness
      multiplicity := P0.multiplicity.trans (by gcongr)
      Cfib_bound := P0.Cfib_bound.trans hcountMono
      part_retention_bound := P0.part_retention_bound.trans hselMono
      part_mass_retention := fun part hp => (P0.part_mass_retention part hp).trans (by gcongr) }
  obtain ⟨F0⟩ := hfactor hd0 hd1 S T M sourceThreadConstant Q Z a m
    (sourceEccentricLogLoss K delta) etaParent bias aw bw cw hbias O Nrm E
    Lsel (A * delta ^ (-(p : Real) * zeta)) hselOne P
  have hB : 1 <= sourceZeroPlankConstant delta bias := by
    apply one_le_mul
    · apply Real.one_le_toNNReal.mpr
      have h3 : (1 : Real) <= 3 ^ ((9 : Real) / 2) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      nlinarith only [h3]
    · exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hbias.le)
  let H := sourceEccentricTransportCost A Lsel p delta bias
  have hH : sourceEccentricTransportCost Afac Lsel pfac delta bias <= H := by
    exact mul_le_mul' (mul_le_mul' hAfA (pow_le_pow_right₀ hselOne hpfp))
      (pow_le_pow_right₀ hB hpfp)
  let F : SourceEccentricFactorTransport Q P H :=
    { F0 with
      bound_one := F0.bound_one.trans hH
      Cw_bound := F0.Cw_bound.trans hH
      Czero_bound := F0.Czero_bound.trans hH
      aspect := F0.aspect.trans (by gcongr)
      dimensions := fun part hp => by
        rcases F0.dimensions part hp with ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩
        exact ⟨(by gcongr : _ <= _).trans hl0, hu0.trans (by gcongr),
          (by gcongr : _ <= _).trans hl1, hu1.trans (by gcongr),
          (by gcongr : _ <= _).trans hl2, hu2.trans (by gcongr)⟩
      old_hull_volume := fun part hp => (F0.old_hull_volume part hp).trans (by gcongr)
      new_hull_volume := fun part hp => (F0.new_hull_volume part hp).trans (by gcongr)
      original_test_body := fun V => by
        obtain ⟨W, hW, hcover⟩ := F0.original_test_body V
        exact ⟨W, hW.trans (by gcongr), hcover⟩ }
  obtain ⟨datum⟩ := source_exists_eccentric_assigned_partB_datum Q F
  refine ⟨{ outer := O
            outer_normalization := ON
            normalization := Nrm
            selection := P
            factor_transport := F
            assigned := datum
            normalized_scale_positive := scales.fine_positive
            normalized_scale_lower := scales.fine_global_lower
            fine_ball := ?_
            fine_density := ?_
            fine_fullness := ?_
            outer_fullness := ?_
            card_product := ?_
            multiplicity := ?_ }, scales⟩
  · intro i hi
    change (P.shading i).toTube.carrier <= _
    rw [P.same_tubes]
    exact (Nrm.fine_ball i (P.leaves_subset hi)).trans
      (Metric.closedBall_subset_closedBall (by norm_num))
  · have hbody : forall i, (P.shading i).toConvexSpaceBody =
        (Nrm.fine i).toConvexSpaceBody := fun i =>
      congrArg Tube.toConvexSpaceBody (P.same_tubes i)
    rw [Kakeya.maxDensity_congr (fun i _ => hbody i)]
    calc
      Kakeya.maxDensity P.leaves (fun i => (Nrm.fine i).toConvexSpaceBody) <=
          Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toConvexSpaceBody) :=
        Kakeya.maxDensity_mono _ P.leaves_subset
      _ <= (Cgeom : ENNReal) * Kakeya.maxDensity S (fun i => (T i).toConvexSpaceBody) :=
        Nrm.maximal_density.trans (by
          gcongr
          exact Kakeya.maxDensity_mono _ (Finset.filter_subset _ _))
      _ <= (A : ENNReal) * (delta : ENNReal) ^ (-etaPlank) := by
        have hpow : ENNReal.ofReal ((delta : Real) ^ (-etaPlank)) =
            (delta : ENNReal) ^ (-etaPlank) := by
          rw [← ENNReal.ofReal_rpow_of_pos (show (0 : Real) < delta by exact_mod_cast hd0)]
          simp only [ENNReal.ofReal_coe_nnreal]
        exact mul_le_mul' (by exact_mod_cast hCAs.trans hAsA)
          (hinput.maximal_density.trans_eq hpow)
  · calc
      delta ^ etaPlank / (A * sourceEccentricLogLoss K delta * Lsel) <=
          delta ^ etaPlank / (Cgeom * sourceEccentricLogLoss K delta * Lsel) := by
        gcongr
        exact hCAs.trans hAsA
      _ = ((delta ^ etaPlank / sourceEccentricLogLoss K delta) / Cgeom) / Lsel := by
        simp only [div_div, mul_comm Cgeom]
      _ <= ((ShadedBody.fullness S (fun i => (Z i).toShadedBody) /
          sourceEccentricLogLoss K delta) / Cgeom) / Lsel := by gcongr
      _ <= (ShadedBody.fullness (Q.cell a O.chosen)
          (fun i => (O.innerShade i).toShadedBody) / Cgeom) / Lsel := by
        gcongr
        exact O.inner_fullness
      _ <= ShadedBody.fullness (Q.cell a O.chosen)
          (fun i => (Nrm.fine i).toShadedBody) / Lsel := by
        gcongr
        exact Nrm.fullness
      _ <= ShadedBody.fullness P.leaves (fun i => (P.shading i).toShadedBody) := P.fullness
  · exact (by gcongr : delta ^ etaPlank / sourceEccentricLogLoss K delta <=
      ShadedBody.fullness S (fun i => (Z i).toShadedBody) /
        sourceEccentricLogLoss K delta).trans O.outer_fullness
  · exact (mul_le_mul_right (by exact_mod_cast Finset.card_le_card P.leaves_subset)
      (O.outer.card : ENNReal)).trans O.card_product
  · calc
      ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          (sourceEccentricLogLoss K delta : ENNReal) *
            ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) *
            ShadedBody.multiplicity (Q.cell a O.chosen)
              (fun i => (Nrm.fine i).toShadedBody) := by
        rw [Nrm.multiplicity]
        exact O.split_multiplicity
      _ <= (sourceEccentricLogLoss K delta : ENNReal) *
            ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) *
            ((Lsel : ENNReal) * ShadedBody.multiplicity P.leaves
              (fun i => (P.shading i).toShadedBody)) := by
        gcongr
        exact P.multiplicity
      _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- Exact zero-defect quantitative P estimate with two count levels.
The ordinary coefficient, density budget and order of all parameters agree
with the protected direct P estimate; no omega factor is silently removed. -/
theorem source_exists_terminal_plank_exit
    {beta etaParent nuPlank kappa : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hF : FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hparent : 0 < etaParent) (hnu : 0 < nuPlank)
    (hnu_upper : nuPlank <= etaParent * beta / 4)
    (hkappa : 0 <= kappa) (hdensity_budget : kappa * (1 - beta) <= nuPlank / 4)
    (N M J : Nat) (e : Real) (eta : Nat -> Real)
    (hwindow : SourceZeroWindowSchedule N M J e eta etaParent)
    (D : NNReal) (hD : 1 <= D) :
    exists (etaPlank : Real) (K : Nat), 0 < etaPlank /\ 1 <= K /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall bias : Real, 0 < bias ->
        bias <= min (etaParent / 16) (etaPlank / 8) ->
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED etaPlank ->
        delta ^ etaPlank <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (a b m : Nat) (aw bw cw : NNReal),
        SourceTerminalPlankStatistics Q Z a m ->
        SourceParentUpperWindow Q sourceBottomED sourceLevelED N eta e a b J ->
        SourceTowerWindow delta M e a b m ->
        SourceDirectPlankFactors Q Z a m etaParent bias D aw bw cw ->
        Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
          (delta : ENNReal) ^ (-kappa) ->
        (sourceParentPlankConstant delta bias : ENNReal) <= (delta : ENNReal) ^ (-etaPlank) /\
        ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          sourceFixedPreparationLoss K delta * (delta : ENNReal) ^ nuPlank *
            (S.card : ENNReal) ^ beta := by
  set_option maxHeartbeats 4000000 in
  classical
  have hN : (4 : Real) < N := by exact_mod_cast hwindow.count_bound
  have he : 0 < e := by
    rw [hwindow.window_exponent]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hehalf : e < 1 / 2 := by
    rw [hwindow.window_exponent]
    have h := Real.rpow_lt_rpow_of_neg (by norm_num : (0 : Real) < 4) hN
      (by norm_num : -(1 : Real) / 2 < 0)
    convert h using 1 <;> norm_num [Real.rpow_neg, Real.sqrt_eq_rpow]
  let G := etaParent * beta
  have hG : 0 < G := mul_pos hparent hbeta0
  obtain ⟨Rnorm, Cgeom, cParent, A, p, K, hR, hC, hc, hCA, hA, hp, hK, hconstruct⟩ :=
    source_exists_terminal_plank_construction N M J e eta etaParent hwindow D hD
  obtain ⟨eta66, h66, sigma0, hsigma0, hsigma1, hpartB⟩ :=
    source_prop66B_of_assigned_coarse_data.{u, u, u}
      hbeta0 hbeta1 hKT (show 0 < e / 2 by positivity)
      (show e / 2 <= 1 by linarith) (G / 64) (by positivity)
  obtain ⟨etaOuter, hOuter, houter⟩ := source_exists_eccentric_outer_estimate
    hbeta0 hbeta1 hKT M hwindow.level_bound Cgeom hC (G / 64) (by positivity)
  obtain ⟨etaPlank, zeta, hetaPlank, heta1, hzeta, hledger⟩ :=
    source_exists_eccentric_fixed_loss_ledger hbeta0 hbeta1 hG he hehalf h66 hOuter
      A hA p K hp hK
  let C0 : NNReal := Real.toNNReal (4 * (3 : Real) ^ ((9 : Real) / 2) * 2 ^ 6)
  obtain ⟨d0, hd0, hd01, hconst⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg'
    (C0 : Real) (show 0 < etaPlank / 2 by positivity)
  have hcut : (0 : NNReal) < sigma0 ^ (1 / e) := by positivity
  refine ⟨etaPlank, K, hetaPlank, hK, ?_⟩
  filter_upwards [hconstruct etaPlank zeta hetaPlank heta1 hzeta, houter, hledger,
    Ioo_mem_nhdsGT hd0, Ioo_mem_nhdsGT hcut] with delta hconstruct houter hledger hd hdcut
  intro bias hbias hbiasUpper iota S T Q Z hinput hfull a b m aw bw cw hstats
    hupper hwindowM P houterDensity
  have hdeltapos := hd.1
  have hdelta0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hdeltaTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdelta1 : delta <= 1 := hd.2.le.trans hd01
  have hdelta1E : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  have hC0 : (C0 : ENNReal) <= (delta : ENNReal) ^ (-(etaPlank / 2)) := by
    have hc := hconst hd.1 hd.2.le
    have hnn : C0 <= delta ^ (-(etaPlank / 2)) := by exact_mod_cast hc
    have hcoe := ENNReal.coe_le_coe.mpr hnn
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hcoe
  have hCP : (sourceParentPlankConstant delta bias : ENNReal) <=
      (delta : ENNReal) ^ (-etaPlank) := by
    change ((C0 * delta ^ (-3 * bias) : NNReal) : ENNReal) <= _
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hd.1.ne']
    calc (C0 : ENNReal) * (delta : ENNReal) ^ (-3 * bias) <=
          (delta : ENNReal) ^ (-(etaPlank / 2)) * (delta : ENNReal) ^ (-3 * bias) :=
            mul_le_mul' hC0 le_rfl
      _ = (delta : ENNReal) ^ (-(etaPlank / 2) + -3 * bias) :=
        (ENNReal.rpow_add _ _ hdelta0 hdeltaTop).symm
      _ <= (delta : ENNReal) ^ (-etaPlank) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdelta1E
          (by have := hbiasUpper.trans (min_le_right _ _); linarith only [this, hetaPlank])
  obtain ⟨E, hparts, X, scales⟩ := hconstruct bias hbias hbiasUpper S T Q Z
    hinput hfull a b m aw bw cw hstats hupper hwindowM P
  let sigma := sourceEccentricFineScale delta M a
  let L := sourceEccentricSelectionCost A p K delta etaPlank zeta
  let H := sourceEccentricTransportCost A L p delta bias
  have hsigma : sigma <= sigma0 := by
    have hpow := NNReal.rpow_le_rpow hdcut.2.le he.le
    rw [← NNReal.rpow_mul, one_div_mul_cancel he.ne', NNReal.rpow_one] at hpow
    exact scales.fine_global_upper.trans ((div_le_self (by positivity) (by norm_num)).trans hpow)
  obtain ⟨hL, hH, hcost, hcount, hCF, hdim, hfinefull, houterfull, hscalar⟩ :=
    hledger bias hbias (hbiasUpper.trans (min_le_right _ _)) sigma
      scales.fine_global_lower scales.fine_global_upper
  have hB := hpartB X.selection.leaves scales.fine_positive X.selection.shading hsigma
    X.fine_ball X.selection.essentially_distinct (hfinefull.trans X.fine_fullness)
    (sourceEccentricParentScale delta M a m cParent)
    X.factor_transport.factors.uniformThin X.factor_transport.factors.uniformMid
    X.factor_transport.factors.uniformThin_le_uniformMid
    (X.factor_transport.factors.uniformMid_le_one X.selection.parent_ball)
    X.selection.parents X.normalization.parent X.selection.n X.selection.Cfib
    (Kakeya.GlobalPlankFactorization.partBFrostmanConst X.factor_transport.Cw X.factor_transport.Czero)
    X.factor_transport.Czero (Kakeya.plankReadingConst X.factor_transport.Cw X.factor_transport.Czero ^ 2)
    (X.factor_transport.Czero_bound.trans hcost) (X.assigned.frostman_budget.trans hCF)
    (X.selection.Cfib_bound.trans hcount) (X.assigned.dimensions_budget.trans hdim)
    scales.coarse_scale_lower X.assigned.parent_le_thin X.assigned.datum
    X.assigned.coarse_fibres_nonempty X.assigned.dimensions X.assigned.capture
  have hO := houter S T Q Z hinput.geometry a (sourceEccentricLogLoss K delta)
    (scales.outer_lt_middle.trans (scales.middle_lt_inner.trans_le scales.inner_bound))
    X.outer X.outer_normalization (houterfull.trans X.outer_fullness)
  have haspect : (X.factor_transport.factors.uniformThin : ENNReal) /
      (X.factor_transport.factors.uniformMid : ENNReal) <=
      3 * (H : ENNReal) ^ 3 * ((aw : ENNReal) / (bw : ENNReal)) := by
    have hbpos : 0 < bw := P.short_positive.trans_le P.short_le_middle
    have hmidpos : 0 < X.factor_transport.factors.uniformMid :=
      scales.parent_positive.trans_le (X.assigned.parent_le_thin.trans
        X.factor_transport.factors.uniformThin_le_uniformMid)
    have hh := ENNReal.coe_le_coe.mpr X.assigned.aspect
    simpa only [ENNReal.coe_div hmidpos.ne', ENNReal.coe_mul, ENNReal.coe_pow,
      ENNReal.coe_ofNat, ENNReal.coe_div hbpos.ne'] using hh
  have hinner : ShadedBody.multiplicity X.selection.leaves
      (fun i => (X.selection.shading i).toShadedBody) <=
      (sigma : ENNReal) ^ (-(G / 64)) *
        ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
        (3 * (H : ENNReal) ^ 3) ^ beta *
        ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
        (X.selection.leaves.card : ENNReal) ^ beta := by
    calc _ <= (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3 * ((aw : ENNReal) / (bw : ENNReal))) ^ beta *
          (X.selection.leaves.card : ENNReal) ^ beta := by
            exact hB.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow X.fine_density (sub_nonneg.mpr hbeta1)))
              (ENNReal.rpow_le_rpow haspect hbeta0.le)) le_rfl)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta0.le]; ring
  have hcard : (X.outer.outer.card : ENNReal) ^ beta *
      (X.selection.leaves.card : ENNReal) ^ beta <=
      (2 : ENNReal) ^ beta * (S.card : ENNReal) ^ beta := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hbeta0.le,
      ← ENNReal.mul_rpow_of_nonneg _ _ hbeta0.le]
    exact ENNReal.rpow_le_rpow X.card_product hbeta0.le
  have hraw : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      (delta : ENNReal) ^ (-(G / 2)) *
        Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
          (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
        (S.card : ENNReal) ^ beta := by
    calc _ <= (sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
        ((delta : ENNReal) ^ (-(G / 64)) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * (X.outer.outer.card : ENNReal) ^ beta) *
        ((sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta *
          ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          (X.selection.leaves.card : ENNReal) ^ beta) :=
            X.multiplicity.trans (mul_le_mul' (mul_le_mul' le_rfl hO) hinner)
      _ = ((sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
          (delta : ENNReal) ^ (-(G / 64)) * (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          ((X.outer.outer.card : ENNReal) ^ beta *
            (X.selection.leaves.card : ENNReal) ^ beta) := by ring
      _ <= ((sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
          (delta : ENNReal) ^ (-(G / 64)) * (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          ((2 : ENNReal) ^ beta * (S.card : ENNReal) ^ beta) := by gcongr
      _ = ((sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
          (delta : ENNReal) ^ (-(G / 64)) * (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta * (2 : ENNReal) ^ beta) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          (S.card : ENNReal) ^ beta := by ring
      _ <= _ := mul_le_mul' (mul_le_mul' (mul_le_mul' hscalar le_rfl) le_rfl) le_rfl
  have hratio : (aw : ENNReal) / (bw : ENNReal) <= (delta : ENNReal) ^ etaParent := by
    have hcoe := ENNReal.coe_le_coe.mpr P.eccentric
    simpa only [ENNReal.coe_div (P.short_positive.trans_le P.short_le_middle).ne',
      ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hcoe
  have hgain : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      (delta : ENNReal) ^ nuPlank * (S.card : ENNReal) ^ beta := by
    calc _ <= (delta : ENNReal) ^ (-(G / 2)) *
          ((delta : ENNReal) ^ (-kappa)) ^ (1 - beta) *
          ((delta : ENNReal) ^ etaParent) ^ beta * (S.card : ENNReal) ^ beta :=
            hraw.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow houterDensity (sub_nonneg.mpr hbeta1)))
              (ENNReal.rpow_le_rpow hratio hbeta0.le)) le_rfl)
      _ = (delta : ENNReal) ^ (etaParent * beta / 2 - kappa * (1 - beta)) *
          (S.card : ENNReal) ^ beta := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_add _ _ hdelta0 hdeltaTop,
          ← ENNReal.rpow_add _ _ hdelta0 hdeltaTop]
        dsimp [G]
        congr 2 <;> ring
      _ <= _ := mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hdelta1E
        (by nlinarith only [hnu_upper, hdensity_budget, hnu])) le_rfl
  refine ⟨hCP, hgain.trans ?_⟩
  have hLone : 1 <= sourceFixedPreparationLoss K delta := by
    change 1 <= (sourceEccentricLogLoss K delta : ENNReal)
    apply ENNReal.coe_le_coe.mpr
    apply Real.one_le_toNNReal.mpr
    apply one_le_pow₀
    have hdReal : 0 < (delta : Real) := by exact_mod_cast hd.1
    have h1 : (1 : Real) <= 1 / (delta : Real) :=
      (le_div_iff₀ hdReal).mpr (by simpa only [one_mul] using
        (show (delta : Real) <= 1 by exact_mod_cast hdelta1))
    have := Real.logb_nonneg (by norm_num : (1 : Real) < 2) h1
    linarith
  simpa only [one_mul] using mul_le_mul' (mul_le_mul' hLone
    (le_refl ((delta : ENNReal) ^ nuPlank))) (le_refl ((S.card : ENNReal) ^ beta))

end Kakeya.ML2Core

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricScaleLedger
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The actual one-scale weighted split and its selected full assigned cell.
The coarse shading need not be contained in the original fine shade union. -/
structure SourceEccentricOuterSplit (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) (a : Nat) (L : NNReal) where
  outer : Finset iota
  outer_subset : outer <= Q.indexSet a
  outer_nonempty : outer.Nonempty
  outerShade : iota -> ShadedTube (sourceTowerRadius delta M a) (EuclideanSpace Real (Fin 3))
  outer_tubes : forall i, (outerShade i).toTube = Q.tube a i
  innerShade : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))
  inner_tubes : forall i, (innerShade i).toTube = T i
  inner_subshade : forall i, (innerShade i).shade <= (Z i).shade
  chosen : iota
  chosen_mem : chosen ∈ outer
  chosen_cell_nonempty : (Q.cell a chosen).Nonempty
  refinedFine : Finset iota
  refined_fine_eq : refinedFine = S.filter (fun i => Q.place a i ∈ outer)
  fine_refinement : ShadedBody.IsCRefinement refinedFine (fun i => (innerShade i).toShadedBody)
    S (fun i => (Z i).toShadedBody) L⁻¹
  refined_mass : (∑ i ∈ S, volume (Z i).shade) <=
    (L : ENNReal) * ∑ i ∈ refinedFine, volume (innerShade i).shade
  fine_under_outer : forall i, i ∈ refinedFine ->
    (innerShade i).shade <= (outerShade (Q.place a i)).shade
  outer_fullness : ShadedBody.fullness S (fun i => (Z i).toShadedBody) / L <=
    ShadedBody.fullness outer (fun i => (outerShade i).toShadedBody)
  inner_fullness : ShadedBody.fullness S (fun i => (Z i).toShadedBody) / L <=
    ShadedBody.fullness (Q.cell a chosen) (fun i => (innerShade i).toShadedBody)
  inner_mass_pos : 0 < ∑ i ∈ Q.cell a chosen, volume (innerShade i).shade
  split_multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    (L : ENNReal) * ShadedBody.multiplicity outer (fun i => (outerShade i).toShadedBody) *
      ShadedBody.multiplicity (Q.cell a chosen) (fun i => (innerShade i).toShadedBody)
  card_product : (outer.card : ENNReal) * ((Q.cell a chosen).card : ENNReal) <=
    2 * (S.card : ENNReal)
  outer_density : Kakeya.maxDensity outer (fun i => (Q.tube a i).toConvexSpaceBody) <=
    Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody)

/-- A single fixed homothety and genuine unit-core replacement resolve the B3
outer window. The two mass identities name the very same outer shade witness. -/
structure SourceEccentricOuterNormalization (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))} {a : Nat} {L : NNReal}
    (O : SourceEccentricOuterSplit Q Z a L) (Cgeom : NNReal) where
  affine : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3)
  affine_eq : forall x, affine x = (1 / 8 : Real) • x
  tubes : iota -> ShadedTube (sourceTowerRadius delta M a / 8) (EuclideanSpace Real (Fin 3))
  shade_image : forall i, i ∈ O.outer -> (tubes i).shade = affine '' (O.outerShade i).shade
  carrier_image : forall i, i ∈ O.outer -> affine '' (Q.tube a i).carrier <= (tubes i).carrier
  volume_comparison : forall i, i ∈ O.outer -> volume (tubes i).carrier <=
    (Cgeom : ENNReal) * volume (affine '' (Q.tube a i).carrier)
  ball : forall i, i ∈ O.outer -> (tubes i).carrier <= Metric.closedBall 0 1
  jacobian_pos : 0 < affineJacobian affine
  jacobian_finite : affineJacobian affine < (⊤ : ENNReal)
  mass_image : (∑ i ∈ O.outer, volume (tubes i).shade) =
    affineJacobian affine * ∑ i ∈ O.outer, volume (O.outerShade i).shade
  union_image : volume (⋃ i ∈ O.outer, (tubes i).shade) =
    affineJacobian affine * volume (⋃ i ∈ O.outer, (O.outerShade i).shade)
  multiplicity : ShadedBody.multiplicity O.outer (fun i => (tubes i).toShadedBody) =
    ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody)
  fullness : ShadedBody.fullness O.outer (fun i => (O.outerShade i).toShadedBody) / Cgeom <=
    ShadedBody.fullness O.outer (fun i => (tubes i).toShadedBody)
  maximal_density : Kakeya.maxDensity O.outer (fun i => (tubes i).toConvexSpaceBody) <=
    (Cgeom : ENNReal) * Kakeya.maxDensity (Q.indexSet a)
      (fun i => (Q.tube a i).toConvexSpaceBody)

set_option maxHeartbeats 1600000 in
/-- The split and its outer normalization are actual outputs on Q, with fixed
losses chosen before delta, the shading and the selected level. -/
theorem source_exists_eccentric_outer_split (M : Nat) (hM : 2 <= M) :
    exists (Cgeom : NNReal) (K : Nat), 1 <= Cgeom /\ 1 <= K /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceTowerGeometry Q sourceBottomED sourceLevelED ->
        SourceTowerStatistics Q Z ->
        (forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <=
          volume (Z i).shade) ->
        forall a : Nat, a < M ->
        exists O : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss K delta),
          Nonempty (SourceEccentricOuterNormalization Q O Cgeom) :=
  set_option maxHeartbeats 1600000 in
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
        (hstats : SourceTowerStatistics Q Z) (ha : a <= M)
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
            (hstats.same_tubes i)
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
              congrArg Tube.toConvexSpaceBody (hstats.same_tubes i)
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
      refine ⟨A, hA, hAne', Za, Zi, j, hj, hZa, (fun i => (hZi i).trans (hstats.same_tubes i)),
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
            Finset.sum_le_sum (fun k hk => hstats.descendant_count a ha j (hA hj) k hk)
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
    intro iota S T Q Z hg hs hfloor a ha
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
          (hs.same_tubes i)
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
      hsplit Q Z hg hs ha.le hd hscale hscale1 hfull
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

/-- This actual outer estimate treats a=0 by the fixed root cardinal bound.
For a>0 the genuine normalized outer family enters the generalized KT estimate. -/
theorem source_exists_eccentric_outer_estimate {beta : Real}
    (hbeta : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (M : Nat) (hM : 2 <= M) (Cgeom : NNReal) (hC : 1 <= Cgeom)
    (eps : Real) (heps : 0 < eps) :
    exists etaOuter : Real, 0 < etaOuter /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceTowerGeometry Q sourceBottomED sourceLevelED ->
        forall (a : Nat) (L : NNReal), a < M ->
        forall O : SourceEccentricOuterSplit Q Z a L,
        SourceEccentricOuterNormalization Q O Cgeom ->
        delta ^ etaOuter <= ShadedBody.fullness O.outer (fun i => (O.outerShade i).toShadedBody) ->
        ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) <=
          (delta : ENNReal) ^ (-eps) *
            Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
              (1 - beta) * (O.outer.card : ENNReal) ^ beta := by
  have hMr : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  have hC0 : 0 < Cgeom := zero_lt_one.trans_le hC
  obtain ⟨eta, heta, rho0, hrho0, hbound⟩ :=
    KatzTaoEstimate.exists_threshold_multiplicity_bound_univ hbeta.le hKT
      (eps / 4) (by positivity)
  let etaOuter := eta / (2 * (M : Real))
  have hetaOuter : 0 < etaOuter := by dsimp [etaOuter]; positivity
  have hcut : (0 : NNReal) < rho0 ^ (M : Real) := by positivity
  refine ⟨etaOuter, hetaOuter, ?_⟩
  filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : Real) < 1),
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num), Ioo_mem_nhdsGT hcut,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (Cgeom : ENNReal)) ENNReal.coe_ne_top hetaOuter,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (Cgeom : ENNReal) ^ (1 - beta)) (by finiteness) (by positivity : 0 < eps / 2),
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((1280 : ENNReal) ^ 6) ^ (1 - beta)) (by finiteness) heps]
    with delta hd hdhalf hdcut hCfull hCcost hrootcost
  have hd0 := hd.2.2.1
  have hd1 : delta <= 1 := hdhalf.2.le.trans (by norm_num)
  have hd0E : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd0.ne'
  have hCfull' : Cgeom <= delta ^ (-etaOuter) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd0.ne'] at hCfull
    exact ENNReal.coe_le_coe.mp hCfull
  have hsmall : delta ^ (1 / (M : Real)) <= rho0 := by
    have h := NNReal.rpow_le_rpow hdcut.2.le (by positivity : 0 <= 1 / (M : Real))
    rwa [← NNReal.rpow_mul, mul_one_div_cancel hMr.ne', NNReal.rpow_one] at h
  intro iota S T Q Z hgeom a L ha O Nrm hfull
  have hr0 : 0 < sourceTowerRadius delta M a := by
    have h := hd.2.2.2.2.1 a ha
    exact lt_of_lt_of_le (by positivity) h
  have hD1 : 1 <= Kakeya.maxDensity (Q.indexSet a)
      (fun i => (Q.tube a i).toConvexSpaceBody) := by
    refine Kakeya.one_le_maxDensity ⟨O.chosen, O.outer_subset O.chosen_mem, ?_⟩
    apply lt_of_lt_of_le _ (Tube.le_volume (Q.tube a O.chosen))
    have h := Tube.le_volume.c_pos (Module.finrank Real (EuclideanSpace Real (Fin 3)))
    positivity
  by_cases ha0 : a = 0
  · subst a
    have hroot : sourceTowerRadius delta M 0 = (1 / 40 : NNReal) := by
      simp [sourceTowerRadius, show 0 < M by omega]
    have hcardReal : ((Q.indexSet 0).card : Real) <= (1280 : Real) ^ 6 := by
      have h := hgeom.coarse_card 0 ha
      norm_num [hroot] at h ⊢
      exact h
    have hcard : (O.outer.card : ENNReal) <= (1280 : ENNReal) ^ 6 := by
      have h := (show (O.outer.card : Real) <= (Q.indexSet 0).card by
        exact_mod_cast Finset.card_le_card O.outer_subset).trans hcardReal
      exact_mod_cast h
    calc ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) <=
          ((1280 : ENNReal) ^ 6) ^ (1 - beta) * (O.outer.card : ENNReal) ^ beta :=
            multiplicity_le_of_card_le hbeta1 hcard
      _ <= (delta : ENNReal) ^ (-eps) * (O.outer.card : ENNReal) ^ beta := by gcongr
      _ <= (delta : ENNReal) ^ (-eps) *
          Kakeya.maxDensity (Q.indexSet 0) (fun i => (Q.tube 0 i).toConvexSpaceBody) ^
            (1 - beta) * (O.outer.card : ENNReal) ^ beta := by
          have hpow : 1 <= Kakeya.maxDensity (Q.indexSet 0)
              (fun i => (Q.tube 0 i).toConvexSpaceBody) ^ (1 - beta) :=
            by simpa only [ENNReal.one_rpow] using
              ENNReal.rpow_le_rpow hD1 (sub_nonneg.mpr hbeta1)
          simpa only [mul_one] using mul_le_mul'
            (mul_le_mul' (le_refl ((delta : ENNReal) ^ (-eps))) hpow)
            (le_refl ((O.outer.card : ENNReal) ^ beta))
  · let rho := sourceTowerRadius delta M a / 8
    have hrho : 0 < rho := div_pos hr0 (by norm_num)
    have hrhou : rho <= delta ^ (1 / (M : Real)) := by
      have hpow : delta ^ ((a : Real) / (M : Real)) <= delta ^ (1 / (M : Real)) :=
        NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1
          (div_le_div_of_nonneg_right (by exact_mod_cast (show 1 <= a by omega)) hMr.le)
      calc rho = ((1 / 40 : NNReal) * delta ^ ((a : Real) / (M : Real))) / 8 := by
            simp [rho, sourceTowerRadius, ha]
        _ <= delta ^ ((a : Real) / (M : Real)) := by
            rw [div_le_iff₀ (show (0 : NNReal) < 8 by norm_num)]
            nlinarith only [show (0 : NNReal) <= delta ^ ((a : Real) / (M : Real)) from bot_le]
        _ <= delta ^ (1 / (M : Real)) := hpow
    have hrhol : delta ^ (2 : Nat) <= rho := by
      change delta ^ (2 : Nat) <= sourceTowerRadius delta M a / 8
      rw [le_div_iff₀ (show (0 : NNReal) < 8 by norm_num)]
      have h := hd.2.2.2.2.1 a ha
      have hh := mul_le_mul_of_nonneg_left hdhalf.2.le delta.2
      nlinarith only [h, hh]
    have hfullN : rho ^ eta <= ShadedBody.fullness O.outer (fun i => (Nrm.tubes i).toShadedBody) := by
      apply le_trans _ Nrm.fullness
      rw [le_div_iff₀ hC0]
      calc rho ^ eta * Cgeom <= (delta ^ (1 / (M : Real))) ^ eta * delta ^ (-etaOuter) := by gcongr
        _ = delta ^ etaOuter := by
            rw [← NNReal.rpow_mul, ← NNReal.rpow_add hd0.ne']
            dsimp [etaOuter]
            congr 1 <;> field_simp <;> ring
        _ <= ShadedBody.fullness O.outer (fun i => (O.outerShade i).toShadedBody) := hfull
    have hKTbound := hbound rho hrho (hrhou.trans hsmall) O.outer Nrm.tubes Nrm.ball hfullN
    have hrhocost : (rho : ENNReal) ^ (-(eps / 4)) <= (delta : ENNReal) ^ (-(eps / 2)) := by
      calc (rho : ENNReal) ^ (-(eps / 4)) <= ((delta : ENNReal) ^ (2 : Nat)) ^ (-(eps / 4)) :=
            by simpa only [ENNReal.coe_pow] using
              rpow_neg_le_rpow_neg_of_le hrhol (by linarith only [heps] : 0 <= eps / 4)
        _ = (delta : ENNReal) ^ (-(eps / 2)) := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            congr 1 <;> norm_num <;> ring
    rw [Nrm.multiplicity] at hKTbound
    calc ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) <=
          (rho : ENNReal) ^ (-(eps / 4)) *
            Kakeya.maxDensity O.outer (fun i => (Nrm.tubes i).toConvexSpaceBody) ^ (1 - beta) *
              (O.outer.card : ENNReal) ^ beta := hKTbound
      _ <= (delta : ENNReal) ^ (-(eps / 2)) *
          ((Cgeom : ENNReal) * Kakeya.maxDensity (Q.indexSet a)
            (fun i => (Q.tube a i).toConvexSpaceBody)) ^ (1 - beta) * (O.outer.card : ENNReal) ^ beta := by
          gcongr
          exact Nrm.maximal_density
      _ = ((delta : ENNReal) ^ (-(eps / 2)) * (Cgeom : ENNReal) ^ (1 - beta)) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^ (1 - beta) *
            (O.outer.card : ENNReal) ^ beta := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith only [hbeta1])]; ac_rfl
      _ <= ((delta : ENNReal) ^ (-(eps / 2)) * (delta : ENNReal) ^ (-(eps / 2))) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^ (1 - beta) *
            (O.outer.card : ENNReal) ^ beta := by gcongr
      _ = (delta : ENNReal) ^ (-eps) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^ (1 - beta) *
            (O.outer.card : ENNReal) ^ beta := by
          rw [← ENNReal.rpow_add _ _ hd0E ENNReal.coe_ne_top]
          congr 3 <;> ring

end Kakeya.ML2Core

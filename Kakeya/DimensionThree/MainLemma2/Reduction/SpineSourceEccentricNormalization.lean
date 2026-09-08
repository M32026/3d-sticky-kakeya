/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricNormalizationData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Reduction

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

set_option maxHeartbeats 3000000 in
/-- All normalizations and transverse comparisons are outputs of one real
construction on the original geometry. Its constants precede every scale. -/
theorem source_exists_eccentric_cell_normalization (M : Nat) (hM : 2 <= M)
    (e : Real) (he : 0 < e) (hehalf : e < 1 / 2) :
    exists (Rnorm : Real) (Cgeom cParent : NNReal),
      64 <= Rnorm /\ 1 <= Cgeom /\ 1 <= cParent /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceTowerGeometry Q sourceBottomED sourceLevelED ->
        forall (a b m : Nat) (L : NNReal),
        SourceEccentricScaleBounds delta M e a b m cParent ->
        forall O : SourceEccentricOuterSplit Q Z a L,
          Nonempty (SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent) := by
  refine ⟨64, 2 ^ 100, 16, by norm_num, by norm_num, by norm_num,
    Filter.Eventually.of_forall ?_⟩
  intro delta iota S T Q Z G a b m L Hs O
  have hFine {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C a b m : Nat}
      {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
      {e : Real} {cParent L : NNReal} (Q : SourceThreadedTower S T M C)
      (Hs : SourceEccentricScaleBounds delta M e a b m cParent)
      (O : SourceEccentricOuterSplit Q Z a L) :
      exists (hpos : 0 < sourceTowerRadius delta M a)
        (U : iota -> ShadedTube (sourceEccentricFineScale delta M a) (EuclideanSpace Real (Fin 3))),
      let A := spineRescaleUnit hpos (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
      U = outerFamily hpos (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
        (sourceEccentricFineScale delta M a) O.innerShade /\
      (forall i, i ∈ Q.cell a O.chosen -> (U i).shade = A '' (O.innerShade i).shade) /\
      (forall i, i ∈ Q.cell a O.chosen -> A '' (T i).carrier <= (U i).carrier) /\
      (forall i, i ∈ Q.cell a O.chosen -> volume (U i).carrier <=
        (outerLoss 64 : ENNReal) * volume (A '' (T i).carrier)) /\
      (forall i, i ∈ Q.cell a O.chosen -> (U i).carrier <= Metric.closedBall 0 (13 / 16)) /\
      (forall q : Finset iota, q <= Q.cell a O.chosen ->
        (∑ i ∈ q, volume (U i).shade) = affineJacobian A * ∑ i ∈ q, volume (O.innerShade i).shade) /\
      (forall q : Finset iota, q <= Q.cell a O.chosen ->
        volume (⋃ i ∈ q, (U i).shade) = affineJacobian A * volume (⋃ i ∈ q, (O.innerShade i).shade)) /\
      ShadedBody.multiplicity (Q.cell a O.chosen) (fun i => (U i).toShadedBody) =
        ShadedBody.multiplicity (Q.cell a O.chosen) (fun i => (O.innerShade i).toShadedBody) /\
      ShadedBody.fullness (Q.cell a O.chosen) (fun i => (O.innerShade i).toShadedBody) / outerLoss 64 <=
        ShadedBody.fullness (Q.cell a O.chosen) (fun i => (U i).toShadedBody) /\
      Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (U i).toConvexSpaceBody) <=
        (outerLoss 64 : ENNReal) * Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (T i).toConvexSpaceBody) := by
    classical
    have htheta : 0 < sourceTowerRadius delta M a :=
      Hs.delta_pos.trans_le (Hs.original_to_middle.trans Hs.middle_to_outer)
    have htheta1 : sourceTowerRadius delta M a <= 1 := Hs.outer_root.trans (by norm_num [div_le_iff₀])
    have haM : a <= M := by have := Hs.outer_lt_middle; have := Hs.middle_lt_inner; have := Hs.inner_bound; omega
    have hdt : delta <= sourceTowerRadius delta M a := Hs.original_to_middle.trans Hs.middle_to_outer
    have hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M a) delta
        (sourceEccentricFineScale delta M a) 64 3 := by
      refine ⟨htheta, hdt, htheta1, Hs.fine_positive, ?_, ?_, ?_⟩
      · exact_mod_cast Hs.fine_small.trans (by norm_num [div_le_iff₀] : (1 / 16 : NNReal) <= 1 / 4)
      · change ((delta / (4 * sourceTowerRadius delta M a) : NNReal) : Real) <= _
        push_cast
        gcongr
        have h : (0 : Real) <= (sourceTowerRadius delta M a : Real) := NNReal.coe_nonneg _
        linarith
      · norm_num [Tube.normalization.C]
    have hratio : (delta : Real) / (sourceTowerRadius delta M a : Real) <=
        4 * (sourceEccentricFineScale delta M a : Real) := by
      unfold sourceEccentricFineScale
      push_cast
      field_simp
      exact le_rfl
    have hsub : forall i, i ∈ Q.cell a O.chosen ->
        (O.innerShade i).carrier <= (Q.tube a O.chosen).carrier := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have hplace : Q.place a i = O.chosen := (Finset.mem_filter.mp hi).2
      have h := Q.leaf_containment a haM i hiS
      rw [hplace] at h
      change (O.innerShade i).toTube.carrier <= _
      rw [O.inner_tubes i]
      exact h
    let A := spineRescaleUnit htheta (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
    let U := outerFamily htheta (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
      (sourceEccentricFineScale delta M a) O.innerShade
    have hshade : forall i, i ∈ Q.cell a O.chosen ->
        (U i).shade = A '' (O.innerShade i).shade := by
      intro i hi
      exact outerShadedTube_shade_eq (by simp) hsit (by norm_num) hratio
        (Q.tube a O.chosen) (O.innerShade i) (hsub i hi)
    have himage : forall i, i ∈ Q.cell a O.chosen ->
        A '' (T i).carrier <= (U i).carrier := by
      intro i hi
      have h := spineImage_le_outerShadedTube (by simp) hsit (by norm_num) hratio
        (Q.tube a O.chosen) (O.innerShade i) (hsub i hi)
      change A '' (O.innerShade i).toTube.carrier <= (U i).carrier at h
      simpa only [O.inner_tubes i] using h
    have hvol : forall i, i ∈ Q.cell a O.chosen -> volume (U i).carrier <=
        (outerLoss 64 : ENNReal) * volume (A '' (T i).carrier) := by
      intro i hi
      have h := outerShadedTube_volume_le (by simp) hsit (by norm_num) hratio
        (Q.tube a O.chosen) (O.innerShade i) (hsub i hi)
      change volume (U i).carrier <= (outerLoss 64 : ENNReal) *
        volume (A '' (O.innerShade i).toTube.carrier) at h
      simpa only [O.inner_tubes i] using h
    refine ⟨htheta, U, rfl, hshade, himage, hvol, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hamb : A '' (Q.tube a O.chosen).carrier <= Metric.closedBall 0 (1 / 4) := by
        rintro x ⟨y, hy, rfl⟩
        change spineRescaleUnit htheta (Q.tube a O.chosen) _ y ∈ _
        rw [spineRescaleUnit_apply]
        exact Tube.rescale_image_ambient_subset_closedBall htheta htheta1
          (by norm_num : (0 : Real) < 64) (by norm_num [Tube.normalization.C])
          (Q.tube a O.chosen) (Set.mem_image_of_mem _ hy)
      have hT : (T i).carrier <= (Q.tube a O.chosen).carrier := by
        have h := hsub i hi
        change (O.innerShade i).toTube.carrier <= _ at h
        simpa only [O.inner_tubes i] using h
      have hx : A (T i).x ∈ Metric.closedBall 0 (1 / 4) :=
        hamb (Set.mem_image_of_mem A (hT (Tube.x_mem_carrier _)))
      have hy : A (T i).y ∈ Metric.closedBall 0 (1 / 4) :=
        hamb (Set.mem_image_of_mem A (hT (Tube.y_mem_carrier _)))
      have hmid : midpoint Real (A (T i).x) (A (T i).y) ∈ Metric.closedBall 0 (1 / 4) :=
        (convex_closedBall (0 : EuclideanSpace Real (Fin 3)) (1 / 4)).midpoint_mem hx hy
      have hcent : midpoint Real (U i).toTube.x (U i).toTube.y =
          midpoint Real (A (T i).x) (A (T i).y) := by
        change (outerTube htheta (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
          (sourceEccentricFineScale delta M a) (O.innerShade i).toTube).center = _
        rw [O.inner_tubes i, outerTube, Tube.center_centredExtension]
        simp only [A, spineRescaleUnit_apply]
      refine (Tube.carrier_subset_closedBall_midpoint (EuclideanSpace Real (Fin 3)) (U i).toTube).trans
        (Metric.closedBall_subset_closedBall' ?_)
      rw [hcent]
      have hmidnorm := Metric.mem_closedBall.mp hmid
      have hsmall : (sourceEccentricFineScale delta M a : Real) <= 1 / 16 := by exact_mod_cast Hs.fine_small
      linarith
    · intro q hq
      calc (∑ i ∈ q, volume (U i).shade) =
          ∑ i ∈ q, affineJacobian A * volume (O.innerShade i).shade := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hshade i (hq hi), volume_image_affineEquiv]
        _ = _ := (Finset.mul_sum _ _ _).symm
    · intro q hq
      rw [← volume_image_affineEquiv]
      congr 1
      simp only [Set.image_iUnion]
      apply Set.iUnion_congr
      intro i
      apply Set.iUnion_congr
      intro hi
      exact hshade i (hq hi)
    · exact outerFamily_multiplicity (by simp) hsit (by norm_num) hratio hsub
    · simpa only [div_eq_mul_inv, mul_comm] using
        outerFamily_le_fullness (by simp) hsit (by norm_num) (by norm_num) hratio hsub
    · have h := outerFamily_maxDensity_le (by simp) hsit (by norm_num) (by norm_num) hratio hsub
      have hT : (fun i => (O.innerShade i).toConvexSpaceBody) = (fun i => (T i).toConvexSpaceBody) := by
        funext i
        change (O.innerShade i).toTube.toConvexSpaceBody = _
        rw [O.inner_tubes i]
      simpa only [hT] using h
  have hFineParent {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
      {theta delta tau : NNReal} (htheta : 0 < theta) (htheta1 : theta <= 1)
      (hdelta : delta <= tau) (T0 : Tube theta E) (T : Tube delta E) (P : Tube tau E)
      (hTP : T.toConvexSpaceBody <= P.toConvexSpaceBody) :
      (outerTube htheta T0 (by norm_num : (0 : Real) < 64) (delta / (4 * theta)) T).toConvexSpaceBody <=
        (outerTube htheta T0 (by norm_num : (0 : Real) < 64) (16 * tau / theta) P).toConvexSpaceBody := by
    have hcentered {p q r s : E} (hpq : p ≠ q) (hrs : r ≠ s)
        {ell eps : Real} (hell : 0 < ell) (heps : 0 <= eps)
        (hlen : ell <= ‖q - p‖) (hlen' : ell <= ‖s - r‖)
        (hclose : (‖p - r‖ <= eps /\ ‖q - s‖ <= eps) \/
          (‖p - s‖ <= eps /\ ‖q - r‖ <= eps))
        {sigma rho : NNReal} (hroom : eps + 2 * eps / ell + (sigma : Real) <= rho) :
        (Tube.centredExtension sigma hpq).toConvexSpaceBody <=
          (Tube.centredExtension rho hrs).toConvexSpaceBody := by
      have hunit : forall v w : E, 0 < ‖v‖ -> 0 < ‖w‖ ->
          ‖‖v‖⁻¹ • v - ‖w‖⁻¹ • w‖ <= 2 * ‖v - w‖ / ‖v‖ := by
        intro v w hv hw
        have heq : ‖v‖⁻¹ • v - ‖w‖⁻¹ • w =
            ‖v‖⁻¹ • (v - w) + (‖v‖⁻¹ - ‖w‖⁻¹) • w := by module
        rw [heq]
        have hn := norm_add_le (‖v‖⁻¹ • (v - w)) ((‖v‖⁻¹ - ‖w‖⁻¹) • w)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hv)] at hn
        have hscalar : |‖v‖⁻¹ - ‖w‖⁻¹| * ‖w‖ = |‖w‖ - ‖v‖| / ‖v‖ := by
          rw [inv_sub_inv hv.ne' hw.ne', abs_div, abs_mul, abs_of_pos hv, abs_of_pos hw]
          field_simp
        rw [hscalar] at hn
        have hnormdiff : |‖w‖ - ‖v‖| <= ‖v - w‖ := by
          simpa only [norm_sub_rev] using abs_norm_sub_norm_le w v
        calc ‖‖v‖⁻¹ • (v - w) + (‖v‖⁻¹ - ‖w‖⁻¹) • w‖ <=
              ‖v‖⁻¹ * ‖v - w‖ + |‖w‖ - ‖v‖| / ‖v‖ := hn
          _ <= ‖v‖⁻¹ * ‖v - w‖ + ‖v - w‖ / ‖v‖ := by gcongr
          _ = _ := by ring
      let U := Tube.centredExtension sigma hpq
      let W := Tube.centredExtension rho hrs
      have hUc : U.midpoint = midpoint Real p q := by
        change (1 / 2 : Real) • (U.x + U.y) = _
        have h := Tube.center_centredExtension (s := sigma) hpq
        change midpoint Real U.x U.y = _ at h
        simpa only [midpoint_eq_smul_add, invOf_eq_inv, one_div] using h
      have hWc : W.midpoint = midpoint Real r s := by
        change (1 / 2 : Real) • (W.x + W.y) = _
        have h := Tube.center_centredExtension (s := rho) hrs
        change midpoint Real W.x W.y = _ at h
        simpa only [midpoint_eq_smul_add, invOf_eq_inv, one_div] using h
      have hUd : U.direction = ‖q - p‖⁻¹ • (q - p) := Tube.direction_centredExtension hpq
      have hWd : W.direction = ‖s - r‖⁻¹ • (s - r) := Tube.direction_centredExtension hrs
      have hcorepos : 0 < ‖q - p‖ := hell.trans_le hlen
      have hcorepos' : 0 < ‖s - r‖ := hell.trans_le hlen'
      have hmid : forall p' q' r' s' : E, ‖p' - r'‖ <= eps -> ‖q' - s'‖ <= eps ->
          ‖midpoint Real p' q' - midpoint Real r' s'‖ <= eps := by
        intro p' q' r' s' hp hq
        rw [midpoint_eq_smul_add, midpoint_eq_smul_add]
        have heq : (2 : Real)⁻¹ • (p' + q') - (2 : Real)⁻¹ • (r' + s') =
            (2 : Real)⁻¹ • ((p' - r') + (q' - s')) := by module
        rw [invOf_eq_inv, heq, norm_smul]
        norm_num
        have hn := norm_add_le (p' - r') (q' - s')
        nlinarith
      have hvec : forall p' q' r' s' : E, ‖p' - r'‖ <= eps -> ‖q' - s'‖ <= eps ->
          ‖(q' - p') - (s' - r')‖ <= 2 * eps := by
        intro p' q' r' s' hp hq
        have heq : (q' - p') - (s' - r') = (q' - s') - (p' - r') := by abel
        rw [heq]
        exact (norm_sub_le _ _).trans (by linarith)
      have hdir : ‖U.direction - W.direction‖ <= 4 * eps / ell \/
          ‖U.direction - W.reverse.direction‖ <= 4 * eps / ell := by
        rcases hclose with ⟨hp, hq⟩ | ⟨hp, hq⟩
        · left
          rw [hUd, hWd]
          calc ‖‖q - p‖⁻¹ • (q - p) - ‖s - r‖⁻¹ • (s - r)‖ <=
              2 * ‖(q - p) - (s - r)‖ / ‖q - p‖ := hunit _ _ hcorepos hcorepos'
            _ <= 2 * (2 * eps) / ell := by gcongr; exact hvec _ _ _ _ hp hq
            _ = _ := by ring
        · right
          rw [Tube.reverse_direction, hUd, hWd]
          have heq : -(‖s - r‖⁻¹ • (s - r)) = ‖r - s‖⁻¹ • (r - s) := by
            rw [norm_sub_rev r s, ← smul_neg, neg_sub]
          rw [heq]
          calc ‖‖q - p‖⁻¹ • (q - p) - ‖r - s‖⁻¹ • (r - s)‖ <=
              2 * ‖(q - p) - (r - s)‖ / ‖q - p‖ :=
                hunit _ _ hcorepos (by simpa only [norm_sub_rev] using hcorepos')
            _ <= 2 * (2 * eps) / ell := by gcongr; exact hvec _ _ _ _ hp hq
            _ = _ := by ring
      have hmidUW : ‖U.midpoint - W.midpoint‖ <= eps := by
        rw [hUc, hWc]
        rcases hclose with ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact hmid _ _ _ _ hp hq
        · rw [_root_.midpoint_comm (R := Real) r s]
          exact hmid _ _ _ _ hp hq
      have hroom' : eps + (4 * eps / ell) / 2 + (sigma : Real) <= rho := by
        convert hroom using 1 <;> ring
      rcases hdir with hd | hd
      · exact Tube.tube_carrier_subset_of_close U W hd hmidUW hroom'
      · have hWr : W.reverse.midpoint = W.midpoint := by
          simp only [Tube.midpoint, Tube.reverse_x, Tube.reverse_y, add_comm]
        have hm : ‖U.midpoint - W.reverse.midpoint‖ <= eps := by rwa [hWr]
        exact Tube.tube_carrier_subset_of_close U W.reverse hd hm hroom'
    let A := spineRescaleUnit htheta T0 (by norm_num : (0 : Real) < 64)
    have hlen {s : NNReal} (U : Tube s E) : (1 / 256 : Real) <= ‖A U.y - A U.x‖ := by
      have h := Tube.dist_le_dist_normalization htheta htheta1 T0 U.y U.x
      have hdist : dist U.y U.x = 1 := by simpa only [dist_eq_norm] using U.norm_direction
      rw [hdist] at h
      change (1 / 256 : Real) <= ‖spineRescaleUnit htheta T0 _ U.y - spineRescaleUnit htheta T0 _ U.x‖
      rw [spineRescaleUnit_apply, spineRescaleUnit_apply, ← dist_eq_norm,
        Tube.dist_rescaleMap T0 (by norm_num : (0 : Real) < 64)]
      norm_num
      linarith
    have hclose {x y : E} (hxy : ‖x - y‖ <= 3 * (tau : Real)) :
        ‖A x - A y‖ <= 3 * (tau : Real) / (256 * (theta : Real)) := by
      have h := Tube.dist_normalization_le htheta htheta1 T0 x y
      rw [dist_eq_norm] at h
      change ‖spineRescaleUnit htheta T0 _ x - spineRescaleUnit htheta T0 _ y‖ <= _
      rw [spineRescaleUnit_apply, spineRescaleUnit_apply, ← dist_eq_norm,
        Tube.dist_rescaleMap T0 (by norm_num : (0 : Real) < 64)]
      calc dist (T0.normalization x) (T0.normalization y) / (4 * 64) <=
          ((theta : Real)⁻¹ * (3 * (tau : Real))) / (4 * 64) := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            calc dist (T0.normalization x) (T0.normalization y) <= (theta : Real)⁻¹ * dist x y :=
                Tube.dist_normalization_le htheta htheta1 T0 x y
              _ <= _ := by rw [dist_eq_norm]; gcongr
        _ = _ := by ring
    have hends := Tube.endpoints_close_of_body_le T P hTP
    have hends' : (‖A T.x - A P.x‖ <= 3 * (tau : Real) / (256 * (theta : Real)) ∧
        ‖A T.y - A P.y‖ <= 3 * (tau : Real) / (256 * (theta : Real))) ∨
        (‖A T.x - A P.y‖ <= 3 * (tau : Real) / (256 * (theta : Real)) ∧
        ‖A T.y - A P.x‖ <= 3 * (tau : Real) / (256 * (theta : Real))) :=
      hends.imp (fun h => ⟨hclose h.1, hclose h.2⟩) (fun h => ⟨hclose h.1, hclose h.2⟩)
    have hroom : 3 * (tau : Real) / (256 * (theta : Real)) +
        2 * (3 * (tau : Real) / (256 * (theta : Real))) / (1 / 256) +
        ((delta / (4 * theta) : NNReal) : Real) <= ((16 * tau / theta : NNReal) : Real) := by
      have ht : (0 : Real) < theta := by exact_mod_cast htheta
      have hd : (delta : Real) <= tau := by exact_mod_cast hdelta
      push_cast
      apply (mul_le_mul_iff_right₀ ht).mp
      field_simp
      nlinarith only [hd, tau.coe_nonneg]
    have hne {s : NNReal} (U : Tube s E) : A U.x ≠ A U.y := by
      intro heq
      have h := hlen U
      rw [heq, sub_self, norm_zero] at h
      norm_num at h
    have h := hcentered (hne T) (hne P)
      (ell := (1 / 256 : Real)) (eps := 3 * (tau : Real) / (256 * (theta : Real)))
      (by norm_num) (by positivity) (hlen T) (hlen P) hends' hroom
    simpa only [outerTube, A, spineRescaleUnit_apply] using h
  have hParentFamily {theta tau : NNReal} (htheta : 0 < theta)
      (htheta1 : theta <= 1) (htau : 0 < tau) (htautheta : tau <= theta)
      (hsmall : 16 * tau / theta <= (1 / 64 : NNReal))
      (r : Finset iota) (T0 : Tube theta (EuclideanSpace Real (Fin 3)))
      (T : iota -> Tube tau (EuclideanSpace Real (Fin 3)))
      (hT : ∀ i ∈ r, (T i).carrier <= T0.carrier) :
      let A := spineRescaleUnit htheta T0 (by norm_num : (0 : Real) < 64)
      let P := fun i => outerTube htheta T0 (by norm_num : (0 : Real) < 64) (16 * tau / theta) (T i)
      (∀ i ∈ r, A '' (T i).carrier <= (P i).carrier) ∧
      (∀ i ∈ r, (P i).carrier <= Metric.closedBall 0 1) ∧
      (∀ q : Finset iota, q.Nonempty -> q <= r ->
        A '' (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier <=
          (q.convexHull_biUnion (fun i => (P i).toConvexSpaceBody)).carrier ∧
        volume (q.convexHull_biUnion (fun i => (P i).toConvexSpaceBody)).carrier <=
          ((2 ^ 100 : NNReal) : ENNReal) * affineJacobian A *
            volume (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier ∧
        ∀ n : Nat, n = 1 \/ n = 2 ->
          ethickness Real (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier n /
            (((2 ^ 100 : NNReal) : ENNReal) * (theta : ENNReal)) <=
            ethickness Real (q.convexHull_biUnion (fun i => (P i).toConvexSpaceBody)).carrier n ∧
          ethickness Real (q.convexHull_biUnion (fun i => (P i).toConvexSpaceBody)).carrier n <=
            ((2 ^ 100 : NNReal) : ENNReal) / theta *
              ethickness Real (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier n) := by
    have hParentHomothety {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
        [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
        {theta tau sigma : NNReal} {R : Real}
        (hsit : Tube.IsRescalingSituation theta tau sigma R 3) (hR : 0 < R)
        (T0 : Tube theta E) (T : Tube tau E) (hT : T.carrier <= T0.carrier)
        (c : NNReal) (hc : 1 <= c) :
        let A := spineRescaleUnit hsit.pos_ambient T0 hR
        let V := outerTube hsit.pos_ambient T0 hR (c * sigma) T
        V.carrier <= (fun x => (16 * R * (c : Real)) • (x - A T.center) + A T.center) ''
          (A '' T.carrier) := by
      classical
      dsimp only
      let A := spineRescaleUnit hsit.pos_ambient T0 hR
      let V := outerTube hsit.pos_ambient T0 hR (c * sigma) T
      let U := outerTube hsit.pos_ambient T0 hR sigma T
      have hcR : (1 : Real) <= c := by exact_mod_cast hc
      have hc0 : (0 : Real) < c := zero_lt_one.trans_le hcR
      have hcenter : V.center = U.center := by
        dsimp [V, U, outerTube]
        rw [Tube.center_centredExtension, Tube.center_centredExtension]
      have hdir : V.direction = U.direction := by
        dsimp [V, U, outerTube]
        rw [Tube.direction_centredExtension, Tube.direction_centredExtension]
      have hVU : V.carrier <= (Kakeya.Tube.dilate U (c : Real)).carrier := by
        intro z hz
        have hz1 := Tube.subset_dilate V (c := (1 : Real)) le_rfl hz
        obtain ⟨s, hs, hzdist⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate V (by norm_num) hz1
        apply Kakeya.Tube.mem_dilate_of_dist_axis_le U hc0 (s := s)
        · exact hs.trans (by linarith)
        · simpa only [hcenter, hdir, one_mul, NNReal.coe_mul, dist_eq_norm] using hzdist
      have hback := Tube.preimage_rescale_dilate_subset_dilate hsit
        (κ := (2 : Real)) (c := (c : Real)) (by norm_num) hcR T0 T
        (Tube.perp_norm_direction_le_of_subset T0 T hT)
        (rescaleMap_x_ne_rescaleMap_y hsit.pos_ambient T0 hR T)
      intro z hz
      have hzpre : A.symm z ∈ (Kakeya.Tube.dilate T (16 * R * (c : Real))).carrier := by
        have h : T0.rescaleMap R (A.symm z) ∈ (Kakeya.Tube.dilate U (c : Real)).carrier := by
          rw [← spineRescaleUnit_apply hsit.pos_ambient T0 hR]
          change A (A.symm z) ∈ _
          rw [A.apply_symm_apply]
          exact hVU hz
        simpa only [show 4 * ((2 : Real) + 2) = 16 by norm_num] using hback h
      have hzdil : A.symm z ∈
          AffineMap.homothety T.center (16 * R * (c : Real)) '' T.carrier := by
        simpa [Kakeya.Tube.dilate] using hzpre
      obtain ⟨x, hx, heq⟩ := hzdil
      refine ⟨A x, Set.mem_image_of_mem A hx, ?_⟩
      have himg := congrArg A heq
      rw [A.apply_symm_apply] at himg
      rw [← himg]
      change (16 * R * (c : Real)) • (A x - A T.center) + A T.center =
        A (AffineMap.homothety T.center (16 * R * (c : Real)) x)
      symm
      simpa only [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply_module'] using
        A.apply_lineMap T.center x (16 * R * (c : Real))
    have hHullHomothety (q : Finset iota) (hq : q.Nonempty)
        (W V : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
        (lam : NNReal) (hlam : 1 <= lam)
        (hWpos : ∀ i ∈ q, 0 < volume (W i).carrier)
        (hWV : ∀ i ∈ q, W i <= V i)
        (hhom : ∀ i ∈ q, ∃ p ∈ (W i).carrier,
          (V i).carrier <= (fun x => (lam : Real) • (x - p) + p) '' (W i).carrier) :
        q.convexHull_biUnion W <= q.convexHull_biUnion V ∧
        volume (q.convexHull_biUnion V).carrier <=
          (384 * lam ^ 3 : NNReal) * volume (q.convexHull_biUnion W).carrier ∧
        ∀ n : Nat, ethickness Real (q.convexHull_biUnion V).carrier n <=
          (2 * lam : NNReal) * ethickness Real (q.convexHull_biUnion W).carrier n := by
      classical
      let K := q.convexHull_biUnion W
      have hWK : ∀ i ∈ q, W i <= K := fun i hi => Finset.le_convexHull_biUnion W hi
      have hlamR : (1 : Real) <= lam := by exact_mod_cast hlam
      have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
      have hinc : q.convexHull_biUnion W <= q.convexHull_biUnion V :=
        (hq.convexHull_biUnion_le_iff W _).mpr fun i hi =>
          (hWV i hi).trans (Finset.le_convexHull_biUnion V hi)
      suffices hthin : ∀ n : Nat, ethickness Real (q.convexHull_biUnion V).carrier n <=
          (2 * lam : NNReal) * ethickness Real K.carrier n by
        refine ⟨hinc, ?_, hthin⟩
        have hu := volume_le_prod_ethickness (q.convexHull_biUnion V).carrier
        have hl := K.convex.ethickness_prod_le_volume
        norm_num [Finset.prod_range_succ, Metric.lt_volume_convexHull.c] at hu hl
        have hp : (ethickness Real (q.convexHull_biUnion V).carrier 0 *
            ethickness Real (q.convexHull_biUnion V).carrier 1 *
            ethickness Real (q.convexHull_biUnion V).carrier 2) <=
            ((2 * lam : NNReal) : ENNReal) ^ 3 *
              (ethickness Real K.carrier 0 * ethickness Real K.carrier 1 * ethickness Real K.carrier 2) := by
          calc _ <= (((2 * lam : NNReal) : ENNReal) * ethickness Real K.carrier 0) *
              (((2 * lam : NNReal) : ENNReal) * ethickness Real K.carrier 1) *
              (((2 * lam : NNReal) : ENNReal) * ethickness Real K.carrier 2) :=
                mul_le_mul' (mul_le_mul' (hthin 0) (hthin 1)) (hthin 2)
            _ = _ := by ring
        calc volume (q.convexHull_biUnion V).carrier <=
            8 * (ethickness Real (q.convexHull_biUnion V).carrier 0 *
              ethickness Real (q.convexHull_biUnion V).carrier 1 *
              ethickness Real (q.convexHull_biUnion V).carrier 2) := hu
          _ <= 8 * (((2 * lam : NNReal) : ENNReal) ^ 3 *
              (ethickness Real K.carrier 0 * ethickness Real K.carrier 1 * ethickness Real K.carrier 2)) :=
            mul_le_mul_left' hp 8
          _ = ((384 * lam ^ 3 : NNReal) : ENNReal) *
              (6⁻¹ * (ethickness Real K.carrier 0 * ethickness Real K.carrier 1 * ethickness Real K.carrier 2)) := by
            norm_num [ENNReal.coe_mul, ENNReal.coe_pow, mul_pow]
            have hnum : (384 : ENNReal) * 6⁻¹ = 64 := by
              change (((384 : NNReal) : ENNReal) * ((6 : NNReal) : ENNReal)⁻¹) = ((64 : NNReal) : ENNReal)
              rw [← ENNReal.coe_inv, ← ENNReal.coe_mul] <;> norm_num
            calc _ = ((384 : ENNReal) * 6⁻¹) * lam ^ 3 *
                (ethickness Real K.carrier 0 * ethickness Real K.carrier 1 * ethickness Real K.carrier 2) := by
                  rw [hnum]
                  ring
              _ = _ := by ring
          _ <= _ := mul_le_mul_left' hl _
      intro n
      rw [le_mul_ethickness_iff _ _ _
        (ENNReal.coe_ne_zero.mpr (by positivity)) ENNReal.coe_ne_top]
      intro r A hA hs
      have hsub : (q.convexHull_biUnion V).carrier <=
          cthickening ((2 * lam * r : NNReal) : Real) (A : Set (EuclideanSpace Real (Fin 3))) := by
        apply (hq.convexHull_biUnion_subset_iff V (A.convex.cthickening _).isConvexSet).mpr
        intro i hi y hy
        obtain ⟨p, hp, hVp⟩ := hhom i hi
        obtain ⟨x, hx, rfl⟩ := hVp hy
        have hclosed : IsClosed (A : Set (EuclideanSpace Real (Fin 3))) :=
          AffineSubspace.closed_of_finiteDimensional _
        have hpA := hs (hWK i hi hp)
        have hxA := hs (hWK i hi hx)
        rw [hclosed.cthickening_eq_biUnion_closedBall r.coe_nonneg] at hpA hxA
        obtain ⟨p', hp', hpp'⟩ := Set.mem_iUnion₂.mp hpA
        obtain ⟨x', hx', hxx'⟩ := Set.mem_iUnion₂.mp hxA
        have hp0 : ‖p - p'‖ <= (r : Real) := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hpp'
        have hx0 : ‖x - x'‖ <= (r : Real) := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hxx'
        have hyA : (lam : Real) • (x' - p') + p' ∈ A := by
          simpa only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using
            AffineMap.homothety_mem hp' (lam : Real) hx'
        apply Metric.mem_cthickening_of_dist_le _ _ _ _ hyA
        rw [dist_eq_norm]
        have heq : (lam : Real) • (x - p) + p - ((lam : Real) • (x' - p') + p') =
            (lam : Real) • (x - x') + (1 - (lam : Real)) • (p - p') := by module
        rw [heq]
        calc ‖(lam : Real) • (x - x') + (1 - (lam : Real)) • (p - p')‖ <=
            ‖(lam : Real) • (x - x')‖ + ‖(1 - (lam : Real)) • (p - p')‖ := norm_add_le _ _
          _ = (lam : Real) * ‖x - x'‖ + ((lam : Real) - 1) * ‖p - p'‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg lam.coe_nonneg, abs_of_nonpos (by linarith)]
            ring
          _ <= (lam : Real) * r + ((lam : Real) - 1) * r := by gcongr
          _ <= ((2 * lam * r : NNReal) : Real) := by
            push_cast
            nlinarith only [r.coe_nonneg]
      simpa only [ENNReal.coe_mul] using ethickness_le_of_cthickening (2 * lam * r) hA hsub
    have hVolumeThickness (K N : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
        (hKpos : 0 < volume K.carrier)
        (hKzero : (1 / 2 : ENNReal) <= ethickness Real K.carrier 0)
        (hNball : N.carrier <= Metric.closedBall 0 1)
        (c D theta : NNReal) (htheta : 0 < theta)
        (hvol : (c : ENNReal) * volume K.carrier <=
          (theta : ENNReal) ^ 2 * volume N.carrier)
        (hupper : forall n : Nat, n = 1 \/ n = 2 ->
          (theta : ENNReal) * ethickness Real N.carrier n <=
            (D : ENNReal) * ethickness Real K.carrier n) :
        forall n : Nat, n = 1 \/ n = 2 ->
          (c : ENNReal) * ethickness Real K.carrier n <=
            (96 * D * theta : NNReal) * ethickness Real N.carrier n := by
      have hkfin (n : Nat) : ethickness Real K.carrier n ≠ (⊤ : ENNReal) :=
        (ethickness_lt_top K.isCompact.isBounded n).ne
      have hnfin (n : Nat) : ethickness Real N.carrier n ≠ (⊤ : ENNReal) :=
        (ethickness_lt_top N.isCompact.isBounded n).ne
      have hkpos (n : Nat) (hn : n < 3) : 0 < (ethickness Real K.carrier n).toReal := by
        apply ENNReal.toReal_pos
        · exact ethickness_ne_zero_of_volume_pos hKpos (by simpa using hn)
        · exact hkfin n
      have hnzero : ethickness Real N.carrier 0 <= (1 : ENNReal) :=
        ethickness_le_of_subset_closedBall 1 hNball 0
      have hlower := K.convex.ethickness_prod_le_volume
      have huppervol := volume_le_prod_ethickness N.carrier
      norm_num [Finset.prod_range_succ, Metric.lt_volume_convexHull.c] at hlower huppervol
      have hk0 : (1 / 2 : Real) <= (ethickness Real K.carrier 0).toReal := by
        simpa using ENNReal.toReal_mono (hkfin 0) hKzero
      have hn0 : (ethickness Real N.carrier 0).toReal <= (1 : Real) := by
        simpa using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hnzero
      have hlowerR := ENNReal.toReal_mono K.isCompact.measure_lt_top.ne hlower
      have hupperR := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hnfin 0) (hnfin 1)) (hnfin 2))) huppervol
      have hvolR := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by simp) N.isCompact.measure_lt_top.ne) hvol
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.coe_toReal] at hlowerR hupperR hvolR
      change (6 : Real)⁻¹ *
        ((ethickness Real K.carrier 0).toReal * (ethickness Real K.carrier 1).toReal *
          (ethickness Real K.carrier 2).toReal) <= (volume K.carrier).toReal at hlowerR
      change (c : Real) * (volume K.carrier).toReal <=
        (theta : Real) ^ 2 * (volume N.carrier).toReal at hvolR
      norm_num at hlowerR
      have hprod : (c : Real) *
          ((ethickness Real K.carrier 1).toReal * (ethickness Real K.carrier 2).toReal) <=
          96 * (theta : Real) ^ 2 *
            ((ethickness Real N.carrier 1).toReal * (ethickness Real N.carrier 2).toReal) := by
        have hk12 : (0 : Real) <=
            (ethickness Real K.carrier 1).toReal * (ethickness Real K.carrier 2).toReal := by positivity
        have hn12 : (0 : Real) <=
            (ethickness Real N.carrier 1).toReal * (ethickness Real N.carrier 2).toReal := by positivity
        have hk : (ethickness Real K.carrier 1).toReal * (ethickness Real K.carrier 2).toReal <=
            12 * (volume K.carrier).toReal := by
          nlinarith only [hlowerR, mul_le_mul_of_nonneg_right hk0 hk12]
        have hn : (volume N.carrier).toReal <=
            8 * ((ethickness Real N.carrier 1).toReal * (ethickness Real N.carrier 2).toReal) := by
          nlinarith only [hupperR, mul_le_mul_of_nonneg_right hn0 hn12]
        calc _ <= (c : Real) * (12 * (volume K.carrier).toReal) := by gcongr
          _ <= 12 * ((theta : Real) ^ 2 * (volume N.carrier).toReal) := by nlinarith only [hvolR]
          _ <= _ := by nlinarith only [mul_le_mul_of_nonneg_left hn (sq_nonneg (theta : Real))]
      have hu (n : Nat) (hn : n = 1 \/ n = 2) :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (hkfin n)) (hupper n hn)
      simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hu
      have hreal1 : (c : Real) * (ethickness Real K.carrier 1).toReal <=
          96 * D * theta * (ethickness Real N.carrier 1).toReal := by
        apply le_of_mul_le_mul_right _ (hkpos 2 (by omega))
        have h := mul_le_mul_of_nonneg_left (hu 2 (Or.inr rfl))
          (show 0 <= 96 * (theta : Real) * (ethickness Real N.carrier 1).toReal by positivity)
        nlinarith only [hprod, h]
      have hreal2 : (c : Real) * (ethickness Real K.carrier 2).toReal <=
          96 * D * theta * (ethickness Real N.carrier 2).toReal := by
        apply le_of_mul_le_mul_left _ (hkpos 1 (by omega))
        have h := mul_le_mul_of_nonneg_left (hu 1 (Or.inl rfl))
          (show 0 <= 96 * (theta : Real) * (ethickness Real N.carrier 2).toReal by positivity)
        nlinarith only [hprod, h]
      intro n hn
      apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top (hkfin n))
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (hnfin n))).mp
      simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_ofNat]
      rcases hn with rfl | rfl
      · exact hreal1
      · exact hreal2
    have hJacobian {theta : NNReal} (htheta : 0 < theta)
        (T0 : Tube theta (EuclideanSpace Real (Fin 3))) :
        let A := spineRescaleUnit htheta T0 (by norm_num : (0 : Real) < 64)
        affineJacobian A = ((1 / 256 ^ 3 : NNReal) : ENNReal) * (theta : ENNReal)⁻¹ ^ (2 : Nat) ∧
        affineJacobian A = ENNReal.ofReal (4 * (64 : Real)) ^ (-(3 : Real)) *
          (theta : ENNReal) ^ (-(2 : Real)) := by
      let A := spineRescaleUnit htheta T0 (by norm_num : (0 : Real) < 64)
      have hjac : affineJacobian A = ENNReal.ofReal ((4 * (64 : Real))⁻¹ ^ (3 : Nat)) *
          (theta : ENNReal)⁻¹ ^ (2 : Nat) := by
        let B := (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).carrier
        have hB0 : volume B ≠ 0 := ConvexSpaceBody.closedUnitBall_volume_pos.ne'
        have hBt : volume B ≠ ⊤ :=
          (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).isCompact'.measure_lt_top.ne
        apply (ENNReal.mul_left_inj hB0 hBt).mp
        rw [← volume_image_affineEquiv]
        have hm : (A : EuclideanSpace Real (Fin 3) -> EuclideanSpace Real (Fin 3)) = T0.rescaleMap 64 :=
          spineRescaleUnit_coe htheta T0 _
        rw [hm, Tube.volume_image_rescaleMap htheta (by norm_num : (0 : Real) < 64) T0 B]
        norm_num [mul_assoc]
      refine ⟨?_, ?_⟩
      · rw [hjac]
        congr 1
        norm_num [← ENNReal.ofReal_coe_nnreal]
      · rw [hjac, ENNReal.rpow_neg, ENNReal.rpow_neg]
        norm_cast
        simp only [inv_pow, ENNReal.coe_pow]
        congr 1 <;> norm_num [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_pow, ENNReal.inv_pow]
    classical
    let A := spineRescaleUnit htheta T0 (by norm_num : (0 : Real) < 64)
    let P := fun i => outerTube htheta T0 (by norm_num : (0 : Real) < 64) (16 * tau / theta) (T i)
    let W := fun i => (T i).toConvexSpaceBody.mapAffine A
    let V := fun i => (P i).toConvexSpaceBody
    have hscale16 : tau <= 16 * tau := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) <= 16)
        (show (0 : NNReal) <= tau from bot_le)
    have hsigma : tau / theta <= (1 / 4 : NNReal) := by
      have h : tau / theta <= 16 * tau / theta := div_le_div_of_nonneg_right hscale16 (by positivity)
      exact h.trans (hsmall.trans (by norm_num [div_le_iff₀]))
    have hsit : Tube.IsRescalingSituation theta tau (tau / theta) 64 3 := by
      refine ⟨htheta, htautheta, htheta1, div_pos htau htheta, ?_, ?_, ?_⟩
      · exact_mod_cast hsigma
      · push_cast; exact le_rfl
      · norm_num [Tube.normalization.C]
    have himage : ∀ i ∈ r, W i <= V i := by
      intro i hi
      have hspec := outerTube_spec (by simp) hsit (by norm_num) (by
        push_cast
        have h : (0 : Real) <= (tau : Real) / theta := by positivity
        linarith) T0 (T i) (hT i hi)
      refine hspec.1.trans ?_
      let U := outerTube htheta T0 (by norm_num : (0 : Real) < 64) (tau / theta) (T i)
      have hr : tau / theta <= 16 * tau / theta := div_le_div_of_nonneg_right hscale16 (by positivity)
      change U.carrier <= _
      have h := Tube.le_rescale U hr
      exact h
    have hhom : ∀ i ∈ r, ∃ p ∈ (W i).carrier,
        (V i).carrier <= (fun x => (16384 : Real) • (x - p) + p) '' (W i).carrier := by
      intro i hi
      refine ⟨A (T i).center, Set.mem_image_of_mem A (Tube.center_mem_carrier _), ?_⟩
      have h := hParentHomothety hsit (by norm_num) T0 (T i) (hT i hi) 16 (by norm_num)
      dsimp only at h
      have hr : (16 : NNReal) * (tau / theta) = 16 * tau / theta := by ring
      rw [hr] at h
      norm_num only [NNReal.coe_ofNat, show 16 * (64 : Real) * 16 = 16384 by norm_num] at h
      exact h
    have hWpos : ∀ i ∈ r, 0 < volume (W i).carrier := by
      intro i hi
      rw [ConvexSpaceBody.volume_mapAffine]
      exact ENNReal.mul_pos (affineJacobian_ne_zero A) (ML2Shaded.volume_carrier_ne_zero htau (T i))
    have hball : ∀ i ∈ r, (P i).carrier <= Metric.closedBall 0 1 := by
      intro i hi
      have hamb : A '' T0.carrier <= Metric.closedBall 0 (1 / 4) := by
        rintro z ⟨x, hx, rfl⟩
        rw [spineRescaleUnit_apply]
        exact Tube.rescale_image_ambient_subset_closedBall htheta htheta1
          (by norm_num : (0 : Real) < 64) (by norm_num [Tube.normalization.C]) T0
          (Set.mem_image_of_mem _ hx)
      have hx := hamb (Set.mem_image_of_mem A (hT i hi (Tube.x_mem_carrier _)))
      have hy := hamb (Set.mem_image_of_mem A (hT i hi (Tube.y_mem_carrier _)))
      have hm := (convex_closedBall (0 : EuclideanSpace Real (Fin 3)) (1 / 4)).midpoint_mem hx hy
      have hcenter : (P i).center = midpoint Real (A (T i).x) (A (T i).y) := by
        dsimp [P, outerTube]
        rw [Tube.center_centredExtension]
        simp only [A, spineRescaleUnit_apply]
      refine (Tube.carrier_subset_closedBall_midpoint (EuclideanSpace Real (Fin 3)) (P i)).trans
        (Metric.closedBall_subset_closedBall' ?_)
      change (1 / 2 + ((16 * tau / theta : NNReal) : Real)) + dist (P i).center 0 <= 1
      rw [hcenter]
      have hmid := Metric.mem_closedBall.mp hm
      have hsmallR : ((16 * tau / theta : NNReal) : Real) <= 1 / 64 := by exact_mod_cast hsmall
      linarith
    have hlip : LipschitzWith (1 / (256 * theta)) A.toAffineMap := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (spineRescaleUnit htheta T0 _ x) (spineRescaleUnit htheta T0 _ y) <= _
      rw [spineRescaleUnit_apply, spineRescaleUnit_apply, Tube.dist_rescaleMap T0 (by norm_num : (0 : Real) < 64)]
      have h := Tube.dist_normalization_le htheta htheta1 T0 x y
      push_cast
      calc _ <= ((theta : Real)⁻¹ * dist x y) / (4 * 64) := div_le_div_of_nonneg_right h (by norm_num)
        _ = _ := by ring
    have hjac := (hJacobian htheta T0).1
    change affineJacobian A = _ at hjac
    refine ⟨himage, hball, ?_⟩
    intro q hq hqr
    let K := q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
    let N := q.convexHull_biUnion V
    have hmap : q.convexHull_biUnion W = K.mapAffine A := by
      ext1
      change (q.convexHull_biUnion W).carrier = (K.mapAffine A).carrier
      dsimp only [K]
      rw [hq.convexHull_biUnion_carrier, ConvexSpaceBody.mapAffine_carrier,
        hq.convexHull_biUnion_carrier]
      change (Convexity.convexHull Real) (⋃ i ∈ q, (W i).carrier) =
        A.toAffineMap '' (Convexity.convexHull Real) (⋃ i ∈ q, (T i).carrier)
      rw [Convexity.affineMap_image_convexHull]
      simp only [Set.image_iUnion]
      rfl
    obtain ⟨hinc, hvol, hthick⟩ := hHullHomothety q hq W V 16384 (by norm_num)
      (fun i hi => hWpos i (hqr hi)) (fun i hi => himage i (hqr hi))
      (fun i hi => by simpa only [NNReal.coe_ofNat] using hhom i (hqr hi))
    rw [hmap, ConvexSpaceBody.volume_mapAffine] at hvol
    rw [hmap] at hinc hthick
    have hupper (n : Nat) : ethickness Real N.carrier n <=
        ((128 : NNReal) : ENNReal) / theta * ethickness Real K.carrier n := by
      have hl := hlip.ethickness_image_le K.carrier n
      have hu := (hthick n).trans (mul_le_mul_right hl ((2 * 16384 : NNReal) : ENNReal))
      change ethickness Real N.carrier n <=
        ((2 * 16384 : NNReal) : ENNReal) *
          (((1 / (256 * theta) : NNReal) : ENNReal) * ethickness Real K.carrier n) at hu
      calc _ <= _ := hu
        _ = _ := by
          rw [← mul_assoc]
          congr 1
          rw [← ENNReal.coe_mul, ← ENNReal.coe_div htheta.ne']
          congr 1
          field_simp
          norm_num
    have hNball : N.carrier <= Metric.closedBall 0 1 :=
      (hq.convexHull_biUnion_subset_iff V (convex_closedBall _ _).isConvexSet).mpr
        (fun i hi => hball i (hqr hi))
    obtain ⟨i0, hi0⟩ := hq
    have hKpos : 0 < volume K.carrier :=
      (pos_iff_ne_zero.mpr (ML2Shaded.volume_carrier_ne_zero htau (T i0))).trans_le
        (measure_mono (Finset.le_convexHull_biUnion (fun i => (T i).toConvexSpaceBody) hi0))
    have hKzero : (1 / 2 : ENNReal) <= ethickness Real K.carrier 0 :=
      (Tube.le_ethickness_zero (T i0)).trans
        (ethickness_monotone (Finset.le_convexHull_biUnion (fun i => (T i).toConvexSpaceBody) hi0) 0)
    have hvolback : (((1 / 256 ^ 3 : NNReal) : ENNReal)) * volume K.carrier <=
        (theta : ENNReal) ^ 2 * volume N.carrier := by
      have h : volume (K.mapAffine A).carrier <= volume N.carrier := measure_mono hinc
      rw [ConvexSpaceBody.volume_mapAffine, hjac] at h
      have h := mul_le_mul_right h ((theta : ENNReal) ^ 2)
      calc (((1 / 256 ^ 3 : NNReal) : ENNReal)) * volume K.carrier =
          (((1 / 256 ^ 3 : NNReal) : ENNReal)) *
            (((theta : ENNReal) * (theta : ENNReal)⁻¹) ^ 2) * volume K.carrier := by
              rw [ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr htheta.ne') ENNReal.coe_ne_top,
                one_pow, mul_one]
        _ = (theta : ENNReal) ^ 2 *
            ((((1 / 256 ^ 3 : NNReal) : ENNReal)) * (theta : ENNReal)⁻¹ ^ 2 * volume K.carrier) := by ring
        _ <= _ := h
    have hupperPaid (n : Nat) (_hn : n = 1 \/ n = 2) :
        (theta : ENNReal) * ethickness Real N.carrier n <=
          ((128 : NNReal) : ENNReal) * ethickness Real K.carrier n := by
      have h := mul_le_mul_right (hupper n) (theta : ENNReal)
      calc _ <= _ := h
        _ = _ := by
          rw [div_eq_mul_inv]
          calc (theta : ENNReal) * ((((128 : NNReal) : ENNReal) * (theta : ENNReal)⁻¹) *
              ethickness Real K.carrier n) =
              ((128 : NNReal) : ENNReal) * ((theta : ENNReal) * (theta : ENNReal)⁻¹) *
                ethickness Real K.carrier n := by ring
            _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr htheta.ne') ENNReal.coe_ne_top, mul_one]
    have hlower := hVolumeThickness K N hKpos hKzero hNball (1 / 256 ^ 3) 128 theta htheta hvolback hupperPaid
    refine ⟨hinc, ?_, ?_⟩
    · refine hvol.trans ?_
      rw [mul_assoc]
      gcongr
      norm_num
    · intro n hn
      refine ⟨?_, (hupper n).trans ?_⟩
      · apply (ENNReal.div_le_iff
          (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr htheta.ne'))
          (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top)).mpr
        have h := mul_le_mul_right (hlower n hn) (((256 ^ 3 : NNReal) : ENNReal))
        have hscale : ethickness Real K.carrier n <=
            ((96 * 128 * 256 ^ 3 * theta : NNReal) : ENNReal) * ethickness Real N.carrier n := by
          calc _ = (((256 ^ 3 : NNReal) : ENNReal)) *
              ((((1 / 256 ^ 3 : NNReal) : ENNReal)) * ethickness Real K.carrier n) := by
                rw [← mul_assoc, ← ENNReal.coe_mul]
                norm_num
            _ <= _ := h
            _ = _ := by
              simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]
              ring
        refine hscale.trans ?_
        rw [mul_comm (ethickness Real N.carrier n)]
        gcongr
        norm_num
        gcongr
        norm_num
      · gcongr
        norm_num
  have hJacobian {theta : NNReal} (htheta : 0 < theta)
      (T0 : Tube theta (EuclideanSpace Real (Fin 3))) :
      let A := spineRescaleUnit htheta T0 (by norm_num : (0 : Real) < 64)
      affineJacobian A = ((1 / 256 ^ 3 : NNReal) : ENNReal) * (theta : ENNReal)⁻¹ ^ (2 : Nat) ∧
      affineJacobian A = ENNReal.ofReal (4 * (64 : Real)) ^ (-(3 : Real)) *
        (theta : ENNReal) ^ (-(2 : Real)) := by
    let A := spineRescaleUnit htheta T0 (by norm_num : (0 : Real) < 64)
    have hjac : affineJacobian A = ENNReal.ofReal ((4 * (64 : Real))⁻¹ ^ (3 : Nat)) *
        (theta : ENNReal)⁻¹ ^ (2 : Nat) := by
      let B := (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).carrier
      have hB0 : volume B ≠ 0 := ConvexSpaceBody.closedUnitBall_volume_pos.ne'
      have hBt : volume B ≠ ⊤ :=
        (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).isCompact'.measure_lt_top.ne
      apply (ENNReal.mul_left_inj hB0 hBt).mp
      rw [← volume_image_affineEquiv]
      have hm : (A : EuclideanSpace Real (Fin 3) -> EuclideanSpace Real (Fin 3)) = T0.rescaleMap 64 :=
        spineRescaleUnit_coe htheta T0 _
      rw [hm, Tube.volume_image_rescaleMap htheta (by norm_num : (0 : Real) < 64) T0 B]
      norm_num [mul_assoc]
    refine ⟨?_, ?_⟩
    · rw [hjac]
      congr 1
      norm_num [← ENNReal.ofReal_coe_nnreal]
    · rw [hjac, ENNReal.rpow_neg, ENNReal.rpow_neg]
      norm_cast
      simp only [inv_pow, ENNReal.coe_pow]
      congr 1 <;> norm_num [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_pow, ENNReal.inv_pow]
  classical
  obtain ⟨htheta, U, hU, hshade, himage, hvol, hball, hmass, hunion, hmul, hfull, hden⟩ :=
    hFine Q Hs O
  let A := spineRescaleUnit htheta (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
  let P := fun k => outerTube htheta (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
    (sourceEccentricParentScale delta M a m 16) (Q.tube m k)
  have htheta1 : sourceTowerRadius delta M a <= 1 :=
    Hs.outer_root.trans (by norm_num [div_le_iff₀])
  have haM : a <= M := by
    have := Hs.outer_lt_middle; have := Hs.middle_lt_inner; have := Hs.inner_bound; omega
  have hmM : m <= M := by have := Hs.middle_lt_inner; have := Hs.inner_bound; omega
  have ham : a <= m := Hs.outer_lt_middle.le
  have htau : 0 < sourceTowerRadius delta M m := Hs.delta_pos.trans_le Hs.original_to_middle
  have hnest : ∀ k, k <= M -> ∀ i ∈ S, ∀ j, j <= k ->
      (Q.tube k (Q.place k i)).toConvexSpaceBody <= (Q.tube j (Q.place j i)).toConvexSpaceBody := by
    intro k
    induction k with
    | zero =>
      intro hk i hi j hj
      have : j = 0 := by omega
      subst j
      exact le_rfl
    | succ k ih =>
      intro hk i hi j hj
      by_cases heq : j = k + 1
      · subst j; exact le_rfl
      have hjk : j <= k := by omega
      have hkM : k < M := by omega
      have hstep := Q.parent_containment k hkM (Q.place (k + 1) i) (Q.place_mem _ hk i hi)
      rw [← Q.parent_composition k hkM i hi] at hstep
      exact hstep.trans (ih (by omega) i hi j hjk)
  have hparents : ∀ k ∈ Q.fibre a m O.chosen,
      (Q.tube m k).carrier <= (Q.tube a O.chosen).carrier := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hiS, hplace⟩ := Finset.mem_filter.mp hi
    have h := hnest m hmM i hiS a ham
    rw [hplace] at h
    exact h
  obtain ⟨hpimage, hpball, hparts⟩ := hParentFamily htheta htheta1 htau Hs.middle_to_outer
    Hs.parent_small (Q.fibre a m O.chosen) (Q.tube a O.chosen) (Q.tube m) hparents
  have hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M a) delta
      (sourceEccentricFineScale delta M a) 64 3 := by
    refine ⟨htheta, Hs.original_to_middle.trans Hs.middle_to_outer, htheta1,
      Hs.fine_positive, ?_, ?_, ?_⟩
    · exact_mod_cast Hs.fine_small.trans (by norm_num [div_le_iff₀] : (1 / 16 : NNReal) <= 1 / 4)
    · change ((delta / (4 * sourceTowerRadius delta M a) : NNReal) : Real) <= _
      push_cast
      gcongr
      have h : (0 : Real) <= (sourceTowerRadius delta M a : Real) := NNReal.coe_nonneg _
      linarith
    · norm_num [Tube.normalization.C]
  have hcost : outerLoss 64 <= (2 ^ 100 : NNReal) := by norm_num [outerLoss]
  refine ⟨{
    radius_lower := by norm_num
    radius_pos := by norm_num
    comparison_one := by norm_num
    parent_dilation_one := by norm_num
    ambient_pos := htheta
    fine_pos := Hs.fine_positive
    parent_pos := Hs.parent_positive
    fine_situation := hsit
    outer_replacement_cost := hcost
    affine := A
    affine_eq := rfl
    fine := U
    parent := P
    fine_shade := hshade
    fine_image := himage
    fine_volume := ?_
    parent_image := hpimage
    parent_volume := ?_
    fine_parent := ?_
    fine_ball := hball
    parent_ball := hpball
    ball_room := Hs.ball_room
    jacobian_pos := pos_iff_ne_zero.mpr (affineJacobian_ne_zero A)
    jacobian_finite := lt_top_iff_ne_top.mpr (affineJacobian_ne_top A)
    jacobian_eq := (hJacobian htheta (Q.tube a O.chosen)).2
    mass_image := hmass
    union_image := hunion
    multiplicity := hmul
    fullness := ?_
    maximal_density := ?_
    part_image := ?_
    part_jacobian := ?_
    part_volume_upper := ?_
    part_thickness_lower := ?_
    part_thickness_upper := ?_ }⟩
  · intro i hi
    refine (hvol i hi).trans ?_
    gcongr
  · intro k hk
    have h := (hparts {k} (Finset.singleton_nonempty k) (Finset.singleton_subset_iff.mpr hk)).2.1
    simpa only [Finset.convexHull_biUnion_singleton, volume_image_affineEquiv, mul_assoc,
      P, A, sourceEccentricParentScale] using h
  · intro i hi
    rw [hU]
    change (outerTube htheta (Q.tube a O.chosen) (by norm_num : (0 : Real) < 64)
      (sourceEccentricFineScale delta M a) (O.innerShade i).toTube).toConvexSpaceBody <= _
    rw [O.inner_tubes i]
    have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
    exact hFineParent htheta htheta1 Hs.original_to_middle (Q.tube a O.chosen) (T i)
      (Q.tube m (Q.place m i)) (Q.leaf_containment m hmM i hiS)
  · refine le_trans ?_ hfull
    gcongr
    norm_num [outerLoss]
  · refine hden.trans ?_
    gcongr
  · intro q hq hqr
    exact (hparts q hq hqr).1
  · intro q hq hqr
    exact volume_image_affineEquiv A _
  · intro q hq hqr
    exact (hparts q hq hqr).2.1
  · intro q hq hqr n hn
    exact ((hparts q hq hqr).2.2 n hn).1
  · intro q hq hqr n hn
    exact ((hparts q hq hqr).2.2 n hn).2

end Kakeya.ML2Core

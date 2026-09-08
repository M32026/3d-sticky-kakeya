/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParentIndependent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceZeroDefectData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQSelectedMiddle

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

theorem source_parent_to_zero_window_schedule {N M J : Nat} {e : Real}
    {eta : Nat -> Real} {etaParent bias : Real}
    (H : SourceParentSchedule N M J e eta etaParent bias) :
    SourceZeroWindowSchedule N M J e eta etaParent := by
  exact ⟨H.count_bound, H.level_bound, H.index_lower, H.index_upper,
    H.window_exponent, H.rung_positive, H.rung_mono, H.rung_upper, H.rung_step,
    H.parent_positive, H.parent_upper, H.global_mesh, H.parent_mesh⟩

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

theorem source_parent_to_zero_retained_state
    (Q : SourceThreadedTower S T M C)
    {Z Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {R : Finset iota} (Q' : SourceThreadedTower R T M C) {loss : ENNReal}
    (H : SourceParentRetainedState Q Z R Q' Z' loss) :
    SourceZeroRetainedState Q Z R Z' Q' loss := by
  exact ⟨H.restriction, H.nonempty, H.original_tubes, H.same_tubes, H.subshade,
    H.mass, H.fullness, H.statistics⟩

theorem source_actual_parent_to_zero_floor (Q : SourceThreadedTower S T M C)
    {e bias etaParent tau : Real} {a b : Nat} {cap : NNReal}
    (B : SourceJointWindowFactors Q e a b bias)
    (P : SourceActualParent Q B etaParent tau cap) (hb : b <= M) :
    SourceZeroFloor Q e tau etaParent a b P.parent := by
  refine ⟨P.coarse_le_parent, ?_, hb, P.parent_before_window, P.parent_admissible, ?_⟩
  · exact (P.parent_before_window _ P.density_level_in_window).trans
      P.density_level_in_window.2.1
  · intro j hj jp hjp k hk _
    exact P.floor k hk j hj jp hjp

theorem source_parent_to_zero_measured_failure (Q : SourceThreadedTower S T M C)
    {R : Finset iota} {a m : Nat} {e tau : Real}
    (H : SourceParentFailedConcentration Q R a m e tau) :
    SourceZeroFailedConcentration Q R a m e tau := by
  exact ⟨H.subset, H.coarse_lt_middle, H.middle_bound, H.old_density,
    H.new_density, H.nontruncated, H.logarithmic_gap⟩

/-- These are the same actual hulls and raw affine thicknesses, with D=2.
No John-axis identity is inferred from a field name. -/
theorem source_parent_to_zero_eccentric_factors
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {e bias etaParent : Real} {a b : Nat}
    (B : SourceJointWindowFactors Q e a b bias)
    (P : SourceParentEccentric Q B etaParent) (hb : b <= M)
    (htubes : forall i, (Z i).toTube = T i)
    (hshade : forall i, i ∈ S ->
      (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <= volume (Z i).shade) :
    exists E : SourceZeroEccentricFactors Q Z a P.level etaParent bias 2
        (B.short P.level) (B.middle P.level) (B.long P.level),
      forall j, forall hj : j ∈ Q.indexSet a,
        (E.factor j hj).parts = (B.factor P.level P.in_window j hj).partition.parts := by
  classical
  refine ⟨{
    factor := P.factorization
    coarse_lt_middle := P.in_window.1
    middle_bound := P.in_window.2.1.le.trans hb
    dimension_comparison := by norm_num
    short_pos := B.short_positive _ P.in_window
    short_le_middle := (B.dimensions_order _ P.in_window).1
    middle_le_long := (B.dimensions_order _ P.in_window).2
    long_lower := B.long_lower _ P.in_window
    long_upper := B.long_upper _ P.in_window
    eccentric := P.eccentric
    dimensions := ?_
    same_tubes := htubes
    shade_floor := hshade
    complete_leaves := ?_
    complete_leaf_mass := ?_
  }, P.same_parts⟩
  · intro j hj part hpart
    rw [P.same_parts] at hpart
    obtain ⟨ha, hb, hc⟩ := B.common_dimensions _ P.in_window j hj part hpart
    have htwo : (2 : ENNReal)⁻¹ <= 1 := by norm_num
    exact ⟨(mul_le_of_le_one_left' htwo).trans hc.1, hc.2,
      (mul_le_of_le_one_left' htwo).trans hb.1, hb.2,
      (mul_le_of_le_one_left' htwo).trans ha.1, ha.2⟩
  · intro j hj
    rw [P.same_parts]
    exact (B.factor _ P.in_window j hj).whole_leaf_partition
  · intro j hj
    rw [P.same_parts]
    exact (B.factor _ P.in_window j hj).whole_leaf_mass Z

/-- Actual global density, including the occupied a=0 root family. All fixed
root-cover and window constants are paid before the runtime a,b are chosen. -/
theorem source_exists_retained_outer_density
    (N M J A0 A1 C : Nat) (hM : 2 <= M)
    (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    (eta : Nat -> Real) (e : Real) (heta : 0 < eta J) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
      forall a b : Nat, SourceParentUpperWindow Q A0 A1 N eta e a b J ->
      Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
        (delta : ENNReal) ^ (-2 * eta J) := by
  classical
  let D : Nat := sourceTowerWindowConstant C A0 A1
  let K : NNReal := 1280 ^ 6 * (D : NNReal) ^ N
  have hD : 1 <= D := by
    dsimp [D, sourceTowerWindowConstant]
    omega
  have hDN : (1 : ENNReal) <= (D : ENNReal) ^ N := by
    exact one_le_pow₀ (by exact_mod_cast hD)
  filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : Real) < 1),
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (ENNReal.coe_ne_top (r := K)) heta,
    Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with delta ht hK hd
  intro iota S T Q hgeometry a b hwindow
  have hM0 : 0 < M := by omega
  have hroot : sourceTowerRadius delta M 0 = (1 / 40 : NNReal) := by
    simp [sourceTowerRadius, hM0]
  have hrootcard : ((Q.indexSet 0).card : ENNReal) <= (1280 : ENNReal) ^ 6 := by
    have hh := hgeometry.coarse_card 0 hM0
    rw [hroot] at hh
    norm_num at hh
    exact_mod_cast hh
  have hδ1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd.2.le
  have hone : (1 : ENNReal) <= (delta : ENNReal) ^ (-eta J) := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (neg_nonpos.mpr heta.le)
  have hbound : Kakeya.maxDensity (Q.indexSet a)
      (fun i => (Q.tube a i).toConvexSpaceBody) <= (K : ENNReal) *
        (delta : ENNReal) ^ (-eta J) := by
    by_cases ha : a = 0
    · subst a
      refine (Kakeya.maxDensity_le_card _ _).trans (hrootcard.trans ?_)
      calc
        (1280 : ENNReal) ^ 6 <= (1280 : ENNReal) ^ 6 * (D : ENNReal) ^ N :=
          le_mul_of_one_le_right' hDN
        _ <= (K : ENNReal) * (delta : ENNReal) ^ (-eta J) := by
          simpa [K] using le_mul_of_one_le_right' (a := (K : ENNReal)) hone
    · have haM : a < M := hwindow.coarse_lt_fine.trans_le hwindow.fine_bound
      have haradius : (delta : Real) <= (sourceTowerRadius delta M a : Real) := by
        have hh := ht.2.2.2.2.1 a haM
        exact_mod_cast (show delta <= sourceTowerRadius delta M a by nlinarith)
      have hratio : (sourceTowerRadius delta M 0 : Real) /
          (sourceTowerRadius delta M a : Real) <= (delta : Real)⁻¹ := by
        rw [hroot]
        have hδ : (0 : Real) < delta := by exact_mod_cast hd.1
        norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
        calc (1 / 40 : Real) / (sourceTowerRadius delta M a : Real) <=
            1 / (sourceTowerRadius delta M a : Real) := by gcongr <;> norm_num
          _ <= (delta : Real)⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le hδ haradius
      have hpow : ENNReal.ofReal
          (((sourceTowerRadius delta M 0 : Real) / (sourceTowerRadius delta M a : Real)) ^ eta J) <=
          (delta : ENNReal) ^ (-eta J) := by
        have hp := Real.rpow_le_rpow (by positivity) hratio heta.le
        have hp' := ENNReal.ofReal_le_ofReal hp
        simpa [Real.inv_rpow (show (0 : Real) <= delta by positivity),
          ← Real.rpow_neg (show (0 : Real) <= delta by positivity),
          ← ENNReal.ofReal_rpow_of_pos (show (0 : Real) < delta by exact_mod_cast hd.1)] using hp'
      have hcover : Q.indexSet a <= (Q.indexSet 0).biUnion (Q.fibre 0 a) := by
        intro j hj
        obtain ⟨i, hi, hij⟩ := Q.place_surjective a haM.le j hj
        refine Finset.mem_biUnion.mpr ⟨Q.place 0 i, Q.place_mem 0 hM0.le i hi, ?_⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hij⟩
      calc
        Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
            ∑ j ∈ Q.indexSet 0, Kakeya.maxDensity (Q.fibre 0 a j)
              (fun i => (Q.tube a i).toConvexSpaceBody) :=
          Kakeya.maxDensity_le_sum_of_subset_biUnion _ hcover
        _ <= ∑ j ∈ Q.indexSet 0,
            (D : ENNReal) ^ N * (delta : ENNReal) ^ (-eta J) := by
          refine Finset.sum_le_sum fun j hj => (hwindow.coarse_density (by omega) j hj).trans ?_
          exact mul_le_mul_left' hpow _
        _ = ((Q.indexSet 0).card : ENNReal) *
            ((D : ENNReal) ^ N * (delta : ENNReal) ^ (-eta J)) := by simp
        _ <= (1280 : ENNReal) ^ 6 *
            ((D : ENNReal) ^ N * (delta : ENNReal) ^ (-eta J)) := by gcongr
        _ = (K : ENNReal) * (delta : ENNReal) ^ (-eta J) := by simp [K, mul_assoc]
  refine hbound.trans ?_
  calc
    (K : ENNReal) * (delta : ENNReal) ^ (-eta J) <=
        (delta : ENNReal) ^ (-eta J) * (delta : ENNReal) ^ (-eta J) := by gcongr
    _ = (delta : ENNReal) ^ (-2 * eta J) := by
      rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hd.1.ne') ENNReal.coe_ne_top]
      congr 1
      ring

end Kakeya.ML2Core

namespace Kakeya.ML2Assembly

open ML2Core ML2Reduction VeryNotSticky

universe u

/-- The original R4 density rows need the genuine retained upper window.
No lower row at the former tau exponent is reconstructed. -/
theorem sourceQ_retained_middle_original_bounds
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) {a p b N J : Nat} {jp : iota} {F : Finset iota}
    (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
    {rho : NNReal} {e zeta etaC q gamma etaD R : Real} {A0 A1 : Nat}
    (hinput : SourceQCoverInput Q a p b jp F Z rho e zeta etaC)
    (eta : Nat -> Real)
    (hwindow : SourceParentUpperWindow Q A0 A1 N eta e a b J)
    (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
      (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R)
    (he : 0 < e) (hrho : rho <= 1) (hS : (S.card : Real) <= (delta : Real) ^ (-(5 : Real)))
    (hfull : rho ^ gamma <= (outerLoss R)⁻¹ * ShadedBody.fullness F
      (fun i => (Z i).toShadedBody))
    (hnormalized : (outerLoss R : ENNReal) * ENNReal.ofReal
      (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ eta J) <=
        (rho : ENNReal) ^ (-q))
    (horiginal : ENNReal.ofReal
      (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ eta J) <=
        (rho : ENNReal) ^ (-(etaD - q))) :
    (forall i, i ∈ F -> (Z i).carrier <= (Q.tube p jp).carrier) /\
    0 < sourceQMiddleCardPower e /\
    (F.card : Real) <= (rho : Real) ^ (-(sourceQMiddleCardPower e : Real)) /\
    Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
      (rho : ENNReal) ^ (-(etaD - q)) /\
    Kakeya.maxDensity F (fun i =>
      (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toConvexSpaceBody) <=
        (rho : ENNReal) ^ (-q) /\
    (rho : ENNReal) ^ gamma <= ShadedBody.fullness F (fun i =>
      (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toShadedBody) := by
  classical
  have hassign : forall k l, k <= l -> l <= M -> forall i, i ∈ S -> forall j, j ∈ S ->
      Q.place l i = Q.place l j -> Q.place k i = Q.place k j := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ _ _ _ _ h => h
    | succ l hkl ih =>
      intro hl i hi j hj heq
      apply ih (by omega) i hi j hj
      rw [Q.parent_composition l (by omega) i hi, Q.parent_composition l (by omega) j hj, heq]
  have hcontains : forall k l, k <= l -> l <= M -> forall i, i ∈ S ->
      (Q.tube l (Q.place l i)).toConvexSpaceBody <=
        (Q.tube k (Q.place k i)).toConvexSpaceBody := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ _ _ => le_rfl
    | succ l hkl ih =>
      intro hl i hi
      refine le_trans ?_ (ih (by omega) i hi)
      rw [Q.parent_composition l (by omega) i hi]
      exact Q.parent_containment l (by omega) _ (Q.place_mem (l + 1) hl i hi)
  have hpM : p <= M := hinput.parent_lt_middle.le.trans hinput.middle_bound
  obtain ⟨i0, hi0, hi0p⟩ := Q.place_surjective p hpM jp hinput.parent_member
  let ja := Q.place a i0
  have hja : ja ∈ Q.indexSet a := Q.place_mem a (hinput.coarse_le_parent.trans hpM) i0 hi0
  have hFcoarse : F <= Q.fibre a b ja := by
    intro i hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp (hinput.family_subset hi)
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩, hxi⟩
    exact hassign a p hinput.coarse_le_parent hpM x hxS i0 hi0 (hxp.trans hi0p.symm)
  have hsub : forall i, i ∈ F -> (Z i).carrier <= (Q.tube p jp).carrier := by
    intro i hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp (hinput.family_subset hi)
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
    have hh := hcontains p b hinput.parent_lt_middle.le hinput.middle_bound x hxS
    rw [hxi, hxp] at hh
    change (Q.tube b i).carrier <= (Q.tube p jp).carrier at hh
    simpa only [← hinput.family_tubes i] using hh
  have hdelta : (0 : Real) < delta := by exact_mod_cast hinput.delta_pos
  have hdelta1 : (delta : Real) <= 1 := by
    have hbound : (40 : NNReal) ^ (-(M : Real)) <= 1 :=
      NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
    exact_mod_cast hinput.delta_small.le.trans hbound
  have hK : 0 < sourceQMiddleCardPower e := by unfold sourceQMiddleCardPower; omega
  have hKreal : 0 < (sourceQMiddleCardPower e : Real) := by exact_mod_cast hK
  have hpower : 5 <= e * (sourceQMiddleCardPower e : Real) / 2 := by
    have hc : 10 / e <= (sourceQMiddleCardPower e : Real) := by
      exact (Nat.le_ceil _).trans (by unfold sourceQMiddleCardPower; norm_cast; omega)
    have hh := (div_le_iff₀ he).mp hc
    nlinarith
  have hcard : (F.card : Real) <= (rho : Real) ^ (-(sourceQMiddleCardPower e : Real)) := by
    have hc : F.card <= S.card :=
      (Finset.card_le_card hinput.family_subset).trans
        (Finset.card_image_le.trans (Finset.card_filter_le S _))
    have hrhoδ : (rho : Real) <= (delta : Real) ^ (e / 2) :=
      hinput.rho_upper.trans (by nlinarith [Real.rpow_nonneg hdelta.le (e / 2)])
    calc
      (F.card : Real) <= (S.card : Real) := by exact_mod_cast hc
      _ <= (delta : Real) ^ (-(5 : Real)) := hS
      _ <= (delta : Real) ^ ((e / 2) * (-(sourceQMiddleCardPower e : Real))) := by
        apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1
        nlinarith
      _ = ((delta : Real) ^ (e / 2)) ^ (-(sourceQMiddleCardPower e : Real)) :=
        Real.rpow_mul hdelta.le _ _
      _ <= (rho : Real) ^ (-(sourceQMiddleCardPower e : Real)) :=
        Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hsit.pos_out) hrhoδ (neg_nonpos.mpr hKreal.le)
  have hmax : Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
      ENNReal.ofReal
        (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ eta J) := by
    rw [Kakeya.maxDensity_congr (fun i _ => congrArg Tube.toConvexSpaceBody (hinput.family_tubes i))]
    exact (Kakeya.maxDensity_mono _ hFcoarse).trans (hwindow.middle_density ja hja)
  have hR1 : 1 <= R := (show (1 : Real) <= (Tube.normalization.C 3 : Real) by
    exact_mod_cast Tube.normalization.one_le_C 3).trans hsit.normalizationConst_le_radius
  have hratio : (sourceTowerRadius delta M b : Real) /
      (sourceTowerRadius delta M p : Real) <= 4 * (rho : Real) := by
    rw [hinput.rho_eq]
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
    have hp : (0 : Real) < sourceTowerRadius delta M p := by exact_mod_cast hsit.pos_ambient
    field_simp
    nlinarith [NNReal.coe_nonneg (sourceTowerRadius delta M b)]
  refine ⟨hsub, hK, hcard, hmax.trans horiginal, ?_, ?_⟩
  · exact (outerFamily_maxDensity_le (by simp) hsit hR hR1 hratio hsub).trans
      ((mul_le_mul_left' hmax _).trans hnormalized)
  · have hh := hfull.trans (outerFamily_le_fullness (by simp) hsit hR hR1 hratio hsub)
    simpa only [ENNReal.coe_rpow_of_ne_zero hsit.pos_out.ne'] using
      (show ((rho ^ gamma : NNReal) : ENNReal) <= _ by exact_mod_cast hh)

end Kakeya.ML2Assembly

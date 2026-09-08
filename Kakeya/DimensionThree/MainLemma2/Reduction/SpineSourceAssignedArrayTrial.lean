/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedPacking
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedAmbientTransport
public import Kakeya.MultiScaleFac.Stopping

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

/-- The finite ladder in S:2619-2624, with its source one-based indexing. -/
structure SourceAssignedArrayLadder (N : Nat) (eta : Nat -> Real) (e : Real) : Prop where
  positive : ∀ j, 1 <= j -> j <= N + 1 -> 0 < eta j
  monotone : ∀ j k, 1 <= j -> j <= k -> k <= N + 1 -> eta j <= eta k
  ceiling : eta (N + 1) <= e
  gap : ∀ j, 1 <= j -> j <= N -> eta j <= (e / 2) * eta (j + 1)

/-- Literal transposition of the existing assigned profile in S:2735-2738. -/
noncomputable def sourceAssignedReverseProfile
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) (k l : Nat) : ENNReal :=
  Q.assignedProfile S (M - l) (M - k)

/-- The ratio of the reversed reciprocal source radii. -/
noncomputable def sourceAssignedReverseRatio (delta : NNReal) (M k l : Nat) : Real :=
  (sourceTowerRadius delta M (M - k) : Real) /
    (sourceTowerRadius delta M (M - l) : Real)

/-- Elementary finite-array properties on the same Q. The strict universal
readback is tied to its existing factor-two statistics, not to a restriction. -/
structure SourceAssignedArrayProperties
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) : Prop where
  profile_sup : ∀ a b, a <= M ->
    Q.assignedProfile S a b = (Q.indexSet a).sup (fun j =>
      Kakeya.maxDensity (Q.fibre a b j) (fun k => (Q.tube b k).toConvexSpaceBody))
  one_le : ∀ a b, a < b -> b <= M -> 1 <= Q.assignedProfile S a b
  finite : ∀ a b, Q.assignedProfile S a b ≠ ⊤
  ancestor_mono : ∀ a p b, a <= p -> p < b -> b <= M ->
    Q.assignedProfile S p b <= Q.assignedProfile S a b
  root_upper : Q.assignedProfile S 0 M <=
    Kakeya.maxDensity S (fun i => (T i).toConvexSpaceBody)
  strict_readback : ∀ a b, a < b -> b <= M -> ∀ t : ENNReal, t ≠ ⊤ ->
    t < Q.assignedProfile S a b -> ∀ j ∈ Q.indexSet a,
      (1 / 2 : ENNReal) * t <
        Kakeya.maxDensity (Q.fibre a b j) (fun k => (Q.tube b k).toConvexSpaceBody)

/-- C1: the finite source maximum and factor-two readback from the SAME
prepared tower statistics, S:2735 and S:5751-5763. -/
theorem source_assignedProfile_array_properties
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (hS : S.Nonempty) (hdelta : 0 < delta)
    (hpos : ∀ k, k <= M -> 0 < sourceTowerRadius delta M k)
    (hstats : SourceTowerStatistics Q Z) :
    SourceAssignedArrayProperties Q := by
  classical
  have hfoot : ∀ a, a <= M -> Q.assignedFootprint S a = Q.indexSet a := by
    intro a ha
    ext j
    constructor
    · rintro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Q.place_mem a ha i hi
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Q.place_surjective a ha j hj
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hsup : ∀ a b, a <= M -> Q.assignedProfile S a b =
      (Q.indexSet a).sup (fun j => Kakeya.maxDensity (Q.fibre a b j)
        (fun k => (Q.tube b k).toConvexSpaceBody)) := by
    intro a b ha
    simp only [SourceThreadedTower.assignedProfile, hfoot a ha,
      source_retainedAssignedFibre_at_ambient]
  refine ⟨hsup, ?_, source_assignedProfile_ne_top Q S, ?_, ?_, ?_⟩
  · intro a b hab hb
    obtain ⟨i, hi⟩ := hS
    rw [hsup a b (by omega)]
    refine (Kakeya.one_le_maxDensity (s := Q.fibre a b (Q.place a i))
      (W := fun k => (Q.tube b k).toConvexSpaceBody) ⟨Q.place b i, ?_, ?_⟩).trans
      (Finset.le_sup (f := fun j => Kakeya.maxDensity (Q.fibre a b j)
        (fun k => (Q.tube b k).toConvexSpaceBody)) (Q.place_mem a (by omega) i hi))
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩
    · have hp := hpos b hb
      have hc := Tube.le_volume.c_pos (Module.finrank Real (EuclideanSpace Real (Fin 3)))
      exact lt_of_lt_of_le (by positivity) (Q.tube b (Q.place b i)).le_volume
  · intro a p b hap hpb hb
    rw [hsup p b (by omega), hsup a b (by omega)]
    refine Finset.sup_le fun j hj => ?_
    obtain ⟨hplace, hmem, _, _⟩ :=
      Kakeya.ML2Assembly.sourceQ_ancestor_fibre_identities Q hap (by omega : p <= M)
    refine (Kakeya.maxDensity_mono _ ?_).trans
      (Finset.le_sup (f := fun j => Kakeya.maxDensity (Q.fibre a b j)
        (fun k => (Q.tube b k).toConvexSpaceBody)) (hmem j hj))
    apply Finset.image_subset_image
    intro i hi
    obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    exact ⟨hiS, (hplace i hiS).symm.trans (congrArg _ hip)⟩
  · rw [hsup 0 M (Nat.zero_le M)]
    refine Finset.sup_le fun j hj => ?_
    have hsub : Q.fibre 0 M j ⊆ S := by
      rintro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hkS, _⟩ := Finset.mem_filter.mp hk
      simpa only [Q.bottom_place k hkS] using hkS
    rw [Kakeya.maxDensity_congr (fun i hi => Q.bottom_body i (hsub hi))]
    exact Kakeya.maxDensity_mono _ hsub
  · intro a b hab hb t ht hlt j hj
    rw [hsup a b (by omega)] at hlt
    have hbound : (Q.indexSet a).sup (fun k => Kakeya.maxDensity (Q.fibre a b k)
        (fun l => (Q.tube b l).toConvexSpaceBody)) <=
        2 * Kakeya.maxDensity (Q.fibre a b j) (fun l => (Q.tube b l).toConvexSpaceBody) :=
      Finset.sup_le fun k hk => hstats.two_level_density a b hab hb k hk j hj
    have hlt' := hlt.trans_le hbound
    have hmul := ENNReal.mul_lt_mul_left (by norm_num : (1 / 2 : ENNReal) ≠ 0)
      (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hlt'
    have hhalf : (1 / 2 : ENNReal) * 2 = 1 := by
      rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    simpa only [mul_comm _ (1 / 2 : ENNReal), ← mul_assoc, hhalf, one_mul] using hmul

/-- Actual fixed-radius coordinates for the integer stopping engine. Both
ratio formulas retain the exceptional bottom radius of the source tower. -/
structure SourceFixedRadiusStoppingCoordinates (delta : NNReal) (N M : Nat)
    (e : Real) : Prop where
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  width_pos : 0 < M / N
  width_bound : M / N <= M
  width_product : M = (M / N) * N
  radius_pos : ∀ k, k <= M -> 0 < sourceTowerRadius delta M k
  radius_le_one : ∀ k, k <= M -> sourceTowerRadius delta M k <= 1
  radius_strict : ∀ a b, a < b -> b <= M ->
    sourceTowerRadius delta M b < sourceTowerRadius delta M a
  interior_ratio : ∀ a b, a <= b -> b < M ->
    (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) =
      (delta : Real) ^ (((b : Real) - (a : Real)) / (M : Real))
  bottom_ratio : ∀ a, a < M ->
    (sourceTowerRadius delta M M : Real) / (sourceTowerRadius delta M a : Real) =
      40 * (delta : Real) ^ (((M : Real) - (a : Real)) / (M : Real))
  small_piece_margin : ∀ a b, a < b -> b <= M ->
    (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <=
      (delta : Real) ^ (e ^ 2) -> a + M / N <= b
  endpoint_lower : (delta : Real) <=
    (sourceTowerRadius delta M M : Real) / (sourceTowerRadius delta M 0 : Real)
  endpoint_upper :
    (sourceTowerRadius delta M M : Real) / (sourceTowerRadius delta M 0 : Real) <=
      (delta : Real) ^ (e ^ 2)
  reverse_cocycle : ∀ a b c, a <= b -> b <= c -> c <= M ->
    sourceAssignedReverseRatio delta M a b * sourceAssignedReverseRatio delta M b c =
      sourceAssignedReverseRatio delta M a c
  reverse_margin : ∀ a b, a < b -> b <= M ->
    sourceAssignedReverseRatio delta M a b <= (delta : Real) ^ (e ^ 2) ->
      a + M / N <= b

/-- C2: N divides M is an internal mesh choice, made before delta. This
auxiliary does not add a condition to the original paid-trial theorem. -/
theorem source_fixed_radius_stopping_coordinates
    {N M : Nat} (hN : 5 <= N) (hM : 2 <= M) (hdiv : N ∣ M)
    {e : Real} (he : 0 < e) (heq : e ^ 2 = 1 / (N : Real)) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0, SourceFixedRadiusStoppingCoordinates delta N M e := by
  have hNr : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hMr : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have he2 : e ^ 2 < 1 := by
    rw [heq, div_lt_one hNr]
    exact_mod_cast (show 1 < N by omega)
  have hgap : 0 < 1 - e ^ 2 := by linarith
  have ht : (0 : NNReal) < (1 / 40 : NNReal) ^ (1 / (1 - e ^ 2)) := by positivity
  filter_upwards [source_eventually_fixed_tower_radius_conditions M hM he,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num), Ioo_mem_nhdsGT ht]
    with delta hd hd1 hdt
  obtain ⟨_, _, hd0, hr0, hlower, hstep⟩ := hd
  have hd0r : 0 < (delta : Real) := hd0
  have hd1r : (delta : Real) < 1 := hd1.2
  have hwp : M = (M / N) * N := (Nat.div_mul_cancel hdiv).symm
  have hwpos : 0 < M / N := by
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) (by omega)
  have hpos : ∀ k, k <= M -> 0 < sourceTowerRadius delta M k := by
    intro k hk
    unfold sourceTowerRadius
    split_ifs <;> positivity
  have hstrict : ∀ a b, a < b -> b <= M ->
      sourceTowerRadius delta M b < sourceTowerRadius delta M a := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hs := hstep b (by omega)
      have hsb : sourceTowerRadius delta M (b + 1) < sourceTowerRadius delta M b :=
        hs.trans_lt (by exact div_lt_self (hpos b (by omega)) (by norm_num))
      by_cases heab : a = b
      · simpa [heab] using hsb
      · exact hsb.trans (ih (by omega) (by omega))
  have hint : ∀ a b, a <= b -> b < M ->
      (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) =
        (delta : Real) ^ (((b : Real) - (a : Real)) / (M : Real)) := by
    intro a b hab hb
    simp only [sourceTowerRadius, if_pos hb, if_pos (show a < M by omega),
      NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_rpow]
    rw [sub_div, Real.rpow_sub hd0r]
    field_simp
  have hbot : ∀ a, a < M ->
      (sourceTowerRadius delta M M : Real) / (sourceTowerRadius delta M a : Real) =
        40 * (delta : Real) ^ (((M : Real) - (a : Real)) / (M : Real)) := by
    intro a ha
    simp only [sourceTowerRadius, lt_self_iff_false, if_false, if_pos ha,
      NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_rpow]
    rw [sub_div, div_self hMr.ne', Real.rpow_sub hd0r, Real.rpow_one]
    field_simp
  have hmargin : ∀ a b, a < b -> b <= M ->
      (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <=
        (delta : Real) ^ (e ^ 2) -> a + M / N <= b := by
    intro a b hab hb hr
    have hpow : (delta : Real) ^ (((b : Real) - (a : Real)) / (M : Real)) <=
        (delta : Real) ^ (e ^ 2) := by
      by_cases hbM : b < M
      · simpa only [hint a b hab.le hbM] using hr
      · have hbe : b = M := by omega
        subst b
        rw [hbot a (by omega)] at hr
        have hp := Real.rpow_pos_of_pos hd0r (((M : Real) - (a : Real)) / (M : Real))
        linarith
    have hexp := (Real.rpow_le_rpow_left_iff_of_base_lt_one hd0r hd1r).mp hpow
    rw [heq] at hexp
    have hwreal : ((M / N : Nat) : Real) = (M : Real) / (N : Real) := by
      rw [eq_div_iff hNr.ne']
      exact_mod_cast hwp.symm
    have hh : (a : Real) + ((M / N : Nat) : Real) <= (b : Real) := by
      rw [hwreal]
      have hh := (le_div_iff₀ hMr).mp hexp
      simp only [one_div, div_eq_mul_inv, one_mul] at hh ⊢
      rw [mul_comm (N : Real)⁻¹] at hh
      linarith
    exact_mod_cast hh
  have hend : (sourceTowerRadius delta M M : Real) /
      (sourceTowerRadius delta M 0 : Real) = 40 * (delta : Real) := by
    rw [hbot 0 (by omega)]
    simp [div_self hMr.ne']
  have hsmall : (delta : Real) ^ (1 - e ^ 2) <= 1 / 40 := by
    have hh := NNReal.rpow_le_rpow hdt.2.le hgap.le
    rw [← NNReal.rpow_mul, one_div_mul_cancel hgap.ne', NNReal.rpow_one] at hh
    exact_mod_cast hh
  have hupper : 40 * (delta : Real) <= (delta : Real) ^ (e ^ 2) := by
    rw [Real.rpow_sub hd0r, Real.rpow_one] at hsmall
    have hp := Real.rpow_pos_of_pos hd0r (e ^ 2)
    have hh := (div_le_iff₀ hp).mp hsmall
    linarith
  refine ⟨hd0, hd1.2, hwpos, Nat.div_le_self _ _, hwp, hpos, ?_, hstrict,
    hint, hbot, hmargin, ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hk0 : k = 0
    · simpa [hk0] using hr0
    · exact (hstrict 0 k (by omega) hk).le.trans hr0
  · rw [hend]
    linarith
  · rwa [hend]
  · intro a b c hab hbc hc
    unfold sourceAssignedReverseRatio
    have hp : (sourceTowerRadius delta M (M - b) : Real) ≠ 0 :=
      ne_of_gt (hpos _ (by omega))
    field_simp
  · intro a b hab hb hh
    have hh' := hmargin (M - b) (M - a) (by omega) (by omega) hh
    omega

/-- The geometric estimates consumed only by intermediate C3. C4 must
construct both fields from A3 and B2 on the actual source tower. -/
structure SourceAssignedArrayEstimates
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M : Nat}
    (Q : SourceThreadedTower S T M sourceThreadConstant) : Prop where
  submultiplicative : ∀ a p c, a < p -> p < c -> c <= M ->
    Q.assignedProfile S a c <=
      (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : ENNReal) *
        Q.assignedProfile S a p * Q.assignedProfile S p c
  crude_four : ∀ a b, a < b -> b <= M ->
    Q.assignedProfile S a b <=
      (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : ENNReal) *
        ENNReal.ofReal (((sourceTowerRadius delta M a : Real) /
          (sourceTowerRadius delta M b : Real)) ^ 4)

/-- C3: the source 7.7(B) readback using actual assigned-array estimates.
The source calibration is retained even though reverse monotonicity has E=1. -/
theorem source_assigned_array_stopping_of_estimates
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {N M : Nat}
    (Q : SourceThreadedTower S T M sourceThreadConstant)
    {e : Real} {eta : Nat -> Real}
    (hN : 5 <= N) (hM : 2 <= M) (hdiv : N ∣ M)
    (he : 0 < e) (heq : e ^ 2 = 1 / (N : Real))
    (hladder : SourceAssignedArrayLadder N eta e)
    (hcoordinates : SourceFixedRadiusStoppingCoordinates delta N M e)
    (hproperties : SourceAssignedArrayProperties Q)
    (hestimates : SourceAssignedArrayEstimates Q)
    (hcalibration : 4 <= (delta : Real) ^ (-(e ^ 2 * eta 1 / 2)))
    (hentry : Q.assignedProfile S 0 M <= ENNReal.ofReal
      (((sourceTowerRadius delta M 0 : Real) / (sourceTowerRadius delta M M : Real)) ^ eta 1)) :
    SourceFixedKTArrayGood Q
        (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : NNReal) N e ∨
      ∃ a b J, SourceTowerDividingWindow Q sourceBottomED sourceLevelED N eta e a b J := by
  classical
  let r := sourceAssignedReverseRatio delta M
  let X := sourceAssignedReverseProfile Q
  let B : ENNReal := sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED
  have hd0 : 0 < (delta : Real) := hcoordinates.delta_pos
  have hd1 : (delta : Real) < 1 := hcoordinates.delta_lt_one
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  have hdp : (delta : Real) ^ (e ^ 2) <= 1 :=
    Real.rpow_le_one hd0.le hd1.le he2.le
  have hrpos : ∀ a b, 0 < r a b := by
    intro a b
    exact div_pos (hcoordinates.radius_pos _ (Nat.sub_le _ _))
      (hcoordinates.radius_pos _ (Nat.sub_le _ _))
  have hrone : ∀ a b, a <= b -> b <= M -> r a b <= 1 := by
    intro a b hab hb
    apply (div_le_one (hcoordinates.radius_pos _ (Nat.sub_le _ _))).mpr
    by_cases heab : a = b
    · simp only [heab, le_refl]
    · exact (hcoordinates.radius_strict (M - b) (M - a) (by omega) (by omega)).le
  have hrcoc : ∀ a b c, a <= b -> b <= c -> c <= M ->
      r a b * r b c = r a c := hcoordinates.reverse_cocycle
  have hrpow : ∀ a b (t : Real), (r a b) ^ (-t) =
      ((sourceTowerRadius delta M (M - b) : Real) /
        (sourceTowerRadius delta M (M - a) : Real)) ^ t := by
    intro a b t
    dsimp [r, sourceAssignedReverseRatio]
    rw [Real.rpow_neg_eq_inv_rpow, inv_div]
  have hXmono : ∀ a c b, a < c -> c <= b -> b <= M -> X a c <= X a b := by
    intro a c b hac hcb hb
    exact hproperties.ancestor_mono (M - b) (M - c) (M - a)
      (by omega) (by omega) (by omega)
  have hXsub : ∀ a b c, a < b -> b < c -> c <= M ->
      X a c <= B * X a b * X b c := by
    intro a b c hab hbc hc
    have hh := hestimates.submultiplicative (M - c) (M - b) (M - a)
      (by omega) (by omega) (by omega)
    simpa only [X, B, sourceAssignedReverseProfile, mul_assoc, mul_comm, mul_left_comm] using hh
  let Good : Nat -> Nat -> Nat -> Unit -> Prop := fun j a b _ =>
    r a b <= (delta : Real) ^ (e ^ 2) ∧
      X a b <= ENNReal.ofReal ((r a b) ^ (-eta (j + 1)))
  let Long : Nat -> Nat -> Prop := fun a b => r a b <= (delta : Real) ^ e
  let Test : Nat -> Nat -> Nat -> Unit -> Prop := fun j a b _ =>
    ∃ c, a < c ∧ c < b ∧ (r a b) ^ (1 - e) <= r a c ∧
      r a c <= (r a b) ^ e ∧
        X c b <= ENNReal.ofReal ((r c b) ^ (-eta (j + 1)))
  have hg0 : Good 0 0 M () := by
    constructor
    · simpa only [r, sourceAssignedReverseRatio, Nat.sub_zero, Nat.sub_self] using
        hcoordinates.endpoint_upper
    · simpa only [hrpow, X, sourceAssignedReverseProfile, Nat.sub_zero, Nat.sub_self,
        Nat.zero_add] using hentry
  have hgmono : ∀ j j', j <= j' -> j' <= N -> ∀ a b, a < b -> ∀ x,
      Good j a b x -> Good j' a b x := by
    intro j j' hj hjN a b hab x hg
    refine ⟨hg.1, hg.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact Real.rpow_le_rpow_of_exponent_ge (hrpos a b) (hg.1.trans hdp)
      (neg_le_neg (hladder.monotone (j + 1) (j' + 1) (by omega) (by omega) (by omega)))
  have hsplit : ∀ j a b, j + 1 <= N -> a < b -> b <= M -> Long a b ->
      ∀ x, Good j a b x -> Test (j + 1) a b x ->
        ∃ (y : Unit) (c : Nat), True ∧ a + M / N <= c ∧ c + M / N <= b ∧
          Good (j + 1) a c y ∧ Good (j + 1) c b y := by
    intro j a b hj hab hb hl x hg ht
    obtain ⟨c, hac, hcb, hlow, hupp, htest⟩ := ht
    have hsmall : (r a b) ^ e <= (delta : Real) ^ (e ^ 2) := by
      calc (r a b) ^ e <= ((delta : Real) ^ e) ^ e :=
          Real.rpow_le_rpow (hrpos a b).le hl he.le
        _ = (delta : Real) ^ (e ^ 2) := by rw [← Real.rpow_mul hd0.le, pow_two]
    have hright : r c b <= (r a b) ^ e := by
      have heq' : r c b = r a b / r a c := by
        rw [← hrcoc a c b hac.le hcb.le hb]
        field_simp [(hrpos a c).ne']
      rw [heq']
      calc r a b / r a c <= r a b / (r a b) ^ (1 - e) :=
          div_le_div_of_nonneg_left (hrpos a b).le
            (Real.rpow_pos_of_pos (hrpos a b) _) hlow
        _ = (r a b) ^ e := by
          calc r a b / (r a b) ^ (1 - e) =
              (r a b) ^ (1 : Real) / (r a b) ^ (1 - e) := by rw [Real.rpow_one]
            _ = (r a b) ^ (1 - (1 - e)) := (Real.rpow_sub (hrpos a b) _ _).symm
            _ = (r a b) ^ e := by congr 1; ring
    have hleftsmall := hupp.trans hsmall
    have hrightsmall := hright.trans hsmall
    refine ⟨(), c, trivial, hcoordinates.reverse_margin a c hac (by omega) hleftsmall,
      hcoordinates.reverse_margin c b hcb hb hrightsmall, ⟨hleftsmall, ?_⟩,
      ⟨hrightsmall, htest⟩⟩
    refine (hXmono a c b hac hcb.le hb).trans (hg.2.trans (ENNReal.ofReal_le_ofReal ?_))
    have heta : 0 < eta (j + 2) := hladder.positive _ (by omega) (by omega)
    have hgap := hladder.gap (j + 1) (by omega) hj
    have hpow : (r a c) ^ eta (j + 2) <= (r a b) ^ eta (j + 1) := by
      calc (r a c) ^ eta (j + 2) <= ((r a b) ^ e) ^ eta (j + 2) :=
          Real.rpow_le_rpow (hrpos a c).le hupp heta.le
        _ = (r a b) ^ (e * eta (j + 2)) := (Real.rpow_mul (hrpos a b).le _ _).symm
        _ <= (r a b) ^ eta (j + 1) :=
          Real.rpow_le_rpow_of_exponent_ge (hrpos a b) (hrone a b hab.le hb) (by nlinarith)
    simpa only [Real.rpow_neg (hrpos a b).le, Real.rpow_neg (hrpos a c).le,
      one_div, Nat.add_assoc] using (one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (hrpos a c) _) hpow)
  obtain ⟨cuts, m, state, hm, _, h0, hMmem, hcutbound, hcard, hblocks⟩ :=
    Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin M N (M / N)
      hcoordinates.width_pos hcoordinates.width_bound hcoordinates.width_product.le
      Good Test Long (fun _ _ _ => True) () (fun _ => trivial)
      (fun _ _ _ _ _ _ _ => trivial) hg0 hgmono
      (fun _ _ _ _ _ _ _ _ hg => hg) hsplit
  have hB : 1 <= B := by
    change (1 : ENNReal) <= (sourceTowerWindowConstant _ _ _ : Nat)
    exact_mod_cast (show 1 <= sourceTowerWindowConstant sourceThreadConstant
      sourceBottomED sourceLevelED from (by norm_num : 1 <= 3).trans (le_max_right _ _))
  let c (i : Nat) : Nat := if hi : i < m + 2 then
    cuts.orderIsoOfFin hcard ⟨i, hi⟩ else M
  have hc (i : Nat) (hi : i < m + 2) :
      c i = (cuts.orderIsoOfFin hcard ⟨i, hi⟩ : Nat) := dif_pos hi
  have hc0 : c 0 = 0 := by
    rw [hc 0 (by omega)]
    exact Kakeya.MultiScaleFac.orderIsoOfFin_zero_eq hcard h0
  have hcM : c (m + 1) = M := by
    rw [hc (m + 1) (by omega)]
    exact Kakeya.MultiScaleFac.orderIsoOfFin_last_eq hcard hMmem hcutbound
  have hcle : ∀ i, i < m + 2 -> c i <= M := by
    intro i hi
    rw [hc i hi]
    exact Kakeya.MultiScaleFac.orderIsoOfFin_le hcard hcutbound _
  have hcinc : ∀ i j, i < j -> j < m + 2 -> c i < c j := by
    intro i j hij hj
    rw [hc i (by omega), hc j hj]
    exact (cuts.orderIsoOfFin hcard).strictMono (show (⟨i, by omega⟩ : Fin (m + 2)) < ⟨j, hj⟩ from hij)
  have hcblock : ∀ i, i <= m -> Good m (c i) (c (i + 1)) state ∧
      (¬ Long (c i) (c (i + 1)) ∨ ¬ Test (m + 1) (c i) (c (i + 1)) state) := by
    intro i hi
    have hadj := Kakeya.MultiScaleFac.orderIsoOfFin_castSucc_lt_succ hcard
      (⟨i, by omega⟩ : Fin (m + 1))
    rw [hc i (by omega), hc (i + 1) (by omega)]
    exact hblocks _ (cuts.orderIsoOfFin hcard _).property _
      (cuts.orderIsoOfFin hcard _).property hadj.1 hadj.2
  have hprod : ∀ a b, a <= b -> b <= M -> ∀ t : Real,
      ENNReal.ofReal ((r a b) ^ t) * ENNReal.ofReal ((r b M) ^ t) =
        ENNReal.ofReal ((r a M) ^ t) := by
    intro a b hab hb t
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hrpos a b).le _),
      ← Real.mul_rpow (hrpos a b).le (hrpos b M).le, hrcoc a b M hab hb le_rfl]
  have htail : ∀ t, t <= m -> X (c (m - t)) M <=
      B ^ t * ENNReal.ofReal ((r (c (m - t)) M) ^ (-eta (m + 1))) := by
    intro t
    induction t with
    | zero =>
      intro ht
      simpa only [Nat.sub_zero, pow_zero, one_mul, hcM] using (hcblock m le_rfl).1.2
    | succ t ih =>
      intro ht
      have hnext : m - (t + 1) + 1 = m - t := by omega
      have hh := (hcblock (m - (t + 1)) (by omega)).1.2
      rw [hnext] at hh
      have ha : c (m - (t + 1)) < c (m - t) := hcinc _ _ (by omega) (by omega)
      have hb : c (m - t) < M := by
        rw [← hcM]
        exact hcinc _ _ (by omega) (by omega)
      calc X (c (m - (t + 1))) M <= B * X (c (m - (t + 1))) (c (m - t)) * X (c (m - t)) M :=
          hXsub _ _ _ ha hb le_rfl
        _ <= B * ENNReal.ofReal ((r (c (m - (t + 1))) (c (m - t))) ^ (-eta (m + 1))) *
            (B ^ t * ENNReal.ofReal ((r (c (m - t)) M) ^ (-eta (m + 1)))) :=
          mul_le_mul' (mul_le_mul' le_rfl hh) (ih (by omega))
        _ = B ^ (t + 1) * ENNReal.ofReal ((r (c (m - (t + 1))) M) ^ (-eta (m + 1))) := by
          rw [← hprod _ _ ha.le hb.le (-eta (m + 1)), pow_succ]
          ring
  have htailcut : ∀ i, i <= m -> X (c i) M <=
      B ^ m * ENNReal.ofReal ((r (c i) M) ^ (-eta (m + 1))) := by
    intro i hi
    have hh := htail (m - i) (by omega)
    rw [show m - (m - i) = i by omega] at hh
    exact hh.trans (mul_le_mul' (pow_le_pow_right₀ hB (Nat.sub_le _ _)) le_rfl)
  by_cases hlong : ∃ i, i <= m ∧ Long (c i) (c (i + 1))
  · obtain ⟨i, hi, hilong⟩ := hlong
    have hab := hcinc i (i + 1) (by omega) (by omega)
    have hb := hcle (i + 1) (by omega)
    have ha := hcle i (by omega)
    obtain ⟨hgood, hstop⟩ := hcblock i hi
    have hfail : ¬ Test (m + 1) (c i) (c (i + 1)) state := hstop.resolve_left (not_not.mpr hilong)
    right
    refine ⟨M - c (i + 1), M - c i, m + 1, ?_⟩
    refine ⟨by omega, by omega, by omega, by omega, hilong, ?_, ?_, ?_⟩
    · intro hcoarse j hj
      have hic : i + 1 <= m := by
        by_contra hh
        have heq' : i + 1 = m + 1 := by omega
        rw [heq', hcM] at hcoarse
        omega
      have hh := htailcut (i + 1) hic
      have hs : Kakeya.maxDensity (Q.fibre 0 (M - c (i + 1)) j)
          (fun k => (Q.tube (M - c (i + 1)) k).toConvexSpaceBody) <= X (c (i + 1)) M := by
        dsimp [X, sourceAssignedReverseProfile]
        rw [Nat.sub_self, hproperties.profile_sup _ _ (Nat.zero_le M)]
        exact Finset.le_sup (f := fun j => Kakeya.maxDensity (Q.fibre 0 (M - c (i + 1)) j)
          (fun k => (Q.tube (M - c (i + 1)) k).toConvexSpaceBody)) hj
      refine (hs.trans hh).trans ?_
      rw [hrpow, Nat.sub_self]
      exact mul_le_mul' (pow_le_pow_right₀ hB (by omega)) le_rfl
    · intro j hj
      have hs : Kakeya.maxDensity (Q.fibre (M - c (i + 1)) (M - c i) j)
          (fun k => (Q.tube (M - c i) k).toConvexSpaceBody) <= X (c i) (c (i + 1)) := by
        dsimp [X, sourceAssignedReverseProfile]
        rw [hproperties.profile_sup _ _ (by omega)]
        exact Finset.le_sup (f := fun j => Kakeya.maxDensity
          (Q.fibre (M - c (i + 1)) (M - c i) j)
          (fun k => (Q.tube (M - c i) k).toConvexSpaceBody)) hj
      simpa only [hrpow] using hs.trans hgood.2
    · intro k hk j hj
      obtain ⟨hak, hkb, hlow, hupp⟩ := hk
      have hkm : k <= M := by omega
      have hr : r (c i) (M - k) =
          (sourceTowerRadius delta M (M - c i) : Real) / (sourceTowerRadius delta M k : Real) := by
        dsimp [r, sourceAssignedReverseRatio]
        rw [Nat.sub_sub_self hkm]
      have hh : ENNReal.ofReal ((r (M - k) (c (i + 1))) ^ (-eta (m + 1 + 1))) <
          X (M - k) (c (i + 1)) := by
        apply lt_of_not_ge
        intro hh
        exact hfail ⟨M - k, by omega, by omega,
          by simpa only [hr, r, sourceAssignedReverseRatio] using hlow,
          by simpa only [hr, r, sourceAssignedReverseRatio] using hupp, hh⟩
      rw [hrpow, Nat.sub_sub_self hkm] at hh
      dsimp [X, sourceAssignedReverseProfile] at hh
      rw [Nat.sub_sub_self hkm] at hh
      exact hproperties.strict_readback _ k hak hkm _ ENNReal.ofReal_ne_top hh j hj
  · have hfull : ∀ k, k < M -> X k M <=
        B ^ (N + 1) * ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
      intro k hk
      let below := (Finset.range (m + 1)).filter (fun i => c i <= k)
      have hbelow : below.Nonempty := by
        refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
        rw [hc0]
        omega
      let i := below.max' hbelow
      have himem : i ∈ below := Finset.max'_mem _ _
      obtain ⟨hirange, hik⟩ := Finset.mem_filter.mp himem
      have hi : i <= m := by have hh := Finset.mem_range.mp hirange; omega
      have hknext : k < c (i + 1) := by
        by_contra hh
        have hck : c (i + 1) <= k := by omega
        have hinext : i + 1 < m + 1 := by
          by_contra hh'
          have heq' : i + 1 = m + 1 := by omega
          rw [heq', hcM] at hck
          omega
        have hmem : i + 1 ∈ below :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hinext, hck⟩
        have hh' : i + 1 <= i := Finset.le_max' _ _ hmem
        omega
      have hb : c (i + 1) <= M := hcle _ (by omega)
      have hnotlong : ¬ Long (c i) (c (i + 1)) := fun hh => hlong ⟨i, hi, hh⟩
      have hpiece : (delta : Real) ^ e <= r k (c (i + 1)) := by
        have hh : (delta : Real) ^ e < r (c i) (c (i + 1)) := lt_of_not_ge hnotlong
        refine hh.le.trans ?_
        have ht := mul_le_mul_of_nonneg_right (hrone (c i) k hik hk.le)
          (hrpos k (c (i + 1))).le
        simpa only [hrcoc (c i) k (c (i + 1)) hik hknext.le hb, one_mul] using ht
      have hcrude : X k (c (i + 1)) <=
          B * ENNReal.ofReal ((delta : Real) ^ (-(4 * e))) := by
        have hh := hestimates.crude_four (M - c (i + 1)) (M - k) (by omega) (by omega)
        have hr : X k (c (i + 1)) <= B * ENNReal.ofReal ((r k (c (i + 1))) ^ (-(4 : Real))) := by
          simpa only [hrpow, Real.rpow_ofNat, X, B, sourceAssignedReverseProfile] using hh
        refine hr.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
        calc (r k (c (i + 1))) ^ (-(4 : Real)) <= ((delta : Real) ^ e) ^ (-(4 : Real)) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hd0 e) hpiece (by norm_num)
          _ = (delta : Real) ^ (-(4 * e)) := by
            rw [← Real.rpow_mul hd0.le]
            congr 1
            ring
      by_cases hbM : c (i + 1) = M
      · rw [hbM] at hcrude
        refine hcrude.trans (mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_))
        · simpa only [pow_one] using pow_le_pow_right₀ hB (show 1 <= N + 1 by omega)
        · exact Real.rpow_le_rpow_of_exponent_ge hd0 hd1.le (by linarith)
      · have hic : i + 1 <= m := by
          by_contra hh
          have heq' : i + 1 = m + 1 := by omega
          exact hbM (heq' ▸ hcM)
        have htaildelta : ENNReal.ofReal ((r (c (i + 1)) M) ^ (-eta (m + 1))) <=
            ENNReal.ofReal ((delta : Real) ^ (-e)) := by
          apply ENNReal.ofReal_le_ofReal
          have hentryratio : (delta : Real) <= r 0 M := by
            simpa only [r, sourceAssignedReverseRatio, Nat.sub_self, Nat.sub_zero] using
              hcoordinates.endpoint_lower
          have hlowerratio : (delta : Real) <= r (c (i + 1)) M := by
            refine hentryratio.trans ?_
            have hh := mul_le_mul_of_nonneg_right (hrone 0 (c (i + 1)) (Nat.zero_le _) hb)
              (hrpos (c (i + 1)) M).le
            simpa only [hrcoc 0 (c (i + 1)) M (Nat.zero_le _) hb le_rfl, one_mul] using hh
          have heta := hladder.positive (m + 1) (by omega) (by omega)
          have hetaE : eta (m + 1) <= e :=
            (hladder.monotone (m + 1) (N + 1) (by omega) (by omega) le_rfl).trans hladder.ceiling
          exact (Real.rpow_le_rpow_of_nonpos hd0 hlowerratio (by linarith)).trans
            (Real.rpow_le_rpow_of_exponent_ge hd0 hd1.le (neg_le_neg hetaE))
        calc X k M <= B * X k (c (i + 1)) * X (c (i + 1)) M :=
            hXsub k (c (i + 1)) M hknext (by omega) le_rfl
          _ <= B * (B * ENNReal.ofReal ((delta : Real) ^ (-(4 * e)))) *
              (B ^ m * ENNReal.ofReal ((delta : Real) ^ (-e))) :=
            mul_le_mul' (mul_le_mul' le_rfl hcrude)
              ((htailcut (i + 1) hic).trans (mul_le_mul' le_rfl htaildelta))
          _ = B ^ (m + 2) * ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
            have hp : ENNReal.ofReal ((delta : Real) ^ (-(4 * e))) *
                ENNReal.ofReal ((delta : Real) ^ (-e)) =
                ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd0.le _), ← Real.rpow_add hd0]
              congr 2
              ring
            rw [← hp, pow_add, pow_two]
            ring
          _ <= B ^ (N + 1) * ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) :=
            mul_le_mul' (pow_le_pow_right₀ hB (by omega)) le_rfl
    left
    intro l hl hlM
    have hh := hfull (M - l) (by omega)
    simpa only [X, sourceAssignedReverseProfile, Nat.sub_self, Nat.sub_sub_self hlM,
      ← ENNReal.ofReal_rpow_of_pos hd0, ENNReal.ofReal_coe_nnreal, B, ENNReal.coe_natCast] using hh

/-- C4: the actual assigned source 7.7(B) supplier. All estimates and scale
thresholds are constructed before the runtime Q; no array law is assumed. -/
theorem source_exists_actual_assigned_array_trial
    {N M : Nat} (hN : 5 <= N) (hM : 2 <= M) (hdiv : N ∣ M)
    {e eta0 : Real} {eta : Nat -> Real}
    (he : 0 < e) (heq : e ^ 2 = 1 / (N : Real))
    (hladder : SourceAssignedArrayLadder N eta e)
    (heta0 : 0 < eta0) (hentry_margin : 2 * eta0 <= eta 1) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      ∀ {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M sourceThreadConstant)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED eta0 ->
        SourceTowerStatistics Q Z ->
        SourceFixedKTArrayGood Q
            (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : NNReal) N e ∨
          ∃ a b J, SourceTowerDividingWindow Q sourceBottomED sourceLevelED N eta e a b J := by
  have heta1 : 0 < eta 1 := hladder.positive 1 le_rfl (by omega)
  have hgap : 0 < eta 1 - eta0 := by linarith
  have hcalpos : 0 < e ^ 2 * eta 1 / 2 := by positivity
  filter_upwards [source_fixed_radius_stopping_coordinates hN hM hdiv he heq,
    source_eventually_fixed_tower_radius_conditions M hM he,
    Kakeya.VeryNotSticky.eventually_real_le_rpow_neg (4 : NNReal) hcalpos,
    Kakeya.VeryNotSticky.eventually_real_le_rpow_neg ((40 : NNReal) ^ eta 1) hgap]
    with delta hc hr hcal hpower
  intro iota S T Q Z hinput hstats
  have hd0 : 0 < (delta : Real) := hc.delta_pos
  have hproperties := source_assignedProfile_array_properties Q Z hinput.geometry.nonempty
    hc.delta_pos hc.radius_pos hstats
  have hmono : ∀ k l, k <= l -> l <= M ->
      sourceTowerRadius delta M l <= sourceTowerRadius delta M k := by
    intro k l hkl hl
    rcases hkl.eq_or_lt with rfl | hkl
    · exact le_rfl
    · exact (hc.radius_strict k l hkl hl).le
  have hB : (300 ^ 9 : ENNReal) <=
      (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : ENNReal) := by
    norm_num [sourceTowerWindowConstant, sourceThreadConstant, sourceBottomED, sourceLevelED]
  have hestimates : SourceAssignedArrayEstimates Q := by
    constructor
    · intro a p c hap hpc hcM
      exact (source_assignedProfile_submultiplicative Q hinput.geometry.nonempty hc.delta_pos
        hc.radius_pos hc.radius_le_one hmono hap hpc hcM).trans
          (mul_le_mul' (mul_le_mul' hB le_rfl) le_rfl)
    · intro a b hab hb
      exact source_assignedProfile_crude_four Q hM hc.delta_pos hr.1 hinput.geometry hab hb
  have hentry : Q.assignedProfile S 0 M <= ENNReal.ofReal
      (((sourceTowerRadius delta M 0 : Real) / (sourceTowerRadius delta M M : Real)) ^ eta 1) := by
    refine (hproperties.root_upper.trans hinput.maximal_density).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h40 : 0 < (40 : Real) ^ eta 1 := Real.rpow_pos_of_pos (by norm_num) _
    have hpower' : (40 : Real) ^ eta 1 <= (delta : Real) ^ (-(eta 1 - eta0)) := by
      exact_mod_cast hpower
    have hmul := mul_le_mul_of_nonneg_right hpower'
      (Real.rpow_nonneg hd0.le (-eta0))
    rw [← Real.rpow_add hd0, show -(eta 1 - eta0) + -eta0 = -eta 1 by ring] at hmul
    have hratio : (sourceTowerRadius delta M 0 : Real) /
        (sourceTowerRadius delta M M : Real) = (delta : Real)⁻¹ / 40 := by
      simp only [sourceTowerRadius, if_pos (show 0 < M by omega), lt_self_iff_false,
        if_false, Nat.cast_zero, zero_div, NNReal.rpow_zero, mul_one,
        NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      ring
    rw [hratio, Real.div_rpow (inv_nonneg.mpr hd0.le) (by norm_num),
      ← Real.rpow_neg_eq_inv_rpow]
    apply (le_div_iff₀ h40).mpr
    simpa only [mul_comm] using hmul
  exact source_assigned_array_stopping_of_estimates Q hN hM hdiv he heq hladder hc
    hproperties hestimates (by exact_mod_cast hcal) hentry

end Kakeya.ML2Core

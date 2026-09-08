/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedAmbientTransport
public import Kakeya.StickyKakeya

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

def sourceStickySampleIndex (M M1 k : Nat) : Nat := k * (M / M1)

/-- The endpoint uses delta itself, including the source's exceptional bottom radius. -/
theorem source_sticky_subtower_radius {delta : NNReal} {M M1 k : Nat}
    (hM : 0 < M) (hM1 : 0 < M1) (hdiv : M1 ∣ M) (hk : k <= M1) :
    sourceTowerRadius delta M (sourceStickySampleIndex M M1 k) =
      sourceTowerRadius delta M1 k := by
  have hq : 0 < M / M1 := Nat.div_pos (Nat.le_of_dvd hM hdiv) hM1
  have hMmul : M1 * (M / M1) = M := Nat.mul_div_cancel' hdiv
  have hindex : sourceStickySampleIndex M M1 k < M ↔ k < M1 := by
    unfold sourceStickySampleIndex
    conv_lhs => rhs; rw [← hMmul]
    exact Nat.mul_lt_mul_right hq
  by_cases hklt : k < M1
  · rw [sourceTowerRadius, if_pos (hindex.mpr hklt), sourceTowerRadius, if_pos hklt]
    congr 2
    have hreal : (M : Real) = (M1 : Real) * ((M / M1 : Nat) : Real) := by
      exact_mod_cast hMmul.symm
    have hM1real : (M1 : Real) ≠ 0 := by exact_mod_cast hM1.ne'
    have hqreal : ((M / M1 : Nat) : Real) ≠ 0 := by exact_mod_cast hq.ne'
    simp only [sourceStickySampleIndex, Nat.cast_mul, hreal]
    field_simp
  · rw [sourceTowerRadius, if_neg (mt hindex.mp hklt), sourceTowerRadius, if_neg hklt]

section Tower

variable {iota : Type u} {delta : NNReal} {R : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M M1 C : Nat}

/-- An actual sub-tower has the same leaves, occupied sampled nodes and assignments. -/
structure SourceStickySubtower (Q : SourceThreadedTower R T M C)
    (Q1 : SourceThreadedTower R T M1 C) : Prop where
  index_identity : ∀ k, k <= M1 ->
    Q1.indexSet k = Q.indexSet (sourceStickySampleIndex M M1 k)
  assignment_identity : ∀ k, k <= M1 ->
    Q1.place k = Q.place (sourceStickySampleIndex M M1 k)
  tube_identity : ∀ k, k <= M1 -> ∀ j,
    (Q1.tube k j).toConvexSpaceBody =
      (Q.tube (sourceStickySampleIndex M M1 k) j).toConvexSpaceBody
  fibre_identity : ∀ a b, a <= M1 -> b <= M1 -> ∀ j,
    Q1.fibre a b j = Q.fibre (sourceStickySampleIndex M M1 a)
      (sourceStickySampleIndex M M1 b) j
  profile_identity : ∀ S : Finset iota, S <= R -> ∀ a b,
    a <= M1 -> b <= M1 ->
    Q1.assignedProfile S a b = Q.assignedProfile S
      (sourceStickySampleIndex M M1 a) (sourceStickySampleIndex M M1 b)

theorem source_exists_sticky_subtower (Q : SourceThreadedTower R T M C)
    (hM : 2 <= M) (hM1 : 2 <= M1) (hdiv : M1 ∣ M)
    (A0 A1 : Nat) (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (hgeometry : SourceTowerGeometry Q A0 A1)
    (hneighbours : SourceTowerNeighbourSharing Q)
    (hstatistics : SourceTowerStatistics Q Z) :
    ∃ Q1 : SourceThreadedTower R T M1 C,
      SourceStickySubtower Q Q1 /\ SourceTowerGeometry Q1 A0 A1 /\
      SourceTowerNeighbourSharing Q1 /\ SourceTowerStatistics Q1 Z := by
  classical
  let s : Nat -> Nat := sourceStickySampleIndex M M1
  have hq : 0 < M / M1 := Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) (by omega)
  have hlast : s M1 = M := Nat.mul_div_cancel' hdiv
  have hstrict : StrictMono s := fun _ _ h => Nat.mul_lt_mul_of_pos_right h hq
  have hbound : ∀ k, k <= M1 -> s k <= M := fun k hk => by
    simpa [hlast] using hstrict.monotone hk
  have hlt : ∀ k, k < M1 -> s k < M := fun k hk => by
    simpa [hlast] using hstrict hk
  have hradius : ∀ k, sourceTowerRadius delta M (s k) = sourceTowerRadius delta M1 k := by
    intro k
    by_cases hk : k <= M1
    · exact source_sticky_subtower_radius (by omega) (by omega) hdiv hk
    · have hs : M <= s k := by simpa [hlast] using hstrict.monotone (by omega : M1 <= k)
      simp [sourceTowerRadius, not_lt.mpr hs, show ¬k < M1 by omega]
  let V : (k : Nat) -> iota -> Tube (sourceTowerRadius delta M1 k) (EuclideanSpace Real (Fin 3)) :=
    fun k j => { Q.tube (s k) j with
      carrier_eq := by simpa only [hradius k] using (Q.tube (s k) j).carrier_eq }
  have hVbody : ∀ k j, (V k j).toConvexSpaceBody = (Q.tube (s k) j).toConvexSpaceBody :=
    fun _ _ => rfl
  have hnested : ∀ a b, a <= b -> b <= M -> ∀ i ∈ R, ∀ i' ∈ R,
      Q.place b i = Q.place b i' -> Q.place a i = Q.place a i' := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun _ _ _ _ _ h => h
    | succ b hab ih =>
      intro hb i hi i' hi' heq
      apply ih (by omega) i hi i' hi'
      rw [Q.parent_composition b (by omega) i hi,
        Q.parent_composition b (by omega) i' hi', heq]
  have hcontain : ∀ a b, a <= b -> b <= M -> ∀ i ∈ R,
      (Q.tube b (Q.place b i)).toConvexSpaceBody <=
        (Q.tube a (Q.place a i)).toConvexSpaceBody := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun _ _ _ => le_rfl
    | succ b hab ih =>
      intro hb i hi
      have hstep := Q.parent_containment b (by omega) (Q.place (b + 1) i)
        (Q.place_mem (b + 1) hb i hi)
      rw [← Q.parent_composition b (by omega) i hi] at hstep
      exact hstep.trans (ih (by omega) i hi)
  let rep : Nat -> iota -> iota := fun k j =>
    if h : k <= M ∧ j ∈ Q.indexSet k then (Q.place_surjective k h.1 j h.2).choose else j
  have hrep : ∀ k, k <= M -> ∀ j ∈ Q.indexSet k,
      rep k j ∈ R ∧ Q.place k (rep k j) = j := by
    intro k hk j hj
    dsimp only [rep]
    rw [dif_pos (show k <= M ∧ j ∈ Q.indexSet k from ⟨hk, hj⟩)]
    exact (Q.place_surjective k hk j hj).choose_spec
  let par : Nat -> iota -> iota := fun k j => Q.place (s (k - 1)) (rep (s k) j)
  let Q1 : SourceThreadedTower R T M1 C := {
    indexSet := fun k => Q.indexSet (s k)
    place := fun k => Q.place (s k)
    parent := par
    tube := V
    tube_injective := by
      intro k hk j hj j' hj' heq
      apply Q.tube_injective (s k) (hbound k hk) hj hj'
      apply Tube.ext
      · exact congrArg (fun t : Tube (sourceTowerRadius delta M1 k)
          (EuclideanSpace Real (Fin 3)) => t.carrier) heq
      · exact congrArg (fun t : Tube (sourceTowerRadius delta M1 k)
          (EuclideanSpace Real (Fin 3)) => t.x) heq
      · exact congrArg (fun t : Tube (sourceTowerRadius delta M1 k)
          (EuclideanSpace Real (Fin 3)) => t.y) heq
    place_mem := fun k hk => Q.place_mem (s k) (hbound k hk)
    place_surjective := fun k hk => Q.place_surjective (s k) (hbound k hk)
    leaf_containment := fun k hk => Q.leaf_containment (s k) (hbound k hk)
    parent_mem := by
      intro k hk j hj
      change Q.place (s (k + 1 - 1)) (rep (s (k + 1)) j) ∈ Q.indexSet (s k)
      simp only [Nat.add_sub_cancel]
      exact Q.place_mem (s k) (hbound k (by omega)) _
        (hrep (s (k + 1)) (hbound _ (by omega)) j hj).1
    parent_composition := by
      intro k hk i hi
      change Q.place (s k) i = Q.place (s (k + 1 - 1))
        (rep (s (k + 1)) (Q.place (s (k + 1)) i))
      simp only [Nat.add_sub_cancel]
      have hr := hrep (s (k + 1)) (hbound _ (by omega))
        (Q.place (s (k + 1)) i) (Q.place_mem _ (hbound _ (by omega)) i hi)
      exact hnested _ _ (hstrict.monotone (by omega)) (hbound _ (by omega)) i hi _ hr.1 hr.2.symm
    parent_containment := by
      intro k hk j hj
      change (Q.tube (s (k + 1)) j).toConvexSpaceBody <=
        (Q.tube (s k) (Q.place (s (k + 1 - 1)) (rep (s (k + 1)) j))).toConvexSpaceBody
      simp only [Nat.add_sub_cancel]
      have hr := hrep (s (k + 1)) (hbound _ (by omega)) j hj
      have hc := hcontain (s k) (s (k + 1)) (hstrict.monotone (by omega))
        (hbound _ (by omega)) _ hr.1
      rwa [hr.2] at hc
    bottom_index := by change Q.indexSet (s M1) = R; rw [hlast, Q.bottom_index]
    bottom_place := by intro i hi; change Q.place (s M1) i = i; rw [hlast]; exact Q.bottom_place i hi
    bottom_body := by intro i hi; change (Q.tube (s M1) i).toConvexSpaceBody = _
                      rw [hlast]; exact Q.bottom_body i hi
    containment_multiplicity := fun k hk => Q.containment_multiplicity (s k) (hbound k hk)
  }
  have hfibre : ∀ a b j, Q1.fibre a b j = Q.fibre (s a) (s b) j := fun _ _ _ => rfl
  refine ⟨Q1, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun k _ j => hVbody k j,
      fun a b _ _ j => hfibre a b j, ?_⟩
    intro S hS a b ha hb
    rfl
  · refine ⟨hgeometry.nonempty, hgeometry.original_centred, hgeometry.original_ball,
      hgeometry.original_ed, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk j hj
      exact hgeometry.coarse_centred (s k) (hlt k hk) j hj
    · intro k hk j hj
      exact hgeometry.coarse_ball (s k) (hlt k hk) j hj
    · intro k hk
      have hed := hgeometry.coarse_ed (s k) (hlt k hk)
      simpa only [Kakeya.VeryNotSticky.IsLineEssDistinct, Q1, V, hradius k] using hed
    · intro k hk
      have hc := hgeometry.coarse_card (s k) (hlt k hk)
      rwa [hradius k] at hc
    · intro k hk x y hxy
      exact hgeometry.segment_sharing (s k) (hlt k hk) x y hxy
  · intro k hk j hj
    exact hneighbours (s k) (hlt k hk) j hj
  · refine ⟨hstatistics.same_tubes, ?_, ?_, ?_, ?_⟩
    · intro k hk j hj j' hj'
      exact hstatistics.descendant_count (s k) (hbound k hk) j hj j' hj'
    · intro a b hab hb j hj j' hj'
      exact hstatistics.two_level_count (s a) (s b) (hstrict hab) (hbound b hb) j hj j' hj'
    · intro a b hab hb j hj j' hj'
      exact hstatistics.two_level_density (s a) (s b) (hstrict hab) (hbound b hb) j hj j' hj'
    · intro k hk j hj j' hj'
      exact hstatistics.fibre_mass (s k) (hbound k hk) j hj j' hj'

/-- The good array is the fixed Q assigned array, not an arbitrary terminal predicate. -/
theorem source_sticky_level_density_of_assigned_good (Q : SourceThreadedTower R T M C)
    {A0 A1 : Nat} (hM : 2 <= M) (hgeometry : SourceTowerGeometry Q A0 A1)
    {B : NNReal} {N : Nat} {e : Real} (hB : 1 <= B) (he : 0 <= e)
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hgood : SourceFixedKTArrayGood Q B N e) :
    ∀ k, k <= M -> Kakeya.maxDensity (Q.indexSet k)
      (fun j => (Q.tube k j).toConvexSpaceBody) <=
      (1280 ^ 6 : ENNReal) * (B : ENNReal) ^ (N + 1) *
        ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
  classical
  have hM0 : 0 < M := by omega
  have hrootcard : ((Q.indexSet 0).card : ENNReal) <= (1280 ^ 6 : ENNReal) := by
    have hc := hgeometry.coarse_card 0 hM0
    have hr : sourceTowerRadius delta M 0 = (1 / 40 : NNReal) := by
      simp [sourceTowerRadius, hM0]
    rw [hr] at hc
    norm_num at hc ⊢
    exact_mod_cast hc
  have hpow : (1 : ENNReal) <= ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
    have hp : (1 : Real) <= (delta : Real) ^ (-(5 * e)) := by
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        (by exact_mod_cast hdelta0) (by exact_mod_cast hdelta1) (by nlinarith)
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hBpow : (1 : ENNReal) <= (B : ENNReal) ^ (N + 1) := by
    apply one_le_pow₀
    exact_mod_cast hB
  have hfac : (1 : ENNReal) <= (B : ENNReal) ^ (N + 1) *
      ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
    simpa using mul_le_mul' hBpow hpow
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    calc
      _ <= ((Q.indexSet 0).card : ENNReal) := Kakeya.maxDensity_le_card _ _
      _ <= (1280 ^ 6 : ENNReal) := hrootcard
      _ <= _ := by
        simpa only [mul_one, mul_assoc] using
          mul_le_mul_left' hfac (1280 ^ 6 : ENNReal)
  · have hcover : Q.indexSet k <= (Q.indexSet 0).biUnion (Q.fibre 0 k) := by
      intro j hj
      obtain ⟨i, hi, hij⟩ := Q.place_surjective k hk j hj
      apply Finset.mem_biUnion.mpr
      refine ⟨Q.place 0 i, Q.place_mem 0 hM0.le i hi, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hij⟩
    have hcell : ∀ j ∈ Q.indexSet 0, Kakeya.maxDensity (Q.fibre 0 k j)
        (fun i => (Q.tube k i).toConvexSpaceBody) <=
          (B : ENNReal) ^ (N + 1) * ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
      intro j hj
      obtain ⟨i, hi, hij⟩ := Q.place_surjective 0 hM0.le j hj
      have hin : j ∈ Q.assignedFootprint R 0 := Finset.mem_image.mpr ⟨i, hi, hij⟩
      have hle := Finset.le_sup (f := fun j =>
        Kakeya.maxDensity (Q.retainedAssignedFibre R 0 k j)
          (fun i => (Q.tube k i).toConvexSpaceBody)) hin
      have hgoodk := hgood k (by omega) hk
      have hconvert : (delta : ENNReal) ^ (-(5 * e)) =
          ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) := by
        rw [← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hdelta0)]
        simp
      rw [hconvert] at hgoodk
      exact hle.trans hgoodk
    calc
      _ <= ∑ j ∈ Q.indexSet 0, Kakeya.maxDensity (Q.fibre 0 k j)
          (fun i => (Q.tube k i).toConvexSpaceBody) :=
        Kakeya.maxDensity_le_sum_of_subset_biUnion _ hcover
      _ <= ∑ _j ∈ Q.indexSet 0,
          (B : ENNReal) ^ (N + 1) * ENNReal.ofReal ((delta : Real) ^ (-(5 * e))) :=
        Finset.sum_le_sum hcell
      _ = ((Q.indexSet 0).card : ENNReal) *
          ((B : ENNReal) ^ (N + 1) * ENNReal.ofReal ((delta : Real) ^ (-(5 * e)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ <= _ := by
        simpa only [mul_assoc] using mul_le_mul_right' hrootcard
          ((B : ENNReal) ^ (N + 1) * ENNReal.ofReal ((delta : Real) ^ (-(5 * e))))

end Tower

/-- Each SSF radius is bracketed by an actual finer source level. The factor 40
is retained at the top and at the exceptional bottom step. -/
theorem source_exists_sticky_scale_bracket {delta : NNReal} {M : Nat}
    (hM : 2 <= M) (hdelta0 : 0 < delta)
    (hdelta : delta < (400 : NNReal) ^ (-(M : Real))) :
    ∃ fineLevel : Nat -> Nat, ∀ k, k <= ssfGridLen delta ->
      1 <= fineLevel k /\ fineLevel k <= M /\
      sourceTowerRadius delta M (fineLevel k) <= gridScale delta (ssfGridLen delta) k /\
      gridScale delta (ssfGridLen delta) k <=
        40 * delta ^ (-(1 / (M : Real))) * sourceTowerRadius delta M (fineLevel k) := by
  classical
  have hMr : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hd1 : delta <= 1 := hdelta.le.trans (by
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp))
  let x : NNReal := delta ^ (1 / (M : Real))
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x <= 1 := NNReal.rpow_le_one hd1 (by positivity)
  have hrep : ∀ k : Nat, delta ^ ((k : Real) / (M : Real)) = x ^ k := by
    intro k
    rw [show (k : Real) / (M : Real) = (1 / (M : Real)) * (k : Real) by ring,
      NNReal.rpow_mul, NNReal.rpow_natCast]
  have hbottom : delta = x ^ M := by
    simpa [div_self hMr.ne', NNReal.rpow_one] using hrep M
  have hinv : delta ^ (-(1 / (M : Real))) = x⁻¹ := NNReal.rpow_neg _ _
  have hfirst : 40 * x⁻¹ * sourceTowerRadius delta M 1 = 1 := by
    rw [sourceTowerRadius, if_pos (show 1 < M by omega), hrep, pow_one]
    field_simp
  have hstep : ∀ k, 1 <= k -> k < M ->
      sourceTowerRadius delta M k <= 40 * x⁻¹ * sourceTowerRadius delta M (k + 1) := by
    intro k hk hkM
    rw [sourceTowerRadius, if_pos hkM, hrep]
    by_cases hnext : k + 1 < M
    · rw [sourceTowerRadius, if_pos hnext, hrep, pow_succ]
      have heq : 40 * x⁻¹ * ((1 / 40) * (x ^ k * x)) = x ^ k := by
        field_simp
      rw [heq]
      exact mul_le_of_le_one_left (by positivity)
        (by norm_num [div_le_iff₀ (show (0 : NNReal) < 40 by norm_num)])
    · have hMk : M = k + 1 := by omega
      rw [sourceTowerRadius, if_neg hnext, hbottom, hMk, pow_succ]
      have heq : 40 * x⁻¹ * (x ^ k * x) = 40 * x ^ k := by field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (by norm_num [div_le_iff₀ (show (0 : NNReal) < 40 by norm_num)]) (by positivity)
  have hex : ∀ k : Nat, k <= ssfGridLen delta -> ∃ l : Nat,
      1 <= l ∧ l <= M ∧ sourceTowerRadius delta M l <= gridScale delta (ssfGridLen delta) k := by
    intro k hk
    refine ⟨M, by omega, le_rfl, ?_⟩
    simpa [sourceTowerRadius] using delta_le_gridScale hdelta0 hd1 hk
  let f : Nat -> Nat := fun k => if hk : k <= ssfGridLen delta then Nat.find (hex k hk) else M
  refine ⟨f, ?_⟩
  intro k hk
  have hf : f k = Nat.find (hex k hk) := dif_pos hk
  have hspec := Nat.find_spec (hex k hk)
  rw [← hf] at hspec
  refine ⟨hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  rw [hinv]
  by_cases hf1 : f k = 1
  · rw [hf1, hfirst]
    exact gridScale_le_one hd1 _ _
  · have hprev : 1 <= f k - 1 := by omega
    have hnot := Nat.find_min (hex k hk) (show f k - 1 < Nat.find (hex k hk) by omega)
    have hprevM : f k - 1 < M := by omega
    have hless : gridScale delta (ssfGridLen delta) k < sourceTowerRadius delta M (f k - 1) := by
      exact lt_of_not_ge fun hh => hnot ⟨hprev, hprevM.le, hh⟩
    have hbound := hstep (f k - 1) hprev hprevM
    rw [show f k - 1 + 1 = f k by omega] at hbound
    exact hless.le.trans hbound

end Kakeya.ML2Core

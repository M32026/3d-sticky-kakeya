/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedProfile
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQMiddleSelection
public import Kakeya.Thickness.Volume
public import Kakeya.Thickness.Cthickening

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody Tube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u v

/-- Auxiliary estimate for source lines 4933-4957, with an explicit
coefficient and no upper bound on `rho`. -/
theorem source_trace_in_tube_explicit {rho : NNReal} (hrho : 0 < rho)
    (U : Tube rho (EuclideanSpace Real (Fin 3)))
    (K : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) :
    volume (K.carrier ∩ U.carrier) *
        volume (Metric.cthickening (5 * (rho : Real)) K.carrier) <=
      (497664 : ENNReal) * volume K.carrier * volume U.carrier := by
  classical
  let E := EuclideanSpace Real (Fin 3)
  let I := K.carrier ∩ U.carrier
  let H := Metric.cthickening (5 * (rho : Real)) K.carrier
  let A := fun i => Metric.thickness Real K.carrier i
  let B := fun i => Metric.thickness Real U.carrier i
  let D := fun i => Metric.thickness Real I i
  let F := fun i => Metric.thickness Real H i
  have hn : Module.finrank Real E = 3 := by simp [E]
  have hI : IsCompact I := K.isCompact.inter U.isCompact
  have hH : IsCompact H := K.isCompact.cthickening
  have hnn (V : Set E) (i : Nat) : 0 <= Metric.thickness Real V i :=
    Metric.thickness_nonneg V i
  have hball : Metric.closedBall U.x (rho : Real) ⊆ U.carrier := by
    intro x hx
    rw [U.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨U.x, left_mem_segment Real U.x U.y, hx⟩
  have hB (i : Nat) (hi : i < 3) : (rho : Real) <= B i :=
    (Metric.thickness_closedBall_ge rho.coe_nonneg (hn.symm ▸ hi)).trans
      (Metric.thickness_monotone U.isCompact.isBounded hball i)
  have hDF (i : Nat) (hi : i ∈ Finset.range 3) :
      D i * F i <= 6 * A i * B i := by
    have hDA : D i <= A i :=
      Metric.thickness_monotone K.isCompact.isBounded Set.inter_subset_left i
    have hDB : D i <= B i :=
      Metric.thickness_monotone U.isCompact.isBounded Set.inter_subset_right i
    have hF : F i <= A i + 5 * B i := by
      have hg := Metric.thickness_cthickening_le K.isCompact.isBounded K.nonempty
        (show 0 <= 5 * (rho : Real) by positivity) i
      have hb := hB i (Finset.mem_range.mp hi)
      exact hg.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left hb (show (0 : Real) <= 5 by norm_num)) _)
    calc D i * F i <= min (A i) (B i) * (A i + 5 * B i) :=
        mul_le_mul (le_min hDA hDB) hF (hnn H i) (le_min (hnn _ _) (hnn _ _))
      _ <= 6 * A i * B i := by
        rcases le_total (A i) (B i) with h | h
        · rw [min_eq_left h]
          nlinarith [mul_nonneg (hnn K.carrier i) (sub_nonneg.mpr h)]
        · rw [min_eq_right h]
          nlinarith [mul_nonneg (hnn U.carrier i) (sub_nonneg.mpr h)]
  have hupper (V : Set E) (hv : Bornology.IsBounded V) :
      volume.real V <= 8 * ∏ i ∈ Finset.range 3, Metric.thickness Real V i := by
    have h := volume_le_prod_thickness hv
    rw [hn] at h
    have hf : (2 ^ 3 * ∏ i ∈ Finset.range 3,
        ENNReal.ofReal (Metric.thickness Real V i) : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num)
        (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
    have hh := ENNReal.toReal_mono hf h
    simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_prod,
      ENNReal.toReal_ofReal (hnn V _), show (2 : Real) ^ 3 = 8 by norm_num] using hh
  have hKA : (∏ i ∈ Finset.range 3, A i) <= 6 * volume.real K.carrier := by
    have h := K.convex.prod_thickness_le_volumeReal K.isCompact.isBounded
    norm_num [Metric.lt_volume_convexHull.c, hn, E] at h
    dsimp [A]
    linarith
  have hUB : (∏ i ∈ Finset.range 3, B i) <= 6 * volume.real U.carrier := by
    have h := U.convex.prod_thickness_le_volumeReal U.isCompact.isBounded
    norm_num [Metric.lt_volume_convexHull.c, hn, E] at h
    dsimp [B]
    linarith
  have hp : (∏ i ∈ Finset.range 3, D i) * (∏ i ∈ Finset.range 3, F i) <=
      216 * (∏ i ∈ Finset.range 3, A i) * (∏ i ∈ Finset.range 3, B i) := by
    calc _ = ∏ i ∈ Finset.range 3, D i * F i := (Finset.prod_mul_distrib).symm
      _ <= ∏ i ∈ Finset.range 3, 6 * A i * B i :=
        Finset.prod_le_prod (fun i _ => mul_nonneg (hnn I i) (hnn H i)) hDF
      _ = _ := by norm_num [Finset.prod_mul_distrib]
  have hreal : volume.real I * volume.real H <=
      497664 * volume.real K.carrier * volume.real U.carrier := by
    calc _ <= (8 * ∏ i ∈ Finset.range 3, D i) *
          (8 * ∏ i ∈ Finset.range 3, F i) :=
        mul_le_mul (hupper I hI.isBounded) (hupper H hH.isBounded)
          (measureReal_nonneg)
          (mul_nonneg (by norm_num) (Finset.prod_nonneg fun i _ => hnn I i))
      _ = 64 * ((∏ i ∈ Finset.range 3, D i) *
          (∏ i ∈ Finset.range 3, F i)) := by ring
      _ <= 64 * (216 * (∏ i ∈ Finset.range 3, A i) *
          (∏ i ∈ Finset.range 3, B i)) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ <= 64 * (216 * (6 * volume.real K.carrier) *
          (6 * volume.real U.carrier)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hKA (by norm_num)) hUB
          (Finset.prod_nonneg fun i _ => hnn U.carrier i) (by positivity)
      _ = _ := by ring
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top hI.measure_ne_top hH.measure_ne_top)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) K.isCompact.measure_ne_top)
      U.isCompact.measure_ne_top)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact hreal

/-- Assigned-parent form used in S:2430-2453 and S:4995-5002. Each fine label
belongs only to its named parent's fibre in the displayed supremum. -/
theorem source_assigned_twoScale_maxDensity
    {iota : Type u} {kappa : Type v} {delta rho : NNReal}
    (s : Finset iota) (v : Finset kappa)
    (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
    (U : kappa -> Tube rho (EuclideanSpace Real (Fin 3)))
    (p : iota -> kappa) (hs : s.Nonempty) (hv : v.Nonempty)
    (hdelta : 0 < delta) (hscale : delta <= rho) (hrho : rho <= 1)
    (hparent : ∀ i ∈ s, p i ∈ v)
    (hcontain : ∀ i ∈ s, (T i).toConvexSpaceBody <= (U (p i)).toConvexSpaceBody) :
    Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) <=
      (300 ^ 9 : ENNReal) *
        Kakeya.maxDensity v (fun j => (U j).toConvexSpaceBody) *
        v.sup (fun j => Kakeya.maxDensity (s.filter (fun i => p i = j))
          (fun i => (T i).toConvexSpaceBody)) := by
  classical
  let W := fun i => (T i).toConvexSpaceBody
  let V := fun j => (U j).toConvexSpaceBody
  let L := v.sup (fun j => Kakeya.maxDensity (s.filter (fun i => p i = j)) W)
  have hrho0 : 0 < rho := hdelta.trans_le hscale
  rw [Kakeya.maxDensity_le_iff]
  intro K
  by_cases hK0 : volume K.carrier = 0
  · rw [Kakeya.densityIn_eq_zero_of_volume_eq_zero hK0]
    exact zero_le
  rw [Kakeya.densityIn_le_iff]
  let f := s.filter (fun i => W i <= K)
  let w := f.image p
  let H := ConvexSpaceBody.cthickening (5 * (rho : Real)) K
  have hf (i : iota) (hi : i ∈ f) : i ∈ s ∧ W i <= K := Finset.mem_filter.mp hi
  have hwv : w ⊆ v := by
    rintro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hparent i (hf i hi).1
  have hH0 : volume H.carrier ≠ 0 := by
    apply ne_bot_of_le_ne_bot hK0
    exact measure_mono (Metric.self_subset_cthickening K.carrier)
  have hwH (j : kappa) (hj : j ∈ w) : V j <= H := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hcore : segment Real (T i).x (T i).y ⊆ K.carrier :=
      (show segment Real (T i).x (T i).y ⊆ (T i).carrier by
        rw [(T i).carrier_eq_cthickening]
        exact Metric.self_subset_cthickening _).trans (hf i hi).2
    intro x hx
    have hx' := Tube.rescale_le_of_le (T i) (U (p i)) (hcontain i (hf i hi).1) hx
    change x ∈ (T i |>.rescale (4 * rho)).carrier at hx'
    rw [(T i |>.rescale (4 * rho)).carrier_eq_cthickening] at hx'
    apply Metric.cthickening_subset_of_subset (5 * (rho : Real)) hcore
    exact Metric.cthickening_mono (by
      norm_num
      exact mul_le_mul_of_nonneg_right (by norm_num) rho.coe_nonneg) _ hx'
  have hlocal (j : kappa) (hj : j ∈ w) :
      (∑ i ∈ f.filter (fun i => p i = j), volume (W i).carrier) * volume H.carrier <=
        L * ((497664 : ENNReal) * volume K.carrier * volume (V j).carrier) := by
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    have hne : (K.carrier ∩ (V j).carrier).Nonempty := by
      obtain ⟨x, hx⟩ := (T i).nonempty
      refine ⟨x, (hf i hi).2 hx, ?_⟩
      rw [← hij]
      exact hcontain i (hf i hi).1 hx
    let I := K.inter (V j) hne
    have hqI : ∀ i ∈ f.filter (fun i => p i = j), W i <= I := by
      intro k hk x hx
      obtain ⟨hk, hkj⟩ := Finset.mem_filter.mp hk
      exact ⟨(hf k hk).2 hx, by
        rw [← hkj]
        exact hcontain k (hf k hk).1 hx⟩
    have hqsub : f.filter (fun i => p i = j) ⊆ s.filter (fun i => p i = j) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have hden : Kakeya.densityIn (f.filter (fun i => p i = j)) W I <= L :=
      (Kakeya.le_maxDensity _ _ _).trans
        ((Kakeya.maxDensity_mono W hqsub).trans
          (Finset.le_sup (f := fun j => Kakeya.maxDensity
            (s.filter (fun i => p i = j)) W) (hwv hj)))
    have heq := Kakeya.sum_volume_eq_densityIn_mul_volume' hqI
    calc
      _ = (Kakeya.densityIn (f.filter (fun i => p i = j)) W I *
          volume I.carrier) * volume H.carrier := by
        rw [heq]
      _ <= (L * volume I.carrier) * volume H.carrier := by gcongr
      _ = L * (volume I.carrier * volume H.carrier) := mul_assoc _ _ _
      _ <= _ := mul_le_mul_left' (source_trace_in_tube_explicit hrho0 (U j) K) L
  have hcoarse : (∑ j ∈ w, volume (V j).carrier) <=
      Kakeya.maxDensity v V * volume H.carrier := by
    have heq := Kakeya.sum_volume_eq_densityIn_mul_volume' hwH
    rw [heq]
    exact mul_le_mul_right'
      ((Kakeya.le_maxDensity _ _ _).trans (Kakeya.maxDensity_mono V hwv)) _
  have hsum :
      (∑ i ∈ f, volume (W i).carrier) * volume H.carrier <=
        ((497664 : ENNReal) * Kakeya.maxDensity v V * L * volume K.carrier) *
          volume H.carrier := by
    calc
      _ = ∑ j ∈ w,
          (∑ i ∈ f.filter (fun i => p i = j), volume (W i).carrier) * volume H.carrier := by
        rw [← Finset.sum_mul, Finset.sum_fiberwise_of_maps_to
          (fun i hi => Finset.mem_image_of_mem p hi)]
      _ <= ∑ j ∈ w, L * ((497664 : ENNReal) * volume K.carrier * volume (V j).carrier) :=
        Finset.sum_le_sum hlocal
      _ = (L * (497664 : ENNReal) * volume K.carrier) *
          (∑ j ∈ w, volume (V j).carrier) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ <= (L * (497664 : ENNReal) * volume K.carrier) *
          (Kakeya.maxDensity v V * volume H.carrier) := mul_le_mul_left' hcoarse _
      _ = _ := by ring
  have hcancel := (ENNReal.mul_le_mul_iff_left hH0 H.isCompact.measure_ne_top).mp hsum
  exact hcancel.trans (by
    change (497664 : ENNReal) * Kakeya.maxDensity v V * L * volume K.carrier <= _
    gcongr
    norm_num)

/-- The actual assigned profile of one named source tower. This is an
auxiliary consequence of assigned-parent two-scale geometry. -/
theorem source_assignedProfile_submultiplicative
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) (hS : S.Nonempty) (hdelta : 0 < delta)
    (hpos : ∀ k, k <= M -> 0 < sourceTowerRadius delta M k)
    (hupper : ∀ k, k <= M -> sourceTowerRadius delta M k <= 1)
    (hmono : ∀ k l, k <= l -> l <= M ->
      sourceTowerRadius delta M l <= sourceTowerRadius delta M k)
    {a p c : Nat} (hap : a < p) (hpc : p < c) (hc : c <= M) :
    Q.assignedProfile S a c <=
      (300 ^ 9 : ENNReal) * Q.assignedProfile S a p * Q.assignedProfile S p c := by
  classical
  have hpM : p <= M := hpc.le.trans hc
  obtain ⟨hanc, hmem, hbody, hfibre⟩ :=
    Kakeya.ML2Assembly.sourceQ_ancestor_fibre_identities Q hpc.le hc
  let parent := Kakeya.ML2Assembly.sourceQAncestor Q p c
  refine Finset.sup_le fun j hj => ?_
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
  let f := Q.retainedAssignedFibre S a c j
  let g := Q.retainedAssignedFibre S a p j
  have hcell : i ∈ S.filter (fun k => Q.place a k = j) := Finset.mem_filter.mpr ⟨hi, hij⟩
  have hfne : f.Nonempty := ⟨Q.place c i, Finset.mem_image_of_mem _ hcell⟩
  have hgne : g.Nonempty := ⟨Q.place p i, Finset.mem_image_of_mem _ hcell⟩
  have hfg : ∀ k ∈ f, parent k ∈ g := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    rw [show parent (Q.place c l) = Q.place p l from hanc l (Finset.mem_filter.mp hl).1]
    exact Finset.mem_image_of_mem _ hl
  have hcontain : ∀ k ∈ f, (Q.tube c k).toConvexSpaceBody <=
      (Q.tube p (parent k)).toConvexSpaceBody := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    exact hbody _ (Q.place_mem c hc l (Finset.mem_filter.mp hl).1)
  have htwo := source_assigned_twoScale_maxDensity f g (Q.tube c) (Q.tube p)
    parent hfne hgne (hpos c hc) (hmono p c hpc.le hc) (hupper p hpM) hfg hcontain
  have hcoarse : Kakeya.maxDensity g (fun k => (Q.tube p k).toConvexSpaceBody) <=
      Q.assignedProfile S a p :=
    Finset.le_sup (f := fun j => Kakeya.maxDensity (Q.retainedAssignedFibre S a p j)
      (fun k => (Q.tube p k).toConvexSpaceBody)) hj
  have hfine : g.sup (fun k => Kakeya.maxDensity (f.filter (fun l => parent l = k))
      (fun l => (Q.tube c l).toConvexSpaceBody)) <= Q.assignedProfile S p c := by
    refine Finset.sup_le fun k hk => ?_
    have hkfoot : k ∈ Q.assignedFootprint S p := by
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hl).1
    have hsub : f.filter (fun l => parent l = k) ⊆ Q.retainedAssignedFibre S p c k := by
      intro l hl
      obtain ⟨hl, hlk⟩ := Finset.mem_filter.mp hl
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
      have hmS := (Finset.mem_filter.mp hm).1
      refine Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hmS, ?_⟩, rfl⟩
      exact (hanc m hmS).symm.trans hlk
    exact (Kakeya.maxDensity_mono (fun l => (Q.tube c l).toConvexSpaceBody) hsub).trans
      (Finset.le_sup (f := fun k => Kakeya.maxDensity (Q.retainedAssignedFibre S p c k)
        (fun l => (Q.tube c l).toConvexSpaceBody)) hkfoot)
  exact htwo.trans (mul_le_mul' (mul_le_mul_left' hcoarse _) hfine)

end Kakeya.ML2Core

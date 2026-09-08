import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Dilation containment from geometric closeness

If two radius-`ρ` tubes have sufficiently close midpoints and directions,
then one carrier is contained in a fixed homothetic dilation of the other.

## Main results

* `dilatedTubeCarrier_eq_cthickening`: the dilated carrier equals the
  `A * ρ`-thickening of the length-`A` segment centered at the midpoint.
* `tube_contained_in_dilated_of_close`: containment from explicit
  midpoint and direction closeness bounds.
* `tube_contained_in_dilated_of_same_dir`: same-direction special case.
-/

noncomputable section

open Metric

namespace Kakeya.Streamlined.GeometricLemmas

/-- The segment of length `A` centered at the tube midpoint. -/
def extendedSegment {ρ : ℝ} (A : ℝ) (T : Kakeya.DeltaTube ρ) : Set Point3 :=
  AffineMap.homothety (tubeMidpoint T) A '' (Kakeya.unitSegment T.base T.direction)

private lemma isCompact_unitSegment {base direction : Point3} :
    IsCompact (Kakeya.unitSegment base direction) := by
  apply IsCompact.image
  · exact isCompact_Icc
  · exact continuous_const.add (continuous_id.smul continuous_const)

private lemma nonempty_unitSegment {base direction : Point3} :
    (Kakeya.unitSegment base direction).Nonempty := by
  exact ⟨base, ⟨0, by norm_num, by simp⟩⟩

/-- Homothety on Point3 written with ordinary vector operations. -/
private lemma homothety_apply' {m : Point3} {A : ℝ} {y : Point3} :
    AffineMap.homothety m A y = m + A • (y - m) := by
  rw [AffineMap.homothety_apply]
  have h : (A • (y -ᵥ m) +ᵥ m) = m + A • (y - m) := by
    ext i
    <;> simp
    <;> ring
  exact h

/--
Homothety scales distances by `A` (for `A ≥ 0`).
-/
private lemma dist_homothety {m : Point3} {A : ℝ} (hA : 0 ≤ A) {y p : Point3} :
    dist (AffineMap.homothety m A y) (AffineMap.homothety m A p) = A * dist y p := by
  have h1 : (AffineMap.homothety m A y) - (AffineMap.homothety m A p) = A • (y - p) := by
    rw [homothety_apply', homothety_apply']
    have h2 : (m + A • (y - m)) - (m + A • (p - m)) = A • (y - m) - A • (p - m) := by abel
    rw [h2, ← smul_sub] <;> abel
  rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
  have h3 : ‖A‖ = A := by
    rw [Real.norm_eq_abs, abs_of_nonneg hA]
  rw [h3]

/--
A point of the form `tubeMidpoint T + s • T.direction` lies in the
extended segment whenever `|s| ≤ A / 2`.
-/
lemma mem_extendedSegment_of_abs_le {ρ : ℝ} {A : ℝ} (hA : 0 ≤ A)
    {T : Kakeya.DeltaTube ρ} {s : ℝ} (hs : |s| ≤ A / 2) :
    tubeMidpoint T + s • T.direction ∈ extendedSegment A T := by
  by_cases hA0 : A = 0
  · have hs0 : s = 0 := by
      have h1 : |s| ≤ 0 := by simpa [hA0] using hs
      have h2 : |s| = 0 := le_antisymm h1 (abs_nonneg s)
      exact abs_eq_zero.mp h2
    rw [hs0]
    have h_mid : tubeMidpoint T + (0 : ℝ) • T.direction = tubeMidpoint T := by
      simp
    rw [h_mid]
    have h_base_in : T.base ∈ Kakeya.unitSegment T.base T.direction :=
      ⟨0, by norm_num, by simp⟩
    have h_hom : AffineMap.homothety (tubeMidpoint T) A T.base = tubeMidpoint T := by
      rw [hA0, homothety_apply'] <;> simp
    exact ⟨T.base, h_base_in, h_hom⟩
  · have hA_pos : 0 < A := by
      exact lt_of_le_of_ne hA (Ne.symm hA0)
    set t : ℝ := s / A + 1 / 2 with ht_def
    have h_s1 : -(A / 2) ≤ s := (abs_le.mp hs).1
    have h_s2 : s ≤ A / 2 := (abs_le.mp hs).2
    have ht0 : 0 ≤ t := by
      rw [ht_def]
      have h : s / A ≥ -1 / 2 := by
        calc s / A ≥ (-(A / 2)) / A := by gcongr
          _ = -1 / 2 := by field_simp [hA_pos.ne'] <;> ring
      linarith
    have ht1 : t ≤ 1 := by
      rw [ht_def]
      have h : s / A ≤ 1 / 2 := by
        calc s / A ≤ (A / 2) / A := by gcongr
          _ = 1 / 2 := by field_simp [hA_pos.ne'] <;> ring
      linarith
    set p : Point3 := T.base + t • T.direction with hp_def
    have hp : p ∈ Kakeya.unitSegment T.base T.direction :=
      ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have h_p_sub : p - tubeMidpoint T = (t - 1 / 2) • T.direction := by
      rw [hp_def, tubeMidpoint]
      ext i
      simp [sub_smul] <;> ring
    have h4 : A * (t - 1 / 2) = s := by
      rw [ht_def] <;> field_simp [hA_pos.ne'] <;> ring
    have h_eq : AffineMap.homothety (tubeMidpoint T) A p =
        tubeMidpoint T + s • T.direction := by
      rw [homothety_apply', h_p_sub, smul_smul, h4]
    exact ⟨p, hp, h_eq⟩

/--
The dilated tube carrier contains the `A * ρ`-thickening of the extended
segment.
-/
lemma cthickening_extendedSegment_subset_dilatedTubeCarrier
    {ρ : ℝ} {A : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ)
    (T : Kakeya.DeltaTube ρ) :
    Metric.cthickening (A * ρ) (extendedSegment A T) ⊆ dilatedTubeCarrier A T := by
  intro x hx
  have h_inf : Metric.infEDist x (extendedSegment A T) ≤ ENNReal.ofReal (A * ρ) := hx
  let f : Point3 → Point3 := AffineMap.homothety (tubeMidpoint T) A
  have h_cont : Continuous f := by fun_prop
  have h_compact : IsCompact (extendedSegment A T) :=
    isCompact_unitSegment.image h_cont
  have h_nonempty : (extendedSegment A T).Nonempty := by
    have h_base_in : T.base ∈ Kakeya.unitSegment T.base T.direction :=
      ⟨0, by norm_num, by simp⟩
    exact ⟨f T.base, T.base, h_base_in, rfl⟩
  rcases h_compact.exists_infEDist_eq_edist h_nonempty x with ⟨p', hp'_seg, h_inf_eq⟩
  have h_edist : edist x p' ≤ ENNReal.ofReal (A * ρ) := by
    rw [← h_inf_eq]; exact h_inf
  have h_dist : dist x p' ≤ A * ρ := by
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h_edist
  rcases hp'_seg with ⟨p, hp_seg, hp'_eq⟩
  set y : Point3 := tubeMidpoint T + (1 / A) • (x - tubeMidpoint T) with hy_def
  have h_y_sub : y - tubeMidpoint T = (1 / A) • (x - tubeMidpoint T) := by
    rw [hy_def] <;> simp [sub_smul] <;> abel
  have h_p'_def : p' = tubeMidpoint T + A • (p - tubeMidpoint T) := by
    rw [← hp'_eq, homothety_apply']
  have h_xp'_eq : x - p' = A • (y - p) := by
    calc
      x - p'
        = x - (tubeMidpoint T + A • (p - tubeMidpoint T)) := by rw [h_p'_def]
      _ = (x - tubeMidpoint T) - A • (p - tubeMidpoint T) := by abel
      _ = A • (y - tubeMidpoint T) - A • (p - tubeMidpoint T) := by
          rw [h_y_sub, smul_smul]
          have h5 : A * (1 / A) = 1 := by field_simp [hA.ne']
          rw [h5, one_smul]
      _ = A • ((y - tubeMidpoint T) - (p - tubeMidpoint T)) := by rw [← smul_sub]
      _ = A • (y - p) := by abel
  have h_eq : dist x p' = A * dist y p := by
    rw [dist_eq_norm, dist_eq_norm, h_xp'_eq, norm_smul]
    have h2 : ‖A‖ = A := by
      rw [Real.norm_eq_abs, abs_of_pos hA]
    rw [h2]
  have h_yp : dist y p ≤ ρ := by
    have h : A * dist y p ≤ A * ρ := by
      rw [← h_eq] <;> exact h_dist
    nlinarith
  have h_y_in : y ∈ T.carrier :=
    Metric.mem_cthickening_of_dist_le y p ρ (Kakeya.unitSegment T.base T.direction) hp_seg h_yp
  have h_final : AffineMap.homothety (tubeMidpoint T) A y = x := by
    rw [homothety_apply', h_y_sub, smul_smul]
    have h5 : A * (1 / A) = 1 := by field_simp [hA.ne']
    rw [h5, one_smul] <;> abel
  exact ⟨y, h_y_in, h_final⟩

/--
The dilated tube carrier is contained in the `A * ρ`-thickening of the
extended segment.
-/
lemma dilatedTubeCarrier_subset_cthickening_extendedSegment
    {ρ : ℝ} {A : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (T : Kakeya.DeltaTube ρ) :
    dilatedTubeCarrier A T ⊆ Metric.cthickening (A * ρ) (extendedSegment A T) := by
  rintro x ⟨y, hy, rfl⟩
  have h_inf : Metric.infEDist y (Kakeya.unitSegment T.base T.direction) ≤ ENNReal.ofReal ρ := hy
  rcases isCompact_unitSegment.exists_infEDist_eq_edist nonempty_unitSegment y
      with ⟨p, hp_seg, h_inf_eq⟩
  have h_edist : edist y p ≤ ENNReal.ofReal ρ := by
    rw [← h_inf_eq]; exact h_inf
  have h_dist : dist y p ≤ ρ := by
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ).mp h_edist
  let p' : Point3 := AffineMap.homothety (tubeMidpoint T) A p
  have hp'_in : p' ∈ extendedSegment A T := ⟨p, hp_seg, rfl⟩
  have h_xp' : dist (AffineMap.homothety (tubeMidpoint T) A y) p' ≤ A * ρ := by
    rw [dist_homothety hA]
    gcongr
  exact Metric.mem_cthickening_of_dist_le _ _ _ (extendedSegment A T) hp'_in h_xp'

/--
The dilated tube carrier equals the `A * ρ`-thickening of the length-`A`
segment centered at the midpoint.
-/
lemma dilatedTubeCarrier_eq_cthickening
    {ρ : ℝ} {A : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ)
    (T : Kakeya.DeltaTube ρ) :
    dilatedTubeCarrier A T = Metric.cthickening (A * ρ) (extendedSegment A T) := by
  apply Set.Subset.antisymm
  · exact dilatedTubeCarrier_subset_cthickening_extendedSegment hA.le hρ T
  · exact cthickening_extendedSegment_subset_dilatedTubeCarrier hA hρ T

/--
Combined closeness criterion: if the midpoint distance plus half the
direction distance is at most `(A - 1) * ρ`, then the first tube is
contained in the `A`-dilation of the second.
-/
lemma tube_contained_in_dilated_of_combined
    {ρ : ℝ} (hρ : 0 ≤ ρ) (A : ℝ) (hA : 1 ≤ A)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h : ‖tubeMidpoint T1 - tubeMidpoint T2‖ +
          ‖T1.direction - T2.direction‖ / 2 ≤ (A - 1) * ρ) :
    T1.carrier ⊆ dilatedTubeCarrier A T2 := by
  have hA_pos : 0 < A := by linarith
  intro x hx
  have h_inf : Metric.infEDist x (Kakeya.unitSegment T1.base T1.direction) ≤
      ENNReal.ofReal ρ := hx
  rcases isCompact_unitSegment.exists_infEDist_eq_edist nonempty_unitSegment x
      with ⟨y, hy_seg, h_inf_eq⟩
  have h_xy : dist x y ≤ ρ := by
    have h_edist : edist x y ≤ ENNReal.ofReal ρ := by
      rw [← h_inf_eq]; exact h_inf
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ).mp h_edist
  rcases hy_seg with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  set s : ℝ := t - 1 / 2 with hs_def
  have h_s1 : -(1 / 2 : ℝ) ≤ s := by
    rw [hs_def] <;> linarith
  have h_s2 : s ≤ (1 / 2 : ℝ) := by
    rw [hs_def] <;> linarith
  have hs_abs : |s| ≤ 1 / 2 := by
    exact abs_le.mpr ⟨h_s1, h_s2⟩
  have hs_A : |s| ≤ A / 2 := by
    calc |s| ≤ 1 / 2 := hs_abs
      _ ≤ A / 2 := by linarith
  let z : Point3 := tubeMidpoint T2 + s • T2.direction
  have hz_in : z ∈ extendedSegment A T2 :=
    mem_extendedSegment_of_abs_le hA_pos.le hs_A
  have h_yz : dist (T1.base + t • T1.direction) z ≤
      ‖tubeMidpoint T1 - tubeMidpoint T2‖ + ‖T1.direction - T2.direction‖ / 2 := by
    have hdiff : (T1.base + t • T1.direction) - z =
        (tubeMidpoint T1 - tubeMidpoint T2) + s • (T1.direction - T2.direction) := by
      simp only [z, tubeMidpoint, s]
      ext i
      simp [sub_smul] <;> ring
    rw [dist_eq_norm, hdiff]
    calc
      ‖(tubeMidpoint T1 - tubeMidpoint T2) + s • (T1.direction - T2.direction)‖
          ≤ ‖tubeMidpoint T1 - tubeMidpoint T2‖ +
              ‖s • (T1.direction - T2.direction)‖ := norm_add_le _ _
      _ = ‖tubeMidpoint T1 - tubeMidpoint T2‖ +
            |s| * ‖T1.direction - T2.direction‖ := by
          rw [norm_smul] <;> rfl
      _ ≤ ‖tubeMidpoint T1 - tubeMidpoint T2‖ +
            (1 / 2 : ℝ) * ‖T1.direction - T2.direction‖ := by
          gcongr
      _ = ‖tubeMidpoint T1 - tubeMidpoint T2‖ +
            ‖T1.direction - T2.direction‖ / 2 := by ring
  have h_xz : dist x z ≤ A * ρ := by
    calc
      dist x z ≤ dist x (T1.base + t • T1.direction) +
          dist (T1.base + t • T1.direction) z := dist_triangle _ _ _
      _ ≤ ρ + (‖tubeMidpoint T1 - tubeMidpoint T2‖ +
            ‖T1.direction - T2.direction‖ / 2) := by gcongr
      _ ≤ ρ + (A - 1) * ρ := by gcongr
      _ = A * ρ := by ring
  have h_main : x ∈ Metric.cthickening (A * ρ) (extendedSegment A T2) :=
    Metric.mem_cthickening_of_dist_le x z (A * ρ) (extendedSegment A T2) hz_in h_xz
  exact cthickening_extendedSegment_subset_dilatedTubeCarrier hA_pos hρ T2 h_main

/--
If the midpoint distance is at most `(A - 1) * ρ / 2` and the direction
distance is at most `(A - 1) * ρ`, then the first tube is contained in
the `A`-dilation of the second.
-/
lemma tube_contained_in_dilated_of_close
    {ρ : ℝ} (hρ : 0 ≤ ρ) (A : ℝ) (hA : 1 ≤ A)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h_mid : ‖tubeMidpoint T1 - tubeMidpoint T2‖ ≤ (A - 1) * ρ / 2)
    (h_dir : ‖T1.direction - T2.direction‖ ≤ (A - 1) * ρ) :
    T1.carrier ⊆ dilatedTubeCarrier A T2 := by
  have h_combined :
      ‖tubeMidpoint T1 - tubeMidpoint T2‖ + ‖T1.direction - T2.direction‖ / 2 ≤
        (A - 1) * ρ := by
    calc
      ‖tubeMidpoint T1 - tubeMidpoint T2‖ + ‖T1.direction - T2.direction‖ / 2
          ≤ (A - 1) * ρ / 2 + ((A - 1) * ρ) / 2 := by gcongr
      _ = (A - 1) * ρ := by ring
  exact tube_contained_in_dilated_of_combined hρ A hA T1 T2 h_combined

/--
If two tubes have the same direction and their midpoints are at most
`(A - 1) * ρ` apart, then the first tube is contained in the `A`-dilation
of the second.
-/
lemma tube_contained_in_dilated_of_same_dir
    {ρ : ℝ} (hρ : 0 ≤ ρ) (A : ℝ) (hA : 1 ≤ A)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h_dir : T1.direction = T2.direction)
    (h_mid : ‖tubeMidpoint T1 - tubeMidpoint T2‖ ≤ (A - 1) * ρ) :
    T1.carrier ⊆ dilatedTubeCarrier A T2 := by
  have h_dir_norm : ‖T1.direction - T2.direction‖ = 0 := by
    rw [h_dir] <;> simp
  have h_combined :
      ‖tubeMidpoint T1 - tubeMidpoint T2‖ + ‖T1.direction - T2.direction‖ / 2 ≤
        (A - 1) * ρ := by
    rw [h_dir_norm] <;> linarith
  exact tube_contained_in_dilated_of_combined hρ A hA T1 T2 h_combined

/--
If a tube is contained in the unit ball, its midpoint has norm at most 1.
-/
lemma tubeMidpoint_norm_le_one {ρ : ℝ} {T : Kakeya.DeltaTube ρ}
    (h : T.IsInUnitBall) : ‖tubeMidpoint T‖ ≤ 1 := by
  have h_mid_on_seg : tubeMidpoint T ∈ Kakeya.unitSegment T.base T.direction := by
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [tubeMidpoint] <;> abel
  have h_mid_in_carrier : tubeMidpoint T ∈ T.carrier := by
    have h2 : Metric.infEDist (tubeMidpoint T) (Kakeya.unitSegment T.base T.direction) ≤
        edist (tubeMidpoint T) (tubeMidpoint T) :=
      Metric.infEDist_le_edist_of_mem (x := tubeMidpoint T) h_mid_on_seg
    have h2' : edist (tubeMidpoint T) (tubeMidpoint T) = 0 := by simp
    rw [h2'] at h2
    have h3 : (0 : ENNReal) ≤ ENNReal.ofReal ρ := by simp
    exact le_trans h2 h3
  have h_mid_in_ball : tubeMidpoint T ∈ Kakeya.DeltaTube.unitBall :=
    h h_mid_in_carrier
  simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_eq_norm] using h_mid_in_ball

/--
Transverse closeness criterion: if the transverse component of the midpoint
difference plus half the transverse component of the direction difference is
at most `(A - 1) * ρ`, then the first tube is contained in the `A`-dilation of
the second.  Axial separation is absorbed by the length-`A` extended segment
(requires `A ≥ 5` and both tubes in the unit ball).
-/
lemma tube_contained_in_dilated_transverse
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (A : ℝ) (hA : 5 ≤ A)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h1 : T1.IsInUnitBall) (h2 : T2.IsInUnitBall)
    (h_trans :
      ‖(tubeMidpoint T1 - tubeMidpoint T2) -
          inner ℝ (tubeMidpoint T1 - tubeMidpoint T2) T2.direction • T2.direction‖
      + (1 / 2 : ℝ) * ‖T1.direction -
          inner ℝ T1.direction T2.direction • T2.direction‖ ≤ (A - 1) * ρ) :
    T1.carrier ⊆ dilatedTubeCarrier A T2 := by
  have hA_pos : 0 < A := by linarith
  set m1 := tubeMidpoint T1 with hm1
  set m2 := tubeMidpoint T2 with hm2
  set d1 := T1.direction with hd1
  set d2 := T2.direction with hd2
  have h_m1_norm : ‖m1‖ ≤ 1 := tubeMidpoint_norm_le_one h1
  have h_m2_norm : ‖m2‖ ≤ 1 := tubeMidpoint_norm_le_one h2
  have h_d1_unit : ‖d1‖ = 1 := T1.direction_unit
  have h_d2_unit : ‖d2‖ = 1 := T2.direction_unit
  intro x hx
  have h_inf : Metric.infEDist x (Kakeya.unitSegment T1.base T1.direction) ≤
      ENNReal.ofReal ρ := hx
  rcases isCompact_unitSegment.exists_infEDist_eq_edist nonempty_unitSegment x
      with ⟨y, hy_seg, h_inf_eq⟩
  have h_xy : dist x y ≤ ρ := by
    have h_edist : edist x y ≤ ENNReal.ofReal ρ := by
      rw [← h_inf_eq]; exact h_inf
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ.le).mp h_edist
  rcases hy_seg with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  set s : ℝ := t - 1 / 2 with hs_def
  have hs1 : -(1 / 2 : ℝ) ≤ s := by rw [hs_def] <;> linarith
  have hs2 : s ≤ (1 / 2 : ℝ) := by rw [hs_def] <;> linarith
  have hs_abs : |s| ≤ 1 / 2 := abs_le.mpr ⟨hs1, hs2⟩
  have h_y_eq : T1.base + t • d1 = m1 + s • d1 := by
    simp [hm1, tubeMidpoint, hs_def] <;> ext i <;> simp <;> ring
  let v : Point3 := (m1 - m2) + s • d1
  let a : ℝ := inner ℝ v d2
  let z : Point3 := m2 + a • d2
  have h_a_bound : |a| ≤ A / 2 := by
    have h4 : a = inner ℝ (m1 - m2) d2 + s * inner ℝ d1 d2 := by
      unfold a v
      rw [inner_add_left, inner_smul_left]
      <;> simp <;> ring
    rw [h4]
    have h5 : |inner ℝ (m1 - m2) d2| ≤ ‖m1 - m2‖ := by
      calc |inner ℝ (m1 - m2) d2| ≤ ‖m1 - m2‖ * ‖d2‖ := abs_real_inner_le_norm _ _
        _ = ‖m1 - m2‖ := by rw [h_d2_unit] <;> ring
    have h6 : ‖m1 - m2‖ ≤ 2 := by
      calc ‖m1 - m2‖ ≤ ‖m1‖ + ‖m2‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by gcongr
        _ = 2 := by norm_num
    have h7 : |s * inner ℝ d1 d2| ≤ 1 / 2 := by
      calc |s * inner ℝ d1 d2|
          = |s| * |inner ℝ d1 d2| := by rw [abs_mul]
        _ ≤ |s| * (‖d1‖ * ‖d2‖) := by gcongr <;> exact abs_real_inner_le_norm _ _
        _ = |s| := by rw [h_d1_unit, h_d2_unit] <;> ring
        _ ≤ 1 / 2 := hs_abs
    calc |inner ℝ (m1 - m2) d2 + s * inner ℝ d1 d2|
        ≤ |inner ℝ (m1 - m2) d2| + |s * inner ℝ d1 d2| := abs_add_le _ _
      _ ≤ ‖m1 - m2‖ + 1 / 2 := by gcongr
      _ ≤ 2 + 1 / 2 := by gcongr
      _ = 5 / 2 := by norm_num
      _ ≤ A / 2 := by linarith
  have hz_in : z ∈ extendedSegment A T2 :=
    mem_extendedSegment_of_abs_le hA_pos.le h_a_bound
  have h_yz : dist (T1.base + t • d1) z ≤ (A - 1) * ρ := by
    rw [h_y_eq]
    have h8 : (m1 + s • d1) - z = v - inner ℝ v d2 • d2 := by
      simp [z, v] <;> abel
    rw [dist_eq_norm, h8]
    set a1 := inner ℝ (m1 - m2) d2 with ha1
    set a2 := inner ℝ d1 d2 with ha2
    have h_inner_v : inner ℝ v d2 = a1 + s * a2 := by
      simp [v, ha1, ha2, inner_add_left, inner_smul_left] <;> ring
    have h9 : v - inner ℝ v d2 • d2 =
        ((m1 - m2) - a1 • d2) + s • (d1 - a2 • d2) := by
      have h_v_exp : v = (m1 - m2) + s • d1 := by simp [v]
      rw [h_v_exp, h_inner_v]
      have h_smul : (a1 + s * a2) • d2 = a1 • d2 + s • (a2 • d2) := by
        rw [add_smul, smul_smul] <;> ring
      rw [h_smul]
      have h_step1 : ((m1 - m2) + s • d1) - (a1 • d2 + s • (a2 • d2)) =
          ((m1 - m2) - a1 • d2) + (s • d1 - s • (a2 • d2)) := by abel
      rw [h_step1]
      have h_step2 : s • d1 - s • (a2 • d2) = s • (d1 - a2 • d2) := by
        rw [← smul_sub]
      rw [h_step2]
    rw [h9]
    calc
      ‖((m1 - m2) - inner ℝ (m1 - m2) d2 • d2) + s • (d1 - inner ℝ d1 d2 • d2)‖
          ≤ ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
              ‖s • (d1 - inner ℝ d1 d2 • d2)‖ := norm_add_le _ _
      _ = ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
            |s| * ‖d1 - inner ℝ d1 d2 • d2‖ := by
          rw [norm_smul] <;> rfl
      _ ≤ ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
            (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ := by gcongr
      _ ≤ (A - 1) * ρ := h_trans
  have h_xz : dist x z ≤ A * ρ := by
    calc
      dist x z ≤ dist x (T1.base + t • d1) + dist (T1.base + t • d1) z :=
        dist_triangle _ _ _
      _ ≤ ρ + (A - 1) * ρ := by gcongr
      _ = A * ρ := by ring
  have h_main : x ∈ Metric.cthickening (A * ρ) (extendedSegment A T2) :=
    Metric.mem_cthickening_of_dist_le x z (A * ρ) (extendedSegment A T2) hz_in h_xz
  exact cthickening_extendedSegment_subset_dilatedTubeCarrier hA_pos hρ.le T2 h_main

/--
The orthogonal component of `v` relative to a unit vector `u` has norm at most
`‖v‖`.
-/
lemma norm_transverse_le {u : Point3} (hu : ‖u‖ = 1) (v : Point3) :
    ‖v - inner ℝ v u • u‖ ≤ ‖v‖ := by
  set c : ℝ := inner ℝ v u with hc
  set x : Point3 := v - c • u with hx
  set y : Point3 := c • u with hy
  have h_iuu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq u, hu] <;> norm_num
  have h_orth : inner ℝ x y = 0 := by
    have h1 : inner ℝ x y = inner ℝ (v - c • u) (c • u) := by rfl
    rw [h1]
    have h2 : inner ℝ (v - c • u) (c • u) =
        inner ℝ v (c • u) - inner ℝ (c • u) (c • u) := by
      rw [inner_sub_left]
    rw [h2]
    have h3 : inner ℝ v (c • u) = c * inner ℝ v u := by
      rw [inner_smul_right] <;> simp
    have h4 : inner ℝ (c • u) (c • u) = c ^ 2 * inner ℝ u u := by
      rw [inner_smul_left, inner_smul_right] <;> simp <;> ring
    rw [h3, h4, h_iuu, hc] <;> ring
  have h_pyth : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real h_orth
    have h' : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ := h
    have h'' : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
      nlinarith
    exact h''
  have h_xy : x + y = v := by
    simp [hx, hy] <;> abel
  rw [h_xy] at h_pyth
  have h_main : ‖x‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h_pyth] <;> nlinarith [sq_nonneg ‖y‖]
  have h_nonneg : 0 ≤ ‖x‖ := by positivity
  have h_v_nonneg : 0 ≤ ‖v‖ := by positivity
  nlinarith

/--
If two tubes of the same radius have intersecting carriers, then the transverse
component of their midpoint difference is bounded by `2ρ` plus half the
transverse direction difference.
-/
lemma transverse_midpoint_bound_of_intersection
    {ρ : ℝ} (hρ : 0 < ρ)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h_nonempty : (T1.carrier ∩ T2.carrier).Nonempty) :
    ‖(tubeMidpoint T1 - tubeMidpoint T2) -
        inner ℝ (tubeMidpoint T1 - tubeMidpoint T2) T2.direction • T2.direction‖
    ≤ 2 * ρ + (1 / 2 : ℝ) * ‖T1.direction -
        inner ℝ T1.direction T2.direction • T2.direction‖ := by
  rcases h_nonempty with ⟨x, hx1, hx2⟩
  -- Find y1 on segment1 close to x
  rcases isCompact_unitSegment.exists_infEDist_eq_edist nonempty_unitSegment x
      with ⟨y1, hy1_seg, h_inf1_eq⟩
  have h_xy1 : dist x y1 ≤ ρ := by
    have h_edist : edist x y1 ≤ ENNReal.ofReal ρ := by
      rw [← h_inf1_eq]; exact hx1
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ.le).mp h_edist
  rcases hy1_seg with ⟨t1, ⟨ht1_0, ht1_1⟩, rfl⟩
  -- Find y2 on segment2 close to x
  rcases isCompact_unitSegment.exists_infEDist_eq_edist nonempty_unitSegment x
      with ⟨y2, hy2_seg, h_inf2_eq⟩
  have h_xy2 : dist x y2 ≤ ρ := by
    have h_edist : edist x y2 ≤ ENNReal.ofReal ρ := by
      rw [← h_inf2_eq]; exact hx2
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ.le).mp h_edist
  rcases hy2_seg with ⟨t2, ⟨ht2_0, ht2_1⟩, rfl⟩
  -- ‖y1 - y2‖ ≤ 2ρ
  have h_y1y2 : ‖(T1.base + t1 • T1.direction) - (T2.base + t2 • T2.direction)‖ ≤ 2 * ρ := by
    have h_xy1' : dist (T1.base + t1 • T1.direction) x ≤ ρ := by
      rw [dist_comm] <;> exact h_xy1
    have h : dist (T1.base + t1 • T1.direction) (T2.base + t2 • T2.direction) ≤ 2 * ρ := by
      calc dist (T1.base + t1 • T1.direction) (T2.base + t2 • T2.direction)
          ≤ dist (T1.base + t1 • T1.direction) x + dist x (T2.base + t2 • T2.direction) :=
            dist_triangle _ _ _
      _ ≤ ρ + ρ := by gcongr
      _ = 2 * ρ := by ring
    simpa [dist_eq_norm] using h
  set m1 := tubeMidpoint T1 with hm1
  set m2 := tubeMidpoint T2 with hm2
  set d1 := T1.direction with hd1
  set d2 := T2.direction with hd2
  set s1 : ℝ := t1 - 1 / 2 with hs1_def
  set s2 : ℝ := t2 - 1 / 2 with hs2_def
  have hs1_abs : |s1| ≤ 1 / 2 := by
    rw [hs1_def] <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_y1_eq : T1.base + t1 • d1 = m1 + s1 • d1 := by
    simp [hm1, tubeMidpoint, hs1_def] <;> ext i <;> simp <;> ring
  have h_y2_eq : T2.base + t2 • d2 = m2 + s2 • d2 := by
    simp [hm2, tubeMidpoint, hs2_def] <;> ext i <;> simp <;> ring
  let trans : Point3 → Point3 := fun v => v - inner ℝ v d2 • d2
  have h_trans_smul : ∀ (c : ℝ) (v : Point3), trans (c • v) = c • trans v := by
    intro c v
    have h1 : trans (c • v) = c • v - inner ℝ (c • v) d2 • d2 := by rfl
    rw [h1]
    have h2 : inner ℝ (c • v) d2 = c * inner ℝ v d2 := by
      rw [inner_smul_left] <;> simp
    rw [h2]
    have h3 : c • v - (c * inner ℝ v d2) • d2 = c • (v - inner ℝ v d2 • d2) := by
      have h4 : (c * inner ℝ v d2) • d2 = c • (inner ℝ v d2 • d2) := by
        rw [smul_smul] <;> ring
      rw [h4, ← smul_sub]
    rw [h3] <;> rfl
  have h_trans_sub : ∀ (v w : Point3), trans (v - w) = trans v - trans w := by
    intro v w
    have h1 : trans (v - w) = (v - w) - inner ℝ (v - w) d2 • d2 := by rfl
    rw [h1]
    have h2 : inner ℝ (v - w) d2 = inner ℝ v d2 - inner ℝ w d2 := by rw [inner_sub_left]
    rw [h2]
    have h3 : (v - w) - (inner ℝ v d2 - inner ℝ w d2) • d2 =
        (v - inner ℝ v d2 • d2) - (w - inner ℝ w d2 • d2) := by
      rw [sub_smul] <;> abel
    rw [h3] <;> rfl
  have h_trans_add : ∀ (v w : Point3), trans (v + w) = trans v + trans w := by
    intro v w
    have h_neg : trans (-w) = -trans w := by
      have h1 : -w = (-1 : ℝ) • w := by simp
      rw [h1, h_trans_smul] <;> simp
    have h : trans (v + w) = trans (v - (-w)) := by congr 1; abel
    rw [h, h_trans_sub, h_neg] <;> abel
  have h_trans_d2 : trans d2 = 0 := by
    have h_inner : inner ℝ d2 d2 = (1 : ℝ) := by
      have h : inner ℝ d2 d2 = ‖d2‖ ^ 2 := real_inner_self_eq_norm_sq d2
      rw [h, T2.direction_unit] <;> norm_num
    have h : trans d2 = d2 - inner ℝ d2 d2 • d2 := by rfl
    rw [h, h_inner] <;> simp
  have h_main_eq : m1 - m2 =
      (T1.base + t1 • d1) - (T2.base + t2 • d2) - s1 • d1 + s2 • d2 := by
    rw [h_y1_eq, h_y2_eq] <;> abel
  set a := (T1.base + t1 • d1) - (T2.base + t2 • d2) with ha
  set b : Point3 := (-s1) • d1 with hb
  set c : Point3 := s2 • d2 with hc
  have h1 : m1 - m2 = a + b + c := by
    rw [h_main_eq, ha, hb, hc] <;> ext i <;> simp <;> ring
  have h3 : trans (a + b + c) = trans a + trans b + trans c := by
    have h31 : trans (a + b + c) = trans (a + b) + trans c := h_trans_add (a + b) c
    have h32 : trans (a + b) = trans a + trans b := h_trans_add a b
    rw [h31, h32] <;> abel
  have h_trans_m : trans (m1 - m2) = trans a - s1 • trans d1 := by
    calc
      trans (m1 - m2) = trans (a + b + c) := by rw [h1]
      _ = trans a + trans b + trans c := h3
      _ = trans a + (-s1) • trans d1 + s2 • trans d2 := by
          rw [h_trans_smul (-s1) d1, h_trans_smul s2 d2] <;> abel
      _ = trans a - s1 • trans d1 := by
          rw [h_trans_d2] <;> simp <;> abel
  have h_goal : ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ = ‖trans (m1 - m2)‖ := by rfl
  rw [h_goal, h_trans_m]
  calc
    ‖trans ((T1.base + t1 • d1) - (T2.base + t2 • d2)) - s1 • trans d1‖
        ≤ ‖trans ((T1.base + t1 • d1) - (T2.base + t2 • d2))‖ + ‖s1 • trans d1‖ :=
          norm_sub_le _ _
    _ = ‖trans ((T1.base + t1 • d1) - (T2.base + t2 • d2))‖ + ‖s1‖ * ‖trans d1‖ := by
          rw [norm_smul]
    _ = ‖trans ((T1.base + t1 • d1) - (T2.base + t2 • d2))‖ + |s1| * ‖trans d1‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ‖(T1.base + t1 • d1) - (T2.base + t2 • d2)‖ + |s1| * ‖trans d1‖ := by
          gcongr <;> exact norm_transverse_le T2.direction_unit _
    _ ≤ 2 * ρ + (1 / 2 : ℝ) * ‖trans d1‖ := by gcongr
    _ = 2 * ρ + (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ := by rfl

/--
Generalized transverse closeness criterion: if the transverse component of the
midpoint difference plus half the transverse component of the direction difference
is at most `(A - 1) * ρ`, and the midpoint norms are bounded by `C`, then the first
tube is contained in the `A`-dilation of the second.  Requires `A ≥ 4*C + 1`.
-/
lemma tube_contained_in_dilated_transverse_general
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (A C : ℝ) (hA : 4 * C + 1 ≤ A) (hC : 0 ≤ C)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h_m1_norm : ‖tubeMidpoint T1‖ ≤ C)
    (h_m2_norm : ‖tubeMidpoint T2‖ ≤ C)
    (h_trans :
      ‖(tubeMidpoint T1 - tubeMidpoint T2) -
          inner ℝ (tubeMidpoint T1 - tubeMidpoint T2) T2.direction • T2.direction‖
      + (1 / 2 : ℝ) * ‖T1.direction -
          inner ℝ T1.direction T2.direction • T2.direction‖ ≤ (A - 1) * ρ) :
    T1.carrier ⊆ dilatedTubeCarrier A T2 := by
  have hA_pos : 0 < A := by linarith
  set m1 := tubeMidpoint T1 with hm1
  set m2 := tubeMidpoint T2 with hm2
  set d1 := T1.direction with hd1
  set d2 := T2.direction with hd2
  have h_d1_unit : ‖d1‖ = 1 := T1.direction_unit
  have h_d2_unit : ‖d2‖ = 1 := T2.direction_unit
  have h_m1m2 : ‖m1 - m2‖ ≤ 2 * C := by
    calc ‖m1 - m2‖ ≤ ‖m1‖ + ‖m2‖ := norm_sub_le _ _
      _ ≤ C + C := by gcongr
      _ = 2 * C := by ring
  intro x hx
  have h_inf : Metric.infEDist x (Kakeya.unitSegment T1.base T1.direction) ≤
      ENNReal.ofReal ρ := hx
  rcases isCompact_unitSegment.exists_infEDist_eq_edist nonempty_unitSegment x
      with ⟨y, hy_seg, h_inf_eq⟩
  have h_xy : dist x y ≤ ρ := by
    have h_edist : edist x y ≤ ENNReal.ofReal ρ := by
      rw [← h_inf_eq]; exact h_inf
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ.le).mp h_edist
  rcases hy_seg with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  set s : ℝ := t - 1 / 2 with hs_def
  have hs1 : -(1 / 2 : ℝ) ≤ s := by rw [hs_def] <;> linarith
  have hs2 : s ≤ (1 / 2 : ℝ) := by rw [hs_def] <;> linarith
  have hs_abs : |s| ≤ 1 / 2 := abs_le.mpr ⟨hs1, hs2⟩
  have h_y_eq : T1.base + t • d1 = m1 + s • d1 := by
    simp [hm1, tubeMidpoint, hs_def] <;> ext i <;> simp <;> ring
  let v : Point3 := (m1 - m2) + s • d1
  let a : ℝ := inner ℝ v d2
  let z : Point3 := m2 + a • d2
  have h_a_bound : |a| ≤ A / 2 := by
    have h4 : a = inner ℝ (m1 - m2) d2 + s * inner ℝ d1 d2 := by
      unfold a v
      rw [inner_add_left, inner_smul_left] <;> simp <;> ring
    rw [h4]
    have h5 : |inner ℝ (m1 - m2) d2| ≤ ‖m1 - m2‖ := by
      calc |inner ℝ (m1 - m2) d2| ≤ ‖m1 - m2‖ * ‖d2‖ := abs_real_inner_le_norm _ _
        _ = ‖m1 - m2‖ := by rw [h_d2_unit] <;> ring
    have h6 : |inner ℝ (m1 - m2) d2| ≤ 2 * C := h5.trans h_m1m2
    have h7 : |s * inner ℝ d1 d2| ≤ 1 / 2 := by
      calc |s * inner ℝ d1 d2|
          = |s| * |inner ℝ d1 d2| := by rw [abs_mul]
        _ ≤ |s| * (‖d1‖ * ‖d2‖) := by gcongr <;> exact abs_real_inner_le_norm _ _
        _ = |s| := by rw [h_d1_unit, h_d2_unit] <;> ring
        _ ≤ 1 / 2 := hs_abs
    calc |inner ℝ (m1 - m2) d2 + s * inner ℝ d1 d2|
        ≤ |inner ℝ (m1 - m2) d2| + |s * inner ℝ d1 d2| := abs_add_le _ _
      _ ≤ 2 * C + 1 / 2 := by gcongr
      _ ≤ A / 2 := by linarith
  have hz_in : z ∈ extendedSegment A T2 :=
    mem_extendedSegment_of_abs_le hA_pos.le h_a_bound
  have h_yz : dist (T1.base + t • d1) z ≤ (A - 1) * ρ := by
    rw [h_y_eq]
    have h8 : (m1 + s • d1) - z = v - inner ℝ v d2 • d2 := by
      simp [z, v] <;> abel
    rw [dist_eq_norm, h8]
    set a1 := inner ℝ (m1 - m2) d2 with ha1
    set a2 := inner ℝ d1 d2 with ha2
    have h_inner_v : inner ℝ v d2 = a1 + s * a2 := by
      simp [v, ha1, ha2, inner_add_left, inner_smul_left] <;> ring
    have h9 : v - inner ℝ v d2 • d2 =
        ((m1 - m2) - a1 • d2) + s • (d1 - a2 • d2) := by
      have h_v_exp : v = (m1 - m2) + s • d1 := by simp [v]
      rw [h_v_exp, h_inner_v]
      have h_smul : (a1 + s * a2) • d2 = a1 • d2 + s • (a2 • d2) := by
        rw [add_smul, smul_smul] <;> ring
      rw [h_smul]
      have h_step1 : ((m1 - m2) + s • d1) - (a1 • d2 + s • (a2 • d2)) =
          ((m1 - m2) - a1 • d2) + (s • d1 - s • (a2 • d2)) := by abel
      rw [h_step1]
      have h_step2 : s • d1 - s • (a2 • d2) = s • (d1 - a2 • d2) := by
        rw [← smul_sub]
      rw [h_step2]
    rw [h9]
    calc
      ‖((m1 - m2) - inner ℝ (m1 - m2) d2 • d2) + s • (d1 - inner ℝ d1 d2 • d2)‖
          ≤ ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
              ‖s • (d1 - inner ℝ d1 d2 • d2)‖ := norm_add_le _ _
      _ = ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
            |s| * ‖d1 - inner ℝ d1 d2 • d2‖ := by
          rw [norm_smul] <;> rfl
      _ ≤ ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
            (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ := by gcongr
      _ ≤ (A - 1) * ρ := h_trans
  have h_xz : dist x z ≤ A * ρ := by
    calc
      dist x z ≤ dist x (T1.base + t • d1) + dist (T1.base + t • d1) z :=
        dist_triangle _ _ _
      _ ≤ ρ + (A - 1) * ρ := by gcongr
      _ = A * ρ := by ring
  have h_main : x ∈ Metric.cthickening (A * ρ) (extendedSegment A T2) :=
    Metric.mem_cthickening_of_dist_le x z (A * ρ) (extendedSegment A T2) hz_in h_xz
  exact cthickening_extendedSegment_subset_dilatedTubeCarrier hA_pos hρ.le T2 h_main

/--
If every point on the unit segment of `T1` is within distance `A * ρ2 - ρ1`
of the extended segment of `T2`, then `T1.carrier ⊆ dilatedTubeCarrier A T2`.
-/
lemma tube_contained_in_dilated_of_segment_witness
    {ρ1 ρ2 : ℝ} (hρ1 : 0 ≤ ρ1) (hρ2 : 0 ≤ ρ2)
    (A : ℝ) (hA : 1 ≤ A)
    (T1 : Kakeya.DeltaTube ρ1) (T2 : Kakeya.DeltaTube ρ2)
    (hbound : A * ρ2 - ρ1 ≥ 0)
    (h_main : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ z ∈ extendedSegment A T2,
        dist (T1.base + t • T1.direction) z ≤ A * ρ2 - ρ1) :
    T1.carrier ⊆ dilatedTubeCarrier A T2 := by
  have hA_pos : 0 < A := by linarith
  intro x hx
  have h_inf : Metric.infEDist x (Kakeya.unitSegment T1.base T1.direction) ≤
      ENNReal.ofReal ρ1 := hx
  rcases isCompact_unitSegment.exists_infEDist_eq_edist nonempty_unitSegment x
      with ⟨y, hy_seg, h_inf_eq⟩
  have h_xy : dist x y ≤ ρ1 := by
    have h_edist : edist x y ≤ ENNReal.ofReal ρ1 := by
      rw [← h_inf_eq]; exact h_inf
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ1).mp h_edist
  rcases hy_seg with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  rcases h_main t ⟨ht0, ht1⟩ with ⟨z, hz_in, h_yz⟩
  have h_xz : dist x z ≤ A * ρ2 := by
    calc
      dist x z ≤ dist x (T1.base + t • T1.direction) +
          dist (T1.base + t • T1.direction) z := dist_triangle _ _ _
      _ ≤ ρ1 + (A * ρ2 - ρ1) := by gcongr
      _ = A * ρ2 := by ring
  have h_main2 : x ∈ Metric.cthickening (A * ρ2) (extendedSegment A T2) :=
    Metric.mem_cthickening_of_dist_le x z (A * ρ2) (extendedSegment A T2) hz_in h_xz
  exact cthickening_extendedSegment_subset_dilatedTubeCarrier hA_pos hρ2 T2 h_main2

end Kakeya.Streamlined.GeometricLemmas

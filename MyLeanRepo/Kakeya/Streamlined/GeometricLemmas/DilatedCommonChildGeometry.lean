import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CommonChildGeometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment

/-!
# Geometry inherited from a child inside a dilated parent

The paper-faithful single-scale construction only places each fine carrier
inside one fixed homothetic dilation of its parent.  This module records the
corresponding axis witnesses, direction control, and midpoint control with
explicit dependence on that dilation factor.
-/

noncomputable section

open Metric

namespace Kakeya.Streamlined.GeometricLemmas

private lemma isCompact_extendedSegment
    {rho A : ℝ} (T : Kakeya.DeltaTube rho) :
    IsCompact (extendedSegment A T) := by
  apply IsCompact.image
  · apply IsCompact.image
    · exact isCompact_Icc
    · exact continuous_const.add (continuous_id.smul continuous_const)
  · fun_prop

private lemma nonempty_extendedSegment
    {rho A : ℝ} (hA : 0 ≤ A) (T : Kakeya.DeltaTube rho) :
    (extendedSegment A T).Nonempty := by
  have hmid :=
    mem_extendedSegment_of_abs_le (T := T) hA
      (show |(0 : ℝ)| ≤ A / 2 by simp; linarith)
  exact ⟨tubeMidpoint T, by simpa using hmid⟩

/--
Every point in an `A`-dilated radius-`rho` carrier lies within `A * rho` of
an axis point whose signed displacement from the parent midpoint is at most
`A / 2`.
-/
lemma exists_extended_axis_point_dist_le
    {rho A : ℝ} (hA : 0 < A) (hrho : 0 ≤ rho)
    (T : Kakeya.DeltaTube rho)
    {x : Point3} (hx : x ∈ dilatedTubeCarrier A T) :
    ∃ s : ℝ, |s| ≤ A / 2 ∧
      dist x (tubeMidpoint T + s • T.direction) ≤ A * rho := by
  have hx' :
      x ∈ Metric.cthickening (A * rho) (extendedSegment A T) := by
    rw [← dilatedTubeCarrier_eq_cthickening hA hrho T]
    exact hx
  rcases (isCompact_extendedSegment T).exists_infEDist_eq_edist
      (nonempty_extendedSegment hA.le T) x with
    ⟨p, hp, hinf⟩
  have hpdist : dist x p ≤ A * rho := by
    have hedist : edist x p ≤ ENNReal.ofReal (A * rho) := by
      rw [← hinf]
      exact hx'
    rw [edist_dist] at hedist
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA.le hrho)).mp hedist
  rcases hp with ⟨y, ⟨t, ht, rfl⟩, rfl⟩
  let s : ℝ := A * (t - 1 / 2)
  have ht_abs : |t - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hs_abs : |s| ≤ A / 2 := by
    rw [show s = A * (t - 1 / 2) by rfl, abs_mul,
      abs_of_pos hA]
    nlinarith
  refine ⟨s, hs_abs, ?_⟩
  have heq :
      AffineMap.homothety (tubeMidpoint T) A
          (T.base + t • T.direction) =
        tubeMidpoint T + s • T.direction := by
    rw [AffineMap.homothety_apply]
    ext i
    simp [tubeMidpoint, s, vsub_eq_sub]
    ring
  rwa [← heq]

/--
If a fine carrier lies in an `A`-dilated parent, the two unit directions are
`4 * A * rho`-close after possibly reversing the parent orientation.
-/
lemma fine_dilated_parent_direction_close_or_reverse
    {delta rho A : ℝ} (hA : 0 < A) (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ dilatedTubeCarrier A parent) :
    ‖fine.direction - parent.direction‖ ≤ 4 * A * rho ∨
      ‖fine.direction + parent.direction‖ ≤ 4 * A * rho := by
  have hbase_segment :
      fine.base ∈ Kakeya.unitSegment fine.base fine.direction :=
    ⟨0, by norm_num, by simp⟩
  have hend_segment :
      fine.base + fine.direction ∈
        Kakeya.unitSegment fine.base fine.direction :=
    ⟨1, by norm_num, by simp⟩
  have hbase : fine.base ∈ fine.carrier := by
    change Metric.infEDist fine.base
        (Kakeya.unitSegment fine.base fine.direction) ≤ ENNReal.ofReal delta
    rw [Metric.infEDist_zero_of_mem hbase_segment]
    exact bot_le
  have hend : fine.base + fine.direction ∈ fine.carrier := by
    change Metric.infEDist (fine.base + fine.direction)
        (Kakeya.unitSegment fine.base fine.direction) ≤ ENNReal.ofReal delta
    rw [Metric.infEDist_zero_of_mem hend_segment]
    exact bot_le
  rcases exists_extended_axis_point_dist_le hA hrho parent
      (hcontained hbase) with ⟨s0, _hs0, h0⟩
  rcases exists_extended_axis_point_dist_le hA hrho parent
      (hcontained hend) with ⟨s1, _hs1, h1⟩
  let a : ℝ := s1 - s0
  have h0_norm :
      ‖fine.base -
          (tubeMidpoint parent + s0 • parent.direction)‖ ≤ A * rho := by
    simpa [dist_eq_norm] using h0
  have h1_norm :
      ‖(fine.base + fine.direction) -
          (tubeMidpoint parent + s1 • parent.direction)‖ ≤ A * rho := by
    simpa [dist_eq_norm] using h1
  have hclose :
      ‖fine.direction - a • parent.direction‖ ≤ 2 * A * rho := by
    have heq :
        fine.direction - a • parent.direction =
          ((fine.base + fine.direction) -
              (tubeMidpoint parent + s1 • parent.direction)) -
            (fine.base -
              (tubeMidpoint parent + s0 • parent.direction)) := by
      dsimp only [a]
      module
    rw [heq]
    calc
      ‖((fine.base + fine.direction) -
            (tubeMidpoint parent + s1 • parent.direction)) -
          (fine.base -
            (tubeMidpoint parent + s0 • parent.direction))‖
          ≤ ‖(fine.base + fine.direction) -
              (tubeMidpoint parent + s1 • parent.direction)‖ +
            ‖fine.base -
              (tubeMidpoint parent + s0 • parent.direction)‖ :=
        norm_sub_le _ _
      _ ≤ A * rho + A * rho := add_le_add h1_norm h0_norm
      _ = 2 * A * rho := by ring
  have hnorm_gap : abs (1 - |a|) ≤ 2 * A * rho := by
    have h := abs_norm_sub_norm_le fine.direction
      (a • parent.direction)
    rw [fine.direction_unit, norm_smul, parent.direction_unit,
      mul_one, Real.norm_eq_abs] at h
    exact h.trans hclose
  by_cases ha : 0 ≤ a
  · left
    have hgap : |1 - a| ≤ 2 * A * rho := by
      simpa [abs_of_nonneg ha] using hnorm_gap
    have hscaled :
        ‖a • parent.direction - parent.direction‖ = |1 - a| := by
      have heq :
          a • parent.direction - parent.direction =
            (a - 1) • parent.direction := by
        module
      rw [heq, norm_smul, parent.direction_unit, mul_one,
        Real.norm_eq_abs]
      exact abs_sub_comm a 1
    have heq :
        fine.direction - parent.direction =
          (fine.direction - a • parent.direction) +
            (a • parent.direction - parent.direction) := by
      module
    rw [heq]
    calc
      ‖(fine.direction - a • parent.direction) +
          (a • parent.direction - parent.direction)‖
          ≤ ‖fine.direction - a • parent.direction‖ +
            ‖a • parent.direction - parent.direction‖ :=
        norm_add_le _ _
      _ ≤ 2 * A * rho + |1 - a| :=
        add_le_add hclose hscaled.le
      _ ≤ 4 * A * rho := by linarith
  · right
    have ha_nonpos : a ≤ 0 := le_of_not_ge ha
    have hgap : |1 + a| ≤ 2 * A * rho := by
      have hrewrite : 1 - -a = 1 + a := by ring
      simpa [abs_of_nonpos ha_nonpos, hrewrite] using hnorm_gap
    have hscaled :
        ‖a • parent.direction - (-parent.direction)‖ = |1 + a| := by
      have heq :
          a • parent.direction - (-parent.direction) =
            (a + 1) • parent.direction := by
        module
      rw [heq, norm_smul, parent.direction_unit, mul_one,
        Real.norm_eq_abs]
      congr 1
      ring
    have heq :
        fine.direction + parent.direction =
          (fine.direction - a • parent.direction) +
            (a • parent.direction - (-parent.direction)) := by
      module
    rw [heq]
    calc
      ‖(fine.direction - a • parent.direction) +
          (a • parent.direction - -parent.direction)‖
          ≤ ‖fine.direction - a • parent.direction‖ +
            ‖a • parent.direction - -parent.direction‖ :=
        norm_add_le _ _
      _ ≤ 2 * A * rho + |1 + a| :=
        add_le_add hclose hscaled.le
      _ ≤ 4 * A * rho := by linarith

/--
After possibly reversing a dilated parent, its carrier, midpoint, and all
homothetic dilations are unchanged, while its direction is close to the fine
direction.
-/
lemma exists_oriented_dilated_parent_direction_close
    {delta rho A : ℝ} (hA : 0 < A) (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ dilatedTubeCarrier A parent) :
    ∃ oriented : Kakeya.DeltaTube rho,
      oriented.carrier = parent.carrier ∧
      tubeMidpoint oriented = tubeMidpoint parent ∧
      (∀ B : ℝ,
        dilatedTubeCarrier B oriented =
          dilatedTubeCarrier B parent) ∧
      ‖fine.direction - oriented.direction‖ ≤ 4 * A * rho := by
  rcases fine_dilated_parent_direction_close_or_reverse
      hA hrho fine parent hcontained with hsame | hreversed
  · exact ⟨parent, rfl, rfl, fun _ => rfl, hsame⟩
  · refine ⟨reverseTube parent, reverseTube_carrier parent,
      reverseTube_midpoint parent,
      (fun B => reverseTube_dilatedCarrier (A := B) parent), ?_⟩
    simpa [reverseTube] using hreversed

/--
The midpoint of an `A`-dilated parent of a unit-ball fine tube has norm at
most `1 + 3A/2`.
-/
lemma dilated_parent_midpoint_norm_le
    {delta rho A : ℝ} (hA : 0 < A)
    (hrho : 0 ≤ rho) (hrho_one : rho ≤ 1)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (hfine_ball : fine.IsInUnitBall)
    (hcontained : fine.carrier ⊆ dilatedTubeCarrier A parent) :
    ‖tubeMidpoint parent‖ ≤ 1 + 3 * A / 2 := by
  let x := tubeMidpoint fine
  have hx_fine : x ∈ fine.carrier :=
    tubeMidpoint_mem_carrier fine
  have hx_parent : x ∈ dilatedTubeCarrier A parent :=
    hcontained hx_fine
  rcases exists_extended_axis_point_dist_le hA hrho parent hx_parent with
    ⟨s, hs, hdist⟩
  let p := tubeMidpoint parent + s • parent.direction
  have hx_norm : ‖x‖ ≤ 1 := by
    have hball := hfine_ball hx_fine
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall,
      dist_eq_norm] using hball
  have hmid_p : dist (tubeMidpoint parent) p = |s| := by
    rw [dist_eq_norm]
    have heq :
        tubeMidpoint parent - p =
          (-s) • parent.direction := by
      dsimp only [p]
      module
    rw [heq, norm_smul, parent.direction_unit, mul_one,
      Real.norm_eq_abs, abs_neg]
  have hp_x : dist p x ≤ A * rho := by
    simpa [p, dist_comm] using hdist
  calc
    ‖tubeMidpoint parent‖
        = dist (tubeMidpoint parent) 0 := by
          simp [dist_eq_norm]
    _ ≤ dist (tubeMidpoint parent) p + dist p 0 :=
      dist_triangle _ _ _
    _ ≤ dist (tubeMidpoint parent) p +
        (dist p x + dist x 0) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ A / 2 + (A * rho + 1) := by
      have hmid_le :
          dist (tubeMidpoint parent) p ≤ A / 2 := by
        rw [hmid_p]
        exact hs
      have hx_zero : dist x 0 ≤ 1 := by
        simpa [dist_eq_norm] using hx_norm
      exact add_le_add hmid_le (add_le_add hp_x hx_zero)
    _ ≤ 1 + 3 * A / 2 := by
      have hArho : A * rho ≤ A := by
        simpa using mul_le_mul_of_nonneg_left hrho_one hA.le
      nlinarith

end Kakeya.Streamlined.GeometricLemmas

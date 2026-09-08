import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.MidpointBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeOrientation

/-!
# Geometry inherited from a common child tube

If a fine tube is contained in a coarse parent, each point of the fine axis is
within the parent radius of a point on the parent axis.  These witnesses are
the elementary input for comparing two independently chosen parents of the
same fine tube.
-/

noncomputable section

open Metric

namespace Kakeya.Streamlined.GeometricLemmas

private lemma isCompact_unitSegment' {base direction : Point3} :
    IsCompact (Kakeya.unitSegment base direction) := by
  apply IsCompact.image
  · exact isCompact_Icc
  · exact continuous_const.add (continuous_id.smul continuous_const)

private lemma nonempty_unitSegment' {base direction : Point3} :
    (Kakeya.unitSegment base direction).Nonempty :=
  ⟨base, ⟨0, by norm_num, by simp⟩⟩

/--
Every point in a nonnegative-radius tube carrier is within the tube radius of
an explicitly parametrized point on its unit segment.
-/
lemma exists_axis_point_dist_le
    {rho : ℝ} (hrho : 0 ≤ rho) (T : Kakeya.DeltaTube rho)
    {x : Point3} (hx : x ∈ T.carrier) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧
      dist x (T.base + t • T.direction) ≤ rho := by
  have hinf :
      Metric.infEDist x (Kakeya.unitSegment T.base T.direction) ≤
        ENNReal.ofReal rho := hx
  rcases (isCompact_unitSegment' (base := T.base)
      (direction := T.direction)).exists_infEDist_eq_edist
      nonempty_unitSegment' x with ⟨y, hy, hinf_eq⟩
  have hedist : edist x y ≤ ENNReal.ofReal rho := by
    rw [← hinf_eq]
    exact hinf
  have hdist : dist x y ≤ rho := by
    rw [edist_dist] at hedist
    exact (ENNReal.ofReal_le_ofReal_iff hrho).mp hedist
  rcases hy with ⟨t, ht, rfl⟩
  exact ⟨t, ht, hdist⟩

/-- Every point on a tube's axis belongs to its carrier. -/
lemma axis_point_mem_carrier
    {delta : ℝ} (T : Kakeya.DeltaTube delta)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    T.base + t • T.direction ∈ T.carrier := by
  have hseg :
      T.base + t • T.direction ∈
        Kakeya.unitSegment T.base T.direction :=
    ⟨t, ht, rfl⟩
  have hzero :
      Metric.infEDist (T.base + t • T.direction)
          (Kakeya.unitSegment T.base T.direction) = 0 :=
    Metric.infEDist_zero_of_mem hseg
  rw [Kakeya.DeltaTube.carrier, Metric.mem_cthickening_iff, hzero]
  simp

/-- A tube carrier lies in the ball of radius `rho + 1/2` about its
midpoint. -/
lemma tube_carrier_subset_closedBall_midpoint
    {rho : ℝ} (hrho : 0 ≤ rho)
    (T : Kakeya.DeltaTube rho) :
    T.carrier ⊆
      Metric.closedBall (tubeMidpoint T) (rho + 1 / 2) := by
  intro x hx
  rcases exists_axis_point_dist_le hrho T hx with
    ⟨t, ht, hxt⟩
  have haxis :
      dist (T.base + t • T.direction) (tubeMidpoint T) ≤
        1 / 2 := by
    rw [dist_eq_norm]
    have heq :
        T.base + t • T.direction - tubeMidpoint T =
          (t - 1 / 2) • T.direction := by
      simp [tubeMidpoint]
      module
    rw [heq, norm_smul, T.direction_unit, mul_one,
      Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  rw [Metric.mem_closedBall]
  calc
    dist x (tubeMidpoint T)
        ≤ dist x (T.base + t • T.direction) +
            dist (T.base + t • T.direction)
              (tubeMidpoint T) :=
      dist_triangle _ _ _
    _ ≤ rho + 1 / 2 := add_le_add hxt haxis

/-- A midpoint bound gives one origin-centered ball containing the entire
tube carrier. -/
lemma tube_carrier_subset_closedBall_zero
    {rho R : ℝ} (hrho : 0 ≤ rho)
    (T : Kakeya.DeltaTube rho)
    (hmid : ‖tubeMidpoint T‖ ≤ R) :
    T.carrier ⊆
      Metric.closedBall (0 : Point3) (R + rho + 1 / 2) := by
  intro x hx
  have hxmid :=
    tube_carrier_subset_closedBall_midpoint hrho T hx
  rw [Metric.mem_closedBall] at hxmid ⊢
  have hmid0 : dist (tubeMidpoint T) 0 ≤ R := by
    simpa [dist_eq_norm] using hmid
  calc
    dist x 0
        ≤ dist x (tubeMidpoint T) +
            dist (tubeMidpoint T) 0 :=
      dist_triangle _ _ _
    _ ≤ (rho + 1 / 2) + R := add_le_add hxmid hmid0
    _ = R + rho + 1 / 2 := by ring

/--
If a fine carrier is contained in a coarse carrier, every point on the fine
axis has a parent-axis witness within the coarse radius.
-/
lemma exists_parent_axis_point_close
    {delta rho : ℝ} (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta) (coarse : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ coarse.carrier)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ s : ℝ, s ∈ Set.Icc 0 1 ∧
      dist (fine.base + t • fine.direction)
        (coarse.base + s • coarse.direction) ≤ rho := by
  have hpoint : fine.base + t • fine.direction ∈ coarse.carrier :=
    hcontained (axis_point_mem_carrier fine ht)
  exact exists_axis_point_dist_le hrho coarse hpoint

/--
The two endpoints of a fine axis have close witnesses on any containing
coarse axis.
-/
lemma exists_parent_endpoint_witnesses
    {delta rho : ℝ} (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta) (coarse : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ coarse.carrier) :
    ∃ s0 s1 : ℝ,
      s0 ∈ Set.Icc 0 1 ∧ s1 ∈ Set.Icc 0 1 ∧
      dist fine.base (coarse.base + s0 • coarse.direction) ≤ rho ∧
      dist (fine.base + fine.direction)
        (coarse.base + s1 • coarse.direction) ≤ rho := by
  rcases exists_parent_axis_point_close hrho fine coarse hcontained
      (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num) with
    ⟨s0, hs0, h0⟩
  rcases exists_parent_axis_point_close hrho fine coarse hcontained
      (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) with
    ⟨s1, hs1, h1⟩
  refine ⟨s0, s1, hs0, hs1, ?_, ?_⟩
  · simpa using h0
  · simpa using h1

/--
Containment of a fine tube in a parent forces the two unit directions to be
`4 * rho`-close up to orientation reversal.
-/
lemma fine_parent_direction_close_or_reverse
    {delta rho : ℝ} (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta) (coarse : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ coarse.carrier) :
    ‖fine.direction - coarse.direction‖ ≤ 4 * rho ∨
      ‖fine.direction + coarse.direction‖ ≤ 4 * rho := by
  rcases exists_parent_endpoint_witnesses hrho fine coarse hcontained with
    ⟨s0, s1, hs0, hs1, h0, h1⟩
  change 0 ≤ s0 ∧ s0 ≤ 1 at hs0
  change 0 ≤ s1 ∧ s1 ≤ 1 at hs1
  let a : ℝ := s1 - s0
  have ha_lower : -1 ≤ a := by
    dsimp only [a]
    linarith [hs0.1, hs1.2]
  have ha_upper : a ≤ 1 := by
    dsimp only [a]
    linarith [hs0.2, hs1.1]
  have h0_norm :
      ‖fine.base - (coarse.base + s0 • coarse.direction)‖ ≤ rho := by
    simpa [dist_eq_norm] using h0
  have h1_norm :
      ‖(fine.base + fine.direction) -
          (coarse.base + s1 • coarse.direction)‖ ≤ rho := by
    simpa [dist_eq_norm] using h1
  have hclose :
      ‖fine.direction - a • coarse.direction‖ ≤ 2 * rho := by
    have heq :
        fine.direction - a • coarse.direction =
          ((fine.base + fine.direction) -
              (coarse.base + s1 • coarse.direction)) -
            (fine.base - (coarse.base + s0 • coarse.direction)) := by
      dsimp only [a]
      module
    rw [heq]
    calc
      ‖((fine.base + fine.direction) -
            (coarse.base + s1 • coarse.direction)) -
          (fine.base - (coarse.base + s0 • coarse.direction))‖
          ≤ ‖(fine.base + fine.direction) -
              (coarse.base + s1 • coarse.direction)‖ +
            ‖fine.base - (coarse.base + s0 • coarse.direction)‖ :=
        norm_sub_le _ _
      _ ≤ rho + rho := add_le_add h1_norm h0_norm
      _ = 2 * rho := by ring
  have hnorm_gap : 1 - |a| ≤ 2 * rho := by
    have h := norm_sub_norm_le fine.direction
      (a • coarse.direction)
    rw [fine.direction_unit, norm_smul, coarse.direction_unit,
      mul_one, Real.norm_eq_abs] at h
    exact h.trans hclose
  by_cases ha : 0 ≤ a
  · left
    have habs : |a| = a := abs_of_nonneg ha
    have hdeficit : 1 - a ≤ 2 * rho := by
      rw [habs] at hnorm_gap
      exact hnorm_gap
    have hscaled :
        ‖a • coarse.direction - coarse.direction‖ = 1 - a := by
      have heq :
          a • coarse.direction - coarse.direction =
            (a - 1) • coarse.direction := by
        module
      rw [heq, norm_smul, coarse.direction_unit, mul_one,
        Real.norm_eq_abs, abs_of_nonpos]
      · ring
      · linarith
    have heq :
        fine.direction - coarse.direction =
          (fine.direction - a • coarse.direction) +
            (a • coarse.direction - coarse.direction) := by
      module
    rw [heq]
    calc
      ‖(fine.direction - a • coarse.direction) +
          (a • coarse.direction - coarse.direction)‖
          ≤ ‖fine.direction - a • coarse.direction‖ +
            ‖a • coarse.direction - coarse.direction‖ :=
        norm_add_le _ _
      _ ≤ 2 * rho + (1 - a) := add_le_add hclose hscaled.le
      _ ≤ 4 * rho := by linarith
  · right
    have ha_nonpos : a ≤ 0 := le_of_not_ge ha
    have habs : |a| = -a := abs_of_nonpos ha_nonpos
    have hdeficit : 1 + a ≤ 2 * rho := by
      rw [habs] at hnorm_gap
      have h : 1 - -a = 1 + a := by ring
      rw [h] at hnorm_gap
      exact hnorm_gap
    have hscaled :
        ‖a • coarse.direction - (-coarse.direction)‖ = 1 + a := by
      have heq :
          a • coarse.direction - (-coarse.direction) =
            (a + 1) • coarse.direction := by
        module
      have ha_plus_one : 0 ≤ a + 1 := by linarith [ha_lower]
      rw [heq, norm_smul, coarse.direction_unit, mul_one,
        Real.norm_eq_abs, abs_of_nonneg ha_plus_one]
      ring
    have heq :
        fine.direction + coarse.direction =
          (fine.direction - a • coarse.direction) +
            (a • coarse.direction - (-coarse.direction)) := by
      module
    rw [heq]
    calc
      ‖(fine.direction - a • coarse.direction) +
          (a • coarse.direction - -coarse.direction)‖
          ≤ ‖fine.direction - a • coarse.direction‖ +
            ‖a • coarse.direction - -coarse.direction‖ :=
        norm_add_le _ _
      _ ≤ 2 * rho + (1 + a) := add_le_add hclose hscaled.le
      _ ≤ 4 * rho := by linarith

/--
After possibly reversing the parent orientation, its carrier and midpoint are
unchanged and its direction is `4 * rho`-close to the fine direction.
-/
lemma exists_oriented_parent_direction_close
    {delta rho : ℝ} (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta) (coarse : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ coarse.carrier) :
    ∃ parent : Kakeya.DeltaTube rho,
      parent.carrier = coarse.carrier ∧
      tubeMidpoint parent = tubeMidpoint coarse ∧
      (∀ A : ℝ,
        dilatedTubeCarrier A parent =
          dilatedTubeCarrier A coarse) ∧
      ‖fine.direction - parent.direction‖ ≤ 4 * rho := by
  rcases fine_parent_direction_close_or_reverse hrho fine coarse hcontained with
    hsame | hreversed
  · exact ⟨coarse, rfl, rfl, fun _ => rfl, hsame⟩
  · refine ⟨reverseTube coarse, reverseTube_carrier coarse,
      reverseTube_midpoint coarse,
      (fun A => reverseTube_dilatedCarrier (A := A) coarse), ?_⟩
    simpa [reverseTube] using hreversed

/--
A parent of a unit-ball fine tube has midpoint norm at most `3`, independently
of the parent orientation.
-/
lemma parent_midpoint_norm_le_three
    {delta rho : ℝ} (hrho : 0 ≤ rho) (hrho_one : rho ≤ 1)
    (fine : Kakeya.DeltaTube delta) (coarse : Kakeya.DeltaTube rho)
    (hfine_ball : fine.IsInUnitBall)
    (hcontained : fine.carrier ⊆ coarse.carrier) :
    ‖tubeMidpoint coarse‖ ≤ 3 := by
  have hmid_fine : tubeMidpoint fine ∈ fine.carrier :=
    tubeMidpoint_mem_carrier fine
  have hmid_parent : tubeMidpoint fine ∈ coarse.carrier :=
    hcontained hmid_fine
  have hnorm_fine : ‖tubeMidpoint fine‖ ≤ 1 := by
    have hball := hfine_ball hmid_fine
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall,
      dist_eq_norm] using hball
  exact tubeMidpoint_bound_of_unitBall_point hrho hrho_one
    coarse (tubeMidpoint fine) hmid_parent hnorm_fine

/--
After possibly reversing the parent orientation, there are endpoint witnesses
whose parameter gap covers all but `2 * rho` of `[0, 1]`.
-/
lemma exists_oriented_parent_with_good_witnesses
    {delta rho : ℝ} (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta) (coarse : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ coarse.carrier) :
    ∃ (parent' : Kakeya.DeltaTube rho) (s0 s1 : ℝ),
      parent'.carrier = coarse.carrier ∧
      s0 ∈ Set.Icc 0 1 ∧ s1 ∈ Set.Icc 0 1 ∧
      dist fine.base (parent'.base + s0 • parent'.direction) ≤ rho ∧
      dist (fine.base + fine.direction)
        (parent'.base + s1 • parent'.direction) ≤ rho ∧
      s1 - s0 ≥ 1 - 2 * rho := by
  rcases exists_parent_endpoint_witnesses hrho fine coarse hcontained with
    ⟨s0, s1, hs0, hs1, h0, h1⟩
  let a : ℝ := s1 - s0
  have h0_norm :
      ‖fine.base - (coarse.base + s0 • coarse.direction)‖ ≤ rho := by
    simpa [dist_eq_norm] using h0
  have h1_norm :
      ‖(fine.base + fine.direction) -
          (coarse.base + s1 • coarse.direction)‖ ≤ rho := by
    simpa [dist_eq_norm] using h1
  have hclose : ‖fine.direction - a • coarse.direction‖ ≤ 2 * rho := by
    have heq :
        fine.direction - a • coarse.direction =
          ((fine.base + fine.direction) -
              (coarse.base + s1 • coarse.direction)) -
            (fine.base - (coarse.base + s0 • coarse.direction)) := by
      dsimp only [a]
      module
    rw [heq]
    calc
      _ ≤ ‖(fine.base + fine.direction) -
              (coarse.base + s1 • coarse.direction)‖ +
            ‖fine.base - (coarse.base + s0 • coarse.direction)‖ :=
        norm_sub_le _ _
      _ ≤ rho + rho := add_le_add h1_norm h0_norm
      _ = 2 * rho := by ring
  have hnorm_gap : 1 - |a| ≤ 2 * rho := by
    have h := norm_sub_norm_le fine.direction (a • coarse.direction)
    rw [fine.direction_unit, norm_smul, coarse.direction_unit,
      mul_one, Real.norm_eq_abs] at h
    exact h.trans hclose
  by_cases ha : 0 ≤ a
  · have hgap : s1 - s0 ≥ 1 - 2 * rho := by
      have habs : |a| = a := abs_of_nonneg ha
      rw [habs] at hnorm_gap
      dsimp only [a] at *
      linarith
    exact ⟨coarse, s0, s1, rfl, hs0, hs1, h0, h1, hgap⟩
  · have ha_neg : a < 0 := by linarith
    have habs : |a| = -a := abs_of_neg ha_neg
    have hgap_neg : -a ≥ 1 - 2 * rho := by
      rw [habs] at hnorm_gap
      dsimp only [a] at *
      linarith
    let parent' := reverseTube coarse
    let s0' := 1 - s0
    let s1' := 1 - s1
    have hs0' : s0' ∈ Set.Icc 0 1 := by
      dsimp only [s0']
      exact ⟨by linarith [hs0.2], by linarith [hs0.1]⟩
    have hs1' : s1' ∈ Set.Icc 0 1 := by
      dsimp only [s1']
      exact ⟨by linarith [hs1.2], by linarith [hs1.1]⟩
    have hcarrier : parent'.carrier = coarse.carrier :=
      reverseTube_carrier coarse
    have hpoint0 :
        parent'.base + s0' • parent'.direction =
          coarse.base + s0 • coarse.direction := by
      simp [parent', reverseTube, s0']
      module
    have hpoint1 :
        parent'.base + s1' • parent'.direction =
          coarse.base + s1 • coarse.direction := by
      simp [parent', reverseTube, s1']
      module
    have h0' :
        dist fine.base
            (parent'.base + s0' • parent'.direction) ≤ rho := by
      rw [hpoint0]
      exact h0
    have h1' :
        dist (fine.base + fine.direction)
            (parent'.base + s1' • parent'.direction) ≤ rho := by
      rw [hpoint1]
      exact h1
    have hgap' : s1' - s0' ≥ 1 - 2 * rho := by
      dsimp only [s1', s0', a] at *
      linarith
    exact ⟨parent', s0', s1', hcarrier, hs0', hs1', h0', h1', hgap'⟩

end Kakeya.Streamlined.GeometricLemmas

import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverGeometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedCommonChildGeometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover

/-!
# Fixed-ball geometric lemmas

Generalizations of key geometric lemmas from unit-ball support to support in a
fixed ball of radius `R ≥ 1`.  These are used by the fixed-ball
`deltaMax` product theorem.

## Main results

- `dilated_parent_midpoint_norm_le_R`: midpoint norm bound with radius-R support.
- `common_child_parent_containment_R`: cross-parent containment with radius-R support.
- `coarse_tube_in_ball_R`: coarse tube carrier lies in a fixed-radius ball.
- `dilated_coarse_tube_in_ball_R`: D-dilated coarse tube lies in a fixed-radius ball.
-/

noncomputable section

open Metric

namespace Kakeya.Streamlined.GeometricLemmas

/--
The midpoint of an `A`-dilated parent of a fine tube supported in the ball of
radius `R` has norm at most `R + 3*A/2`.
-/
lemma dilated_parent_midpoint_norm_le_R
    {delta rho A R : ℝ} (hA : 0 < A)
    (hrho : 0 ≤ rho) (hrho_one : rho ≤ 1)
    (_hR : 0 ≤ R)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (hfine_ball_R : fine.carrier ⊆ Metric.closedBall (0 : Point3) R)
    (hcontained : fine.carrier ⊆ dilatedTubeCarrier A parent) :
    ‖tubeMidpoint parent‖ ≤ R + 3 * A / 2 := by
  let x := tubeMidpoint fine
  have hx_fine : x ∈ fine.carrier :=
    tubeMidpoint_mem_carrier fine
  have hx_parent : x ∈ dilatedTubeCarrier A parent :=
    hcontained hx_fine
  rcases exists_extended_axis_point_dist_le hA hrho parent hx_parent with
    ⟨s, hs, hdist⟩
  let p := tubeMidpoint parent + s • parent.direction
  have hx_norm : ‖x‖ ≤ R := by
    have hball : x ∈ Metric.closedBall (0 : Point3) R := hfine_ball_R hx_fine
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
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
    _ ≤ A / 2 + (A * rho + R) := by
      have hmid_le :
          dist (tubeMidpoint parent) p ≤ A / 2 := by
        rw [hmid_p]
        exact hs
      have hx_zero : dist x 0 ≤ R := by
        simpa [dist_eq_norm] using hx_norm
      exact add_le_add hmid_le (add_le_add hp_x hx_zero)
    _ ≤ R + 3 * A / 2 := by
      have hArho : A * rho ≤ A := by
        simpa using mul_le_mul_of_nonneg_left hrho_one hA.le
      nlinarith

/--
Dilation factor sufficient for cross-parent containment when the fine family
is supported in a ball of radius `R`.
-/
def fixedBallParentDilation (A R : ℝ) : ℝ :=
  4 * (A ^ 2 + R) + 6 * A + 1

/--
If one fine tube supported in the ball of radius `R` lies in the `A`-dilations
of two parents and the first parent radius is no larger than the second, then
the first carrier lies in the `fixedBallParentDilation A R` dilation of
the second.
-/
lemma common_child_parent_containment_R
    {delta rho sigma A R : ℝ} (hA : 1 ≤ A)
    (hrho_pos : 0 < rho) (hsigma_one : sigma ≤ 1)
    (hrs : rho ≤ sigma)
    (hR : 0 ≤ R)
    (fine : Kakeya.DeltaTube delta)
    (hfine_ball_R : fine.carrier ⊆ Metric.closedBall (0 : Point3) R)
    (parentR : Kakeya.DeltaTube rho)
    (parentS : Kakeya.DeltaTube sigma)
    (hfine_r :
      fine.carrier ⊆ dilatedTubeCarrier A parentR)
    (hfine_s :
      fine.carrier ⊆ dilatedTubeCarrier A parentS) :
    parentR.carrier ⊆
      dilatedTubeCarrier (fixedBallParentDilation A R)
        parentS := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hsigma_pos : 0 < sigma := lt_of_lt_of_le hrho_pos hrs
  have hrho_nonneg : 0 ≤ rho := hrho_pos.le
  have hsigma_nonneg : 0 ≤ sigma := hsigma_pos.le
  have hrho_one : rho ≤ 1 := hrs.trans hsigma_one

  rcases exists_oriented_dilated_parent_direction_close
      hA_pos hrho_nonneg fine parentR hfine_r with
    ⟨orientedR, hRCarrier, hRMidpoint, hRDilation, hRDirection⟩
  rcases exists_oriented_dilated_parent_direction_close
      hA_pos hsigma_nonneg fine parentS hfine_s with
    ⟨orientedS, hSCarrier, hSMidpoint, hSDilation, hSDirection⟩

  have h_direction :
      ‖orientedR.direction - orientedS.direction‖ ≤
        8 * A * sigma := by
    have hR :
        ‖orientedR.direction - fine.direction‖ ≤ 4 * A * rho := by
      simpa [norm_sub_rev] using hRDirection
    calc
      ‖orientedR.direction - orientedS.direction‖
          ≤ ‖orientedR.direction - fine.direction‖ +
            ‖fine.direction - orientedS.direction‖ := by
          have h := norm_add_le
            (orientedR.direction - fine.direction)
            (fine.direction - orientedS.direction)
          simpa only [sub_add_sub_cancel] using h
      _ ≤ 4 * A * rho + 4 * A * sigma :=
        add_le_add hR hSDirection
      _ ≤ 8 * A * sigma := by
        nlinarith [mul_le_mul_of_nonneg_left hrs hA_pos.le]

  have h_direction_transverse :
      ‖orientedR.direction -
          inner ℝ orientedR.direction orientedS.direction •
            orientedS.direction‖ ≤
        8 * A * sigma := by
    have h_inner_self :
        inner ℝ orientedS.direction orientedS.direction = 1 := by
      have h :=
        real_inner_self_eq_norm_sq orientedS.direction
      rw [orientedS.direction_unit] at h
      norm_num at h ⊢
      exact h
    have heq :
        orientedR.direction -
            inner ℝ orientedR.direction orientedS.direction •
              orientedS.direction =
          (orientedR.direction - orientedS.direction) -
            inner ℝ
              (orientedR.direction - orientedS.direction)
              orientedS.direction • orientedS.direction := by
      rw [inner_sub_left, h_inner_self]
      module
    rw [heq]
    exact (norm_transverse_le orientedS.direction_unit
      (orientedR.direction - orientedS.direction)).trans h_direction

  let Cmid : ℝ := R + 3 * A / 2
  have hmid_r : ‖tubeMidpoint orientedR‖ ≤ Cmid := by
    have h := dilated_parent_midpoint_norm_le_R hA_pos
      hrho_nonneg hrho_one hR fine parentR hfine_ball_R hfine_r
    simpa [Cmid, hRMidpoint] using h
  have hmid_s : ‖tubeMidpoint orientedS‖ ≤ Cmid := by
    have h := dilated_parent_midpoint_norm_le_R hA_pos
      hsigma_nonneg hsigma_one hR fine parentS hfine_ball_R hfine_s
    simpa [Cmid, hSMidpoint] using h
  have hCmid : 0 ≤ Cmid := by
    dsimp only [Cmid]
    positivity

  let x := tubeMidpoint fine
  have hx_fine : x ∈ fine.carrier :=
    tubeMidpoint_mem_carrier fine
  have hx_r : x ∈ dilatedTubeCarrier A orientedR := by
    rw [hRDilation A]
    exact hfine_r hx_fine
  have hx_s : x ∈ dilatedTubeCarrier A orientedS := by
    rw [hSDilation A]
    exact hfine_s hx_fine
  rcases exists_extended_axis_point_dist_le
      hA_pos hrho_nonneg orientedR hx_r with
    ⟨a, ha, hxa⟩
  rcases exists_extended_axis_point_dist_le
      hA_pos hsigma_nonneg orientedS hx_s with
    ⟨b, hb, hxb⟩
  let pR := tubeMidpoint orientedR + a • orientedR.direction
  let pS := tubeMidpoint orientedS + b • orientedS.direction
  have hpR_pS : ‖pR - pS‖ ≤ 2 * A * sigma := by
    have hdist :
        dist pR pS ≤ dist pR x + dist x pS :=
      dist_triangle _ _ _
    have hdist_r : dist pR x ≤ A * rho := by
      simpa [pR, dist_comm] using hxa
    have hdist_s : dist x pS ≤ A * sigma := by
      simpa [pS] using hxb
    rw [dist_eq_norm] at hdist
    calc
      ‖pR - pS‖ ≤ dist pR x + dist x pS := hdist
      _ ≤ A * rho + A * sigma :=
        add_le_add hdist_r hdist_s
      _ ≤ 2 * A * sigma := by
        nlinarith [mul_le_mul_of_nonneg_left hrs hA_pos.le]

  have hmid_transverse :
      ‖(tubeMidpoint orientedR - tubeMidpoint orientedS) -
          inner ℝ
            (tubeMidpoint orientedR - tubeMidpoint orientedS)
            orientedS.direction • orientedS.direction‖ ≤
        2 * A * sigma +
          (A / 2) *
            ‖orientedR.direction -
                inner ℝ orientedR.direction orientedS.direction •
                  orientedS.direction‖ := by
    have h_inner_self :
        inner ℝ orientedS.direction orientedS.direction = 1 := by
      rw [real_inner_self_eq_norm_sq,
        orientedS.direction_unit]
      norm_num
    have h_inner_p :
        inner ℝ (pR - pS) orientedS.direction =
          inner ℝ
              (tubeMidpoint orientedR - tubeMidpoint orientedS)
              orientedS.direction +
            a * inner ℝ orientedR.direction orientedS.direction - b := by
      dsimp only [pR, pS]
      simp only [inner_sub_left, inner_add_left, inner_smul_left,
        h_inner_self, starRingEnd_apply, star_trivial]
      ring
    have heq :
        (tubeMidpoint orientedR - tubeMidpoint orientedS) -
            inner ℝ
              (tubeMidpoint orientedR - tubeMidpoint orientedS)
              orientedS.direction • orientedS.direction =
          ((pR - pS) -
              inner ℝ (pR - pS) orientedS.direction •
                orientedS.direction) -
            a •
              (orientedR.direction -
                inner ℝ orientedR.direction orientedS.direction •
                  orientedS.direction) := by
      rw [h_inner_p, inner_sub_left]
      dsimp only [pR, pS]
      module
    rw [heq]
    calc
      ‖((pR - pS) -
            inner ℝ (pR - pS) orientedS.direction •
              orientedS.direction) -
          a •
            (orientedR.direction -
              inner ℝ orientedR.direction orientedS.direction •
                orientedS.direction)‖
          ≤ ‖(pR - pS) -
              inner ℝ (pR - pS) orientedS.direction •
                orientedS.direction‖ +
            ‖a •
              (orientedR.direction -
                inner ℝ orientedR.direction orientedS.direction •
                  orientedS.direction)‖ :=
        norm_sub_le _ _
      _ ≤ ‖pR - pS‖ +
          |a| *
            ‖orientedR.direction -
              inner ℝ orientedR.direction orientedS.direction •
                orientedS.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact norm_transverse_le orientedS.direction_unit _
      _ ≤ 2 * A * sigma +
          (A / 2) *
            ‖orientedR.direction -
              inner ℝ orientedR.direction orientedS.direction •
                orientedS.direction‖ := by
        gcongr

  let D := fixedBallParentDilation A R
  have hDlarge : 4 * Cmid + 1 ≤ D := by
    dsimp only [D, Cmid, fixedBallParentDilation]
    nlinarith [sq_nonneg A, hR]
  have htrans :
      ‖(tubeMidpoint (withRadius sigma orientedR) -
          tubeMidpoint orientedS) -
          inner ℝ
            (tubeMidpoint (withRadius sigma orientedR) -
              tubeMidpoint orientedS)
            orientedS.direction • orientedS.direction‖ +
        (1 / 2 : ℝ) *
          ‖(withRadius sigma orientedR).direction -
            inner ℝ (withRadius sigma orientedR).direction
              orientedS.direction • orientedS.direction‖ ≤
        (D - 1) * sigma := by
    rw [withRadius_midpoint, withRadius_direction]
    calc
      ‖(tubeMidpoint orientedR - tubeMidpoint orientedS) -
          inner ℝ (tubeMidpoint orientedR - tubeMidpoint orientedS)
            orientedS.direction • orientedS.direction‖ +
          (1 / 2 : ℝ) *
            ‖orientedR.direction -
              inner ℝ orientedR.direction orientedS.direction •
                orientedS.direction‖
          ≤ (2 * A * sigma +
              (A / 2) *
                ‖orientedR.direction -
                  inner ℝ orientedR.direction orientedS.direction •
                    orientedS.direction‖) +
            (1 / 2 : ℝ) *
              ‖orientedR.direction -
                inner ℝ orientedR.direction orientedS.direction •
                  orientedS.direction‖ := by
          exact add_le_add hmid_transverse le_rfl
      _ ≤ (2 * A * sigma + (A / 2) * (8 * A * sigma)) +
          (1 / 2 : ℝ) * (8 * A * sigma) := by
        gcongr
      _ ≤ (D - 1) * sigma := by
        dsimp only [D, fixedBallParentDilation]
        have hR_nonneg : 0 ≤ R := hR
        have hsigma_nonneg' : 0 ≤ sigma := hsigma_nonneg
        nlinarith

  have hlifted :
      (withRadius sigma orientedR).carrier ⊆
        dilatedTubeCarrier D orientedS :=
    tube_contained_in_dilated_transverse_general
      hsigma_pos hsigma_one D Cmid hDlarge hCmid
      (withRadius sigma orientedR) orientedS
      (by simpa using hmid_r) hmid_s htrans
  intro y hy
  have hy_oriented : y ∈ orientedR.carrier := by
    rw [hRCarrier]
    exact hy
  have hy_lifted :
      y ∈ (withRadius sigma orientedR).carrier :=
    carrier_subset_withRadius hrs orientedR hy_oriented
  have hy_out : y ∈ dilatedTubeCarrier D orientedS :=
    hlifted hy_lifted
  rw [hSDilation D] at hy_out
  exact hy_out

/--
For a plain `DilatedTubeCover` with fine family supported in the ball of
radius `R`, every coarse tube carrier is contained in a ball of radius
`R + 2*A + 1`.
-/
lemma coarse_tube_in_ball_R
    {delta rho A R : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (hA : 1 ≤ A) (hrho_pos : 0 < rho) (hrho_one : rho ≤ 1)
    (hR : 0 ≤ R)
    (hfine_ball_R : ∀ i, (fine.tube i).carrier ⊆ Metric.closedBall (0 : Point3) R)
    (C : DilatedTubeCover A fine coarse)
    {j : Fin coarse.card} :
    (coarse.tube j).carrier ⊆
      Metric.closedBall (0 : Point3) (R + 2 * A + 1) := by
  rcases C.parent_surjective j with ⟨i, hi⟩
  let T := coarse.tube j
  have hcontained : (fine.tube i).carrier ⊆ dilatedTubeCarrier A T := by
    have h : (fine.tube i).carrier ⊆ dilatedTubeCarrier A (coarse.tube (C.parent i)) := C.nested i
    have h' : C.parent i = j := hi
    rw [h'] at h
    exact h
  have hmid : ‖tubeMidpoint T‖ ≤ R + 3 * A / 2 :=
    dilated_parent_midpoint_norm_le_R
      (lt_of_lt_of_le zero_lt_one hA) hrho_pos.le hrho_one hR
      (fine.tube i) T (hfine_ball_R i) hcontained
  have hball : T.carrier ⊆ Metric.closedBall (0 : Point3)
      ((R + 3 * A / 2) + rho + 1 / 2) :=
    tube_carrier_subset_closedBall_zero hrho_pos.le T hmid
  have hbound : (R + 3 * A / 2) + rho + 1 / 2 ≤ R + 2 * A + 1 := by
    linarith [hrho_one, hA]
  exact hball.trans (Metric.closedBall_subset_closedBall hbound)

/--
For a plain `DilatedTubeCover` with fine family supported in the ball of
radius `R`, the `D`-dilation of every coarse tube carrier is contained in a
ball of radius `(R + 2*A + 1) * (1 + 4*D)`.
-/
lemma dilated_coarse_tube_in_ball_R
    {delta rho A R D : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (hA : 1 ≤ A) (hrho_pos : 0 < rho) (hrho_one : rho ≤ 1)
    (hR : 0 ≤ R) (hD : 0 < D)
    (hfine_ball_R : ∀ i, (fine.tube i).carrier ⊆ Metric.closedBall (0 : Point3) R)
    (C : DilatedTubeCover A fine coarse)
    {j : Fin coarse.card} :
    dilatedTubeCarrier D (coarse.tube j) ⊆
      Metric.closedBall (0 : Point3) ((R + 2 * A + 1) * (1 + 4 * D)) := by
  rcases C.parent_surjective j with ⟨i, hi⟩
  let T := coarse.tube j
  have hcontained : (fine.tube i).carrier ⊆ dilatedTubeCarrier A T := by
    have h : (fine.tube i).carrier ⊆ dilatedTubeCarrier A (coarse.tube (C.parent i)) := C.nested i
    have h' : C.parent i = j := hi
    rw [h'] at h
    exact h
  have hmid : ‖tubeMidpoint T‖ ≤ R + 3 * A / 2 :=
    dilated_parent_midpoint_norm_le_R
      (lt_of_lt_of_le zero_lt_one hA) hrho_pos.le hrho_one hR
      (fine.tube i) T (hfine_ball_R i) hcontained
  let midpoint := tubeMidpoint T
  have hcarrier : T.carrier ⊆ Metric.closedBall (0 : Point3)
      ((R + 3 * A / 2) + rho + 1 / 2) :=
    tube_carrier_subset_closedBall_zero hrho_pos.le T hmid
  have hbound1 : (R + 3 * A / 2) + rho + 1 / 2 ≤ R + 2 * A + 1 := by
    linarith [hrho_one, hA]
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx_norm : ‖x‖ ≤ R + 2 * A + 1 := by
    have h : ‖x‖ ≤ (R + 3 * A / 2) + rho + 1 / 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hcarrier hx
    exact h.trans hbound1
  have hmid_norm : ‖midpoint‖ ≤ R + 3 * A / 2 := hmid
  have hmid_bound : ‖midpoint‖ ≤ R + 2 * A + 1 := by
    linarith [hA]
  have h1 : AffineMap.homothety midpoint D x = D • (x - midpoint) + midpoint :=
    AffineMap.homothety_apply midpoint D x
  have h_main : ‖AffineMap.homothety midpoint D x‖ ≤
      (R + 2 * A + 1) + D * ((R + 2 * A + 1) + (R + 2 * A + 1)) := by
    rw [h1]
    have h_comm : D • (x - midpoint) + midpoint = midpoint + D • (x - midpoint) := by abel
    rw [h_comm]
    have hns : ‖D • (x - midpoint)‖ = |D| * ‖x - midpoint‖ := by
      simpa [Real.norm_eq_abs] using norm_smul D (x - midpoint)
    have hD_abs : |D| = D := abs_of_pos hD
    calc
      ‖midpoint + D • (x - midpoint)‖
        ≤ ‖midpoint‖ + ‖D • (x - midpoint)‖ := norm_add_le _ _
      _ = ‖midpoint‖ + |D| * ‖x - midpoint‖ := by rw [hns]
      _ = ‖midpoint‖ + D * ‖x - midpoint‖ := by rw [hD_abs]
      _ ≤ ‖midpoint‖ + D * (‖x‖ + ‖midpoint‖) := by
          gcongr; exact norm_sub_le x midpoint
      _ ≤ (R + 2 * A + 1) + D * ((R + 2 * A + 1) + (R + 2 * A + 1)) := by
          gcongr
  have h_final : (R + 2 * A + 1) + D * ((R + 2 * A + 1) + (R + 2 * A + 1)) ≤
      (R + 2 * A + 1) * (1 + 4 * D) := by
    have h_pos : 0 < R + 2 * A + 1 := by linarith [hA, hR]
    have h_eq : (R + 2 * A + 1) + D * ((R + 2 * A + 1) + (R + 2 * A + 1)) =
        (R + 2 * A + 1) * (1 + 2 * D) := by ring
    rw [h_eq]
    gcongr
    ; norm_num
  have h_goal : ‖(AffineMap.homothety midpoint D) x‖ ≤
      (R + 2 * A + 1) * (1 + 4 * D) :=
    h_main.trans h_final
  have h_dist : dist ((AffineMap.homothety midpoint D) x) 0 ≤
      (R + 2 * A + 1) * (1 + 4 * D) := by
    rw [dist_zero_right]; exact h_goal
  exact h_dist

end Kakeya.Streamlined.GeometricLemmas

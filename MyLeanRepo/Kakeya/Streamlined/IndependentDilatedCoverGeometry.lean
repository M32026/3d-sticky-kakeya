import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverRelations
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedCommonChildGeometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius

/-!
# Geometry of independent dilated paper-grid covers

This is the cross-scale geometry compatible with the validated Section 2
refinement.  If two coarse tubes are parents of one fine tube only after the
fixed cover dilation `A`, the smaller parent still lies in one explicit
dilation of the larger parent.
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

/-- Universal parent-to-parent dilation induced by a cover dilation `A`. -/
def independentCoverParentDilation (A : ℝ) : ℝ :=
  4 * A ^ 2 + 6 * A + 1

namespace DilatedDiscreteUniformTubeStructure

/--
If one unit-ball fine tube lies in the `A`-dilations of two parents and the
first parent radius is no larger than the second, then the first carrier lies
in the `independentCoverParentDilation A` dilation of the second.
-/
theorem common_child_parent_containment
    {delta rho sigma A : ℝ} (hA : 1 ≤ A)
    (hrho_pos : 0 < rho) (hsigma_one : sigma ≤ 1)
    (hrs : rho ≤ sigma)
    (fine : Kakeya.DeltaTube delta)
    (hfine_ball : fine.IsInUnitBall)
    (parentR : Kakeya.DeltaTube rho)
    (parentS : Kakeya.DeltaTube sigma)
    (hfine_r :
      fine.carrier ⊆ dilatedTubeCarrier A parentR)
    (hfine_s :
      fine.carrier ⊆ dilatedTubeCarrier A parentS) :
    parentR.carrier ⊆
      dilatedTubeCarrier (independentCoverParentDilation A)
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

  let Cmid : ℝ := 1 + 3 * A / 2
  have hmid_r : ‖tubeMidpoint orientedR‖ ≤ Cmid := by
    have h := dilated_parent_midpoint_norm_le hA_pos
      hrho_nonneg hrho_one fine parentR hfine_ball hfine_r
    simpa [Cmid, hRMidpoint] using h
  have hmid_s : ‖tubeMidpoint orientedS‖ ≤ Cmid := by
    have h := dilated_parent_midpoint_norm_le hA_pos
      hsigma_nonneg hsigma_one fine parentS hfine_ball hfine_s
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
        h_inner_self, map_star, starRingEnd_apply, star_trivial]
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

  let D := independentCoverParentDilation A
  have hDlarge : 4 * Cmid + 1 ≤ D := by
    dsimp only [D, Cmid, independentCoverParentDilation]
    nlinarith [sq_nonneg (A - 1)]
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
      _ = (D - 1) * sigma := by
        dsimp only [D, independentCoverParentDilation]
        ring

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
If two parents in independent paper-grid covers share an assigned fine child
and the first radius is no larger than the second, then the first carrier lies
in the universal dilation of the second.
-/
theorem related_parent_containment
    {delta A : ℝ} (hA : 1 ≤ A) (hdelta : 0 < delta)
    {F : TubeFamily delta} (hF_ball : F.IsInUnitBall)
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (j : Fin (U.coarse r).card)
    (k : Fin (U.coarse s).card)
    (hrel : U.ParentRelation r s j k) :
    ((U.coarse r).tube j).carrier ⊆
      dilatedTubeCarrier (independentCoverParentDilation A)
        ((U.coarse s).tube k) := by
  rcases hrel with ⟨i, hparent_r, hparent_s⟩
  have hfine_r :
      (F.tube i).carrier ⊆
        dilatedTubeCarrier A ((U.coarse r).tube j) := by
    have h := (U.cover r).nested i
    simpa [hparent_r] using h
  have hfine_s :
      (F.tube i).carrier ⊆
        dilatedTubeCarrier A ((U.coarse s).tube k) := by
    have h := (U.cover s).nested i
    simpa [hparent_s] using h
  exact common_child_parent_containment hA
    (lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1)
    (uniformScale delta hdelta_le_one s).property.2
    hrs (F.tube i) (hF_ball i)
    ((U.coarse r).tube j) ((U.coarse s).tube k)
    hfine_r hfine_s

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined

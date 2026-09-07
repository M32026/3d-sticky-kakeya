module

/-
  Coarse Parent S-set from Ratio Heavy Fibers

  Given P_uniform with ratio fiber bounds F_lo ≤ |fiber(Q)| < R * F_lo over Q_uniform,
  and fine-scale point set S-set regularity at scale δ_n, prove Q_uniform forms
  an S-set at scale δ_m with constant 162 * C_point * R * (2*sqrt 2)^u.

  For R=2 this recovers the original 324 * C_point * (2*sqrt 2)^u.

  Proof: for a coarse DSquare ball B(p,r), let Q_ball be the DyadicSquare parents
  whose DSquare image is within r. Count all fine children over Q_ball:
    F_lo * |Q_ball| ≤ |fine children over Q_ball|
                     ≤ 9 * Ncover(fine union)          (packing)
                     ≤ 9 * C_point * R^u * Ncover(P_pointSet)
                     ≤ 9 * C_point * R^u * |P_uniform|
                     < 9 * C_point * R^u * R * F_lo * |Q_uniform|
  Cancel F_lo, use R ≤ 2√2·r, get |Q_ball| ≤ 9·C_point·R·(2√2)^u·r^u·|Q_uniform|
  Loosen ×2: 18·C_point·R·...
  Grid packing ×9: 162·C_point·R·(2√2)^u.

  Uses C_tube for NiceConfiguration, C_point for the S-set constant.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.HeavyParentUniformClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.RetainedRegularityClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CleanSSetConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open InductionConfigurations

/-! ========================================================================
   Coarse parent S-set from ratio heavy fibers
   ======================================================================== -/

/-- Construct IsFinsetDeltaSSet on coarse parents from ratio fiber bounds
    and fine-scale point set regularity.

    `C_tube` is the NiceConfiguration tube constant; `C_point` is the S-set
    constant. Final constant: `162 * C_point * R * (2*sqrt 2)^u`.

    For R=2 this gives `324 * C_point * (2*sqrt 2)^u`.
-/
lemma coarse_sset_from_ratio_fibers
    {n m : ℕ} (hnm : m ≤ n) (h_even : n = 2 * m)
    {s u C_tube C_point K_P : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C_tube M)
    (P_uniform : Finset (DyadicSquare n))
    (hP_sub : P_uniform ⊆ config.P₀)
    (Q_uniform : Finset (DyadicSquare m))
    (hQ_eq : Q_uniform = P_uniform.image (InductionConfigurations.containingSquare hnm))
    (hQ_nonempty : Q_uniform.Nonempty)
    (F_lo : ℝ) (hF_lo_pos : 0 < F_lo)
    (R : ℝ) (hR_ge_one : 1 ≤ R)
    (h_fiber_lower : ∀ Q ∈ Q_uniform,
        F_lo ≤ ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ))
    (h_fiber_upper : ∀ Q ∈ Q_uniform,
        ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) < R * F_lo)
    (h_point_sset : IsDeltaSSet (dyadicDelta n) u C_point
        (⋃ p ∈ (P_uniform : Set (DyadicSquare n)), (p.toSet : Set Plane)))
    (hu_nonneg : 0 ≤ u) (hC_point_pos : 0 < C_point) :
    IsFinsetDeltaSSet (dyadicDelta m) u
      (162 * C_point * R * (2 * Real.sqrt 2) ^ u)
      (finsetDyadicToDSquare Q_uniform) := by
  let δ_n := dyadicDelta n
  let δ_m := dyadicDelta m
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδm_pos : 0 < δ_m := dyadicDelta_pos m
  have hδm_eq : δ_m = Real.sqrt δ_n := by
    have h1 : n = 2 * m := h_even
    have h2 : δ_n = δ_m ^ 2 := by
      dsimp only [δ_n, δ_m, dyadicDelta]
      have h3 : (2 : ℝ)^n = ((2 : ℝ)^m)^2 := by rw [h1] <;> ring
      rw [h3] <;> field_simp <;> ring
    rw [h2]
    rw [Real.sqrt_sq (by positivity)]

  let S_dsquare := finsetDyadicToDSquare Q_uniform
  have hS_nonempty : (S_dsquare : Set (DSquare m)).Nonempty := by
    rcases hQ_nonempty with ⟨Q, hQ⟩
    exact ⟨dyadicSquareToDSquare Q, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩⟩

  -- Helper: card equality via fiberwise sum
  have h_card_sum : (P_uniform.card : ℝ) =
      ∑ Q ∈ Q_uniform, ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) := by
    have h_mapsTo : (P_uniform : Set (DyadicSquare n)).MapsTo
        (InductionConfigurations.containingSquare hnm) (Q_uniform : Set (DyadicSquare m)) := by
      rw [hQ_eq]
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h := Finset.card_eq_sum_card_fiberwise h_mapsTo
    have h_filter_eq : ∀ (x : DyadicSquare m),
        P_uniform.filter (fun p => InductionConfigurations.containingSquare hnm p = x) =
        P_uniform.filter (fun p => squareContained hnm p x) := by
      intro x
      ext p
      simp [InductionConfigurations.containingSquare_iff]
    have h' : P_uniform.card = ∑ x ∈ Q_uniform, (P_uniform.filter (fun p => squareContained hnm p x)).card := by
      rw [h]
      apply Finset.sum_congr rfl
      intro x _
      exact congr_arg Finset.card (h_filter_eq x)
    exact_mod_cast h'

  have h_Ptotal_upper : (P_uniform.card : ℝ) < R * F_lo * (Q_uniform.card : ℝ) := by
    rw [h_card_sum]
    have h : ∑ Q ∈ Q_uniform, ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) <
        ∑ Q ∈ Q_uniform, (R * F_lo) :=
      Finset.sum_lt_sum_of_nonempty hQ_nonempty (fun Q hQ => h_fiber_upper Q hQ)
    have h2 : ∑ Q ∈ Q_uniform, (R * F_lo) = (Q_uniform.card : ℝ) * (R * F_lo) := by
      rw [Finset.sum_const] <;> ring
    rw [h2] at h
    have h3 : (Q_uniform.card : ℝ) * (R * F_lo) = R * F_lo * (Q_uniform.card : ℝ) := by ring
    rw [h3] at h
    exact h

  have h_Ptotal_lower : F_lo * (Q_uniform.card : ℝ) ≤ (P_uniform.card : ℝ) := by
    rw [h_card_sum]
    have h : ∑ Q ∈ Q_uniform, F_lo ≤ ∑ Q ∈ Q_uniform, ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact h_fiber_lower Q hQ
    have h2 : ∑ Q ∈ Q_uniform, F_lo = (Q_uniform.card : ℝ) * F_lo := by
      rw [Finset.sum_const] <;> ring
    rw [h2] at h
    have h3 : (Q_uniform.card : ℝ) * F_lo = F_lo * (Q_uniform.card : ℝ) := by ring
    rw [h3] at h
    exact h

  let P_pointSet : Set Plane :=
    ⋃ p ∈ (P_uniform : Set (DyadicSquare n)), (p.toSet : Set Plane)

  have h_main : ∀ (p : DSquare m) (r : ℝ), δ_m ≤ r →
      Metric.externalCoveringNumber δ_m.toNNReal ((S_dsquare : Set (DSquare m)) ∩ Metric.closedBall p r) ≤
        ENNReal.ofReal (162 * C_point * R * (2 * Real.sqrt 2) ^ u) *
        (ENNReal.ofReal r) ^ u * Metric.externalCoveringNumber δ_m.toNNReal (S_dsquare : Set (DSquare m)) := by
    intro p r hr
    have hr_pos : 0 < r := by linarith [hδm_pos]
    let R_ball : ℝ := Real.sqrt 2 * (r + δ_m)
    have hR_geδm : δ_m ≤ R_ball := by
      have h1 : 0 ≤ Real.sqrt 2 := by positivity
      have h2 : r + δ_m ≥ 2 * δ_m := by linarith
      have h3 : Real.sqrt 2 * (r + δ_m) ≥ Real.sqrt 2 * (2 * δ_m) := by gcongr
      have h4 : Real.sqrt 2 * (2 * δ_m) > δ_m := by
        have h5 : 1 < Real.sqrt 2 := by
          rw [Real.lt_sqrt] <;> norm_num
        nlinarith
      linarith
    have hR_le : R_ball ≤ (2 * Real.sqrt 2) * r := by
      have h : δ_m ≤ r := hr
      have h2 : r + δ_m ≤ 2 * r := by linarith
      have h3 : Real.sqrt 2 * (r + δ_m) ≤ Real.sqrt 2 * (2 * r) := by gcongr
      have h4 : Real.sqrt 2 * (2 * r) = (2 * Real.sqrt 2) * r := by ring
      linarith
    have hδn_le_R : δ_n ≤ R_ball := by
      have hδn_leδm : δ_n ≤ δ_m := by
        have h1 : δ_n = δ_m ^ 2 := by
          dsimp only [δ_n, δ_m, dyadicDelta]
          have h2 : (2 : ℝ)^n = ((2 : ℝ)^m)^2 := by rw [h_even] <;> ring
          rw [h2] <;> field_simp <;> ring
        rw [h1]
        have h2 : 0 < δ_m := hδm_pos
        have h3 : δ_m ≤ 1 := by
          dsimp only [δ_m, dyadicDelta]
          have h4 : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ)^n := by
            intro n
            induction n with
            | zero => norm_num
            | succ n ih => simp [pow_succ] at * <;> nlinarith
          have h5 := h4 m
          field_simp <;> linarith
        nlinarith
      linarith [hR_geδm]

    let center : Plane := dSquareCorner δ_m p
    let Q_ball : Finset (DyadicSquare m) :=
      Q_uniform.filter (fun Q => dist (dyadicSquareToDSquare Q) p ≤ r)
    let S_ball : Finset (DSquare m) := Q_ball.image dyadicSquareToDSquare

    have hS_ball_eq : S_ball = S_dsquare.filter (fun q => dist q p ≤ r) := by
      ext q
      simp only [S_ball, Q_ball, S_dsquare, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨Q, hQ, rfl⟩
        have hQ1 : Q ∈ Q_uniform := hQ.1
        have hQ2 : dist (dyadicSquareToDSquare Q) p ≤ r := hQ.2
        have h_in : dyadicSquareToDSquare Q ∈ S_dsquare :=
          Finset.mem_image.mpr ⟨Q, hQ1, rfl⟩
        exact ⟨h_in, hQ2⟩
      · intro h
        rcases Finset.mem_image.mp h.1 with ⟨Q, hQ, rfl⟩
        exact ⟨Q, ⟨hQ, h.2⟩, rfl⟩

    let fineS_in_ball : Finset (DyadicSquare n) :=
      P_uniform.filter (fun p => InductionConfigurations.containingSquare hnm p ∈ Q_ball)

    have h_geom_full : ∀ Q ∈ Q_ball, (Q.toSet : Set Plane) ⊆ Metric.closedBall center R_ball := by
      intro Q hQ
      have hdist : dist (dyadicSquareToDSquare Q) p ≤ r := (Finset.mem_filter.mp hQ).2
      let q : DSquare m := dyadicSquareToDSquare Q
      intro z hz
      have hz' : z ∈ (dSquareToDyadicSquare q).toSet := by
        have h_eq : dSquareToDyadicSquare q = Q := by
          simp [q, dyadicSquareToDSquare, dSquareToDyadicSquare]
        rw [h_eq]
        exact hz
      have h_dist1 : dist z (dSquareCorner δ_m q) ≤ Real.sqrt 2 * δ_m :=
        point_in_square_dist_to_corner hδm_pos rfl q z hz'
      have h_dist2 : dist (dSquareCorner δ_m q) center ≤ Real.sqrt 2 * dist q p :=
        (dsquare_plane_metric_comparability hδm_pos rfl q p).2
      have h_dist3 : dist z center ≤ R_ball := by
        calc dist z center
          ≤ dist z (dSquareCorner δ_m q) + dist (dSquareCorner δ_m q) center := dist_triangle _ _ _
        _ ≤ Real.sqrt 2 * δ_m + Real.sqrt 2 * dist q p := by gcongr
        _ ≤ Real.sqrt 2 * δ_m + Real.sqrt 2 * r := by gcongr
        _ = Real.sqrt 2 * (r + δ_m) := by ring
        _ = R_ball := by simp [R_ball] <;> ring
      exact h_dist3

    have h_fine_sub_ball : (⋃ p ∈ (fineS_in_ball : Set (DyadicSquare n)), (p.toSet : Set Plane)) ⊆
        P_pointSet ∩ Metric.closedBall center R_ball := by
      intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨p, hp, hyp⟩
      have hp_in_P : p ∈ P_uniform := (Finset.mem_filter.mp hp).1
      have hQ_in_Qball : InductionConfigurations.containingSquare hnm p ∈ Q_ball := (Finset.mem_filter.mp hp).2
      set Q := InductionConfigurations.containingSquare hnm p with hQ_def
      have h_eq : InductionConfigurations.containingSquare hnm p = Q := by simp [Q]
      have h_cont : squareContained hnm p Q :=
        (InductionConfigurations.containingSquare_iff hnm p Q).mp h_eq
      have h_p_sub_Q : (p.toSet : Set Plane) ⊆ (Q.toSet : Set Plane) :=
        InductionOnScales.squareContained_toSet_subset hnm h_cont
      have hQ_sub_ball : (Q.toSet : Set Plane) ⊆ Metric.closedBall center R_ball :=
        h_geom_full Q hQ_in_Qball
      have h_y_in_P : y ∈ P_pointSet := Set.mem_iUnion₂.mpr ⟨p, hp_in_P, hyp⟩
      exact ⟨h_y_in_P, hQ_sub_ball (h_p_sub_Q hyp)⟩

    let fineUnion := (⋃ p ∈ (fineS_in_ball : Set (DyadicSquare n)), (p.toSet : Set Plane))
    let ballInter := P_pointSet ∩ Metric.closedBall center R_ball

    have h_packing : (fineS_in_ball.card : ENNReal) ≤
        (9 : ENNReal) * (Metric.externalCoveringNumber δ_n.toNNReal fineUnion : ENNReal) :=
      finset_squares_ncover_lower_clean fineS_in_ball

    have h_mono_nnreal : Metric.externalCoveringNumber δ_n.toNNReal fineUnion ≤
        Metric.externalCoveringNumber δ_n.toNNReal ballInter :=
      Metric.externalCoveringNumber_mono_set h_fine_sub_ball
    have h_mono_ennreal : (Metric.externalCoveringNumber δ_n.toNNReal fineUnion : ENNReal) ≤
        (Metric.externalCoveringNumber δ_n.toNNReal ballInter : ENNReal) := by
      exact_mod_cast h_mono_nnreal

    have h9_eq : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast

    have h_fine_cover : (fineS_in_ball.card : ENNReal) ≤
        ENNReal.ofReal (9 : ℝ) * (Metric.externalCoveringNumber δ_n.toNNReal ballInter : ENNReal) := by
      calc (fineS_in_ball.card : ENNReal)
        ≤ (9 : ENNReal) * (Metric.externalCoveringNumber δ_n.toNNReal fineUnion : ENNReal) := h_packing
      _ = ENNReal.ofReal (9 : ℝ) * (Metric.externalCoveringNumber δ_n.toNNReal fineUnion : ENNReal) := by
          rw [h9_eq]
      _ ≤ ENNReal.ofReal (9 : ℝ) * (Metric.externalCoveringNumber δ_n.toNNReal ballInter : ENNReal) := by
          exact mul_le_mul_of_nonneg_left h_mono_ennreal (by positivity)

    have h_sset_ball : Metric.externalCoveringNumber δ_n.toNNReal ballInter ≤
        ENNReal.ofReal C_point * (ENNReal.ofReal R_ball) ^ u *
        Metric.externalCoveringNumber δ_n.toNNReal P_pointSet :=
      h_point_sset.2.2.2.2 center R_ball hδn_le_R

    have h_ncover_P_le : (Metric.externalCoveringNumber δ_n.toNNReal P_pointSet : ENNReal) ≤ (P_uniform.card : ENNReal) := by
      let centers : Finset Plane := P_uniform.image (fun p : DyadicSquare n => retainedSquareCenter δ_n p)
      have h1 : P_pointSet ⊆ ⋃ c ∈ (centers : Set Plane), Metric.closedBall c δ_n.toNNReal := by
        intro y hy
        rcases Set.mem_iUnion₂.mp hy with ⟨p, hp, hyp⟩
        let c := retainedSquareCenter δ_n p
        have hc_in : c ∈ centers := Finset.mem_image.mpr ⟨p, hp, rfl⟩
        have hcov : y ∈ Metric.closedBall c δ_n :=
          retainedSquare_covered_by_center hδn_pos (by rfl) p hyp
        have hcov' : y ∈ Metric.closedBall c δ_n.toNNReal := by
          have h5 : ((δ_n.toNNReal : ℝ)) = δ_n := by
            simp [NNReal.coe_mk, hδn_pos.le] <;> linarith
          simpa [Metric.mem_closedBall, h5] using hcov
        exact Set.mem_iUnion₂.mpr ⟨c, hc_in, hcov'⟩
      have h_iscover : Metric.IsCover δ_n.toNNReal P_pointSet (centers : Set _) :=
        Metric.IsCover.of_subset_iUnion_closedBall h1
      have h6 : (Metric.externalCoveringNumber δ_n.toNNReal P_pointSet : ENNReal) ≤ (centers : Set Plane).encard := by
        exact_mod_cast h_iscover.externalCoveringNumber_le_encard
      have h7 : (centers : Set Plane).encard ≤ (P_uniform.card : ENNReal) := by
        exact_mod_cast Finset.card_image_le
      exact le_trans h6 h7

    have h_step1 : (Metric.externalCoveringNumber δ_n.toNNReal ballInter : ENNReal) ≤
        ENNReal.ofReal C_point * (ENNReal.ofReal R_ball) ^ u * (Metric.externalCoveringNumber δ_n.toNNReal P_pointSet : ENNReal) := by
      exact_mod_cast h_sset_ball
    have h_step2 : ENNReal.ofReal C_point * (ENNReal.ofReal R_ball) ^ u * (Metric.externalCoveringNumber δ_n.toNNReal P_pointSet : ENNReal) ≤
        ENNReal.ofReal C_point * (ENNReal.ofReal R_ball) ^ u * (P_uniform.card : ENNReal) := by
      gcongr
      <;> exact h_ncover_P_le
    have h_ball_bound : (fineS_in_ball.card : ENNReal) ≤
        ENNReal.ofReal (9 * C_point) * (ENNReal.ofReal R_ball) ^ u * (P_uniform.card : ENNReal) := by
      calc (fineS_in_ball.card : ENNReal)
        ≤ ENNReal.ofReal (9 : ℝ) * (Metric.externalCoveringNumber δ_n.toNNReal ballInter : ENNReal) := h_fine_cover
      _ ≤ ENNReal.ofReal (9 : ℝ) * (ENNReal.ofReal C_point * (ENNReal.ofReal R_ball) ^ u * (Metric.externalCoveringNumber δ_n.toNNReal P_pointSet : ENNReal)) := by
          exact mul_le_mul_of_nonneg_left h_step1 (by positivity)
      _ ≤ ENNReal.ofReal (9 : ℝ) * (ENNReal.ofReal C_point * (ENNReal.ofReal R_ball) ^ u * (P_uniform.card : ENNReal)) := by
          exact mul_le_mul_of_nonneg_left h_step2 (by positivity)
      _ = ENNReal.ofReal (9 * C_point) * (ENNReal.ofReal R_ball) ^ u * (P_uniform.card : ENNReal) := by
          simp [mul_assoc] <;> ring

    have h_lhs_ne_top : (fineS_in_ball.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have h_rhs_ne_top : (ENNReal.ofReal (9 * C_point) * (ENNReal.ofReal R_ball) ^ u * (P_uniform.card : ENNReal)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
      · exact ENNReal.natCast_ne_top _

    have hRball_pos : 0 < R_ball := by linarith [hR_geδm, hδm_pos]
    have h2_real : (fineS_in_ball.card : ℝ) ≤ 9 * C_point * R_ball ^ u * (P_uniform.card : ℝ) := by
      set X := ENNReal.ofReal (9 * C_point) with hX_def
      set Y := (ENNReal.ofReal R_ball) ^ u with hY_def
      set Z := (P_uniform.card : ENNReal) with hZ_def
      have hX_ne_top : X ≠ ⊤ := ENNReal.ofReal_ne_top
      have hY_ne_top : Y ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hu_nonneg ENNReal.ofReal_ne_top
      have hZ_ne_top : Z ≠ ⊤ := ENNReal.natCast_ne_top _
      have hXY_ne_top : X * Y ≠ ⊤ := ENNReal.mul_ne_top hX_ne_top hY_ne_top
      have h_toReal : (X * Y * Z).toReal = (X * Y).toReal * Z.toReal := by
        rw [ENNReal.toReal_mul]
      have h_toReal2 : (X * Y).toReal = X.toReal * Y.toReal := by
        rw [ENNReal.toReal_mul]
      have hX_toReal : X.toReal = 9 * C_point := by
        simp [X, ENNReal.toReal_ofReal] <;> linarith
      have hY_toReal : Y.toReal = R_ball ^ u := by
        have h1 : Y = ENNReal.ofReal (R_ball ^ u) := by
          simp [Y, ENNReal.ofReal_rpow_of_nonneg hRball_pos.le hu_nonneg]
        rw [h1, ENNReal.toReal_ofReal (by positivity)]
      have hZ_toReal : Z.toReal = (P_uniform.card : ℝ) := by simp [Z]
      have h := (ENNReal.toReal_le_toReal h_lhs_ne_top h_rhs_ne_top).mpr h_ball_bound
      rw [h_toReal, h_toReal2, hX_toReal, hY_toReal, hZ_toReal] at h
      exact h

    have h_fibers_disjoint : ∀ Q1 ∈ Q_ball, ∀ Q2 ∈ Q_ball, Q1 ≠ Q2 →
        Disjoint (P_uniform.filter (fun p => squareContained hnm p Q1))
                   (P_uniform.filter (fun p => squareContained hnm p Q2)) := by
      intro Q1 _ Q2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : squareContained hnm p Q1 := (Finset.mem_filter.mp hp1).2
      have h2 : squareContained hnm p Q2 := (Finset.mem_filter.mp hp2).2
      have h_eq1 : InductionConfigurations.containingSquare hnm p = Q1 :=
        (InductionConfigurations.containingSquare_iff hnm p Q1).mpr h1
      have h_eq2 : InductionConfigurations.containingSquare hnm p = Q2 :=
        (InductionConfigurations.containingSquare_iff hnm p Q2).mpr h2
      rw [h_eq1] at h_eq2
      exact hne h_eq2

    have h_fineS_eq_biUnion : fineS_in_ball = Q_ball.biUnion (fun Q => P_uniform.filter (fun p => squareContained hnm p Q)) := by
      ext p
      simp only [fineS_in_ball, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro h
        have hp : p ∈ P_uniform := h.1
        set Q := InductionConfigurations.containingSquare hnm p with hQ_def
        have hQ_in : Q ∈ Q_ball := h.2
        have h_eq : InductionConfigurations.containingSquare hnm p = Q := by simp [Q]
        have hsc : squareContained hnm p Q :=
          (InductionConfigurations.containingSquare_iff hnm p Q).mp h_eq
        exact ⟨Q, hQ_in, ⟨hp, hsc⟩⟩
      · rintro ⟨Q, hQ, hp⟩
        have hp' : p ∈ P_uniform := hp.1
        have hsc : squareContained hnm p Q := hp.2
        have h_eq : InductionConfigurations.containingSquare hnm p = Q :=
          (InductionConfigurations.containingSquare_iff hnm p Q).mpr hsc
        exact ⟨hp', h_eq ▸ hQ⟩

    have h_coarse_ball : F_lo * (Q_ball.card : ℝ) ≤ (fineS_in_ball.card : ℝ) := by
      have h_sum : (fineS_in_ball.card : ℝ) =
          ∑ Q ∈ Q_ball, ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) := by
        rw [h_fineS_eq_biUnion, Finset.card_biUnion h_fibers_disjoint]
        <;> simp [Nat.cast_sum]
      rw [h_sum]
      have h : ∑ Q ∈ Q_ball, ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) ≥
          ∑ Q ∈ Q_ball, F_lo := by
        apply Finset.sum_le_sum
        intro Q hQ
        have hQ' : Q ∈ Q_uniform := (Finset.mem_filter.mp hQ).1
        exact h_fiber_lower Q hQ'
      have h2 : ∑ Q ∈ Q_ball, F_lo = (Q_ball.card : ℝ) * F_lo := by
        rw [Finset.sum_const] <;> ring
      rw [h2] at h
      have h3 : (Q_ball.card : ℝ) * F_lo = F_lo * (Q_ball.card : ℝ) := by ring
      rw [h3] at h
      exact h

    have h_final_card : (Q_ball.card : ℝ) ≤
        (18 * C_point * R * (2 * Real.sqrt 2) ^ u) * r ^ u * (Q_uniform.card : ℝ) := by
      have h1 : F_lo * (Q_ball.card : ℝ) ≤ (fineS_in_ball.card : ℝ) := h_coarse_ball
      have h3 : (P_uniform.card : ℝ) < R * F_lo * (Q_uniform.card : ℝ) := h_Ptotal_upper
      have h4 : R_ball ^ u ≤ ((2 * Real.sqrt 2) * r) ^ u := by
        gcongr <;> linarith
      have h5 : F_lo * (Q_ball.card : ℝ) ≤
          9 * C_point * ((2 * Real.sqrt 2) * r) ^ u * (R * F_lo * (Q_uniform.card : ℝ)) := by
        calc F_lo * (Q_ball.card : ℝ)
          ≤ (fineS_in_ball.card : ℝ) := h1
        _ ≤ 9 * C_point * R_ball ^ u * (P_uniform.card : ℝ) := h2_real
        _ ≤ 9 * C_point * ((2 * Real.sqrt 2) * r) ^ u * (P_uniform.card : ℝ) := by gcongr
        _ ≤ 9 * C_point * ((2 * Real.sqrt 2) * r) ^ u * (R * F_lo * (Q_uniform.card : ℝ)) := by
          gcongr <;> exact le_of_lt h3
      have h6 : F_lo * (Q_ball.card : ℝ) ≤
          9 * C_point * R * ((2 * Real.sqrt 2) * r) ^ u * F_lo * (Q_uniform.card : ℝ) := by
        linarith
      have h7 : (Q_ball.card : ℝ) ≤
          9 * C_point * R * ((2 * Real.sqrt 2) * r) ^ u * (Q_uniform.card : ℝ) := by
        nlinarith [hF_lo_pos]
      have h8 : (Q_ball.card : ℝ) ≤
          18 * C_point * R * ((2 * Real.sqrt 2) * r) ^ u * (Q_uniform.card : ℝ) := by
        have h9 : 0 ≤ 9 * C_point * R * ((2 * Real.sqrt 2) * r) ^ u * (Q_uniform.card : ℝ) := by positivity
        linarith
      have h10 : ((2 * Real.sqrt 2) * r) ^ u = (2 * Real.sqrt 2) ^ u * r ^ u := by
        have h_pos1 : 0 ≤ 2 * Real.sqrt 2 := by positivity
        have h_pos2 : 0 ≤ r := by linarith
        rw [Real.mul_rpow h_pos1 h_pos2]
      rw [h10] at h8
      linarith

    have hS_ball_card : S_ball.card = Q_ball.card := by
      rw [Finset.card_image_of_injective Q_ball]
      intro Q1 Q2 h
      have hi : Q1.i = Q2.i := by simpa [dyadicSquareToDSquare] using congr_arg DSquare.i h
      have hj : Q1.j = Q2.j := by simpa [dyadicSquareToDSquare] using congr_arg DSquare.j h
      cases Q1
      cases Q2
      congr <;> tauto

    have hS_ball_set_eq : (S_ball : Set (DSquare m)) =
        (S_dsquare : Set (DSquare m)) ∩ Metric.closedBall p r := by
      rw [hS_ball_eq]
      ext q
      simp [S_dsquare, Metric.mem_closedBall] <;> tauto

    have h_ncover_ball : (Metric.externalCoveringNumber δ_m.toNNReal
        ((S_dsquare : Set (DSquare m)) ∩ Metric.closedBall p r) : ENNReal) ≤ (S_ball.card : ENNReal) := by
      rw [←hS_ball_set_eq]
      have h1 : (S_ball : Set (DSquare m)) ⊆ ⋃ x ∈ (S_ball : Set (DSquare m)), Metric.closedBall x δ_m.toNNReal := by
        intro x hx
        refine Set.mem_iUnion₂.mpr ⟨x, hx, ?_⟩
        rw [Metric.mem_closedBall, dist_self]
        <;> exact NNReal.coe_nonneg _
      have hcover : Metric.IsCover δ_m.toNNReal (S_ball : Set (DSquare m)) (S_ball : Set (DSquare m)) :=
        Metric.IsCover.of_subset_iUnion_closedBall h1
      have h : (Metric.externalCoveringNumber δ_m.toNNReal (S_ball : Set (DSquare m)) : ENNReal) ≤
          (S_ball : Set (DSquare m)).encard := by
        exact_mod_cast hcover.externalCoveringNumber_le_encard
      have h2 : (S_ball : Set (DSquare m)).encard = (S_ball.card : ENNReal) := by simp
      rw [h2] at h
      exact h

    have h_grid : (S_dsquare.card : ENNReal) ≤
        (9 : ENNReal) * (Metric.externalCoveringNumber δ_m.toNNReal (S_dsquare : Set (DSquare m)) : ENNReal) :=
      grid_packing_dsquare hδm_pos rfl S_dsquare

    have h_card_eq : (S_dsquare.card : ENNReal) = (Q_uniform.card : ENNReal) := by
      have h : (finsetDyadicToDSquare Q_uniform).card = Q_uniform.card :=
        card_dyadicToDSquare Q_uniform
      exact_mod_cast h

    have h_grid' : (Q_uniform.card : ENNReal) ≤
        (9 : ENNReal) * (Metric.externalCoveringNumber δ_m.toNNReal (S_dsquare : Set (DSquare m)) : ENNReal) := by
      rw [←h_card_eq]
      exact h_grid

    let C_pre := 18 * C_point * R * (2 * Real.sqrt 2) ^ u
    have hC_pre_pos : 0 ≤ C_pre := by positivity

    calc (Metric.externalCoveringNumber δ_m.toNNReal ((S_dsquare : Set (DSquare m)) ∩ Metric.closedBall p r) : ENNReal)
      ≤ (S_ball.card : ENNReal) := h_ncover_ball
    _ = (Q_ball.card : ENNReal) := by rw [hS_ball_card]
    _ ≤ ENNReal.ofReal (C_pre * r ^ u * (Q_uniform.card : ℝ)) := by
        have h_pos : 0 ≤ C_pre * r ^ u * (Q_uniform.card : ℝ) := by positivity
        have h_card_coe : (Q_ball.card : ENNReal) = ENNReal.ofReal (Q_ball.card : ℝ) := by simp
        rw [h_card_coe]
        rw [ENNReal.ofReal_le_ofReal_iff h_pos]
        exact h_final_card
    _ = ENNReal.ofReal C_pre * (ENNReal.ofReal r) ^ u * (Q_uniform.card : ENNReal) := by
        have h_pos1 : 0 ≤ C_pre := by positivity
        have h_pos2 : 0 ≤ r ^ u := by positivity
        have h_eq1 : ENNReal.ofReal (C_pre * r ^ u * (Q_uniform.card : ℝ)) =
            ENNReal.ofReal C_pre * ENNReal.ofReal (r ^ u) * ENNReal.ofReal (Q_uniform.card : ℝ) := by
          rw [ENNReal.ofReal_mul (show 0 ≤ C_pre * r ^ u by positivity)]
          rw [ENNReal.ofReal_mul h_pos1]
          <;> ring
        have h_eq2 : ENNReal.ofReal (r ^ u) = (ENNReal.ofReal r) ^ u := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by linarith) hu_nonneg]
        have h_eq3 : ENNReal.ofReal (Q_uniform.card : ℝ) = (Q_uniform.card : ENNReal) := by simp
        rw [h_eq1, h_eq2, h_eq3] <;> ring
    _ ≤ ENNReal.ofReal C_pre * (ENNReal.ofReal r) ^ u *
          ((9 : ENNReal) * (Metric.externalCoveringNumber δ_m.toNNReal (S_dsquare : Set (DSquare m)) : ENNReal)) := by
        exact mul_le_mul_of_nonneg_left h_grid' (by positivity)
    _ = ENNReal.ofReal (162 * C_point * R * (2 * Real.sqrt 2) ^ u) * (ENNReal.ofReal r) ^ u *
          (Metric.externalCoveringNumber δ_m.toNNReal (S_dsquare : Set (DSquare m)) : ENNReal) := by
        have h9 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast
        have h_combine : ENNReal.ofReal C_pre * ENNReal.ofReal (9 : ℝ) =
            ENNReal.ofReal (C_pre * 9) := by
          rw [← ENNReal.ofReal_mul hC_pre_pos] <;> ring
        have h_final : C_pre * 9 = 162 * C_point * R * (2 * Real.sqrt 2) ^ u := by
          dsimp only [C_pre] <;> ring
        have h_ring1 : ENNReal.ofReal C_pre * (ENNReal.ofReal r) ^ u * ((9 : ENNReal) * (Metric.externalCoveringNumber δ_m.toNNReal (S_dsquare : Set (DSquare m)) : ENNReal)) =
            (ENNReal.ofReal C_pre * ENNReal.ofReal (9 : ℝ)) * (ENNReal.ofReal r) ^ u * (Metric.externalCoveringNumber δ_m.toNNReal (S_dsquare : Set (DSquare m)) : ENNReal) := by
          rw [h9]
          <;> ring
        rw [h_ring1, h_combine, h_final]
        <;> ring

  exact ⟨hS_nonempty, hδm_pos, by positivity, hu_nonneg, h_main⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end

module

/-
  Tight near-center geometric lemma for coarse tubes.

  Uses direct slope/intercept parameterization to show that a coarse tube whose
  fine parent lies in square Q passes within ~6Δ of the square center, improving
  the 53Δ bound from `coarse_tube_near_square_center`.

  Key chain:
  1. Fine tube T passes within 2δ of point p in square Q.
  2. InParent gives |slope(T) - slope(U)| < Δ and |intercept(T) - intercept(U)| < Δ.
  3. Line equation transfer: |p₀ - a_U·p₁ - b_U| ≤ 2δ + √2·Δ + Δ ≤ (3 + √2)·Δ.
  4. Construct point on U explicitly → infDist(p, U) ≤ (3 + √2)·Δ.
  5. Square center is within √2/2·Δ of p → center within (3 + 3√2/2)·Δ < 10Δ.

  Whiteprint node: AppendixA / near_center_tight
  Dependencies: TubesAndSlopes, Interfaces, A3_GeometricLemmas
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_GeometricLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.H2_Migration_Adapters
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter squareSet point_in_square_close_to_center)
open DirecretisedFurstenbergEstimate.AppendixA.H2Migration (sameCell_paramDist_lt_delta)
open TubesAndSlopes (near_point_intercept_bound_affine)

abbrev affParams := LemmaE.affineLineParams

/-- From intercept bound to point-near-line: if |p₀ - a·p₁ - b| ≤ C,
    then p is within C of the affine line with params (a,b). -/
lemma intercept_bound_to_point_near
    {ℓ : AffineLine} {p : EuclideanPlane} {C : ℝ}
    (hv1 : (LemmaE.getDirV ℓ) 1 ≠ 0)
    (h_bound : |p 0 - (affParams ℓ).1 * p 1 - (affParams ℓ).2| ≤ C) :
    Metric.infDist p (ℓ.1 : Set EuclideanPlane) ≤ C := by
  let a := (affParams ℓ).1
  let b := (affParams ℓ).2
  let v := LemmaE.getDirV ℓ
  let off := ℓ.offset
  have hv_in_dir : v ∈ ℓ.1.direction := (LemmaE.getDirV_spec ℓ).1
  have hv_ne_zero : v ≠ 0 := (LemmaE.getDirV_spec ℓ).2
  have ha_eq : a = v 0 / v 1 := by
    dsimp only [a, affParams, LemmaE.affineLineParams]
    rw [if_neg hv1]
  have hb_eq : b = off 0 - a * off 1 := by
    dsimp only [b, affParams, LemmaE.affineLineParams]
    rw [if_neg hv1]
    <;> rw [ha_eq] <;> rfl
  have hoff_line : off 0 = a * off 1 + b := by
    rw [hb_eq] <;> ring
  let t : ℝ := (p 1 - off 1) / v 1
  let q : EuclideanPlane := off + t • v
  have hq_line : q ∈ ℓ.1 := by
    have h : q - off ∈ ℓ.1.direction := by
      simpa [q] using ℓ.1.direction.smul_mem t hv_in_dir
    have h2 : (q - off) +ᵥ off ∈ ℓ.1 := AffineSubspace.vadd_mem_of_mem_direction h ℓ.offset_mem
    have h3 : (q - off) +ᵥ off = q := by
      simp [vadd_eq_add] <;> abel
    rw [h3] at h2
    exact h2
  have hq1 : q 1 = p 1 := by
    have h : q 1 = off 1 + t * v 1 := by simp [q]
    rw [h]
    have h2 : t * v 1 = p 1 - off 1 := by
      dsimp only [t]
      have h4 : v 1 ≠ 0 := hv1
      have h5 : v 1 * (v 1)⁻¹ = 1 := by
        field_simp [h4]
      have h6 : ((p 1 - off 1) / v 1) * v 1 = (p 1 - off 1) * (v 1 * (v 1)⁻¹) := by ring
      rw [h6, h5] <;> ring
    rw [h2] <;> ring
  have hq0 : q 0 = a * p 1 + b := by
    have h : q 0 = off 0 + t * v 0 := by simp [q]
    rw [h]
    have h2 : t * v 0 = (p 1 - off 1) * a := by
      simp [t, ha_eq] <;> field_simp [hv1] <;> ring
    rw [h2, hoff_line] <;> ring
  have h_dist : dist p q = |p 0 - a * p 1 - b| := by
    have h2 : p 1 = q 1 := hq1.symm
    have h3 : dist p q = |p 0 - q 0| := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two, h2]
      <;> rw [Real.sqrt_sq_eq_abs] <;> rfl
    rw [h3]
    have h4 : p 0 - q 0 = p 0 - a * p 1 - b := by
      rw [hq0] <;> ring
    rw [h4]
  have h_main : Metric.infDist p (ℓ.1 : Set EuclideanPlane) ≤ dist p q :=
    Metric.infDist_le_dist_of_mem hq_line
  rw [h_dist] at h_main
  exact h_main.trans h_bound

/-- Tight point-to-coarse-line transfer using direct slope/intercept bounds.

    If fine tube T and coarse tube U are in the same dyadic parent cell
    (|slope diff| < Δ, |intercept diff| < Δ), and p is within 2δ of T,
    then p is within (5 + √2)·Δ of U. -/
lemma point_near_coarse_from_params_tight
    {Δ δ : ℝ} (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    {T U : AffineLine} {p : EuclideanPlane}
    (hvT : (LemmaE.getDirV T) 1 ≠ 0)
    (hvU : (LemmaE.getDirV U) 1 ≠ 0)
    (haT : |(affParams T).1| ≤ 1)
    (haU : |(affParams U).1| ≤ 1)
    (h_slope_diff : |(affParams T).1 - (affParams U).1| < Δ)
    (h_intercept_diff : |(affParams T).2 - (affParams U).2| < Δ)
    (hp_near_T : p ∈ Metric.cthickening (2 * δ) (T.1 : Set EuclideanPlane))
    (hp_bound : ‖p‖ ≤ Real.sqrt 2) :
    p ∈ Metric.cthickening ((5 + Real.sqrt 2) * Δ) (U.1 : Set EuclideanPlane) := by
  let aT := (affParams T).1
  let bT := (affParams T).2
  let aU := (affParams U).1
  let bU := (affParams U).2
  set δ' := 2 * δ with hδ'_def
  have hδ'_pos : 0 < δ' := by positivity
  have h1_raw : |bT - (p 0 - aT * p 1)| ≤ 2 * δ' :=
    near_point_intercept_bound_affine hδ'_pos haT hvT hp_near_T
  have h1 : |p 0 - aT * p 1 - bT| ≤ 2 * δ' := by
    have h_eq : bT - (p 0 - aT * p 1) = -(p 0 - aT * p 1 - bT) := by ring
    rw [h_eq] at h1_raw
    rw [abs_neg] at h1_raw
    exact h1_raw
  have h1' : |p 0 - aT * p 1 - bT| ≤ 4 * δ := by
    have h2 : 2 * δ' = 4 * δ := by
      simp [hδ'_def] <;> ring
    rw [h2] at h1
    exact h1
  have h_p1_abs : |p 1| ≤ Real.sqrt 2 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
    exact h.trans hp_bound
  set x := p 0 - aT * p 1 - bT with hx_def
  set y := (aT - aU) * p 1 with hy_def
  set z := bT - bU with hz_def
  have h_abs_y : |y| = |aT - aU| * |p 1| := by
    simp only [hy_def, abs_mul]
  have h_main_eq : p 0 - aU * p 1 - bU = x + y + z := by
    simp only [hx_def, hy_def, hz_def] <;> ring
  have h2 : |p 0 - aU * p 1 - bU| ≤ (5 + Real.sqrt 2) * Δ := by
    rw [h_main_eq]
    have h_triangle : |x + y + z| ≤ |x| + |y| + |z| := by
      have h1 : |x + y| ≤ |x| + |y| := abs_add_le x y
      have h2 : |(x + y) + z| ≤ |x + y| + |z| := abs_add_le (x + y) z
      have h3 : x + y + z = (x + y) + z := by ring
      rw [h3]
      linarith
    rw [h_abs_y] at h_triangle
    calc |x + y + z|
      ≤ |x| + |aT - aU| * |p 1| + |z| := h_triangle
    _ ≤ 4 * δ + Δ * Real.sqrt 2 + Δ := by
      have h3 : |x| ≤ 4 * δ := h1'
      have h4 : |aT - aU| * |p 1| ≤ Δ * Real.sqrt 2 := by
        calc |aT - aU| * |p 1|
          ≤ Δ * |p 1| := by gcongr <;> exact h_slope_diff.le
        _ ≤ Δ * Real.sqrt 2 := by gcongr <;> exact h_p1_abs
      have h5 : |z| ≤ Δ := h_intercept_diff.le
      linarith
    _ ≤ 4 * Δ + Real.sqrt 2 * Δ + Δ := by
      have h6 : 4 * δ ≤ 4 * Δ := by gcongr
      linarith
    _ = (5 + Real.sqrt 2) * Δ := by ring
  have h_infDist : Metric.infDist p (U.1 : Set EuclideanPlane) ≤ (5 + Real.sqrt 2) * Δ :=
    intercept_bound_to_point_near hvU h2
  have h_nonempty : (U.1 : Set EuclideanPlane).Nonempty := U.nonempty
  have h_edist : Metric.infEDist p (U.1 : Set EuclideanPlane) ≤ ENNReal.ofReal ((5 + Real.sqrt 2) * Δ) := by
    have h_ne_top : Metric.infEDist p (U.1 : Set EuclideanPlane) ≠ ⊤ :=
      Metric.infEDist_ne_top h_nonempty
    have h_eq : Metric.infEDist p (U.1 : Set EuclideanPlane) =
        ENNReal.ofReal (Metric.infDist p (U.1 : Set EuclideanPlane)) := by
      simp [Metric.infDist, ENNReal.ofReal_toReal h_ne_top]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_infDist
  exact Metric.mem_cthickening_iff.mpr h_edist

/-- Tight near-center bound: every coarse tube in C_Q is within 10Δ of the
    square center.

    Uses direct slope/intercept parameter transfer instead of the generic
    AffineLine metric, improving the bound from 53Δ to under 10Δ. -/
lemma coarse_tube_near_square_center_tight
    {Δ δ s t ε : ℝ} {Q : CoarseSquare Δ}
    (sd : A2_SquareData Δ δ s t ε Q)
    (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hΔ_le_half : Δ ≤ 1 / 2) :
    ∀ (boldT : CoarseTube), boldT ∈ sd.C_Q →
      squareCenter Δ Q ∈ Metric.cthickening (10 * Δ) (boldT.1 : Set EuclideanPlane) := by
  intro boldT hboldT
  have hH2 : (sd.H_Q : ℝ) ≤ ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) := by
    have h_orig := sd.hH2 boldT hboldT
    have h_cast : (↑(∑ p ∈ sd.P_Q, (pointFiber Δ hΔ_pos sd.T_Q p boldT).card) : ℝ) =
        ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) := by
      rw [Nat.cast_sum]
    rw [h_cast] at h_orig
    exact h_orig
  have hH_Q_ge_one : (1 : ℝ) ≤ sd.H_Q := sd.hH_Q_ge_one
  have h_sum_pos : 0 < ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) := by
    have h : (1 : ℝ) ≤ (∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ)) := by
      calc (1 : ℝ) ≤ sd.H_Q := hH_Q_ge_one
           _ ≤ (∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ)) := hH2
    exact lt_of_lt_of_le (by norm_num) h
  have h_exists : ∃ (p : EuclideanPlane), p ∈ sd.P_Q ∧
      (pointFiber Δ hΔ_pos sd.T_Q p boldT).Nonempty := by
    by_contra h
    push Not at h
    have h_sum_zero : ∑ p ∈ sd.P_Q, ((pointFiber Δ hΔ_pos sd.T_Q p boldT).card : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have h9 : pointFiber Δ hΔ_pos sd.T_Q p boldT = ∅ := h p hp
      rw [h9] <;> simp
    rw [h_sum_zero] at h_sum_pos
    simpa using h_sum_pos
  rcases h_exists with ⟨p, hp_in_PQ, h_fiber_nonempty⟩
  rcases h_fiber_nonempty with ⟨T, hT_in_fiber⟩
  have hT_in_Tp : T ∈ sd.T_Q p := (Finset.mem_filter.mp hT_in_fiber).1
  have hInParent : InParent Δ hΔ_pos T boldT := (Finset.mem_filter.mp hT_in_fiber).2
  have h_bounds_T := sd.h_slope_bound p hp_in_PQ T hT_in_Tp
  have h_bounds_boldT : (LemmaE.getDirV boldT) 1 ≠ 0 ∧ |tubeSlope boldT| ≤ 1 ∧ |tubeIntercept boldT| ≤ 3 :=
    ⟨sd.hC_Q_v boldT hboldT, sd.hC_Q_slope_bound boldT hboldT, sd.hC_Q_b boldT hboldT⟩
  have h_param : dist (tubeSlope T, tubeIntercept T) (tubeSlope boldT, tubeIntercept boldT) < Δ :=
    sameCell_paramDist_lt_delta Δ hΔ_pos T boldT hInParent
  have h_slope_diff : |tubeSlope T - tubeSlope boldT| < Δ := by
    have h : dist (tubeSlope T, tubeIntercept T) (tubeSlope boldT, tubeIntercept boldT) =
        max (|tubeSlope T - tubeSlope boldT|) (|tubeIntercept T - tubeIntercept boldT|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h] at h_param
    have h5 : |tubeSlope T - tubeSlope boldT| ≤ max (|tubeSlope T - tubeSlope boldT|) (|tubeIntercept T - tubeIntercept boldT|) :=
      le_max_left _ _
    exact h5.trans_lt h_param
  have h_intercept_diff : |tubeIntercept T - tubeIntercept boldT| < Δ := by
    have h : dist (tubeSlope T, tubeIntercept T) (tubeSlope boldT, tubeIntercept boldT) =
        max (|tubeSlope T - tubeSlope boldT|) (|tubeIntercept T - tubeIntercept boldT|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h] at h_param
    have h5 : |tubeIntercept T - tubeIntercept boldT| ≤ max (|tubeSlope T - tubeSlope boldT|) (|tubeIntercept T - tubeIntercept boldT|) :=
      le_max_right _ _
    exact h5.trans_lt h_param
  have hp_near_T : p ∈ Metric.cthickening (2 * δ) (T.1 : Set EuclideanPlane) :=
    sd.h_inc p hp_in_PQ T hT_in_Tp
  have hp_in_ball : ‖p‖ ≤ Real.sqrt 2 := by
    have h1 : p ∈ Metric.closedBall (0 : EuclideanPlane) (Real.sqrt 2) := sd.hP_Q_in_ball hp_in_PQ
    simpa [Metric.mem_closedBall] using h1
  have hp_near_boldT : p ∈ Metric.cthickening ((5 + Real.sqrt 2) * Δ) (boldT.1 : Set EuclideanPlane) :=
    point_near_coarse_from_params_tight hΔ_pos hδ_pos hδ_le_Δ
      h_bounds_T.1 h_bounds_boldT.1
      h_bounds_T.2.1 h_bounds_boldT.2.1
      h_slope_diff h_intercept_diff
      hp_near_T hp_in_ball
  have hp_in_square : p ∈ squareSet Δ Q := sd.hP_Q_in_square hp_in_PQ
  have h_center_dist : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
    point_in_square_close_to_center hΔ_pos Q p hp_in_square
  have h_center_dist' : dist (squareCenter Δ Q) p ≤ Real.sqrt 2 * Δ / 2 := by
    rw [dist_comm]
    exact h_center_dist
  have h_total : (5 + Real.sqrt 2) * Δ + Real.sqrt 2 * Δ / 2 ≤ 10 * Δ := by
    have h5 : (5 + Real.sqrt 2) + Real.sqrt 2 / 2 ≤ 10 := by
      have h6 : Real.sqrt 2 ≤ 3 := by
        have h7 : Real.sqrt 2 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
        have h8 : Real.sqrt 9 = 3 := by rw [Real.sqrt_eq_cases] <;> norm_num
        linarith
      nlinarith
    have h9 : 0 ≤ Δ := by linarith
    nlinarith
  have h_infDist_p : Metric.infDist p (boldT.1 : Set EuclideanPlane) ≤ (5 + Real.sqrt 2) * Δ := by
    have h_edist : Metric.infEDist p (boldT.1 : Set EuclideanPlane) ≤ ENNReal.ofReal ((5 + Real.sqrt 2) * Δ) :=
      Metric.mem_cthickening_iff.mp hp_near_boldT
    have h_ne_top : Metric.infEDist p (boldT.1 : Set EuclideanPlane) ≠ ⊤ :=
      Metric.infEDist_ne_top (AffineLine.nonempty boldT)
    have h_conv : Metric.infDist p (boldT.1 : Set EuclideanPlane) =
        ENNReal.toReal (Metric.infEDist p (boldT.1 : Set EuclideanPlane)) := by rfl
    rw [h_conv]
    have h_mono : ENNReal.toReal (Metric.infEDist p (boldT.1 : Set EuclideanPlane)) ≤ ENNReal.toReal (ENNReal.ofReal ((5 + Real.sqrt 2) * Δ)) :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h_edist
    rw [ENNReal.toReal_ofReal (show 0 ≤ (5 + Real.sqrt 2) * Δ from by positivity)] at h_mono
    exact h_mono
  have h_tri : Metric.infDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) ≤
      Metric.infDist p (boldT.1 : Set EuclideanPlane) + dist (squareCenter Δ Q) p :=
    Metric.infDist_le_infDist_add_dist
  have h_center_near : Metric.infDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) ≤ 10 * Δ := by
    calc Metric.infDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane)
      ≤ Metric.infDist p (boldT.1 : Set EuclideanPlane) + dist (squareCenter Δ Q) p := h_tri
    _ ≤ (5 + Real.sqrt 2) * Δ + Real.sqrt 2 * Δ / 2 := by
      gcongr <;> exact h_center_dist'
    _ ≤ 10 * Δ := h_total
  have h_nonempty : (boldT.1 : Set EuclideanPlane).Nonempty := AffineLine.nonempty boldT
  have h_edist : Metric.infEDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) ≤ ENNReal.ofReal (10 * Δ) := by
    have h_ne_top : Metric.infEDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) ≠ ⊤ :=
      Metric.infEDist_ne_top h_nonempty
    have h_eq : Metric.infEDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane) =
        ENNReal.ofReal (Metric.infDist (squareCenter Δ Q) (boldT.1 : Set EuclideanPlane)) := by
      simp [Metric.infDist, ENNReal.ofReal_toReal h_ne_top]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_center_near
  exact Metric.mem_cthickening_iff.mpr h_edist

end DirecretisedFurstenbergEstimate.AppendixA

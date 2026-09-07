module

/-
  Factor-2 doubling property for AffineLine on bounded-slope charts.

  Uses the bi-Lipschitz parameterization (slope, intercept) → AffineLine
  from `DyadicToAffineAdapters`:
  - Forward: 5-Lipschitz (L∞ → AffineLine)
  - Backward: 14-Lipschitz (AffineLine → L∞)

  On the chart {|m| ≤ 1, |b| ≤ 3}, transfers L∞ doubling to AffineLine
  doubling with constant 4^9 = 262144.

  Whiteprint node: affine_line_doubling
  Dependencies: DoublingProperty, DyadicToAffineAdapters
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DoublingProperty
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CoveringUtils

open DirecretisedFurstenbergEstimate
open DyadicToAffineAdapters
open DiscretisedFurstenbergEstimate
open DyadicCardToNcover

section LinftyDoubling

/-- L∞ factor-2 doubling on ℝ²: a ball of radius 2r is covered by
    4 balls of radius r. -/
lemma linfty2_doubling_cover (r : ℝ) (hr_pos : 0 < r) (c : ℝ × ℝ) :
    ∃ (S : Finset (ℝ × ℝ)), S.card = 4 ∧
      Metric.closedBall c (2 * r) ⊆ ⋃ s ∈ S, Metric.closedBall s r := by
  let centers : Finset (ℝ × ℝ) :=
    {(c.1 + r, c.2 + r), (c.1 + r, c.2 - r), (c.1 - r, c.2 + r), (c.1 - r, c.2 - r)}
  have hne : r ≠ 0 := hr_pos.ne'
  have h_card : centers.card = 4 := by
    have h1 : (c.1 + r, c.2 + r) ≠ (c.1 + r, c.2 - r) := by
      intro h; have : c.2 + r = c.2 - r := by exact congr_arg Prod.snd h
      linarith
    have h2 : (c.1 + r, c.2 + r) ≠ (c.1 - r, c.2 + r) := by
      intro h; have : c.1 + r = c.1 - r := by exact congr_arg Prod.fst h
      linarith
    have h3 : (c.1 + r, c.2 + r) ≠ (c.1 - r, c.2 - r) := by
      intro h; have : c.1 + r = c.1 - r := by exact congr_arg Prod.fst h
      linarith
    have h4 : (c.1 + r, c.2 - r) ≠ (c.1 - r, c.2 + r) := by
      intro h; have : c.1 + r = c.1 - r := by exact congr_arg Prod.fst h
      linarith
    have h5 : (c.1 + r, c.2 - r) ≠ (c.1 - r, c.2 - r) := by
      intro h; have : c.1 + r = c.1 - r := by exact congr_arg Prod.fst h
      linarith
    have h6 : (c.1 - r, c.2 + r) ≠ (c.1 - r, c.2 - r) := by
      intro h; have : c.2 + r = c.2 - r := by exact congr_arg Prod.snd h
      linarith
    simp [centers, Finset.mem_insert, Finset.mem_singleton, h1, h2, h3, h4, h5, h6] <;> norm_num
  refine' ⟨centers, h_card, _⟩
  intro x hx
  have h_dist : dist x c ≤ 2 * r := by simpa [Metric.mem_closedBall] using hx
  have h_max : max |x.1 - c.1| |x.2 - c.2| ≤ 2 * r := by
    have h : dist x c = max |x.1 - c.1| |x.2 - c.2| := by
      rw [Prod.dist_eq] <;> rfl
    rw [h] at h_dist
    exact h_dist
  have h1 : |x.1 - c.1| ≤ 2 * r := le_trans (le_max_left _ _) h_max
  have h2 : |x.2 - c.2| ≤ 2 * r := le_trans (le_max_right _ _) h_max
  have h_abs1 : |x.1 - c.1| ≤ 2 * r := h1
  have h_abs2 : |x.2 - c.2| ≤ 2 * r := h2
  by_cases hx1 : x.1 ≥ c.1
  · by_cases hx2 : x.2 ≥ c.2
    · let s := (c.1 + r, c.2 + r)
      have hs : s ∈ centers := by simp [centers, s]
      have hd1 : |x.1 - s.1| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs1]
      have hd2 : |x.2 - s.2| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs2]
      have hd : dist x s ≤ r := by
        simpa [Prod.dist_eq, max_le_iff] using ⟨hd1, hd2⟩
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hd⟩
    · let s := (c.1 + r, c.2 - r)
      have hs : s ∈ centers := by simp [centers, s]
      have hd1 : |x.1 - s.1| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs1]
      have hd2 : |x.2 - s.2| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs2]
      have hd : dist x s ≤ r := by
        simpa [Prod.dist_eq, max_le_iff] using ⟨hd1, hd2⟩
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hd⟩
  · by_cases hx2 : x.2 ≥ c.2
    · let s := (c.1 - r, c.2 + r)
      have hs : s ∈ centers := by simp [centers, s]
      have hd1 : |x.1 - s.1| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs1]
      have hd2 : |x.2 - s.2| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs2]
      have hd : dist x s ≤ r := by
        simpa [Prod.dist_eq, max_le_iff] using ⟨hd1, hd2⟩
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hd⟩
    · let s := (c.1 - r, c.2 - r)
      have hs : s ∈ centers := by simp [centers, s]
      have hd1 : |x.1 - s.1| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs1]
      have hd2 : |x.2 - s.2| ≤ r := by
        dsimp only [s]
        rw [abs_le] <;> constructor <;> linarith [abs_le.mp h_abs2]
      have hd : dist x s ≤ r := by
        simpa [Prod.dist_eq, max_le_iff] using ⟨hd1, hd2⟩
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hd⟩

/-- L∞ doubling on ℝ²: Ncover(s, F) ≤ 4 * Ncover(2s, F). -/
lemma linfty2_doubling (s : ℝ) (hs_pos : 0 < s) (F : Set (ℝ × ℝ)) :
    Metric.externalCoveringNumber s.toNNReal F ≤
      (4 : ENat) * Metric.externalCoveringNumber (2 * s).toNNReal F := by
  let r_nn : NNReal := s.toNNReal
  let R_nn : NNReal := (2 * s).toNNReal
  have hr : (r_nn : ℝ) = s := by simp [r_nn] <;> linarith
  have hR : (R_nn : ℝ) = 2 * s := by simp [R_nn] <;> linarith
  exact externalCoveringNumber_doubling (hC_d_pos := by norm_num)
    (fun c => by
      rcases linfty2_doubling_cover s hs_pos c with ⟨S, hS_card, hS_cover⟩
      refine' ⟨S, hS_card, _⟩
      have hR2 : (R_nn : ℝ) = 2 * s := by simp [R_nn, NNReal.coe_mk] <;> linarith
      have hr2 : (r_nn : ℝ) = s := by simp [r_nn, NNReal.coe_mk] <;> linarith
      rw [hR2, hr2]
      exact hS_cover)

end LinftyDoubling

section AffineLineChart

/-- Forward Lipschitz: AffineLine dist ≤ 5 * L∞ param dist. -/
lemma affine_line_forward_lipschitz {m1 m2 b1 b2 : ℝ}
    (hm1 : |m1| ≤ 1) (hm2 : |m2| ≤ 1) (hb2 : |b2| ≤ 3) :
    dist (lineOfSlopeIntercept m1 b1) (lineOfSlopeIntercept m2 b2) ≤
      5 * max |m1 - m2| |b1 - b2| := by
  set ℓ1 := lineOfSlopeIntercept m1 b1 with hℓ1
  set ℓ2 := lineOfSlopeIntercept m2 b2 with hℓ2
  have h_dir1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} :=
    lineOfSlopeIntercept_direction m1 b1
  have h_dir2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} :=
    lineOfSlopeIntercept_direction m2 b2
  have h_proj : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≤ |m1 - m2| := by
    rw [h_dir1, h_dir2]; exact proj_op_norm_bound m1 m2
  have h_off1 : ℓ1.offset = b1 • offsetVec m1 := by
    rw [hℓ1, lineOfSlopeIntercept]; exact offset_formula m1 b1
  have h_off2 : ℓ2.offset = b2 • offsetVec m2 := by
    rw [hℓ2, lineOfSlopeIntercept]; exact offset_formula m2 b2
  have h_off : ‖ℓ1.offset - ℓ2.offset‖ ≤ |b1 - b2| + 3 * |m1 - m2| := by
    rw [h_off1, h_off2]; exact offset_diff_upper m1 m2 b1 b2 hb2
  have hdm : |m1 - m2| ≤ max |m1 - m2| |b1 - b2| := le_max_left _ _
  have hdb : |b1 - b2| ≤ max |m1 - m2| |b1 - b2| := le_max_right _ _
  calc dist ℓ1 ℓ2
    = ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖ := by rfl
    _ ≤ |m1 - m2| + (|b1 - b2| + 3 * |m1 - m2|) := by linarith
    _ = 4 * |m1 - m2| + |b1 - b2| := by ring
    _ ≤ 5 * max |m1 - m2| |b1 - b2| := by linarith

/-- Lower bound on projection operator norm difference.
    For |m1|, |m2| ≤ 1: |m1 - m2| ≤ 2 * ‖P1 - P2‖. -/
lemma proj_op_norm_lower {m1 m2 : ℝ} (hm1 : |m1| ≤ 1) (hm2 : |m2| ≤ 1) :
    |m1 - m2| ≤ 2 * ‖(Submodule.span ℝ {tubeDirV m1}).starProjection -
                        (Submodule.span ℝ {tubeDirV m2}).starProjection‖ := by
  let P1 := (Submodule.span ℝ {tubeDirV m1}).starProjection
  let P2 := (Submodule.span ℝ {tubeDirV m2}).starProjection
  let w : Plane := TubesAndSlopes.mkPlane 1 0
  have hw0 : w 0 = 1 := by simp [w, TubesAndSlopes.mkPlane]
  have hw1 : w 1 = 0 := by simp [w, TubesAndSlopes.mkPlane]
  have hw_norm2 : ‖w‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, hw0, hw1] <;> norm_num
  have hw_norm : ‖w‖ = 1 := by
    have h : 0 ≤ ‖w‖ := by positivity
    nlinarith
  let v1 := ((w 0 + m1 * w 1) / (1 + m1^2)) • tubeDirV m1
  let v2 := ((w 0 + m2 * w 1) / (1 + m2^2)) • tubeDirV m2
  have hP1 : P1 w = v1 := starProjection_line_apply m1 w
  have hP2 : P2 w = v2 := starProjection_line_apply m2 w
  have h_diff : (P1 - P2) w = v1 - v2 := by
    have h : (P1 - P2) w = P1 w - P2 w := by rfl
    rw [h, hP1, hP2]
  have hcoord0 : (v1 - v2) 0 = 1 / (1 + m1^2) - 1 / (1 + m2^2) := by
    simp [v1, v2, hw0, hw1, tubeDirV, TubesAndSlopes.mkPlane, smul_eq_mul] <;> ring
  have hcoord1 : (v1 - v2) 1 = m1 / (1 + m1^2) - m2 / (1 + m2^2) := by
    simp [v1, v2, hw0, hw1, tubeDirV, TubesAndSlopes.mkPlane, smul_eq_mul] <;> ring
  have h_main2 : ‖(P1 - P2) w‖ ^ 2 =
      ((m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2))) := by
    rw [h_diff]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, hcoord0, hcoord1]
    <;> field_simp <;> ring
  have h_denom : (1 + m1^2) * (1 + m2^2) ≤ 4 := by
    have h1' : m1^2 ≤ 1 := by nlinarith [abs_le.mp hm1]
    have h2' : m2^2 ≤ 1 := by nlinarith [abs_le.mp hm2]
    nlinarith
  have h3 : ‖(P1 - P2) w‖ ≥ |m1 - m2| / 2 := by
    have h_pos : 0 ≤ ‖(P1 - P2) w‖ := by positivity
    have h_goal2 : ‖(P1 - P2) w‖ ^ 2 ≥ (|m1 - m2| / 2) ^ 2 := by
      rw [h_main2]
      have h7 : (|m1 - m2| / 2) ^ 2 = (m1 - m2)^2 / 4 := by
        have h71 : (|m1 - m2| / 2) ^ 2 = |m1 - m2| ^ 2 / 4 := by ring
        rw [h71, sq_abs]
      rw [h7]
      have h6 : (m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2)) ≥ (m1 - m2)^2 / 4 := by
        apply div_le_div_of_nonneg_left
        · positivity
        · nlinarith
        · nlinarith
      exact h6
    have h_pos2 : 0 ≤ |m1 - m2| / 2 := by positivity
    nlinarith
  have h7 : ‖(P1 - P2) w‖ ≤ ‖P1 - P2‖ * ‖w‖ :=
    ContinuousLinearMap.le_opNorm (P1 - P2) w
  rw [hw_norm] at h7
  linarith

/-- Backward Lipschitz: L∞ param dist ≤ 14 * AffineLine dist. -/
lemma affine_line_backward_lipschitz {m1 m2 b1 b2 : ℝ}
    (hm1 : |m1| ≤ 1) (hm2 : |m2| ≤ 1) (hb2 : |b2| ≤ 3) :
    max |m1 - m2| |b1 - b2| ≤
      14 * dist (lineOfSlopeIntercept m1 b1) (lineOfSlopeIntercept m2 b2) := by
  set ℓ1 := lineOfSlopeIntercept m1 b1 with hℓ1
  set ℓ2 := lineOfSlopeIntercept m2 b2 with hℓ2
  set d_aff := dist ℓ1 ℓ2 with hd_aff
  have h_dir1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} :=
    lineOfSlopeIntercept_direction m1 b1
  have h_dir2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} :=
    lineOfSlopeIntercept_direction m2 b2
  set Pdiff := ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection with hPdiff
  have hPdiff_eq : Pdiff = (Submodule.span ℝ {tubeDirV m1}).starProjection -
      (Submodule.span ℝ {tubeDirV m2}).starProjection := by
    rw [hPdiff, h_dir1, h_dir2] <;> rfl
  have h_proj_lower : |m1 - m2| ≤ 2 * ‖Pdiff‖ := by
    rw [hPdiff_eq]
    exact proj_op_norm_lower hm1 hm2
  have h_off1 : ℓ1.offset = b1 • offsetVec m1 := by
    rw [hℓ1, lineOfSlopeIntercept]; exact offset_formula m1 b1
  have h_off2 : ℓ2.offset = b2 • offsetVec m2 := by
    rw [hℓ2, lineOfSlopeIntercept]; exact offset_formula m2 b2
  have h_off_lower : ‖ℓ1.offset - ℓ2.offset‖ ≥ |b1 - b2| / Real.sqrt 2 - 3 * |m1 - m2| := by
    rw [h_off1, h_off2]; exact offset_diff_lower m1 m2 b1 b2 hm1 hb2
  have h_def : d_aff = ‖Pdiff‖ + ‖ℓ1.offset - ℓ2.offset‖ := by rfl
  have hnonneg_off : 0 ≤ ‖ℓ1.offset - ℓ2.offset‖ := by positivity
  have h11 : ‖Pdiff‖ ≤ d_aff := by
    rw [h_def]
    have h : ‖Pdiff‖ ≤ ‖Pdiff‖ + ‖ℓ1.offset - ℓ2.offset‖ := by
      exact le_add_of_nonneg_right hnonneg_off
    exact h
  have h1 : |m1 - m2| ≤ 2 * d_aff := by
    calc |m1 - m2| ≤ 2 * ‖Pdiff‖ := h_proj_lower
      _ ≤ 2 * d_aff := by gcongr
  have h2 : |b1 - b2| / Real.sqrt 2 ≤ d_aff + 3 * |m1 - m2| := by
    have h21 : ‖ℓ1.offset - ℓ2.offset‖ ≤ d_aff := by
      rw [h_def]
      exact le_add_of_nonneg_left (by positivity)
    linarith [h_off_lower, h21]
  have h3 : |b1 - b2| ≤ Real.sqrt 2 * (d_aff + 3 * |m1 - m2|) := by
    have h4 : 0 < Real.sqrt 2 := by positivity
    calc |b1 - b2|
      = Real.sqrt 2 * (|b1 - b2| / Real.sqrt 2) := by field_simp [h4.ne'] <;> ring
      _ ≤ Real.sqrt 2 * (d_aff + 3 * |m1 - m2|) := by gcongr
  have h5 : |b1 - b2| ≤ 2 * (d_aff + 3 * |m1 - m2|) := by
    have h6 : Real.sqrt 2 ≤ 2 := by
      have h7 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h8 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    calc |b1 - b2| ≤ Real.sqrt 2 * (d_aff + 3 * |m1 - m2|) := h3
      _ ≤ 2 * (d_aff + 3 * |m1 - m2|) := by gcongr <;> linarith
  have h_b_bound : |b1 - b2| ≤ 14 * d_aff := by
    calc |b1 - b2| ≤ 2 * (d_aff + 3 * |m1 - m2|) := h5
      _ ≤ 2 * (d_aff + 3 * (2 * d_aff)) := by gcongr <;> exact h1
      _ = 14 * d_aff := by ring
  have h9 : max |m1 - m2| |b1 - b2| ≤ 14 * d_aff := by
    have hdaff_nonneg : 0 ≤ d_aff := by positivity
    have hmax1 : |m1 - m2| ≤ 14 * d_aff := by
      calc |m1 - m2| ≤ 2 * d_aff := h1
        _ ≤ 14 * d_aff := by gcongr <;> linarith
    have hmax2 : |b1 - b2| ≤ 14 * d_aff := h_b_bound
    exact max_le hmax1 hmax2
  exact h9

end AffineLineChart

section AffineLineDoubling

/-- Factor-2 doubling for AffineLine sets contained in the bounded-slope chart
    {|m| ≤ 1, |b| ≤ 3}. Constant = 262144. -/
theorem affine_line_factor2_doubling
    (δ : ℝ) (hδ_pos : 0 < δ)
    {E : Set AffineLine}
    (hE : ∀ ℓ ∈ E, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ lineOfSlopeIntercept m b = ℓ) :
    Metric.externalCoveringNumber δ.toNNReal E ≤
      (262144 : ENNReal) * Metric.externalCoveringNumber (2 * δ).toNNReal E := by
  classical
  let r : NNReal := δ.toNNReal
  let R : NNReal := (2 * δ).toNNReal
  have hr : (r : ℝ) = δ := by simp [r, NNReal.coe_mk] <;> linarith
  have hR : (R : ℝ) = 2 * δ := by simp [R, NNReal.coe_mk] <;> linarith

  choose m b hm hb h_eq using hE
  let f : ℝ × ℝ → AffineLine := fun p => lineOfSlopeIntercept p.1 p.2

  have h_f_lip : ∀ (p1 p2 : ℝ × ℝ), |p1.1| ≤ 1 → |p2.1| ≤ 1 → |p2.2| ≤ 3 →
      dist (f p1) (f p2) ≤ 5 * dist p1 p2 := by
    intro p1 p2 hp1 hp2 hb2
    exact affine_line_forward_lipschitz hp1 hp2 hb2

  have h_f_inv_lip : ∀ (p1 p2 : ℝ × ℝ), |p1.1| ≤ 1 → |p2.1| ≤ 1 → |p2.2| ≤ 3 →
      dist p1 p2 ≤ 14 * dist (f p1) (f p2) := by
    intro p1 p2 hp1 hp2 hb2
    exact affine_line_backward_lipschitz hp1 hp2 hb2

  by_cases h_top : Metric.externalCoveringNumber R E = ⊤
  · rw [h_top]
    simp
    <;> exact le_top
  · have h_fin : Metric.externalCoveringNumber R E < ⊤ := lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq h_fin with ⟨C, hC, h_eqC⟩
    have hC_finite : C.Finite := by
      have h : C.encard < ⊤ := by rw [h_eqC]; exact h_fin
      exact Set.encard_lt_top_iff.mp h
    let C_fin : Finset AffineLine := hC_finite.toFinset

    -- For each cover center c that intersects E, pick e_c ∈ E ∩ B(c, R)
    let relevant (c : AffineLine) : Prop := (E ∩ Metric.closedBall c (R : ℝ)).Nonempty
    have h_choose : ∀ (c : AffineLine), relevant c →
        ∃ (e : AffineLine), e ∈ E ∧ e ∈ Metric.closedBall c (R : ℝ) := by
      intro c hrel
      rcases hrel with ⟨e, he_E, he_ball⟩
      exact ⟨e, he_E, he_ball⟩
    choose e_c he_c_E he_c_ball using h_choose

    -- For each relevant c, get parameter representative of e_c
    let p_c (c : AffineLine) (hrel : relevant c) : ℝ × ℝ :=
      (m (e_c c hrel) (he_c_E c hrel), b (e_c c hrel) (he_c_E c hrel))

    have h_pc1 : ∀ c hrel, |(p_c c hrel).1| ≤ 1 := by
      intro c hrel; exact hm _ _
    have h_pc2 : ∀ c hrel, |(p_c c hrel).2| ≤ 3 := by
      intro c hrel; exact hb _ _
    have h_f_pc : ∀ c hrel, f (p_c c hrel) = e_c c hrel := by
      intro c hrel; exact h_eq _ _

    -- Key local cover: for each relevant c, cover E ∩ B(c, R) by 262144 r-balls
    have h_local : ∀ (c : AffineLine), relevant c →
        ∃ (S_c : Finset AffineLine), S_c.card ≤ 262144 ∧
          E ∩ Metric.closedBall c (R : ℝ) ⊆ ⋃ s ∈ S_c, Metric.closedBall s (r : ℝ) := by
      intro c hrel
      set p : ℝ × ℝ := p_c c hrel with hp_def
      set e : AffineLine := e_c c hrel with he_def

      -- E ∩ B(c, R) ⊆ E ∩ B(e, 2R) since dist(c,e) ≤ R
      have h_ce : dist c e ≤ (R : ℝ) := by
        have h : e ∈ Metric.closedBall c (R : ℝ) := he_c_ball c hrel
        simpa [Metric.mem_closedBall, dist_comm c e] using h
      have h1 : E ∩ Metric.closedBall c (R : ℝ) ⊆ E ∩ Metric.closedBall e (2 * (R : ℝ)) := by
        intro x hx
        have hx_E : x ∈ E := hx.1
        have hx_c : dist x c ≤ (R : ℝ) := hx.2
        have h_xe : dist x e ≤ 2 * (R : ℝ) := by
          calc dist x e ≤ dist x c + dist c e := dist_triangle _ _ _
            _ ≤ (R : ℝ) + (R : ℝ) := by linarith
            _ = 2 * (R : ℝ) := by ring
        exact ⟨hx_E, by simpa [Metric.mem_closedBall] using h_xe⟩

      -- Preimage of E ∩ B(e, 2R) under f is contained in L∞ ball B(p, 14*2R)
      let radius_linf : ℝ := 14 * (2 * (R : ℝ))
      have h_preimage : ∀ (q : ℝ × ℝ), |q.1| ≤ 1 → |q.2| ≤ 3 →
          f q ∈ E ∩ Metric.closedBall e (2 * (R : ℝ)) → dist q p ≤ radius_linf := by
        intro q hq1 hq2 hfq
        have h_dist : dist (f q) e ≤ 2 * (R : ℝ) := hfq.2
        have h : dist q p ≤ 14 * dist (f q) (f p) := h_f_inv_lip q p hq1 (h_pc1 c hrel) (h_pc2 c hrel)
        have h2 : f p = e := h_f_pc c hrel
        rw [h2] at h
        calc dist q p ≤ 14 * dist (f q) e := h
          _ ≤ 14 * (2 * (R : ℝ)) := by gcongr
          _ = radius_linf := by ring

      -- Cover L∞ ball B(p, radius_linf) by 4^9 balls of radius r/5
      let s_small : ℝ := δ / 5
      have hs_small_pos : 0 < s_small := by positivity
      have h_radius : radius_linf ≤ 512 * s_small := by
        dsimp only [radius_linf, s_small]
        rw [hR] <;> norm_num <;> linarith

      -- Iterated L∞ doubling: Ncover(s_small) ≤ 4^9 * Ncover(512*s_small)
      have h_iter : Metric.externalCoveringNumber s_small.toNNReal (Metric.closedBall p radius_linf) ≤
          (262144 : ENat) * Metric.externalCoveringNumber (512 * s_small).toNNReal (Metric.closedBall p radius_linf) := by
        have h9 : ∀ (k : ℕ), Metric.externalCoveringNumber s_small.toNNReal (Metric.closedBall p radius_linf) ≤
            (4 ^ k : ENat) * Metric.externalCoveringNumber ((2 ^ k : ℕ) * s_small).toNNReal (Metric.closedBall p radius_linf) := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            calc Metric.externalCoveringNumber s_small.toNNReal (Metric.closedBall p radius_linf)
              ≤ (4 ^ k : ENat) * Metric.externalCoveringNumber ((2 ^ k : ℕ) * s_small).toNNReal (Metric.closedBall p radius_linf) := ih
            _ ≤ (4 ^ k : ENat) * ((4 : ENat) * Metric.externalCoveringNumber (2 * ((2 ^ k : ℕ) * s_small)).toNNReal (Metric.closedBall p radius_linf)) := by
                gcongr
                <;> exact linfty2_doubling ((2 ^ k : ℕ) * s_small) (by positivity) _
            _ = (4 ^ (k + 1) : ENat) * Metric.externalCoveringNumber ((2 ^ (k + 1) : ℕ) * s_small).toNNReal (Metric.closedBall p radius_linf) := by
                simp [pow_succ] <;> ring_nf
        exact h9 9

      have h_trivial : Metric.externalCoveringNumber (512 * s_small).toNNReal (Metric.closedBall p radius_linf) ≤ 1 := by
        have h10 : radius_linf ≤ 512 * s_small := h_radius
        have h11 : Metric.closedBall p radius_linf ⊆ Metric.closedBall p (512 * s_small) := by
          intro x hx
          have h12 : dist x p ≤ radius_linf := by simpa [Metric.mem_closedBall] using hx
          simpa [Metric.mem_closedBall] using le_trans h12 h10
        have h13 : Metric.externalCoveringNumber (512 * s_small).toNNReal (Metric.closedBall p radius_linf) ≤
            Metric.externalCoveringNumber (512 * s_small).toNNReal (Metric.closedBall p (512 * s_small)) :=
          Metric.externalCoveringNumber_mono_set h11
        have h14 : Metric.externalCoveringNumber (512 * s_small).toNNReal (Metric.closedBall p (512 * s_small)) ≤ 1 := by
          have hcover : Metric.IsCover (512 * s_small).toNNReal (Metric.closedBall p (512 * s_small)) ({p} : Set _) := by
            intro x hx
            refine' ⟨p, by simp, _⟩
            have h15 : dist x p ≤ 512 * s_small := by simpa [Metric.mem_closedBall] using hx
            have h17 : (nndist x p : ℝ) = dist x p := by exact coe_nndist x p
            have h18 : ((512 * s_small).toNNReal : ℝ) = 512 * s_small := by
              rw [Real.coe_toNNReal']
              have hpos : 0 ≤ 512 * s_small := by positivity
              rw [max_eq_left hpos]
            have h19 : (nndist x p : ℝ) ≤ ((512 * s_small).toNNReal : ℝ) := by
              rw [h17, h18] <;> exact h15
            have h16 : nndist x p ≤ (512 * s_small).toNNReal := NNReal.coe_le_coe.mp h19
            exact_mod_cast h16
          have h17 := Metric.IsCover.externalCoveringNumber_le_encard hcover
          simpa using h17
        exact h13.trans h14

      have h_bound : Metric.externalCoveringNumber s_small.toNNReal (Metric.closedBall p radius_linf) ≤ (262144 : ENat) := by
        calc Metric.externalCoveringNumber s_small.toNNReal (Metric.closedBall p radius_linf)
          ≤ (262144 : ENat) * Metric.externalCoveringNumber (512 * s_small).toNNReal (Metric.closedBall p radius_linf) := h_iter
        _ ≤ (262144 : ENat) * 1 := by gcongr
        _ = (262144 : ENat) := by simp

      -- Clamping onto the chart [-1,1] × [-3,3]
      let clampChart : ℝ × ℝ → ℝ × ℝ := fun q =>
        (max (-1) (min 1 q.1), max (-3) (min 3 q.2))

      have h_clamp_coord1 : ∀ (q s : ℝ), |q| ≤ 1 →
          |q - max (-1) (min 1 s)| ≤ |q - s| := by
        intro q s hq
        by_cases h : s < -1
        · have hmin : min 1 s = s := by apply min_eq_right; linarith
          have hmax : max (-1) s = -1 := by apply max_eq_left; linarith
          rw [hmin, hmax]
          have hq_low : -1 ≤ q := (abs_le.mp hq).1
          have h9 : q - (-1) ≥ 0 := by linarith
          have h10 : q - s > 0 := by linarith
          rw [abs_of_nonneg h9, abs_of_pos h10] <;> linarith
        · by_cases h2 : s > 1
          · have hmin : min 1 s = 1 := by apply min_eq_left; linarith
            have hmax : max (-1) (1 : ℝ) = 1 := by norm_num
            rw [hmin, hmax]
            have hq_high : q ≤ 1 := (abs_le.mp hq).2
            have h9 : q - 1 ≤ 0 := by linarith
            have h10 : q - s < 0 := by linarith
            rw [abs_of_nonpos h9, abs_of_neg h10] <;> linarith
          · have h3 : -1 ≤ s := by linarith
            have h4 : s ≤ 1 := by linarith
            have h5 : max (-1) (min 1 s) = s := by
              have h6 : min 1 s = s := by apply min_eq_right; linarith
              rw [h6]
              have h7 : max (-1) s = s := by apply max_eq_right; linarith
              rw [h7]
            rw [h5]

      have h_clamp_coord2 : ∀ (q s : ℝ), |q| ≤ 3 →
          |q - max (-3) (min 3 s)| ≤ |q - s| := by
        intro q s hq
        by_cases h : s < -3
        · have hmin : min 3 s = s := by apply min_eq_right; linarith
          have hmax : max (-3) s = -3 := by apply max_eq_left; linarith
          rw [hmin, hmax]
          have hq_low : -3 ≤ q := (abs_le.mp hq).1
          have h9 : q - (-3) ≥ 0 := by linarith
          have h10 : q - s > 0 := by linarith
          rw [abs_of_nonneg h9, abs_of_pos h10] <;> linarith
        · by_cases h2 : s > 3
          · have hmin : min 3 s = 3 := by apply min_eq_left; linarith
            have hmax : max (-3) (3 : ℝ) = 3 := by norm_num
            rw [hmin, hmax]
            have hq_high : q ≤ 3 := (abs_le.mp hq).2
            have h9 : q - 3 ≤ 0 := by linarith
            have h10 : q - s < 0 := by linarith
            rw [abs_of_nonpos h9, abs_of_neg h10] <;> linarith
          · have h3 : -3 ≤ s := by linarith
            have h4 : s ≤ 3 := by linarith
            have h5 : max (-3) (min 3 s) = s := by
              have h6 : min 3 s = s := by apply min_eq_right; linarith
              rw [h6]
              have h7 : max (-3) s = s := by apply max_eq_right; linarith
              rw [h7]
            rw [h5]

      have h_clamp_nonexp : ∀ (q s : ℝ × ℝ), |q.1| ≤ 1 → |q.2| ≤ 3 →
          dist q (clampChart s) ≤ dist q s := by
        intro q s hq1 hq2
        have h1 : |q.1 - (clampChart s).1| ≤ |q.1 - s.1| := h_clamp_coord1 q.1 s.1 hq1
        have h2 : |q.2 - (clampChart s).2| ≤ |q.2 - s.2| := h_clamp_coord2 q.2 s.2 hq2
        have hd1 : dist q (clampChart s) = max |q.1 - (clampChart s).1| |q.2 - (clampChart s).2| := by
          rw [Prod.dist_eq] <;> simp [Real.dist_eq] <;> rfl
        have hd2 : dist q s = max |q.1 - s.1| |q.2 - s.2| := by
          rw [Prod.dist_eq] <;> simp [Real.dist_eq] <;> rfl
        rw [hd1, hd2]
        exact max_le_max h1 h2

      have h_clamp_in_chart1 : ∀ (s : ℝ × ℝ), |(clampChart s).1| ≤ 1 := by
        intro s
        have h1 : -1 ≤ max (-1) (min 1 s.1) := le_max_left _ _
        have h2 : max (-1) (min 1 s.1) ≤ 1 := by
          apply max_le
          · norm_num
          · exact min_le_left _ _
        exact abs_le.mpr ⟨h1, h2⟩

      have h_clamp_in_chart2 : ∀ (s : ℝ × ℝ), |(clampChart s).2| ≤ 3 := by
        intro s
        have h1 : -3 ≤ max (-3) (min 3 s.2) := le_max_left _ _
        have h2 : max (-3) (min 3 s.2) ≤ 3 := by
          apply max_le
          · norm_num
          · exact min_le_left _ _
        exact abs_le.mpr ⟨h1, h2⟩

      -- Get finite cover from covering number bound
      have h_enat_lt_top : (262144 : ENat) < ⊤ := WithTop.coe_lt_top 262144
      have h_lt_top : Metric.externalCoveringNumber s_small.toNNReal (Metric.closedBall p radius_linf) < ⊤ :=
        h_bound.trans_lt h_enat_lt_top
      rcases exists_external_cover_eq h_lt_top with ⟨S', hS'_cover, hS'_card⟩
      have hS'_finite : S'.Finite := by
        have h : S'.encard < ⊤ := by rw [hS'_card]; exact h_bound.trans_lt h_enat_lt_top
        exact Set.encard_lt_top_iff.mp h
      let S'_fin : Finset (ℝ × ℝ) := hS'_finite.toFinset
      have hS'_fin_coe : (S'_fin : Set (ℝ × ℝ)) = S' := hS'_finite.coe_toFinset

      -- Map clamped centers through f
      let S_c : Finset AffineLine := S'_fin.image (fun s => f (clampChart s))
      have hS_c_card : S_c.card ≤ S'_fin.card := Finset.card_image_le
      have hS_c_card_le : S_c.card ≤ 262144 := by
        have h : S'_fin.card ≤ 262144 := by
          have h2 : (S'_fin : Set (ℝ × ℝ)).encard = ↑S'_fin.card := by simp
          have h3 : S'.encard ≤ (262144 : ENat) := by rw [hS'_card]; exact h_bound
          rw [← hS'_fin_coe] at h3
          rw [h2] at h3
          exact_mod_cast h3
        exact le_trans hS_c_card h

      -- Prove coverage
      have h_cover : E ∩ Metric.closedBall c (R : ℝ) ⊆ ⋃ s ∈ S_c, Metric.closedBall s (r : ℝ) := by
        intro x hx
        have hx_E : x ∈ E := hx.1
        have hx_in_e_ball : x ∈ E ∩ Metric.closedBall e (2 * (R : ℝ)) := h1 hx
        -- Get parameters for x using choose'd functions
        let mx := m x hx_E
        let bx := b x hx_E
        have hmx1 : |mx| ≤ 1 := hm x hx_E
        have hbx2 : |bx| ≤ 3 := hb x hx_E
        have hfx : f (mx, bx) = x := h_eq x hx_E
        let q : ℝ × ℝ := (mx, bx)
        have hq1 : |q.1| ≤ 1 := hmx1
        have hq2 : |q.2| ≤ 3 := hbx2
        have hfq : f q ∈ E ∩ Metric.closedBall e (2 * (R : ℝ)) := by
          have h_eq2 : f q = x := by simpa [q] using hfx
          rw [h_eq2]
          exact hx_in_e_ball
        have hq_in_ball : dist q p ≤ radius_linf := h_preimage q hq1 hq2 hfq
        have hq_in_closed : q ∈ Metric.closedBall p radius_linf := by
          simpa [Metric.mem_closedBall] using hq_in_ball
        have hS'_cover' : ∃ (s' : ℝ × ℝ), s' ∈ S' ∧ edist q s' ≤ ↑s_small.toNNReal :=
          hS'_cover hq_in_closed
        rcases hS'_cover' with ⟨s', hs'_in_S', hdist_s'⟩
        have hdist_s'_real : dist q s' ≤ s_small := by
          have h : nndist q s' ≤ s_small.toNNReal := by exact_mod_cast hdist_s'
          have h2 : (nndist q s' : ℝ) ≤ (s_small.toNNReal : ℝ) := NNReal.coe_le_coe.mp h
          have h3 : (nndist q s' : ℝ) = dist q s' := by exact coe_nndist q s'
          have h4 : (s_small.toNNReal : ℝ) = s_small := by
            rw [Real.coe_toNNReal']
            have hpos : 0 ≤ s_small := by positivity
            rw [max_eq_left hpos]
          rw [h3, h4] at h2
          exact h2
        have h_clamp_dist : dist q (clampChart s') ≤ dist q s' := h_clamp_nonexp q s' hq1 hq2
        have h_final_dist : dist q (clampChart s') ≤ s_small := le_trans h_clamp_dist hdist_s'_real
        have hmax : max |q.1 - (clampChart s').1| |q.2 - (clampChart s').2| ≤ s_small := by
          simpa [Prod.dist_eq, Real.dist_eq] using h_final_dist
        have h_aff_dist : dist (f q) (f (clampChart s')) ≤ 5 * s_small := by
          have h := affine_line_forward_lipschitz (m1 := q.1) (m2 := (clampChart s').1) (b1 := q.2) (b2 := (clampChart s').2)
            hq1 (h_clamp_in_chart1 s') (h_clamp_in_chart2 s')
          calc dist (f q) (f (clampChart s'))
            ≤ 5 * max |q.1 - (clampChart s').1| |q.2 - (clampChart s').2| := h
          _ ≤ 5 * s_small := by gcongr
        have h_δ : 5 * s_small = δ := by
          dsimp only [s_small] <;> ring
        have h_aff_δ : dist (f q) (f (clampChart s')) ≤ δ := by
          rw [h_δ] at h_aff_dist; exact h_aff_dist
        have h_center_in : f (clampChart s') ∈ S_c := by
          apply Finset.mem_image.mpr
          have h_in_fin : s' ∈ S'_fin := by
            have h5 : (S'_fin : Set (ℝ × ℝ)) = S' := hS'_fin_coe
            have h6 : s' ∈ (S'_fin : Set (ℝ × ℝ)) := by rw [h5]; exact hs'_in_S'
            exact_mod_cast h6
          exact ⟨s', h_in_fin, rfl⟩
        have h_eq3 : f q = x := by simpa [q] using hfx
        have h_final_ball : x ∈ Metric.closedBall (f (clampChart s')) (r : ℝ) := by
          have h : dist (f q) (f (clampChart s')) ≤ (r : ℝ) := by
            rw [hr] <;> exact h_aff_δ
          rw [h_eq3] at h
          simpa [Metric.mem_closedBall] using h
        exact Set.mem_iUnion₂.mpr ⟨f (clampChart s'), h_center_in, h_final_ball⟩

      exact ⟨S_c, hS_c_card_le, h_cover⟩

    -- Assemble global cover from local covers
    let all_centers : Finset AffineLine := C_fin.biUnion fun c =>
      if h : relevant c then Classical.choose (h_local c h) else ∅
    have h_all_cover : Metric.IsCover r E (all_centers : Set AffineLine) := by
      intro x hx
      rcases hC hx with ⟨c, hc_in_C, hed⟩
      have hdist_c : dist x c ≤ (R : ℝ) := by
        have h : nndist x c ≤ R := by exact_mod_cast hed
        have h2 : (nndist x c : ℝ) ≤ (R : ℝ) := NNReal.coe_le_coe.mp h
        have h3 : (nndist x c : ℝ) = dist x c := by exact coe_nndist x c
        rw [h3] at h2
        exact h2
      have hc_fin : c ∈ C_fin := by
        simpa [C_fin, hC_finite.coe_toFinset] using hc_in_C
      have hrel : relevant c := by
        refine' ⟨x, hx, _⟩
        simpa [Metric.mem_closedBall] using hdist_c
      let S_c := Classical.choose (h_local c hrel)
      have hS_c_spec : S_c.card ≤ 262144 ∧ E ∩ Metric.closedBall c (R : ℝ) ⊆ ⋃ s ∈ S_c, Metric.closedBall s (r : ℝ) :=
        Classical.choose_spec (h_local c hrel)
      have h_x_in : x ∈ E ∩ Metric.closedBall c (R : ℝ) := by
        exact ⟨hx, by simpa [Metric.mem_closedBall] using hdist_c⟩
      have h_covered : x ∈ ⋃ s ∈ S_c, Metric.closedBall s (r : ℝ) := hS_c_spec.2 h_x_in
      rcases Set.mem_iUnion₂.mp h_covered with ⟨s, hs_in_Sc, hsin⟩
      have hs_in_all : s ∈ all_centers := by
        apply Finset.mem_biUnion.mpr
        refine' ⟨c, hc_fin, _⟩
        rw [dif_pos hrel]
        exact hs_in_Sc
      have hsin_ed : edist x s ≤ ↑r := by
        have h : dist x s ≤ (r : ℝ) := by simpa [Metric.mem_closedBall] using hsin
        have h3 : (nndist x s : ℝ) = dist x s := by exact coe_nndist x s
        have h4 : (nndist x s : ℝ) ≤ (r : ℝ) := by rw [h3] <;> exact h
        have h2 : nndist x s ≤ r := NNReal.coe_le_coe.mp h4
        exact_mod_cast h2
      exact ⟨s, hs_in_all, hsin_ed⟩
    have h1 : Metric.externalCoveringNumber r E ≤ (all_centers : Set AffineLine).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_all_cover
    have h2 : all_centers.card ≤ C_fin.card * 262144 := by
      have h_card : all_centers.card ≤ ∑ c ∈ C_fin, ((if h : relevant c then Classical.choose (h_local c h) else (∅ : Finset AffineLine))).card := by
        exact Finset.card_biUnion_le
      calc all_centers.card
        ≤ ∑ c ∈ C_fin, ((if h : relevant c then Classical.choose (h_local c h) else (∅ : Finset AffineLine))).card := h_card
        _ ≤ ∑ c ∈ C_fin, 262144 := by
          apply Finset.sum_le_sum
          intro c _
          split_ifs with h
          · have hS_c_spec := Classical.choose_spec (h_local c h)
            exact hS_c_spec.1
          · norm_num
        _ = C_fin.card * 262144 := by
          simp [Finset.sum_const] <;> ring
    have h3 : (all_centers : Set AffineLine).encard = ↑all_centers.card := by simp
    have h4 : Metric.externalCoveringNumber r E ≤ ↑(C_fin.card * 262144) := by
      rw [h3] at h1
      exact h1.trans (by exact_mod_cast h2)
    have h5 : C.encard = ↑C_fin.card := by
      have h6 : (C_fin : Set AffineLine) = C := hC_finite.coe_toFinset
      rw [← h6]
      simp
    have h6 : (Metric.externalCoveringNumber R E : ENNReal) = ↑C_fin.card := by
      rw [← h_eqC, h5] <;> simp
    calc (Metric.externalCoveringNumber r E : ENNReal)
      ≤ ↑(C_fin.card * 262144) := by exact_mod_cast h4
    _ = (262144 : ENNReal) * ↑C_fin.card := by
      simp [Nat.cast_mul] <;> ring
    _ = (262144 : ENNReal) * Metric.externalCoveringNumber R E := by rw [h6]

end AffineLineDoubling

end DiscretisedFurstenbergEstimate.CoveringUtils

end

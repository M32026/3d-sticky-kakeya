module

/-
  A9 Support: affine normalization map and affine line geometry helpers.

  Extracted from A9_Helpers for compilation performance.
  Contains: AffineNormalization namespace, A9Support namespace.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.CoarseParamsSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate

open LemmaE
open DiscretisedFurstenbergEstimate.CoveringUtils
open TubesAndSlopes

/-! ========================================================================
   Affine normalization map and its properties
   ======================================================================== -/

namespace AffineNormalization

abbrev Plane := EuclideanPlane

/-- The affine normalization map sending line x = σ*y + b to x' = 0. -/
def normalizeMap (σ b : ℝ) (p : Plane) : Plane :=
  WithLp.toLp 2 fun i : Fin 2 =>
    if i = 0 then p 0 - σ * p 1 - b else p 1

/-- Inverse of normalizeMap. -/
def denormalizeMap (σ b : ℝ) (q : Plane) : Plane :=
  WithLp.toLp 2 fun i : Fin 2 =>
    if i = 0 then q 0 + σ * q 1 + b else q 1

lemma normalizeMap_left_inverse (σ b : ℝ) :
    Function.LeftInverse (denormalizeMap σ b) (normalizeMap σ b) := by
  intro p
  ext i
  fin_cases i <;> simp [normalizeMap, denormalizeMap] <;> ring

lemma normalizeMap_right_inverse (σ b : ℝ) :
    Function.RightInverse (denormalizeMap σ b) (normalizeMap σ b) := by
  intro q
  ext i
  fin_cases i <;> simp [normalizeMap, denormalizeMap] <;> ring

lemma normalizeMap_injective (σ b : ℝ) :
    Function.Injective (normalizeMap σ b) :=
  (normalizeMap_left_inverse σ b).injective

end AffineNormalization

/-! ========================================================================
   A9Support: metric transfer lemma
   ======================================================================== -/

namespace A9Support

open DirecretisedFurstenbergEstimate.AppendixA

abbrev Plane := EuclideanPlane

/-- Lipschitz transfer for affine lines with bounded parameters.
    If both lines have nonzero y-direction and |slope|≤1, |intercept|≤3,
    then dist(params) ≤ 8 * dist(lines). -/
lemma bounded_metric_transfer (ℓ₁ ℓ₂ : AffineLine)
    (hv1 : (getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (getDirV ℓ₂) 1 ≠ 0)
    (ha1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (ha2 : |(affineLineParams ℓ₂).1| ≤ 1)
    (hb1 : |(affineLineParams ℓ₁).2| ≤ 3)
    (hb2 : |(affineLineParams ℓ₂).2| ≤ 3) :
    dist (affineLineParams ℓ₁) (affineLineParams ℓ₂) ≤ 8 * dist ℓ₁ ℓ₂ :=
  AffineLineLipschitzTransfer.affineLineParams_lipschitz_upper
    ℓ₁ ℓ₂ hv1 hv2 ha1 ha2 hb1 hb2

/-- If a line's direction has zero y-component (horizontal), its starProjection kills e2. -/
lemma horizontal_starProjection_kills_e2 (ℓ : AffineLine)
    (hv1 : (getDirV ℓ) 1 = 0) :
    ℓ.1.direction.starProjection (TubesAndSlopes.e2) = 0 := by
  let v := getDirV ℓ
  have hv_in_dir : v ∈ ℓ.1.direction := (getDirV_spec ℓ).1
  have hv_ne_zero : v ≠ 0 := (getDirV_spec ℓ).2
  have h_dir_eq : ℓ.1.direction = Submodule.span ℝ {v} := by
    have h_span : Submodule.span ℝ {v} ≤ ℓ.1.direction := by
      apply Submodule.span_le.mpr; intro x hx; simpa [Set.mem_singleton_iff] using hx ▸ hv_in_dir
    have h1 : Module.finrank ℝ ℓ.1.direction = 1 := ℓ.2
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 := by
      simp [hv_ne_zero, finrank_span_singleton]
    have h3 : Module.finrank ℝ (Submodule.span ℝ {v}) = Module.finrank ℝ ℓ.1.direction := by rw [h2, h1]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h3).symm
  have h_inner : inner ℝ TubesAndSlopes.e2 v = 0 := by
    have h : inner ℝ TubesAndSlopes.e2 v = v 1 := by
      have h_sum : inner ℝ TubesAndSlopes.e2 v = ∑ i : Fin 2, inner ℝ (TubesAndSlopes.e2 i) (v i) := PiLp.inner_apply _ _
      rw [h_sum, Fin.sum_univ_two]
      have h4 := TubesAndSlopes.e2_apply
      simp [h4.1, h4.2] <;> ring
    rw [h, hv1] <;> ring
  have h_orth : ∀ w ∈ ℓ.1.direction, inner ℝ TubesAndSlopes.e2 w = 0 := by
    rw [h_dir_eq]
    intro w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    rw [inner_smul_right]
    rw [h_inner] <;> ring
  have h_in_orth : TubesAndSlopes.e2 ∈ ℓ.1.directionᗮ := by
    simpa [Submodule.mem_orthogonal] using fun w hw => by
      have h' := h_orth w hw
      have h'' : inner ℝ w TubesAndSlopes.e2 = inner ℝ TubesAndSlopes.e2 w :=
        (real_inner_comm w TubesAndSlopes.e2).symm
      rw [h'']
      exact h'
  exact (Submodule.starProjection_apply_eq_zero_iff (K := ℓ.1.direction)).mpr h_in_orth

/-- If ℓ₁ has nonzero y-direction and |slope| ≤ 1, and dist(ℓ₁, ℓ₂) ≤ Δ < 1/2,
    then ℓ₂ also has nonzero y-direction. -/
lemma dirV_nonzero_of_close (ℓ₁ ℓ₂ : AffineLine) (Δ : ℝ)
    (hΔ_lt_half : Δ < 1 / 2)
    (h_dist : dist ℓ₁ ℓ₂ ≤ Δ)
    (hv1 : (getDirV ℓ₁) 1 ≠ 0)
    (ha1 : |tubeSlope ℓ₁| ≤ 1) :
    (getDirV ℓ₂) 1 ≠ 0 := by
  by_contra hv2
  let P1 := ℓ₁.1.direction.starProjection
  let P2 := ℓ₂.1.direction.starProjection
  have hP1 := TubesAndSlopes.starProjection_e2_semicircle ℓ₁ hv1
  have hP2 : P2 TubesAndSlopes.e2 = 0 := horizontal_starProjection_kills_e2 ℓ₂ hv2
  set a1 := tubeSlope ℓ₁ with ha1_def
  have h_a1_sq : a1^2 ≤ 1 := by nlinarith [abs_le.mp ha1]
  have h_y1 : (P1 TubesAndSlopes.e2) 1 = 1 / (1 + a1^2) := hP1.2
  have h_y2 : (P2 TubesAndSlopes.e2) 1 = 0 := by rw [hP2] <;> simp
  have h_diff : ((P1 - P2) TubesAndSlopes.e2) 1 = 1 / (1 + a1^2) := by
    simp [h_y1, h_y2] <;> ring
  have h_half : 1 / (1 + a1^2) ≥ 1 / 2 := by
    have h : 1 + a1^2 ≤ 2 := by nlinarith
    gcongr
  have h_coord : |((P1 - P2) TubesAndSlopes.e2) 1| ≥ 1 / 2 := by
    rw [h_diff]
    have h_pos : 0 < 1 / (1 + a1^2) := by positivity
    rw [abs_of_pos h_pos]
    linarith
  have h_norm : ‖(P1 - P2) TubesAndSlopes.e2‖ ≥ 1 / 2 := by
    have h : |((P1 - P2) TubesAndSlopes.e2) 1| ≤ ‖(P1 - P2) TubesAndSlopes.e2‖ :=
      TubesAndSlopes.coord_abs_le_norm _ 1
    linarith
  have h_op : ‖P1 - P2‖ ≥ ‖(P1 - P2) TubesAndSlopes.e2‖ := by
    have h : ‖(P1 - P2) TubesAndSlopes.e2‖ ≤ ‖P1 - P2‖ * ‖TubesAndSlopes.e2‖ :=
      ContinuousLinearMap.le_opNorm (P1 - P2) TubesAndSlopes.e2
    rw [TubesAndSlopes.e2_norm] at h
    linarith
  have h_dist' : dist ℓ₁ ℓ₂ ≥ ‖P1 - P2‖ := by
    have h : dist ℓ₁ ℓ₂ = ‖P1 - P2‖ + ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    have h_off_nonneg : 0 ≤ ‖ℓ₁.offset - ℓ₂.offset‖ := by positivity
    linarith [h_off_nonneg]
  have h_contra : dist ℓ₁ ℓ₂ ≥ 1 / 2 := by linarith
  linarith

/-- Distance from point to affine line transfers with the AffineLine distance
    when the point is in the unit ball. -/
lemma point_line_dist_transfer (p : Plane) (ℓ₁ ℓ₂ : AffineLine)
    (hp_norm : ‖p‖ ≤ Real.sqrt 2) :
    Metric.infDist p (ℓ₂.1 : Set Plane) ≤ Metric.infDist p (ℓ₁.1 : Set Plane) + Real.sqrt 2 * dist ℓ₁ ℓ₂ := by
  let P1 := ℓ₁.1.direction.starProjection
  let P2 := ℓ₂.1.direction.starProjection
  let off1 := ℓ₁.offset
  let off2 := ℓ₂.offset
  have hP1_off : P1 off1 = 0 := by
    have h3 : (0 : Plane) - off1 ∈ ℓ₁.1.directionᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal (s := ℓ₁.1) (0 : Plane)
    have h4 : off1 ∈ ℓ₁.1.directionᗮ := by
      have h5 : -((0 : Plane) - off1) = off1 := by simp
      rw [←h5]
      exact ℓ₁.1.directionᗮ.neg_mem h3
    exact (Submodule.starProjection_apply_eq_zero_iff (K := ℓ₁.1.direction)).mpr h4
  have hP2_off : P2 off2 = 0 := by
    have h3 : (0 : Plane) - off2 ∈ ℓ₂.1.directionᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal (s := ℓ₂.1) (0 : Plane)
    have h4 : off2 ∈ ℓ₂.1.directionᗮ := by
      have h5 : -((0 : Plane) - off2) = off2 := by simp
      rw [←h5]
      exact ℓ₂.1.directionᗮ.neg_mem h3
    exact (Submodule.starProjection_apply_eq_zero_iff (K := ℓ₂.1.direction)).mpr h4
  have h_proj1 : ∀ (q : Plane), EuclideanGeometry.orthogonalProjection ℓ₁.1 q = P1 q + off1 := by
    intro q
    have h1 : EuclideanGeometry.orthogonalProjection ℓ₁.1 q =
        P1 (q - off1) + off1 := by
      have h := EuclideanGeometry.orthogonalProjection_apply_mem ℓ₁.1 ℓ₁.offset_mem (p := q)
      have h' : EuclideanGeometry.orthogonalProjection ℓ₁.1 q = off1 + P1 (q - off1) := by
        convert h using 2 <;> simp [P1, vsub_eq_sub] <;> abel
      rw [h'] <;> abel
    rw [h1]
    have h2 : P1 (q - off1) = P1 q - P1 off1 := P1.map_sub q off1
    rw [h2, hP1_off] <;> abel
  have h_proj2 : ∀ (q : Plane), EuclideanGeometry.orthogonalProjection ℓ₂.1 q = P2 q + off2 := by
    intro q
    have h1 : EuclideanGeometry.orthogonalProjection ℓ₂.1 q =
        P2 (q - off2) + off2 := by
      have h := EuclideanGeometry.orthogonalProjection_apply_mem ℓ₂.1 ℓ₂.offset_mem (p := q)
      have h' : EuclideanGeometry.orthogonalProjection ℓ₂.1 q = off2 + P2 (q - off2) := by
        convert h using 2 <;> simp [P2, vsub_eq_sub] <;> abel
      rw [h'] <;> abel
    rw [h1]
    have h2 : P2 (q - off2) = P2 q - P2 off2 := P2.map_sub q off2
    rw [h2, hP2_off] <;> abel
  have h_dist1 : Metric.infDist p (ℓ₁.1 : Set Plane) = ‖p - (P1 p + off1)‖ := by
    have h : Metric.infDist p (ℓ₁.1 : Set Plane) = dist p (EuclideanGeometry.orthogonalProjection ℓ₁.1 p) :=
      (EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ₁.1 p).symm
    rw [h]
    have h2 : dist p (EuclideanGeometry.orthogonalProjection ℓ₁.1 p) = ‖p - EuclideanGeometry.orthogonalProjection ℓ₁.1 p‖ := by
      simp [dist_eq_norm]
    rw [h2, h_proj1 p]
  have h_dist2 : Metric.infDist p (ℓ₂.1 : Set Plane) = ‖p - (P2 p + off2)‖ := by
    have h : Metric.infDist p (ℓ₂.1 : Set Plane) = dist p (EuclideanGeometry.orthogonalProjection ℓ₂.1 p) :=
      (EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ₂.1 p).symm
    rw [h]
    have h2 : dist p (EuclideanGeometry.orthogonalProjection ℓ₂.1 p) = ‖p - EuclideanGeometry.orthogonalProjection ℓ₂.1 p‖ := by
      simp [dist_eq_norm]
    rw [h2, h_proj2 p]
  rw [h_dist2]
  have h_eq : ‖p - (P2 p + off2)‖ =
      ‖(p - (P1 p + off1)) + (P1 p - P2 p) + (off1 - off2)‖ := by
    have h_vec : p - (P2 p + off2) = (p - (P1 p + off1)) + (P1 p - P2 p) + (off1 - off2) := by
      ext i
      simp [sub_eq_add_neg] <;> ring
    rw [h_vec]
  calc ‖p - (P2 p + off2)‖
    = ‖(p - (P1 p + off1)) + (P1 p - P2 p) + (off1 - off2)‖ := h_eq
  _ ≤ ‖p - (P1 p + off1)‖ + ‖(P1 - P2) p‖ + ‖off1 - off2‖ := by
    have h_tri : ‖(p - (P1 p + off1)) + ((P1 - P2) p) + (off1 - off2)‖ ≤
        ‖p - (P1 p + off1)‖ + ‖(P1 - P2) p‖ + ‖off1 - off2‖ := by
      calc ‖(p - (P1 p + off1)) + ((P1 - P2) p) + (off1 - off2)‖
        ≤ ‖(p - (P1 p + off1)) + ((P1 - P2) p)‖ + ‖off1 - off2‖ := norm_add_le _ _
      _ ≤ ‖p - (P1 p + off1)‖ + ‖(P1 - P2) p‖ + ‖off1 - off2‖ := by
        have h2 : ‖(p - (P1 p + off1)) + ((P1 - P2) p)‖ ≤
            ‖p - (P1 p + off1)‖ + ‖(P1 - P2) p‖ := norm_add_le _ _
        linarith
    exact h_tri
  _ ≤ ‖p - (P1 p + off1)‖ + ‖P1 - P2‖ * ‖p‖ + ‖off1 - off2‖ := by
    gcongr
    exact ContinuousLinearMap.le_opNorm (P1 - P2) p
  _ ≤ ‖p - (P1 p + off1)‖ + Real.sqrt 2 * ‖P1 - P2‖ + ‖off1 - off2‖ := by
    have h_norm_p : ‖p‖ ≤ Real.sqrt 2 := hp_norm
    have h_nonneg : 0 ≤ ‖P1 - P2‖ := by positivity
    have h_mul : ‖P1 - P2‖ * ‖p‖ ≤ Real.sqrt 2 * ‖P1 - P2‖ := by
      calc ‖P1 - P2‖ * ‖p‖
        ≤ ‖P1 - P2‖ * Real.sqrt 2 := by gcongr
        _ = Real.sqrt 2 * ‖P1 - P2‖ := by ring
    linarith
  _ ≤ Metric.infDist p (ℓ₁.1 : Set Plane) + Real.sqrt 2 * dist ℓ₁ ℓ₂ := by
    rw [h_dist1]
    have h_dist_eq : ‖P1 - P2‖ + ‖off1 - off2‖ = dist ℓ₁ ℓ₂ := by
      dsimp only [P1, P2, off1, off2, AffineLine.dist]
      <;> rfl
    have h_goal : ‖p - (P1 p + off1)‖ + Real.sqrt 2 * ‖P1 - P2‖ + ‖off1 - off2‖ ≤
        ‖p - (P1 p + off1)‖ + Real.sqrt 2 * dist ℓ₁ ℓ₂ := by
      have h_dist_eq : ‖P1 - P2‖ + ‖off1 - off2‖ = dist ℓ₁ ℓ₂ := by
        dsimp only [P1, P2, off1, off2, AffineLine.dist] <;> rfl
      have h : Real.sqrt 2 * ‖P1 - P2‖ + ‖off1 - off2‖ ≤ Real.sqrt 2 * (‖P1 - P2‖ + ‖off1 - off2‖) := by
        have h2 : 0 ≤ ‖off1 - off2‖ := by positivity
        have h_sqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
          apply Real.le_sqrt_of_sq_le <;> norm_num
        have h3 : ‖off1 - off2‖ ≤ Real.sqrt 2 * ‖off1 - off2‖ := by
          calc ‖off1 - off2‖
            = 1 * ‖off1 - off2‖ := by ring
          _ ≤ Real.sqrt 2 * ‖off1 - off2‖ := by gcongr <;> linarith
        linarith
      rw [h_dist_eq] at *
      <;> linarith
    exact h_goal

/-- Intercept bound from a nearby point in the unit ball. -/
lemma intercept_bound_from_nearby (p : Plane) (ℓ : AffineLine) (r : ℝ)
    (hp_ball : p ∈ Metric.closedBall (0 : Plane) (Real.sqrt 2))
    (h_dist : Metric.infDist p (ℓ.1 : Set Plane) ≤ r)
    (hv : (getDirV ℓ) 1 ≠ 0)
    (ha : |tubeSlope ℓ| ≤ 1) :
    |tubeIntercept ℓ| ≤ 2 + Real.sqrt 2 * r := by
  set a := tubeSlope ℓ with ha_def
  set b := tubeIntercept ℓ with hb_def
  set off := ℓ.offset with hoff_def
  have h_off_dist : ‖off‖ = Metric.infDist (0 : Plane) (ℓ.1 : Set Plane) := by
    have h : Metric.infDist (0 : Plane) (ℓ.1 : Set Plane) = dist (0 : Plane) off :=
      (EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 (0 : Plane)).symm
    have h2 : dist (0 : Plane) off = ‖off‖ := by
      simp [dist_eq_norm]
    linarith
  have h_p_norm : ‖p‖ ≤ Real.sqrt 2 := by
    simpa [Metric.mem_closedBall] using hp_ball
  have h0_dist : Metric.infDist (0 : Plane) (ℓ.1 : Set Plane) ≤ ‖p‖ + Metric.infDist p (ℓ.1 : Set Plane) := by
    have h : Metric.infDist (0 : Plane) (ℓ.1 : Set Plane) ≤ Metric.infDist p (ℓ.1 : Set Plane) + dist (0 : Plane) p :=
      Metric.infDist_le_infDist_add_dist (x := (0 : Plane)) (y := p) (s := (ℓ.1 : Set Plane))
    have h2 : dist (0 : Plane) p = ‖p‖ := by simp [dist_eq_norm]
    rw [h2] at h
    linarith
  have h_off_norm : ‖off‖ ≤ Real.sqrt 2 + r := by
    rw [h_off_dist]
    linarith [h_p_norm, h_dist]
  have h_off_norm_sq : ‖off‖ ^ 2 = b ^ 2 / (1 + a ^ 2) := by
    have h1 : off 0 = b / (1 + a^2) := by
      simpa [a, b, tubeSlope, tubeIntercept] using TubesAndSlopes.offset_formula ℓ hv |>.1
    have h2 : off 1 = -a * b / (1 + a^2) := by
      simpa [a, b, tubeSlope, tubeIntercept] using TubesAndSlopes.offset_formula ℓ hv |>.2
    have h3 : ‖off‖ ^ 2 = (off 0)^2 + (off 1)^2 := by
      have h_norm2 : ‖off‖ ^ 2 = ∑ i : Fin 2, (off i)^2 := by
        have h4 : ‖off‖ = Real.sqrt (∑ i : Fin 2, |off i|^2) := by
          simpa [EuclideanSpace.norm_eq] using rfl
        rw [h4]
        have h5 : 0 ≤ ∑ i : Fin 2, |off i|^2 := by positivity
        rw [Real.sq_sqrt h5]
        apply Finset.sum_congr rfl
        intro i _
        simp [sq_abs]
      rw [h_norm2, Fin.sum_univ_two]
    rw [h3, h1, h2]
    <;> field_simp <;> ring
  have h_bound : |b| ≤ Real.sqrt 2 * ‖off‖ := by
    have h4 : 0 ≤ 1 + a^2 := by positivity
    have h5 : b^2 = ‖off‖^2 * (1 + a^2) := by
      have h_eq : ‖off‖^2 = b^2 / (1 + a^2) := h_off_norm_sq
      have h_pos : 0 < 1 + a^2 := by positivity
      field_simp [h_pos.ne'] at h_eq ⊢ <;> linarith
    have h6 : |b|^2 = ‖off‖^2 * (1 + a^2) := by
      rw [show |b|^2 = b^2 from by simp, h5]
    have ha' : |a| ≤ 1 := by simpa [ha_def] using ha
    have h7 : 1 + a^2 ≤ 2 := by
      have h_a2 : a^2 ≤ 1 := by
        rw [abs_le] at ha' <;> nlinarith
      linarith
    have h8 : |b|^2 ≤ 2 * ‖off‖^2 := by
      rw [h6]
      have h10 : ‖off‖^2 * (1 + a^2) ≤ ‖off‖^2 * 2 := by gcongr <;> linarith
      linarith
    have h9 : 0 ≤ |b| := by positivity
    have h10 : 0 ≤ Real.sqrt 2 * ‖off‖ := by positivity
    have h11 : (Real.sqrt 2 * ‖off‖) ^ 2 = 2 * ‖off‖^2 := by
      calc (Real.sqrt 2 * ‖off‖) ^ 2
        = (Real.sqrt 2)^2 * ‖off‖^2 := by ring
      _ = 2 * ‖off‖^2 := by
        have h12 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
        rw [h12] <;> ring
    nlinarith [h8, h11, h9, h10]
  have h_result : Real.sqrt 2 * ‖off‖ ≤ 2 + Real.sqrt 2 * r := by
    have h5 : ‖off‖ ≤ Real.sqrt 2 + r := h_off_norm
    have h6 : Real.sqrt 2 * ‖off‖ ≤ Real.sqrt 2 * (Real.sqrt 2 + r) := by gcongr <;> positivity
    have h7 : Real.sqrt 2 * (Real.sqrt 2 + r) = 2 + Real.sqrt 2 * r := by
      have h8 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        have h9 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
        have h10 : Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2)^2 := by ring
        rw [h10, h9]
      rw [mul_add, h8] <;> ring
    rw [h7] at h6
    exact h6
  rw [show b = tubeIntercept ℓ from rfl]
  exact le_trans h_bound h_result

/-- Weaken the constant in an IsDeltaSSet. -/
lemma a9_weaken_constant {X : Type*} [PseudoMetricSpace X]
    {δ s C1 C2 : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C1 P) (hC : C1 ≤ C2) :
    IsDeltaSSet δ s C2 P := by
  rcases h with ⟨hne, hδ, hC1_pos, hs, hmain⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
  have h6 := hmain x r hr
  have hC_le : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  exact le_trans h6 (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC_le (by positivity)) (by positivity))

end A9Support

end DirecretisedFurstenbergEstimate

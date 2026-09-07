import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseDirectionPacking.CylinderVolume
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseDirectionPacking.OverlapSupport
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Geometric overlap lemma for coarse direction packing

If two `rho`-tubes pass through the same point with nearly parallel directions,
close axial parameters, and close transverse closest points, then their
intersection volume exceeds half the tube volume, so they are **not**
essentially distinct.

This is the core geometric ingredient of WZ1 Lemma 7.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

open Kakeya

/-- Axial parameter of the closest point on T's unit segment to p. -/
def tubeAxialParam {δ : ℝ} (T : DeltaTube δ) (p : Point3) : ℝ :=
  max 0 (min 1 (inner ℝ (p - T.base) T.direction))

/-- Closest point on T's unit segment to p. -/
def tubeClosestPoint {δ : ℝ} (T : DeltaTube δ) (p : Point3) : Point3 :=
  T.base + (tubeAxialParam T p) • T.direction

/-- The axial parameter always lies in [0,1]. -/
lemma tubeAxialParam_mem_Icc {δ : ℝ} (T : DeltaTube δ) (p : Point3) :
    tubeAxialParam T p ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 : 0 ≤ tubeAxialParam T p := by
    simp [tubeAxialParam] <;> exact le_max_left _ _
  have h2 : tubeAxialParam T p ≤ 1 := by
    simp [tubeAxialParam] <;> omega
  exact ⟨h1, h2⟩

/-- If p ∈ T.carrier, then dist(p, tubeClosestPoint T p) ≤ δ. -/
lemma tube_closest_point_dist {δ : ℝ} (hδ : 0 ≤ δ)
    (T : DeltaTube δ) (p : Point3) (hp : p ∈ T.carrier) :
    ‖p - tubeClosestPoint T p‖ ≤ δ := by
  let t0 := inner ℝ (p - T.base) T.direction
  let t := tubeAxialParam T p
  have ht_def : t = max 0 (min 1 t0) := by rfl
  have hcarrier : T.carrier = Metric.cthickening δ (unitSegment T.base T.direction) := by
    simp [DeltaTube.carrier]
  rw [hcarrier] at hp
  have hcompact : IsCompact (unitSegment T.base T.direction) := by
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  rw [hcompact.cthickening_eq_biUnion_closedBall hδ] at hp
  rcases Set.mem_iUnion₂.mp hp with ⟨y, hy_seg, hy_ball⟩
  rcases hy_seg with ⟨s, hs, rfl⟩
  have h_dist : dist p (T.base + s • T.direction) ≤ δ := hy_ball
  let q := p - T.base
  have hdir : ‖T.direction‖ = 1 := T.direction_unit
  have h_t0 : t0 = inner ℝ q T.direction := by rfl
  have h_norm2 : ∀ (u : ℝ), ‖q - u • T.direction‖ ^ 2 = ‖q‖ ^ 2 - 2 * u * t0 + u ^ 2 := by
    intro u
    let y := u • T.direction
    have h_expand : inner ℝ (q - y) (q - y) = inner ℝ q q - 2 * inner ℝ q y + inner ℝ y y := by
      have h1 : inner ℝ (q - y) (q - y) = inner ℝ q (q - y) - inner ℝ y (q - y) := by
        rw [inner_sub_left]
      have h2 : inner ℝ q (q - y) = inner ℝ q q - inner ℝ q y := by rw [inner_sub_right]
      have h3 : inner ℝ y (q - y) = inner ℝ y q - inner ℝ y y := by rw [inner_sub_right]
      have h4 : inner ℝ y q = inner ℝ q y := Eq.symm (real_inner_comm y q)
      rw [h1, h2, h3, h4] <;> ring
    have h_q : inner ℝ q q = ‖q‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have h_y : inner ℝ y y = ‖y‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have h_main : ‖q - y‖ ^ 2 = ‖q‖ ^ 2 - 2 * inner ℝ q y + ‖y‖ ^ 2 := by
      have h' : ‖q - y‖ ^ 2 = inner ℝ (q - y) (q - y) := by rw [← real_inner_self_eq_norm_sq]
      rw [h', h_expand, h_q, h_y] <;> ring
    rw [h_main]
    have h2 : inner ℝ q y = u * t0 := by
      simp only [y]
      rw [inner_smul_right, h_t0] <;> ring
    have h3 : ‖y‖ ^ 2 = u ^ 2 := by
      simp only [y]
      rw [norm_smul, hdir] <;> simp <;> ring
    rw [h2, h3] <;> ring
  have h_goal : ∀ (u : ℝ), 0 ≤ u → u ≤ 1 → ‖q - t • T.direction‖ ≤ ‖q - u • T.direction‖ := by
    intro u hu0 hu1
    have h4 : ‖q - u • T.direction‖ ^ 2 ≥ ‖q - t • T.direction‖ ^ 2 := by
      rw [h_norm2 u, h_norm2 t]
      have h5 : t = max 0 (min 1 t0) := by rfl
      rcases le_total t0 0 with (h6 | h6)
      · have ht : t = 0 := by simp [h5, h6] <;> linarith
        rw [ht] <;> nlinarith
      · rcases le_total t0 1 with (h7 | h7)
        · have ht : t = t0 := by simp [h5, h6, h7] <;> linarith
          rw [ht] <;> nlinarith [sq_nonneg (u - t0)]
        · have ht : t = 1 := by simp [h5, h7] <;> linarith
          rw [ht] <;> nlinarith [sq_nonneg (u - 1)]
    have h5 : 0 ≤ ‖q - t • T.direction‖ := by positivity
    have h6 : 0 ≤ ‖q - u • T.direction‖ := by positivity
    nlinarith
  have h_min : ‖p - tubeClosestPoint T p‖ ≤ ‖p - (T.base + s • T.direction)‖ := by
    have h7 : p - tubeClosestPoint T p = q - t • T.direction := by
      simp [tubeClosestPoint, q] <;> abel
    have h8 : p - (T.base + s • T.direction) = q - s • T.direction := by
      simp [q] <;> abel
    rw [h7, h8]
    exact h_goal s hs.1 hs.2
  calc
    ‖p - tubeClosestPoint T p‖ ≤ ‖p - (T.base + s • T.direction)‖ := h_min
    _ = dist p (T.base + s • T.direction) := by rw [dist_eq_norm]
    _ ≤ δ := h_dist

/-- Cross product norm squared equals 1 - inner^2 for unit vectors. -/
lemma cross_norm_sq (u v : Point3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖wz1Cross u v‖ ^ 2 = 1 - (inner ℝ u v)^2 := by
  have h1 : ‖wz1Cross u v‖ =
      ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) :=
    InnerProductGeometry.norm_toLp_symm_crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  have h2 : Real.cos (InnerProductGeometry.angle u v) = inner ℝ u v := by
    rw [InnerProductGeometry.cos_angle] <;> rw [hu, hv] <;> ring
  have h3 : Real.sin (InnerProductGeometry.angle u v) ^ 2 +
      Real.cos (InnerProductGeometry.angle u v) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have h4 : Real.sin (InnerProductGeometry.angle u v) ^ 2 = 1 - (inner ℝ u v)^2 := by
    have h5 : Real.cos (InnerProductGeometry.angle u v) ^ 2 = (inner ℝ u v)^2 := by rw [h2]
    linarith
  have h6 : ‖wz1Cross u v‖ ^ 2 =
      (‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v)) ^ 2 := by rw [h1]
  have h7 : (‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v)) ^ 2 =
      Real.sin (InnerProductGeometry.angle u v) ^ 2 := by
    rw [hu, hv] <;> ring
  rw [h6, h7]
  exact h4

/-- Distance from a point on T's axis to its orthogonal projection on U's line. -/
lemma axis_point_to_U_line {rho : ℝ} (hrho : 0 < rho)
    (T U : DeltaTube rho) (p : Point3)
    (h_cross : ‖wz1Cross T.direction U.direction‖ ≤ rho / 100)
    (h_transverse : ‖tubeClosestPoint T p - tubeClosestPoint U p‖ ≤ rho / 100)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖(T.base + s • T.direction) -
      (U.base + inner ℝ (T.base + s • T.direction - U.base) U.direction • U.direction)‖
    ≤ rho / 50 := by
  let tT := tubeAxialParam T p
  let cT := tubeClosestPoint T p
  let cU := tubeClosestPoint U p
  let alpha := inner ℝ T.direction U.direction
  let v := T.direction - alpha • U.direction
  let d := T.base - U.base - inner ℝ (T.base - U.base) U.direction • U.direction
  have hv_perp : inner ℝ v U.direction = 0 := by
    have h1 : inner ℝ v U.direction = inner ℝ T.direction U.direction - inner ℝ (alpha • U.direction) U.direction := by
      have h : inner ℝ (T.direction - alpha • U.direction) U.direction =
          inner ℝ T.direction U.direction - inner ℝ (alpha • U.direction) U.direction :=
        inner_sub_left T.direction (alpha • U.direction) U.direction
      simpa [v] using h
    rw [h1]
    have h2 : inner ℝ (alpha • U.direction) U.direction = alpha * inner ℝ U.direction U.direction := by
      simpa [inner_smul_left] using rfl
    rw [h2]
    have h3 : inner ℝ U.direction U.direction = 1 := by
      rw [real_inner_self_eq_norm_sq, U.direction_unit] <;> norm_num
    rw [h3] <;> ring
  have hv_norm2 : ‖v‖ ^ 2 = 1 - alpha ^ 2 := by
    rw [norm_sub_sq_real T.direction (alpha • U.direction)]
    have h1 : inner ℝ T.direction (alpha • U.direction) = alpha * alpha := by
      rw [inner_smul_right] <;> ring
    have h2 : ‖alpha • U.direction‖ ^ 2 = alpha ^ 2 := by
      rw [norm_smul, U.direction_unit] <;> simp [abs_pow] <;> ring
    rw [h1, h2, T.direction_unit] <;> ring
  have h_cross2 : ‖wz1Cross T.direction U.direction‖ ^ 2 = 1 - alpha ^ 2 :=
    cross_norm_sq T.direction U.direction T.direction_unit U.direction_unit
  have hv_norm : ‖v‖ ≤ rho / 100 := by
    have h : ‖v‖ ^ 2 = ‖wz1Cross T.direction U.direction‖ ^ 2 := by
      rw [hv_norm2, h_cross2]
    have h_cross_sq : ‖wz1Cross T.direction U.direction‖ ^ 2 ≤ (rho / 100) ^ 2 := by gcongr
    have h_v_sq : ‖v‖ ^ 2 ≤ (rho / 100) ^ 2 := by
      rw [h]
      exact h_cross_sq
    have h_pos1 : 0 ≤ ‖v‖ := by positivity
    have h_pos2 : 0 ≤ rho / 100 := by positivity
    nlinarith
  have h_decomp : ∀ (t : ℝ),
      (T.base + t • T.direction) -
        (U.base + inner ℝ (T.base + t • T.direction - U.base) U.direction • U.direction)
      = d + t • v := by
    intro t
    have h_inner : inner ℝ (T.base + t • T.direction - U.base) U.direction =
        inner ℝ (T.base - U.base) U.direction + t * alpha := by
      have h : T.base + t • T.direction - U.base = (T.base - U.base) + t • T.direction := by abel
      rw [h]
      have h2 : inner ℝ ((T.base - U.base) + t • T.direction) U.direction =
          inner ℝ (T.base - U.base) U.direction + inner ℝ (t • T.direction) U.direction := by
        rw [inner_add_left]
      rw [h2]
      have h3 : inner ℝ (t • T.direction) U.direction = t * alpha := by
        simpa [inner_smul_left, alpha] using rfl
      rw [h3] <;> ring
    have h_goal : (T.base + t • T.direction) -
        (U.base + (inner ℝ (T.base - U.base) U.direction + t * alpha) • U.direction) =
        d + t • v := by
      have h1 : (U.base + (inner ℝ (T.base - U.base) U.direction + t * alpha) • U.direction) =
          U.base + inner ℝ (T.base - U.base) U.direction • U.direction + (t * alpha) • U.direction := by
        rw [add_smul] <;> simp [add_assoc] <;> abel
      rw [h1]
      have h2 : d + t • v =
          T.base - U.base - inner ℝ (T.base - U.base) U.direction • U.direction + t • T.direction - (t * alpha) • U.direction := by
        dsimp only [d, v]
        have hsmul : t • (T.direction - alpha • U.direction) = t • T.direction - (t * alpha) • U.direction := by
          rw [smul_sub, smul_smul] <;> ring
        rw [hsmul] <;> abel
      rw [h2] <;> abel
    rw [h_inner]
    exact h_goal
  let proj := U.base + inner ℝ (cT - U.base) U.direction • U.direction
  have hproj_eq : proj = U.base + inner ℝ (cT - U.base) U.direction • U.direction := by rfl
  have h1 : inner ℝ (cT - proj) U.direction = 0 := by
    rw [hproj_eq]
    have h_eq : cT - (U.base + inner ℝ (cT - U.base) U.direction • U.direction) =
        (cT - U.base) - inner ℝ (cT - U.base) U.direction • U.direction := by abel
    have h_expand : inner ℝ (cT - (U.base + inner ℝ (cT - U.base) U.direction • U.direction)) U.direction =
        inner ℝ (cT - U.base) U.direction - inner ℝ (inner ℝ (cT - U.base) U.direction • U.direction) U.direction := by
      rw [h_eq]
      exact inner_sub_left (cT - U.base) (inner ℝ (cT - U.base) U.direction • U.direction) U.direction
    rw [h_expand]
    have h2 : inner ℝ (inner ℝ (cT - U.base) U.direction • U.direction) U.direction =
        inner ℝ (cT - U.base) U.direction * inner ℝ U.direction U.direction := by
      simpa [inner_smul_left] using rfl
    rw [h2]
    have h3 : inner ℝ U.direction U.direction = 1 := by
      rw [real_inner_self_eq_norm_sq, U.direction_unit] <;> norm_num
    rw [h3] <;> ring
  have h2 : cU - proj = (tubeAxialParam U p - inner ℝ (cT - U.base) U.direction) • U.direction := by
    have hcU : cU = U.base + (tubeAxialParam U p) • U.direction := by rfl
    have h : cU - proj =
        (U.base + (tubeAxialParam U p) • U.direction) -
        (U.base + inner ℝ (cT - U.base) U.direction • U.direction) := by
      rw [hcU, hproj_eq]
    rw [h]
    have h2 : (U.base + (tubeAxialParam U p) • U.direction) -
        (U.base + inner ℝ (cT - U.base) U.direction • U.direction) =
        (tubeAxialParam U p) • U.direction - inner ℝ (cT - U.base) U.direction • U.direction := by abel
    rw [h2, ←sub_smul]
  have h3 : inner ℝ (cT - proj) (cU - proj) = 0 := by
    rw [h2]
    have h4 : inner ℝ (cT - proj) ((tubeAxialParam U p - inner ℝ (cT - U.base) U.direction) • U.direction) =
        (tubeAxialParam U p - inner ℝ (cT - U.base) U.direction) * inner ℝ (cT - proj) U.direction := by
      rw [inner_smul_right] <;> ring
    rw [h4, h1] <;> ring
  have h4 : cT - cU = (cT - proj) - (cU - proj) := by abel
  have h5 : ‖cT - cU‖ ^ 2 = ‖cT - proj‖ ^ 2 + ‖cU - proj‖ ^ 2 := by
    rw [h4, norm_sub_sq_real, h3] <;> ring
  have h_proj_closest : ‖cT - proj‖ ≤ ‖cT - cU‖ := by
    have h7 : ‖cT - proj‖ ^ 2 ≤ ‖cT - cU‖ ^ 2 := by
      rw [h5] <;> exact le_add_of_nonneg_right (by positivity)
    have h8 : 0 ≤ ‖cT - proj‖ := by positivity
    have h9 : 0 ≤ ‖cT - cU‖ := by positivity
    nlinarith
  have h_at_tT : ‖d + tT • v‖ ≤ rho / 100 := by
    have h_eq : d + tT • v = cT - proj := by
      simpa [cT, proj, tubeClosestPoint] using (h_decomp tT).symm
    rw [h_eq]
    exact h_proj_closest.trans h_transverse
  have h_st_diff : |s - tT| ≤ 1 := by
    have h_tT0 : 0 ≤ tT := (tubeAxialParam_mem_Icc T p).1
    have h_tT1 : tT ≤ 1 := (tubeAxialParam_mem_Icc T p).2
    exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h_norm_smul : ‖(s - tT) • v‖ = |s - tT| * ‖v‖ := norm_smul (s - tT) v
  calc
    ‖(T.base + s • T.direction) - _‖
      = ‖d + s • v‖ := by rw [h_decomp s]
    _ = ‖(d + tT • v) + (s - tT) • v‖ := by
      have h : d + s • v = (d + tT • v) + (s - tT) • v := by
        simp [sub_smul] <;> abel
      rw [h]
    _ ≤ ‖d + tT • v‖ + ‖(s - tT) • v‖ := norm_add_le _ _
    _ = ‖d + tT • v‖ + |s - tT| * ‖v‖ := by rw [h_norm_smul]
    _ ≤ rho / 100 + 1 * (rho / 100) := by gcongr <;> linarith
    _ = rho / 50 := by ring

/-- Existence of axial overlap interval of length ≥ 3/4 - O(rho). -/
lemma axial_overlap_interval {rho : ℝ} (hrho : 0 < rho) (hrho2 : rho ≤ 1 / 10000)
    (T U : DeltaTube rho) (p : Point3)
    (h_orient : 0 < inner ℝ T.direction U.direction)
    (h_axial : |tubeAxialParam T p - tubeAxialParam U p| ≤ 1 / 4)
    (h_transverse : ‖tubeClosestPoint T p - tubeClosestPoint U p‖ ≤ rho / 100)
    (h_cross : ‖wz1Cross T.direction U.direction‖ ≤ rho / 100) :
    ∃ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      b - a ≥ 3 / 4 - rho / 100 - (rho / 100)^2 ∧
      ∀ s ∈ Set.Icc a b, s ∈ Set.Icc (0 : ℝ) 1 ∧
        inner ℝ (T.base + s • T.direction - U.base) U.direction ∈ Set.Icc (0 : ℝ) 1 := by
  let tT := tubeAxialParam T p
  let tU := tubeAxialParam U p
  let cT := tubeClosestPoint T p
  let cU := tubeClosestPoint U p
  let alpha := inner ℝ T.direction U.direction
  let eps : ℝ := (rho / 100)^2
  have h_eps_pos : 0 < eps := by positivity
  have h_alpha_pos : 0 < alpha := h_orient
  have h_alpha_le_one : alpha ≤ 1 := by
    have h' : |alpha| ≤ ‖T.direction‖ * ‖U.direction‖ := abs_real_inner_le_norm T.direction U.direction
    have h1 : |alpha| ≤ 1 := by simpa [alpha, T.direction_unit, U.direction_unit] using h'
    have h2 : alpha ≤ |alpha| := le_abs_self alpha
    linarith
  have h_one_minus_alpha : 1 - alpha ≤ eps := by
    have h_cross_sq : ‖wz1Cross T.direction U.direction‖ ^ 2 ≤ (rho / 100) ^ 2 := by gcongr
    have h2 : ‖wz1Cross T.direction U.direction‖ ^ 2 = 1 - alpha^2 :=
      cross_norm_sq T.direction U.direction T.direction_unit U.direction_unit
    have h3 : 1 - alpha^2 ≤ eps := by
      have h4 : (rho / 100) ^ 2 = eps := by simp [eps]
      rw [h4] at h_cross_sq
      rw [h2] at h_cross_sq
      exact h_cross_sq
    have h5 : alpha^2 ≤ alpha := by nlinarith [h_alpha_pos, h_alpha_le_one]
    have h6 : 1 - alpha ≤ 1 - alpha^2 := by linarith
    exact le_trans h6 h3
  let t : ℝ → ℝ := fun s => inner ℝ (T.base + s • T.direction - U.base) U.direction
  have h_ts : ∀ s : ℝ, t s = t tT + (s - tT) * alpha := by
    intro s
    have h_eq1 : T.base + s • T.direction - U.base = (T.base - U.base) + s • T.direction := by abel
    have h_main : inner ℝ (T.base + s • T.direction - U.base) U.direction =
        inner ℝ (T.base - U.base) U.direction + s * alpha := by
      rw [h_eq1]
      have h : inner ℝ ((T.base - U.base) + s • T.direction) U.direction =
          inner ℝ (T.base - U.base) U.direction + inner ℝ (s • T.direction) U.direction :=
        inner_add_left _ _ _
      rw [h]
      have h2 : inner ℝ (s • T.direction) U.direction = s * inner ℝ T.direction U.direction := by
        simpa [inner_smul_left] using rfl
      rw [h2] <;> rfl
    have h_tT_eq : t tT = inner ℝ (T.base - U.base) U.direction + tT * alpha := by
      dsimp only [t]
      have h : T.base + tT • T.direction - U.base = (T.base - U.base) + tT • T.direction := by abel
      rw [h]
      have h2 : inner ℝ ((T.base - U.base) + tT • T.direction) U.direction =
          inner ℝ (T.base - U.base) U.direction + inner ℝ (tT • T.direction) U.direction :=
        inner_add_left _ _ _
      rw [h2]
      have h3 : inner ℝ (tT • T.direction) U.direction = tT * inner ℝ T.direction U.direction := by
        simpa [inner_smul_left] using rfl
      rw [h3] <;> rfl
    have h_main2 : t s = inner ℝ (T.base - U.base) U.direction + s * alpha := by
      exact h_main
    have h_tT_eq2 : t tT = inner ℝ (T.base - U.base) U.direction + tT * alpha := h_tT_eq
    calc
      t s = inner ℝ (T.base - U.base) U.direction + s * alpha := h_main2
      _ = t tT + (s - tT) * alpha := by rw [h_tT_eq2] <;> ring
  have h_tT0 : 0 ≤ tT := (tubeAxialParam_mem_Icc T p).1
  have h_tT1 : tT ≤ 1 := (tubeAxialParam_mem_Icc T p).2
  let c' := t tT - tT
  have h_tri : ∀ (x y : ℝ), |x + y| ≤ |x| + |y| := by
    exact abs_add_le
  have h_c'_abs : |c'| ≤ 1 / 4 + rho / 100 := by
    calc
      |c'| = |t tT - tT| := by rfl
      _ = |(t tT - tU) + (tU - tT)| := by rw [show t tT - tT = (t tT - tU) + (tU - tT) by abel]
      _ ≤ |t tT - tU| + |tU - tT| := h_tri _ _
      _ ≤ rho / 100 + 1 / 4 := by
        have h3 : |tU - tT| ≤ 1 / 4 := by
          have h31 : tU - tT = -(tubeAxialParam T p - tubeAxialParam U p) := by
            dsimp only [tU, tT] <;> ring
          rw [h31, abs_neg]
          exact h_axial
        have h4 : |t tT - tU| ≤ rho / 100 := by
          have h_eq : t tT - tU = inner ℝ (cT - cU) U.direction := by
            dsimp only [t, cT, cU, tubeClosestPoint]
            have h1 : inner ℝ (cT - cU) U.direction =
                inner ℝ (T.base + tT • T.direction - U.base) U.direction - tU := by
              have h2 : cT - cU = (T.base + tT • T.direction - U.base) - tU • U.direction := by
                dsimp only [cT, cU, tubeClosestPoint] <;> abel
              rw [h2]
              have h3 : inner ℝ ((T.base + tT • T.direction - U.base) - tU • U.direction) U.direction =
                  inner ℝ (T.base + tT • T.direction - U.base) U.direction - inner ℝ (tU • U.direction) U.direction :=
                inner_sub_left _ _ _
              rw [h3]
              have h4 : inner ℝ (tU • U.direction) U.direction = tU := by
                have h41 : inner ℝ (tU • U.direction) U.direction = tU * inner ℝ U.direction U.direction := by
                  simpa [inner_smul_left] using rfl
                rw [h41, real_inner_self_eq_norm_sq, U.direction_unit] <;> ring
              rw [h4] <;> ring
            exact h1.symm
          have h_cs : |inner ℝ (cT - cU) U.direction| ≤ ‖cT - cU‖ * ‖U.direction‖ :=
            abs_real_inner_le_norm _ _
          rw [h_eq]
          rw [U.direction_unit] at h_cs
          <;> linarith [h_transverse]
        linarith
      _ = 1 / 4 + rho / 100 := by ring
  have h_t_approx : ∀ s ∈ Set.Icc (0 : ℝ) 1, |t s - (s + c')| ≤ eps := by
    intro s hs
    have h1 : t s - (s + c') = -(s - tT) * (1 - alpha) := by
      rw [h_ts s] <;> ring
    rw [h1]
    have h1ma : 0 ≤ 1 - alpha := by linarith [h_alpha_le_one]
    have h2 : |-(s - tT) * (1 - alpha)| = |s - tT| * (1 - alpha) := by
      rw [abs_mul, abs_neg, abs_of_nonneg h1ma] <;> ring
    rw [h2]
    have h3 : |s - tT| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [hs.1, h_tT0], by linarith [hs.2, h_tT1]⟩
    have h4 : |s - tT| * (1 - alpha) ≤ eps := by
      have h5 : |s - tT| ≤ 1 := h3
      have h6 : (1 - alpha) ≤ eps := h_one_minus_alpha
      have h7 : 0 ≤ |s - tT| := by positivity
      have h8 : 0 ≤ (1 - alpha) := h1ma
      calc |s - tT| * (1 - alpha)
          ≤ 1 * (1 - alpha) := by gcongr <;> linarith
        _ ≤ 1 * eps := by gcongr <;> linarith
        _ = eps := by ring
    exact h4
  let a := max 0 (eps - c')
  let b := min 1 (1 - c' - eps)
  have ha0 : 0 ≤ a := by simp [a] <;> linarith
  have hb1 : b ≤ 1 := by simp [b] <;> linarith
  have h_c'_lower : -(1 / 4 + rho / 100) ≤ c' := by linarith [abs_le.mp h_c'_abs]
  have h_c'_upper : c' ≤ 1 / 4 + rho / 100 := by linarith [abs_le.mp h_c'_abs]
  have h_eps_small : eps ≤ 1 / 4 := by
    dsimp only [eps]
    nlinarith [hrho2]
  have h_ab : a ≤ b := by
    by_cases h1 : c' < -eps
    · have ha : a = eps - c' := by
        have h2 : 0 ≤ eps - c' := by linarith
        simp [a, h2] <;> linarith
      have hb : b = 1 := by
        have h2 : 1 < 1 - c' - eps := by linarith
        simp [b, h2] <;> linarith
      rw [ha, hb] <;> linarith [h_c'_lower, h_eps_pos]
    · have h2 : -eps ≤ c' := by linarith
      have hb : b = 1 - c' - eps := by
        have h3 : 1 - c' - eps ≤ 1 := by linarith
        simp [b, h3] <;> linarith
      rw [hb]
      by_cases h3 : c' ≤ eps
      · have ha : a = eps - c' := by
          have h4 : 0 ≤ eps - c' := by linarith
          simp [a, h4] <;> linarith
        rw [ha] <;> linarith [h_eps_pos]
      · have hc' : c' > eps := by linarith
        have ha : a = 0 := by
          have h4 : eps - c' < 0 := by linarith
          have h5 : max 0 (eps - c') = 0 := by
            apply max_eq_left
            linarith
          simpa [a] using h5
        rw [ha] <;> linarith [h_c'_upper, hrho2, h_eps_pos]
  have h_len : b - a ≥ 3 / 4 - rho / 100 - eps := by
    by_cases h1 : c' < -eps
    · have ha : a = eps - c' := by
        have h2 : 0 ≤ eps - c' := by linarith
        simp [a, h2] <;> linarith
      have hb : b = 1 := by
        have h2 : 1 < 1 - c' - eps := by linarith
        simp [b, h2] <;> linarith
      rw [ha, hb]
      linarith [h_c'_lower]
    · have h2 : -eps ≤ c' := by linarith
      have hb : b = 1 - c' - eps := by
        have h3 : 1 - c' - eps ≤ 1 := by linarith
        simp [b, h3] <;> linarith
      rw [hb]
      by_cases h3 : c' ≤ eps
      · have ha : a = eps - c' := by
          have h4 : 0 ≤ eps - c' := by linarith
          simp [a, h4] <;> linarith
        rw [ha] <;> linarith [h_eps_pos, h_eps_small]
      · have hc' : c' > eps := by linarith
        have ha : a = 0 := by
          have h4 : eps - c' < 0 := by linarith
          have h5 : max 0 (eps - c') = 0 := by
            apply max_eq_left
            linarith
          simpa [a] using h5
        rw [ha]
        linarith [h_c'_upper, hrho2]
  have h_main : ∀ s ∈ Set.Icc a b,
      s ∈ Set.Icc (0 : ℝ) 1 ∧ t s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans ha0 hs.1
    have hs1 : s ≤ 1 := le_trans hs.2 hb1
    have h_approx : |t s - (s + c')| ≤ eps := h_t_approx s ⟨hs0, hs1⟩
    have h_approx' : -eps ≤ t s - (s + c') ∧ t s - (s + c') ≤ eps := abs_le.mp h_approx
    have h5 : t s ≥ s + c' - eps := by linarith
    have h6 : t s ≤ s + c' + eps := by linarith
    have h_lower1 : eps - c' ≤ s := by
      have h : a ≤ s := hs.1
      simp only [a] at h
      exact le_trans (le_max_right 0 (eps - c')) h
    have h_upper1 : s ≤ 1 - c' - eps := by
      have h : s ≤ b := hs.2
      simp only [b] at h
      exact le_trans h (min_le_right 1 (1 - c' - eps))
    have h_t_lower : 0 ≤ t s := by
      have h7 : s + c' - eps ≥ 0 := by linarith
      linarith
    have h_t_upper : t s ≤ 1 := by
      have h7 : s + c' + eps ≤ 1 := by linarith
      linarith
    exact ⟨⟨hs0, hs1⟩, ⟨h_t_lower, h_t_upper⟩⟩
  exact ⟨a, b, ha0, h_ab, hb1, h_len, h_main⟩

/-- Applying a reflection isometry mapping `direction → e0` followed by
translation by `-base` to a general cylinder yields an axis-aligned cylinder. -/
lemma rotated_cylinder_eq_axis_aligned (a b r : ℝ) (ha : a ≤ b) (hr : 0 ≤ r)
    (base direction : Point3) (dir_unit : ‖direction‖ = 1)
    (A : Point3 ≃ₗᵢ[ℝ] Point3) (hA : A direction = EuclideanSpace.single (0 : Fin 3) 1) :
    let F : Point3 → Point3 := fun x => A (x - base)
    F '' {x : Point3 | ∃ s ∈ Set.Icc a b, ∃ (e : Point3),
      inner ℝ e direction = 0 ∧ ‖e‖ ≤ r ∧ x = base + s • direction + e}
    = {y : Point3 | y 0 ∈ Set.Icc a b ∧ (y 1)^2 + (y 2)^2 ≤ r^2} := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) 1
  have he0 : ‖e0‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  let F : Point3 → Point3 := fun x => A (x - base)
  let C : Set Point3 := {x | ∃ s ∈ Set.Icc a b, ∃ (e : Point3),
    inner ℝ e direction = 0 ∧ ‖e‖ ≤ r ∧ x = base + s • direction + e}
  have hA_norm : ∀ (x : Point3), ‖A x‖ = ‖x‖ := A.norm_map
  have hA_inner : ∀ (x y : Point3), inner ℝ (A x) (A y) = inner ℝ x y :=
    fun x y => A.inner_map_map x y
  have h_coord_norm : ∀ (z : Point3), ‖z‖ ^ 2 = (z 0)^2 + (z 1)^2 + (z 2)^2 := by
    intro z
    have h1 : ‖z‖ ^ 2 = inner ℝ z z := by rw [← real_inner_self_eq_norm_sq]
    rw [h1]
    have h2 : inner ℝ z z = ∑ i : Fin 3, (z i)^2 := by
      rw [PiLp.inner_apply]
      <;> simp [mul_comm]
      <;> ring
    rw [h2]
    have h3 : ∑ i : Fin 3, (z i)^2 = (z 0)^2 + (z 1)^2 + (z 2)^2 := by
      simp [Fin.sum_univ_succ] <;> ring
    exact h3
  have h_inner_e0 : ∀ (z : Point3), inner ℝ z e0 = z 0 := by
    intro z
    rw [PiLp.inner_apply]
    simp [e0, EuclideanSpace.single_apply, Fin.sum_univ_succ] <;> ring
  ext y
  simp only [C, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨s, hs, e, he_perp, he_norm, rfl⟩, rfl⟩
    have h_y_eq : A ((base + s • direction + e) - base) = s • e0 + A e := by
      have h1 : (base + s • direction + e) - base = s • direction + e := by abel
      rw [h1, A.map_add, A.map_smul, hA] <;> abel
    have h3 : inner ℝ (A e) e0 = 0 := by
      have h4 : inner ℝ (A e) (A direction) = inner ℝ e direction := hA_inner e direction
      rw [hA] at h4; exact h4.trans he_perp
    have h4 : (A e) 0 = 0 := by
      have h5 : inner ℝ (A e) e0 = (A e) 0 := h_inner_e0 (A e)
      rw [h5] at h3; exact h3
    have h6 : ‖A e‖ ≤ r := by
      have h7 : ‖A e‖ = ‖e‖ := hA_norm e
      rw [h7]; exact he_norm
    have h_coord1 : (s • e0 + A e) 1 = (A e) 1 := by
      simp [e0, EuclideanSpace.single_apply] <;> ring
    have h_coord2 : (s • e0 + A e) 2 = (A e) 2 := by
      simp [e0, EuclideanSpace.single_apply] <;> ring
    have h7 : ((s • e0 + A e) 1)^2 + ((s • e0 + A e) 2)^2 ≤ r^2 := by
      have h8 : ‖A e‖ ^ 2 = (A e) 0 ^ 2 + (A e) 1 ^ 2 + (A e) 2 ^ 2 := h_coord_norm (A e)
      have h9 : ‖A e‖ ^ 2 ≤ r ^ 2 := by
        have h_pos1 : 0 ≤ ‖A e‖ := by positivity
        have h_pos2 : 0 ≤ r := hr
        calc
          ‖A e‖ ^ 2 = ‖A e‖ * ‖A e‖ := by ring
          _ ≤ ‖A e‖ * r := by gcongr
          _ ≤ r * r := by gcongr
          _ = r ^ 2 := by ring
      have h12 : (A e) 0 ^ 2 + (A e) 1 ^ 2 + (A e) 2 ^ 2 ≤ r ^ 2 := by
        rw [← h8]; exact h9
      have h13 : (A e) 1 ^ 2 + (A e) 2 ^ 2 ≤ r ^ 2 := by
        have h14 : (A e) 0 = 0 := h4
        rw [h14] at h12
        ring_nf at h12 ⊢
        exact h12
      have h15 : ((s • e0 + A e) 1)^2 + ((s • e0 + A e) 2)^2 = (A e) 1 ^ 2 + (A e) 2 ^ 2 := by
        rw [h_coord1, h_coord2] <;> ring
      rw [h15]
      exact h13
    have h9 : (s • e0 + A e) 0 = s := by
      simp [e0, EuclideanSpace.single_apply, h4] <;> ring
    have h_final : (s • e0 + A e) 0 ∈ Set.Icc a b ∧
        ((s • e0 + A e) 1)^2 + ((s • e0 + A e) 2)^2 ≤ r^2 := by
      rw [h9]; exact ⟨hs, h7⟩
    exact h_y_eq ▸ h_final
  · rintro ⟨hs, h8⟩
    let s : ℝ := y 0
    let e' : Point3 := y - s • e0
    have h_perp : inner ℝ e' e0 = 0 := by
      have h1 : inner ℝ e' e0 = inner ℝ y e0 - s * inner ℝ e0 e0 := by
        have h_eq : e' = y - s • e0 := by rfl
        rw [h_eq]
        have h2 : inner ℝ (y - s • e0) e0 = inner ℝ y e0 - inner ℝ (s • e0) e0 := by
          rw [inner_sub_left]
        rw [h2]
        have h3 : inner ℝ (s • e0) e0 = s * inner ℝ e0 e0 := by
          rw [inner_smul_left] <;> simp
        rw [h3] <;> ring
      rw [h1]
      have h2 : inner ℝ y e0 = y 0 := h_inner_e0 y
      have h3 : inner ℝ e0 e0 = 1 := by
        have h4 : ‖e0‖ = 1 := by
          simp [e0, EuclideanSpace.single_apply, PiLp.norm_eq_of_L2, Fin.sum_univ_succ] <;> norm_num
        rw [real_inner_self_eq_norm_sq, h4] <;> norm_num
      rw [h2, h3] <;> simp [s] <;> ring
    have he0_1 : e0 1 = 0 := by
      simp [e0, EuclideanSpace.single_apply] <;> decide
    have he0_2 : e0 2 = 0 := by
      simp [e0, EuclideanSpace.single_apply] <;> decide
    have h_e0 : e' 0 = 0 := by simp [e', e0, EuclideanSpace.single_apply] <;> ring
    have h_e1 : e' 1 = y 1 := by simp [e', he0_1] <;> ring
    have h_e2 : e' 2 = y 2 := by simp [e', he0_2] <;> ring
    have h9 : ‖e'‖ ^ 2 = (y 1)^2 + (y 2)^2 := by
      rw [h_coord_norm e', h_e0, h_e1, h_e2] <;> ring
    have h14 : ‖e'‖ ≤ r := by
      have h15 : ‖e'‖^2 ≤ r^2 := by rw [h9]; exact h8
      have h16 : 0 ≤ ‖e'‖ := by positivity
      have h17 : 0 ≤ r := by positivity
      nlinarith
    let e : Point3 := A.symm e'
    have h_eq_Ae : A e = e' := A.apply_symm_apply e'
    have he_perp : inner ℝ e direction = 0 := by
      have h1 : inner ℝ (A e) (A direction) = inner ℝ e direction := hA_inner e direction
      have h2 : inner ℝ (A e) e0 = 0 := by rw [h_eq_Ae]; exact h_perp
      have h3 : A direction = e0 := hA
      rw [h3] at h1
      exact h1.symm.trans h2
    have he_norm : ‖e‖ ≤ r := by
      have h1 : ‖A e‖ = ‖e‖ := hA_norm e
      have h2 : ‖A e‖ = ‖e'‖ := by rw [h_eq_Ae]
      have h3 : ‖e‖ = ‖e'‖ := by linarith
      rw [h3]; exact h14
    let x : Point3 := base + s • direction + e
    have hFx : F x = y := by
      simp [F, x, e', A.map_add, A.map_smul, hA, h_eq_Ae] <;> abel
    exact ⟨x, ⟨s, hs, e, he_perp, he_norm, rfl⟩, hFx⟩

/--
Geometric overlap lemma: two nearby tubes through the same point are NOT
essentially distinct.
-/
lemma geometric_overlap_not_essentially_distinct
    {rho : ℝ} (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 10000)
    (T U : DeltaTube rho)
    (p : Point3)
    (hpT : p ∈ T.carrier)
    (hpU : p ∈ U.carrier)
    (h_cross : ‖wz1Cross T.direction U.direction‖ ≤ rho / 100)
    (h_orient : 0 < inner ℝ T.direction U.direction)
    (h_axial : |tubeAxialParam T p - tubeAxialParam U p| ≤ 1 / 4)
    (h_transverse : dist (tubeClosestPoint T p) (tubeClosestPoint U p) ≤ rho / 100) :
    ¬ T.EssentiallyDistinct U := by
  set cT : Point3 := tubeClosestPoint T p with hcT_def
  set cU : Point3 := tubeClosestPoint U p with hcU_def
  have h_transverse' : ‖cT - cU‖ ≤ rho / 100 := by
    simpa [dist_eq_norm] using h_transverse

  -- Step 1: Get overlap interval [a,b]
  rcases axial_overlap_interval hrho hrho_small T U p h_orient h_axial h_transverse' h_cross
    with ⟨a, b, ha0, hab, hb1, h_len, h_main⟩

  -- Step 2: For each s ∈ [a,b], get a point on U's segment within rho/50
  have h1 : ∀ s ∈ Set.Icc a b, ∃ (z : Point3),
      z ∈ Kakeya.unitSegment U.base U.direction ∧
      dist (T.base + s • T.direction) z ≤ rho / 50 := by
    intro s hs
    have hms := h_main s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := hms.1
    have h_t_in : inner ℝ (T.base + s • T.direction - U.base) U.direction ∈ Set.Icc (0 : ℝ) 1 := hms.2
    let tU_s : ℝ := inner ℝ (T.base + s • T.direction - U.base) U.direction
    let z : Point3 := U.base + tU_s • U.direction
    have hz_in : z ∈ Kakeya.unitSegment U.base U.direction :=
      ⟨tU_s, h_t_in, rfl⟩
    have hdist : dist (T.base + s • T.direction) z ≤ rho / 50 :=
      axis_point_to_U_line hrho T U p h_cross h_transverse' s hs01
    exact ⟨z, hz_in, hdist⟩

  -- Step 3: Define cylinder and show it's in T ∩ U
  let r : ℝ := 49 * rho / 50
  let C : Set Point3 :=
    {x | ∃ s ∈ Set.Icc a b, ∃ (e : Point3),
      inner ℝ e T.direction = 0 ∧ ‖e‖ ≤ r ∧ x = T.base + s • T.direction + e}
  have hC_sub : C ⊆ T.carrier ∩ U.carrier :=
    cylinder_in_intersection hrho T U a b hab (by
      intro s hs; exact (h_main s hs).1) h1

  -- Step 4: Rotate cylinder to axis-aligned position and compute volume
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm : ‖T.direction‖ = ‖e0‖ := by rw [T.direction_unit, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
  have hA : A T.direction = e0 := Submodule.reflection_sub hnorm
  have hA_norm : ∀ (x : Point3), ‖A x‖ = ‖x‖ := A.norm_map
  have hA_inner : ∀ (x y : Point3), inner ℝ (A x) (A y) = inner ℝ x y :=
    fun x y => A.inner_map_map x y
  have hA_meas : MeasurePreserving A volume volume := A.measurePreserving

  let translate : Point3 ≃ᵢ Point3 :=
    { toFun := fun x => x - T.base
      invFun := fun y => y + T.base
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      isometry_toFun := by intro x y; simp [edist_dist, dist_eq_norm] }
  have htrans_meas : MeasurePreserving translate volume volume :=
    measurePreserving_sub_right volume T.base

  let F : Point3 ≃ᵢ Point3 := translate.trans (A : Point3 ≃ᵢ Point3)
  have hF : ∀ x, F x = A (x - T.base) := by intro x; rfl
  have hF_meas : MeasurePreserving F volume volume := hA_meas.comp htrans_meas
  have hF_inj : Function.Injective F := F.injective

  let C' : Set Point3 := F '' C
  have hvol_C : volume C = volume C' := by
    have h_map : Measure.map F volume = volume := hF_meas.map_eq
    have hC'_meas : MeasurableSet C' := by
      have hS_compact : IsCompact C := by
        let K : Set (ℝ × Point3) := Set.Icc a b ×ˢ {e | inner ℝ e T.direction = 0 ∧ ‖e‖ ≤ r}
        have hK1 : IsCompact (Set.Icc a b : Set ℝ) := isCompact_Icc
        have hK2 : IsCompact {e : Point3 | inner ℝ e T.direction = 0 ∧ ‖e‖ ≤ r} := by
          have h_closed : IsClosed {e : Point3 | inner ℝ e T.direction = 0 ∧ ‖e‖ ≤ r} := by
            apply IsClosed.inter
            · exact isClosed_eq (by fun_prop) continuous_const
            · exact isClosed_le continuous_norm continuous_const
          have h_sub : {e : Point3 | inner ℝ e T.direction = 0 ∧ ‖e‖ ≤ r} ⊆ Metric.closedBall (0 : Point3) r := by
            intro x hx; simpa [Metric.mem_closedBall, dist_zero_right] using hx.2
          exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Point3) r) h_closed h_sub
        have hK : IsCompact K := hK1.prod hK2
        let f : ℝ × Point3 → Point3 := fun p => T.base + p.1 • T.direction + p.2
        have hf : Continuous f := by fun_prop
        have hS_eq : C = f '' K := by
          ext x
          simp only [C, K, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
          constructor
          · rintro ⟨s, hs, e, he1, he2, rfl⟩
            exact ⟨(s, e), ⟨hs, ⟨he1, he2⟩⟩, rfl⟩
          · rintro ⟨⟨s, e⟩, ⟨hs, ⟨he1, he2⟩⟩, rfl⟩
            exact ⟨s, hs, e, he1, he2, rfl⟩
        rw [hS_eq]; exact hK.image hf
      exact hS_compact.image (by fun_prop) |>.measurableSet
    have h1 : volume C' = volume C := by
      calc
        volume C'
          = Measure.map F volume C' := by rw [h_map]
        _ = volume (F ⁻¹' C') := Measure.map_apply (by fun_prop) hC'_meas
        _ = volume C := by
          have h3 : F ⁻¹' C' = C := by
            have h4 : C' = F '' C := by rfl
            rw [h4]
            exact Set.preimage_image_eq C hF_inj
          rw [h3]
    exact h1.symm

  have hC'_eq : C' = {x : Point3 | x 0 ∈ Set.Icc a b ∧ (x 1)^2 + (x 2)^2 ≤ r^2} := by
    have h_helper := rotated_cylinder_eq_axis_aligned a b r hab (by positivity)
      T.base T.direction T.direction_unit A hA
    have hF_eq : (fun x : Point3 => A (x - T.base)) = F := by
      funext x; exact hF x
    rw [hF_eq] at h_helper
    exact h_helper

  have hvol : volume C = ENNReal.ofReal ((b - a) * Real.pi * r^2) := by
    calc
      volume C = volume C' := hvol_C
      _ = volume {x : Point3 | x 0 ∈ Set.Icc a b ∧ (x 1)^2 + (x 2)^2 ≤ r^2} := by rw [hC'_eq]
      _ = ENNReal.ofReal ((b - a) * Real.pi * r^2) := cylinder_volume a b r hab (by positivity)

  -- Step 5: Numerical inequality and conclusion
  have h_num : (b - a) * Real.pi * r^2 > (2 + 4 * rho) * rho^2 := by
    set c : ℝ := 3 / 4 - rho / 100 - (rho / 100)^2 with hc_def
    have hc_pos : 0 ≤ c := by nlinarith [hrho_small]
    have h_len' : b - a ≥ c := h_len
    have h_r2 : r^2 = (49 / 50 : ℝ)^2 * rho^2 := by
      have hr_def : r = 49 * rho / 50 := by rfl
      rw [hr_def] <;> ring
    have h_ineq : c * Real.pi * (49 / 50 : ℝ)^2 > 2 + 4 * rho :=
      cylinder_numerical_inequality hrho hrho_small
    calc
      (b - a) * Real.pi * r^2
        = (b - a) * (Real.pi * (49 / 50 : ℝ)^2 * rho^2) := by rw [h_r2] <;> ring
      _ ≥ c * (Real.pi * (49 / 50 : ℝ)^2 * rho^2) := by
        exact mul_le_mul_of_nonneg_right h_len' (by positivity)
      _ = (c * Real.pi * (49 / 50 : ℝ)^2) * rho^2 := by ring
      _ > (2 + 4 * rho) * rho^2 := by
        exact mul_lt_mul_of_pos_right h_ineq (by positivity)
  have h_vol_upper : T.volume ≤ ENNReal.ofReal (4 * rho^2 + 8 * rho^3) := by
    have hT_vol : T.volume = Kakeya.deltaTubeVolume rho := tube_volume_scaling.1 rho T
    rw [hT_vol]
    have h_upper := canonical_volume_upper_tight hrho (by linarith [hrho_small])
    have h_simp : (1 + 2 * rho) * (2 * rho) * (2 * rho) = 4 * rho^2 + 8 * rho^3 := by ring
    rw [h_simp] at h_upper
    exact h_upper
  have h4 : (2 : ENNReal)⁻¹ * ENNReal.ofReal (4 * rho^2 + 8 * rho^3) =
      ENNReal.ofReal ((2 + 4 * rho) * rho^2) := by
    have h5 : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by
      have h6 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_cast
      rw [h6]
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      <;> norm_num
    have h_pos2 : 0 ≤ 4 * rho^2 + 8 * rho^3 := by positivity
    have h_mul : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (4 * rho^2 + 8 * rho^3) =
        ENNReal.ofReal ((1 / 2 : ℝ) * (4 * rho^2 + 8 * rho^3)) := by
      exact Eq.symm (ENNReal.ofReal_mul' h_pos2)
    have h_eq : (1 / 2 : ℝ) * (4 * rho^2 + 8 * rho^3) = (2 + 4 * rho) * rho^2 := by ring
    rw [h5, h_mul, h_eq]
  have h_half_upper : (2 : ENNReal)⁻¹ * T.volume ≤ ENNReal.ofReal ((2 + 4 * rho) * rho^2) := by
    calc
      (2 : ENNReal)⁻¹ * T.volume
        ≤ (2 : ENNReal)⁻¹ * ENNReal.ofReal (4 * rho^2 + 8 * rho^3) := by gcongr
      _ = ENNReal.ofReal ((2 + 4 * rho) * rho^2) := h4
  let eps : ℝ := (rho / 100)^2
  have h_pos_right : 0 < (b - a) * Real.pi * r^2 := by
    have h_pos : 0 < 3 / 4 - rho / 100 - eps := by
      dsimp only [eps]
      nlinarith [hrho_small]
    have h_b_a_pos : 0 < b - a := by
      have h : b - a ≥ 3 / 4 - rho / 100 - eps := h_len
      linarith [h_pos]
    have h_r2_pos : 0 < r^2 := by
      dsimp only [r]
      positivity
    exact mul_pos (mul_pos h_b_a_pos Real.pi_pos) h_r2_pos
  have h_ofReal_lt : ENNReal.ofReal ((2 + 4 * rho) * rho^2) <
      ENNReal.ofReal ((b - a) * Real.pi * r^2) := by
    rw [ENNReal.ofReal_lt_ofReal_iff h_pos_right]
    exact h_num
  have h_main_vol : (2 : ENNReal)⁻¹ * T.volume < ENNReal.ofReal ((b - a) * Real.pi * r^2) :=
    lt_of_le_of_lt h_half_upper h_ofReal_lt
  have h_inter : volume C ≤ volume (T.carrier ∩ U.carrier) := measure_mono hC_sub
  have hT_eq_U : T.volume = U.volume := by
    have h1 : T.volume = Kakeya.deltaTubeVolume rho := tube_volume_scaling.1 rho T
    have h2 : U.volume = Kakeya.deltaTubeVolume rho := tube_volume_scaling.1 rho U
    rw [h1, h2]
  have hmax : max T.volume U.volume = T.volume := by
    rw [hT_eq_U] <;> simp
  have h_vol_C : volume C = ENNReal.ofReal ((b - a) * Real.pi * r^2) := hvol
  have h_final : (2 : ENNReal)⁻¹ * max T.volume U.volume < volume (T.carrier ∩ U.carrier) := by
    rw [hmax]
    have h6 : (2 : ENNReal)⁻¹ * T.volume < volume C := by
      rw [h_vol_C]; exact h_main_vol
    exact lt_of_lt_of_le h6 h_inter
  simpa [DeltaTube.EssentiallyDistinct] using h_final

end Kakeya.Assouad

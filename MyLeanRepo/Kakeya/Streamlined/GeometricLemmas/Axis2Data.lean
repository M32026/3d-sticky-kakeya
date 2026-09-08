import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PhaseSpaceGridIntercept
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PlaneIntercept
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PlankDirectionBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.InterceptBounds

/-!
# Per-tube intercept data for axis-2-dominant tubes in a plank

Constructs `plane_idx`, `q1`, `q2`, `t0`, `du1`, `du2` and proves range bounds
for use with `phase_space_grid_packing_intercept`.
-/

noncomputable section

namespace Kakeya.Streamlined.GeometricLemmas

open Kakeya.Streamlined

/-! ### Plane index bounds (copied from InterceptBounds.lean) -/

lemma planeIndex_nat_nonneg' (p2 A : ℝ) (hA : 0 ≤ A)
    (hlo : -A / 2 ≤ p2) (hhi : p2 ≤ A / 2) :
    0 ≤ planeIndex p2 + (Nat.ceil A : ℤ) := by
  have h_bounds : -A ≤ (planeIndex p2 : ℝ) :=
    (planeIndex_bound p2 A hA hlo hhi).1
  have h_ceil : (Nat.ceil A : ℝ) ≥ A := Nat.le_ceil A
  have h : (planeIndex p2 : ℝ) + (Nat.ceil A : ℝ) ≥ 0 := by linarith
  exact_mod_cast h

lemma planeIndex_nat_lt' (p2 A : ℝ) (hA : 0 ≤ A)
    (hlo : -A / 2 ≤ p2) (hhi : p2 ≤ A / 2) :
    (planeIndex p2 + (Nat.ceil A : ℤ)).toNat < 2 * Nat.ceil A + 2 := by
  have h_bounds : (planeIndex p2 : ℝ) ≤ A + 1 :=
    (planeIndex_bound p2 A hA hlo hhi).2
  have h_ceil : (Nat.ceil A : ℝ) ≥ A := Nat.le_ceil A
  have h2 : ((planeIndex p2 + (Nat.ceil A : ℤ)).toNat : ℤ) = planeIndex p2 + (Nat.ceil A : ℤ) :=
    Int.toNat_of_nonneg (planeIndex_nat_nonneg' p2 A hA hlo hhi)
  have h3 : ((planeIndex p2 + (Nat.ceil A : ℤ)).toNat : ℝ) = (planeIndex p2 : ℝ) + (Nat.ceil A : ℝ) := by
    exact_mod_cast h2
  have h4 : ((planeIndex p2 + (Nat.ceil A : ℤ)).toNat : ℝ) < (2 * (Nat.ceil A : ℝ) + 2) := by
    rw [h3]
    linarith
  exact_mod_cast h4

/-! ### Helper: both endpoints of normalized segment lie in the outer box -/

/-- A point in the tube's unit segment belongs to the tube carrier. -/
private lemma segment_point_in_tube {δ : ℝ} (T : DeltaTube δ) (x : Point3)
    (hx : x ∈ unitSegment T.base T.direction) : x ∈ T.carrier := by
  have h1 : Metric.infEDist x (unitSegment T.base T.direction) ≤ ENNReal.ofReal δ := by
    have h2 : Metric.infEDist x (unitSegment T.base T.direction) ≤ edist x x :=
      Metric.infEDist_le_edist_of_mem hx
    have h3 : edist x x = 0 := edist_self _
    rw [h3] at h2
    exact le_trans h2 (by simp)
  exact h1

/--
A point on the original tube segment (in frame coordinates) lies in the outer box.
-/
private lemma frame_segment_point_in_box
    {δ : ℝ} (T : DeltaTube δ) (plank : Body)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3) (a b A : ℝ)
    (h_dim : plank.HasDimensionsInFrame frame a b 1 A)
    (h_sub : T.carrier ⊆ plank.carrier)
    (p u : Point3)
    (hp_def : p = frame.symm T.base)
    (hu_def : u = frame.symm.linearIsometryEquiv T.direction)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    p + s • u ∈ axisBox (A * a) (A * b) A := by
  rcases h_dim with ⟨_, _, _, _, _, h_outer⟩
  have hA1 : A * 1 = A := by ring
  have h_outer' : plank.carrier ⊆ frame '' axisBox (A * a) (A * b) A := by
    have h_box_eq : axisBox (A * a) (A * b) (A * 1) = axisBox (A * a) (A * b) A := by
      congr <;> ring
    rw [h_box_eq] at h_outer
    exact h_outer
  have h_orig_pt : T.base + s • T.direction ∈ T.carrier :=
    segment_point_in_tube T (T.base + s • T.direction) ⟨s, hs, by simp⟩
  have h_in_plank : T.base + s • T.direction ∈ plank.carrier := h_sub h_orig_pt
  have h_frame_map : frame (p + s • u) = T.base + s • T.direction := by
    have h1 : frame (p + s • u) = frame p + s • frame.linearIsometryEquiv u := by
      have h2 : frame (s • u + p) = frame.linearIsometryEquiv (s • u) + frame p := by
        have h3 := frame.map_vadd (p := p) (v := s • u)
        simpa [vadd_eq_add] using h3
      have h_comm : p + s • u = s • u + p := (add_comm (s • u) p).symm
      rw [h_comm]
      rw [h2]
      have h4 : frame.linearIsometryEquiv (s • u) = s • frame.linearIsometryEquiv u := by
        exact frame.linearIsometryEquiv.map_smul s u
      rw [h4]
      exact (add_comm (frame p) (s • frame.linearIsometryEquiv u)).symm
    rw [h1]
    have hfp : frame p = T.base := by
      rw [hp_def]
      exact frame.apply_symm_apply T.base
    have hfu : frame.linearIsometryEquiv u = T.direction := by
      rw [hu_def]
      exact frame.linearIsometryEquiv.apply_symm_apply T.direction
    rw [hfp, hfu]
  have h_img : frame (p + s • u) ∈ frame '' axisBox (A * a) (A * b) A := by
    rw [h_frame_map]
    exact h_outer' h_in_plank
  rcases h_img with ⟨x, hx, hfx⟩
  have h_x_eq : x = p + s • u := by
    have h : frame x = frame (p + s • u) := hfx
    exact frame.injective h
  have h_goal : p + s • u ∈ axisBox (A * a) (A * b) A := by
    convert hx using 1
    exact h_x_eq.symm
  exact h_goal

/--
Both the normalized base `p'` and the other endpoint `p' + u'` lie in the
outer axis-aligned box, because they are points on the original tube segment.
-/
lemma normalized_endpoints_in_box
    {δ : ℝ} (T : DeltaTube δ) (plank : Body)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3) (a b A : ℝ)
    (h_dim : plank.HasDimensionsInFrame frame a b 1 A)
    (h_sub : T.carrier ⊆ plank.carrier)
    (p u p' u' : Point3)
    (hp_def : p = frame.symm T.base)
    (hu_def : u = frame.symm.linearIsometryEquiv T.direction)
    (h_segment : Set.image (fun t : ℝ => p' + t • u') (Set.Icc (0 : ℝ) 1) =
                   Set.image (fun t : ℝ => p + t • u) (Set.Icc (0 : ℝ) 1))
    (h_p'_eq : p' = p ∨ p' = p + u) :
    p' ∈ axisBox (A * a) (A * b) A ∧
    (p' + u') ∈ axisBox (A * a) (A * b) A := by
  -- p' is either p (s=0) or p+u (s=1), both on original segment
  have h_p'_box : p' ∈ axisBox (A * a) (A * b) A := by
    rcases h_p'_eq with (h | h)
    · rw [h]
      have h6 := frame_segment_point_in_box T plank frame a b A h_dim h_sub p u hp_def hu_def 0 (by norm_num)
      simpa using h6
    · rw [h]
      have h6 := frame_segment_point_in_box T plank frame a b A h_dim h_sub p u hp_def hu_def 1 (by norm_num)
      simpa using h6

  -- p' + u' is at t=1 in normalized segment, hence on original segment
  have h_p'u'_in_orig : p' + u' ∈ Set.image (fun t : ℝ => p + t • u) (Set.Icc (0 : ℝ) 1) := by
    have h1 : p' + u' ∈ Set.image (fun t : ℝ => p' + t • u') (Set.Icc (0 : ℝ) 1) := by
      refine ⟨1, by norm_num, ?_⟩
      simp
    rw [←h_segment]
    exact h1
  rcases h_p'u'_in_orig with ⟨s, hs, h_eq⟩
  have h_p'u'_box : p' + u' ∈ axisBox (A * a) (A * b) A := by
    have h_goal : p + s • u ∈ axisBox (A * a) (A * b) A :=
      frame_segment_point_in_box T plank frame a b A h_dim h_sub p u hp_def hu_def s hs
    have h_eq2 : (fun t : ℝ => p + t • u) s = p + s • u := by simp
    have h_eq3 : p' + u' = p + s • u := by
      calc p' + u' = (fun t : ℝ => p + t • u) s := h_eq.symm
        _ = p + s • u := h_eq2
    rw [h_eq3]
    exact h_goal

  exact ⟨h_p'_box, h_p'u'_box⟩

/-! ### Main data construction lemma -/

/--
Construct per-tube intercept data functions and prove their range bounds
for a family of axis-2-dominant tubes contained in a framed plank.
-/
lemma axis2_intercept_data
    {δ a b A : ℝ} (hA : 1 ≤ A)
    {plank : Body} {frame : Point3 ≃ᵃⁱ[ℝ] Point3}
    (hdim : plank.HasDimensionsInFrame frame a b 1 A)
    {F : Kakeya.TubeFamily δ}
    (hcontain : ∀ T ∈ F, T.carrier ⊆ plank.carrier)
    (h_axis2 : ∀ T ∈ F, |(frame.symm.linearIsometryEquiv T.direction) 2| ≥ 1 / 2) :
    ∃ (plane_idx : DeltaTube δ → ℕ)
      (q1 q2 t0 du1 du2 : DeltaTube δ → ℝ),
      (∀ T ∈ F, plane_idx T < 2 * Nat.ceil A + 2) ∧
      (∀ T ∈ F, |q1 T| ≤ 2 * A * a) ∧
      (∀ T ∈ F, |q2 T| ≤ 2 * A * b) ∧
      (∀ T ∈ F, t0 T ∈ Set.Icc 0 1) ∧
      (∀ T ∈ F, |du1 T| ≤ A * a) ∧
      (∀ T ∈ F, |du2 T| ≤ A * b) := by
  let pF (T : DeltaTube δ) : Point3 := frame.symm T.base
  let uF (T : DeltaTube δ) : Point3 := frame.symm.linearIsometryEquiv T.direction
  let hasAxis2 (T : DeltaTube δ) : Prop := |uF T 2| ≥ 1 / 2

  let h_norm_unit (T : DeltaTube δ) : ‖uF T‖ = 1 := by
    have h1 : ‖uF T‖ = ‖T.direction‖ := frame.symm.linearIsometryEquiv.norm_map T.direction
    rw [h1, T.direction_unit]

  let getData (T : DeltaTube δ) (h : hasAxis2 T) : TubePlaneData (pF T) (uF T) :=
    computeTubePlaneData (pF T) (uF T) h (h_norm_unit T)

  let plane_idx (T : DeltaTube δ) : ℕ :=
    if h : hasAxis2 T then
      ((getData T h).k + (Nat.ceil A : ℤ)).toNat
    else 0

  let q1 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).q 0 else 0

  let q2 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).q 1 else 0

  let t0 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).t0 else 0

  let du1 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).u' 0 else 0

  let du2 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).u' 1 else 0

  refine' ⟨plane_idx, q1, q2, t0, du1, du2, _⟩
  have hA_nonneg : 0 ≤ A := by linarith

  constructor
  · -- h_plane
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : plane_idx T = ((data.k + (Nat.ceil A : ℤ)).toNat) := by
      dsimp only [plane_idx]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p'2 : |data.p' 2| ≤ A / 2 := h_endpoints.1.2.2
    have hlo : -A / 2 ≤ data.p' 2 := by
      have h : -(A / 2) ≤ data.p' 2 := (abs_le.mp h_p'2).1
      have h' : -(A / 2) = -A / 2 := by ring
      rw [h'] at h
      exact h
    have hhi : data.p' 2 ≤ A / 2 := (abs_le.mp h_p'2).2
    have h_k_def : (data.k : ℝ) = planeIndex (data.p' 2) := data.h_k_def
    have h_main : (data.k + (Nat.ceil A : ℤ)).toNat < 2 * Nat.ceil A + 2 := by
      have h2 : (planeIndex (data.p' 2) + (Nat.ceil A : ℤ)).toNat < 2 * Nat.ceil A + 2 :=
        planeIndex_nat_lt' (data.p' 2) A hA_nonneg hlo hhi
      have h3 : (data.k + (Nat.ceil A : ℤ)).toNat = (planeIndex (data.p' 2) + (Nat.ceil A : ℤ)).toNat := by
        apply congr_arg (fun x : ℤ => (x + (Nat.ceil A : ℤ)).toNat)
        exact_mod_cast h_k_def
      rw [h3]
      exact h2
    exact h_main

  constructor
  · -- h_q1
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : q1 T = data.q 0 := by
      dsimp only [q1]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p'_box : data.p' ∈ axisBox (A * a) (A * b) A := h_endpoints.1
    have h_p0 : |data.p' 0| ≤ A * a / 2 := h_p'_box.1
    have h_p1 : |data.p' 1| ≤ A * b / 2 := h_p'_box.2.1
    have h_p'u'_box : (data.p' + data.u') ∈ axisBox (A * a) (A * b) A := h_endpoints.2
    have h_u0 : |data.u' 0| ≤ A * a := by
      have h_eq1 : data.u' 0 = (data.p' + data.u') 0 - data.p' 0 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 0 - data.p' 0|
        ≤ |(data.p' + data.u') 0| + |data.p' 0| := abs_sub _ _
      _ ≤ A * a / 2 + A * a / 2 := add_le_add h_p'u'_box.1 h_p'_box.1
      _ = A * a := by ring
    have h_u1 : |data.u' 1| ≤ A * b := by
      have h_eq1 : data.u' 1 = (data.p' + data.u') 1 - data.p' 1 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 1 - data.p' 1|
        ≤ |(data.p' + data.u') 1| + |data.p' 1| := abs_sub _ _
      _ ≤ A * b / 2 + A * b / 2 := add_le_add h_p'u'_box.2.1 h_p'_box.2.1
      _ = A * b := by ring
    have h_t0_pos : 0 ≤ data.t0 := data.h_t0_pos.le
    have h_t0_le_one : data.t0 ≤ 1 := data.h_t0_le_one
    have h_q_def : data.q = data.p' + data.t0 • data.u' := data.h_q_def
    rw [h_q_def]
    have ha_nonneg : 0 ≤ a := by linarith [hdim.1]
    have hb_nonneg : 0 ≤ b := by linarith [hdim.1, hdim.2.1]
    have h_bound := plank_intercept_bounds data.p' data.u' data.t0 A a b hA_nonneg
      ha_nonneg hb_nonneg h_p0 h_p1 h_u0 h_u1 h_t0_pos h_t0_le_one
    have h : |(data.p' + data.t0 • data.u') 0| ≤ 3 * A * a / 2 := h_bound.1
    have h_final : 3 * A * a / 2 ≤ 2 * A * a := by nlinarith
    linarith

  constructor
  · -- h_q2
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : q2 T = data.q 1 := by
      dsimp only [q2]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p'_box : data.p' ∈ axisBox (A * a) (A * b) A := h_endpoints.1
    have h_p0 : |data.p' 0| ≤ A * a / 2 := h_p'_box.1
    have h_p1 : |data.p' 1| ≤ A * b / 2 := h_p'_box.2.1
    have h_p'u'_box : (data.p' + data.u') ∈ axisBox (A * a) (A * b) A := h_endpoints.2
    have h_u0 : |data.u' 0| ≤ A * a := by
      have h_eq1 : data.u' 0 = (data.p' + data.u') 0 - data.p' 0 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 0 - data.p' 0|
        ≤ |(data.p' + data.u') 0| + |data.p' 0| := abs_sub _ _
      _ ≤ A * a / 2 + A * a / 2 := add_le_add h_p'u'_box.1 h_p'_box.1
      _ = A * a := by ring
    have h_u1 : |data.u' 1| ≤ A * b := by
      have h_eq1 : data.u' 1 = (data.p' + data.u') 1 - data.p' 1 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 1 - data.p' 1|
        ≤ |(data.p' + data.u') 1| + |data.p' 1| := abs_sub _ _
      _ ≤ A * b / 2 + A * b / 2 := add_le_add h_p'u'_box.2.1 h_p'_box.2.1
      _ = A * b := by ring
    have h_t0_pos : 0 ≤ data.t0 := data.h_t0_pos.le
    have h_t0_le_one : data.t0 ≤ 1 := data.h_t0_le_one
    have h_q_def : data.q = data.p' + data.t0 • data.u' := data.h_q_def
    rw [h_q_def]
    have ha_nonneg : 0 ≤ a := by linarith [hdim.1]
    have hb_nonneg : 0 ≤ b := by linarith [hdim.1, hdim.2.1]
    have h_bound := plank_intercept_bounds data.p' data.u' data.t0 A a b hA_nonneg
      ha_nonneg hb_nonneg h_p0 h_p1 h_u0 h_u1 h_t0_pos h_t0_le_one
    have h : |(data.p' + data.t0 • data.u') 1| ≤ 3 * A * b / 2 := h_bound.2
    have h_final : 3 * A * b / 2 ≤ 2 * A * b := by nlinarith
    linarith

  constructor
  · -- h_t0
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : t0 T = data.t0 := by
      dsimp only [t0]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    exact ⟨data.h_t0_pos.le, data.h_t0_le_one⟩

  constructor
  · -- h_du1
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : du1 T = data.u' 0 := by
      dsimp only [du1]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p'_box : data.p' ∈ axisBox (A * a) (A * b) A := h_endpoints.1
    have h_p'u'_box : (data.p' + data.u') ∈ axisBox (A * a) (A * b) A := h_endpoints.2
    have h_eq1 : data.u' 0 = (data.p' + data.u') 0 - data.p' 0 := by simp
    rw [h_eq1]
    calc |(data.p' + data.u') 0 - data.p' 0|
      ≤ |(data.p' + data.u') 0| + |data.p' 0| := abs_sub _ _
    _ ≤ A * a / 2 + A * a / 2 := by gcongr <;> [exact h_p'u'_box.1; exact h_p'_box.1]
    _ = A * a := by ring

  · -- h_du2
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : du2 T = data.u' 1 := by
      dsimp only [du2]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p'_box : data.p' ∈ axisBox (A * a) (A * b) A := h_endpoints.1
    have h_p'u'_box : (data.p' + data.u') ∈ axisBox (A * a) (A * b) A := h_endpoints.2
    have h_eq1 : data.u' 1 = (data.p' + data.u') 1 - data.p' 1 := by simp
    rw [h_eq1]
    calc |(data.p' + data.u') 1 - data.p' 1|
      ≤ |(data.p' + data.u') 1| + |data.p' 1| := abs_sub _ _
    _ ≤ A * b / 2 + A * b / 2 := by gcongr <;> [exact h_p'u'_box.2.1; exact h_p'_box.2.1]
    _ = A * b := by ring

end Kakeya.Streamlined.GeometricLemmas

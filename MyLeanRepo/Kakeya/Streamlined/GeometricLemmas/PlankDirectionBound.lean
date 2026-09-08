import MyLeanRepo.Kakeya.Streamlined.Geometry

/-!
# Direction and position bounds for a tube contained in a framed plank

If a δ-tube is contained in a body with `HasDimensionsInFrame frame a b c A`,
then in the frame coordinates the tube's base and direction satisfy explicit
coordinate bounds.  For a plank (`c = 1`) this gives the transverse direction
bounds used in phase-space packing.

## Main result

`tube_in_frame_direction_bound`: all six coordinate bounds for base and direction
in the frame of the containing body.
-/

noncomputable section

namespace Kakeya.Streamlined.GeometricLemmas

open Kakeya.Streamlined

/--
If a δ-tube `T` is contained in a body with `HasDimensionsInFrame frame a b c A`,
then in `frame.symm` coordinates the tube's base `p'` and direction `u'` satisfy:
- `|p' 0| ≤ A*a/2`, `|p' 1| ≤ A*b/2`, `|p' 2| ≤ A*c/2`
- `|u' 0| ≤ A*a`,   `|u' 1| ≤ A*b`,   `|u' 2| ≤ A*c`

The direction bounds follow by applying the triangle inequality to the two
endpoints of the tube's unit segment, both of which lie inside the outer box.
-/
theorem tube_in_frame_direction_bound
    {δ : ℝ} (T : DeltaTube δ) (K : Body)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3) (a b c A : ℝ)
    (h_dim : K.HasDimensionsInFrame frame a b c A)
    (h_sub : T.carrier ⊆ K.carrier) :
    |(frame.symm T.base) 0| ≤ A * a / 2 ∧
    |(frame.symm T.base) 1| ≤ A * b / 2 ∧
    |(frame.symm T.base) 2| ≤ A * c / 2 ∧
    |(frame.symm.linearIsometryEquiv T.direction) 0| ≤ A * a ∧
    |(frame.symm.linearIsometryEquiv T.direction) 1| ≤ A * b ∧
    |(frame.symm.linearIsometryEquiv T.direction) 2| ≤ A * c := by
  rcases h_dim with ⟨_, _, _, _, _, h_outer⟩
  set p' : Point3 := frame.symm T.base with hp'_def
  set u' : Point3 := frame.symm.linearIsometryEquiv T.direction with hu'_def
  set q' : Point3 := frame.symm (T.base + T.direction) with hq'_def

  -- Both endpoints of the unit segment belong to the tube carrier.
  have h_base_in : T.base ∈ T.carrier := by
    have h1 : T.base ∈ unitSegment T.base T.direction := by
      refine ⟨0, by norm_num, ?_⟩
      simp
    have h2 : Metric.infEDist T.base (unitSegment T.base T.direction) ≤ ENNReal.ofReal δ := by
      have h3 : Metric.infEDist T.base (unitSegment T.base T.direction) ≤
          edist T.base T.base := Metric.infEDist_le_edist_of_mem h1
      have h4 : edist T.base T.base = 0 := edist_self _
      rw [h4] at h3
      exact le_trans h3 (by simp)
    exact h2
  have h_end_in : T.base + T.direction ∈ T.carrier := by
    have h1 : T.base + T.direction ∈ unitSegment T.base T.direction := by
      refine ⟨1, by norm_num, ?_⟩
      simp
    have h2 : Metric.infEDist (T.base + T.direction) (unitSegment T.base T.direction) ≤
        ENNReal.ofReal δ := by
      have h3 : Metric.infEDist (T.base + T.direction) (unitSegment T.base T.direction) ≤
          edist (T.base + T.direction) (T.base + T.direction) :=
        Metric.infEDist_le_edist_of_mem h1
      have h4 : edist (T.base + T.direction) (T.base + T.direction) = 0 := edist_self _
      rw [h4] at h3
      exact le_trans h3 (by simp)
    exact h2

  -- Both endpoints lie in the outer axis-aligned box (in frame coordinates).
  have h_p'_in : p' ∈ axisBox (A * a) (A * b) (A * c) := by
    have h_base_K : T.base ∈ K.carrier := h_sub h_base_in
    have h_base_img : T.base ∈ frame '' axisBox (A * a) (A * b) (A * c) := h_outer h_base_K
    rcases h_base_img with ⟨x, hx, hfx⟩
    have h_x_eq : x = frame.symm T.base := by
      have h : frame x = T.base := hfx
      exact (frame.eq_symm_apply).mpr h
    have h_goal : frame.symm T.base ∈ axisBox (A * a) (A * b) (A * c) := by
      rw [← h_x_eq]
      exact hx
    simpa [hp'_def] using h_goal
  have h_q'_in : q' ∈ axisBox (A * a) (A * b) (A * c) := by
    have h_end_K : T.base + T.direction ∈ K.carrier := h_sub h_end_in
    have h_end_img : T.base + T.direction ∈ frame '' axisBox (A * a) (A * b) (A * c) :=
      h_outer h_end_K
    rcases h_end_img with ⟨x, hx, hfx⟩
    have h_x_eq : x = frame.symm (T.base + T.direction) := by
      have h : frame x = T.base + T.direction := hfx
      exact (frame.eq_symm_apply).mpr h
    have h_goal : frame.symm (T.base + T.direction) ∈ axisBox (A * a) (A * b) (A * c) := by
      rw [← h_x_eq]
      exact hx
    simpa [hq'_def] using h_goal

  -- The second endpoint equals p' + u' in frame coordinates.
  have h_q'_add : q' = p' + u' := by
    rw [hq'_def, hp'_def, hu'_def]
    have h := frame.symm.map_vadd (p := T.base) (v := T.direction)
    have h1 : (T.direction +ᵥ T.base) = T.base + T.direction := by
      simp [vadd_eq_add, add_comm]
    have h2 : (frame.symm.linearIsometryEquiv T.direction +ᵥ frame.symm T.base) =
        frame.symm T.base + frame.symm.linearIsometryEquiv T.direction := by
      simp [vadd_eq_add, add_comm]
    rw [h1, h2] at h
    exact h

  rcases h_p'_in with ⟨h_p0, h_p1, h_p2⟩
  rcases h_q'_in with ⟨h_q0, h_q1, h_q2⟩

  have h_u0 : |u' 0| ≤ A * a := by
    have h_eq : u' 0 = q' 0 - p' 0 := by
      rw [h_q'_add]; simp
    rw [h_eq]
    calc |q' 0 - p' 0|
        ≤ |q' 0| + |p' 0| := abs_sub _ _
      _ ≤ A * a / 2 + A * a / 2 := by gcongr
      _ = A * a := by ring
  have h_u1 : |u' 1| ≤ A * b := by
    have h_eq : u' 1 = q' 1 - p' 1 := by
      rw [h_q'_add]; simp
    rw [h_eq]
    calc |q' 1 - p' 1|
        ≤ |q' 1| + |p' 1| := abs_sub _ _
      _ ≤ A * b / 2 + A * b / 2 := by gcongr
      _ = A * b := by ring
  have h_u2 : |u' 2| ≤ A * c := by
    have h_eq : u' 2 = q' 2 - p' 2 := by
      rw [h_q'_add]; simp
    rw [h_eq]
    calc |q' 2 - p' 2|
        ≤ |q' 2| + |p' 2| := abs_sub _ _
      _ ≤ A * c / 2 + A * c / 2 := by gcongr
      _ = A * c := by ring

  exact ⟨h_p0, h_p1, h_p2, h_u0, h_u1, h_u2⟩

/--
Specialization to a plank with dimensions `a × b × 1`.
The transverse direction components (coordinates 0 and 1) are bounded by `A*a`
and `A*b` respectively; the base coordinates are bounded by the corresponding
half-widths.
-/
theorem tube_in_plank_direction_bound
    {δ : ℝ} (T : DeltaTube δ) (plank : Body)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3) (a b A : ℝ)
    (h_dim : plank.HasDimensionsInFrame frame a b 1 A)
    (h_sub : T.carrier ⊆ plank.carrier) :
    |(frame.symm T.base) 0| ≤ A * a / 2 ∧
    |(frame.symm T.base) 1| ≤ A * b / 2 ∧
    |(frame.symm T.base) 2| ≤ A / 2 ∧
    |(frame.symm.linearIsometryEquiv T.direction) 0| ≤ A * a ∧
    |(frame.symm.linearIsometryEquiv T.direction) 1| ≤ A * b ∧
    |(frame.symm.linearIsometryEquiv T.direction) 2| ≤ A :=
  by
    have h := tube_in_frame_direction_bound T plank frame a b 1 A h_dim h_sub
    simpa [mul_one] using h

end Kakeya.Streamlined.GeometricLemmas

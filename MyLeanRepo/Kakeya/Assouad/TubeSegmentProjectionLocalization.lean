import MyLeanRepo.Kakeya.Assouad.Statements

/-!
WZ Lemma 30: localize the scalar projection of a thickened tube-axis segment
around the projection of its midpoint, with the exact radial and axial errors.
-/

namespace Kakeya.Assouad

theorem tube_segment_projection_localization :
    TubeSegmentProjectionLocalizationStatement := by
  intro delta rho start hdelta hrho base direction v hv
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  let axisSet : Set Point3 :=
    (fun t : ℝ => base + t • direction) '' Set.Icc start (start + Real.sqrt rho)
  have h_compact : IsCompact axisSet := by
    apply IsCompact.image
    · exact isCompact_Icc
    · exact continuous_const.add (continuous_id.smul continuous_const)
  have h_closed : IsClosed axisSet := h_compact.isClosed
  have h1 : p ∈ Metric.cthickening delta axisSet := hp
  have h_closure : closure axisSet = axisSet := h_closed.closure_eq
  have h2 : ∃ (x : Point3), x ∈ axisSet ∧ dist p x ≤ delta := by
    have h_eq : Metric.cthickening delta axisSet =
        ⋃ x ∈ closure axisSet, Metric.closedBall x delta :=
      Metric.cthickening_eq_biUnion_closedBall axisSet hdelta
    rw [h_eq, h_closure] at h1
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using h1
  rcases h2 with ⟨x, hx, hdist⟩
  rcases hx with ⟨t, ht, rfl⟩
  have ht1 : start ≤ t := ht.1
  have ht2 : t ≤ start + Real.sqrt rho := ht.2
  set mid := start + Real.sqrt rho / 2 with hmid
  have hsqrt_nonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have h_t_bound : |t - mid| ≤ Real.sqrt rho / 2 := by
    have h5 : -(Real.sqrt rho / 2) ≤ t - mid := by
      rw [hmid]
      linarith
    have h6 : t - mid ≤ Real.sqrt rho / 2 := by
      rw [hmid]
      linarith
    exact abs_le.mpr ⟨h5, h6⟩
  set axis_t := base + t • direction with haxis_t
  set axis_mid := base + mid • direction with haxis_mid
  have h_main : |inner ℝ p v - inner ℝ axis_mid v| ≤
      delta + |inner ℝ direction v| * Real.sqrt rho / 2 := by
    have h7 : inner ℝ p v - inner ℝ axis_mid v =
        inner ℝ (p - axis_t) v + (t - mid) * inner ℝ direction v := by
      simp [axis_t, axis_mid, inner_add_left, inner_sub_left, inner_smul_left]
      ring
    rw [h7]
    have h8 : |inner ℝ (p - axis_t) v| ≤ delta := by
      have h9 : |inner ℝ (p - axis_t) v| ≤ ‖p - axis_t‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      have h10 : ‖p - axis_t‖ = dist p axis_t := by rfl
      rw [h10, hv] at h9
      linarith [hdist]
    have h11 : |(t - mid) * inner ℝ direction v| ≤
        |inner ℝ direction v| * Real.sqrt rho / 2 := by
      calc
        |(t - mid) * inner ℝ direction v|
          = |t - mid| * |inner ℝ direction v| := by rw [abs_mul]
        _ ≤ (Real.sqrt rho / 2) * |inner ℝ direction v| := by
          gcongr
        _ = |inner ℝ direction v| * Real.sqrt rho / 2 := by ring
    have h12 : |inner ℝ (p - axis_t) v + (t - mid) * inner ℝ direction v| ≤
        |inner ℝ (p - axis_t) v| + |(t - mid) * inner ℝ direction v| :=
      abs_add_le _ _
    linarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using h_main

end Kakeya.Assouad

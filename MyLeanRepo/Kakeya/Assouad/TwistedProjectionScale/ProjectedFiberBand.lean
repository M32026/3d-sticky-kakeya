import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBandStatements

/-!
WZ2 Section 7: select one dyadic band of the fiber-integrated projected
multiplicity and pull it back to a same-family shading.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem projected_fiber_band :
    ProjectedFiberBandStatement := by
  intro h_mass h_cap h_pullback h_band
  intro delta hδ_pos hδ_one F hF_nonempty hvert hparams Y hY_slab hY_mass_nonzero hY_mass_ne_top f h_ns h0 threshold h_thresh_nonzero h_thresh_ne_top h_lowtail levelCount h_level

  -- Step 1: Measurability and total integral
  have h1 := h_mass F Y f
  have h_meas : Measurable (projectedFiberMultiplicity Y f) := h1.1
  have h_integral : (∫⁻ q : Point2, projectedFiberMultiplicity Y f q) = Y.mass := h1.2

  -- Step 2: IsInSlopeWindow from horizontalSlab 0 1 containment
  have h_slope_window : IsInSlopeWindow Y := by
    have h1 : horizontalSlab (0 : ℝ) 1 ⊆ horizontalSlab (-1 : ℝ) 1 := by
      intro x hx
      have h2 : x 2 ∈ Set.Icc (0 : ℝ) 1 := by simpa [horizontalSlab] using hx
      have h3 : x 2 ∈ Set.Icc (-1 : ℝ) 1 := by
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
      simpa [horizontalSlab] using h3
    exact Set.Subset.trans hY_slab h1

  -- Support containment: fiber multiplicity vanishes outside the rectangle
  have hsupport : ∀ q, q ∉ section7ProjectionRectangle → projectedFiberMultiplicity Y f q = 0 := by
    intro q hq
    have h : ∀ y : ℝ, (Y.pointMultiplicity (point3 (q 0 - f (q 1) * y) y (q 1)) : ENNReal) = 0 := by
      intro y
      by_contra h2
      have h3 : Y.pointMultiplicity (point3 (q 0 - f (q 1) * y) y (q 1)) ≠ 0 := by exact_mod_cast h2
      let p := point3 (q 0 - f (q 1) * y) y (q 1)
      have h4 : p ∈ Y.union := by
        classical
        have h_pos : 0 < Y.pointMultiplicity p := Nat.pos_of_ne_zero h3
        have h_nonempty : (Finset.univ.filter fun i : Fin F.card => p ∈ Y.carrier i).Nonempty :=
          Finset.card_pos.mp h_pos
        rcases h_nonempty with ⟨i, hi⟩
        have h_i_in : p ∈ Y.carrier i := (Finset.mem_filter.mp hi).2
        exact ⟨i, h_i_in⟩
      have h_p0 : p 0 = q 0 - f (q 1) * y := by
        simp [p, point3, EuclideanSpace.single]
      have h_p1 : p 1 = y := by
        simp [p, point3, EuclideanSpace.single]
      have h_p2 : p 2 = q 1 := by
        simp [p, point3, EuclideanSpace.single]
      have h_coord0 : (twistedProjection f p) 0 = q 0 := by
        have h_eq : (twistedProjection f p) 0 = p 0 + f (p 2) * p 1 := by simp [twistedProjection]
        rw [h_eq, h_p0, h_p1, h_p2] <;> ring
      have h_coord1 : (twistedProjection f p) 1 = q 1 := by
        have h_eq : (twistedProjection f p) 1 = p 2 := by simp [twistedProjection]
        rw [h_eq, h_p2]
      have h_all : ∀ (i : Fin 2), (twistedProjection f p) i = q i := by
        intro i
        by_cases h : i = 0
        · rw [h]; exact h_coord0
        · have h' : i = 1 := by
            simp only [Fin.ext_iff] at h ⊢ <;> omega
          rw [h']; exact h_coord1
      have h5 : twistedProjection f p = q := by
        ext i
        exact h_all i
      have h6 : q ∈ twistedUnion Y f := ⟨p, h4, h5⟩
      have h7 : q ∈ section7ProjectionRectangle :=
        twisted_union_contained_of_params hparams hvert hδ_pos hδ_one h_slope_window h_ns h0 h6
      exact hq h7
    have h_def : projectedFiberMultiplicity Y f q =
        ∫⁻ (y : ℝ), (Y.pointMultiplicity (point3 (q 0 - f (q 1) * y) y (q 1)) : ENNReal) := by
      rfl
    rw [h_def]
    rw [MeasureTheory.lintegral_congr h]
    simp

  -- Step 3: Pointwise upper bound
  set b : ENNReal := ENNReal.ofReal (6 * delta) * F.enncard with hb_def
  have h_pointwise_cap : ∀ q, projectedFiberMultiplicity Y f q ≤ b :=
    h_cap hδ_pos F hvert Y f
  have hb_ne_top : b ≠ ⊤ := by
    rw [hb_def]
    have h1 : ENNReal.ofReal (6 * delta) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : F.enncard ≠ ⊤ := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]
    exact ENNReal.mul_ne_top h1 h2

  -- Step 4: Rectangle measurability
  have hX_meas : MeasurableSet section7ProjectionRectangle := by
    have h3 : Measurable (fun q : Point2 => q 0) := by fun_prop
    have h4 : Measurable (fun q : Point2 => q 1) := by fun_prop
    have h5 : MeasurableSet {q : Point2 | |q 0| ≤ 51} := by
      have h6 : {q : Point2 | |q 0| ≤ 51} = (fun q : Point2 => q 0) ⁻¹' (Set.Icc (-51 : ℝ) 51) := by
        ext q; simp [abs_le]
      rw [h6]; exact measurableSet_Icc.preimage h3
    have h7 : MeasurableSet {q : Point2 | |q 1| ≤ 1} := by
      have h8 : {q : Point2 | |q 1| ≤ 1} = (fun q : Point2 => q 1) ⁻¹' (Set.Icc (-1 : ℝ) 1) := by
        ext q; simp [abs_le]
      rw [h8]; exact measurableSet_Icc.preimage h4
    have h9 : section7ProjectionRectangle = {q : Point2 | |q 0| ≤ 51} ∩ {q : Point2 | |q 1| ≤ 1} := by
      ext q; simp [section7ProjectionRectangle]
    rw [h9]
    exact h5.inter h7

  -- Rectangle finite volume
  have hX_fin : volume section7ProjectionRectangle ≠ ⊤ := by
    have h1 : section7ProjectionRectangle ⊆ Metric.closedBall (0 : Point2) 52 := by
      intro p hp
      have h4 : |p 0| ≤ 51 := hp.1
      have h5 : |p 1| ≤ 1 := hp.2
      have h6 : ‖p‖ ≤ 52 := by
        have h7 : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 := by
          simp [EuclideanSpace.real_norm_sq_eq]
        nlinarith [abs_le.mp h4, abs_le.mp h5]
      simpa [Metric.mem_closedBall] using h6
    have h_bdd : Bornology.IsBounded section7ProjectionRectangle :=
      Metric.isBounded_closedBall.subset h1
    exact h_bdd.measure_lt_top.ne

  -- Integral nonzero and non-top
  have h_I_nonzero : (∫⁻ q : Point2, projectedFiberMultiplicity Y f q) ≠ 0 := by
    rw [h_integral] <;> exact hY_mass_nonzero
  have h_I_ne_top : (∫⁻ q : Point2, projectedFiberMultiplicity Y f q) ≠ ⊤ := by
    rw [h_integral] <;> exact hY_mass_ne_top

  -- Rewrite lowtail to use the integral
  have h_lowtail' : 2 * (threshold * volume section7ProjectionRectangle) ≤ ∫⁻ q : Point2, projectedFiberMultiplicity Y f q := by
    rw [h_integral]
    exact h_lowtail

  -- Step 5: Apply dyadic integral band selector
  rcases h_band Point2 volume (projectedFiberMultiplicity Y f) h_meas
    section7ProjectionRectangle hX_meas hsupport hX_fin
    threshold b h_thresh_nonzero h_thresh_ne_top hb_ne_top h_pointwise_cap
    levelCount h_level h_lowtail' h_I_nonzero h_I_ne_top
    with ⟨k, hk_le, hB_meas, hB_subset, h_retention⟩

  -- Step 6: Construct the band data
  let band := dyadicValueBand (projectedFiberMultiplicity Y f) threshold k
  let shading := projectionPullbackShading Y f band hB_meas

  have h_mass_id : shading.mass = ∫⁻ q in band, projectedFiberMultiplicity Y f q :=
    h_pullback F Y f band hB_meas

  have h_retention' : Y.mass ≤ 2 * (levelCount + 1 : ENNReal) * shading.mass := by
    have h9 : (∫⁻ q : Point2, projectedFiberMultiplicity Y f q) ≤
        2 * (levelCount + 1 : ENNReal) * ∫⁻ q in band, projectedFiberMultiplicity Y f q := h_retention
    rw [h_integral] at h9
    rw [h_mass_id] at *
    <;> exact h9

  exact ⟨k, hk_le, band, rfl, hB_meas, hB_subset, shading, rfl,
    projectionPullback_isSubshading Y f band hB_meas,
    h_mass_id, h_retention',
    (fun q hq => (Set.mem_setOf_eq.mp hq).1),
    (fun q hq => (Set.mem_setOf_eq.mp hq).2),
    projectionPullback_twistedUnion_subset Y f band hB_meas⟩

end Kakeya.Assouad

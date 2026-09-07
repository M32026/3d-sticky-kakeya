import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackSupportStatement

/-!
# Exact support of a projected-fiber pullback shading

A pointwise positive projected-fiber density supplies an actual shaded point
on every retained fiber, giving the reverse support inclusion.
-/

namespace Kakeya.Assouad

theorem projected_fiber_pullback_support :
    ProjectedFiberPullbackSupportStatement := by
  intro delta F Y f X hX hpos
  have h1 :
      twistedUnion (projectionPullbackShading Y f X hX) f ⊆ X :=
    projectionPullback_twistedUnion_subset Y f X hX
  have h2 :
      X ⊆ twistedUnion (projectionPullbackShading Y f X hX) f := by
    intro q hq
    have hmult : projectedFiberMultiplicity Y f q ≠ 0 :=
      hpos q hq
    have h3 : ∃ (y : ℝ),
        (Y.pointMultiplicity
          (point3 (q 0 - f (q 1) * y) y (q 1)) : ENNReal) ≠ 0 := by
      by_contra h
      push Not at h
      have h4 : (fun y : ℝ => (Y.pointMultiplicity
          (point3 (q 0 - f (q 1) * y) y (q 1)) : ENNReal)) = 0 := by
        funext y
        exact h y
      have h5 : projectedFiberMultiplicity Y f q = 0 := by
        rw [projectedFiberMultiplicity, h4]
        exact MeasureTheory.lintegral_eq_zero_of_ae_eq_zero
          (Filter.Eventually.of_forall fun _ => rfl)
      exact hmult h5
    rcases h3 with ⟨y, hy⟩
    let p : Point3 :=
      point3 (q 0 - f (q 1) * y) y (q 1)
    have hpm_ne_zero : Y.pointMultiplicity p ≠ 0 := by
      exact_mod_cast hy
    have hpm_pos : 0 < Y.pointMultiplicity p :=
      Nat.pos_of_ne_zero hpm_ne_zero
    have h4 :
        ∃ (i : Fin F.toBodyFamily.card), p ∈ Y.carrier i := by
      classical
      have h5 :
          (Finset.univ.filter fun i : Fin F.toBodyFamily.card =>
            p ∈ Y.carrier i).Nonempty :=
        Finset.card_pos.mp (by
          simpa [Kakeya.Streamlined.Shading.pointMultiplicity] using
            hpm_pos)
      rcases h5 with ⟨i, hi⟩
      have h6 : p ∈ Y.carrier i :=
        (Finset.mem_filter.mp hi).2
      exact ⟨i, h6⟩
    rcases h4 with ⟨i, hi⟩
    have htp : twistedProjection f p = q := by
      ext j
      fin_cases j <;> simp [twistedProjection, p, point3]
    have hpre : p ∈ twistedProjection f ⁻¹' X := by
      have h7 : twistedProjection f p ∈ X := by
        rw [htp]
        exact hq
      exact h7
    have h5 :
        p ∈ (projectionPullbackShading Y f X hX).carrier i := by
      simp only [projectionPullbackShading]
      exact ⟨hi, hpre⟩
    have h6 :
        p ∈ (projectionPullbackShading Y f X hX).union :=
      ⟨i, h5⟩
    exact ⟨p, h6, htp⟩
  apply Set.Subset.antisymm h1 h2

end Kakeya.Assouad

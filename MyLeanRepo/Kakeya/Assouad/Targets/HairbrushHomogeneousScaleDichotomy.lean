import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves

/-!
# Homogeneous two-ends scale dichotomy

This is the numerical split at (B.20)--(B.21) in the self-contained
Appendix-B proof.  The low-density branch is explicit; its complement supplies
the scale separation consumed by the homogeneous far-radius leaf.
-/

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_scale_dichotomy :
    HairbrushHomogeneousScaleDichotomyStatement := by
  intro δ zeta familyLoss separation angleScale sigma hδ hzeta_pos hzeta_lt_one
    hsep hang hangle_sigma H Z hairDensity twoEnds
  let threshold := hairbrushHomogeneousLowDensityThreshold δ zeta separation angleScale
  by_cases h : hairDensity ≤ threshold
  · exact Or.inl h
  · -- Complementary case: threshold < hairDensity
    have h' : threshold < hairDensity := by exact lt_of_not_ge h
    have hrel : hairDensity ≤ ENNReal.ofReal 100 *
        ENNReal.ofReal (Real.rpow twoEnds.radius (1 - zeta)) :=
      twoEnds.density_radius_relation
    have h1 : threshold < ENNReal.ofReal 100 *
        ENNReal.ofReal (Real.rpow twoEnds.radius (1 - zeta)) :=
      lt_of_lt_of_le h' hrel
    have h_pos1 : 0 < separation * δ / angleScale := by positivity
    have h_radius_pos : 0 < twoEnds.radius := by
      linarith [twoEnds.delta_le_radius]
    have h_exp_pos : 0 < 1 - zeta := by linarith
    have h_rpow_nonneg1 : 0 ≤ Real.rpow (separation * δ / angleScale) (1 - zeta) :=
      Real.rpow_nonneg (by positivity) _
    have h100_ne_zero : (ENNReal.ofReal 100 : ENNReal) ≠ 0 := by simp
    have h100_ne_top : (ENNReal.ofReal 100 : ENNReal) ≠ ⊤ := by simp
    have h2 : ENNReal.ofReal (Real.rpow (separation * δ / angleScale) (1 - zeta)) <
        ENNReal.ofReal (Real.rpow twoEnds.radius (1 - zeta)) := by
      have h3 : ENNReal.ofReal 100 *
          ENNReal.ofReal (Real.rpow (separation * δ / angleScale) (1 - zeta)) <
          ENNReal.ofReal 100 *
          ENNReal.ofReal (Real.rpow twoEnds.radius (1 - zeta)) := by
        simpa [threshold, hairbrushHomogeneousLowDensityThreshold] using h1
      exact (ENNReal.mul_lt_mul_iff_right h100_ne_zero h100_ne_top).mp h3
    have h4 : Real.rpow (separation * δ / angleScale) (1 - zeta) <
        Real.rpow twoEnds.radius (1 - zeta) := by
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_rpow_nonneg1).mp h2
    have h5 : separation * δ / angleScale < twoEnds.radius := by
      exact (Real.rpow_lt_rpow_iff (by positivity) (by positivity) h_exp_pos).mp h4
    have h6 : separation * δ < angleScale * twoEnds.radius := by
      have h7 : (separation * δ / angleScale) * angleScale < twoEnds.radius * angleScale :=
        mul_lt_mul_of_pos_right h5 hang
      have h8 : (separation * δ / angleScale) * angleScale = separation * δ := by
        field_simp [hang.ne']
        <;> ring
      rw [h8] at h7
      linarith [mul_comm twoEnds.radius angleScale]
    have h9 : angleScale * twoEnds.radius ≤ sigma * twoEnds.radius := by
      exact mul_le_mul_of_nonneg_right hangle_sigma (by linarith)
    have h10 : separation * δ ≤ sigma * twoEnds.radius := by linarith
    exact Or.inr h10

end Kakeya.Assouad

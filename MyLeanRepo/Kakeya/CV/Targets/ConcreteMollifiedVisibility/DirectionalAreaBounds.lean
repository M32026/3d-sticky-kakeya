import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MainAssembly


/-!
# Directional surface area bounds

Helper lemmas for the concrete mollified visibility theorem:
- `directionalSurfaceArea_zero`: zero polynomial has zero surface area
- `directionalSurfaceArea_U_bound`: uniform bound over a bounded region `U`
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace BigOperators

namespace Kakeya.CV

/-- The directional surface area of the zero polynomial is zero. -/
lemma directionalSurfaceArea_zero (e : Point 3) (S : Set (Point 3)) :
    directionalSurfaceArea e (0 : MvPolynomial (Fin 3) ℝ) S = 0 := by
  have h1 : ∀ (x : Point 3), polynomialGradient (0 : MvPolynomial (Fin 3) ℝ) x = 0 := by
    intro x
    simp [polynomialGradient] <;> rfl
  have h2 : ∀ (x : Point 3), polynomialUnitNormal (0 : MvPolynomial (Fin 3) ℝ) x = 0 := by
    intro x
    rw [polynomialUnitNormal]
    have h3 : ‖polynomialGradient (0 : MvPolynomial (Fin 3) ℝ) x‖ = 0 := by
      rw [h1 x] <;> simp
    rw [dif_pos h3] <;> simp
  have h4 : ∀ (x : Point 3),
      ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal (0 : MvPolynomial (Fin 3) ℝ) x)‖ = 0 := by
    intro x
    rw [h2 x] <;> simp
  have h5 : ∀ (x : Point 3), x ∈ S →
      ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal (0 : MvPolynomial (Fin 3) ℝ) x)‖ = 0 := by
    intro x _
    exact h4 x
  have h6 : (∫⁻ (x : Point 3) in S,
      ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal (0 : MvPolynomial (Fin 3) ℝ) x)‖
        ∂(MeasureTheory.Measure.hausdorffMeasure 2)) = 0 :=
    set_lintegral_eq_zero_of_forall h5
  simpa [directionalSurfaceArea] using h6

/-- Uniform bound on directional surface area over `U ⊆ closedBall c 1`. -/
lemma directionalSurfaceArea_U_bound
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hk : p.totalDegree ≤ k)
    (U : Set (Point 3)) (c : Point 3) (hU : U ⊆ Metric.closedBall c 1)
    (u : Point 3) :
    directionalSurfaceArea u p (polynomialZeroSet p ∩ U) ≤
      (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ℝ≥0∞)) *
      ENNReal.ofReal ‖u‖ := by
  let B : ENNReal := 12 * planeConstant * ENNReal.ofReal Real.pi * (k : ℝ≥0∞)
  by_cases hz : u = 0
  · -- u = 0
    subst hz
    have h5 : directionalSurfaceArea (0 : Point 3) p (polynomialZeroSet p ∩ U) = 0 := by
      have h6 := directionalSurfaceArea_homogeneity (0 : ℝ) (by norm_num) (0 : Point 3) p (polynomialZeroSet p ∩ U)
      simpa using h6
    rw [h5] <;> simp
  · -- u ≠ 0
    have hnorm_pos : 0 < ‖u‖ := by
      rw [norm_pos_iff] <;> exact hz
    let u' : Point 3 := ‖u‖⁻¹ • u
    have hu'_norm : ‖u'‖ = 1 := by
      simp [u', norm_smul, hnorm_pos.ne'] <;> field_simp [hnorm_pos.ne'] <;> norm_num
    have hU_tube : U ⊆ unitTube c u' := by
      calc U
        ⊆ Metric.closedBall c 1 := hU
      _ ⊆ unitTube c u' := unitBall_subset_unitTube c u' hu'_norm
    have hS_subset : polynomialZeroSet p ∩ U ⊆ polynomialZeroSet p ∩ unitTube c u' :=
      Set.inter_subset_inter_right _ hU_tube
    have h_cyl : directionalSurfaceArea u' p (polynomialZeroSet p ∩ U) ≤ B := by
      calc directionalSurfaceArea u' p (polynomialZeroSet p ∩ U)
        ≤ directionalSurfaceArea u' p (polynomialZeroSet p ∩ unitTube c u') :=
          directionalSurfaceArea_mono u' p hS_subset
      _ ≤ B := by
        by_cases hp : p = 0
        · rw [hp]
          rw [directionalSurfaceArea_zero] <;> positivity
        · rcases exists_rotation_to_e3 u' hu'_norm with ⟨R, hR⟩
          let p' := rotatedPoly p R
          have hp'_ne : p' ≠ 0 := rotatedPoly_ne_zero p R hp
          have hp'_deg : p'.totalDegree ≤ k :=
            (rotatedPoly_totalDegree_le p R).trans hk
          let S := polynomialZeroSet p ∩ unitTube c u'
          let S' := polynomialZeroSet p' ∩ unitTube (R c) e3
          have hS1 : R '' polynomialZeroSet p = polynomialZeroSet p' := rotated_zeroSet p R
          have hS2 : R '' unitTube c u' = unitTube (R c) e3 := rotated_unitTube R c u' hR
          have hS' : R '' S = S' := by
            have h : R '' S = (R '' polynomialZeroSet p) ∩ (R '' unitTube c u') := by
              ext y
              simp only [Set.mem_image, Set.mem_inter_iff]
              constructor
              · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
                exact ⟨⟨x, hx1, rfl⟩, ⟨x, hx2, rfl⟩⟩
              · rintro ⟨⟨x1, hx1, rfl⟩, ⟨x2, hx2, h_eq⟩⟩
                have h_xeq : x2 = x1 := R.injective h_eq
                rw [h_xeq] at hx2
                exact ⟨x1, ⟨hx1, hx2⟩, rfl⟩
            rw [h, hS1, hS2] <;> rfl
          have h_transfer : directionalSurfaceArea u' p S = directionalSurfaceArea e3 p' S' := by
            have h_tmp := directionalSurfaceArea_transfer p R u' hR S
            rw [hS'] at h_tmp
            exact h_tmp
          rw [h_transfer]
          exact directional_estimate_e3 p' (R c) k hp'_ne hp'_deg
    have h_u_eq : u = ‖u‖ • u' := by
      simp [u', smul_smul] <;> field_simp [hnorm_pos.ne'] <;> simp
    have h_hom : directionalSurfaceArea (‖u‖ • u') p (polynomialZeroSet p ∩ U) =
        ENNReal.ofReal ‖u‖ * directionalSurfaceArea u' p (polynomialZeroSet p ∩ U) :=
      directionalSurfaceArea_homogeneity (‖u‖) (by positivity) u' p (polynomialZeroSet p ∩ U)
    have h9 : directionalSurfaceArea u p (polynomialZeroSet p ∩ U) =
        directionalSurfaceArea (‖u‖ • u') p (polynomialZeroSet p ∩ U) :=
      congr_arg (fun v : Point 3 => directionalSurfaceArea v p (polynomialZeroSet p ∩ U)) h_u_eq
    have h10 : directionalSurfaceArea u p (polynomialZeroSet p ∩ U) ≤
        B * ENNReal.ofReal ‖u‖ := by
      rw [h9, h_hom]
      have h11 : ENNReal.ofReal ‖u‖ * directionalSurfaceArea u' p (polynomialZeroSet p ∩ U) ≤
          ENNReal.ofReal ‖u‖ * B := by gcongr
      have h12 : ENNReal.ofReal ‖u‖ * B = B * ENNReal.ofReal ‖u‖ := by ring
      rw [h12] at h11
      exact h11
    exact h10

end Kakeya.CV

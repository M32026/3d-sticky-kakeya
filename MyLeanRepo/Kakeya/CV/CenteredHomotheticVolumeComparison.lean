import MyLeanRepo.Kakeya.CV.Statements

/-!
# Volume comparison for centered homothetically close bodies

Converts the homothetic inclusions used by the stable ellipsoid palette into
the cubic volume bounds needed to count translate indices.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Real

namespace Kakeya.CV

theorem centered_homothetic_volume_comparison :
    CenteredHomotheticVolumeComparisonStatement := by
  intro α K A hα _hK hclose
  let E := JohnEllipsoid.ellipsoid 0 A
  have h1 : dilateAbout 0 α⁻¹ K ⊆ E := hclose.1
  have h2 : E ⊆ dilateAbout 0 α K := hclose.2
  have hα_nonneg : 0 ≤ α := by linarith
  have hαinv_nonneg : 0 ≤ α⁻¹ := by positivity
  have hfinrank : Module.finrank ℝ (Point 3) = 3 := finrank_euclideanSpace_fin
  have h_dilate_zero : ∀ (r : ℝ) (S : Set (Point 3)),
      dilateAbout 0 r S = (fun x : Point 3 => r • x) '' S := by
    intro r S
    ext y
    simp only [dilateAbout, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [AffineMap.homothety_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [AffineMap.homothety_apply]⟩
  have hvol1 : volume (dilateAbout 0 α⁻¹ K) =
      ENNReal.ofReal (α⁻¹ ^ 3) * volume K := by
    rw [h_dilate_zero α⁻¹ K]
    have h : volume ((fun x : Point 3 => α⁻¹ • x) '' K) =
        ENNReal.ofReal (α⁻¹ ^ Module.finrank ℝ (Point 3)) * volume K :=
      MeasureTheory.Measure.addHaar_smul_of_nonneg volume hαinv_nonneg K
    rw [h, hfinrank]
  have hvol2 : volume (dilateAbout 0 α K) =
      ENNReal.ofReal (α ^ 3) * volume K := by
    rw [h_dilate_zero α K]
    have h : volume ((fun x : Point 3 => α • x) '' K) =
        ENNReal.ofReal (α ^ Module.finrank ℝ (Point 3)) * volume K :=
      MeasureTheory.Measure.addHaar_smul_of_nonneg volume hα_nonneg K
    rw [h, hfinrank]
  have hineq1 : volume (dilateAbout 0 α⁻¹ K) ≤ volume E :=
    measure_mono h1
  have hineq2 : volume E ≤ volume (dilateAbout 0 α K) :=
    measure_mono h2
  rw [hvol1] at hineq1
  rw [hvol2] at hineq2
  exact ⟨hineq1, hineq2⟩

end Kakeya.CV

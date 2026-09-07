import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Volume scaling under the anisotropic rescaling map

The anisotropic map Φ has linear part L with determinant m.
For any measurable set A, volume(Φ '' A) = m * volume(A).
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The matrix of the linear part (upper triangular). -/
private def anisotropicMatrix (g : SlopeFunction) (c d m : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, g (c + (d - c) / 2), 0;
     0, m * (d - c) / 2, 0;
     0, 0, 2 / (d - c)]

/-- The linear part from the matrix via PiLp matrix action. -/
def anisotropicRescalingLinearMap (g : SlopeFunction) (c d m : ℝ) :
    Point3 →ₗ[ℝ] Point3 :=
  Matrix.toLpLin 2 2 (anisotropicMatrix g c d m)

/-- Continuous linear map version. -/
def anisotropicRescalingLinear (g : SlopeFunction) (c d m : ℝ) :
    Point3 →L[ℝ] Point3 :=
  (anisotropicRescalingLinearMap g c d m).toContinuousLinearMap

/-- Determinant of the matrix is m. -/
private lemma anisotropicMatrix_det
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d) :
    (anisotropicMatrix g c d m).det = m := by
  let M := anisotropicMatrix g c d m
  have hUpper : M.BlockTriangular id := by
    intro i j h
    have h' : j < i := by simpa using h
    fin_cases i <;> fin_cases j <;>
      (try { contradiction }) <;>
      (try { simp [M, anisotropicMatrix] <;> rfl })
  rw [Matrix.det_of_upperTriangular hUpper]
  have hell : d - c ≠ 0 := by linarith
  simp [M, anisotropicMatrix, Fin.prod_univ_three, hell]
  <;> field_simp [hell] <;> ring

/-- Determinant of the linear map is m. -/
lemma anisotropicRescalingLinear_det
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d) (hm : 0 < m) :
    LinearMap.det (anisotropicRescalingLinearMap g c d m) = m := by
  have h_def : anisotropicRescalingLinearMap g c d m =
      Matrix.toLpLin 2 2 (anisotropicMatrix g c d m) := by rfl
  rw [h_def]
  rw [LinearMap.det_toLpLin 2 (anisotropicMatrix g c d m)]
  exact anisotropicMatrix_det g hcd

/-- Helper: matrix-vector product coordinate formula. -/
private lemma toLpLin_coord
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) (i : Fin 3) :
    (anisotropicRescalingLinearMap g c d m p) i =
      ∑ j : Fin 3, (anisotropicMatrix g c d m) i j * p j := by
  rw [anisotropicRescalingLinearMap, Matrix.toLpLin_apply]
  simp [Matrix.mulVec]
  <;> rfl

/-- Coordinate 0 of the linear map. -/
lemma anisotropicRescalingLinearMap_apply_zero
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    (anisotropicRescalingLinearMap g c d m p) 0 =
      p 0 + g (c + (d - c) / 2) * p 1 := by
  rw [toLpLin_coord g c d m p 0]
  simp [anisotropicMatrix, Fin.sum_univ_three] <;> ring

/-- Coordinate 1 of the linear map. -/
lemma anisotropicRescalingLinearMap_apply_one
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    (anisotropicRescalingLinearMap g c d m p) 1 =
      (m * (d - c) / 2) * p 1 := by
  rw [toLpLin_coord g c d m p 1]
  simp [anisotropicMatrix, Fin.sum_univ_three] <;> ring

/-- Coordinate 2 of the linear map. -/
lemma anisotropicRescalingLinearMap_apply_two
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    (anisotropicRescalingLinearMap g c d m p) 2 =
      (2 / (d - c)) * p 2 := by
  rw [toLpLin_coord g c d m p 2]
  simp [anisotropicMatrix, Fin.sum_univ_three] <;> ring

/-- The full anisotropic map is the linear part plus a z-translation. -/
lemma anisotropicRescalingMap_eq
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    anisotropicRescalingMap g c d m p =
      anisotropicRescalingLinear g c d m p +
        point3 0 0 (2 * (-c) / (d - c) - 1) := by
  ext i
  fin_cases i <;>
    simp [anisotropicRescalingMap, anisotropicRescalingLinear,
      point3, EuclideanSpace.single_apply,
      anisotropicRescalingLinearMap_apply_zero,
      anisotropicRescalingLinearMap_apply_one,
      anisotropicRescalingLinearMap_apply_two] <;> ring

/--
Volume scaling: for any measurable set A,
volume(Φ '' A) = ENNReal.ofReal m * volume(A).
-/
lemma volume_image_anisotropicRescalingMap
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (A : Set Point3) (hA : MeasurableSet A) :
    MeasureTheory.volume (anisotropicRescalingMap g c d m '' A) =
      ENNReal.ofReal m * MeasureTheory.volume A := by
  let L := anisotropicRescalingLinear g c d m
  let t : Point3 := point3 0 0 (2 * (-c) / (d - c) - 1)
  -- Step 1: image of affine map = translation of image of linear map
  have h1 : (anisotropicRescalingMap g c d m '' A) =
      (fun y : Point3 => y + t) '' (L '' A) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, hz⟩
      have h_eq : anisotropicRescalingMap g c d m x = L x + t :=
        anisotropicRescalingMap_eq g c d m x
      rw [h_eq] at hz
      exact ⟨L x, ⟨x, hx, rfl⟩, hz⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      have h_eq : anisotropicRescalingMap g c d m x = L x + t :=
        anisotropicRescalingMap_eq g c d m x
      exact ⟨x, hx, h_eq⟩
  rw [h1]
  -- Step 2: translation by t preserves volume
  have hmp_sub : MeasureTheory.MeasurePreserving (fun z : Point3 => z - t)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_sub_right MeasureTheory.volume t
  have hmap : MeasureTheory.Measure.map (fun z : Point3 => z - t) MeasureTheory.volume =
      MeasureTheory.volume := hmp_sub.map_eq
  have hLmeas : MeasurableSet (L '' A) := by
    have h_eq : L.toLinearMap = anisotropicRescalingLinearMap g c d m := by rfl
    have hdet' : LinearMap.det L.toLinearMap ≠ 0 := by
      rw [h_eq, anisotropicRescalingLinear_det g hcd hm]
      exact hm.ne'
    let L_equiv : Point3 ≃L[ℝ] Point3 :=
      L.toContinuousLinearEquivOfDetNeZero hdet'
    exact L_equiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hA
  have h2 : (fun y : Point3 => y + t) '' (L '' A) =
      (fun z : Point3 => z - t) ⁻¹' (L '' A) := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨z - t, h, by abel⟩
  rw [h2]
  have h_transl : MeasureTheory.volume ((fun z : Point3 => z - t) ⁻¹' (L '' A)) =
      MeasureTheory.volume (L '' A) := by
    have hmeas : Measurable (fun z : Point3 => z - t) :=
      (continuous_id.sub continuous_const).measurable
    have h_eq : MeasureTheory.Measure.map (fun z : Point3 => z - t) MeasureTheory.volume (L '' A) =
        MeasureTheory.volume ((fun z : Point3 => z - t) ⁻¹' (L '' A)) :=
      MeasureTheory.Measure.map_apply hmeas hLmeas
    have h_main : MeasureTheory.volume ((fun z : Point3 => z - t) ⁻¹' (L '' A)) =
        MeasureTheory.Measure.map (fun z : Point3 => z - t) MeasureTheory.volume (L '' A) :=
      h_eq.symm
    rw [h_main, hmap]
  rw [h_transl]
  -- Step 3: linear map scales volume by |det|
  have hdet : LinearMap.det L.toLinearMap = m :=
    anisotropicRescalingLinear_det g hcd hm
  have h : MeasureTheory.volume (L '' A) =
      ENNReal.ofReal |LinearMap.det L.toLinearMap| * MeasureTheory.volume A :=
    MeasureTheory.Measure.addHaar_image_continuousLinearMap
      MeasureTheory.volume L A
  rw [h, hdet]
  have habs : |m| = m := abs_of_pos hm
  rw [habs]

end Kakeya.Assouad

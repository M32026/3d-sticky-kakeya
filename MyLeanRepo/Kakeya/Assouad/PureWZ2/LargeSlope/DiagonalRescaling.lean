import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Diagonal rescaling for large slope (paper's actual approach)

Paper: sticky_kakeya Lemma 32 + Proposition 29.
Pure diagonal dilation: φ(x,y,z) = (x, m²/100 · y, 100/m · z)
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric Matrix

/-- The diagonal rescaling matrix. -/
def diagonalRescalingMatrix (m : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, m^2 / 100, 100 / m]

/-- The linear part of the diagonal rescaling. -/
def diagonalRescalingLinear (m : ℝ) : Point3 →ₗ[ℝ] Point3 :=
  Matrix.toLpLin 2 2 (diagonalRescalingMatrix m)

/-- The paper's diagonal rescaling map. -/
def diagonalRescalingMap (m : ℝ) (p : Point3) : Point3 :=
  diagonalRescalingLinear m p

lemma diagonalRescalingMap_apply (m : ℝ) (p : Point3) :
    diagonalRescalingMap m p =
      point3 (p 0) (m^2 / 100 * p 1) (100 / m * p 2) := by
  ext i
  fin_cases i <;> simp [diagonalRescalingMap, diagonalRescalingLinear,
    diagonalRescalingMatrix, Matrix.toLpLin_apply, point3, Matrix.mulVec,
    Fin.sum_univ_succ]

/-- Determinant of the diagonal rescaling is m. -/
lemma diagonalRescaling_det (m : ℝ) (hm : 0 < m) :
    LinearMap.det (diagonalRescalingLinear m) = m := by
  rw [diagonalRescalingLinear, LinearMap.det_toLpLin 2 (diagonalRescalingMatrix m)]
  simp [diagonalRescalingMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]
  <;> field_simp [hm.ne'] <;> ring

/-- Volume scaling: volume(Φ '' A) = m * volume(A). -/
lemma volume_image_diagonalRescalingMap
    (m : ℝ) (hm : 0 < m) {A : Set Point3} (hA : MeasurableSet A) :
    volume (diagonalRescalingMap m '' A) =
      ENNReal.ofReal m * volume A := by
  let L : Point3 →L[ℝ] Point3 := (diagonalRescalingLinear m).toContinuousLinearMap
  have h_eq : (diagonalRescalingMap m '' A) = (L '' A) := by rfl
  rw [h_eq]
  have hdet : LinearMap.det (diagonalRescalingLinear m) = m :=
    diagonalRescaling_det m hm
  have h : volume (L '' A) = ENNReal.ofReal |LinearMap.det (diagonalRescalingLinear m)| * volume A :=
    MeasureTheory.Measure.addHaar_image_continuousLinearMap volume L A
  rw [h, hdet]
  have habs : |m| = m := abs_of_pos hm
  rw [habs]

/-- Volume of preimage: volume(Φ⁻¹' W) = (1/m) * volume(W). -/
lemma volume_preimage_diagonalRescalingMap
    (m : ℝ) (hm : 0 < m) {W : Set Point3} (hW : MeasurableSet W) :
    volume ((diagonalRescalingMap m) ⁻¹' W) =
      ENNReal.ofReal (1 / m) * volume W := by
  let L : Point3 →L[ℝ] Point3 := (diagonalRescalingLinear m).toContinuousLinearMap
  have h_eq : (diagonalRescalingMap m ⁻¹' W) = (L ⁻¹' W) := by rfl
  rw [h_eq]
  have hdet : LinearMap.det (diagonalRescalingLinear m) = m :=
    diagonalRescaling_det m hm
  have hdet_ne : LinearMap.det (diagonalRescalingLinear m) ≠ 0 := by
    rw [hdet]; positivity
  have h : volume (L ⁻¹' W) =
      ENNReal.ofReal |(LinearMap.det (diagonalRescalingLinear m))⁻¹| * volume W :=
    MeasureTheory.Measure.addHaar_preimage_linearMap volume hdet_ne W
  rw [h, hdet]
  have h4 : |(m : ℝ)⁻¹| = 1 / m := by
    rw [abs_of_pos (by positivity)] <;> field_simp
  rw [h4]

/-- Preimage of convex set under diagonal rescaling is convex. -/
lemma convex_preimage_diagonalRescalingMap
    (m : ℝ) (_hm : 0 < m) {W : Set Point3} (hW : Convex ℝ W) :
    Convex ℝ ((diagonalRescalingMap m) ⁻¹' W) :=
  hW.linear_preimage (diagonalRescalingLinear m)

/-- The rescaled slope. -/
def diagonalRescaledSlope (f : SlopeFunction) (m : ℝ) : SlopeFunction where
  toFun z := (100 / m^2) * f (m / 100 * z)
  contDiff := by
    have hg_cd : ContDiff ℝ 2 (f : ℝ → ℝ) := f.contDiff
    have h_id : ContDiff ℝ 2 (fun t : ℝ => t) := contDiff_id
    have h_const_m100 : ContDiff ℝ 2 (fun _ : ℝ => m / 100) := contDiff_const
    have h_mul : ContDiff ℝ 2 (fun t : ℝ => m / 100 * t) :=
      h_const_m100.mul h_id
    set phi : ℝ → ℝ := fun t => m / 100 * t with hphi_def
    have hphi_cd : ContDiff ℝ 2 phi := by simpa [hphi_def] using h_mul
    let gphi : ℝ → ℝ := (f : ℝ → ℝ) ∘ phi
    have hgphi_cd : ContDiff ℝ 2 gphi := hg_cd.comp hphi_cd
    have h : ContDiff ℝ 2 (fun t => gphi t / (m^2 / 100)) :=
      hgphi_cd.div_const (m^2 / 100)
    have h_final : ContDiff ℝ 2 (fun t => (100 / m^2) * gphi t) := by
      have h_eq : (fun t : ℝ => (100 / m^2) * gphi t) = (fun t : ℝ => gphi t / (m^2 / 100)) := by
        funext t; field_simp
      rw [h_eq]
      exact h
    exact h_final

/-- Derivative of the rescaled slope. -/
lemma diagonalRescaledSlope_deriv (f : SlopeFunction) (m : ℝ) (hm : 0 < m) (z : ℝ) :
    deriv (diagonalRescaledSlope f m) z = (1 / m) * deriv f (m / 100 * z) := by
  set phi : ℝ → ℝ := fun t => m / 100 * t with hphi_def
  let gphi : ℝ → ℝ := (f : ℝ → ℝ) ∘ phi
  set fRaw : ℝ → ℝ := fun t => (100 / m^2) * gphi t with hfRaw_def
  have hg_cd : ContDiff ℝ 2 (f : ℝ → ℝ) := f.contDiff
  have h_id : ContDiff ℝ 2 (fun t : ℝ => t) := contDiff_id
  have h_const_m100 : ContDiff ℝ 2 (fun _ : ℝ => m / 100) := contDiff_const
  have h_mul : ContDiff ℝ 2 (fun t : ℝ => m / 100 * t) := h_const_m100.mul h_id
  have hphi_cd : ContDiff ℝ 2 phi := by simpa [hphi_def] using h_mul
  have hg_diff : Differentiable ℝ (f : ℝ → ℝ) :=
    f.contDiff.differentiable (by norm_num)
  have hphi_diff : ∀ t, DifferentiableAt ℝ phi t :=
    fun t => (hphi_cd.differentiable (by norm_num)).differentiableAt
  have hphi_deriv : ∀ t, deriv phi t = m / 100 := by
    intro t
    have hder : HasDerivAt phi (m / 100) t := by
      rw [hphi_def]
      exact hasDerivAt_const_mul (m / 100)
    exact hder.deriv
  have hraw : deriv (diagonalRescaledSlope f m) z =
      (100 / m^2) * deriv gphi z := by
    have h : HasDerivAt gphi (deriv gphi z) z :=
      (hg_diff.differentiableAt).comp z (hphi_diff z) |>.hasDerivAt
    have h2 : HasDerivAt (diagonalRescaledSlope f m)
        ((100 / m^2) * deriv gphi z) z := h.const_mul (100 / m^2)
    exact h2.deriv
  have hcomp : deriv gphi z = deriv f (phi z) * deriv phi z :=
    deriv_comp z hg_diff.differentiableAt (hphi_diff z)
  rw [hraw, hcomp, hphi_deriv z]
  have h_eq : (100 / m^2) * (deriv f (phi z) * (m / 100)) =
      (1 / m) * deriv f (phi z) := by
    field_simp [hm.ne'] <;> ring
  rw [h_eq]
  <;> rfl

/-- Second derivative of the rescaled slope. -/
lemma diagonalRescaledSlope_deriv2 (f : SlopeFunction) (m : ℝ) (hm : 0 < m) (z : ℝ) :
    deriv (deriv (diagonalRescaledSlope f m)) z =
      (1 / 100) * deriv (deriv f) (m / 100 * z) := by
  set phi : ℝ → ℝ := fun t => m / 100 * t with hphi_def
  let gphi : ℝ → ℝ := (f : ℝ → ℝ) ∘ phi
  have hg_cd : ContDiff ℝ 2 (f : ℝ → ℝ) := f.contDiff
  have h_id : ContDiff ℝ 2 (fun t : ℝ => t) := contDiff_id
  have h_const_m100 : ContDiff ℝ 2 (fun _ : ℝ => m / 100) := contDiff_const
  have h_mul : ContDiff ℝ 2 (fun t : ℝ => m / 100 * t) := h_const_m100.mul h_id
  have hphi_cd : ContDiff ℝ 2 phi := by simpa [hphi_def] using h_mul
  have hg_deriv_diff : Differentiable ℝ (deriv (f : ℝ → ℝ)) :=
    f.contDiff.differentiable_deriv_two
  have hphi_diff : ∀ t, DifferentiableAt ℝ phi t :=
    fun t => (hphi_cd.differentiable (by norm_num)).differentiableAt
  have hphi_deriv : ∀ t, deriv phi t = m / 100 := by
    intro t
    have hder : HasDerivAt phi (m / 100) t := by
      rw [hphi_def]
      exact hasDerivAt_const_mul (m / 100)
    exact hder.deriv
  have h1 : ∀ t, deriv (diagonalRescaledSlope f m) t =
      (1 / m) * deriv f (phi t) := by
    intro t
    exact diagonalRescaledSlope_deriv f m hm t
  have h3 : (deriv (diagonalRescaledSlope f m)) = fun t => (1 / m) * deriv f (phi t) := by
    funext t; exact h1 t
  have hdiff_at : DifferentiableAt ℝ (deriv (f : ℝ → ℝ)) (phi z) :=
    hg_deriv_diff.differentiableAt (x := phi z)
  have h41 : HasDerivAt (deriv (f : ℝ → ℝ)) (deriv (deriv f) (phi z)) (phi z) :=
    hdiff_at.hasDerivAt
  have h42 : HasDerivAt phi (deriv phi z) z := (hphi_diff z).hasDerivAt
  have h4 : HasDerivAt (fun t => deriv f (phi t))
      (deriv (deriv f) (phi z) * deriv phi z) z :=
    h41.comp z h42
  have h4mul : HasDerivAt (fun t => (1 / m) * deriv f (phi t))
      ((1 / m) * (deriv (deriv f) (phi z) * deriv phi z)) z :=
    h4.const_mul (1 / m)
  have h_eq_deriv : deriv (deriv (diagonalRescaledSlope f m)) z =
      deriv (fun t => (1 / m) * deriv f (phi t)) z := by
    apply congr_fun
    apply congr_arg deriv
    exact h3
  have h6 : deriv (fun t => (1 / m) * deriv f (phi t)) z =
      (1 / m) * (deriv (deriv f) (phi z) * deriv phi z) := h4mul.deriv
  have hphi_val : phi z = m / 100 * z := by
    rw [hphi_def] <;> rfl
  have h_final : (1 / m) * (deriv (deriv f) (phi z) * deriv phi z) =
      (1 / 100) * deriv (deriv f) (m / 100 * z) := by
    rw [hphi_deriv z, hphi_val]
    <;> field_simp [hm.ne'] <;> ring
  rw [h_eq_deriv, h6]
  exact h_final

/-- If m ≤ |f'| ≤ 2m on [0,1], then 1 ≤ |f̃'| ≤ 2 on [0, 100/m]. -/
lemma diagonalRescaledSlope_nonsingular
    (f : SlopeFunction) (m : ℝ) (hm : 0 < m)
    (h_low : ∀ z ∈ Set.Icc (0 : ℝ) 1, m ≤ |deriv f z|)
    (h_high : ∀ z ∈ Set.Icc (0 : ℝ) 1, |deriv f z| ≤ 2 * m) :
    ∀ z ∈ Set.Icc (0 : ℝ) (100 / m),
      1 ≤ |deriv (diagonalRescaledSlope f m) z| ∧
      |deriv (diagonalRescaledSlope f m) z| ≤ 2 := by
  intro z hz
  have h1 : m / 100 * z ∈ Set.Icc (0 : ℝ) 1 := by
    have hz1 : 0 ≤ z := hz.1
    have hz2 : z ≤ 100 / m := hz.2
    constructor
    · positivity
    · calc m / 100 * z
          ≤ m / 100 * (100 / m) := by gcongr
        _ = 1 := by field_simp [hm.ne'] <;> ring
  have hder : deriv (diagonalRescaledSlope f m) z = (1 / m) * deriv f (m / 100 * z) :=
    diagonalRescaledSlope_deriv f m hm z
  rw [hder]
  have h2 : m ≤ |deriv f (m / 100 * z)| := h_low (m / 100 * z) h1
  have h3 : |deriv f (m / 100 * z)| ≤ 2 * m := h_high (m / 100 * z) h1
  have hpos : 0 < 1 / m := by positivity
  have habs : |(1 / m) * deriv f (m / 100 * z)| = (1 / m) * |deriv f (m / 100 * z)| := by
    rw [abs_mul, abs_of_pos hpos]
  rw [habs]
  constructor
  · calc 1
      = (1 / m) * m := by field_simp [hm.ne'] <;> ring
    _ ≤ (1 / m) * |deriv f (m / 100 * z)| := by gcongr
  · calc (1 / m) * |deriv f (m / 100 * z)|
      ≤ (1 / m) * (2 * m) := by gcongr
    _ = 2 := by field_simp [hm.ne'] <;> ring

/-- Projection identity. -/
lemma diagonalRescaling_projection_identity
    (f : SlopeFunction) (m : ℝ) (hm : 0 < m) (p : Point3) (z : ℝ) :
    inner ℝ p (globalGrainDirection (f z)) =
    inner ℝ (diagonalRescalingMap m p)
      (globalGrainDirection ((diagonalRescaledSlope f m) (100 / m * z))) := by
  have h_mul : m / 100 * (100 / m * z) = z := by field_simp [hm.ne'] <;> ring
  have h1 : (diagonalRescaledSlope f m) (100 / m * z) = (100 / m^2) * f z := by
    dsimp only [diagonalRescaledSlope]
    rw [h_mul]
    <;> rfl
  rw [h1]
  have hq0 : (diagonalRescalingMap m p) 0 = p 0 := by
    rw [diagonalRescalingMap_apply] <;> simp [point3]
  have hq1 : (diagonalRescalingMap m p) 1 = m^2 / 100 * p 1 := by
    rw [diagonalRescalingMap_apply] <;> simp [point3]
  have h_left : inner ℝ p (globalGrainDirection (f z)) = p 0 + f z * p 1 := by
    simp [globalGrainDirection, point3, Fin.sum_univ_succ, inner] <;> ring
  have h_right : inner ℝ (diagonalRescalingMap m p)
        (globalGrainDirection ((100 / m^2) * f z)) =
      (diagonalRescalingMap m p) 0 + ((100 / m^2) * f z) * (diagonalRescalingMap m p) 1 := by
    simp [globalGrainDirection, point3, Fin.sum_univ_succ, inner] <;> ring
  rw [h_left, h_right, hq0, hq1]
  <;> field_simp [hm.ne'] <;> ring

/-- Setwise projection identity under diagonal rescaling. -/
lemma diagonalRescaling_projection_set
    (f : SlopeFunction) (m : ℝ) (hm : 0 < m) (E : Set Point3) (t : ℝ) :
    scalarProjection (globalGrainDirection ((diagonalRescaledSlope f m) t))
      (horizontalSlice (diagonalRescalingMap m '' E) t) =
    scalarProjection (globalGrainDirection (f (m / 100 * t)))
      (horizontalSlice E (m / 100 * t)) := by
  set z : ℝ := m / 100 * t with hz_def
  set φ : Point3 → Point3 := diagonalRescalingMap m with hφ_def
  set v : Point3 := globalGrainDirection ((diagonalRescaledSlope f m) t) with hv_def
  set w : Point3 := globalGrainDirection (f z) with hw_def
  let S : Set Point3 := {p | p ∈ E ∧ p 2 = z}
  have h_z_rel : ∀ (p : Point3), (φ p) 2 = t ↔ p 2 = z := by
    intro p
    have h2 : (φ p) 2 = 100 / m * (p 2) := by
      rw [hφ_def, diagonalRescalingMap_apply] <;> simp [point3]
    rw [h2]
    constructor
    · intro h
      have h3 : 100 / m * (p 2) = t := h
      have h4 : p 2 = m / 100 * t := by
        field_simp [hm.ne'] at h3 ⊢ <;> linarith
      exact h4
    · intro h
      rw [h]
      <;> field_simp [hm.ne'] <;> ring
  have h_slice_image : horizontalSlice (φ '' E) t = φ '' S := by
    ext q
    simp only [horizontalSlice, S, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hqin, hq2⟩
      rcases hqin with ⟨p, hpE, hq_eq⟩
      have hp2 : p 2 = z := (h_z_rel p).mp (by rw [hq_eq] <;> exact hq2)
      exact ⟨p, ⟨hpE, hp2⟩, hq_eq⟩
    · rintro ⟨p, ⟨hpE, hp2⟩, hq_eq⟩
      have hq2 : (φ p) 2 = t := (h_z_rel p).mpr hp2
      have hq3 : q 2 = t := by rw [←hq_eq] <;> exact hq2
      exact ⟨⟨p, hpE, hq_eq⟩, hq3⟩
  have h_pointwise : ∀ p ∈ S, inner ℝ (φ p) v = inner ℝ p w := by
    intro p _
    have h : inner ℝ p w = inner ℝ (φ p)
        (globalGrainDirection ((diagonalRescaledSlope f m) (100 / m * z))) :=
      diagonalRescaling_projection_identity f m hm p z
    have h5 : 100 / m * z = t := by
      rw [hz_def] <;> field_simp [hm.ne'] <;> ring
    rw [h5] at h
    simpa [hv_def] using h.symm
  have h_main : scalarProjection v (φ '' S) = scalarProjection w S := by
    ext x
    simp only [scalarProjection, Set.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨p, hpS, rfl⟩
      exact ⟨p, hpS, (h_pointwise p hpS).symm⟩
    · rintro ⟨p, hpS, rfl⟩
      exact ⟨φ p, ⟨p, hpS, rfl⟩, h_pointwise p hpS⟩
  rw [h_slice_image]
  exact h_main

end Kakeya.Assouad

end

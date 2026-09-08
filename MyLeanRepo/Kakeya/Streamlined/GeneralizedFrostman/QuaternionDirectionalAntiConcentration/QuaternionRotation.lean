import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.Analysis.Quaternion
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Quaternion rotation map for directional anti-concentration
-/

noncomputable section

open scoped Quaternion RealInnerProductSpace

open Quaternion Metric MeasureTheory

namespace Kakeya.Streamlined.GeneralizedFrostman

/-! ## Measurable space structure for quaternions -/

instance : MeasurableSpace ℍ := borel ℍ
instance : BorelSpace ℍ := ⟨rfl⟩

/-! ## Purely imaginary quaternions submodule -/

def imaginaryQuaternions : Submodule ℝ ℍ :=
  { carrier := {q | q.re = 0}
    zero_mem' := by
      simp only [Set.mem_setOf_eq] <;> simp
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      have h : (a + b).re = a.re + b.re := by
        exact re_add a b
      rw [h, ha, hb] <;> norm_num
    smul_mem' := by
      intro r a ha
      simp only [Set.mem_setOf_eq] at ha ⊢
      have h : (r • a).re = r * a.re := by
        exact Real.ext_cauchy rfl
      rw [h, ha] <;> ring }

def point3ToImaginary : Point3 ≃ₗᵢ[ℝ] imaginaryQuaternions :=
  let e3 : Point3 ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  let toFun : Point3 → imaginaryQuaternions := fun v =>
    let f := e3 v
    ⟨⟨0, f 0, f 1, f 2⟩, by simp [imaginaryQuaternions]⟩
  let invFun : imaginaryQuaternions → Point3 := fun q =>
    e3.symm ![q.val.imI, q.val.imJ, q.val.imK]
  { toFun := toFun
    invFun := invFun
    left_inv := by
      intro v
      have h : e3 (invFun (toFun v)) = e3 v := by
        funext i
        fin_cases i <;> simp [toFun, invFun, e3.apply_symm_apply]
      exact e3.injective h
    right_inv := by
      intro q
      have hre : q.val.re = 0 := q.property
      apply Subtype.ext
      apply QuaternionAlgebra.ext
      · exact hre.symm
      · simp [toFun, invFun, e3.apply_symm_apply]
      · simp [toFun, invFun, e3.apply_symm_apply]
      · simp [toFun, invFun, e3.apply_symm_apply]
    map_add' := by
      intro v w
      apply Subtype.ext
      apply QuaternionAlgebra.ext <;> simp [toFun, map_add]
    map_smul' := by
      intro r v
      apply Subtype.ext
      apply QuaternionAlgebra.ext <;> simp [toFun, map_smul]
    norm_map' := by
      intro v
      let f := e3 v
      let q0 : ℍ := ⟨0, f 0, f 1, f 2⟩
      have hfi : ∀ (i : Fin 3), f i = v i := by intro i; rfl
      have h_normSq : normSq q0 = (f 0) ^ 2 + (f 1) ^ 2 + (f 2) ^ 2 := by
        simp [normSq_def', q0]
      have h1 : ‖q0‖ ^ 2 = normSq q0 := by
        rw [normSq_eq_norm_mul_self, pow_two]
      have h2 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq v, Fin.sum_univ_three]
      have h3 : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = (f 0) ^ 2 + (f 1) ^ 2 + (f 2) ^ 2 := by
        rw [hfi 0, hfi 1, hfi 2]
      have h4 : ‖q0‖ ^ 2 = ‖v‖ ^ 2 := by linarith [h_normSq, h1, h2, h3]
      have h5 : 0 ≤ ‖q0‖ := by positivity
      have h6 : 0 ≤ ‖v‖ := by positivity
      have h7 : ‖q0‖ = ‖v‖ := by nlinarith
      exact h7 }

/-! ## Quaternion conjugation -/

def quaternionConj (q : ℍ) (hq : ‖q‖ = 1) : ℍ ≃ₗᵢ[ℝ] ℍ :=
  have h_normSq : normSq q = 1 := by
    rw [normSq_eq_norm_mul_self, hq] <;> ring
  have h_mul_star : q * star q = (1 : ℍ) := by
    have h := self_mul_star q
    rw [h, h_normSq] <;> norm_cast
  have h_star_mul : star q * q = (1 : ℍ) := by
    have h := star_mul_self q
    rw [h, h_normSq] <;> norm_cast
  let f : ℍ → ℍ := fun x => q * x * star q
  let g : ℍ → ℍ := fun x => star q * x * q
  have hfg : ∀ x, g (f x) = x := by
    intro x
    calc
      star q * (q * x * star q) * q
        = (star q * q) * x * (star q * q) := by simp [mul_assoc]
      _ = (1 : ℍ) * x * (1 : ℍ) := by rw [h_star_mul]
      _ = x := by simp
  have hgf : ∀ x, f (g x) = x := by
    intro x
    calc
      q * (star q * x * q) * star q
        = (q * star q) * x * (q * star q) := by simp [mul_assoc]
      _ = (1 : ℍ) * x * (1 : ℍ) := by rw [h_mul_star]
      _ = x := by simp
  have h_add : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    dsimp only [f]
    rw [mul_add, right_distrib]
  have h_smul : ∀ (r : ℝ) x, f (r • x) = r • f x := by
    intro r x
    dsimp only [f]
    have h1 : q * (r • x) = r • (q * x) := by
      exact mul_smul_comm r q x
    rw [h1, smul_mul_assoc]
  have h_norm : ∀ x, ‖f x‖ = ‖x‖ := by
    intro x
    dsimp only [f]
    have h1 : ‖q * x * star q‖ = ‖q‖ * ‖x‖ * ‖star q‖ := by
      rw [norm_mul (q * x) (star q), norm_mul q x] <;> ring
    have h2 : ‖star q‖ = ‖q‖ := _root_.norm_star q
    have h3 : ‖q * x * star q‖ = ‖x‖ := by
      rw [h1, h2, hq] <;> ring
    exact h3
  { toFun := f
    invFun := g
    left_inv := hfg
    right_inv := hgf
    map_add' := h_add
    map_smul' := h_smul
    norm_map' := h_norm }

theorem quaternionConj_preserves_imaginary (q : ℍ) (hq : ‖q‖ = 1)
    {x : ℍ} (hx : x ∈ imaginaryQuaternions) :
    (quaternionConj q hq) x ∈ imaginaryQuaternions := by
  have h1 : star x = -x := by
    have h2 : star x = -x ↔ x.re = 0 := star_eq_neg
    exact h2.mpr hx
  let y := q * x * star q
  have h3 : star y = -y := by
    dsimp only [y]
    calc
      star (q * x * star q)
        = star (star q) * star (q * x) := by rw [star_mul]
      _ = star (star q) * (star x * star q) := by rw [star_mul]
      _ = star (star q) * star x * star q := by simp [mul_assoc]
      _ = q * star x * star q := by rw [star_star]
      _ = q * (-x) * star q := by rw [h1]
      _ = -(q * x * star q) := by simp [mul_neg]
  have h4 : y.re = 0 := by
    have h5 : star y = -y := h3
    have h6 : (star y).re = y.re := by rw [re_star]
    have h7 : (-y).re = -y.re := by simp
    rw [h5] at h6
    rw [h7] at h6
    linarith
  have hfy : (quaternionConj q hq) x = y := by
    rfl
  rw [hfy]
  simpa [imaginaryQuaternions, Set.mem_setOf_eq] using h4

def quaternionConjImaginary (q : ℍ) (hq : ‖q‖ = 1) :
    imaginaryQuaternions ≃ₗᵢ[ℝ] imaginaryQuaternions :=
  let f := quaternionConj q hq
  let hq2 : ‖star q‖ = 1 := by
    rw [_root_.norm_star q, hq]
  let g := quaternionConj (star q) hq2
  have hg_eq : ∀ (y : ℍ), g y = f.symm y := by
    intro y
    dsimp only [g, f, quaternionConj]
    have h : star (star q) = q := star_star q
    simp [h]
    <;> rfl
  have hfg : ∀ (x : imaginaryQuaternions), g (f x.val) = x.val := by
    intro x
    rw [hg_eq (f x.val)]
    exact f.left_inv x.val
  have hgf : ∀ (x : imaginaryQuaternions), f (g x.val) = x.val := by
    intro x
    rw [hg_eq x.val]
    exact f.right_inv x.val
  { toFun := fun x : imaginaryQuaternions =>
      ⟨f x.val, quaternionConj_preserves_imaginary q hq x.property⟩
    invFun := fun x : imaginaryQuaternions =>
      ⟨g x.val, quaternionConj_preserves_imaginary (star q) hq2 x.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact hfg x
    right_inv := by
      intro x
      apply Subtype.ext
      exact hgf x
    map_add' := by
      intro x y
      apply Subtype.ext
      exact f.map_add' x.val y.val
    map_smul' := by
      intro r x
      apply Subtype.ext
      exact f.map_smul' r x.val
    norm_map' := by
      intro x
      exact f.norm_map' x.val }

def quaternionRotation (q : ℍ) (hq : ‖q‖ = 1) : Point3 ≃ₗᵢ[ℝ] Point3 :=
  let e1 := point3ToImaginary
  let e2 := quaternionConjImaginary q hq
  let e3 := point3ToImaginary.symm
  (e1.trans e2).trans e3

def quaternionRotationSphere (q : Metric.sphere (0 : ℍ) 1) : Point3 ≃ₗᵢ[ℝ] Point3 :=
  have hq' : ‖q.val‖ = 1 := by
    have h : dist q.val 0 = 1 := q.property
    simpa [dist_zero_right] using h
  quaternionRotation q.val hq'

/-! ## Transport to Euclidean 4-sphere -/

def quaternionToEuclidean4 : ℍ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  Quaternion.linearIsometryEquivTuple

def sphere3HomeoEuclidean4 :
    Metric.sphere (0 : ℍ) 1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  let e := quaternionToEuclidean4
  { toFun := fun q : Metric.sphere (0 : ℍ) 1 =>
      ⟨e q.val, by
        have h1 : ‖e q.val‖ = ‖q.val‖ := e.norm_map q.val
        have h2 : ‖q.val‖ = 1 := by simpa [dist_zero_right] using q.property
        simpa [dist_zero_right, Metric.mem_sphere] using h1 ▸ h2⟩
    invFun := fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 =>
      ⟨e.symm x.val, by
        have h1 : ‖e.symm x.val‖ = ‖x.val‖ := e.symm.norm_map x.val
        have h2 : ‖x.val‖ = 1 := by simpa [dist_zero_right] using x.property
        simpa [dist_zero_right, Metric.mem_sphere] using h1 ▸ h2⟩
    left_inv := by intro q; apply Subtype.ext; exact e.left_inv q.val
    right_inv := by intro x; apply Subtype.ext; exact e.right_inv x.val
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

def euclideanRotation (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Point3 ≃ₗᵢ[ℝ] Point3 :=
  let q : Metric.sphere (0 : ℍ) 1 := sphere3HomeoEuclidean4.symm x
  quaternionRotationSphere q

/-! ## Measurability / Continuity -/

theorem continuous_quaternionRotationSphere_eval (u : Point3) :
    Continuous fun q : Metric.sphere (0 : ℍ) 1 => quaternionRotationSphere q u := by
  have h_eq : ∀ (q : Metric.sphere (0 : ℍ) 1),
      quaternionRotationSphere q u =
        point3ToImaginary.symm
          (⟨q.val * (point3ToImaginary u).val * star q.val,
            quaternionConj_preserves_imaginary q.val
              (by have h : dist q.val 0 = 1 := q.property
                  simpa [dist_zero_right] using h)
              (point3ToImaginary u).property⟩) := by
    intro q
    simp [quaternionRotationSphere, quaternionRotation, quaternionConjImaginary,
      point3ToImaginary]
    <;> rfl
  have h_cont : Continuous (fun q : Metric.sphere (0 : ℍ) 1 =>
      point3ToImaginary.symm
        (⟨q.val * (point3ToImaginary u).val * star q.val,
          quaternionConj_preserves_imaginary q.val
            (by have h : dist q.val 0 = 1 := q.property
                simpa [dist_zero_right] using h)
            (point3ToImaginary u).property⟩)) := by
    fun_prop
  rw [funext h_eq]
  exact h_cont

theorem continuous_euclideanRotation_eval (u : Point3) :
    Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 =>
      euclideanRotation x u := by
  have h : (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 =>
        euclideanRotation x u) =
      (fun q : Metric.sphere (0 : ℍ) 1 => quaternionRotationSphere q u) ∘
        sphere3HomeoEuclidean4.symm := by
    funext x
    rfl
  rw [h]
  exact (continuous_quaternionRotationSphere_eval u).comp
    sphere3HomeoEuclidean4.symm.continuous

theorem measurable_euclideanRotation_eval (u : Point3) :
    Measurable fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 =>
      euclideanRotation x u :=
  (continuous_euclideanRotation_eval u).measurable

end Kakeya.Streamlined.GeneralizedFrostman

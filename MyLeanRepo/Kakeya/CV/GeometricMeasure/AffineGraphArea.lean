import MyLeanRepo.Kakeya.CV.Isoperimetric.Statements
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaBasics
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Affine graph area formula in R³

This module proves the standard Hausdorff-area formula for affine graphs over
the coordinate plane. It is the closed affine input for the general C¹ graph
area formula.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

variable {g : R2 → ℝ}

local instance : (μH[2] : Measure R2).IsAddHaarMeasure := by
  have hfin : Module.finrank ℝ R2 = 2 := finrank_euclideanSpace_fin
  have h_eq : (μH[2] : Measure R2) = μH[Module.finrank ℝ R2] := by
    congr 1 <;> exact_mod_cast hfin.symm
  exact h_eq ▸
    (inferInstance :
      (μH[Module.finrank ℝ R2] : Measure R2).IsAddHaarMeasure)

/-- Unit normal to the affine graph `z = a0*x + a1*y`. -/
def affineNormalVec (a0 a1 : ℝ) : R3 :=
  let s := Real.sqrt (1 + a0^2 + a1^2)
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![-(a0/s), -(a1/s), 1/s]

/-- The affine graph map. -/
def affineGraph (a0 a1 : ℝ) : R2 → R3 :=
  graphMap (fun y : R2 => a0 * y 0 + a1 * y 1)

/-- Linear extension of the affine graph by its normal direction. -/
def affineExtend (a0 a1 : ℝ) : R3 →ₗ[ℝ] R3 :=
  let v := affineNormalVec a0 a1
  {
    toFun := fun x : R3 =>
      affineGraph a0 a1
          ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0, x 1]) +
        x 2 • v
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp [affineGraph, graphMap] <;> ring
    map_smul' := by
      intro c x
      ext i
      fin_cases i <;> simp [affineGraph, graphMap, smul_eq_mul] <;> ring
  }

def affineExtendCLM (a0 a1 : ℝ) : R3 →L[ℝ] R3 :=
  (affineExtend a0 a1).toContinuousLinearMap

lemma affineNormal_norm (a0 a1 : ℝ) : ‖affineNormalVec a0 a1‖ = 1 := by
  set s : ℝ := Real.sqrt (1 + a0^2 + a1^2) with hs
  have hs_pos : 0 < s := by positivity
  have hs2 : s^2 = 1 + a0^2 + a1^2 :=
    Real.sq_sqrt (by positivity)
  set v : R3 := affineNormalVec a0 a1 with hv
  have hsqrt : Real.sqrt (1 + a0^2 + a1^2) = s := by rfl
  have h1 : v 0 = -(a0/s) := by
    simp [hv, affineNormalVec, hsqrt]
  have h2 : v 1 = -(a1/s) := by
    simp [hv, affineNormalVec, hsqrt]
  have h3 : v 2 = 1/s := by
    simp [hv, affineNormalVec, hsqrt]
  have h4 : ‖v‖^2 = (v 0)^2 + (v 1)^2 + (v 2)^2 :=
    norm_sq_R3 v
  have h5 : ‖v‖^2 = 1 := by
    rw [h4, h1, h2, h3]
    have hne : s ≠ 0 := hs_pos.ne'
    field_simp [hne]
    <;> nlinarith [hs2]
  have h6 : 0 ≤ ‖v‖ := by positivity
  nlinarith

private def b3 : Module.Basis (Fin 3) ℝ R3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

lemma affineExtend_det (a0 a1 : ℝ) :
    (affineExtendCLM a0 a1).det =
      Real.sqrt (1 + a0^2 + a1^2) := by
  let s := Real.sqrt (1 + a0^2 + a1^2)
  have hs_pos : 0 < s := by positivity
  have hs2 : s^2 = 1 + a0^2 + a1^2 :=
    Real.sq_sqrt (by positivity)
  have h_main : (affineExtendCLM a0 a1).det =
      (LinearMap.toMatrix b3 b3 (affineExtend a0 a1)).det := by
    simp [affineExtendCLM, LinearMap.det_toMatrix]
  rw [h_main]
  have hmat : LinearMap.toMatrix b3 b3 (affineExtend a0 a1) =
      !![1, 0, -(a0 / s); 0, 1, -(a1 / s); a0, a1, 1 / s] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [affineExtend, affineGraph, affineNormalVec, graphMap, b3,
        LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply] <;>
      (try aesop)
  rw [hmat]
  have h_det :
      (!![1, 0, -(a0 / s); 0, 1, -(a1 / s); a0, a1, 1 / s]).det =
        s := by
    rw [Matrix.det_fin_three]
    simp [Matrix.cons_val']
    <;> field_simp [hs_pos.ne'] <;> nlinarith [hs2]
  exact h_det

/-- Standard embedding of `R2` into `R3` as the xy-plane. -/
def stdEmb : R2 → R3 := fun y =>
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![y 0, y 1, 0]

/-- Projection from `R3` to its first two coordinates. -/
def stdProj2 : R3 →ₗ[ℝ] R2 :=
  { toFun := fun x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0, x 1]
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp
    map_smul' := by
      intro c x
      ext i
      fin_cases i <;> simp <;> ring }

lemma stdProj2_apply (x : R3) :
    stdProj2 x =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0, x 1] := by
  ext i
  fin_cases i <;> simp [stdProj2]

lemma stdProj2_cont : Continuous stdProj2 :=
  LinearMap.continuous_of_finiteDimensional stdProj2

lemma stdProj2_meas : Measurable stdProj2 :=
  stdProj2_cont.measurable

lemma x2_meas : Measurable (fun x : R3 => x 2) := by
  have h : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) := by
    continuity
  exact (continuous_apply 2).comp h |>.measurable

lemma stdEmb_isometry : Isometry stdEmb := by
  have h : ∀ (x y : R2),
      ‖stdEmb x - stdEmb y‖^2 = ‖x - y‖^2 := by
    intro x y
    have h1 :
        ‖stdEmb x - stdEmb y‖^2 =
          (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
      rw [norm_sq_R3]
      simp [stdEmb]
    have h2 :
        ‖x - y‖^2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
      rw [norm_sq_R2]
      have h21 : (x - y) 0 = x 0 - y 0 := by simp
      have h22 : (x - y) 1 = x 1 - y 1 := by simp
      rw [h21, h22]
    rw [h1, h2]
  have h' : ∀ (x y : R2),
      ‖stdEmb x - stdEmb y‖ = ‖x - y‖ := by
    intro x y
    have hsq := h x y
    have hnonneg1 : 0 ≤ ‖stdEmb x - stdEmb y‖ := by positivity
    have hnonneg2 : 0 ≤ ‖x - y‖ := by positivity
    nlinarith
  exact Isometry.of_dist_eq
    (fun x y => by simpa [dist_eq_norm] using h' x y)

lemma stdProj2_stdEmb : stdProj2 ∘ stdEmb = id := by
  funext x
  ext i
  fin_cases i <;> simp [stdProj2, stdEmb]

/-- Standard basis vector in the third coordinate. -/
def e3vec : R3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![0, 0, 1]

lemma e3vec_norm : ‖e3vec‖ = 1 := by
  have h0 : e3vec 0 = 0 := by simp [e3vec]
  have h1 : e3vec 1 = 0 := by simp [e3vec]
  have h2 : e3vec 2 = 1 := by simp [e3vec]
  have h3 : ‖e3vec‖^2 = 1 := by
    rw [norm_sq_R3, h0, h1, h2]
    norm_num
  have hpos : 0 ≤ ‖e3vec‖ := by positivity
  nlinarith

lemma e3vec_ne_zero : e3vec ≠ 0 := by
  intro h
  have h2 : ‖e3vec‖ = 0 := by simpa [h] using norm_zero
  rw [e3vec_norm] at h2
  norm_num at h2

lemma inner_e3vec (z : R3) : inner ℝ z e3vec = z 2 := by
  have h1 : inner ℝ z e3vec =
      ∑ i : Fin 3, inner ℝ (z i) (e3vec i) := by
    rw [PiLp.inner_apply]
  rw [h1, Fin.sum_univ_three]
  have h2 : e3vec 0 = 0 := by simp [e3vec]
  have h3 : e3vec 1 = 0 := by simp [e3vec]
  have h4 : e3vec 2 = 1 := by simp [e3vec]
  have h5 : ∀ (x y : ℝ), inner ℝ x y = x * y := by
    intro x y
    simp [mul_comm]
  rw [h5, h5, h5, h2, h3, h4]
  ring

lemma plane_iff (v : R3) (hv : ‖v‖ = 1) (x : ℝ) (z : R3) :
    z ∈ (AffineSubspace.mk' (x • v) (ℝ ∙ v)ᗮ : Set R3) ↔
      inner ℝ z v = x := by
  have h6 : inner ℝ v v = 1 := by
    have h7 : inner ℝ v v = ‖v‖^2 := by
      simpa [inner_self_eq_norm_sq_to_K] using rfl
    rw [h7, hv]
    norm_num
  constructor
  · intro h
    have h4 : inner ℝ v (z - x • v) = 0 :=
      h v (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
    have h5 : inner ℝ v z - x * inner ℝ v v = 0 := by
      simpa [inner_sub_right, inner_smul_right] using h4
    rw [h6] at h5
    have h7 : inner ℝ v z = x := by linarith
    have h8 : inner ℝ z v = inner ℝ v z :=
      (real_inner_comm z v).symm
    rw [h8]
    exact h7
  · intro h
    intro w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    have h9 : inner ℝ v z = x := by
      have h_comm : inner ℝ v z = inner ℝ z v :=
        (real_inner_comm v z).symm
      rw [h_comm, h]
    have h_vsub : (z -ᵥ x • v) = (z - x • v) := by rfl
    have h11 :
        inner ℝ (c • v) (z -ᵥ x • v) =
          c * inner ℝ v (z -ᵥ x • v) := by
      rw [h_vsub, real_inner_smul_left]
    rw [h11]
    have h12 :
        inner ℝ v (z -ᵥ x • v) =
          inner ℝ v z - x * inner ℝ v v := by
      rw [h_vsub, inner_sub_right, inner_smul_right] <;> ring
    rw [h12, h9, h6] <;> ring

/-- Affine graph area formula via double slicing. -/
lemma affine_graph_area_formula
    (a0 a1 : ℝ) {B : Set R2} (hB : MeasurableSet B) :
    μH[2] (affineGraph a0 a1 '' B) =
      planeConstant *
        ENNReal.ofReal (Real.sqrt (1 + a0^2 + a1^2)) *
          volume B := by
  let s := Real.sqrt (1 + a0^2 + a1^2)
  let v := affineNormalVec a0 a1
  let A : R3 →ₗ[ℝ] R3 := affineExtend a0 a1
  let ACLM : R3 →L[ℝ] R3 := affineExtendCLM a0 a1
  let w : R3 := e3vec

  have hfin3 : Module.finrank ℝ R3 = 3 :=
    finrank_euclideanSpace_fin

  let D : Set R3 :=
    {x | stdProj2 x ∈ B ∧ x 2 ∈ Ioo (-1 : ℝ) 1}

  have hD_meas : MeasurableSet D :=
    hB.preimage stdProj2_meas |>.inter
      (measurableSet_Ioo.preimage x2_meas)

  have h_step1 : volume D = 2 * volume B := by
    have h_vol : (μHE[3] : Measure R3) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume 3
    have h_slice_raw :=
      EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral
        (0 : R3) e3vec_ne_zero hD_meas
    have h_weq : w = e3vec := by rfl
    have h_slice :
        μHE[3] D =
          ‖w‖ₑ *
            ∫⁻ (x : ℝ),
              μHE[2]
                (D ∩
                  (AffineSubspace.mk'
                    (x • w) (ℝ ∙ w)ᗮ : Set R3)) := by
      simpa [hfin3, h_weq, vadd_zero] using h_slice_raw
    have h_norm1 : ‖w‖ₑ = 1 := by
      have h : ‖w‖ = 1 := e3vec_norm
      simpa [enorm] using
        congr_arg (fun x : ℝ => ENNReal.ofReal x) h

    have h_intersection : ∀ (x : ℝ),
        D ∩
            (AffineSubspace.mk'
              (x • w) (ℝ ∙ w)ᗮ : Set R3) =
          if x ∈ Ioo (-1 : ℝ) 1 then
            (fun z : R3 => z + x • w) '' (stdEmb '' B)
          else ∅ := by
      intro x
      by_cases hx : x ∈ Ioo (-1 : ℝ) 1
      · rw [if_pos hx]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_image,
          Set.mem_setOf_eq]
        constructor
        · rintro ⟨hD, hplane⟩
          have hz2 : z 2 = x := by
            have h_inner : inner ℝ z w = x :=
              (plane_iff w e3vec_norm x z).mp hplane
            rw [inner_e3vec z] at h_inner
            exact h_inner
          let y : R2 := stdProj2 z
          have hy : y ∈ B := hD.1
          have h_eq : z = stdEmb y + x • w := by
            ext i
            fin_cases i <;>
              simp [stdEmb, y, w, e3vec, hz2] <;> rfl
          exact
            ⟨stdEmb y, ⟨y, hy, rfl⟩, h_eq.symm⟩
        · rintro ⟨z', hz', rfl⟩
          rcases hz' with ⟨y, hy, rfl⟩
          have hz2 : (stdEmb y + x • w) 2 = x := by
            simp [stdEmb, w, e3vec]
          have h_inner :
              inner ℝ (stdEmb y + x • w) w = x := by
            rw [inner_e3vec (stdEmb y + x • w)]
            exact hz2
          have hplane :
              stdEmb y + x • w ∈
                (AffineSubspace.mk'
                  (x • w) (ℝ ∙ w)ᗮ : Set R3) :=
            (plane_iff w e3vec_norm x _).mpr h_inner
          have hD1 :
              stdProj2 (stdEmb y + x • w) ∈ B := by
            have h :
                stdProj2 (stdEmb y + x • w) = y := by
              ext i
              fin_cases i <;>
                simp [stdProj2, stdEmb, w, e3vec]
            rw [h]
            exact hy
          have hD2 :
              (stdEmb y + x • w) 2 ∈ Ioo (-1 : ℝ) 1 := by
            simpa [stdEmb, w, e3vec] using hx
          exact ⟨⟨hD1, hD2⟩, hplane⟩
      · rw [if_neg hx]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hD hplane
        have hz2 : z 2 = x := by
          have h_inner : inner ℝ z w = x :=
            (plane_iff w e3vec_norm x z).mp hplane
          rw [inner_e3vec z] at h_inner
          exact h_inner
        have h_contra : z 2 ∈ Ioo (-1 : ℝ) 1 := hD.2
        rw [hz2] at h_contra
        exact hx h_contra

    have h_emb : μHE[2] (stdEmb '' B) = volume B := by
      have h1 : μHE[2] (stdEmb '' B) = μHE[2] B :=
        Isometry.euclideanHausdorffMeasure_image
          stdEmb_isometry B
      rw [h1]
      have h2 : (μHE[2] : Measure R2) = volume :=
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2
      rw [h2]

    have h_translation : ∀ (c : R3),
        μHE[2] ((fun z : R3 => z + c) '' (stdEmb '' B)) =
          μHE[2] (stdEmb '' B) := by
      intro c
      let transl : R3 → R3 := fun z => z + c
      have h_iso : Isometry transl := by
        intro x y
        simp [transl, dist_eq_norm]
      exact Isometry.euclideanHausdorffMeasure_image
        h_iso (stdEmb '' B)

    let c0 : ENNReal := μHE[2] (stdEmb '' B)

    have h_eq : ∀ (x : ℝ),
        μHE[2]
            (D ∩
              (AffineSubspace.mk'
                (x • w) (ℝ ∙ w)ᗮ : Set R3)) =
          Set.indicator
            (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c0) x := by
      intro x
      rw [h_intersection x]
      by_cases hx : x ∈ Ioo (-1 : ℝ) 1
      · rw [if_pos hx]
        have h_ind :
            Set.indicator
                (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c0) x =
              c0 := by
          simp [Set.indicator, hx]
        rw [h_ind, h_translation (x • w)]
      · rw [if_neg hx]
        have h_ind :
            Set.indicator
                (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c0) x =
              0 := by
          simp [Set.indicator, hx]
        rw [h_ind]
        simp

    have h_integral :
        (∫⁻ (x : ℝ),
          μHE[2]
            (D ∩
              (AffineSubspace.mk'
                (x • w) (ℝ ∙ w)ᗮ : Set R3))) =
          2 * c0 := by
      have h1 :
          (∫⁻ (x : ℝ),
            μHE[2]
              (D ∩
                (AffineSubspace.mk'
                  (x • w) (ℝ ∙ w)ᗮ : Set R3))) =
            ∫⁻ (x : ℝ),
              Set.indicator
                (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c0) x := by
        congr with x
        exact h_eq x
      rw [h1]
      have h2 :
          ∫⁻ (x : ℝ),
              Set.indicator
                (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c0) x =
            ∫⁻ (_x : ℝ) in Ioo (-1 : ℝ) 1, c0 := by
        rw [lintegral_indicator measurableSet_Ioo] <;> rfl
      have h_volIoo :
          volume (Ioo (-1 : ℝ) 1) = (2 : ENNReal) := by
        rw [Real.volume_Ioo
          (a := (-1 : ℝ)) (b := (1 : ℝ))]
        norm_num
      rw [h2, setLIntegral_const, h_volIoo]
      ring

    have h_goal : volume D = 2 * volume B := by
      have h9 : μHE[3] D = 2 * c0 := by
        rw [h_slice, h_norm1, h_integral]
        ring
      rw [h_vol] at h9
      dsimp only [c0] at h9
      rw [h_emb] at h9
      exact h9
    exact h_goal

  have h_cov :
      volume (ACLM '' D) = ENNReal.ofReal s * volume D := by
    have h :
        (volume : Measure R3) (A '' D) =
          ENNReal.ofReal |A.det| * (volume : Measure R3) D :=
      (volume : Measure R3).addHaar_image_linearMap A D
    have hdet1 : A.det = s := by
      exact_mod_cast affineExtend_det a0 a1
    rw [hdet1] at h
    have habs : |s| = s := by
      have hpos : 0 < s := by positivity
      rw [abs_of_pos hpos]
    rw [habs] at h
    have h_ACLM_eq :
        (ACLM : R3 → R3) = (A : R3 → R3) := by
      funext x
      rfl
    have h_eq : ACLM '' D = A '' D := by
      rw [h_ACLM_eq]
    rw [h_eq]
    exact h

  let t_set : Set R3 := ACLM '' D

  have ht_meas : MeasurableSet t_set := by
    have hdet : A.det ≠ 0 := by
      have hdet1 : A.det = s := by
        exact_mod_cast affineExtend_det a0 a1
      rw [hdet1]
      have hpos : 0 < s := by positivity
      exact hpos.ne'
    have h_inj : Function.Injective ACLM :=
      (LinearMap.equivOfDetNeZero A hdet).injective
    exact hD_meas.image_of_measurable_injOn
      ACLM.measurable (fun x _ y _ h => h_inj h)

  have h_image :
      t_set =
        {w | ∃ (y : R2), y ∈ B ∧
          ∃ (t : ℝ), t ∈ Ioo (-1 : ℝ) 1 ∧
            w = affineGraph a0 a1 y + t • v} := by
    ext z
    simp only [t_set, D, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      let y : R2 := stdProj2 x
      let t : ℝ := x 2
      have hy : y ∈ B := hx.1
      have ht : t ∈ Ioo (-1 : ℝ) 1 := hx.2
      refine ⟨y, hy, t, ht, ?_⟩
      have h1 : stdProj2 x = y := by rfl
      have h2 : x 2 = t := by rfl
      simp only [ACLM, affineExtendCLM, affineExtend,
        stdProj2_apply, h1, h2]
      rfl
    · rintro ⟨y, hy, t, ht, rfl⟩
      let x : R3 :=
        (EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![y 0, y 1, t]
      have hx1 : stdProj2 x = y := by
        ext i
        fin_cases i <;> simp [stdProj2, x]
      have hx2 : x 2 = t := by simp [x]
      have hx : x ∈ D :=
        ⟨by rw [hx1]; exact hy, by rw [hx2]; exact ht⟩
      refine ⟨x, hx, ?_⟩
      simp only [ACLM, affineExtendCLM, affineExtend,
        stdProj2_apply, hx1, hx2]
      rfl

  have hv_ne_zero : v ≠ 0 := by
    intro h
    have h2 : ‖v‖ = 0 := by simpa [h] using norm_zero
    rw [affineNormal_norm] at h2
    norm_num at h2

  have hv_norm : ‖v‖ = 1 :=
    affineNormal_norm a0 a1

  have h_perp :
      ∀ (y : R2),
        inner ℝ (affineGraph a0 a1 y) v = 0 := by
    intro y
    set s' : ℝ :=
      Real.sqrt (1 + a0^2 + a1^2) with hs'
    have hs_pos : 0 < s' := by positivity
    have hne : s' ≠ 0 := hs_pos.ne'
    have h1 :
        inner ℝ (affineGraph a0 a1 y) v =
          ∑ i : Fin 3,
            inner ℝ ((affineGraph a0 a1 y) i) (v i) := by
      rw [PiLp.inner_apply]
    rw [h1, Fin.sum_univ_three]
    have h5 :
        ∀ (x y : ℝ), inner ℝ x y = x * y := by
      intro x y
      simp [mul_comm]
    rw [h5, h5, h5]
    have hg0 :
        (affineGraph a0 a1 y) 0 = y 0 := by
      simp [affineGraph, graphMap]
    have hg1 :
        (affineGraph a0 a1 y) 1 = y 1 := by
      simp [affineGraph, graphMap]
    have hg2 :
        (affineGraph a0 a1 y) 2 =
          a0 * y 0 + a1 * y 1 := by
      simp [affineGraph, graphMap]
    have hv0 : v 0 = -(a0 / s') := by
      simp [v, affineNormalVec, hs']
    have hv1 : v 1 = -(a1 / s') := by
      simp [v, affineNormalVec, hs']
    have hv2 : v 2 = 1 / s' := by
      simp [v, affineNormalVec, hs']
    rw [hg0, hg1, hg2, hv0, hv1, hv2]
    field_simp [hne]
    ring

  have hinner : inner ℝ v v = 1 := by
    have h : inner ℝ v v = ‖v‖^2 := by
      simpa [inner_self_eq_norm_sq_to_K] using rfl
    rw [h, hv_norm]
    norm_num

  have h_intersection2 : ∀ (x : ℝ),
      t_set ∩
          (AffineSubspace.mk'
            (x • v) (ℝ ∙ v)ᗮ : Set R3) =
        if x ∈ Ioo (-1 : ℝ) 1 then
          (fun z : R3 => z + x • v) ''
            (affineGraph a0 a1 '' B)
        else ∅ := by
    intro x
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · rw [if_pos hx]
      ext z
      simp only [Set.mem_inter_iff, Set.mem_image,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨h_t, h_plane⟩
        rw [h_image] at h_t
        rcases h_t with ⟨y, hy, t, ht, rfl⟩
        have h_inner_eq :
            inner ℝ (affineGraph a0 a1 y + t • v) v = x :=
          (plane_iff v hv_norm x _).mp h_plane
        have h_t_eq_x : t = x := by
          have h7 :
              inner ℝ (affineGraph a0 a1 y + t • v) v =
                t := by
            have h8 :
                inner ℝ (affineGraph a0 a1 y) v = 0 :=
              h_perp y
            have h9 :
                inner ℝ (affineGraph a0 a1 y + t • v) v =
                  inner ℝ (affineGraph a0 a1 y) v +
                    inner ℝ (t • v) v := by
              rw [inner_add_left]
            rw [h9, h8]
            have h10 :
                inner ℝ (t • v) v =
                  t * inner ℝ v v := by
              rw [real_inner_smul_left]
            rw [h10, hinner]
            ring
          linarith
        rw [h_t_eq_x]
        exact
          ⟨affineGraph a0 a1 y, ⟨y, hy, rfl⟩, by simp⟩
      · rintro ⟨z', hz', rfl⟩
        rcases hz' with ⟨y, hy, rfl⟩
        have h_t :
            affineGraph a0 a1 y + x • v ∈ t_set := by
          rw [h_image]
          exact ⟨y, hy, x, hx, rfl⟩
        have h_plane :
            affineGraph a0 a1 y + x • v ∈
              (AffineSubspace.mk'
                (x • v) (ℝ ∙ v)ᗮ : Set R3) := by
          have h8 :
              inner ℝ (affineGraph a0 a1 y) v = 0 :=
            h_perp y
          have h9 :
              inner ℝ (affineGraph a0 a1 y + x • v) v =
                x := by
            have h10 :
                inner ℝ (affineGraph a0 a1 y + x • v) v =
                  inner ℝ (affineGraph a0 a1 y) v +
                    inner ℝ (x • v) v := by
              rw [inner_add_left]
            rw [h10, h8]
            have h11 :
                inner ℝ (x • v) v =
                  x * inner ℝ v v := by
              rw [real_inner_smul_left]
            rw [h11, hinner]
            ring
          exact (plane_iff v hv_norm x _).mpr h9
        exact ⟨h_t, h_plane⟩
    · rw [if_neg hx]
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h_t h_plane
      rw [h_image] at h_t
      rcases h_t with ⟨y, hy, t, ht, rfl⟩
      have h_t_eq_x : t = x := by
        have h7 :
            inner ℝ (affineGraph a0 a1 y + t • v) v =
              t := by
          have h8 :
              inner ℝ (affineGraph a0 a1 y) v = 0 :=
            h_perp y
          have h9 :
              inner ℝ (affineGraph a0 a1 y + t • v) v =
                inner ℝ (affineGraph a0 a1 y) v +
                  inner ℝ (t • v) v := by
            rw [inner_add_left]
          rw [h9, h8]
          have h10 :
              inner ℝ (t • v) v =
                t * inner ℝ v v := by
            rw [real_inner_smul_left]
          rw [h10, hinner]
          ring
        have h_inner_eq :
            inner ℝ (affineGraph a0 a1 y + t • v) v = x :=
          (plane_iff v hv_norm x _).mp h_plane
        linarith
      rw [h_t_eq_x] at ht
      exact hx ht

  have h_slice2_raw :=
    EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral
      (0 : R3) hv_ne_zero ht_meas
  have h_slice2 :
      volume t_set =
        ‖v‖ₑ *
          ∫⁻ (x : ℝ),
            μHE[2]
              (t_set ∩
                (AffineSubspace.mk'
                  (x • v) (ℝ ∙ v)ᗮ : Set R3)) := by
    have h_vol2 : (μHE[3] : Measure R3) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume 3
    have h :
        μHE[3] t_set =
          ‖v‖ₑ *
            ∫⁻ (x : ℝ),
              μHE[2]
                (t_set ∩
                  (AffineSubspace.mk'
                    (x • v) (ℝ ∙ v)ᗮ : Set R3)) := by
      simpa [hfin3, vadd_zero] using h_slice2_raw
    rw [h_vol2] at h
    exact h

  have h_norm_v : ‖v‖ₑ = 1 := by
    have h : ‖v‖ = 1 := hv_norm
    simpa [enorm] using
      congr_arg (fun x : ℝ => ENNReal.ofReal x) h

  let c1 : ENNReal :=
    μHE[2] (affineGraph a0 a1 '' B)

  have h_translation2 : ∀ (c : R3),
      μHE[2]
          ((fun z : R3 => z + c) ''
            (affineGraph a0 a1 '' B)) =
        c1 := by
    intro c
    let transl : R3 → R3 := fun z => z + c
    have h_iso : Isometry transl := by
      intro x y
      simp [transl, dist_eq_norm]
    exact Isometry.euclideanHausdorffMeasure_image
      h_iso (affineGraph a0 a1 '' B)

  have h_eq2 : ∀ (x : ℝ),
      μHE[2]
          (t_set ∩
            (AffineSubspace.mk'
              (x • v) (ℝ ∙ v)ᗮ : Set R3)) =
        Set.indicator
          (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c1) x := by
    intro x
    rw [h_intersection2 x]
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · rw [if_pos hx]
      have h_ind :
          Set.indicator
              (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c1) x =
            c1 := by
        simp [Set.indicator, hx]
      rw [h_ind, h_translation2 (x • v)]
    · rw [if_neg hx]
      have h_ind :
          Set.indicator
              (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c1) x =
            0 := by
        simp [Set.indicator, hx]
      rw [h_ind]
      simp

  have h_integral2 :
      (∫⁻ (x : ℝ),
        μHE[2]
          (t_set ∩
            (AffineSubspace.mk'
              (x • v) (ℝ ∙ v)ᗮ : Set R3))) =
        2 * c1 := by
    have h1 :
        (∫⁻ (x : ℝ),
          μHE[2]
            (t_set ∩
              (AffineSubspace.mk'
                (x • v) (ℝ ∙ v)ᗮ : Set R3))) =
          ∫⁻ (x : ℝ),
            Set.indicator
              (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c1) x := by
      congr with x
      exact h_eq2 x
    rw [h1]
    have h2 :
        ∫⁻ (x : ℝ),
            Set.indicator
              (Ioo (-1 : ℝ) 1) (fun _ : ℝ => c1) x =
          ∫⁻ (_x : ℝ) in Ioo (-1 : ℝ) 1, c1 := by
      rw [lintegral_indicator measurableSet_Ioo] <;> rfl
    have h_volIoo2 :
        volume (Ioo (-1 : ℝ) 1) = (2 : ENNReal) := by
      rw [Real.volume_Ioo
        (a := (-1 : ℝ)) (b := (1 : ℝ))]
      norm_num
    rw [h2, setLIntegral_const, h_volIoo2]
    ring

  have h_main1 : volume t_set = 2 * c1 := by
    rw [h_slice2, h_integral2, h_norm_v]
    ring

  have h_main2 :
      2 * c1 =
        2 * (ENNReal.ofReal s * volume B) := by
    calc
      2 * c1 = volume t_set := h_main1.symm
      _ = volume (ACLM '' D) := by rfl
      _ = ENNReal.ofReal s * volume D := h_cov
      _ = ENNReal.ofReal s * (2 * volume B) := by
        rw [h_step1]
      _ = 2 * (ENNReal.ofReal s * volume B) := by
        ring

  have h_main3 :
      c1 = ENNReal.ofReal s * volume B := by
    have h : (2 : ENNReal) ≠ 0 := by norm_num
    have h' : (2 : ENNReal) ≠ ⊤ := by norm_num
    have h_eq4 :
        c1 * 2 =
          (ENNReal.ofReal s * volume B) * 2 := by
      have h_comm1 : c1 * 2 = 2 * c1 := by ring
      have h_comm2 :
          (ENNReal.ofReal s * volume B) * 2 =
            2 * (ENNReal.ofReal s * volume B) := by
        ring
      rw [h_comm1, h_comm2]
      exact h_main2
    exact (ENNReal.mul_left_inj h h').mp h_eq4

  let hf : NNReal :=
    MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure R2) (μH[2] : Measure R2)
  have h_def :
      (μHE[2] : Measure R3) =
        (hf : ENNReal) • (μH[2] : Measure R3) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def 2
  have hf_ne_zero : (hf : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr
      (MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2)
  have hf_ne_top : (hf : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top

  have h4 :
      μHE[2] (affineGraph a0 a1 '' B) =
        (hf : ENNReal) *
          μH[2] (affineGraph a0 a1 '' B) := by
    rw [h_def]
    rfl
  have h5 :
      μH[2] (affineGraph a0 a1 '' B) =
        planeConstant *
          μHE[2] (affineGraph a0 a1 '' B) := by
    rw [h4]
    dsimp only [planeConstant]
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel hf_ne_zero hf_ne_top]
    simp
  have h_final :
      μH[2] (affineGraph a0 a1 '' B) =
        planeConstant * ENNReal.ofReal s * volume B := by
    rw [h5]
    dsimp only [c1] at h_main3
    rw [h_main3]
    ring
  exact h_final

/-- Area formula for an affine graph `z = a·y + b`. -/
lemma affine_graph_area_unweighted
    {A : Set R2} (hA : MeasurableSet A)
    {a : R2 →L[ℝ] ℝ} {b : ℝ} :
    μH[2] (graphMap (fun y => a y + b) '' A) =
      planeConstant *
        ENNReal.ofReal (Real.sqrt (1 + ‖a‖^2)) *
          volume A := by
  let a0 : ℝ := a e02
  let a1 : ℝ := a e12
  have hnorm : ‖a‖^2 = a0^2 + a1^2 := by
    let b2 : OrthonormalBasis (Fin 2) ℝ R2 :=
      EuclideanSpace.basisFun (Fin 2) ℝ
    have h_b0 : b2 0 = e02 := by
      simp [b2, EuclideanSpace.basisFun_apply, e02]
      <;> ext i <;> fin_cases i <;> simp
    have h_b1 : b2 1 = e12 := by
      simp [b2, EuclideanSpace.basisFun_apply, e12]
      <;> ext i <;> fin_cases i <;> simp
    have h1 :
        ‖a‖^2 = ∑ i : Fin 2, (a (b2 i))^2 :=
      b2.norm_dual a
    rw [h1, Fin.sum_univ_two, h_b0, h_b1]
  have h_eq1 :
      ∀ (y : R2),
        a y = a0 * y 0 + a1 * y 1 := by
    intro y
    have hy :
        y = y 0 • e02 + y 1 • e12 := by
      ext i
      fin_cases i <;> simp [e02, e12] <;> ring
    have h5 :
        a y = a (y 0 • e02 + y 1 • e12) :=
      congr_arg a hy
    rw [h5]
    have h6 :
        a (y 0 • e02 + y 1 • e12) =
          y 0 * a e02 + y 1 * a e12 := by
      rw [map_add, map_smul, map_smul]
      ring
    rw [h6]
    have ha0 : a e02 = a0 := by rfl
    have ha1 : a e12 = a1 := by rfl
    rw [ha0, ha1] <;> ring
  have h1 :
      (fun y : R2 => a y + b) =
        fun y : R2 =>
          a0 * y 0 + a1 * y 1 + b := by
    funext y
    rw [h_eq1 y] <;> ring
  rw [h1]
  let shift : R3 :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm ![0, 0, b]
  have h_shift :
      graphMap
          (fun y : R2 =>
            a0 * y 0 + a1 * y 1 + b) =
        fun y =>
          graphMap
              (fun y : R2 =>
                a0 * y 0 + a1 * y 1) y +
            shift := by
    funext y
    ext i
    fin_cases i <;> simp [graphMap, shift] <;> ring
  rw [h_shift]
  have h_transl :
      μH[2]
          ((fun y =>
            graphMap
                (fun y : R2 =>
                  a0 * y 0 + a1 * y 1) y +
              shift) '' A) =
        μH[2]
          (graphMap
            (fun y : R2 =>
              a0 * y 0 + a1 * y 1) '' A) := by
    let transl : R3 → R3 := fun z => z + shift
    have h_set :
        (fun y : R2 =>
            graphMap
                (fun y : R2 =>
                  a0 * y 0 + a1 * y 1) y +
              shift) '' A =
          transl ''
            (graphMap
              (fun y : R2 =>
                a0 * y 0 + a1 * y 1) '' A) := by
      ext z
      simp only [Set.mem_image, transl]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact
          ⟨graphMap
              (fun y : R2 =>
                a0 * y 0 + a1 * y 1) y,
            ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [h_set]
    have h_iso : Isometry transl := by
      intro x y
      simp [transl, edist_dist, dist_eq_norm]
    exact Isometry.hausdorffMeasure_image h_iso
      (Or.inl (by norm_num : (0 : ℝ) ≤ 2))
      (graphMap
        (fun y : R2 =>
          a0 * y 0 + a1 * y 1) '' A)
  rw [h_transl]
  have h6 :
      graphMap
          (fun y : R2 =>
            a0 * y 0 + a1 * y 1) =
        affineGraph a0 a1 := by
    simp [affineGraph]
  rw [h6]
  rw [affine_graph_area_formula a0 a1 hA]
  have h7 :
      Real.sqrt (1 + ‖a‖^2) =
        Real.sqrt (1 + a0^2 + a1^2) := by
    rw [hnorm]
    congr 1
    ring
  rw [← h7]

end Kakeya.CV

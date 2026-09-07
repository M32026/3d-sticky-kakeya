/-
# Perimeter Basics — De Giorgi Perimeter and Translation Bound

## Definitions

- `divergence φ`: trace of the derivative of a vector field
- `TestVectorField`: smooth, compactly supported vector field with ‖φ‖ ≤ 1
- `TestScalar`: smooth, compactly supported scalar function with |φ| ≤ 1
- `perimeter S`: De Giorgi perimeter = sup |∫_S div φ|
- `directionalVariation S v`: total variation of distributional derivative ∂_v χ_S
- `translateSet S v`: set translation

## Main results

1. `directionalVariation_le_perimeter`: directional variation ≤ ‖v‖ · P(S)
2. `perimeter_translation`: P(S + v) = P(S)
3. `perimeter_scaling`: P(t · S) = t^(n-1) · P(S)

## References

- Ambrosio-Fusco-Pallara, Functions of BV, Ch. 2
- Maggi, Sets of Finite Perimeter, Ch. 3
- Evans-Gariepy, Measure Theory, Ch. 5
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Divergence of a vector field `φ : E n → E n`. -/
noncomputable def divergence (φ : E n → E n) : E n → ℝ :=
  fun x => ∑ i : Fin n, fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single i 1)

/-- A test vector field for the perimeter: smooth, compactly supported, ‖φ‖ ≤ 1. -/
structure TestVectorField where
  toFun : E n → E n
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  bound : ∀ x, ‖toFun x‖ ≤ 1

/-- A test scalar function for directional variation: smooth, compactly supported, |φ| ≤ 1. -/
structure TestScalar where
  toFun : E n → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  bound : ∀ x, |toFun x| ≤ 1

/-- Divergence of a smooth compactly supported vector field is smooth. -/
lemma divergence_smooth (φ : TestVectorField) :
    ContDiff ℝ ∞ (divergence (φ.toFun : E n → E n)) := by
  let g (i : Fin n) : E n → ℝ := fun y => φ.toFun y i
  let f (i : Fin n) : E n → ℝ :=
    fun y => fderiv ℝ (g i) y (EuclideanSpace.single i 1)
  have h1 : ∀ i, ContDiff ℝ ∞ (f i) := by
    intro i
    have hproj : ContDiff ℝ ∞ (fun v : E n => v i) := by fun_prop
    have hgi_smooth : ContDiff ℝ ∞ (g i) := by
      have h_eq :
          g i = (fun v : E n => v i) ∘ (φ.toFun : E n → E n) := by
        funext z
        rfl
      rw [h_eq]
      exact hproj.comp φ.smooth
    have h_fd : ContDiff ℝ ∞ (fderiv ℝ (g i)) := by
      apply hgi_smooth.fderiv_right
      simp
    let v : E n := EuclideanSpace.single i 1
    let ev : (E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
      { toFun := fun f' => f' v
        map_add' := by
          intro f' g'
          simp
        map_smul' := by
          intro c f'
          simp }
    exact ev.contDiff.comp h_fd
  have h_sum :
      ContDiff ℝ ∞ (fun x : E n => ∑ i : Fin n, f i x) :=
    ContDiff.sum (fun i _ => h1 i)
  have h_eq :
      divergence (φ.toFun : E n → E n) =
        fun x : E n => ∑ i : Fin n, f i x := by
    funext x
    rfl
  rw [h_eq]
  exact h_sum

/-- Divergence of a compactly supported vector field has compact support. -/
lemma divergence_hasCompactSupport (φ : TestVectorField) :
    HasCompactSupport (divergence (φ.toFun : E n → E n)) := by
  let g (i : Fin n) : E n → ℝ :=
    fun y => fderiv ℝ (fun z : E n => φ.toFun z i) y
      (EuclideanSpace.single i 1)
  have h1 : ∀ i, HasCompactSupport (g i) := by
    intro i
    have hproj : ContDiff ℝ ∞ (fun v : E n => v i) := by fun_prop
    have hφi_smooth : ContDiff ℝ ∞ (fun y : E n => φ.toFun y i) := by
      have h_eq :
          (fun y : E n => φ.toFun y i) =
            (fun v : E n => v i) ∘ (φ.toFun : E n → E n) := by
        funext z
        rfl
      rw [h_eq]
      exact hproj.comp φ.smooth
    have hφi_support : HasCompactSupport (fun y : E n => φ.toFun y i) := by
      have h :
          Function.support (fun y : E n => φ.toFun y i) ⊆
            Function.support (φ.toFun : E n → E n) := by
        intro y hy
        have h2 : φ.toFun y i ≠ 0 := hy
        have h3 : φ.toFun y ≠ 0 := by
          intro h4
          have h5 : φ.toFun y i = 0 := by
            rw [h4]
            simp
          exact h2 h5
        simpa [Function.mem_support] using h3
      exact φ.compact.mono h
    exact hφi_support.fderiv_apply (𝕜 := ℝ)
      (EuclideanSpace.single i 1)
  have h_union :
      IsCompact (⋃ i ∈ Finset.univ, tsupport (g i)) := by
    exact Finset.isCompact_biUnion Finset.univ fun i _ => (h1 i).isCompact
  have h_supp :
      Function.support (fun x : E n => ∑ i : Fin n, g i x) ⊆
        ⋃ i ∈ Finset.univ, tsupport (g i) := by
    intro x hx
    by_contra h
    have hzero : ∀ i, g i x = 0 := by
      intro i
      have hnot : x ∉ tsupport (g i) := by
        intro hi
        exact h (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hnot' : x ∉ Function.support (g i) := by
        intro hi
        exact hnot (subset_closure hi)
      simpa [Function.mem_support] using hnot'
    exact hx (Finset.sum_eq_zero fun i _ => hzero i)
  have h_tsupp :
      tsupport (fun x : E n => ∑ i : Fin n, g i x) ⊆
        ⋃ i ∈ Finset.univ, tsupport (g i) :=
    closure_minimal h_supp h_union.isClosed
  have h_sum_support :
      HasCompactSupport (fun x : E n => ∑ i : Fin n, g i x) :=
    h_union.of_isClosed_subset isClosed_closure h_tsupp
  have h_eq :
      divergence (φ.toFun : E n → E n) =
        fun x : E n => ∑ i : Fin n, g i x := by
    funext x
    rfl
  rw [h_eq]
  exact h_sum_support

/-- **De Giorgi perimeter** of a set `S`. -/
noncomputable def perimeter (S : Set (E n)) : ENNReal :=
  iSup fun (φ : TestVectorField) =>
    ENNReal.ofReal |∫ x in S, divergence φ.toFun x|

/-- **Directional variation** of `S` in direction `v`. -/
noncomputable def directionalVariation (S : Set (E n)) (v : E n) : ENNReal :=
  iSup fun (φ : TestScalar) =>
    ENNReal.ofReal |∫ x in S, fderiv ℝ φ.toFun x v|

/-- Translation of a set by a vector. -/
def translateSet (S : Set (E n)) (v : E n) : Set (E n) :=
  (fun x => x + v) '' S

-- ============================================================================
-- Divergence of scalar times constant vector
-- ============================================================================

/-- For smooth scalar φ and constant vector w, `divergence (φ • w) = fderiv φ w`. -/
lemma divergence_smul_const {φ : E n → ℝ} {w : E n} (hφ : ContDiff ℝ ∞ φ) :
    divergence (fun x => φ x • w) = fun x => fderiv ℝ φ x w := by
  funext x
  have hdiff : DifferentiableAt ℝ φ x :=
    (hφ.differentiable (by simp)).differentiableAt
  have h2 : HasFDerivAt φ (fderiv ℝ φ x) x := hdiff.hasFDerivAt
  have h1 : ∀ i : Fin n, fderiv ℝ (fun y : E n => (φ y • w) i) x =
      (fderiv ℝ φ x).smulRight (w i) := by
    intro i
    have h_eq : (fun y : E n => (φ y • w) i) = (fun y : E n => w i * φ y) := by
      funext y; simp [mul_comm]
    rw [h_eq]
    have h3 : HasFDerivAt (fun y : E n => w i * φ y) ((w i) • fderiv ℝ φ x) x :=
      h2.const_mul (w i)
    have h5 : (w i) • fderiv ℝ φ x = (fderiv ℝ φ x).smulRight (w i) := by
      ext z; simp [LinearMap.smulRight_apply] <;> ring
    rw [h5] at h3
    exact h3.fderiv
  have hdiv : divergence (fun x : E n => φ x • w) x =
      ∑ i : Fin n, (w i) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    have h_eq1 : divergence (fun x : E n => φ x • w) x =
        ∑ i : Fin n, (fderiv ℝ (fun y : E n => (φ y • w) i) x) (EuclideanSpace.single i 1) := by rfl
    rw [h_eq1]
    apply Finset.sum_congr rfl
    intro i _
    have h6 : (fderiv ℝ (fun y : E n => (φ y • w) i) x) (EuclideanSpace.single i 1) =
        (fderiv ℝ φ x).smulRight (w i) (EuclideanSpace.single i 1) := by
      rw [h1 i]
    rw [h6]
    simp [LinearMap.smulRight_apply] <;> ring
  rw [hdiv]
  let b := PiLp.basisFun 2 ℝ (Fin n)
  have hsum : ∑ i : Fin n, b.repr w i • b i = w := b.sum_repr w
  have h2 : ∀ i : Fin n, b.repr w i = w i := by
    intro i
    simp [b, PiLp.basisFun_apply] <;> rfl
  have h3 : ∀ i : Fin n, b i = EuclideanSpace.single i 1 := by
    intro i
    simp [b, PiLp.basisFun_apply] <;> rfl
  have h4 : ∑ i : Fin n, b.repr w i • b i = ∑ i : Fin n, (w i) • EuclideanSpace.single i 1 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h2 i, h3 i]
  have hbasis : w = ∑ i : Fin n, (w i) • EuclideanSpace.single i 1 :=
    hsum.symm.trans h4
  have h_goal : fderiv ℝ φ x w =
      ∑ i : Fin n, (w i) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    have h_arg : fderiv ℝ φ x w = fderiv ℝ φ x (∑ i : Fin n, (w i) • EuclideanSpace.single i 1) :=
      congr_arg (fderiv ℝ φ x) hbasis
    rw [h_arg]
    have h8 : fderiv ℝ φ x (∑ i : Fin n, (w i) • EuclideanSpace.single i 1) =
        ∑ i : Fin n, fderiv ℝ φ x ((w i) • EuclideanSpace.single i 1) := by
      rw [map_sum]
      <;> rfl
    rw [h8]
    apply Finset.sum_congr rfl
    intro i _
    have h10 : fderiv ℝ φ x ((w i) • EuclideanSpace.single i 1) =
        (w i) * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      (fderiv ℝ φ x).map_smul (w i) (EuclideanSpace.single i 1)
    exact h10
  exact h_goal.symm

-- ============================================================================
-- Lemma 1: Directional variation ≤ ‖v‖ * perimeter
-- ============================================================================

/-- Directional variation is bounded by `‖v‖ * perimeter S`. -/
lemma directionalVariation_le_perimeter {S : Set (E n)} {v : E n} :
    directionalVariation S v ≤ ENNReal.ofReal ‖v‖ * perimeter S := by
  by_cases hv : v = 0
  · -- v = 0
    have h1 : directionalVariation S v = 0 := by
      subst hv
      rw [directionalVariation]
      rw [iSup_eq_zero]
      intro φ
      have h2 : ∀ x, fderiv ℝ φ.toFun x (0 : E n) = 0 := by
        intro x
        exact map_zero (fderiv ℝ φ.toFun x)
      have h3 : (∫ x in S, fderiv ℝ φ.toFun x (0 : E n)) = 0 := by
        have h4 : (fun x : E n => fderiv ℝ φ.toFun x (0 : E n)) = fun (_ : E n) => (0 : ℝ) := by
          funext x; exact h2 x
        rw [h4] <;> simp
      rw [h3] <;> simp
    rw [h1] <;> simp
  · -- v ≠ 0
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let c : ℝ := ‖v‖
    let w : E n := (c⁻¹ : ℝ) • v
    have hwnorm : ‖w‖ = 1 := by
      simp [w, c, norm_smul, hnv.ne'] <;> field_simp [hnv.ne'] <;> ring
    have hwv : v = c • w := by
      have h : c • w = v := by
        simp [w, c, smul_smul, hnv.ne'] <;> field_simp [hnv.ne'] <;> simp
      exact h.symm
    apply iSup_le
    intro φ
    let ψ : TestVectorField :=
      { toFun := fun x => φ.toFun x • w
        smooth := φ.smooth.smul_const w
        compact := by
          have h : Function.support (fun x : E n => φ.toFun x • w) ⊆ Function.support φ.toFun := by
            intro x hx
            simp only [Function.mem_support] at hx ⊢
            by_contra h2
            have h3 : φ.toFun x = 0 := by simpa [Function.mem_support] using h2
            rw [h3] at hx <;> simp at hx
          exact φ.compact.mono h
        bound := fun x => by
          have h : ‖φ.toFun x • w‖ = |φ.toFun x| * ‖w‖ := by
            simp [norm_smul] <;> ring
          rw [h, hwnorm]
          have h2 : |φ.toFun x| ≤ 1 := φ.bound x
          simpa using h2 }
    have hdiv : ∀ x, divergence ψ.toFun x = fderiv ℝ φ.toFun x w := by
      intro x
      have h : divergence ψ.toFun = fun y => fderiv ℝ φ.toFun y w := divergence_smul_const φ.smooth
      exact congr_fun h x
    have h6 : ∀ x, fderiv ℝ φ.toFun x v = c * divergence ψ.toFun x := by
      intro x
      have h7 : fderiv ℝ φ.toFun x v = c * fderiv ℝ φ.toFun x w := by
        have h71 : v = c • w := hwv
        have h : fderiv ℝ φ.toFun x v = fderiv ℝ φ.toFun x (c • w) := by
          apply congr_arg (fderiv ℝ φ.toFun x) h71
        rw [h]
        have h2 : fderiv ℝ φ.toFun x (c • w) = c * fderiv ℝ φ.toFun x w :=
          (fderiv ℝ φ.toFun x).map_smul c w
        exact h2
      rw [h7, hdiv x] <;> ring
    have h_eq : (∫ x in S, fderiv ℝ φ.toFun x v) =
        c * (∫ x in S, divergence ψ.toFun x) := by
      have h9 : ∀ᵐ x ∂volume.restrict S, fderiv ℝ φ.toFun x v = c * divergence ψ.toFun x :=
        ae_of_all _ (fun x => h6 x)
      rw [integral_congr_ae h9, integral_const_mul]
    have h_abs : |∫ x in S, fderiv ℝ φ.toFun x v| =
        c * |∫ x in S, divergence ψ.toFun x| := by
      rw [h_eq]
      rw [abs_mul, abs_of_nonneg (show 0 ≤ c from norm_nonneg _)] <;> ring
    rw [h_abs]
    have h9 : ENNReal.ofReal (c * |∫ x in S, divergence ψ.toFun x|) =
        ENNReal.ofReal c * ENNReal.ofReal |∫ x in S, divergence ψ.toFun x| := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _)] <;> simp
    rw [h9]
    exact mul_le_mul_of_nonneg_left (le_iSup (fun (θ : TestVectorField) =>
      ENNReal.ofReal |∫ x in S, divergence θ.toFun x|) ψ) (by positivity)


-- ============================================================================
-- Divergence under translation
-- ============================================================================

/-- Divergence is preserved under translation. -/
lemma divergence_comp_translation {Φ : E n → E n} (hΦ : ContDiff ℝ ∞ Φ) (v : E n) :
    divergence (fun x : E n => Φ (x + v)) = fun x : E n => divergence Φ (x + v) := by
  funext x
  let idCLM : E n →L[ℝ] E n := ContinuousLinearMap.id ℝ (E n)
  have hmain : ∀ (i : Fin n), fderiv ℝ (fun y : E n => (Φ (y + v)) i) x (EuclideanSpace.single i 1) =
      fderiv ℝ (fun z : E n => Φ z i) (x + v) (EuclideanSpace.single i 1) := by
    intro i
    let π_i : E n →L[ℝ] ℝ :=
      { toFun := fun w => w i
        map_add' := by intro a b; rfl
        map_smul' := by intro c a; rfl }
    let f_i : E n → ℝ := fun z => Φ z i
    have hproj : ContDiff ℝ ∞ π_i := π_i.contDiff
    have hf_i : ContDiff ℝ ∞ f_i := hproj.comp hΦ
    have hL : HasFDerivAt (fun y : E n => y + v) idCLM x :=
      (hasFDerivAt_id x).add_const v
    have hfdiff : HasFDerivAt f_i (fderiv ℝ f_i (x + v)) (x + v) :=
      (hf_i.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp_raw : HasFDerivAt (f_i ∘ (fun y : E n => y + v))
        ((fderiv ℝ f_i (x + v)).comp idCLM) x := hfdiff.comp x hL
    have hfun : (f_i ∘ (fun y : E n => y + v)) = (fun y : E n => f_i (y + v)) := by
      funext y; rfl
    have hcomp : HasFDerivAt (fun y : E n => f_i (y + v))
        ((fderiv ℝ f_i (x + v)).comp idCLM) x := by
      rw [hfun] at hcomp_raw; exact hcomp_raw
    have h_id : ∀ (z : E n), idCLM z = z := by intro z; rfl
    have h_eq : (fderiv ℝ f_i (x + v)).comp idCLM = fderiv ℝ f_i (x + v) := by
      ext z
      rw [ContinuousLinearMap.comp_apply, h_id z]
    have h_main2 : fderiv ℝ (fun y : E n => f_i (y + v)) x = (fderiv ℝ f_i (x + v)).comp idCLM :=
      hcomp.fderiv
    rw [h_main2, h_eq]
  have hsum : ∑ i : Fin n, fderiv ℝ (fun y : E n => (Φ (y + v)) i) x (EuclideanSpace.single i 1) =
      ∑ i : Fin n, fderiv ℝ (fun z : E n => Φ z i) (x + v) (EuclideanSpace.single i 1) := by
    apply Finset.sum_congr rfl; intro i _; exact hmain i
  rw [divergence, hsum] <;> rfl

-- ============================================================================
-- Translation invariance
-- ============================================================================

/-- Perimeter is translation invariant. -/
theorem perimeter_translation (S : Set (E n)) (hS : MeasurableSet S) (v : E n) :
    perimeter (translateSet S v) = perimeter S := by
  let e : E n ≃ₜ E n := Homeomorph.addRight v
  let idCLM : E n →L[ℝ] E n := ContinuousLinearMap.id ℝ (E n)
  have h_inj : Set.InjOn (e : E n → E n) S := by
    intro x _ y _ hxy; exact e.injective hxy
  have h_fderiv : ∀ x ∈ S, HasFDerivWithinAt (e : E n → E n) idCLM S x := by
    intro x _
    have h : HasFDerivAt (e : E n → E n) idCLM x :=
      (hasFDerivAt_id x).add_const v
    exact h.hasFDerivWithinAt
  have h_det : |idCLM.det| = (1 : ℝ) := by
    have h1 : idCLM.toLinearMap = LinearMap.id (R := ℝ) (M := E n) := by
      ext x; rfl
    have h2 : idCLM.det = 1 := by
      have h3 : idCLM.det = LinearMap.det idCLM.toLinearMap := by rfl
      rw [h3, h1]
      exact LinearMap.det_id
    rw [h2] <;> norm_num
  have h_img : translateSet S v = (e : E n → E n) '' S := by rfl
  have h1 : perimeter (translateSet S v) ≤ perimeter S := by
    apply iSup_le
    intro φ
    let h : E n ≃ₜ E n := Homeomorph.addRight (-v)
    let ψ : TestVectorField :=
      { toFun := fun x => φ.toFun (x + v)
        smooth := φ.smooth.comp (contDiff_id.add contDiff_const)
        compact := by
          have h_supp : Function.support (fun x : E n => φ.toFun (x + v)) =
              h '' Function.support φ.toFun := by
            ext y; simp [Function.mem_support, h] <;> aesop
          have h_ts : tsupport (fun x : E n => φ.toFun (x + v)) = h '' tsupport φ.toFun := by
            rw [tsupport, h_supp]
            exact (h.image_closure (Function.support φ.toFun)).symm
          have h_compact : IsCompact (tsupport (fun x : E n => φ.toFun (x + v))) := by
            rw [h_ts]
            exact φ.compact.image h.continuous
          exact h_compact
        bound := fun x => φ.bound (x + v) }
    have h_e_eq : ∀ x, e x = x + v := by intro x; rfl
    have h_eq1 : ∫ y in translateSet S v, divergence φ.toFun y =
        ∫ x in S, divergence φ.toFun (x + v) := by
      rw [h_img]
      rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
        volume hS h_fderiv h_inj (divergence φ.toFun)]
      rw [h_det]
      <;> simp [h_e_eq]
    have hdiv_eq : divergence ψ.toFun = fun x => divergence φ.toFun (x + v) :=
      divergence_comp_translation φ.smooth v
    have h_eq2 : ∫ x in S, divergence φ.toFun (x + v) = ∫ x in S, divergence ψ.toFun x := by
      rw [← hdiv_eq] <;> rfl
    rw [h_eq1, h_eq2]
    exact le_iSup (fun (θ : TestVectorField) => ENNReal.ofReal |∫ x in S, divergence θ.toFun x|) ψ
  have h2 : perimeter S ≤ perimeter (translateSet S v) := by
    apply iSup_le
    intro ψ
    let h : E n ≃ₜ E n := Homeomorph.addRight v
    let φ : TestVectorField :=
      { toFun := fun x => ψ.toFun (x - v)
        smooth := ψ.smooth.comp (contDiff_id.sub contDiff_const)
        compact := by
          have h_supp : Function.support (fun x : E n => ψ.toFun (x - v)) =
              h '' Function.support ψ.toFun := by
            ext y; simp [Function.mem_support, h] <;> aesop
          have h_ts : tsupport (fun x : E n => ψ.toFun (x - v)) = h '' tsupport ψ.toFun := by
            rw [tsupport, h_supp]
            exact (h.image_closure (Function.support ψ.toFun)).symm
          have h_compact : IsCompact (tsupport (fun x : E n => ψ.toFun (x - v))) := by
            rw [h_ts]
            exact ψ.compact.image h.continuous
          exact h_compact
        bound := fun x => ψ.bound (x - v) }
    have hdiv_eq : divergence φ.toFun = fun y => divergence ψ.toFun (y - v) :=
      divergence_comp_translation ψ.smooth (-v)
    have h3 : ∀ x, divergence φ.toFun (x + v) = divergence ψ.toFun x := by
      intro x
      have h4 : divergence φ.toFun (x + v) = divergence ψ.toFun ((x + v) - v) := by
        rw [hdiv_eq] <;> rfl
      rw [h4]
      have h5 : (x + v) - v = x := by abel
      rw [h5]
    have h_e_eq : ∀ x, e x = x + v := by intro x; rfl
    have h_eq1 : ∫ y in translateSet S v, divergence φ.toFun y =
        ∫ x in S, divergence φ.toFun (x + v) := by
      rw [h_img]
      rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
        volume hS h_fderiv h_inj (divergence φ.toFun)]
      rw [h_det] <;> simp [h_e_eq]
    have h_eq2 : ∫ x in S, divergence φ.toFun (x + v) = ∫ x in S, divergence ψ.toFun x := by
      apply integral_congr_ae
      exact ae_of_all _ h3
    have h_final : ∫ y in translateSet S v, divergence φ.toFun y = ∫ x in S, divergence ψ.toFun x := by
      rw [h_eq1, h_eq2]
    have h_goal : ENNReal.ofReal |∫ x in S, divergence ψ.toFun x| ≤ perimeter (translateSet S v) := by
      rw [← h_final]
      exact le_iSup (fun (θ : TestVectorField) =>
        ENNReal.ofReal |∫ x in translateSet S v, divergence θ.toFun x|) φ
    exact h_goal
  exact le_antisymm h1 h2

-- ============================================================================
-- Scaling property
-- ============================================================================

/-- Scaled set `t • S := {t • x | x ∈ S}`. -/
def scaleSet (t : ℝ) (S : Set (E n)) : Set (E n) :=
  (fun x => t • x) '' S

private lemma fderiv_comp_smul_scalar {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (ht : t ≠ 0) (x : E n) :
    fderiv ℝ (fun y : E n => f (t • y)) x = t • fderiv ℝ f (t • x) := by
  let L : E n →L[ℝ] E n :=
    { toFun := fun z => t • z
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c a => by simp [smul_smul, mul_comm c t] }
  have hL : HasFDerivAt (fun y : E n => t • y) L x := L.hasFDerivAt
  have hfdiff : HasFDerivAt f (fderiv ℝ f (t • x)) (t • x) :=
    (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E n => f (t • y))
      ((fderiv ℝ f (t • x)).comp L) x := hfdiff.comp x hL
  have h_eq : (fderiv ℝ f (t • x)).comp L = t • fderiv ℝ f (t • x) := by
    ext z; simp [L, ContinuousLinearMap.comp_apply, smul_smul] <;> ring
  have h_main : fderiv ℝ (fun y : E n => f (t • y)) x = (fderiv ℝ f (t • x)).comp L :=
    hcomp.fderiv
  rw [h_main, h_eq]

/-- Divergence under scaling: `div(Φ(t·x)) = t · div Φ(t·x)`. -/
lemma divergence_comp_smul {Φ : E n → E n} (hΦ : ContDiff ℝ ∞ Φ) {t : ℝ} (ht : t ≠ 0) :
    divergence (fun x : E n => Φ (t • x)) = fun x : E n => t * divergence Φ (t • x) := by
  funext x
  let π_i (i : Fin n) : E n →L[ℝ] ℝ :=
    { toFun := fun w => w i
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hmain : ∀ (i : Fin n), fderiv ℝ (fun y : E n => (Φ (t • y)) i) x (EuclideanSpace.single i 1) =
      t * fderiv ℝ (fun z : E n => Φ z i) (t • x) (EuclideanSpace.single i 1) := by
    intro i
    let f_i : E n → ℝ := fun z => Φ z i
    have hproj : ContDiff ℝ ∞ (π_i i) := (π_i i).contDiff
    have hf_i : ContDiff ℝ ∞ f_i := hproj.comp hΦ
    rw [fderiv_comp_smul_scalar hf_i ht x] <;> rfl
  have hsum : ∑ i : Fin n, fderiv ℝ (fun y : E n => (Φ (t • y)) i) x (EuclideanSpace.single i 1) =
      ∑ i : Fin n, t * fderiv ℝ (fun z : E n => Φ z i) (t • x) (EuclideanSpace.single i 1) := by
    apply Finset.sum_congr rfl; intro i _; exact hmain i
  have hdiv_def : divergence Φ (t • x) =
      ∑ i : Fin n, fderiv ℝ (fun z : E n => Φ z i) (t • x) (EuclideanSpace.single i 1) := by
    simp [divergence] <;> rfl
  rw [divergence, hsum]
  rw [hdiv_def]
  rw [Finset.mul_sum]

/-- Perimeter scales as `t^(n-1)`. -/
theorem perimeter_scaling (S : Set (E n)) (hS : MeasurableSet S) {t : ℝ} (ht : 0 < t) (hn : 1 ≤ n) :
    perimeter (scaleSet t S) = (ENNReal.ofReal (t ^ (n - 1))) * perimeter S := by
  have hfinrank : Module.finrank ℝ (E n) = n := by simp
  have ht_ne : t ≠ 0 := ht.ne'
  have h_pow : t ^ n = t * t ^ (n - 1) := by
    cases n with
    | zero => contradiction
    | succ n' => simp [pow_succ] <;> ring
  have h_scale_set : scaleSet t S = (fun x : E n => t • x) '' S := by rfl
  let hmap_inv : E n → E n := fun x => t⁻¹ • x
  have hcont_inv : Continuous hmap_inv := by fun_prop
  let hmap_fwd : E n → E n := fun x => t • x
  have hcont_fwd : Continuous hmap_fwd := by fun_prop
  have h_compact_scaled : ∀ (φ : TestVectorField), HasCompactSupport (fun x : E n => φ.toFun (t • x)) := by
    intro φ
    have h_sub : Function.support (fun x : E n => φ.toFun (t • x)) ⊆ hmap_inv '' tsupport φ.toFun := by
      intro x hx
      have h1 : φ.toFun (t • x) ≠ 0 := hx
      have h2 : t • x ∈ Function.support φ.toFun := h1
      have h3 : t • x ∈ tsupport φ.toFun := by
        exact subset_tsupport (f := φ.toFun) h2
      refine ⟨t • x, h3, ?_⟩
      have h4 : hmap_inv (t • x) = x := by
        simp [hmap_inv, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h4
    have h_img_compact : IsCompact (hmap_inv '' tsupport φ.toFun) :=
      φ.compact.image hcont_inv
    have h_closed : IsClosed (hmap_inv '' tsupport φ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => φ.toFun (t • x)) ⊆ hmap_inv '' tsupport φ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts
  have h_compact_unscaled : ∀ (ψ : TestVectorField), HasCompactSupport (fun x : E n => ψ.toFun (t⁻¹ • x)) := by
    intro ψ
    have h_sub : Function.support (fun x : E n => ψ.toFun (t⁻¹ • x)) ⊆ hmap_fwd '' tsupport ψ.toFun := by
      intro x hx
      have h1 : ψ.toFun (t⁻¹ • x) ≠ 0 := hx
      have h2 : t⁻¹ • x ∈ Function.support ψ.toFun := h1
      have h3 : t⁻¹ • x ∈ tsupport ψ.toFun := by
        exact subset_tsupport (f := ψ.toFun) h2
      refine ⟨t⁻¹ • x, h3, ?_⟩
      have h4 : hmap_fwd (t⁻¹ • x) = x := by
        simp [hmap_fwd, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h4
    have h_img_compact : IsCompact (hmap_fwd '' tsupport ψ.toFun) :=
      ψ.compact.image hcont_fwd
    have h_closed : IsClosed (hmap_fwd '' tsupport ψ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => ψ.toFun (t⁻¹ • x)) ⊆ hmap_fwd '' tsupport ψ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts
  have h1 : perimeter (scaleSet t S) ≤ (ENNReal.ofReal (t ^ (n - 1))) * perimeter S := by
    apply iSup_le
    intro φ
    let ψ : TestVectorField :=
      { toFun := fun x => φ.toFun (t • x)
        smooth := φ.smooth.comp (contDiff_id.const_smul t)
        compact := h_compact_scaled φ
        bound := fun x => φ.bound (t • x) }
    have hdiv : divergence ψ.toFun = fun x => t * divergence φ.toFun (t • x) :=
      divergence_comp_smul φ.smooth ht_ne
    have h_change : ∫ x in scaleSet t S, divergence φ.toFun x =
        (t ^ n) * ∫ x in S, divergence φ.toFun (t • x) := by
      have h : ∫ x in S, divergence φ.toFun (t • x) =
          (t ^ n)⁻¹ * ∫ x in scaleSet t S, divergence φ.toFun x := by
        rw [MeasureTheory.Measure.setIntegral_comp_smul volume (divergence φ.toFun) S ht_ne]
        rw [hfinrank]
        have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
          rw [abs_of_nonneg] <;> positivity
        rw [h_abs] <;> rfl
      have h' : ∫ x in scaleSet t S, divergence φ.toFun x =
          (t ^ n) * ∫ x in S, divergence φ.toFun (t • x) := by
        rw [h] <;> field_simp [ht_ne] <;> ring
      exact h'
    have h2 : ∫ x in S, divergence ψ.toFun x = ∫ x in S, t * divergence φ.toFun (t • x) := by
      rw [hdiv] <;> rfl
    have h_eq : ∫ x in scaleSet t S, divergence φ.toFun x =
        (t ^ (n - 1)) * (∫ x in S, divergence ψ.toFun x) := by
      rw [h_change, h2, integral_const_mul, h_pow] <;> ring
    rw [h_eq]
    have h_abs : |t ^ (n - 1) * ∫ x in S, divergence ψ.toFun x| =
        t ^ (n - 1) * |∫ x in S, divergence ψ.toFun x| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h3 : ENNReal.ofReal |t ^ (n - 1) * ∫ x in S, divergence ψ.toFun x| =
        ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence ψ.toFun x| := by
      rw [h_abs, ← ENNReal.ofReal_mul (by positivity)] <;> simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left
      (le_iSup (fun (θ : TestVectorField) => ENNReal.ofReal |∫ x in S, divergence θ.toFun x|) ψ)
      (by positivity)
  have h2 : (ENNReal.ofReal (t ^ (n - 1))) * perimeter S ≤ perimeter (scaleSet t S) := by
    have h_iSup : (ENNReal.ofReal (t ^ (n - 1))) * perimeter S =
        iSup fun (ψ : TestVectorField) =>
          ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence ψ.toFun x| := by
      rw [perimeter, ENNReal.mul_iSup] <;> rfl
    rw [h_iSup]
    apply iSup_le
    intro ψ
    let φ : TestVectorField :=
      { toFun := fun x => ψ.toFun (t⁻¹ • x)
        smooth := ψ.smooth.comp (contDiff_id.const_smul t⁻¹)
        compact := h_compact_unscaled ψ
        bound := fun x => ψ.bound (t⁻¹ • x) }
    have hdiv : divergence φ.toFun = fun x => t⁻¹ * divergence ψ.toFun (t⁻¹ • x) :=
      divergence_comp_smul ψ.smooth (inv_ne_zero ht_ne)
    have h_change : ∫ x in scaleSet t S, divergence φ.toFun x =
        (t ^ n) * ∫ x in S, divergence φ.toFun (t • x) := by
      have h : ∫ x in S, divergence φ.toFun (t • x) =
          (t ^ n)⁻¹ * ∫ x in scaleSet t S, divergence φ.toFun x := by
        rw [MeasureTheory.Measure.setIntegral_comp_smul volume (divergence φ.toFun) S ht_ne]
        rw [hfinrank]
        have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
          rw [abs_of_nonneg] <;> positivity
        rw [h_abs] <;> rfl
      have h' : ∫ x in scaleSet t S, divergence φ.toFun x =
          (t ^ n) * ∫ x in S, divergence φ.toFun (t • x) := by
        rw [h] <;> field_simp [ht_ne] <;> ring
      exact h'
    have h3 : ∀ x, divergence φ.toFun (t • x) = t⁻¹ * divergence ψ.toFun x := by
      intro x
      have h4 : divergence φ.toFun (t • x) = t⁻¹ * divergence ψ.toFun (t⁻¹ • (t • x)) := by
        rw [hdiv] <;> rfl
      rw [h4]
      have h5 : t⁻¹ • (t • x) = x := by
        simp [smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      rw [h5]
    have h4int : ∫ x in S, divergence φ.toFun (t • x) = t⁻¹ * ∫ x in S, divergence ψ.toFun x := by
      have h41 : ∀ x, divergence φ.toFun (t • x) = t⁻¹ * divergence ψ.toFun x := h3
      have h : ∫ x in S, divergence φ.toFun (t • x) = ∫ x in S, t⁻¹ * divergence ψ.toFun x := by
        apply integral_congr_ae
        exact ae_of_all _ h41
      rw [h, integral_const_mul]
    have h_eq : ∫ x in scaleSet t S, divergence φ.toFun x =
        (t ^ (n - 1)) * (∫ x in S, divergence ψ.toFun x) := by
      rw [h_change, h4int]
      have h : t ^ n * (t⁻¹ * ∫ x in S, divergence ψ.toFun x) =
          (t ^ (n - 1)) * (∫ x in S, divergence ψ.toFun x) := by
        calc
          t ^ n * (t⁻¹ * ∫ x in S, divergence ψ.toFun x)
            = (t ^ n * t⁻¹) * ∫ x in S, divergence ψ.toFun x := by ring
          _ = (t * t ^ (n - 1)) * t⁻¹ * ∫ x in S, divergence ψ.toFun x := by rw [h_pow]
          _ = t ^ (n - 1) * (t * t⁻¹) * ∫ x in S, divergence ψ.toFun x := by ring
          _ = t ^ (n - 1) * ∫ x in S, divergence ψ.toFun x := by
            have h_t : t * t⁻¹ = 1 := by field_simp [ht_ne]
            rw [h_t] <;> ring
      exact h
    have h_abs2 : |(t ^ (n - 1)) * (∫ x in S, divergence ψ.toFun x)| =
        (t ^ (n - 1)) * |∫ x in S, divergence ψ.toFun x| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h5 : ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence ψ.toFun x| =
        ENNReal.ofReal |∫ x in scaleSet t S, divergence φ.toFun x| := by
      have h6 : ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence ψ.toFun x| =
          ENNReal.ofReal ((t ^ (n - 1)) * |∫ x in S, divergence ψ.toFun x|) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> simp
      rw [h6]
      have h7 : (t ^ (n - 1)) * |∫ x in S, divergence ψ.toFun x| =
          |(t ^ (n - 1)) * (∫ x in S, divergence ψ.toFun x)| := by
        rw [h_abs2]
      rw [h7]
      rw [h_eq]
    rw [h5]
    exact le_iSup (fun (θ : TestVectorField) =>
      ENNReal.ofReal |∫ x in scaleSet t S, divergence θ.toFun x|) φ
  exact le_antisymm h1 h2

end Geometry.Perimeter

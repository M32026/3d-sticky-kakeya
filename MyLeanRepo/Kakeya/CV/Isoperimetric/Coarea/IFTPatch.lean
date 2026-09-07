import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaPermutedDirection
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {m : ℕ} [Nonempty (Fin m)]

/-!
# IFT Patch Construction for Coarea Formula

Given a C¹ function `f` and a point `y₀` where `∂f/∂e_j ≠ 0`,
construct an `OpenPartialHomeomorph` patch of the form
`φ(y) = projDir j y + f y • e_j` with C¹ inverse on its target.
-/

/-- The map `F_j(y) = projDir j y + f y • e_j`. -/
noncomputable def patchMap (j : Fin (m + 1)) (f : E (m + 1) → ℝ) :
    E (m + 1) → E (m + 1) :=
  fun y => projDir j y + f y • EuclideanSpace.single j (1 : ℝ)

/-- Derivative of `patchMap j f` at `y`. -/
noncomputable def patchMapDeriv (j : Fin (m + 1)) (f : E (m + 1) → ℝ)
    (y : E (m + 1)) : E (m + 1) →L[ℝ] E (m + 1) :=
  (projDir j : E (m + 1) →L[ℝ] E (m + 1)) +
  (fderiv ℝ f y).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- The derivative of `patchMap j f` is injective when `∂f/∂e_j ≠ 0`. -/
lemma patchMapDeriv_injective
    (j : Fin (m + 1)) (f : E (m + 1) → ℝ) (y : E (m + 1))
    (h_reg : (fderiv ℝ f y) (EuclideanSpace.single j (1 : ℝ)) ≠ 0) :
    Function.Injective (patchMapDeriv j f y) := by
  let e_j := EuclideanSpace.single j (1 : ℝ)
  let g := fderiv ℝ f y
  let DF := patchMapDeriv j f y
  have h_proj : ∀ (v : E (m + 1)), projDir j v = v - (v j) • e_j := by
    intro v
    simp [projDir, coordJ] <;> rfl
  have hDF_eq : ∀ (v : E (m + 1)), DF v = v + (g v - v j) • e_j := by
    intro v
    have h1 : DF v = projDir j v + (g v) • e_j := by
      simp [DF, patchMapDeriv] <;> rfl
    rw [h1, h_proj v]
    have h2 : v - (v j) • e_j + (g v) • e_j = v + (g v - v j) • e_j := by
      simp [sub_smul, add_smul] <;> abel
    exact h2
  intro v w hvw
  set h := v - w with hh
  have hDF_h : DF h = 0 := by
    have h1 : DF v = DF w := hvw
    have h2 : DF h = DF v - DF w := DF.map_sub v w
    rw [h2, h1, sub_self]
  have h_eq : h + (g h - h j) • e_j = 0 := by
    have h_expand : DF h = h + (g h - h j) • e_j := hDF_eq h
    rw [h_expand] at hDF_h
    exact hDF_h
  have h_gh : g h = 0 := by
    have h4 : (h + (g h - h j) • e_j) j = 0 := by
      rw [h_eq] <;> simp
    have h5 : (h + (g h - h j) • e_j) j = g h := by
      simp [e_j, EuclideanSpace.single_apply] <;> ring
    rw [h5] at h4
    exact h4
  have h5 : h - (h j) • e_j = 0 := by
    rw [h_gh] at h_eq
    have h6 : h + (0 - h j) • e_j = 0 := h_eq
    have h7 : h + (0 - h j) • e_j = h - (h j) • e_j := by
      simp [sub_smul] <;> abel
    rw [h7] at h6
    exact h6
  have h6 : h = (h j) • e_j := by
    simpa [sub_eq_zero] using h5
  have h71 : g h = g ((h j) • e_j) := congr_arg g h6
  have h72 : g ((h j) • e_j) = (h j) * g e_j := by
    rw [g.map_smul] <;> rfl
  have h7 : g h = (h j) * g e_j := by
    rw [h71, h72]
  rw [h7] at h_gh
  have h8 : h j = 0 := by
    apply (mul_eq_zero.mp h_gh).resolve_right
    exact h_reg
  rw [h8] at h6
  have h9 : h = 0 := by simpa using h6
  have h10 : v - w = 0 := by simpa [hh] using h9
  exact sub_eq_zero.mp h10

/-- **IFT patch construction.**

Given `f` C¹ and `y₀` with `∂f/∂e_j ≠ 0`, there exists an open
neighborhood `V` of `y₀` and an `OpenPartialHomeomorph` `φ` such that:
- `φ(y) = projDir j y + f y • e_j` everywhere
- `V ⊆ φ.source`
- `φ.symm` is C¹ on `φ.target`
- `∂f/∂e_j ≠ 0` on `V` -/
lemma ift_patch_dir
    (f : E (m + 1) → ℝ) (hf : ContDiff ℝ 1 f)
    (j : Fin (m + 1)) (y₀ : E (m + 1))
    (h_reg : (fderiv ℝ f y₀) (EuclideanSpace.single j (1 : ℝ)) ≠ 0) :
    ∃ (φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)))
      (V : Set (E (m + 1))),
      y₀ ∈ V ∧ IsOpen V ∧
      V ⊆ φ.source ∧
      (φ : E (m + 1) → E (m + 1)) = patchMap j f ∧
      ContDiffOn ℝ 1 φ.symm φ.target ∧
      ∀ y ∈ V, (fderiv ℝ f y) (EuclideanSpace.single j (1 : ℝ)) ≠ 0 := by
  classical
  let e_j := EuclideanSpace.single j (1 : ℝ)
  let F := patchMap j f
  let DF y := patchMapDeriv j f y
  have hF_diff : ContDiff ℝ 1 F := by
    have h1 : ContDiff ℝ 1 (projDir j : E (m + 1) → E (m + 1)) :=
      (projDir j).contDiff
    have h2 : ContDiff ℝ 1 (fun y : E (m + 1) => f y • e_j) :=
      hf.smul_const e_j
    exact h1.add h2
  have hDF_y₀_inj : Function.Injective (DF y₀) :=
    patchMapDeriv_injective j f y₀ h_reg
  let le : E (m + 1) ≃ₗ[ℝ] E (m + 1) :=
    LinearEquiv.ofInjectiveEndo (DF y₀).toLinearMap hDF_y₀_inj
  let DF_equiv : E (m + 1) ≃L[ℝ] E (m + 1) :=
    le.toContinuousLinearEquiv
  have h_fderiv_eq : fderiv ℝ F y₀ = (DF_equiv : E (m + 1) →L[ℝ] E (m + 1)) := by
    have h_proj_fd : HasFDerivAt (projDir j) (projDir j : E (m + 1) →L[ℝ] E (m + 1)) y₀ :=
      (projDir j).hasFDerivAt
    have h_smul_fd : HasFDerivAt (fun y : E (m + 1) => f y • e_j)
        ((fderiv ℝ f y₀).smulRight e_j) y₀ := by
      have h_diff : Differentiable ℝ f := ContDiff.differentiable hf (by norm_num)
      have h_fd : HasFDerivAt f (fderiv ℝ f y₀) y₀ := h_diff.differentiableAt.hasFDerivAt
      exact HasFDerivAt.smul_const h_fd e_j
    have h1 : HasFDerivAt F (DF y₀) y₀ := h_proj_fd.add h_smul_fd
    have h2 : fderiv ℝ F y₀ = DF y₀ := h1.fderiv
    have h3 : (DF y₀ : E (m + 1) →L[ℝ] E (m + 1)) = (DF_equiv : E (m + 1) →L[ℝ] E (m + 1)) := by rfl
    rw [h2, h3]
  have h_strict1 : HasStrictFDerivAt F (fderiv ℝ F y₀) y₀ :=
    ContDiff.hasStrictFDerivAt hF_diff (by norm_num)
  have h_strict : HasStrictFDerivAt F (DF_equiv : E (m + 1) →L[ℝ] E (m + 1)) y₀ := by
    rw [h_fderiv_eq] at h_strict1
    exact h_strict1
  let φ₀ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)) :=
    h_strict.toOpenPartialHomeomorph F
  have hφ₀_coe : (φ₀ : E (m + 1) → E (m + 1)) = F :=
    h_strict.toOpenPartialHomeomorph_coe
  have h_y₀_in_source : y₀ ∈ φ₀.source :=
    h_strict.mem_toOpenPartialHomeomorph_source
  have h_cda_y₀ : ContDiffAt ℝ 1 F y₀ := hF_diff.contDiffAt
  have h_symm_cda_y₀ : ContDiffAt ℝ 1 φ₀.symm (φ₀ y₀) := by
    have h_point : φ₀.symm (φ₀ y₀) = y₀ := φ₀.left_inv h_y₀_in_source
    have h_fd : HasFDerivAt (φ₀ : E (m + 1) → E (m + 1)) (DF_equiv : E (m + 1) →L[ℝ] E (m + 1)) (φ₀.symm (φ₀ y₀)) := by
      rw [h_point]
      have h4 : (φ₀ : E (m + 1) → E (m + 1)) = F := hφ₀_coe
      rw [h4]
      exact h_strict.hasFDerivAt
    have h_cda : ContDiffAt ℝ 1 (φ₀ : E (m + 1) → E (m + 1)) (φ₀.symm (φ₀ y₀)) := by
      rw [h_point]
      have h4 : (φ₀ : E (m + 1) → E (m + 1)) = F := hφ₀_coe
      rw [h4]
      exact h_cda_y₀
    exact φ₀.contDiffAt_symm (h_strict.image_mem_toOpenPartialHomeomorph_target) h_fd h_cda
  let φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)) :=
    φ₀.restrContDiff ℝ 1 (by norm_num)
  have hφ_coe : (φ : E (m + 1) → E (m + 1)) = F := by
    have h : (φ : E (m + 1) → E (m + 1)) = (φ₀ : E (m + 1) → E (m + 1)) := by
      funext x
      simp [φ]
      <;> rfl
    rw [h, hφ₀_coe]
  have h_y₀_in_φ_source : y₀ ∈ φ.source := by
    simp [φ, h_y₀_in_source, h_cda_y₀, h_symm_cda_y₀]
    <;> tauto
  let W : Set (E (m + 1)) := {y | (fderiv ℝ f y) e_j ≠ 0}
  have hW_open : IsOpen W := by
    have h_cont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have h_eval : Continuous (fun (g : E (m + 1) →L[ℝ] ℝ) => g e_j) := by exact continuous_eval_const e_j
    have h_cont2 : Continuous (fun y => (fderiv ℝ f y) e_j) := h_eval.comp h_cont
    exact h_cont2.isOpen_preimage {0}ᶜ isOpen_compl_singleton
  have h_y₀_in_W : y₀ ∈ W := h_reg
  let V : Set (E (m + 1)) := φ.source ∩ W
  have hV_open : IsOpen V := φ.open_source.inter hW_open
  have h_y₀_in_V : y₀ ∈ V := ⟨h_y₀_in_φ_source, h_y₀_in_W⟩
  have hV_source : V ⊆ φ.source := by
    intro x hx; exact hx.1
  have hV_reg : ∀ y ∈ V, (fderiv ℝ f y) e_j ≠ 0 := by
    intro y hy
    exact hy.2
  have h_symm_diff : ContDiffOn ℝ 1 φ.symm φ.target := by
    have h1 : ContDiffOn ℝ 1 φ₀.symm φ.target := by
      exact OpenPartialHomeomorph.contDiffOn_restrContDiff_target ℝ φ₀
        (of_eq_true
          (Eq.trans
            (Eq.trans
              (congrArg Not (Eq.trans WithTop.one_eq_coe._simp_2 (Eq.trans ENat.top_ne_one._simp_1 (eq_false not_false))))
              not_false_eq_true)
            (eq_true True.intro)))
    have h_eq : ∀ y ∈ φ.target, φ.symm y = φ₀.symm y := by
      intro y _
      simp [φ]
      <;> rfl
    exact h1.congr h_eq
  exact ⟨φ, V, h_y₀_in_V, hV_open, hV_source, hφ_coe, h_symm_diff, hV_reg⟩

end Geometry

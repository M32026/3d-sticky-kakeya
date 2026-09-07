import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaSinglePatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.ImplicitDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {m : ℕ} [Nonempty (Fin m)]

/-!
# Local Coarea Patch Construction

Constructs an `OpenPartialHomeomorph` around a point where a partial
derivative is nonzero, using the inverse function theorem.
-/

/-- Construct a local coarea patch around `x0` where `∂_last u ≠ 0`. -/
lemma local_coarea_patch_last
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (x0 : E (m + 1))
    (h : (fderiv ℝ u x0) (eLast : E (m + 1)) ≠ 0) :
    ∃ (V : Set (E (m + 1)))
      (φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1))),
      IsOpen V ∧ x0 ∈ V ∧
      ((φ : E (m + 1) → E (m + 1)) =
        fun y => projHCL y + u y • (eLast : E (m + 1))) ∧
      ContDiffOn ℝ 1 φ.symm φ.target ∧
      V ⊆ φ.source ∧
      ∀ y ∈ V, (fderiv ℝ u y) (eLast : E (m + 1)) ≠ 0 := by
  classical
  let Φ : E (m + 1) → E (m + 1) :=
    fun y => projHCL y + u y • (eLast : E (m + 1))
  let f' : E (m + 1) →L[ℝ] E (m + 1) :=
    coareaPhiFDeriv (fderiv ℝ u x0)
  have h_det : f'.det = (fderiv ℝ u x0) (eLast : E (m + 1)) :=
    det_coareaPhiFDeriv (fderiv ℝ u x0)
  have h_det_ne_zero : f'.det ≠ 0 := by
    rw [h_det]; exact h
  let f'_equiv : E (m + 1) ≃L[ℝ] E (m + 1) :=
    f'.toContinuousLinearEquivOfDetNeZero h_det_ne_zero
  have h_strict : HasStrictFDerivAt Φ (f'_equiv : E (m + 1) →L[ℝ] E (m + 1)) x0 := by
    have h1 : HasStrictFDerivAt Φ f' x0 := by
      have h_diff : Differentiable ℝ u := (contDiff_one_iff_fderiv.mp hu).1
      have h_cont : Continuous (fderiv ℝ u) := (contDiff_one_iff_fderiv.mp hu).2
      have h_der : ∀ᶠ w in nhds x0, HasFDerivAt u (fderiv ℝ u w) w := by
        filter_upwards with w
        exact h_diff.differentiableAt.hasFDerivAt
      have h_fderiv_strict : HasStrictFDerivAt u (fderiv ℝ u x0) x0 :=
        hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt h_der h_cont.continuousAt
      have h_a : HasStrictFDerivAt (fun y => projHCL y) projHCL x0 :=
        projHCL.hasStrictFDerivAt
      have h_b : HasStrictFDerivAt (fun y : E (m + 1) => u y • (eLast : E (m + 1)))
          ((fderiv ℝ u x0).smulRight (eLast : E (m + 1))) x0 :=
        h_fderiv_strict.smul_const (eLast : E (m + 1))
      have h_sum : HasStrictFDerivAt Φ
          (projHCL + (scaleE.comp (fderiv ℝ u x0))) x0 := h_a.add h_b
      have h_eq : f' = projHCL + scaleE.comp (fderiv ℝ u x0) := by
        ext x; rfl
      rw [h_eq] at *
      exact h_sum
    exact h1
  let φ0 : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)) :=
    h_strict.toOpenPartialHomeomorph Φ
  have hφ0_coe : (φ0 : E (m + 1) → E (m + 1)) = Φ :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe h_strict
  have hx0_in_source : x0 ∈ φ0.source :=
    HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source h_strict
  have h_contDiffAt_Φ : ContDiffAt ℝ 1 Φ x0 := by
    have h1 : ContDiff ℝ 1 Φ := by
      have h_proj : ContDiff ℝ 1 (projHCL : E (m + 1) → E (m + 1)) := by fun_prop
      have h_smul : ContDiff ℝ 1 (fun y : E (m + 1) => u y • (eLast : E (m + 1))) :=
        hu.smul_const (eLast : E (m + 1))
      exact h_proj.add h_smul
    exact h1.contDiffAt
  have h_contDiffAt_symm : ContDiffAt ℝ 1 φ0.symm (Φ x0) := by
    have h2 : ContDiffAt ℝ 1 Φ x0 := h_contDiffAt_Φ
    have h3 : HasFDerivAt Φ (f'_equiv : E (m + 1) →L[ℝ] E (m + 1)) x0 :=
      h_strict.hasFDerivAt
    exact h2.to_localInverse h3 (by norm_num)
  let φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)) :=
    φ0.restrContDiff ℝ 1 (by norm_num)
  have hφ_coe : (φ : E (m + 1) → E (m + 1)) = Φ := by
    have h : (φ : E (m + 1) → E (m + 1)) = (φ0 : E (m + 1) → E (m + 1)) := by rfl
    rw [h, hφ0_coe]
  have hx0_in_φ_source : x0 ∈ φ.source := by
    have h_def : φ.source = φ0.source ∩
        {x | ContDiffAt ℝ 1 φ0 x ∧ ContDiffAt ℝ 1 φ0.symm (φ0 x)} := by rfl
    rw [h_def]
    exact ⟨hx0_in_source, h_contDiffAt_Φ, h_contDiffAt_symm⟩
  have h_source_open : IsOpen φ.source := φ.open_source
  have h_symm_diff : ContDiffOn ℝ 1 φ.symm φ.target := by
    have h : ContDiffOn ℝ 1 φ0.symm (φ0.restrContDiff ℝ 1 (by norm_num)).target :=
      OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := φ0) (hn := by norm_num)
    dsimp only [φ] at *
    exact h
  let g : E (m + 1) → ℝ := fun y => (fderiv ℝ u y) (eLast : E (m + 1))
  have hg_cont : Continuous g := by
    have h1 : Continuous (fderiv ℝ u) := (contDiff_one_iff_fderiv.mp hu).2
    have h2 : Continuous (fun L : (E (m + 1) →L[ℝ] ℝ) => L (eLast : E (m + 1))) := by exact continuous_eval_const eLast
    exact h2.comp h1
  have h_x0_nonzero : g x0 ≠ 0 := h
  have h_nhds : ∀ᶠ y in nhds x0, g y ≠ 0 :=
    hg_cont.continuousAt.eventually_ne h_x0_nonzero
  have h_exists_nhds : ∃ (U : Set (E (m + 1))), IsOpen U ∧ x0 ∈ U ∧
      U ⊆ φ.source ∧ ∀ y ∈ U, g y ≠ 0 := by
    have h1 : ∀ᶠ y in nhds x0, y ∈ φ.source := h_source_open.mem_nhds hx0_in_φ_source
    have h2 : ∀ᶠ y in nhds x0, y ∈ φ.source ∧ g y ≠ 0 := h1.and h_nhds
    rcases (_root_.mem_nhds_iff.mp h2) with ⟨U, hU_sub, hU_open, hx0_U⟩
    refine ⟨U, hU_open, hx0_U, fun y hy => (hU_sub hy).1, fun y hy => (hU_sub hy).2⟩
  rcases h_exists_nhds with ⟨V, hV_open, hx0_V, hV_sub, hV_nonzero⟩
  exact ⟨V, φ, hV_open, hx0_V, hφ_coe, h_symm_diff, hV_sub, hV_nonzero⟩

end Geometry

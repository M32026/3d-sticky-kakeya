module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Determinant
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open scoped ContDiff

/-- Local straightening lemma - derivative invertible: Given `h : E → ℝ` smooth with
`fderiv ℝ h x ≠ 0`, there exists a coordinate `i` such that the map
`φ(y) j := if j = i then h(y) else y j` has bijective derivative at `x`. -/
lemma local_straightening_fderiv_invertible {m : ℕ} (_h_pos : 0 < m)
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : ContDiff ℝ ∞ h) (x : EuclideanSpace ℝ (Fin m))
    (hx : fderiv ℝ h x ≠ 0) :
    ∃ (i : Fin m),
      Function.Bijective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) =>
        (EuclideanSpace.equiv (Fin m) ℝ).symm
          (fun j : Fin m => if j = i then h y else y j)) x) := by
  let e : (EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  have h1 : ∃ (i : Fin m), (fderiv ℝ h x) (e.symm (Pi.single i 1)) ≠ 0 := by
    by_contra h2
    push Not at h2
    have h3 : ∀ (i : Fin m), (fderiv ℝ h x) (e.symm (Pi.single i 1)) = 0 := by simpa using h2
    have h4 : fderiv ℝ h x = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      have h_basis : e v = ∑ i : Fin m, (e v) i • (Pi.single i 1 : Fin m → ℝ) := by
        ext j
        simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
      have h5 : v = e.symm (e v) := by simp
      rw [h5]
      rw [h_basis]
      simp [map_sum, h3]
    exact hx h4
  rcases h1 with ⟨i, hi⟩
  let φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => e.symm (fun j : Fin m => if j = i then h y else y j)
  let ψ : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ) :=
    fun y => fun j : Fin m => if j = i then h y else y j
  have h_ψ_eq : ψ = e ∘ φ := by
    funext y
    simp [ψ, φ]
  let proj_j : Fin m → (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    fun j => (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).comp (e : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ))
  let fderiv_ψ : (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ)) :=
    ContinuousLinearMap.pi fun j : Fin m =>
      if j = i then fderiv ℝ h x else proj_j j
  have h_fderiv_ψ : HasFDerivAt ψ fderiv_ψ x := by
    have h2 : ∀ (j : Fin m), HasFDerivAt (fun y => ψ y j)
        ((if j = i then fderiv ℝ h x else proj_j j)) x := by
      intro j
      by_cases hj : j = i
      · subst hj
        have hdiff : Differentiable ℝ h := hh.differentiable (by simp)
        have hdiff_at : DifferentiableAt ℝ h x := hdiff.differentiableAt
        simpa [ψ, proj_j] using hdiff_at.hasFDerivAt
      · have h_eq1 : (fun y : EuclideanSpace ℝ (Fin m) => ψ y j) = proj_j j := by
          funext y
          simp [ψ, proj_j, hj]
          rfl
        rw [h_eq1]
        have h_if : (if j = i then fderiv ℝ h x else proj_j j) = proj_j j := by simp [hj]
        rw [h_if]
        exact (proj_j j).hasFDerivAt
    exact hasFDerivAt_pi.mpr h2
  let fderiv_φ : (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    (e.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp fderiv_ψ
  have h_fderiv_φ : HasFDerivAt φ fderiv_φ x := by
    have h_e_symm : HasFDerivAt (e.symm : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))
        (e.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) (ψ x) :=
      (e.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).hasFDerivAt
    exact h_e_symm.comp x h_fderiv_ψ
  have h_fderiv_eq : fderiv ℝ φ x = fderiv_φ := h_fderiv_φ.fderiv
  let fderiv_φ_lin : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (fderiv_φ : _)
  let v : Fin m → ℝ := fun k : Fin m => (fderiv ℝ h x) (e.symm (Pi.single k 1))
  let M_clm : ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) :=
    ContinuousLinearMap.pi fun j : Fin m =>
      if j = i then (fderiv ℝ h x).comp (e.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
      else ContinuousLinearMap.proj j
  let M : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := (M_clm : _)
  have h_conj1 : ∀ (z : Fin m → ℝ), e (fderiv_φ_lin (e.symm z)) = M z := by
    intro z
    ext j
    by_cases hj : j = i
    · subst hj
      simp [fderiv_φ_lin, fderiv_φ, fderiv_ψ, M, M_clm]
    · simp [hj, fderiv_φ_lin, fderiv_φ, fderiv_ψ, M, M_clm, proj_j]
  let e' : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] (Fin m → ℝ) := e
  let conj_map : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := e'.conj fderiv_φ_lin
  have h_eq : conj_map = M := by
    apply LinearMap.ext
    intro z
    exact h_conj1 z
  have h_conj : fderiv_φ_lin.det = M.det := by
    have h2 : fderiv_φ_lin.det = conj_map.det := by
      exact (LinearMap.det_conj fderiv_φ_lin e').symm
    rw [h2, h_eq]
  let M_mat : Matrix (Fin m) (Fin m) ℝ := (1 : Matrix (Fin m) (Fin m) ℝ).updateRow i v
  let b : Module.Basis (Fin m) ℝ (Fin m → ℝ) := Pi.basisFun ℝ (Fin m)
  have h_M_matrix : ∀ (j k : Fin m), M (Pi.single k 1 : Fin m → ℝ) j = M_mat j k := by
    intro j k
    by_cases h_j : j = i
    · subst h_j
      simp [M, M_clm, M_mat, v, Matrix.updateRow_apply]
    · simp [h_j, M, M_clm, M_mat, Matrix.updateRow_apply, Pi.single_apply]
      rfl
  have h_M_basis : ∀ (k : Fin m), M (Pi.single k 1 : Fin m → ℝ) = M_mat.mulVec (Pi.single k 1 : Fin m → ℝ) := by
    intro k
    ext j
    simpa [Matrix.mulVec] using h_M_matrix j k
  have h_M_lin : ∀ (w : Fin m → ℝ), M w = M_mat.mulVec w := by
    intro w
    have h_sum : w = ∑ k : Fin m, w k • (Pi.single k 1 : Fin m → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [h_sum]
    have h9 : M (∑ k : Fin m, w k • (Pi.single k 1 : Fin m → ℝ)) =
        ∑ k : Fin m, w k • M (Pi.single k 1 : Fin m → ℝ) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact M.map_smul (w k) (Pi.single k 1)
    rw [h9]
    have h10 : M_mat.mulVec (∑ k : Fin m, w k • (Pi.single k 1 : Fin m → ℝ)) =
        ∑ k : Fin m, w k • M_mat.mulVec (Pi.single k 1 : Fin m → ℝ) := by
      rw [Matrix.mulVec_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact Matrix.mulVec_smul M_mat (w k) (Pi.single k 1)
    rw [h10]
    apply Finset.sum_congr rfl
    intro k _
    rw [h_M_basis k]
  have h_M_eq : M = Matrix.toLin b b M_mat := by
    apply LinearMap.ext
    intro w
    exact h_M_lin w
  have h_det_val : M_mat.det = v i := det_updateRow_one_row i v
  have h_det_ne_zero : fderiv_φ_lin.det ≠ 0 := by
    rw [h_conj, h_M_eq, LinearMap.det_toLin b M_mat, h_det_val]
    exact hi
  have h_not : fderiv_φ_lin.ker = ⊥ := by
    have h_contra : fderiv_φ_lin.det = 0 ↔ fderiv_φ_lin.ker ≠ ⊥ :=
      LinearMap.det_eq_zero_iff_ker_ne_bot
    have h6 : ¬(fderiv_φ_lin.ker ≠ ⊥) := by tauto
    simpa using h6
  have h_inj : Function.Injective fderiv_φ_lin := LinearMap.ker_eq_bot.mp h_not
  have h_range : fderiv_φ_lin.range = ⊤ := by
    exact LinearMap.ker_eq_bot_iff_range_eq_top.mp h_not
  refine ⟨i, ?_⟩
  rw [h_fderiv_eq]
  exact ⟨h_inj, LinearMap.range_eq_top.mp h_range⟩


end ForMathlib.Analysis.Calculus.Sard

module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.LocalStraightening
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open scoped ContDiff

/-- Local straightening lemma returning an OpenPartialHomeomorph: Given `h : E → ℝ` smooth with
`fderiv ℝ h x ≠ 0`, there exists a coordinate `i`, a map `φ : E → E`, and an
`OpenPartialHomeomorph` `e_phi` such that:
1. `φ` is `ContDiff ℝ ∞`
2. `e_phi y = φ y` for all `y ∈ e_phi.source`
3. `(e_phi y) i = h y` for all `y ∈ e_phi.source`
4. `HasStrictFDerivAt φ f' x` for some `f' : E ≃L[ℝ] E` -/
lemma local_straightening_oph {m : ℕ} (h_pos : 0 < m) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : ContDiff ℝ ∞ h) (x : EuclideanSpace ℝ (Fin m)) (hx : fderiv ℝ h x ≠ 0) :
    ∃ (i : Fin m)
      (φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
      (e_phi : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))),
      x ∈ e_phi.source ∧
      ContDiff ℝ ∞ φ ∧
      (∀ y ∈ e_phi.source, e_phi y = φ y) ∧
      (∀ (y : EuclideanSpace ℝ (Fin m)), y ∈ e_phi.source → (e_phi y) i = h y) ∧
      (∃ (f' : (EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (EuclideanSpace ℝ (Fin m))),
        HasStrictFDerivAt φ (f' : (EuclideanSpace ℝ (Fin m)) →L[ℝ] (EuclideanSpace ℝ (Fin m))) x) := by
  rcases local_straightening_fderiv_invertible h_pos h hh x hx with ⟨i, h_bij⟩
  let φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => (EuclideanSpace.equiv (Fin m) ℝ).symm
      (fun j : Fin m => if j = i then h y else y j)
  have hφ_diff : ContDiff ℝ ∞ φ := by
    let e_equiv : (EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ
    have h1 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin m) => (fun j : Fin m => if j = i then h y else y j)) := by
      apply contDiff_pi.mpr
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hh
      · have h_j : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin m) => y j) := by
          exact (ContinuousLinearMap.proj j).contDiff.comp e_equiv.contDiff
        simpa [hj] using h_j
    have h2 : ContDiff ℝ ∞ (fun y => e_equiv (φ y)) := by
      have h_eq : (fun y : EuclideanSpace ℝ (Fin m) => e_equiv (φ y)) = (fun y : EuclideanSpace ℝ (Fin m) => (fun j : Fin m => if j = i then h y else y j)) := by
        funext y
        exact rfl
      rw [h_eq]
      exact h1
    exact (e_equiv.comp_contDiff_iff).mp h2
  let f' : (EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (EuclideanSpace ℝ (Fin m)) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ φ x) (LinearMap.ker_eq_bot.mpr h_bij.1) (LinearMap.range_eq_top.mpr h_bij.2)
  have h_strict : HasStrictFDerivAt φ (f' : (EuclideanSpace ℝ (Fin m)) →L[ℝ] (EuclideanSpace ℝ (Fin m))) x :=
    hφ_diff.hasStrictFDerivAt (by simp)
  let e_phi : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) :=
    h_strict.toOpenPartialHomeomorph φ
  have hx_in_source : x ∈ e_phi.source := h_strict.mem_toOpenPartialHomeomorph_source
  have h_phi_eq : ∀ y ∈ e_phi.source, e_phi y = φ y := by
    intro y _
    exact HasStrictFDerivAt.toOpenPartialHomeomorph_coe h_strict ▸ rfl
  have h1 : ∀ (y : EuclideanSpace ℝ (Fin m)), y ∈ e_phi.source → (e_phi y) i = h y := by
    intro y hy
    have h_eq1 : e_phi y = φ y := h_phi_eq y hy
    rw [h_eq1]
    simp [φ]
  refine' ⟨i, φ, e_phi, hx_in_source, hφ_diff, h_phi_eq, h1, ⟨f', h_strict⟩⟩


end ForMathlib.Analysis.Calculus.Sard

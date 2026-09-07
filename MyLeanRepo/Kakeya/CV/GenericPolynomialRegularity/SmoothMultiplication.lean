import MyLeanRepo.Kakeya.CV.PolynomialMollification
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Algebra.MvPolynomial.Degrees

noncomputable section

open MvPolynomial

namespace Kakeya.CV

/-- Degree bound for q^2 * r when deg(q) ≤ d and deg(r) ≤ k - 2d. -/
lemma square_mul_degree_bound {k d : ℕ} (h2d : 2 * d ≤ k)
    {q : MvPolynomial (Fin 3) ℝ} (hq : q.totalDegree ≤ d)
    {r : MvPolynomial (Fin 3) ℝ} (hr : r.totalDegree ≤ k - 2 * d) :
    (q ^ 2 * r).totalDegree ≤ k := by
  have h1 : (q ^ 2 * r).totalDegree ≤ (q ^ 2).totalDegree + r.totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have h2 : (q ^ 2).totalDegree ≤ 2 * q.totalDegree := MvPolynomial.totalDegree_pow q 2
  have h3 : (q ^ 2 * r).totalDegree ≤ 2 * q.totalDegree + r.totalDegree :=
    h1.trans (add_le_add h2 le_rfl)
  have h4 : 2 * q.totalDegree + r.totalDegree ≤ 2 * d + (k - 2 * d) :=
    add_le_add (mul_le_mul_of_nonneg_left hq (by norm_num)) hr
  have h5 : 2 * d + (k - 2 * d) = k := by omega
  rw [h5] at h4
  exact h3.trans h4

lemma factorizationMap_smooth {k d : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (h2d : 2 * d ≤ k)
    (eE : E ≃ₗ[ℝ] degreeLESubmodule d)
    (eF : F ≃ₗ[ℝ] degreeLESubmodule (k - 2 * d))
    (eG : G ≃ₗ[ℝ] degreeLESubmodule k) :
    ContDiff ℝ ⊤ (fun (p : E × F) =>
      eG.symm ⟨(eE p.1 : MvPolynomial (Fin 3) ℝ) * (eE p.1 : MvPolynomial (Fin 3) ℝ) * (eF p.2 : MvPolynomial (Fin 3) ℝ), by
        let q : MvPolynomial (Fin 3) ℝ := (eE p.1 : MvPolynomial (Fin 3) ℝ)
        let r : MvPolynomial (Fin 3) ℝ := (eF p.2 : MvPolynomial (Fin 3) ℝ)
        have hq : q.totalDegree ≤ d := (eE p.1).prop
        have hr : r.totalDegree ≤ k - 2 * d := (eF p.2).prop
        calc
          (q * q * r).totalDegree
            ≤ (q * q).totalDegree + r.totalDegree := totalDegree_mul _ _
          _ ≤ (q ^ 2).totalDegree + r.totalDegree := by rw [show q * q = q ^ 2 by ring]
          _ ≤ 2 * q.totalDegree + r.totalDegree := by gcongr; exact totalDegree_pow q 2
          _ ≤ 2 * d + (k - 2 * d) := by gcongr <;> omega
          _ = k := by omega⟩) := by
  -- Multiplication map: degreeLE d × degreeLE d → degreeLE (2*d)
  let mul1 : (degreeLESubmodule d) →ₗ[ℝ] (degreeLESubmodule d) →ₗ[ℝ] (degreeLESubmodule (2 * d)) :=
    { toFun := fun q =>
      { toFun := fun r => ⟨(q : MvPolynomial (Fin 3) ℝ) * (r : MvPolynomial (Fin 3) ℝ),
          (totalDegree_mul _ _).trans ((add_le_add q.prop r.prop).trans (by simp [two_mul]))⟩
        map_add' := by intro r1 r2; apply Subtype.ext; simp [mul_add]
        map_smul' := by intro c r; apply Subtype.ext; simp [smul_mul_assoc] }
      map_add' := by
        intro q1 q2
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        simp [add_mul]
      map_smul' := by
        intro c q
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        simp [smul_mul_assoc] }

  -- Multiplication map: degreeLE (2*d) × degreeLE (k-2*d) → degreeLE k
  let mul2 : (degreeLESubmodule (2 * d)) →ₗ[ℝ] (degreeLESubmodule (k - 2 * d)) →ₗ[ℝ] (degreeLESubmodule k) :=
    { toFun := fun q =>
      { toFun := fun r => ⟨(q : MvPolynomial (Fin 3) ℝ) * (r : MvPolynomial (Fin 3) ℝ),
          (totalDegree_mul _ _).trans ((add_le_add q.prop r.prop).trans (by omega))⟩
        map_add' := by intro r1 r2; apply Subtype.ext; simp [mul_add]
        map_smul' := by intro c r; apply Subtype.ext; simp [smul_mul_assoc] }
      map_add' := by
        intro q1 q2
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        simp [add_mul]
      map_smul' := by
        intro c q
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        simp [smul_mul_assoc] }

  -- The raw trilinear function
  let t_fun (x : E) (y : E) (z : F) : G :=
    eG.symm (mul2 (mul1 (eE x) (eE y)) (eF z))

  -- t_z(x,y) : F →ₗ G
  let t_z (x y : E) : F →ₗ[ℝ] G :=
    { toFun := fun z => t_fun x y z
      map_add' := by
        intro z1 z2
        dsimp only [t_fun]
        have h1 : eF (z1 + z2) = eF z1 + eF z2 := eF.map_add z1 z2
        rw [h1]
        have h2 : mul2 (mul1 (eE x) (eE y)) (eF z1 + eF z2) =
                 mul2 (mul1 (eE x) (eE y)) (eF z1) + mul2 (mul1 (eE x) (eE y)) (eF z2) :=
          (mul2 _).map_add' _ _
        rw [h2, eG.symm.map_add]
      map_smul' := by
        intro c z
        dsimp only [t_fun]
        have h1 : eF (c • z) = c • eF z := eF.map_smul c z
        rw [h1]
        have h2 : mul2 (mul1 (eE x) (eE y)) (c • eF z) =
                 c • mul2 (mul1 (eE x) (eE y)) (eF z) :=
          (mul2 _).map_smul' c _
        rw [h2, eG.symm.map_smul]
        <;> simp }

  -- Helper: t_z application unfolds to t_fun
  have h_t_z : ∀ (x y : E) (z : F), (t_z x y) z = t_fun x y z := by
    intro x y z
    rfl

  -- t_y(x) : E →ₗ (F →ₗ G)
  let t_y (x : E) : E →ₗ[ℝ] (F →ₗ[ℝ] G) :=
    { toFun := fun y => t_z x y
      map_add' := by
        intro y1 y2
        apply LinearMap.ext
        intro z
        have h : t_fun x (y1 + y2) z = t_fun x y1 z + t_fun x y2 z := by
          dsimp only [t_fun]
          have h1 : eE (y1 + y2) = eE y1 + eE y2 := eE.map_add y1 y2
          have h2 : mul1 (eE x) (eE (y1 + y2)) = mul1 (eE x) (eE y1) + mul1 (eE x) (eE y2) := by
            rw [h1]; exact (mul1 (eE x)).map_add' _ _
          have h3 : mul2 (mul1 (eE x) (eE (y1 + y2))) =
                   mul2 (mul1 (eE x) (eE y1)) + mul2 (mul1 (eE x) (eE y2)) := by
            rw [h2]; exact mul2.map_add' _ _
          have h4 : (mul2 (mul1 (eE x) (eE (y1 + y2)))) (eF z) =
                   (mul2 (mul1 (eE x) (eE y1))) (eF z) + (mul2 (mul1 (eE x) (eE y2))) (eF z) := by
            rw [h3] <;> rfl
          rw [h4, eG.symm.map_add]
        have h5 : (t_z x (y1 + y2)) z = (t_z x y1) z + (t_z x y2) z := by
          rw [h_t_z, h_t_z, h_t_z, h]
        simpa [add_apply] using h5
      map_smul' := by
        intro c y
        apply LinearMap.ext
        intro z
        have h : t_fun x (c • y) z = c • t_fun x y z := by
          dsimp only [t_fun]
          have h1 : eE (c • y) = c • eE y := eE.map_smul c y
          have h2 : mul1 (eE x) (eE (c • y)) = c • mul1 (eE x) (eE y) := by
            rw [h1]; exact (mul1 (eE x)).map_smul' c _
          have h3 : mul2 (mul1 (eE x) (eE (c • y))) = c • mul2 (mul1 (eE x) (eE y)) := by
            rw [h2]; exact mul2.map_smul' c _
          have h4 : (mul2 (mul1 (eE x) (eE (c • y)))) (eF z) =
                   c • (mul2 (mul1 (eE x) (eE y))) (eF z) := by
            rw [h3] <;> rfl
          rw [h4, eG.symm.map_smul]
        have h5 : (t_z x (c • y)) z = c • (t_z x y) z := by
          rw [h_t_z, h_t_z, h]
        simpa [smul_apply] using h5 }

  -- Helper: t_y application unfolds to t_fun
  have h_t_y : ∀ (x y : E) (z : F), (t_y x y) z = t_fun x y z := by
    intro x y z
    rfl

  -- t_x : E →ₗ (E →ₗ (F →ₗ G))
  let t_x : E →ₗ[ℝ] (E →ₗ[ℝ] (F →ₗ[ℝ] G)) :=
    { toFun := fun x => t_y x
      map_add' := by
        intro x1 x2
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        have h : t_fun (x1 + x2) y z = t_fun x1 y z + t_fun x2 y z := by
          dsimp only [t_fun]
          have h1 : eE (x1 + x2) = eE x1 + eE x2 := eE.map_add x1 x2
          have h2 : mul1 (eE (x1 + x2)) = mul1 (eE x1) + mul1 (eE x2) := by
            rw [h1]; exact mul1.map_add' _ _
          have h3 : (mul1 (eE (x1 + x2))) (eE y) = (mul1 (eE x1)) (eE y) + (mul1 (eE x2)) (eE y) := by
            rw [h2] <;> rfl
          have h4 : mul2 ((mul1 (eE (x1 + x2))) (eE y)) =
                   mul2 ((mul1 (eE x1)) (eE y)) + mul2 ((mul1 (eE x2)) (eE y)) := by
            rw [h3]; exact mul2.map_add' _ _
          have h5 : (mul2 ((mul1 (eE (x1 + x2))) (eE y))) (eF z) =
                   (mul2 ((mul1 (eE x1)) (eE y))) (eF z) + (mul2 ((mul1 (eE x2)) (eE y))) (eF z) := by
            rw [h4] <;> rfl
          rw [h5, eG.symm.map_add]
        have h6 : (t_y (x1 + x2) y) z = (t_y x1 y) z + (t_y x2 y) z := by
          rw [h_t_y, h_t_y, h_t_y, h]
        simpa [add_apply] using h6
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        have h : t_fun (c • x) y z = c • t_fun x y z := by
          dsimp only [t_fun]
          have h1 : eE (c • x) = c • eE x := eE.map_smul c x
          have h2 : mul1 (eE (c • x)) = c • mul1 (eE x) := by
            rw [h1]; exact mul1.map_smul' c _
          have h3 : (mul1 (eE (c • x))) (eE y) = c • (mul1 (eE x)) (eE y) := by
            rw [h2] <;> rfl
          have h4 : mul2 ((mul1 (eE (c • x))) (eE y)) = c • mul2 ((mul1 (eE x)) (eE y)) := by
            rw [h3]; exact mul2.map_smul' c _
          have h5 : (mul2 ((mul1 (eE (c • x))) (eE y))) (eF z) =
                   c • (mul2 ((mul1 (eE x)) (eE y))) (eF z) := by
            rw [h4] <;> rfl
          rw [h5, eG.symm.map_smul]
        have h6 : (t_y (c • x) y) z = c • (t_y x y) z := by
          rw [h_t_y, h_t_y, h]
        simpa [smul_apply] using h6 }

  -- Promote to continuous maps using finite-dimensionality
  let t_xc_lin : E →ₗ[ℝ] (E →L[ℝ] (F →L[ℝ] G)) :=
    { toFun := fun x => (t_y x).toContinuousBilinearMap
      map_add' := by
        intro x1 x2
        ext y z
        have h_eq : t_y (x1 + x2) = t_y x1 + t_y x2 := t_x.map_add' x1 x2
        simpa [LinearMap.toContinuousBilinearMap_apply, add_apply] using congr_arg (fun (f : E →ₗ[ℝ] (F →ₗ[ℝ] G)) => (f y) z) h_eq
      map_smul' := by
        intro c x
        ext y z
        have h_eq : t_y (c • x) = c • t_y x := t_x.map_smul' c x
        simpa [LinearMap.toContinuousBilinearMap_apply, smul_apply] using congr_arg (fun (f : E →ₗ[ℝ] (F →ₗ[ℝ] G)) => (f y) z) h_eq }
  let t_xc : E →L[ℝ] (E →L[ℝ] (F →L[ℝ] G)) :=
    t_xc_lin.toContinuousLinearMap

  -- Smoothness by composition using ContDiff.clm_apply
  have h_fst : ContDiff ℝ ⊤ (Prod.fst : E × F → E) := contDiff_fst
  have h_snd : ContDiff ℝ ⊤ (Prod.snd : E × F → F) := contDiff_snd

  letI : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
  letI : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (F →L[ℝ] G)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (F →L[ℝ] G)) := inferInstance
  have h_t_xc_diff : ContDiff ℝ ⊤ ⇑t_xc :=
    ContinuousLinearMap.contDiff t_xc
  have h_step1 : ContDiff ℝ ⊤ (fun p : E × F => t_xc (p.1 : E)) :=
    h_t_xc_diff.comp h_fst

  have h_step2 : ContDiff ℝ ⊤ (fun p : E × F => (t_xc (p.1 : E)) (p.1 : E)) :=
    ContDiff.clm_apply h_step1 h_fst

  have h_main : ContDiff ℝ ⊤ (fun p : E × F => (t_xc (p.1 : E) (p.1 : E)) (p.2 : F)) :=
    ContDiff.clm_apply h_step2 h_snd

  -- Show equality to desired expression
  have h4 : (fun (p : E × F) => (t_xc (p.1 : E) (p.1 : E)) (p.2 : F)) =
           (fun (p : E × F) => eG.symm (mul2 (mul1 (eE p.1) (eE p.1)) (eF p.2))) := by
    funext p
    have h5 : (t_xc (p.1 : E) (p.1 : E)) (p.2 : F) =
             eG.symm (mul2 (mul1 (eE p.1) (eE p.1)) (eF p.2)) := by
      simp [t_xc, t_xc_lin, LinearMap.toContinuousBilinearMap_apply, h_t_z, t_fun]
      <;> rfl
    exact h5
  have h_main2 : ContDiff ℝ ⊤ (fun (p : E × F) => eG.symm (mul2 (mul1 (eE p.1) (eE p.1)) (eF p.2))) := by
    rw [←h4]
    exact h_main
  convert h_main2
  rfl

end Kakeya.CV

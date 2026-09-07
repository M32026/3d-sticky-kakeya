import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaBasics
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Graph area: polynomial fderiv computations
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

-- ============================================================================
-- Chain rule infrastructure
-- ============================================================================

/-- Gradient as continuous linear functional. -/
def gradientCLM (p : MvPolynomial (Fin 3) ℝ) (x : R3) : R3 →L[ℝ] ℝ :=
  { toFun := fun w : R3 => inner ℝ (polynomialGradient p x) w
    map_add' := by intro u v; exact inner_add_right _ _ _
    map_smul' := by
      intro c u
      have h : inner ℝ (polynomialGradient p x) (c • u) = c * inner ℝ (polynomialGradient p x) u := by
        simpa [inner_smul_right] using rfl
      exact h }

/-- The fderiv CLM of the graph map. -/
def graphMapFderiv (f : R2 → ℝ) (y : R2) : R2 →L[ℝ] R3 :=
  { toFun := fun v : R2 =>
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![v 0, v 1, fderiv ℝ f y v]
    map_add' := by
      intro u v
      ext i
      fin_cases i <;> simp <;> abel
    map_smul' := by
      intro c u
      ext i
      fin_cases i <;> simp [smul_eq_mul] <;> ring }

/-- Projection onto coordinate n as a CLM. -/
def projCLM (n : Fin 3) : R3 →L[ℝ] ℝ :=
  { toFun := fun x : R3 => x n
    map_add' := by intro u v; rfl
    map_smul' := by intro c u; rfl }

lemma gradientCLM_apply (p : MvPolynomial (Fin 3) ℝ) (x : R3) (v : R3) :
    gradientCLM p x v = ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x * v i := by
  calc
    gradientCLM p x v
      = inner ℝ (polynomialGradient p x) v := by rfl
    _ = ∑ i : Fin 3, inner ℝ ((polynomialGradient p x) i) (v i) := PiLp.inner_apply _ _
    _ = ∑ i : Fin 3, v i * (polynomialGradient p x) i := by
        apply Finset.sum_congr rfl; intro i _; simp
    _ = ∑ i : Fin 3, (polynomialGradient p x) i * v i := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ = ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x * v i := by
        apply Finset.sum_congr rfl; intro i _; simp [polynomialGradient]

lemma polynomialValue_fderiv (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    HasFDerivAt (fun x : R3 => polynomialValue p x) (gradientCLM p x) x := by
  let P : MvPolynomial (Fin 3) ℝ → Prop := fun q =>
    ∀ (x : R3), HasFDerivAt (fun x => polynomialValue q x) (gradientCLM q x) x
  have hC : ∀ (a : ℝ), P (MvPolynomial.C a) := by
    intro a x
    have h1 : (fun y : R3 => polynomialValue (MvPolynomial.C a) y) = fun (_ : R3) => a := by
      funext y; simp [polynomialValue, MvPolynomial.eval_C]
    have h2 : gradientCLM (MvPolynomial.C a) x = (0 : R3 →L[ℝ] ℝ) := by
      ext v
      rw [gradientCLM_apply]
      simp [MvPolynomial.pderiv_C, polynomialValue, Finset.sum_const_zero]
    rw [h1, h2]
    exact hasFDerivAt_const a x
  have hAdd : ∀ (p q : MvPolynomial (Fin 3) ℝ), P p → P q → P (p + q) := by
    intro p q hp hq x
    have h1 : (fun y : R3 => polynomialValue (p + q) y) =
        fun y => polynomialValue p y + polynomialValue q y := by
      funext y; simp [polynomialValue, MvPolynomial.eval_add]
    have h2 : gradientCLM (p + q) x = gradientCLM p x + gradientCLM q x := by
      ext v
      simp only [ContinuousLinearMap.add_apply]
      rw [gradientCLM_apply (p + q), gradientCLM_apply p, gradientCLM_apply q]
      have h3 : ∀ i, MvPolynomial.pderiv i (p + q) =
          MvPolynomial.pderiv i p + MvPolynomial.pderiv i q := by
        intro i; exact (MvPolynomial.pderiv i).map_add p q
      have h4 : ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i (p + q)) x * v i =
          ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x +
            polynomialValue (MvPolynomial.pderiv i q) x) * v i := by
        apply Finset.sum_congr rfl
        intro i _
        have h41 : MvPolynomial.pderiv i (p + q) = MvPolynomial.pderiv i p + MvPolynomial.pderiv i q := h3 i
        rw [h41]
        have h42 : polynomialValue (MvPolynomial.pderiv i p + MvPolynomial.pderiv i q) x =
            polynomialValue (MvPolynomial.pderiv i p) x + polynomialValue (MvPolynomial.pderiv i q) x := by
          simp [polynomialValue, MvPolynomial.eval_add]
        rw [h42] <;> rfl
      rw [h4]
      have h5 : ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x +
              polynomialValue (MvPolynomial.pderiv i q) x) * v i =
          ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x * v i) +
          ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i q) x * v i) := by
        have h51 : ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x +
                polynomialValue (MvPolynomial.pderiv i q) x) * v i =
            ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x * v i +
                polynomialValue (MvPolynomial.pderiv i q) x * v i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [h51, Finset.sum_add_distrib]
      exact h5
    rw [h1, h2]
    exact (hp x).add (hq x)
  have hMulX : ∀ (p : MvPolynomial (Fin 3) ℝ) (n : Fin 3), P p → P (p * MvPolynomial.X n) := by
    intro p n hp x
    let f : R3 → ℝ := fun y => polynomialValue p y
    let f' : R3 →L[ℝ] ℝ := gradientCLM p x
    let g : R3 → ℝ := fun y => y n
    let g' : R3 →L[ℝ] ℝ := projCLM n
    have hf : HasFDerivAt f f' x := hp x
    have hg : HasFDerivAt g g' x := g'.hasFDerivAt
    have h_prod : HasFDerivAt (fun y => f y * g y) (f x • g' + g x • f') x :=
      hf.mul hg
    have h_eq1 : (fun y : R3 => f y * g y) = fun y => polynomialValue (p * MvPolynomial.X n) y := by
      funext y; simp [f, g, polynomialValue, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    have h_eq2 : f x • g' + g x • f' = gradientCLM (p * MvPolynomial.X n) x := by
      ext v
      have h_sum : gradientCLM (p * MvPolynomial.X n) x v =
          g x * f' v + f x * v n := by
        rw [gradientCLM_apply]
        have h4 : ∀ i : Fin 3, MvPolynomial.pderiv i (p * MvPolynomial.X n) =
            MvPolynomial.pderiv i p * MvPolynomial.X n + p * MvPolynomial.pderiv i (MvPolynomial.X n) := by
          intro i; exact MvPolynomial.pderiv_mul
        have h5 : ∀ i : Fin 3, polynomialValue (MvPolynomial.pderiv i (p * MvPolynomial.X n)) x =
            polynomialValue (MvPolynomial.pderiv i p) x * g x +
            f x * (if i = n then (1 : ℝ) else 0) := by
          intro i
          have h51 : MvPolynomial.pderiv i (p * MvPolynomial.X n) =
              MvPolynomial.pderiv i p * MvPolynomial.X n + p * MvPolynomial.pderiv i (MvPolynomial.X n) := h4 i
          rw [h51]
          have h52 : polynomialValue (MvPolynomial.pderiv i p * MvPolynomial.X n + p * MvPolynomial.pderiv i (MvPolynomial.X n)) x =
              polynomialValue (MvPolynomial.pderiv i p) x * g x +
              f x * polynomialValue (MvPolynomial.pderiv i (MvPolynomial.X n)) x := by
            simp [polynomialValue, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X, f, g]
            <;> ring
          rw [h52]
          have h53 : polynomialValue (MvPolynomial.pderiv i (MvPolynomial.X n)) x =
              if i = n then (1 : ℝ) else 0 := by
            by_cases h : i = n
            · have h1 : MvPolynomial.pderiv i (MvPolynomial.X n) = MvPolynomial.C (1 : ℝ) := by
                rw [h]; exact MvPolynomial.pderiv_X_self n
              rw [h1]
              have h_eval : polynomialValue (MvPolynomial.C (1 : ℝ)) x = (1 : ℝ) := by
                simp [polynomialValue, MvPolynomial.eval_C]
              rw [h_eval, if_pos h]
            · have h1 : MvPolynomial.pderiv i (MvPolynomial.X n) = (0 : MvPolynomial (Fin 3) ℝ) :=
                MvPolynomial.pderiv_X_of_ne (Ne.symm h)
              rw [h1]
              have h_eval : polynomialValue (0 : MvPolynomial (Fin 3) ℝ) x = (0 : ℝ) := by
                simp [polynomialValue]
              rw [h_eval, if_neg h]
          rw [h53] <;> rfl
        have h_sum1 : ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i (p * MvPolynomial.X n)) x * v i =
            ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x * g x +
                f x * (if i = n then (1 : ℝ) else 0)) * v i := by
          apply Finset.sum_congr rfl
          intro i _
          exact congr_arg (fun a : ℝ => a * v i) (h5 i)
        rw [h_sum1]
        have h6 : ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x * g x +
                f x * (if i = n then (1 : ℝ) else 0)) * v i =
            g x * f' v + f x * v n := by
          have h61 : ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x * g x +
                  f x * (if i = n then (1 : ℝ) else 0)) * v i =
              ∑ i : Fin 3, (polynomialValue (MvPolynomial.pderiv i p) x * g x * v i) +
              ∑ i : Fin 3, (f x * (if i = n then (1 : ℝ) else 0) * v i) := by
            have h : ∀ i, (polynomialValue (MvPolynomial.pderiv i p) x * g x +
                    f x * (if i = n then (1 : ℝ) else 0)) * v i =
                polynomialValue (MvPolynomial.pderiv i p) x * g x * v i +
                f x * (if i = n then (1 : ℝ) else 0) * v i := by
              intro i; ring
            rw [Finset.sum_congr rfl (fun i _ => h i)]
            rw [Finset.sum_add_distrib]
          rw [h61]
          have h7 : ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x * g x * v i = g x * f' v := by
            have h_comm : ∀ i, polynomialValue (MvPolynomial.pderiv i p) x * g x * v i =
                g x * (polynomialValue (MvPolynomial.pderiv i p) x * v i) := by
              intro i; ring
            have h71 : ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x * g x * v i =
                g x * ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x * v i := by
              rw [Finset.sum_congr rfl (fun i _ => h_comm i)]
              rw [Finset.mul_sum]
            rw [h71, ←gradientCLM_apply p x v] <;> rfl
          have h8 : ∑ i : Fin 3, f x * (if i = n then (1 : ℝ) else 0) * v i = f x * v n := by
            have h_comm : ∀ i, f x * (if i = n then (1 : ℝ) else 0) * v i =
                f x * ((if i = n then (1 : ℝ) else 0) * v i) := by
              intro i; ring
            have h81 : ∑ i : Fin 3, f x * (if i = n then (1 : ℝ) else 0) * v i =
                f x * ∑ i : Fin 3, (if i = n then (1 : ℝ) else 0) * v i := by
              rw [Finset.sum_congr rfl (fun i _ => h_comm i)]
              rw [Finset.mul_sum]
            rw [h81]
            have h82 : ∑ i : Fin 3, (if i = n then (1 : ℝ) else 0) * v i = v n := by
              simp [Finset.sum_ite_eq', Finset.mem_univ] <;> ring
            rw [h82] <;> ring
          rw [h7, h8] <;> ring
        exact h6
      have h_goal : (f x • g' + g x • f') v = g x * f' v + f x * v n := by
        simp [f', g', projCLM, f, g, ContinuousLinearMap.add_apply,
              ContinuousLinearMap.smul_apply] <;> ring
      rw [h_goal, h_sum]
    rw [h_eq1, h_eq2] at h_prod
    exact h_prod
  exact MvPolynomial.induction_on p hC hAdd hMulX x

lemma graphMap_fderiv (f : R2 → ℝ) (y : R2) (h_diff : DifferentiableAt ℝ f y) :
    HasFDerivAt (graphMap f) (graphMapFderiv f y) y := by
  let proj0 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 0, map_add' := by intro u v; rfl, map_smul' := by intro c u; rfl }
  let proj1 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 1, map_add' := by intro u v; rfl, map_smul' := by intro c u; rfl }
  have h1 : HasFDerivAt (fun x : R2 => x 0) proj0 y := proj0.hasFDerivAt
  have h2 : HasFDerivAt (fun x : R2 => x 1) proj1 y := proj1.hasFDerivAt
  have h3 : HasFDerivAt f (fderiv ℝ f y) y := h_diff.hasFDerivAt
  let e : (Fin 3 → ℝ) ≃L[ℝ] R3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm
  let F : R2 → (Fin 3 → ℝ) := fun x => ![x 0, x 1, f x]
  let φ' : Fin 3 → (R2 →L[ℝ] ℝ) := fun i =>
    if i = 0 then proj0 else if i = 1 then proj1 else fderiv ℝ f y
  let F' : R2 →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi φ'
  have hF : HasFDerivAt F F' y := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i <;> simp [F, φ', h1, h2, h3] <;> tauto
  have h_main : HasFDerivAt (e ∘ F) (e.toContinuousLinearMap.comp F') y :=
    e.toContinuousLinearMap.hasFDerivAt.comp y hF
  have h_eq1 : e ∘ F = graphMap f := by
    funext x
    simp [graphMap, F, e]
    <;> rfl
  have h_eq2 : e.toContinuousLinearMap.comp F' = graphMapFderiv f y := by
    ext v i
    fin_cases i <;> simp [graphMapFderiv, F', φ', e, ContinuousLinearMap.pi_apply] <;> rfl
  rw [h_eq1, h_eq2] at h_main
  exact h_main

-- ============================================================================
-- graphG and graphG' fderiv computations
-- ============================================================================

/-- The fderiv CLM of graphG. -/
def fderiv_graphG (f : R2 → ℝ) (y : R2) : R2 →L[ℝ] R2 :=
  { toFun := fun v : R2 =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![v 1, fderiv ℝ f y v]
    map_add' := by intro u v; ext i; fin_cases i <;> simp [map_add] <;> abel
    map_smul' := by intro c u; ext i; fin_cases i <;> simp [map_smul] <;> ring }

lemma hasFDerivAt_graphG {f : R2 → ℝ} {y : R2} (hf : DifferentiableAt ℝ f y) :
    HasFDerivAt (graphG f) (fderiv_graphG f y) y := by
  let proj1 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 1, map_add' := by intro u v; rfl, map_smul' := by intro c u; rfl }
  have h1 : HasFDerivAt (fun x : R2 => x 1) proj1 y := proj1.hasFDerivAt
  have h2 : HasFDerivAt f (fderiv ℝ f y) y := hf.hasFDerivAt
  let e : (Fin 2 → ℝ) ≃L[ℝ] R2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let F : R2 → (Fin 2 → ℝ) := fun x => ![x 1, f x]
  let φ' : Fin 2 → (R2 →L[ℝ] ℝ) := fun i =>
    if i = 0 then proj1 else fderiv ℝ f y
  let F' : R2 →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi φ'
  have hF : HasFDerivAt F F' y := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i <;> simp [F, φ', h1, h2] <;> tauto
  have h_main : HasFDerivAt (e ∘ F) (e.toContinuousLinearMap.comp F') y :=
    e.toContinuousLinearMap.hasFDerivAt.comp y hF
  have h_eq1 : e ∘ F = graphG f := by
    funext x
    simp [graphG, F, e] <;> rfl
  have h_eq2 : e.toContinuousLinearMap.comp F' = fderiv_graphG f y := by
    ext v i
    fin_cases i <;> simp [fderiv_graphG, F', φ', e, ContinuousLinearMap.pi_apply] <;> rfl
  rw [h_eq1, h_eq2] at h_main
  exact h_main

lemma det_fderiv_graphG (f : R2 → ℝ) (y : R2) :
    (fderiv_graphG f y).det = - (fderiv ℝ f y e02) := by
  let m : Matrix (Fin 2) (Fin 2) ℝ :=
    !![0, 1; fderiv ℝ f y e02, fderiv ℝ f y e12]
  have h_eq : (fderiv_graphG f y).toLinearMap = m.toLpLin 2 2 := by
    ext v i
    fin_cases i
    · simp [fderiv_graphG, m, Matrix.toLpLin_apply, Matrix.mulVec, Fin.sum_univ_two] <;> rfl
    · simp [fderiv_graphG, m, Matrix.toLpLin_apply, Matrix.mulVec, Fin.sum_univ_two]
      rw [fderiv_decomp f y v] <;> rfl
  have h_mdet : m.det = - (fderiv ℝ f y e02) := by
    rw [Matrix.det_fin_two_of 0 1 (fderiv ℝ f y e02) (fderiv ℝ f y e12)] <;> ring
  calc
    (fderiv_graphG f y).det
      = (m.toLpLin 2 2).det := by rw [←h_eq] <;> rfl
    _ = m.det := LinearMap.det_toLpLin 2 m
    _ = - (fderiv ℝ f y e02) := h_mdet

/-- The fderiv CLM of graphG'. -/
def fderiv_graphG' (f : R2 → ℝ) (y : R2) : R2 →L[ℝ] R2 :=
  { toFun := fun v : R2 =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![v 0, fderiv ℝ f y v]
    map_add' := by intro u v; ext i; fin_cases i <;> simp [map_add] <;> abel
    map_smul' := by intro c u; ext i; fin_cases i <;> simp [map_smul] <;> ring }

lemma hasFDerivAt_graphG' {f : R2 → ℝ} {y : R2} (hf : DifferentiableAt ℝ f y) :
    HasFDerivAt (graphG' f) (fderiv_graphG' f y) y := by
  let proj0 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 0, map_add' := by intro u v; rfl, map_smul' := by intro c u; rfl }
  have h1 : HasFDerivAt (fun x : R2 => x 0) proj0 y := proj0.hasFDerivAt
  have h2 : HasFDerivAt f (fderiv ℝ f y) y := hf.hasFDerivAt
  let e : (Fin 2 → ℝ) ≃L[ℝ] R2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let F : R2 → (Fin 2 → ℝ) := fun x => ![x 0, f x]
  let φ' : Fin 2 → (R2 →L[ℝ] ℝ) := fun i =>
    if i = 0 then proj0 else fderiv ℝ f y
  let F' : R2 →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi φ'
  have hF : HasFDerivAt F F' y := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i <;> simp [F, φ', h1, h2] <;> tauto
  have h_main : HasFDerivAt (e ∘ F) (e.toContinuousLinearMap.comp F') y :=
    e.toContinuousLinearMap.hasFDerivAt.comp y hF
  have h_eq1 : e ∘ F = graphG' f := by
    funext x
    simp [graphG', F, e] <;> rfl
  have h_eq2 : e.toContinuousLinearMap.comp F' = fderiv_graphG' f y := by
    ext v i
    fin_cases i <;> simp [fderiv_graphG', F', φ', e, ContinuousLinearMap.pi_apply] <;> rfl
  rw [h_eq1, h_eq2] at h_main
  exact h_main

lemma det_fderiv_graphG' (f : R2 → ℝ) (y : R2) :
    (fderiv_graphG' f y).det = fderiv ℝ f y e12 := by
  let m : Matrix (Fin 2) (Fin 2) ℝ :=
    !![1, 0; fderiv ℝ f y e02, fderiv ℝ f y e12]
  have h_eq : (fderiv_graphG' f y).toLinearMap = m.toLpLin 2 2 := by
    ext v i
    fin_cases i
    · simp [fderiv_graphG', m, Matrix.toLpLin_apply, Matrix.mulVec, Fin.sum_univ_two] <;> rfl
    · simp [fderiv_graphG', m, Matrix.toLpLin_apply, Matrix.mulVec, Fin.sum_univ_two]
      rw [fderiv_decomp f y v] <;> rfl
  have h_mdet : m.det = fderiv ℝ f y e12 := by
    rw [Matrix.det_fin_two_of 1 0 (fderiv ℝ f y e02) (fderiv ℝ f y e12)] <;> ring
  calc
    (fderiv_graphG' f y).det
      = (m.toLpLin 2 2).det := by rw [←h_eq] <;> rfl
    _ = m.det := LinearMap.det_toLpLin 2 m
    _ = fderiv ℝ f y e12 := h_mdet


end Kakeya.CV

import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.Basic
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.TubeProjectionArea
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Implicit function cover lemma (using ProdDomain API)

For a nonzero polynomial p in R³ and a unit direction e, the set
`S = {x : p(x) = 0, e · ∇p(x) ≠ 0}`
can be covered by countably many graph patches over e⊥.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.CV

variable (p : MvPolynomial (Fin 3) ℝ)

/-- `polynomialValue p` is analytic at every point. -/
lemma polynomial_analyticAt (x : Point 3) : AnalyticAt ℝ (polynomialValue p) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : AnalyticAt ℝ (fun (_ : Point 3) => a) x := analyticAt_const
    have h' : polynomialValue (MvPolynomial.C a) = (fun (_ : Point 3) => a) := by
      funext y; simp [polynomialValue]
    rw [h']
    exact h
  | add p q hp hq =>
    have h_p : AnalyticAt ℝ (fun y : Point 3 => polynomialValue p y) x := hp
    have h_q : AnalyticAt ℝ (fun y : Point 3 => polynomialValue q y) x := hq
    have h_add : AnalyticAt ℝ (fun y : Point 3 => polynomialValue p y + polynomialValue q y) x := h_p.add h_q
    have h_eq : polynomialValue (p + q) = (fun y : Point 3 => polynomialValue p y + polynomialValue q y) := by
      funext y; simp [polynomialValue, MvPolynomial.eval_add]
    have h_goal : AnalyticAt ℝ (polynomialValue (p + q)) x := by
      convert h_add using 1 <;> exact h_eq
    exact h_goal
  | mul_X p i hp =>
    let coordI : Point 3 →L[ℝ] ℝ :=
      { toFun := fun x => x i
        map_add' := by intro x y; simp
        map_smul' := by intro c x; simp }
    have hcoord : AnalyticAt ℝ (fun y : Point 3 => y i) x := coordI.analyticAt x
    have h_p : AnalyticAt ℝ (fun y : Point 3 => polynomialValue p y) x := hp
    have h_mul : AnalyticAt ℝ (fun y : Point 3 => polynomialValue p y * y i) x := h_p.mul hcoord
    have h_eq : polynomialValue (p * MvPolynomial.X i) = (fun y : Point 3 => polynomialValue p y * y i) := by
      funext y; simp [polynomialValue, MvPolynomial.eval_mul, MvPolynomial.eval_X] <;> ring
    have h_goal : AnalyticAt ℝ (polynomialValue (p * MvPolynomial.X i)) x := by
      convert h_mul using 1 <;> exact h_eq
    exact h_goal

/-- `polynomialValue p` is C^∞. -/
lemma polynomial_contDiff : ContDiff ℝ ⊤ (polynomialValue p) := by
  have h : ∀ (x : Point 3), AnalyticAt ℝ (polynomialValue p) x := polynomial_analyticAt p
  have h' : ContDiff ℝ ⊤ (polynomialValue p) := by
    exact contDiff_omega_iff_analyticOnNhd.mpr fun x _ => h x
  exact h'

/--
Gradient product rule: the directional derivative of `p * X i` in direction `e`.
-/
lemma gradient_mul_X_dir (i : Fin 3) (x e : Point 3) :
    inner ℝ e (polynomialGradient (p * MvPolynomial.X i) x) =
      (x i) * inner ℝ e (polynomialGradient p x) + (polynomialValue p x) * (e i) := by
  have h1 : ∀ (j : Fin 3), polynomialValue (MvPolynomial.pderiv j (p * MvPolynomial.X i)) x =
      (x i) * polynomialValue (MvPolynomial.pderiv j p) x +
        (if j = i then polynomialValue p x else 0) := by
    intro j
    have h2 : MvPolynomial.pderiv j (p * MvPolynomial.X i) =
        MvPolynomial.pderiv j p * MvPolynomial.X i + p * MvPolynomial.pderiv j (MvPolynomial.X i) := by
      rw [MvPolynomial.pderiv_mul] <;> ring
    rw [h2]
    by_cases hji : j = i
    · subst hji
      have h3 : MvPolynomial.pderiv j (MvPolynomial.X j : MvPolynomial (Fin 3) ℝ) = 1 := by simp
      rw [h3]
      simp [polynomialValue, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      <;> ring
    · have hne : i ≠ j := by
        intro h; exact hji h.symm
      have h3 : MvPolynomial.pderiv j (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ) = 0 :=
        MvPolynomial.pderiv_X_of_ne (h := hne)
      rw [h3]
      have h4 : MvPolynomial.pderiv j p * MvPolynomial.X i + p * (0 : MvPolynomial (Fin 3) ℝ) =
          MvPolynomial.pderiv j p * MvPolynomial.X i := by simp
      rw [h4]
      have hif : (if j = i then polynomialValue p x else 0) = 0 := by
        rw [if_neg hji]
      rw [hif]
      simp [polynomialValue, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      <;> ring
  have hsum : ∀ (q : MvPolynomial (Fin 3) ℝ),
      inner ℝ e (polynomialGradient q x) = ∑ j : Fin 3, e j * polynomialValue (MvPolynomial.pderiv j q) x := by
    intro q
    have h : inner ℝ e (polynomialGradient q x) = ∑ j : Fin 3, inner ℝ (e j) ((polynomialGradient q x) j) := by
      rw [PiLp.inner_apply]
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    simp [polynomialGradient]
    <;> ring
  rw [hsum (p * MvPolynomial.X i), hsum p]
  have h3 : ∑ j : Fin 3, e j * polynomialValue (MvPolynomial.pderiv j (p * MvPolynomial.X i)) x =
      ∑ j : Fin 3, e j * ((x i) * polynomialValue (MvPolynomial.pderiv j p) x +
        (if j = i then polynomialValue p x else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [h1 j]
  rw [h3]
  have h4 : ∑ j : Fin 3, e j * (x i * polynomialValue (MvPolynomial.pderiv j p) x + (if j = i then polynomialValue p x else 0)) =
      ∑ j : Fin 3, (e j * x i * polynomialValue (MvPolynomial.pderiv j p) x + e j * (if j = i then polynomialValue p x else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h4, Finset.sum_add_distrib]
  have h4 : ∑ j : Fin 3, e j * (if j = i then polynomialValue p x else 0) =
      (polynomialValue p x) * (e i) := by
    have h5 : ∑ j : Fin 3, e j * (if j = i then polynomialValue p x else 0) =
        ∑ j : Fin 3, (if j = i then e j * polynomialValue p x else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [h5]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin 3)) i]
    <;> simp [Finset.mem_univ] <;> ring
  have h5 : ∑ j : Fin 3, e j * x i * polynomialValue (MvPolynomial.pderiv j p) x =
      x i * ∑ j : Fin 3, e j * polynomialValue (MvPolynomial.pderiv j p) x := by
    have h51 : ∑ j : Fin 3, e j * x i * polynomialValue (MvPolynomial.pderiv j p) x =
        ∑ j : Fin 3, x i * (e j * polynomialValue (MvPolynomial.pderiv j p) x) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h51, Finset.mul_sum]
  rw [h4, h5] <;> ring

/--
Directional derivative of polynomial evaluation:
`d/dt|_{t=0} p(x + t·e) = e · ∇p(x)`.
-/
lemma polynomial_directional_deriv (x e : Point 3) :
    HasDerivAt (fun t : ℝ => polynomialValue p (x + t • e))
      (inner ℝ e (polynomialGradient p x)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hfunc : (fun t : ℝ => polynomialValue (MvPolynomial.C a) (x + t • e)) = fun (_ : ℝ) => a := by
      funext t; simp [polynomialValue]
    have hgrad0 : polynomialGradient (MvPolynomial.C a) x = 0 := by
      ext j
      simp [polynomialGradient]
      <;> rfl
    have hinner0 : inner ℝ e (polynomialGradient (MvPolynomial.C a) x) = 0 := by
      rw [hgrad0] <;> simp
    rw [hfunc, hinner0]
    exact hasDerivAt_const (0 : ℝ) a
  | add p q hp hq =>
    have h_p : HasDerivAt (fun t : ℝ => polynomialValue p (x + t • e)) (inner ℝ e (polynomialGradient p x)) 0 := hp
    have h_q : HasDerivAt (fun t : ℝ => polynomialValue q (x + t • e)) (inner ℝ e (polynomialGradient q x)) 0 := hq
    have h1 : (fun t : ℝ => polynomialValue (p + q) (x + t • e)) =
        fun t => polynomialValue p (x + t • e) + polynomialValue q (x + t • e) := by
      funext t; simp [polynomialValue, MvPolynomial.eval_add]
    have hgrad : polynomialGradient (p + q) x = polynomialGradient p x + polynomialGradient q x := by
      ext j
      have hpd : MvPolynomial.pderiv j (p + q) = MvPolynomial.pderiv j p + MvPolynomial.pderiv j q := by
        exact Derivation.map_add (MvPolynomial.pderiv j) p q
      have hval : polynomialValue (MvPolynomial.pderiv j (p + q)) x =
          polynomialValue (MvPolynomial.pderiv j p) x + polynomialValue (MvPolynomial.pderiv j q) x := by
        rw [hpd]
        simp [polynomialValue, MvPolynomial.eval_add] <;> ring
      simpa [polynomialGradient] using hval
    have h2 : inner ℝ e (polynomialGradient (p + q) x) =
        inner ℝ e (polynomialGradient p x) + inner ℝ e (polynomialGradient q x) := by
      rw [hgrad]
      rw [inner_add_right]
    rw [h1, h2]
    exact h_p.add h_q
  | mul_X p i hp =>
    have h1 : (fun t : ℝ => polynomialValue (p * MvPolynomial.X i) (x + t • e)) =
        fun t => polynomialValue p (x + t • e) * ((x + t • e) i) := by
      funext t
      simp [polynomialValue, MvPolynomial.eval_mul, MvPolynomial.eval_X] <;> ring
    have hg : HasDerivAt (fun t : ℝ => (x + t • e) i) (e i) 0 := by
      have h3 : (fun t : ℝ => (x + t • e) i) = fun t => x i + t * e i := by
        funext t; simp [Pi.add_apply, Pi.smul_apply] <;> ring
      rw [h3]
      have h4 : HasDerivAt (fun t : ℝ => t * e i) (e i) 0 := by
        have h5 : HasDerivAt (fun t : ℝ => e i * t) (e i) 0 := by
          have h6 := (hasDerivAt_id (0 : ℝ)).const_mul (e i)
          simpa using h6
        have h7 : (fun t : ℝ => e i * t) = (fun t : ℝ => t * e i) := by
          funext t; ring
        rw [h7] at h5
        exact h5
      have h4' : HasDerivAt (fun t : ℝ => x i + t * e i) (e i) 0 := by
        have h_eq : (fun t : ℝ => x i + t * e i) = fun t => t * e i + x i := by
          funext t; ring
        rw [h_eq]
        exact h4.add_const (x i)
      exact h4'
    have hres := hp.mul hg
    have hcomm : (inner ℝ e (polynomialGradient p x)) * (x i) =
        (x i) * (inner ℝ e (polynomialGradient p x)) := by ring
    have h4 : (inner ℝ e (polynomialGradient p x)) * (x i) + (polynomialValue p x) * (e i) =
        inner ℝ e (polynomialGradient (p * MvPolynomial.X i) x) := by
      rw [hcomm]
      exact (gradient_mul_X_dir p i x e).symm
    rw [h1]
    have h_simp : (inner ℝ e (polynomialGradient p x)) * ((x + (0 : ℝ) • e) i) +
        polynomialValue p (x + (0 : ℝ) • e) * (e i) =
        (inner ℝ e (polynomialGradient p x)) * (x i) + (polynomialValue p x) * (e i) := by
      have hz : x + (0 : ℝ) • e = x := by simp
      rw [hz] <;> rfl
    have h_final : (inner ℝ e (polynomialGradient p x)) * ((x + (0 : ℝ) • e) i) +
        polynomialValue p (x + (0 : ℝ) • e) * (e i) =
        inner ℝ e (polynomialGradient (p * MvPolynomial.X i) x) := by
      rw [h_simp, h4]
    exact h_final ▸ hres

/-- Orthogonal decomposition Point 3 ≅ Point 2 × ℝ via (proj2 x, x 2). -/
def equivProd2 : Point 3 ≃L[ℝ] Point 2 × ℝ :=
  let toFun : Point 3 → Point 2 × ℝ := fun x => (proj2 x, x 2)
  let invFun : Point 2 × ℝ → Point 3 := fun p =>
    (EuclideanSpace.equiv (Fin 3) ℝ).symm ![p.1 0, p.1 1, p.2]
  have h_left : ∀ x, invFun (toFun x) = x := by
    intro x
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    funext i
    fin_cases i <;> simp [toFun, invFun, proj2] <;> rfl
  have h_right : ∀ p, toFun (invFun p) = p := by
    intro p
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
      funext i
      fin_cases i <;> simp [toFun, invFun, proj2]
    · simp [toFun, invFun]
  have h_add : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    ext <;> simp [toFun, proj2] <;> rfl
  have h_smul : ∀ (c : ℝ) x, toFun (c • x) = c • toFun x := by
    intro c x
    ext <;> simp [toFun, proj2] <;> rfl
  have h_cont_to : Continuous toFun := by
    have h1 : Continuous proj2 := by
      unfold proj2
      apply Continuous.comp (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
      have hpi : ∀ (i : Fin 2), Continuous (fun x : Point 3 => x (Fin.castSucc i)) := by
        intro i
        exact PiLp.continuous_apply 2 (fun _ => ℝ) i.castSucc
      exact continuous_pi hpi
    have h2 : Continuous (fun x : Point 3 => x 2) :=
      PiLp.continuous_apply 2 (fun _ => ℝ) 2
    exact Continuous.prodMk h1 h2
  have h_cont_inv : Continuous invFun := by
    have h : Continuous (fun p : Point 2 × ℝ => ![p.1 0, p.1 1, p.2]) := by
      exact continuous_pi (fun i : Fin 3 => by fin_cases i <;> fun_prop)
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp h
  { toFun := toFun
    invFun := invFun
    left_inv := h_left
    right_inv := h_right
    map_add' := h_add
    map_smul' := h_smul
    continuous_toFun := h_cont_to
    continuous_invFun := h_cont_inv }

/-- General fact: partial derivative ∂/∂t of p∘Φ.symm at Φ z equals (∇p(z))₂. -/
lemma partial_deriv_grad2 (z : Point 3) :
    (fderiv ℝ (fun w : Point 2 × ℝ => polynomialValue p (equivProd2.symm w)) (equivProd2 z))
      (0, (1 : ℝ)) = (polynomialGradient p z) 2 := by
  let f : (Point 2 × ℝ) → ℝ := fun w => polynomialValue p (equivProd2.symm w)
  have hpoly_an : AnalyticAt ℝ (polynomialValue p) (equivProd2.symm (equivProd2 z)) :=
    polynomial_analyticAt p _
  have hpoly_diff : DifferentiableAt ℝ (polynomialValue p) (equivProd2.symm (equivProd2 z)) :=
    hpoly_an.differentiableAt
  have hsymm_diff : DifferentiableAt ℝ (equivProd2.symm) (equivProd2 z) :=
    ContinuousLinearEquiv.differentiableAt equivProd2.symm
  have h8 : DifferentiableAt ℝ f (equivProd2 z) :=
    hpoly_diff.comp (equivProd2 z) hsymm_diff
  have h_line : lineDeriv ℝ f (equivProd2 z) (0, (1 : ℝ)) =
      (fderiv ℝ f (equivProd2 z)) (0, (1 : ℝ)) := h8.lineDeriv_eq_fderiv
  rw [← h_line]
  have h_eq1 : (fun t : ℝ => f (equivProd2 z + t • (0, (1 : ℝ)))) =
      (fun t : ℝ => polynomialValue p (z + t • e3)) := by
    funext t
    have hlin : equivProd2.symm (equivProd2 z + t • (0, (1 : ℝ))) =
        equivProd2.symm (equivProd2 z) + t • equivProd2.symm (0, (1 : ℝ)) := by
      rw [equivProd2.symm.map_add, equivProd2.symm.map_smul]
    have h2 : equivProd2.symm (equivProd2 z) = z := equivProd2.left_inv z
    have h3 : equivProd2.symm (0, (1 : ℝ)) = e3 := by
      simp [equivProd2, proj2, e3] <;> ext i <;> fin_cases i <;> simp <;> rfl
    have h4 : equivProd2.symm (equivProd2 z + t • (0, (1 : ℝ))) = z + t • e3 := by
      calc
        equivProd2.symm (equivProd2 z + t • (0, (1 : ℝ)))
          = equivProd2.symm (equivProd2 z) + t • equivProd2.symm (0, (1 : ℝ)) := hlin
        _ = z + t • equivProd2.symm (0, (1 : ℝ)) := by rw [h2]
        _ = z + t • e3 := by rw [h3]
    dsimp only [f]
    rw [h4]
  have h_inner : inner ℝ e3 (polynomialGradient p z) = (polynomialGradient p z) 2 := by
    simp [e3, EuclideanSpace.inner_single_left] <;> ring
  have h_deriv : deriv (fun t : ℝ => f (equivProd2 z + t • (0, (1 : ℝ)))) 0 =
      (polynomialGradient p z) 2 := by
    have h1 : deriv (fun t : ℝ => polynomialValue p (z + t • e3)) 0 =
        inner ℝ e3 (polynomialGradient p z) :=
      (polynomial_directional_deriv p z e3).deriv
    rw [h_eq1, h1, h_inner]
  simpa [lineDeriv] using h_deriv

/-- Data for a single z-graph patch in the cover. -/
structure ZGraphPatchData (p : MvPolynomial (Fin 3) ℝ) where
  U : Set (Point 3)
  V : Set (Point 2)
  f : Point 2 → ℝ
  hU_open : IsOpen U
  hV_open : IsOpen V
  hf_diff : ContDiffOn ℝ 1 f V
  h_zero : zGraph V f ⊆ polynomialZeroSet p
  h_reg : ∀ z ∈ zGraph V f, (polynomialGradient p z) 2 ≠ 0
  h_cover : ({x ∈ polynomialZeroSet p | (polynomialGradient p x) 2 ≠ 0} ∩ U) ⊆ zGraph V f


/-- Local implicit function cover: each regular point has a z-graph patch neighborhood. -/
lemma local_zGraph_cover (p : MvPolynomial (Fin 3) ℝ)
    {x : Point 3} (hx : x ∈ polynomialZeroSet p ∧ (polynomialGradient p x) 2 ≠ 0) :
    ∃ (d : ZGraphPatchData p), x ∈ d.U := by
  let S : Set (Point 3) :=
    {x ∈ polynomialZeroSet p | (polynomialGradient p x) 2 ≠ 0}
  let Φ : Point 3 ≃L[ℝ] Point 2 × ℝ := equivProd2
  have hdiff : ContDiff ℝ ⊤ (polynomialValue p) := polynomial_contDiff p
  let u : Point 2 × ℝ := Φ x
  let f : (Point 2 × ℝ) → ℝ := fun z => polynomialValue p (Φ.symm z)
  have hf_contDiff : ContDiff ℝ ⊤ f :=
    hdiff.comp (Φ.symm).contDiff
  have hf_diff : ContDiffAt ℝ ⊤ f u := hf_contDiff.contDiffAt
  let c : ℝ := (polynomialGradient p x) 2
  have hc : c ≠ 0 := hx.2
  have h_fu : f u = 0 := by simpa [f, u, polynomialZeroSet] using hx.1
  have h7 : (fderiv ℝ f u) (0, (1 : ℝ)) = c := partial_deriv_grad2 p x
  let c_clm : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  have hpart : (fderiv ℝ f u) ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ = c_clm := by
    have h_eq : ∀ (t : ℝ), ((fderiv ℝ f u) ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ) t = c_clm t := by
      intro t
      have h_inr : ((fderiv ℝ f u) ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ) t =
          (fderiv ℝ f u) ((0 : Point 2), t) := by rfl
      have hsmul : (fderiv ℝ f u) ((0 : Point 2), t) = t * (fderiv ℝ f u) (0, (1 : ℝ)) := by
        have h6 : ((0 : Point 2), t) = t • (0, (1 : ℝ)) := by
          apply Prod.ext <;> simp <;> abel
        rw [h6]
        exact (fderiv ℝ f u).map_smul t (0, (1 : ℝ))
      rw [h_inr, hsmul, h7] <;> simp [c_clm] <;> ring
    exact ContinuousLinearMap.ext h_eq
  let c_equiv : ℝ ≃L[ℝ] ℝ :=
    { toFun := fun x : ℝ => c * x
      invFun := fun x : ℝ => c⁻¹ * x
      left_inv := fun x => by field_simp [hc] <;> ring
      right_inv := fun x => by field_simp [hc] <;> ring
      map_add' := by intro x y; ring
      map_smul' := by intro r x; simp <;> ring
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have h_clm_eq : c_clm = (c_equiv : ℝ →L[ℝ] ℝ) := by
    ext <;> simp [c_clm, c_equiv] <;> ring
  have hinv' : ((fderiv ℝ f u) ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ).IsInvertible := by
    rw [hpart, h_clm_eq]
    exact ContinuousLinearMap.isInvertible_equiv (f := c_equiv)
  let ψ : Point 2 → ℝ := hf_diff.implicitFunction (by simp) hinv'
  have hψ_diff : ContDiffAt ℝ ⊤ ψ u.1 :=
    hf_diff.contDiffAt_implicitFunction (by simp) hinv'
  have h_eventually : ∀ᶠ v in nhds u, f v = f u ↔ ψ v.1 = v.2 :=
    hf_diff.eventually_apply_eq_iff_implicitFunction (by simp) hinv'
  have hψ_at_u : ψ u.1 = u.2 :=
    hf_diff.implicitFunction_apply_self (by simp) hinv'
  rcases hψ_diff.contDiffOn (show (1 : WithTop ℕ∞) ≤ ⊤ from le_top) (by simp) with ⟨W, hW_nhds, hW_diff⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W_open, hW_sub, hW_open', hW_mem⟩
  have hW_open_diff : ContDiffOn ℝ 1 ψ W_open := hW_diff.mono hW_sub
  rcases h_eventually.exists_mem with ⟨N, hN_nhds, hN_prop⟩
  rcases mem_nhds_iff.mp hN_nhds with ⟨N_open, hN_sub, hN_open', hN_mem⟩
  have hN_open_prop : ∀ v ∈ N_open, f v = f u ↔ ψ v.1 = v.2 :=
    fun v hv => hN_prop v (hN_sub hv)
  let R' : Set (Point 2 × ℝ) :=
    {v | (fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ).IsInvertible}
  have h1 : Continuous (fderiv ℝ f) := hf_contDiff.continuous_fderiv (by simp)
  have h_fderiv_cont : Continuous (fun v : Point 2 × ℝ => (fderiv ℝ f v) (0, (1 : ℝ))) := by
    have h_eval : Continuous (fun (L : (Point 2 × ℝ) →L[ℝ] ℝ) => L (0, (1 : ℝ))) :=
      continuous_eval_const (0, (1 : ℝ))
    exact h_eval.comp h1
  have hR'_open : IsOpen R' := by
    have h1 : R' = {v | (fderiv ℝ f v) (0, (1 : ℝ)) ≠ 0} := by
      ext v
      simp only [R', Set.mem_setOf_eq]
      constructor
      · intro hinv
        by_contra h
        have h_eq : (fderiv ℝ f v) (0, (1 : ℝ)) = 0 := by simpa using h
        set L : ℝ →L[ℝ] ℝ := fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ with hL
        have hL1 : L 1 = (fderiv ℝ f v) (0, (1 : ℝ)) := by
          rw [hL]
          have h1 : (fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ) 1 =
              (fderiv ℝ f v) ((ContinuousLinearMap.inr ℝ (Point 2) ℝ) 1) := by rfl
          rw [h1]
          have h2 : (ContinuousLinearMap.inr ℝ (Point 2) ℝ) (1 : ℝ) = (0, (1 : ℝ)) := by rfl
          rw [h2]
        have hL1' : L 1 = 0 := by
          rw [hL1, h_eq]
        have h2 : L = 0 := by
          apply ContinuousLinearMap.ext
          intro t
          have h3 : L (t • (1 : ℝ)) = t • L 1 := L.map_smul t 1
          have h4 : L t = L (t • (1 : ℝ)) := by congr 1; simp [smul_eq_mul]
          rw [h4, h3, hL1'] <;> simp
        have h5 : L.IsInvertible := hinv
        rw [h2] at h5
        have h_subs : Subsingleton ℝ := by
          exact (ContinuousLinearMap.isInvertible_zero_iff (R := ℝ) (M := ℝ)).mp h5 |>.1
        have h_contra : (0 : ℝ) = (1 : ℝ) := Subsingleton.elim (0 : ℝ) (1 : ℝ)
        norm_num at h_contra
      · intro hne
        let c_equiv' : ℝ ≃L[ℝ] ℝ :=
          { toFun := fun x => (fderiv ℝ f v) (0, (1 : ℝ)) * x
            invFun := fun x => ((fderiv ℝ f v) (0, (1 : ℝ)))⁻¹ * x
            left_inv := fun x => by field_simp [hne] <;> ring
            right_inv := fun x => by field_simp [hne] <;> ring
            map_add' := by intro x y; ring
            map_smul' := by intro r x; simp <;> ring
            continuous_toFun := continuous_const.mul continuous_id
            continuous_invFun := continuous_const.mul continuous_id }
        have h_eq : (fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ) =
            (c_equiv' : ℝ →L[ℝ] ℝ) := by
          apply ContinuousLinearMap.ext
          intro z
          have h_inr : (fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ) z =
              (fderiv ℝ f v) ((0 : Point 2), z) := by rfl
          have hsmul : (fderiv ℝ f v) ((0 : Point 2), z) =
              z * (fderiv ℝ f v) (0, (1 : ℝ)) := by
            have h4 : ((0 : Point 2), z) = z • (0, (1 : ℝ)) := by
              apply Prod.ext <;> simp <;> abel
            rw [h4]
            exact (fderiv ℝ f v).map_smul z (0, (1 : ℝ))
          rw [h_inr, hsmul] <;> simp [c_equiv'] <;> ring
        rw [h_eq]
        exact ContinuousLinearMap.isInvertible_equiv (f := c_equiv')
    rw [h1]
    exact h_fderiv_cont.isOpen_preimage _ isOpen_compl_singleton
  have hR'_mem : u ∈ R' := by simpa [R'] using hinv'
  let g : Point 2 → Point 2 × ℝ := fun y => (y, ψ y)
  have hg_cont : ContinuousAt g u.1 := by fun_prop
  let N0 : Set (Point 2 × ℝ) := N_open ∩ R'
  have hN0_open : IsOpen N0 := hN_open'.inter hR'_open
  have hN0_mem : u ∈ N0 := ⟨hN_mem, hR'_mem⟩
  have hN0_nhds : N0 ∈ nhds u := hN0_open.mem_nhds hN0_mem
  have hg_u : g u.1 = u := by
    ext <;> simp [g, hψ_at_u] <;> rfl
  have hN0_nhds' : N0 ∈ nhds (g u.1) := by
    rw [hg_u] <;> exact hN0_nhds
  have hV_g_nhds : g ⁻¹' N0 ∈ nhds u.1 := hg_cont.preimage_mem_nhds hN0_nhds'
  rcases mem_nhds_iff.mp hV_g_nhds with ⟨V_g_open, hV_g_sub, hV_g_open', hV_g_mem⟩
  have hV_g_map : ∀ y ∈ V_g_open, g y ∈ N0 := fun y hy => hV_g_sub hy
  let V : Set (Point 2) := W_open ∩ V_g_open
  have hV_open : IsOpen V := hW_open'.inter hV_g_open'
  have hVu : u.1 ∈ V := ⟨hW_mem, hV_g_mem⟩
  have hV_sub : V ⊆ W_open := by
    intro y hy
    exact hy.1
  have hV_diff : ContDiffOn ℝ 1 ψ V := hW_open_diff.mono hV_sub
  have hV_N0 : ∀ y ∈ V, g y ∈ N0 := fun y hy => hV_g_map y hy.2
  let N' : Set (Point 2 × ℝ) := N0 ∩ (V ×ˢ Set.univ)
  have hN'_open : IsOpen N' := hN0_open.inter (hV_open.prod isOpen_univ)
  have hN'_mem : u ∈ N' := ⟨hN0_mem, ⟨hVu, trivial⟩⟩
  let U : Set (Point 3) := Φ.symm '' N'
  have hU_open : IsOpen U := Φ.symm.isOpenMap N' hN'_open
  have hxU : x ∈ U := ⟨u, hN'_mem, Φ.left_inv x⟩
  have h_zero_graph : zGraph V ψ ⊆ polynomialZeroSet p := by
    intro z hz
    have h5 : proj2 z ∈ V ∧ z 2 = ψ (proj2 z) := by simpa [zGraph] using hz
    have h6 : z = Φ.symm (g (proj2 z)) := by
      have h7 : Φ z = g (proj2 z) := by
        ext <;> simp [Φ, equivProd2, g, h5.2, proj2] <;> rfl
      have h10 : Φ.symm (Φ z) = z := Φ.left_inv z
      rw [h7] at h10
      exact h10.symm
    have h8 : g (proj2 z) ∈ N0 := hV_N0 (proj2 z) h5.1
    have h9 : f (g (proj2 z)) = f u := (hN_open_prop (g (proj2 z)) h8.1).mpr (by simp [g])
    have h10 : polynomialValue p z = 0 := by
      rw [h6]
      simpa [f, h_fu] using h9
    simpa [polynomialZeroSet] using h10
  have h_reg : ∀ z ∈ zGraph V ψ, (polynomialGradient p z) 2 ≠ 0 := by
    intro z hz
    have hz' : proj2 z ∈ V ∧ z 2 = ψ (proj2 z) := by simpa [zGraph] using hz
    have h5 : proj2 z ∈ V := hz'.1
    have h_eqz : Φ z = g (proj2 z) := by
      ext <;> simp [Φ, equivProd2, g, hz'.2, proj2] <;> rfl
    have h6 : z = Φ.symm (g (proj2 z)) := by
      have h10 : Φ.symm (Φ z) = z := Φ.left_inv z
      rw [h_eqz] at h10
      exact h10.symm
    have h8 : g (proj2 z) ∈ R' := (hV_N0 (proj2 z) h5).2
    have h9 : (fderiv ℝ f (g (proj2 z)) ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ).IsInvertible := h8
    have h10 : (fderiv ℝ f (g (proj2 z))) (0, (1 : ℝ)) ≠ 0 := by
      by_contra h
      have h_eq : (fderiv ℝ f (g (proj2 z))) (0, (1 : ℝ)) = 0 := by simpa using h
      set L : ℝ →L[ℝ] ℝ := fderiv ℝ f (g (proj2 z)) ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ with hL
      have hL1 : L 1 = (fderiv ℝ f (g (proj2 z))) (0, (1 : ℝ)) := by
        rw [hL]
        have h1 : (fderiv ℝ f (g (proj2 z)) ∘L ContinuousLinearMap.inr ℝ (Point 2) ℝ) 1 =
            (fderiv ℝ f (g (proj2 z))) ((ContinuousLinearMap.inr ℝ (Point 2) ℝ) 1) := by rfl
        rw [h1]
        have h2 : (ContinuousLinearMap.inr ℝ (Point 2) ℝ) (1 : ℝ) = (0, (1 : ℝ)) := by rfl
        rw [h2]
      have hL1' : L 1 = 0 := by
        rw [hL1, h_eq]
      have h11 : L = 0 := by
        apply ContinuousLinearMap.ext
        intro t
        have h3 : L (t • (1 : ℝ)) = t • L 1 := L.map_smul t 1
        have h4 : L t = L (t • (1 : ℝ)) := by congr 1; simp [smul_eq_mul]
        rw [h4, h3, hL1'] <;> simp
      have h10 : L.IsInvertible := h9
      rw [h11] at h10
      have h_subs : Subsingleton ℝ := by
        exact (ContinuousLinearMap.isInvertible_zero_iff (R := ℝ) (M := ℝ)).mp h10 |>.1
      have h_contra : (0 : ℝ) = (1 : ℝ) := Subsingleton.elim (0 : ℝ) (1 : ℝ)
      norm_num at h_contra
    have h11 : (fderiv ℝ f (g (proj2 z))) (0, (1 : ℝ)) =
        (polynomialGradient p z) 2 := by
      have h12 := partial_deriv_grad2 p z
      have h13 : equivProd2 z = g (proj2 z) := by simpa [Φ] using h_eqz
      rw [h13] at h12
      exact h12
    rw [h11] at h10
    exact h10
  have h_cover : (S ∩ U) ⊆ zGraph V ψ := by
    intro z hz
    have hzS : z ∈ S := hz.1
    have hzU : z ∈ U := hz.2
    rcases hzU with ⟨w, hwN', h_eq⟩
    have hwN : w ∈ N_open := hwN'.1.1
    have hwR' : w ∈ R' := hwN'.1.2
    have hwV : w.1 ∈ V := hwN'.2.1
    have hz0 : f w = 0 := by
      dsimp only [f]
      rw [h_eq]
      exact hzS.1
    have h1 : f w = f u ↔ ψ w.1 = w.2 := hN_open_prop w hwN
    have h2 : ψ w.1 = w.2 := h1.mp (by rw [hz0, h_fu])
    have hΦz : Φ z = w := by
      have h : Φ (Φ.symm w) = w := Φ.right_inv w
      rw [h_eq] at h
      exact h
    have hproj : proj2 z = w.1 := by
      have h : (Φ z).1 = w.1 := by rw [hΦz]
      simpa [Φ, equivProd2, proj2] using h
    have hz2 : z 2 = w.2 := by
      have h : (Φ z).2 = z 2 := by simp [Φ, equivProd2] <;> rfl
      rw [hΦz] at h
      exact h.symm
    have h3 : z ∈ zGraph V ψ := by
      simp only [zGraph, Set.mem_setOf_eq]
      constructor
      · rw [hproj] <;> exact hwV
      · rw [hz2, ←h2, hproj]
    exact h3
  exact ⟨⟨U, V, ψ, hU_open, hV_open, hV_diff, h_zero_graph, h_reg, h_cover⟩, hxU⟩


/-- **Implicit function cover adapted to z-graph patches.** -/
theorem regular_zero_set_zGraph_cover (p : MvPolynomial (Fin 3) ℝ) :
    ∃ (patches : ℕ → Set (Point 3)),
      (∀ i, ∃ (U : Set (Point 2)) (f : Point 2 → ℝ),
        IsOpen U ∧ ContDiffOn ℝ 1 f U ∧
        patches i = zGraph U f ∧
        patches i ⊆ polynomialZeroSet p ∧
        ∀ x ∈ patches i, (polynomialGradient p x) 2 ≠ 0) ∧
      {x ∈ polynomialZeroSet p | (polynomialGradient p x) 2 ≠ 0} ⊆ ⋃ i, patches i := by
  let S : Set (Point 3) :=
    {x ∈ polynomialZeroSet p | (polynomialGradient p x) 2 ≠ 0}
  have h_main : ∀ (x : Point 3), x ∈ S → ∃ (d : ZGraphPatchData p), x ∈ d.U := by
    intro x hx
    exact local_zGraph_cover p hx
  choose d hd using h_main
  let U' (x : {x // x ∈ S}) : Set (Point 3) := (d x.val x.property).U
  let patchSet (x : {x // x ∈ S}) : Set (Point 3) :=
    zGraph (d x.val x.property).V (d x.val x.property).f
  have hU'_open : ∀ (x : {x // x ∈ S}), IsOpen (U' x) :=
    fun x => (d x.val x.property).hU_open
  have h_coverS : S ⊆ ⋃ (i : {x // x ∈ S}), U' i := by
    intro z hz
    have h : z ∈ U' (⟨z, hz⟩ : {x // x ∈ S}) := hd z hz
    exact Set.mem_iUnion.mpr ⟨(⟨z, hz⟩ : {x // x ∈ S}), h⟩
  have hLindelof : IsLindelof S := HereditarilyLindelofSpace.isLindelof S
  have h_main2 : ∃ (r : Set {x // x ∈ S}), r.Countable ∧ S ⊆ ⋃ i ∈ r, U' i :=
    IsLindelof.elim_countable_subcover hLindelof U' hU'_open h_coverS
  rcases h_main2 with ⟨r, hr_count, hr_cover⟩
  by_cases hS : S = ∅
  · let dummyU : Set (Point 2) := ∅
    let dummyF : Point 2 → ℝ := fun _ => 0
    exact ⟨fun _ => zGraph dummyU dummyF,
      ⟨fun _ => ⟨dummyU, dummyF, isOpen_empty, (contDiffOn_empty : ContDiffOn ℝ 1 dummyF ∅), rfl, by simp [zGraph, dummyU], by simp [zGraph, dummyU]⟩,
      by simpa [S, hS] using Set.empty_subset _⟩⟩
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    have hr_nonempty : r.Nonempty := by
      by_contra h
      have h' : r = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [h'] at hr_cover
      have h_empty : (⋃ i ∈ (∅ : Set {x // x ∈ S}), U' i) = (∅ : Set (Point 3)) := by simp
      rw [h_empty] at hr_cover
      have hS_empty : S = ∅ := Set.subset_empty_iff.mp hr_cover
      exact hS hS_empty
    letI : Nonempty {x // x ∈ S} := ⟨hr_nonempty.some⟩
    have h_enum : ∃ (g : ℕ → {x // x ∈ S}), r = Set.range g :=
      hr_count.exists_eq_range hr_nonempty
    rcases h_enum with ⟨g, hg⟩
    refine' ⟨fun i => patchSet (g i), _⟩
    constructor
    · intro i
      let di := d (g i).val (g i).property
      exact ⟨di.V, di.f, di.hV_open, di.hf_diff, rfl, di.h_zero, di.h_reg⟩
    · intro x hx
      have h20 : x ∈ ⋃ i ∈ r, U' i := hr_cover hx
      have h20' : ∃ (y : {x // x ∈ S}), y ∈ r ∧ x ∈ U' y := by simpa using h20
      rcases h20' with ⟨y, hy_r, hxy⟩
      have h21 : y ∈ Set.range g := hg ▸ hy_r
      rcases h21 with ⟨i, rfl⟩
      have h22 : x ∈ U' (g i) := hxy
      have h23 : x ∈ S ∩ U' (g i) := ⟨hx, h22⟩
      have h24 : x ∈ patchSet (g i) :=
        (d (g i).val (g i).property).h_cover h23
      exact Set.mem_iUnion.mpr ⟨i, h24⟩

end Kakeya.CV

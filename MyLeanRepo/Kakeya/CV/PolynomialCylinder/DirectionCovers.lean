import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaBasics
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.ImplicitCover
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Compactness.Lindelof

/-!
# X and Y direction simultaneous graph-patch covers

Given a z-direction family cover, construct x- and y-direction covers by
coordinate permutation. Swapping coordinate `i` with `2` transforms
direction-`i` regularity into direction-`2` regularity, allowing application
of the z-cover to the renamed polynomial and pushing patches back.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

/-- A z-direction graph patch for a polynomial family. -/
structure FamilyZGraphPatch (k : ℕ) (P : PolynomialParameterization k) where
  V : Set (CoefficientSpace P.dim)
  A : Set (Point 2)
  g : CoefficientSpace P.dim → Point 2 → ℝ
  hV_open : IsOpen V
  hA_open : IsOpen A
  hg_smooth : ContDiffOn ℝ 1
    (fun p : (CoefficientSpace P.dim) × Point 2 => g p.1 p.2) (V ×ˢ A)
  h_zero : ∀ x ∈ V, ∀ y ∈ A,
    polynomialValue (parameterPolynomial P x) (graphMap (g x) y) = 0
  h_reg : ∀ x ∈ V, ∀ y ∈ A,
    (polynomialGradient (parameterPolynomial P x) (graphMap (g x) y)) 2 ≠ 0

/-- The function `(x, z) ↦ p_x(z)` is smooth. -/
lemma family_polynomialValue_contDiff :
    ContDiff ℝ ⊤ (fun p : (CoefficientSpace P.dim) × Point 3 =>
      polynomialValue (parameterPolynomial P p.1) p.2) := by
  let Coeff := CoefficientSpace P.dim
  let b : Module.Basis (Fin P.dim) ℝ Coeff :=
    PiLp.basisFun 2 ℝ (Fin P.dim)
  let polys : Fin P.dim → MvPolynomial (Fin 3) ℝ := fun i =>
    parameterPolynomial P (b i)
  have h_expand : ∀ (x : Coeff),
      parameterPolynomial P x = ∑ i : Fin P.dim, (b.repr x) i • polys i := by
    intro x
    have h1 : (∑ i : Fin P.dim, (b.repr x) i • b i) = x := b.sum_repr x
    have h2 : (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
        (∑ i : Fin P.dim, (b.repr x) i • b i) =
        ∑ i : Fin P.dim, (b.repr x) i •
          (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) := by
      rw [map_sum (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) ((b.repr x) i) (b i)
    have h3 : (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) x =
        ∑ i : Fin P.dim, (b.repr x) i •
          (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) := by
      calc
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) x =
            (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
              (∑ i : Fin P.dim, (b.repr x) i • b i) := by rw [h1]
        _ = ∑ i : Fin P.dim, (b.repr x) i •
              (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) := h2
    simpa [polys, parameterPolynomial] using
      congr_arg
        (fun p : degreeLESubmodule k => (p : MvPolynomial (Fin 3) ℝ)) h3
  have h_main_eq : ∀ (x : Coeff) (z : Point 3),
      polynomialValue (parameterPolynomial P x) z =
      ∑ i : Fin P.dim, (b.repr x) i * polynomialValue (polys i) z := by
    intro x z
    rw [h_expand x]
    have h_eval :
        polynomialValue (∑ i : Fin P.dim, (b.repr x) i • polys i) z =
          ∑ i : Fin P.dim, (b.repr x) i * polynomialValue (polys i) z := by
      have h9 : ∀ (q : MvPolynomial (Fin 3) ℝ),
          polynomialValue q z = MvPolynomial.eval z q := fun _ => rfl
      rw [h9, MvPolynomial.eval_sum]
      apply Finset.sum_congr rfl
      intro i _
      have h_smul : MvPolynomial.eval z ((b.repr x) i • polys i) =
          (b.repr x) i * MvPolynomial.eval z (polys i) := by
        simpa [smul_eq_mul] using
          map_smul (MvPolynomial.eval z) ((b.repr x) i) (polys i)
      rw [h_smul, ← h9 (polys i)]
    exact h_eval
  have h_final :
      (fun p : Coeff × Point 3 =>
        polynomialValue (parameterPolynomial P p.1) p.2) =
      fun p : Coeff × Point 3 =>
        ∑ i : Fin P.dim, (b.repr p.1) i * polynomialValue (polys i) p.2 := by
    funext p
    exact h_main_eq p.1 p.2
  rw [h_final]
  apply ContDiff.sum
  intro i _
  let coordLinear : Coeff →ₗ[ℝ] ℝ :=
    { toFun := fun x => (b.repr x) i
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  let coord : Coeff →L[ℝ] ℝ := coordLinear.toContinuousLinearMap
  have h1 : ContDiff ℝ ⊤ (fun p : Coeff × Point 3 => (b.repr p.1) i) :=
    coord.contDiff.comp contDiff_fst
  have h2 :
      ContDiff ℝ ⊤
        (fun p : Coeff × Point 3 => polynomialValue (polys i) p.2) :=
    (polynomial_contDiff (polys i)).comp contDiff_snd
  exact h1.mul h2

/-- The family evaluation after splitting off the last coordinate is smooth. -/
lemma family_f_contDiffAt (u : (CoefficientSpace P.dim × Point 2) × ℝ) :
    ContDiffAt ℝ ⊤ (fun w : (CoefficientSpace P.dim × Point 2) × ℝ =>
      polynomialValue (parameterPolynomial P w.1.1)
        (equivProd2.symm (w.1.2, w.2))) u := by
  let Coeff := CoefficientSpace P.dim
  let Φ : Point 3 ≃L[ℝ] Point 2 × ℝ := equivProd2
  let p1 : ((Coeff × Point 2) × ℝ) →L[ℝ] (Coeff × Point 2) :=
    ContinuousLinearMap.fst ℝ (Coeff × Point 2) ℝ
  let p2 : ((Coeff × Point 2) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (Coeff × Point 2) ℝ
  let p11 : (Coeff × Point 2) →L[ℝ] Coeff :=
    ContinuousLinearMap.fst ℝ Coeff (Point 2)
  let p12 : (Coeff × Point 2) →L[ℝ] (Point 2) :=
    ContinuousLinearMap.snd ℝ Coeff (Point 2)
  let h1 : ((Coeff × Point 2) × ℝ) →L[ℝ] Coeff := p11.comp p1
  let h21 : ((Coeff × Point 2) × ℝ) →L[ℝ] (Point 2) := p12.comp p1
  let h21x22 : ((Coeff × Point 2) × ℝ) →L[ℝ] ((Point 2) × ℝ) :=
    h21.prod p2
  let h2 : ((Coeff × Point 2) × ℝ) →L[ℝ] (Point 3) :=
    Φ.symm.toContinuousLinearMap.comp h21x22
  let h : ((Coeff × Point 2) × ℝ) →L[ℝ] (Coeff × Point 3) := h1.prod h2
  have heq : (fun w : (Coeff × Point 2) × ℝ =>
      polynomialValue (parameterPolynomial P w.1.1) (Φ.symm (w.1.2, w.2))) =
      (fun p : Coeff × Point 3 =>
        polynomialValue (parameterPolynomial P p.1) p.2) ∘ h := by
    funext w
    rfl
  rw [heq]
  exact family_polynomialValue_contDiff.contDiffAt.comp u h.contDiff.contDiffAt

/-- The partial derivative in the last coordinate is the third gradient component. -/
lemma family_partial_deriv_at
    (x : CoefficientSpace P.dim) (y : Point 2) (t : ℝ) :
    (fderiv ℝ (fun w : (CoefficientSpace P.dim × Point 2) × ℝ =>
      polynomialValue (parameterPolynomial P w.1.1)
        (equivProd2.symm (w.1.2, w.2))) ((x, y), t)) (0, (1 : ℝ)) =
    (polynomialGradient (parameterPolynomial P x)
      (equivProd2.symm (y, t))) 2 := by
  let Coeff := CoefficientSpace P.dim
  let Φ : Point 3 ≃L[ℝ] Point 2 × ℝ := equivProd2
  let f : (Coeff × Point 2) × ℝ → ℝ := fun w =>
    polynomialValue (parameterPolynomial P w.1.1) (Φ.symm (w.1.2, w.2))
  let z : Point 3 := Φ.symm (y, t)
  let q : Point 2 × ℝ → ℝ := fun w =>
    polynomialValue (parameterPolynomial P x) (Φ.symm w)
  have hf : DifferentiableAt ℝ f ((x, y), t) :=
    (family_f_contDiffAt ((x, y), t)).differentiableAt (by simp)
  have hq : DifferentiableAt ℝ q (y, t) :=
    (polynomial_analyticAt (p := parameterPolynomial P x) (Φ.symm (y, t)))
      |>.differentiableAt.comp (y, t) Φ.symm.differentiableAt
  have heq :
      (fun s : ℝ => f (((x, y), t) + s • (0, (1 : ℝ)))) =
        fun s : ℝ => q ((y, t) + s • (0, (1 : ℝ))) := by
    funext s
    simp [f, q]
  have hline :
      lineDeriv ℝ f ((x, y), t) (0, (1 : ℝ)) =
        lineDeriv ℝ q (y, t) (0, (1 : ℝ)) := by
    rw [lineDeriv, lineDeriv, heq]
  have hfinal :
      (fderiv ℝ f ((x, y), t)) (0, (1 : ℝ)) =
        (fderiv ℝ q (y, t)) (0, (1 : ℝ)) := by
    rw [← hf.lineDeriv_eq_fderiv, hline, hq.lineDeriv_eq_fderiv]
  have hΦz : Φ z = (y, t) := Φ.right_inv (y, t)
  have hgoal :
      (fderiv ℝ q (y, t)) (0, (1 : ℝ)) =
        (polynomialGradient (parameterPolynomial P x) z) 2 := by
    have h := partial_deriv_grad2 (parameterPolynomial P x) z
    rw [hΦz] at h
    exact h
  exact hfinal.trans hgoal

/-- A regular family zero has a simultaneous local z-graph patch. -/
lemma family_local_zGraph_cover
    (x0 : CoefficientSpace P.dim) (z0 : Point 3)
    (hx_zero : polynomialValue (parameterPolynomial P x0) z0 = 0)
    (hx_reg : (polynomialGradient (parameterPolynomial P x0) z0) 2 ≠ 0) :
    ∃ (patch : FamilyZGraphPatch k P)
        (O : Set ((CoefficientSpace P.dim) × Point 3)),
      IsOpen O ∧ (x0, z0) ∈ O ∧
      ∀ (x : CoefficientSpace P.dim) (z : Point 3),
        (x, z) ∈ O →
        polynomialValue (parameterPolynomial P x) z = 0 →
        (polynomialGradient (parameterPolynomial P x) z) 2 ≠ 0 →
        x ∈ patch.V ∧ ∃ y ∈ patch.A, z = graphMap (patch.g x) y := by
  let Coeff := CoefficientSpace P.dim
  let Φ : Point 3 ≃L[ℝ] Point 2 × ℝ := equivProd2
  let y0 : Point 2 := (Φ z0).1
  let t0 : ℝ := (Φ z0).2
  let u : (Coeff × Point 2) × ℝ := ((x0, y0), t0)
  let f : (Coeff × Point 2) × ℝ → ℝ := fun w =>
    polynomialValue (parameterPolynomial P w.1.1) (Φ.symm (w.1.2, w.2))
  have hf : ContDiffAt ℝ ⊤ f u := family_f_contDiffAt u
  have hf' : ContDiff ℝ ⊤ f :=
    contDiff_iff_contDiffAt.mpr fun v => family_f_contDiffAt v
  have hΦz : Φ.symm (y0, t0) = z0 := Φ.left_inv z0
  have hfu : f u = 0 := by
    simpa [f, u, y0, t0, hΦz] using hx_zero
  have hderiv : (fderiv ℝ f u) (0, (1 : ℝ)) =
      (polynomialGradient (parameterPolynomial P x0) z0) 2 := by
    have h := family_partial_deriv_at x0 y0 t0
    rw [hΦz] at h
    exact h
  let c : ℝ := (polynomialGradient (parameterPolynomial P x0) z0) 2
  have hc : c ≠ 0 := hx_reg
  have hpart :
      (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (Coeff × Point 2) ℝ) =
        c • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro t
    have hsmul : (fderiv ℝ f u) ((0 : Coeff × Point 2), t) =
        t * (fderiv ℝ f u) (0, (1 : ℝ)) := by
      have heq : ((0 : Coeff × Point 2), t) = t • (0, (1 : ℝ)) := by
        apply Prod.ext <;> simp
      rw [heq]
      exact (fderiv ℝ f u).map_smul t (0, (1 : ℝ))
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hsmul, hderiv]
    simp [smul_apply]
    ring
  let ce : ℝ ≃L[ℝ] ℝ :=
    { toFun := fun x => c * x
      invFun := fun x => c⁻¹ * x
      left_inv := fun x => by field_simp [hc]
      right_inv := fun x => by field_simp [hc]
      map_add' := by intro x y; ring
      map_smul' := by intro r x; simp; ring
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hinv :
      (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (Coeff × Point 2) ℝ).IsInvertible := by
    rw [hpart]
    exact ContinuousLinearMap.isInvertible_equiv (f := ce)
  let ψ : Coeff × Point 2 → ℝ := hf.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ⊤ ψ u.1 :=
    hf.contDiffAt_implicitFunction (by simp) hinv
  have hevent : ∀ᶠ v in nhds u, f v = f u ↔ ψ v.1 = v.2 :=
    hf.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  have hψu : ψ u.1 = u.2 := hf.implicitFunction_apply_self (by simp) hinv
  rcases hψ.contDiffOn (show (1 : WithTop ℕ∞) ≤ ⊤ from le_top) (by simp) with
    ⟨W, hW, hWdiff⟩
  rcases _root_.mem_nhds_iff.mp hW with
    ⟨Wopen, hWsub, hWopen, hWmem⟩
  have hWdiff' : ContDiffOn ℝ 1 ψ Wopen := hWdiff.mono hWsub
  rcases hevent.exists_mem with ⟨N, hN, hNprop⟩
  rcases _root_.mem_nhds_iff.mp hN with
    ⟨Nopen, hNsub, hNopen, hNmem⟩
  have hNprop' : ∀ v ∈ Nopen, f v = f u ↔ ψ v.1 = v.2 :=
    fun v hv => hNprop v (hNsub hv)
  let R : Set ((Coeff × Point 2) × ℝ) :=
    {v | (fderiv ℝ f v) (0, (1 : ℝ)) ≠ 0}
  have hfd : Continuous (fderiv ℝ f) := hf'.continuous_fderiv (by simp)
  have heval :
      Continuous (fun v : (Coeff × Point 2) × ℝ =>
        (fderiv ℝ f v) (0, (1 : ℝ))) := by
    have h :
        Continuous (fun (L : ((Coeff × Point 2) × ℝ) →L[ℝ] ℝ) =>
          L (0, (1 : ℝ))) := by fun_prop
    exact h.comp hfd
  have hRopen : IsOpen R :=
    heval.isOpen_preimage _ isOpen_compl_singleton
  have hRmem : u ∈ R := by simpa [R, hderiv, c] using hc
  let graph : Coeff × Point 2 → (Coeff × Point 2) × ℝ := fun p => (p, ψ p)
  have hgraph : ContinuousAt graph u.1 := by fun_prop
  let N0 : Set ((Coeff × Point 2) × ℝ) := Nopen ∩ R
  have hN0open : IsOpen N0 := hNopen.inter hRopen
  have hN0mem : u ∈ N0 := ⟨hNmem, hRmem⟩
  have hgraphu : graph u.1 = u := by ext <;> simp [graph, hψu]
  have hpre : graph ⁻¹' N0 ∈ nhds u.1 := by
    apply hgraph.preimage_mem_nhds
    rw [hgraphu]
    exact hN0open.mem_nhds hN0mem
  rcases _root_.mem_nhds_iff.mp hpre with
    ⟨Gopen, hGsub, hGopen, hGmem⟩
  let VA : Set (Coeff × Point 2) := Wopen ∩ Gopen
  have hVAopen : IsOpen VA := hWopen.inter hGopen
  have hVAmem : u.1 ∈ VA := ⟨hWmem, hGmem⟩
  rcases isOpen_prod_iff.mp hVAopen u.1.1 u.1.2 hVAmem with
    ⟨V, A, hVopen, hAopen, hVmem, hAmem, hsub⟩
  have hdiff : ContDiffOn ℝ 1 ψ (V ×ˢ A) :=
    hWdiff'.mono (hsub.trans inter_subset_left)
  have hN0 : ∀ p ∈ V ×ˢ A, graph p ∈ N0 :=
    fun p hp => hGsub (hsub hp).2
  let patch : FamilyZGraphPatch k P :=
    { V := V
      A := A
      g := fun x y => ψ (x, y)
      hV_open := hVopen
      hA_open := hAopen
      hg_smooth := hdiff
      h_zero := by
        intro x hx y hy
        have hp : (x, y) ∈ V ×ˢ A := ⟨hx, hy⟩
        have hpN := hN0 (x, y) hp
        have heq : f (graph (x, y)) = f u :=
          (hNprop' (graph (x, y)) hpN.1).mpr (by simp [graph])
        have hz : f (graph (x, y)) = 0 := by rw [heq, hfu]
        have hmap :
            Φ.symm (y, ψ (x, y)) = graphMap (fun y => ψ (x, y)) y := by
          simp [graphMap, Φ, equivProd2] <;>
            ext i <;> fin_cases i <;> simp <;> rfl
        simpa [f, graph, hmap] using hz
      h_reg := by
        intro x hx y hy
        have hp : (x, y) ∈ V ×ˢ A := ⟨hx, hy⟩
        have hne : (fderiv ℝ f (graph (x, y))) (0, (1 : ℝ)) ≠ 0 :=
          (hN0 (x, y) hp).2
        let z : Point 3 := graphMap (fun y => ψ (x, y)) y
        have heq :
            (fderiv ℝ f (graph (x, y))) (0, (1 : ℝ)) =
              (polynomialGradient (parameterPolynomial P x) z) 2 :=
          family_partial_deriv_at x y (ψ (x, y))
        rw [heq] at hne
        exact hne }
  let N1 : Set ((Coeff × Point 2) × ℝ) :=
    N0 ∩ ((V ×ˢ A) ×ˢ Set.univ)
  have hN1open : IsOpen N1 :=
    hN0open.inter ((hVopen.prod hAopen).prod isOpen_univ)
  have hN1mem : u ∈ N1 := ⟨hN0mem, ⟨⟨hVmem, hAmem⟩, trivial⟩⟩
  let homeo : (Coeff × Point 3) ≃ₜ ((Coeff × Point 2) × ℝ) :=
    { toFun := fun p => ((p.1, (Φ p.2).1), (Φ p.2).2)
      invFun := fun q => (q.1.1, Φ.symm (q.1.2, q.2))
      left_inv := by intro p; simp
      right_inv := by intro q; simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let O : Set (Coeff × Point 3) := homeo.symm '' N1
  have hOopen : IsOpen O := homeo.symm.isOpenMap N1 hN1open
  have hOmem : (x0, z0) ∈ O := by
    refine ⟨homeo (x0, z0), hN1mem, ?_⟩
    simp [homeo]
  refine ⟨patch, O, hOopen, hOmem, ?_⟩
  intro x z hzO hz hreg
  rcases hzO with ⟨w, hw, heq⟩
  have hwx : w.1.1 = x := by
    have h : (homeo.symm w).1 = w.1.1 := by simp [homeo]
    rw [heq] at h
    exact h.symm
  have hwz : Φ z = (w.1.2, w.2) := by
    have h : Φ (homeo.symm w).2 = (w.1.2, w.2) := by simp [homeo]
    rw [heq] at h
    exact h
  have hwN : w ∈ Nopen := hw.1.1
  have hwVA : w.1 ∈ V ×ˢ A := hw.2.1
  have hsymm : Φ.symm (w.1.2, w.2) = z := by
    rw [← hwz]
    exact Φ.left_inv z
  have hfw : f w = 0 := by simpa [f, hwx, hsymm] using hz
  have hψw : ψ w.1 = w.2 :=
    (hNprop' w hwN).mp (by rw [hfw, hfu])
  refine ⟨by rw [← hwx]; exact hwVA.1, w.1.2, hwVA.2, ?_⟩
  have hψx : ψ (x, w.1.2) = w.2 := by
    rw [← hwx]
    exact hψw
  have hΦ : Φ z = (w.1.2, ψ (x, w.1.2)) := by rw [hwz, hψx]
  have hz' : z = Φ.symm (w.1.2, ψ (x, w.1.2)) := by
    exact Φ.left_inv z ▸ congr_arg Φ.symm hΦ
  rw [hz']
  simp [patch, graphMap, Φ, equivProd2] <;>
    ext i <;> fin_cases i <;> simp <;> rfl

/-- Countable simultaneous cover of the z-regular family zero sets. -/
lemma exists_countable_zgraph_cover (P : PolynomialParameterization k) :
    ∃ patches : ℕ → FamilyZGraphPatch k P,
      ∀ (x : CoefficientSpace P.dim) (z : Point 3),
        polynomialValue (parameterPolynomial P x) z = 0 →
        (polynomialGradient (parameterPolynomial P x) z) 2 ≠ 0 →
        ∃ n, x ∈ (patches n).V ∧
          ∃ y ∈ (patches n).A, z = graphMap ((patches n).g x) y := by
  let Coeff := CoefficientSpace P.dim
  let R : Set (Coeff × Point 3) :=
    {p | polynomialValue (parameterPolynomial P p.1) p.2 = 0 ∧
      (polynomialGradient (parameterPolynomial P p.1) p.2) 2 ≠ 0}
  have hlocal : ∀ p : Coeff × Point 3, p ∈ R →
      ∃ (patch : FamilyZGraphPatch k P) (O : Set (Coeff × Point 3)),
        IsOpen O ∧ p ∈ O ∧
        ∀ (x : Coeff) (z : Point 3), (x, z) ∈ O →
          polynomialValue (parameterPolynomial P x) z = 0 →
          (polynomialGradient (parameterPolynomial P x) z) 2 ≠ 0 →
          x ∈ patch.V ∧ ∃ y ∈ patch.A, z = graphMap (patch.g x) y := by
    intro p hp
    exact family_local_zGraph_cover p.1 p.2 hp.1 hp.2
  choose patch O hOopen hOmem hcover using hlocal
  let U (p : R) : Set (Coeff × Point 3) := O p.val p.property
  have hUopen : ∀ p : R, IsOpen (U p) := fun p => hOopen p.val p.property
  have hUR : R ⊆ ⋃ p : R, U p := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hOmem z hz⟩
  have hL : IsLindelof R := HereditarilyLindelofSpace.isLindelof R
  rcases IsLindelof.elim_countable_subcover hL U hUopen hUR with
    ⟨r, hrc, hr⟩
  by_cases hR : R = ∅
  · let dummyV : Set Coeff := ∅
    let dummyA : Set (Point 2) := ∅
    let dummyG : Coeff → Point 2 → ℝ := fun _ _ => 0
    let dummy : FamilyZGraphPatch k P :=
      { V := dummyV
        A := dummyA
        g := dummyG
        hV_open := isOpen_empty
        hA_open := isOpen_empty
        hg_smooth := by simp [dummyV, dummyA]
        h_zero := by simp [dummyV]
        h_reg := by simp [dummyV] }
    refine ⟨fun _ => dummy, ?_⟩
    intro x z hz hreg
    have h : (x, z) ∈ R := ⟨hz, hreg⟩
    rw [hR] at h
    exact h.elim
  · have hrn : r.Nonempty := by
      by_contra h
      have h' : r = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [h'] at hr
      simp at hr <;> tauto
    rcases hrc.exists_eq_range hrn with ⟨e, he⟩
    let patches : ℕ → FamilyZGraphPatch k P :=
      fun n => patch (e n).val (e n).property
    refine ⟨patches, ?_⟩
    intro x z hz hreg
    have hp : (x, z) ∈ R := ⟨hz, hreg⟩
    rcases Set.mem_iUnion₂.mp (hr hp) with ⟨i, hir, hiU⟩
    have hi : i ∈ Set.range e := by rw [← he]; exact hir
    rcases hi with ⟨n, rfl⟩
    exact ⟨n, hcover (e n).val (e n).property x z hiU hz hreg⟩

/-- Permute the coordinates of `Point 3`, retaining the isometry structure. -/
def permuteCoordsIsometry
    (σ : Equiv.Perm (Fin 3)) : Point 3 ≃ₗᵢ[ℝ] Point 3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

/-- Swap two coordinates of `Point 3`, retaining the isometry structure. -/
def swapCoordsIsometry
    (i j : Fin 3) : Point 3 ≃ₗᵢ[ℝ] Point 3 :=
  permuteCoordsIsometry (Equiv.swap i j)

/-- Permute the coordinates of `Point 3`. -/
def permuteCoords (σ : Equiv.Perm (Fin 3)) : Point 3 ≃L[ℝ] Point 3 :=
  (permuteCoordsIsometry σ).toContinuousLinearEquiv

/-- Swap two coordinates of `Point 3`. -/
def swapCoords (i j : Fin 3) : Point 3 ≃L[ℝ] Point 3 :=
  permuteCoords (Equiv.swap i j)

@[simp]
lemma permuteCoordsIsometry_apply
    (σ : Equiv.Perm (Fin 3)) (z : Point 3) (i : Fin 3) :
    (permuteCoordsIsometry σ z) i = z (σ.symm i) := by
  simp [permuteCoordsIsometry,
    LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permuteCoords_apply
    (σ : Equiv.Perm (Fin 3)) (z : Point 3) (i : Fin 3) :
    (permuteCoords σ z) i = z (σ.symm i) := by
  exact permuteCoordsIsometry_apply σ z i

lemma permuteCoords_involutive
    {σ : Equiv.Perm (Fin 3)} (hσ : σ = σ.symm) :
    Function.Involutive (permuteCoords σ) := by
  intro z
  ext i
  have h1 : (permuteCoords σ (permuteCoords σ z)) i =
      (permuteCoords σ z) (σ.symm i) :=
    permuteCoords_apply σ (permuteCoords σ z) i
  rw [h1]
  have h2 : (permuteCoords σ z) (σ.symm i) =
      z (σ.symm (σ.symm i)) :=
    permuteCoords_apply σ z (σ.symm i)
  rw [h2]
  have h3 : σ.symm (σ.symm i) = i := by
    have hs : σ.symm = σ := hσ.symm
    have hright : σ (σ.symm i) = i := σ.apply_symm_apply i
    have heq : σ.symm (σ.symm i) = σ (σ.symm i) := by rw [hs]
    rw [heq]
    exact hright
  rw [h3]

lemma swapCoords_involutive (i j : Fin 3) :
    Function.Involutive (swapCoords i j) := by
  change Function.Involutive (permuteCoords (Equiv.swap i j))
  exact permuteCoords_involutive (by simp)

/-- Rename polynomial variables by a coordinate permutation. -/
def renamePoly (σ : Equiv.Perm (Fin 3))
    (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.rename σ p

lemma renamePoly_eval
    (σ : Equiv.Perm (Fin 3)) (p : MvPolynomial (Fin 3) ℝ) (z : Point 3) :
    polynomialValue (renamePoly σ p) z =
      polynomialValue p (permuteCoords σ.symm z) := by
  dsimp only [polynomialValue, renamePoly]
  have heq : z ∘ σ = permuteCoords σ.symm z := by
    funext i
    exact (permuteCoords_apply σ.symm z i).symm
  rw [MvPolynomial.eval_rename σ z p, heq]

lemma renamePoly_pderiv
    (σ : Equiv.Perm (Fin 3)) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    MvPolynomial.pderiv i (renamePoly σ p) =
      renamePoly σ (MvPolynomial.pderiv (σ.symm i) p) := by
  have h := MvPolynomial.pderiv_rename σ.injective (σ.symm i) p
  have hi : σ (σ.symm i) = i := by simp
  rw [hi] at h
  exact h

lemma renamePoly_gradient
    (σ : Equiv.Perm (Fin 3)) (p : MvPolynomial (Fin 3) ℝ) (z : Point 3) :
    polynomialGradient (renamePoly σ p) z =
      permuteCoords σ
        (polynomialGradient p (permuteCoords σ.symm z)) := by
  ext i
  have h1 : polynomialValue (MvPolynomial.pderiv i (renamePoly σ p)) z =
      polynomialValue (MvPolynomial.pderiv (σ.symm i) p)
        (permuteCoords σ.symm z) := by
    rw [renamePoly_pderiv]
    exact renamePoly_eval σ (MvPolynomial.pderiv (σ.symm i) p) z
  have h2 :
      (permuteCoords σ
        (polynomialGradient p (permuteCoords σ.symm z))) i =
      (polynomialGradient p (permuteCoords σ.symm z)) (σ.symm i) :=
    permuteCoords_apply σ _ i
  rw [h2]
  simpa [polynomialGradient] using h1

lemma renamePoly_totalDegree
    (σ : Equiv.Perm (Fin 3)) (p : MvPolynomial (Fin 3) ℝ) :
    (renamePoly σ p).totalDegree = p.totalDegree := by
  have h1 : (renamePoly σ p).totalDegree ≤ p.totalDegree :=
    MvPolynomial.totalDegree_rename_le σ p
  have h2 : p.totalDegree ≤ (renamePoly σ p).totalDegree := by
    have h3 :
        (renamePoly σ.symm (renamePoly σ p)).totalDegree ≤
          (renamePoly σ p).totalDegree :=
      MvPolynomial.totalDegree_rename_le σ.symm (renamePoly σ p)
    have h4 : renamePoly σ.symm (renamePoly σ p) = p := by
      simp [renamePoly, MvPolynomial.rename_rename]
    rw [h4] at h3
    exact h3
  exact le_antisymm h1 h2

/-- Linear equivalence of the bounded-degree polynomial space induced by
coordinate renaming. -/
def renameDegreeLEEquiv (σ : Equiv.Perm (Fin 3)) (k : ℕ) :
    degreeLESubmodule k ≃ₗ[ℝ] degreeLESubmodule k :=
  let e : MvPolynomial (Fin 3) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.renameEquiv ℝ σ
  let e' : MvPolynomial (Fin 3) ℝ ≃ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun c x => by
        simpa [Algebra.smul_def] using
          congr_arg (fun y => y * e x) (e.commutes c) }
  have hf : ∀ x : MvPolynomial (Fin 3) ℝ,
      x ∈ degreeLESubmodule k → e x ∈ degreeLESubmodule k := by
    intro x hx
    dsimp only [degreeLESubmodule, Submodule.mem_mk] at hx ⊢
    exact (renamePoly_totalDegree σ x).le.trans hx
  have hb : ∀ x : MvPolynomial (Fin 3) ℝ,
      x ∈ degreeLESubmodule k → e.symm x ∈ degreeLESubmodule k := by
    intro x hx
    dsimp only [degreeLESubmodule, Submodule.mem_mk] at hx ⊢
    exact (renamePoly_totalDegree σ.symm x).le.trans hx
  { toFun := fun p => ⟨e p, hf p p.property⟩
    invFun := fun p => ⟨e.symm p, hb p p.property⟩
    left_inv := by intro p; apply Subtype.ext; exact e.left_inv p
    right_inv := by intro p; apply Subtype.ext; exact e.right_inv p
    map_add' := by intro p q; apply Subtype.ext; exact e'.map_add' p q
    map_smul' := by intro c p; apply Subtype.ext; exact e'.map_smul' c p }

/-- Rename the output coordinates of a polynomial parameterization. -/
def renameParameterization (σ : Equiv.Perm (Fin 3))
    (P : PolynomialParameterization k) : PolynomialParameterization k :=
  { dim := P.dim
    equiv := P.equiv.trans (renameDegreeLEEquiv σ k) }

lemma parameterPolynomial_rename
    (σ : Equiv.Perm (Fin 3)) (P : PolynomialParameterization k)
    (x : CoefficientSpace P.dim) :
    parameterPolynomial (renameParameterization σ P) x =
      renamePoly σ (parameterPolynomial P x) := by
  rfl

/-- The x-graph point with base coordinates `(x₁, x₂)`. -/
def xGraphMap (g : Point 2 → ℝ) (y : Point 2) : Point 3 :=
  swapCoords 0 2 (graphMap g y)

/-- An x-direction graph patch for a polynomial family. -/
structure FamilyXGraphPatch (k : ℕ) (P : PolynomialParameterization k) where
  V : Set (CoefficientSpace P.dim)
  A : Set (Point 2)
  g : CoefficientSpace P.dim → Point 2 → ℝ
  hV_open : IsOpen V
  hA_open : IsOpen A
  hg_smooth : ContDiffOn ℝ 1
    (fun p : (CoefficientSpace P.dim) × Point 2 => g p.1 p.2) (V ×ˢ A)
  h_zero : ∀ x ∈ V, ∀ y ∈ A,
    polynomialValue (parameterPolynomial P x) (xGraphMap (g x) y) = 0
  h_reg : ∀ x ∈ V, ∀ y ∈ A,
    (polynomialGradient (parameterPolynomial P x) (xGraphMap (g x) y)) 0 ≠ 0

/-- Countable simultaneous cover of the x-regular family zero sets. -/
theorem exists_countable_xgraph_cover (P : PolynomialParameterization k) :
    ∃ patches : ℕ → FamilyXGraphPatch k P,
      ∀ (x : CoefficientSpace P.dim) (z : Point 3),
        polynomialValue (parameterPolynomial P x) z = 0 →
        (polynomialGradient (parameterPolynomial P x) z) 0 ≠ 0 →
        ∃ n, x ∈ (patches n).V ∧
          ∃ y ∈ (patches n).A, z = xGraphMap ((patches n).g x) y := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let P' := renameParameterization σ P
  let L := swapCoords 0 2
  have hσ : σ.symm = σ := by
    ext i
    fin_cases i <;> decide
  have hL : Function.Involutive L := swapCoords_involutive 0 2
  have hval : ∀ (x : CoefficientSpace P.dim) (z : Point 3),
      polynomialValue (parameterPolynomial P' x) z =
        polynomialValue (parameterPolynomial P x) (L z) := by
    intro x z
    rw [parameterPolynomial_rename σ P x, renamePoly_eval]
    rfl
  have hgrad : ∀ (x : CoefficientSpace P.dim) (z : Point 3),
      (polynomialGradient (parameterPolynomial P' x) z) 2 =
        (polynomialGradient (parameterPolynomial P x) (L z)) 0 := by
    intro x z
    rw [parameterPolynomial_rename σ P x, renamePoly_gradient, hσ]
    rfl
  rcases exists_countable_zgraph_cover P' with ⟨zpatches, hcover⟩
  let patches : ℕ → FamilyXGraphPatch k P := fun n =>
    { V := (zpatches n).V
      A := (zpatches n).A
      g := (zpatches n).g
      hV_open := (zpatches n).hV_open
      hA_open := (zpatches n).hA_open
      hg_smooth := (zpatches n).hg_smooth
      h_zero := by
        intro x hx y hy
        have hz := (zpatches n).h_zero x hx y hy
        have ht := hval x (graphMap ((zpatches n).g x) y)
        exact ht ▸ hz
      h_reg := by
        intro x hx y hy
        have hz := (zpatches n).h_reg x hx y hy
        have ht := hgrad x (graphMap ((zpatches n).g x) y)
        exact ht ▸ hz }
  refine ⟨patches, ?_⟩
  intro x z hz hreg
  have hz' : polynomialValue (parameterPolynomial P' x) (L z) = 0 := by
    rw [hval, hL z]
    exact hz
  have hreg' :
      (polynomialGradient (parameterPolynomial P' x) (L z)) 2 ≠ 0 := by
    rw [hgrad, hL z]
    exact hreg
  rcases hcover x (L z) hz' hreg' with ⟨n, hx, y, hy, heq⟩
  refine ⟨n, hx, y, hy, ?_⟩
  have h1 :
      L (xGraphMap ((zpatches n).g x) y) =
        graphMap ((zpatches n).g x) y := by
    have hdef :
        xGraphMap ((zpatches n).g x) y =
          L (graphMap ((zpatches n).g x) y) := by rfl
    rw [hdef, hL]
  have h2 : L (xGraphMap ((zpatches n).g x) y) = L z := by
    rw [h1, heq.symm]
  exact L.injective h2.symm

/-- The y-graph point with base coordinates `(x₀, x₂)`. -/
def yGraphMap (g : Point 2 → ℝ) (y : Point 2) : Point 3 :=
  swapCoords 1 2 (graphMap g y)

/-- A y-direction graph patch for a polynomial family. -/
structure FamilyYGraphPatch (k : ℕ) (P : PolynomialParameterization k) where
  V : Set (CoefficientSpace P.dim)
  A : Set (Point 2)
  g : CoefficientSpace P.dim → Point 2 → ℝ
  hV_open : IsOpen V
  hA_open : IsOpen A
  hg_smooth : ContDiffOn ℝ 1
    (fun p : (CoefficientSpace P.dim) × Point 2 => g p.1 p.2) (V ×ˢ A)
  h_zero : ∀ x ∈ V, ∀ y ∈ A,
    polynomialValue (parameterPolynomial P x) (yGraphMap (g x) y) = 0
  h_reg : ∀ x ∈ V, ∀ y ∈ A,
    (polynomialGradient (parameterPolynomial P x) (yGraphMap (g x) y)) 1 ≠ 0

/-- Countable simultaneous cover of the y-regular family zero sets. -/
theorem exists_countable_ygraph_cover (P : PolynomialParameterization k) :
    ∃ patches : ℕ → FamilyYGraphPatch k P,
      ∀ (x : CoefficientSpace P.dim) (z : Point 3),
        polynomialValue (parameterPolynomial P x) z = 0 →
        (polynomialGradient (parameterPolynomial P x) z) 1 ≠ 0 →
        ∃ n, x ∈ (patches n).V ∧
          ∃ y ∈ (patches n).A, z = yGraphMap ((patches n).g x) y := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let P' := renameParameterization σ P
  let L := swapCoords 1 2
  have hσ : σ.symm = σ := by
    ext i
    fin_cases i <;> decide
  have hL : Function.Involutive L := swapCoords_involutive 1 2
  have hval : ∀ (x : CoefficientSpace P.dim) (z : Point 3),
      polynomialValue (parameterPolynomial P' x) z =
        polynomialValue (parameterPolynomial P x) (L z) := by
    intro x z
    rw [parameterPolynomial_rename σ P x, renamePoly_eval]
    rfl
  have hgrad : ∀ (x : CoefficientSpace P.dim) (z : Point 3),
      (polynomialGradient (parameterPolynomial P' x) z) 2 =
        (polynomialGradient (parameterPolynomial P x) (L z)) 1 := by
    intro x z
    rw [parameterPolynomial_rename σ P x, renamePoly_gradient, hσ]
    rfl
  rcases exists_countable_zgraph_cover P' with ⟨zpatches, hcover⟩
  let patches : ℕ → FamilyYGraphPatch k P := fun n =>
    { V := (zpatches n).V
      A := (zpatches n).A
      g := (zpatches n).g
      hV_open := (zpatches n).hV_open
      hA_open := (zpatches n).hA_open
      hg_smooth := (zpatches n).hg_smooth
      h_zero := by
        intro x hx y hy
        have hz := (zpatches n).h_zero x hx y hy
        have ht := hval x (graphMap ((zpatches n).g x) y)
        exact ht ▸ hz
      h_reg := by
        intro x hx y hy
        have hz := (zpatches n).h_reg x hx y hy
        have ht := hgrad x (graphMap ((zpatches n).g x) y)
        exact ht ▸ hz }
  refine ⟨patches, ?_⟩
  intro x z hz hreg
  have hz' : polynomialValue (parameterPolynomial P' x) (L z) = 0 := by
    rw [hval, hL z]
    exact hz
  have hreg' :
      (polynomialGradient (parameterPolynomial P' x) (L z)) 2 ≠ 0 := by
    rw [hgrad, hL z]
    exact hreg
  rcases hcover x (L z) hz' hreg' with ⟨n, hx, y, hy, heq⟩
  refine ⟨n, hx, y, hy, ?_⟩
  have h1 :
      L (yGraphMap ((zpatches n).g x) y) =
        graphMap ((zpatches n).g x) y := by
    have hdef :
        yGraphMap ((zpatches n).g x) y =
          L (graphMap ((zpatches n).g x) y) := by rfl
    rw [hdef, hL]
  have h2 : L (yGraphMap ((zpatches n).g x) y) = L z := by
    rw [h1, heq.symm]
  exact L.injective h2.symm

end Kakeya.CV

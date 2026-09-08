/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

lemma product_finrank_helper (A C : Type _) [AddCommGroup A] [Module ℝ A] [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ A] [FiniteDimensional ℝ C]
    (p : Submodule ℝ A) (q : Submodule ℝ C) :
    Module.finrank ℝ (p.prod q : Submodule ℝ (A × C)) = Module.finrank ℝ p + Module.finrank ℝ q := by
  let S : Submodule ℝ (A × C) := p.prod q
  let e : S ≃ₗ[ℝ] (p × q) :=
    { toFun := fun x : S =>
        (⟨(x : A × C).1, x.property.1⟩, ⟨(x : A × C).2, x.property.2⟩)
      invFun := fun y : p × q => ⟨( (y.1 : A), (y.2 : C) ), Submodule.mem_prod.mpr ⟨y.1.property, y.2.property⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro y
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  have h : Module.finrank ℝ S = Module.finrank ℝ (p × q) := e.finrank_eq
  have h2 : Module.finrank ℝ (p × q) = Module.finrank ℝ p + Module.finrank ℝ q := Module.finrank_prod
  exact h.trans h2

lemma helper_crucial_final (A C : Type _) [AddCommGroup A] [Module ℝ A] [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ A] [FiniteDimensional ℝ C]
    (p : Submodule ℝ A) (q : Submodule ℝ C) :
    let s : Submodule ℝ (A × C) := p.prod q
    Module.finrank ℝ s = Module.finrank ℝ p + Module.finrank ℝ q := by
  let s : Submodule ℝ (A × C) := p.prod q
  have h1 := product_finrank_helper A C p q
  exact h1

lemma round1_h_main_rank_lemma (V1 V2 W2 : Type _)
    [AddCommGroup V1] [Module ℝ V1] [FiniteDimensional ℝ V1]
    [AddCommGroup V2] [Module ℝ V2] [FiniteDimensional ℝ V2]
    [AddCommGroup W2] [Module ℝ W2] [FiniteDimensional ℝ W2]
    (Q : (V1 × V2) →ₗ[ℝ] W2) :
    let L : (V1 × V2) →ₗ[ℝ] (V1 × W2) :=
      { toFun := fun p : V1 × V2 => (p.1, Q p)
        map_add' := by
          intro p q
          ext <;> simp [map_add]
        map_smul' := by
          intro c p
          ext <;> simp [map_smul] }
    let Q_B : V2 →ₗ[ℝ] W2 :=
      { toFun := fun w : V2 => Q (0, w)
        map_add' := by
          intro w1 w2
          have h : Q ((0 : V1), w1 + w2) = Q ((0 : V1), w1) + Q ((0 : V1), w2) := by
            have h' : ((0 : V1), w1 + w2) = ((0 : V1), w1) + ((0 : V1), w2) := by ext <;> simp
            rw [h']
            exact map_add Q _ _
          exact h
        map_smul' := by
          intro c w
          have h : Q ((0 : V1), c • w) = c • Q ((0 : V1), w) := by
            have h' : ((0 : V1), c • w) = c • ((0 : V1), w) := by ext <;> simp
            rw [h']
            exact map_smul Q c _
          exact h }
    Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ V1 + Module.finrank ℝ (LinearMap.range Q_B) := by
  let L : (V1 × V2) →ₗ[ℝ] (V1 × W2) :=
    { toFun := fun p : V1 × V2 => (p.1, Q p)
      map_add' := by
        intro p q
        ext <;> simp [map_add]
      map_smul' := by
        intro c p
        ext <;> simp [map_smul] }
  let Q_B : V2 →ₗ[ℝ] W2 :=
    { toFun := fun w : V2 => Q (0, w)
      map_add' := by
        intro w1 w2
        have h : Q ((0 : V1), w1 + w2) = Q ((0 : V1), w1) + Q ((0 : V1), w2) := by
          have h' : ((0 : V1), w1 + w2) = ((0 : V1), w1) + ((0 : V1), w2) := by ext <;> simp
          rw [h']
          exact map_add Q _ _
        exact h
      map_smul' := by
        intro c w
        have h : Q ((0 : V1), c • w) = c • Q ((0 : V1), w) := by
          have h' : ((0 : V1), c • w) = c • ((0 : V1), w) := by ext <;> simp
          rw [h']
          exact map_smul Q c _
        exact h }
  let K : Submodule ℝ (V1 × V2) := Submodule.prod (⊥ : Submodule ℝ V1) (LinearMap.ker Q_B)
  have h1 : LinearMap.ker L = K := by
    ext ⟨v1, v2⟩
    simp only [L, LinearMap.mem_ker, K, Submodule.mem_prod, Submodule.mem_bot, Q_B]
    constructor
    · intro h
      have h11 : v1 = 0 := by
        simp at h
        exact h.1
      have h12 : Q (0, v2) = 0 := by simpa [h11] using (Prod.ext_iff.mp h).2
      exact ⟨h11, h12⟩
    · rintro ⟨rfl, h2⟩
      simpa using h2
  have h_rank1 : Module.finrank ℝ (LinearMap.range L) + Module.finrank ℝ (LinearMap.ker L) = Module.finrank ℝ (V1 × V2) := by
    exact LinearMap.finrank_range_add_finrank_ker L
  have h_rank2 : Module.finrank ℝ (LinearMap.range Q_B) + Module.finrank ℝ (LinearMap.ker Q_B) = Module.finrank ℝ V2 := by
    exact LinearMap.finrank_range_add_finrank_ker Q_B
  have h3 : Module.finrank ℝ (V1 × V2) = Module.finrank ℝ V1 + Module.finrank ℝ V2 := by
    exact finrank_prod
  have h41 : Module.finrank ℝ K = Module.finrank ℝ (⊥ : Submodule ℝ V1) + Module.finrank ℝ (LinearMap.ker Q_B) :=
    product_finrank_helper V1 V2 (⊥ : Submodule ℝ V1) (LinearMap.ker Q_B)
  have h42 : Module.finrank ℝ (⊥ : Submodule ℝ V1) = 0 := by simp
  have h4 : Module.finrank ℝ (LinearMap.ker L) = Module.finrank ℝ (LinearMap.ker Q_B) := by
    calc
      Module.finrank ℝ (LinearMap.ker L) = Module.finrank ℝ K := by rw [h1]
      _ = Module.finrank ℝ (⊥ : Submodule ℝ V1) + Module.finrank ℝ (LinearMap.ker Q_B) := h41
      _ = 0 + Module.finrank ℝ (LinearMap.ker Q_B) := by rw [h42]
      _ = Module.finrank ℝ (LinearMap.ker Q_B) := by ring
  linarith

lemma round1_h_partial_deriv {m n r : ℕ}
    (G : (E r × E (m - r)) → E (n - r))
    (hG_diff : ContDiff ℝ ⊤ G)
    (y : E r × E (m - r)) :
    let j : E (m - r) → (E r × E (m - r)) := fun w : E (m - r) => (y.1, w)
    let Q : (E r × E (m - r)) →ₗ[ℝ] E (n - r) := (fderiv ℝ G y).toLinearMap
    let Q_B : E (m - r) →ₗ[ℝ] E (n - r) :=
      { toFun := fun w : E (m - r) => Q (0, w)
        map_add' := by
          intro w1 w2
          have h : Q ((0 : E r), w1 + w2) = Q ((0 : E r), w1) + Q ((0 : E r), w2) := by
            have h' : ((0 : E r), w1 + w2) = ((0 : E r), w1) + ((0 : E r), w2) := by ext <;> simp
            rw [h']
            exact map_add Q _ _
          exact h
        map_smul' := by
          intro c w
          have h : Q ((0 : E r), c • w) = c • Q ((0 : E r), w) := by
            have h' : ((0 : E r), c • w) = c • ((0 : E r), w) := by ext <;> simp
            rw [h']
            exact map_smul Q c _
          exact h }
    (fderiv ℝ (fun b : E (m - r) => G (j b)) y.2).toLinearMap = Q_B := by
  let j : E (m - r) → (E r × E (m - r)) := fun w : E (m - r) => (y.1, w)
  let Q : (E r × E (m - r)) →ₗ[ℝ] E (n - r) := (fderiv ℝ G y).toLinearMap
  let Q_B : E (m - r) →ₗ[ℝ] E (n - r) :=
    { toFun := fun w : E (m - r) => Q (0, w)
      map_add' := by
        intro w1 w2
        have h : Q ((0 : E r), w1 + w2) = Q ((0 : E r), w1) + Q ((0 : E r), w2) := by
          have h' : ((0 : E r), w1 + w2) = ((0 : E r), w1) + ((0 : E r), w2) := by ext <;> simp
          rw [h']
          exact map_add Q _ _
        exact h
      map_smul' := by
        intro c w
        have h : Q ((0 : E r), c • w) = c • Q ((0 : E r), w) := by
          have h' : ((0 : E r), c • w) = c • ((0 : E r), w) := by ext <;> simp
          rw [h']
          exact map_smul Q c _
        exact h }
  let inr_clm : (E (m - r)) →L[ℝ] (E r × E (m - r)) := (LinearMap.inr ℝ (E r) (E (m - r))).toContinuousLinearMap
  let c : (E r × E (m - r)) := (y.1, 0)
  have h_j : j = fun z : E (m - r) => c + inr_clm z := by
    funext z
    ext <;> simp [j, c, inr_clm, LinearMap.inr_apply]
  have h3 : HasFDerivAt j inr_clm y.2 := by
    rw [h_j]
    exact inr_clm.hasFDerivAt.const_add c
  have h_ne : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hG_diff' : Differentiable ℝ G := hG_diff.differentiable h_ne
  have hG_at : HasFDerivAt G (fderiv ℝ G y) y := hG_diff'.differentiableAt.hasFDerivAt
  have h5 : HasFDerivAt (G ∘ j) ((fderiv ℝ G y).comp inr_clm) y.2 := hG_at.comp y.2 h3
  have h5' : fderiv ℝ (G ∘ j) y.2 = (fderiv ℝ G y).comp inr_clm := h5.fderiv
  have h6 : (fderiv ℝ (G ∘ j) y.2).toLinearMap = (fderiv ℝ G y).toLinearMap.comp (inr_clm : (E (m - r)) →ₗ[ℝ] (E r × E (m - r))) := by
    rw [h5']
    rfl
  convert h6 using 1
  <;> ext w <;> simp <;> rfl

lemma round1_finrank_map_equiv {A B : Type _} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A] [AddCommGroup B] [Module ℝ B] [FiniteDimensional ℝ B]
    (e : A ≃ₗ[ℝ] B) (S : Submodule ℝ A) :
    Module.finrank ℝ (Submodule.map (e : A →ₗ[ℝ] B) S) = Module.finrank ℝ S := by
  let e' : S ≃ₗ[ℝ] (Submodule.map (e : A →ₗ[ℝ] B) S) :=
    Submodule.equivMapOfInjective (e : A →ₗ[ℝ] B) e.injective S
  exact LinearEquiv.finrank_eq e'.symm

lemma round1_correct_rank_formula_straightened {m n r : ℕ}
    (f : E m → E n) (G : (E r × E (m - r)) → E (n - r))
    (H : E m → E r × E (m - r))
    (e : (E r × E (n - r)) ≃L[ℝ] E n)
    (h_eq : ∀ x, e ((H x).1, G (H x)) = f x)
    (hH_diff : ContDiff ℝ ⊤ H)
    (hG_diff : ContDiff ℝ ⊤ G)
    (x : E m)
    (h_bij : Function.Bijective ((fderiv ℝ H x) : E m → (E r × E (m - r)))) :
    fderivRank f x = r + fderivRank (fun b : E (m - r) => G ((H x).1, b)) (H x).2 := by
  set y : E r × E (m - r) := H x with hy_def
  set F : (E r × E (m - r)) → (E r × E (n - r)) := fun p => (p.1, G p) with hF_def
  have h1 : ∀ x, f x = e (F (H x)) := by
    intro x
    have h_eq2 : e ((H x).1, G (H x)) = f x := h_eq x
    simpa [hF_def] using Eq.symm h_eq2
  have hFst_diff : ContDiff ℝ ⊤ (fun p : E r × E (m - r) => p.1) := by
    exact contDiff_fst
  have hF_diff : ContDiff ℝ ⊤ F := by
    exact ContDiff.prodMk hFst_diff hG_diff
  set Q : (E r × E (m - r)) →ₗ[ℝ] E (n - r) := (fderiv ℝ G y).toLinearMap with hQ_def
  set L : (E r × E (m - r)) →ₗ[ℝ] (E r × E (n - r)) :=
    { toFun := fun p : (E r × E (m - r)) => (p.1, Q p)
      map_add' := fun p q => by ext <;> simp [map_add]
      map_smul' := fun c p => by ext <;> simp [map_smul] } with hL_def
  set Q_B : E (m - r) →ₗ[ℝ] E (n - r) :=
    { toFun := fun w : E (m - r) => Q (0, w)
      map_add' := fun w1 w2 => by
        have h' : ((0 : E r), w1 + w2) = ((0 : E r), w1) + ((0 : E r), w2) := by ext <;> simp
        rw [h']
        exact map_add Q _ _
      map_smul' := fun c w => by
        have h' : ((0 : E r), c • w) = c • ((0 : E r), w) := by ext <;> simp
        rw [h']
        exact map_smul Q c _ } with hQB_def
  let fst_clm : (E r × E (m - r)) →L[ℝ] E r := (LinearMap.fst ℝ (E r) (E (m - r))).toContinuousLinearMap
  have h_ne_top : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hG_diff' : Differentiable ℝ G := hG_diff.differentiable h_ne_top
  have h21 : HasFDerivAt (fun p : E r × E (m - r) => p.1) fst_clm y := hasFDerivAt_fst
  have h22 : HasFDerivAt G (fderiv ℝ G y) y := hG_diff'.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt F (fst_clm.prod (fderiv ℝ G y)) y := HasFDerivAt.prodMk h21 h22
  have h_fderiv_F_eq : fderiv ℝ F y = fst_clm.prod (fderiv ℝ G y) := h2.fderiv
  have h_fderiv_F : (fderiv ℝ F y).toLinearMap = L := by
    rw [h_fderiv_F_eq]
    apply LinearMap.ext
    intro p
    let v1 : E r := p.1
    let v2 : E (m - r) := p.2
    have h_goal : ((fst_clm.prod (fderiv ℝ G y)).toLinearMap) p = (v1, Q p) := by
      simp [fst_clm, hQ_def]
      rfl
    have h_Lp : L p = (v1, Q p) := by
      simp [hL_def]
      rfl
    rw [h_goal, h_Lp]
  have h_fderiv_Gb : (fderiv ℝ (fun b : E (m - r) => G ((y.1, b))) y.2).toLinearMap = Q_B :=
    round1_h_partial_deriv G hG_diff y
  have h_main_rank : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ (E r) + Module.finrank ℝ (LinearMap.range Q_B) :=
    round1_h_main_rank_lemma (E r) (E (m - r)) (E (n - r)) Q
  have h_finrank_Er : Module.finrank ℝ (E r) = r := by
    simp [E]
  let g' : (E r × E (m - r)) →ₗ[ℝ] (E r × E (n - r)) := (fderiv ℝ F y).toLinearMap
  let h' : E m →ₗ[ℝ] (E r × E (m - r)) := (fderiv ℝ H x).toLinearMap
  have hH_diff' : Differentiable ℝ H := hH_diff.differentiable h_ne_top
  have hF_diff' : Differentiable ℝ F := hF_diff.differentiable h_ne_top
  have h_dh : DifferentiableAt ℝ H x := hH_diff'.differentiableAt
  have h_dF : DifferentiableAt ℝ F y := hF_diff'.differentiableAt
  have h_comp1 : fderiv ℝ (F ∘ H) x = (fderiv ℝ F y).comp (fderiv ℝ H x) := by
    exact fderiv_comp x h_dF h_dh
  let A : (E m →ₗ[ℝ] (E r × E (n - r))) := (fderiv ℝ (F ∘ H) x).toLinearMap
  have h_comp1_linear : A = g'.comp h' := by
    rw [show A = (fderiv ℝ (F ∘ H) x).toLinearMap from rfl, h_comp1]
    rfl
  have h4 : DifferentiableAt ℝ (F ∘ H) x := h_dF.comp x h_dh
  have h4' : HasFDerivAt (e ∘ (F ∘ H)) ((e : (E r × E (n - r)) →L[ℝ] E n).comp (fderiv ℝ (F ∘ H) x)) x :=
    e.hasFDerivAt.comp x h4.hasFDerivAt
  have h_comp2 : fderiv ℝ f x = (e : (E r × E (n - r)) →L[ℝ] E n).comp (fderiv ℝ (F ∘ H) x) := by
    have h : f = e ∘ (F ∘ H) := by funext x; exact h1 x
    rw [h]
    exact h4'.fderiv
  have h_comp2_linear : (fderiv ℝ f x).toLinearMap = (e : (E r × E (n - r)) →ₗ[ℝ] E n).comp A := by
    rw [h_comp2]
    rfl
  have h_range1 : LinearMap.range (fderiv ℝ f x).toLinearMap = Submodule.map (e : (E r × E (n - r)) →ₗ[ℝ] E n) (LinearMap.range A) := by
    rw [h_comp2_linear, LinearMap.range_comp]
  let e' : (E r × E (n - r)) ≃ₗ[ℝ] E n := e.toLinearEquiv
  have h_finrank1 : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = Module.finrank ℝ (LinearMap.range A) := by
    rw [h_range1]
    exact round1_finrank_map_equiv e' (LinearMap.range A)
  have h_surj_h' : LinearMap.range h' = ⊤ := LinearMap.range_eq_top.mpr h_bij.2
  have h_range2 : LinearMap.range (g'.comp h') = LinearMap.range g' := by
    exact LinearMap.range_comp_of_range_eq_top g' h_surj_h'
  have h_finrank2 : Module.finrank ℝ (LinearMap.range A) = Module.finrank ℝ (LinearMap.range g') := by
    have h : LinearMap.range A = LinearMap.range (g'.comp h') := by rw [h_comp1_linear]
    rw [h, h_range2]
  have h_g'_eq_L : g' = L := h_fderiv_F
  have h_finrank3 : Module.finrank ℝ (LinearMap.range g') = Module.finrank ℝ (LinearMap.range L) := by
    rw [h_g'_eq_L]
  have h_final : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = r + Module.finrank ℝ (LinearMap.range Q_B) := by
    calc
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)
        = Module.finrank ℝ (LinearMap.range A) := h_finrank1
      _ = Module.finrank ℝ (LinearMap.range g') := h_finrank2
      _ = Module.finrank ℝ (LinearMap.range L) := h_finrank3
      _ = Module.finrank ℝ (E r) + Module.finrank ℝ (LinearMap.range Q_B) := h_main_rank
      _ = r + Module.finrank ℝ (LinearMap.range Q_B) := by rw [h_finrank_Er]
  have h_last : fderivRank (fun b : E (m - r) => G ((H x).1, b)) (H x).2 = Module.finrank ℝ (LinearMap.range Q_B) := by
    have h_eq1 : fderivRank (fun b : E (m - r) => G ((H x).1, b)) (H x).2 = Module.finrank ℝ (LinearMap.range (fderiv ℝ (fun b : E (m - r) => G ((H x).1, b)) (H x).2).toLinearMap) := by rfl
    rw [h_eq1]
    rw [h_fderiv_Gb]
  have h_main_goal : fderivRank f x = Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) := by rfl
  rw [h_main_goal, h_final, h_last]

lemma range_comp_surjective {X Y Z : Type _} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    (φ : X →ₗ[ℝ] Y) (hφ : Function.Surjective φ) (B : Y →ₗ[ℝ] Z) :
    LinearMap.range (B.comp φ) = LinearMap.range B := by
  ext z
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨φ x, hx⟩
  · rintro ⟨y, hy⟩
    rcases hφ y with ⟨x, rfl⟩
    exact ⟨x, hy⟩

lemma fderiv_F_def {m r n : ℕ} (G : (E r × E (m - r)) → E (n - r))
    (hG_diff : ContDiff ℝ ∞ G) (y : E r × E (m - r)) :
    (fderiv ℝ (fun p : E r × E (m - r) => (p.1, G p)) y).toLinearMap =
      let Q : (E r × E (m - r)) →ₗ[ℝ] E (n - r) := (fderiv ℝ G y).toLinearMap
      { toFun := fun p : E r × E (m - r) => (p.1, Q p)
        map_add' := by
          intro p q
          ext <;> simp [map_add]
        map_smul' := by
          intro c p
          ext <;> simp [map_smul] } := by
  let Q_clm : (E r × E (m - r)) →L[ℝ] E (n - r) := fderiv ℝ G y
  let L_clm : (E r × E (m - r)) →L[ℝ] (E r × E (n - r)) :=
    (ContinuousLinearMap.fst ℝ (E r) (E (m - r))).prod Q_clm
  have h_pos : 0 < (∞ : WithTop ℕ∞) := by
    exact sign_eq_one_iff.mp rfl
  have h1 : HasFDerivAt (fun p : E r × E (m - r) => p.1) (ContinuousLinearMap.fst ℝ (E r) (E (m - r))) y := by
    exact hasFDerivAt_fst
  have h2 : HasFDerivAt G Q_clm y := (hG_diff.differentiable h_pos.ne').differentiableAt.hasFDerivAt
  have hF_hasFDeriv : HasFDerivAt (fun p : E r × E (m - r) => (p.1, G p)) L_clm y :=
    HasFDerivAt.prodMk h1 h2
  have h_fderiv_eq : fderiv ℝ (fun p : E r × E (m - r) => (p.1, G p)) y = L_clm := hF_hasFDeriv.fderiv
  rw [h_fderiv_eq]
  ext p <;> simp [L_clm] <;> rfl

/-- Given H and Hinv are two-sided inverses and both smooth,
    then fderiv ℝ H x is bijective (hence preserves rank). -/
lemma fderiv_bijective_of_local_inverse {m r : ℕ}
    (H : E m → E r × E (m - r))
    (Hinv : (E r × E (m - r)) → E m)
    (hH_diff : ContDiff ℝ ∞ H)
    (hHinv_diff : ContDiff ℝ ∞ Hinv)
    (h1 : ∀ (y : E r × E (m - r)), H (Hinv y) = y)
    (h2 : ∀ (x : E m), Hinv (H x) = x)
    (x : E m) :
    Function.Bijective (fderiv ℝ H x) := by
  have h_pos : 0 < (∞ : WithTop ℕ∞) := by
    exact sign_eq_one_iff.mp rfl
  let A : E m →L[ℝ] (E r × E (m - r)) := fderiv ℝ H x
  let y : E r × E (m - r) := H x
  let B : (E r × E (m - r)) →L[ℝ] E m := fderiv ℝ Hinv y
  have h_Hdiff : Differentiable ℝ H := hH_diff.differentiable h_pos.ne'
  have h_Hinvdiff : Differentiable ℝ Hinv := hHinv_diff.differentiable h_pos.ne'
  have h_Hdiff_at : DifferentiableAt ℝ H x := h_Hdiff.differentiableAt
  have h_Hinvdiff_at : DifferentiableAt ℝ Hinv y := h_Hinvdiff.differentiableAt
  have h_Hdiff_at2 : DifferentiableAt ℝ H (Hinv y) := by
    have h4 : Hinv y = x := by simpa [y] using h2 x
    rw [h4]
    exact h_Hdiff_at
  have h_fderiv_id1 : fderiv ℝ (id : E m → E m) x = ContinuousLinearMap.id ℝ (E m) := by
    simp
  have h_fderiv_id2 : fderiv ℝ (id : (E r × E (m - r)) → (E r × E (m - r))) y = ContinuousLinearMap.id ℝ (E r × E (m - r)) := by
    simp
  have h_id1 : Hinv ∘ H = id := by
    funext z
    exact h2 z
  have h_id2 : H ∘ Hinv = id := by
    funext z
    exact h1 z
  have h_eq1 : fderiv ℝ (Hinv ∘ H) x = B.comp A := by
    rw [fderiv_comp x h_Hinvdiff_at h_Hdiff_at]
  have h_comp1 : B.comp A = ContinuousLinearMap.id ℝ (E m) := by
    have h5 : fderiv ℝ (Hinv ∘ H) x = fderiv ℝ (id : E m → E m) x := by rw [h_id1]
    rw [h5, h_fderiv_id1] at h_eq1
    exact h_eq1.symm
  have h_eq2 : fderiv ℝ (H ∘ Hinv) y = A.comp B := by
    rw [fderiv_comp y h_Hdiff_at2 h_Hinvdiff_at]
    · simp [y, h2 x]
      rfl
  have h_comp2 : A.comp B = ContinuousLinearMap.id ℝ (E r × E (m - r)) := by
    have h6 : fderiv ℝ (H ∘ Hinv) y = fderiv ℝ (id : (E r × E (m - r)) → (E r × E (m - r))) y := by rw [h_id2]
    rw [h6, h_fderiv_id2] at h_eq2
    exact h_eq2.symm
  have h_left_inverse : ∀ (z : E m), B (A z) = z := by
    intro z
    have h := congr_arg (fun (f : E m →L[ℝ] E m) => f z) h_comp1
    simpa using h
  have h_right_inverse : ∀ (z : E r × E (m - r)), A (B z) = z := by
    intro z
    have h := congr_arg (fun (f : (E r × E (m - r)) →L[ℝ] (E r × E (m - r))) => f z) h_comp2
    simpa using h
  have h_inj : Function.Injective A := by
    intro z1 z2 h
    have h5 : B (A z1) = B (A z2) := by rw [h]
    simpa [h_left_inverse] using h5
  have h_surj : Function.Surjective A := by
    intro z
    use B z
    exact h_right_inverse z
  exact ⟨h_inj, h_surj⟩

lemma our_partial_deriv {m n r : ℕ}
    (G : (E r × E (m - r)) → E (n - r))
    (hG_diff : ContDiff ℝ ∞ G)
    (y : E r × E (m - r)) :
    (fderiv ℝ (fun b : E (m - r) => G ((y.1, b))) y.2).toLinearMap =
    let Q : (E r × E (m - r)) →ₗ[ℝ] E (n - r) := (fderiv ℝ G y).toLinearMap
    { toFun := fun w : E (m - r) => Q (0, w)
      map_add' := fun w1 w2 => by
        have h' : ((0 : E r), w1 + w2) = ((0 : E r), w1) + ((0 : E r), w2) := by ext <;> simp
        have h : Q ((0 : E r), w1 + w2) = Q (((0 : E r), w1) + ((0 : E r), w2)) := by rw [h']
        rw [h]
        exact map_add Q _ _
      map_smul' := fun c w => by
        have h' : ((0 : E r), c • w) = c • ((0 : E r), w) := by ext <;> simp
        have h : Q ((0 : E r), c • w) = Q (c • ((0 : E r), w)) := by rw [h']
        rw [h]
        exact map_smul Q c _ } := by
  let j : E (m - r) → (E r × E (m - r)) := fun w : E (m - r) => (y.1, w)
  let Q : (E r × E (m - r)) →ₗ[ℝ] E (n - r) := (fderiv ℝ G y).toLinearMap
  let dj : (E (m - r)) →L[ℝ] (E r × E (m - r)) :=
    { toFun := fun w : E (m - r) => (0, w)
      map_add' := by intro a b; ext <;> simp
      map_smul' := by intro c a; ext <;> simp }
  let Q_B' : E (m - r) →ₗ[ℝ] E (n - r) :=
    { toFun := fun w : E (m - r) => Q (0, w)
      map_add' := fun w1 w2 => by
        have h' : ((0 : E r), w1 + w2) = ((0 : E r), w1) + ((0 : E r), w2) := by ext <;> simp
        have h : Q ((0 : E r), w1 + w2) = Q (((0 : E r), w1) + ((0 : E r), w2)) := by rw [h']
        rw [h]
        exact map_add Q _ _
      map_smul' := fun c w => by
        have h' : ((0 : E r), c • w) = c • ((0 : E r), w) := by ext <;> simp
        have h : Q ((0 : E r), c • w) = Q (c • ((0 : E r), w)) := by rw [h']
        rw [h]
        exact map_smul Q c _ }
  have h11 : HasFDerivAt (fun w : E (m - r) => (0, w)) dj y.2 := by
    exact dj.hasFDerivAt
  have h1 : HasFDerivAt j dj y.2 := by
    have h_j : j = fun w : E (m - r) => (y.1, 0) + (0, w) := by
      funext w
      ext <;> simp [j]
    rw [h_j]
    exact h11.const_add (y.1, 0)
  have hG_diff' : Differentiable ℝ G := hG_diff.differentiable (by simp)
  have h21 : DifferentiableAt ℝ G y := hG_diff' y
  have h2 : HasFDerivAt G (fderiv ℝ G y) y := h21.hasFDerivAt
  have h3 : HasFDerivAt (G ∘ j) ((fderiv ℝ G y).comp dj) y.2 := h2.comp y.2 h1
  have h4 : (fderiv ℝ (G ∘ j) y.2) = (fderiv ℝ G y).comp dj := h3.fderiv
  have h_main : (fderiv ℝ (G ∘ j) y.2).toLinearMap = Q_B' := by
    ext w i
    have h5 : (fderiv ℝ (G ∘ j) y.2).toLinearMap w = ((fderiv ℝ G y).comp dj).toLinearMap w := by
      rw [h4]
    have h6 : ((fderiv ℝ G y).comp dj).toLinearMap w = Q_B' w := by
      simp [Q_B', Q, dj]
    have h7 : (fderiv ℝ (G ∘ j) y.2).toLinearMap w = Q_B' w := by
      rw [h5, h6]
    exact congr_arg (fun x : E (n - r) => x i) h7
  exact h_main

lemma almost_done_proof_final {m n r : ℕ}
    (f : E m → E n) (G : (E r × E (m - r)) → E (n - r))
    (H : E m → E r × E (m - r))
    (e : (E r × E (n - r)) ≃L[ℝ] E n)
    (h_eq : ∀ x, e ((H x).1, G (H x)) = f x)
    (hH_diff : ContDiff ℝ ∞ H)
    (hG_diff : ContDiff ℝ ∞ G)
    (x : E m)
    (h_bij : Function.Bijective ((fderiv ℝ H x) : E m → (E r × E (m - r)))) :
    fderivRank f x = r + fderivRank (fun b : E (m - r) => G ((H x).1, b)) (H x).2 := by
  set y := H x with hy_def
  set F : (E r × E (m - r)) → (E r × E (n - r)) := fun z => (z.1, G z) with hF_def
  have h_main_eq1 : f = e ∘ (F ∘ H) := by
    funext z
    have h : e ((H z).1, G (H z)) = f z := h_eq z
    exact h.symm
  have hF_diff : ContDiff ℝ ∞ F := by
    fun_prop
  have hF_diff' : Differentiable ℝ F := hF_diff.differentiable (by simp)
  have hH_diff' : Differentiable ℝ H := hH_diff.differentiable (by simp)
  set dH : (E m) →ₗ[ℝ] (E r × E (m - r)) := (fderiv ℝ H x).toLinearMap with hdH_def
  set L2 : (E r × E (m - r)) →ₗ[ℝ] (E r × E (n - r)) := (fderiv ℝ F y).toLinearMap with hL2_def
  have hF_at_y : DifferentiableAt ℝ F y := hF_diff' y
  have hF_at : HasFDerivAt F (fderiv ℝ F y) y := hF_at_y.hasFDerivAt
  have hH_at_x : DifferentiableAt ℝ H x := hH_diff' x
  have hH_at : HasFDerivAt H (fderiv ℝ H x) x := hH_at_x.hasFDerivAt
  have h_chain_has : HasFDerivAt (F ∘ H) ((fderiv ℝ F y).comp (fderiv ℝ H x)) x := hF_at.comp x hH_at
  have h_chain : (fderiv ℝ (F ∘ H) x) = (fderiv ℝ F y).comp (fderiv ℝ H x) := h_chain_has.fderiv
  have h_chain_has2 : HasFDerivAt (F ∘ H) (fderiv ℝ (F ∘ H) x) x := by
    simpa [h_chain] using h_chain_has
  set L1 : (E m) →ₗ[ℝ] (E r × E (n - r)) := (fderiv ℝ (F ∘ H) x).toLinearMap with hL1_def
  have h_chain2 : L1 = L2.comp dH := by
    exact congr_arg (fun (f : (E m →L[ℝ] (E r × E (n - r)))) => f.toLinearMap) h_chain
  have h_surj : Function.Surjective dH := h_bij.surjective
  have h_range_eq : LinearMap.range L1 = LinearMap.range L2 := by
    rw [h_chain2]
    exact range_comp_surjective dH h_surj L2
  set e' : (E r × E (n - r)) →L[ℝ] E n := (e : (E r × E (n - r)) →L[ℝ] E n) with he'_def
  have h_e_has : HasFDerivAt e e' (F (H x)) := e.hasFDerivAt
  have h_fderiv_f_has : HasFDerivAt (e ∘ (F ∘ H)) (e'.comp (fderiv ℝ (F ∘ H) x)) x := h_e_has.comp x h_chain_has2
  have h_fderiv_f : (fderiv ℝ f x) = e'.comp (fderiv ℝ (F ∘ H) x) := by
    rw [h_main_eq1]
    exact h_fderiv_f_has.fderiv
  set df : (E m) →ₗ[ℝ] E n := (fderiv ℝ f x).toLinearMap with hdf_def
  have h_df_eq : df = (e'.toLinearMap).comp L1 := by
    exact congr_arg (fun (f : (E m →L[ℝ] E n)) => f.toLinearMap) h_fderiv_f
  have h_range_df : LinearMap.range df = Submodule.map (e'.toLinearMap) (LinearMap.range L1) := by
    rw [h_df_eq]
    exact LinearMap.range_comp L1 (e'.toLinearMap)
  have h_rank1 : Module.finrank ℝ (LinearMap.range df) = Module.finrank ℝ (LinearMap.range L1) := by
    rw [h_range_df]
    exact round1_finrank_map_equiv (e.toLinearEquiv) (LinearMap.range L1)
  set Q : (E r × E (m - r)) →ₗ[ℝ] E (n - r) := (fderiv ℝ G y).toLinearMap with hQ_def
  let Q_B' : E (m - r) →ₗ[ℝ] E (n - r) :=
    { toFun := fun w : E (m - r) => Q (0, w)
      map_add' := fun w1 w2 => by
        have h' : ((0 : E r), w1 + w2) = ((0 : E r), w1) + ((0 : E r), w2) := by ext <;> simp
        have h : Q ((0 : E r), w1 + w2) = Q (((0 : E r), w1) + ((0 : E r), w2)) := by rw [h']
        rw [h]
        exact map_add Q _ _
      map_smul' := fun c w => by
        have h' : ((0 : E r), c • w) = c • ((0 : E r), w) := by ext <;> simp
        have h : Q ((0 : E r), c • w) = Q (c • ((0 : E r), w)) := by rw [h']
        rw [h]
        exact map_smul Q c _ }
  have h_rank2 : Module.finrank ℝ (LinearMap.range L2) = Module.finrank ℝ (E r) + Module.finrank ℝ (LinearMap.range Q_B') := by
    have hL2_eq : L2 = {
        toFun := fun p : (E r × E (m - r)) => (p.1, Q p)
        map_add' := by
          intro p q
          ext <;> simp [map_add]
        map_smul' := by
          intro c p
          ext <;> simp [map_smul] } := by
      exact fderiv_F_def G hG_diff y
    rw [hL2_eq]
    exact round1_h_main_rank_lemma (E r) (E (m - r)) (E (n - r)) Q
  set Q_B : E (m - r) →ₗ[ℝ] E (n - r) := (fderiv ℝ (fun b : E (m - r) => G ((H x).1, b)) (H x).2).toLinearMap with hQB_def
  have hQB : Q_B' = Q_B := (our_partial_deriv G hG_diff y).symm
  have h_finrank_Er : Module.finrank ℝ (E r) = r := by simp [E]
  have h_goal1 : fderivRank f x = Module.finrank ℝ (LinearMap.range df) := by rfl
  have h_goal2 : fderivRank (fun b : E (m - r) => G ((H x).1, b)) (H x).2 = Module.finrank ℝ (LinearMap.range Q_B) := by rfl
  rw [h_goal1, h_goal2]
  rw [h_rank1, h_range_eq, h_rank2, hQB, h_finrank_Er]

lemma rank_formula_straightened_corrected {m n r : ℕ}
    (f : E m → E n) (G : (E r × E (m - r)) → E (n - r))
    (H : E m → E r × E (m - r))
    (e : (E r × E (n - r)) ≃L[ℝ] E n)
    (h_eq : ∀ x, e ((H x).1, G (H x)) = f x)
    (hH_diff : ContDiff ℝ ∞ H)
    (hG_diff : ContDiff ℝ ∞ G)
    (hH_inv : ∃ (Hinv : (E r × E (m - r)) → E m),
      (ContDiff ℝ ∞ Hinv) ∧
      (∀ (y : E r × E (m - r)), H (Hinv y) = y) ∧
      (∀ (x : E m), Hinv (H x) = x))
    (x : E m) :
    fderivRank f x = r + fderivRank (fun b : E (m - r) => G ((H x).1, b)) (H x).2 := by
  rcases hH_inv with ⟨Hinv, hHinv_diff, h1, h2⟩
  have h_bij : Function.Bijective (fderiv ℝ H x) :=
    fderiv_bijective_of_local_inverse H Hinv hH_diff hHinv_diff h1 h2 x
  exact almost_done_proof_final f G H e h_eq hH_diff hG_diff x h_bij

/-- Lemma 7 (Rank formula in straightened coordinates).
    If f(H⁻¹(a, b)) = (a, G(a, b)), then
      rank(Df at H⁻¹(a,b)) = r + rank(D_b G at (a, b))
    where D_b G is the partial derivative in the b-coordinate. -/
theorem rank_formula_straightened {m n r : ℕ}
    (f : E m → E n) (G : (E r × E (m - r)) → E (n - r))
    (H : E m → E r × E (m - r))
    (e : (E r × E (n - r)) ≃L[ℝ] E n)
    (h_eq : ∀ x, e ((H x).1, G (H x)) = f x)
    (hH_diff : ContDiff ℝ ∞ H)
    (hG_diff : ContDiff ℝ ∞ G)
    (hH_inv : ∃ (Hinv : (E r × E (m - r)) → E m),
      (ContDiff ℝ ∞ Hinv) ∧
      (∀ (y : E r × E (m - r)), H (Hinv y) = y) ∧
      (∀ (x : E m), Hinv (H x) = x))
    (x : E m) :
    fderivRank f x = r + fderivRank (fun b : E (m - r) => G ((H x).1, b)) (H x).2 :=
  rank_formula_straightened_corrected f G H e h_eq hH_diff hG_diff hH_inv x

/-- Lemma 8 (Fubini for parameterized critical images).
    If S ⊆ E r × E (n - r) is a measurable set such that for almost every a : E r,
    the fiber {b : E (n - r) | (a, b) ∈ S} has volume zero,
    then S has (r + (n-r)) = n-dimensional volume zero.
    This is just Fubini's theorem for product measure. -/
theorem fubini_critical_image {r n : ℕ} (S : Set (E r × E (n - r)))
    (hS : MeasurableSet S)
    (h : ∀ᵐ a : E r, volume {b : E (n - r) | (a, b) ∈ S} = 0) :
    volume S = 0 := by
  have h_main : (volume : Measure (E r × E (n - r))) = (volume : Measure (E r)).prod (volume : Measure (E (n - r))) := by
    exact Measure.volume_eq_prod (E r) (E (n - r))
  rw [h_main]
  exact Measure.measure_prod_null_of_ae_null hS h


end ForMathlib.Analysis.Calculus.Sard.General

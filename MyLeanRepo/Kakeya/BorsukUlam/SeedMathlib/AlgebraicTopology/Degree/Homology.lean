/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Category.TopCat.Basic
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.EuclideanSpace.TopSphereHomology

@[expose] public section

/-!
# Homology-Based Degree Theory

This file defines the degree of a map f : S^n → S^n using singular homology.

The degree is the integer d such that the induced map f_* : H_n(S^n) → H_n(S^n)
corresponds to multiplication by d, under the isomorphism H_n(S^n) ≅ ℤ.

This approach gives us for free:
- Well-definedness (no need for Sard's theorem)
- Homotopy invariance (follows from functoriality of homology)
- Degree is multiplicative under composition
- Degree is a group homomorphism on homotopy groups

The hard direction of the Hopf degree theorem (degree 0 ⇒ nullhomotopic)
requires smooth techniques and is handled in SmoothDegree.lean.
-/

open Metric AlgebraicTopology CategoryTheory

noncomputable section

namespace SeedMathlib.AlgebraicTopology.Degree

variable {n : ℕ}

/-- The n-sphere as the unit sphere in (n+1)-dimensional Euclidean space. -/
abbrev Sphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The n-sphere as an object of TopCat. -/
abbrev TopSphere (n : ℕ) : TopCat := TopCat.of (Sphere n)

/-- Abbreviation for the n-th singular homology with ℤ coefficients. -/
abbrev Hn (X : TopCat) (n : ℕ) : AddCommGrpCat :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj X

/-!
## H_n(S^n) ≅ ℤ

The n-th singular homology group of the n-sphere is isomorphic to the integers.
Proved using Mayer-Vietoris and induction on n.
-/

/-- The n-th singular homology of the n-sphere is isomorphic to ℤ (for n > 0). -/
noncomputable def sphereTopHomologyIso (n : ℕ) (hn : 0 < n) :
    Hn (TopSphere n) n ≅ AddCommGrpCat.of ℤ :=
  have h1 : 1 ≤ n := by linarith
  SeedMathlib.AlgebraicTopology.SingularHomology.EuclideanSpace.topSphereHomologyIsoInt n h1

/-!
## Definition of degree

Given a continuous map f : S^n → S^n, its degree is the integer d
such that f_* : H_n(S^n) → H_n(S^n) corresponds to multiplication by d.
-/

/-- The map on homology induced by a continuous map of spheres. -/
def homologyMap (f : C(Sphere n, Sphere n)) :
    Hn (TopSphere n) n ⟶ Hn (TopSphere n) n :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
    (TopCat.ofHom f)

/-- The degree of a continuous map f : S^n → S^n.
    This is the integer d such that f_* corresponds to multiplication by d
    under the isomorphism H_n(S^n) ≅ ℤ. -/
def degree (f : C(Sphere n, Sphere n)) (hn : 0 < n) : ℤ :=
  let e := sphereTopHomologyIso n hn
  let f_star := homologyMap f
  let g : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ := e.inv ≫ f_star ≫ e.hom
  (g : ℤ → ℤ) 1

/-!
## Basic properties of degree
-/

/-- Homotopic maps have the same degree. -/
theorem degree_homotopy_invariant {f g : C(Sphere n, Sphere n)} (hn : 0 < n)
    (h : f.Homotopic g) : degree f hn = degree g hn := by
  have h1 : homologyMap f = homologyMap g := by
    dsimp only [homologyMap]
    let f' : TopSphere n ⟶ TopSphere n := TopCat.ofHom f
    let g' : TopSphere n ⟶ TopSphere n := TopCat.ofHom g
    rcases h with ⟨H⟩
    have h_hom : TopCat.Homotopy f' g' := H
    exact h_hom.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
  rw [degree, degree, h1]

/-- The degree of the identity map is 1. -/
theorem degree_id (hn : 0 < n) : degree (ContinuousMap.id (Sphere n)) hn = 1 := by
  dsimp only [degree, homologyMap]
  rw [TopCat.ofHom_id]
  rw [((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map_id]
  have h : (sphereTopHomologyIso n hn).inv ≫ 𝟙 (Hn (TopSphere n) n) ≫
      (sphereTopHomologyIso n hn).hom = 𝟙 (AddCommGrpCat.of ℤ) := by
    simp [CategoryTheory.Iso.inv_hom_id]
  rw [h]
  rfl

/-- The degree of a constant map is 0 (for positive n). -/
theorem degree_const (x0 : Sphere n) (hn : 0 < n) :
    degree (ContinuousMap.const (Sphere n) x0) hn = 0 := by
  have hn' : n ≠ 0 := by linarith
  dsimp only [degree, homologyMap]
  -- The constant map factors through a point
  let f : C(Sphere n, PUnit) := ContinuousMap.const (Sphere n) PUnit.unit
  let g : C(PUnit, Sphere n) := ContinuousMap.const PUnit x0
  have h_fg : (ContinuousMap.const (Sphere n) x0) = g.comp f := by
    ext x
    rfl
  rw [h_fg]
  rw [TopCat.ofHom_comp f g]
  rw [((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map_comp]
  -- H_n(PUnit) = 0 for n > 0
  haveI : TotallyDisconnectedSpace (TopCat.of PUnit) := by
    infer_instance
  have h_zero : CategoryTheory.Limits.IsZero (Hn (TopCat.of PUnit) n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (C := AddCommGrpCat) (n := n) (R := AddCommGrpCat.of ℤ) (X := TopCat.of PUnit) hn'
  -- The map through a zero object is zero
  let f' : Hn (TopSphere n) n ⟶ Hn (TopCat.of PUnit) n :=
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)
  let g' : Hn (TopCat.of PUnit) n ⟶ Hn (TopSphere n) n :=
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom g)
  have h_f'_zero : f' = 0 := h_zero.eq_zero_of_tgt f'
  have h : f' ≫ g' = 0 := by
    rw [h_f'_zero]
    simp
  rw [h]
  simp

/-- **Easy direction of Hopf degree theorem:**
    If f is nullhomotopic (homotopic to a constant map), then deg(f) = 0. -/
theorem degree_zero_of_nullhomotopic (f : C(Sphere n, Sphere n)) (hn : 0 < n)
    (h_null : ∃ (x0 : Sphere n), f.Homotopic (ContinuousMap.const (Sphere n) x0)) :
    degree f hn = 0 := by
  rcases h_null with ⟨x0, h⟩
  have h1 : degree f hn = degree (ContinuousMap.const (Sphere n) x0) hn :=
    degree_homotopy_invariant hn h
  rw [h1]
  exact degree_const x0 hn

/-- Helper: any group homomorphism φ : ℤ → ℤ satisfies φ(k) = k * φ(1). -/
lemma int_hom_mul (φ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (k : ℤ) :
    (φ : ℤ → ℤ) k = k * (φ : ℤ → ℤ) 1 := by
  let d : ℤ := (φ : ℤ → ℤ) 1
  let mul_d : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
    AddCommGrpCat.ofHom (AddMonoidHom.mulRight d)
  have h_eq : φ = mul_d := by
    apply AddCommGrpCat.int_hom_ext
    simp [mul_d, d]
  rw [h_eq]
  simp [mul_d, AddMonoidHom.mulRight]

/-- Helper: composition in AddCommGrpCat corresponds to function composition. -/
lemma addCommGrpCat_comp_apply {X Y Z : AddCommGrpCat}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ((f ≫ g) : X → Z) x = (g : Y → Z) ((f : X → Y) x) := by
  have h : ((f ≫ g) : X → Z) = (g : Y → Z) ∘ (f : X → Y) :=
    CategoryTheory.ConcreteCategory.coe_comp f g
  rw [h]
  rfl

/-- Evaluation at `1` after composing a scaled map out of `ℤ`. -/
lemma addCommGrpCat_zsmul_comp_apply_one {X : AddCommGrpCat}
    (c : ℤ) (f : AddCommGrpCat.of ℤ ⟶ X) (g : X ⟶ AddCommGrpCat.of ℤ) :
    (((c • f) ≫ g : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) : ℤ → ℤ) 1 =
      c * (((f ≫ g : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) : ℤ → ℤ) 1) := by
  rw [addCommGrpCat_comp_apply, addCommGrpCat_comp_apply]
  change (g : X → AddCommGrpCat.of ℤ) (c • (f : ℤ → X) 1) =
    c * (g : X → AddCommGrpCat.of ℤ) ((f : ℤ → X) 1)
  simp [map_zsmul]

/-- Helper: conjugating a composition is the composition of conjugations. -/
lemma conjugate_comp {A B : AddCommGrpCat} (e : A ≅ B) (f g : A ⟶ A) :
    e.inv ≫ g ≫ f ≫ e.hom = (e.inv ≫ g ≫ e.hom) ≫ (e.inv ≫ f ≫ e.hom) := by
  calc
    e.inv ≫ g ≫ f ≫ e.hom
      = e.inv ≫ (g ≫ f) ≫ e.hom := by rfl
    _ = e.inv ≫ (g ≫ (𝟙 A ≫ f)) ≫ e.hom := by
      simp [Category.id_comp]
    _ = e.inv ≫ (g ≫ (e.hom ≫ e.inv) ≫ f) ≫ e.hom := by
      rw [e.hom_inv_id]
    _ = e.inv ≫ (g ≫ e.hom ≫ e.inv ≫ f) ≫ e.hom := by
      simp [Category.assoc]
    _ = (e.inv ≫ g ≫ e.hom) ≫ (e.inv ≫ f ≫ e.hom) := by
      simp [Category.assoc]

/-- Conjugate an endomorphism of H_n(S^n) by the isomorphism H_n(S^n) ≅ ℤ. -/
def conjEndo (f_star : Hn (TopSphere n) n ⟶ Hn (TopSphere n) n) (hn : 0 < n) :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  (sphereTopHomologyIso n hn).inv ≫ f_star ≫ (sphereTopHomologyIso n hn).hom

/-- Degree expressed in terms of conjEndo. -/
lemma degree_eq_conjEndo (f : C(Sphere n, Sphere n)) (hn : 0 < n) :
    degree f hn = (conjEndo (homologyMap f) hn : ℤ → ℤ) 1 := by
  rfl

/-- The conjugated endomorphism equals degree(f) times the identity. -/
lemma conjEndo_eq_degree_smul (f : C(Sphere n, Sphere n)) (hn : 0 < n) :
    conjEndo (homologyMap f) hn = degree f hn • 𝟙 (AddCommGrpCat.of ℤ) := by
  let φ := conjEndo (homologyMap f) hn
  let d := degree f hn
  let mul_d : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
    AddCommGrpCat.ofHom (AddMonoidHom.mulRight d)
  have h_eq1 : φ = mul_d := by
    apply AddCommGrpCat.int_hom_ext
    have h : (φ : ℤ → ℤ) 1 = d := by
      rfl
    simpa [mul_d] using h
  have h_eq2 : mul_d = d • 𝟙 (AddCommGrpCat.of ℤ) := by
    apply AddCommGrpCat.ext
    intro k
    simp [mul_d, AddMonoidHom.mulRight]
    ring
  exact Eq.trans h_eq1 h_eq2

/-- Conjugation preserves composition. -/
lemma conjEndo_comp (f_star g_star : Hn (TopSphere n) n ⟶ Hn (TopSphere n) n) (hn : 0 < n) :
    conjEndo (g_star ≫ f_star) hn = conjEndo g_star hn ≫ conjEndo f_star hn :=
  conjugate_comp (sphereTopHomologyIso n hn) f_star g_star

/-- The degree of a composition is the product of degrees. -/
theorem degree_comp (f g : C(Sphere n, Sphere n)) (hn : 0 < n) :
    degree (f.comp g) hn = degree f hn * degree g hn := by
  have h1 : homologyMap (f.comp g) = homologyMap g ≫ homologyMap f := by
    simp only [homologyMap]
    rw [TopCat.ofHom_comp]
    rw [((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map_comp]
  have h2 : conjEndo (homologyMap (f.comp g)) hn = conjEndo (homologyMap g) hn ≫ conjEndo (homologyMap f) hn := by
    calc
      conjEndo (homologyMap (f.comp g)) hn
        = conjEndo (homologyMap g ≫ homologyMap f) hn := by rw [h1]
      _ = conjEndo (homologyMap g) hn ≫ conjEndo (homologyMap f) hn :=
        conjEndo_comp (homologyMap f) (homologyMap g) hn
  have h3 : degree (f.comp g) hn = (conjEndo (homologyMap (f.comp g)) hn : ℤ → ℤ) 1 :=
    degree_eq_conjEndo (f.comp g) hn
  have h4 : degree f hn = (conjEndo (homologyMap f) hn : ℤ → ℤ) 1 :=
    degree_eq_conjEndo f hn
  have h5 : degree g hn = (conjEndo (homologyMap g) hn : ℤ → ℤ) 1 :=
    degree_eq_conjEndo g hn
  rw [h3, h2]
  have h6 : ((conjEndo (homologyMap g) hn ≫ conjEndo (homologyMap f) hn) : ℤ → ℤ) 1 =
      (conjEndo (homologyMap f) hn : ℤ → ℤ) ((conjEndo (homologyMap g) hn : ℤ → ℤ) 1) :=
    addCommGrpCat_comp_apply (conjEndo (homologyMap g) hn) (conjEndo (homologyMap f) hn) 1
  rw [h6]
  have h7 : (conjEndo (homologyMap f) hn : ℤ → ℤ) ((conjEndo (homologyMap g) hn : ℤ → ℤ) 1) =
      ((conjEndo (homologyMap g) hn : ℤ → ℤ) 1) * ((conjEndo (homologyMap f) hn : ℤ → ℤ) 1) :=
    int_hom_mul (conjEndo (homologyMap f) hn) ((conjEndo (homologyMap g) hn : ℤ → ℤ) 1)
  rw [h7, h5, h4]
  ring

end SeedMathlib.AlgebraicTopology.Degree

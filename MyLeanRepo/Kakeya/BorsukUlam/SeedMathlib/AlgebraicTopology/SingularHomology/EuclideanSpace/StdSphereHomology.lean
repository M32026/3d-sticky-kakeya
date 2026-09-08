/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.EuclideanSpace.PuncturedSpace
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.H0MapIso
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.HomologyOfPoint
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.MayerVietoris.OpenCover

@[expose] public section

open Topology.EuclideanSpace

/-!
# Homology of the Standard Sphere (Concrete Version)

Prove that for the standard unit sphere Sⁿ ⊂ ℝ^{n+1}:
- H_i(Sⁿ) = 0 for 0 < i < n (vanishing below top degree)
- H_n(Sⁿ) ≅ ℤ (top degree)

Proof uses the Mayer-Vietoris sequence for the open cover by
Sⁿ \ {p} and Sⁿ \ {-p}, both of which are contractible via
stereographic projection (from Mathlib).
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial
open TopCat (toSSet)
open Metric

universe w v u

namespace AlgebraicTopology
namespace StdSphereHomology

variable (n : ℕ)

-- The standard n-sphere: the unit sphere in EuclideanSpace ℝ (Fin (n + 1))
abbrev SphereType : Type _ :=
  {x : EuclideanSpace ℝ (Fin (n + 1)) // x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}

-- Sⁿ \ {p}
def sphereMinusPoint (p : SphereType n) : Set (SphereType n) :=
  {p}ᶜ

/-!
## Contractibility of punctured sphere
-/

lemma contractible_sphereMinusPoint (p : SphereType n) :
    ContractibleSpace (sphereMinusPoint n p) := by
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
    simp
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨h_finrank⟩
  let S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  let e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin n)) :=
    stereographic' n p
  have h_source : e.source = ({p}ᶜ : Set S) :=
    stereographic'_source p
  have h_target : e.target = Set.univ :=
    stereographic'_target p
  let h1 : e.source ≃ₜ e.target := e.toHomeomorphSourceTarget
  let h2 : e.target ≃ₜ EuclideanSpace ℝ (Fin n) :=
    { toFun := fun x => (x : EuclideanSpace ℝ (Fin n))
      invFun := fun y => ⟨y, by rw [h_target] ; exact Set.mem_univ y⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := by fun_prop }
  let h3 : e.source ≃ₜ EuclideanSpace ℝ (Fin n) := h1.trans h2
  have h4 : ContractibleSpace (EuclideanSpace ℝ (Fin n)) := by exact RealTopologicalVectorSpace.contractibleSpace
  have h5 : ContractibleSpace e.source := h3.contractibleSpace
  have h_set_eq : e.source = sphereMinusPoint n p := by
    rw [h_source] ; rfl
  let h6 : e.source ≃ₜ sphereMinusPoint n p :=
    { toFun := fun x => ⟨x.val, by exact h_set_eq ▸ x.property⟩
      invFun := fun y => ⟨y.val, by exact h_set_eq.symm ▸ y.property⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact h6.symm.contractibleSpace

/-!
## Antipodal point and two-point removal
-/

/-- The antipodal point of p on the sphere. -/
def antipodal (p : SphereType n) : SphereType n :=
  ⟨-p.val, by
    have h1 : ‖(-p.val : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖p.val‖ := by
      rw [norm_neg]
    have h2 : dist p.val (0 : EuclideanSpace ℝ (Fin (n + 1))) = 1 := p.property
    have h3 : ‖p.val‖ = 1 := by simp
    have h4 : ‖(-p.val : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
      rw [h1, h3]
    have h5 : dist (-p.val) (0 : EuclideanSpace ℝ (Fin (n + 1))) = 1 := by
      simp [dist_zero_right]
    exact h5⟩

lemma antipodal_ne_self (p : SphereType n) :
    antipodal n p ≠ p := by
  intro h
  have h2 : -(p.val : EuclideanSpace ℝ (Fin (n + 1))) = p.val :=
    congr_arg Subtype.val h
  have h3 : (2 : ℝ) • p.val = 0 := by
    have h31 : p.val + p.val = 0 := by
      calc
        p.val + p.val = p.val + (-p.val) := by rw [h2]
        _ = 0 := by simp
    simpa [two_smul] using h31
  have h4 : ‖(2 : ℝ) • p.val‖ = 0 := by
    rw [h3] ; simp
  have h5 : ‖(2 : ℝ) • p.val‖ = (2 : ℝ) * ‖p.val‖ := by
    rw [norm_smul] ; rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have h6 : ‖p.val‖ = 1 := by
    have h7 : dist p.val (0 : EuclideanSpace ℝ (Fin (n + 1))) = 1 := p.property
    simp
  rw [h5, h6] at h4
  ; norm_num at h4

-- Sⁿ \ {p, antipodal p}
def sphereMinusTwoPoints (p : SphereType n) : Set (SphereType n) :=
  sphereMinusPoint n p ∩ sphereMinusPoint n (antipodal n p)

lemma isOpen_sphereMinusPoint (p : SphereType n) :
    IsOpen (sphereMinusPoint n p) :=
  isOpen_compl_singleton

lemma cover_sphere_twoPoints (p : SphereType n) :
    (Set.univ : Set (SphereType n)) ⊆
      sphereMinusPoint n p ∪ sphereMinusPoint n (antipodal n p) := by
  intro x _
  by_cases h : x = p
  · right
    have h_ne : x ≠ antipodal n p := by
      intro h_eq
      have h_contra : antipodal n p = p := by
        rw [←h_eq, h]
      exact antipodal_ne_self n p h_contra
    exact Set.mem_compl h_ne
  · left
    exact Set.mem_compl h

/-!
## Homology of twice-punctured sphere

Sⁿ \ {p, -p} is homeomorphic to ℝⁿ \ {0}, which is homotopy equivalent
to Sⁿ⁻¹. Hence their singular homology groups are isomorphic.
-/

variable (p : SphereType n)

/-- Homeomorphism from Sⁿ \ {p} to ℝⁿ via stereographic projection. -/
noncomputable def stereographicHomeo :
    sphereMinusPoint n p ≃ₜ EuclideanSpace ℝ (Fin n) := by
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
    simp
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨h_finrank⟩
  let S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  let e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin n)) :=
    stereographic' n p
  have h_source : e.source = sphereMinusPoint n p := by
    rw [stereographic'_source p] ; rfl
  have h_target : e.target = Set.univ := stereographic'_target p
  let h1 : e.source ≃ₜ e.target := e.toHomeomorphSourceTarget
  let h2 : e.target ≃ₜ EuclideanSpace ℝ (Fin n) :=
    { toFun := fun x => (x : EuclideanSpace ℝ (Fin n))
      invFun := fun y => ⟨y, by rw [h_target] ; exact Set.mem_univ y⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := by fun_prop }
  let h3 : e.source ≃ₜ EuclideanSpace ℝ (Fin n) := h1.trans h2
  let h4 : e.source ≃ₜ sphereMinusPoint n p :=
    { toFun := fun x => ⟨x.val, by exact h_source ▸ x.property⟩
      invFun := fun y => ⟨y.val, by exact h_source.symm ▸ y.property⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact h4.symm.trans h3

/-- The image of the antipodal point under stereographic projection. -/
noncomputable def antipodalImage : EuclideanSpace ℝ (Fin n) :=
  stereographicHomeo n p ⟨antipodal n p, Set.mem_compl (antipodal_ne_self n p)⟩

/-- Homeomorphism from Sⁿ \ {p, -p} to ℝⁿ \ {antipodalImage}. -/
noncomputable def twicePuncturedToPuncturedAtImage :
    {x : SphereType n // x ∈ sphereMinusTwoPoints n p} ≃ₜ
    {y : EuclideanSpace ℝ (Fin n) // y ≠ antipodalImage n p} := by
  let e := stereographicHomeo n p
  let q_in_U : sphereMinusPoint n p :=
    ⟨antipodal n p, Set.mem_compl (antipodal_ne_self n p)⟩
  let y0 : EuclideanSpace ℝ (Fin n) := e q_in_U
  have h_y0_eq : y0 = antipodalImage n p := by rfl
  let e' : {x : sphereMinusPoint n p // x ≠ q_in_U} ≃ₜ
      {y : EuclideanSpace ℝ (Fin n) // y ≠ y0} := by
    refine' {
      toFun := fun x => ⟨e x.val, by
        intro h
        have h' : x.val = q_in_U := by
          exact e.injective h
        exact x.property h'⟩,
      invFun := fun y => ⟨e.symm y.val, by
        intro h
        have h' : y.val = y0 := by
          calc
            y.val = e (e.symm y.val) := (e.right_inv y.val).symm
            _ = e q_in_U := by rw [h]
            _ = y0 := by rfl
        exact y.property h'⟩,
      left_inv := by intro x; ext; simp,
      right_inv := by intro y; ext; simp,
      continuous_toFun := by
        have h : Continuous (fun (x : {x : sphereMinusPoint n p // x ≠ q_in_U}) => e x.val) :=
          e.continuous_toFun.comp continuous_subtype_val
        exact Continuous.subtype_mk h _,
      continuous_invFun := by
        have h : Continuous (fun (y : {y : EuclideanSpace ℝ (Fin n) // y ≠ y0}) => e.symm y.val) :=
          e.continuous_invFun.comp continuous_subtype_val
        exact Continuous.subtype_mk h _
    }
  -- Now we need to relate {x : SphereType n // x ∈ sphereMinusTwoPoints n p}
  -- with {x : sphereMinusPoint n p // x ≠ q_in_U}
  let h_set_eq : ∀ (x : SphereType n), x ∈ sphereMinusTwoPoints n p ↔
      (∃ (hx : x ∈ sphereMinusPoint n p), (⟨x, hx⟩ : sphereMinusPoint n p) ≠ q_in_U) := by
    intro x
    simp only [sphereMinusTwoPoints, Set.mem_inter_iff, sphereMinusPoint, Set.mem_compl_iff]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine' ⟨hx1, _⟩
      intro h_eq
      have h : x = antipodal n p := by
        exact congr_arg Subtype.val h_eq
      exact hx2 h
    · rintro ⟨hx1, hx2⟩
      constructor
      · exact hx1
      · intro h_eq
        have h : (⟨x, hx1⟩ : sphereMinusPoint n p) = q_in_U := by
          apply Subtype.ext
          exact h_eq
        exact hx2 h
  let h1 : {x : SphereType n // x ∈ sphereMinusTwoPoints n p} ≃ₜ
      {x : sphereMinusPoint n p // x ≠ q_in_U} := by
    refine' {
      toFun := fun x => ⟨⟨x.val, (h_set_eq x.val).mp x.property |>.choose⟩,
        (h_set_eq x.val).mp x.property |>.choose_spec⟩,
      invFun := fun y => ⟨y.val.val, (h_set_eq y.val.val).mpr ⟨y.val.property, y.property⟩⟩,
      left_inv := by intro x; ext; rfl,
      right_inv := by intro y; ext; rfl,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop
    }
  let h2 : {y : EuclideanSpace ℝ (Fin n) // y ≠ y0} ≃ₜ
      {y : EuclideanSpace ℝ (Fin n) // y ≠ antipodalImage n p} := by
    refine' {
      toFun := fun y => ⟨y.val, by
        intro h_contra
        have h : y.val = y0 := by
          exact h_contra.trans h_y0_eq.symm
        exact y.property h⟩,
      invFun := fun y => ⟨y.val, by
        intro h_contra
        have h : y.val = antipodalImage n p := by
          exact h_contra.trans h_y0_eq
        exact y.property h⟩,
      left_inv := by intro y; ext; rfl,
      right_inv := by intro y; ext; rfl,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop
    }
  exact h1.trans (e'.trans h2)

/-- Translation homeomorphism: ℝⁿ \ {y} ≅ ℝⁿ \ {0} for any point y. -/
noncomputable def translationPuncturedHomeo (y : EuclideanSpace ℝ (Fin n)) :
    {x : EuclideanSpace ℝ (Fin n) // x ≠ y} ≃ₜ
    {x : EuclideanSpace ℝ (Fin n) // x ≠ 0} := by
  refine' {
    toFun := fun x => ⟨x.val - y, by
      intro h
      have h' : x.val = y := by simpa [sub_eq_zero] using h
      exact x.property h'⟩,
    invFun := fun x => ⟨x.val + y, by
      intro h
      have h' : x.val = 0 := by simpa [add_eq_zero_iff_eq_neg] using h
      exact x.property h'⟩,
    left_inv := by intro x; ext; simp,
    right_inv := by intro y; ext; simp,
    continuous_toFun := by fun_prop,
    continuous_invFun := by fun_prop
  }

/-- Homotopy equivalence between twice-punctured Sⁿ and Sⁿ⁻¹. -/
noncomputable def twicePuncturedSphereHomotopyEquiv (hn : 0 < n) :
    ContinuousMap.HomotopyEquiv
      {x : SphereType n // x ∈ sphereMinusTwoPoints n p}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let e1 := twicePuncturedToPuncturedAtImage n p
  let e2 := translationPuncturedHomeo n (antipodalImage n p)
  let e12 : {x : SphereType n // x ∈ sphereMinusTwoPoints n p} ≃ₜ
      {x : EuclideanSpace ℝ (Fin n) // x ≠ 0} := e1.trans e2
  letI : Nonempty (Fin n) := by
    exact Fin.pos_iff_nonempty.mp hn
  let e3 : ContinuousMap.HomotopyEquiv
      {x : EuclideanSpace ℝ (Fin n) // x ≠ 0}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    puncturedSphereHomotopyEquiv (m := n)
  exact e12.toHomotopyEquiv.trans e3

/-!
## Mayer-Vietoris for the sphere

We apply the MV boundary isomorphism to the open cover
U = Sⁿ \ {p}, V = Sⁿ \ {-p} of Sⁿ.
-/

variable (p : SphereType n)
variable (hn_pos : 0 < n)

-- Open cover data
def U_set : Set (SphereType n) := sphereMinusPoint n p
def V_set : Set (SphereType n) := sphereMinusPoint n (antipodal n p)
def UV_set : Set (SphereType n) := sphereMinusTwoPoints n p

lemma hU_open : IsOpen (U_set n p) := isOpen_compl_singleton
lemma hV_open : IsOpen (V_set n p) := isOpen_compl_singleton

lemma hcover : (Set.univ : Set (SphereType n)) ⊆ U_set n p ∪ V_set n p :=
  cover_sphere_twoPoints n p

-- Contractibility implies vanishing of positive-degree homology
lemma hU_vanishing (i : ℕ) (hi_pos : 0 < i) :
    IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i
      (TwoSubspaces.twoSubspacesOfOpens (U_set n p) (V_set n p)).U) := by
  have h_contr : ContractibleSpace (U_set n p) := contractible_sphereMinusPoint n p
  exact isZero_singularHomologyOfContractible AddCommGrpCat i (AddCommGrpCat.of ℤ) (ne_of_gt hi_pos)

lemma hV_vanishing (i : ℕ) (hi_pos : 0 < i) :
    IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i
      (TwoSubspaces.twoSubspacesOfOpens (U_set n p) (V_set n p)).V) := by
  have h_contr : ContractibleSpace (V_set n p) := contractible_sphereMinusPoint n (antipodal n p)
  exact isZero_singularHomologyOfContractible AddCommGrpCat i (AddCommGrpCat.of ℤ) (ne_of_gt hi_pos)

/-- MV boundary isomorphism for the sphere: H_{i+1}(Sⁿ) ≅ H_i(Sⁿ \ {p, -p}) for i ≥ 1. -/
noncomputable def sphere_mv_boundaryIso (i : ℕ) (hi_pos : 0 < i) :
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (i + 1)
      (TopCat.of (SphereType n)) ≅
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i
      (TwoSubspaces.twoSubspacesOfOpens (U_set n p) (V_set n p)).UV :=
  TwoSubspaces.mayerVietoris_boundaryIso_openCover
    (U_set n p) (V_set n p)
    (hU_open n p) (hV_open n p)
    (hcover n p)
    i
    (hU_vanishing n p i hi_pos)
    (hV_vanishing n p i hi_pos)
    (hU_vanishing n p (i + 1) (by linarith))
    (hV_vanishing n p (i + 1) (by linarith))

/-!
## Inductive computation of sphere homology

We prove by induction on n:
- H_i(Sⁿ) = 0 for 0 < i < n (vanishing below top degree)
- H_n(Sⁿ) ≅ ℤ (top degree)
-/

variable (n : ℕ)

/-- Homology isomorphism: H_i(S^{n+1} \ {p, -p}) ≅ H_i(Sⁿ). -/
noncomputable def twicePuncturedHomologyIso (p : SphereType (n + 1)) (i : ℕ) :
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i
      (TwoSubspaces.twoSubspacesOfOpens
        (U_set (n + 1) p) (V_set (n + 1) p)).UV ≅
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i
      (TopCat.of (SphereType n)) := by
  let ts_UV := (TwoSubspaces.twoSubspacesOfOpens
    (U_set (n + 1) p) (V_set (n + 1) p)).UV
  let e_homotopy : ContinuousMap.HomotopyEquiv
      {x : SphereType (n + 1) // x ∈ sphereMinusTwoPoints (n + 1) p}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    twicePuncturedSphereHomotopyEquiv (n + 1) p (by linarith)
  exact singularHomologyIsoOfHomotopyEquiv AddCommGrpCat i (AddCommGrpCat.of ℤ)
    ts_UV
    (TopCat.of (SphereType n))
    (by exact e_homotopy)

/-- The standard n-sphere is non-empty. -/
instance nonempty_sphereType : Nonempty (SphereType n) := by
  let i₀ : Fin (n + 1) := ⟨0, by linarith⟩
  let v := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) i₀
  have h_norm : ‖v‖ = 1 := by
    have h_orthonormal : Orthonormal ℝ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) := by
      exact OrthonormalBasis.orthonormal (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)
    exact h_orthonormal.1 i₀
  have h_sphere : dist v (0 : EuclideanSpace ℝ (Fin (n + 1))) = 1 := by
    simpa [dist_zero_right] using h_norm
  exact ⟨⟨v, h_sphere⟩⟩

/-- Combined: H_{i+1}(S^{n+1}) ≅ H_i(Sⁿ) for i ≥ 1. -/
noncomputable def sphere_homology_shift (p : SphereType (n + 1)) (i : ℕ) (hi_pos : 0 < i) :
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (i + 1)
      (TopCat.of (SphereType (n + 1))) ≅
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i
      (TopCat.of (SphereType n)) :=
  (sphere_mv_boundaryIso (n + 1) p i hi_pos) ≪≫
    twicePuncturedHomologyIso n p i

/-!
### H₁(Sⁿ) = 0 for n ≥ 2

Using the Mayer-Vietoris long exact sequence at the H₁/H₀ level:
- H₁(U) = H₁(V) = 0 (both contractible) ⇒ δ : H₁(small) → H₀(UV) is injective
- UV is path-connected for n ≥ 2 ⇒ H₀(UV) → H₀(U)⊕H₀(V) is injective
- By exactness, im(δ) = ker(H₀(UV) → H₀(U)⊕H₀(V)) = 0
- δ injective with image 0 ⇒ H₁(small) = 0
- Small chain theorem ⇒ H₁(Sⁿ) = 0
-/

variable (n : ℕ)

/-- For n ≥ 2, the twice-punctured n-sphere Sⁿ \ {p, -p} is path-connected. -/
theorem twicePunctured_pathConnected (p : SphereType n) (hn : 2 ≤ n) :
    PathConnectedSpace {x : SphereType n // x ∈ sphereMinusTwoPoints n p} := by
  have hn_pos : 0 < n := by linarith
  let e1 := twicePuncturedToPuncturedAtImage n p
  let e2 := translationPuncturedHomeo n (antipodalImage n p)
  let e : {x : SphereType n // x ∈ sphereMinusTwoPoints n p} ≃ₜ
      {x : EuclideanSpace ℝ (Fin n) // x ≠ (0 : EuclideanSpace ℝ (Fin n))} :=
    e1.trans e2
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) :=
      finrank_euclideanSpace (𝕜 := ℝ)
    rw [h]
    simp
  have h_one_lt_finrank : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [h_finrank] ; linarith
  have h_one_lt_rank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) :=
    Module.one_lt_rank_of_one_lt_finrank h_one_lt_finrank
  have h_pc_set : IsPathConnected ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    isPathConnected_compl_singleton_of_one_lt_rank h_one_lt_rank (0 : EuclideanSpace ℝ (Fin n))
  have h_pc_subtype : PathConnectedSpace {x : EuclideanSpace ℝ (Fin n) // x ≠ (0 : EuclideanSpace ℝ (Fin n))} :=
    isPathConnected_iff_pathConnectedSpace.mp h_pc_set
  have h_main : PathConnectedSpace {x : SphereType n // x ∈ sphereMinusTwoPoints n p} := by
    let e' : {x : EuclideanSpace ℝ (Fin n) // x ≠ (0 : EuclideanSpace ℝ (Fin n))} ≃ₜ
        {x : SphereType n // x ∈ sphereMinusTwoPoints n p} := e.symm
    have h_univ : IsPathConnected (Set.univ : Set {x : EuclideanSpace ℝ (Fin n) // x ≠ (0 : EuclideanSpace ℝ (Fin n))}) :=
      pathConnectedSpace_iff_univ.mp h_pc_subtype
    have h_image : IsPathConnected (Set.univ : Set {x : SphereType n // x ∈ sphereMinusTwoPoints n p}) := by
      have h4 : e' '' Set.univ = Set.univ := by simp
      have h5 : IsPathConnected (e' '' Set.univ) := e'.isPathConnected_image.mpr h_univ
      rw [h4] at h5
      exact h5
    exact pathConnectedSpace_iff_univ.mpr h_image
  exact h_main

/-- H₁(Sⁿ) = 0 for n ≥ 2. -/
theorem stdSphere_h1_zero (n : ℕ) (hn : 2 ≤ n) :
    IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1 (TopCat.of (SphereType n))) := by
  have hn_pos : 0 < n := by linarith
  let p : SphereType n := Classical.arbitrary _
  let ts := TwoSubspaces.twoSubspacesOfOpens (U_set n p) (V_set n p)
  have hcover' : (Set.univ : Set (SphereType n)) ⊆ U_set n p ∪ V_set n p :=
    hcover n p
  have h_jU_emb : Topology.IsEmbedding ts.jU :=
    TwoSubspaces.twoSubspacesOfOpens_jU_emb (U_set n p) (V_set n p)
  have h_jV_emb : Topology.IsEmbedding ts.jV :=
    TwoSubspaces.twoSubspacesOfOpens_jV_emb (U_set n p) (V_set n p)
  have h_pullback : IsPullback ts.iU ts.iV ts.jU ts.jV :=
    TwoSubspaces.twoSubspacesOfOpens_isPullback (U_set n p) (V_set n p)
  have h_range_jU : Set.range ts.jU = U_set n p := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have h_y : y.val ∈ U_set n p := y.prop
      have h_eq : (ts.jU y) = x := hy
      have h_x_in_U : x ∈ U_set n p := by
        have h1 : (ts.jU y) = y.val := by rfl
        have h2 : x = y.val := h_eq.symm.trans h1
        rw [h2]
        exact h_y
      exact h_x_in_U
    · intro hx
      have h_y : ∃ (y : {x // x ∈ U_set n p}), (ts.jU y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩ ; rfl
      rcases h_y with ⟨y, hy⟩
      exact ⟨y, hy⟩
  have h_range_jV : Set.range ts.jV = V_set n p := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have h_y : y.val ∈ V_set n p := y.prop
      have h_eq : (ts.jV y) = x := hy
      have h_x_in_V : x ∈ V_set n p := by
        have h1 : (ts.jV y) = y.val := by rfl
        have h2 : x = y.val := h_eq.symm.trans h1
        rw [h2]
        exact h_y
      exact h_x_in_V
    · intro hx
      have h_y : ∃ (y : {x // x ∈ V_set n p}), (ts.jV y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩ ; rfl
      rcases h_y with ⟨y, hy⟩
      exact ⟨y, hy⟩
  haveI hMono_jU : Mono ts.jU := by
    rw [TopCat.mono_iff_injective ts.jU]
    exact h_jU_emb.injective
  haveI hMono_jV : Mono ts.jV := by
    rw [TopCat.mono_iff_injective ts.jV]
    exact h_jV_emb.injective
  have h_iU_emb : Topology.IsEmbedding ts.iU := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    have h_subset : (U_set n p ∩ V_set n p : Set (SphereType n)) ⊆ U_set n p := by simp
    have h_main : Topology.IsEmbedding (Set.inclusion h_subset) := Topology.IsEmbedding.inclusion h_subset
    exact h_main
  haveI hMono_iU : Mono ts.iU := by
    rw [TopCat.mono_iff_injective ts.iU]
    exact h_iU_emb.injective
  have h_dw_pullback : DegreewisePullbackAssumption ts :=
    degreewisePullback_of_isPullback_of_embeddings ts h_pullback h_jU_emb h_jV_emb
  have hS : (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).ShortExact :=
    mvSES_shortExact' AddCommGrpCat (AddCommGrpCat.of ℤ) ts h_dw_pullback
  have h_mid_1 : IsZero ((mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₂.homology 1) :=
    isZero_biprod_homology (K := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U)
      (L := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.V) (n := 1)
      (hU_vanishing n p 1 (by norm_num))
      (hV_vanishing n p 1 (by norm_num))
  have h_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
    simp [ComplexShape.down_Rel]
  have h_exact3 := hS.homology_exact₃ 1 0 h_rel10
  have h1_g_zero : HomologicalComplex.homologyMap (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).g 1 = 0 := by
    have h : ∀ (f g : (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₂.homology 1 ⟶
        (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₃.homology 1), f = g :=
      h_mid_1.eq_of_src
    exact h _ _
  have hδ_mono : Mono (hS.δ 1 0 h_rel10) := h_exact3.mono_g h1_g_zero
  have h_small_chain_1 :
      IsIso (HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) 1) :=
    TwoSubspaces.smallChainTheorem_TwoSubspaces_pseudoMetric ts rfl h_jU_emb h_jV_emb
      (by rw [h_range_jU]; exact hU_open n p)
      (by rw [h_range_jV]; exact hV_open n p)
      (by rw [h_range_jU, h_range_jV]; exact hcover') 0
  -- Step 1: H₀(f) is mono, using path-connectedness of UV and U
  have h_uv_pc : PathConnectedSpace ts.UV := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    have h_set_eq : (U_set n p ∩ V_set n p : Set (SphereType n)) = sphereMinusTwoPoints n p := by rfl
    have h1 : IsPathConnected (sphereMinusTwoPoints n p) :=
      isPathConnected_iff_pathConnectedSpace.mpr (twicePunctured_pathConnected n p hn)
    have h2 : IsPathConnected (U_set n p ∩ V_set n p : Set (SphereType n)) := by
      rw [h_set_eq] ; exact h1
    exact isPathConnected_iff_pathConnectedSpace.mp h2
  have h_U_contr : ContractibleSpace ts.U := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    exact contractible_sphereMinusPoint n p
  let f0 := HomologicalComplex.homologyMap (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).f 0
  let iU_star := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ) |>.map ts.iU
  have h1_comp : mvMapF AddCommGrpCat (AddCommGrpCat.of ℤ) ts ≫ biprod.fst = iU_star := by
    simp [mvMapF, Preadditive.sub_comp] ; abel
  have h_f0_comp : f0 ≫ HomologicalComplex.homologyMap (biprod.fst :
      (singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U) ⊞
      (singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.V) ⟶
      singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U) 0 =
      HomologicalComplex.homologyMap iU_star 0 := by
    dsimp only [f0]
    let S := mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts
    let π₁ : (singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U) ⊞
        (singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.V) ⟶
        singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U := biprod.fst
    have h_mvF : S.f = mvMapF AddCommGrpCat (AddCommGrpCat.of ℤ) ts := by rfl
    have h_eq1 : HomologicalComplex.homologyMap S.f 0 ≫ HomologicalComplex.homologyMap π₁ 0 =
        HomologicalComplex.homologyMap (S.f ≫ π₁) 0 := by
      exact (HomologicalComplex.homologyMap_comp S.f π₁ 0).symm
    have h_eq2 : HomologicalComplex.homologyMap (S.f ≫ π₁) 0 =
        HomologicalComplex.homologyMap (mvMapF AddCommGrpCat (AddCommGrpCat.of ℤ) ts ≫ π₁) 0 := by
      exact congr_arg (fun (x : _) => HomologicalComplex.homologyMap (x ≫ π₁) 0) h_mvF
    have h_eq3 : HomologicalComplex.homologyMap (mvMapF AddCommGrpCat (AddCommGrpCat.of ℤ) ts ≫ π₁) 0 =
        HomologicalComplex.homologyMap iU_star 0 := by
      rw [h1_comp]
    rw [h_eq1, h_eq2, h_eq3]
  have h_iso_iU : IsIso (HomologicalComplex.homologyMap iU_star 0) :=
    isIso_singularHomologyMap_zero_of_pathConnected (AddCommGrpCat.of ℤ) ts.iU
  have h_mono_iU : Mono (HomologicalComplex.homologyMap iU_star 0) := by
    let f := HomologicalComplex.homologyMap iU_star 0
    have h_iso : IsIso f := h_iso_iU
    let g := inv f
    have h_hom_inv : f ≫ g = 𝟙 _ := IsIso.hom_inv_id f
    rw [Preadditive.mono_iff_cancel_zero f]
    intro Z h hz
    have h1 : h ≫ f ≫ g = 0 := by
      calc
        h ≫ f ≫ g = (h ≫ f) ≫ g := by rw [Category.assoc]
        _ = 0 ≫ g := by rw [hz]
        _ = 0 := by simp
    have h2 : h ≫ (f ≫ g) = 0 := h1
    have h3 : h ≫ 𝟙 _ = 0 := by rw [h_hom_inv] at h2; exact h2
    simpa using h3
  have h_mono_f0 : Mono f0 := by
    have h_eq : f0 ≫ HomologicalComplex.homologyMap (biprod.fst :
        (singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U) ⊞
        (singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.V) ⟶
        singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U) 0 =
        HomologicalComplex.homologyMap iU_star 0 := h_f0_comp
    rw [Preadditive.mono_iff_cancel_zero f0]
    intro Z k hk
    have h_kf : k ≫ f0 = 0 := hk
    have h1 : (k ≫ f0) ≫ HomologicalComplex.homologyMap (biprod.fst : _) 0 = 0 := by
      rw [h_kf, zero_comp]
    have h2 : k ≫ (f0 ≫ HomologicalComplex.homologyMap (biprod.fst : _) 0) = 0 := by
      rwa [Category.assoc] at h1
    have h3 : k ≫ HomologicalComplex.homologyMap iU_star 0 = 0 := by
      rw [h_eq] at h2
      exact h2
    have h4 : ∀ (Z' : _) (g : Z' ⟶ _), g ≫ HomologicalComplex.homologyMap iU_star 0 = 0 → g = 0 :=
      (Preadditive.mono_iff_cancel_zero (HomologicalComplex.homologyMap iU_star 0)).mp h_mono_iU
    exact h4 Z k h3
  -- Step 2: From exactness at H₀(X₁), δ = 0 since H₀(f) is mono
  have h_exact1 := hS.homology_exact₁ 1 0 h_rel10
  have hδ_zero : hS.δ 1 0 h_rel10 = 0 := by
    have h_iff : Mono (HomologicalComplex.homologyMap (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).f 0) ↔
        hS.δ 1 0 h_rel10 = 0 := h_exact1.mono_g_iff
    exact h_iff.mp h_mono_f0
  -- Step 3: δ is mono and δ = 0, so H₁(X₃) = 0
  have h1_small : IsZero ((mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₃.homology 1) := by
    have hδ : Mono (hS.δ 1 0 h_rel10) := hδ_mono
    rw [hδ_zero] at hδ
    exact IsZero.of_mono_eq_zero (hS.δ 1 0 h_rel10) hδ_zero
  -- Step 4: By small chain theorem, H₁(X) ≅ H₁(X₃), so H₁(X) = 0
  have h_small_iso : (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₃.homology 1 ≅
      singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1 ts.X := by
    let f := HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) 1
    have h : IsIso f := h_small_chain_1
    have h_out : ∃ (g : singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1 ts.X ⟶
        (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₃.homology 1),
        f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := h.out
    let g := Classical.choose h_out
    have hg : f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := Classical.choose_spec h_out
    exact ⟨f, g, hg.1, hg.2⟩
  have h_final : IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1 ts.X) :=
    IsZero.of_iso h1_small h_small_iso.symm
  have h_goal : ts.X = TopCat.of (SphereType n) := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
  rw [h_goal] at h_final
  exact h_final

/-!
### Vanishing of homology below top degree

We prove H_i(Sⁿ) = 0 for 0 < i < n by induction on n,
using the H₁ = 0 base case and the degree-shifting isomorphism.
-/

/-- Vanishing for degrees ≥ 2: if H₁(Sⁿ) = 0 for all n ≥ 2, then H_i(Sⁿ) = 0 for all 0 < i < n. -/
theorem stdSphere_vanishing_of_h1_zero
    (h_h1_zero : ∀ n, 2 ≤ n → IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1 (TopCat.of (SphereType n)))) :
    ∀ (n : ℕ) (i : ℕ), 0 < i → i < n →
      IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i (TopCat.of (SphereType n))) := by
  intro n
  induction n with
  | zero =>
    intro i hi_pos hi_lt
    exfalso
    linarith
  | succ n ih =>
    let p : SphereType (n + 1) := Classical.arbitrary _
    intro i hi_pos hi_lt
    by_cases h_i1 : i = 1
    · -- Case i = 1
      rw [h_i1]
      exact h_h1_zero (n + 1) (by linarith)
    · -- Case i ≥ 2
      have h_i_ge2 : 2 ≤ i := by omega
      have h_i_minus1_pos : 0 < i - 1 := by omega
      have h_i_minus1_lt : i - 1 < n := by omega
      have h_iso : singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i
          (TopCat.of (SphereType (n + 1))) ≅
          singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (i - 1)
          (TopCat.of (SphereType n)) := by
        have h_i' : i = (i - 1) + 1 := by omega
        rw [h_i']
        exact sphere_homology_shift n p (i - 1) h_i_minus1_pos
      exact IsZero.of_iso (ih (i - 1) h_i_minus1_pos h_i_minus1_lt) h_iso

/-- **Vanishing below top degree:** H_i(Sⁿ) = 0 for all 0 < i < n. -/
theorem stdSphere_vanishing :
    ∀ (n : ℕ) (i : ℕ), 0 < i → i < n →
      IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) i (TopCat.of (SphereType n))) :=
  stdSphere_vanishing_of_h1_zero (fun n hn => stdSphere_h1_zero n hn)

end StdSphereHomology
end AlgebraicTopology
end

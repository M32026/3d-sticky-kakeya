/-
Transfer sequence for the antipodal action on S^n with Z/2 coefficients.

This file proves the key algebraic fact: for each degree k,
the map p = 1 + a_# on singular chains satisfies im(p) = ker(p).

It then defines the image subcomplex D_* and proves the short exact sequence
0 → D_* → C_*(S^n; Z/2) → D_* → 0.
-/
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.Degree.Homology
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range

noncomputable section

namespace BorsukUlamBackup

open Metric AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open Vendored.AlgebraicTopology.Degree
open Finsupp

variable {n : ℕ}

abbrev Z2 := ZMod 2

--! ########## Part 1: Free involution lemma on Finsupp ##########

variable {α : Type*} [DecidableEq α]

/-- A free involution on α: a^2 = id and no fixed points. -/
structure FreeInvolution (α : Type*) where
  a : α ≃ α
  sq : a.trans a = Equiv.refl α
  free : ∀ x, a x ≠ x

variable (h : FreeInvolution α)

/-- The action of the involution on finitely supported functions. -/
def involutionAction : (α →₀ Z2) →ₗ[Z2] (α →₀ Z2) :=
  { toFun := fun f => Finsupp.mapDomain h.a f
    map_add' := by
      intro f g
      exact mapDomain_add
    map_smul' := by
      intro c f
      exact mapDomain_smul c f }

/-- Evaluation of involution action: (a·f)(x) = f(a(x)). -/
lemma involutionAction_eval (f : α →₀ Z2) (x : α) :
    (involutionAction h f) x = f (h.a x) := by
  have h_a2 : h.a.symm = h.a := by
    ext y
    have h4 : h.a (h.a y) = y := by
      simpa [Equiv.trans_apply] using congr_fun (congr_arg Equiv.toFun h.sq) y
    have h5 : h.a.symm y = h.a y := by
      rw [Equiv.symm_apply_eq]; exact h4.symm
    exact h5
  have h_map : (Finsupp.mapDomain h.a f) x = f (h.a.symm x) := by
    exact mapDomain_equiv_apply f x
  have h_eq : (involutionAction h f) x = (Finsupp.mapDomain h.a f) x := by rfl
  rw [h_eq, h_map, h_a2]

/-- p = 1 + a on finitely supported functions. -/
def pMap : (α →₀ Z2) →ₗ[Z2] (α →₀ Z2) :=
  { toFun := fun f => f + involutionAction h f
    map_add' := by intro f g; have h_ia := (involutionAction h).map_add f g; simp [h_ia, add_assoc, add_comm, add_left_comm]
    map_smul' := by intro c f; have h_ia := (involutionAction h).map_smul c f; simp [h_ia, smul_add] }

/-- p^2 = 0 in characteristic 2. -/
lemma pMap_squared : (pMap h).comp (pMap h) = 0 := by
  apply LinearMap.ext; intro f; apply Finsupp.ext; intro x
  have h_a2 : ∀ y, h.a (h.a y) = y := by
    intro y; simpa [Equiv.trans_apply] using congr_fun (congr_arg Equiv.toFun h.sq) y
  have h4 : ∀ (z : Z2), z + z = 0 := by intro z; fin_cases z <;> decide
  have h_comp : ((pMap h).comp (pMap h)) f = (pMap h) ((pMap h) f) := by rfl
  rw [h_comp]
  have h_eval : (pMap h ((pMap h) f)) x = f x + f (h.a x) + (f (h.a x) + f x) := by
    simp [pMap, involutionAction_eval h, h_a2] <;> rfl
  rw [h_eval]
  have h' : f x + f (h.a x) + (f (h.a x) + f x) = (f x + f x) + (f (h.a x) + f (h.a x)) := by
    simp [add_assoc, add_comm, add_left_comm]
  rw [h', h4 (f x), h4 (f (h.a x))] <;> simp

/-- im(p) ⊆ ker(p). -/
lemma range_pMap_subset_ker : LinearMap.range (pMap h) ≤ LinearMap.ker (pMap h) := by
  intro x hx; rcases hx with ⟨y, rfl⟩
  have h9 : (pMap h) ((pMap h) y) = 0 := by
    have h10 : ((pMap h).comp (pMap h)) y = 0 := by rw [pMap_squared h] <;> rfl
    exact h10
  exact h9

/-- ker(p) ⊆ im(p). -/
lemma ker_pMap_subset_range : LinearMap.ker (pMap h) ≤ LinearMap.range (pMap h) := by
  intro f hf
  have h4 : ∀ (x : Z2), x + x = 0 := by intro x; fin_cases x <;> decide
  have h_ff : f + f = 0 := by ext z; exact h4 (f z)
  have h2 : f + involutionAction h f = 0 := hf
  have h1 : involutionAction h f = f := by
    calc involutionAction h f
      = 0 + involutionAction h f := by simp
    _ = (f + f) + involutionAction h f := by rw [h_ff]
    _ = f + (f + involutionAction h f) := by simp [add_assoc]
    _ = f + 0 := by rw [h2]
    _ = f := by simp
  have h_inv : ∀ (x : α), f (h.a x) = f x := by
    intro x; have h3 : (involutionAction h f) x = f x := by rw [h1]
    rw [involutionAction_eval h f x] at h3; exact h3
  classical
  let s : Setoid α :=
    { r := fun x y => x = y ∨ x = h.a y
      iseqv := by
        refine' ⟨_, _, _⟩
        · intro x; exact Or.inl rfl
        · intro x y hxy
          rcases hxy with (rfl | hxy)
          · exact Or.inl rfl
          · have h4 : h.a (h.a y) = y := by simpa [Equiv.trans_apply] using congr_fun (congr_arg Equiv.toFun h.sq) y
            have h51 : h.a x = h.a (h.a y) := by rw [hxy]
            have h5 : h.a x = y := by rw [h51, h4]
            exact Or.inr h5.symm
        · intro x y z hxy hyz
          rcases hxy with (rfl | hxy)
          · rcases hyz with (rfl | hyz)
            · exact Or.inl rfl
            · exact Or.inr hyz
          · rcases hyz with (rfl | hyz)
            · exact Or.inr hxy
            · have h4 : h.a (h.a z) = z := by simpa [Equiv.trans_apply] using congr_fun (congr_arg Equiv.toFun h.sq) z
              have h51 : x = h.a y := hxy
              have h52 : y = h.a z := hyz
              have h53 : h.a y = h.a (h.a z) := by rw [h52]
              have h5 : x = z := by rw [h51, h53, h4]
              exact Or.inl h5 }
  let P : Quotient s → Prop := fun q => ∃ (x : α), Quotient.mk s x = q
  have hP : ∀ q, P q := by intro q; induction q using Quotient.inductionOn with | h x => exact ⟨x, rfl⟩
  let rep_of_orbit : Quotient s → α := fun q => Classical.choose (hP q)
  have h_rep_spec : ∀ q, Quotient.mk s (rep_of_orbit q) = q := by intro q; exact Classical.choose_spec (hP q)
  let rep : α → α := fun x => rep_of_orbit (Quotient.mk s x)
  have h_rep_orbit : ∀ x, rep x = x ∨ rep x = h.a x := by
    intro x; have h5 : Quotient.mk s (rep x) = Quotient.mk s x := h_rep_spec (Quotient.mk s x)
    have h7 : Setoid.r (rep x) x := Quotient.exact h5; exact h7
  have h_rep_invar : ∀ x, rep (h.a x) = rep x := by
    intro x; have h7 : Quotient.mk s (h.a x) = Quotient.mk s x := by apply Quotient.sound; exact Or.inr rfl
    dsimp only [rep]; rw [h7]
  let g : α →₀ Z2 :=
    { toFun := fun x => if x = rep x then f x else 0
      support := f.support.filter (fun x => x = rep x)
      mem_support_toFun := by
        intro x; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h_in, h_eq⟩; rw [if_pos h_eq]; exact Finsupp.mem_support_iff.mp h_in
        · intro h; by_cases h_eq : x = rep x
          · rw [if_pos h_eq] at h; exact ⟨Finsupp.mem_support_iff.mpr h, h_eq⟩
          · rw [if_neg h_eq] at h; contradiction }
  have h_g_eval : ∀ x, g x = (if x = rep x then f x else 0) := by intro x; rfl
  have h_main : (pMap h) g = f := by
    apply Finsupp.ext; intro y
    have h_p_eval : ∀ z, (pMap h g) z = g z + g (h.a z) := by intro z; simp [pMap, involutionAction_eval h] <;> rfl
    rw [h_p_eval y]
    by_cases h_case : y = rep y
    · have h9 : rep (h.a y) = rep y := h_rep_invar y
      have h10 : h.a y ≠ rep (h.a y) := by rw [h9, h_case.symm]; exact h.free y
      rw [h_g_eval y, h_g_eval (h.a y), if_pos h_case, if_neg h10] <;> simp
    · have h_rep_ax : rep y = h.a y := by
        rcases h_rep_orbit y with (h_eq | h_eq)
        · exfalso; exact h_case h_eq.symm
        · exact h_eq
      have h11 : h.a y = rep (h.a y) := by rw [h_rep_invar y, h_rep_ax]
      rw [h_g_eval y, h_g_eval (h.a y), if_neg h_case, if_pos h11]
      <;> simp [h_inv y] <;> rfl
  exact ⟨g, h_main⟩

/-- im(p) = ker(p). -/
lemma range_pMap_eq_ker : LinearMap.range (pMap h) = LinearMap.ker (pMap h) := by
  apply le_antisymm; exact range_pMap_subset_ker h; exact ker_pMap_subset_range h

--! ########## Part 2: Transport across linear equivalence ##########

/-- Transport ker=im across a linear equivalence. -/
lemma transport_ker_eq_im {M N : Type*} [AddCommGroup M] [Module Z2 M] [AddCommGroup N] [Module Z2 N]
    (e : M ≃ₗ[Z2] N) (P : M →ₗ[Z2] M) (P' : N →ₗ[Z2] N)
    (h_comm : e.toLinearMap.comp P = P'.comp e.toLinearMap)
    (h_main : LinearMap.ker P' = LinearMap.range P') :
    LinearMap.ker P = LinearMap.range P := by
  have h_ker : ∀ (x : M), x ∈ LinearMap.ker P ↔ e x ∈ LinearMap.ker P' := by
    intro x
    simp only [LinearMap.mem_ker]
    have h2 : e (P x) = P' (e x) := by
      exact congr_arg (fun (f : M →ₗ[Z2] N) => f x) h_comm
    constructor
    · intro h; rw [←h2, h]; simp
    · intro h
      have h3 : e (P x) = P' (e x) := by exact congr_arg (fun (f : M →ₗ[Z2] N) => f x) h_comm
      have h4 : e (P x) = 0 := by rw [h3]; exact h
      have h5 : e (P x) = e 0 := by rw [h4]; simp
      exact e.injective h5
  have h_range : ∀ (x : M), x ∈ LinearMap.range P ↔ e x ∈ LinearMap.range P' := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩; refine ⟨e y, ?_⟩
      exact (congr_arg (fun (f : M →ₗ[Z2] N) => f y) h_comm).symm
    · rintro ⟨z, hz⟩; let y := e.symm z; refine ⟨y, ?_⟩
      have h3 : e (P y) = P' (e y) := by
        exact congr_arg (fun (f : M →ₗ[Z2] N) => f y) h_comm
      have h4 : e y = z := by simp [y]
      rw [h4] at h3; exact e.injective (hz ▸ h3)
  ext x
  have h5 : x ∈ LinearMap.ker P ↔ e x ∈ LinearMap.ker P' := h_ker x
  have h6 : e x ∈ LinearMap.ker P' ↔ e x ∈ LinearMap.range P' := by rw [h_main]
  have h7 : x ∈ LinearMap.range P ↔ e x ∈ LinearMap.range P' := h_range x
  rw [h5, h6, ←h7]

--! ########## Part 3: Antipodal map and chain complex ##########

abbrev ap (x : Sphere n) : Sphere n :=
  AlgebraicTopology.StdSphereHomology.antipodal n x

lemma ap_continuous : Continuous (ap : Sphere n → Sphere n) := by
  have h1 : ∀ (x : Sphere n), (-x : EuclideanSpace ℝ (Fin (n + 1))) ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    intro x; have hx : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    simpa [norm_neg, mem_sphere_zero_iff_norm] using hx
  exact Continuous.subtype_mk (continuous_neg.comp continuous_subtype_val) h1

lemma ap_invol (x : Sphere n) : ap (ap x) = x := by
  ext; simp [ap, AlgebraicTopology.StdSphereHomology.antipodal]

/-- The singular chain complex functor with Z/2 coefficients. -/
def chainFunctor2 : TopCat ⥤ ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  (singularChainComplexFunctor (ModuleCat (ZMod 2))).obj (ModuleCat.of (ZMod 2) (ZMod 2))

/-- The singular chain complex of S^n with Z/2 coefficients. -/
abbrev ChainSphere2 (n : ℕ) : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  chainFunctor2.obj (TopCat.of (Sphere n))

/-- The antipodal map as a continuous map. -/
def apCmap : C(Sphere n, Sphere n) := ⟨ap, ap_continuous⟩

/-- The chain map induced by the antipodal map. -/
def aHash2 (n : ℕ) : ChainSphere2 n ⟶ ChainSphere2 n :=
  chainFunctor2.map (TopCat.ofHom (apCmap : C(Sphere n, Sphere n)))

/-- p = 1 + a_# on chains. -/
def pHash2 (n : ℕ) : ChainSphere2 n ⟶ ChainSphere2 n :=
  𝟙 (ChainSphere2 n) + aHash2 n

/-- p^2 = 0. -/
lemma pHash2_squared (n : ℕ) : pHash2 n ≫ pHash2 n = 0 := by
  have h_ap2 : (apCmap.comp apCmap : C(Sphere n, Sphere n)) = ContinuousMap.id (Sphere n) := by
    apply ContinuousMap.ext; intro x; exact ap_invol x
  have h1 : aHash2 n ≫ aHash2 n = 𝟙 (ChainSphere2 n) := by
    have h_map : chainFunctor2.map (TopCat.ofHom (apCmap.comp apCmap)) =
        chainFunctor2.map (TopCat.ofHom (ContinuousMap.id (Sphere n))) := by rw [h_ap2]
    have h_comp : chainFunctor2.map (TopCat.ofHom (apCmap.comp apCmap)) =
        aHash2 n ≫ aHash2 n := by
      rw [TopCat.ofHom_comp] <;> simp [aHash2, chainFunctor2, Functor.map_comp] <;> rfl
    have h_id : chainFunctor2.map (TopCat.ofHom (ContinuousMap.id (Sphere n))) =
        𝟙 (ChainSphere2 n) := by
      simp [aHash2, chainFunctor2, Functor.map_id] <;> rfl
    rw [h_comp, h_id] at h_map; exact h_map
  have h_step1 : (𝟙 (ChainSphere2 n) + aHash2 n) ≫ (𝟙 (ChainSphere2 n) + aHash2 n) =
      𝟙 (ChainSphere2 n) + aHash2 n + aHash2 n + aHash2 n ≫ aHash2 n := by
    simp [Preadditive.add_comp, Preadditive.comp_add, add_assoc, add_comm, add_left_comm]
  have h_step2 : 𝟙 (ChainSphere2 n) + aHash2 n + aHash2 n + aHash2 n ≫ aHash2 n =
      𝟙 (ChainSphere2 n) + aHash2 n + aHash2 n + 𝟙 (ChainSphere2 n) := by rw [h1]
  have h_step3 : 𝟙 (ChainSphere2 n) + aHash2 n + aHash2 n + 𝟙 (ChainSphere2 n) =
      (𝟙 (ChainSphere2 n) + 𝟙 (ChainSphere2 n)) + (aHash2 n + aHash2 n) := by
    simp [add_assoc, add_comm, add_left_comm]
  have h_main : pHash2 n ≫ pHash2 n = (𝟙 (ChainSphere2 n) + 𝟙 (ChainSphere2 n)) + (aHash2 n + aHash2 n) := by
    dsimp only [pHash2]
    rw [h_step1, h_step2, h_step3]
  have h2 : (𝟙 (ChainSphere2 n) + 𝟙 (ChainSphere2 n)) = 0 := ZModModule.add_self (𝟙 (ChainSphere2 n))
  have h3 : aHash2 n + aHash2 n = 0 := ZModModule.add_self (aHash2 n)
  rw [h_main, h2, h3] <;> simp

--! ########## Part 4: Degree-wise ker=im for the chain complex ##########

/-- The singular simplicial set of S^n. -/
abbrev sphereSSet (n : ℕ) := TopCat.toSSet.obj (TopCat.of (Sphere n))

/-- The type of singular k-simplices of S^n. -/
abbrev SingularSimplices (n k : ℕ) := sphereSSet n _⦋k⦌

/-- Antipodal map has no fixed points on S^n. -/
lemma ap_no_fixed_points {n : ℕ} (x : Sphere n) : ap x ≠ x := by
  intro h
  have h' : (ap x : EuclideanSpace ℝ (Fin (n + 1))) = (x : EuclideanSpace ℝ (Fin (n + 1))) := by
    exact congr_arg Subtype.val h
  have h'' : -(x : EuclideanSpace ℝ (Fin (n + 1))) = (x : EuclideanSpace ℝ (Fin (n + 1))) := h'
  have h3 : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
    have h4 : (x : EuclideanSpace ℝ (Fin (n + 1))) + (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
      have h5 : -(x : EuclideanSpace ℝ (Fin (n + 1))) = (x : EuclideanSpace ℝ (Fin (n + 1))) := h''
      have h6 : -(x : EuclideanSpace ℝ (Fin (n + 1))) + (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by simp
      rw [h5] at h6
      exact h6
    have h7 : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
      simpa [two_smul] using h4
    exact (smul_eq_zero.mp h7).resolve_left (by norm_num)
  have h4 : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.property
  rw [h3] at h4
  norm_num at h4

/-- The antipodal action on singular k-simplices. -/
def antipodalSimplexAction (n k : ℕ) : SingularSimplices n k ≃ SingularSimplices n k :=
  let a_set : sphereSSet n ⟶ sphereSSet n := TopCat.toSSet.map (TopCat.ofHom apCmap)
  { toFun := a_set.app _
    invFun := a_set.app _
    left_inv := by
      intro σ
      have h_ap2 : a_set ≫ a_set = 𝟙 (sphereSSet n) := by
        have h_comp : a_set ≫ a_set = TopCat.toSSet.map (TopCat.ofHom (apCmap.comp apCmap)) := by
          exact SSet.hom_ext (congrFun rfl)
        rw [h_comp]
        have h : (apCmap.comp apCmap : C(Sphere n, Sphere n)) = ContinuousMap.id (Sphere n) := by
          apply ContinuousMap.ext; intro x; exact ap_invol x
        rw [h] <;> simp
      simpa using congr_arg (fun (f : sphereSSet n ⟶ sphereSSet n) => f.app _ σ) h_ap2
    right_inv := by
      intro σ
      have h_ap2 : a_set ≫ a_set = 𝟙 (sphereSSet n) := by
        have h_comp : a_set ≫ a_set = TopCat.toSSet.map (TopCat.ofHom (apCmap.comp apCmap)) := by
          exact SSet.hom_ext (congrFun rfl)
        rw [h_comp]
        have h : (apCmap.comp apCmap : C(Sphere n, Sphere n)) = ContinuousMap.id (Sphere n) := by
          apply ContinuousMap.ext; intro x; exact ap_invol x
        rw [h] <;> simp
      simpa using congr_arg (fun (f : sphereSSet n ⟶ sphereSSet n) => f.app _ σ) h_ap2 }

/-- The antipodal action on singular simplices is free. -/
lemma antipodalSimplexAction_free (n k : ℕ) :
    ∀ (σ : SingularSimplices n k), antipodalSimplexAction n k σ ≠ σ := by
  intro σ h
  classical
  let Δk := stdSimplex ℝ (Fin (k + 1))
  have h_nonempty : Nonempty Δk := by
    exact stdSimplex.instNonemptyElemForall
  let t : Δk := Classical.arbitrary Δk
  let e : SingularSimplices n k ≃ C(Δk, Sphere n) :=
    TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op ⦋k⦌)
  have h_nat : e (antipodalSimplexAction n k σ) = apCmap.comp (e σ) := by
    exact (Equiv.apply_eq_iff_eq_symm_apply e).mpr rfl
  have h_eq : e (antipodalSimplexAction n k σ) = e σ := by rw [h]
  have h_cont : apCmap.comp (e σ) = e σ := by
    rw [←h_nat, h_eq]
  have h_val : ap ((e σ) t) = (e σ) t := by
    have h9 := congr_fun (congr_arg ContinuousMap.toFun h_cont) t
    exact h9
  exact ap_no_fixed_points ((e σ) t) h_val

/-- For each degree k, ker(pHash2 n at k) = range(pHash2 n at k). -/
theorem pHash2_ker_eq_range (n k : ℕ) :
    LinearMap.ker ((pHash2 n).f k).hom = LinearMap.range ((pHash2 n).f k).hom := by
  classical
  let X := sphereSSet n
  let ι := SingularSimplices n k
  let R2 := ModuleCat.of (ZMod 2) (ZMod 2)
  let Z : ι → ModuleCat (ZMod 2) := fun _ => R2
  let a_simplex : ι ≃ ι := antipodalSimplexAction n k
  let h_free : FreeInvolution ι :=
    { a := a_simplex
      sq := by
        ext x
        exact a_simplex.left_inv x
      free := antipodalSimplexAction_free n k }
  let Ck := (ChainSphere2 n).X k
  let e1 : Ck ≅ ModuleCat.of (ZMod 2) (DirectSum ι (fun i => ↑(Z i))) :=
    ModuleCat.coprodIsoDirectSum Z
  let e2 : (ι →₀ ZMod 2) ≃ₗ[ZMod 2] DirectSum ι (fun i => ↑(Z i)) :=
    finsuppLequivDFinsupp (ZMod 2)
  let e : Ck ≃ₗ[ZMod 2] (ι →₀ ZMod 2) :=
    e1.toLinearEquiv.trans e2.symm
  let A : Ck →ₗ[ZMod 2] Ck := ((aHash2 n).f k).hom
  let P : Ck →ₗ[ZMod 2] Ck := ((pHash2 n).f k).hom
  let P' : (ι →₀ ZMod 2) →ₗ[ZMod 2] (ι →₀ ZMod 2) := pMap h_free
  let a_set : X ⟶ X := TopCat.toSSet.map (TopCat.ofHom apCmap)
  let T := ModuleCat.of (ZMod 2) (ι →₀ ZMod 2)
  let e_cat : Ck ⟶ T := ModuleCat.ofHom e.toLinearMap
  let invol_cat : T ⟶ T := ModuleCat.ofHom (involutionAction h_free)

  -- Helper: the coproduct inclusion as a morphism R2 → Ck
  let ι_inc (σ : ι) : R2 ⟶ Ck :=
    show R2 ⟶ Ck from X.ιChainComplex (R := R2) σ

  -- Basis fact: e maps ι_inc σ 1 to Finsupp.single σ 1
  have h_basis : ∀ (σ : ι), e.toLinearMap ((ι_inc σ).hom 1) = Finsupp.single σ 1 := by
    intro σ
    have h_iso : (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ e1.inv = ι_inc σ :=
      ModuleCat.lof_coprodIsoDirectSum_inv Z σ
    have h2 : ι_inc σ ≫ e1.hom =
        ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ) := by
      calc
        ι_inc σ ≫ e1.hom
          = ((ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ e1.inv) ≫ e1.hom := by rw [h_iso]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ (e1.inv ≫ e1.hom) := by rw [Category.assoc]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ 𝟙 _ := by rw [e1.inv_hom_id]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) := by simp
    have h1 : e1.toLinearEquiv ((ι_inc σ).hom 1) =
        (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ) 1 := by
      exact congr_arg (fun (f : R2 ⟶ _) => f.hom 1) h2
    have h5 : DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ 1 = DFinsupp.single σ 1 := by
      exact Eq.symm (DirectSum.ext (fun i => ZMod 2) (congrFun rfl))
    have h6 : e2.symm (DFinsupp.single σ 1) = Finsupp.single σ 1 := by
      have h_e2 : (e2.symm : DirectSum ι (fun i : ι => ZMod 2) → (ι →₀ ZMod 2)) = DFinsupp.toFinsupp := by
        exact finsuppLequivDFinsupp_symm_apply (R := ZMod 2)
      rw [h_e2]
      have h_toFinsupp : DFinsupp.toFinsupp (DFinsupp.single σ (1 : ZMod 2)) = Finsupp.single σ (1 : ZMod 2) := by
        ext x
        simp [DFinsupp.toFinsupp]
        <;> aesop
      exact h_toFinsupp
    have h4 : e2.symm (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ 1) = Finsupp.single σ 1 := by
      rw [h5]
      exact h6
    calc
      e.toLinearMap ((ι_inc σ).hom 1)
        = e2.symm (e1.toLinearEquiv ((ι_inc σ).hom 1)) := by rfl
      _ = e2.symm (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ 1) := by rw [h1]
      _ = Finsupp.single σ 1 := h4

  -- A maps basis σ to basis a_simplex σ
  have h_A_basis : ∀ (σ : ι), A ((ι_inc σ).hom 1) = (ι_inc (a_simplex σ)).hom 1 := by
    intro σ
    have h1 : ι_inc σ ≫ (aHash2 n).f k = ι_inc (a_simplex σ) := by
      have h_map := SSet.ι_chainComplexMap_f (R := R2) (f := a_set) (x := σ)
      exact h_map
    exact congr_arg (fun (f : R2 ⟶ Ck) => f.hom 1) h1

  -- Commutativity on basis elements
  have h_basis_comm : ∀ (σ : ι),
      e.toLinearMap (A ((ι_inc σ).hom 1)) =
      involutionAction h_free (e.toLinearMap ((ι_inc σ).hom 1)) := by
    intro σ
    calc
      e.toLinearMap (A ((ι_inc σ).hom 1))
        = e.toLinearMap ((ι_inc (a_simplex σ)).hom 1) := by rw [h_A_basis σ]
      _ = Finsupp.single (a_simplex σ) 1 := h_basis (a_simplex σ)
      _ = involutionAction h_free (Finsupp.single σ 1) := by
        simp [involutionAction, Finsupp.mapDomain_single] <;> rfl
      _ = involutionAction h_free (e.toLinearMap ((ι_inc σ).hom 1)) := by rw [h_basis σ]

  -- Use chainComplex_hom_ext to lift from basis to whole module
  let f_cat : Ck ⟶ T := ModuleCat.ofHom (e.toLinearMap.comp A)
  let g_cat : Ck ⟶ T := ModuleCat.ofHom ((involutionAction h_free).comp e.toLinearMap)
  have h_eq : f_cat = g_cat := by
    apply SSet.chainComplex_hom_ext (R := R2)
    intro σ
    have h_hom : (ι_inc σ ≫ f_cat).hom = (ι_inc σ ≫ g_cat).hom := by
      apply LinearMap.ext
      intro z
      have h_z : z = 0 ∨ z = 1 := by fin_cases z <;> tauto
      rcases h_z with (h0 | h1)
      · rw [h0]; simp
      · rw [h1]; exact h_basis_comm σ
    have h_morph : (ι_inc σ ≫ f_cat) = (ι_inc σ ≫ g_cat) := by
      exact ModuleCat.hom_ext h_hom
    exact h_morph
  have h_comm_A : e.toLinearMap.comp A = (involutionAction h_free).comp e.toLinearMap := by
    have h : f_cat.hom = g_cat.hom := by rw [h_eq]
    exact h
  have h_comm_P : e.toLinearMap.comp P = P'.comp e.toLinearMap := by
    have hP : P = LinearMap.id + A := by rfl
    rw [hP]
    simp [LinearMap.add_comp, LinearMap.comp_add, h_comm_A] <;> rfl
  exact transport_ker_eq_im e P P' h_comm_P (range_pMap_eq_ker h_free).symm

end BorsukUlamBackup

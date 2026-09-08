/-
H_0(D) Base Case for Transfer LES.

Proves for the transfer SES 0 → D → C → D → 0 on S^n (n ≥ 1, Z/2 coeffs):
- q_* : H_0(C) → H_0(D) is an isomorphism
- i_* : H_0(D) → H_0(C) is zero
- H_0(D) ≅ Z/2
- For any odd map f, f_D = id on H_0(D)
-/

import MyLeanRepo.Kakeya.BorsukUlam.TransferFull
import MyLeanRepo.Kakeya.BorsukUlam.TransferInstantiation
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Data.ZMod.Basic

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open SeedMathlib.AlgebraicTopology.Degree
open BorsukUlamBackup

namespace BorsukUlam.H0BaseCase

abbrev Z2 := ZMod 2
abbrev R2 := ModuleCat.of Z2 Z2

/-- Path-connectedness of S^n for n ≥ 1. -/
lemma spherePathConnected (n : ℕ) (hn : 1 ≤ n) :
    PathConnectedSpace (Sphere n) := by
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
  have h_rank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
    Module.lt_rank_of_lt_finrank (by omega)
  exact isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere h_rank 0 (by norm_num))

/-- Any continuous self-map of S^n induces identity on H_0(C; Z/2). -/
lemma selfMapIdH0 (n : ℕ) (hn : 1 ≤ n)
    (f : TopCat.of (Sphere n) ⟶ TopCat.of (Sphere n)) :
    HomologicalComplex.homologyMap (chainFunctor2.map f) 0 =
    𝟙 ((ChainSphere2 n).homology 0) := by
  letI : PathConnectedSpace (Sphere n) := spherePathConnected n hn
  let X : TopCat := TopCat.of (Sphere n)
  let C := ChainSphere2 n
  let ε : C.homology 0 ⟶ R2 := TopCat.singularHomology₀ε X R2
  have h_iso : IsIso ε := by
    letI : PathConnectedSpace X := by
      exact spherePathConnected n hn
    exact TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier X R2
  let f' := TopCat.toSSet.map f
  have h_nat : HomologicalComplex.homologyMap (chainFunctor2.map f) 0 ≫ ε = ε :=
    SSet.augmentation_naturality (f := f') R2
  have h_main : HomologicalComplex.homologyMap (chainFunctor2.map f) 0 = 𝟙 (C.homology 0) := by
    have h1 : HomologicalComplex.homologyMap (chainFunctor2.map f) 0 =
        (HomologicalComplex.homologyMap (chainFunctor2.map f) 0 ≫ ε) ≫ inv ε := by
      rw [Category.assoc, IsIso.hom_inv_id ε, Category.comp_id]
    rw [h1, h_nat, IsIso.hom_inv_id ε]
  exact h_main

/-- p_* = 0 on H_0(C) for n ≥ 1. -/
lemma pStarZero (n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (pHash2 n) 0 = 0 := by
  let C := ChainSphere2 n
  have h1 : pHash2 n = 𝟙 C + aHash2 n := by rfl
  rw [h1]
  have h2 : HomologicalComplex.homologyMap (𝟙 C + aHash2 n) 0 =
      HomologicalComplex.homologyMap (𝟙 C) 0 +
      HomologicalComplex.homologyMap (aHash2 n) 0 :=
    homologyMap_add (𝟙 C) (aHash2 n) 0
  rw [h2, HomologicalComplex.homologyMap_id]
  have h_a : HomologicalComplex.homologyMap (aHash2 n) 0 = 𝟙 (C.homology 0) :=
    selfMapIdH0 n hn (TopCat.ofHom apCmap)
  rw [h_a]
  have h3 : (𝟙 (C.homology 0)) + (𝟙 (C.homology 0)) =
      (0 : C.homology 0 ⟶ C.homology 0) := by
    have h4 : (𝟙 (C.homology 0)) + (𝟙 (C.homology 0)) =
        (2 : ZMod 2) • (𝟙 (C.homology 0)) := by
      rw [two_smul]
    rw [h4]
    have h5 : (2 : ZMod 2) = 0 := by decide
    rw [h5]
    <;> simp
  exact h3

/-- q ≫ i = p as chain maps C → C. -/
lemma qCompI (n : ℕ) :
    tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n) ≫
    tinclusionMap (pHash2 n) = pHash2 n := by
  ext k x
  <;> rfl

/-- q_* is epi on H_0.

At degree 0, the opcycles map is epi (instance from ShortExact),
and homologyι is an iso, so the homology map is epi. -/
lemma qStarEpi (n : ℕ) :
    Epi (HomologicalComplex.homologyMap
      (tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n)) 0) := by
  let S := ttransferShortComplex (pHash2 n) (pHash2_rangePi_eq_ker n)
  let hS : S.ShortExact := sphereTransferShortExact n
  have h_epi_g : Epi S.g := hS.epi_g
  have h_rel : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
    simp [ComplexShape.down_Rel] <;> omega
  have h_iso2 : IsIso (S.X₂.homologyι 0) := by
    apply ShortComplex.isIso_homologyι
    exact S.X₂.shape _ _ h_rel
  have h_iso3 : IsIso (S.X₃.homologyι 0) := by
    apply ShortComplex.isIso_homologyι
    exact S.X₃.shape _ _ h_rel
  have h_opcycles_epi : Epi (HomologicalComplex.opcyclesMap S.g 0) := by
    -- The opcycles map is epi because S.g is epi (instance from opcycles_right_exact)
    have h_main : (ShortComplex.mk (HomologicalComplex.opcyclesMap S.f 0)
        (HomologicalComplex.opcyclesMap S.g 0) _).Exact :=
      HomologicalComplex.opcycles_right_exact S hS.exact 0
    exact instEpiOpcyclesMapOfF S.g 0
  have h_comm : HomologicalComplex.homologyMap S.g 0 ≫ (S.X₃.homologyι 0) =
      (S.X₂.homologyι 0) ≫ HomologicalComplex.opcyclesMap S.g 0 := by
    exact homologyι_naturality S.g 0
  have h_epi_rhs : Epi ((S.X₂.homologyι 0) ≫ HomologicalComplex.opcyclesMap S.g 0) :=
    epi_comp _ _
  have h_epi_comp : Epi (HomologicalComplex.homologyMap S.g 0 ≫ (S.X₃.homologyι 0)) := by
    rw [h_comm] <;> exact h_epi_rhs
  have h_decomp : HomologicalComplex.homologyMap S.g 0 =
      (HomologicalComplex.homologyMap S.g 0 ≫ (S.X₃.homologyι 0)) ≫
      inv (S.X₃.homologyι 0) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have h_goal : Epi (HomologicalComplex.homologyMap S.g 0) := by
    rw [h_decomp]
    exact epi_comp _ _
  exact h_goal

/-- i_* = 0 on H_0(D). -/
lemma iStarZero (n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (tinclusionMap (pHash2 n)) 0 = 0 := by
  let qMap := tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n)
  let iMap := tinclusionMap (pHash2 n)
  have h_comp : qMap ≫ iMap = pHash2 n := qCompI n
  have h1 : HomologicalComplex.homologyMap qMap 0 ≫
      HomologicalComplex.homologyMap iMap 0 =
      HomologicalComplex.homologyMap (qMap ≫ iMap) 0 := by
    rw [← HomologicalComplex.homologyMap_comp]
  have h2 : HomologicalComplex.homologyMap qMap 0 ≫
      HomologicalComplex.homologyMap iMap 0 = 0 := by
    rw [h1, h_comp, pStarZero n hn]
  haveI : Epi (HomologicalComplex.homologyMap qMap 0) := qStarEpi n
  exact (cancel_epi (HomologicalComplex.homologyMap qMap 0)).mp h2

/-- q_* is mono on H_0.

By exactness of the homology LES, im(i_*) = ker(q_*). Since i_* = 0,
ker(q_*) = 0, so q_* is mono. -/
lemma qStarMono (n : ℕ) (hn : 1 ≤ n) :
    Mono (HomologicalComplex.homologyMap
      (tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n)) 0) := by
  let S := ttransferShortComplex (pHash2 n) (pHash2_rangePi_eq_ker n)
  let hS : S.ShortExact := sphereTransferShortExact n
  let qMap := S.g
  let iMap := S.f
  let S_hom : CategoryTheory.ShortComplex (ModuleCat Z2) :=
    (S.map (HomologicalComplex.homologyFunctor (ModuleCat Z2) (ComplexShape.down ℕ) 0))
  have h_exact : S_hom.Exact := hS.homology_exact₂ 0
  have h_i_zero : S_hom.f = 0 := by
    have h : HomologicalComplex.homologyMap iMap 0 = 0 := iStarZero n hn
    exact h
  exact h_exact.mono_g h_i_zero

/-- q_* is an isomorphism on H_0. -/
lemma qStarIso (n : ℕ) (hn : 1 ≤ n) :
    IsIso (HomologicalComplex.homologyMap
      (tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n)) 0) := by
  haveI : Epi _ := qStarEpi n
  haveI : Mono _ := qStarMono n hn
  exact isIso_of_mono_of_epi _

/-- H_0(D) ≅ Z/2. -/
noncomputable def h0DIso (n : ℕ) (hn : 1 ≤ n) :
    (timageSubcomplex (pHash2 n)).homology 0 ≅ R2 := by
  letI : PathConnectedSpace (Sphere n) := spherePathConnected n hn
  let X : TopCat := TopCat.of (Sphere n)
  let C := ChainSphere2 n
  let qMap := tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n)
  let ε : C.homology 0 ⟶ R2 := TopCat.singularHomology₀ε X R2
  have h_iso : IsIso ε := by
    letI : PathConnectedSpace X := by exact spherePathConnected n hn
    exact TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier X R2
  letI : IsIso (HomologicalComplex.homologyMap qMap 0) := qStarIso n hn
  exact (asIso (HomologicalComplex.homologyMap qMap 0)).symm ≪≫ asIso ε

/-- For an odd map f, f_D = id on H_0(D). -/
lemma fDIdH0 (n : ℕ) (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n))
    (hf_odd : ∀ x, f (ap x) = ap (f x)) :
    HomologicalComplex.homologyMap (oddMapInducedOnD f hf_odd) 0 =
    𝟙 ((timageSubcomplex (pHash2 n)).homology 0) := by
  let fC := chainFunctor2.map (TopCat.ofHom f)
  let fD := oddMapInducedOnD f hf_odd
  let qMap := tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n)
  have h_comm : fC ≫ pHash2 n = pHash2 n ≫ fC :=
    oddMap_comm_pHash f hf_odd
  have h_comm_q : qMap ≫ fD = fC ≫ qMap := by
    ext i x
    dsimp only [qMap, tcorestrictionMap, fD, oddMapInducedOnD]
    apply Subtype.ext
    have h_at_i : (fC.f i) ≫ (pHash2 n).f i = (pHash2 n).f i ≫ (fC.f i) := by
      have h := congr_arg (fun (h : ChainSphere2 n ⟶ ChainSphere2 n) => h.f i) h_comm
      exact h
    have h_lin : (fC.f i).hom ∘ₗ ((pHash2 n).f i).hom =
        ((pHash2 n).f i).hom ∘ₗ (fC.f i).hom := by
      have h2 := congr_arg ModuleCat.Hom.hom h_at_i
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
      exact h2.symm
    exact LinearMap.congr_fun h_lin x
  have h_hom : HomologicalComplex.homologyMap qMap 0 ≫
      HomologicalComplex.homologyMap fD 0 =
      HomologicalComplex.homologyMap fC 0 ≫
      HomologicalComplex.homologyMap qMap 0 := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, h_comm_q]
  have h_fC : HomologicalComplex.homologyMap fC 0 = 𝟙 ((ChainSphere2 n).homology 0) :=
    selfMapIdH0 n hn (TopCat.ofHom f)
  rw [h_fC] at h_hom
  rw [Category.id_comp] at h_hom
  haveI : IsIso (HomologicalComplex.homologyMap qMap 0) := qStarIso n hn
  let qStar := HomologicalComplex.homologyMap qMap 0
  have h : qStar ≫ HomologicalComplex.homologyMap fD 0 = qStar := h_hom
  have h2 : qStar ≫ HomologicalComplex.homologyMap fD 0 = qStar ≫ 𝟙 _ := by
    rw [h, Category.comp_id]
  exact (cancel_epi qStar).mp h2

end BorsukUlam.H0BaseCase

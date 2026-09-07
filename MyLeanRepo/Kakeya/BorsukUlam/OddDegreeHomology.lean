/-
# Odd Degree Lemma via Homology LES

Proves that any odd continuous self-map of S^n induces the identity on
H_n(S^n; Z/2), i.e., its mod-2 degree is 1.

## Proof Sketch

Uses the transfer short exact sequence 0 → D → C(S^n; Z/2) → D → 0 and its
long exact sequence in homology, where D = im(1 + a_#) is the image subcomplex.

1. H_0(D) ≅ Z/2 and f_D = id on H_0(D) (transferred to AddCommGrpCat)
2. For 1 ≤ k < n, the LES gives δ : H_k(D) ≅ H_{k-1}(D)
3. By induction, f_D = id on H_k(D) for all 0 ≤ k < n
4. At degree n, δ is epi, so f_D(n) = id by naturality
5. If f_C(n) = 0, naturality gives i_* = 0 and q_* = 0
6. Exactness + q_* mono + q_* = 0 implies H_n(C) = 0, contradiction
7. Therefore f_C ≠ 0, and since H_n(C) ≅ Z/2, f_C = id

## Whiteprint Node
- `odd_degree_lemma_homology`
-/

import MyLeanRepo.Kakeya.BorsukUlam.TransferInstantiation
import MyLeanRepo.Kakeya.BorsukUlam.TransferH0BaseCase
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.CategoryBridge
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.CoefficientBockstein
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.SphereHomologyZ2Bockstein
import MyLeanRepo.Kakeya.BorsukUlam.Mod2Degree
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open Vendored.AlgebraicTopology.Degree
open BorsukUlamBackup
open BorsukUlam.H0BaseCase

namespace BorsukUlam.OddDegreeHomology

variable {n : ℕ}

/-! ### Transfer from ModuleCat(Z2) to AddCommGrpCat -/

/-- Transfer zero homologyMap through forgetful functor. -/
lemma transfer_homologyMap_zero {C₁ C₂ : ChainComplex (ModuleCat (ZMod 2)) ℕ}
    (f : C₁ ⟶ C₂) (i : ℕ) (h : HomologicalComplex.homologyMap f i = 0) :
    HomologicalComplex.homologyMap (forgetZ2Chain.map f) i = 0 := by
  let F := forgetZ2
  let scF := HomologicalComplex.shortComplexFunctor (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) i
  let S₁ := scF.obj C₁
  let S₂ := scF.obj C₂
  let φ : S₁ ⟶ S₂ := scF.map f
  have h' : CategoryTheory.ShortComplex.homologyMap φ = 0 := by exact_mod_cast h
  have hFmap : F.map (CategoryTheory.ShortComplex.homologyMap φ) = 0 := by
    rw [h', Functor.map_zero]
  have h_main : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i ≫
      (S₂.mapHomologyIso F).hom =
      (S₁.mapHomologyIso F).hom ≫ F.map (CategoryTheory.ShortComplex.homologyMap φ) :=
    CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality (F := F) (φ := φ)
  have h1 : (S₁.mapHomologyIso F).hom ≫ F.map (CategoryTheory.ShortComplex.homologyMap φ) = 0 := by
    rw [hFmap]; exact comp_zero
  have h_zero : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i ≫
      (S₂.mapHomologyIso F).hom = 0 := by
    calc _ = (S₁.mapHomologyIso F).hom ≫ F.map (CategoryTheory.ShortComplex.homologyMap φ) := h_main
         _ = 0 := h1
  haveI : IsIso (S₂.mapHomologyIso F).hom := Iso.isIso_hom (S₂.mapHomologyIso F)
  have h_goal : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i = 0 := by
    have h' : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i ≫
        (S₂.mapHomologyIso F).hom = (0 : _) ≫ (S₂.mapHomologyIso F).hom := by
      rw [h_zero, zero_comp]
    exact (cancel_mono (S₂.mapHomologyIso F).hom).mp h'
  exact h_goal

/-- Transfer id homologyMap through forgetful functor. -/
lemma transfer_homologyMap_id {C : ChainComplex (ModuleCat (ZMod 2)) ℕ}
    (f : C ⟶ C) (i : ℕ) (h : HomologicalComplex.homologyMap f i = 𝟙 _) :
    HomologicalComplex.homologyMap (forgetZ2Chain.map f) i = 𝟙 _ := by
  let F := forgetZ2
  let scF := HomologicalComplex.shortComplexFunctor (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) i
  let S := scF.obj C
  let φ : S ⟶ S := scF.map f
  have h' : CategoryTheory.ShortComplex.homologyMap φ = 𝟙 _ := by exact_mod_cast h
  have hFmap : F.map (CategoryTheory.ShortComplex.homologyMap φ) = 𝟙 _ := by
    rw [h']; simp
  have h_main : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i ≫
      (S.mapHomologyIso F).hom =
      (S.mapHomologyIso F).hom ≫ F.map (CategoryTheory.ShortComplex.homologyMap φ) :=
    CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality (F := F) (φ := φ)
  have h_eq : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i ≫
      (S.mapHomologyIso F).hom = (S.mapHomologyIso F).hom := by
    rw [h_main, hFmap] <;> simp
  haveI : IsIso (S.mapHomologyIso F).hom := Iso.isIso_hom (S.mapHomologyIso F)
  have h_goal : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i = 𝟙 _ := by
    have h' : HomologicalComplex.homologyMap (forgetZ2Chain.map f) i ≫
        (S.mapHomologyIso F).hom = (𝟙 _) ≫ (S.mapHomologyIso F).hom := by
      rw [h_eq, Category.id_comp]
    exact (cancel_mono (S.mapHomologyIso F).hom).mp h'
  exact h_goal

/-! ### Definitions -/

/-- The transfer SES in ModuleCat(Z2). -/
abbrev S_Mod (n : ℕ) :=
  ttransferShortComplex (pHash2 n) (pHash2_rangePi_eq_ker n)

/-- The transfer SES passed through the forgetful functor to AddCommGrpCat. -/
abbrev S_Add (n : ℕ) :=
  (S_Mod n).map forgetZ2Chain

/-- Short exactness of the transfer SES in AddCommGrpCat. -/
lemma hS_Add (n : ℕ) : (S_Add n).ShortExact :=
  sphereTransferShortExactAddGrp n

/-- The induced chain map on C(S^n; Z/2) from an odd map f. -/
abbrev f_C_Mod {n : ℕ} (f : C(Sphere n, Sphere n)) :=
  chainFunctor2.map (TopCat.ofHom f)

/-- The induced chain map on D from an odd map f. -/
abbrev f_D_Mod {n : ℕ} (f : C(Sphere n, Sphere n)) (hf_odd) :=
  oddMapInducedOnD f hf_odd

/-- The forgotten induced map on C. -/
abbrev f_C_Add {n : ℕ} (f : C(Sphere n, Sphere n)) :=
  forgetZ2Chain.map (f_C_Mod f)

/-- The forgotten induced map on D. -/
abbrev f_D_Add {n : ℕ} (f : C(Sphere n, Sphere n)) (hf_odd) :=
  forgetZ2Chain.map (f_D_Mod f hf_odd)

/-- i_* = 0 on H_0(D) in AddCommGrpCat. -/
lemma iStarZero_Add (n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (S_Add n).f 0 = 0 :=
  transfer_homologyMap_zero (tinclusionMap (pHash2 n)) 0 (iStarZero n hn)

/-- f_D = id on H_0(D) in AddCommGrpCat. -/
lemma fDIdH0_Add (n : ℕ) (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf_odd : ∀ x, f (ap x) = ap (f x)) :
    HomologicalComplex.homologyMap (f_D_Add f hf_odd) 0 = 𝟙 _ :=
  transfer_homologyMap_id (oddMapInducedOnD f hf_odd) 0 (fDIdH0 n hn f hf_odd)

/-! ### Commutativity in ModuleCat -/

lemma comm_inclusion_Mod {n : ℕ}
    (f : C(Sphere n, Sphere n)) (hf_odd : ∀ x, f (ap x) = ap (f x)) :
    f_D_Mod f hf_odd ≫ tinclusionMap (pHash2 n) =
    tinclusionMap (pHash2 n) ≫ f_C_Mod f := by
  ext i x <;> rfl

lemma comm_corestriction_Mod {n : ℕ}
    (f : C(Sphere n, Sphere n)) (hf_odd : ∀ x, f (ap x) = ap (f x)) :
    f_C_Mod f ≫ tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n) =
    tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n) ≫ f_D_Mod f hf_odd := by
  let q := tcorestrictionMap (pHash2 n) (pHash2_rangePi_eq_ker n)
  let i := tinclusionMap (pHash2 n)
  have hqi : q ≫ i = pHash2 n := by ext k x <;> rfl
  have h1 : (f_C_Mod f ≫ q) ≫ i = (q ≫ f_D_Mod f hf_odd) ≫ i := by
    calc
      (f_C_Mod f ≫ q) ≫ i
        = f_C_Mod f ≫ (q ≫ i) := by rw [Category.assoc]
      _ = f_C_Mod f ≫ pHash2 n := by rw [hqi]
      _ = pHash2 n ≫ f_C_Mod f := oddMap_comm_pHash f hf_odd
      _ = (q ≫ i) ≫ f_C_Mod f := by rw [hqi]
      _ = q ≫ (i ≫ f_C_Mod f) := by rw [Category.assoc]
      _ = q ≫ (f_D_Mod f hf_odd ≫ i) := by rw [comm_inclusion_Mod f hf_odd]
      _ = (q ≫ f_D_Mod f hf_odd) ≫ i := by rw [Category.assoc]
  have h_mono : Mono i := HomologicalComplex.mono_of_mono_f i fun k => by
    rw [ModuleCat.mono_iff_injective]
    intro x y h
    have h_i : (i.f k) = ModuleCat.ofHom (Submodule.subtype (trangePi (pHash2 n) k)) := by rfl
    rw [h_i] at h
    exact Subtype.coe_injective h
  letI : Mono i := h_mono
  exact (cancel_mono i).mp h1

/-- The map of short exact sequences induced by an odd map. -/
def φ (n : ℕ) (f : C(Sphere n, Sphere n)) (hf_odd : ∀ x, f (ap x) = ap (f x)) :
    S_Add n ⟶ S_Add n where
  τ₁ := f_D_Add f hf_odd
  τ₂ := f_C_Add f
  τ₃ := f_D_Add f hf_odd
  comm₁₂ := by
    have h := congr_arg forgetZ2Chain.map (comm_inclusion_Mod f hf_odd)
    exact h
  comm₂₃ := by
    have h := congr_arg forgetZ2Chain.map (comm_corestriction_Mod f hf_odd)
    exact h

/-! ### Homology transfer from standard singular homology to ChainSphere2 -/

/-- Chain complex isomorphism from forgotten ChainSphere2 to standard singular chains. -/
abbrev chainIso (n : ℕ) :
    (S_Add n).X₂ ≅
    ((singularChainComplexFunctor AddCommGrpCat).obj (BorsukUlam.BackupRoute.R2)).obj
      (TopCat.of (Sphere n)) :=
  BorsukUlamBackup.chainSphere2ForgetIso n

/-- Homology isomorphism at degree k. -/
noncomputable def homologyIso (n k : ℕ) :
    (S_Add n).X₂.homology k ≅
    singularHomology' AddCommGrpCat (BorsukUlam.BackupRoute.R2) k (TopCat.of (Sphere n)) :=
  HomologicalComplex.homologyMapIso (chainIso n) k

/-- H_k(C) = 0 for 0 < k < n. -/
lemma hC_vanishing (n i : ℕ) (hi_pos : 0 < i) (hi_lt : i < n) :
    IsZero ((S_Add n).X₂.homology i) := by
  let e : (S_Add n).X₂.homology i ≅ _ := homologyIso n i
  have h_std : IsZero (singularHomology' AddCommGrpCat (BorsukUlam.BackupRoute.R2) i
      (TopCat.of (Sphere n))) :=
    BorsukUlam.BackupRoute.stdSphereVanishingZ2 n i hi_pos hi_lt
  exact h_std.of_iso e

/-- H_n(C) ≅ Z/2. -/
noncomputable def hC_topIso (n : ℕ) (hn : 1 ≤ n) :
    (S_Add n).X₂.homology n ≅ BorsukUlam.BackupRoute.R2 :=
  homologyIso n n ≪≫ BorsukUlam.BackupRoute.topSphereHomologyIsoZ2 n hn

/-- H_0(D) ≅ Z/2 in AddCommGrpCat. -/
noncomputable def h0DIso_Add (n : ℕ) (hn : 1 ≤ n) :
    (S_Add n).X₁.homology 0 ≅ BorsukUlam.BackupRoute.R2 := by
  let F := forgetZ2
  let C_Mod := timageSubcomplex (pHash2 n)
  let scF := HomologicalComplex.shortComplexFunctor (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) 0
  let S := scF.obj C_Mod
  let e_forget : (S_Add n).X₁.homology 0 ≅ F.obj (C_Mod.homology 0) :=
    asIso ((S.mapHomologyIso F).hom)
  let e_mod2 : F.obj (C_Mod.homology 0) ≅ F.obj H0BaseCase.R2 :=
    F.mapIso (h0DIso n hn)
  exact e_forget ≪≫ e_mod2

/-! ## δ is an isomorphism for middle degrees -/

/-- δ : H_k(D) → H_{k-1}(D). -/
abbrev delta (n : ℕ) (k : ℕ) (hk : 0 < k) :=
  (hS_Add n).δ k (k - 1) (by simp [ComplexShape.down_Rel] <;> omega)

/-- δ is an isomorphism for 1 ≤ k < n. -/
lemma deltaIso (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < n) :
    IsIso (delta n k hk_pos) := by
  let hS := hS_Add n
  have hij : (ComplexShape.down ℕ).Rel k (k - 1) := by
    simp [ComplexShape.down_Rel] <;> omega
  let δ := hS.δ k (k - 1) hij
  let qStar := HomologicalComplex.homologyMap (S_Add n).g k
  let iStar := HomologicalComplex.homologyMap (S_Add n).f (k - 1)
  have h_q0 : qStar = 0 :=
    IsZero.eq_zero_of_src (hC_vanishing n k hk_pos hk_lt) qStar
  have h_i0 : iStar = 0 := by
    by_cases h_k1 : k = 1
    · subst h_k1
      simpa [iStar] using iStarZero_Add n hn
    · have h_j_pos : 0 < k - 1 := by omega
      have h_j_lt : k - 1 < n := by omega
      exact IsZero.eq_zero_of_tgt (hC_vanishing n (k - 1) h_j_pos h_j_lt) iStar
  have h_exact3 : (ShortComplex.mk qStar δ _).Exact :=
    hS.homology_exact₃ k (k - 1) hij
  have hδ_mono : Mono δ := h_exact3.mono_g_iff.mpr h_q0
  have h_exact1 : (ShortComplex.mk δ iStar _).Exact :=
    hS.homology_exact₁ k (k - 1) hij
  have hδ_epi : Epi δ := h_exact1.epi_f_iff.mpr h_i0
  exact isIso_of_mono_of_epi δ

/-- H_k(D) ≅ Z/2 for all k < n, by induction via δ isomorphisms. -/
noncomputable def hD_k_iso (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk_lt : k < n) :
    (S_Add n).X₁.homology k ≅ BorsukUlam.BackupRoute.R2 := by
  induction k with
  | zero => exact h0DIso_Add n hn
  | succ k ih =>
    have h_k_pos : 0 < k + 1 := by omega
    have h_k_lt : k + 1 < n := hk_lt
    have hδ : IsIso (delta n (k + 1) h_k_pos) := deltaIso n hn (k + 1) h_k_pos h_k_lt
    haveI : IsIso (delta n (k + 1) h_k_pos) := hδ
    let eX : (S_Add n).X₁.homology (k + 1) ≅ (S_Add n).X₃.homology (k + 1) :=
      eqToIso (by rfl)
    exact eX ≪≫ asIso (delta n (k + 1) h_k_pos) ≪≫ ih (by omega)

/-- f_D = id on H_k(D) for all k < n, by induction. -/
lemma fD_id (n : ℕ) (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf_odd : ∀ x, f (ap x) = ap (f x))
    (k : ℕ) (hk_lt : k < n) :
    HomologicalComplex.homologyMap (f_D_Add f hf_odd) k =
    𝟙 ((S_Add n).X₁.homology k) := by
  induction k with
  | zero => exact fDIdH0_Add n hn f hf_odd
  | succ k ih =>
    have h_k_pos : 0 < k + 1 := by omega
    have h_k_lt : k + 1 < n := hk_lt
    let δ := delta n (k + 1) h_k_pos
    have hδ : IsIso δ := deltaIso n hn (k + 1) h_k_pos h_k_lt
    let φ' := φ n f hf_odd
    have h_nat : δ ≫ HomologicalComplex.homologyMap φ'.τ₁ k =
        HomologicalComplex.homologyMap φ'.τ₃ (k + 1) ≫ δ :=
      HomologicalComplex.HomologySequence.δ_naturality
        φ' (hS_Add n) (hS_Add n) (k + 1) k
        (by simp [ComplexShape.down_Rel] <;> omega)
    have h_ih : HomologicalComplex.homologyMap φ'.τ₁ k = 𝟙 _ := ih (by omega)
    rw [h_ih] at h_nat
    have h_main : HomologicalComplex.homologyMap φ'.τ₃ (k + 1) ≫ δ = δ := by
      simpa [Category.comp_id] using h_nat.symm
    haveI : IsIso δ := hδ
    have h_goal : HomologicalComplex.homologyMap φ'.τ₃ (k + 1) = 𝟙 _ :=
      (cancel_mono δ).mp (by simpa [Category.id_comp] using h_main)
    convert h_goal using 1 <;> rfl


/-- H_{n+1}(C) = 0. -/
lemma hC_above (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((S_Add n).X₂.homology (n + 1)) := by
  let e : (S_Add n).X₂.homology (n + 1) ≅
      singularHomology' AddCommGrpCat BorsukUlam.BackupRoute.R2 (n + 1) (TopCat.of (Sphere n)) :=
    homologyIso n (n + 1)
  have h_main : IsZero (singularHomology' AddCommGrpCat BorsukUlam.BackupRoute.R2 (n + 1) (TopCat.of (Sphere n))) :=
    BorsukUlam.BackupRoute.stdSphereVanishingAboveZ2 n (n + 1) (by omega)
  exact h_main.of_iso e


end BorsukUlam.OddDegreeHomology

end

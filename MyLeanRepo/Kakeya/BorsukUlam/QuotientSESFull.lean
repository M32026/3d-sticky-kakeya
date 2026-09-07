/-
# Quotient Short Exact Sequence

Constructs the short exact sequence:
  0 → D → C(S^n; Z/2) → C(RP^n; Z/2) → 0
where D = im(1 + a_#) and the second map is the quotient chain map.

## Main Results
- `quotientChainMap_epi`: the quotient chain map is epi
- `quotientShortExact`: the SES in ModuleCat(ZMod 2)

## Whiteprint Node
- hD_top_iso (supporting)
-/

import MyLeanRepo.Kakeya.BorsukUlam.QuotientKernel
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.TransferSequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequence

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open Vendored.AlgebraicTopology.Degree
open BorsukUlamBackup
open BorsukUlam.QuotientSES
open BorsukUlam.QuotientKernel

variable {n : ℕ}

namespace BorsukUlam.QuotientSESFull

/-! ### Surjectivity of quotient chain map -/

/-- The quotient chain map is epi in each degree.

Proof: every singular simplex of RP^n lifts to S^n (covering lifting property),
so every basis element of the free chain module is in the image. Since the
basis elements generate the module, the map is surjective. -/
lemma quotientChainMap_epi (n k : ℕ) : Epi ((quotientChainMap n).f k) := by
  classical
  let X_S := sphereSSet n
  let X_RP := QuotientSES.rpSSet n
  let ι_S := SingularSimplices n k
  let ι_RP := RPSingularSimplices n k
  let R2 := ModuleCat.of (ZMod 2) (ZMod 2)
  let Q := (quotientChainMap n).f k
  let Ck_RP := (ChainRP2 n).X k

  have h_lifts : ∀ (τ : ι_RP), ∃ (σ : ι_S), quotientSimplexMap n k σ = τ :=
    quotientSimplexMap_surjective n k

  have h_on_basis : ∀ (σ : ι_S),
      (X_S.ιChainComplex (R := R2) σ) ≫ Q =
      X_RP.ιChainComplex (R := R2) (quotientSimplexMap n k σ) := by
    intro σ
    exact SSet.ι_chainComplexMap_f (R := R2)
      (f := TopCat.toSSet.map (TopCat.ofHom quotientCmap)) (x := σ)

  -- Identify Ck_RP with ι_RP →₀ ZMod 2
  let Z_RP : ι_RP → ModuleCat (ZMod 2) := fun _ => R2
  let e1_RP : Ck_RP ≅ ModuleCat.of (ZMod 2) (DirectSum ι_RP (fun i => ↑(Z_RP i))) :=
    ModuleCat.coprodIsoDirectSum Z_RP
  let e2_RP : (ι_RP →₀ ZMod 2) ≃ₗ[ZMod 2] DirectSum ι_RP (fun i => ↑(Z_RP i)) :=
    finsuppLequivDFinsupp (ZMod 2)
  let e_RP : Ck_RP ≃ₗ[ZMod 2] (ι_RP →₀ ZMod 2) :=
    e1_RP.toLinearEquiv.trans e2_RP.symm

  let ι_inc_RP (τ : ι_RP) : R2 ⟶ Ck_RP := X_RP.ιChainComplex (R := R2) τ
  let ι_inc_S (σ : ι_S) : R2 ⟶ (ChainSphere2 n).X k := X_S.ιChainComplex (R := R2) σ

  -- Each basis element single τ 1 is in the image of e_RP ∘ Q
  have h_basis_in_image : ∀ (τ : ι_RP),
      Finsupp.single τ (1 : ZMod 2) ∈ LinearMap.range (e_RP.toLinearMap.comp Q.hom) := by
    intro τ
    rcases h_lifts τ with ⟨σ, hσ⟩
    refine ⟨(ι_inc_S σ).hom 1, ?_⟩
    have h4 : Q.hom ((ι_inc_S σ).hom 1) = (ι_inc_RP τ).hom 1 := by
      have h5 : (ι_inc_S σ) ≫ Q = ι_inc_RP (quotientSimplexMap n k σ) := h_on_basis σ
      rw [hσ] at h5
      exact congr_arg (fun (f : R2 ⟶ Ck_RP) => f.hom 1) h5
    have h6 : e_RP.toLinearMap (Q.hom ((ι_inc_S σ).hom 1)) = Finsupp.single τ 1 := by
      rw [h4]
      have h7 : e_RP.toLinearMap ((ι_inc_RP τ).hom 1) = Finsupp.single τ 1 := by
        have h_iso : (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ e1_RP.inv = ι_inc_RP τ :=
          ModuleCat.lof_coprodIsoDirectSum_inv Z_RP τ
        have h2 : ι_inc_RP τ ≫ e1_RP.hom =
            ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ) := by
          calc
            ι_inc_RP τ ≫ e1_RP.hom
              = ((ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ e1_RP.inv) ≫ e1_RP.hom := by rw [h_iso]
            _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ (e1_RP.inv ≫ e1_RP.hom) := by rw [Category.assoc]
            _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ 𝟙 _ := by rw [e1_RP.inv_hom_id]
            _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) := by simp
        have h1 : e1_RP.toLinearEquiv ((ι_inc_RP τ).hom 1) =
            (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ) 1 := by
          exact congr_arg (fun (f : R2 ⟶ _) => f.hom 1) h2
        have h5 : DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ 1 =
            DFinsupp.single τ 1 := by
          exact Eq.symm (DirectSum.ext (fun i => ZMod 2) (congrFun rfl))
        have h6 : e2_RP.symm (DFinsupp.single τ 1) = Finsupp.single τ 1 := by
          have h_e2 : (e2_RP.symm : DirectSum ι_RP (fun i : ι_RP => ZMod 2) → (ι_RP →₀ ZMod 2)) = DFinsupp.toFinsupp := by
            exact finsuppLequivDFinsupp_symm_apply (R := ZMod 2)
          rw [h_e2]
          have h_toFinsupp : DFinsupp.toFinsupp (DFinsupp.single τ (1 : ZMod 2)) = Finsupp.single τ (1 : ZMod 2) := by
            ext x; simp [DFinsupp.toFinsupp] <;> aesop
          exact h_toFinsupp
        calc
          e_RP.toLinearMap ((ι_inc_RP τ).hom 1)
            = e2_RP.symm (e1_RP.toLinearEquiv ((ι_inc_RP τ).hom 1)) := by rfl
          _ = e2_RP.symm (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ 1) := by rw [h1]
          _ = Finsupp.single τ 1 := by rw [h5] <;> exact h6
      exact h7
    exact h6

  -- The single elements generate the whole finsupp module
  have h_span : Submodule.span (ZMod 2) (Set.range (fun τ : ι_RP => Finsupp.single τ (1 : ZMod 2))) =
      (⊤ : Submodule (ZMod 2) (ι_RP →₀ ZMod 2)) := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    have h_sum : x = ∑ i ∈ x.support, x i • Finsupp.single i (1 : ZMod 2) := by
      ext j
      simp [Finsupp.sum_apply, Finsupp.single_apply]
      <;> by_cases h : j ∈ x.support <;> simp [h, Finsupp.mem_support_iff] at * <;> tauto
    rw [h_sum]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp

  have h3 : Submodule.span (ZMod 2) (Set.range (fun τ : ι_RP => Finsupp.single τ (1 : ZMod 2))) ≤
      LinearMap.range (e_RP.toLinearMap.comp Q.hom) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨τ, rfl⟩
    exact h_basis_in_image τ

  have h_range_top : LinearMap.range (e_RP.toLinearMap.comp Q.hom) =
      (⊤ : Submodule (ZMod 2) (ι_RP →₀ ZMod 2)) := by
    have h4 : (⊤ : Submodule (ZMod 2) (ι_RP →₀ ZMod 2)) ≤ LinearMap.range (e_RP.toLinearMap.comp Q.hom) := by
      rw [←h_span]
      exact h3
    exact le_antisymm le_top h4

  have h_surj : Function.Surjective (e_RP.toLinearMap.comp Q.hom) := by
    rw [←LinearMap.range_eq_top]
    exact h_range_top
  have h_Q_surj : Function.Surjective Q := by
    intro y
    rcases h_surj (e_RP.toLinearMap y) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact e_RP.injective hx
  rw [ModuleCat.epi_iff_surjective]
  exact h_Q_surj

/-! ### Quotient short exact sequence -/

/-- The quotient short complex: 0 → D → C(S^n) → C(RP^n) → 0. -/
def quotientShortComplex (n : ℕ) :
    ShortComplex (ChainComplex (ModuleCat (ZMod 2)) ℕ) :=
  let iMap := tinclusionMap (pHash2 n)
  let qMap := quotientChainMap n
  ShortComplex.mk iMap qMap (by
    ext k x
    have h_eq : LinearMap.ker ((quotientChainMap n).f k).hom =
        LinearMap.range ((pHash2 n).f k).hom := quotientChainMap_ker_eq_D n k
    have h_ker : (iMap.f k).hom x ∈ LinearMap.ker ((quotientChainMap n).f k).hom := by
      rw [h_eq]
      exact x.prop
    exact LinearMap.mem_ker.mp h_ker)

/-- The quotient short complex is short exact. -/
theorem quotientShortExact (n : ℕ) : (quotientShortComplex n).ShortExact := by
  let S := quotientShortComplex n
  have h_mono : ∀ k, Mono (S.f.f k) := by
    intro k
    rw [ModuleCat.mono_iff_injective]
    intro a b h
    exact Subtype.ext h
  have h_epi : ∀ k, Epi (S.g.f k) := by
    intro k
    exact quotientChainMap_epi n k
  have hfg : S.f ≫ S.g = 0 := S.zero
  have hfg_k : ∀ k, (S.f.f k) ≫ (S.g.f k) = 0 := by
    intro k
    have h : (S.f ≫ S.g).f k = (S.f.f k) ≫ (S.g.f k) := by rfl
    have h2 : (S.f ≫ S.g).f k = 0 := by rw [hfg] <;> simp
    rw [←h] <;> exact h2
  have h_exact : ∀ k, (S.map (HomologicalComplex.eval (ModuleCat (ZMod 2)) _ k)).Exact := by
    intro k
    let S_k := S.map (HomologicalComplex.eval (ModuleCat (ZMod 2)) _ k)
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker S_k]
    have h_f : S_k.f = ((tinclusionMap (pHash2 n)).f k : S_k.X₁ ⟶ S_k.X₂) := by rfl
    have h_g : S_k.g = ((quotientChainMap n).f k : S_k.X₂ ⟶ S_k.X₃) := by rfl
    have h1 : LinearMap.ker S_k.g.hom = LinearMap.range ((pHash2 n).f k).hom := by
      have h_g_hom : S_k.g.hom = ((quotientChainMap n).f k).hom := by
        exact congr_arg (fun (f : S_k.X₂ ⟶ S_k.X₃) => f.hom) h_g
      rw [h_g_hom]
      exact quotientChainMap_ker_eq_D n k
    have h2 : LinearMap.range S_k.f.hom = LinearMap.range ((pHash2 n).f k).hom := by
      have h_f_hom : S_k.f.hom = ((tinclusionMap (pHash2 n)).f k).hom := by
        exact congr_arg (fun (f : S_k.X₁ ⟶ S_k.X₂) => f.hom) h_f
      rw [h_f_hom]
      ext (z : (ChainSphere2 n).X k)
      simp only [LinearMap.mem_range, Submodule.mem_carrier]
      constructor
      · rintro ⟨y, rfl⟩
        exact y.prop
      · intro hz
        refine ⟨(⟨z, hz⟩ : (timageSubcomplex (pHash2 n)).X k), ?_⟩
        exact ((fun a => a) ∘ fun a => a) rfl
    rw [h2, h1]
  have h_degreewise : ∀ k, (S.map (HomologicalComplex.eval (ModuleCat (ZMod 2)) _ k)).ShortExact := by
    intro k
    exact CategoryTheory.ShortComplex.ShortExact.mk' (h_exact k) (h_mono k) (h_epi k)
  exact HomologicalComplex.shortExact_of_degreewise_shortExact S h_degreewise

end BorsukUlam.QuotientSESFull

end

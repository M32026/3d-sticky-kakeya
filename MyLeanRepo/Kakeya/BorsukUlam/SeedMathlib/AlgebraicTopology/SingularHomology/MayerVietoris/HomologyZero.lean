/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.Geometry.Euclidean.ConcreteKSphere

@[expose] public section


open AlgebraicTopology CategoryTheory Limits HomologicalComplex Preadditive
open scoped Simplicial

universe w v u

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable [HasBinaryBiproducts C] [HasBinaryBiproducts (ChainComplex C ℕ)]
variable [CategoryWithHomology C]
variable (R : C) [Projective R]

-- ============================================================
-- General biproduct kernel lemma
-- ============================================================

section GeneralBiprodKernel

variable {A B X C' : C}
variable (iA : A ⟶ X) (iB : B ⟶ X)
variable (pA : X ⟶ A) (pB : X ⟶ B)
variable (hiA_pA : iA ≫ pA = 𝟙 A)
variable (hiB_pB : iB ≫ pB = 𝟙 B)
variable (hiA_pB : iA ≫ pB = 0)
variable (hiB_pA : iB ≫ pA = 0)
variable (h_total : pA ≫ iA + pB ≫ iB = 𝟙 X)

/-- **General kernel lemma for any biproduct structure.** -/
noncomputable def generalBiprodKernelIso
    (p : X ⟶ C') (f : A ⟶ C') (g : B ⟶ C')
    (hp_iA : iA ≫ p = f) (hp_iB : iB ≫ p = g)
    [IsIso f] :
    kernel p ≅ B := by
  let K := kernel p
  let k : K ⟶ X := kernel.ι p
  let a : K ⟶ A := k ≫ pA
  let b : K ⟶ B := k ≫ pB
  let s : B ⟶ X := (-(g ≫ inv f)) ≫ iA + (𝟙 B) ≫ iB
  have hs : s ≫ p = 0 := by
    have h2 : s ≫ p = ((-(g ≫ inv f)) ≫ iA) ≫ p + ((𝟙 B) ≫ iB) ≫ p := by
      rw [add_comp]
    rw [h2]
    have h3 : ((-(g ≫ inv f)) ≫ iA) ≫ p = (-(g ≫ inv f)) ≫ (iA ≫ p) := by
      rw [Category.assoc]
    have h4 : ((𝟙 B) ≫ iB) ≫ p = (𝟙 B) ≫ (iB ≫ p) := by
      rw [Category.assoc]
    rw [h3, h4, hp_iA, hp_iB]
    have h5 : (-(g ≫ inv f)) ≫ f + (𝟙 B) ≫ g = 0 := by
      have h6 : (-(g ≫ inv f)) ≫ f = -g := by
        have h7 : (-(g ≫ inv f)) ≫ f = -((g ≫ inv f) ≫ f) := by exact neg_comp (g ≫ inv f) f
        rw [h7]
        have h8 : (g ≫ inv f) ≫ f = g := by
          calc
            (g ≫ inv f) ≫ f
              = g ≫ (inv f ≫ f) := by rw [Category.assoc]
            _ = g ≫ 𝟙 C' := by rw [IsIso.inv_hom_id]
            _ = g := by simp
        rw [h8]
      rw [h6]
      have h9 : -g + (𝟙 B) ≫ g = 0 := by
        have h10 : (𝟙 B) ≫ g = g := by simp
        rw [h10] ; abel
      exact h9
    exact h5
  let s' : B ⟶ K := kernel.lift p s hs
  have hs' : s' ≫ k = s := kernel.lift_ι p s hs
  let π : K ⟶ B := b
  have h1 : s' ≫ π = 𝟙 B := by
    dsimp only [π, b]
    calc
      s' ≫ (k ≫ pB)
        = (s' ≫ k) ≫ pB := by rw [Category.assoc]
      _ = s ≫ pB := by rw [hs']
      _ = ((-(g ≫ inv f)) ≫ iA + (𝟙 B) ≫ iB) ≫ pB := by rfl
      _ = ((-(g ≫ inv f)) ≫ iA) ≫ pB + ((𝟙 B) ≫ iB) ≫ pB := by rw [add_comp]
      _ = (-(g ≫ inv f)) ≫ (iA ≫ pB) + (𝟙 B) ≫ (iB ≫ pB) := by
        rw [Category.assoc, Category.assoc]
      _ = (-(g ≫ inv f)) ≫ 0 + (𝟙 B) ≫ (𝟙 B) := by rw [hiA_pB, hiB_pB]
      _ = 𝟙 B := by simp
  have h_k_decomp : k = a ≫ iA + b ≫ iB := by
    calc
      k = k ≫ 𝟙 X := by rw [Category.comp_id]
      _ = k ≫ (pA ≫ iA + pB ≫ iB) := by rw [h_total]
      _ = k ≫ (pA ≫ iA) + k ≫ (pB ≫ iB) := by rw [comp_add]
      _ = (k ≫ pA) ≫ iA + (k ≫ pB) ≫ iB := by
        rw [Category.assoc, Category.assoc]
      _ = a ≫ iA + b ≫ iB := by rfl
  have h_key : a ≫ f = -(b ≫ g) := by
    have h_zero : k ≫ p = 0 := kernel.condition p
    have h_eq1 : k ≫ p = (a ≫ iA + b ≫ iB) ≫ p := by rw [h_k_decomp]
    rw [h_eq1] at h_zero
    have h_eq2 : (a ≫ iA + b ≫ iB) ≫ p = (a ≫ iA) ≫ p + (b ≫ iB) ≫ p := by
      rw [add_comp]
    rw [h_eq2] at h_zero
    have h_eq3 : (a ≫ iA) ≫ p + (b ≫ iB) ≫ p = a ≫ (iA ≫ p) + b ≫ (iB ≫ p) := by
      have h1 : (a ≫ iA) ≫ p = a ≫ (iA ≫ p) := by rw [Category.assoc]
      have h2 : (b ≫ iB) ≫ p = b ≫ (iB ≫ p) := by rw [Category.assoc]
      rw [h1, h2]
    rw [h_eq3, hp_iA, hp_iB] at h_zero
    exact add_eq_zero_iff_eq_neg.mp h_zero
  have h_a_eq : a = b ≫ (-(g ≫ inv f)) := by
    have h : a ≫ f = -(b ≫ g) := h_key
    have h2 : (a ≫ f) ≫ inv f = (-(b ≫ g)) ≫ inv f := by rw [h]
    have h3 : (a ≫ f) ≫ inv f = a := by
      have h31 : (a ≫ f) ≫ inv f = a ≫ (f ≫ inv f) := by rw [Category.assoc]
      rw [h31]
      have h32 : f ≫ inv f = 𝟙 A := IsIso.hom_inv_id f
      rw [h32] ; simp
    have h4 : (-(b ≫ g)) ≫ inv f = b ≫ (-(g ≫ inv f)) := by
      have h41 : (-(b ≫ g)) ≫ inv f = -((b ≫ g) ≫ inv f) := by exact neg_comp (b ≫ g) (inv f)
      have h42 : (b ≫ g) ≫ inv f = b ≫ (g ≫ inv f) := by rw [Category.assoc]
      have h43 : -((b ≫ g) ≫ inv f) = -(b ≫ (g ≫ inv f)) := by rw [h42]
      have h44 : -(b ≫ (g ≫ inv f)) = b ≫ (-(g ≫ inv f)) := by
        exact (comp_neg b (g ≫ inv f)).symm
      rw [h41, h43, h44]
    calc
      a = (a ≫ f) ≫ inv f := h3.symm
      _ = (-(b ≫ g)) ≫ inv f := h2
      _ = b ≫ (-(g ≫ inv f)) := h4
  have h_s_comp_pA : s ≫ pA = (-(g ≫ inv f)) := by
    calc
      s ≫ pA
        = ((-(g ≫ inv f)) ≫ iA + (𝟙 B) ≫ iB) ≫ pA := by rfl
      _ = ((-(g ≫ inv f)) ≫ iA) ≫ pA + ((𝟙 B) ≫ iB) ≫ pA := by rw [add_comp]
      _ = (-(g ≫ inv f)) ≫ (iA ≫ pA) + (𝟙 B) ≫ (iB ≫ pA) := by
        rw [Category.assoc, Category.assoc]
      _ = (-(g ≫ inv f)) ≫ (𝟙 A) + (𝟙 B) ≫ 0 := by rw [hiA_pA, hiB_pA]
      _ = (-(g ≫ inv f)) := by simp
  have h_s_comp_pB : s ≫ pB = (𝟙 B) := by
    calc
      s ≫ pB
        = ((-(g ≫ inv f)) ≫ iA + (𝟙 B) ≫ iB) ≫ pB := by rfl
      _ = ((-(g ≫ inv f)) ≫ iA) ≫ pB + ((𝟙 B) ≫ iB) ≫ pB := by rw [add_comp]
      _ = (-(g ≫ inv f)) ≫ (iA ≫ pB) + (𝟙 B) ≫ (iB ≫ pB) := by
        rw [Category.assoc, Category.assoc]
      _ = (-(g ≫ inv f)) ≫ 0 + (𝟙 B) ≫ (𝟙 B) := by rw [hiA_pB, hiB_pB]
      _ = (𝟙 B) := by simp
  have h_components : (π ≫ s) ≫ pA = a ∧ (π ≫ s) ≫ pB = b := by
    constructor
    · calc
        (π ≫ s) ≫ pA
          = π ≫ (s ≫ pA) := by rw [Category.assoc]
        _ = b ≫ (-(g ≫ inv f)) := by
          dsimp only [π, b] ; rw [h_s_comp_pA]
        _ = a := h_a_eq.symm
    · calc
        (π ≫ s) ≫ pB
          = π ≫ (s ≫ pB) := by rw [Category.assoc]
        _ = b ≫ (𝟙 B) := by
          dsimp only [π, b] ; rw [h_s_comp_pB]
        _ = b := by simp
  have h_cancel : ∀ (x y : K ⟶ X), x ≫ pA = y ≫ pA → x ≫ pB = y ≫ pB → x = y := by
    intro x y h1 h2
    have h1' : x ≫ (pA ≫ iA) = y ≫ (pA ≫ iA) := by
      calc
        x ≫ (pA ≫ iA) = (x ≫ pA) ≫ iA := by rw [Category.assoc]
        _ = (y ≫ pA) ≫ iA := by rw [h1]
        _ = y ≫ (pA ≫ iA) := by rw [Category.assoc]
    have h2' : x ≫ (pB ≫ iB) = y ≫ (pB ≫ iB) := by
      calc
        x ≫ (pB ≫ iB) = (x ≫ pB) ≫ iB := by rw [Category.assoc]
        _ = (y ≫ pB) ≫ iB := by rw [h2]
        _ = y ≫ (pB ≫ iB) := by rw [Category.assoc]
    have h : x ≫ (pA ≫ iA + pB ≫ iB) = y ≫ (pA ≫ iA + pB ≫ iB) := by
      have h3 : x ≫ (pA ≫ iA + pB ≫ iB) = x ≫ (pA ≫ iA) + x ≫ (pB ≫ iB) := by
        rw [comp_add]
      have h4 : y ≫ (pA ≫ iA + pB ≫ iB) = y ≫ (pA ≫ iA) + y ≫ (pB ≫ iB) := by
        rw [comp_add]
      rw [h3, h4, h1', h2']
    rw [h_total] at h
    simpa using h
  have h_eq : π ≫ s = k := by
    exact h_cancel (π ≫ s) k h_components.1 h_components.2
  have h2 : π ≫ s' = 𝟙 K := by
    have h_main : (π ≫ s') ≫ k = (𝟙 K) ≫ k := by
      calc
        (π ≫ s') ≫ k
          = π ≫ (s' ≫ k) := by rw [Category.assoc]
        _ = π ≫ s := by rw [hs']
        _ = k := h_eq
        _ = (𝟙 K) ≫ k := by simp
    have h_mono_k : Mono k := by exact equalizer.ι_mono
    exact (cancel_mono k).mp h_main
  exact
    { hom := π
      inv := s'
      hom_inv_id := h2
      inv_hom_id := h1 }

end GeneralBiprodKernel

-- ============================================================
-- H₀ computation from exactness (copy of atlas's version)
-- ============================================================

section AbelianLemmas

variable {A B C' : C}

omit [HasCoproducts C] [HasBinaryBiproducts C] [HasBinaryBiproducts (ChainComplex C ℕ)] in
/-- Given exactness at B, we have a SES 0 → ker(f) → A → ker(g) → 0. -/
lemma shortExactOfExactAtMiddle (f : A ⟶ B) (g : B ⟶ C') (hfg : f ≫ g = 0)
    (h_exact_B : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk (kernel.ι f) (kernel.lift g f hfg)
      (show (kernel.ι f) ≫ kernel.lift g f hfg = 0 from by
        have h1 : kernel.ι f ≫ f = 0 := kernel.condition f
        haveI : Mono (kernel.ι g) := by exact equalizer.ι_mono
        apply (cancel_mono (kernel.ι g)).mp
        rw [Category.assoc, kernel.lift_ι g f hfg]
        rw [zero_comp]
        exact h1)).ShortExact := by
  let e : A ⟶ kernel g := kernel.lift g f hfg
  let k : kernel f ⟶ A := kernel.ι f
  have h_zero : k ≫ e = 0 := by
    have h1 : k ≫ f = 0 := kernel.condition f
    haveI : Mono (kernel.ι g) := by exact equalizer.ι_mono
    apply (cancel_mono (kernel.ι g)).mp
    have h2 : (k ≫ e) ≫ kernel.ι g = 0 := by
      have h3 : (k ≫ e) ≫ kernel.ι g = k ≫ (e ≫ kernel.ι g) := by rw [Category.assoc]
      rw [h3, kernel.lift_ι g f hfg]
      exact h1
    simpa using h2
  let S' := ShortComplex.mk k e h_zero
  have h_mono_k : Mono k := by exact equalizer.ι_mono
  have h_epi_e : Epi e := h_exact_B.epi_kernelLift
  letI : Mono S'.f := h_mono_k
  letI : Epi S'.g := h_epi_e
  have h_exact_middle : S'.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    let l : kernel f ⟶ kernel e := kernel.lift e k h_zero
    have h_key : ∀ {X : C} (x : X ⟶ A), x ≫ e = 0 ↔ x ≫ f = 0 := by
      intro X x
      constructor
      · intro h
        have h6 : x ≫ f = x ≫ (e ≫ kernel.ι g) := by rw [kernel.lift_ι g f hfg]
        rw [h6, ← Category.assoc, h, zero_comp]
      · intro h
        haveI : Mono (kernel.ι g) := by exact equalizer.ι_mono
        apply (cancel_mono (kernel.ι g)).mp
        have h7 : (x ≫ e) ≫ kernel.ι g = x ≫ (e ≫ kernel.ι g) := by rw [Category.assoc]
        rw [h7, kernel.lift_ι g f hfg, h] ; simp
    have h_cond : kernel.ι e ≫ f = 0 := (h_key (kernel.ι e)).mp (kernel.condition e)
    let l' : kernel e ⟶ kernel f := kernel.lift f (kernel.ι e) h_cond
    have h_inv : l' ≫ l = 𝟙 (kernel e) := by
      have h : (l' ≫ l) ≫ kernel.ι e = (𝟙 (kernel e)) ≫ kernel.ι e := by
        calc
          (l' ≫ l) ≫ kernel.ι e
            = l' ≫ (l ≫ kernel.ι e) := by rw [Category.assoc]
          _ = l' ≫ k := by rw [kernel.lift_ι]
          _ = kernel.ι e := by rw [kernel.lift_ι]
          _ = (𝟙 (kernel e)) ≫ kernel.ι e := by simp
      haveI : Mono (kernel.ι e) := by exact equalizer.ι_mono
      exact (cancel_mono (kernel.ι e)).mp h
    have h_split_epi : SplitEpi l := ⟨l', h_inv⟩
    letI : SplitEpi l := h_split_epi
    exact SplitEpi.epi h_split_epi
  exact { exact := h_exact_middle }

/-- A splitting gives X₂ ≅ X₁ ⊕ X₃. -/
noncomputable def splittingIsoBiprod {S : ShortComplex C} (hS : S.Splitting) :
    S.X₂ ≅ S.X₁ ⊞ S.X₃ := by
  let f := S.f
  let g := S.g
  let r : S.X₂ ⟶ S.X₁ := hS.r
  let s : S.X₃ ⟶ S.X₂ := hS.s
  have h_fr : f ≫ r = 𝟙 S.X₁ := hS.f_r
  have h_sg : s ≫ g = 𝟙 S.X₃ := hS.s_g
  have h_rf : r ≫ f + g ≫ s = 𝟙 S.X₂ := hS.id
  have h_sr : s ≫ r = 0 := hS.s_r
  have h_fg : f ≫ g = 0 := S.zero
  let to_biprod : S.X₁ ⊞ S.X₃ ⟶ S.X₂ := biprod.desc f s
  let fro_biprod : S.X₂ ⟶ S.X₁ ⊞ S.X₃ := biprod.lift r g
  have h11 : biprod.inl ≫ (to_biprod ≫ fro_biprod) ≫ biprod.fst =
      biprod.inl ≫ (𝟙 (S.X₁ ⊞ S.X₃)) ≫ biprod.fst := by
    simp [to_biprod, fro_biprod, biprod.lift_fst, Category.assoc, h_fr]
  have h12 : biprod.inr ≫ (to_biprod ≫ fro_biprod) ≫ biprod.fst =
      biprod.inr ≫ (𝟙 (S.X₁ ⊞ S.X₃)) ≫ biprod.fst := by
    simp [to_biprod, fro_biprod, biprod.lift_fst, Category.assoc, h_sr]
  have h_fst : (to_biprod ≫ fro_biprod) ≫ biprod.fst = (𝟙 (S.X₁ ⊞ S.X₃)) ≫ biprod.fst := by
    exact biprod.hom_ext' ((to_biprod ≫ fro_biprod) ≫ biprod.fst) (𝟙 (S.X₁ ⊞ S.X₃) ≫ biprod.fst) h11 h12
  have h21 : biprod.inl ≫ (to_biprod ≫ fro_biprod) ≫ biprod.snd =
      biprod.inl ≫ (𝟙 (S.X₁ ⊞ S.X₃)) ≫ biprod.snd := by
    simp [to_biprod, fro_biprod, biprod.lift_snd, Category.assoc, h_fg]
  have h22 : biprod.inr ≫ (to_biprod ≫ fro_biprod) ≫ biprod.snd =
      biprod.inr ≫ (𝟙 (S.X₁ ⊞ S.X₃)) ≫ biprod.snd := by
    simp [to_biprod, fro_biprod, biprod.lift_snd, Category.assoc, h_sg]
  have h_snd : (to_biprod ≫ fro_biprod) ≫ biprod.snd = (𝟙 (S.X₁ ⊞ S.X₃)) ≫ biprod.snd := by
    exact biprod.hom_ext' ((to_biprod ≫ fro_biprod) ≫ biprod.snd) (𝟙 (S.X₁ ⊞ S.X₃) ≫ biprod.snd) h21 h22
  have h_to_fro : to_biprod ≫ fro_biprod = 𝟙 (S.X₁ ⊞ S.X₃) := by exact biprod.hom_ext (to_biprod ≫ fro_biprod) (𝟙 (S.X₁ ⊞ S.X₃)) h_fst h_snd
  have h_fro_to : fro_biprod ≫ to_biprod = 𝟙 S.X₂ := by
    have h : fro_biprod ≫ to_biprod = r ≫ f + g ≫ s := by
      simp [to_biprod, fro_biprod, biprod.lift_desc]
    rw [h, h_rf]
  exact
    { hom := fro_biprod
      inv := to_biprod
      hom_inv_id := h_fro_to
      inv_hom_id := h_to_fro }

/-- **H₀ computation from exactness at the middle object.** -/
noncomputable def h0_computation_from_exact
    (f : A ⟶ B) (g : B ⟶ C') (hfg : f ≫ g = 0)
    (h_ker_f_iso : kernel f ≅ R)
    (h_ker_g_iso : kernel g ≅ R)
    (h_exact_B : (ShortComplex.mk f g hfg).Exact) :
    A ≅ R ⊞ R := by
  let e : A ⟶ kernel g := kernel.lift g f hfg
  let k : kernel f ⟶ A := kernel.ι f
  have h_zero : k ≫ e = 0 := by
    have h1 : k ≫ f = 0 := kernel.condition f
    haveI : Mono (kernel.ι g) := by exact equalizer.ι_mono
    apply (cancel_mono (kernel.ι g)).mp
    have h2 : (k ≫ e) ≫ kernel.ι g = 0 := by
      have h3 : (k ≫ e) ≫ kernel.ι g = k ≫ (e ≫ kernel.ι g) := by rw [Category.assoc]
      rw [h3, kernel.lift_ι g f hfg]
      exact h1
    simpa using h2
  let S' := ShortComplex.mk k e h_zero
  have hS_ses : S'.ShortExact := shortExactOfExactAtMiddle f g hfg h_exact_B
  letI : Projective (kernel g) := (Projective.iso_iff h_ker_g_iso).mpr inferInstance
  have h_split : S'.Splitting := hS_ses.splittingOfProjective
  have h_iso1 : S'.X₂ ≅ S'.X₁ ⊞ S'.X₃ := splittingIsoBiprod h_split
  have h_iso2 : A ≅ (kernel f) ⊞ (kernel g) := by
    simpa [S'] using h_iso1
  have h_iso3 : (kernel f) ⊞ (kernel g) ≅ R ⊞ R :=
    biprod.mapIso h_ker_f_iso h_ker_g_iso
  exact h_iso2 ≪≫ h_iso3

end AbelianLemmas

-- ============================================================
-- Degree-0 boundary isomorphism
-- ============================================================

section DegreeZeroBoundary

variable {S : ShortComplex (ChainComplex C ℕ)} (hS : S.ShortExact)

/-- **Degree-0 boundary isomorphism (general version).** -/
noncomputable def degreeZeroBoundaryIso
    (h1 : IsZero (S.X₂.homology 1)) :
    S.X₃.homology 1 ≅ kernel (homologyMap S.f 0) := by
  have hij : (ComplexShape.down ℕ).Rel 1 0 := by
    simp [ComplexShape.down_Rel]
  let δ : S.X₃.homology 1 ⟶ S.X₁.homology 0 := hS.δ 1 0 hij
  let g : S.X₁.homology 0 ⟶ S.X₂.homology 0 := homologyMap S.f 0
  have h_mono_δ : Mono δ := hS.mono_δ 1 0 hij h1
  have h_zero : δ ≫ g = 0 := hS.δ_comp 1 0 hij
  let S' : ShortComplex C := ShortComplex.mk δ g h_zero
  have h_exact : S'.Exact := hS.homology_exact₁ 1 0 hij
  have h_epi_lift : Epi (kernel.lift g δ h_zero) :=
    S'.exact_iff_epi_kernel_lift.mp h_exact
  have h_mono_lift : Mono (kernel.lift g δ h_zero) := by exact kernel.lift_mono g δ h_zero
  letI : IsIso (kernel.lift g δ h_zero) := isIso_of_mono_of_epi (kernel.lift g δ h_zero)
  exact asIso (kernel.lift g δ h_zero)

end DegreeZeroBoundary

-- ============================================================
-- Main theorem: MV H₀ of the intersection
-- ============================================================

section MVDegree0Main

variable (ts : TwoSubspaces.{w})
variable (h_is_pullback : IsPullback ts.iU ts.iV ts.jU ts.jV)
variable (h_jU_emb : Topology.IsEmbedding ts.jU)
variable (h_jV_emb : Topology.IsEmbedding ts.jV)
variable (h_small_chain : ∀ n : ℕ, IsIso (homologyMap (smallChainInclusion C R ts) n))
variable (h1_U : IsZero (singularHomology' C R 1 ts.U))
variable (h1_V : IsZero (singularHomology' C R 1 ts.V))
variable (h_h1_X : singularHomology' C R 1 ts.X ≅ R)
variable (h_h0_U_iso : singularHomology' C R 0 ts.U ≅ R)
variable (h_h0_V_iso : singularHomology' C R 0 ts.V ≅ R)
variable (h_h0_jU_iso : IsIso (homologyMap ((singularChainComplexFunctor C).obj R |>.map ts.jU) 0))

/-- **H₀ of the intersection: H₀(UV) ≅ R ⊕ R.**

    This is the main degree-0 Mayer-Vietoris result. -/
noncomputable def mv_h0_UV_iso :
    singularHomology' C R 0 ts.UV ≅ R ⊞ R := by
  haveI hMono_jU : Mono ts.jU := by
    rw [TopCat.mono_iff_injective ts.jU]
    exact h_jU_emb.injective
  haveI hMono_jV : Mono ts.jV := by
    rw [TopCat.mono_iff_injective ts.jV]
    exact h_jV_emb.injective
  haveI h_small_chain_iso1 : IsIso (homologyMap (smallChainInclusion C R ts) 1) := h_small_chain 1
  haveI h_small_chain_iso0 : IsIso (homologyMap (smallChainInclusion C R ts) 0) := h_small_chain 0
  have h_iU_emb : Topology.IsEmbedding ts.iU := by
    have h_can : IsPullback (Limits.pullback.fst ts.jU ts.jV)
        (Limits.pullback.snd ts.jU ts.jV) ts.jU ts.jV := by exact IsPullback.of_hasPullback ts.jU ts.jV
    let e : ts.UV ≅ Limits.pullback ts.jU ts.jV :=
      h_is_pullback.isoIsPullback ts.U ts.V h_can
    have h_eq1 : e.hom ≫ Limits.pullback.fst ts.jU ts.jV = ts.iU :=
      h_is_pullback.isoIsPullback_hom_fst ts.U ts.V h_can
    have h_fst_emb : Topology.IsEmbedding (Limits.pullback.fst ts.jU ts.jV) :=
      TopCat.fst_isEmbedding_of_right ts.jU (show Topology.IsEmbedding (↑ts.jV) from h_jV_emb)
    have h_e_emb : Topology.IsEmbedding e.hom :=
      (TopCat.homeoOfIso e).isEmbedding
    have h : Topology.IsEmbedding (e.hom ≫ Limits.pullback.fst ts.jU ts.jV) :=
      h_fst_emb.comp h_e_emb
    rwa [h_eq1] at h
  haveI hMono_iU : Mono ts.iU := by
    rw [TopCat.mono_iff_injective ts.iU]
    exact h_iU_emb.injective
  have h_dw_pullback : DegreewisePullbackAssumption ts :=
    degreewisePullback_of_isPullback_of_embeddings ts h_is_pullback h_jU_emb h_jV_emb
  let hS : (mvShortComplex C R ts).ShortExact :=
    mvSES_shortExact' C R ts h_dw_pullback
  let K_U := singularChainComplex' C R ts.U
  let K_V := singularChainComplex' C R ts.V
  -- Homology biproduct structure on (K_U ⊞ K_V).homology 0
  let h0_inl : K_U.homology 0 ⟶ (K_U ⊞ K_V).homology 0 :=
    homologyMap (biprod.inl : K_U ⟶ K_U ⊞ K_V) 0
  let h0_inr : K_V.homology 0 ⟶ (K_U ⊞ K_V).homology 0 :=
    homologyMap (biprod.inr : K_V ⟶ K_U ⊞ K_V) 0
  let h0_fst : (K_U ⊞ K_V).homology 0 ⟶ K_U.homology 0 :=
    homologyMap (biprod.fst : K_U ⊞ K_V ⟶ K_U) 0
  let h0_snd : (K_U ⊞ K_V).homology 0 ⟶ K_V.homology 0 :=
    homologyMap (biprod.snd : K_U ⊞ K_V ⟶ K_V) 0
  have h_inl_fst : h0_inl ≫ h0_fst = 𝟙 (K_U.homology 0) := by
    have h : (biprod.inl : K_U ⟶ K_U ⊞ K_V) ≫ (biprod.fst : K_U ⊞ K_V ⟶ K_U) = 𝟙 K_U := by exact biprod.inl_fst
    have h2 : homologyMap ((biprod.inl : K_U ⟶ K_U ⊞ K_V) ≫ (biprod.fst : K_U ⊞ K_V ⟶ K_U)) 0 =
        h0_inl ≫ h0_fst := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h] at h2
    have h3 : homologyMap (𝟙 K_U) 0 = 𝟙 (K_U.homology 0) := by
      simp
    rw [h3] at h2
    exact h2.symm
  have h_inr_snd : h0_inr ≫ h0_snd = 𝟙 (K_V.homology 0) := by
    have h : (biprod.inr : K_V ⟶ K_U ⊞ K_V) ≫ (biprod.snd : K_U ⊞ K_V ⟶ K_V) = 𝟙 K_V := by exact biprod.inr_snd
    have h2 : homologyMap ((biprod.inr : K_V ⟶ K_U ⊞ K_V) ≫ (biprod.snd : K_U ⊞ K_V ⟶ K_V)) 0 =
        h0_inr ≫ h0_snd := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h] at h2
    have h3 : homologyMap (𝟙 K_V) 0 = 𝟙 (K_V.homology 0) := by
      simp
    rw [h3] at h2
    exact h2.symm
  have h_inl_snd : h0_inl ≫ h0_snd = 0 := by
    have h : (biprod.inl : K_U ⟶ K_U ⊞ K_V) ≫ (biprod.snd : K_U ⊞ K_V ⟶ K_V) = 0 := by exact biprod.inl_snd
    have h2 : homologyMap ((biprod.inl : K_U ⟶ K_U ⊞ K_V) ≫ (biprod.snd : K_U ⊞ K_V ⟶ K_V)) 0 =
        h0_inl ≫ h0_snd := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h] at h2
    simpa using h2.symm
  have h_inr_fst : h0_inr ≫ h0_fst = 0 := by
    have h : (biprod.inr : K_V ⟶ K_U ⊞ K_V) ≫ (biprod.fst : K_U ⊞ K_V ⟶ K_U) = 0 := by exact biprod.inr_fst
    have h2 : homologyMap ((biprod.inr : K_V ⟶ K_U ⊞ K_V) ≫ (biprod.fst : K_U ⊞ K_V ⟶ K_U)) 0 =
        h0_inr ≫ h0_fst := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h] at h2
    simpa using h2.symm
  have h_total : h0_fst ≫ h0_inl + h0_snd ≫ h0_inr = 𝟙 ((K_U ⊞ K_V).homology 0) := by
    let f1 := (biprod.fst : K_U ⊞ K_V ⟶ K_U) ≫ (biprod.inl : K_U ⟶ K_U ⊞ K_V)
    let f2 := (biprod.snd : K_U ⊞ K_V ⟶ K_V) ≫ (biprod.inr : K_V ⟶ K_U ⊞ K_V)
    have h_sum : f1 + f2 = 𝟙 (K_U ⊞ K_V) := by exact biprod.total
    have h21 : homologyMap f1 0 = h0_fst ≫ h0_inl := by
      rw [HomologicalComplex.homologyMap_comp]
    have h22 : homologyMap f2 0 = h0_snd ≫ h0_inr := by
      rw [HomologicalComplex.homologyMap_comp]
    have h_add : homologyMap (f1 + f2) 0 = homologyMap f1 0 + homologyMap f2 0 := by exact homologyMap_add f1 f2 0
    have h_id : homologyMap (𝟙 (K_U ⊞ K_V)) 0 = 𝟙 ((K_U ⊞ K_V).homology 0) :=
      by simp
    calc
      h0_fst ≫ h0_inl + h0_snd ≫ h0_inr
        = homologyMap f1 0 + homologyMap f2 0 := by rw [h21, h22]
      _ = homologyMap (f1 + f2) 0 := h_add.symm
      _ = homologyMap (𝟙 (K_U ⊞ K_V)) 0 := by rw [h_sum]
      _ = 𝟙 ((K_U ⊞ K_V).homology 0) := h_id
  -- Degree-0 boundary iso: H₁(X) ≅ ker(H₀(mvMapF))
  let g0 := homologyMap (mvMapF C R ts) 0
  let g1 := homologyMap (mvMapG C R ts) 0
  have h_mid_succ : IsZero ((mvShortComplex C R ts).X₂.homology 1) :=
    isZero_biprod_homology (K := K_U) (L := K_V) (n := 1) h1_U h1_V
  have h_small_boundary_iso :
      (mvShortComplex C R ts).X₃.homology 1 ≅ kernel g0 := by
    exact degreeZeroBoundaryIso hS h_mid_succ
  have h_small_h1_iso : (mvShortComplex C R ts).X₃.homology 1 ≅ singularHomology' C R 1 ts.X := by
    let f := homologyMap (smallChainInclusion C R ts) 1
    have h : IsIso f := h_small_chain 1
    have h_out : ∃ (g : singularHomology' C R 1 ts.X ⟶ (mvShortComplex C R ts).X₃.homology 1),
        f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := h.out
    let g := Classical.choose h_out
    have hg : f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := Classical.choose_spec h_out
    exact ⟨f, g, hg.1, hg.2⟩
  have h_boundary_iso :
      singularHomology' C R 1 ts.X ≅ kernel g0 :=
    h_small_h1_iso.symm ≪≫ h_small_boundary_iso
  have h_ker_f_iso : kernel g0 ≅ R :=
    h_boundary_iso.symm ≪≫ h_h1_X
  have hfg : g0 ≫ g1 = 0 := by
    have h_eq1 : (mvShortComplex C R ts).f = mvMapF C R ts := by rfl
    have h_eq2 : (mvShortComplex C R ts).g = mvMapG C R ts := by rfl
    have h : (mvShortComplex C R ts).f ≫ (mvShortComplex C R ts).g = 0 :=
      (mvShortComplex C R ts).zero
    have h' : mvMapF C R ts ≫ mvMapG C R ts = 0 := by
      rw [←h_eq1, ←h_eq2]
      exact h
    have h2 : homologyMap (mvMapF C R ts ≫ mvMapG C R ts) 0 =
        homologyMap (mvMapF C R ts) 0 ≫ homologyMap (mvMapG C R ts) 0 := by
      exact HomologicalComplex.homologyMap_comp (mvMapF C R ts) (mvMapG C R ts) 0
    have h3 : homologyMap (mvMapF C R ts ≫ mvMapG C R ts) 0 = 0 := by
      rw [h']
      ; simp
    rw [h2] at h3
    exact h3
  have h_exact_middle : (ShortComplex.mk g0 g1 hfg).Exact :=
    hS.homology_exact₂ 0
  -- Show H₀(smallChainFromU) is an isomorphism
  let h_small_incl_0 := homologyMap (smallChainInclusion C R ts) 0
  haveI h_small_incl_iso : IsIso h_small_incl_0 := h_small_chain 0
  let jU_star := (singularChainComplexFunctor C).obj R |>.map ts.jU
  let sU_star := smallChainFromU C R ts
  let sV_star := smallChainFromV C R ts
  have h_sU_comp : sU_star ≫ smallChainInclusion C R ts = jU_star := by
    have h43 : smallChainFromU C R ts = ((SSet.chainComplexFunctor C).obj R).map (smallFromU ts) := by rfl
    have h44 : smallChainInclusion C R ts = ((SSet.chainComplexFunctor C).obj R).map (smallι ts) := by rfl
    have h_goal : smallChainFromU C R ts ≫ smallChainInclusion C R ts =
        ((SSet.chainComplexFunctor C).obj R).map (smallFromU ts ≫ smallι ts) := by
      rw [h43, h44]
      have h45 : ((SSet.chainComplexFunctor C).obj R).map (smallFromU ts) ≫
          ((SSet.chainComplexFunctor C).obj R).map (smallι ts) =
          ((SSet.chainComplexFunctor C).obj R).map (smallFromU ts ≫ smallι ts) := by exact Eq.symm (((SSet.chainComplexFunctor C).obj R).map_comp (smallFromU ts) (smallι ts))
      exact h45
    have h_final : smallChainFromU C R ts ≫ smallChainInclusion C R ts = jU_star := by
      rw [h_goal, smallFromU_comp_ι ts]
      ; rfl
    exact h_final
  have h_h0_sU_iso : IsIso (homologyMap sU_star 0) := by
    have h_comp : homologyMap sU_star 0 ≫ h_small_incl_0 = homologyMap jU_star 0 := by
      have h : homologyMap (sU_star ≫ smallChainInclusion C R ts) 0 =
          homologyMap sU_star 0 ≫ h_small_incl_0 := by
        rw [HomologicalComplex.homologyMap_comp]
      rw [h_sU_comp] at h
      exact h.symm
    haveI : IsIso (homologyMap jU_star 0) := h_h0_jU_iso
    exact IsIso.of_isIso_fac_right h_comp
  -- Components of g1 = H₀(mvMapG) on the homology biproduct
  let f0_U := homologyMap sU_star 0
  let f0_V := homologyMap sV_star 0
  have hp_iA : h0_inl ≫ g1 = f0_U := by
    have h : (biprod.inl : K_U ⟶ K_U ⊞ K_V) ≫ mvMapG C R ts = sU_star := by
      dsimp only [mvMapG, sU_star]
      rw [biprod.inl_desc]
    have h2 : homologyMap ((biprod.inl : K_U ⟶ K_U ⊞ K_V) ≫ mvMapG C R ts) 0 =
        h0_inl ≫ g1 := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h] at h2
    exact h2.symm
  have hp_iB : h0_inr ≫ g1 = f0_V := by
    have h : (biprod.inr : K_V ⟶ K_U ⊞ K_V) ≫ mvMapG C R ts = sV_star := by
      dsimp only [mvMapG, sV_star]
      rw [biprod.inr_desc]
    have h2 : homologyMap ((biprod.inr : K_V ⟶ K_U ⊞ K_V) ≫ mvMapG C R ts) 0 =
        h0_inr ≫ g1 := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h] at h2
    exact h2.symm
  -- Apply general kernel lemma
  haveI : IsIso f0_U := h_h0_sU_iso
  have h_ker_g1_iso : kernel g1 ≅ K_V.homology 0 :=
    generalBiprodKernelIso h0_inl h0_inr h0_fst h0_snd h_inl_fst h_inr_snd h_inl_snd h_inr_fst h_total g1 f0_U f0_V hp_iA hp_iB
  have h_ker_g_iso : kernel g1 ≅ R :=
    h_ker_g1_iso ≪≫ h_h0_V_iso
  -- Apply h0_computation_from_exact
  exact h0_computation_from_exact R g0 g1 hfg h_ker_f_iso h_ker_g_iso h_exact_middle

end MVDegree0Main

end AlgebraicTopology

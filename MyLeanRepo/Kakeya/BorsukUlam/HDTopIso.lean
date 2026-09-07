/-
# H_n(D) ≅ Z/2 — Top Homology of Transfer Complex

## Proof

For n ≥ 1:

1. Quotient SES: 0 → D → C(S^n) → C(RP^n) → 0
   LES gives: H_{n+1}(RP^n) → H_n(D) → H_n(S^n)
   Since H_{n+1}(RP^n) = 0, iStar: H_n(D) → H_n(S^n) is mono.

2. Transfer SES LES: H_n(D) → H_n(S^n) → H_n(D)
   If H_n(D) = 0, then iStar = 0, exactness gives Mono qStar,
   and qStar = 0 (target zero), so Mono(0) implies H_n(S^n) = 0,
   contradicting H_n(S^n) ≅ Z/2.

3. Since iStar is mono and H_n(D) ≠ 0, and H_n(S^n) ≅ Z/2,
   iStar is an isomorphism.

For n=1, we use the direct proof via RP^1 ≅ S^1 (BaseCaseH1),
avoiding the vanishing axiom.

## Whiteprint Node
- hD_top_iso
-/

import MyLeanRepo.Kakeya.BorsukUlam.QuotientSESFull
import MyLeanRepo.Kakeya.BorsukUlam.BaseCaseH1
import MyLeanRepo.Kakeya.BorsukUlam.TransferInstantiation
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.CategoryBridge
import MyLeanRepo.Kakeya.BorsukUlam.OddDegreeHomology
import MyLeanRepo.Kakeya.BorsukUlam.RPHomologyVanishing
import MyLeanRepo.Kakeya.BorsukUlam.RealProjective.MetricEmbedding
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequence

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open BorsukUlamBackup
open BorsukUlam.QuotientSESFull
open BorsukUlam.OddDegreeHomology
open BorsukUlam.BaseCaseH1
open BorsukUlam.RealProjective.Cover

variable {n : ℕ}

namespace BorsukUlam.OddDegreeHomology

/-- H_{n+1}(RP^n) = 0 for n ≥ 1.

Proved via RP^n homology vanishing above dimension n, using the
Mayer-Vietoris induction and the Z/2 small chain theorem. -/
lemma hRPVanishing (n : ℕ) (hn : 1 ≤ n) :
    IsZero (((QuotientSESFull.quotientShortComplex n).map forgetZ2Chain).X₃.homology (n + 1)) := by
  let C := ((QuotientSESFull.quotientShortComplex n).map forgetZ2Chain).X₃
  -- C = singular chains of RPType n with Z/2, viewed in AddCommGrpCat
  let e1 : C ≅
      ((singularChainComplexFunctor AddCommGrpCat).obj (forgetZ2.obj (BorsukUlamBackup.R2))).obj
        (TopCat.of (BorsukUlam.BackupRoute.RPType n)) :=
    singularChainComplexForgetIso (TopCat.of (BorsukUlam.BackupRoute.RPType n))
  -- Homology isomorphism from chain complex isomorphism
  let h1 : C.homology (n + 1) ≅
      singularHomology' AddCommGrpCat (forgetZ2.obj (BorsukUlamBackup.R2)) (n + 1)
        (TopCat.of (BorsukUlam.BackupRoute.RPType n)) :=
    HomologicalComplex.homologyMapIso e1 (n + 1)
  -- Homeomorphism RPType n ≃ₜ EmbeddedRP n
  let h_homeo : BorsukUlam.BackupRoute.RPType n ≃ₜ EmbeddedRP n :=
    BorsukUlam.RealProjective.veroneseHomeo n
  let e_homotopy : ContinuousMap.HomotopyEquiv
      (BorsukUlam.BackupRoute.RPType n) (EmbeddedRP n) :=
    h_homeo.toHomotopyEquiv
  -- Homology isomorphism from homeomorphism
  let h2 : singularHomology' AddCommGrpCat (forgetZ2.obj (BorsukUlamBackup.R2)) (n + 1)
        (TopCat.of (BorsukUlam.BackupRoute.RPType n)) ≅
      singularHomology' AddCommGrpCat BorsukUlam.BackupRoute.R2 (n + 1)
        (TopCat.of (EmbeddedRP n)) :=
    singularHomologyIsoOfHomotopyEquiv (C := AddCommGrpCat) (n := n + 1)
      (R := forgetZ2.obj (BorsukUlamBackup.R2))
      (X := TopCat.of (BorsukUlam.BackupRoute.RPType n))
      (Y := TopCat.of (EmbeddedRP n))
      e_homotopy
  -- Vanishing above dimension n
  have h3 : IsZero (singularHomology' AddCommGrpCat BorsukUlam.BackupRoute.R2 (n + 1)
        (TopCat.of (EmbeddedRP n))) :=
    BorsukUlam.RPHomologyVanishing.rpHomologyVanishing n (n + 1) (by linarith)
  -- Transfer IsZero back through the isomorphisms
  exact IsZero.of_iso h3 (h1 ≪≫ h2)

/-- Helper: any element of Z/2 is 0 or 1. -/
lemma z2_eq_zero_or_one' (z : BorsukUlam.BackupRoute.R2) : z = 0 ∨ z = 1 := by
  have h' : ∀ (x : ZMod 2), x = 0 ∨ x = 1 := by
    intro x
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h : (z : ZMod 2) = 0 ∨ (z : ZMod 2) = 1 := h' (z : ZMod 2)
  exact_mod_cast h

/-- H_n(D) ≅ Z/2 for all n ≥ 1.

For n=1, uses the direct proof via RP^1 ≅ S^1 (no axiom).
For n≥2, uses the quotient SES LES with the hRPVanishing axiom. -/
noncomputable def hD_top_iso (n : ℕ) (hn : 1 ≤ n) :
    (S_Add n).X₁.homology n ≅ BorsukUlam.BackupRoute.R2 := by
  by_cases h_n1 : n = 1
  · -- Base case n=1: direct proof via RP^1 ≅ S^1
    subst h_n1
    exact h1D_S1_iso_Z2
  · -- General case n≥2: quotient SES LES proof
    have h_n2 : 2 ≤ n := by omega
    let S_quot := (QuotientSESFull.quotientShortComplex n).map forgetZ2Chain
    let hS_quot : S_quot.ShortExact :=
      (QuotientSESFull.quotientShortExact n).map_of_exact forgetZ2Chain
    let hS_trans := hS_Add n
    let iStar := HomologicalComplex.homologyMap (S_Add n).f n
    let qStar := HomologicalComplex.homologyMap (S_Add n).g n
    let H_D := (S_Add n).X₁.homology n
    let H_C := (S_Add n).X₂.homology n

    -- Step 1: iStar is injective (from quotient LES)
    have hij : (ComplexShape.down ℕ).Rel (n + 1) n := by
      simp [ComplexShape.down_Rel] <;> omega
    let δ_quot : S_quot.X₃.homology (n + 1) ⟶ H_D := hS_quot.δ (n + 1) n hij
    have h_exact_quot : (ShortComplex.mk δ_quot iStar _).Exact :=
      hS_quot.homology_exact₁ (n + 1) n hij
    have hδ_zero : δ_quot = 0 := IsZero.eq_zero_of_src (hRPVanishing n hn) δ_quot
    have h_iStar_mono : Mono iStar := h_exact_quot.mono_g_iff.mpr hδ_zero

    -- Step 2: H_n(D) is not zero (from transfer LES)
    have h_exact_trans : (ShortComplex.mk iStar qStar _).Exact :=
      hS_trans.homology_exact₂ n
    have hC_iso : H_C ≅ BorsukUlam.BackupRoute.R2 := hC_topIso n hn
    have hC_not_zero : ¬ IsZero H_C := by
      intro h
      have hR2_zero : IsZero BorsukUlam.BackupRoute.R2 :=
        IsZero.of_iso h hC_iso.symm
      have h_id_zero : (𝟙 BorsukUlam.BackupRoute.R2) = 0 :=
        hR2_zero.eq_zero_of_src (𝟙 _)
      have h1 : (1 : BorsukUlam.BackupRoute.R2) = 0 := by
        have h2 : ∀ (f : BorsukUlam.BackupRoute.R2 ⟶ BorsukUlam.BackupRoute.R2),
            f = 0 → ∀ (x : BorsukUlam.BackupRoute.R2), f x = 0 := by
          intro f hf x
          rw [hf] <;> simp
        exact h2 (𝟙 _) h_id_zero 1
      simpa using h1
    have hD_not_zero : ¬ IsZero H_D := by
      intro hD
      have hi_zero : iStar = 0 := IsZero.eq_zero_of_src hD iStar
      have h_mono_q : Mono qStar := h_exact_trans.mono_g_iff.mpr hi_zero
      have hq_zero : qStar = 0 := IsZero.eq_zero_of_tgt hD qStar
      have h_mono_zero : Mono (0 : H_C ⟶ H_D) := by
        have h : Mono qStar := h_mono_q
        rwa [hq_zero] at h
      have hC_zero : IsZero H_C := IsZero.of_mono_zero H_C H_D
      exact hC_not_zero hC_zero

    -- Step 3: iStar ≠ 0 (since H_n(D) ≠ 0 and iStar is mono)
    have h_iStar_ne_zero : iStar ≠ 0 := by
      intro h
      have h_mono_zero : Mono (0 : H_D ⟶ H_C) := by
        have h' : Mono iStar := h_iStar_mono
        rwa [h] at h'
      have hD_zero : IsZero H_D := IsZero.of_mono_zero H_D H_C
      exact hD_not_zero hD_zero

    -- Step 4: iStar is surjective (nonzero map to Z/2)
    let eC : H_C ≅ BorsukUlam.BackupRoute.R2 := hC_iso
    let iStar' : H_D ⟶ BorsukUlam.BackupRoute.R2 := iStar ≫ eC.hom
    letI : Mono iStar := h_iStar_mono
    have h_iStar'_mono : Mono iStar' := mono_comp iStar eC.hom
    have h_iStar'_ne_zero : iStar' ≠ 0 := by
      intro h
      have h5 : iStar = 0 := by
        calc iStar = iStar' ≫ eC.inv := by simp [iStar', Category.assoc] <;> rfl
        _ = 0 := by rw [h] <;> simp
      exact h_iStar_ne_zero h5
    have h_surj : Function.Surjective iStar' := by
      intro y
      have h_y_cases : y = 0 ∨ y = 1 := z2_eq_zero_or_one' y
      rcases h_y_cases with (rfl | rfl)
      · exact ⟨0, by simp⟩
      · have h6 : ∃ (x : H_D), iStar' x ≠ 0 := by
          by_contra h7
          push Not at h7
          have h8 : iStar' = 0 := by
            apply AddCommGrpCat.ext
            intro x
            exact h7 x
          exact h_iStar'_ne_zero h8
        rcases h6 with ⟨x, hx⟩
        have h9 : iStar' x = 1 := by
          have h11 : iStar' x = 0 ∨ iStar' x = 1 := z2_eq_zero_or_one' (iStar' x)
          rcases h11 with (h11 | h11)
          · exfalso; exact hx h11
          · exact h11
        exact ⟨x, h9⟩
    have h_inj : Function.Injective iStar' :=
      (AddCommGrpCat.mono_iff_injective iStar').mp h_iStar'_mono
    have h_bij : Function.Bijective iStar' := ⟨h_inj, h_surj⟩
    have h_iso : IsIso iStar' := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact h_bij
    exact asIso iStar'

end BorsukUlam.OddDegreeHomology

end

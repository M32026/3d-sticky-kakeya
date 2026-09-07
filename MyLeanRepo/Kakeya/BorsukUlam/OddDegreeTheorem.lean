/-
# Odd Degree Theorem — Complete Proof

Proves `odd_degree_lemma`: any odd continuous self-map of S^n has odd degree.

Uses `fC_id` from OddDegreeHomology, then transfers to standard singular homology
and applies `degree_odd_of_z2_id`.

## Whiteprint Node
- odd_degree_lemma_homology
-/

import MyLeanRepo.Kakeya.BorsukUlam.OddDegreeHomology
import MyLeanRepo.Kakeya.BorsukUlam.FCId
import MyLeanRepo.Kakeya.BorsukUlam.Mod2Degree
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.CategoryBridge
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.Degree.Homology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open Vendored.AlgebraicTopology.Degree
open BorsukUlamBackup
open BorsukUlam.OddDegreeHomology

namespace BorsukUlam.OddDegreeTheorem

/-! ## Chain complex isomorphism naturality -/

/-- Naturality of the chain complex forgetful isomorphism. -/
lemma chainIso_naturality (n : ℕ) (f : C(Sphere n, Sphere n)) :
    f_C_Add f ≫ (chainIso n).hom =
    (chainIso n).hom ≫ ((singularChainComplexFunctor AddCommGrpCat).obj
      BorsukUlam.BackupRoute.R2).map (TopCat.ofHom f) :=
  singularChainComplexForgetIso_naturality (TopCat.ofHom f)

/-! ## Main theorem -/

/-- The odd degree lemma: any odd self-map of S^n has odd degree. -/
theorem odd_degree_lemma (n : ℕ) (hm : 0 < n)
    (f : C(Sphere n, Sphere n))
    (hf_odd : ∀ x, f (-x) = -f x) :
    degree f hm ≠ 0 := by
  have hn' : 1 ≤ n := by linarith
  have hf_odd' : ∀ x, f (ap x) = ap (f x) := by
    intro x
    have h1 : (ap x : Sphere n) = -x := by
      exact SetCoe.ext rfl
    have h2 : (ap (f x) : Sphere n) = -(f x) := by
      exact SetCoe.ext rfl
    rw [h1, h2]
    exact hf_odd x

  let fC : (S_Add n).X₂ ⟶ (S_Add n).X₂ := f_C_Add f

  have h_main : HomologicalComplex.homologyMap fC n =
      𝟙 ((S_Add n).X₂.homology n) := fC_id n hn' f hf_odd'

  let e_hom : (S_Add n).X₂.homology n ≅
      singularHomology' AddCommGrpCat BorsukUlam.BackupRoute.R2 n (TopCat.of (Sphere n)) :=
    homologyIso n n

  have h_chain : fC ≫ (chainIso n).hom =
      (chainIso n).hom ≫ ((singularChainComplexFunctor AddCommGrpCat).obj
        BorsukUlam.BackupRoute.R2).map (TopCat.ofHom f) :=
    chainIso_naturality n f

  have h_nat : HomologicalComplex.homologyMap fC n ≫ e_hom.hom =
      e_hom.hom ≫ ((singularHomologyFunctor AddCommGrpCat n).obj
        BorsukUlam.BackupRoute.R2).map (TopCat.ofHom f) := by
    let singularMap := ((singularChainComplexFunctor AddCommGrpCat).obj
        BorsukUlam.BackupRoute.R2).map (TopCat.ofHom f)
    let homologySingularMap := ((singularHomologyFunctor AddCommGrpCat n).obj
        BorsukUlam.BackupRoute.R2).map (TopCat.ofHom f)
    have h_e_def : e_hom.hom = HomologicalComplex.homologyMap (chainIso n).hom n := by rfl
    have h := congr_arg (fun (k : _) => HomologicalComplex.homologyMap k n) h_chain
    simp only [HomologicalComplex.homologyMap_comp] at h
    convert h using 2 <;> rfl

  have h_std_id : ((singularHomologyFunctor AddCommGrpCat n).obj
        BorsukUlam.BackupRoute.R2).map (TopCat.ofHom f) = 𝟙 _ := by
    rw [h_main] at h_nat
    have h4 : e_hom.hom ≫ ((singularHomologyFunctor AddCommGrpCat n).obj
          BorsukUlam.BackupRoute.R2).map (TopCat.ofHom f) = e_hom.hom := by
      simpa [Category.id_comp] using h_nat.symm
    exact (cancel_epi e_hom.hom).mp h4

  have h_surj : Epi (coeffChangeHomology (TopSphere n) n) :=
    coeffChange_surjective n hn'

  let e_z2 : singularHomology' AddCommGrpCat BorsukUlam.BackupRoute.R2 n
      (TopCat.of (Sphere n)) ≅ BorsukUlam.BackupRoute.R2 :=
    BorsukUlam.BackupRoute.topSphereHomologyIsoZ2 n hn'

  have h_odd : Odd (degree f hm) :=
    degree_odd_of_z2_id f hm h_std_id h_surj e_z2

  rcases h_odd with ⟨k, hk⟩
  omega

end BorsukUlam.OddDegreeTheorem

end

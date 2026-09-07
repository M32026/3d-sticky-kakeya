module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.HomologyZero

@[expose] public section

/-!
# Kernel isomorphism lemma

Given isomorphic domains and compatible maps to the same codomain,
their kernels are isomorphic.

This is a key lemma for proving homotopy invariance of reduced homology:
if `e : X ≅ Y` is a homotopy equivalence (inducing an isomorphism on H₀),
and `ε_X : H₀(X) → R`, `ε_Y : H₀(Y) → R` are the augmentation maps
with `e.hom ≫ ε_Y = ε_X`, then `kernel ε_X ≅ kernel ε_Y`.
-/

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Limits.KernelIsoOfCompatibleIso

variable {C : Type*} [Category C] [Preadditive C] [HasKernels C]
variable {X Y Z : C} (e : X ≅ Y) (f : X ⟶ Z) (g : Y ⟶ Z) (h : e.hom ≫ g = f)

/-- If `e : X ≅ Y` is an isomorphism and `e.hom ≫ g = f`,
    then `kernel f ≅ kernel g`. -/
noncomputable def kernelIsoOfCompatibleIso : kernel f ≅ kernel g := by
  have h1 : kernel f ≅ kernel (e.hom ≫ g) := kernelIsoOfEq h.symm
  have h2 : kernel (e.hom ≫ g) ≅ kernel g := by
    let k_ef : kernel (e.hom ≫ g) ⟶ X := kernel.ι (e.hom ≫ g)
    let k_g : kernel g ⟶ Y := kernel.ι g
    have h_eq1 : k_ef ≫ e.hom ≫ g = 0 := kernel.condition (e.hom ≫ g)
    have h_eq2 : (k_ef ≫ e.hom) ≫ g = 0 := by
      have h : k_ef ≫ e.hom ≫ g = (k_ef ≫ e.hom) ≫ g := by rw [Category.assoc]
      rw [h] at h_eq1
      exact h_eq1
    let l : kernel (e.hom ≫ g) ⟶ kernel g := kernel.lift g (k_ef ≫ e.hom) h_eq2
    have h_eq3 : (k_g ≫ e.inv) ≫ (e.hom ≫ g) = 0 := by
      calc
        (k_g ≫ e.inv) ≫ (e.hom ≫ g)
          = k_g ≫ (e.inv ≫ e.hom) ≫ g := by rw [Category.assoc, Category.assoc]
        _ = k_g ≫ (𝟙 Y) ≫ g := by rw [e.inv_hom_id]
        _ = k_g ≫ g := by rw [Category.id_comp]
        _ = 0 := kernel.condition g
    let l' : kernel g ⟶ kernel (e.hom ≫ g) := kernel.lift (e.hom ≫ g) (k_g ≫ e.inv) h_eq3
    have h4 : l ≫ l' = 𝟙 (kernel (e.hom ≫ g)) := by
      have h_eq4 : l' ≫ k_ef = k_g ≫ e.inv := kernel.lift_ι (e.hom ≫ g) (k_g ≫ e.inv) h_eq3
      have h_eq5 : l ≫ k_g = k_ef ≫ e.hom := kernel.lift_ι g (k_ef ≫ e.hom) h_eq2
      have h_eq6 : (l ≫ l') ≫ k_ef = k_ef := by
        calc
          (l ≫ l') ≫ k_ef
            = l ≫ (l' ≫ k_ef) := by rw [Category.assoc]
          _ = l ≫ (k_g ≫ e.inv) := by rw [h_eq4]
          _ = (l ≫ k_g) ≫ e.inv := by rw [Category.assoc]
          _ = (k_ef ≫ e.hom) ≫ e.inv := by rw [h_eq5]
          _ = k_ef ≫ (e.hom ≫ e.inv) := by rw [Category.assoc]
          _ = k_ef ≫ (𝟙 X) := by rw [e.hom_inv_id]
          _ = k_ef := by simp
      have h_eq7 : (l ≫ l') ≫ k_ef = (𝟙 (kernel (e.hom ≫ g))) ≫ k_ef := by
        rw [h_eq6, Category.id_comp]
      exact (cancel_mono k_ef).mp h_eq7
    have h5 : l' ≫ l = 𝟙 (kernel g) := by
      have h_eq4 : l ≫ k_g = k_ef ≫ e.hom := kernel.lift_ι g (k_ef ≫ e.hom) h_eq2
      have h_eq5 : l' ≫ k_ef = k_g ≫ e.inv := kernel.lift_ι (e.hom ≫ g) (k_g ≫ e.inv) h_eq3
      have h_eq6 : (l' ≫ l) ≫ k_g = k_g := by
        calc
          (l' ≫ l) ≫ k_g
            = l' ≫ (l ≫ k_g) := by rw [Category.assoc]
          _ = l' ≫ (k_ef ≫ e.hom) := by rw [h_eq4]
          _ = (l' ≫ k_ef) ≫ e.hom := by rw [Category.assoc]
          _ = (k_g ≫ e.inv) ≫ e.hom := by rw [h_eq5]
          _ = k_g ≫ (e.inv ≫ e.hom) := by rw [Category.assoc]
          _ = k_g ≫ (𝟙 Y) := by rw [e.inv_hom_id]
          _ = k_g := by simp
      have h_eq7 : (l' ≫ l) ≫ k_g = (𝟙 (kernel g)) ≫ k_g := by
        rw [h_eq6, Category.id_comp]
      exact (cancel_mono k_g).mp h_eq7
    exact ⟨l, l', h4, h5⟩
  exact h1 ≪≫ h2

end CategoryTheory.Limits.KernelIsoOfCompatibleIso

end

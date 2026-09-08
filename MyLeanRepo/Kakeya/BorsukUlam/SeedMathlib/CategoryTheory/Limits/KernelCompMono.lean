/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace SeedMathlib.CategoryTheory.Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasKernels C]

/-- If `g : Y ⟶ Z` is mono, then `kernel (f ≫ g) ≅ kernel f`. -/
noncomputable def kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    kernel (f ≫ g) ≅ kernel f := by
  let kf : kernel f ⟶ X := kernel.ι f
  let kfg : kernel (f ≫ g) ⟶ X := kernel.ι (f ≫ g)
  have h1 : kf ≫ f ≫ g = 0 := by
    have hkf : kf ≫ f = 0 := kernel.condition f
    calc
      kf ≫ f ≫ g = (kf ≫ f) ≫ g := by rw [Category.assoc]
      _ = 0 ≫ g := by rw [hkf]
      _ = 0 := by simp
  let l : kernel f ⟶ kernel (f ≫ g) := kernel.lift (f ≫ g) kf h1
  have hlι : l ≫ kfg = kf := kernel.lift_ι (f ≫ g) kf h1
  have h2 : kfg ≫ f ≫ g = 0 := kernel.condition (f ≫ g)
  have h3 : (kfg ≫ f) ≫ g = 0 ≫ g := by
    rw [Category.assoc, h2]
    simp
  have h4 : kfg ≫ f = 0 := (cancel_mono g).mp h3
  let l' : kernel (f ≫ g) ⟶ kernel f := kernel.lift f kfg h4
  have hl'ι : l' ≫ kf = kfg := kernel.lift_ι f kfg h4
  have h5 : l ≫ l' = 𝟙 (kernel f) := by
    have h_eq : (l ≫ l') ≫ kf = kf := by
      calc
        (l ≫ l') ≫ kf = l ≫ (l' ≫ kf) := by rw [Category.assoc]
        _ = l ≫ kfg := by rw [hl'ι]
        _ = kf := hlι
    have h_eq2 : (l ≫ l') ≫ kf = (𝟙 (kernel f)) ≫ kf := by
      rw [h_eq, Category.id_comp]
    exact (cancel_mono kf).mp h_eq2
  have h6 : l' ≫ l = 𝟙 (kernel (f ≫ g)) := by
    have h_eq : (l' ≫ l) ≫ kfg = kfg := by
      calc
        (l' ≫ l) ≫ kfg = l' ≫ (l ≫ kfg) := by rw [Category.assoc]
        _ = l' ≫ kf := by rw [hlι]
        _ = kfg := hl'ι
    have h_eq2 : (l' ≫ l) ≫ kfg = (𝟙 (kernel (f ≫ g))) ≫ kfg := by
      rw [h_eq, Category.id_comp]
    exact (cancel_mono kfg).mp h_eq2
  exact ⟨l', l, h6, h5⟩

end SeedMathlib.CategoryTheory.Limits

end

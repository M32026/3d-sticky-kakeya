/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace SeedMathlib.CategoryTheory.Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    [HasCoproductsOfShape Bool C]

/-- The coproduct over `Bool` of two copies of `R` is isomorphic to the binary biproduct `R ⊞ R`. -/
noncomputable def sigmaBoolIsoBiprod (R : C) :
    (∐ (fun (_ : Bool) => R)) ≅ R ⊞ R := by
  let F : Bool → C := fun _ => R
  let f : (∐ F) ⟶ R ⊞ R :=
    Sigma.desc (fun b : Bool => if b then (biprod.inl : R ⟶ R ⊞ R) else biprod.inr)
  let g : R ⊞ R ⟶ (∐ F) :=
    biprod.desc (Sigma.ι F true) (Sigma.ι F false)
  refine
    { hom := f
      inv := g
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro b
    cases b
    · calc
        Sigma.ι F false ≫ f ≫ g = (Sigma.ι F false ≫ f) ≫ g := by
          rw [Category.assoc]
        _ = biprod.inr ≫ g := by
          have h : Sigma.ι F false ≫ f = (biprod.inr : R ⟶ R ⊞ R) := by
            simpa [f] using
              (Sigma.ι_desc
                (fun b : Bool => if b then (biprod.inl : R ⟶ R ⊞ R) else biprod.inr)
                false)
          rw [h]
        _ = Sigma.ι F false := biprod.inr_desc _ _
        _ = Sigma.ι F false ≫ 𝟙 (∐ F) := by simp
    · calc
        Sigma.ι F true ≫ f ≫ g = (Sigma.ι F true ≫ f) ≫ g := by
          rw [Category.assoc]
        _ = biprod.inl ≫ g := by
          have h : Sigma.ι F true ≫ f = (biprod.inl : R ⟶ R ⊞ R) := by
            simpa [f] using
              (Sigma.ι_desc
                (fun b : Bool => if b then (biprod.inl : R ⟶ R ⊞ R) else biprod.inr)
                true)
          rw [h]
        _ = Sigma.ι F true := biprod.inl_desc _ _
        _ = Sigma.ι F true ≫ 𝟙 (∐ F) := by simp
  · apply biprod.hom_ext'
    · calc
        biprod.inl ≫ (g ≫ f) = (biprod.inl ≫ g) ≫ f := by
          rw [Category.assoc]
        _ = Sigma.ι F true ≫ f := by
          rw [biprod.inl_desc]
        _ = biprod.inl := by
          simpa [f] using
            (Sigma.ι_desc
              (fun b : Bool => if b then (biprod.inl : R ⟶ R ⊞ R) else biprod.inr)
              true)
        _ = biprod.inl ≫ 𝟙 (R ⊞ R) := (Category.comp_id _).symm
    · calc
        biprod.inr ≫ (g ≫ f) = (biprod.inr ≫ g) ≫ f := by
          rw [Category.assoc]
        _ = Sigma.ι F false ≫ f := by
          rw [biprod.inr_desc]
        _ = biprod.inr := by
          simpa [f] using
            (Sigma.ι_desc
              (fun b : Bool => if b then (biprod.inl : R ⟶ R ⊞ R) else biprod.inr)
              false)
        _ = biprod.inr ≫ 𝟙 (R ⊞ R) := (Category.comp_id _).symm

@[simp]
lemma sigmaBoolIsoBiprod_ι_true (R : C) :
    Sigma.ι (fun (_ : Bool) => R) true ≫ (sigmaBoolIsoBiprod R).hom =
      (biprod.inl : R ⟶ R ⊞ R) := by
  dsimp only [sigmaBoolIsoBiprod]
  simpa using
    (Sigma.ι_desc
      (fun b : Bool => if b then (biprod.inl : R ⟶ R ⊞ R) else biprod.inr)
      true)

@[simp]
lemma sigmaBoolIsoBiprod_ι_false (R : C) :
    Sigma.ι (fun (_ : Bool) => R) false ≫ (sigmaBoolIsoBiprod R).hom =
      (biprod.inr : R ⟶ R ⊞ R) := by
  dsimp only [sigmaBoolIsoBiprod]
  simpa using
    (Sigma.ι_desc
      (fun b : Bool => if b then (biprod.inl : R ⟶ R ⊞ R) else biprod.inr)
      false)

end SeedMathlib.CategoryTheory.Limits

end

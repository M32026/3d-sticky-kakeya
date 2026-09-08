/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.LocallyConstant.Basic
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.PiZeroPathComponents
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.ReducedHomology

@[expose] public section

namespace AlgebraicTopology

noncomputable section

open CategoryTheory Limits TopCat Simplicial SSet Opposite
open HomologicalComplex

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable (R : C) [CategoryWithHomology C]

variable (X : TopCat.{w})

/-- Singular H₀(X) is isomorphic to the coproduct of copies of R
    indexed by π₀ of the singular simplicial set. -/
noncomputable def singularHomologyZeroIsoPiZero :
    ((singularHomologyFunctor C 0).obj R).obj X ≅
    ∐ (fun (_ : SSet.π₀ (TopCat.toSSet.obj X)) ↦ R) :=
  SSet.homology₀Iso (TopCat.toSSet.obj X) R

/-- Singular H₀(X) is isomorphic to the coproduct of copies of R
    indexed by the path components of X. -/
noncomputable def singularHomologyZeroIsoZerothHomotopy :
    ((singularHomologyFunctor C 0).obj R).obj X ≅
    ∐ (fun (_ : ZerothHomotopy X) ↦ R) :=
  (singularHomologyZeroIsoPiZero R X) ≪≫
    Sigma.reindex (singularPiZeroEquivZerothHomotopy X) (fun (_ : ZerothHomotopy X) => R)

/-- For locally path-connected spaces, singular H₀(X) is isomorphic to the
    coproduct of copies of R indexed by the connected components of X. -/
noncomputable def singularHomologyZeroIsoConnectedComponents
    [LocPathConnectedSpace X] :
    ((singularHomologyFunctor C 0).obj R).obj X ≅
    ∐ (fun (_ : ConnectedComponents X) ↦ R) :=
  (singularHomologyZeroIsoZerothHomotopy R X) ≪≫
    Sigma.reindex connectedComponentsEquivZerothHomotopy.symm
      (fun (_ : ConnectedComponents X) => R)

/-- If two types have the same cardinality, then the coproducts of copies of R
    indexed by those types are isomorphic. -/
noncomputable def coproductEquivOfEquiv {α β : Type w} (e : α ≃ β) :
    ∐ (fun (_ : α) ↦ R) ≅ ∐ (fun (_ : β) ↦ R) :=
  Sigma.reindex e (fun (_ : β) => R)

section TwoComponents

variable [HasBinaryBiproducts C]

/-- The map `biprod.inl - biprod.inr : R → R ⊞ R` is the kernel of
    `biprod.desc (𝟙 R) (𝟙 R) : R ⊞ R → R`. -/
noncomputable def isLimit_kernelFold_desc_id_id :
    IsLimit (KernelFork.ofι (biprod.inl - biprod.inr : R ⟶ R ⊞ R)
      (show (biprod.inl - biprod.inr : R ⟶ R ⊞ R) ≫ biprod.desc (𝟙 R) (𝟙 R) = 0 by
        simp [biprod.inl_desc, biprod.inr_desc] )) := by
  let f : R ⊞ R ⟶ R := biprod.desc (𝟙 R) (𝟙 R)
  let i : R ⟶ R ⊞ R := biprod.inl - biprod.inr
  have hi : i ≫ f = 0 := by
    simp [f, i, biprod.inl_desc, biprod.inr_desc]
  refine' KernelFork.IsLimit.ofι i hi (fun {W'} g' _ => g' ≫ biprod.fst) _ _
  · -- fac: lift g' hg' ≫ i = g'
    intro W' g' hg'
    let g₁ : W' ⟶ R := g' ≫ biprod.fst
    let g₂ : W' ⟶ R := g' ≫ biprod.snd
    have h_sum : g₁ + g₂ = 0 := by
      have h : g' ≫ f = 0 := hg'
      simpa [f, g₁, g₂, biprod.desc_eq] using h
    have h_g2 : g₂ = -g₁ := by
      have h : g₁ + g₂ = 0 := h_sum
      exact Eq.symm (neg_eq_of_add_eq_zero_right h_sum)
    have h_total : g₁ ≫ biprod.inl + g₂ ≫ biprod.inr = g' := by
      have h : (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : R ⊞ R ⟶ R ⊞ R) = 𝟙 (R ⊞ R) := by
        exact biprod.total
      have h2 : g' ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) = g' := by
        rw [h] ; simp
      have h3 : g' ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) =
          g' ≫ (biprod.fst ≫ biprod.inl) + g' ≫ (biprod.snd ≫ biprod.inr) := by
        exact Preadditive.comp_add W' (R ⊞ R) (R ⊞ R) g' (biprod.fst ≫ biprod.inl) (biprod.snd ≫ biprod.inr)
      have h4 : g' ≫ (biprod.fst ≫ biprod.inl) + g' ≫ (biprod.snd ≫ biprod.inr) =
          (g' ≫ biprod.fst) ≫ biprod.inl + (g' ≫ biprod.snd) ≫ biprod.inr := by
        rw [Category.assoc, Category.assoc]
      have h5 : (g' ≫ biprod.fst) ≫ biprod.inl + (g' ≫ biprod.snd) ≫ biprod.inr = g' := by
        rw [←h4, ←h3, h2]
      exact h5
    have h_main : g₁ ≫ i = g' := by
      have h21 : g₁ ≫ (biprod.inl - biprod.inr) = g₁ ≫ biprod.inl - g₁ ≫ biprod.inr := by exact Preadditive.comp_sub g₁ biprod.inl biprod.inr
      have h_eq : g₁ ≫ biprod.inl - g₁ ≫ biprod.inr = g₁ ≫ biprod.inl + g₂ ≫ biprod.inr := by
        have h : g₂ = -g₁ := h_g2
        rw [h]
        ; simp [sub_eq_add_neg]

      have h1 : g₁ ≫ i = g₁ ≫ (biprod.inl - biprod.inr) := by rfl
      rw [h1, h21, h_eq]
      exact h_total
    exact h_main
  · -- uniq: uniqueness
    intro W' g' _ m hm
    have h : m ≫ i = g' := hm
    have h4 : (m ≫ i) ≫ biprod.fst = g' ≫ biprod.fst := by rw [h]
    have h5 : m ≫ (i ≫ biprod.fst) = g' ≫ biprod.fst := by
      rwa [Category.assoc] at h4
    have h6 : i ≫ biprod.fst = 𝟙 R := by
      simp [i]
    rw [h6] at h5
    simpa using h5

end TwoComponents

section KernelBiprodDesc

variable [HasBinaryBiproducts C] {A : C} (g : A ⟶ R)

/-- The kernel of `biprod.desc (𝟙 R) g : R ⊞ A → R` is isomorphic to `A`.

    The kernel inclusion is `(-g) ≫ biprod.inl + biprod.inr : A → R ⊞ A`. -/
noncomputable def isLimit_kernelBiprodDescId :
    IsLimit (KernelFork.ofι (f := biprod.desc (𝟙 R) g)
      ((-g) ≫ (biprod.inl : R ⟶ R ⊞ A) + (biprod.inr : A ⟶ R ⊞ A))
      (by
        let f : R ⊞ A ⟶ R := biprod.desc (𝟙 R) g
        let i : A ⟶ R ⊞ A := (-g) ≫ (biprod.inl : R ⟶ R ⊞ A) + (biprod.inr : A ⟶ R ⊞ A)
        have h1 : (biprod.inl : R ⟶ R ⊞ A) ≫ f = 𝟙 R := biprod.inl_desc _ _
        have h2 : (biprod.inr : A ⟶ R ⊞ A) ≫ f = g := biprod.inr_desc _ _
        have h_comp : i ≫ f = ((-g) ≫ (biprod.inl : R ⟶ R ⊞ A)) ≫ f + (biprod.inr : A ⟶ R ⊞ A) ≫ f := by
          simp only [i, Preadditive.add_comp]
        have h_goal : i ≫ f = 0 := by
          calc
            i ≫ f
              = ((-g) ≫ (biprod.inl : R ⟶ R ⊞ A)) ≫ f + (biprod.inr : A ⟶ R ⊞ A) ≫ f := h_comp
            _ = (-g) ≫ ((biprod.inl : R ⟶ R ⊞ A) ≫ f) + (biprod.inr : A ⟶ R ⊞ A) ≫ f := by
              rw [←Category.assoc]
            _ = (-g) ≫ 𝟙 R + g := by rw [h1, h2]
            _ = -g + g := by rw [Category.comp_id]
            _ = 0 := by abel
        exact h_goal)) := by
  let f : R ⊞ A ⟶ R := biprod.desc (𝟙 R) g
  let i : A ⟶ R ⊞ A := (-g) ≫ (biprod.inl : R ⟶ R ⊞ A) + (biprod.inr : A ⟶ R ⊞ A)
  have hi : i ≫ f = 0 := by
    have h1 : (biprod.inl : R ⟶ R ⊞ A) ≫ f = 𝟙 R := biprod.inl_desc _ _
    have h2 : (biprod.inr : A ⟶ R ⊞ A) ≫ f = g := biprod.inr_desc _ _
    have h_comp : i ≫ f = ((-g) ≫ (biprod.inl : R ⟶ R ⊞ A)) ≫ f + (biprod.inr : A ⟶ R ⊞ A) ≫ f := by
      exact Preadditive.add_comp A (R ⊞ A) R ((-g) ≫ biprod.inl) biprod.inr f
    calc
      i ≫ f
        = ((-g) ≫ (biprod.inl : R ⟶ R ⊞ A)) ≫ f + (biprod.inr : A ⟶ R ⊞ A) ≫ f := h_comp
      _ = (-g) ≫ ((biprod.inl : R ⟶ R ⊞ A) ≫ f) + (biprod.inr : A ⟶ R ⊞ A) ≫ f := by
        rw [←Category.assoc]
      _ = (-g) ≫ 𝟙 R + g := by rw [h1, h2]
      _ = -g + g := by rw [Category.comp_id]
      _ = 0 := by abel
  let kf : KernelFork f := KernelFork.ofι i hi
  refine' KernelFork.IsLimit.ofι i hi (fun {K} k hk => k ≫ biprod.snd) _ _
  · -- fac
    intro K k hk
    let k₁ : K ⟶ R := k ≫ biprod.fst
    let k₂ : K ⟶ A := k ≫ biprod.snd
    have h_decomp : k = k₁ ≫ (biprod.inl : R ⟶ R ⊞ A) + k₂ ≫ (biprod.inr : A ⟶ R ⊞ A) := by
      ext <;> simp [k₁, k₂]
    have h_sum : k₁ + k₂ ≫ g = 0 := by
      have h : k ≫ f = 0 := hk
      have h_comp : (k₁ ≫ (biprod.inl : R ⟶ R ⊞ A) + k₂ ≫ (biprod.inr : A ⟶ R ⊞ A)) ≫ f =
          (k₁ ≫ (biprod.inl : R ⟶ R ⊞ A)) ≫ f + (k₂ ≫ (biprod.inr : A ⟶ R ⊞ A)) ≫ f := by
        exact Preadditive.add_comp K (R ⊞ A) R (k₁ ≫ biprod.inl) (k₂ ≫ biprod.inr) f
      have h2 : k ≫ f = k₁ + k₂ ≫ g := by
        calc
          k ≫ f
            = (k₁ ≫ (biprod.inl : R ⟶ R ⊞ A) + k₂ ≫ (biprod.inr : A ⟶ R ⊞ A)) ≫ f := by rw [h_decomp]
            _ = (k₁ ≫ (biprod.inl : R ⟶ R ⊞ A)) ≫ f + (k₂ ≫ (biprod.inr : A ⟶ R ⊞ A)) ≫ f := h_comp
            _ = k₁ ≫ ((biprod.inl : R ⟶ R ⊞ A) ≫ f) + (k₂ ≫ (biprod.inr : A ⟶ R ⊞ A)) ≫ f := by
              rw [←Category.assoc]
            _ = k₁ ≫ 𝟙 R + k₂ ≫ g := by
              have h51 : k₁ ≫ ((biprod.inl : R ⟶ R ⊞ A) ≫ f) = k₁ ≫ 𝟙 R := by
                rw [biprod.inl_desc _ _]
              have h52 : (k₂ ≫ (biprod.inr : A ⟶ R ⊞ A)) ≫ f = k₂ ≫ g := by
                have h521 : (k₂ ≫ (biprod.inr : A ⟶ R ⊞ A)) ≫ f = k₂ ≫ ((biprod.inr : A ⟶ R ⊞ A) ≫ f) := by
                  exact Category.assoc _ _ _
                rw [h521, biprod.inr_desc _ _]
              rw [h51, h52]
            _ = k₁ + k₂ ≫ g := by
              have h4 : k₁ ≫ 𝟙 R = k₁ := by rw [Category.comp_id]
              rw [h4]
      rw [h2] at h
      exact h
    have h_k1 : k₁ = -(k₂ ≫ g) := by
      have h : k₁ + k₂ ≫ g = 0 := h_sum
      simpa [add_eq_zero_iff_eq_neg] using h
    have h_main : (k ≫ biprod.snd) ≫ i = k := by
      ext
      · -- fst component
        simp [i, k₁, k₂, Category.assoc, h_k1]
      · -- snd component
        simp [i, Category.assoc]
    exact h_main
  · -- uniq
    intro K k _ m hm
    have h : m ≫ i = k := hm
    have h4 : (m ≫ i) ≫ biprod.snd = k ≫ biprod.snd := by rw [h]
    have h5 : m ≫ (i ≫ biprod.snd) = k ≫ biprod.snd := by
      rwa [Category.assoc] at h4
    have h6 : i ≫ biprod.snd = 𝟙 A := by
      simp [i]
    rw [h6] at h5
    simpa using h5

end KernelBiprodDesc

section ReducedHomologyTwoComponents

variable [HasBinaryBiproducts C] [LocPathConnectedSpace X] [Nonempty X]

/-- For a nonempty locally path-connected space `X` with exactly two connected components,
    reduced singular homology in degree 0 is isomorphic to `R`. -/
noncomputable def reducedSingularHomologyZero_iso_of_card_components_eq_two
    (h_card : Nat.card (ConnectedComponents X) = 2) :
    reducedSingularHomology C 0 R X ≅ R := by
  let X' : SSet := TopCat.toSSet.obj X
  have h_nonempty_X' : X'.Nonempty := by
    have hne_cc : Nonempty (ConnectedComponents X) := by
      have hne : Nonempty X := inferInstance
      exact Nonempty.map ConnectedComponents.mk hne
    let e : SSet.π₀ X' ≃ ConnectedComponents X :=
      (singularPiZeroEquivZerothHomotopy X).trans connectedComponentsEquivZerothHomotopy.symm
    have hpi : Nonempty (SSet.π₀ X') := Nonempty.map e.symm hne_cc
    exact (SSet.π₀.nonempty_iff (X := X')).mp hpi
  have h_card_pi0 : Nat.card (SSet.π₀ X') = 2 := by
    have e1 : SSet.π₀ X' ≃ ZerothHomotopy X := singularPiZeroEquivZerothHomotopy X
    have e2 : ZerothHomotopy X ≃ ConnectedComponents X :=
      connectedComponentsEquivZerothHomotopy.symm
    have e : SSet.π₀ X' ≃ ConnectedComponents X := e1.trans e2
    rw [Nat.card_congr e]
    exact h_card
  let S := (X'.augmentedChainComplex R).sc' 2 1 0
  let h : S.RightHomologyData := S.rightHomologyData
  let Q' := ∐ (fun (_ : SSet.π₀ X') ↦ R)
  let p' : S.X₂ ⟶ Q' := SSet.π₀.fromChainComplexXZero X' R
  have hwp' : S.f ≫ p' = 0 := by
    have h_f : S.f = (X'.chainComplex R).d 1 0 := by
      simp [S, SSet.augmentedChainComplex, ChainComplex.augment]
    rw [h_f]
    exact SSet.π₀.d_fromChainComplexXZero X' R 1
  let hp' : IsColimit (CokernelCofork.ofπ p' hwp') :=
    SSet.isColimitCokernelCoforkChainComplexDOneZero X' R
  let e_hom : h.Q ⟶ Q' := h.descQ p' hwp'
  let e_inv : Q' ⟶ h.Q := hp'.desc (CokernelCofork.ofπ h.p h.wp)
  have he1 : h.p ≫ e_hom = p' := h.p_descQ p' hwp'
  have he2 : p' ≫ e_inv = h.p := by
    exact hp'.fac (CokernelCofork.ofπ h.p h.wp) WalkingParallelPair.one
  have e_hom_inv : e_hom ≫ e_inv = 𝟙 h.Q := by
    apply Cofork.IsColimit.hom_ext h.hp
    have h_eq : h.p ≫ (e_hom ≫ e_inv) = h.p ≫ 𝟙 h.Q := by
      calc
        h.p ≫ (e_hom ≫ e_inv) = (h.p ≫ e_hom) ≫ e_inv := by rw [Category.assoc]
        _ = p' ≫ e_inv := by rw [he1]
        _ = h.p := by rw [he2]
        _ = h.p ≫ 𝟙 h.Q := by rw [Category.comp_id]
    exact h_eq
  have e_inv_hom : e_inv ≫ e_hom = 𝟙 Q' := by
    apply Cofork.IsColimit.hom_ext hp'
    have h_eq : p' ≫ (e_inv ≫ e_hom) = p' ≫ 𝟙 Q' := by
      calc
        p' ≫ (e_inv ≫ e_hom) = (p' ≫ e_inv) ≫ e_hom := by rw [Category.assoc]
        _ = h.p ≫ e_hom := by rw [he2]
        _ = p' := by rw [he1]
        _ = p' ≫ 𝟙 Q' := by rw [Category.comp_id]
    exact h_eq
  let e : h.Q ≅ Q' :=
    { hom := e_hom, inv := e_inv, hom_inv_id := e_hom_inv, inv_hom_id := e_inv_hom }
  let g' : Q' ⟶ R := Sigma.desc (fun (_ : SSet.π₀ X') ↦ 𝟙 R)
  have hε : S.g = p' ≫ g' := by
    have h_g : S.g = X'.augmentationMap R := by
      simp [S, SSet.augmentedChainComplex, ChainComplex.augment]
    rw [h_g, SSet.augmentationMap] ; rfl
  let g : h.Q ⟶ R := h.descQ S.g S.zero
  have h_induced : g = e.hom ≫ g' := by
    apply Cofork.IsColimit.hom_ext h.hp
    have h_left : h.p ≫ g = S.g := h.p_descQ S.g S.zero
    have h_right : h.p ≫ (e.hom ≫ g') = S.g := by
      calc
        h.p ≫ (e.hom ≫ g') = (h.p ≫ e_hom) ≫ g' := by rw [Category.assoc]
        _ = p' ≫ g' := by rw [he1]
        _ = S.g := by rw [hε]
    have h_goal : (CokernelCofork.ofπ h.p h.wp).π ≫ g =
        (CokernelCofork.ofπ h.p h.wp).π ≫ (e.hom ≫ g') := by
      have h_pi : (CokernelCofork.ofπ h.p h.wp).π = h.p := by
        simp [CokernelCofork.ofπ]
      rw [h_pi]
      exact h_left.trans h_right.symm
    exact h_goal
  have h1 : (h.ι ≫ e.hom) ≫ g' = 0 := by
    calc
      (h.ι ≫ e.hom) ≫ g' = h.ι ≫ (e.hom ≫ g') := by rw [Category.assoc]
      _ = h.ι ≫ g := by rw [←h_induced]
      _ = 0 := h.wι
  let kf' : KernelFork g' := KernelFork.ofι (h.ι ≫ e.hom) h1
  have h_kf' : IsLimit kf' := by
    refine' KernelFork.IsLimit.ofι (h.ι ≫ e.hom) h1
      (fun {K} k hk =>
        have h_kx_comp : (k ≫ e.inv) ≫ g = 0 := by
          calc
            (k ≫ e.inv) ≫ g = k ≫ (e.inv ≫ g) := by rw [Category.assoc]
            _ = k ≫ (e.inv ≫ (e.hom ≫ g')) := by rw [h_induced]
            _ = k ≫ ((e.inv ≫ e.hom) ≫ g') := by rw [Category.assoc]
            _ = k ≫ (𝟙 Q' ≫ g') := by rw [e.inv_hom_id]
            _ = k ≫ g' := by rw [Category.id_comp]
            _ = 0 := hk
        (KernelFork.IsLimit.lift' h.hι (k ≫ e.inv) h_kx_comp).val) _ _
    · -- fac
      intro K k hk
      have h_kx_comp : (k ≫ e.inv) ≫ g = 0 := by
        calc
          (k ≫ e.inv) ≫ g = k ≫ (e.inv ≫ g) := by rw [Category.assoc]
          _ = k ≫ (e.inv ≫ (e.hom ≫ g')) := by rw [h_induced]
          _ = k ≫ ((e.inv ≫ e.hom) ≫ g') := by rw [Category.assoc]
          _ = k ≫ (𝟙 Q' ≫ g') := by rw [e.inv_hom_id]
          _ = k ≫ g' := by rw [Category.id_comp]
          _ = 0 := hk
      let l : K ⟶ h.H := (KernelFork.IsLimit.lift' h.hι (k ≫ e.inv) h_kx_comp).val
      have hl : l ≫ h.ι = k ≫ e.inv := (KernelFork.IsLimit.lift' h.hι (k ≫ e.inv) h_kx_comp).property
      calc
        l ≫ (h.ι ≫ e.hom) = (l ≫ h.ι) ≫ e.hom := by rw [Category.assoc]
        _ = (k ≫ e.inv) ≫ e.hom := by rw [hl]
        _ = k ≫ (e.inv ≫ e.hom) := by rw [Category.assoc]
        _ = k ≫ 𝟙 Q' := by rw [e.inv_hom_id]
        _ = k := by simp
    · -- uniq
      intro K k hk m hm
      have h_kx_comp : (k ≫ e.inv) ≫ g = 0 := by
        calc
          (k ≫ e.inv) ≫ g = k ≫ (e.inv ≫ g) := by rw [Category.assoc]
          _ = k ≫ (e.inv ≫ (e.hom ≫ g')) := by rw [h_induced]
          _ = k ≫ ((e.inv ≫ e.hom) ≫ g') := by rw [Category.assoc]
          _ = k ≫ (𝟙 Q' ≫ g') := by rw [e.inv_hom_id]
          _ = k ≫ g' := by rw [Category.id_comp]
          _ = 0 := hk
      let l : K ⟶ h.H := (KernelFork.IsLimit.lift' h.hι (k ≫ e.inv) h_kx_comp).val
      have hl : l ≫ h.ι = k ≫ e.inv := (KernelFork.IsLimit.lift' h.hι (k ≫ e.inv) h_kx_comp).property
      have h_eq : m ≫ (h.ι ≫ e.hom) = k := hm
      have h2 : (m ≫ h.ι) ≫ e.hom = k := by simpa [Category.assoc] using h_eq
      have h3 : m ≫ h.ι = k ≫ e.inv := by
        have h4 : m ≫ h.ι = (m ≫ h.ι) ≫ 𝟙 h.Q := by rw [Category.comp_id]
        rw [h4]
        have h5 : (m ≫ h.ι) ≫ 𝟙 h.Q = (m ≫ h.ι) ≫ (e.hom ≫ e.inv) := by
          rw [←e.hom_inv_id]
        rw [h5]
        have h6 : (m ≫ h.ι) ≫ (e.hom ≫ e.inv) = ((m ≫ h.ι) ≫ e.hom) ≫ e.inv := by
          simp [Category.assoc]
        rw [h6, h2]
      have h7 : m ≫ h.ι = l ≫ h.ι := by rw [h3, hl]
      have h_mono : Mono h.ι := Fork.IsLimit.mono h.hι
      exact (cancel_mono h.ι).mp h7
  have h2 : ∃ (a₁ a₂ : SSet.π₀ X'), a₁ ≠ a₂ ∧ ({a₁, a₂} : Set (SSet.π₀ X')) = Set.univ :=
    (Nat.card_eq_two_iff (α := SSet.π₀ X')).mp h_card_pi0
  let a₁ : SSet.π₀ X' := Classical.choose h2
  have h21 : ∃ (a₂ : SSet.π₀ X'), a₁ ≠ a₂ ∧ ({a₁, a₂} : Set (SSet.π₀ X')) = Set.univ :=
    Classical.choose_spec h2
  let a₂ : SSet.π₀ X' := Classical.choose h21
  have h_ne : a₁ ≠ a₂ := (Classical.choose_spec h21).1
  have h_univ : ({a₁, a₂} : Set (SSet.π₀ X')) = Set.univ := (Classical.choose_spec h21).2
  classical
  let fwd : Q' ⟶ R ⊞ R :=
    Sigma.desc (fun i : SSet.π₀ X' => if i = a₁ then biprod.inl else biprod.inr)
  let bwd : R ⊞ R ⟶ Q' :=
    biprod.desc (Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁) (Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂)
  have h_fwd_bwd : fwd ≫ bwd = 𝟙 Q' := by
    apply Sigma.hom_ext
    intro i
    have h_cases : i = a₁ ∨ i = a₂ := by
      have h_i_in_univ : i ∈ (Set.univ : Set (SSet.π₀ X')) := trivial
      rw [←h_univ] at h_i_in_univ
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h_i_in_univ
    rcases h_cases with (rfl | rfl)
    · -- i = a₁
      have h1 : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ fwd = biprod.inl := by
        rw [Sigma.ι_desc] ; rw [if_pos rfl]
      calc
        Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ (fwd ≫ bwd)
          = (Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ fwd) ≫ bwd := by rw [Category.assoc]
        _ = biprod.inl ≫ bwd := by rw [h1]
        _ = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ := by
          simp [bwd, biprod.inl_desc]
        _ = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ 𝟙 Q' := by rw [Category.comp_id]
    · -- i = a₂
      have h1 : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ fwd = biprod.inr := by
        rw [Sigma.ι_desc] ; rw [if_neg h_ne.symm]
      calc
        Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ (fwd ≫ bwd)
          = (Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ fwd) ≫ bwd := by rw [Category.assoc]
        _ = biprod.inr ≫ bwd := by rw [h1]
        _ = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ := by
          simp [bwd, biprod.inr_desc]
        _ = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ 𝟙 Q' := by rw [Category.comp_id]
  have h_bwd_fwd : bwd ≫ fwd = 𝟙 (R ⊞ R) := by
    have h_inl : biprod.inl ≫ bwd ≫ fwd = biprod.inl ≫ 𝟙 (R ⊞ R) := by
      have h1 : biprod.inl ≫ bwd = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ := by
        simp [bwd, biprod.inl_desc]
      have h2 : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ fwd = biprod.inl := by
        rw [Sigma.ι_desc] ; rw [if_pos rfl]
      calc
        biprod.inl ≫ bwd ≫ fwd
          = (biprod.inl ≫ bwd) ≫ fwd := by rw [Category.assoc]
        _ = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ fwd := by rw [h1]
        _ = biprod.inl := by rw [h2]
        _ = biprod.inl ≫ 𝟙 (R ⊞ R) := by rw [Category.comp_id]
    have h_inr : biprod.inr ≫ bwd ≫ fwd = biprod.inr ≫ 𝟙 (R ⊞ R) := by
      have h1 : biprod.inr ≫ bwd = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ := by
        simp [bwd, biprod.inr_desc]
      have h2 : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ fwd = biprod.inr := by
        rw [Sigma.ι_desc] ; rw [if_neg h_ne.symm]
      calc
        biprod.inr ≫ bwd ≫ fwd
          = (biprod.inr ≫ bwd) ≫ fwd := by rw [Category.assoc]
        _ = Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ fwd := by rw [h1]
        _ = biprod.inr := by rw [h2]
        _ = biprod.inr ≫ 𝟙 (R ⊞ R) := by rw [Category.comp_id]
    exact biprod.hom_ext' (bwd ≫ fwd) (𝟙 (R ⊞ R)) h_inl h_inr
  let e_biprod : Q' ≅ R ⊞ R :=
    { hom := fwd, inv := bwd, hom_inv_id := h_fwd_bwd, inv_hom_id := h_bwd_fwd }
  let g_fold : R ⊞ R ⟶ R := biprod.desc (𝟙 R) (𝟙 R)
  have h_g'_eq : g' = fwd ≫ g_fold := by
    apply Sigma.hom_ext
    intro i
    have h_cases : i = a₁ ∨ i = a₂ := by
      have h_i_in_univ : i ∈ (Set.univ : Set (SSet.π₀ X')) := trivial
      rw [←h_univ] at h_i_in_univ
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h_i_in_univ
    rcases h_cases with (rfl | rfl)
    · -- i = a₁
      have h1 : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ fwd = biprod.inl := by
        rw [Sigma.ι_desc] ; rw [if_pos rfl]
      have h_right : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ (fwd ≫ g_fold) = 𝟙 R := by
        rw [←Category.assoc, h1, biprod.inl_desc]
      have h_left : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₁ ≫ g' = 𝟙 R := by
        simp [g', Sigma.ι_desc]
      rw [h_left, h_right]
    · -- i = a₂
      have h1 : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ fwd = biprod.inr := by
        rw [Sigma.ι_desc] ; rw [if_neg h_ne.symm]
      have h_right : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ (fwd ≫ g_fold) = 𝟙 R := by
        rw [←Category.assoc, h1, biprod.inr_desc]
      have h_left : Sigma.ι (fun (_ : SSet.π₀ X') ↦ R) a₂ ≫ g' = 𝟙 R := by
        simp [g', Sigma.ι_desc]
      rw [h_left, h_right]
  let k_total : h.H ⟶ R ⊞ R := (h.ι ≫ e.hom) ≫ fwd
  have h_k_total_zero : k_total ≫ g_fold = 0 := by
    calc
      k_total ≫ g_fold
        = (h.ι ≫ e.hom) ≫ (fwd ≫ g_fold) := by rw [Category.assoc]
      _ = (h.ι ≫ e.hom) ≫ g' := by rw [←h_g'_eq]
      _ = 0 := h1
  let kf_total : KernelFork g_fold := KernelFork.ofι k_total h_k_total_zero
  have h_kf_total : IsLimit kf_total := by
    refine' KernelFork.IsLimit.ofι k_total h_k_total_zero
      (fun {K} k hk =>
        have h_kx_comp : (k ≫ bwd) ≫ g' = 0 := by
          calc
            (k ≫ bwd) ≫ g' = k ≫ (bwd ≫ g') := by rw [Category.assoc]
            _ = k ≫ (bwd ≫ (fwd ≫ g_fold)) := by rw [h_g'_eq]
            _ = k ≫ ((bwd ≫ fwd) ≫ g_fold) := by rw [Category.assoc]
            _ = k ≫ (𝟙 (R ⊞ R) ≫ g_fold) := by rw [h_bwd_fwd]
            _ = k ≫ g_fold := by rw [Category.id_comp]
            _ = 0 := hk
        (KernelFork.IsLimit.lift' h_kf' (k ≫ bwd) h_kx_comp).val) _ _
    · -- fac
      intro K k hk
      have h_kx_comp : (k ≫ bwd) ≫ g' = 0 := by
        calc
          (k ≫ bwd) ≫ g' = k ≫ (bwd ≫ g') := by rw [Category.assoc]
          _ = k ≫ (bwd ≫ (fwd ≫ g_fold)) := by rw [h_g'_eq]
          _ = k ≫ ((bwd ≫ fwd) ≫ g_fold) := by rw [Category.assoc]
          _ = k ≫ (𝟙 (R ⊞ R) ≫ g_fold) := by rw [h_bwd_fwd]
          _ = k ≫ g_fold := by rw [Category.id_comp]
          _ = 0 := hk
      let l : K ⟶ h.H := (KernelFork.IsLimit.lift' h_kf' (k ≫ bwd) h_kx_comp).val
      have hl : l ≫ (h.ι ≫ e.hom) = k ≫ bwd := (KernelFork.IsLimit.lift' h_kf' (k ≫ bwd) h_kx_comp).property
      have h_goal : l ≫ k_total = k := by
        calc
          l ≫ k_total = l ≫ ((h.ι ≫ e.hom) ≫ fwd) := by rfl
          _ = (l ≫ (h.ι ≫ e.hom)) ≫ fwd := by simp [Category.assoc]
          _ = (k ≫ bwd) ≫ fwd := by rw [hl]
          _ = k ≫ (bwd ≫ fwd) := by rw [Category.assoc]
          _ = k ≫ 𝟙 (R ⊞ R) := by rw [h_bwd_fwd]
          _ = k := by simp
      exact h_goal
    · -- uniq
      intro K k hk m hm
      have h_kx_comp : (k ≫ bwd) ≫ g' = 0 := by
        calc
          (k ≫ bwd) ≫ g' = k ≫ (bwd ≫ g') := by rw [Category.assoc]
          _ = k ≫ (bwd ≫ (fwd ≫ g_fold)) := by rw [h_g'_eq]
          _ = k ≫ ((bwd ≫ fwd) ≫ g_fold) := by rw [Category.assoc]
          _ = k ≫ (𝟙 (R ⊞ R) ≫ g_fold) := by rw [h_bwd_fwd]
          _ = k ≫ g_fold := by rw [Category.id_comp]
          _ = 0 := hk
      let l : K ⟶ h.H := (KernelFork.IsLimit.lift' h_kf' (k ≫ bwd) h_kx_comp).val
      have hl : l ≫ (h.ι ≫ e.hom) = k ≫ bwd := (KernelFork.IsLimit.lift' h_kf' (k ≫ bwd) h_kx_comp).property
      have h_eq : m ≫ k_total = k := hm
      have h2 : (m ≫ (h.ι ≫ e.hom)) ≫ fwd = k := by simpa [k_total, Category.assoc] using h_eq
      have h3 : m ≫ (h.ι ≫ e.hom) = k ≫ bwd := by
        have h4 : m ≫ (h.ι ≫ e.hom) = (m ≫ (h.ι ≫ e.hom)) ≫ 𝟙 Q' := by rw [Category.comp_id]
        rw [h4]
        have h5 : (m ≫ (h.ι ≫ e.hom)) ≫ 𝟙 Q' = (m ≫ (h.ι ≫ e.hom)) ≫ (fwd ≫ bwd) := by
          rw [←h_fwd_bwd]
        rw [h5]
        have h6 : (m ≫ (h.ι ≫ e.hom)) ≫ (fwd ≫ bwd) = ((m ≫ (h.ι ≫ e.hom)) ≫ fwd) ≫ bwd := by
          simp [Category.assoc]
        rw [h6, h2]
      have h7 : m ≫ (h.ι ≫ e.hom) = l ≫ (h.ι ≫ e.hom) := by rw [h3, hl]
      have h_mono : Mono (h.ι ≫ e.hom) := Fork.IsLimit.mono h_kf'
      exact (cancel_mono (h.ι ≫ e.hom)).mp h7
  have h_main_iso : h.H ≅ R := by
    let k_fold : R ⟶ R ⊞ R := biprod.inl - biprod.inr
    have h_k_fold_zero : k_fold ≫ g_fold = 0 := by
      simp [k_fold, g_fold, biprod.inl_desc, biprod.inr_desc]
    let kf_fold : KernelFork g_fold := KernelFork.ofι k_fold h_k_fold_zero
    have h_kf_fold : IsLimit kf_fold := isLimit_kernelFold_desc_id_id (C := C) (R := R)
    let l : h.H ⟶ R := (KernelFork.IsLimit.lift' h_kf_fold k_total h_k_total_zero).val
    have hl : l ≫ k_fold = k_total := (KernelFork.IsLimit.lift' h_kf_fold k_total h_k_total_zero).property
    let m : R ⟶ h.H := (KernelFork.IsLimit.lift' h_kf_total k_fold h_k_fold_zero).val
    have hm : m ≫ k_total = k_fold := (KernelFork.IsLimit.lift' h_kf_total k_fold h_k_fold_zero).property
    have h_mono_total : Mono k_total := Fork.IsLimit.mono h_kf_total
    have h_mono_fold : Mono k_fold := Fork.IsLimit.mono h_kf_fold
    have h1 : l ≫ m = 𝟙 h.H := by
      apply (cancel_mono k_total).mp
      calc
        (l ≫ m) ≫ k_total = l ≫ (m ≫ k_total) := by rw [Category.assoc]
        _ = l ≫ k_fold := by rw [hm]
        _ = k_total := by rw [hl]
        _ = (𝟙 h.H) ≫ k_total := by rw [Category.id_comp]
    have h2 : m ≫ l = 𝟙 R := by
      apply (cancel_mono k_fold).mp
      calc
        (m ≫ l) ≫ k_fold = m ≫ (l ≫ k_fold) := by rw [Category.assoc]
        _ = m ≫ k_total := by rw [hl]
        _ = k_fold := by rw [hm]
        _ = (𝟙 R) ≫ k_fold := by rw [Category.id_comp]
    exact { hom := l, inv := m, hom_inv_id := h1, inv_hom_id := h2 }
  have h_iso_Htilde_hH : X'.reducedHomology R 0 ≅ h.H := by
    let h1 : (X'.augmentedChainComplex R).homology 1 ≅ S.homology :=
      (X'.augmentedChainComplex R).homologyIsoSc' 2 1 0 (by simp) (by simp)
    let h2 : S.homology ≅ S.rightHomology := S.rightHomologyIso.symm
    let h3 : S.rightHomology ≅ h.H := h.rightHomologyIso
    exact h1 ≪≫ h2 ≪≫ h3
  have h_final : reducedSingularHomology C 0 R X ≅ R := by
    have h4 : reducedSingularHomology C 0 R X = X'.reducedHomology R 0 := by rfl
    rw [h4]
    exact h_iso_Htilde_hH ≪≫ h_main_iso
  exact h_final

end ReducedHomologyTwoComponents

section ConverseIBN

variable [HasBinaryBiproducts C] [LocPathConnectedSpace X] [Nonempty X]
variable [Finite (ConnectedComponents X)]

omit [Nonempty ↑X] in
/-- If coproducts of `R` satisfy the invariant basis number property
    (i.e., `∐_α R ≅ ∐_β R` implies `Nat.card α = Nat.card β` for finite `α, β`),
    and `H₀(X) ≅ R ⊞ R`, then `Nat.card (ConnectedComponents X) = 2`. -/
theorem card_eq_two_of_h0_rank_two_of_ibn
    (h_ibn : ∀ (α β : Type w) [Finite α] [Finite β],
      (∐ (fun (_ : α) ↦ R) ≅ ∐ (fun (_ : β) ↦ R)) → Nat.card α = Nat.card β)
    (h : ((singularHomologyFunctor C 0).obj R).obj X ≅ R ⊞ R) :
    Nat.card (ConnectedComponents X) = 2 := by
  let CC := ConnectedComponents X
  have h1 : ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : CC) ↦ R) :=
    singularHomologyZeroIsoConnectedComponents R X
  have h2 : (∐ (fun (_ : CC) ↦ R)) ≅ R ⊞ R := h1.symm ≪≫ h
  let β := ULift (Fin 2)
  have hβ_fin : Finite β := by infer_instance
  have h3 : (∐ (fun (_ : β) ↦ R)) ≅ R ⊞ R := by
    let a₀ : β := ⟨0⟩
    let a₁ : β := ⟨1⟩
    have h_ne : a₀ ≠ a₁ := by
      intro h
      injection h with h'
      ; contradiction
    have h_univ : ({a₀, a₁} : Set β) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have h_cases : (ULift.down x : ℕ) = 0 ∨ (ULift.down x : ℕ) = 1 := by
        have h : (ULift.down x : ℕ) < 2 := by exact Fin.is_lt (ULift.down x)
        omega
      rcases h_cases with (h0 | h1)
      · have hx : x = a₀ := by
          have hx' : ULift.down x = 0 := by
            apply Fin.ext
            exact h0
          have hx'' : ULift.down x = ULift.down a₀ := by
            rw [hx']
          exact ULift.ext _ _ hx''
        simp [hx]
      · have hx : x = a₁ := by
          have hx' : ULift.down x = 1 := by
            apply Fin.ext
            exact h1
          have hx'' : ULift.down x = ULift.down a₁ := by
            rw [hx']
          exact ULift.ext _ _ hx''
        simp [hx]
    classical
    let fwd : (∐ (fun (_ : β) ↦ R)) ⟶ R ⊞ R :=
      Sigma.desc (fun i : β => if i = a₀ then biprod.inl else biprod.inr)
    let bwd : R ⊞ R ⟶ (∐ (fun (_ : β) ↦ R)) :=
      biprod.desc (Sigma.ι (fun (_ : β) ↦ R) a₀) (Sigma.ι (fun (_ : β) ↦ R) a₁)
    have h_fwd_bwd : fwd ≫ bwd = 𝟙 (∐ (fun (_ : β) ↦ R)) := by
      apply Sigma.hom_ext
      intro i
      have h_cases : i = a₀ ∨ i = a₁ := by
        have h_i_in_univ : i ∈ (Set.univ : Set β) := trivial
        rw [←h_univ] at h_i_in_univ
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h_i_in_univ
      rcases h_cases with (rfl | rfl)
      · -- i = a₀
        have h1 : Sigma.ι (fun (_ : β) ↦ R) a₀ ≫ fwd = biprod.inl := by
          rw [Sigma.ι_desc] ; rw [if_pos rfl]
        calc
          Sigma.ι (fun (_ : β) ↦ R) a₀ ≫ (fwd ≫ bwd)
            = (Sigma.ι (fun (_ : β) ↦ R) a₀ ≫ fwd) ≫ bwd := by rw [Category.assoc]
          _ = biprod.inl ≫ bwd := by rw [h1]
          _ = Sigma.ι (fun (_ : β) ↦ R) a₀ := by simp [bwd, biprod.inl_desc]
          _ = Sigma.ι (fun (_ : β) ↦ R) a₀ ≫ 𝟙 (∐ (fun (_ : β) ↦ R)) := by rw [Category.comp_id]
      · -- i = a₁
        have h1 : Sigma.ι (fun (_ : β) ↦ R) a₁ ≫ fwd = biprod.inr := by
          rw [Sigma.ι_desc] ; rw [if_neg h_ne.symm]
        calc
          Sigma.ι (fun (_ : β) ↦ R) a₁ ≫ (fwd ≫ bwd)
            = (Sigma.ι (fun (_ : β) ↦ R) a₁ ≫ fwd) ≫ bwd := by rw [Category.assoc]
          _ = biprod.inr ≫ bwd := by rw [h1]
          _ = Sigma.ι (fun (_ : β) ↦ R) a₁ := by simp [bwd, biprod.inr_desc]
          _ = Sigma.ι (fun (_ : β) ↦ R) a₁ ≫ 𝟙 (∐ (fun (_ : β) ↦ R)) := by rw [Category.comp_id]
    have h_bwd_fwd : bwd ≫ fwd = 𝟙 (R ⊞ R) := by
      have h_inl : biprod.inl ≫ bwd ≫ fwd = biprod.inl ≫ 𝟙 (R ⊞ R) := by
        have h1 : biprod.inl ≫ bwd = Sigma.ι (fun (_ : β) ↦ R) a₀ := by
          simp [bwd, biprod.inl_desc]
        have h2 : Sigma.ι (fun (_ : β) ↦ R) a₀ ≫ fwd = biprod.inl := by
          rw [Sigma.ι_desc] ; rw [if_pos rfl]
        calc
          biprod.inl ≫ bwd ≫ fwd
            = (biprod.inl ≫ bwd) ≫ fwd := by rw [Category.assoc]
          _ = Sigma.ι (fun (_ : β) ↦ R) a₀ ≫ fwd := by rw [h1]
          _ = biprod.inl := by rw [h2]
          _ = biprod.inl ≫ 𝟙 (R ⊞ R) := by rw [Category.comp_id]
      have h_inr : biprod.inr ≫ bwd ≫ fwd = biprod.inr ≫ 𝟙 (R ⊞ R) := by
        have h1 : biprod.inr ≫ bwd = Sigma.ι (fun (_ : β) ↦ R) a₁ := by
          simp [bwd, biprod.inr_desc]
        have h2 : Sigma.ι (fun (_ : β) ↦ R) a₁ ≫ fwd = biprod.inr := by
          rw [Sigma.ι_desc] ; rw [if_neg h_ne.symm]
        calc
          biprod.inr ≫ bwd ≫ fwd
            = (biprod.inr ≫ bwd) ≫ fwd := by rw [Category.assoc]
          _ = Sigma.ι (fun (_ : β) ↦ R) a₁ ≫ fwd := by rw [h1]
          _ = biprod.inr := by rw [h2]
          _ = biprod.inr ≫ 𝟙 (R ⊞ R) := by rw [Category.comp_id]
      exact biprod.hom_ext' (bwd ≫ fwd) (𝟙 (R ⊞ R)) h_inl h_inr
    exact { hom := fwd, inv := bwd, hom_inv_id := h_fwd_bwd, inv_hom_id := h_bwd_fwd }
  have h4 : (∐ (fun (_ : CC) ↦ R)) ≅ ∐ (fun (_ : β) ↦ R) := h2 ≪≫ h3.symm
  have h5 : Nat.card CC = Nat.card β := by
    letI : Finite β := hβ_fin
    exact h_ibn CC β h4
  have h6 : Nat.card β = 2 := by
    rw [Nat.card_congr (Equiv.ulift (α := Fin 2))]
    ; simp [Nat.card_eq_fintype_card]
  rw [h5, h6]

/-- If coproducts of `R` satisfy the invariant basis number property,
    and `H̃₀(X) ≅ R`, then `Nat.card (ConnectedComponents X) = 2`. -/
theorem card_eq_two_of_reducedH0_rank_one_of_ibn
    (h_ibn : ∀ (α β : Type w) [Finite α] [Finite β],
      (∐ (fun (_ : α) ↦ R) ≅ ∐ (fun (_ : β) ↦ R)) → Nat.card α = Nat.card β)
    (h : reducedSingularHomology C 0 R X ≅ R) :
    Nat.card (ConnectedComponents X) = 2 := by
  have h1 : ((singularHomologyFunctor C 0).obj R).obj X ≅
      (reducedSingularHomology C 0 R X) ⊞ R :=
    singularHomologyZeroIsoReducedSingularHomologyZeroPlusR C R
  have h2 : ((singularHomologyFunctor C 0).obj R).obj X ≅ R ⊞ R := by
    calc
      ((singularHomologyFunctor C 0).obj R).obj X
        ≅ (reducedSingularHomology C 0 R X) ⊞ R := h1
      _ ≅ R ⊞ R := by
        refine' {
          hom := biprod.map h.hom (𝟙 R),
          inv := biprod.map h.inv (𝟙 R),
          hom_inv_id := _,
          inv_hom_id := _
        }
        · ext <;> simp [biprod.map]
        · ext <;> simp [biprod.map]
  exact card_eq_two_of_h0_rank_two_of_ibn (C := C) (R := R) (X := X) h_ibn h2

end ConverseIBN

end

section LocallyConstant

open TopologicalSpace

universe w u

variable {X : Type w} [TopologicalSpace X]
variable {R : Type u}

/-- A locally constant function descends to a function on connected components. -/
def locallyConstantToConnectedComponentsFun (f : LocallyConstant X R) :
    ConnectedComponents X → R := by
  have h : ∀ (a b : X), (connectedComponentSetoid X).r a b → f a = f b := by
    intro a b hab
    have h₁ : connectedComponent a = connectedComponent b := hab
    have h₂ : a ∈ connectedComponent b := by
      rw [← h₁]
      exact mem_connectedComponent
    have h₃ : IsPreconnected (connectedComponent b) :=
      isConnected_connectedComponent.isPreconnected
    exact f.isLocallyConstant.apply_eq_of_isPreconnected h₃ h₂ mem_connectedComponent
  exact Quotient.lift f h

@[simp]
lemma locallyConstantToConnectedComponentsFun_mk (f : LocallyConstant X R) (x : X) :
    locallyConstantToConnectedComponentsFun f (ConnectedComponents.mk x) = f x := by
  rfl

/-- For locally connected spaces, a function on connected components
    gives a locally constant function. -/
def connectedComponentsFunToLocallyConstant [LocallyConnectedSpace X]
    (g : ConnectedComponents X → R) : LocallyConstant X R :=
  have h_main : ∀ (x : X), ∀ (y : X), y ∈ connectedComponent x →
      (g ∘ ConnectedComponents.mk) y = (g ∘ ConnectedComponents.mk) x := by
    intro x y hy
    have h₁ : (y : ConnectedComponents X) = (x : ConnectedComponents X) := by
      rw [ConnectedComponents.coe_eq_coe']
      exact hy
    have h₂ : g (y : ConnectedComponents X) = g (x : ConnectedComponents X) := by
      rw [h₁]
    exact h₂
  ⟨g ∘ ConnectedComponents.mk,
    IsLocallyConstant.of_constant_on_connected_components h_main⟩

@[simp]
lemma connectedComponentsFunToLocallyConstant_apply [LocallyConnectedSpace X]
    (g : ConnectedComponents X → R) (x : X) :
    connectedComponentsFunToLocallyConstant g x = g (ConnectedComponents.mk x) := by
  rfl

/-- For locally connected spaces, locally constant functions on X are in bijection
    with functions on the connected components of X. -/
noncomputable def locallyConstantEquivConnectedComponents [LocallyConnectedSpace X] :
    LocallyConstant X R ≃ (ConnectedComponents X → R) := by
  refine' {
    toFun := locallyConstantToConnectedComponentsFun,
    invFun := connectedComponentsFunToLocallyConstant,
    left_inv := _,
    right_inv := _
  }
  · -- left inverse
    intro f
    ext x
    simp
  · -- right inverse
    intro g
    funext y
    have h_surj : Function.Surjective (ConnectedComponents.mk : X → ConnectedComponents X) :=
      ConnectedComponents.surjective_coe
    obtain ⟨x, hx⟩ := h_surj y
    rw [← hx]
    simp

end LocallyConstant

end AlgebraicTopology

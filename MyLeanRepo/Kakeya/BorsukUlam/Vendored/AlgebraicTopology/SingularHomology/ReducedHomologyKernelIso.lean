module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.ReducedHomology

@[expose] public section


open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open scoped Simplicial

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable [HasBinaryBiproducts C] [CategoryWithHomology C]
variable {X : SSet.{w}} (R : C) [X.Nonempty]

/-- **Reduced H₀ is the kernel of the augmentation map.**

    When X is nonempty, `ker(H₀(X) → R) ≅ H̃₀(X)` where the map is `homology₀ε`. -/
noncomputable def kernelHomology₀εIsoReducedHomologyZero :
    kernel (X.homology₀ε R) ≅ X.reducedHomology R 0 := by
  let S_aug := (X.augmentedChainComplex R).sc' 2 1 0
  let h_aug : S_aug.RightHomologyData := S_aug.rightHomologyData
  let Q' := ∐ (fun (_ : π₀ X) ↦ R)
  let p' : S_aug.X₂ ⟶ Q' := π₀.fromChainComplexXZero X R
  have hwp' : S_aug.f ≫ p' = 0 := by
    have h_f : S_aug.f = (X.chainComplex R).d 1 0 := by
      simp [S_aug, augmentedChainComplex, ChainComplex.augment]
    rw [h_f]
    exact π₀.d_fromChainComplexXZero X R 1
  let hp' : IsColimit (CokernelCofork.ofπ p' hwp') :=
    isColimitCokernelCoforkChainComplexDOneZero X R
  let e_hom : h_aug.Q ⟶ Q' := h_aug.descQ p' hwp'
  let e_inv : Q' ⟶ h_aug.Q := hp'.desc (CokernelCofork.ofπ h_aug.p h_aug.wp)
  have he1 : h_aug.p ≫ e_hom = p' := h_aug.p_descQ p' hwp'
  have he2 : p' ≫ e_inv = h_aug.p := by
    exact hp'.fac (CokernelCofork.ofπ h_aug.p h_aug.wp) WalkingParallelPair.one
  have e_hom_inv : e_hom ≫ e_inv = 𝟙 h_aug.Q := by
    apply Cofork.IsColimit.hom_ext h_aug.hp
    have h_eq : h_aug.p ≫ (e_hom ≫ e_inv) = h_aug.p ≫ 𝟙 h_aug.Q := by
      calc
        h_aug.p ≫ (e_hom ≫ e_inv)
          = (h_aug.p ≫ e_hom) ≫ e_inv := by simp [Category.assoc]
        _ = p' ≫ e_inv := by rw [he1]
        _ = h_aug.p := by rw [he2]
        _ = h_aug.p ≫ 𝟙 h_aug.Q := by rw [Category.comp_id]
    exact h_eq
  have e_inv_hom : e_inv ≫ e_hom = 𝟙 Q' := by
    apply Cofork.IsColimit.hom_ext hp'
    have h_eq : p' ≫ (e_inv ≫ e_hom) = p' ≫ 𝟙 Q' := by
      calc
        p' ≫ (e_inv ≫ e_hom)
          = (p' ≫ e_inv) ≫ e_hom := by simp [Category.assoc]
        _ = h_aug.p ≫ e_hom := by rw [he2]
        _ = p' := by rw [he1]
        _ = p' ≫ 𝟙 Q' := by rw [Category.comp_id]
    exact h_eq
  let e_iso : h_aug.Q ≅ Q' :=
    { hom := e_hom, inv := e_inv, hom_inv_id := e_hom_inv, inv_hom_id := e_inv_hom }
  let g' : Q' ⟶ R := Sigma.desc (fun (_ : π₀ X) ↦ 𝟙 R)
  have hε : S_aug.g = p' ≫ g' := by
    have h_g : S_aug.g = X.augmentationMap R := by
      simp [S_aug, augmentedChainComplex, ChainComplex.augment]
    rw [h_g, augmentationMap] ; rfl
  let g : h_aug.Q ⟶ R := h_aug.descQ S_aug.g S_aug.zero
  have h_induced : g = e_iso.hom ≫ g' := by
    apply Cofork.IsColimit.hom_ext h_aug.hp
    have h_left : h_aug.p ≫ g = S_aug.g := h_aug.p_descQ S_aug.g S_aug.zero
    have h_right : h_aug.p ≫ (e_iso.hom ≫ g') = S_aug.g := by
      calc
        h_aug.p ≫ (e_iso.hom ≫ g')
          = (h_aug.p ≫ e_hom) ≫ g' := by simp [Category.assoc] ; rfl
        _ = p' ≫ g' := by rw [he1]
        _ = S_aug.g := by rw [hε]
    exact h_left.trans h_right.symm
  let k_g : h_aug.H ⟶ h_aug.Q := h_aug.ι
  have h_k_g : k_g ≫ g = 0 := h_aug.wι
  let h_iso_H0_hQ : X.homology R 0 ≅ h_aug.Q :=
    X.homology₀Iso R ≪≫ e_iso.symm
  have h_comm : X.homology₀ε R = h_iso_H0_hQ.hom ≫ g := by
    dsimp only [h_iso_H0_hQ]
    have h1 : X.homology₀ε R = (X.homology₀Iso R).hom ≫ g' := by rfl
    have h2 : (X.homology₀Iso R).hom ≫ g' = (X.homology₀Iso R).hom ≫ (e_iso.inv ≫ g) := by
      congr 1
      rw [h_induced] ; simp
    have h3 : (X.homology₀Iso R).hom ≫ (e_iso.inv ≫ g) = (X.homology₀Iso R).hom ≫ e_iso.inv ≫ g := by
      simp
    have h4 : h_iso_H0_hQ.hom ≫ g = (X.homology₀Iso R).hom ≫ e_iso.inv ≫ g := by
      simp [h_iso_H0_hQ]
    rw [h1, h2, h3, ← h4]
  let k_ε : kernel (X.homology₀ε R) ⟶ X.homology R 0 := kernel.ι (X.homology₀ε R)
  have h1 : (k_ε ≫ h_iso_H0_hQ.hom) ≫ g = 0 := by
    have h_assoc : (k_ε ≫ h_iso_H0_hQ.hom) ≫ g = k_ε ≫ (h_iso_H0_hQ.hom ≫ g) := by
      simp [Category.assoc]
    rw [h_assoc, ← h_comm, kernel.condition (X.homology₀ε R)]
  let fwd_comm : kernel (X.homology₀ε R) ⟶ h_aug.H :=
    h_aug.hι.lift (KernelFork.ofι (k_ε ≫ h_iso_H0_hQ.hom) h1)
  have h_fwd_comm : fwd_comm ≫ k_g = k_ε ≫ h_iso_H0_hQ.hom :=
    h_aug.hι.fac (KernelFork.ofι (k_ε ≫ h_iso_H0_hQ.hom) h1) WalkingParallelPair.zero
  let bwd_map : h_aug.H ⟶ X.homology R 0 := k_g ≫ h_iso_H0_hQ.inv
  have h_bwd_comp : bwd_map ≫ X.homology₀ε R = 0 := by
    calc
      bwd_map ≫ X.homology₀ε R
        = (k_g ≫ h_iso_H0_hQ.inv) ≫ X.homology₀ε R := by rfl
      _ = k_g ≫ (h_iso_H0_hQ.inv ≫ X.homology₀ε R) := by simp [Category.assoc]
      _ = k_g ≫ (h_iso_H0_hQ.inv ≫ (h_iso_H0_hQ.hom ≫ g)) := by rw [h_comm]
      _ = k_g ≫ ((h_iso_H0_hQ.inv ≫ h_iso_H0_hQ.hom) ≫ g) := by simp
      _ = k_g ≫ (𝟙 h_aug.Q ≫ g) := by rw [Iso.inv_hom_id]
      _ = k_g ≫ g := by rw [Category.id_comp]
      _ = 0 := h_k_g
  let bwd_comm : h_aug.H ⟶ kernel (X.homology₀ε R) :=
    kernel.lift (X.homology₀ε R) bwd_map h_bwd_comp
  have h_bwd_comm_ι : bwd_comm ≫ k_ε = bwd_map :=
    kernel.lift_ι (X.homology₀ε R) bwd_map h_bwd_comp
  have h_iso_Htilde_hH : X.reducedHomology R 0 ≅ h_aug.H := by
    let S2 := (X.augmentedChainComplex R).sc' 2 1 0
    have h1 : (X.augmentedChainComplex R).homology 1 ≅ S2.homology :=
      (X.augmentedChainComplex R).homologyIsoSc' 2 1 0 (by simp) (by simp)
    have h2 : S2.homology ≅ S2.rightHomology := S2.rightHomologyIso.symm
    have h3 : S2.rightHomology ≅ h_aug.H := h_aug.rightHomologyIso
    exact h1 ≪≫ h2 ≪≫ h3
  have h_mono_k_g : Mono k_g := by exact ShortComplex.RightHomologyData.instMonoι h_aug
  have h_kern_comm : kernel (X.homology₀ε R) ≅ h_aug.H := by
    have h1 : fwd_comm ≫ bwd_comm = 𝟙 (kernel (X.homology₀ε R)) := by
      have h_eq : (fwd_comm ≫ bwd_comm) ≫ k_ε = 𝟙 (kernel (X.homology₀ε R)) ≫ k_ε := by
        calc
          (fwd_comm ≫ bwd_comm) ≫ k_ε
            = fwd_comm ≫ (bwd_comm ≫ k_ε) := by simp [Category.assoc]
          _ = fwd_comm ≫ bwd_map := by rw [h_bwd_comm_ι]
          _ = fwd_comm ≫ (k_g ≫ h_iso_H0_hQ.inv) := by rfl
          _ = (fwd_comm ≫ k_g) ≫ h_iso_H0_hQ.inv := by simp [Category.assoc]
          _ = (k_ε ≫ h_iso_H0_hQ.hom) ≫ h_iso_H0_hQ.inv := by rw [h_fwd_comm]
          _ = k_ε ≫ (h_iso_H0_hQ.hom ≫ h_iso_H0_hQ.inv) := by simp [Category.assoc]
          _ = k_ε ≫ 𝟙 (X.homology R 0) := by rw [Iso.hom_inv_id]
          _ = k_ε := by rw [Category.comp_id]
          _ = 𝟙 (kernel (X.homology₀ε R)) ≫ k_ε := by rw [Category.id_comp]
      exact (cancel_mono k_ε).mp h_eq
    have h2 : bwd_comm ≫ fwd_comm = 𝟙 h_aug.H := by
      have h_eq : (bwd_comm ≫ fwd_comm) ≫ k_g = 𝟙 h_aug.H ≫ k_g := by
        calc
          (bwd_comm ≫ fwd_comm) ≫ k_g
            = bwd_comm ≫ (fwd_comm ≫ k_g) := by simp [Category.assoc]
          _ = bwd_comm ≫ (k_ε ≫ h_iso_H0_hQ.hom) := by rw [h_fwd_comm]
          _ = (bwd_comm ≫ k_ε) ≫ h_iso_H0_hQ.hom := by simp [Category.assoc]
          _ = bwd_map ≫ h_iso_H0_hQ.hom := by rw [h_bwd_comm_ι]
          _ = (k_g ≫ h_iso_H0_hQ.inv) ≫ h_iso_H0_hQ.hom := by rfl
          _ = k_g ≫ (h_iso_H0_hQ.inv ≫ h_iso_H0_hQ.hom) := by simp [Category.assoc]
          _ = k_g ≫ 𝟙 h_aug.Q := by rw [Iso.inv_hom_id]
          _ = k_g := by rw [Category.comp_id]
          _ = 𝟙 h_aug.H ≫ k_g := by rw [Category.id_comp]
      exact (cancel_mono k_g).mp h_eq
    exact ⟨fwd_comm, bwd_comm, h1, h2⟩
  exact h_kern_comm ≪≫ h_iso_Htilde_hH.symm

end SSet

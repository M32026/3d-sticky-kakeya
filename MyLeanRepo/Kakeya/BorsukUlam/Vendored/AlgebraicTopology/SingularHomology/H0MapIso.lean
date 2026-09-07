module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.Topology.Connected.PathConnected
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.HomologyZeroPathComponents
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.PiZeroPathComponents
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.ReducedHomology

@[expose] public section


open AlgebraicTopology CategoryTheory Limits TopCat Simplicial SSet
open HomologicalComplex

universe w v u

-- SSet-level lemmas (proved earlier)
namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C]
variable (R : C) [CategoryWithHomology C]

variable {X Y : SSet} (f : X ⟶ Y)

lemma liftCycles_cyclesMap_comm (x : X _⦋0⦌) :
    (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
    HomologicalComplex.cyclesMap (chainComplexMap f R) 0 =
    (Y.chainComplex R).liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
  let CX := X.chainComplex R
  let CY := Y.chainComplex R
  let φ := chainComplexMap f R
  let iX := CX.iCycles 0
  let iY := CY.iCycles 0
  let a := CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp)
  let b := CY.liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp)
  have h1 : a ≫ iX = X.ιChainComplex x := by
    exact liftCycles_i CX (X.ιChainComplex x) 0 (by simp) (by simp)
  have h2 : HomologicalComplex.cyclesMap φ 0 ≫ iY = iX ≫ φ.f 0 := by exact cyclesMap_i φ 0
  have h3 : b ≫ iY = Y.ιChainComplex (f.app _ x) := by
    exact liftCycles_i CY (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp)
  have h4 : X.ιChainComplex x ≫ φ.f 0 = Y.ιChainComplex (f.app _ x) := by exact ι_chainComplexMap_f X Y f R x
  have h5 : (a ≫ HomologicalComplex.cyclesMap φ 0) ≫ iY = b ≫ iY := by
    calc
      (a ≫ HomologicalComplex.cyclesMap φ 0) ≫ iY
        = a ≫ (HomologicalComplex.cyclesMap φ 0 ≫ iY) := by rw [Category.assoc]
      _ = a ≫ (iX ≫ φ.f 0) := by rw [h2]
      _ = (a ≫ iX) ≫ φ.f 0 := by rw [← Category.assoc]
      _ = X.ιChainComplex x ≫ φ.f 0 := by rw [h1]
      _ = Y.ιChainComplex (f.app _ x) := by rw [h4]
      _ = b ≫ iY := by rw [h3]
  have h_mono : Mono iY := by exact instMonoICycles CY 0
  exact (cancel_mono iY).mp h5

lemma liftCycles_homologyMap_homologyπ (x : X _⦋0⦌) :
    ((X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex R).homologyπ 0) ≫ homologyMap (chainComplexMap f R) 0 =
    (Y.chainComplex R).liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) ≫
      (Y.chainComplex R).homologyπ 0 := by
  let CX := X.chainComplex R
  let CY := Y.chainComplex R
  let φ := chainComplexMap f R
  have h_comm : CX.homologyπ 0 ≫ homologyMap φ 0 =
      HomologicalComplex.cyclesMap φ 0 ≫ CY.homologyπ 0 := by exact homologyπ_naturality φ 0
  have h_lift_cyc := liftCycles_cyclesMap_comm R f x
  calc
    (CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫ CX.homologyπ 0)
        ≫ homologyMap φ 0
      = CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
          (CX.homologyπ 0 ≫ homologyMap φ 0) := by rw [← Category.assoc]
    _ = CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
          (HomologicalComplex.cyclesMap φ 0 ≫ CY.homologyπ 0) := by rw [h_comm]
    _ = (CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
          HomologicalComplex.cyclesMap φ 0) ≫ CY.homologyπ 0 := by rw [← Category.assoc]
    _ = CY.liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) ≫
          CY.homologyπ 0 := by rw [h_lift_cyc]

lemma augmentation_naturality :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  let CX := X.chainComplex R
  let CY := Y.chainComplex R
  let g1 := SSet.homologyMap f R 0 ≫ Y.homology₀ε R
  let g2 := X.homology₀ε R
  let φ_iso := (X.homology₀Iso R).hom
  let e (x : X _⦋0⦌) := CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫ CX.homologyπ 0
  have h_e_φ : ∀ (x : X _⦋0⦌),
      (e x) ≫ φ_iso = Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) := by
    intro x
    have h : (e x) ≫ φ_iso =
        CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
          CX.homologyπ 0 ≫ (X.homology₀Iso R).hom := by
      dsimp only [e] ; rw [← Category.assoc]
    rw [h]
    have h' : CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
        CX.homologyπ 0 ≫ (X.homology₀Iso R).hom =
        Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) := by exact liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x
    exact h'
  have h_eq1 : ∀ (x : X _⦋0⦌), (e x) ≫ g1 = 𝟙 R := by
    intro x
    let y : Y _⦋0⦌ := f.app _ x
    have h_lift := liftCycles_homologyMap_homologyπ R f x
    have h_main : (e x) ≫ SSet.homologyMap f R 0 ≫ Y.homology₀ε R = 𝟙 R := by
      have h1 : (e x) ≫ SSet.homologyMap f R 0 =
          CY.liftCycles (Y.ιChainComplex y) 0 (by simp) (by simp) ≫ CY.homologyπ 0 := by
        dsimp only [e, SSet.homologyMap] ; exact h_lift
      have h2 : (e x) ≫ SSet.homologyMap f R 0 ≫ Y.homology₀ε R =
          ((e x) ≫ SSet.homologyMap f R 0) ≫ Y.homology₀ε R := by rw [← Category.assoc]
      rw [h2, h1]
      have h3 : (CY.liftCycles (Y.ιChainComplex y) 0 (by simp) (by simp) ≫
            CY.homologyπ 0) ≫ Y.homology₀ε R =
          CY.liftCycles (Y.ιChainComplex y) 0 (by simp) (by simp) ≫
            CY.homologyπ 0 ≫ Y.homology₀ε R := by rw [← Category.assoc]
      rw [h3]
      have h4 : CY.liftCycles (Y.ιChainComplex y) 0 (by simp) (by simp) ≫
          CY.homologyπ 0 ≫ Y.homology₀ε R = 𝟙 R := by exact liftCycles_ιChainComplex_homologyπ_homology₀ε Y R y
      exact h4
    exact h_main
  have h_eq2 : ∀ (x : X _⦋0⦌), (e x) ≫ g2 = 𝟙 R := by
    intro x
    dsimp only [g2, e]
    have h : (CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
          CX.homologyπ 0) ≫ X.homology₀ε R =
        CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
          CX.homologyπ 0 ≫ X.homology₀ε R := by rw [← Category.assoc]
    rw [h]
    have h' : CX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
        CX.homologyπ 0 ≫ X.homology₀ε R = 𝟙 R := by exact liftCycles_ιChainComplex_homologyπ_homology₀ε X R x
    exact h'
  have h_gen : ∀ (x : X _⦋0⦌), (e x) ≫ g1 = (e x) ≫ g2 := by
    intro x; rw [h_eq1 x, h_eq2 x]
  have h_sigma_jointly_epi : ∀ (Z : C) (k1 k2 : (∐ fun (_ : π₀ X) => R) ⟶ Z),
      (∀ (x : X _⦋0⦌), Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) ≫ k1 =
                        Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) ≫ k2) → k1 = k2 := by
    intro Z k1 k2 h
    apply Sigma.hom_ext k1 k2
    intro i
    obtain ⟨x, rfl⟩ : ∃ (x : X _⦋0⦌), π₀.mk x = i := π₀.mk_surjective i
    exact h x
  have h_jointly_epi : ∀ (Z : C) (k1 k2 : X.homology R 0 ⟶ Z),
      (∀ (x : X _⦋0⦌), (e x) ≫ k1 = (e x) ≫ k2) → k1 = k2 := by
    intro Z k1 k2 h
    have h_φ_mono : Mono φ_iso := by exact IsIso.mono_of_iso φ_iso
    have h' : ∀ (x : X _⦋0⦌),
        Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) ≫ (inv φ_iso ≫ k1) =
        Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) ≫ (inv φ_iso ≫ k2) := by
      intro x
      have h_e_φ_x : (e x) ≫ φ_iso = Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) := h_e_φ x
      have h_left : (e x) ≫ k1 = (e x) ≫ k2 := h x
      have h6 : ((e x) ≫ φ_iso) ≫ (inv φ_iso ≫ k1) = (e x) ≫ k1 := by
        have h_step1 : ((e x) ≫ φ_iso) ≫ (inv φ_iso ≫ k1) =
            (e x) ≫ φ_iso ≫ inv φ_iso ≫ k1 := by rw [Category.assoc]
        rw [h_step1]
        have h_step2 : (e x) ≫ φ_iso ≫ inv φ_iso ≫ k1 =
            ((e x) ≫ (φ_iso ≫ inv φ_iso)) ≫ k1 := by simp
        rw [h_step2]
        have h_step3 : (e x) ≫ (φ_iso ≫ inv φ_iso) = (e x) := by
          rw [IsIso.hom_inv_id φ_iso] ; exact Category.comp_id (e x)
        rw [h_step3]
      have h8 : ((e x) ≫ φ_iso) ≫ (inv φ_iso ≫ k2) = (e x) ≫ k2 := by
        have h_step1 : ((e x) ≫ φ_iso) ≫ (inv φ_iso ≫ k2) =
            (e x) ≫ φ_iso ≫ inv φ_iso ≫ k2 := by rw [Category.assoc]
        rw [h_step1]
        have h_step2 : (e x) ≫ φ_iso ≫ inv φ_iso ≫ k2 =
            ((e x) ≫ (φ_iso ≫ inv φ_iso)) ≫ k2 := by simp
        rw [h_step2]
        have h_step3 : (e x) ≫ (φ_iso ≫ inv φ_iso) = (e x) := by
          rw [IsIso.hom_inv_id φ_iso] ; exact Category.comp_id (e x)
        rw [h_step3]
      calc
        Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) ≫ (inv φ_iso ≫ k1)
          = ((e x) ≫ φ_iso) ≫ (inv φ_iso ≫ k1) := by rw [h_e_φ_x]
        _ = (e x) ≫ k1 := h6
        _ = (e x) ≫ k2 := h_left
        _ = ((e x) ≫ φ_iso) ≫ (inv φ_iso ≫ k2) := h8.symm
        _ = Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) ≫ (inv φ_iso ≫ k2) := by rw [h_e_φ_x]
    have h_eq : inv φ_iso ≫ k1 = inv φ_iso ≫ k2 :=
      h_sigma_jointly_epi Z (inv φ_iso ≫ k1) (inv φ_iso ≫ k2) h'
    haveI : Epi (inv φ_iso) := by exact IsIso.epi_of_iso (inv φ_iso)
    exact (cancel_epi (inv φ_iso)).mp h_eq
  exact h_jointly_epi R g1 g2 h_gen

lemma h0_map_iso_of_connected [X.IsConnected] [Y.IsConnected] :
    IsIso (SSet.homologyMap f R 0) := by
  have hεX : IsIso (X.homology₀ε R) := by exact instIsIsoHomology₀εOfIsConnected X R
  have hεY : IsIso (Y.homology₀ε R) := by exact instIsIsoHomology₀εOfIsConnected Y R
  have h_nat : SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R :=
    augmentation_naturality R f
  let g : Y.homology R 0 ⟶ X.homology R 0 :=
    Y.homology₀ε R ≫ inv (X.homology₀ε R)
  have h1 : SSet.homologyMap f R 0 ≫ g = 𝟙 (X.homology R 0) := by
    dsimp only [g]
    have h : SSet.homologyMap f R 0 ≫ Y.homology₀ε R ≫ inv (X.homology₀ε R) =
        (SSet.homologyMap f R 0 ≫ Y.homology₀ε R) ≫ inv (X.homology₀ε R) := by rw [← Category.assoc]
    rw [h, h_nat] ; simp [IsIso.hom_inv_id]
  have h2 : g ≫ SSet.homologyMap f R 0 = 𝟙 (Y.homology R 0) := by
    dsimp only [g]
    have h3 : SSet.homologyMap f R 0 = X.homology₀ε R ≫ inv (Y.homology₀ε R) := by
      calc
        SSet.homologyMap f R 0
          = SSet.homologyMap f R 0 ≫ 𝟙 (Y.homology R 0) := by simp
        _ = SSet.homologyMap f R 0 ≫ (Y.homology₀ε R ≫ inv (Y.homology₀ε R)) := by
            rw [IsIso.hom_inv_id (Y.homology₀ε R)]
        _ = (SSet.homologyMap f R 0 ≫ Y.homology₀ε R) ≫ inv (Y.homology₀ε R) := by
            rw [← Category.assoc]
        _ = X.homology₀ε R ≫ inv (Y.homology₀ε R) := by rw [h_nat]
    rw [h3]
    have h4 : (Y.homology₀ε R ≫ inv (X.homology₀ε R)) ≫
        (X.homology₀ε R ≫ inv (Y.homology₀ε R)) = 𝟙 (Y.homology R 0) := by
      calc
        (Y.homology₀ε R ≫ inv (X.homology₀ε R)) ≫
            (X.homology₀ε R ≫ inv (Y.homology₀ε R))
          = Y.homology₀ε R ≫ (inv (X.homology₀ε R) ≫ X.homology₀ε R) ≫ inv (Y.homology₀ε R) := by
            simp [Category.assoc]
        _ = Y.homology₀ε R ≫ 𝟙 R ≫ inv (Y.homology₀ε R) := by
            rw [IsIso.inv_hom_id (X.homology₀ε R)]
        _ = Y.homology₀ε R ≫ inv (Y.homology₀ε R) := by simp
        _ = 𝟙 (Y.homology R 0) := IsIso.hom_inv_id (Y.homology₀ε R)
    exact h4
  exact ⟨g, h1, h2⟩

end SSet

namespace AlgebraicTopology

section TopologicalSSetConnected

variable {X : TopCat.{w}}

/-- If X is path-connected, then its singular simplicial set is connected. -/
lemma isConnected_sset_of_pathConnected [PathConnectedSpace X] :
    (TopCat.toSSet.obj X).IsConnected := by
  have h_main : Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) :=
    pathConnectedSpace_iff_zerothHomotopy.mp inferInstance
  have h_sub : Subsingleton (ZerothHomotopy X) := h_main.2
  have h_nonempty : Nonempty (ZerothHomotopy X) := h_main.1
  let e : SSet.π₀ (TopCat.toSSet.obj X) ≃ ZerothHomotopy X :=
    singularPiZeroEquivZerothHomotopy X
  have h1 : Subsingleton (SSet.π₀ (TopCat.toSSet.obj X)) := by
    exact (Equiv.subsingleton_congr (_root_.id e.symm)).mp h_sub
  have h2 : Nonempty (SSet.π₀ (TopCat.toSSet.obj X)) := by
    exact Nonempty.map e.symm h_nonempty
  rw [SSet.isConnected_iff_nonempty_unique]
  letI h_sub' : Subsingleton (SSet.π₀ (TopCat.toSSet.obj X)) := h1
  letI h_nonempty' : Nonempty (SSet.π₀ (TopCat.toSSet.obj X)) := h2
  letI h_inhabited : Inhabited (SSet.π₀ (TopCat.toSSet.obj X)) :=
    Classical.inhabited_of_nonempty h_nonempty'
  have h_unique : Unique (SSet.π₀ (TopCat.toSSet.obj X)) :=
    Unique.mk' _
  exact ⟨h_unique⟩

end TopologicalSSetConnected

section TopologicalH0MapIso

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable (R : C) [CategoryWithHomology C]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)

/-- If both X and Y are path-connected, then the induced map H₀(f) is an isomorphism. -/
theorem isIso_singularHomologyMap_zero_of_pathConnected
    [PathConnectedSpace X] [PathConnectedSpace Y] :
    IsIso (homologyMap ((singularChainComplexFunctor C).obj R |>.map f) 0) := by
  let X' := TopCat.toSSet.obj X
  let Y' := TopCat.toSSet.obj Y
  let f' := TopCat.toSSet.map f
  have hX_conn : X'.IsConnected := by
    exact isConnected_sset_of_pathConnected (X := X)
  have hY_conn : Y'.IsConnected := by
    exact isConnected_sset_of_pathConnected (X := Y)
  letI : X'.IsConnected := hX_conn
  letI : Y'.IsConnected := hY_conn
  have h_main : IsIso (SSet.homologyMap f' R 0) :=
    SSet.h0_map_iso_of_connected R f'
  exact (MorphismProperty.isomorphisms.iff (homologyMap (((singularChainComplexFunctor C).obj R).map f) 0)).mp h_main

end TopologicalH0MapIso

end AlgebraicTopology

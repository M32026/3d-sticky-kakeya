module

public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.SphereZeroZerothHomotopy
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.H0MapIso
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.HomologyZeroPathComponents
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.HomologyZero
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.ReducedHomologyKernelIso
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.CategoryTheory.Limits.KernelCompMono
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.CategoryTheory.Limits.KernelIsoOfCompatibleIso
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.CategoryTheory.Limits.SigmaBoolIsoBiprod

@[expose] public section

/-!
# First Homology of the Circle

This file computes the first singular homology of the standard Euclidean
one-sphere with integer coefficients.
-/


noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open TopCat (toSSet)
open Metric

namespace Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace

open StdSphereHomology


/-- A homotopy equivalence induces an equivalence on zeroth homotopy groups (path components). -/
noncomputable def zerothHomotopyEquivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    ZerothHomotopy X ≃ ZerothHomotopy Y := by
  let f : C(X, Y) := e.toFun
  let g : C(Y, X) := e.invFun
  let f_star : ZerothHomotopy X → ZerothHomotopy Y :=
    ZerothHomotopy.lift (fun x : X => ZerothHomotopy.mk (f x))
      (by
        intro x y p
        exact ZerothHomotopy.sound (p.map f.continuous))
  let g_star : ZerothHomotopy Y → ZerothHomotopy X :=
    ZerothHomotopy.lift (fun y : Y => ZerothHomotopy.mk (g y))
      (by
        intro y z p
        exact ZerothHomotopy.sound (p.map g.continuous))
  have h1 : ∀ (y : Y), f_star (g_star (ZerothHomotopy.mk y)) = ZerothHomotopy.mk y := by
    intro y
    rcases e.right_inv with ⟨H⟩
    have h_path : Path (f (g y)) y := H.evalAt y
    exact ZerothHomotopy.sound h_path
  have h2 : ∀ (x : X), g_star (f_star (ZerothHomotopy.mk x)) = ZerothHomotopy.mk x := by
    intro x
    rcases e.left_inv with ⟨H⟩
    have h_path : Path (g (f x)) x := H.evalAt x
    exact ZerothHomotopy.sound h_path
  refine' {
    toFun := f_star,
    invFun := g_star,
    left_inv := by
      intro z
      obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
      exact h2 x,
    right_inv := by
      intro z
      obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective z
      exact h1 y
  }

variable (n : ℕ)

/-!
## H₁(S¹) ≅ ℤ

Proof using the Mayer-Vietoris sequence:
1. Cover S¹ with two open arcs U, V (both contractible)
2. Their intersection UV has two contractible components
3. By degreeZeroBoundaryIso: H₁(S¹) ≅ ker(H₀(UV) → H₀(U) ⊕ H₀(V))
4. The kernel is isomorphic to ℤ (the "diagonal" subgroup)
-/

/-- H₁(S¹) ≅ ℤ -/
noncomputable def h1SphereOneIsoInt :
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1
      (TopCat.of (SphereType 1)) ≅ AddCommGrpCat.of ℤ := by
  let n := 1
  have hn_pos : 0 < n := by norm_num
  let p : SphereType n := Classical.arbitrary _
  let ts := TwoSubspaces.twoSubspacesOfOpens (U_set n p) (V_set n p)
  have hcover' : (Set.univ : Set (SphereType n)) ⊆ U_set n p ∪ V_set n p :=
    hcover n p
  have h_jU_emb : Topology.IsEmbedding ts.jU :=
    TwoSubspaces.twoSubspacesOfOpens_jU_emb (U_set n p) (V_set n p)
  have h_jV_emb : Topology.IsEmbedding ts.jV :=
    TwoSubspaces.twoSubspacesOfOpens_jV_emb (U_set n p) (V_set n p)
  have h_pullback : IsPullback ts.iU ts.iV ts.jU ts.jV :=
    TwoSubspaces.twoSubspacesOfOpens_isPullback (U_set n p) (V_set n p)
  have h_range_jU : Set.range ts.jU = U_set n p := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have h_y : y.val ∈ U_set n p := y.prop
      have h_eq : (ts.jU y) = x := hy
      have h_x_in_U : x ∈ U_set n p := by
        have h1 : (ts.jU y) = y.val := by
          dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
          rfl
        have h2 : (ts.jU y) = x := h_eq
        rw [←h2, h1]
        exact h_y
      exact h_x_in_U
    · intro hx
      have h_y : ∃ (y : {x // x ∈ U_set n p}), (ts.jU y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩
        rfl
      rcases h_y with ⟨y, hy⟩
      exact ⟨y, hy⟩
  have h_range_jV : Set.range ts.jV = V_set n p := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have h_y : y.val ∈ V_set n p := y.prop
      have h_eq : (ts.jV y) = x := hy
      have h_x_in_V : x ∈ V_set n p := by
        have h1 : (ts.jV y) = y.val := by
          dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
          rfl
        have h2 : (ts.jV y) = x := h_eq
        rw [←h2, h1]
        exact h_y
      exact h_x_in_V
    · intro hx
      have h_y : ∃ (y : {x // x ∈ V_set n p}), (ts.jV y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩
        rfl
      rcases h_y with ⟨y, hy⟩
      exact ⟨y, hy⟩
  haveI hMono_jU : Mono ts.jU := by
    rw [TopCat.mono_iff_injective ts.jU]
    exact h_jU_emb.injective
  haveI hMono_jV : Mono ts.jV := by
    rw [TopCat.mono_iff_injective ts.jV]
    exact h_jV_emb.injective
  have h_iU_emb : Topology.IsEmbedding ts.iU := by
    have h_subset : (U_set n p ∩ V_set n p : Set (SphereType n)) ⊆ U_set n p := by simp
    have h_main : Topology.IsEmbedding (Set.inclusion h_subset) := Topology.IsEmbedding.inclusion h_subset
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    exact h_main
  haveI hMono_iU : Mono ts.iU := by
    rw [TopCat.mono_iff_injective ts.iU]
    exact h_iU_emb.injective
  have h_dw_pullback : DegreewisePullbackAssumption ts :=
    degreewisePullback_of_isPullback_of_embeddings ts h_pullback h_jU_emb h_jV_emb
  let S := mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts
  have hS : S.ShortExact :=
    mvSES_shortExact' AddCommGrpCat (AddCommGrpCat.of ℤ) ts h_dw_pullback
  have h_mid_1 : IsZero (S.X₂.homology 1) :=
    isZero_biprod_homology (K := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U)
      (L := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.V) (n := 1)
      (hU_vanishing n p 1 (by norm_num))
      (hV_vanishing n p 1 (by norm_num))
  have h_small_chain_1 :
      IsIso (HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) 1) :=
    TwoSubspaces.smallChainTheorem_TwoSubspaces_pseudoMetric ts rfl h_jU_emb h_jV_emb
      (by rw [h_range_jU]; exact hU_open n p)
      (by rw [h_range_jV]; exact hV_open n p)
      (by rw [h_range_jU, h_range_jV]; exact hcover') 0
  let f0 := HomologicalComplex.homologyMap S.f 0
  have h_boundary_iso : S.X₃.homology 1 ≅ kernel f0 :=
    degreeZeroBoundaryIso hS h_mid_1
  let f_small := HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) 1
  have h_small_isIso : IsIso f_small := h_small_chain_1
  have h_small_iso : (smallChainComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).homology 1 ≅
      singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1 ts.X := by
    have h_out : ∃ (g : singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) 1 ts.X ⟶
        (smallChainComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).homology 1),
        f_small ≫ g = 𝟙 _ ∧ g ≫ f_small = 𝟙 _ := h_small_isIso.out
    let g := Classical.choose h_out
    have hg : f_small ≫ g = 𝟙 _ ∧ g ≫ f_small = 𝟙 _ := Classical.choose_spec h_out
    exact ⟨f_small, g, hg.1, hg.2⟩
  let R := AddCommGrpCat.of ℤ
  let iU_star := (singularChainComplexFunctor AddCommGrpCat).obj R |>.map ts.iU
  let iV_star := (singularChainComplexFunctor AddCommGrpCat).obj R |>.map ts.iV
  let iU_h0 := HomologicalComplex.homologyMap iU_star 0
  let iV_h0 := HomologicalComplex.homologyMap iV_star 0
  let H0_UV := singularHomology' AddCommGrpCat R 0 ts.UV
  let H0_U := singularHomology' AddCommGrpCat R 0 ts.U
  let H0_V := singularHomology' AddCommGrpCat R 0 ts.V
  let π1 : S.X₂.homology 0 ⟶ H0_U :=
    HomologicalComplex.homologyMap (biprod.fst : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.U) 0
  let π2 : S.X₂.homology 0 ⟶ H0_V :=
    HomologicalComplex.homologyMap (biprod.snd : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.V) 0
  have h1_fst : S.f ≫ biprod.fst = iU_star := by
    have h : mvMapF AddCommGrpCat R ts ≫ biprod.fst = iU_star := by
      simp [mvMapF, Preadditive.sub_comp]
      abel
    exact h
  have h1_snd : S.f ≫ biprod.snd = -iV_star := by
    have h : mvMapF AddCommGrpCat R ts ≫ biprod.snd = -iV_star := by
      simp [mvMapF, Preadditive.sub_comp]
      abel
    exact h
  have h_f0_comp1 : f0 ≫ π1 = iU_h0 := by
    have h_comp : HomologicalComplex.homologyMap (S.f ≫ biprod.fst) 0 = f0 ≫ π1 :=
      HomologicalComplex.homologyMap_comp S.f biprod.fst 0
    have h : HomologicalComplex.homologyMap (S.f ≫ biprod.fst) 0 = iU_h0 := by
      rw [h1_fst]
      rfl
    rw [←h_comp]
    exact h
  have h_f0_comp2 : f0 ≫ π2 = -iV_h0 := by
    have h_comp : HomologicalComplex.homologyMap (S.f ≫ biprod.snd) 0 = f0 ≫ π2 :=
      HomologicalComplex.homologyMap_comp S.f biprod.snd 0
    have h : HomologicalComplex.homologyMap (S.f ≫ biprod.snd) 0 = -iV_h0 := by
      rw [h1_snd]
      have h_neg : HomologicalComplex.homologyMap (-iV_star) 0 = -iV_h0 := by
        simp [iV_h0]
      exact h_neg
    rw [←h_comp]
    exact h
  -- Augmentation maps and their naturality
  let X_UV := TopCat.toSSet.obj ts.UV
  let X_U := TopCat.toSSet.obj ts.U
  let X_V := TopCat.toSSet.obj ts.V
  let ε_UV : H0_UV ⟶ R := X_UV.homology₀ε R
  let ε_U : H0_U ⟶ R := X_U.homology₀ε R
  let ε_V : H0_V ⟶ R := X_V.homology₀ε R
  have h_nat_U : iU_h0 ≫ ε_U = ε_UV := by
    let f' := TopCat.toSSet.map ts.iU
    have h_main : SSet.homologyMap f' R 0 ≫ ε_U = ε_UV := SSet.augmentation_naturality (f := f') R
    have h_eq_chain : SSet.chainComplexMap f' R = iU_star := by
      exact Functor.congr_map ((SSet.chainComplexFunctor AddCommGrpCat).obj R) rfl
    have h_eq : SSet.homologyMap f' R 0 = iU_h0 := by
      dsimp only [SSet.homologyMap, iU_h0]
      exact congr_arg (fun (f : _) => HomologicalComplex.homologyMap f 0) h_eq_chain
    rw [←h_eq]
    exact h_main
  have h_nat_V : iV_h0 ≫ ε_V = ε_UV := by
    let f' := TopCat.toSSet.map ts.iV
    have h_main : SSet.homologyMap f' R 0 ≫ ε_V = ε_UV := SSet.augmentation_naturality (f := f') R
    have h_eq_chain : SSet.chainComplexMap f' R = iV_star := by
      exact Functor.congr_map ((SSet.chainComplexFunctor AddCommGrpCat).obj R) rfl
    have h_eq : SSet.homologyMap f' R 0 = iV_h0 := by
      dsimp only [SSet.homologyMap, iV_h0]
      exact congr_arg (fun (f : _) => HomologicalComplex.homologyMap f 0) h_eq_chain
    rw [←h_eq]
    exact h_main
  -- U and V are contractible, hence path-connected, so ε_U and ε_V are isomorphisms
  have h_U_contr : ContractibleSpace ts.U := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    exact contractible_sphereMinusPoint n p
  have h_V_contr : ContractibleSpace ts.V := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    exact contractible_sphereMinusPoint n (antipodal n p)
  letI : ContractibleSpace ts.U := h_U_contr
  letI : ContractibleSpace ts.V := h_V_contr
  have h_U_pc : PathConnectedSpace ts.U := by
    exact ContractibleSpace.instPathConnectedSpace
  have h_V_pc : PathConnectedSpace ts.V := by
    exact ContractibleSpace.instPathConnectedSpace
  have h_U_pi0_sub : Subsingleton (SSet.π₀ X_U) := by
    have h_sub : Subsingleton (ZerothHomotopy ts.U) := by
      have h := pathConnectedSpace_iff_zerothHomotopy.mp h_U_pc
      exact h.2
    let e := singularPiZeroEquivZerothHomotopy ts.U
    haveI : Subsingleton (ZerothHomotopy ts.U) := h_sub
    refine' ⟨fun a b => _⟩
    have h_eq : e a = e b := Subsingleton.elim (e a) (e b)
    exact e.injective h_eq
  have h_V_pi0_sub : Subsingleton (SSet.π₀ X_V) := by
    have h_sub : Subsingleton (ZerothHomotopy ts.V) := by
      have h := pathConnectedSpace_iff_zerothHomotopy.mp h_V_pc
      exact h.2
    let e := singularPiZeroEquivZerothHomotopy ts.V
    haveI : Subsingleton (ZerothHomotopy ts.V) := h_sub
    refine' ⟨fun a b => _⟩
    have h_eq : e a = e b := Subsingleton.elim (e a) (e b)
    exact e.injective h_eq
  have h_U_pi0_nonempty : Nonempty (SSet.π₀ X_U) := by
    have hne : Nonempty (ZerothHomotopy ts.U) := by
      have h := pathConnectedSpace_iff_zerothHomotopy.mp h_U_pc
      exact h.1
    exact Nonempty.map (singularPiZeroEquivZerothHomotopy ts.U).symm hne
  have h_V_pi0_nonempty : Nonempty (SSet.π₀ X_V) := by
    have hne : Nonempty (ZerothHomotopy ts.V) := by
      have h := pathConnectedSpace_iff_zerothHomotopy.mp h_V_pc
      exact h.1
    exact Nonempty.map (singularPiZeroEquivZerothHomotopy ts.V).symm hne
  letI h_U_conn : X_U.IsConnected := by
    rw [SSet.isConnected_iff_nonempty_unique]
    have h_inh : Inhabited (SSet.π₀ X_U) := Classical.inhabited_of_nonempty h_U_pi0_nonempty
    letI : Inhabited (SSet.π₀ X_U) := h_inh
    exact nonempty_unique X_U.π₀
  letI h_V_conn : X_V.IsConnected := by
    rw [SSet.isConnected_iff_nonempty_unique]
    have h_inh : Inhabited (SSet.π₀ X_V) := Classical.inhabited_of_nonempty h_V_pi0_nonempty
    letI : Inhabited (SSet.π₀ X_V) := h_inh
    exact nonempty_unique X_V.π₀
  haveI h_iso_U : IsIso ε_U := SSet.homology₀ε_isIso_of_isConnected (X := X_U) R
  haveI h_iso_V : IsIso ε_V := SSet.homology₀ε_isIso_of_isConnected (X := X_V) R
  -- f0 ≫ π1 ≫ ε_U = ε_UV and f0 ≫ π2 ≫ ε_V = -ε_UV
  have h_eq1 : f0 ≫ π1 ≫ ε_U = ε_UV := by
    have h_step1 : f0 ≫ π1 ≫ ε_U = (f0 ≫ π1) ≫ ε_U := by rw [Category.assoc]
    have h_step2 : (f0 ≫ π1) ≫ ε_U = iU_h0 ≫ ε_U := by
      exact congr_arg (fun (x : H0_UV ⟶ H0_U) => x ≫ ε_U) h_f0_comp1
    rw [h_step1, h_step2]
    exact h_nat_U
  have h_eq2 : f0 ≫ π2 ≫ ε_V = -ε_UV := by
    have h_step1 : f0 ≫ π2 ≫ ε_V = (f0 ≫ π2) ≫ ε_V := by rw [Category.assoc]
    have h_step2 : (f0 ≫ π2) ≫ ε_V = (-iV_h0) ≫ ε_V := by
      exact congr_arg (fun (x : H0_UV ⟶ H0_V) => x ≫ ε_V) h_f0_comp2
    have h_step3 : (-iV_h0) ≫ ε_V = -(iV_h0 ≫ ε_V) := by
      exact neg_comp iV_h0 ε_V
    have h_step4 : -(iV_h0 ≫ ε_V) = -ε_UV := by
      exact congr_arg (fun (x : H0_UV ⟶ R) => -x) h_nat_V
    rw [h_step1, h_step2, h_step3, h_step4]
  -- Biproduct inclusions
  let i1 : H0_U ⟶ S.X₂.homology 0 :=
    HomologicalComplex.homologyMap (biprod.inl : singularChainComplex' AddCommGrpCat R ts.U ⟶ S.X₂) 0
  let i2 : H0_V ⟶ S.X₂.homology 0 :=
    HomologicalComplex.homologyMap (biprod.inr : singularChainComplex' AddCommGrpCat R ts.V ⟶ S.X₂) 0
  have h_i1π1 : i1 ≫ π1 = 𝟙 H0_U := by
    have h : HomologicalComplex.homologyMap (biprod.inl ≫ (biprod.fst : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.U)) 0 = i1 ≫ π1 :=
      HomologicalComplex.homologyMap_comp _ _ _
    have h_comp : (biprod.inl : singularChainComplex' AddCommGrpCat R ts.U ⟶ S.X₂) ≫ (biprod.fst : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.U) = 𝟙 (singularChainComplex' AddCommGrpCat R ts.U) :=
      biprod.inl_fst
    rw [h_comp] at h
    have h_id : HomologicalComplex.homologyMap (𝟙 (singularChainComplex' AddCommGrpCat R ts.U)) 0 = 𝟙 ((singularChainComplex' AddCommGrpCat R ts.U).homology 0) := by
      simp
    rw [h_id] at h
    exact_mod_cast h.symm
  have h_i2π2 : i2 ≫ π2 = 𝟙 H0_V := by
    have h : HomologicalComplex.homologyMap (biprod.inr ≫ (biprod.snd : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.V)) 0 = i2 ≫ π2 :=
      HomologicalComplex.homologyMap_comp _ _ _
    have h_comp : (biprod.inr : singularChainComplex' AddCommGrpCat R ts.V ⟶ S.X₂) ≫ (biprod.snd : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.V) = 𝟙 (singularChainComplex' AddCommGrpCat R ts.V) :=
      biprod.inr_snd
    rw [h_comp] at h
    have h_id : HomologicalComplex.homologyMap (𝟙 (singularChainComplex' AddCommGrpCat R ts.V)) 0 = 𝟙 ((singularChainComplex' AddCommGrpCat R ts.V).homology 0) := by
      simp
    rw [h_id] at h
    exact_mod_cast h.symm
  have h_i1π2 : i1 ≫ π2 = 0 := by
    have h : HomologicalComplex.homologyMap (biprod.inl ≫ (biprod.snd : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.V)) 0 = i1 ≫ π2 :=
      HomologicalComplex.homologyMap_comp _ _ _
    have h_comp : (biprod.inl : singularChainComplex' AddCommGrpCat R ts.U ⟶ S.X₂) ≫ (biprod.snd : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.V) = (0 : singularChainComplex' AddCommGrpCat R ts.U ⟶ singularChainComplex' AddCommGrpCat R ts.V) :=
      biprod.inl_snd
    rw [h_comp] at h
    have h_zero : HomologicalComplex.homologyMap (0 : singularChainComplex' AddCommGrpCat R ts.U ⟶ singularChainComplex' AddCommGrpCat R ts.V) 0 = (0 : (singularChainComplex' AddCommGrpCat R ts.U).homology 0 ⟶ (singularChainComplex' AddCommGrpCat R ts.V).homology 0) := by
      simp
    rw [h_zero] at h
    exact_mod_cast h.symm
  have h_i2π1 : i2 ≫ π1 = 0 := by
    have h : HomologicalComplex.homologyMap (biprod.inr ≫ (biprod.fst : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.U)) 0 = i2 ≫ π1 :=
      HomologicalComplex.homologyMap_comp _ _ _
    have h_comp : (biprod.inr : singularChainComplex' AddCommGrpCat R ts.V ⟶ S.X₂) ≫ (biprod.fst : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.U) = (0 : singularChainComplex' AddCommGrpCat R ts.V ⟶ singularChainComplex' AddCommGrpCat R ts.U) :=
      biprod.inr_fst
    rw [h_comp] at h
    have h_zero : HomologicalComplex.homologyMap (0 : singularChainComplex' AddCommGrpCat R ts.V ⟶ singularChainComplex' AddCommGrpCat R ts.U) 0 = (0 : (singularChainComplex' AddCommGrpCat R ts.V).homology 0 ⟶ (singularChainComplex' AddCommGrpCat R ts.U).homology 0) := by
      simp
    rw [h_zero] at h
    exact_mod_cast h.symm
  have h_total : π1 ≫ i1 + π2 ≫ i2 = 𝟙 (S.X₂.homology 0) := by
    have h_map_add : ∀ (f g : S.X₂ ⟶ S.X₂),
        HomologicalComplex.homologyMap (f + g) 0 =
        HomologicalComplex.homologyMap f 0 + HomologicalComplex.homologyMap g 0 := by
      intro f g
      exact homologyMap_add f g 0
    let f1 : S.X₂ ⟶ S.X₂ := (biprod.fst : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.U) ≫ biprod.inl
    let f2 : S.X₂ ⟶ S.X₂ := (biprod.snd : S.X₂ ⟶ singularChainComplex' AddCommGrpCat R ts.V) ≫ biprod.inr
    have h1 : π1 ≫ i1 = HomologicalComplex.homologyMap f1 0 := by
      rw [HomologicalComplex.homologyMap_comp]
      rfl
    have h2 : π2 ≫ i2 = HomologicalComplex.homologyMap f2 0 := by
      rw [HomologicalComplex.homologyMap_comp]
      rfl
    have h_sum : π1 ≫ i1 + π2 ≫ i2 = HomologicalComplex.homologyMap f1 0 + HomologicalComplex.homologyMap f2 0 := by
      rw [h1, h2]
    have h4 : f1 + f2 = 𝟙 S.X₂ := by exact biprod.total
    have h6 : HomologicalComplex.homologyMap (𝟙 S.X₂) 0 = 𝟙 (S.X₂.homology 0) := by
      simp
    calc
      π1 ≫ i1 + π2 ≫ i2
        = HomologicalComplex.homologyMap f1 0 + HomologicalComplex.homologyMap f2 0 := h_sum
      _ = HomologicalComplex.homologyMap (f1 + f2) 0 := (h_map_add f1 f2).symm
      _ = HomologicalComplex.homologyMap (𝟙 S.X₂) 0 := by rw [h4]
      _ = 𝟙 (S.X₂.homology 0) := h6
  have h_jointly_mono : ∀ {Z : AddCommGrpCat} (h : Z ⟶ S.X₂.homology 0), h ≫ π1 = 0 → h ≫ π2 = 0 → h = 0 := by
    intro Z h h1 h2
    have h_id : h = h ≫ 𝟙 (S.X₂.homology 0) := by exact (Category.comp_id h).symm
    rw [h_id]
    have h_rw : h ≫ 𝟙 (S.X₂.homology 0) = h ≫ (π1 ≫ i1 + π2 ≫ i2) := by rw [h_total]
    rw [h_rw]
    have h_add : h ≫ (π1 ≫ i1 + π2 ≫ i2) = (h ≫ π1) ≫ i1 + (h ≫ π2) ≫ i2 := by
      rw [Preadditive.comp_add]
      simp [Category.assoc]
    rw [h_add]
    have h_goal : (h ≫ π1) ≫ i1 + (h ≫ π2) ≫ i2 = 0 := by
      rw [h1, h2]
      simp
    exact h_goal
  -- Step: kernel f0 ≅ kernel ε_UV
  have h_k0_ε : (kernel.ι f0) ≫ ε_UV = 0 := by
    have h1 : (kernel.ι f0) ≫ f0 = 0 := kernel.condition f0
    have h_step1 : (kernel.ι f0) ≫ ε_UV = (kernel.ι f0) ≫ (f0 ≫ π1 ≫ ε_U) :=
      congr_arg (fun (x : H0_UV ⟶ R) => (kernel.ι f0) ≫ x) h_eq1.symm
    rw [h_step1]
    have h_step2 : (kernel.ι f0) ≫ (f0 ≫ π1 ≫ ε_U) = ((kernel.ι f0) ≫ f0) ≫ π1 ≫ ε_U := by
      rw [←Category.assoc, ←Category.assoc]
    rw [h_step2, h1]
    simp
  let φ : kernel f0 ⟶ kernel ε_UV := kernel.lift ε_UV (kernel.ι f0) h_k0_ε
  have hφ : φ ≫ kernel.ι ε_UV = kernel.ι f0 := kernel.lift_ι ε_UV (kernel.ι f0) h_k0_ε
  have h_f0π1 : f0 ≫ π1 = ε_UV ≫ inv ε_U := by
    have h1 : (f0 ≫ π1) ≫ ε_U = ε_UV := by
      simpa [Category.assoc] using h_eq1
    calc
      f0 ≫ π1
        = (f0 ≫ π1) ≫ 𝟙 H0_U := by exact (Category.comp_id _).symm
      _ = (f0 ≫ π1) ≫ (ε_U ≫ inv ε_U) := by rw [IsIso.hom_inv_id ε_U]
      _ = ((f0 ≫ π1) ≫ ε_U) ≫ inv ε_U := by simp [Category.assoc]
      _ = ε_UV ≫ inv ε_U := by
        have h_goal : ((f0 ≫ π1) ≫ ε_U) ≫ inv ε_U = ε_UV ≫ inv ε_U := by
          exact h1 ▸ rfl
        exact h_goal
  have h_f0π2 : f0 ≫ π2 = (-ε_UV) ≫ inv ε_V := by
    have h1 : (f0 ≫ π2) ≫ ε_V = -ε_UV := by
      simpa [Category.assoc] using h_eq2
    calc
      f0 ≫ π2
        = (f0 ≫ π2) ≫ 𝟙 H0_V := by exact (Category.comp_id _).symm
      _ = (f0 ≫ π2) ≫ (ε_V ≫ inv ε_V) := by rw [IsIso.hom_inv_id ε_V]
      _ = ((f0 ≫ π2) ≫ ε_V) ≫ inv ε_V := by simp [Category.assoc]
      _ = (-ε_UV) ≫ inv ε_V := by
        have h_goal : ((f0 ≫ π2) ≫ ε_V) ≫ inv ε_V = (-ε_UV) ≫ inv ε_V := by
          exact h1 ▸ rfl
        exact h_goal
  have h_kε_f0π1 : (kernel.ι ε_UV) ≫ f0 ≫ π1 = 0 := by
    have h_assoc : (kernel.ι ε_UV) ≫ f0 ≫ π1 = (kernel.ι ε_UV) ≫ (f0 ≫ π1) := by
      simp
    rw [h_assoc]
    have h_rew : (kernel.ι ε_UV) ≫ (f0 ≫ π1) = (kernel.ι ε_UV) ≫ (ε_UV ≫ inv ε_U) :=
      congr_arg (fun x : H0_UV ⟶ H0_U => (kernel.ι ε_UV) ≫ x) h_f0π1
    rw [h_rew]
    have h3 : (kernel.ι ε_UV) ≫ (ε_UV ≫ inv ε_U) = ((kernel.ι ε_UV) ≫ ε_UV) ≫ inv ε_U := by
      rw [Category.assoc]
    rw [h3, kernel.condition ε_UV]
    simp
  have h_kε_f0π2 : (kernel.ι ε_UV) ≫ f0 ≫ π2 = 0 := by
    have h_assoc : (kernel.ι ε_UV) ≫ f0 ≫ π2 = (kernel.ι ε_UV) ≫ (f0 ≫ π2) := by
      simp
    rw [h_assoc]
    have h_rew : (kernel.ι ε_UV) ≫ (f0 ≫ π2) = (kernel.ι ε_UV) ≫ ((-ε_UV) ≫ inv ε_V) :=
      congr_arg (fun x : H0_UV ⟶ H0_V => (kernel.ι ε_UV) ≫ x) h_f0π2
    rw [h_rew]
    have h3 : (kernel.ι ε_UV) ≫ ((-ε_UV) ≫ inv ε_V) = ((kernel.ι ε_UV) ≫ (-ε_UV)) ≫ inv ε_V := by
      rw [Category.assoc]
    rw [h3]
    have h4 : (kernel.ι ε_UV) ≫ (-ε_UV) = -((kernel.ι ε_UV) ≫ ε_UV) := by
      exact Preadditive.comp_neg (kernel.ι ε_UV) ε_UV
    rw [h4, kernel.condition ε_UV]
    simp
  have h_kε_f0 : (kernel.ι ε_UV) ≫ f0 = 0 :=
    h_jointly_mono ((kernel.ι ε_UV) ≫ f0) h_kε_f0π1 h_kε_f0π2
  let ψ : kernel ε_UV ⟶ kernel f0 := kernel.lift f0 (kernel.ι ε_UV) h_kε_f0
  have hψ : ψ ≫ kernel.ι f0 = kernel.ι ε_UV := kernel.lift_ι f0 (kernel.ι ε_UV) h_kε_f0
  have h_φψ : φ ≫ ψ = 𝟙 (kernel f0) := by
    have h1 : (φ ≫ ψ) ≫ kernel.ι f0 = φ ≫ (ψ ≫ kernel.ι f0) := Category.assoc φ ψ (kernel.ι f0)
    have h2 : φ ≫ (ψ ≫ kernel.ι f0) = φ ≫ kernel.ι ε_UV := by
      exact congr_arg (fun (x : kernel ε_UV ⟶ H0_UV) => φ ≫ x) hψ
    have h3 : φ ≫ kernel.ι ε_UV = kernel.ι f0 := hφ
    have h4 : (φ ≫ ψ) ≫ kernel.ι f0 = kernel.ι f0 := Eq.trans h1 (Eq.trans h2 h3)
    have h5 : (φ ≫ ψ) ≫ kernel.ι f0 = 𝟙 (kernel f0) ≫ kernel.ι f0 := by
      rw [h4, Category.id_comp]
    exact (cancel_mono (kernel.ι f0)).mp h5
  have h_ψφ : ψ ≫ φ = 𝟙 (kernel ε_UV) := by
    have h1 : (ψ ≫ φ) ≫ kernel.ι ε_UV = ψ ≫ (φ ≫ kernel.ι ε_UV) := Category.assoc ψ φ (kernel.ι ε_UV)
    have h2 : ψ ≫ (φ ≫ kernel.ι ε_UV) = ψ ≫ kernel.ι f0 := by
      exact congr_arg (fun (x : kernel f0 ⟶ H0_UV) => ψ ≫ x) hφ
    have h3 : ψ ≫ kernel.ι f0 = kernel.ι ε_UV := hψ
    have h4 : (ψ ≫ φ) ≫ kernel.ι ε_UV = kernel.ι ε_UV := Eq.trans h1 (Eq.trans h2 h3)
    have h5 : (ψ ≫ φ) ≫ kernel.ι ε_UV = 𝟙 (kernel ε_UV) ≫ kernel.ι ε_UV := by
      rw [h4, Category.id_comp]
    exact (cancel_mono (kernel.ι ε_UV)).mp h5
  let h_kernels_iso : kernel f0 ≅ kernel ε_UV :=
    { hom := φ, inv := ψ, hom_inv_id := h_φψ, inv_hom_id := h_ψφ }
  -- Step: kernel ε_UV ≅ kernel (X_UV.homology₀ε R) (by rfl)
  let X_UV := TopCat.toSSet.obj ts.UV
  have h_eq_ε : ε_UV = X_UV.homology₀ε R := by rfl
  have h_kern_eq : kernel ε_UV = kernel (X_UV.homology₀ε R) := by
    rfl
  let h_main4 : kernel ε_UV ≅ kernel (X_UV.homology₀ε R) := eqToIso h_kern_eq
  -- Step: Nonempty ts.UV (needed for kernelHomology₀εIsoReducedHomologyZero)
  have h_uv_nonempty : Nonempty ts.UV := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    let e := twicePuncturedSphereHomotopyEquiv n p (by norm_num)
    have h_codom_nonempty : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      refine' ⟨⟨EuclideanSpace.single 0 (1 : ℝ), _⟩⟩
      have h : dist (EuclideanSpace.single 0 (1 : ℝ)) (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
        rw [dist_zero_right, PiLp.norm_single]
        norm_num
      exact h
    exact Nonempty.map e.invFun h_codom_nonempty
  have h_nonempty_sset : X_UV.Nonempty := by
    have hne : Nonempty ts.UV := h_uv_nonempty
    let x : ts.UV := hne.some
    exact ⟨TopCat.toSSetObj₀Equiv.symm x⟩
  letI : X_UV.Nonempty := h_nonempty_sset
  -- Step: kernel (X_UV.homology₀ε R) ≅ X_UV.reducedHomology R 0
  let h_kernel_reduced : kernel (X_UV.homology₀ε R) ≅ X_UV.reducedHomology R 0 :=
    SSet.kernelHomology₀εIsoReducedHomologyZero R
  -- Step: H₁(small) ≅ kernel f0 already (h_boundary_iso)
  -- Step: singular H₁ ≅ H₁(small) (h_small_iso.symm)
  let h_h1_iso : singularHomology' AddCommGrpCat R 1 ts.X ≅ S.X₃.homology 1 :=
    h_small_iso.symm
  -- Now we need: kernel (X_UV.homology₀ε R) ≅ R
  -- We use the fact that ts.UV has two path components (via homotopy equivalence to S⁰)
  let S0 := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
  have h_s0_nonempty : Nonempty S0 := by
    refine' ⟨⟨EuclideanSpace.single 0 (1 : ℝ), _⟩⟩
    have h : dist (EuclideanSpace.single 0 (1 : ℝ)) (0 : EuclideanSpace ℝ (Fin 1)) = 1 := by
      rw [dist_zero_right, PiLp.norm_single]
      norm_num
    exact h
  -- Homotopy equivalence ts.UV ≃ₕ S0
  let e_uv : {x : SphereType n // x ∈ sphereMinusTwoPoints n p} ≃ₜ ts.UV := by
    dsimp only [ts, TwoSubspaces.twoSubspacesOfOpens]
    refine' {
      toFun := fun x => ⟨x.val, by
        have h : x.val ∈ U_set n p ∩ V_set n p := by
          exact x.property
        exact h⟩,
      invFun := fun y => ⟨y.val, by
        have h : y.val ∈ U_set n p ∩ V_set n p := y.property
        exact h⟩,
      left_inv := by intro x; ext; rfl,
      right_inv := by intro y; ext; rfl,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop
    }
  let e_homotopy : ContinuousMap.HomotopyEquiv ts.UV S0 :=
    (e_uv.symm.toHomotopyEquiv).trans (twicePuncturedSphereHomotopyEquiv n p (by norm_num))
  -- ZerothHomotopy S0 ≃ Bool
  let e_z0_bool_S0 : ZerothHomotopy S0 ≃ Bool := Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.sphereZeroZerothHomotopyEquivBool
  -- Transfer via homotopy equivalence: ZerothHomotopy ts.UV ≃ Bool
  let e_z0_uv : ZerothHomotopy ts.UV ≃ ZerothHomotopy S0 :=
    zerothHomotopyEquivOfHomotopyEquiv e_homotopy
  let e_z0_bool_uv : ZerothHomotopy ts.UV ≃ Bool :=
    e_z0_uv.trans e_z0_bool_S0
  -- SSet.π₀ X_UV ≃ Bool
  let e_pi0_bool_uv : SSet.π₀ X_UV ≃ Bool :=
    (singularPiZeroEquivZerothHomotopy ts.UV).trans e_z0_bool_uv
  -- Now compute kernel (X_UV.homology₀ε R) ≅ R directly
  let ε_UV' := X_UV.homology₀ε R
  let h0_iso_UV : X_UV.homology R 0 ≅ ∐ (fun (_ : SSet.π₀ X_UV) ↦ R) :=
    X_UV.homology₀Iso R
  let g'_UV : (∐ (fun (_ : SSet.π₀ X_UV) ↦ R)) ⟶ R :=
    Sigma.desc (fun (_ : SSet.π₀ X_UV) ↦ 𝟙 R)
  have h1_UV : ε_UV' = h0_iso_UV.hom ≫ g'_UV := by rfl
  -- Reindex the coproduct
  let e_coprod_uv : (∐ (fun (_ : SSet.π₀ X_UV) ↦ R)) ≅ (∐ (fun (_ : Bool) ↦ R)) :=
    Sigma.reindex e_pi0_bool_uv (fun (_ : Bool) ↦ R)
  -- Isomorphism between ∐ over Bool and binary biproduct
  let F_bool : Bool → AddCommGrpCat := fun (_ : Bool) => R
  let e_sigma_biprod : (∐ F_bool) ≅ R ⊞ R := Vendored.CategoryTheory.Limits.sigmaBoolIsoBiprod R
  let g_bool : (∐ F_bool) ⟶ R := Sigma.desc (fun (_ : Bool) => 𝟙 R)
  -- The g'_UV corresponds to g_bool via reindexing
  have h_desc_compat1 : g'_UV = e_coprod_uv.hom ≫ g_bool := by
    apply Sigma.hom_ext
    intro i
    have h : Sigma.ι (fun (_ : SSet.π₀ X_UV) ↦ R) i ≫ g'_UV = 𝟙 R := by
      simpa [g'_UV] using Sigma.ι_desc (fun (_ : SSet.π₀ X_UV) ↦ 𝟙 R) i
    have h2 : Sigma.ι (fun (_ : SSet.π₀ X_UV) ↦ R) i ≫ (e_coprod_uv.hom ≫ g_bool) = 𝟙 R := by
      have h_reindex : Sigma.ι (fun (_ : SSet.π₀ X_UV) ↦ R) i ≫ e_coprod_uv.hom =
          Sigma.ι (fun (_ : Bool) ↦ R) (e_pi0_bool_uv i) := by
        exact Sigma.ι_reindex_hom e_pi0_bool_uv (fun (_ : Bool) ↦ R) i
      calc
        Sigma.ι (fun (_ : SSet.π₀ X_UV) ↦ R) i ≫ (e_coprod_uv.hom ≫ g_bool)
          = (Sigma.ι (fun (_ : SSet.π₀ X_UV) ↦ R) i ≫ e_coprod_uv.hom) ≫ g_bool := by rw [Category.assoc]
        _ = Sigma.ι (fun (_ : Bool) ↦ R) (e_pi0_bool_uv i) ≫ g_bool := by rw [h_reindex]
        _ = 𝟙 R := by
          simpa [g_bool] using Sigma.ι_desc (fun (_ : Bool) ↦ 𝟙 R) (e_pi0_bool_uv i)
    rw [h, h2]
  -- g_bool corresponds to biprod.desc (𝟙 R) (𝟙 R) via e_sigma_biprod
  have h_desc_compat2 : g_bool = e_sigma_biprod.hom ≫ biprod.desc (𝟙 R) (𝟙 R) := by
    apply Sigma.hom_ext
    intro i
    fin_cases i
    · -- case true
      have h1 : Sigma.ι F_bool true ≫ g_bool = 𝟙 R := by
        simpa [g_bool] using Sigma.ι_desc (fun (_ : Bool) ↦ 𝟙 R) true
      have h2 : Sigma.ι F_bool true ≫ (e_sigma_biprod.hom ≫ biprod.desc (𝟙 R) (𝟙 R)) = 𝟙 R := by
        calc
          Sigma.ι F_bool true ≫ (e_sigma_biprod.hom ≫ biprod.desc (𝟙 R) (𝟙 R))
            = (Sigma.ι F_bool true ≫ e_sigma_biprod.hom) ≫ biprod.desc (𝟙 R) (𝟙 R) := by rw [Category.assoc]
          _ = biprod.inl ≫ biprod.desc (𝟙 R) (𝟙 R) := by
            have h : Sigma.ι F_bool true ≫ e_sigma_biprod.hom = biprod.inl :=
              Vendored.CategoryTheory.Limits.sigmaBoolIsoBiprod_ι_true R
            rw [h]
          _ = 𝟙 R := biprod.inl_desc _ _
      rw [h1, h2]
    · -- case false
      have h1 : Sigma.ι F_bool false ≫ g_bool = 𝟙 R := by
        simpa [g_bool] using Sigma.ι_desc (fun (_ : Bool) ↦ 𝟙 R) false
      have h2 : Sigma.ι F_bool false ≫ (e_sigma_biprod.hom ≫ biprod.desc (𝟙 R) (𝟙 R)) = 𝟙 R := by
        calc
          Sigma.ι F_bool false ≫ (e_sigma_biprod.hom ≫ biprod.desc (𝟙 R) (𝟙 R))
            = (Sigma.ι F_bool false ≫ e_sigma_biprod.hom) ≫ biprod.desc (𝟙 R) (𝟙 R) := by rw [Category.assoc]
          _ = biprod.inr ≫ biprod.desc (𝟙 R) (𝟙 R) := by
            have h : Sigma.ι F_bool false ≫ e_sigma_biprod.hom = biprod.inr :=
              Vendored.CategoryTheory.Limits.sigmaBoolIsoBiprod_ι_false R
            rw [h]
          _ = 𝟙 R := biprod.inr_desc _ _
      rw [h1, h2]
  -- Hence ε_UV' corresponds to biprod.desc (𝟙 R) (𝟙 R)
  let e_total_uv : X_UV.homology R 0 ≅ R ⊞ R :=
    h0_iso_UV ≪≫ e_coprod_uv ≪≫ e_sigma_biprod
  have h_ε_compat_uv : ε_UV' = e_total_uv.hom ≫ biprod.desc (𝟙 R) (𝟙 R) := by
    rw [h1_UV, h_desc_compat1, h_desc_compat2]
    simp [e_total_uv, Iso.trans, Category.assoc]
  -- kernel ε_UV' ≅ kernel (biprod.desc (𝟙 R) (𝟙 R))
  let h_kern_biprod_uv : kernel ε_UV' ≅ kernel (biprod.desc (𝟙 R) (𝟙 R)) :=
    CategoryTheory.Limits.KernelIsoOfCompatibleIso.kernelIsoOfCompatibleIso e_total_uv
      ε_UV' (biprod.desc (𝟙 R) (𝟙 R)) h_ε_compat_uv.symm
  -- kernel (biprod.desc (𝟙 R) (𝟙 R)) ≅ R
  let k_fold : R ⟶ R ⊞ R := biprod.inl - biprod.inr
  let hk_fold : k_fold ≫ biprod.desc (𝟙 R) (𝟙 R) = 0 := by
    simp [k_fold, biprod.inl_desc, biprod.inr_desc]
  let h_isLimit_fold : IsLimit (KernelFork.ofι k_fold hk_fold) :=
    isLimit_kernelFold_desc_id_id (C := AddCommGrpCat) (R := R)
  let h_kern_fold_iso : kernel (biprod.desc (𝟙 R) (𝟙 R)) ≅ R := by
    exact h_isLimit_fold.conePointUniqueUpToIso (limit.isLimit _) |>.symm
  -- Final: kernel (X_UV.homology₀ε R) ≅ R
  let h_kern_uv_iso : kernel ε_UV' ≅ R := h_kern_biprod_uv ≪≫ h_kern_fold_iso
  -- Now compose all isomorphisms
  let h_final1 : singularHomology' AddCommGrpCat R 1 ts.X ≅ S.X₃.homology 1 :=
    h_small_iso.symm
  let h_final2 : S.X₃.homology 1 ≅ kernel f0 := h_boundary_iso
  let h_final3 : kernel f0 ≅ kernel ε_UV := h_kernels_iso
  let h_final4 : kernel ε_UV ≅ kernel (X_UV.homology₀ε R) := h_main4
  let h_final5 : kernel (X_UV.homology₀ε R) ≅ R := h_kern_uv_iso
  exact h_final1 ≪≫ h_final2 ≪≫ h_final3 ≪≫ h_final4 ≪≫ h_final5

end Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace

end

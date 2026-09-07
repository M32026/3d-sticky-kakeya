/-
# RP^n Homology Vanishing Above Dimension n

Proves H_k(RP^n; Z/2) = 0 for k > n by Mayer-Vietoris induction.

## Proof

Base case n=0: RP^0 is a single point, so H_k(RP^0) = 0 for k > 0.

Inductive step: Assume H_k(RP^m) = 0 for k > m. Cover RP^{m+1} by:
- U ≅ R^{m+1} (contractible): H_k(U) = 0 for k > 0
- V ≃ RP^m: H_k(V) = 0 for k > m by induction
- U∩V ≃ S^m: H_k(U∩V) = 0 for k > m

For k > m+1, the MV boundary isomorphism gives:
H_k(RP^{m+1}) ≅ H_{k-1}(U∩V) ≅ H_{k-1}(S^m) = 0
since k-1 > m.

## Whiteprint Node
- rp_homology_vanishing
-/

import MyLeanRepo.Kakeya.BorsukUlam.RealProjective.Cover
import MyLeanRepo.Kakeya.BorsukUlam.RealProjective.VDeformation
import MyLeanRepo.Kakeya.BorsukUlam.SmallChainBockstein
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.SphereHomologyZ2VanishingAbove
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.PuncturedSpace
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.HomologyOfPoint
import Mathlib.Algebra.Homology.HomologySequence

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open BorsukUlam.RealProjective
open BorsukUlam.RealProjective.Cover

open AlgebraicTopology.StdSphereHomology
open Topology.EuclideanSpace
open BorsukUlam.SmallChainBockstein

variable {m : ℕ}

namespace BorsukUlam.RPHomologyVanishing

local notation "R2" => BorsukUlam.BackupRoute.R2

/-- The UV subtype from twoSubspacesOfOpens is homeomorphic to UInterVType. -/
noncomputable def uvEquiv (m : ℕ) :
    {x : EmbeddedRP m // x ∈ U m ∩ V m} ≃ₜ UInterVType m := by
  refine' {
    toFun := fun x => ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩,
    invFun := fun y => ⟨y.val.val, y.val.prop, y.prop⟩,
    left_inv := by intro x; ext; rfl,
    right_inv := by intro y; ext; rfl,
    continuous_toFun := by fun_prop,
    continuous_invFun := by fun_prop
  }

/-- Homology of U vanishes in positive degrees since U ≅ R^m is contractible. -/
lemma hU_vanishing (m : ℕ) (i : ℕ) (hi_pos : 0 < i) :
    IsZero (singularHomology' AddCommGrpCat R2 i
      (TwoSubspaces.twoSubspacesOfOpens (U m) (V m)).U) := by
  let h : UType m ≃ₜ EuclideanSpace ℝ (Fin m) := uHomeo (n := m)
  letI : ContractibleSpace (EuclideanSpace ℝ (Fin m)) :=
    RealTopologicalVectorSpace.contractibleSpace
  letI : ContractibleSpace (UType m) := h.contractibleSpace
  exact isZero_singularHomologyOfContractible AddCommGrpCat i R2
    (X := UType m) (ne_of_gt hi_pos)

/-- Homology of U∩V for RP^{n+1} is isomorphic to homology of S^n. -/
noncomputable def hUV_iso (n : ℕ) (i : ℕ) :
    singularHomology' AddCommGrpCat R2 i
      (TwoSubspaces.twoSubspacesOfOpens (U (n + 1)) (V (n + 1))).UV ≅
    singularHomology' AddCommGrpCat R2 i (TopCat.of (SphereType n)) := by
  let e1 : {x : EmbeddedRP (n + 1) // x ∈ U (n + 1) ∩ V (n + 1)} ≃ₜ
      UInterVType (n + 1) := uvEquiv (n + 1)
  let e2 : UInterVType (n + 1) ≃ₜ RnMinus0 (n + 1) := uInterVHomeo (n := n + 1)
  letI : Nonempty (Fin (n + 1)) := Fin.pos_iff_nonempty.mp (by omega)
  let e3 : ContinuousMap.HomotopyEquiv (PuncturedSpace (n + 1)) (UnitSphere (n + 1)) :=
    puncturedSphereHomotopyEquiv (m := n + 1)
  let e_homeo : {x : EmbeddedRP (n + 1) // x ∈ U (n + 1) ∩ V (n + 1)} ≃ₜ
      PuncturedSpace (n + 1) := e1.trans e2
  let e_h1 : ContinuousMap.HomotopyEquiv
      (TwoSubspaces.twoSubspacesOfOpens (U (n + 1)) (V (n + 1))).UV
      (PuncturedSpace (n + 1)) := e_homeo.toHomotopyEquiv
  let e_homotopy : ContinuousMap.HomotopyEquiv
      (TwoSubspaces.twoSubspacesOfOpens (U (n + 1)) (V (n + 1))).UV
      (SphereType n) := e_h1.trans e3
  exact singularHomologyIsoOfHomotopyEquiv AddCommGrpCat i R2
    (TwoSubspaces.twoSubspacesOfOpens (U (n + 1)) (V (n + 1))).UV
    (TopCat.of (SphereType n))
    e_homotopy

/-- Homology of U∩V for RP^{m+1} vanishes above dimension m. -/
lemma hUV_vanishing_succ (m : ℕ) (i : ℕ) (hi : m < i) :
    IsZero (singularHomology' AddCommGrpCat R2 i
      (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).UV) := by
  have h_iso : singularHomology' AddCommGrpCat R2 i
      (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).UV ≅
      singularHomology' AddCommGrpCat R2 i (TopCat.of (SphereType m)) :=
    hUV_iso m i
  have h_sphere : IsZero (singularHomology' AddCommGrpCat R2 i (TopCat.of (SphereType m))) :=
    BorsukUlam.BackupRoute.stdSphereVanishingAboveZ2 m i hi
  exact IsZero.of_iso h_sphere h_iso

/-- Homology of V vanishes above dimension m (using induction and V ≃ RP^m). -/
lemma hV_vanishing (m : ℕ) (i : ℕ) (hi : m < i)
    (h_ind : ∀ (k : ℕ), m < k →
      IsZero (singularHomology' AddCommGrpCat R2 k (TopCat.of (EmbeddedRP m)))) :
    IsZero (singularHomology' AddCommGrpCat R2 i
      (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).V) := by
  let e_homotopy : ContinuousMap.HomotopyEquiv
      (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).V
      (EmbeddedRP m) := vHomotopyEquiv m
  let h_iso : singularHomology' AddCommGrpCat R2 i
      (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).V ≅
      singularHomology' AddCommGrpCat R2 i (TopCat.of (EmbeddedRP m)) :=
    singularHomologyIsoOfHomotopyEquiv AddCommGrpCat i R2
      (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).V
      (TopCat.of (EmbeddedRP m))
      e_homotopy
  have h_ind' : IsZero (singularHomology' AddCommGrpCat R2 i (TopCat.of (EmbeddedRP m))) :=
    h_ind i hi
  exact IsZero.of_iso h_ind' h_iso

/-- H_k(RP^n; Z/2) = 0 for k > n. -/
theorem rpHomologyVanishing (n : ℕ) : ∀ (k : ℕ), n < k →
    IsZero (singularHomology' AddCommGrpCat R2 k (TopCat.of (EmbeddedRP n))) := by
  induction n with
  | zero =>
    intro k hk
    -- Base case: EmbeddedRP 0 is a single point (erp0 0)
    have h_pos : 0 < k := by linarith
    have h_all_eq : ∀ (z : EmbeddedRP 0), z = erp0 0 := by
      intro z
      have h_coord : z.val (0, 0) = 1 := by
        obtain ⟨x, hx⟩ := z.property
        let y : SphereType 0 := Quotient.out x
        have h_eq1 : BorsukUlam.BackupRoute.quotientMap 0 y = x :=
          Quotient.out_eq x
        have h_eq2 : veroneseMap x = veroneseFun y := by
          have h3 : veroneseMap (BorsukUlam.BackupRoute.quotientMap 0 y) =
              veroneseFun y := by
            simp [veroneseMap, Quotient.lift_mk] <;> rfl
          rw [←h_eq1] <;> exact h3
        have h_main : z.val (0, 0) = (veroneseFun y) (0, 0) := by
          rw [←hx, h_eq2]
        rw [h_main, veroneseFun_apply y 0 0]
        have h5 : ‖y.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
        have h6 : ‖y.val‖ ^ 2 = (y.val 0) ^ 2 := by
          have h7 : ‖y.val‖ ^ 2 = ∑ j : Fin 1, (y.val j) ^ 2 :=
            EuclideanSpace.real_norm_sq_eq y.val
          rw [h7, Fin.sum_univ_one] <;> ring
        have h8 : (y.val 0) ^ 2 = 1 := by
          have h9 : ‖y.val‖ ^ 2 = 1 := by
            rw [h5] <;> norm_num
          rw [h6] at h9
          exact h9
        have h10 : y.val 0 * y.val 0 = (y.val 0) ^ 2 := by ring
        rw [h10, h8]
      exact (coord00_eq_one_iff_erp0 z).mp h_coord
    letI : Subsingleton (EmbeddedRP 0) :=
      ⟨fun a b => by
        have ha : a = erp0 0 := h_all_eq a
        have hb : b = erp0 0 := h_all_eq b
        rw [ha, hb]⟩
    letI : Nonempty (EmbeddedRP 0) := ⟨erp0 0⟩
    exact isZero_singularHomologyOfContractible AddCommGrpCat k R2
      (X := EmbeddedRP 0) (ne_of_gt h_pos)
  | succ m ih =>
    intro k h
    -- Inductive step: MV on RP^{m+1}
    have h_k_gt_m1 : m + 1 < k := h
    have h_k_gt_m : m < k := by linarith
    set nMV := k - 1 with hnMV_def
    have h_nMV_gt_m : m < nMV := by omega
    have h_nMV_pos : 0 < nMV := by omega
    have h_k_pos : 0 < k := by linarith

    have h_k_eq : k = nMV + 1 := by
      simp [hnMV_def] <;> omega

    -- Apply MV boundary isomorphism
    have h_mv : singularHomology' AddCommGrpCat R2 (nMV + 1) (TopCat.of (EmbeddedRP (m + 1))) ≅
        singularHomology' AddCommGrpCat R2 nMV
          (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).UV :=
      mayerVietoris_boundaryIso_openCover_z2
        (U (m + 1)) (V (m + 1))
        (U_open (m + 1)) (V_open (m + 1))
        (cover (m + 1) (by linarith))
        nMV
        (hU_vanishing (m + 1) nMV h_nMV_pos)
        (hV_vanishing m nMV h_nMV_gt_m ih)
        (hU_vanishing (m + 1) (nMV + 1) (by omega))
        (hV_vanishing m (nMV + 1) (by omega) ih)

    -- H_{k-1}(U∩V) = 0 since k-1 > m
    have h_uv : IsZero (singularHomology' AddCommGrpCat R2 nMV
        (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).UV) :=
      hUV_vanishing_succ m nMV h_nMV_gt_m

    rw [h_k_eq]
    exact IsZero.of_iso h_uv h_mv

end BorsukUlam.RPHomologyVanishing

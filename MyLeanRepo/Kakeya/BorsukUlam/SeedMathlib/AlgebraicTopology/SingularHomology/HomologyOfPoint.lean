/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.ReducedHomology

@[expose] public section

/-!
# Homology of a Point and Contractible Spaces

Computation of singular homology of a point and contractible spaces.

## Main results

- `singularHomologyPointZero`: `H₀({*}) ≅ R`
- `isZero_singularHomologyPoint`: `Hₙ({*}) = 0` for `n > 0`
- `singularHomologyIsoOfHomotopyEquiv`: a homotopy equivalence induces an isomorphism on homology
- `isZero_singularHomologyOfContractible`: `Hₙ(X) = 0` for `n > 0` when `X` is contractible
- `singularHomologyZeroOfContractible`: `H₀(X) ≅ R` when `X` is contractible
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex

universe w v u

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable (n : ℕ) (R : C)
variable [CategoryWithHomology C]

/-- The 0-th singular homology of a one-point space is isomorphic to `R`.

    `H₀({*}) ≅ R` because a point has exactly one path component,
    and `H₀` is the free `R`-module on path components. -/
noncomputable def singularHomologyPointZero :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of PUnit) ≅ R := by
  letI : TotallyDisconnectedSpace (TopCat.of PUnit) :=
    TotallySeparatedSpace.totallyDisconnectedSpace (α := (TopCat.of PUnit))
  let h₁ : ((singularHomologyFunctor C 0).obj R).obj (TopCat.of PUnit) ≅
      ∐ fun (_ : (TopCat.of PUnit)) ↦ R :=
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace C R (TopCat.of PUnit)
  exact h₁ ≪≫ by
    refine' {
      hom := Sigma.desc (fun (_ : (TopCat.of PUnit)) ↦ 𝟙 R),
      inv := Sigma.ι (fun (_ : (TopCat.of PUnit)) ↦ R) PUnit.unit,
      hom_inv_id := _,
      inv_hom_id := _
    }
    · apply Sigma.hom_ext
      intro j
      have h_j : j = PUnit.unit := by exact Subsingleton.elim j PUnit.unit
      rw [h_j]
      have h1 : (Sigma.ι (fun (_ : (TopCat.of PUnit)) ↦ R) PUnit.unit ≫
          Sigma.desc (fun (_ : (TopCat.of PUnit)) ↦ 𝟙 R)) = 𝟙 R :=
        Sigma.ι_desc (fun (_ : (TopCat.of PUnit)) ↦ 𝟙 R) PUnit.unit
      simpa [CategoryTheory.Category.assoc, h1] using
        show (Sigma.ι (fun (_ : (TopCat.of PUnit)) ↦ R) PUnit.unit ≫
            Sigma.desc (fun (_ : (TopCat.of PUnit)) ↦ 𝟙 R)) ≫
            Sigma.ι (fun (_ : (TopCat.of PUnit)) ↦ R) PUnit.unit =
          Sigma.ι (fun (_ : (TopCat.of PUnit)) ↦ R) PUnit.unit from by
        rw [h1] ; simp
    · simp [Sigma.ι_desc]

/-- For `n > 0`, the singular homology of a point is zero.

    This follows from the fact that a point is totally disconnected,
    and for totally disconnected spaces `Hₙ = 0` for all `n ≠ 0`. -/
lemma isZero_singularHomologyPoint (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)) := by
  letI : TotallyDisconnectedSpace (TopCat.of PUnit) :=
    TotallySeparatedSpace.totallyDisconnectedSpace (α := (TopCat.of PUnit))
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R (TopCat.of PUnit) hn

section HomotopyInvariance

variable {X Y : TopCat.{w}} {f g : X ⟶ Y}

/-- If two maps are homotopic, they induce the same map on singular homology. -/
lemma congr_singularHomologyMap (H : TopCat.Homotopy f g) :
    ((singularHomologyFunctor C n).obj R).map f =
    ((singularHomologyFunctor C n).obj R).map g :=
  H.congr_homologyMap_singularChainComplexFunctor R n

/-- If two maps are homotopic (`Prop` version), they induce the same map on singular homology. -/
lemma congr_singularHomologyMap' (h : ContinuousMap.Homotopic f.hom g.hom) :
    ((singularHomologyFunctor C n).obj R).map f =
    ((singularHomologyFunctor C n).obj R).map g := by
  rcases h with ⟨H⟩
  exact congr_singularHomologyMap C n R H

variable (X Y : TopCat.{w})

/-- A homotopy equivalence between two topological spaces induces an isomorphism
on singular homology in any degree. -/
noncomputable def singularHomologyIsoOfHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) :
    ((singularHomologyFunctor C n).obj R).obj X ≅
    ((singularHomologyFunctor C n).obj R).obj Y := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : ((singularHomologyFunctor C n).obj R).map f ≫
      ((singularHomologyFunctor C n).obj R).map g = 𝟙 _ := by
    have h : ((singularHomologyFunctor C n).obj R).map (f ≫ g) =
        ((singularHomologyFunctor C n).obj R).map (𝟙 X) :=
      congr_singularHomologyMap' C n R e.left_inv
    have h_comp : ((singularHomologyFunctor C n).obj R).map (f ≫ g) =
        ((singularHomologyFunctor C n).obj R).map f ≫
        ((singularHomologyFunctor C n).obj R).map g :=
      ((singularHomologyFunctor C n).obj R).map_comp f g
    have h_id : ((singularHomologyFunctor C n).obj R).map (𝟙 X) = 𝟙 _ :=
      ((singularHomologyFunctor C n).obj R).map_id X
    rw [h_comp] at h
    rw [h_id] at h
    exact h
  have h2 : ((singularHomologyFunctor C n).obj R).map g ≫
      ((singularHomologyFunctor C n).obj R).map f = 𝟙 _ := by
    have h : ((singularHomologyFunctor C n).obj R).map (g ≫ f) =
        ((singularHomologyFunctor C n).obj R).map (𝟙 Y) :=
      congr_singularHomologyMap' C n R e.right_inv
    have h_comp : ((singularHomologyFunctor C n).obj R).map (g ≫ f) =
        ((singularHomologyFunctor C n).obj R).map g ≫
        ((singularHomologyFunctor C n).obj R).map f :=
      ((singularHomologyFunctor C n).obj R).map_comp g f
    have h_id : ((singularHomologyFunctor C n).obj R).map (𝟙 Y) = 𝟙 _ :=
      ((singularHomologyFunctor C n).obj R).map_id Y
    rw [h_comp] at h
    rw [h_id] at h
    exact h
  exact {
    hom := ((singularHomologyFunctor C n).obj R).map f
    inv := ((singularHomologyFunctor C n).obj R).map g
    hom_inv_id := h1
    inv_hom_id := h2
  }

end HomotopyInvariance

section Contractible

variable {X : Type w} [TopologicalSpace X] [ContractibleSpace X]

/-- Any contractible space `X` is homotopy equivalent to `PUnit`. -/
noncomputable def contractibleHomotopyEquivPUnit :
    ContinuousMap.HomotopyEquiv X PUnit := by
  classical
  have h : Nonempty (ContinuousMap.HomotopyEquiv X PUnit) :=
    ContractibleSpace.hequiv X PUnit
  exact Classical.choice h

/-- If `X` is contractible, then its singular homology is isomorphic to that of a point. -/
noncomputable def singularHomologyIsoOfContractible :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit) :=
  singularHomologyIsoOfHomotopyEquiv C n R (TopCat.of X) (TopCat.of PUnit)
    (contractibleHomotopyEquivPUnit (X := X))

/-- If `X` is contractible and `n > 0`, then `Hₙ(X) = 0`. -/
lemma isZero_singularHomologyOfContractible (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of X)) := by
  have hIso := singularHomologyIsoOfContractible C n R (X := X)
  exact IsZero.of_iso (isZero_singularHomologyPoint C n R hn) hIso

/-- If `X` is contractible, then `H₀(X) ≅ R`. -/
noncomputable def singularHomologyZeroOfContractible :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of X) ≅ R :=
  singularHomologyIsoOfContractible C 0 R (X := X) ≪≫ singularHomologyPointZero C R

end Contractible

section ReducedHomologyPoint

/-- Reduced homology of a point is zero in degrees ≥ 1. -/
lemma isZero_reducedHomologyPoint_succ :
    IsZero (reducedSingularHomology C (n + 1) R (TopCat.of PUnit)) := by
  have h : SSet.reducedHomology (TopCat.toSSet.obj (TopCat.of PUnit)) R (n + 1) ≅
      (TopCat.toSSet.obj (TopCat.of PUnit)).homology R (n + 1) :=
    SSet.reducedHomologySuccIso (TopCat.toSSet.obj (TopCat.of PUnit)) R n
  have h' : IsZero ((TopCat.toSSet.obj (TopCat.of PUnit)).homology R (n + 1)) :=
    isZero_singularHomologyPoint C (n + 1) R (by simp)
  exact IsZero.of_iso h' h

/-- Reduced homology of a point is zero in degree 0. -/
lemma isZero_reducedHomologyPoint_zero :
    IsZero (reducedSingularHomology C 0 R (TopCat.of PUnit)) :=
  isZero_reducedSingularHomologyZero_of_pathConnected (C := C) (R := R)

end ReducedHomologyPoint

end AlgebraicTopology

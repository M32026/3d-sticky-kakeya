/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.HomologyOfPoint
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.Topology.EuclideanSpace.PuncturedSpace

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits ContinuousMap Topology.EuclideanSpace

universe w v u

namespace AlgebraicTopology

variable {m : ℕ} [Nonempty (Fin m)]
variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C) (n : ℕ)

/-- The singular homology of punctured Euclidean space is isomorphic to that of the unit
sphere. -/
noncomputable def puncturedSpaceHomologyIsoSphere :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of (ULift (PuncturedSpace m))) ≅
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of (ULift (UnitSphere m))) := by
  let e1 : ContinuousMap.HomotopyEquiv (ULift (PuncturedSpace m)) (PuncturedSpace m) :=
    (Homeomorph.ulift : ULift (PuncturedSpace m) ≃ₜ PuncturedSpace m).toHomotopyEquiv
  let e2 : ContinuousMap.HomotopyEquiv (PuncturedSpace m) (UnitSphere m) :=
    puncturedSphereHomotopyEquiv
  let e3 : ContinuousMap.HomotopyEquiv (UnitSphere m) (ULift (UnitSphere m)) :=
    (Homeomorph.ulift.symm : UnitSphere m ≃ₜ ULift (UnitSphere m)).toHomotopyEquiv
  let e : ContinuousMap.HomotopyEquiv (ULift (PuncturedSpace m)) (ULift (UnitSphere m)) :=
    e1.trans e2 |>.trans e3
  exact singularHomologyIsoOfHomotopyEquiv C n R
    (TopCat.of (ULift (PuncturedSpace m)))
    (TopCat.of (ULift (UnitSphere m)))
    e

end AlgebraicTopology

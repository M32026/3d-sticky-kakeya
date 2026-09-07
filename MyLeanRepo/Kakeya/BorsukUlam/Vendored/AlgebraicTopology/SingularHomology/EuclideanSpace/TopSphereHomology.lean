module

public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.H1SphereOne
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology

@[expose] public section

/-!
# Top Homology of Euclidean Spheres

This file computes the top singular homology of the standard Euclidean sphere
with integer coefficients.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Metric Simplicial
open TopCat (toSSet)

namespace Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace

open AlgebraicTopology.StdSphereHomology

/-- The top singular homology of the standard `n`-sphere is isomorphic to `ℤ`, for `n ≥ 1`. -/
noncomputable def topSphereHomologyIsoInt (n : ℕ) (hn : 1 ≤ n) :
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) n
      (TopCat.of (SphereType n)) ≅ AddCommGrpCat.of ℤ := by
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    by_cases h_n0 : n = 0
    · subst h_n0
      exact h1SphereOneIsoInt
    · have hn1 : 1 ≤ n := by
        omega
      let p : SphereType (n + 1) := Classical.arbitrary _
      have h_iso :
          singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (n + 1)
              (TopCat.of (SphereType (n + 1))) ≅
            singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) n
              (TopCat.of (SphereType n)) :=
        sphere_homology_shift n p n hn1
      exact h_iso ≪≫ ih hn1

end Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace

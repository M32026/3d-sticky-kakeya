module

public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.Algebra.Homology.ShortExactDeltaIso
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains

@[expose] public section


/-!
# Mayer-Vietoris Boundary Isomorphism

The boundary isomorphism for the Mayer-Vietoris sequence of small chains.

Placed in a separate file with minimal imports to avoid type inference
performance issues that occur in the heavier context of the main
Mayer–Vietoris sequence file.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex

universe w v u

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable [CategoryWithHomology C]
variable (R : C)
variable (ts : TwoSubspaces.{w})

/-- **Boundary isomorphism for the small chain complex (proved version).**

    Given the short exact sequence 0 → C(UV) → C(U)⊕C(V) → C_small → 0,
    if H_{n+1}(C(U)⊕C(V)) = 0 and H_n(C(U)⊕C(V)) = 0, then the connecting
    homomorphism gives an isomorphism H_{n+1}(small) ≅ H_n(UV).

    This follows directly from `shortExact_δIso`. The proof is placed in
    this separate file with minimal type class assumptions to avoid
    performance issues: having both `[Preadditive C]` and `[Abelian C]`
    as separate variables creates a type class diamond that makes
    `whnf` reduction of `mvShortComplex C R ts` extremely slow.
    Using only `[Abelian C]` (which extends `Preadditive`) avoids the diamond. -/
noncomputable def mv_boundaryIso_small_proved (n : ℕ)
    (hS : (mvShortComplex C R ts).ShortExact)
    (h_mid_succ : IsZero ((mvShortComplex C R ts).X₂.homology (n + 1)))
    (h_mid_n : IsZero ((mvShortComplex C R ts).X₂.homology n)) :
    (mvShortComplex C R ts).X₃.homology (n + 1) ≅
    (mvShortComplex C R ts).X₁.homology n := by
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := by
    simp [ComplexShape.down]
  exact Algebra.Homology.shortExact_δIso hS hij h_mid_succ h_mid_n

end AlgebraicTopology

end section

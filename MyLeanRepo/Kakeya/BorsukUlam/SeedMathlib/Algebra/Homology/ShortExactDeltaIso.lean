/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public section

open CategoryTheory Limits HomologicalComplex

universe u v

/-!
# Boundary isomorphism from short exact sequences

Given a short exact sequence of chain complexes `0 → X₁ → X₂ → X₃ → 0`
in an abelian category, if the middle complex `X₂` has trivial homology
in degrees `i` and `j` (with `j + 1 = i`), then the connecting
homomorphism `δ : H_i(X₃) → H_j(X₁)` is an isomorphism.

This is a direct consequence of the long exact sequence in homology
and is extracted into its own file for performance reasons: the
definition is much faster to type-check in a minimal context.
-/

namespace Algebra.Homology

/-- **Boundary isomorphism from a short exact sequence of chain complexes.**

    Given `0 → X₁ → X₂ → X₃ → 0` exact, if `H_i(X₂) = 0` and `H_j(X₂) = 0`
    with `j + 1 = i`, then the connecting homomorphism gives an isomorphism
    `H_i(X₃) ≅ H_j(X₁)`. -/
noncomputable def shortExact_δIso {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (ChainComplex C ℕ)}
    (hS : S.ShortExact) {i j : ℕ} (hij : (ComplexShape.down ℕ).Rel i j)
    (hi : IsZero (S.X₂.homology i))
    (hj : IsZero (S.X₂.homology j)) :
    S.X₃.homology i ≅ S.X₁.homology j :=
  hS.δIso i j hij hi hj

end Algebra.Homology

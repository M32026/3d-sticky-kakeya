module

/-
# Core Definitions for Product-Like Incidence Theorem

This module contains the OS A.7 definitions not already owned by the
discretised Furstenberg base module.

Dyadic infrastructure (`dyadicScales`, `dyadicCube`, `dyadicCubes`,
`dyadicCoveringNumber`, `IsDeltaSCSet`), Appendix duality, and product-like
contract definitions are re-exported through `ProjectionBasic`.

## Definitions

- Half-open unit square and family-level dyadic covering numbers
- Appendix A parameter rectangles
- Compatibility lemmas for the canonical product-like definitions
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section


/--
[def.dyadic_cubes_and_covering_numbers.327] The half-open unit square `[0,1)^2`.
-/
def halfOpenUnitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i : Fin 2, x i ∈ Set.Ico (0 : ℝ) 1}

/--
[def.dyadic_cubes_and_covering_numbers.327] The abbreviation `𝒟_δ` for
`𝒟_δ([0,1)^2)`.
-/
def dyadicUnitSquareCubes (δ : ℝ) : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  dyadicCubesMeeting (d := 2) δ halfOpenUnitSquare

/--
[def.dyadic_cubes_and_covering_numbers.327] For a family `P` of dyadic cubes,
`P_Δ = 𝒟_Δ(⋃₀ P)` is the family of `Δ`-dyadic cubes meeting the union of `P`.
-/
def dyadicFamilyCubesAtScale {d : ℕ} (Δ : ℝ)
    (P : Set (Set (EuclideanSpace ℝ (Fin d)))) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  dyadicCubesMeeting (d := d) Δ (⋃₀ P)

/--
[def.dyadic_cubes_and_covering_numbers.327] For a family `P` of dyadic cubes,
`|P|_Δ = |𝒟_Δ(⋃₀ P)|`, recorded as an extended natural cardinality.
-/
def dyadicFamilyCoveringNumber {d : ℕ} (Δ : ℝ)
    (P : Set (Set (EuclideanSpace ℝ (Fin d)))) : ℕ∞ :=
  (dyadicFamilyCubesAtScale (d := d) Δ P).encard

/--
[def.appendix_duality.2338] The half-open parameter rectangle
`[a, a + δ) × [b, b + δ)`.
-/
def appendixDyadicParameterRectangle (a b δ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Set.Ico a (a + δ) ∧ p 1 ∈ Set.Ico b (b + δ)}

/--
[def.appendix_duality.2338] The tube `D([a, a + δ) × [b, b + δ))` obtained by
applying the Appendix-A duality to a half-open parameter rectangle.
-/
def appendixDyadicTubeFromRectangle (a b δ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  appendixDualOfParameterSet (appendixDyadicParameterRectangle a b δ)

/--
[def.appendix_duality.2338] The slope of the represented dyadic `δ`-tube
`D([a, a + δ) × [b, b + δ))` is the lower-left slope coordinate `a`.
-/
def appendixDyadicTubeSlope (a b δ : ℝ) : ℝ :=
  a

noncomputable section

@[simp] lemma productLikeRealLineCopy_mem (A : Set ℝ)
    (x : EuclideanSpace ℝ (Fin 1)) :
    x ∈ productLikeRealLineCopy A ↔ x 0 ∈ A := by rfl

lemma productLikeRealLineCopy_eq (A : Set ℝ) :
    productLikeRealLineCopy A = realLineCopy A := by
  ext x; simp [productLikeRealLineCopy, realLineCopy]

@[simp] lemma IsProductLikeRealDeltaSCSet_iff (δ s C : ℝ) (A : Set ℝ) :
    IsProductLikeRealDeltaSCSet δ s C A ↔
    IsDeltaSCSet (d := 1) δ s C (productLikeRealLineCopy A) := by rfl

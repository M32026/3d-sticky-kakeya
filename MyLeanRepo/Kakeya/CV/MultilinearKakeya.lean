import MyLeanRepo.Kakeya.CV.PolynomialVisibilityComplete
import MyLeanRepo.Kakeya.CV.Targets.PreliminaryReduction
import MyLeanRepo.Kakeya.CV.Targets.VisibilityDegreeBound
import MyLeanRepo.Kakeya.CV.Targets.VisibilityDirectionalBound
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Three-dimensional multilinear Kakeya statements

Paper-faithful interfaces connecting the completed Carbery--Valdimarsson
polynomial visibility theorem to the delta-tube form consumed by WZ1.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Kakeya.CV

/-- A finite indexed family of unit neighborhoods of affine lines. -/
structure UnitLineFamily where
  card : ℕ
  base : Fin card → Point 3
  direction : Fin card → Point 3
  direction_unit : ∀ i, ‖direction i‖ = 1

namespace UnitLineFamily

/-- The unit-neighborhood carrier of one line in the family. -/
def tube (F : UnitLineFamily) (i : Fin F.card) : Set (Point 3) :=
  unitTube (F.base i) (F.direction i)

end UnitLineFamily

/-- The integer lattice indexing the unit cubes in the CV reduction. -/
abbrev UnitLatticeCube := Fin 3 → ℤ

/-- The Euclidean center associated to one integer lattice index. -/
def latticeCubeCenter (q : UnitLatticeCube) : Point 3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm fun i => (q i : ℝ)

/-- A unit-line neighborhood meets the closed lattice cube indexed by `q`. -/
def unitLineMeetsLatticeCube
    (F : UnitLineFamily) (i : Fin F.card) (q : UnitLatticeCube) : Prop :=
  (F.tube i ∩ unitCube (latticeCubeCenter q)).Nonempty

/-- The unsigned triple volume as a nonnegative real. -/
def tripleVolumeNNReal (v : Fin 3 → Point 3) : NNReal :=
  Real.toNNReal (tripleVolume v)

/--
The local lattice-cube weight from CV Proposition 2.  A triple contributes
only when all three unit-line neighborhoods meet the cube.
-/
def unitScaleCubeWeight
    (F₁ F₂ F₃ : UnitLineFamily) (q : UnitLatticeCube)
    (i : Fin F₁.card) (j : Fin F₂.card) (k : Fin F₃.card) : NNReal :=
  by
    classical
    exact
      if unitLineMeetsLatticeCube F₁ i q ∧
          unitLineMeetsLatticeCube F₂ j q ∧
          unitLineMeetsLatticeCube F₃ k q then
        tripleVolumeNNReal ![F₁.direction i, F₂.direction j, F₃.direction k]
      else
        0

/-- The `ENNReal` indicator of a spatial set. -/
def setIndicator (S : Set (Point 3)) (x : Point 3) : ENNReal :=
  S.indicator (fun _ => (1 : ENNReal)) x

/-- The trilinear multiplicity for three unit-scale line families. -/
def unitScaleTrilinearMultiplicity
    (F₁ F₂ F₃ : UnitLineFamily) (x : Point 3) : ENNReal :=
  ∑ i : Fin F₁.card, ∑ j : Fin F₂.card, ∑ k : Fin F₃.card,
    setIndicator (F₁.tube i) x * setIndicator (F₂.tube j) x *
      setIndicator (F₃.tube k) x *
        ENNReal.ofReal
          (tripleVolume ![F₁.direction i, F₂.direction j, F₃.direction k])

/-- The three-dimensional unit-scale specialization of CV Theorem 1. -/
def UnitScaleMultilinearKakeyaStatement : Prop :=
  ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ F₁ F₂ F₃ : UnitLineFamily,
      ∫⁻ x : Point 3,
          (unitScaleTrilinearMultiplicity F₁ F₂ F₃ x) ^ (1 / 2 : ℝ)
        ∂volume ≤
      C * ((F₁.card : ENNReal) * (F₂.card : ENNReal) *
        (F₃.card : ENNReal)) ^ (1 / 2 : ℝ)

/--
CV Section 4 local factorization on every finite collection of lattice cubes.

The dimensional constant is placed as an inverse factor on the geometric
weight, so the three column budgets are normalized exactly as required by
`PreliminaryReductionStatement`.
-/
def UnitScaleLatticeFactorizationStatement : Prop :=
  ∃ A : NNReal, 0 < A ∧
    ∀ F₁ F₂ F₃ : UnitLineFamily,
      ∀ cubes : Finset UnitLatticeCube,
        ∀ M : cubes → NNReal,
          (∑ q, M q ^ 3) = 1 →
            ∃ (S₁ : cubes → Fin F₁.card → NNReal)
                (S₂ : cubes → Fin F₂.card → NNReal)
                (S₃ : cubes → Fin F₃.card → NNReal),
              (∀ (q : cubes) i j k,
                A⁻¹ * unitScaleCubeWeight F₁ F₂ F₃ q.1 i j k *
                    M q ^ 3 ≤
                  S₁ q i * S₂ q j * S₃ q k) ∧
              (∀ i, ∑ q, S₁ q i ≤ 1) ∧
              (∀ j, ∑ q, S₂ q j ≤ 1) ∧
              (∀ k, ∑ q, S₃ q k ≤ 1)

/--
CV Section 4: the completed polynomial-visibility and directional-area
estimates produce the normalized finite lattice-cube factorization.
-/
def PolynomialVisibilityToLatticeFactorizationStatement : Prop :=
  PolynomialVisibilityStatement.{0} →
    ConcreteMollifiedSurfaceStatement →
      ConcreteMollifiedVisibilityStatement →
        PolynomialCylinderEstimateStatement →
          VisibilityDirectionalBoundStatement →
            VisibilityDegreeBoundStatement →
              UnitScaleLatticeFactorizationStatement

/-- Trilinear multiplicity of an indexed family of project delta-tubes. -/
def deltaTubeTrilinearMultiplicity {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ) (x : Point 3) : ENNReal :=
  ∑ i : Fin F.card, ∑ j : Fin F.card, ∑ k : Fin F.card,
    setIndicator (F.tube i).carrier x *
      setIndicator (F.tube j).carrier x *
      setIndicator (F.tube k).carrier x *
        ENNReal.ofReal
          (tripleVolume ![(F.tube i).direction, (F.tube j).direction,
            (F.tube k).direction])

/-- Trilinear multiplicity restricted to one measurable tube shading. -/
def shadingTrilinearMultiplicity {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (x : Point 3) : ENNReal :=
  ∑ i : Fin F.card, ∑ j : Fin F.card, ∑ k : Fin F.card,
    setIndicator (Y.carrier i) x * setIndicator (Y.carrier j) x *
      setIndicator (Y.carrier k) x *
        ENNReal.ofReal
          (tripleVolume ![(F.tube i).direction, (F.tube j).direction,
            (F.tube k).direction])

/-- The carrier form of WZ1 Theorem 10 for project delta-tubes. -/
def DeltaTubeMultilinearKakeyaStatement : Prop :=
  ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ F : Kakeya.Streamlined.TubeFamily δ,
        ∫⁻ x : Point 3,
            (deltaTubeTrilinearMultiplicity F x) ^ (1 / 2 : ℝ)
          ∂volume ≤
        C * (ENNReal.ofReal (δ ^ 2) * F.enncard) ^ (3 / 2 : ℝ)

/-- The exact shaded form of WZ1 Theorem 10. -/
def MultilinearKakeyaThreeStatement : Prop :=
  ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ F : Kakeya.Streamlined.TubeFamily δ,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
          ∫⁻ x : Point 3,
              (shadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ)
            ∂volume ≤
          C * (ENNReal.ofReal (δ ^ 2) * F.enncard) ^ (3 / 2 : ℝ)

/--
CV Sections 2--4: polynomial visibility, mollified directional surface area,
the cylinder estimate, and the finite preliminary reduction imply the
unit-scale endpoint trilinear inequality.
-/
def PolynomialVisibilityToUnitScaleMultilinearKakeyaStatement : Prop :=
  PolynomialVisibilityStatement.{0} →
    ConcreteMollifiedSurfaceStatement →
      ConcreteMollifiedVisibilityStatement →
        PolynomialCylinderEstimateStatement →
          VisibilityDirectionalBoundStatement →
            VisibilityDegreeBoundStatement →
              PreliminaryReductionStatement.{0, 0, 0, 0} →
                UnitScaleMultilinearKakeyaStatement

/-- Rescale the unit-line theorem to project delta-tube carriers. -/
def DeltaTubeMultilinearKakeyaScalingStatement : Prop :=
  UnitScaleMultilinearKakeyaStatement →
    DeltaTubeMultilinearKakeyaStatement

end Kakeya.CV

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Assertion D from the three-dimensional Kakeya paper

This file formalizes the statement of Assertion D, not its hairbrush proof.

## Geometric conventions

* The ambient space is `EuclideanSpace ℝ (Fin 3)`.
* A `δ`-tube is the **closed** `δ`-thickening of a **closed** unit line segment.
* The unit ball is the closed ball `Metric.closedBall 0 1`.
* A slab is the intersection of that closed unit ball with the **closed**
  `r`-thickening of an affine hyperplane. Thus the field `radius` is the
  neighbourhood radius; its full transverse width is `2 * radius`.
* All volumes are Lebesgue outer measures with values in `ℝ≥0∞`. No conversion
  with `ENNReal.toReal` is used.

The paper defines the Katz--Tao and Frostman constants by infima. Assertion D
only needs the corresponding inequalities with a specified error constant, so
the predicates below take that constant directly.
-/

noncomputable section

open MeasureTheory

namespace Kakeya

/-- The ambient copy of `ℝ³`. -/
abbrev Point3 := EuclideanSpace ℝ (Fin 3)

/-- The closed line segment `{base + t • direction | 0 ≤ t ≤ 1}`. -/
def unitSegment (base direction : Point3) : Set Point3 :=
  (fun t : ℝ => base + t • direction) '' Set.Icc 0 1

/--
The data determining a `δ`-tube. The norm condition makes `unitSegment base
direction` a unit line segment.
-/
structure DeltaTube (δ : ℝ) where
  base : Point3
  direction : Point3
  direction_unit : ‖direction‖ = 1

namespace DeltaTube

/-- The closed `δ`-neighbourhood of the tube's unit line segment. -/
def carrier {δ : ℝ} (T : DeltaTube δ) : Set Point3 :=
  Metric.cthickening δ (unitSegment T.base T.direction)

/-- Lebesgue volume of a tube. -/
def volume {δ : ℝ} (T : DeltaTube δ) : ENNReal :=
  MeasureTheory.volume T.carrier

/-- The closed unit ball convention used throughout Assertion D. -/
def unitBall : Set Point3 :=
  Metric.closedBall 0 1

/-- A tube is contained in the (closed) unit ball. -/
def IsInUnitBall {δ : ℝ} (T : DeltaTube δ) : Prop :=
  T.carrier ⊆ unitBall

/--
Two tubes are essentially distinct when the volume of their intersection is at
most one half of the larger tube volume.
-/
def EssentiallyDistinct {δ : ℝ} (T U : DeltaTube δ) : Prop :=
  MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
    (2 : ENNReal)⁻¹ * max T.volume U.volume

end DeltaTube

/-- A finite family of `δ`-tubes. -/
abbrev TubeFamily (δ : ℝ) := Finset (DeltaTube δ)

namespace TubeFamily

/-- Every tube in the family is contained in the closed unit ball. -/
def IsInUnitBall {δ : ℝ} (F : TubeFamily δ) : Prop :=
  ∀ ⦃T : DeltaTube δ⦄, T ∈ F → T.IsInUnitBall

/-- Distinct members of the finite family are essentially distinct. -/
def IsEssentiallyDistinct {δ : ℝ} (F : TubeFamily δ) : Prop :=
  ∀ ⦃T : DeltaTube δ⦄, T ∈ F →
    ∀ ⦃U : DeltaTube δ⦄, U ∈ F → T ≠ U → T.EssentiallyDistinct U

/-- Total tube mass `∑ T ∈ F, |T|`, valued in `ℝ≥0∞`. -/
def mass {δ : ℝ} (F : TubeFamily δ) : ENNReal :=
  ∑ T ∈ F, T.volume

/-- Number of members of a tube family, coerced to `ℝ≥0∞`. -/
def enncard {δ : ℝ} (F : TubeFamily δ) : ENNReal :=
  F.card

/-- Number of tubes whose closed carriers are contained in `W`. -/
def containedCount {δ : ℝ} (F : TubeFamily δ) (W : Set Point3) : ENNReal :=
  by
    classical
    exact ((F.filter fun (T : DeltaTube δ) => T.carrier ⊆ W).card : ENNReal)

end TubeFamily

/--
A measurable shading on `F`. Only values at members of `F` matter; for each
such tube, the shading is measurable and is a subset of the tube.
-/
structure Shading {δ : ℝ} (F : TubeFamily δ) where
  carrier : DeltaTube δ → Set Point3
  measurable_carrier :
    ∀ ⦃T : DeltaTube δ⦄, T ∈ F → MeasurableSet (carrier T)
  subset_tube :
    ∀ ⦃T : DeltaTube δ⦄, T ∈ F → carrier T ⊆ T.carrier

namespace Shading

/-- The union `⋃ T ∈ F, Y(T)`. -/
def union {δ : ℝ} {F : TubeFamily δ} (Y : Shading F) : Set Point3 :=
  {x | ∃ T : DeltaTube δ, T ∈ F ∧ x ∈ Y.carrier T}

/-- Total shaded mass `∑ T ∈ F, |Y(T)|`. -/
def mass {δ : ℝ} {F : TubeFamily δ} (Y : Shading F) : ENNReal :=
  ∑ T ∈ F, MeasureTheory.volume (Y.carrier T)

/-- The paper's aggregate `λ`-density condition. -/
def IsLambdaDense {δ : ℝ} {F : TubeFamily δ} (Y : Shading F)
    (lambda : ENNReal) : Prop :=
  lambda * F.mass ≤ Y.mass

end Shading

/--
An affine hyperplane together with a nonnegative closed-neighbourhood radius.
The unit normal removes the degenerate zero-normal presentation.
-/
structure Slab where
  normal : Point3
  offset : ℝ
  radius : ℝ
  normal_unit : ‖normal‖ = 1
  radius_nonneg : 0 ≤ radius

namespace Slab

/-- The affine hyperplane `{x | ⟪x, normal⟫ = offset}`. -/
def hyperplane (S : Slab) : Set Point3 :=
  {x | inner ℝ x S.normal = S.offset}

/--
The slab convention: closed unit ball intersected with the closed thickening
of an affine hyperplane.
-/
def carrier (S : Slab) : Set Point3 :=
  DeltaTube.unitBall ∩ Metric.cthickening S.radius S.hyperplane

end Slab

/-- Convert a nonnegative real power to `ℝ≥0∞` without using `toReal`. -/
def realRpowENN (x exponent : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.rpow x exponent)

/--
The common formal value denoted by `|T|` for a `δ`-tube: the Lebesgue volume
of the closed `δ`-tube around the canonical unit segment from `0` to `e₀`.
-/
def deltaTubeVolume (δ : ℝ) : ENNReal :=
  MeasureTheory.volume <|
    Metric.cthickening δ <|
      unitSegment 0 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

/--
Katz--Tao convex Wolff bound with the supplied constant `C`:
`#{T ⊆ W} ≤ C |W| |T|⁻¹` for every convex set `W`.
-/
def KatzTaoConvexWolffBound {δ : ℝ} (F : TubeFamily δ) (C : ℝ) : Prop :=
  ∀ W : Set Point3, Convex ℝ W →
    F.containedCount W ≤
      ENNReal.ofReal C * MeasureTheory.volume W * (deltaTubeVolume δ)⁻¹

/--
Frostman slab Wolff bound with the supplied constant `C`:
`#{T ⊆ W} ≤ C |W| (#F)` for every slab `W`.
-/
def FrostmanSlabWolffBound {δ : ℝ} (F : TubeFamily δ) (C : ℝ) : Prop :=
  ∀ S : Slab,
    F.containedCount S.carrier ≤
      ENNReal.ofReal C * MeasureTheory.volume S.carrier * F.enncard

/-- The exact lower-bound expression in Assertion D. -/
def AssertionDLowerBound {δ : ℝ} (F : TubeFamily δ) (Y : Shading F)
    (kappa sigma omega epsilon : ℝ) : Prop :=
  MeasureTheory.volume Y.union ≥
    ENNReal.ofReal kappa *
      realRpowENN δ (omega + epsilon) *
      F.enncard *
      deltaTubeVolume δ *
      ENNReal.rpow (F.enncard * ENNReal.rpow (deltaTubeVolume δ) (1 / 2)) (-sigma)

/--
Assertion `D(σ, ω)` from Definition 1.7/Assertion D of the paper.

The hypotheses that the family is essentially distinct and contained in the
unit ball are explicit here; in the paper they are bundled into the notation
`(𝕋, Y)δ`.
-/
def AssertionD (sigma omega : ℝ) : Prop :=
  0 ≤ sigma ∧ 0 ≤ omega ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ kappa eta : ℝ, 0 < kappa ∧ 0 < eta ∧
        ∀ delta : ℝ, 0 < delta →
          ∀ F : TubeFamily delta,
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            ∀ Y : Shading F,
              Y.IsLambdaDense (realRpowENN delta eta) →
              KatzTaoConvexWolffBound F (Real.rpow delta (-eta)) →
              FrostmanSlabWolffBound F (Real.rpow delta (-eta)) →
              AssertionDLowerBound F Y kappa sigma omega epsilon

end Kakeya

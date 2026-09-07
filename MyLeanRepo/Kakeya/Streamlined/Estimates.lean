import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Concentration conditions and Kakeya estimate statements

All estimates are explicit propositions.  No theorem from the sticky Kakeya
papers is declared as an axiom; `StickyKakeyaHypothesis` is a proposition that
later theorems receive as an ordinary proof argument.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace BodyFamily

/-- Density of members contained in `K`. -/
def density (F : BodyFamily) (K : Set Point3) : ENNReal :=
  F.containedMass K / MeasureTheory.volume K

/-- Maximal convex-set density. -/
def deltaMax (F : BodyFamily) : ENNReal :=
  sSup {d : ENNReal |
    ∃ K : Set Point3, Convex ℝ K ∧ d = F.density K}

/-- Frostman constant relative to the containing body `U`. -/
def frostmanConstantIn (F : BodyFamily) (U : Set Point3) : ENNReal :=
  sSup {c : ENNReal |
    ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ U ∧
      c = F.density K / F.density U}

/-- Katz--Tao non-concentration with the supplied constant. -/
def IsCKatzTao (F : BodyFamily) (C : ENNReal) : Prop :=
  F.deltaMax ≤ C

/-- Frostman non-concentration inside `U` with the supplied constant. -/
def IsCFrostmanIn (F : BodyFamily) (U : Set Point3) (C : ENNReal) : Prop :=
  F.frostmanConstantIn U ≤ C

/-- All members have common dimensions up to the factor `A`. -/
def HasComparableDimensions (F : BodyFamily) (a b c A : ℝ) : Prop :=
  ∀ i, (F.body i).HasDimensions a b c A

/-- All members are `a × b × 1` planks up to the factor `A`. -/
def IsPlankFamily (F : BodyFamily) (a b A : ℝ) : Prop :=
  ∀ i, (F.body i).IsPlank a b A

end BodyFamily

/-- Two nonnegative quantities are comparable by the multiplicative factor `C`. -/
def ComparableBy (C x y : ENNReal) : Prop :=
  1 ≤ C ∧ x ≤ C * y ∧ y ≤ C * x

namespace Factoring

/-- Every fiber is `C`-Frostman inside its parent body. -/
def FibersAreCFrostman {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (C : ENNReal) : Prop :=
  ∀ j, ∀ K : Set Point3, Convex ℝ K →
    K ⊆ (coarse.body j).carrier →
      P.fiberContainedMass j K * (coarse.body j).volume ≤
        C * P.fiberMass j * MeasureTheory.volume K

/-- Fiber density in each parent is comparable to the supplied density `D`. -/
def FibersHaveDensity {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (D C : ENNReal) : Prop :=
  ∀ j, ComparableBy C
    (P.fiberMass j / (coarse.body j).volume) D

end Factoring

namespace TubeCover

/-- Regard a tube cover as a factoring of indexed body families. -/
def toFactoring {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) :
    Factoring fine.toBodyFamily coarse.toBodyFamily where
  parent := P.parent
  parent_surjective := P.parent_surjective
  contained := P.nested

/-- Every fine fiber is Frostman inside its assigned coarse tube. -/
def FibersAreCFrostman {δ ρ : ℝ} {fine : TubeFamily δ}
    {coarse : TubeFamily ρ} (P : TubeCover fine coarse)
    (C : ENNReal) : Prop :=
  P.toFactoring.FibersAreCFrostman C

end TubeCover

/-- The subtype of scales between `δ` and `1`. -/
abbrev AdmissibleScale (δ : ℝ) :=
  {rho : ℝ // δ ≤ rho ∧ rho ≤ 1}

/--
A paper-level choice of coarse tube family and parent map at every scale.
Coarse tubes are required to be essentially distinct, preventing duplicate
coarse carriers from making uniformity vacuous. The paper does not require
the choices at different scales to come with transition maps.
-/
structure UniformTubeStructure {δ : ℝ} (F : TubeFamily δ) where
  coarse : ∀ rho : AdmissibleScale δ, TubeFamily rho.1
  cover : ∀ rho : AdmissibleScale δ, TubeCover F (coarse rho)
  uniformity : ENNReal
  one_le_uniformity : 1 ≤ uniformity
  uniformity_ne_top : uniformity ≠ ⊤
  uniform : ∀ rho, (cover rho).IsCUniform uniformity
  coarse_distinct : ∀ rho, (coarse rho).IsEssentiallyDistinct

/--
An optional strengthening in which the selected covers form a strict
cross-scale hierarchy.
-/
structure CoherentUniformTubeStructure {δ : ℝ} (F : TubeFamily δ) extends
    UniformTubeStructure F where
  transition :
    ∀ rho sigma : AdmissibleScale δ, rho.1 ≤ sigma.1 →
      Fin (coarse rho).card → Fin (coarse sigma).card
  transition_nested :
    ∀ rho sigma (h : rho.1 ≤ sigma.1) i,
      ((coarse rho).tube i).carrier ⊆
        ((coarse sigma).tube (transition rho sigma h i)).carrier
  transition_refl :
    ∀ rho i, transition rho rho le_rfl i = i
  transition_comp :
    ∀ rho sigma tau
      (h₁ : rho.1 ≤ sigma.1) (h₂ : sigma.1 ≤ tau.1) i,
      transition sigma tau h₂ (transition rho sigma h₁ i) =
        transition rho tau (le_trans h₁ h₂) i
  parent_compatible :
    ∀ rho sigma (h : rho.1 ≤ sigma.1) i,
      transition rho sigma h ((cover rho).parent i) =
        (cover sigma).parent i

namespace UniformTubeStructure

/-- Every fine fiber is Frostman inside its selected parent at every scale. -/
def IsFrostmanAtEveryScale {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.cover rho).FibersAreCFrostman C

/-- Every chosen coarse family is Katz--Tao at every scale. -/
def IsKatzTaoAtEveryScale {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.coarse rho).toBodyFamily.IsCKatzTao C

end UniformTubeStructure

/--
The partial Katz--Tao estimate `K_KT(β)`, with all quantifiers and losses
explicit and average multiplicity written without division.
-/
def KatzTaoEstimate (beta : ℝ) : Prop :=
  0 ≤ beta ∧ beta ≤ 1 ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ, 0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.Nonempty →
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            F.toBodyFamily.IsCKatzTao
              (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              Y.HasAverageMultiplicityAtMost
                (Kakeya.realRpowENN delta (-epsilon) *
                  ENNReal.rpow F.enncard beta)

/--
The partial Frostman estimate `K_F(β)`, in its multiplicity formulation.
-/
def FrostmanEstimate (beta : ℝ) : Prop :=
  0 ≤ beta ∧ beta ≤ 1 ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ, 0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.Nonempty →
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            F.toBodyFamily.IsCFrostmanIn unitBall.carrier
              (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              Y.HasAverageMultiplicityAtMost
                (Kakeya.realRpowENN delta (-epsilon - 2 * beta) *
                  ENNReal.rpow
                    (Kakeya.realRpowENN delta 2 * F.enncard)
                    (1 - beta / 2))

/--
The generalized every-scale sticky theorem used as the sole external
hypothesis in the streamlined reduction.
-/
def StickyKakeyaHypothesis : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ, 0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ U : UniformTubeStructure F,
          U.uniformity ≤ Kakeya.realRpowENN delta (-eta) →
          U.IsFrostmanAtEveryScale
            (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
            MeasureTheory.volume Y.union ≥
              Kakeya.realRpowENN delta epsilon

/-- The Katz--Tao-at-every-scale consequence derived from sticky Kakeya. -/
def KatzTaoEveryScaleEstimate : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ, 0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ U : UniformTubeStructure F,
          U.uniformity ≤ Kakeya.realRpowENN delta (-eta) →
          U.IsKatzTaoAtEveryScale
            (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
            Y.HasAverageMultiplicityAtMost
              (Kakeya.realRpowENN delta (-epsilon))

/-- The discretized three-dimensional Kakeya conclusion in the introduction. -/
def GeneralKakeyaStatement : Prop :=
  ∀ beta : ℝ, 0 < beta →
    ∃ eta delta₀ : ℝ, 0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : TubeFamily delta,
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          F.toBodyFamily.IsCKatzTao
            (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
            MeasureTheory.volume Y.union ≥
              Kakeya.realRpowENN delta beta * F.nominalMass

end Kakeya.Streamlined

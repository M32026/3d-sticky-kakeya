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

/-- Every assigned parent-map fiber is Frostman inside its parent tube. -/
def AssignedFibersAreCFrostman {δ ρ : ℝ} {fine : TubeFamily δ}
    {coarse : TubeFamily ρ} (P : TubeCover fine coarse)
    (C : ENNReal) : Prop :=
  P.toFactoring.FibersAreCFrostman C

/-- Every complete geometric containment fiber is Frostman in its coarse tube. -/
def FibersAreCFrostman {δ ρ : ℝ} {fine : TubeFamily δ}
    {coarse : TubeFamily ρ} (_P : TubeCover fine coarse)
    (C : ENNReal) : Prop :=
  ∀ parent,
    (fine.containedFamily coarse parent).toBodyFamily.frostmanConstantIn
      (coarse.tube parent).carrier ≤ C

end TubeCover

/-- The subtype of scales between `δ` and `1`. -/
abbrev AdmissibleScale (δ : ℝ) :=
  {rho : ℝ // δ ≤ rho ∧ rho ≤ 1}

/--
Raw quantitative coarse-family data at every real scale.

The finite number `uniformity` belongs to the fixed runtime pair `(delta,F)`.
It is not by itself the paper's all-real `≈` convention.  Paper-facing uses
must additionally provide an `ApproxUniformTubeStructure epsilon F`
certificate, i.e. the subpolynomial bound
`uniformity ≤ delta⁻ᵉᵖˢⁱˡᵒⁿ`.

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
  uniform :
    ∀ rho, (cover rho).toFactoring.FibersAreCUniform uniformity
  coarse_distinct : ∀ rho, (coarse rho).IsEssentiallyDistinct

/-- Paper-facing all-real `≈`-uniformity at one requested loss exponent. -/
structure ApproxUniformTubeStructure
    {δ : ℝ} (epsilon : ℝ) (F : TubeFamily δ) extends
    UniformTubeStructure F where
  uniformity_le :
    toUniformTubeStructure.uniformity ≤
      Kakeya.realRpowENN δ (-epsilon)

namespace ApproxUniformTubeStructure

/-- Forget the subpolynomial certificate and retain the raw all-scale data. -/
abbrev raw
    {δ epsilon : ℝ} {F : TubeFamily δ}
    (U : ApproxUniformTubeStructure epsilon F) :
    UniformTubeStructure F :=
  U.toUniformTubeStructure

end ApproxUniformTubeStructure

/--
Internal all-scale structure whose chosen parent-map fibers are uniform.

This is the historical bookkeeping structure used by exact partitions and
random-translation genealogies. It is not the paper-facing Definition 2.1.
-/
structure AssignedUniformTubeStructure {δ : ℝ} (F : TubeFamily δ) where
  coarse : ∀ rho : AdmissibleScale δ, TubeFamily rho.1
  cover : ∀ rho : AdmissibleScale δ, TubeCover F (coarse rho)
  assignedUniformity : ENNReal
  one_le_assignedUniformity : 1 ≤ assignedUniformity
  assignedUniformity_ne_top : assignedUniformity ≠ ⊤
  assignedUniform :
    ∀ rho, (cover rho).toFactoring.FibersAreCUniform assignedUniformity
  coarse_distinct : ∀ rho, (coarse rho).IsEssentiallyDistinct

namespace UniformTubeStructure

/-- View a legacy uniform structure as explicit assigned-fiber data. -/
def toAssigned {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) :
    AssignedUniformTubeStructure F where
  coarse := U.coarse
  cover := U.cover
  assignedUniformity := U.uniformity
  one_le_assignedUniformity := U.one_le_uniformity
  assignedUniformity_ne_top := U.uniformity_ne_top
  assignedUniform := U.uniform
  coarse_distinct := U.coarse_distinct

end UniformTubeStructure

/--
Internal optional strengthening in which the selected raw covers form a
strict cross-scale hierarchy. This is not a paper `≈` certificate.
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

/--
Internal sidecar asserting quantitative uniformity of the chosen parent-map
fibers of a public structure.  This is not implied by paper full-fiber
uniformity.
-/
def HasAssignedUniformity {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.cover rho).toFactoring.FibersAreCUniform C

/-- Every assigned parent-map fiber is Frostman at every scale. -/
def IsFrostmanAtEveryScale {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.cover rho).AssignedFibersAreCFrostman C

/-- Every complete geometric containment fiber is Frostman at every scale. -/
def FullContainmentIsFrostmanAtEveryScale {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.cover rho).FibersAreCFrostman C

/-- Every chosen coarse family is Katz--Tao at every scale. -/
def IsKatzTaoAtEveryScale {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.coarse rho).toBodyFamily.IsCKatzTao C

end UniformTubeStructure

namespace AssignedUniformTubeStructure

/--
Forget the quantitative assigned-fiber comparison while retaining the same
strict covers as a paper-semantic full-fiber structure.

The full-fiber constant is the crude finite bound `max 1 #F`.  This projection
uses only finiteness and parent-map surjectivity; it does not identify
assigned fibers with complete geometric containment fibers.
-/
def toCrudeFullUniformTubeStructure
    {δ : ℝ} {F : TubeFamily δ}
    (U : AssignedUniformTubeStructure F) :
    UniformTubeStructure F where
  coarse := U.coarse
  cover := U.cover
  uniformity := max 1 F.enncard
  one_le_uniformity := le_max_left _ _
  uniformity_ne_top := by
    exact max_ne_top (by simp) (by simp [TubeFamily.enncard])
  uniform := by
    intro rho
    exact (U.cover rho).factoringFibersAreCUniform_of_enncard_le
      (le_max_left _ _) (le_max_right _ _)
  coarse_distinct := U.coarse_distinct

/-- Every assigned parent-map fiber is Frostman at every scale. -/
def AssignedIsFrostmanAtEveryScale {δ : ℝ} {F : TubeFamily δ}
    (U : AssignedUniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.cover rho).AssignedFibersAreCFrostman C

/-- Every chosen coarse family is Katz--Tao at every scale. -/
def IsKatzTaoAtEveryScale {δ : ℝ} {F : TubeFamily δ}
    (U : AssignedUniformTubeStructure F) (C : ENNReal) : Prop :=
  ∀ rho, (U.coarse rho).toBodyFamily.IsCKatzTao C

end AssignedUniformTubeStructure

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
Legacy undilated sticky interface retained for historical strict-fiber
compatibility modules.

Its raw `UniformTubeStructure` plus the explicit subpolynomial bound is
logically equivalent to an `ApproxUniformTubeStructure` input, but it is not
the canonical Yosemite paper boundary. New paper-facing code uses
`GWZStickyVolumeSocket` from `DilatedStickyInput`.
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

/--
Legacy strict-undilated Katz--Tao-at-every-scale estimate retained for
compatibility modules. The canonical fixed-dilation paper result is
`FullFiberKatzTaoEveryScaleEstimate` in `Statements`.
-/
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

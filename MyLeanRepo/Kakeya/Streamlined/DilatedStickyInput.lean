import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DilatedUniformTubeStructure

/-!
# Sticky Kakeya input with an explicit fixed cover dilation

The paper treats absolute enlargement of coarse tubes and replacement of the
unit support ball by any fixed ball as harmless changes of constants.  The
strict undilated all-real-scale cover model is nevertheless false for
unit-length tubes, so those conventions must be visible in the formal input.

`FixedSupportDilatedStickyHypothesis A R` is the minimal corrected theorem
socket. `DilatedStickyKakeyaHypothesis A` is its stronger uniform closure over
all fixed support radii. Both are propositions, not axioms and not GWZ
random-translation producers.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/--
External fixed-support condition for a tube family.

This predicate is deliberately separate from branching uniformity, Frostman
control, and cover dilation.  Changing the support radius changes only
fixed-geometry constants and theorem thresholds.
-/
def TubeFamily.IsSupportedInClosedBall
    {delta : ℝ} (F : TubeFamily delta) (R : ℝ) : Prop :=
  ∀ index,
    (F.tube index).carrier ⊆
      Metric.closedBall (0 : Point3) R

namespace TubeFamily.IsSupportedInClosedBall

/-- A family supported in a smaller ball is supported in every larger ball. -/
theorem mono
    {delta Rsmall Rlarge : ℝ}
    {F : TubeFamily delta}
    (hRadius : Rsmall ≤ Rlarge)
    (hSupport : F.IsSupportedInClosedBall Rsmall) :
    F.IsSupportedInClosedBall Rlarge := by
  intro index
  exact (hSupport index).trans
    (Metric.closedBall_subset_closedBall hRadius)

end TubeFamily.IsSupportedInClosedBall

/-- The absolute cover dilation used by the repaired Theorem 7.3 proof. -/
def theoremSevenThreeCoverDilation : ℝ :=
  7998000

@[simp]
lemma theoremSevenThreeCoverDilation_eq :
    theoremSevenThreeCoverDilation = 7998000 := rfl

lemma one_le_theoremSevenThreeCoverDilation :
    1 ≤ theoremSevenThreeCoverDilation := by
  norm_num [theoremSevenThreeCoverDilation]

/--
Every-scale sticky Kakeya at one explicit cover dilation and one fixed support
radius.

This is the smallest theorem socket consumed by a single GWZ assembly. The
small-scale threshold and density exponent may depend on both fixed geometric
parameters.
-/
def FixedSupportDilatedStickyHypothesis (A R : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.Nonempty →
            F.IsSupportedInClosedBall R →
            F.IsEssentiallyDistinct →
            ∀ U :
                ApproxDilatedUniformTubeStructure
                  (A := A) eta F,
              U.raw.IsFrostmanAtEveryScale
                (Kakeya.realRpowENN delta (-eta)) →
              ∀ Y : TubeShading F,
                Y.IsLambdaDense
                  (Kakeya.realRpowENN delta eta) →
                volume Y.union ≥
                  Kakeya.realRpowENN delta epsilon

/-- Uniform fixed-dilation sticky Kakeya over every fixed support radius. -/
def DilatedStickyKakeyaHypothesis (A : ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R →
    FixedSupportDilatedStickyHypothesis A R

namespace FixedSupportDilatedStickyHypothesis

/-- A theorem for a larger support ball applies to every smaller support
ball, with no change to its exponent or scale threshold. -/
theorem mono_support
    {A Rsmall Rlarge : ℝ}
    (hRadius : Rsmall ≤ Rlarge)
    (hSticky : FixedSupportDilatedStickyHypothesis A Rlarge) :
    FixedSupportDilatedStickyHypothesis A Rsmall := by
  intro epsilon hepsilon
  rcases hSticky epsilon hepsilon with
    ⟨eta, delta₀, heta, hdelta₀,
      hdelta₀One, hmain⟩
  refine
    ⟨eta, delta₀, heta, hdelta₀,
      hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall F
  intro hFNonempty hFSupport hFDistinct U
  intro hUFrostman Y hYDense
  exact hmain delta hdelta hdeltaSmall F
    hFNonempty
    (hFSupport.mono hRadius)
    hFDistinct U hUFrostman Y hYDense

end FixedSupportDilatedStickyHypothesis

/-- Specialize the all-support-radii hypothesis to one fixed radius. -/
theorem DilatedStickyKakeyaHypothesis.atRadius
    {A R : ℝ}
    (hSticky : DilatedStickyKakeyaHypothesis A)
    (hR : 1 ≤ R) :
    FixedSupportDilatedStickyHypothesis A R :=
  hSticky R hR

/-- The support radius produced by the current GWZ random translations. -/
def theoremSevenThreeSupportRadius : ℝ :=
  10

@[simp]
lemma theoremSevenThreeSupportRadius_eq :
    theoremSevenThreeSupportRadius = 10 := rfl

lemma one_le_theoremSevenThreeSupportRadius :
    1 ≤ theoremSevenThreeSupportRadius := by
  norm_num [theoremSevenThreeSupportRadius]

/-- The minimal external volume-lower-bound socket used by GWZ Theorem 7.3. -/
abbrev GWZStickyVolumeSocket : Prop :=
  FixedSupportDilatedStickyHypothesis
    theoremSevenThreeCoverDilation
    theoremSevenThreeSupportRadius

/-- The stronger all-support-radii theorem supplies the minimal GWZ socket. -/
theorem DilatedStickyKakeyaHypothesis.toGWZSocket
    (hSticky :
      DilatedStickyKakeyaHypothesis
        theoremSevenThreeCoverDilation) :
    GWZStickyVolumeSocket :=
  hSticky.atRadius one_le_theoremSevenThreeSupportRadius

end Kakeya.Streamlined

end

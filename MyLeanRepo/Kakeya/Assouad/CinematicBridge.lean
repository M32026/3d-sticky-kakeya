import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Cinematic.Definitions

/-!
# WZ2-to-PYZ cinematic bridge

Definitions for the family
`g_{a,b,d}(t) = a + b f(t) + d t f(t)` used in WZ2 Section 7.
-/

noncomputable section

open Set

namespace Kakeya.Assouad

/-- Global representative of the projected curve with parameters `(a,b,d)`. -/
def slopeCurveFunction (f : SlopeFunction) (a b d : ℝ) (t : ℝ) : ℝ :=
  a + b * f t + d * t * f t

/-- A cinematic `C²` object represents the displayed slope curve and its jet. -/
def RepresentsSlopeCurve (g : Kakeya.Cinematic.C2Function)
    (f : SlopeFunction) (a b d : ℝ) : Prop :=
  ∀ x : Kakeya.Cinematic.UnitPoint,
    g x = slopeCurveFunction f a b d x ∧
      g.firstDeriv x = deriv (slopeCurveFunction f a b d) x ∧
      g.secondDeriv x =
        deriv (deriv (slopeCurveFunction f a b d)) x

/-- Exact membership predicate for the three-parameter cinematic family. -/
def IsSlopeCurveFamily (family : Set Kakeya.Cinematic.C2Function)
    (f : SlopeFunction) : Prop :=
  ∀ g : Kakeya.Cinematic.C2Function,
    g ∈ family ↔
      ∃ a ∈ Set.Icc (-1 : ℝ) 1,
        ∃ b ∈ Set.Icc (-1 : ℝ) 1,
          ∃ d ∈ Set.Icc (-1 : ℝ) 1,
            RepresentsSlopeCurve g f a b d

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorUniformBound

/-!
# Quadratic-certified centered Taylor transport

The original centered Taylor transport statement records the copied jet and
relative metric distortion, but it does not characterize the two Taylor
tails.  Absolute-`C²` globalization must use the same transport witness for
cinematicity, graph transport, and the uniform bound.  This strengthened
statement therefore carries the pointwise quadratic-extension certificate
on that witness.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

def CenteredTaylorQuadraticCinematicTransportStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ I : ParameterInterval,
        0 < I.length →
        I.IsShort (12 * K) →
        ∃ transport : C2Function → C2Function,
          Set.InjOn transport family ∧
          IsCinematicFamily
            (transport '' family)
            (12 * K)
            ((D * Real.rpow (6 * K) (Real.log D / Real.log 2)) ^ 3) ∧
          (∀ f ∈ family, IsCenteredJetCopy I f (transport f)) ∧
          (∀ f ∈ family,
            IsCenteredQuadraticJetExtension I f (transport f)) ∧
          ∀ f ∈ family, ∀ g ∈ family,
            restrictedC2Distance I f g ≤
                c2Distance (transport f) (transport g) ∧
              c2Distance (transport f) (transport g) ≤
                3 * restrictedC2Distance I f g

end Kakeya.Cinematic

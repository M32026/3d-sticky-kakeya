import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorCinematicTransportInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.TaylorJetBounds

/-!
# Uniform absolute bound for centered Taylor transport

The centered Taylor construction copies the original jet on the translated
physical interval and uses quadratic Taylor jets based at an endpoint on the
two tails.  This module isolates the exact pointwise property needed to carry
an absolute `C²` normalization through that construction.
-/

namespace Kakeya.Cinematic

/--
Every transported two-jet is a quadratic Taylor jet based at one point of the
physical interval, at a displacement of absolute value at most `1/2`.
-/
def IsCenteredQuadraticJetExtension
    (I : ParameterInterval) (f transported : C2Function) : Prop :=
  ∀ y : UnitPoint,
    ∃ x : I.LocalPoint, ∃ t : ℝ,
      |t| ≤ 1 / 2 ∧
        transported y =
          f x.1 + f.firstDeriv x.1 * t +
            (f.secondDeriv x.1 / 2) * t ^ 2 ∧
        transported.firstDeriv y =
          f.firstDeriv x.1 + f.secondDeriv x.1 * t ∧
        transported.secondDeriv y = f.secondDeriv x.1

/--
A centered quadratic Taylor transport sends an absolute two-jet bound `M` to
the family-independent bound `2*M`.
-/
theorem hasUniformC2Bound_transportImage_of_centeredQuadraticJetExtension
    {family : Set C2Function} {M : ℝ}
    (hM : 0 ≤ M) (hfamily : HasUniformC2Bound family M)
    (I : ParameterInterval) (transport : C2Function → C2Function)
    (htransport :
      ∀ f ∈ family,
        IsCenteredQuadraticJetExtension I f (transport f)) :
    HasUniformC2Bound (transport '' family) (2 * M) := by
  rintro transported ⟨f, hf, rfl⟩ y
  rcases htransport f hf y with
    ⟨x, t, ht, hvalue, hfirst, hsecond⟩
  rcases hfamily hf x.1 with ⟨hv₀, hv₁, hv₂⟩
  rw [hvalue, hfirst, hsecond]
  exact quadraticTaylorJet_abs_le_two_mul hM ht hv₀ hv₁ hv₂

end Kakeya.Cinematic

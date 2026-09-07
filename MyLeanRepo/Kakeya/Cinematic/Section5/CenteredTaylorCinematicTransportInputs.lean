import MyLeanRepo.Kakeya.Cinematic.Section5.RestrictedFamily

/-!
# Centered Taylor transport for short physical intervals

The interval restriction used after PYZ Lemma 39 cannot be fed directly to
the controlled-interval forms of Lemmas 16 and 17: both conclusions are false
for the unscaled physical `C²` metric on arbitrarily short intervals.

The replacement route moves the restricted jet to the center of `[0, 1]` and
extends it outside the copied interval by the quadratic Taylor polynomials at
the two endpoints.  Horizontal translation does not rescale derivatives, and
the triangular Taylor formulas distort the physical restricted `C²` metric
by at most an absolute factor.  The transported image is therefore again a
cinematic family, now with an explicit fixed loss in its cinematic and
doubling constants.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

/--
`transported` contains an exact horizontally translated copy of the two-jet
of `f` on `I`, centered at `1/2`.  Both directions are recorded so later graph
neighborhood transport does not need to reconstruct the inverse coordinate
map.
-/
def IsCenteredJetCopy
    (I : ParameterInterval) (f transported : C2Function) : Prop :=
  (∀ x : I.LocalPoint,
      ∃ y : UnitPoint,
        (y : ℝ) = (x.1 : ℝ) + (1 / 2 - I.midpoint) ∧
          transported y = f x.1 ∧
          transported.firstDeriv y = f.firstDeriv x.1 ∧
          transported.secondDeriv y = f.secondDeriv x.1) ∧
    (∀ y : UnitPoint,
      |(y : ℝ) - 1 / 2| ≤ I.length / 2 →
        ∃ x : I.LocalPoint,
          (x.1 : ℝ) = (y : ℝ) - (1 / 2 - I.midpoint) ∧
            transported y = f x.1 ∧
            transported.firstDeriv y = f.firstDeriv x.1 ∧
            transported.secondDeriv y = f.secondDeriv x.1)

/--
Quantitative Taylor-extension transport for a short physical interval.

The image metric is bi-Lipschitz equivalent to `restrictedC2Distance I` with
absolute distortion `3`.  Three iterations of the restricted doubling cover
absorb that distortion.  The factor `12` in the cinematic constant leaves
room for the inverse triangular Taylor estimate outside the copied interval.
-/
def CenteredTaylorCinematicTransportStatement : Prop :=
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
          ∀ f ∈ family, ∀ g ∈ family,
            restrictedC2Distance I f g ≤
                c2Distance (transport f) (transport g) ∧
              c2Distance (transport f) (transport g) ≤
                3 * restrictedC2Distance I f g

end Kakeya.Cinematic

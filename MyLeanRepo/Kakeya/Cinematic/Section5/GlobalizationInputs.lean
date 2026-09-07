import MyLeanRepo.Kakeya.Cinematic.WZ2Input
import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Inputs for globalizing the short-curve estimate

The globalization following PYZ Lemma 39 has three logically separate parts:

1. a logarithmic family of intervals whose centered sixteenths cover the
   parameter interval away from two endpoint stubs;
2. restriction transport for the cinematic family and finite subfamily;
3. the multiplicity-weighted estimate on the endpoint stubs.

This module freezes only the propositions shared by those leaves.
-/

namespace Kakeya.Cinematic

/--
Logarithmic centered-sixteenth cover of the unit parameter interval.

For small graph radius `rho`, the interval away from two endpoint stubs of
length `2*rho` is covered by the centered sixteenths of `O(|log rho|)`
parameter intervals. Each interval is short enough for the local geometry and
at least `4*rho` long, so graph-neighborhood witnesses at radius `rho` remain
inside the restricted domain. No fixed `IsControlled` lower bound is imposed:
the intervals approaching the endpoints shrink geometrically, exactly as in
the proof following PYZ Lemma 39.
-/
def CenteredSixteenthIntervalCoverStatement : Prop :=
  ∀ {K : ℝ}, 1 ≤ K →
    ∃ C_cover : ℝ, 0 < C_cover ∧
      ∀ {rho : ℝ}, 0 < rho → rho ≤ (24 * K)⁻¹ →
        ∃ intervals : IntervalFamily,
          0 < intervals.card ∧
          (∀ i,
            4 * rho ≤ (intervals.interval i).length ∧
              (intervals.interval i).IsShort K) ∧
          (intervals.card : ℝ) ≤
            C_cover * (|Real.log rho| + 1) ∧
          Set.Icc (2 * rho) (1 - 2 * rho) ⊆
            ⋃ i, (intervals.interval i).realCenteredCarrier (1 / 16)

/--
Absorb the two endpoint stubs into the final level-set loss.

The multiplicity-weighted stub estimate gives an `O(rho^2 * F.card / mu)`
bound. With `rho = lambda * delta`, Katz--Tao cardinality and the nonempty
level condition give `F.card ≤ C_KT / delta` and `mu ≤ F.card`; after shrinking
`delta₀`, the remaining family-dependent constant is absorbed by
`delta^(-epsilon)`.
-/
def HorizontalStubLevelSetAbsorptionStatement : Prop :=
  HorizontalGraphNeighborhoodVolumeStatement →
    HorizontalStubMultiplicityVolumeStatement →
      ∀ {C_KT lambda L epsilon : ℝ},
        1 ≤ C_KT →
        1 ≤ lambda →
        0 ≤ L →
        0 < epsilon →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧
          delta₀ ≤ 1 / lambda ∧
          ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
            ∀ {F : FiniteFunctionFamily} {mu : ℕ}
                {E : Set (ℝ × ℝ)} {a b : ℝ},
              F.HasKatzTaoBound delta C_KT →
              0 < mu →
              E.Nonempty →
              MeasurableSet E →
              a ≤ b →
              Set.Icc a b ⊆ unitInterval →
              b - a ≤ 2 * lambda * delta →
              (∀ f ∈ F.carrier, ∀ x : UnitPoint,
                |f.firstDeriv x| ≤ L) →
              E ⊆ Set.Icc a b ×ˢ (Set.univ : Set ℝ) →
              (∀ p ∈ E,
                (mu : ℝ) ≤ multiplicity F (lambda * delta) p) →
              MeasureTheory.volume E ≤
                ENNReal.ofReal
                  (Real.rpow delta (-epsilon) *
                    Real.rpow (mu : ℝ) (-3 / 2 : ℝ))

end Kakeya.Cinematic

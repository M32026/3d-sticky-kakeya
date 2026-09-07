import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorCinematicTransportInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.RestrictedGraphs
import MyLeanRepo.Kakeya.Cinematic.Section5.RestrictedScales

/-!
# Finite graph transport through a centered Taylor extension

This is the finite-family consumer of `CenteredTaylorCinematicTransportStatement`.
It records the exact data needed to apply the controlled short-curve estimate
to a genuinely tiny physical interval without asserting false arbitrary-short
forms of PYZ Lemmas 16 or 17.

The local metric scale becomes `delta / (3*K)`.  Consequently the graph
neighborhood dilation becomes `3*K*lambda`, while its physical radius remains
exactly `lambda*delta`.  The Katz--Tao constant incurs a factor `2`: its ball
center is arbitrary, so a nonempty image ball is recentered at one transported
family element and the radius doubles.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

/-- Image of a finite function family under an arbitrary function map. -/
def FiniteFunctionFamily.transportImage
    (F : FiniteFunctionFamily) (transport : C2Function → C2Function) :
    FiniteFunctionFamily where
  carrier := transport '' F.carrier
  finite := F.finite.image transport

/-- Horizontal displacement that moves the midpoint of `I` to `1/2`. -/
def centeredHorizontalShift (I : ParameterInterval) : ℝ :=
  1 / 2 - I.midpoint

/-- Apply the centered horizontal displacement to a point of the plane. -/
def centeredHorizontalPoint
    (I : ParameterInterval) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + centeredHorizontalShift I, p.2)

/--
The finite graph-transport conclusions for one fixed transport witness.

Naming this package lets the family-dependent and absolute-`C²`-uniform
callers share the same proved transport mechanics without reselecting the
existential witness.
-/
def CenteredTaylorFiniteGraphTransportData
    (K D C_KT lambda : ℝ)
    (family : Set C2Function)
    (I : ParameterInterval)
    (delta : ℝ)
    (F : FiniteFunctionFamily)
    (transport : C2Function → C2Function) : Prop :=
  let imageFamily := transport '' family
  let transportedF := F.transportImage transport
  Set.InjOn transport family ∧
    IsCinematicFamily
      imageFamily
      (12 * K)
      ((D *
          Real.rpow (6 * K)
            (Real.log D / Real.log 2)) ^ 3) ∧
    transportedF.carrier ⊆ imageFamily ∧
    transportedF.card = F.card ∧
    transportedF.IsDeltaSeparated (delta / (3 * K)) ∧
    transportedF.HasKatzTaoBound
      (delta / (3 * K)) (2 * C_KT) ∧
    (∀ f ∈ family,
      IsCenteredJetCopy I f (transport f)) ∧
    (∀ f ∈ family, ∀ g ∈ family,
      restrictedC2Distance I f g ≤
          c2Distance (transport f) (transport g) ∧
        c2Distance (transport f) (transport g) ≤
          3 * restrictedC2Distance I f g) ∧
    (∀ f ∈ F.carrier, ∀ p : ℝ × ℝ,
      p.1 ∈ I.realCenteredCarrier (1 / 16) →
        (p ∈ graphNeighborhood f (lambda * delta) ↔
          centeredHorizontalPoint I p ∈
            graphNeighborhood
              (transport f) (lambda * delta))) ∧
    ∀ p : ℝ × ℝ,
      p.1 ∈ I.realCenteredCarrier (1 / 16) →
        multiplicity F (lambda * delta) p =
          multiplicity transportedF (lambda * delta)
            (centeredHorizontalPoint I p)

/--
Transport a finite separated Katz--Tao family and its graph multiplicity from
a genuinely tiny physical interval to a global cinematic family.

The margin `4*(lambda*delta) ≤ I.length` guarantees that every graph-
neighborhood witness above the centered sixteenth stays inside the copied
jet interval in both directions.  Hence the Taylor tails create no spurious
multiplicity there.
-/
def CenteredTaylorFiniteGraphTransportStatement : Prop :=
  CenteredTaylorCinematicTransportStatement →
    ∀ K D C_KT lambda : ℝ,
      1 ≤ K →
      1 ≤ D →
      1 ≤ C_KT →
      1 ≤ lambda →
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval,
          0 < I.length →
          I.IsShort (12 * K) →
          ∀ delta : ℝ,
            0 < delta →
            4 * (lambda * delta) ≤ I.length →
            ∀ F : FiniteFunctionFamily,
              F.carrier ⊆ family →
              F.IsDeltaSeparated delta →
              F.HasKatzTaoBound delta C_KT →
              ∃ transport : C2Function → C2Function,
                CenteredTaylorFiniteGraphTransportData
                  K D C_KT lambda family I delta F transport

end Kakeya.Cinematic

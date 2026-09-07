import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientCardinalityRpowLinearizationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.LinearAmbientFineVolumeAssemblyInputs

/-!
# Fixed-ambient volume from a Proposition 26 cardinality bound

Compose ambient-cardinality `3/2`-power linearization with the ENNReal
fine-shading volume conversion.  The output retains one linear copy of the
fixed ambient cardinality and exposes the exact real local coefficient that
must later be absorbed.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def FixedAmbientRpowFineVolumeAssemblyStatement : Prop :=
  AmbientCardinalityRpowLinearizationStatement →
    LinearAmbientFineVolumeAssemblyStatement →
    ∀ {E : Set (ℝ × ℝ)}
      (fineCard ambientCard : ℕ)
      (prefactor cardUpper coefficient logTail area : ℝ),
      0 ≤ prefactor →
      0 ≤ cardUpper →
      (ambientCard : ℝ) ≤ cardUpper →
      0 ≤ coefficient →
      0 ≤ logTail →
      0 ≤ area →
      (fineCard : ℝ) ≤
        coefficient *
          Real.rpow
            (prefactor * (ambientCard : ℝ)) (3 / 2 : ℝ) *
          logTail →
      volume E ≤
        (fineCard : ENNReal) * ENNReal.ofReal area →
      volume E ≤
        ENNReal.ofReal
            ((coefficient * prefactor *
              Real.sqrt (prefactor * cardUpper) * logTail) * area) *
          ambientCard

end Kakeya.Cinematic

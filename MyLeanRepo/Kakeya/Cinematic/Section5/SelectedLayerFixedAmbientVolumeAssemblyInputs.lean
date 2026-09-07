import MyLeanRepo.Kakeya.Cinematic.Section5.FixedAmbientRpowFineVolumeAssemblyInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedLayerMassCancellationInputs

/-!
# Fixed-ambient volume with selected-layer cancellation

This interface keeps the PYZ Lemma 43 dyadic mass visible while composing a
cardinality estimate with the fixed-ambient `3/2`-power linearization.  The
only cancellation premise is the isolated pure real-algebra statement.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def SelectedLayerFixedAmbientVolumeAssemblyStatement : Prop :=
  SelectedLayerMassCancellationStatement →
    FixedAmbientRpowFineVolumeAssemblyStatement →
    ∀ {E : Set (ℝ × ℝ)}
      (fineCard ambientCard : ℕ)
      (prefactor cardUpper baseCoefficient logTail layerFactor
        parentArea fineArea layerMass : ℝ),
      0 ≤ prefactor →
      0 ≤ cardUpper →
      (ambientCard : ℝ) ≤ cardUpper →
      0 ≤ baseCoefficient →
      0 ≤ logTail →
      0 ≤ layerFactor →
      0 ≤ parentArea →
      0 ≤ fineArea →
      0 < layerMass →
      layerMass ≤ fineArea →
      (fineCard : ℝ) ≤
        (baseCoefficient *
            Real.rpow (parentArea / layerMass) (1 / 4 : ℝ)) *
          Real.rpow
            (prefactor * (ambientCard : ℝ)) (3 / 2 : ℝ) *
          logTail →
      volume E ≤
        (fineCard : ENNReal) *
          ENNReal.ofReal (layerFactor * layerMass) →
      volume E ≤
        ENNReal.ofReal
            (((baseCoefficient * prefactor *
                Real.sqrt (prefactor * cardUpper) * logTail) *
                layerFactor) *
              Real.rpow parentArea (1 / 4 : ℝ) *
              Real.rpow fineArea (3 / 4 : ℝ)) *
          ambientCard

end Kakeya.Cinematic

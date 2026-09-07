import MyLeanRepo.Kakeya.Cinematic.Section5.FixedAmbientRpowFineVolumeAssembly
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedLayerFixedAmbientVolumeAssemblyInputs

/-!
# Fixed-ambient volume with selected-layer cancellation
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem selected_layer_fixed_ambient_volume_assembly :
    SelectedLayerFixedAmbientVolumeAssemblyStatement := by
  intro hCancel hAssembly E fineCard ambientCard prefactor cardUpper
    baseCoefficient logTail layerFactor parentArea fineArea layerMass
    hprefactor hcardUpper hambient hbase hlogTail hlayerFactor
    hparentArea hfineArea hlayerMass hlayerFine hcard hvolume
  let interpolatedCoefficient : ℝ :=
    baseCoefficient *
      Real.rpow (parentArea / layerMass) (1 / 4 : ℝ)
  let layerArea : ℝ := layerFactor * layerMass
  have hratio_nonneg : 0 ≤ parentArea / layerMass :=
    div_nonneg hparentArea hlayerMass.le
  have hinterpolatedCoefficient :
      0 ≤ interpolatedCoefficient := by
    exact mul_nonneg hbase (Real.rpow_nonneg hratio_nonneg _)
  have hlayerArea : 0 ≤ layerArea :=
    mul_nonneg hlayerFactor hlayerMass.le
  have hraw :=
    hAssembly ambient_cardinality_rpow_linearization
      linear_ambient_fine_volume_assembly
      (E := E) fineCard ambientCard prefactor cardUpper
      interpolatedCoefficient logTail layerArea
      hprefactor hcardUpper hambient hinterpolatedCoefficient
      hlogTail hlayerArea hcard hvolume
  let coefficient : ℝ :=
    (baseCoefficient * prefactor *
        Real.sqrt (prefactor * cardUpper) * logTail) *
      layerFactor
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (prefactor * cardUpper) :=
    Real.sqrt_nonneg _
  have hcoefficient : 0 ≤ coefficient := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hbase hprefactor)
          hsqrt_nonneg)
        hlogTail)
      hlayerFactor
  have hcancelled :=
    hCancel coefficient parentArea fineArea layerMass
      hcoefficient hparentArea hfineArea hlayerMass hlayerFine
  have hreal :
      ((interpolatedCoefficient * prefactor *
          Real.sqrt (prefactor * cardUpper) * logTail) *
          layerArea) ≤
        ((baseCoefficient * prefactor *
            Real.sqrt (prefactor * cardUpper) * logTail) *
            layerFactor) *
          Real.rpow parentArea (1 / 4 : ℝ) *
          Real.rpow fineArea (3 / 4 : ℝ) := by
    dsimp only [interpolatedCoefficient, layerArea, coefficient] at hcancelled ⊢
    calc
      ((baseCoefficient *
            Real.rpow (parentArea / layerMass) (1 / 4 : ℝ)) *
          prefactor * Real.sqrt (prefactor * cardUpper) * logTail) *
          (layerFactor * layerMass) =
        ((baseCoefficient * prefactor *
            Real.sqrt (prefactor * cardUpper) * logTail) *
            layerFactor) *
          Real.rpow (parentArea / layerMass) (1 / 4 : ℝ) *
          layerMass := by ring
      _ ≤
        ((baseCoefficient * prefactor *
            Real.sqrt (prefactor * cardUpper) * logTail) *
            layerFactor) *
          Real.rpow parentArea (1 / 4 : ℝ) *
          Real.rpow fineArea (3 / 4 : ℝ) :=
        hcancelled
  exact hraw.trans <|
    mul_le_mul_right'
      (ENNReal.ofReal_le_ofReal hreal)
      (ambientCard : ENNReal)

end Kakeya.Cinematic

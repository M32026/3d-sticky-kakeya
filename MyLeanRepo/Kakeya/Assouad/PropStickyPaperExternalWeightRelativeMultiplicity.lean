import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRelativeMultiplicityStatements

/-!
# Target: relative source multiplicity after source-weight selection

Combine the old target multiplicity floor and final union-volume floor with
the old target mass upper bound, then absorb the weighted source-cardinality
loss and cancel the positive target-scale power.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_external_weight_relative_multiplicity :
    WZ2PaperExternalWeightRelativeMultiplicityStatement := by
  intro sourceScale targetScale sigma floorLoss strongLoss hscale _hscaleOne
    _hloss packedSource selectedSource packedShading selectedShading
    oldTarget finalTarget oldTargetShading finalTargetShading multiplicity
    h1 h2 h3 h4 h5 massConstant weight cardinalityLoss h6 hweight_ne_zero
    hweight_ne_top h7 h8 point
  have hmassVolume :
      (multiplicity : ENNReal) *
          MeasureTheory.volume oldTargetShading.union ≤
        oldTargetShading.mass :=
    multiplicity_floor_le_mass h3
  have hvolumeMono :
      MeasureTheory.volume finalTargetShading.union ≤
        MeasureTheory.volume oldTargetShading.union :=
    MeasureTheory.measure_mono h4
  have hfloorVolume :
      Kakeya.realRpowENN targetScale (sigma + floorLoss) ≤
        MeasureTheory.volume oldTargetShading.union :=
    h5.trans hvolumeMono
  have hfloorMass :
      (multiplicity : ENNReal) *
          Kakeya.realRpowENN targetScale (sigma + floorLoss) ≤
        oldTargetShading.mass := by
    calc
      (multiplicity : ENNReal) *
            Kakeya.realRpowENN targetScale (sigma + floorLoss)
          ≤ (multiplicity : ENNReal) *
              MeasureTheory.volume oldTargetShading.union := by
        gcongr
      _ ≤ oldTargetShading.mass := hmassVolume
  have hmassUpper :
      (2 * multiplicity : ENNReal) *
          Kakeya.realRpowENN targetScale (sigma + floorLoss) ≤
        (2 * massConstant) *
          Kakeya.realRpowENN targetScale 2 *
            packedSource.enncard := by
    calc
      (2 * multiplicity : ENNReal) *
            Kakeya.realRpowENN targetScale (sigma + floorLoss)
          = 2 *
              ((multiplicity : ENNReal) *
                Kakeya.realRpowENN targetScale (sigma + floorLoss)) := by
        ring
      _ ≤ 2 *
          (massConstant *
            Kakeya.realRpowENN targetScale 2 *
              packedSource.enncard) := by
        exact mul_le_mul_left' (hfloorMass.trans h6) 2
      _ = (2 * massConstant) *
          Kakeya.realRpowENN targetScale 2 *
            packedSource.enncard := by
        ring
  have hcardRetention :
      packedSource.enncard ≤
        weight⁻¹ * cardinalityLoss * selectedSource.enncard := by
    have h9 : weight⁻¹ * (weight * packedSource.enncard) ≤
        weight⁻¹ * (cardinalityLoss * selectedSource.enncard) :=
      mul_le_mul_left' h7 weight⁻¹
    have h10 : weight⁻¹ * weight = 1 :=
      ENNReal.inv_mul_cancel hweight_ne_zero hweight_ne_top
    have h11 : weight⁻¹ * (weight * packedSource.enncard) =
        packedSource.enncard := by
      rw [← mul_assoc, h10, one_mul]
    have h12 : weight⁻¹ * (cardinalityLoss * selectedSource.enncard) =
        weight⁻¹ * cardinalityLoss * selectedSource.enncard := by
      ring
    rw [h11, h12] at h9
    exact h9
  have hmassUpperSelected :
      (2 * multiplicity : ENNReal) *
          Kakeya.realRpowENN targetScale (sigma + floorLoss) ≤
        (2 * massConstant) * (weight⁻¹ * cardinalityLoss) *
          Kakeya.realRpowENN targetScale 2 *
            selectedSource.enncard := by
    calc
      (2 * multiplicity : ENNReal) *
            Kakeya.realRpowENN targetScale (sigma + floorLoss)
          ≤ (2 * massConstant) *
              Kakeya.realRpowENN targetScale 2 *
                packedSource.enncard := hmassUpper
      _ ≤ (2 * massConstant) *
              Kakeya.realRpowENN targetScale 2 *
                (weight⁻¹ * cardinalityLoss * selectedSource.enncard) := by
          gcongr
      _ = (2 * massConstant) * (weight⁻¹ * cardinalityLoss) *
              Kakeya.realRpowENN targetScale 2 *
                selectedSource.enncard := by
          ring
  have habsorbed :
      (2 * multiplicity : ENNReal) *
          Kakeya.realRpowENN targetScale (sigma + floorLoss) ≤
        Kakeya.realRpowENN targetScale (2 + floorLoss - strongLoss) *
          selectedSource.enncard := by
    calc
      (2 * multiplicity : ENNReal) *
            Kakeya.realRpowENN targetScale (sigma + floorLoss)
          ≤ (2 * massConstant) * (weight⁻¹ * cardinalityLoss) *
              Kakeya.realRpowENN targetScale 2 *
                selectedSource.enncard := hmassUpperSelected
      _ ≤ Kakeya.realRpowENN targetScale (-(strongLoss - floorLoss)) *
              Kakeya.realRpowENN targetScale 2 *
                selectedSource.enncard := by
          gcongr
      _ = Kakeya.realRpowENN targetScale (2 + floorLoss - strongLoss) *
              selectedSource.enncard := by
          have h_exp : Kakeya.realRpowENN targetScale (-(strongLoss - floorLoss)) *
                Kakeya.realRpowENN targetScale 2 =
              Kakeya.realRpowENN targetScale (2 + floorLoss - strongLoss) := by
            rw [← realRpowENN_add hscale (-(strongLoss - floorLoss)) 2]
            congr 1
            ring
          rw [h_exp]
          <;> ring
  have hfactor :
      Kakeya.realRpowENN targetScale (2 + floorLoss - strongLoss) =
        Kakeya.realRpowENN targetScale (sigma + floorLoss) *
          Kakeya.realRpowENN targetScale (2 - sigma - strongLoss) := by
    rw [← realRpowENN_add hscale (sigma + floorLoss) (2 - sigma - strongLoss)]
    congr 1
    ring
  have hscaleZero :
      Kakeya.realRpowENN targetScale (sigma + floorLoss) ≠ 0 := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hscale]
  have hscaleTop :
      Kakeya.realRpowENN targetScale (sigma + floorLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hmultiplicity :
      (2 * multiplicity : ENNReal) ≤
        Kakeya.realRpowENN targetScale (2 - sigma - strongLoss) *
          selectedSource.enncard := by
    have hwithFactor :
        Kakeya.realRpowENN targetScale (sigma + floorLoss) *
            (2 * multiplicity : ENNReal) ≤
          Kakeya.realRpowENN targetScale (sigma + floorLoss) *
            (Kakeya.realRpowENN targetScale (2 - sigma - strongLoss) *
              selectedSource.enncard) := by
      calc
        Kakeya.realRpowENN targetScale (sigma + floorLoss) *
              (2 * multiplicity : ENNReal)
            = (2 * multiplicity : ENNReal) *
                Kakeya.realRpowENN targetScale (sigma + floorLoss) := by
              ring
        _ ≤ Kakeya.realRpowENN targetScale (2 + floorLoss - strongLoss) *
                selectedSource.enncard := habsorbed
        _ = (Kakeya.realRpowENN targetScale (sigma + floorLoss) *
                Kakeya.realRpowENN targetScale (2 - sigma - strongLoss)) *
              selectedSource.enncard := by
            rw [← hfactor]
        _ = Kakeya.realRpowENN targetScale (sigma + floorLoss) *
                (Kakeya.realRpowENN targetScale (2 - sigma - strongLoss) *
                  selectedSource.enncard) := by
            ring
    exact (ENNReal.mul_le_mul_iff_right hscaleZero hscaleTop).mp hwithFactor
  have hpointBound :
      (selectedShading.pointMultiplicity point : ENNReal) ≤
        (2 * multiplicity : ENNReal) :=
    (h1 point).trans (h2 point)
  exact hpointBound.trans hmultiplicity

end Kakeya.Assouad

end

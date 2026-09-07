import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Two-scale power arithmetic for the final component floors

The fine component uses the lower endpoint of the paper scale window, while
the coarse component uses the upper endpoint.  Both products are bounded by
the same power of the source scale.
-/

noncomputable section

namespace Kakeya.Assouad

private lemma finalComponent_realRpowENN_add
    {scale : ℝ} (hscale : 0 < scale) (first second : ℝ) :
    Kakeya.realRpowENN scale (first + second) =
      Kakeya.realRpowENN scale first *
        Kakeya.realRpowENN scale second := by
  simp only [Kakeya.realRpowENN]
  rw [show
    Real.rpow scale (first + second) =
      Real.rpow scale first * Real.rpow scale second from
        Real.rpow_add hscale first second]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg hscale.le first)

private lemma finalComponent_realRpowENN_div_mul
    {delta rho exponent : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho) :
    Kakeya.realRpowENN (delta / rho) exponent *
        Kakeya.realRpowENN rho exponent =
      Kakeya.realRpowENN delta exponent := by
  have hproduct :
      (delta / rho) * rho = delta := by
    field_simp [hrho.ne']
  calc
    Kakeya.realRpowENN (delta / rho) exponent *
          Kakeya.realRpowENN rho exponent =
        Kakeya.realRpowENN ((delta / rho) * rho) exponent := by
      rw [realRpowENN_mul (div_pos hdelta hrho) hrho]
    _ = Kakeya.realRpowENN delta exponent := by
      rw [hproduct]

private theorem fine_window_negative_power
    {delta rho outputLoss gap : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hlower : Real.rpow delta (1 - outputLoss) ≤ rho)
    (hgap : 0 ≤ gap) :
    Kakeya.realRpowENN rho (-gap) ≤
      Kakeya.realRpowENN delta (-(1 - outputLoss) * gap) := by
  apply ENNReal.ofReal_mono
  have hbasePos :
      0 < Real.rpow delta (1 - outputLoss) :=
    Real.rpow_pos_of_pos hdelta _
  have hpow :
      Real.rpow delta ((1 - outputLoss) * gap) ≤
        Real.rpow rho gap := by
    calc
      Real.rpow delta ((1 - outputLoss) * gap) =
          Real.rpow (Real.rpow delta (1 - outputLoss)) gap :=
        Real.rpow_mul hdelta.le _ _
      _ ≤ Real.rpow rho gap :=
        Real.rpow_le_rpow hbasePos.le hlower hgap
  have hinv :
      (Real.rpow rho gap)⁻¹ ≤
        (Real.rpow delta ((1 - outputLoss) * gap))⁻¹ :=
    (inv_le_inv₀
      (Real.rpow_pos_of_pos hrho gap)
      (Real.rpow_pos_of_pos hdelta
        ((1 - outputLoss) * gap))).2 hpow
  have hExponent :
      -(1 - outputLoss) * gap =
        -((1 - outputLoss) * gap) := by ring
  rw [hExponent]
  simpa [Kakeya.realRpowENN, Real.rpow_neg hdelta.le,
    Real.rpow_neg hrho.le] using hinv

private theorem coarse_window_positive_power
    {delta rho outputLoss gap : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hupper : rho ≤ Real.rpow delta outputLoss)
    (hgap : 0 ≤ gap) :
    Kakeya.realRpowENN rho gap ≤
      Kakeya.realRpowENN delta (outputLoss * gap) := by
  apply ENNReal.ofReal_mono
  calc
    Real.rpow rho gap ≤
        Real.rpow (Real.rpow delta outputLoss) gap :=
      Real.rpow_le_rpow hrho.le hupper hgap
    _ = Real.rpow delta (outputLoss * gap) :=
      (Real.rpow_mul hdelta.le _ _).symm

theorem wz2_paper_final_fine_component_scale
    {delta rho sigma sourceLoss capLoss componentFloorLoss outputLoss : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hlower : Real.rpow delta (1 - outputLoss) ≤ rho)
    (hLoss : 0 ≤ componentFloorLoss + capLoss) :
    Kakeya.realRpowENN (delta / rho)
          (2 - sigma + componentFloorLoss) *
        Kakeya.realRpowENN rho
          (2 - sigma - capLoss) *
        Kakeya.realRpowENN delta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN delta
        (2 - sourceLoss - capLoss +
          outputLoss * (componentFloorLoss + capLoss)) := by
  let fineExponent := 2 - sigma + componentFloorLoss
  let coarseExponent := 2 - sigma - capLoss
  let gap := componentFloorLoss + capLoss
  have hCoarseSplit :
      Kakeya.realRpowENN rho coarseExponent =
        Kakeya.realRpowENN rho fineExponent *
          Kakeya.realRpowENN rho (-gap) := by
    rw [← finalComponent_realRpowENN_add hrho]
    congr 1
    dsimp only [fineExponent, coarseExponent, gap]
    ring
  have hWindow :
      Kakeya.realRpowENN rho (-gap) ≤
        Kakeya.realRpowENN delta (-(1 - outputLoss) * gap) :=
    fine_window_negative_power hdelta hrho hlower hLoss
  calc
    Kakeya.realRpowENN (delta / rho) fineExponent *
          Kakeya.realRpowENN rho coarseExponent *
          Kakeya.realRpowENN delta (sigma - sourceLoss) =
        (Kakeya.realRpowENN (delta / rho) fineExponent *
            Kakeya.realRpowENN rho fineExponent) *
          Kakeya.realRpowENN rho (-gap) *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
      rw [hCoarseSplit]
      ring
    _ =
        Kakeya.realRpowENN delta fineExponent *
          Kakeya.realRpowENN rho (-gap) *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
      rw [finalComponent_realRpowENN_div_mul hdelta hrho]
    _ ≤
        Kakeya.realRpowENN delta fineExponent *
          Kakeya.realRpowENN delta (-(1 - outputLoss) * gap) *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
      gcongr
    _ =
        Kakeya.realRpowENN delta
          (2 - sourceLoss - capLoss +
            outputLoss * (componentFloorLoss + capLoss)) := by
      rw [← finalComponent_realRpowENN_add hdelta,
        ← finalComponent_realRpowENN_add hdelta]
      dsimp only [fineExponent, gap]
      congr 1
      ring

theorem wz2_paper_final_coarse_component_scale
    {delta rho sigma sourceLoss capLoss componentFloorLoss outputLoss : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hupper : rho ≤ Real.rpow delta outputLoss)
    (hLoss : 0 ≤ componentFloorLoss + capLoss) :
    Kakeya.realRpowENN rho
          (2 - sigma + componentFloorLoss) *
        Kakeya.realRpowENN (delta / rho)
          (2 - sigma - capLoss) *
        Kakeya.realRpowENN delta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN delta
        (2 - sourceLoss - capLoss +
          outputLoss * (componentFloorLoss + capLoss)) := by
  let coarseFloorExponent := 2 - sigma + componentFloorLoss
  let fiberExponent := 2 - sigma - capLoss
  let gap := componentFloorLoss + capLoss
  have hCoarseSplit :
      Kakeya.realRpowENN rho coarseFloorExponent =
        Kakeya.realRpowENN rho fiberExponent *
          Kakeya.realRpowENN rho gap := by
    rw [← finalComponent_realRpowENN_add hrho]
    congr 1
    dsimp only [coarseFloorExponent, fiberExponent, gap]
    ring
  have hWindow :
      Kakeya.realRpowENN rho gap ≤
        Kakeya.realRpowENN delta (outputLoss * gap) :=
    coarse_window_positive_power hdelta hrho hupper hLoss
  calc
    Kakeya.realRpowENN rho coarseFloorExponent *
          Kakeya.realRpowENN (delta / rho) fiberExponent *
          Kakeya.realRpowENN delta (sigma - sourceLoss) =
        (Kakeya.realRpowENN (delta / rho) fiberExponent *
            Kakeya.realRpowENN rho fiberExponent) *
          Kakeya.realRpowENN rho gap *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
      rw [hCoarseSplit]
      ring
    _ =
        Kakeya.realRpowENN delta fiberExponent *
          Kakeya.realRpowENN rho gap *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
      rw [finalComponent_realRpowENN_div_mul hdelta hrho]
    _ ≤
        Kakeya.realRpowENN delta fiberExponent *
          Kakeya.realRpowENN delta (outputLoss * gap) *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
      gcongr
    _ =
        Kakeya.realRpowENN delta
          (2 - sourceLoss - capLoss +
            outputLoss * (componentFloorLoss + capLoss)) := by
      rw [← finalComponent_realRpowENN_add hdelta,
        ← finalComponent_realRpowENN_add hdelta]
      dsimp only [fiberExponent, gap]
      congr 1
      ring

end Kakeya.Assouad

end

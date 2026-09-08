import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.GridFrostmanTransfer

/-!
# Reanchored-parent volume comparison

An ordinary tube of radius `8*A*rho` has volume at most `1280` times the
volume of the centered `A`-dilation of an ordinary `rho`-tube.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Fixed volume comparison used by the reanchored Frostman transfer. -/
theorem pureWZ2_reanchored_parent_volume_ratio
    {A rho : ℝ}
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (reanchoredParent : Kakeya.DeltaTube (8 * A * rho))
    (originalParent : Kakeya.DeltaTube rho) :
    volume reanchoredParent.carrier ≤
      (1280 : ENNReal) *
        volume
          (wz2PaperCenteredDilatedCarrier A originalParent) := by
  have hreanchoredVolume :
      volume reanchoredParent.carrier =
        Kakeya.deltaTubeVolume (8 * A * rho) := by
    let canonical : Kakeya.DeltaTube (8 * A * rho) :=
      {
        base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    exact
      Kakeya.Streamlined.tube_volume_eq
        reanchoredParent canonical
  have horiginalVolume :
      volume originalParent.carrier =
        Kakeya.deltaTubeVolume rho := by
    let canonical : Kakeya.DeltaTube rho :=
      {
        base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    exact
      Kakeya.Streamlined.tube_volume_eq
        originalParent canonical
  have hgrid :=
    grid_tube_volume_ratio
      (A := 4 * A) (ρ := rho)
      (by nlinarith) hrho hrhoOne
  rw [show 2 * (4 * A) * rho = 8 * A * rho by ring] at hgrid
  rw [hreanchoredVolume]
  rw [wz2_paper_centeredDilatedCarrier_volume,
    abs_of_nonneg (show 0 ≤ A by linarith),
    horiginalVolume]
  have hfactor :
      ENNReal.ofReal ((4 * A) ^ 3) =
        (64 : ENNReal) * ENNReal.ofReal (A ^ 3) := by
    rw [show (4 * A) ^ 3 = 64 * A ^ 3 by ring]
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hfactor] at hgrid
  calc
    Kakeya.deltaTubeVolume (8 * A * rho)
        ≤
      (20 : ENNReal) *
        ((64 : ENNReal) * ENNReal.ofReal (A ^ 3)) *
        Kakeya.deltaTubeVolume rho := hgrid
    _ =
      (1280 : ENNReal) *
        (ENNReal.ofReal (A ^ 3) *
          Kakeya.deltaTubeVolume rho) := by
      norm_num
      ring

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperConvexWolffCardinalityStatements
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Paper-tube cardinality floor from normalized Convex-Wolff

This is the conditional composition of the two independently frozen leaves:

* finite-capsule geometry for one cropped `L₃` paper tube;
* the normalized Convex-Wolff cardinality core.

Once those providers are comparator-validated, the theorem gives the paper's
explicit reciprocal-volume cardinality floor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2PaperConvexWolff_cardinality_floor
    (hgeometry : WZ2PaperTubeCarrierGeometryStatement)
    (hcardinality : WZ2PaperConvexWolffCardinalityCoreStatement)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hnonempty : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (hcwa : WZ2PaperConvexWolffBound family C) :
    1 ≤
      C *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) *
        family.enncard := by
  apply hcardinality hnonempty hcwa
  · intro index
    exact
      (wz2PaperTubeCarrier_convex_and_volume_quadratic
        hgeometry hdelta hdeltaSmall
        (family.tube index) (hline index)).1
  · intro index
    exact
      (wz2PaperTubeCarrier_convex_and_volume_quadratic
        hgeometry hdelta hdeltaSmall
        (family.tube index) (hline index)).2

/--
After absorbing the absolute carrier-volume constant into one additional loss
power, normalized Convex-Wolff gives the cardinality lower bound used in WZ2
Lemma 3.3.
-/
theorem wz2PaperConvexWolff_cardinality_lower
    (hgeometry : WZ2PaperTubeCarrierGeometryStatement)
    (hcardinality : WZ2PaperConvexWolffCardinalityCoreStatement)
    {delta strongLoss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hnonempty : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (hcwa :
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-strongLoss)))
    (habsorb :
      55296 * Kakeya.deltaTubeVolume 1 ≤
        Kakeya.realRpowENN delta (-strongLoss)) :
    Kakeya.realRpowENN delta (-2 + 2 * strongLoss) ≤
      family.enncard := by
  have hfloor :=
    wz2PaperConvexWolff_cardinality_floor
      hgeometry hcardinality hdelta hdeltaSmall
      hnonempty hline hcwa
  have hpowerBound :
      1 ≤
        (Kakeya.realRpowENN delta (-strongLoss) *
          Kakeya.realRpowENN delta (-strongLoss) *
          Kakeya.realRpowENN delta 2) *
          family.enncard := by
    calc
      1 ≤
          Kakeya.realRpowENN delta (-strongLoss) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2) *
            family.enncard := hfloor
      _ =
          (Kakeya.realRpowENN delta (-strongLoss) *
            (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2) *
            family.enncard := by ring
      _ ≤
          (Kakeya.realRpowENN delta (-strongLoss) *
            Kakeya.realRpowENN delta (-strongLoss) *
            Kakeya.realRpowENN delta 2) *
            family.enncard := by
        gcongr
  let power :=
    Kakeya.realRpowENN delta (2 - 2 * strongLoss)
  have hpowerEq :
      Kakeya.realRpowENN delta (-strongLoss) *
          Kakeya.realRpowENN delta (-strongLoss) *
          Kakeya.realRpowENN delta 2 =
        power := by
    have hfirst :
        Kakeya.realRpowENN delta (-strongLoss) *
            Kakeya.realRpowENN delta (-strongLoss) =
          Kakeya.realRpowENN delta
            ((-strongLoss) + (-strongLoss)) :=
      (realRpowENN_add hdelta
        (-strongLoss) (-strongLoss)).symm
    have hsecond :
        Kakeya.realRpowENN delta
              ((-strongLoss) + (-strongLoss)) *
            Kakeya.realRpowENN delta 2 =
          Kakeya.realRpowENN delta
            (((-strongLoss) + (-strongLoss)) + 2) :=
      (realRpowENN_add hdelta
        ((-strongLoss) + (-strongLoss)) 2).symm
    calc
      Kakeya.realRpowENN delta (-strongLoss) *
            Kakeya.realRpowENN delta (-strongLoss) *
            Kakeya.realRpowENN delta 2 =
          Kakeya.realRpowENN delta
            ((-strongLoss) + (-strongLoss)) *
            Kakeya.realRpowENN delta 2 := by
        rw [hfirst]
      _ = Kakeya.realRpowENN delta
            (((-strongLoss) + (-strongLoss)) + 2) := by
        exact hsecond
      _ = power := by
        change
          Kakeya.realRpowENN delta
              (((-strongLoss) + (-strongLoss)) + 2) =
            Kakeya.realRpowENN delta (2 - 2 * strongLoss)
        congr 1
        ring
  rw [hpowerEq] at hpowerBound
  have hpowerPos : 0 < power := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos hdelta _
  have hpowerTop : power ≠ ⊤ := by
    simp [power, Kakeya.realRpowENN]
  have hinverseBound : power⁻¹ ≤ family.enncard := by
    calc
      power⁻¹ = 1 * power⁻¹ := by simp
      _ ≤ (power * family.enncard) * power⁻¹ := by
        gcongr
      _ = family.enncard * (power * power⁻¹) := by ring
      _ = family.enncard := by
        rw [ENNReal.mul_inv_cancel hpowerPos.ne' hpowerTop]
        simp
  have hpowerInverse :
      power⁻¹ =
        Kakeya.realRpowENN delta (-2 + 2 * strongLoss) := by
    have hrealPos :
        0 < Real.rpow delta (2 - 2 * strongLoss) :=
      Real.rpow_pos_of_pos hdelta _
    calc
      power⁻¹ =
          ENNReal.ofReal
            ((Real.rpow delta (2 - 2 * strongLoss))⁻¹) := by
        dsimp only [power, Kakeya.realRpowENN]
        exact (ENNReal.ofReal_inv_of_pos hrealPos).symm
      _ = ENNReal.ofReal
            (Real.rpow delta (-(2 - 2 * strongLoss))) := by
        exact congrArg ENNReal.ofReal
          (Real.rpow_neg hdelta.le
            (2 - 2 * strongLoss)).symm
      _ = Kakeya.realRpowENN delta
            (-2 + 2 * strongLoss) := by
        congr 2
        ring
  rw [hpowerInverse] at hinverseBound
  exact hinverseBound

end Kakeya.Assouad

end

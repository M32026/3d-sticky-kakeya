import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParentLevelWholeFiberSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Uniform upper bound for actual-fiber shaded weights

Every source carrier is contained in one cropped paper tube.  The quadratic
paper-carrier bound therefore controls the shaded mass of each complete
actual fiber by the same per-tube constant times its cardinality.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem pureWZ2_actual_fiber_shaded_mass_upper
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily actual}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (fineLine : WZ1PaperIsLineClass fine)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) :
    pureWZ2ActualFiberShadedMass shading parent ≤
      ((55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta 2) *
        wz2PaperOrdinaryFullFiberCount fine coarse parent := by
  let fiber :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent)
  let fiberShading := restrictPaperShading fiber shading
  have hMass :
      pureWZ2ActualFiberShadedMass shading parent =
        fiberShading.mass := by
    rw [restrictPaperShading_mass]
    let equivalence :
        Fin fiber.family.card ≃
          wz2PaperOrdinaryFullFiberIndices fine coarse parent :=
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent)
        |>.orderIsoOfFin rfl |>.toEquiv
    exact
      ((Fintype.sum_equiv equivalence
          (fun index : Fin fiber.family.card =>
            volume (shading.carrier (fiber.embedding index)))
          (fun source :
            wz2PaperOrdinaryFullFiberIndices fine coarse parent =>
            volume (shading.carrier source.1))
          (fun _ => rfl)).trans
        (Finset.sum_coe_sort
          (wz2PaperOrdinaryFullFiberIndices fine coarse parent)
          (fun source => volume (shading.carrier source)))).symm
  rw [hMass]
  have hUpper :=
    wz2_paper_shading_mass_upper
      hdelta hdeltaSmall
      (fineLine.subfamily fiber) fiberShading
  have hCard :
      fiber.family.enncard =
        wz2PaperOrdinaryFullFiberCount fine coarse parent := by
    rfl
  calc
    fiberShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 *
          fiber.family.enncard := hUpper
    _ =
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2) *
          wz2PaperOrdinaryFullFiberCount fine coarse parent := by
      rw [hCard]

end Kakeya.Assouad

end

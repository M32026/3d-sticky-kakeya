import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume

/-!
# Vacuity in the frozen dense cubicalization interface

The density threshold in `pureWZ2DenseCubicalization` vanishes when the
ordinary source set is empty.  Consequently every grid cube fully contained
in the cropped paper carrier is selected, despite carrying no ordinary source
mass.  This is the minimal obstruction to recovering an ordinary critical
witness from an arbitrary frozen normalization certificate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem pureWZ2DenseCubicalization_empty_source
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    pureWZ2DenseCubicalization tube ∅ =
      {point |
        wz1PaperGridCube delta
            (wz1PaperGridIndex delta point) ⊆
          wz1PaperTubeCarrier tube} := by
  ext point
  simp [pureWZ2DenseCubicalization]

theorem wz1PaperGridCube_subset_denseCubicalization_empty
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (cell : ℤ × ℤ × ℤ)
    (cellSubset :
      wz1PaperGridCube delta cell ⊆
        wz1PaperTubeCarrier tube) :
    wz1PaperGridCube delta cell ⊆
      pureWZ2DenseCubicalization tube ∅ := by
  intro point pointCell
  rw [pureWZ2DenseCubicalization_empty_source]
  have pointIndex :
      wz1PaperGridIndex delta point = cell :=
    (mem_wz1PaperGridCube delta cell point).mp pointCell
  simpa [pointIndex] using cellSubset

theorem pureWZ2DenseCubicalization_empty_source_volume_pos
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (cell : ℤ × ℤ × ℤ)
    (cellSubset :
      wz1PaperGridCube delta cell ⊆
        wz1PaperTubeCarrier tube) :
    0 <
      volume (pureWZ2DenseCubicalization tube ∅) := by
  exact
    (wz1PaperGridCube_volume_pos hdelta cell).trans_le
      (measure_mono
        (wz1PaperGridCube_subset_denseCubicalization_empty
          tube cell cellSubset))

end Kakeya.Assouad

end

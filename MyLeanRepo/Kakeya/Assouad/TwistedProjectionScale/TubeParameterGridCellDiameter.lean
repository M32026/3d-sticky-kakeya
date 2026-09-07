import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridCellDiameterStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTree

namespace Kakeya.Assouad

theorem tube_parameter_grid_cell_diameter :
    TubeParameterGridCellDiameterStatement := by
  intro base level hbase parameters cell hcell first hfirst second hsecond
    coordinate
  rcases Finset.mem_image.mp hcell with ⟨point, hpoint, rfl⟩
  have hfirst_idx :
      tubeParameterGridIndex base level first =
        tubeParameterGridIndex base level point :=
    (Finset.mem_filter.mp hfirst).2
  have hsecond_idx :
      tubeParameterGridIndex base level second =
        tubeParameterGridIndex base level point :=
    (Finset.mem_filter.mp hsecond).2
  have h_eq :
      tubeParameterGridIndex base level first =
        tubeParameterGridIndex base level second :=
    hfirst_idx.trans hsecond_idx.symm
  have hfloor :
      ⌊first coordinate * (base ^ level : ℝ)⌋ =
        ⌊second coordinate * (base ^ level : ℝ)⌋ :=
    congrFun h_eq coordinate
  have hM_pos : 0 < (base ^ level : ℝ) := by
    positivity
  have h_main :
      |first coordinate - second coordinate| <
        1 / (base ^ level : ℝ) :=
    same_floor_abs_sub_lt_one_div hM_pos hfloor
  simpa [one_div] using h_main

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridData.GridAssembly

/-!
# Closed fixed-depth power-grid construction
-/

namespace Kakeya.Streamlined.RandomTranslation.WithShading

theorem fixed_depth_power_grid_data :
    FixedDepthPowerGridDataStatement := by
  intro N hN
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro delta hδ_pos hδ_le
  exact fixed_depth_power_grid_aux N hN delta hδ_pos (by linarith)

end Kakeya.Streamlined.RandomTranslation.WithShading

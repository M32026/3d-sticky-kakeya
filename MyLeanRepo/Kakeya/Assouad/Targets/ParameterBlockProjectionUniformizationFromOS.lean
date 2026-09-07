import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionUniformizationFromOSStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCorridor
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridLevelSelection
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellThickening
import MyLeanRepo.Kakeya.Assouad.Targets.AssignedCurveProjectionContainment
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicShearCorridorTransfer
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridCinematicCorridorCount
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicCellSelection

/-!
WZ2 Proposition 7.1: assemble the same-family projection-uniform continuation
from the completed projected-fiber OS preparation, occupied-cell system,
local-block corridor, and cinematic globalization theorems.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

theorem parameter_block_projection_uniformization_from_os :
    ParameterBlockProjectionUniformizationFromOSStatement := by
  intro hArithmetic hPrune hPreparation hLevelSystem hCorridor hGlobalization
  intro epsilon rhoMax eta hepsilon hepsilon_small
    hrhoMax hrhoMax_one hrhoMax_lower heta heta_small
  rcases hPreparation eta heta with
    ⟨base, hbase, deltaPreparation, hdeltaPreparation,
      hdeltaPreparation_one, hPrepare⟩
  rcases hArithmetic base hbase epsilon eta
      hepsilon hepsilon_small heta heta_small with
    ⟨deltaArithmetic, hdeltaArithmetic,
      hdeltaArithmetic_one, hArithmeticAt⟩
  let delta₀ := min deltaPreparation deltaArithmetic
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ < 1 :=
    (min_le_left _ _).trans_lt hdeltaPreparation_one
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le
    F hF_nonempty hF_vertical hF_bounds
    C hC_one hC_top hC_bound hF_frostman
    Y hY_dense hY_slab f hf hf_zero
  have hdelta_prep : delta ≤ deltaPreparation :=
    hdelta_le.trans (min_le_left _ _)
  have hdelta_arithmetic : delta ≤ deltaArithmetic :=
    hdelta_le.trans (min_le_right _ _)
  have hdelta_one : delta ≤ 1 :=
    hdelta_le.trans hdelta₀_one.le
  rcases hPrepare delta hdelta hdelta_prep
      F hF_nonempty hF_vertical hF_bounds
      Y hY_dense hY_slab f hf hf_zero with
    ⟨prepared, hprepared_base⟩
  let globalShading := prepared.density.globalShading
  rcases hPrune delta (4 * eta) hdelta hdelta_one
      (by positivity) F globalShading
      prepared.density.density with
    ⟨fullShading, hfull_sub, hfull_mass, _hfull_dense,
      hfull_per_tube, hfull_whole⟩
  refine ⟨{
    globalShading := globalShading
    subshading := prepared.density.subshading
    density := prepared.density.density
    slab := prepared.density.slab
    fullShading := fullShading
    full_subshading := hfull_sub
    full_whole := hfull_whole
    full_mass := hfull_mass
    full_per_tube := hfull_per_tube
    globalize := ?_
  }⟩
  intro c0 windowedShading hwindow_sub _hwindow_mass
    _hwindow_whole hwindow_c
  dsimp only
  intro clustered localBlock representatives amplification pullback
  let rho := localBlock.blockScale
  have hrho : 0 < rho := localBlock.blockScale_pos
  have hdelta_rho : delta ≤ rho := localBlock.fine_le_block
  have hrho_small : rho ≤ 1 / 100 := by
    dsimp only [rho]
    linarith [localBlock.blockScale_small]
  have hrho_one : rho ≤ 1 := hrho_small.trans (by norm_num)
  have hrho_max : rho ≤ rhoMax :=
    hrho_small.trans hrhoMax_lower
  have hwindow_slab :
      windowedShading.union ⊆ horizontalSlab 0 1 := by
    have h1 : windowedShading.union ⊆ fullShading.union :=
      IsSubshading.union_subset hwindow_sub
    have h2 : fullShading.union ⊆ globalShading.union :=
      IsSubshading.union_subset hfull_sub
    exact h1.trans (h2.trans prepared.density.slab)
  have hF_c : ∀ i : Fin F.card, |(tubeParams i).c| ≤ 2 :=
    fun i => (hF_bounds i).2.2.1
  let fullLocal :=
    parameterLocalBlockShading clustered localBlock.sourcePoints
  have hfullLocal_sub : IsSubshading fullLocal fullLocal := by
    intro i
    exact Set.Subset.rfl
  have hCorridorFull :=
    hCorridor
      assigned_curve_projection_containment_from_vertical_chart
      cinematic_shear_corridor_transfer
      hdelta hdelta_one F hF_vertical hF_c
      windowedShading hwindow_slab C
      (ENNReal.ofReal (delta / 8) *
        Kakeya.realRpowENN delta (5 * eta))
      clustered epsilon localBlock f hf hf_zero
      fullLocal hfullLocal_sub
  let g := parameterLocalBlockCentralCurve localBlock f
  let localSet : Set Point2 := twistedUnion pullback.shading f
  let corridorRadius : ℝ := 30100 * rho
  have hlocal_full :
      localSet ⊆ twistedUnion fullLocal f := by
    exact
      parameterLocalRepresentative_twisted_subset_local
        representatives pullback.shading pullback.subshading f
  have hlocal_corridor :
      localSet ⊆
        Metric.cthickening corridorRadius
          (cinematicExtensionGraph g) := by
    dsimp only [corridorRadius, rho, g]
    exact hlocal_full.trans hCorridorFull.1
  have hg_lipschitz :
      LipschitzOnWith (131 : NNReal) g.extension
        (Set.Icc (0 : ℝ) 1) := by
    dsimp only [g]
    exact hCorridorFull.2
  have hlocal_global :
      localSet ⊆ twistedUnion globalShading f := by
    have hrepresentative :
        pullback.shading.union ⊆ fullLocal.union :=
      parameterLocalRepresentative_union_subset_local
        representatives pullback.shading pullback.subshading
    have hlocal_window :
        fullLocal.union ⊆ windowedShading.union :=
      localBlock.local_union_subset
    have hwindow_full :
        windowedShading.union ⊆ fullShading.union :=
      IsSubshading.union_subset hwindow_sub
    have hfull_global :
        fullShading.union ⊆ globalShading.union :=
      IsSubshading.union_subset hfull_sub
    have hunion :
        pullback.shading.union ⊆ globalShading.union :=
      hrepresentative.trans
        (hlocal_window.trans
          (hwindow_full.trans hfull_global))
    intro point hpoint
    rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, hunion hsourcePoint, rfl⟩
  rcases hLevelSystem
      projected_fiber_grid_level_selection
      projected_fiber_os_cell_thickening
      hdelta F Y f prepared rho hrho hdelta_rho hrho_one with
    ⟨level, ⟨cellSystem⟩⟩
  let radiusBlocks :=
    parameterBlockProjectionRadiusBlocks base
  have hbase_pos : (0 : ℝ) < prepared.base := by
    exact_mod_cast
      (show 0 < prepared.base from
        lt_of_lt_of_le (by norm_num) prepared.base_ge_three)
  have hterminal :
      ((prepared.base ^ prepared.levels : ℝ)⁻¹) <
        (prepared.base : ℝ) * rho := by
    calc
      ((prepared.base ^ prepared.levels : ℝ)⁻¹)
          < (prepared.base : ℝ) * delta :=
        prepared.mesh_upper
      _ ≤ (prepared.base : ℝ) * rho := by
        gcongr
  have hscaled_mesh :
      (30100 + 2 * (prepared.base : ℝ)) * rho <
        (30100 + 2 * (prepared.base : ℝ)) *
          ((prepared.base : ℝ) *
            ((prepared.base ^ level : ℝ)⁻¹)) := by
    gcongr
    exact cellSystem.rho_lt_coarse_mesh
  have hexpanded_raw :
      projectedFiberOSCinematicExpandedRadius
          prepared corridorRadius <
        ((30100 + 2 * (prepared.base : ℝ)) *
          (prepared.base : ℝ)) *
            ((prepared.base ^ level : ℝ)⁻¹) := by
    simp only [projectedFiberOSCinematicExpandedRadius,
      corridorRadius, rho]
    nlinarith
  have hradius_cast :
      (radiusBlocks : ℝ) =
        (30100 + 2 * (prepared.base : ℝ)) *
            (prepared.base : ℝ) + 1 := by
    simp [radiusBlocks, parameterBlockProjectionRadiusBlocks,
      hprepared_base]
  have hmesh_pos :
      0 < ((prepared.base ^ level : ℝ)⁻¹) := by
    positivity
  have hexpanded :
      projectedFiberOSCinematicExpandedRadius
          prepared corridorRadius ≤
        (radiusBlocks : ℝ) *
          ((prepared.base ^ level : ℝ)⁻¹) := by
    calc
      projectedFiberOSCinematicExpandedRadius
          prepared corridorRadius
          ≤ ((30100 + 2 * (prepared.base : ℝ)) *
              (prepared.base : ℝ)) *
                ((prepared.base ^ level : ℝ)⁻¹) :=
        hexpanded_raw.le
      _ ≤
          (((30100 + 2 * (prepared.base : ℝ)) *
              (prepared.base : ℝ)) + 1) *
                ((prepared.base ^ level : ℝ)⁻¹) := by
        gcongr
        norm_num
      _ =
          (radiusBlocks : ℝ) *
            ((prepared.base ^ level : ℝ)⁻¹) := by
        rw [hradius_cast]
  let localVolume : ENNReal := volume localSet
  let cellFactor : ENNReal :=
    4 *
      (projectedFiberOSCinematicCellBound
        prepared.base level 131 radiusBlocks : ENNReal) *
      projectedFiberOSPreparedCellThickeningBound prepared rho
  have hglobalization :
      localVolume *
          volume
            (Metric.cthickening rho
              (twistedUnion globalShading f)) ≤
        cellFactor * volume (twistedUnion globalShading f) := by
    exact
      hGlobalization
        planar_grid_cinematic_corridor_count
        projected_fiber_os_cinematic_cell_selection
        F Y f prepared level cellSystem g
        131 radiusBlocks hg_lipschitz
        corridorRadius (by positivity) hexpanded
        localSet hlocal_global hlocal_corridor
        localVolume le_rfl
  have harithmetic :
      Kakeya.realRpowENN (delta / rho) epsilon *
          cellFactor ≤ localVolume := by
    have h :=
      hArithmeticAt delta hdelta hdelta_arithmetic
        F Y f prepared hprepared_base
        windowedShading C
        (ENNReal.ofReal (delta / 8) *
          Kakeya.realRpowENN delta (5 * eta))
        clustered localBlock representatives amplification pullback
        level cellSystem
    dsimp only [rho, cellFactor, localVolume, localSet, radiusBlocks]
    simpa only [parameterBlockProjectionWorkingEpsilon, mul_assoc] using h
  have hcellFactor_pos : 0 < cellFactor := by
    have hcellCount :
        0 <
          projectedFiberOSCinematicCellBound
            prepared.base level 131 radiusBlocks := by
      simp only [projectedFiberOSCinematicCellBound]
      positivity
    have hcellCountENN :
        (0 : ENNReal) <
          (projectedFiberOSCinematicCellBound
            prepared.base level 131 radiusBlocks : ENNReal) := by
      exact_mod_cast hcellCount
    have hthickening :
        0 <
          projectedFiberOSPreparedCellThickeningBound
            prepared rho := by
      simp only [projectedFiberOSPreparedCellThickeningBound]
      apply ENNReal.ofReal_pos.mpr
      positivity
    dsimp only [cellFactor]
    positivity
  have hcellFactor_zero : cellFactor ≠ 0 :=
    hcellFactor_pos.ne'
  have hcellFactor_top : cellFactor ≠ ⊤ := by
    simp only [cellFactor,
      projectedFiberOSPreparedCellThickeningBound]
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
        ENNReal.ofReal_ne_top
  have hprojection :
      volume (twistedUnion globalShading f) ≥
        Kakeya.realRpowENN (delta / rho) epsilon *
          volume
            (Metric.cthickening rho
              (twistedUnion globalShading f)) := by
    let exponentFactor :=
      Kakeya.realRpowENN (delta / rho) epsilon
    let thickVolume :=
      volume
        (Metric.cthickening rho
          (twistedUnion globalShading f))
    let globalVolume :=
      volume (twistedUnion globalShading f)
    have h1 :
        cellFactor * (exponentFactor * thickVolume) ≤
          cellFactor * globalVolume := by
      calc
        cellFactor * (exponentFactor * thickVolume) =
            (exponentFactor * cellFactor) * thickVolume := by
          ring
        _ ≤ localVolume * thickVolume := by
          gcongr
        _ ≤ cellFactor * globalVolume := hglobalization
    exact
      (ENNReal.mul_le_mul_iff_right
        hcellFactor_zero hcellFactor_top).mp h1
  exact
    ⟨rho, by
      have hsep :
          Real.rpow delta (1 - epsilon ^ 2) <
            localBlock.blockScale / 10 := by
        simpa [parameterBlockProjectionWorkingEpsilon] using
          localBlock.separated_scale
      dsimp only [rho]
      nlinarith [localBlock.blockScale_pos],
      hrho_max, hprojection⟩

end Kakeya.Assouad

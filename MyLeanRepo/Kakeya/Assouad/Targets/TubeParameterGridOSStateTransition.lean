import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateTransitionStatements

/-!
WZ2 Proposition 7.1: assemble one corrected iterable transition on the
delta-grid parameter OS tree.

The proof chains six separated leaves:

1. four-block package (uniform OS cell geometry),
2. tube-piece Fubini density transfer,
3. two-sided window clipping with cap absorption,
4. parameter Frostman transfer,
5. twisted-projection containment,
6. planar forty-thickening volume bound.

Setting the window-absorption normalization `L = 1` makes the output density
exactly `gridOSNextDensity fineDensity`.
-/

namespace Kakeya.Assouad

theorem tube_parameter_grid_os_state_transition :
    TubeParameterGridOSStateTransitionStatement := by
  intro fourBlockPackage densityInput frostmanTransfer windowAbsorption
        projectionResult volumeResult
  intro delta source active base levels hbase terminal representatives uniform
        currentScale currentLevel currentFamily currentShading state
        fineShading hfine_sub hfine_window fineDensity hfine_density_nonzero
        hfine_density_top hfine_density rho hrho_pos hrho_le_eighth hscale_six
        nextLevel hnext_le mesh hmesh_six hbudget f hf_nonsing hf_zero epsilon
        hepsilon_pos hscale_ineq
  have hscale_le : currentScale ≤ rho := by linarith
  have hrho_le_one : rho ≤ 1 := by linarith
  have hmesh_nonneg : 0 ≤ mesh := by positivity
  have hmesh_le_sixth : mesh ≤ rho / 6 := by linarith
  have hpackage_condition : 3 * currentScale + 3 * mesh ≤ rho := by linarith
  have hpkg : Nonempty
      (TubeParameterGridOSFourBlockPackageData state fineShading rho nextLevel) :=
    fourBlockPackage source active base levels hbase terminal representatives
      uniform currentFamily currentShading state fineShading hfine_sub
      hfine_window rho hrho_pos hrho_le_eighth nextLevel hnext_le
      hpackage_condition
  rcases hpkg with ⟨package⟩
  let coarseFamily := package.blocks.coarse
  let rawShading : Kakeya.Streamlined.TubeShading coarseFamily :=
    package.blocks.exactShading rho
  let nextShading : Kakeya.Streamlined.TubeShading coarseFamily :=
    slabRestriction rawShading (-1) 1
  have hmul_top : ∀ (a b : ENNReal), a ≠ ⊤ → b ≠ ⊤ → a * b ≠ ⊤ := by
    intro a b ha hb h
    have h5 : a = ⊤ ∨ b = ⊤ := by
      rw [ENNReal.mul_eq_top] at h
      tauto
    cases h5 with
    | inl h5 => exact ha h5
    | inr h5 => exact hb h5
  have hraw_union : rawShading.union ⊆ Metric.cthickening rho fineShading.union := by
    intro x hx
    rcases hx with ⟨j, hj⟩
    set S : Set Point3 :=
      {p | ∃ i : Fin currentFamily.card,
        package.blocks.relation i j ∧ p ∈ fineShading.carrier i} with hS
    have h_def : rawShading.carrier j =
        (coarseFamily.tube j).carrier ∩ Metric.cthickening rho S := by rfl
    have h2 : x ∈ Metric.cthickening rho S := by
      rw [h_def] at hj
      exact hj.2
    have h3 : S ⊆ fineShading.union := by
      intro p hp
      rcases hp with ⟨i, _, hpi⟩
      exact ⟨i, hpi⟩
    have h4 : Metric.cthickening rho S ⊆ Metric.cthickening rho fineShading.union :=
      Metric.cthickening_subset_of_subset rho h3
    exact h4 h2
  have hdensity_raw :
      gridOSRawDensity fineDensity * coarseFamily.toBodyFamily.mass ≤ rawShading.mass := by
    have h := densityInput (delta := currentScale) (rho := rho)
      state.scale_pos hscale_le hrho_le_one currentFamily fineShading
      package.blocks fineDensity hfine_density
    simpa [gridOSRawDensity, rawShading] using h
  have hdensity_raw' :
      gridOSRawDensity fineDensity * coarseFamily.toBodyFamily.mass ≤
        (1 : ENNReal) * rawShading.mass := by
    simpa [one_mul] using hdensity_raw
  have hlambda_top : gridOSRawDensity fineDensity ≠ ⊤ := by
    simp only [gridOSRawDensity]
    exact hmul_top (ENNReal.ofReal (1 / 800 : ℝ)) fineDensity
      (by simp) hfine_density_top
  have hbudget' :
      ENNReal.ofReal (400 * rho) * (1 : ENNReal) ≤
        gridOSRawDensity fineDensity := by
    simpa [mul_one] using hbudget
  have hwindow := windowAbsorption (rho := rho) hrho_pos hrho_le_eighth
    currentFamily fineShading hfine_window coarseFamily package.coarse_vertical
    rawShading hraw_union (gridOSRawDensity fineDensity) (1 : ENNReal)
    hlambda_top (by simp) (by simp) hdensity_raw' hbudget'
  rcases hwindow with ⟨hsub, hslope, hdensity, hunion⟩
  have hdensity' : nextShading.IsLambdaDense (gridOSNextDensity fineDensity) := by
    have h_eq : (2 * (1 : ENNReal))⁻¹ * gridOSRawDensity fineDensity =
        gridOSNextDensity fineDensity := by
      simp [gridOSNextDensity]
    rw [h_eq] at hdensity
    exact hdensity
  have hdensity_const_ne_zero : gridOSNextDensity fineDensity ≠ 0 := by
    simp only [gridOSNextDensity, gridOSRawDensity]
    have h1 : (2 : ENNReal)⁻¹ ≠ 0 := by
      simp [ENNReal.inv_eq_zero]
    have h2 : ENNReal.ofReal (1 / 800 : ℝ) ≠ 0 := by positivity
    exact mul_ne_zero h1 (mul_ne_zero h2 hfine_density_nonzero)
  have hdensity_const_ne_top : gridOSNextDensity fineDensity ≠ ⊤ := by
    simp only [gridOSNextDensity, gridOSRawDensity]
    exact hmul_top ((2 : ENNReal)⁻¹)
      (ENNReal.ofReal (1 / 800 : ℝ) * fineDensity)
      (by simp) (hmul_top _ _ (by simp) hfine_density_top)
  have hparam_one : 1 ≤ (8 : ENNReal) * state.parameterConstant := by
    have h1 : 1 ≤ state.parameterConstant := state.parameter_one
    have h2 : (8 : ENNReal) * 1 ≤
        (8 : ENNReal) * state.parameterConstant := by
      gcongr
    have h3 : (1 : ENNReal) ≤ (8 : ENNReal) * 1 := by norm_num
    exact le_trans h3 h2
  have hparam_ne_top : (8 : ENNReal) * state.parameterConstant ≠ ⊤ := by
    exact hmul_top (8 : ENNReal) state.parameterConstant
      (by simp) state.parameter_ne_top
  have hfrostman :
      TubeParameterFrostmanBound coarseFamily
        ((8 : ENNReal) * state.parameterConstant) :=
    frostmanTransfer (delta := currentScale) (rho := rho) hrho_pos hscale_le
      currentFamily fineShading package.blocks package.representative
      package.representative_parent package.block_parameters mesh hmesh_nonneg
      hmesh_le_sixth package.parameter_close state.parameterConstant
      state.parameter_one state.parameter_ne_top state.parameter_frostman
  have hnext_cells_eq :
      package.coarse_cells =
        occupiedPartitionCells uniform.selectedRepresentatives
          (fun gridLevel =>
            tubeParameterGridPartition base gridLevel representatives.parameters)
          nextLevel := by
    calc
      package.coarse_cells = package.nextCells := package.coarse_cells_eq
      _ = _ := package.nextCells_eq
  have hnext_cells_nonempty : package.coarse_cells.Nonempty := by
    rw [package.coarse_cells_eq]
    exact package.nextCells_nonempty
  have hwindowed_exact :
      IsWindowedExactRelationInducedShading package.blocks.relation fineShading
        nextShading rho := by
    intro j
    dsimp only [nextShading, slabRestriction, rawShading,
      UniformFourBlockRelationData.exactShading]
    ext x
    simp [Set.mem_inter_iff]
    ; tauto
  let nextState : TubeParameterGridOSStateData terminal representatives uniform
      rho nextLevel coarseFamily nextShading :=
    { level_le := package.nextLevel_le
      scale_pos := hrho_pos
      scale_le_one := hrho_le_one
      terminal_or_mesh_control := Or.inr hmesh_six
      family_nonempty := package.coarse_nonempty
      vertical := package.coarse_vertical
      parameter_bounds := package.coarse_parameter_bounds
      cells := package.coarse_cells
      cells_eq := hnext_cells_eq
      cells_nonempty := hnext_cells_nonempty
      parent := package.coarse_parent
      parent_surjective := package.coarse_parent_surjective
      representative := package.coarse_representative
      representative_parent := package.coarse_representative_parent
      parameter_cell := package.coarse_parameter_cell
      representative_parameter := package.coarse_representative_parameter
      fiberMultiplicity := 4
      fiberMultiplicity_pos := by norm_num
      fiber_lower := package.coarse_fiber_lower
      fiber_upper := package.coarse_fiber_upper
      densityConstant := gridOSNextDensity fineDensity
      density_ne_zero := hdensity_const_ne_zero
      density_ne_top := hdensity_const_ne_top
      density := hdensity'
      slope_window := hslope
      parameterConstant := (8 : ENNReal) * state.parameterConstant
      parameter_one := hparam_one
      parameter_ne_top := hparam_ne_top
      parameter_frostman := hfrostman }
  have hprojection :
      twistedUnion nextShading f ⊆
        Metric.cthickening (40 * rho) (twistedUnion fineShading f) :=
    projectionResult currentScale rho rho state.scale_pos state.scale_le_one
      hrho_pos.le currentFamily state.vertical state.parameter_bounds
      coarseFamily package.blocks.relation fineShading hfine_window nextShading
      hwindowed_exact f hf_nonsing hf_zero
  have hvolume40 :
      MeasureTheory.volume (Metric.cthickening (40 * rho)
        (twistedUnion fineShading f)) ≤
      (6889 : ENNReal) * MeasureTheory.volume
        (Metric.cthickening rho (twistedUnion fineShading f)) :=
    volumeResult (twistedUnion fineShading f) rho hrho_pos
  have hnext_twisted_volume :
      MeasureTheory.volume (twistedUnion nextShading f) ≤
      (6889 : ENNReal) * MeasureTheory.volume
        (Metric.cthickening rho (twistedUnion fineShading f)) := by
    calc
      MeasureTheory.volume (twistedUnion nextShading f)
          ≤ MeasureTheory.volume (Metric.cthickening (40 * rho)
              (twistedUnion fineShading f)) :=
        MeasureTheory.measure_mono hprojection
      _ ≤ (6889 : ENNReal) * MeasureTheory.volume
            (Metric.cthickening rho (twistedUnion fineShading f)) :=
        hvolume40
  have hfine_union_sub : fineShading.union ⊆ currentShading.union := by
    intro x hx
    have h_def1 : fineShading.union =
        {x : Point3 |
          ∃ (i : Fin currentFamily.card), x ∈ fineShading.carrier i} := by rfl
    rw [h_def1] at hx
    rcases hx with ⟨i, hi⟩
    have h3 : x ∈ currentShading.carrier i := hfine_sub i hi
    have h_def2 : currentShading.union =
        {x : Point3 |
          ∃ (i : Fin currentFamily.card), x ∈ currentShading.carrier i} := by rfl
    rw [h_def2]
    exact ⟨i, h3⟩
  have hfine_twisted_sub :
      twistedUnion fineShading f ⊆ twistedUnion currentShading f :=
    Set.image_mono hfine_union_sub
  set a : ENNReal := Kakeya.realRpowENN (currentScale / rho) epsilon with ha_def
  have htelescoping :
      a * MeasureTheory.volume (twistedUnion nextShading f) ≤
      (6889 : ENNReal) *
        MeasureTheory.volume (twistedUnion currentShading f) := by
    calc
      a * MeasureTheory.volume (twistedUnion nextShading f)
          ≤ a * ((6889 : ENNReal) * MeasureTheory.volume
              (Metric.cthickening rho (twistedUnion fineShading f))) := by
        gcongr
      _ = (6889 : ENNReal) * (a * MeasureTheory.volume
              (Metric.cthickening rho (twistedUnion fineShading f))) := by
        have hcomm :
            a * ((6889 : ENNReal) *
                MeasureTheory.volume
                  (Metric.cthickening rho (twistedUnion fineShading f))) =
              (6889 : ENNReal) *
                (a * MeasureTheory.volume
                  (Metric.cthickening rho (twistedUnion fineShading f))) := by
          rw [←mul_assoc, mul_comm a (6889 : ENNReal), mul_assoc]
        exact hcomm
      _ ≤ (6889 : ENNReal) *
            MeasureTheory.volume (twistedUnion fineShading f) := by
        gcongr
      _ ≤ (6889 : ENNReal) *
            MeasureTheory.volume (twistedUnion currentShading f) := by
        gcongr
  refine' ⟨package, rawShading, rfl, nextShading, rfl, hfine_sub, hraw_union,
    hwindowed_exact, nextState, hmesh_six, rfl, rfl, hprojection,
    hnext_twisted_volume, htelescoping⟩

end Kakeya.Assouad

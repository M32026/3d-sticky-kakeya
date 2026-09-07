import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSPreparationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMass
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMultiplicityCap
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackMass
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.DyadicIntegralBand
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingCellCardinality
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackSupport
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBandMeasureAreaComparison

/-!
# Same-family projected-fiber OS preparation

Assemble the projected-fiber band, terminal atomization, exact OS pruning,
density absorption, and same-level planar cell uniformity.
-/

namespace Kakeya.Assouad

theorem projected_fiber_os_preparation :
    ProjectedFiberOSPreparationStatement := by
  intro eta heta
  -- Step 1: Choose grid base and band threshold scales
  rcases projected_fiber_grid_parameter_selection eta heta with
    ⟨base, hbase3, δ₀g, hδ₀g_pos, hδ₀g_lt1, hg⟩
  refine ⟨base, hbase3, ?_⟩
  rcases projected_fiber_band_parameter_selection eta heta with
    ⟨δ₀b, hδ₀b_pos, hδ₀b_lt1, hb⟩
  let δ₀ : ℝ := min δ₀g δ₀b
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_lt1 : δ₀ < 1 := by
    have h : δ₀ ≤ δ₀g := min_le_left _ _
    exact h.trans_lt hδ₀g_lt1
  refine ⟨δ₀, hδ₀_pos, hδ₀_lt1, ?_⟩
  intro delta hdelta hδ₀le F hF hvert hparams Y hYdense hY_slab f h_ns h0

  -- Step 2: Choose terminal grid level at this concrete scale
  have hδg_le : delta ≤ δ₀g := hδ₀le.trans (min_le_left _ _)
  rcases hg delta hdelta hδg_le with
    ⟨levels, hmesh_lower, hmesh_upper, hloss_atom_os⟩

  -- Step 3: Choose band threshold and dyadic range
  have hδb_le : delta ≤ δ₀b := hδ₀le.trans (min_le_right _ _)
  rcases hb delta hdelta hδb_le F hF Y hYdense with
    ⟨threshold, levelCount, hth0, hthtop, hmass0, hmasstop, hlowtail, hdyadic, hbandloss⟩

  have hdelta_le_one : delta ≤ 1 := by linarith

  -- Step 4: Assemble the projected-fiber band
  rcases projected_fiber_band
      projected_fiber_mass projected_fiber_multiplicity_cap
      projected_fiber_pullback_mass dyadic_integral_band
      hdelta hdelta_le_one F hF hvert hparams Y hY_slab hmass0 hmasstop
      f h_ns h0 threshold hth0 hthtop hlowtail levelCount hdyadic with
    ⟨bandData⟩

  -- Step 5: Rectangle grid cover
  let indexBound : ℕ := section7GridIndexBound base levels
  have hcov : bandData.band ⊆
      finiteAtomUnion (boundedPlanarGridCenters base levels indexBound)
        (projectedFiberGridAtom bandData.band base levels) :=
    section7_projection_rectangle_grid_cover base levels hbase3
      bandData.band bandData.band_subset_rectangle

  -- Step 6: Prove band shading mass nonzero and non-top
  have hband_shading_mass_pos : bandData.shading.mass ≠ 0 := by
    intro h
    have h9 : Y.mass ≤ 2 * (levelCount + 1 : ENNReal) * bandData.shading.mass :=
      bandData.mass_retention
    rw [h] at h9
    have h10 : Y.mass = 0 := by simpa using h9
    exact hmass0 h10

  have hfmass := projected_fiber_mass F Y f
  have hband_shading_mass_le : bandData.shading.mass ≤ Y.mass := by
    rw [bandData.mass_identity, ←hfmass.2]
    exact MeasureTheory.setLIntegral_le_lintegral bandData.band (projectedFiberMultiplicity Y f)
  have hband_shading_mass_ne_top : bandData.shading.mass ≠ ⊤ :=
    ne_top_of_le_ne_top hmasstop hband_shading_mass_le

  -- Step 7: Atomize the band
  rcases projected_fiber_grid_atomization
      projected_fiber_mass projected_fiber_pullback_mass
      F Y f bandData
      hband_shading_mass_pos hband_shading_mass_ne_top
      base levels indexBound hbase3 hcov with
    ⟨atomized⟩

  -- Step 8: Apply weighted OS pruning
  rcases projected_fiber_atomization_to_os
      F Y f bandData
      base levels indexBound hbase3 atomized with
    ⟨uniform⟩

  -- Step 9: Prove total loss bound
  have h3 : projectedFiberBandLoss levelCount *
      (projectedFiberAtomizationLoss base levels indexBound *
       projectedFiberOSLoss base levels) ≤
      Kakeya.realRpowENN delta (-eta) * Kakeya.realRpowENN delta (-2 * eta) := by
    gcongr

  have h4 : Kakeya.realRpowENN delta (-eta) * Kakeya.realRpowENN delta (-2 * eta) =
      Kakeya.realRpowENN delta (-3 * eta) := by
    rw [← Kakeya.Assouad.realRpowENN_add hdelta (-eta) (-2 * eta)]
    ; ring_nf

  have h5 : projectedFiberBandLoss levelCount *
      (projectedFiberAtomizationLoss base levels indexBound *
       projectedFiberOSLoss base levels) ≤
      Kakeya.realRpowENN delta (-3 * eta) := by
    rw [h4] at h3
    exact h3
  have h_assoc : projectedFiberTotalLoss levelCount base levels indexBound =
      projectedFiberBandLoss levelCount *
        (projectedFiberAtomizationLoss base levels indexBound *
         projectedFiberOSLoss base levels) := by
    simp [projectedFiberTotalLoss, mul_assoc]
  have htotal : projectedFiberTotalLoss levelCount base levels indexBound ≤
      Kakeya.realRpowENN delta (-3 * eta) := by
    rw [h_assoc]
    exact h5

  -- Step 10: Density absorption
  rcases projected_fiber_os_density_absorption
      hdelta hdelta_le_one heta F Y hYdense hY_slab f
      bandData base levels indexBound
      atomized uniform htotal with
    ⟨density⟩

  -- Step 11: Cell mass uniformity
  rcases projected_fiber_os_cell_mass_uniformity
      os_branching_cell_cardinality
      F Y f bandData
      base levels indexBound hbase3 atomized uniform with
    ⟨cellMass⟩

  -- Step 12: Cell area uniformity
  rcases projected_fiber_os_cell_area_uniformity
      projected_fiber_pullback_support projected_fiber_band_measure_area_comparison
      F Y f hth0 hthtop bandData
      base levels indexBound atomized uniform cellMass with
    ⟨cellArea⟩

  -- Step 13: Global support identity
  have global_twisted_eq :
      twistedUnion density.globalShading f = uniform.retainedBand := by
    rw [density.globalShading_eq]
    exact cellArea.twisted_eq

  -- Step 14: Atomic mesh inequality
  have hbase_pos : (0 : ℝ) < (base : ℝ) := by
    exact_mod_cast (show 0 < base from by linarith)
  have hbase_ne_zero : (base : ℝ) ≠ 0 := hbase_pos.ne'
  have h_eq : (base ^ (levels + 1) : ℝ)⁻¹ = (base ^ levels : ℝ)⁻¹ / (base : ℝ) := by
    field_simp [pow_succ, hbase_ne_zero]
    ; ring_nf
  have atomic_mesh_lt : (base ^ (levels + 1) : ℝ)⁻¹ < delta := by
    rw [h_eq]
    have h2 : (base ^ levels : ℝ)⁻¹ < (base : ℝ) * delta := hmesh_upper
    have h3 : (base ^ levels : ℝ)⁻¹ / (base : ℝ) < ((base : ℝ) * delta) / (base : ℝ) :=
      div_lt_div_of_pos_right h2 hbase_pos
    have h4 : ((base : ℝ) * delta) / (base : ℝ) = delta := by
      field_simp [hbase_ne_zero]
    rw [h4] at h3
    exact h3

  -- Step 15: Assemble the final data
  exact ⟨{
    base := base
    base_ge_three := hbase3
    levels := levels
    mesh_lower := hmesh_lower
    mesh_upper := hmesh_upper
    atomic_mesh_lt := atomic_mesh_lt
    threshold := threshold
    levelCount := levelCount
    threshold_ne_zero := hth0
    threshold_ne_top := hthtop
    bandData := bandData
    atomized := atomized
    uniform := uniform
    density := density
    cellMass := cellMass
    cellArea := cellArea
    global_twisted_eq := global_twisted_eq
  }, rfl⟩

end Kakeya.Assouad

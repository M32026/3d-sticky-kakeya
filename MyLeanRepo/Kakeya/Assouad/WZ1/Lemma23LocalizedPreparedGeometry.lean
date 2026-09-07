import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23UnitBallGraph

/-!
# Geometric Theorem 22 inputs for the sharp localized Lemma 23 graph

The sharp localized prepared package changes only the global-bin bound used
in the finite abundance argument.  Its actual cells and graph maps are the
same faithful objects, so the closed height-window bounds, y-residue
separation, coordinate Katz--Tao control, and common unit-ball normalization
apply without modification.
-/

namespace Kakeya.Assouad

noncomputable section

/--
The sharp localized normalized graph, together with all geometric inputs to
the final Theorem 22 interface.
-/
structure WZ1Lemma23LocalizedPreparedGeometry
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue :
      WZ1Lemma23YResiduePackage windowed.global}
    {localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    (prepared :
      WZ1Lemma23LocalizedPreparedPackage
        windowed localized residue localBins) where
  vertex_bounds :
    (∀ point ∈ prepared.normalized.F,
        dist point 0 ≤ 2) ∧
      (∀ point ∈ prepared.normalized.G₁,
        dist point 0 ≤ 5) ∧
      ∀ point ∈ prepared.normalized.G₂,
        dist point 0 ≤ 5
  coordinate_separation :
    (∀ first ∈ prepared.normalized.F,
        ∀ second ∈ prepared.normalized.F,
          first ≠ second →
            Real.sqrt rho / Real.sqrt 3 ≤
              |first 0 - second 0|) ∧
      (∀ first ∈ prepared.normalized.G₁,
        ∀ second ∈ prepared.normalized.G₁,
          first ≠ second →
            Real.sqrt rho / Real.sqrt 3 ≤
              |first 1 - second 1|) ∧
      ∀ first ∈ prepared.normalized.G₂,
        ∀ second ∈ prepared.normalized.G₂,
          first ≠ second →
            Real.sqrt rho / Real.sqrt 3 ≤
              |first 1 - second 1|
  vertex_separation :
    prepared.normalized.F.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      prepared.normalized.G₁.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      prepared.normalized.G₂.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3)
  vertex_katzTao :
    prepared.normalized.F.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
      prepared.normalized.G₁.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
      prepared.normalized.G₂.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4
  unitBall :
    WZ1Lemma23UnitBallGraph
      rho prepared.normalized.F prepared.normalized.G₁
      prepared.normalized.G₂ prepared.normalized.H

/--
Attach all closed geometric Theorem 22 inputs to the sharp localized graph.
-/
theorem wz1_lemma23_localized_prepared_geometry_of_coord
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue :
      WZ1Lemma23YResiduePackage windowed.global}
    {localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (prepared :
      WZ1Lemma23LocalizedPreparedPackage
        windowed localized residue localBins) :
    Nonempty (WZ1Lemma23LocalizedPreparedGeometry prepared) := by
  have hbounds :=
    prepared.actual.vertex_bounds_of_coord
      windowed.global.rho_pos hrho_one hcoord
      windowed.global.extendedSlope_lipschitz
      prepared.selectedLocal.g_bounded
      residue.cells_active
      (windowed.residue_cells_window residue)
  have hcoords :=
    prepared.actual.vertex_coordinate_separation
      windowed.global.rho_pos residue.y_separated
  have hsep :=
    prepared.actual.vertex_separation
      windowed.global.rho_pos residue.y_separated
  have hkt :=
    prepared.actual.vertex_katzTao
      windowed.global.rho_pos residue.y_separated
  have hboundsNormalized :
      (∀ point ∈ prepared.normalized.F,
          dist point 0 ≤ 2) ∧
        (∀ point ∈ prepared.normalized.G₁,
          dist point 0 ≤ 5) ∧
        ∀ point ∈ prepared.normalized.G₂,
          dist point 0 ≤ 5 := by
    rw [prepared.normalized.F_eq,
      prepared.normalized.G₁_eq,
      prepared.normalized.G₂_eq,
      prepared.normalized_sourceF,
      prepared.normalized_sourceG₁,
      prepared.normalized_sourceG₂]
    exact hbounds
  have hcoordsNormalized :
      (∀ first ∈ prepared.normalized.F,
          ∀ second ∈ prepared.normalized.F,
            first ≠ second →
              Real.sqrt rho / Real.sqrt 3 ≤
                |first 0 - second 0|) ∧
        (∀ first ∈ prepared.normalized.G₁,
          ∀ second ∈ prepared.normalized.G₁,
            first ≠ second →
              Real.sqrt rho / Real.sqrt 3 ≤
                |first 1 - second 1|) ∧
        ∀ first ∈ prepared.normalized.G₂,
          ∀ second ∈ prepared.normalized.G₂,
            first ≠ second →
              Real.sqrt rho / Real.sqrt 3 ≤
                |first 1 - second 1| := by
    rw [prepared.normalized.F_eq,
      prepared.normalized.G₁_eq,
      prepared.normalized.G₂_eq,
      prepared.normalized_sourceF,
      prepared.normalized_sourceG₁,
      prepared.normalized_sourceG₂]
    exact hcoords
  have hsepNormalized :
      prepared.normalized.F.IsDeltaSeparated
          (Real.sqrt rho / Real.sqrt 3) ∧
        prepared.normalized.G₁.IsDeltaSeparated
          (Real.sqrt rho / Real.sqrt 3) ∧
        prepared.normalized.G₂.IsDeltaSeparated
          (Real.sqrt rho / Real.sqrt 3) := by
    rw [prepared.normalized.F_eq,
      prepared.normalized.G₁_eq,
      prepared.normalized.G₂_eq,
      prepared.normalized_sourceF,
      prepared.normalized_sourceG₁,
      prepared.normalized_sourceG₂]
    exact hsep
  have hktNormalized :
      prepared.normalized.F.IsKatzTao
          (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
        prepared.normalized.G₁.IsKatzTao
          (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
        prepared.normalized.G₂.IsKatzTao
          (Real.sqrt rho / Real.sqrt 3) 1 4 := by
    rw [prepared.normalized.F_eq,
      prepared.normalized.G₁_eq,
      prepared.normalized.G₂_eq,
      prepared.normalized_sourceF,
      prepared.normalized_sourceG₁,
      prepared.normalized_sourceG₂]
    exact hkt
  rcases hboundsNormalized with ⟨hFbound, hG₁bound, hG₂bound⟩
  rcases hcoordsNormalized with ⟨hFcoord, hG₁coord, hG₂coord⟩
  rcases
      wz1_lemma23_unit_ball_graph
        windowed.global.rho_pos
        prepared.normalized.edge_support
        hFbound hG₁bound hG₂bound
        hFcoord hG₁coord hG₂coord with
    ⟨unitBall⟩
  exact
    ⟨{ vertex_bounds := ⟨hFbound, hG₁bound, hG₂bound⟩
       coordinate_separation := ⟨hFcoord, hG₁coord, hG₂coord⟩
       vertex_separation := hsepNormalized
       vertex_katzTao := hktNormalized
       unitBall := unitBall }⟩

/-- Historical unit-ball wrapper for the coordinate-crop geometry. -/
theorem wz1_lemma23_localized_prepared_geometry
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized : WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue : WZ1Lemma23YResiduePackage windowed.global}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C windowed.global.cells}
    (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (prepared : WZ1Lemma23LocalizedPreparedPackage
      windowed localized residue localBins) :
    Nonempty (WZ1Lemma23LocalizedPreparedGeometry prepared) := by
  apply wz1_lemma23_localized_prepared_geometry_of_coord hrho_one _ prepared
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

end

end Kakeya.Assouad

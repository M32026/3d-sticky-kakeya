import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26RepairedStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.BudgetedSegmentConversionAssembly

/-!
# Ordinary-shadow view of a pure Corollary-26 hierarchy

The Proposition-27 segment arithmetic is carrier-independent.  This module
therefore exposes a pure cropped-paper hierarchy on the equal-union ordinary
active-cell shadow.  No uniform tube structure, assigned fibers, or
exact-scale cover is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

/--
View a pure paper hierarchy as the legacy carrier-independent hierarchy on
the equal ordinary active-cell shadow.
-/
def PureWZ2AnchoredHierarchyData.toActiveCellShadow
    {delta hierarchyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sourceSlope : ℝ → ℝ}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (data :
      PureWZ2AnchoredHierarchyData
        shading sourceSlope hierarchyLoss) :
    WZ1Corollary26AnchoredHierarchyData
      (pureWZ2ActiveCellShading shading hdelta)
      sourceSlope hierarchyLoss := by
  have hunion :
      (pureWZ2ActiveCellShading shading hdelta).union = shading.union :=
    pureWZ2ActiveCellShading_union shading hdelta hcubical
  exact
    { levelCount := data.levelCount
      levelCount_two := data.levelCount_two
      trapezoids := data.trapezoids
      level_nonempty := data.level_nonempty
      height_eq := data.height_eq
      slope_bound := data.slope_bound
      length_bounds := data.length_bounds
      separated_cores := data.separated_cores
      active_endpoints := by
        intro level trapezoid htrapezoid
        rw [hunion]
        exact data.active_endpoints level trapezoid htrapezoid
      slope_approximation := by
        intro level trapezoid htrapezoid z hz hactive
        apply data.slope_approximation level trapezoid htrapezoid z hz
        rwa [← hunion]
      active_height_coverage := by
        intro level z hz hactive
        apply data.active_height_coverage level z hz
        rwa [← hunion]
      unique_parent := data.unique_parent }

/-- View a pure paper hierarchy on the equal-union partial-cell shadow.
This is the paper-faithful adapter after Corollary 5.6 height thinning, where
the final shading is no longer required to contain whole grid cells. -/
def PureWZ2AnchoredHierarchyData.toPartialActiveCellShadow
    {delta hierarchyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sourceSlope : ℝ → ℝ}
    (hdelta : 0 < delta)
    (data :
      PureWZ2AnchoredHierarchyData
        shading sourceSlope hierarchyLoss) :
    WZ1Corollary26AnchoredHierarchyData
      (pureWZ2PartialActiveCellShading shading hdelta)
      sourceSlope hierarchyLoss := by
  have hunion :
      (pureWZ2PartialActiveCellShading shading hdelta).union =
        shading.union :=
    pureWZ2PartialActiveCellShading_union shading hdelta
  exact
    { levelCount := data.levelCount
      levelCount_two := data.levelCount_two
      trapezoids := data.trapezoids
      level_nonempty := data.level_nonempty
      height_eq := data.height_eq
      slope_bound := data.slope_bound
      length_bounds := data.length_bounds
      separated_cores := data.separated_cores
      active_endpoints := by
        intro level trapezoid htrapezoid
        rw [hunion]
        exact data.active_endpoints level trapezoid htrapezoid
      slope_approximation := by
        intro level trapezoid htrapezoid z hz hactive
        apply data.slope_approximation level trapezoid htrapezoid z hz
        rwa [← hunion]
      active_height_coverage := by
        intro level z hz hactive
        apply data.active_height_coverage level z hz
        rwa [← hunion]
      unique_parent := data.unique_parent }

/-- Level-zero affine endpoint values are uniformly bounded on the paper crop. -/
theorem PureWZ2AnchoredHierarchyData.levelZero_endpoint_bound
    {delta hierarchyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sourceSlope : ℝ → ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hslope : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |sourceSlope z| ≤ 3)
    (data :
      PureWZ2AnchoredHierarchyData
        shading sourceSlope hierarchyLoss) :
    ∀ level, ∀ trapezoid ∈ data.trapezoids level,
      (level : ℕ) = 0 →
        |trapezoid.affine trapezoid.left| ≤ 4 ∧
          |trapezoid.affine trapezoid.right| ≤ 4 := by
  intro level trapezoid htrapezoid _hlevelZero
  have hendpoints := data.active_endpoints level trapezoid htrapezoid
  have hheight :
      0 < wz1Corollary26Scale delta data.levelCount level :=
    Real.rpow_pos_of_pos hdelta _
  have hscaleOne :
      wz1Corollary26Scale delta data.levelCount level ≤ 1 := by
    exact Real.rpow_le_one hdelta.le hdelta_one (by positivity)
  have endpoint_mem_Icc :
      ∀ z : ℝ, horizontalSlice shading.union z ≠ ∅ →
        z ∈ Set.Icc (-1 : ℝ) 1 := by
    intro z hactive
    rcases Set.nonempty_iff_ne_empty.mpr hactive with ⟨point, hpoint⟩
    have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      shading_union_subset_axisBox hpoint.1
    have hz : |z| ≤ 1 := by
      rw [← hpoint.2]
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    exact abs_le.mp hz
  have bound_endpoint :
      ∀ z ∈ trapezoid.core, horizontalSlice shading.union z ≠ ∅ →
        |trapezoid.affine z| ≤ 4 := by
    intro z hz hactive
    have hsource := hslope z (endpoint_mem_Icc z hactive)
    have happrox :=
      data.slope_approximation level trapezoid htrapezoid z hz hactive
    calc
      |trapezoid.affine z|
          = |sourceSlope z -
              (sourceSlope z - trapezoid.affine z)| := by ring_nf
      _ ≤ |sourceSlope z| +
            |sourceSlope z - trapezoid.affine z| := abs_sub _ _
      _ ≤ 3 + wz1Corollary26Scale delta data.levelCount level := by
        linarith
      _ ≤ 4 := by linarith
  constructor
  · apply bound_endpoint trapezoid.left
    · simp [WZ1VerticalTrapezoid.core, trapezoid.left_lt_right.le]
    · exact hendpoints.1
  · apply bound_endpoint trapezoid.right
    · simp [WZ1VerticalTrapezoid.core, trapezoid.left_lt_right.le]
    · exact hendpoints.2

end Kakeya.Assouad

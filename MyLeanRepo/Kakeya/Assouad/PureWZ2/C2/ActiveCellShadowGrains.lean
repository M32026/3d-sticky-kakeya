import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadow
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Grain data on the ordinary active-cell shadow

The finite WZ1 Lemma-23 graph is phrased for ordinary tube shadings.  This
module transports the paper-facing local and exact-slice global grain data to
the ordinary active-cell shadow without changing the shaded set.

The ambient plane map is a finite-dimensional Lipschitz extension of the
paper map.  Incidence is inherited from the genuine source tube selected for
each active cell.  The paper-literal AD certificates are converted only at
this internal boundary, through `PureWZ2PaperADBridgeStatement`.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Points in the literal paper crop have Euclidean norm at most two. -/
theorem norm_le_two_of_mem_paperShading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {point : Point3} (hpoint : point ∈ shading.union) :
    ‖point‖ ≤ 2 := by
  have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    shading_union_subset_axisBox hpoint
  have hcoord : ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    intro coordinate
    fin_cases coordinate <;> tauto
  have hsq : ‖point‖ ^ 2 ≤ 3 := by
    have h0 : point 0 ^ 2 ≤ 1 := by
      nlinarith [sq_abs (point 0), abs_nonneg (point 0), hcoord 0]
    have h1 : point 1 ^ 2 ≤ 1 := by
      nlinarith [sq_abs (point 1), abs_nonneg (point 1), hcoord 1]
    have h2 : point 2 ^ 2 ≤ 1 := by
      nlinarith [sq_abs (point 2), abs_nonneg (point 2), hcoord 2]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    nlinarith
  nlinarith [norm_nonneg point]

/-- Any unit-direction scalar projection of a paper shading lies in `[-4,4]`. -/
theorem scalarProjection_paperShading_subset_Icc
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {direction : Point3} (hdirection : ‖direction‖ = 1)
    {subset : Set Point3} (hsubset : subset ⊆ shading.union) :
    scalarProjection direction subset ⊆ Set.Icc (-4 : ℝ) 4 := by
  rintro value ⟨point, hpoint, rfl⟩
  have hinner : |inner ℝ point direction| ≤ 2 := by
    calc
      |inner ℝ point direction| ≤ ‖point‖ * ‖direction‖ :=
        abs_real_inner_le_norm point direction
      _ = ‖point‖ * 1 := by rw [hdirection]
      _ ≤ 2 * 1 := by
        gcongr
        exact norm_le_two_of_mem_paperShading (hsubset hpoint)
      _ = 2 := by norm_num
  exact ⟨by linarith [neg_abs_le (inner ℝ point direction)],
    by linarith [le_abs_self (inner ℝ point direction)]⟩

/--
The pure subtype-valued local grains, viewed on the equal ordinary active-cell
shadow.  No historical uniform structure is introduced.
-/
def PureWZ2LocalGrainData.toActiveCellShadow
    {delta sigma : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (data : PureWZ2LocalGrainData shading sigma C) :
    WZ1LocalGrainData
      (pureWZ2ActiveCellShading shading hdelta) sigma (10 * C) := by
  classical
  let extension : Point3 → Point3 :=
    Classical.choose data.exists_ambient_extension
  have hextension :
      LipschitzWith (lipschitzExtensionConstant Point3) extension :=
    (Classical.choose_spec data.exists_ambient_extension).1
  have hextension_eq :
      ∀ point : {point : Point3 // point ∈ shading.union},
        extension (point : Point3) = data.planeMap point :=
    (Classical.choose_spec data.exists_ambient_extension).2
  have hunion :
      (pureWZ2ActiveCellShading shading hdelta).union = shading.union :=
    pureWZ2ActiveCellShading_union shading hdelta hcubical
  refine
    { planeMap := extension
      measurable := hextension.continuous.measurable
      lipschitzConstant := lipschitzExtensionConstant Point3
      lipschitz := hextension.lipschitzOnWith
      unit := ?_
      incidence := ?_
      local_ad := ?_ }
  · intro point hpoint
    have hsource : point ∈ shading.union := by simpa [hunion] using hpoint
    rw [hextension_eq ⟨point, hsource⟩]
    exact data.planeMap_unit ⟨point, hsource⟩
  · intro index point hpoint
    let cell : PureWZ2ActivePaperCell shading hdelta :=
      (wz1PaperActiveCells shading hdelta).equivFin.symm index
    have hpointCell : point ∈ wz1PaperGridCube delta cell.1 := by
      exact hpoint
    have hpointSource :
        point ∈ shading.carrier
          (pureWZ2ActiveCellSource shading hdelta cell) :=
      pureWZ2ActiveCell_subset_source shading hdelta hcubical cell hpointCell
    have hpointUnion : point ∈ shading.union :=
      ⟨pureWZ2ActiveCellSource shading hdelta cell, hpointSource⟩
    rw [hextension_eq ⟨point, hpointUnion⟩]
    rw [pureWZ2ActiveCellFamily_direction]
    exact (data.planeMap_incidence
      (pureWZ2ActiveCellSource shading hdelta cell) point hpointSource).trans
        (by nlinarith [hdelta.le])
  · intro rho hdelta_rho hrho_one point hpoint
    have hsource : point ∈ shading.union := by simpa [hunion] using hpoint
    have hextension_point :
        extension point = data.planeMap ⟨point, hsource⟩ :=
      hextension_eq ⟨point, hsource⟩
    have hliteral :=
      data.local_ad rho hdelta_rho hrho_one ⟨point, hsource⟩
    have hset :
        scalarProjection (extension point)
            ((pureWZ2ActiveCellShading shading hdelta).union ∩
              Metric.closedBall point (Real.sqrt rho)) =
          scalarProjection (data.planeMap ⟨point, hsource⟩)
            (shading.union ∩ Metric.closedBall point (Real.sqrt rho)) := by
      rw [hunion, hextension_point]
    rw [hset]
    exact hbridge.1 _ rho (1 - sigma) C
      (scalarProjection_paperShading_subset_Icc
        (data.planeMap_unit ⟨point, hsource⟩) Set.inter_subset_left)
      hliteral

/-- On the equal active-cell shadow, the ordinary plane map is exactly the
original pure plane map. -/
theorem PureWZ2LocalGrainData.toActiveCellShadow_planeMap_eq
    {delta sigma : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (point : Point3)
    (hpoint :
      point ∈
        (pureWZ2ActiveCellShading shading hdelta).union) :
    (data.toActiveCellShadow hdelta hcubical hbridge).planeMap point =
      data.planeMap
        ⟨point, by
          rw [pureWZ2ActiveCellShading_union shading hdelta hcubical] at hpoint
          exact hpoint⟩ := by
  change
    Classical.choose data.exists_ambient_extension point =
      data.planeMap _
  let sourcePoint :
      {point : Point3 // point ∈ shading.union} :=
    ⟨point, by
      rw [pureWZ2ActiveCellShading_union shading hdelta hcubical] at hpoint
      exact hpoint⟩
  simpa [sourcePoint] using
    (Classical.choose_spec data.exists_ambient_extension).2 sourcePoint

/--
The pure subtype-valued local grains on the equal-union partial-cell shadow.

Unlike `toActiveCellShadow`, this construction does not assume that the paper
shading contains whole cells.  Incidence for the auxiliary cell tube is
transferred from a genuine shaded witness in the same paper cell; the
one-Lipschitz variation of the plane map and the cell diameter cost at most
`2 * delta`, which is absorbed by the ordinary `6 * delta` incidence bound.
-/
def PureWZ2LocalGrainData.toPartialActiveCellShadow
    {delta sigma : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (data : PureWZ2LocalGrainData shading sigma C) :
    WZ1LocalGrainData
      (pureWZ2PartialActiveCellShading shading hdelta) sigma (10 * C) := by
  classical
  let extension : Point3 → Point3 :=
    Classical.choose data.exists_ambient_extension
  have hextension :
      LipschitzWith (lipschitzExtensionConstant Point3) extension :=
    (Classical.choose_spec data.exists_ambient_extension).1
  have hextension_eq :
      ∀ point : {point : Point3 // point ∈ shading.union},
        extension (point : Point3) = data.planeMap point :=
    (Classical.choose_spec data.exists_ambient_extension).2
  have hunion :
      (pureWZ2PartialActiveCellShading shading hdelta).union = shading.union :=
    pureWZ2PartialActiveCellShading_union shading hdelta
  refine
    { planeMap := extension
      measurable := hextension.continuous.measurable
      lipschitzConstant := lipschitzExtensionConstant Point3
      lipschitz := hextension.lipschitzOnWith
      unit := ?_
      incidence := ?_
      local_ad := ?_ }
  · intro point hpoint
    have hsource : point ∈ shading.union := by simpa [hunion] using hpoint
    rw [hextension_eq ⟨point, hsource⟩]
    exact data.planeMap_unit ⟨point, hsource⟩
  · intro index point hpoint
    let cell : PureWZ2ActivePaperCell shading hdelta :=
      (wz1PaperActiveCells shading hdelta).equivFin.symm index
    let witness := pureWZ2ActiveCellPoint shading hdelta cell
    let sourceIndex := pureWZ2ActiveCellSource shading hdelta cell
    have hpointUnion : point ∈ shading.union := hpoint.1
    have hwitnessUnion : witness ∈ shading.union :=
      pureWZ2ActiveCellPoint_mem_union shading hdelta cell
    have hwitnessSource : witness ∈ shading.carrier sourceIndex :=
      pureWZ2ActiveCellPoint_mem_source shading hdelta cell
    have hpointCell : point ∈ wz1PaperGridCube delta cell.1 := hpoint.2
    have hwitnessCell : witness ∈ wz1PaperGridCube delta cell.1 :=
      pureWZ2ActiveCellPoint_mem_cell shading hdelta cell
    have hcellDistance :
        dist (⟨point, hpointUnion⟩ :
          {point : Point3 // point ∈ shading.union})
            ⟨witness, hwitnessUnion⟩ < 2 * delta := by
      change dist point witness < 2 * delta
      exact wz1_paper_grid_cube_diameter_lt_two_rho hdelta
        hpointCell hwitnessCell
    have hmapDistance :
        dist (data.planeMap ⟨point, hpointUnion⟩)
            (data.planeMap ⟨witness, hwitnessUnion⟩) < 2 * delta := by
      exact (data.planeMap_lipschitz.dist_le_mul
        ⟨point, hpointUnion⟩ ⟨witness, hwitnessUnion⟩).trans_lt (by
          simpa using hcellDistance)
    have hvariation :
        |inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨point, hpointUnion⟩ -
              data.planeMap ⟨witness, hwitnessUnion⟩)| < 2 * delta := by
      calc
        |inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨point, hpointUnion⟩ -
              data.planeMap ⟨witness, hwitnessUnion⟩)| ≤
            ‖(source.tube sourceIndex).direction‖ *
              ‖data.planeMap ⟨point, hpointUnion⟩ -
                data.planeMap ⟨witness, hwitnessUnion⟩‖ :=
          abs_real_inner_le_norm _ _
        _ = dist (data.planeMap ⟨point, hpointUnion⟩)
            (data.planeMap ⟨witness, hwitnessUnion⟩) := by
          rw [(source.tube sourceIndex).direction_unit, one_mul, dist_eq_norm]
        _ < 2 * delta := hmapDistance
    have hsourceIncidence :
        |inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨witness, hwitnessUnion⟩)| ≤ delta :=
      data.planeMap_incidence sourceIndex witness hwitnessSource
    rw [pureWZ2ActiveCellFamily_direction]
    rw [hextension_eq ⟨point, hpointUnion⟩]
    have hsplit :
        inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨point, hpointUnion⟩) =
          inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨witness, hwitnessUnion⟩) +
          inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨point, hpointUnion⟩ -
              data.planeMap ⟨witness, hwitnessUnion⟩) := by
      rw [inner_sub_right]
      ring
    rw [hsplit]
    calc
      |inner ℝ (source.tube sourceIndex).direction
          (data.planeMap ⟨witness, hwitnessUnion⟩) +
        inner ℝ (source.tube sourceIndex).direction
          (data.planeMap ⟨point, hpointUnion⟩ -
            data.planeMap ⟨witness, hwitnessUnion⟩)| ≤
          |inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨witness, hwitnessUnion⟩)| +
          |inner ℝ (source.tube sourceIndex).direction
            (data.planeMap ⟨point, hpointUnion⟩ -
              data.planeMap ⟨witness, hwitnessUnion⟩)| := abs_add_le _ _
      _ ≤ delta + 2 * delta :=
        (add_lt_add_of_le_of_lt hsourceIncidence hvariation).le
      _ ≤ 6 * delta := by linarith
  · intro rho hdelta_rho hrho_one point hpoint
    have hsource : point ∈ shading.union := by simpa [hunion] using hpoint
    have hextension_point :
        extension point = data.planeMap ⟨point, hsource⟩ :=
      hextension_eq ⟨point, hsource⟩
    have hliteral :=
      data.local_ad rho hdelta_rho hrho_one ⟨point, hsource⟩
    have hset :
        scalarProjection (extension point)
            ((pureWZ2PartialActiveCellShading shading hdelta).union ∩
              Metric.closedBall point (Real.sqrt rho)) =
          scalarProjection (data.planeMap ⟨point, hsource⟩)
            (shading.union ∩ Metric.closedBall point (Real.sqrt rho)) := by
      rw [hunion, hextension_point]
    rw [hset]
    exact hbridge.1 _ rho (1 - sigma) C
      (scalarProjection_paperShading_subset_Icc
        (data.planeMap_unit ⟨point, hsource⟩) Set.inter_subset_left)
      hliteral

/-- The partial-cell shadow uses the same ambient extension on the unchanged
union, so it preserves the source vertical-component bound. -/
theorem PureWZ2LocalGrainData.toPartialActiveCellShadow_vertical_bound
    {delta sigma : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (data : PureWZ2LocalGrainData shading sigma C)
    (hvertical :
      ∀ point : {point : Point3 // point ∈ shading.union},
        |data.planeMap point (2 : Fin 3)| ≤ 1 / 2) :
    ∀ point ∈ (pureWZ2PartialActiveCellShading shading hdelta).union,
      |(data.toPartialActiveCellShadow hdelta hbridge).planeMap point
          (2 : Fin 3)| ≤ 1 / 2 := by
  intro point hpoint
  have hunion :
      (pureWZ2PartialActiveCellShading shading hdelta).union = shading.union :=
    pureWZ2PartialActiveCellShading_union shading hdelta
  have hsource : point ∈ shading.union := by simpa [hunion] using hpoint
  let extension : Point3 → Point3 :=
    Classical.choose data.exists_ambient_extension
  have hextension_eq :
      extension point = data.planeMap ⟨point, hsource⟩ :=
    (Classical.choose_spec data.exists_ambient_extension).2 ⟨point, hsource⟩
  change |extension point (2 : Fin 3)| ≤ 1 / 2
  rw [hextension_eq]
  exact hvertical ⟨point, hsource⟩

/-- Bounded-slope exact-slice global AD on the equal-union partial-cell
shadow.  No whole-cell hypothesis is needed because its union is definitionally
the original paper union up to `pureWZ2PartialActiveCellShading_union`. -/
theorem PureWZ2LipschitzGlobalGrainData.partialActiveCellShadow_exactAD
    {delta sigma : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C)
    (hslope : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |data.slope z| ≤ 3) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (data.slope z))
          (horizontalSlice
            (pureWZ2PartialActiveCellShading shading hdelta).union z))
        delta (1 - sigma) (10 * C) := by
  intro z hz
  have hunion :
      (pureWZ2PartialActiveCellShading shading hdelta).union = shading.union :=
    pureWZ2PartialActiveCellShading_union shading hdelta
  have hbounded :
      scalarProjection (globalGrainDirection (data.slope z))
          (horizontalSlice shading.union z) ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      shading_union_subset_axisBox hpoint.1
    have hcoord0 : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hcoord1 : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hformula :
        inner ℝ point (globalGrainDirection (data.slope z)) =
          point 0 + data.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point (globalGrainDirection (data.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    have habs : |point 0 + data.slope z * point 1| ≤ 4 := by
      calc
        |point 0 + data.slope z * point 1|
            ≤ |point 0| + |data.slope z| * |point 1| := by
              calc
                |point 0 + data.slope z * point 1|
                    ≤ |point 0| + |data.slope z * point 1| := abs_add_le _ _
                _ = |point 0| + |data.slope z| * |point 1| := by rw [abs_mul]
        _ ≤ 1 + 3 * 1 := by gcongr; exact hslope z hz
        _ = 4 := by norm_num
    exact abs_le.mp habs
  rw [hunion]
  exact hbridge.1 _ delta (1 - sigma) C hbounded (data.global_ad z hz)

/-- The ambient extension preserves the source vertical bound on the shadow union. -/
theorem PureWZ2LocalGrainData.toActiveCellShadow_vertical_bound
    {delta sigma : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (data : PureWZ2LocalGrainData shading sigma C)
    (hvertical :
      ∀ point : {point : Point3 // point ∈ shading.union},
        |data.planeMap point (2 : Fin 3)| ≤ 1 / 2) :
    ∀ point ∈ (pureWZ2ActiveCellShading shading hdelta).union,
      |(data.toActiveCellShadow hdelta hcubical hbridge).planeMap point
          (2 : Fin 3)| ≤ 1 / 2 := by
  intro point hpoint
  have hunion :
      (pureWZ2ActiveCellShading shading hdelta).union = shading.union :=
    pureWZ2ActiveCellShading_union shading hdelta hcubical
  have hsource : point ∈ shading.union := by simpa [hunion] using hpoint
  let extension : Point3 → Point3 :=
    Classical.choose data.exists_ambient_extension
  have hextension_eq :
      extension point = data.planeMap ⟨point, hsource⟩ :=
    (Classical.choose_spec data.exists_ambient_extension).2 ⟨point, hsource⟩
  change |extension point (2 : Fin 3)| ≤ 1 / 2
  rw [hextension_eq]
  exact hvertical ⟨point, hsource⟩

/--
Bounded-slope exact-slice global AD on the equal ordinary active-cell shadow.
The coordinate proof uses the literal crop directly, not a unit-ball surrogate.
-/
theorem PureWZ2LipschitzGlobalGrainData.activeCellShadow_exactAD
    {delta sigma : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C)
    (hslope : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |data.slope z| ≤ 3) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (data.slope z))
          (horizontalSlice
            (pureWZ2ActiveCellShading shading hdelta).union z))
        delta (1 - sigma) (10 * C) := by
  intro z hz
  have hunion :
      (pureWZ2ActiveCellShading shading hdelta).union = shading.union :=
    pureWZ2ActiveCellShading_union shading hdelta hcubical
  have hbounded :
      scalarProjection (globalGrainDirection (data.slope z))
          (horizontalSlice shading.union z) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      shading_union_subset_axisBox hpoint.1
    have hcoord0 : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hcoord1 : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hformula :
        inner ℝ point (globalGrainDirection (data.slope z)) =
          point 0 + data.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point (globalGrainDirection (data.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    have habs : |point 0 + data.slope z * point 1| ≤ 4 := by
      calc
        |point 0 + data.slope z * point 1|
            ≤ |point 0| + |data.slope z| * |point 1| := by
              calc
                |point 0 + data.slope z * point 1|
                    ≤ |point 0| + |data.slope z * point 1| := abs_add_le _ _
                _ = |point 0| + |data.slope z| * |point 1| := by rw [abs_mul]
        _ ≤ 1 + 3 * 1 := by gcongr; exact hslope z hz
        _ = 4 := by norm_num
    exact abs_le.mp habs
  rw [hunion]
  exact hbridge.1 _ delta (1 - sigma) C hbounded (data.global_ad z hz)

end Kakeya.Assouad

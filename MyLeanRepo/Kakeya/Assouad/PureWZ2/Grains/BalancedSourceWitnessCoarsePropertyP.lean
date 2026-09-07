import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperPropertyPEnergySelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialHull
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WholeCellBalancedRestriction

/-!
# Source-witness Property (P) on an arbitrary frozen balanced cover

This is the balanced-cover form of the sticky-specific source-witness energy
selection.  It can therefore be run after a previous common whole-cell
restriction, keeping the local and global grain constructions nested.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

structure PureWZ2BalancedSourceWitnessCoarsePropertyPData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading) where
  sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced
  distinguished : Fin coarse.card
  propertyThree : WZ1PaperTubeShading coarse
  propertyThree_sub_witness :
    PaperIsSubshading propertyThree sourceWitness.shading
  propertyThree_common_spatial :
    ∀ parent, propertyThree.carrier parent =
      sourceWitness.shading.carrier parent ∩ propertyThree.union
  propertyThree_sub : PaperIsSubshading propertyThree coarseShading
  propertyThree_cubical : WZ1PaperIsCubicalShading propertyThree
  propertyP :
    ∀ point ∈ propertyThree.union,
      ∃ witness ∈ propertyThree.carrier distinguished,
        rhoGridIndex ((Real.sqrt 3 / 2) * rho) point =
          rhoGridIndex ((Real.sqrt 3 / 2) * rho) witness
  energy :
    sourceWitness.shading.mass ^ 2 ≤
      volume sourceWitness.shading.union *
        coarse.enncard * propertyThree.mass
  distinguished_source_witness :
    ∀ point ∈ propertyThree.carrier distinguished,
      ∃ cell source sourcePoint,
        point ∈ wz1PaperGridCube rho cell ∧
          cover.toPaperTubeCover.parent source = distinguished ∧
          sourcePoint ∈ fineShading.carrier source ∧
          sourcePoint ∈ wz1PaperGridCube rho cell

/-- Run the honest source-witness energy selector on any nonempty balanced
coarse family. -/
theorem balanced_source_witness_coarse_property_p
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hrho : 0 < rho)
    (hcoarse : coarse.Nonempty) :
    Nonempty
      (PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced) := by
  rcases source_witness_coarse_shading balanced with ⟨sourceWitness⟩
  rcases paper_property_p_energy_selection sourceWitness.shading
      hrho hcoarse sourceWitness.balanced.coarse_cubical with
    ⟨distinguished, propertyThree, hsubWitness, hcommon, hcubical,
      hpropertyP, henergy⟩
  have hsub : PaperIsSubshading propertyThree coarseShading :=
    fun parent =>
      (hsubWitness parent).trans (sourceWitness.subshading parent)
  have hsource :
      ∀ point ∈ propertyThree.carrier distinguished,
        ∃ cell source sourcePoint,
          point ∈ wz1PaperGridCube rho cell ∧
            cover.toPaperTubeCover.parent source = distinguished ∧
            sourcePoint ∈ fineShading.carrier source ∧
            sourcePoint ∈ wz1PaperGridCube rho cell := by
    intro point hpoint
    have hpointWitness :
        point ∈ sourceWitness.shading.carrier distinguished :=
      hsubWitness distinguished hpoint
    rw [sourceWitness.shading_carrier_eq distinguished] at hpointWitness
    rcases Set.mem_iUnion.mp hpointWitness with ⟨cell, hpointWitness⟩
    rcases Set.mem_iUnion.mp hpointWitness with ⟨hcell, hpointCell⟩
    rcases sourceWitness.source_witness distinguished cell hcell with
      ⟨sourceIndex, sourcePoint, hparent, hsourcePoint, hsourceCell⟩
    exact ⟨cell, sourceIndex, sourcePoint, hpointCell, hparent,
      hsourcePoint, hsourceCell⟩
  exact
    ⟨{ sourceWitness := sourceWitness
       distinguished := distinguished
       propertyThree := propertyThree
       propertyThree_sub_witness := hsubWitness
       propertyThree_common_spatial := hcommon
       propertyThree_sub := hsub
       propertyThree_cubical := hcubical
       propertyP := hpropertyP
       energy := henergy
       distinguished_source_witness := hsource }⟩

/-- Every selected coarse point is close to an actual shaded fine point from
the distinguished parent fiber. -/
theorem PureWZ2BalancedSourceWitnessCoarsePropertyPData.point_near_fine_source
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho)
    (point : Point3) (hpoint : point ∈ data.propertyThree.union) :
    ∃ sourceIndex sourcePoint,
      cover.toPaperTubeCover.parent sourceIndex = data.distinguished ∧
        sourcePoint ∈ fineShading.carrier sourceIndex ∧
        dist point sourcePoint ≤ 4 * rho := by
  rcases data.propertyP point hpoint with
    ⟨witness, hwitness, hpropertyCell⟩
  rcases data.distinguished_source_witness witness hwitness with
    ⟨cell, sourceIndex, sourcePoint, hwitnessCell, hparent,
      hsourcePoint, hsourceCell⟩
  let propertyScale : ℝ := (Real.sqrt 3 / 2) * rho
  have hpropertyScale : 0 < propertyScale := by
    dsimp only [propertyScale]
    positivity
  have hpointWitness : dist point witness ≤ 2 * propertyScale :=
    grid_cell_diameter hpropertyScale hpropertyCell
  have hwitnessSource :
      dist witness sourcePoint ≤ rho * Real.sqrt 3 :=
    wz1PaperGridCube_diameter hrho cell hwitnessCell hsourceCell
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  refine ⟨sourceIndex, sourcePoint, hparent, hsourcePoint, ?_⟩
  calc
    dist point sourcePoint ≤
        dist point witness + dist witness sourcePoint :=
      dist_triangle point witness sourcePoint
    _ ≤ 2 * propertyScale + rho * Real.sqrt 3 := by gcongr
    _ ≤ 4 * rho := by
      dsimp only [propertyScale]
      nlinarith

namespace PureWZ2BalancedSourceWitnessCoarsePropertyPData

/-- Freeze one honest fine source index for each distinguished parent cell.
Outside the retained cell set use the nonempty distinguished fiber only as a
total-function fallback. -/
noncomputable def sourceAnchorIndex
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (cell : ℤ × ℤ × ℤ) : Fin fine.card :=
  if hcell : cell ∈ data.sourceWitness.parentCells data.distinguished then
    Classical.choose
      (data.sourceWitness.source_witness data.distinguished cell hcell)
  else
    Classical.choose (cover.parent_hit data.distinguished)

/-- The actual shaded point paired with `sourceAnchorIndex` on a retained
cell.  Its value outside retained cells is irrelevant. -/
noncomputable def sourceAnchorPoint
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (cell : ℤ × ℤ × ℤ) : Point3 :=
  if hcell : cell ∈ data.sourceWitness.parentCells data.distinguished then
    Classical.choose
      (Classical.choose_spec
        (data.sourceWitness.source_witness
          data.distinguished cell hcell))
  else 0

lemma sourceAnchor_spec
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈
      data.sourceWitness.parentCells data.distinguished) :
    cover.toPaperTubeCover.parent (data.sourceAnchorIndex cell) =
        data.distinguished ∧
      data.sourceAnchorPoint cell ∈
        fineShading.carrier (data.sourceAnchorIndex cell) ∧
      data.sourceAnchorPoint cell ∈ wz1PaperGridCube rho cell := by
  simp only [sourceAnchorIndex, sourceAnchorPoint, dif_pos hcell]
  exact Classical.choose_spec (Classical.choose_spec
    (data.sourceWitness.source_witness data.distinguished cell hcell))

/-- A point retained by coarse Property (P) lies in a distinguished cell that
has a frozen honest source anchor. -/
lemma point_cell_mem_distinguished
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho)
    (point : Point3) (hpoint : point ∈ data.propertyThree.union) :
    wz1PaperGridIndex rho point ∈
      data.sourceWitness.parentCells data.distinguished := by
  rcases data.propertyP point hpoint with
    ⟨witness, hwitness, hpropertyCell⟩
  have hwitnessSource :
      witness ∈ data.sourceWitness.shading.carrier data.distinguished :=
    data.propertyThree_sub_witness data.distinguished hwitness
  rw [data.sourceWitness.shading_carrier_eq data.distinguished] at hwitnessSource
  rcases Set.mem_iUnion.mp hwitnessSource with ⟨cell, hwitnessSource⟩
  rcases Set.mem_iUnion.mp hwitnessSource with
    ⟨hcell, hwitnessCell⟩
  have hpaper : wz1PaperGridIndex rho point =
      wz1PaperGridIndex rho witness := by
    have hgrid := property_p_grid_index_eq_paper_grid_index hrho
    simpa [hgrid] using hpropertyCell
  have hwitnessIndex : wz1PaperGridIndex rho witness = cell :=
    (mem_wz1PaperGridCube rho cell witness).mp hwitnessCell
  rwa [hpaper, hwitnessIndex]

/-- The frozen cell anchor is within `sqrt(3) * rho` of every point in that
same coarse paper cell. -/
lemma point_dist_sourceAnchor_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho)
    (point : Point3)
    (hcell : wz1PaperGridIndex rho point ∈
      data.sourceWitness.parentCells data.distinguished) :
    dist point (data.sourceAnchorPoint (wz1PaperGridIndex rho point)) ≤
      rho * Real.sqrt 3 := by
  let cell := wz1PaperGridIndex rho point
  have hpointCell : point ∈ wz1PaperGridCube rho cell :=
    (mem_wz1PaperGridCube rho cell point).mpr rfl
  have hanchorCell := (data.sourceAnchor_spec cell hcell).2.2
  exact wz1PaperGridCube_diameter hrho cell hpointCell hanchorCell

/-- Every point in the honest fine pullback uses a coarse cell carrying a
frozen distinguished-parent source anchor. -/
lemma finePullback_point_cell_mem_distinguished
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho)
    (point : Point3)
    (hpoint : point ∈
      (propertyThreeFinePullbackShading
        cover fineShading data.propertyThree).union) :
    wz1PaperGridIndex rho point ∈
      data.sourceWitness.parentCells data.distinguished := by
  rcases hpoint with ⟨source, hsource⟩
  rcases propertyThreeFinePullbackShading_support
      cover fineShading data.propertyThree source point hsource with
    ⟨witness, hwitness, hgrid⟩
  have hwitnessCell := data.point_cell_mem_distinguished
    hrho witness hwitness
  simpa [hgrid] using hwitnessCell

/-- A fine-pullback point and its frozen honest source anchor occupy the same
coarse paper cell. -/
lemma finePullback_point_dist_sourceAnchor_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho)
    (point : Point3)
    (hpoint : point ∈
      (propertyThreeFinePullbackShading
        cover fineShading data.propertyThree).union) :
    dist point (data.sourceAnchorPoint (wz1PaperGridIndex rho point)) ≤
      rho * Real.sqrt 3 :=
  data.point_dist_sourceAnchor_le hrho point
    (data.finePullback_point_cell_mem_distinguished hrho point hpoint)

end PureWZ2BalancedSourceWitnessCoarsePropertyPData

/-- The generic source-witness selector retains at least an inverse square
fraction of the balanced active cells. -/
theorem PureWZ2BalancedSourceWitnessCoarsePropertyPData.activeCells_le_coarse_sq_goodCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho) :
    (balanced.activeCells.card : ENNReal) ≤
      coarse.enncard ^ 2 *
        ((propertyThreeGoodCells balanced data.propertyThree).card :
          ENNReal) := by
  let active : ENNReal := balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells balanced data.propertyThree).card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  let witnessMass := data.sourceWitness.shading.mass
  let propertyMass := data.propertyThree.mass
  let coarseCard := coarse.enncard
  have hcubeZero : cubeVolume ≠ 0 :=
    (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcubeTop : cubeVolume ≠ ⊤ :=
    wz1PaperGridCube_volume_ne_top hrho (0, 0, 0)
  by_cases hactiveZero : active = 0
  · change active ≤ coarse.enncard ^ 2 * good
    rw [hactiveZero]
    exact bot_le
  have hwitnessVolume :
      volume data.sourceWitness.shading.union = active * cubeVolume := by
    have hvolume :=
      balanced_cover_coarse_volume data.sourceWitness.balanced hrho
    rw [data.sourceWitness.balanced_activeCells_eq] at hvolume
    simpa [active, cubeVolume] using hvolume
  have hwitnessMassLower : active * cubeVolume ≤ witnessMass := by
    rw [← hwitnessVolume]
    simpa [witnessMass] using multiplicity_floor_le_mass
      (one_le_pointMultiplicity_on_union data.sourceWitness.shading)
  have hpropertyMassUpper : propertyMass ≤
      coarseCard * (good * cubeVolume) := by
    calc
      propertyMass ≤ coarseCard * volume data.propertyThree.union := by
        apply mass_le_of_pointMultiplicity_le
        intro point hpoint
        have hnat : data.propertyThree.pointMultiplicity point ≤
            (wz1PaperBodyFamily coarse).card := by
          change
            ((Finset.univ : Finset (Fin coarse.card)).filter
              fun parent => point ∈ data.propertyThree.carrier parent).card ≤
              (wz1PaperBodyFamily coarse).card
          simpa only [Fintype.card_fin] using
            (Finset.card_le_univ
              ((Finset.univ : Finset (Fin coarse.card)).filter
                fun parent => point ∈ data.propertyThree.carrier parent))
        simpa [coarseCard, Kakeya.Streamlined.TubeFamily.enncard,
          wz1PaperBodyFamily] using
          (show (data.propertyThree.pointMultiplicity point : ENNReal) ≤
              ((wz1PaperBodyFamily coarse).card : ENNReal) by
            exact_mod_cast hnat)
      _ = coarseCard * (good * cubeVolume) := by
        rw [propertyThree_volume_eq_goodCells balanced
          data.propertyThree_sub data.propertyThree_cubical hrho]
  have henergy : witnessMass ^ 2 ≤
      (active * cubeVolume) * coarseCard * propertyMass := by
    have hunion :
        volume data.sourceWitness.shading.union = active * cubeVolume :=
      hwitnessVolume
    simpa [witnessMass, propertyMass, coarseCard, hunion] using data.energy
  have hchain : (active * cubeVolume) ^ 2 ≤
      (active * cubeVolume) *
        (coarseCard ^ 2 * good * cubeVolume) := by
    calc
      (active * cubeVolume) ^ 2 ≤ witnessMass ^ 2 := by gcongr
      _ ≤ (active * cubeVolume) * coarseCard * propertyMass := henergy
      _ ≤ (active * cubeVolume) * coarseCard *
          (coarseCard * (good * cubeVolume)) := by gcongr
      _ = (active * cubeVolume) *
          (coarseCard ^ 2 * good * cubeVolume) := by ring
  have hactiveCubeZero : active * cubeVolume ≠ 0 :=
    mul_ne_zero hactiveZero hcubeZero
  have hactiveCubeTop : active * cubeVolume ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact hcubeTop
  have hcancel : active * cubeVolume ≤
      coarseCard ^ 2 * good * cubeVolume := by
    apply (ENNReal.mul_le_mul_iff_right
      hactiveCubeZero hactiveCubeTop).mp
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hchain
  exact (ENNReal.mul_le_mul_iff_right hcubeZero hcubeTop).mp <| by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcancel

/-- The honest coarse Property-(P) selection restricts the balanced cover to
exactly its selected whole cells. -/
def PureWZ2BalancedSourceWitnessCoarsePropertyPData.balancedRestriction
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced) :
    PureWZ2BalancedCoverData cover
      (propertyThreeFinePullbackShading
        cover fineShading data.propertyThree)
      data.propertyThree :=
  wholeCellBalancedRestriction data.sourceWitness.balanced
    data.propertyThree_sub_witness data.propertyThree_cubical
    data.propertyThree_common_spatial

/-- Common-spatial fine shading selected by the generic source-witness
Property-(P) output. -/
def balancedSourceWitnessCommonHull
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced) :
    WZ1PaperTubeShading fine :=
  paperCommonSpatialHull fineShading
    (propertyThreeFinePullbackShading
      cover fineShading data.propertyThree)

lemma balancedSourceWitnessCommonHull_subshading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced) :
    PaperIsSubshading
      (balancedSourceWitnessCommonHull data) fineShading :=
  paperCommonSpatialHull_subshading _ _

lemma balancedSourceWitnessCommonHull_union
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced) :
    (balancedSourceWitnessCommonHull data).union =
      (propertyThreeFinePullbackShading
        cover fineShading data.propertyThree).union :=
  paperCommonSpatialHull_union
    (propertyThreeFinePullbackShading_subshading
      cover fineShading data.propertyThree)

/-- Without a dyadic multiplicity band, the honest source-witness common
hull still loses at most `#fine * #coarse^2`.  This weaker polynomial bound
is sufficient when a later loss gap absorbs all finite geometric costs. -/
theorem PureWZ2BalancedSourceWitnessCoarsePropertyPData.commonHull_mass_lower
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho) :
    ((fine.enncard * coarse.enncard ^ 2 : ENNReal)⁻¹) *
        fineShading.mass ≤
      (balancedSourceWitnessCommonHull data).mass := by
  let active : ENNReal := balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells balanced data.propertyThree).card
  let cellMass : ENNReal := balanced.cellMass
  have hcount : active ≤ coarse.enncard ^ 2 * good := by
    simpa [active, good] using
      data.activeCells_le_coarse_sq_goodCells hrho
  have hsourceVolume :
      volume fineShading.union = active * cellMass := by
    simpa [active, cellMass] using
      balanced_cover_fine_union_volume balanced hrho
  have htargetVolume :
      volume (balancedSourceWitnessCommonHull data).union =
        good * cellMass := by
    rw [balancedSourceWitnessCommonHull_union data]
    simpa [good, cellMass] using
      propertyThreeFinePullback_volume_eq_goodCells
        balanced data.propertyThree_sub
  have hsourceMass : fineShading.mass ≤
      fine.enncard * (active * cellMass) := by
    calc
      fineShading.mass ≤ fine.enncard * volume fineShading.union := by
        apply mass_le_of_pointMultiplicity_le
        intro point _
        have hnat : fineShading.pointMultiplicity point ≤
            (wz1PaperBodyFamily fine).card := by
          change
            ((Finset.univ : Finset (Fin fine.card)).filter
              fun index => point ∈ fineShading.carrier index).card ≤
              (wz1PaperBodyFamily fine).card
          simpa only [Fintype.card_fin] using Finset.card_le_univ
            ((Finset.univ : Finset (Fin fine.card)).filter
              fun index => point ∈ fineShading.carrier index)
        simpa [Kakeya.Streamlined.TubeFamily.enncard,
          wz1PaperBodyFamily] using
          (show (fineShading.pointMultiplicity point : ENNReal) ≤
              ((wz1PaperBodyFamily fine).card : ENNReal) by
            exact_mod_cast hnat)
      _ = fine.enncard * (active * cellMass) := by rw [hsourceVolume]
  have htargetMass : good * cellMass ≤
      (balancedSourceWitnessCommonHull data).mass := by
    rw [← htargetVolume]
    simpa using multiplicity_floor_le_mass
      (one_le_pointMultiplicity_on_union
        (balancedSourceWitnessCommonHull data))
  have hfineZero : fine.enncard ≠ 0 := by
    have hnonempty : fine.Nonempty :=
      Nat.zero_lt_of_lt (data.sourceAnchorIndex (0, 0, 0)).isLt
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using hnonempty.ne'
  have hcoarseZero : coarse.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      (Nat.zero_lt_of_lt data.distinguished.isLt).ne'
  have hfineTop : fine.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hcoarseTop : coarse.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hlossZero : fine.enncard * coarse.enncard ^ 2 ≠ 0 :=
    mul_ne_zero hfineZero (pow_ne_zero _ hcoarseZero)
  have hlossTop : fine.enncard * coarse.enncard ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top hfineTop (ENNReal.pow_ne_top hcoarseTop)
  calc
    (fine.enncard * coarse.enncard ^ 2)⁻¹ * fineShading.mass ≤
        (fine.enncard * coarse.enncard ^ 2)⁻¹ *
          (fine.enncard * (active * cellMass)) := by gcongr
    _ = (coarse.enncard ^ 2)⁻¹ * (active * cellMass) := by
      have hcancel : fine.enncard⁻¹ * fine.enncard = 1 :=
        ENNReal.inv_mul_cancel hfineZero hfineTop
      rw [ENNReal.mul_inv (Or.inl hfineZero) (Or.inl hfineTop)]
      rw [show
        (fine.enncard⁻¹ * (coarse.enncard ^ 2)⁻¹) *
              (fine.enncard * (active * cellMass)) =
            (fine.enncard⁻¹ * fine.enncard) *
              ((coarse.enncard ^ 2)⁻¹ * (active * cellMass)) by ring,
        hcancel, one_mul]
    _ ≤ good * cellMass := by
      calc
        (coarse.enncard ^ 2)⁻¹ * (active * cellMass) =
            ((coarse.enncard ^ 2)⁻¹ * active) * cellMass := by ring
        _ ≤ good * cellMass := by
          gcongr
          calc
            (coarse.enncard ^ 2)⁻¹ * active ≤
                (coarse.enncard ^ 2)⁻¹ *
                  (coarse.enncard ^ 2 * good) := by gcongr
            _ = good := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel
                (pow_ne_zero _ hcoarseZero)
                (ENNReal.pow_ne_top hcoarseTop), one_mul]
    _ ≤ (balancedSourceWitnessCommonHull data).mass := htargetMass

/-- On a dyadic-multiplicity balanced fine shading, the generic nested
source-witness selection loses only `2 * #coarse^2`. -/
theorem PureWZ2BalancedSourceWitnessCoarsePropertyPData.commonHull_mass_lower_of_dyadic
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (data : PureWZ2BalancedSourceWitnessCoarsePropertyPData balanced)
    (hrho : 0 < rho)
    (multiplicity : ℕ)
    (hsourceLower : ∀ point ∈ fineShading.union,
      multiplicity ≤ fineShading.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈ fineShading.union,
      fineShading.pointMultiplicity point < 2 * multiplicity) :
    ((2 * coarse.enncard ^ 2 : ENNReal)⁻¹) * fineShading.mass ≤
      (balancedSourceWitnessCommonHull data).mass := by
  let active : ENNReal := balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells balanced data.propertyThree).card
  let cellMass : ENNReal := balanced.cellMass
  have hcount : active ≤ coarse.enncard ^ 2 * good := by
    simpa [active, good] using
      data.activeCells_le_coarse_sq_goodCells hrho
  have hsourceVolume :
      volume fineShading.union = active * cellMass := by
    simpa [active, cellMass] using
      balanced_cover_fine_union_volume balanced hrho
  have hpullbackVolume :
      volume
          (propertyThreeFinePullbackShading
            cover fineShading data.propertyThree).union =
        good * cellMass := by
    simpa [good, cellMass] using
      propertyThreeFinePullback_volume_eq_goodCells
        balanced data.propertyThree_sub
  have hsourceMass :
      fineShading.mass ≤
        (2 * multiplicity : ENNReal) * (active * cellMass) := by
    calc
      fineShading.mass ≤ (2 * multiplicity : ENNReal) *
          volume fineShading.union := by
        apply mass_le_of_pointMultiplicity_le
        intro point hpoint
        exact_mod_cast (hsourceUpper point hpoint).le
      _ = (2 * multiplicity : ENNReal) *
          (active * cellMass) := by rw [hsourceVolume]
  have htargetMultiplicity : ∀ point ∈
      (balancedSourceWitnessCommonHull data).union,
      multiplicity ≤
        (balancedSourceWitnessCommonHull data).pointMultiplicity point := by
    intro point hpoint
    have hmultiplicity :
        (balancedSourceWitnessCommonHull data).pointMultiplicity point =
          fineShading.pointMultiplicity point := by
      change
        (paperCommonSpatialHull fineShading
          (propertyThreeFinePullbackShading
            cover fineShading data.propertyThree)).pointMultiplicity point =
          fineShading.pointMultiplicity point
      exact paperCommonSpatialHull_pointMultiplicity_eq
        fineShading
        (propertyThreeFinePullbackShading
          cover fineShading data.propertyThree) point hpoint
    rw [hmultiplicity]
    have hsourcePoint : point ∈ fineShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, balancedSourceWitnessCommonHull_subshading
        data index hindex⟩
    exact hsourceLower point hsourcePoint
  have htargetMass :
      (multiplicity : ENNReal) * (good * cellMass) ≤
        (balancedSourceWitnessCommonHull data).mass := by
    calc
      (multiplicity : ENNReal) * (good * cellMass) =
          (multiplicity : ENNReal) *
            volume (balancedSourceWitnessCommonHull data).union := by
        rw [balancedSourceWitnessCommonHull_union data, hpullbackVolume]
      _ ≤ _ := multiplicity_floor_le_mass fun point hpoint => by
        exact_mod_cast htargetMultiplicity point hpoint
  have hcoarseZero : coarse.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      (Nat.zero_lt_of_lt data.distinguished.isLt).ne'
  have hcoarseTop : coarse.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hcoarseSqZero : coarse.enncard ^ 2 ≠ 0 :=
    pow_ne_zero _ hcoarseZero
  have hcoarseSqTop : coarse.enncard ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top hcoarseTop
  have hinverseTwo : (2 : ENNReal)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hinverseLoss :
      (2 * coarse.enncard ^ 2 : ENNReal)⁻¹ =
        (2 : ENNReal)⁻¹ * (coarse.enncard ^ 2)⁻¹ := by
    exact ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hnormalized :
      (coarse.enncard ^ 2)⁻¹ * active ≤ good := by
    calc
      (coarse.enncard ^ 2)⁻¹ * active ≤
          (coarse.enncard ^ 2)⁻¹ *
            (coarse.enncard ^ 2 * good) := by gcongr
      _ = good := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel
          hcoarseSqZero hcoarseSqTop, one_mul]
  have hnormalizedMass :
      (coarse.enncard ^ 2)⁻¹ * (active * cellMass) ≤
        good * cellMass := by
    calc
      (coarse.enncard ^ 2)⁻¹ * (active * cellMass) =
          ((coarse.enncard ^ 2)⁻¹ * active) * cellMass := by ring
      _ ≤ good * cellMass := by gcongr
  calc
    ((2 * coarse.enncard ^ 2 : ENNReal)⁻¹) * fineShading.mass ≤
        ((2 * coarse.enncard ^ 2 : ENNReal)⁻¹) *
          ((2 * multiplicity : ENNReal) *
            (active * cellMass)) := by gcongr
    _ = (multiplicity : ENNReal) *
        (coarse.enncard ^ 2)⁻¹ * (active * cellMass) := by
      rw [hinverseLoss]
      rw [show (2 * multiplicity : ENNReal) =
        2 * (multiplicity : ENNReal) by norm_num]
      rw [show
        ((2 : ENNReal)⁻¹ * (coarse.enncard ^ 2)⁻¹) *
              (2 * (multiplicity : ENNReal) * (active * cellMass)) =
            ((2 : ENNReal)⁻¹ * 2) * (multiplicity : ENNReal) *
              (coarse.enncard ^ 2)⁻¹ * (active * cellMass) by ring]
      rw [hinverseTwo, one_mul]
    _ ≤ (multiplicity : ENNReal) * (good * cellMass) := by
      calc
        (multiplicity : ENNReal) *
              (coarse.enncard ^ 2)⁻¹ * (active * cellMass) =
            (multiplicity : ENNReal) *
              ((coarse.enncard ^ 2)⁻¹ *
                (active * cellMass)) := by ring
        _ ≤ (multiplicity : ENNReal) * (good * cellMass) :=
          mul_le_mul_left' hnormalizedMass _
    _ ≤ _ := htargetMass

end Kakeya.Assouad.PureWZ2

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase1
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers

/-! Whole-cell pullback of a coarse Property-P shading to the selected fine family. -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The existential Section 6 cover has a canonical unique parent map.
Existence is `covers`, surjectivity is `parent_hit`, and uniqueness follows
from coarse essential distinctness plus the triangle inequality. -/
def PureWZ2Section6Cover.toPaperTubeCover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse) :
    WZ1PaperTubeCover fine coarse where
  parent := PureWZ2.selectParent cover
  parent_surjective := by
    intro parent
    rcases cover.parent_hit parent with ⟨source, hsource⟩
    refine ⟨source, ?_⟩
    have hparent : PureWZ2.selectParent cover source = parent := by
      by_contra hne
      have hdist :
          wz1PaperLineDistance
              (coarse.tube parent)
              (coarse.tube (PureWZ2.selectParent cover source)) ≤ rho := by
        calc
          wz1PaperLineDistance
              (coarse.tube parent)
              (coarse.tube (PureWZ2.selectParent cover source))
              ≤ wz1PaperLineDistance (coarse.tube parent) (fine.tube source) +
                  wz1PaperLineDistance (fine.tube source)
                    (coarse.tube (PureWZ2.selectParent cover source)) :=
                wz1PaperLineDistance_triangle _ _ _
          _ = wz1PaperLineDistance (fine.tube source) (coarse.tube parent) +
                  wz1PaperLineDistance (fine.tube source)
                    (coarse.tube (PureWZ2.selectParent cover source)) := by
                rw [wz1PaperLineDistance_symm]
          _ ≤ rho / 2 + rho / 2 := by
                exact add_le_add hsource (PureWZ2.selectedParent_covers cover source)
          _ = rho := by ring
      exact (not_lt_of_ge hdist)
        (cover.coarse_essentially_distinct parent
          (PureWZ2.selectParent cover source) (Ne.symm hne))
    exact hparent
  parent_covers := PureWZ2.selectedParent_covers cover
  parent_unique := by
    intro source candidate hcandidate
    by_contra hne
    have hdist :
        wz1PaperLineDistance
            (coarse.tube candidate)
            (coarse.tube (PureWZ2.selectParent cover source)) ≤ rho := by
      calc
        wz1PaperLineDistance
            (coarse.tube candidate)
            (coarse.tube (PureWZ2.selectParent cover source))
            ≤ wz1PaperLineDistance (coarse.tube candidate) (fine.tube source) +
                wz1PaperLineDistance (fine.tube source)
                  (coarse.tube (PureWZ2.selectParent cover source)) :=
              wz1PaperLineDistance_triangle _ _ _
        _ = wz1PaperLineDistance (fine.tube source) (coarse.tube candidate) +
                wz1PaperLineDistance (fine.tube source)
                  (coarse.tube (PureWZ2.selectParent cover source)) := by
              rw [wz1PaperLineDistance_symm]
        _ ≤ rho / 2 + rho / 2 := by
              exact add_le_add hcandidate (PureWZ2.selectedParent_covers cover source)
        _ = rho := by ring
    exact (not_lt_of_ge hdist)
      (cover.coarse_essentially_distinct candidate
        (PureWZ2.selectParent cover source) hne)

lemma PureWZ2Section6Cover.fullFiberIndices_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperFullFiberIndices fine coarse parent =
      cover.toPaperTubeCover.fiberIndices parent := by
  ext source
  rw [mem_wz2PaperFullFiberIndices_iff]
  simp only [WZ1PaperTubeCover.fiberIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hcovered
    exact (cover.toPaperTubeCover.parent_unique source parent hcovered).symm
  · intro hparent
    rw [← hparent]
    exact cover.toPaperTubeCover.parent_covers source

lemma PureWZ2Section6Cover.fullFiberPointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) (point : Point3) :
    wz2PaperFullFiberPointMultiplicity coarse shading parent point =
      cover.toPaperTubeCover.fiberPointMultiplicity shading parent point := by
  simp only [wz2PaperFullFiberPointMultiplicity,
    WZ1PaperTubeCover.fiberPointMultiplicity]
  rw [cover.fullFiberIndices_eq parent]

namespace PureWZ2

/-- Fine points lying in a `rho`-grid cell touched by the retained coarse
Property-P shading.  Property-P is a global whole-cell restriction, so this
selection is deliberately by spatial cell, not by an assigned parent. -/
def propertyThreeFinePullbackShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (propertyThree : WZ1PaperTubeShading coarse) :
    WZ1PaperTubeShading fine := by
  let touchedCells : Set (ℤ × ℤ × ℤ) :=
    wz1PaperGridIndex rho '' propertyThree.union
  let grid : Point3 → ℤ × ℤ × ℤ := wz1PaperGridIndex rho
  have hgrid : Measurable grid := by
    have h : Measurable (fun p : Point3 =>
        (⌊p 0 / rho⌋, ⌊p 1 / rho⌋, ⌊p 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext p
    simp [grid, wz1PaperGridIndex, gridIndex]
  exact
    { carrier := fun index =>
        fineShading.carrier index ∩ grid ⁻¹' touchedCells
      measurable_carrier := by
        intro index
        exact (fineShading.measurable_carrier index).inter
          (hgrid MeasurableSet.of_discrete)
      subset_body := fun index =>
        Set.inter_subset_left.trans (fineShading.subset_body index) }

@[simp] lemma propertyThreeFinePullbackShading_carrier
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (propertyThree : WZ1PaperTubeShading coarse)
    (index : Fin fine.card) :
    (propertyThreeFinePullbackShading cover fineShading propertyThree).carrier index =
      fineShading.carrier index ∩
        (wz1PaperGridIndex rho) ⁻¹'
          (wz1PaperGridIndex rho '' propertyThree.union) := by
  rfl

lemma propertyThreeFinePullbackShading_subshading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (propertyThree : WZ1PaperTubeShading coarse) :
    PaperIsSubshading
      (propertyThreeFinePullbackShading cover fineShading propertyThree)
      fineShading :=
  fun _ => Set.inter_subset_left

/-- Every retained fine point has a Property-P witness in its exact coarse
grid cell. -/
lemma propertyThreeFinePullbackShading_support
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (propertyThree : WZ1PaperTubeShading coarse) :
    ∀ index point,
      point ∈ (propertyThreeFinePullbackShading cover fineShading propertyThree).carrier index →
        ∃ witness,
          witness ∈ propertyThree.union ∧
          wz1PaperGridIndex rho witness = wz1PaperGridIndex rho point := by
  intro index point hpoint
  rcases hpoint.2 with ⟨witness, hwitness, hcell⟩
  exact ⟨witness, hwitness, hcell⟩

/-- If the coarse selection consists of whole coarse cells, every point of
its fine pullback still lies in the coarse geometric union. -/
lemma propertyThreeFinePullbackShading_union_subset
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (propertyThree : WZ1PaperTubeShading coarse)
    (hcubical : WZ1PaperIsCubicalShading propertyThree) :
    (propertyThreeFinePullbackShading cover fineShading propertyThree).union ⊆
      propertyThree.union := by
  rintro point ⟨source, hsource⟩
  rcases propertyThreeFinePullbackShading_support
      cover fineShading propertyThree source point hsource with
    ⟨witness, ⟨parent, hwitness⟩, hgrid⟩
  refine ⟨parent, hcubical parent witness hwitness ?_⟩
  exact (mem_wz1PaperGridCube rho
    (wz1PaperGridIndex rho witness) point).mpr hgrid.symm

/-- A whole-cell global Property-P restriction contains every retained fine
point in the carrier of its selected geometric parent. -/
lemma propertyThreeFinePullbackShading_point_compatibility
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hproperty_cubical : WZ1PaperIsCubicalShading propertyThree)
    (hglobal : ∀ parent, propertyThree.carrier parent =
      coarseShading.carrier parent ∩ propertyThree.union) :
    ∀ source point,
      point ∈ (propertyThreeFinePullbackShading cover fineShading propertyThree).carrier source →
        point ∈ propertyThree.carrier (selectParent cover source) := by
  intro source point hpoint
  rcases propertyThreeFinePullbackShading_support
      cover fineShading propertyThree source point hpoint with
    ⟨witness, hwitness, hcell⟩
  have hpoint_property : point ∈ propertyThree.union := by
    rcases hwitness with ⟨parent, hwitnessParent⟩
    refine ⟨parent, hproperty_cubical parent witness hwitnessParent ?_⟩
    exact (mem_wz1PaperGridCube rho
      (wz1PaperGridIndex rho witness) point).mpr hcell.symm
  have hpoint_coarse :
      point ∈ coarseShading.carrier (selectParent cover source) :=
    balanced.point_compatibility source (selectParent cover source)
      (selectedParent_covers cover source) point hpoint.1
  rw [hglobal]
  exact ⟨hpoint_coarse, hpoint_property⟩

/-- At an integer-aligned scale `rho = K * delta`, whole coarse-cell pullback
preserves the fine cubical convention. -/
lemma propertyThreeFinePullbackShading_cubical
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (propertyThree : WZ1PaperTubeShading coarse)
    (hcubical : WZ1PaperIsCubicalShading fineShading)
    (K : ℕ) (hK_pos : 0 < K)
    (hrho : rho = (K : ℝ) * delta) :
    WZ1PaperIsCubicalShading
      (propertyThreeFinePullbackShading cover fineShading propertyThree) := by
  intro index point hpoint other hother
  have hotherFine : other ∈ fineShading.carrier index :=
    hcubical index point hpoint.1 hother
  have hdeltaCell :
      wz1PaperGridIndex delta other = wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta (wz1PaperGridIndex delta point) other).mp hother
  have hrhoCell :
      wz1PaperGridIndex rho other = wz1PaperGridIndex rho point :=
    wz1PaperGridIndex_fine_to_coarse K hK_pos hrho hdeltaCell
  refine ⟨hotherFine, ?_⟩
  simpa [hrhoCell] using hpoint.2

end PureWZ2

end Kakeya.Assouad

end

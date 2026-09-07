import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma43
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionAlignment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullback

/-!
# The Lemma 4.4 step in Proposition 6.3

This module records the dependent form of the second scale change in
`wz2_63.tex`, lines 254--274.  It starts from the actual weak-plane-map
refinement supplied by Lemma 4.3 and from Proposition 6.2 data applied to
that same refinement.

For every active coarse cell we choose one genuine point of the fine
refinement.  A coarse parent is retained on that whole cell precisely when
the chosen point lies in one of its fine children.  Thus every retained
coarse cell meets the fine refinement, and the coarse plane map is literally
the value of the fine map at that point.  No regularity of the fine plane map
is used here; Lipschitz regularization belongs to the later Lemma 4.7 step.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- Point multiplicity is bounded by the cardinality of the ambient fine
family. -/
private lemma proposition63Lemma44_pointMultiplicity_le_card
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (fineShading : WZ1PaperTubeShading fine) (point : Point3) :
    fineShading.pointMultiplicity point ≤ fine.card := by
  change
    (Finset.univ.filter fun index : Fin fine.card =>
      point ∈ fineShading.carrier index).card ≤ fine.card
  simpa using Finset.card_le_card
    (Finset.filter_subset
      (fun index : Fin fine.card => point ∈ fineShading.carrier index)
      Finset.univ)

/-- Every active balanced coarse cell contains a point at which the fine
point multiplicity is maximal on the fine union inside that cell.  The set of
points need not be finite: its multiplicities lie in the finite set
`{0, ..., fine.card}`. -/
private lemma proposition63Lemma44_exists_max_representative
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ balanced.activeCells) :
    ∃ representative,
      representative ∈ fineShading.union ∧
      representative ∈ wz1PaperGridCube rho cell ∧
      ∀ point, point ∈ fineShading.union →
        point ∈ wz1PaperGridCube rho cell →
          fineShading.pointMultiplicity point ≤
            fineShading.pointMultiplicity representative := by
  let realized : Finset ℕ :=
    (Finset.range (fine.card + 1)).filter fun multiplicity =>
      ∃ point,
        point ∈ fineShading.union ∧
        point ∈ wz1PaperGridCube rho cell ∧
        fineShading.pointMultiplicity point = multiplicity
  have realized_nonempty : realized.Nonempty := by
    rcases balanced.cellIntersection_nonempty cell hcell with
      ⟨point, point_union, point_cell⟩
    refine ⟨fineShading.pointMultiplicity point, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
      (proposition63Lemma44_pointMultiplicity_le_card fineShading point)), ?_⟩
    exact ⟨point, point_union, point_cell, rfl⟩
  rcases Finset.exists_max_image realized id realized_nonempty with
    ⟨maximum, maximum_mem, maximum_is_max⟩
  rcases (Finset.mem_filter.mp maximum_mem).2 with
    ⟨representative, representative_union, representative_cell,
      representative_multiplicity⟩
  refine ⟨representative, representative_union, representative_cell, ?_⟩
  intro point point_union point_cell
  have point_mem : fineShading.pointMultiplicity point ∈ realized := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
      (proposition63Lemma44_pointMultiplicity_le_card fineShading point)), ?_⟩
    exact ⟨point, point_union, point_cell, rfl⟩
  simpa [id, representative_multiplicity] using
    maximum_is_max (fineShading.pointMultiplicity point) point_mem

/-- The maximal fine point-multiplicity representative in an active coarse
cell.  Outside the finite active set its value is irrelevant. -/
noncomputable def proposition63Lemma44CellRepresentative
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : ℤ × ℤ × ℤ) : Point3 :=
  if hcell : cell ∈ balanced.activeCells then
    Classical.choose
      (proposition63Lemma44_exists_max_representative balanced cell hcell)
  else
    0

lemma proposition63Lemma44CellRepresentative_in_union
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ balanced.activeCells) :
    proposition63Lemma44CellRepresentative balanced cell ∈
      fineShading.union := by
  simp only [proposition63Lemma44CellRepresentative, dif_pos hcell]
  exact (Classical.choose_spec
    (proposition63Lemma44_exists_max_representative
      balanced cell hcell)).1

lemma proposition63Lemma44CellRepresentative_in_cell
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ balanced.activeCells) :
    proposition63Lemma44CellRepresentative balanced cell ∈
      wz1PaperGridCube rho cell := by
  simp only [proposition63Lemma44CellRepresentative, dif_pos hcell]
  exact (Classical.choose_spec
    (proposition63Lemma44_exists_max_representative
      balanced cell hcell)).2.1

lemma proposition63Lemma44CellRepresentative_maximal
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ balanced.activeCells)
    (point : Point3) (point_union : point ∈ fineShading.union)
    (point_cell : point ∈ wz1PaperGridCube rho cell) :
    fineShading.pointMultiplicity point ≤
      fineShading.pointMultiplicity
        (proposition63Lemma44CellRepresentative balanced cell) := by
  simp only [proposition63Lemma44CellRepresentative, dif_pos hcell]
  exact (Classical.choose_spec
    (proposition63Lemma44_exists_max_representative
      balanced cell hcell)).2.2 point point_union point_cell

/-- Parent--cell incidences associated to the one common fine representative
of a coarse cell, as in the proof of Lemma 12. -/
def proposition63Lemma44ParentCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (parent : Fin coarse.card) : Finset (ℤ × ℤ × ℤ) :=
  balanced.activeCells.filter fun cell =>
    ∃ source : Fin fine.card,
      cover.toPaperTubeCover.parent source = parent ∧
        proposition63Lemma44CellRepresentative balanced cell ∈
          fineShading.carrier source

/-- The coarse shading consisting exactly of the associated parent--cell
pairs.  Each retained carrier is a union of whole `rho`-cells. -/
noncomputable def proposition63Lemma44CoarseShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading) :
    WZ1PaperTubeShading coarse where
  carrier parent :=
    ⋃ cell ∈ proposition63Lemma44ParentCells balanced parent,
      wz1PaperGridCube rho cell
  measurable_carrier parent := by
    apply MeasurableSet.iUnion
    intro cell
    apply MeasurableSet.iUnion
    intro _
    exact wz1PaperGridCube_measurable cell
  subset_body parent := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    rcases (Finset.mem_filter.mp hcell).2 with
      ⟨source, hsourceParent, hrepresentative⟩
    have hrepresentativeCoarse :
        proposition63Lemma44CellRepresentative balanced cell ∈
          coarseShading.carrier parent := by
      rw [← hsourceParent]
      exact balanced.point_compatibility source
        (cover.toPaperTubeCover.parent source)
        (cover.toPaperTubeCover.parent_covers source)
        (proposition63Lemma44CellRepresentative balanced cell)
        hrepresentative
    have hwhole := balanced.coarse_cubical parent
      (proposition63Lemma44CellRepresentative balanced cell)
      hrepresentativeCoarse
    have hactive : cell ∈ balanced.activeCells :=
      (Finset.mem_filter.mp hcell).1
    have hrepresentativeCell :
        proposition63Lemma44CellRepresentative balanced cell ∈
          wz1PaperGridCube rho cell := by
      exact proposition63Lemma44CellRepresentative_in_cell
        balanced cell hactive
    have hrepresentativeIndex :
        wz1PaperGridIndex rho
            (proposition63Lemma44CellRepresentative balanced cell) = cell :=
      (mem_wz1PaperGridCube rho cell _).mp hrepresentativeCell
    apply coarseShading.subset_body parent
    apply hwhole
    rwa [hrepresentativeIndex]

lemma proposition63Lemma44CoarseShading_subshading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading) :
    PaperIsSubshading
      (proposition63Lemma44CoarseShading balanced) coarseShading := by
  intro parent point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointCell⟩
  rcases (Finset.mem_filter.mp hcell).2 with
    ⟨source, hsourceParent, hrepresentative⟩
  have hrepresentativeCoarse :
      proposition63Lemma44CellRepresentative balanced cell ∈
        coarseShading.carrier parent := by
    rw [← hsourceParent]
    exact balanced.point_compatibility source
      (cover.toPaperTubeCover.parent source)
      (cover.toPaperTubeCover.parent_covers source)
      (proposition63Lemma44CellRepresentative balanced cell)
      hrepresentative
  have hwhole := balanced.coarse_cubical parent
    (proposition63Lemma44CellRepresentative balanced cell)
    hrepresentativeCoarse
  have hactive : cell ∈ balanced.activeCells :=
    (Finset.mem_filter.mp hcell).1
  have hrepresentativeCell :
      proposition63Lemma44CellRepresentative balanced cell ∈
        wz1PaperGridCube rho cell := by
    exact proposition63Lemma44CellRepresentative_in_cell
      balanced cell hactive
  have hrepresentativeIndex :
      wz1PaperGridIndex rho
          (proposition63Lemma44CellRepresentative balanced cell) = cell :=
    (mem_wz1PaperGridCube rho cell _).mp hrepresentativeCell
  apply hwhole
  rwa [hrepresentativeIndex]

lemma proposition63Lemma44CoarseShading_cubical
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading) :
    WZ1PaperIsCubicalShading
      (proposition63Lemma44CoarseShading balanced) := by
  intro parent point hpoint other hother
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointCell⟩
  have hpointIndex : wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  have hotherCell : other ∈ wz1PaperGridCube rho cell := by
    apply (mem_wz1PaperGridCube rho cell other).mpr
    exact ((mem_wz1PaperGridCube rho
      (wz1PaperGridIndex rho point) other).mp hother).trans hpointIndex
  exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hotherCell⟩

/-- The associated-cell construction deletes parent memberships, not spatial
cells: its union is exactly the Proposition 6.2 coarse union. -/
lemma proposition63Lemma44CoarseShading_union_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading) :
    (proposition63Lemma44CoarseShading balanced).union =
      coarseShading.union := by
  apply Set.Subset.antisymm
  · rintro point ⟨parent, hpoint⟩
    exact ⟨parent,
      proposition63Lemma44CoarseShading_subshading balanced parent hpoint⟩
  · intro point hpoint
    rw [balanced.coarse_union_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have hrepFine :
        proposition63Lemma44CellRepresentative balanced cell ∈
          fineShading.union := by
      exact proposition63Lemma44CellRepresentative_in_union
        balanced cell hcell
    rcases hrepFine with ⟨source, hsource⟩
    let parent := cover.toPaperTubeCover.parent source
    have hparentCell :
        cell ∈ proposition63Lemma44ParentCells balanced parent := by
      apply Finset.mem_filter.mpr
      exact ⟨hcell, source, rfl, hsource⟩
    exact ⟨parent, Set.mem_iUnion₂.mpr
      ⟨cell, hparentCell, hpointCell⟩⟩

/-- Every retained coarse cell contains the actual fine representative from
which its normal is sampled. -/
lemma proposition63Lemma44CoarseShading_representative
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    {point : Point3}
    (hpoint : point ∈
      (proposition63Lemma44CoarseShading balanced).union) :
    proposition63Lemma44CellRepresentative balanced
        (wz1PaperGridIndex rho point) ∈ fineShading.union ∧
      wz1PaperGridIndex rho
          (proposition63Lemma44CellRepresentative balanced
            (wz1PaperGridIndex rho point)) =
        wz1PaperGridIndex rho point := by
  rcases hpoint with ⟨parent, hpointParent⟩
  rcases Set.mem_iUnion₂.mp hpointParent with
    ⟨cell, hcell, hpointCell⟩
  have hpointIndex : wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  rcases (Finset.mem_filter.mp hcell).2 with
    ⟨source, _hsourceParent, hsource⟩
  have hrepCell :
      proposition63Lemma44CellRepresentative balanced cell ∈
        wz1PaperGridCube rho cell := by
    have hactive := (Finset.mem_filter.mp hcell).1
    exact proposition63Lemma44CellRepresentative_in_cell
      balanced cell hactive
  constructor
  · rw [hpointIndex]
    exact ⟨source, hsource⟩
  · rw [hpointIndex]
    exact (mem_wz1PaperGridCube rho cell _).mp hrepCell

/-- A coarse point stores an actual fine child through the common
representative of its cell. -/
lemma proposition63Lemma44CoarseShading_associated
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    {parent : Fin coarse.card} {point : Point3}
    (hpoint : point ∈
      (proposition63Lemma44CoarseShading balanced).carrier parent) :
    ∃ source : Fin fine.card,
      cover.toPaperTubeCover.parent source = parent ∧
        proposition63Lemma44CellRepresentative balanced
            (wz1PaperGridIndex rho point) ∈
          fineShading.carrier source := by
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointCell⟩
  have hpointIndex : wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  rcases (Finset.mem_filter.mp hcell).2 with
    ⟨source, hsourceParent, hsource⟩
  exact ⟨source, hsourceParent, by simpa [hpointIndex] using hsource⟩

/-- Pointwise finite Fubini at one point.  Unlike the global helper, this
version only asks for parent compatibility at the queried point; that is the
form available for the common representative selected in Lemma 4.4. -/
private lemma proposition63Lemma44_pointMultiplicity_le_at
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (point : Point3)
    (pointCompatibility :
      ∀ source, point ∈ fineShading.carrier source →
        point ∈ coarseShading.carrier (cover.parent source))
    (fiberCap : ENNReal)
    (fiberMultiplicity : ∀ parent,
      (cover.fiberPointMultiplicity fineShading parent point : ENNReal) ≤
        fiberCap) :
    (fineShading.pointMultiplicity point : ENNReal) ≤
      (coarseShading.pointMultiplicity point : ENNReal) * fiberCap := by
  let fineAtPoint : Finset (Fin fine.card) :=
    Finset.univ.filter fun source => point ∈ fineShading.carrier source
  let coarseAtPoint : Finset (Fin coarse.card) :=
    Finset.univ.filter fun parent => point ∈ coarseShading.carrier parent
  have mapsTo :
      Set.MapsTo cover.parent
        (fineAtPoint : Set (Fin fine.card))
        (coarseAtPoint : Set (Fin coarse.card)) := by
    intro source source_mem
    have source_point : point ∈ fineShading.carrier source :=
      (Finset.mem_filter.mp source_mem).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, pointCompatibility source source_point⟩
  have fiberCard : ∀ parent,
      (fineAtPoint.filter fun source => cover.parent source = parent).card =
        cover.fiberPointMultiplicity fineShading parent point := by
    intro parent
    congr 1
    ext source
    constructor
    · intro source_mem
      have outer := Finset.mem_filter.mp source_mem
      have source_point : point ∈ fineShading.carrier source :=
        (Finset.mem_filter.mp outer.1).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, source_point⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ source, outer.2⟩
    · intro source_mem
      have outer := Finset.mem_filter.mp source_mem
      have source_parent : cover.parent source = parent :=
        (Finset.mem_filter.mp outer.1).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, source_parent⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ source, outer.2⟩
  have card_decomposition :
      fineAtPoint.card =
        ∑ parent ∈ coarseAtPoint,
          cover.fiberPointMultiplicity fineShading parent point := by
    rw [Finset.card_eq_sum_card_fiberwise mapsTo]
    exact Finset.sum_congr rfl fun parent _ => fiberCard parent
  have decomposition :
      (fineShading.pointMultiplicity point : ENNReal) =
        ∑ parent ∈ coarseAtPoint,
          (cover.fiberPointMultiplicity fineShading parent point : ENNReal) := by
    change (fineAtPoint.card : ENNReal) = _
    exact_mod_cast card_decomposition
  have sum_le :
      (∑ parent ∈ coarseAtPoint,
          (cover.fiberPointMultiplicity fineShading parent point : ENNReal)) ≤
        (coarseAtPoint.card : ENNReal) * fiberCap := by
    calc
      (∑ parent ∈ coarseAtPoint,
          (cover.fiberPointMultiplicity fineShading parent point : ENNReal)) ≤
          ∑ _parent ∈ coarseAtPoint, fiberCap := by
            exact Finset.sum_le_sum fun parent _ =>
              fiberMultiplicity parent
      _ = (coarseAtPoint.card : ENNReal) * fiberCap := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have coarse_card :
      (coarseAtPoint.card : ENNReal) =
        (coarseShading.pointMultiplicity point : ENNReal) := by
    rfl
  rw [decomposition, ← coarse_card]
  exact sum_le

/-- The maximal common representative converts the terminal full-fiber cap
into the pointwise Lemma 4.4 comparison, with no coarse-cardinality loss. -/
theorem proposition63Lemma44_pointMultiplicity_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fiberCap : ENNReal)
    (fiberMultiplicity : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤ fiberCap) :
    ∀ point,
      (fineShading.pointMultiplicity point : ENNReal) ≤
        fiberCap *
          ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
            point : ENNReal) := by
  intro point
  by_cases point_union : point ∈ fineShading.union
  · let cell := wz1PaperGridIndex rho point
    have point_coarse : point ∈ coarseShading.union := by
      rcases point_union with ⟨source, source_point⟩
      exact ⟨cover.toPaperTubeCover.parent source,
        balanced.point_compatibility source
          (cover.toPaperTubeCover.parent source)
          (cover.toPaperTubeCover.parent_covers source) point source_point⟩
    have cell_active : cell ∈ balanced.activeCells := by
      rw [balanced.coarse_union_eq] at point_coarse
      rcases Set.mem_iUnion₂.mp point_coarse with
        ⟨otherCell, other_active, point_otherCell⟩
      have cell_eq : cell = otherCell :=
        (mem_wz1PaperGridCube rho otherCell point).mp point_otherCell
      rwa [cell_eq]
    let representative :=
      proposition63Lemma44CellRepresentative balanced cell
    have representative_union : representative ∈ fineShading.union :=
      proposition63Lemma44CellRepresentative_in_union
        balanced cell cell_active
    have representative_cell :
        representative ∈ wz1PaperGridCube rho cell :=
      proposition63Lemma44CellRepresentative_in_cell
        balanced cell cell_active
    have point_cell : point ∈ wz1PaperGridCube rho cell :=
      (mem_wz1PaperGridCube rho cell point).mpr rfl
    have fine_le_representative :
        fineShading.pointMultiplicity point ≤
          fineShading.pointMultiplicity representative :=
      proposition63Lemma44CellRepresentative_maximal
        balanced cell cell_active point point_union point_cell
    have representative_compatibility : ∀ source,
        representative ∈ fineShading.carrier source →
          representative ∈
            (proposition63Lemma44CoarseShading balanced).carrier
              (cover.toPaperTubeCover.parent source) := by
      intro source source_mem
      have parent_cell : cell ∈
          proposition63Lemma44ParentCells balanced
            (cover.toPaperTubeCover.parent source) := by
        apply Finset.mem_filter.mpr
        exact ⟨cell_active, source, rfl, source_mem⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, parent_cell, representative_cell⟩
    have representative_bound :
        (fineShading.pointMultiplicity representative : ENNReal) ≤
          ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
            representative : ENNReal) * fiberCap :=
      proposition63Lemma44_pointMultiplicity_le_at
        cover.toPaperTubeCover fineShading
        (proposition63Lemma44CoarseShading balanced) representative
        representative_compatibility fiberCap
        (fun parent => fiberMultiplicity parent representative)
    have same_cell :
        wz1PaperGridIndex rho representative =
          wz1PaperGridIndex rho point := by
      exact ((mem_wz1PaperGridCube rho cell representative).mp
        representative_cell).trans rfl
    have coarse_multiplicity_eq :
        (proposition63Lemma44CoarseShading balanced).pointMultiplicity
            representative =
          (proposition63Lemma44CoarseShading balanced).pointMultiplicity
            point :=
      (proposition63Lemma44CoarseShading_cubical balanced)
        |>.pointMultiplicity_eq_of_same_cell same_cell
    calc
      (fineShading.pointMultiplicity point : ENNReal) ≤
          (fineShading.pointMultiplicity representative : ENNReal) := by
        exact_mod_cast fine_le_representative
      _ ≤
          ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
            representative : ENNReal) * fiberCap := representative_bound
      _ = fiberCap *
          ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
            point : ENNReal) := by
        rw [coarse_multiplicity_eq, mul_comm]
  · have point_zero : fineShading.pointMultiplicity point = 0 := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro source _ source_point
      exact point_union ⟨source, source_point⟩
    rw [point_zero]
    norm_num

/-- The paper's cellwise associated-parent comparison.  A lower bound for
the total fine multiplicity at the common representative, divided by the
full-fiber cap, retains a fixed proportion of the original coarse
multiplicity in that cell. -/
theorem proposition63Lemma44_associated_pointMultiplicity_lower
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fineFloor coarseCap fiberCap retention : ENNReal)
    (hfiberPos : 0 < fiberCap)
    (hfiberTop : fiberCap ≠ ⊤)
    (hrepresentativeFloor : ∀ cell ∈ balanced.activeCells,
      fineFloor ≤
        (fineShading.pointMultiplicity
          (proposition63Lemma44CellRepresentative balanced cell) : ENNReal))
    (hcoarseCap : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiberCap : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤ fiberCap)
    (hretention : retention * coarseCap * fiberCap ≤ fineFloor) :
    ∀ point,
      retention * (coarseShading.pointMultiplicity point : ENNReal) ≤
        ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
          point : ENNReal) := by
  intro point
  by_cases pointUnion : point ∈ coarseShading.union
  · rw [balanced.coarse_union_eq] at pointUnion
    rcases Set.mem_iUnion₂.mp pointUnion with
      ⟨cell, cellActive, pointCell⟩
    let representative :=
      proposition63Lemma44CellRepresentative balanced cell
    have representativeCell : representative ∈
        wz1PaperGridCube rho cell :=
      proposition63Lemma44CellRepresentative_in_cell
        balanced cell cellActive
    have representativeFloor : fineFloor ≤
        (fineShading.pointMultiplicity representative : ENNReal) :=
      hrepresentativeFloor cell cellActive
    have representativeUpper :
        (fineShading.pointMultiplicity representative : ENNReal) ≤
          fiberCap *
            ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
              representative : ENNReal) :=
      proposition63Lemma44_pointMultiplicity_le
        balanced fiberCap hfiberCap representative
    have sameCell : wz1PaperGridIndex rho representative =
        wz1PaperGridIndex rho point := by
      exact ((mem_wz1PaperGridCube rho cell representative).mp
        representativeCell).trans
          ((mem_wz1PaperGridCube rho cell point).mp pointCell).symm
    have associatedEq :
        (proposition63Lemma44CoarseShading balanced).pointMultiplicity
            representative =
          (proposition63Lemma44CoarseShading balanced).pointMultiplicity
            point :=
      (proposition63Lemma44CoarseShading_cubical balanced)
        |>.pointMultiplicity_eq_of_same_cell sameCell
    have scaled :
        (retention * (coarseShading.pointMultiplicity point : ENNReal)) *
            fiberCap ≤
          ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
            point : ENNReal) * fiberCap := by
      calc
        (retention *
              (coarseShading.pointMultiplicity point : ENNReal)) *
            fiberCap ≤ retention * coarseCap * fiberCap :=
          mul_le_mul_right'
            (mul_le_mul_left' (hcoarseCap point) retention) fiberCap
        _ ≤ fineFloor := hretention
        _ ≤ (fineShading.pointMultiplicity representative : ENNReal) :=
          representativeFloor
        _ ≤ fiberCap *
            ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
              representative : ENNReal) := representativeUpper
        _ =
            ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
              point : ENNReal) * fiberCap := by
              rw [associatedEq, mul_comm]
    apply (ENNReal.mul_le_mul_iff_right hfiberPos.ne' hfiberTop).mp
    simpa [mul_comm] using scaled
  · have originalZero : coarseShading.pointMultiplicity point = 0 := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro parent _ parentPoint
      exact pointUnion ⟨parent, parentPoint⟩
    rw [originalZero]
    simp

/-- Integrating the cellwise associated-parent comparison gives exactly the
indexed-mass retention used in paper Lemma 4.4. -/
theorem proposition63Lemma44_associated_mass_retention
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fineFloor coarseCap fiberCap retention : ENNReal)
    (hfiberPos : 0 < fiberCap)
    (hfiberTop : fiberCap ≠ ⊤)
    (hrepresentativeFloor : ∀ cell ∈ balanced.activeCells,
      fineFloor ≤
        (fineShading.pointMultiplicity
          (proposition63Lemma44CellRepresentative balanced cell) : ENNReal))
    (hcoarseCap : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiberCap : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤ fiberCap)
    (hretention : retention * coarseCap * fiberCap ≤ fineFloor) :
    retention * coarseShading.mass ≤
      (proposition63Lemma44CoarseShading balanced).mass := by
  have pointwise := proposition63Lemma44_associated_pointMultiplicity_lower
    balanced fineFloor coarseCap fiberCap retention hfiberPos hfiberTop
    hrepresentativeFloor hcoarseCap hfiberCap hretention
  calc
    retention * coarseShading.mass =
        ∫⁻ point, retention *
          (coarseShading.pointMultiplicity point : ENNReal) := by
      have measurableCoarse : Measurable fun point : Point3 =>
          (coarseShading.pointMultiplicity point : ENNReal) := by
        have pointMultiplicityEq :
            (fun point =>
              (coarseShading.pointMultiplicity point : ENNReal)) =
              fun point =>
                ∑ parent : Fin coarse.card,
                  Set.indicator (coarseShading.carrier parent)
                    (fun _ : Point3 => (1 : ENNReal)) point := by
          funext point
          exact coe_pointMultiplicity_eq_sum_indicator coarseShading point
        rw [pointMultiplicityEq]
        exact Finset.measurable_sum _ fun parent _ =>
          measurable_const.indicator
            (coarseShading.measurable_carrier parent)
      calc
        retention * coarseShading.mass =
            retention * ∫⁻ point,
              (coarseShading.pointMultiplicity point : ENNReal) := by
          rw [lintegral_pointMultiplicity]
        _ = ∫⁻ point, retention *
            (coarseShading.pointMultiplicity point : ENNReal) := by
          rw [MeasureTheory.lintegral_const_mul retention measurableCoarse]
    _ ≤ ∫⁻ point,
        ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
          point : ENNReal) := MeasureTheory.lintegral_mono pointwise
    _ = (proposition63Lemma44CoarseShading balanced).mass :=
      lintegral_pointMultiplicity _

/-- A retained proportion of a dense coarse shading remains dense, with the
density constant multiplied by that proportion. -/
theorem proposition63Lemma44_associated_dense
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fineFloor coarseCap fiberCap retention lambda : ENNReal)
    (hfiberPos : 0 < fiberCap)
    (hfiberTop : fiberCap ≠ ⊤)
    (hrepresentativeFloor : ∀ cell ∈ balanced.activeCells,
      fineFloor ≤
        (fineShading.pointMultiplicity
          (proposition63Lemma44CellRepresentative balanced cell) : ENNReal))
    (hcoarseCap : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiberCap : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤ fiberCap)
    (hretention : retention * coarseCap * fiberCap ≤ fineFloor)
    (hdense : coarseShading.IsLambdaDense lambda) :
    (proposition63Lemma44CoarseShading balanced).IsLambdaDense
      (retention * lambda) := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense] at hdense ⊢
  calc
    retention * lambda * (wz1PaperBodyFamily coarse).mass =
        retention * (lambda * (wz1PaperBodyFamily coarse).mass) := by ring
    _ ≤ retention * coarseShading.mass := by gcongr
    _ ≤ (proposition63Lemma44CoarseShading balanced).mass :=
      proposition63Lemma44_associated_mass_retention
        balanced fineFloor coarseCap fiberCap retention hfiberPos hfiberTop
        hrepresentativeFloor hcoarseCap hfiberCap hretention

/-- Integrating the common-representative comparison gives the sharp
aggregate Lemma 4.4 mass bridge. -/
theorem proposition63Lemma44_fine_mass_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fiberCap : ENNReal)
    (fiberMultiplicity : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤ fiberCap) :
    fineShading.mass ≤
      fiberCap * (proposition63Lemma44CoarseShading balanced).mass := by
  have pointwise := proposition63Lemma44_pointMultiplicity_le
    balanced fiberCap fiberMultiplicity
  have measurable_coarse : Measurable fun point =>
      ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
        point : ENNReal) := by
    have pointMultiplicity_eq :
        (fun point =>
          ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
            point : ENNReal)) =
          fun point =>
            ∑ parent : Fin coarse.card,
              Set.indicator
                ((proposition63Lemma44CoarseShading balanced).carrier parent)
                (fun _ : Point3 => (1 : ENNReal)) point := by
      funext point
      exact coe_pointMultiplicity_eq_sum_indicator
        (proposition63Lemma44CoarseShading balanced) point
    rw [pointMultiplicity_eq]
    exact Finset.measurable_sum _ fun parent _ =>
      measurable_const.indicator
        ((proposition63Lemma44CoarseShading balanced).measurable_carrier
          parent)
  calc
    fineShading.mass =
        ∫⁻ point, (fineShading.pointMultiplicity point : ENNReal) :=
      (lintegral_pointMultiplicity fineShading).symm
    _ ≤ ∫⁻ point, fiberCap *
        ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
          point : ENNReal) := MeasureTheory.lintegral_mono pointwise
    _ = fiberCap * ∫⁻ point,
        ((proposition63Lemma44CoarseShading balanced).pointMultiplicity
          point : ENNReal) := by
      rw [MeasureTheory.lintegral_const_mul fiberCap measurable_coarse]
    _ = fiberCap *
        (proposition63Lemma44CoarseShading balanced).mass := by
      rw [lintegral_pointMultiplicity]

/-- Restrict the Lemma 4.3 map to the precise fine family selected by the
second Proposition 6.2 call. -/
noncomputable def proposition63Lemma44FinePlaneMap
    {delta incidence sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidence)
    {rho : WZ2PaperRequestedScale delta}
    {stickyLoss : ℝ} {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent) :
    PaperWZ1WeakPlaneMapData sticky.refined incidence where
  planeMap := lemma43.planeMap.planeMap
  measurable := lemma43.planeMap.measurable
  unit := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact lemma43.planeMap.unit point
      ⟨sticky.selected.embedding index, sticky.subshading index hindex⟩
  incidence := by
    intro index point hpoint
    have hraw := lemma43.planeMap.incidence
      (sticky.selected.embedding index) point
      (sticky.subshading index hpoint)
    simpa only [sticky.selected.tube_eq] using hraw

/-- The paper Lemma 12 coarse plane map from any synchronized fine weak map
and balanced fine/coarse pair, sampled at one common point in each active
coarse cell. -/
noncomputable def proposition63Lemma44CoarsePlaneMapOfBalanced
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (fineMap : PaperWZ1WeakPlaneMapData fineShading (rho / 2))
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading) :
    PaperWZ1WeakPlaneMapData
      (proposition63Lemma44CoarseShading balanced) rho where
  planeMap point :=
    fineMap.planeMap
      (proposition63Lemma44CellRepresentative balanced
        (wz1PaperGridIndex rho point))
  measurable := by
    have hrepresentative : Measurable
        (proposition63Lemma44CellRepresentative balanced) :=
      measurable_of_countable _
    have hgrid : Measurable (wz1PaperGridIndex rho) := by
      have h : Measurable (fun point : Point3 =>
          (⌊point 0 / rho⌋, ⌊point 1 / rho⌋,
            ⌊point 2 / rho⌋)) := by
        fun_prop
      convert h using 1
      funext point
      simp [wz1PaperGridIndex, gridIndex]
    exact fineMap.measurable.comp
      (hrepresentative.comp hgrid)
  unit := by
    intro point hpoint
    have hrepresentative :=
      proposition63Lemma44CoarseShading_representative
        balanced hpoint
    exact fineMap.unit _ hrepresentative.1
  incidence := by
    intro parent point hpoint
    rcases proposition63Lemma44CoarseShading_associated
        balanced hpoint with
      ⟨fineIndex, hparent, hrepresentative⟩
    let representative := proposition63Lemma44CellRepresentative
      balanced (wz1PaperGridIndex rho point)
    have hfine :
        |inner ℝ (fine.tube fineIndex).direction
            (fineMap.planeMap representative)| ≤ rho / 2 :=
      fineMap.incidence fineIndex representative hrepresentative
    have hcover : WZ1PaperTubeCovers
        (fine.tube fineIndex)
        (coarse.tube parent) := by
      rw [← hparent]
      exact cover.toPaperTubeCover.parent_covers fineIndex
    have hfinePaper :
        |inner ℝ (wz1PaperDirection
            (fine.tube fineIndex))
            (fineMap.planeMap representative)| ≤ rho / 2 := by
      have heq :
          |inner ℝ (wz1PaperDirection
              (fine.tube fineIndex))
              (fineMap.planeMap representative)| =
            |inner ℝ (fine.tube fineIndex).direction
              (fineMap.planeMap representative)| := by
        unfold wz1PaperDirection
        split_ifs <;> simp [inner_neg_left]
      rw [heq]
      exact hfine
    have hparentIncidence := paper_cover_parent_incidence
      (incidence := rho / 2) hcover
      (fineMap.unit representative ⟨fineIndex, hrepresentative⟩)
      hfinePaper
    have hraw :
        |inner ℝ (coarse.tube parent).direction
            (fineMap.planeMap representative)| ≤ rho := by
      have heq :
          |inner ℝ (coarse.tube parent).direction
              (fineMap.planeMap representative)| =
            |inner ℝ (wz1PaperDirection (coarse.tube parent))
              (fineMap.planeMap representative)| := by
        unfold wz1PaperDirection
        split_ifs <;> simp [inner_neg_left]
      rw [heq]
      calc
        |inner ℝ (wz1PaperDirection (coarse.tube parent))
            (fineMap.planeMap representative)| ≤
            rho / 2 + rho / 2 := hparentIncidence
        _ = rho := by
          ring
    exact hraw

/-- The paper Lemma 12 coarse plane map, sampled at one common fine point in
each active coarse cell. -/
noncomputable def proposition63Lemma44CoarsePlaneMap
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {stickyLoss : ℝ} {logExponent : ℕ}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source (rho.1 / 2))
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent) :
    PaperWZ1WeakPlaneMapData
      (proposition63Lemma44CoarseShading sticky.balanced) rho.1 :=
  proposition63Lemma44CoarsePlaneMapOfBalanced
    (proposition63Lemma44FinePlaneMap lemma43 sticky) sticky.balanced

lemma proposition63Lemma44CoarsePlaneMapOfBalanced_constant_on_cells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (fineMap : PaperWZ1WeakPlaneMapData fineShading (rho / 2))
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading) :
    ∀ first second,
      wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
      (proposition63Lemma44CoarsePlaneMapOfBalanced fineMap balanced).planeMap
          first =
        (proposition63Lemma44CoarsePlaneMapOfBalanced fineMap balanced).planeMap
          second := by
  intro first second same_cell
  simp only [proposition63Lemma44CoarsePlaneMapOfBalanced]
  rw [same_cell]

lemma proposition63Lemma44CoarsePlaneMap_constant_on_cells
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {stickyLoss : ℝ} {logExponent : ℕ}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source (rho.1 / 2))
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent) :
    ∀ first second,
      wz1PaperGridIndex rho.1 first =
        wz1PaperGridIndex rho.1 second →
      (proposition63Lemma44CoarsePlaneMap lemma43 sticky).planeMap first =
        (proposition63Lemma44CoarsePlaneMap lemma43 sticky).planeMap second := by
  intro first second hcell
  exact proposition63Lemma44CoarsePlaneMapOfBalanced_constant_on_cells
    (proposition63Lemma44FinePlaneMap lemma43 sticky) sticky.balanced
    first second hcell

/-- The complete paper Lemma 12 output used by Proposition 6.3. -/
structure Proposition63Lemma44Data
    {delta sigma sourceLoss lemma43Loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {stickyLoss : ℝ} {logExponent : ℕ}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2))
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent)
    (outputLoss : ℝ) where
  fineShading : WZ1PaperTubeShading sticky.selected.family
  fine_subshading : ∀ index point, point ∈ fineShading.carrier index →
    point ∈ source.carrier (sticky.selected.embedding index)
  coarseShading : WZ1PaperTubeShading sticky.coarse
  coarse_subshading : PaperIsSubshading coarseShading
    sticky.croppedCoarseShading
  coarse_extremal : WZ2PaperCroppedIsExtremal
    sigma outputLoss sticky.coarse coarseShading
  planeMap : PaperWZ1WeakPlaneMapData coarseShading rho.1
  planeMap_constant_on_cells : ∀ first second,
    wz1PaperGridIndex rho.1 first = wz1PaperGridIndex rho.1 second →
      planeMap.planeMap first = planeMap.planeMap second
  coarse_point_has_fine_witness : ∀ point ∈ coarseShading.union,
    ∃ finePoint ∈ fineShading.union,
      wz1PaperGridIndex rho.1 finePoint =
        wz1PaperGridIndex rho.1 point

/-- Proposition 6.2 plus the Lemma 4.3 map give the paper's Lemma 4.4
coarse pair.  The only loss after Proposition 6.2 is deletion of unsupported
parent--cell memberships; its exact multiplicity cost is exposed in
`hrestore`. -/
theorem proposition63_paper_lemma44_coarse_pair
    {delta sigma sourceLoss lemma43Loss stickyLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2))
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent)
    (hstickyOutput : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore :
      (Kakeya.realRpowENN rho.1 (2 - sigma - stickyLoss) *
          sticky.coarse.enncard) *
          Kakeya.realRpowENN rho.1 outputLoss ≤
        Kakeya.realRpowENN rho.1 stickyLoss) :
    Nonempty (Proposition63Lemma44Data lemma43 sticky outputLoss) := by
  let coarseShading :=
    proposition63Lemma44CoarseShading sticky.balanced
  let multiplicityCap : ENNReal :=
    Kakeya.realRpowENN rho.1 (2 - sigma - stickyLoss) *
      sticky.coarse.enncard
  have hcapZero : multiplicityCap ≠ 0 := by
    apply mul_ne_zero
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos sticky.coarse_extremal.delta_pos _)).ne'
    · simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        sticky.coarse_extremal.nonempty.ne'
  have hcapTop : multiplicityCap ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hcoarseMass : multiplicityCap⁻¹ *
      sticky.croppedCoarseShading.mass ≤ coarseShading.mass := by
    have horiginalMass : sticky.croppedCoarseShading.mass ≤
        multiplicityCap * volume sticky.croppedCoarseShading.union :=
      mass_le_of_pointMultiplicity_le fun point _ =>
        sticky.coarse_multiplicity_upper point
    have hselectedVolume : volume coarseShading.union ≤ coarseShading.mass := by
      simpa using multiplicity_floor_le_mass
        (one_le_pointMultiplicity_on_union coarseShading)
    calc
      multiplicityCap⁻¹ * sticky.croppedCoarseShading.mass ≤
          multiplicityCap⁻¹ *
            (multiplicityCap * volume sticky.croppedCoarseShading.union) := by
        gcongr
      _ = volume sticky.croppedCoarseShading.union := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcapZero hcapTop, one_mul]
      _ = volume coarseShading.union := by
        rw [proposition63Lemma44CoarseShading_union_eq sticky.balanced]
      _ ≤ coarseShading.mass := hselectedVolume
  have hcoarseExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss sticky.coarse coarseShading := by
    apply transfer_cropped_extremal_to_subshading multiplicityCap
      (bot_lt_iff_ne_bot.mpr hcapZero) hcapTop sticky.coarse_extremal
      (proposition63Lemma44CoarseShading_subshading sticky.balanced)
      hcoarseMass
      (proposition63Lemma44CoarseShading_cubical sticky.balanced)
      hstickyOutput
    · simpa [multiplicityCap] using hrestore
    · exact sticky.coarse_extremal.delta_pos
    · exact sticky.coarse_extremal.delta_le_one
    · exact houtputLoss
  refine ⟨{
    fineShading := sticky.refined
    coarseShading := coarseShading
    fine_subshading := ?_
    coarse_subshading :=
      proposition63Lemma44CoarseShading_subshading sticky.balanced
    coarse_extremal := hcoarseExtremal
    planeMap := proposition63Lemma44CoarsePlaneMap lemma43 sticky
    planeMap_constant_on_cells :=
      proposition63Lemma44CoarsePlaneMap_constant_on_cells lemma43 sticky
    coarse_point_has_fine_witness := ?_
  }⟩
  · intro index point hpoint
    exact lemma43.subshading _ (sticky.subshading index hpoint)
  · intro point hpoint
    let finePoint := proposition63Lemma44CellRepresentative
      sticky.balanced (wz1PaperGridIndex rho.1 point)
    have hrepresentative :=
      proposition63Lemma44CoarseShading_representative
        sticky.balanced hpoint
    exact ⟨finePoint, hrepresentative.1, hrepresentative.2⟩

end Kakeya.Assouad.PureWZ2

end

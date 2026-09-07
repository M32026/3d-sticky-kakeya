import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseFiniteLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BalancedFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeBalancedRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RebalancedFiniteRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RebalancedSourceWitnessCoarsePlaneMap
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Exact aligned residue refinement

When `rho = K * delta`, a literal `rho`-cell contains exactly `K^3` literal
`delta`-cell residue classes.  In every occupied coarse cell, keep the residue
carrying maximal indexed shaded mass.  The loss is exactly `K^3`, while the
surviving fine union in each retained coarse cell is one complete `delta`-cube.
This restores a genuine balanced cover without a point-multiplicity band or a
boundary layer.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private def alignedGridResidue
    (K : ℕ) (hK : 0 < K) (cell : ℤ × ℤ × ℤ) :
    Fin K × Fin K × Fin K :=
  let residue (value : ℤ) : Fin K :=
    ⟨(value % (K : ℤ)).toNat, by
      have hnonnegative : 0 ≤ value % (K : ℤ) :=
        Int.emod_nonneg value (by exact_mod_cast hK.ne')
      have hlt : value % (K : ℤ) < (K : ℤ) :=
        Int.emod_lt_of_pos value (by exact_mod_cast hK)
      omega⟩
  (residue cell.1, residue cell.2.1, residue cell.2.2)

private lemma aligned_coarse_grid_index_eq_ediv
    {delta rho : ℝ} (hdelta : 0 < delta)
    (K : ℕ) (hK : 0 < K)
    (hrho : rho = (K : ℝ) * delta)
    (point : Point3) :
    wz1PaperGridIndex rho point =
      ((wz1PaperGridIndex delta point).1 / (K : ℤ),
        (wz1PaperGridIndex delta point).2.1 / (K : ℤ),
        (wz1PaperGridIndex delta point).2.2 / (K : ℤ)) := by
  have hcoordinate : ∀ coordinate : Fin 3,
      ⌊point coordinate / rho⌋ =
        ⌊point coordinate / delta⌋ / (K : ℤ) := by
    intro coordinate
    rw [hrho]
    have hrewrite : point coordinate / ((K : ℝ) * delta) =
        (point coordinate / delta) / (K : ℝ) := by
      field_simp [hdelta.ne', hK.ne']
    rw [hrewrite]
    exact Int.floor_div_natCast (point coordinate / delta) K
  simp only [wz1PaperGridIndex, gridIndex]
  exact Prod.ext (hcoordinate 0)
    (Prod.ext (hcoordinate 1) (hcoordinate 2))

private lemma int_eq_of_ediv_emod_eq
    (K : ℕ) (first second : ℤ)
    (hdiv : first / (K : ℤ) = second / (K : ℤ))
    (hmod : first % (K : ℤ) = second % (K : ℤ)) :
    first = second := by
  calc
    first = first / (K : ℤ) * (K : ℤ) + first % (K : ℤ) :=
      (Int.ediv_mul_add_emod first (K : ℤ)).symm
    _ = second / (K : ℤ) * (K : ℤ) + second % (K : ℤ) := by
      rw [hdiv, hmod]
    _ = second := Int.ediv_mul_add_emod second (K : ℤ)

private lemma aligned_grid_residue_coordinate_eq
    (K : ℕ) (hK : 0 < K)
    {first second : ℤ}
    (hresidue :
      (⟨(first % (K : ℤ)).toNat, by
          have hnonnegative : 0 ≤ first % (K : ℤ) :=
            Int.emod_nonneg first (by exact_mod_cast hK.ne')
          have hlt : first % (K : ℤ) < (K : ℤ) :=
            Int.emod_lt_of_pos first (by exact_mod_cast hK)
          omega⟩ : Fin K) =
        ⟨(second % (K : ℤ)).toNat, by
          have hnonnegative : 0 ≤ second % (K : ℤ) :=
            Int.emod_nonneg second (by exact_mod_cast hK.ne')
          have hlt : second % (K : ℤ) < (K : ℤ) :=
            Int.emod_lt_of_pos second (by exact_mod_cast hK)
          omega⟩) :
    first % (K : ℤ) = second % (K : ℤ) := by
  have hnat := congrArg Fin.val hresidue
  have hfirstNonnegative : 0 ≤ first % (K : ℤ) :=
    Int.emod_nonneg first (by exact_mod_cast hK.ne')
  have hsecondNonnegative : 0 ≤ second % (K : ℤ) :=
    Int.emod_nonneg second (by exact_mod_cast hK.ne')
  rw [← Int.toNat_of_nonneg hfirstNonnegative,
    ← Int.toNat_of_nonneg hsecondNonnegative]
  exact_mod_cast hnat

private lemma aligned_fine_index_eq_of_coarse_residue
    {delta rho : ℝ} (hdelta : 0 < delta)
    (K : ℕ) (hK : 0 < K)
    (hrho : rho = (K : ℝ) * delta)
    {first second : Point3}
    (hcoarse : wz1PaperGridIndex rho first =
      wz1PaperGridIndex rho second)
    (hresidue : alignedGridResidue K hK
        (wz1PaperGridIndex delta first) =
      alignedGridResidue K hK
        (wz1PaperGridIndex delta second)) :
    wz1PaperGridIndex delta first = wz1PaperGridIndex delta second := by
  let firstIndex := wz1PaperGridIndex delta first
  let secondIndex := wz1PaperGridIndex delta second
  have hdivTuple :
      (firstIndex.1 / (K : ℤ), firstIndex.2.1 / (K : ℤ),
          firstIndex.2.2 / (K : ℤ)) =
        (secondIndex.1 / (K : ℤ), secondIndex.2.1 / (K : ℤ),
          secondIndex.2.2 / (K : ℤ)) := by
    rw [← aligned_coarse_grid_index_eq_ediv hdelta K hK hrho first,
      ← aligned_coarse_grid_index_eq_ediv hdelta K hK hrho second]
    exact hcoarse
  have hdiv0 : firstIndex.1 / (K : ℤ) = secondIndex.1 / (K : ℤ) :=
    congrArg Prod.fst hdivTuple
  have hdiv1 : firstIndex.2.1 / (K : ℤ) =
      secondIndex.2.1 / (K : ℤ) :=
    congrArg (fun value => value.2.1) hdivTuple
  have hdiv2 : firstIndex.2.2 / (K : ℤ) =
      secondIndex.2.2 / (K : ℤ) :=
    congrArg (fun value => value.2.2) hdivTuple
  have hresidue0 := congrArg (fun value => value.1) hresidue
  have hresidue1 := congrArg (fun value => value.2.1) hresidue
  have hresidue2 := congrArg (fun value => value.2.2) hresidue
  have hmod0 : firstIndex.1 % (K : ℤ) = secondIndex.1 % (K : ℤ) := by
    exact aligned_grid_residue_coordinate_eq K hK hresidue0
  have hmod1 : firstIndex.2.1 % (K : ℤ) =
      secondIndex.2.1 % (K : ℤ) := by
    exact aligned_grid_residue_coordinate_eq K hK hresidue1
  have hmod2 : firstIndex.2.2 % (K : ℤ) =
      secondIndex.2.2 % (K : ℤ) := by
    exact aligned_grid_residue_coordinate_eq K hK hresidue2
  exact Prod.ext
    (int_eq_of_ediv_emod_eq K firstIndex.1 secondIndex.1 hdiv0 hmod0)
    (Prod.ext
      (int_eq_of_ediv_emod_eq K firstIndex.2.1 secondIndex.2.1
        hdiv1 hmod1)
      (int_eq_of_ediv_emod_eq K firstIndex.2.2 secondIndex.2.2
        hdiv2 hmod2))

/-- The part of a Section 6 cover/shading pair needed before aligned residue
balancing.  Exact balance is the output of the residue selector, not a
premise of this compatibility interface. -/
structure PureWZ2CompatibleCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse) : Prop where
  point_compatibility :
    ∀ source parent,
      WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
        ∀ point, point ∈ fineShading.carrier source →
          point ∈ coarseShading.carrier parent
  coarse_cubical : WZ1PaperIsCubicalShading coarseShading

def balancedCoverToCompatible
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading) :
    PureWZ2CompatibleCoverData cover fineShading coarseShading where
  point_compatibility := balanced.point_compatibility
  coarse_cubical := balanced.coarse_cubical

/-- A finite planiness shading restricted to one aligned fine-cell residue in
each occupied coarse cell, together with the resulting honest balanced cover. -/
structure AlignedResidueFiniteRefinementData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading)
    (K : ℕ) where
  selected : WZ1PaperTubeShading fine
  selected_subshading : PaperIsSubshading selected candidate
  selected_cubical : WZ1PaperIsCubicalShading selected
  mass_retention : candidate.mass ≤ (K ^ 3 : ENNReal) * selected.mass
  coarse : WZ1PaperTubeShading coarse
  coarse_subshading : PaperIsSubshading coarse coarseShading
  balanced : PureWZ2BalancedCoverData cover selected coarse
  fine_cube_subset_coarse_cube : ∀ source point,
    point ∈ selected.carrier source →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        wz1PaperGridCube rho (wz1PaperGridIndex rho point)

/-- Select the heaviest aligned fine-cell residue separately in every
occupied coarse cell. -/
theorem aligned_residue_finite_refinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading)
    (hcandidateSub : PaperIsSubshading candidate fineShading)
    (hcandidateCubical : WZ1PaperIsCubicalShading candidate)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho = (K : ℝ) * delta) :
    Nonempty (AlignedResidueFiniteRefinementData
      (candidate := candidate) compatible K) := by
  let coarseCell : Point3 → ℤ × ℤ × ℤ := wz1PaperGridIndex rho
  let fineResidue : Point3 → Fin K × Fin K × Fin K := fun point =>
    alignedGridResidue K hK (wz1PaperGridIndex delta point)
  let candidateFineCells := wz1PaperActiveCells candidate hdelta
  let candidateCoarseCells : Finset (ℤ × ℤ × ℤ) :=
    candidateFineCells.image fun fineCell =>
      wz1PaperGridIndex rho (cellCorner delta fineCell)
  have hcoarseMeasurable : Measurable coarseCell := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / rho⌋, ⌊point 1 / rho⌋, ⌊point 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [coarseCell, wz1PaperGridIndex, gridIndex]
  have hfineResidueMeasurable : Measurable fineResidue := by
    have hindex : Measurable (wz1PaperGridIndex delta) := by
      have h : Measurable (fun point : Point3 =>
          (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
            ⌊point 2 / delta⌋)) := by
        fun_prop
      convert h using 1
      funext point
      simp [wz1PaperGridIndex, gridIndex]
    exact (measurable_of_countable (alignedGridResidue K hK)).comp hindex
  have hsupport : ∀ point ∈ candidate.union,
      coarseCell point ∈ candidateCoarseCells := by
    intro point hpoint
    let fineCell := wz1PaperGridIndex delta point
    have hbody : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
      rcases hpoint with ⟨source, hsource⟩
      exact (candidate.subset_body source hsource).2
    have hfineActive : fineCell ∈ candidateFineCells := by
      rw [mem_wz1PaperActiveCells]
      refine ⟨paper_point_gridIndex_in_window hdelta hbody,
        point, hpoint, ?_⟩
      exact (mem_wz1PaperGridCube delta fineCell point).mpr rfl
    apply Finset.mem_image.mpr
    refine ⟨fineCell, hfineActive, ?_⟩
    have hcorner := cellCorner_mem_gridCube hdelta fineCell
    have hfineIndex : wz1PaperGridIndex delta point =
        wz1PaperGridIndex delta (cellCorner delta fineCell) := by
      exact rfl.trans ((mem_wz1PaperGridCube delta fineCell
        (cellCorner delta fineCell)).mp hcorner).symm
    exact (wz1PaperGridIndex_fine_to_coarse K hK hrhoAligned
      hfineIndex).symm
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  rcases paper_cellwise_finite_label_mass_refinement candidate
      coarseCell hcoarseMeasurable candidateCoarseCells hsupport
      fineResidue hfineResidueMeasurable
      (fun chosen => measurable_of_countable chosen) with
    ⟨chosen, selected, hselectedSub, hselectedEq, hselectedLabel,
      hselectedMass⟩
  have hcellConst : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        coarseCell first = coarseCell second := by
    intro first second hfine
    exact wz1PaperGridIndex_fine_to_coarse K hK hrhoAligned hfine
  have hlabelConst : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        fineResidue first = fineResidue second := by
    intro first second hfine
    exact congrArg (alignedGridResidue K hK) hfine
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    rw [hselectedEq]
    exact paperCellwiseLabelRestriction_cubical hcandidateCubical
      coarseCell hcoarseMeasurable fineResidue hfineResidueMeasurable
      chosen (measurable_of_countable chosen) hcellConst hlabelConst
  have hselectedMass' : candidate.mass ≤ (K ^ 3 : ENNReal) * selected.mass := by
    have hcard : Fintype.card (Fin K × Fin K × Fin K) = K ^ 3 := by
      simp [pow_succ]
      ring
    simpa [hcard] using hselectedMass

  let selectedFineCells := wz1PaperActiveCells selected hdelta
  let coarseParent : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun fineCell =>
    wz1PaperGridIndex rho (cellCorner delta fineCell)
  let retainedCoarseCells : Finset (ℤ × ℤ × ℤ) :=
    selectedFineCells.image coarseParent
  let restrictedCoarse : WZ1PaperTubeShading coarse :=
    coarseWholeCellRestriction coarseShading retainedCoarseCells

  have hactiveCellLabel : ∀ fineCell ∈ selectedFineCells,
      alignedGridResidue K hK fineCell = chosen (coarseParent fineCell) := by
    intro fineCell hfineCell
    let point := cellCorner delta fineCell
    have hpointCell : point ∈ wz1PaperGridCube delta fineCell :=
      cellCorner_mem_gridCube hdelta fineCell
    have hpointUnion : point ∈ selected.union := by
      have hinter := hselectedCubical.inter_activeCell_eq hdelta hfineCell
      have : point ∈ selected.union ∩ wz1PaperGridCube delta fineCell := by
        rw [hinter]
        exact hpointCell
      exact this.1
    have hlabel := hselectedLabel point hpointUnion
    have hfineIndex : wz1PaperGridIndex delta point = fineCell :=
      (mem_wz1PaperGridCube delta fineCell point).mp hpointCell
    simpa [fineResidue, coarseCell, coarseParent, hfineIndex] using hlabel
  have hcoarseParentInjective : Set.InjOn coarseParent selectedFineCells := by
    intro first hfirst second hsecond hparent
    let firstPoint := cellCorner delta first
    let secondPoint := cellCorner delta second
    have hfirstCell : firstPoint ∈ wz1PaperGridCube delta first :=
      cellCorner_mem_gridCube hdelta first
    have hsecondCell : secondPoint ∈ wz1PaperGridCube delta second :=
      cellCorner_mem_gridCube hdelta second
    have hfirstIndex : wz1PaperGridIndex delta firstPoint = first :=
      (mem_wz1PaperGridCube delta first firstPoint).mp hfirstCell
    have hsecondIndex : wz1PaperGridIndex delta secondPoint = second :=
      (mem_wz1PaperGridCube delta second secondPoint).mp hsecondCell
    have hresidue : alignedGridResidue K hK
        (wz1PaperGridIndex delta firstPoint) =
      alignedGridResidue K hK
        (wz1PaperGridIndex delta secondPoint) := by
      rw [hfirstIndex, hsecondIndex, hactiveCellLabel first hfirst,
        hactiveCellLabel second hsecond, hparent]
    have hcoarse : wz1PaperGridIndex rho firstPoint =
        wz1PaperGridIndex rho secondPoint := by
      simpa [coarseParent] using hparent
    exact hfirstIndex.symm.trans <|
      (aligned_fine_index_eq_of_coarse_residue hdelta K hK hrhoAligned
        hcoarse hresidue).trans hsecondIndex
  have hselectedUnion : selected.union =
      ⋃ fineCell ∈ selectedFineCells, wz1PaperGridCube delta fineCell :=
    hselectedCubical.union_eq_activeCells hdelta
  have hfineContained : ∀ fineCell ∈ selectedFineCells,
      wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho (coarseParent fineCell) := by
    intro fineCell _
    exact aligned_fine_grid_cube_subset_coarse_grid_cube
      hdelta K hK hrhoAligned fineCell
  have hretainedSubsetOriginal :
      (⋃ coarseCell ∈ retainedCoarseCells,
        wz1PaperGridCube rho coarseCell) ⊆ coarseShading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨coarseCell, hcoarseCell, hpointCell⟩
    rcases Finset.mem_image.mp hcoarseCell with
      ⟨fineCell, hfineCell, hparent⟩
    let witness := cellCorner delta fineCell
    have hwitnessFineCell : witness ∈ wz1PaperGridCube delta fineCell :=
      cellCorner_mem_gridCube hdelta fineCell
    have hwitnessSelected : witness ∈ selected.union := by
      rw [hselectedUnion]
      exact Set.mem_iUnion₂.mpr ⟨fineCell, hfineCell, hwitnessFineCell⟩
    rcases hwitnessSelected with ⟨source, hwitnessSource⟩
    let parent := cover.toPaperTubeCover.parent source
    have hwitnessOriginalFine : witness ∈ fineShading.carrier source :=
      hcandidateSub source (hselectedSub source hwitnessSource)
    have hwitnessCoarse : witness ∈ coarseShading.carrier parent :=
      compatible.point_compatibility source parent
        (cover.toPaperTubeCover.parent_covers source) witness
        hwitnessOriginalFine
    have hwitnessParentCell : wz1PaperGridIndex rho witness = coarseCell := by
      simpa [witness, coarseParent] using hparent
    exact ⟨parent, compatible.coarse_cubical parent witness hwitnessCoarse
      (by rwa [hwitnessParentCell])⟩
  have hcoarseUnion : restrictedCoarse.union =
      ⋃ coarseCell ∈ retainedCoarseCells,
        wz1PaperGridCube rho coarseCell := by
    apply Set.Subset.antisymm
    · rintro point ⟨parent, hpoint⟩
      exact hpoint.2
    · intro point hpoint
      rcases hretainedSubsetOriginal hpoint with ⟨parent, hparent⟩
      exact ⟨parent, hparent, hpoint⟩
  have hpointCompatibility : ∀ source parent,
      WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
      ∀ point, point ∈ selected.carrier source →
        point ∈ restrictedCoarse.carrier parent := by
    intro source parent hcover point hpoint
    have horiginal : point ∈ coarseShading.carrier parent :=
      compatible.point_compatibility source parent hcover point
        (hcandidateSub source (hselectedSub source hpoint))
    let fineCell := wz1PaperGridIndex delta point
    have hbody : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      (selected.subset_body source hpoint).2
    have hfineActive : fineCell ∈ selectedFineCells := by
      rw [mem_wz1PaperActiveCells]
      refine ⟨paper_point_gridIndex_in_window hdelta hbody,
        point, ⟨source, hpoint⟩, ?_⟩
      exact (mem_wz1PaperGridCube delta fineCell point).mpr rfl
    have hcoarseActive : coarseParent fineCell ∈ retainedCoarseCells :=
      Finset.mem_image.mpr ⟨fineCell, hfineActive, rfl⟩
    have hpointCoarseCell : point ∈
        wz1PaperGridCube rho (coarseParent fineCell) :=
      hfineContained fineCell hfineActive
        ((mem_wz1PaperGridCube delta fineCell point).mpr rfl)
    exact ⟨horiginal, Set.mem_iUnion₂.mpr
      ⟨coarseParent fineCell, hcoarseActive, hpointCoarseCell⟩⟩
  have hfineCellMass : ∀ coarseCell ∈ retainedCoarseCells,
      volume (selected.union ∩ wz1PaperGridCube rho coarseCell) =
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
    intro coarseCell hcoarseCell
    rcases Finset.mem_image.mp hcoarseCell with
      ⟨fineCell, hfineCell, hparent⟩
    have hset : selected.union ∩ wz1PaperGridCube rho coarseCell =
        wz1PaperGridCube delta fineCell := by
      apply Set.Subset.antisymm
      · rintro point ⟨hpointSelected, hpointCoarse⟩
        rw [hselectedUnion] at hpointSelected
        rcases Set.mem_iUnion₂.mp hpointSelected with
          ⟨otherFine, hotherFine, hpointOther⟩
        have hotherParent : coarseParent otherFine = coarseCell := by
          have hcontain := hfineContained otherFine hotherFine hpointOther
          have hfirst := (mem_wz1PaperGridCube rho
            (coarseParent otherFine) point).mp hcontain
          have hsecond := (mem_wz1PaperGridCube rho coarseCell point).mp
            hpointCoarse
          exact hfirst.symm.trans hsecond
        have heq : otherFine = fineCell :=
          hcoarseParentInjective hotherFine hfineCell
            (hotherParent.trans hparent.symm)
        rwa [heq] at hpointOther
      · intro point hpointFine
        refine ⟨?_, ?_⟩
        · rw [hselectedUnion]
          exact Set.mem_iUnion₂.mpr ⟨fineCell, hfineCell, hpointFine⟩
        · rw [← hparent]
          exact hfineContained fineCell hfineCell hpointFine
    rw [hset]
    exact wz1PaperGridCube_volume_eq hdelta fineCell (0, 0, 0)
  let newBalanced : PureWZ2BalancedCoverData cover selected restrictedCoarse :=
    { point_compatibility := hpointCompatibility
      coarse_cubical := coarseWholeCellRestriction_cubical
        compatible.coarse_cubical retainedCoarseCells
      activeCells := retainedCoarseCells
      coarse_union_eq := by
        simpa [restrictedCoarse] using hcoarseUnion
      cellMass := volume (wz1PaperGridCube delta (0, 0, 0))
      cellMass_pos := wz1PaperGridCube_volume_pos hdelta (0, 0, 0)
      cellMass_ne_top := wz1PaperGridCube_volume_ne_top hdelta (0, 0, 0)
      fine_cell_mass := hfineCellMass }
  have hfineInside : ∀ source point, point ∈ selected.carrier source →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        wz1PaperGridCube rho (wz1PaperGridIndex rho point) := by
    intro source point _
    let fineCell := wz1PaperGridIndex delta point
    have hcontain := aligned_fine_grid_cube_subset_coarse_grid_cube
      hdelta K hK hrhoAligned fineCell
    have hcorner := cellCorner_mem_gridCube hdelta fineCell
    have hsame : wz1PaperGridIndex rho point =
        wz1PaperGridIndex rho (cellCorner delta fineCell) :=
      wz1PaperGridIndex_fine_to_coarse K hK hrhoAligned
        (rfl.trans ((mem_wz1PaperGridCube delta fineCell
          (cellCorner delta fineCell)).mp hcorner).symm)
    rwa [hsame]
  exact ⟨{
    selected := selected
    selected_subshading := hselectedSub
    selected_cubical := hselectedCubical
    mass_retention := hselectedMass'
    coarse := restrictedCoarse
    coarse_subshading := coarseWholeCellRestriction_subshading _ _
    balanced := newBalanced
    fine_cube_subset_coarse_cube := hfineInside
  }⟩

/-- A sampled Lip-1 coarse plane map after aligned residue balancing. -/
structure AlignedFiniteCoarsePlaneMapData
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading)
    (finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading)
    (hdelta : 0 < delta) (K : ℕ) where
  residue : AlignedResidueFiniteRefinementData
    (candidate := finite.refinement.shading) compatible K
  sourceWitness : PureWZ2SourceWitnessCoarseShadingData residue.balanced
  sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
    (target := target) sourceWitness
  fine_mass_retention : finite.leftFactor * fineShading.mass ≤
    (finite.rightFactor * (K ^ 3 : ENNReal)) * residue.selected.mass

/-- Align, retain one heavy fine-cell residue per coarse cell, and sample the
finite planiness map on honest coarse source witnesses. -/
theorem aligned_finite_coarse_plane_map
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading)
    (finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho = (K : ℝ) * delta)
    (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ 1 / 5)
    (hbudget : finite.incidence + coefficient * (rho * Real.sqrt 3) +
      rho / 2 ≤ target) :
    Nonempty (AlignedFiniteCoarsePlaneMapData
      (target := target) compatible finite hdelta K) := by
  rcases aligned_residue_finite_refinement compatible
      finite.refinement.subshading finite.refinement.cubical hdelta hrho
      K hK hrhoAligned with ⟨residue⟩
  rcases source_witness_coarse_shading residue.balanced with
    ⟨sourceWitness⟩
  let selectedMap := paperWeakPlaneMapRestrict finite.refinement.planeMap
    residue.selected_subshading
  have hselectedLipschitz : LipschitzWith (Real.toNNReal coefficient)
      (fun point : {point : Point3 // point ∈ residue.selected.union} =>
        selectedMap.planeMap point) := by
    have hunion : residue.selected.union ⊆
        finite.refinement.shading.union := by
      rintro point ⟨source, hpoint⟩
      exact ⟨source, residue.selected_subshading source hpoint⟩
    intro first second
    exact finite.refinement.lipschitz
      ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
  have hcoefficientNN :
      ((Real.toNNReal coefficient : NNReal) : ℝ) ≤ 1 / 5 := by
    rw [Real.coe_toNNReal _ hcoefficientNonnegative]
    exact hcoefficient
  rcases source_witness_coarse_plane_map_lipschitz_one_balanced
      sourceWitness hrho selectedMap hselectedLipschitz hcoefficientNN
      (by simpa only [Real.coe_toNNReal _ hcoefficientNonnegative] using
        hbudget) with ⟨sampled⟩
  have hmass : finite.leftFactor * fineShading.mass ≤
      (finite.rightFactor * (K ^ 3 : ENNReal)) * residue.selected.mass := by
    calc
      finite.leftFactor * fineShading.mass ≤
          finite.rightFactor * finite.refinement.shading.mass :=
        finite.refinement.mass_retention
      _ ≤ finite.rightFactor *
          ((K ^ 3 : ENNReal) * residue.selected.mass) := by
        gcongr
        exact residue.mass_retention
      _ = (finite.rightFactor * (K ^ 3 : ENNReal)) *
          residue.selected.mass := by ring
  exact ⟨{
    residue := residue
    sourceWitness := sourceWitness
    sampled := sampled
    fine_mass_retention := hmass
  }⟩

/-- Total normalized cost of aligned residue balancing, conversion from fine
incidences to honest coarse source witnesses, and the fixed sampled-map
refinement.  The added `1` makes positivity independent of accidental zero
values in an upper-bound factor. -/
def AlignedFiniteCoarsePlaneMapData.selectionLoss
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta} {K : ℕ}
    (_data : AlignedFiniteCoarsePlaneMapData
      (target := target) compatible finite hdelta K)
    (fiberCap : ENNReal) : ENNReal :=
  1 + finite.leftFactor⁻¹ *
    (((finite.rightFactor * (K ^ 3 : ENNReal)) * fiberCap) * 27)

/-- A uniform complete-fiber point-multiplicity cap converts the aligned
retained fine mass into mass of the actual sampled coarse shading. -/
theorem AlignedFiniteCoarsePlaneMapData.fine_to_sampled_mass
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta} {K : ℕ}
    (data : AlignedFiniteCoarsePlaneMapData
      (target := target) compatible finite hdelta K)
    (fiberCap : ENNReal)
    (hfiberCap : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          data.residue.selected parent point : ENNReal) ≤ fiberCap) :
    finite.leftFactor * fineShading.mass ≤
      (((finite.rightFactor * (K ^ 3 : ENNReal)) * fiberCap) * 27) *
        data.sampled.selected.mass := by
  have hfineCoarse : data.residue.selected.mass ≤
      fiberCap * data.sourceWitness.shading.mass :=
    cover.toPaperTubeCover.fine_mass_le_fiberCap_mul_coarse_mass
      data.residue.selected data.sourceWitness.shading
      (fun source point hpoint =>
        data.sourceWitness.balanced.point_compatibility source
          (cover.toPaperTubeCover.parent source)
          (cover.toPaperTubeCover.parent_covers source) point hpoint)
      hfiberCap
  calc
    finite.leftFactor * fineShading.mass ≤
        (finite.rightFactor * (K ^ 3 : ENNReal)) *
          data.residue.selected.mass := data.fine_mass_retention
    _ ≤ (finite.rightFactor * (K ^ 3 : ENNReal)) *
        (fiberCap * data.sourceWitness.shading.mass) := by gcongr
    _ ≤ (finite.rightFactor * (K ^ 3 : ENNReal)) *
        (fiberCap * (27 * data.sampled.selected.mass)) := by
      gcongr
      exact data.sampled.mass_retention
    _ = (((finite.rightFactor * (K ^ 3 : ENNReal)) * fiberCap) * 27) *
        data.sampled.selected.mass := by ring

/-- The normalized aligned selection loss is strictly positive. -/
lemma AlignedFiniteCoarsePlaneMapData.selectionLoss_pos
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta} {K : ℕ}
    (data : AlignedFiniteCoarsePlaneMapData
      (target := target) compatible finite hdelta K)
    (fiberCap : ENNReal) :
    0 < data.selectionLoss fiberCap := by
  exact zero_lt_one.trans_le <| by
    simp only [AlignedFiniteCoarsePlaneMapData.selectionLoss]
    exact le_add_right le_rfl

/-- Finite fiber caps give a finite normalized aligned selection loss. -/
lemma AlignedFiniteCoarsePlaneMapData.selectionLoss_ne_top
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta} {K : ℕ}
    (data : AlignedFiniteCoarsePlaneMapData
      (target := target) compatible finite hdelta K)
    (fiberCap : ENNReal) (hfiberCapTop : fiberCap ≠ ⊤) :
    data.selectionLoss fiberCap ≠ ⊤ := by
  unfold AlignedFiniteCoarsePlaneMapData.selectionLoss
  rw [ENNReal.add_ne_top]
  refine ⟨by norm_num, ?_⟩
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr finite.leftFactor_pos.ne') <|
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top finite.rightFactor_ne_top (by simp))
          hfiberCapTop)
        (by norm_num)

/-- Normalized source-to-sampled mass retention, ready for cropped-extremal
transfer and small-scale loss absorption. -/
theorem AlignedFiniteCoarsePlaneMapData.fine_to_sampled_mass_normalized
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {compatible : PureWZ2CompatibleCoverData
      cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta} {K : ℕ}
    (data : AlignedFiniteCoarsePlaneMapData
      (target := target) compatible finite hdelta K)
    (fiberCap : ENNReal)
    (hfiberCap : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          data.residue.selected parent point : ENNReal) ≤ fiberCap) :
    fineShading.mass ≤
      data.selectionLoss fiberCap * data.sampled.selected.mass := by
  let rawCost : ENNReal :=
    ((finite.rightFactor * (K ^ 3 : ENNReal)) * fiberCap) * 27
  have hraw : finite.leftFactor * fineShading.mass ≤
      rawCost * data.sampled.selected.mass := by
    simpa [rawCost] using data.fine_to_sampled_mass fiberCap hfiberCap
  calc
    fineShading.mass = finite.leftFactor⁻¹ *
        (finite.leftFactor * fineShading.mass) := by
      rw [ENNReal.inv_mul_cancel_left finite.leftFactor_pos.ne'
        finite.leftFactor_ne_top]
    _ ≤ finite.leftFactor⁻¹ *
        (rawCost * data.sampled.selected.mass) := by gcongr
    _ = (finite.leftFactor⁻¹ * rawCost) *
        data.sampled.selected.mass := by ring
    _ ≤ data.selectionLoss fiberCap * data.sampled.selected.mass := by
      gcongr
      exact le_add_left le_rfl

end Kakeya.Assouad.PureWZ2

end

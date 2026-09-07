import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section6CoverParentMap
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers

/-!
# Canonical parent map for the pure Section-6 cover

The pure cover stores the paper's existential line cover and coarse essential
distinctness.  At the same coarse radius these imply a unique parent: two
parents covering the same fine tube would be at line distance at most the
coarse radius.  This adapter exposes the resulting `WZ1PaperTubeCover` and
its complete fibers without adding a uniform tube structure.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Forget the extra pure provenance while retaining the literal balanced cover. -/
noncomputable def PureWZ2BalancedCoverData.toWZ1PaperBalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading) :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover fineShading coarseShading where
  point_compatibility source point hpoint := by
    exact balanced.point_compatibility source
      (cover.toWZ1PaperTubeCover.parent source)
      (cover.toWZ1PaperTubeCover.parent_covers source) point hpoint
  coarse_cubical := balanced.coarse_cubical
  activeCells := balanced.activeCells
  coarse_union_eq := balanced.coarse_union_eq
  cellMass := balanced.cellMass
  cellMass_pos := balanced.cellMass_pos
  cellMass_ne_top := balanced.cellMass_ne_top
  fine_cell_mass := balanced.fine_cell_mass

@[simp] theorem PureWZ2BalancedCoverData.toWZ1PaperBalancedCoverData_activeCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading) :
    balanced.toWZ1PaperBalancedCoverData.activeCells =
      balanced.activeCells := rfl

@[simp] theorem PureWZ2Section6Cover.mem_fullFiber_iff_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈ wz2PaperFullFiberIndices fine coarse parent ↔
      cover.toWZ1PaperTubeCover.parent source = parent := by
  constructor
  · intro h
    exact
      (cover.toWZ1PaperTubeCover.parent_unique source parent
        ((mem_wz2PaperFullFiberIndices_iff parent source).mp h)).symm
  · intro h
    rw [← h]
    exact
      (mem_wz2PaperFullFiberIndices_iff
        (cover.toWZ1PaperTubeCover.parent source) source).mpr
        (cover.toWZ1PaperTubeCover.parent_covers source)

theorem PureWZ2Section6Cover.c2_fullFiberIndices_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperFullFiberIndices fine coarse parent =
      cover.toWZ1PaperTubeCover.fiberIndices parent := by
  ext source
  simp [cover.mem_fullFiber_iff_parent,
    WZ1PaperTubeCover.fiberIndices]

/-- The canonical parent fibers partition indexed shaded mass exactly. -/
theorem WZ1PaperTubeCover.sum_fiberShadedMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (shading : WZ1PaperTubeShading fine) :
    ∑ parent : Fin coarse.card,
        cover.fiberShadedMass shading parent = shading.mass := by
  have hmaps :
      Set.MapsTo cover.parent
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card)) :=
    fun _ _ => Finset.mem_univ _
  have hsum :=
    Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ)
      (g := cover.parent) hmaps
      (fun source => MeasureTheory.volume (shading.carrier source))
  change
    (∑ parent : Fin coarse.card,
        ∑ source ∈ Finset.univ with cover.parent source = parent,
          MeasureTheory.volume (shading.carrier source)) =
      ∑ source : Fin fine.card,
        MeasureTheory.volume (shading.carrier source)
  simpa using hsum

/-- One canonical parent carries at least the average indexed shaded mass. -/
theorem WZ1PaperTubeCover.exists_heavy_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (hfine : fine.Nonempty)
    (shading : WZ1PaperTubeShading fine) :
    ∃ parent : Fin coarse.card,
      shading.mass ≤
        coarse.enncard * cover.fiberShadedMass shading parent := by
  let source : Fin fine.card := ⟨0, hfine⟩
  let first : Fin coarse.card := cover.parent source
  let weight : Fin coarse.card → ENNReal :=
    cover.fiberShadedMass shading
  rcases Finset.exists_max_image
      (Finset.univ : Finset (Fin coarse.card)) weight
      ⟨first, Finset.mem_univ _⟩ with
    ⟨parent, _, hmax⟩
  refine ⟨parent, ?_⟩
  rw [← cover.sum_fiberShadedMass shading]
  calc
    ∑ other : Fin coarse.card, weight other ≤
        ∑ _other : Fin coarse.card, weight parent := by
      exact Finset.sum_le_sum fun other _ =>
        hmax other (Finset.mem_univ _)
    _ = coarse.enncard * weight parent := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]

/-- Restricting to one canonical parent fiber realizes its fiber multiplicity exactly. -/
theorem WZ1PaperTubeCover.restrict_fiber_pointMultiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) (point : Point3) :
    let selected := Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine (cover.fiberIndices parent)
    (restrictPaperShading selected shading).pointMultiplicity point =
      cover.fiberPointMultiplicity shading parent point := by
  classical
  let indices := cover.fiberIndices parent
  let selected := Kakeya.Streamlined.TubeSubfamily.fromFinset fine indices
  let selectedAtPoint : Finset (Fin selected.family.card) :=
    Finset.univ.filter fun index =>
      point ∈ shading.carrier (selected.embedding index)
  let ambientAtPoint : Finset (Fin fine.card) :=
    indices.filter fun source => point ∈ shading.carrier source
  have himage :
      selectedAtPoint.image selected.embedding = ambientAtPoint := by
    ext source
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with ⟨index, hindex, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.orderEmbOfFin_mem indices rfl index,
          (Finset.mem_filter.mp hindex).2⟩
    · intro hsource
      have hsourceIndex := (Finset.mem_filter.mp hsource).1
      let index : Fin indices.card :=
        (indices.orderIsoOfFin rfl).symm ⟨source, hsourceIndex⟩
      have hembed : selected.embedding index = source := by
        change (indices.orderEmbOfFin rfl) index = source
        have hval :
            ((indices.orderIsoOfFin rfl) index).1 = source := by
          simp [index]
        exact hval
      refine Finset.mem_image.mpr ⟨index, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by
            rw [hembed]
            exact
              (Finset.mem_filter.mp hsource).2⟩
      · exact hembed
  change selectedAtPoint.card = ambientAtPoint.card
  rw [← himage, Finset.card_image_of_injective _ selected.embedding.injective]

/-- The balanced fine union is the disjoint union of the active coarse cells. -/
theorem PureWZ2BalancedCoverData.fine_union_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading) :
    MeasureTheory.volume fineShading.union =
      (balanced.activeCells.card : ENNReal) * balanced.cellMass :=
  balanced.toWZ1PaperBalancedCoverData.fine_union_volume

/-- Forget the Node 5-only receipts and expose the underlying paper cover. -/
noncomputable def PureWZ2Node5BalancedCoverData.toWZ1PaperBalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (_balanced : PureWZ2Node5BalancedCoverData base) :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover fineShading coarseShading :=
  base.toWZ1PaperBalancedCoverData

@[simp] theorem
    PureWZ2Node5BalancedCoverData.toWZ1PaperBalancedCoverData_activeCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData base) :
    balanced.toWZ1PaperBalancedCoverData.activeCells =
      balanced.activeCells := rfl

/-- The union-volume identity depends only on the underlying balanced cover. -/
theorem PureWZ2Node5BalancedCoverData.fine_union_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData base) :
    MeasureTheory.volume fineShading.union =
      (balanced.activeCells.card : ENNReal) * balanced.cellMass :=
  base.fine_union_volume

/-- The indexed fine mass is balanced cell by balanced cell. -/
theorem PureWZ2Node5BalancedCoverData.fine_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData base) :
    fineShading.mass =
      (balanced.activeCells.card : ENNReal) * balanced.incidenceMass := by
  have carrierPartition :
      ∀ source : Fin fine.card,
        fineShading.carrier source =
          ⋃ cell ∈ balanced.activeCells,
            fineShading.carrier source ∩ wz1PaperGridCube rho cell := by
    intro sourceIndex
    ext point
    constructor
    · intro hpoint
      have hcoarse := balanced.point_compatibility sourceIndex
        (cover.toWZ1PaperTubeCover.parent sourceIndex)
        (cover.toWZ1PaperTubeCover.parent_covers sourceIndex)
        point hpoint
      have hcoarseUnion : point ∈ coarseShading.union :=
        ⟨cover.toWZ1PaperTubeCover.parent sourceIndex, hcoarse⟩
      rw [balanced.coarse_union_eq] at hcoarseUnion
      rcases Set.mem_iUnion₂.mp hcoarseUnion with
        ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, hcell, hpoint, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_cell, _hcell, hsource, _hpointCell⟩
      exact hsource
  have carrierVolume :
      ∀ source : Fin fine.card,
        MeasureTheory.volume (fineShading.carrier source) =
          ∑ cell ∈ balanced.activeCells,
            MeasureTheory.volume
              (fineShading.carrier source ∩
                wz1PaperGridCube rho cell) := by
    intro sourceIndex
    calc
      MeasureTheory.volume (fineShading.carrier sourceIndex) =
          MeasureTheory.volume
            (⋃ cell ∈ balanced.activeCells,
              fineShading.carrier sourceIndex ∩
                wz1PaperGridCube rho cell) :=
        congrArg MeasureTheory.volume (carrierPartition sourceIndex)
      _ = _ := by
        apply MeasureTheory.measure_biUnion_finset
        · intro first _ second _ hne
          exact (wz1PaperGridCube_disjoint hne).mono
            Set.inter_subset_right Set.inter_subset_right
        · intro cell _
          exact (fineShading.measurable_carrier sourceIndex).inter
            (wz1PaperGridCube_measurable cell)
  calc
    fineShading.mass =
        ∑ sourceIndex : Fin fine.card,
          ∑ cell ∈ balanced.activeCells,
            MeasureTheory.volume
              (fineShading.carrier sourceIndex ∩
                wz1PaperGridCube rho cell) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      exact carrierVolume sourceIndex
    _ =
        ∑ cell ∈ balanced.activeCells,
          ∑ sourceIndex : Fin fine.card,
            MeasureTheory.volume
              (fineShading.carrier sourceIndex ∩
                wz1PaperGridCube rho cell) := by
      rw [Finset.sum_comm]
    _ = ∑ _cell ∈ balanced.activeCells, balanced.incidenceMass := by
      apply Finset.sum_congr rfl
      exact balanced.fine_cell_incidence_mass
    _ =
        (balanced.activeCells.card : ENNReal) *
          balanced.incidenceMass := by
      simp [Finset.sum_const]

/--
The pointwise multiplicity band on the retained fine shading is exactly the
ratio between the two quantities balanced on every active coarse cell.  The
common active-cell count cancels from the global mass--volume inequalities,
so no second balanced cell mass is paid in this comparison.
-/
theorem PureWZ2Node5StickyData.balanced_incidenceMass_band
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      (sourceShading := sourceShading) (rho := rho)
      (logExponent := logExponent)) :
    (data.fineMultiplicity : ENNReal) * data.balanced.cellMass ≤
        data.balanced.incidenceMass ∧
      data.balanced.incidenceMass ≤
        (2 * data.fineMultiplicity : ENNReal) *
          data.balanced.cellMass := by
  let count : ENNReal := data.balanced.activeCells.card
  have hvolume :
      MeasureTheory.volume data.refined.union =
        count * data.balanced.cellMass :=
    data.data.balanced.fine_union_volume
  have hmass :
      data.refined.mass = count * data.balanced.incidenceMass :=
    data.balanced.fine_mass
  have hcountZero : count ≠ 0 := by
    have hnonempty : data.balanced.activeCells.Nonempty := by
      by_contra hempty
      have hcells : data.balanced.activeCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hzero : MeasureTheory.volume data.refined.union = 0 := by
        rw [hvolume]
        simp [count, hcells]
      have hpositive :
          0 < Kakeya.realRpowENN delta (sigma + outputLoss) :=
        ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos data.refined_extremal.delta_pos _)
      have himpossible := data.refined_volume_lower
      rw [hzero] at himpossible
      exact (not_le_of_gt hpositive) himpossible
    change (data.balanced.activeCells.card : ENNReal) ≠ 0
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hcountTop : count ≠ ⊤ := by simp [count]
  have hglobal :=
    constant_multiplicity_mass_volume_generic
      data.refined_multiplicity_band
  constructor
  · apply (ENNReal.mul_le_mul_iff_left hcountZero hcountTop).mp
    calc
      ((data.fineMultiplicity : ENNReal) *
            data.balanced.cellMass) * count =
          (data.fineMultiplicity : ENNReal) *
            MeasureTheory.volume data.refined.union := by
        rw [hvolume]
        ring
      _ ≤ data.refined.mass := hglobal.1
      _ = data.balanced.incidenceMass * count := by
        rw [hmass]
        ring
  · apply (ENNReal.mul_le_mul_iff_left hcountZero hcountTop).mp
    calc
      data.balanced.incidenceMass * count = data.refined.mass := by
        rw [hmass]
        ring
      _ ≤ (2 * data.fineMultiplicity : ENNReal) *
            MeasureTheory.volume data.refined.union := hglobal.2
      _ = ((2 * data.fineMultiplicity : ENNReal) *
            data.balanced.cellMass) * count := by
        rw [hvolume]
        ring

/--
Every balanced coarse cell inherits a lower volume floor by cancelling the
common active-cell count between the fine and coarse unions.  This is the
single-cover form of the source-floor argument used at both sticky stages.
-/
theorem PureWZ2Node5StickyData.source_floor_raw
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      (sourceShading := sourceShading) (rho := rho)
      (logExponent := logExponent)) :
    Kakeya.realRpowENN delta (sigma + outputLoss) *
        MeasureTheory.volume
          (wz1PaperGridCube rho.1 (0, 0, 0)) ≤
      Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
        data.balanced.cellMass := by
  let balanced := data.data.balanced.toWZ1PaperBalancedCoverData
  let count : ENNReal := balanced.activeCells.card
  let cubeVolume := MeasureTheory.volume
    (wz1PaperGridCube rho.1 (0, 0, 0))
  let fineVolume := MeasureTheory.volume data.refined.union
  let coarseVolume := MeasureTheory.volume data.croppedCoarseShading.union
  have hfine :
      Kakeya.realRpowENN delta (sigma + outputLoss) ≤ fineVolume :=
    data.refined_volume_lower
  have hcoarse :
      coarseVolume ≤
        Kakeya.realRpowENN rho.1 (sigma - outputLoss) :=
    data.coarse_extremal.volume_upper
  have hfineEq : fineVolume = count * balanced.cellMass :=
    balanced.fine_union_volume
  have hcoarseEq : coarseVolume = count * cubeVolume :=
    balanced.coarse_union_volume data.coarse_extremal.delta_pos
  have hscaled :
      count *
          (Kakeya.realRpowENN delta (sigma + outputLoss) * cubeVolume) ≤
        count *
          (Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
            balanced.cellMass) := by
    calc
      count *
            (Kakeya.realRpowENN delta (sigma + outputLoss) * cubeVolume) =
          Kakeya.realRpowENN delta (sigma + outputLoss) *
            (count * cubeVolume) := by ring
      _ = Kakeya.realRpowENN delta (sigma + outputLoss) *
            coarseVolume := by rw [← hcoarseEq]
      _ ≤ fineVolume *
            Kakeya.realRpowENN rho.1 (sigma - outputLoss) := by gcongr
      _ = count *
            (Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
              balanced.cellMass) := by
        rw [hfineEq]
        ring
  have hcountZero : count ≠ 0 := by
    have hnonempty : balanced.activeCells.Nonempty := by
      by_contra hempty
      have hcells : balanced.activeCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hzero : fineVolume = 0 := by simp [hfineEq, count, hcells]
      have hpositive :
          0 < Kakeya.realRpowENN delta (sigma + outputLoss) :=
        ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos data.refined_extremal.delta_pos _)
      rw [hzero] at hfine
      exact (not_le_of_gt hpositive) hfine
    change (balanced.activeCells.card : ENNReal) ≠ 0
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hcountTop : count ≠ ⊤ := by simp [count]
  change Kakeya.realRpowENN delta (sigma + outputLoss) * cubeVolume ≤
    Kakeya.realRpowENN rho.1 (sigma - outputLoss) * balanced.cellMass
  apply (ENNReal.mul_le_mul_iff_left hcountZero hcountTop).mp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- The source-floor cancellation uses only the terminal balanced cover, the
fine volume lower bound, the coarse volume upper bound, and positivity of the
literal fine scale. -/
theorem PureWZ2TerminalStickyCore.source_floor_raw
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2TerminalStickyCore
      (sigma := sigma) (outputLoss := outputLoss)
      (sourceShading := sourceShading) (rho := rho)
      (logExponent := logExponent))
    (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta (sigma + outputLoss) *
        MeasureTheory.volume
          (wz1PaperGridCube rho.1 (0, 0, 0)) ≤
      Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
        data.balanced.cellMass := by
  let balanced := data.balancedBase.toWZ1PaperBalancedCoverData
  let count : ENNReal := balanced.activeCells.card
  let cubeVolume := MeasureTheory.volume
    (wz1PaperGridCube rho.1 (0, 0, 0))
  let fineVolume := MeasureTheory.volume data.refined.union
  let coarseVolume := MeasureTheory.volume data.croppedCoarseShading.union
  have hfine :
      Kakeya.realRpowENN delta (sigma + outputLoss) ≤ fineVolume :=
    data.refined_volume_lower
  have hcoarse :
      coarseVolume ≤
        Kakeya.realRpowENN rho.1 (sigma - outputLoss) :=
    data.coarse_extremal.volume_upper
  have hfineEq : fineVolume = count * balanced.cellMass :=
    balanced.fine_union_volume
  have hcoarseEq : coarseVolume = count * cubeVolume :=
    balanced.coarse_union_volume data.coarse_extremal.delta_pos
  have hscaled :
      count *
          (Kakeya.realRpowENN delta (sigma + outputLoss) * cubeVolume) ≤
        count *
          (Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
            balanced.cellMass) := by
    calc
      count *
            (Kakeya.realRpowENN delta (sigma + outputLoss) * cubeVolume) =
          Kakeya.realRpowENN delta (sigma + outputLoss) *
            (count * cubeVolume) := by ring
      _ = Kakeya.realRpowENN delta (sigma + outputLoss) *
            coarseVolume := by rw [← hcoarseEq]
      _ ≤ fineVolume *
            Kakeya.realRpowENN rho.1 (sigma - outputLoss) := by gcongr
      _ = count *
            (Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
              balanced.cellMass) := by
        rw [hfineEq]
        ring
  have hcountZero : count ≠ 0 := by
    have hnonempty : balanced.activeCells.Nonempty := by
      by_contra hempty
      have hcells : balanced.activeCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hzero : fineVolume = 0 := by simp [hfineEq, count, hcells]
      have hpositive :
          0 < Kakeya.realRpowENN delta (sigma + outputLoss) :=
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
      rw [hzero] at hfine
      exact (not_le_of_gt hpositive) hfine
    change (balanced.activeCells.card : ENNReal) ≠ 0
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hcountTop : count ≠ ⊤ := by simp [count]
  change Kakeya.realRpowENN delta (sigma + outputLoss) * cubeVolume ≤
    Kakeya.realRpowENN rho.1 (sigma - outputLoss) * balanced.cellMass
  apply (ENNReal.mul_le_mul_iff_left hcountZero hcountTop).mp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

/--
The same active-cell cancellation for indexed shaded mass.  The left side
keeps the literal retained fraction of the supplied source mass, so later
density estimates remain on the original family rather than a coarse proxy.
-/
theorem PureWZ2Node5StickyData.incidence_floor_raw
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      (sourceShading := sourceShading) (rho := rho)
      (logExponent := logExponent)) :
    (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) *
        MeasureTheory.volume
          (wz1PaperGridCube rho.1 (0, 0, 0)) ≤
      Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
        data.balanced.incidenceMass := by
  let balanced := data.data.balanced.toWZ1PaperBalancedCoverData
  let count : ENNReal := balanced.activeCells.card
  let cubeVolume := MeasureTheory.volume
    (wz1PaperGridCube rho.1 (0, 0, 0))
  let fineMass := data.refined.mass
  let coarseVolume := MeasureTheory.volume data.croppedCoarseShading.union
  have hmass :
      wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass ≤ fineMass :=
    data.retained_mass
  have hcoarse :
      coarseVolume ≤
        Kakeya.realRpowENN rho.1 (sigma - outputLoss) :=
    data.coarse_extremal.volume_upper
  have hmassEq : fineMass = count * data.balanced.incidenceMass :=
    data.balanced.fine_mass
  have hcoarseEq : coarseVolume = count * cubeVolume :=
    balanced.coarse_union_volume data.coarse_extremal.delta_pos
  have hscaled :
      count *
          ((wz2PaperPureRefinementFraction delta logExponent *
              sourceShading.mass) * cubeVolume) ≤
        count *
          (Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
            data.balanced.incidenceMass) := by
    calc
      count *
            ((wz2PaperPureRefinementFraction delta logExponent *
                sourceShading.mass) * cubeVolume) =
          (wz2PaperPureRefinementFraction delta logExponent *
              sourceShading.mass) * (count * cubeVolume) := by ring
      _ = (wz2PaperPureRefinementFraction delta logExponent *
              sourceShading.mass) * coarseVolume := by rw [← hcoarseEq]
      _ ≤ fineMass *
            Kakeya.realRpowENN rho.1 (sigma - outputLoss) := by gcongr
      _ = count *
            (Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
              data.balanced.incidenceMass) := by
        rw [hmassEq]
        ring
  have hcountZero : count ≠ 0 := by
    have hnonempty : balanced.activeCells.Nonempty := by
      by_contra hempty
      have hcells : balanced.activeCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hcellsPure : data.data.balanced.activeCells = ∅ := by
        exact hcells
      have hzeroVolume : MeasureTheory.volume data.refined.union = 0 := by
        rw [data.data.balanced.fine_union_volume, hcellsPure]
        simp
      have hpositive :
          0 < Kakeya.realRpowENN delta (sigma + outputLoss) :=
        ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos data.refined_extremal.delta_pos _)
      have himpossible := data.refined_volume_lower
      rw [hzeroVolume] at himpossible
      exact (not_le_of_gt hpositive) himpossible
    change (balanced.activeCells.card : ENNReal) ≠ 0
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hcountTop : count ≠ ⊤ := by simp [count]
  change (wz2PaperPureRefinementFraction delta logExponent *
      sourceShading.mass) * cubeVolume ≤
    Kakeya.realRpowENN rho.1 (sigma - outputLoss) *
      data.balanced.incidenceMass
  apply (ENNReal.mul_le_mul_iff_left hcountZero hcountTop).mp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

end Kakeya.Assouad

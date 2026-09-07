import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleTwoScaleSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter

/-!
# Genuine fine witnesses for the first sticky coarse cells

The Lemma-23 auxiliary carrier lives at the first sticky scale.  Its plane
normal must nevertheless come from the original fine plane map.  This record
chooses, in every active coarse cell, an actual fine shaded point in that same
cell and retains all source-tube and local-AD provenance.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2CoarseCellWitnessData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) where
  activeCells : Finset (ℤ × ℤ × ℤ)
  activeCells_eq :
    activeCells = twoScale.coarse.balanced.activeCells
  witness : (ℤ × ℤ × ℤ) → Point3
  witness_mem_refined :
    ∀ cell ∈ activeCells, witness cell ∈ twoScale.coarse.refined.union
  witness_mem_cell :
    ∀ cell ∈ activeCells,
      witness cell ∈ wz1PaperGridCube rho cell
  sourceIndex : (ℤ × ℤ × ℤ) → Fin source.family.card
  witness_mem_source :
    ∀ cell ∈ activeCells,
      witness cell ∈ source.shading.carrier (sourceIndex cell)
  normal : (ℤ × ℤ × ℤ) → Point3
  normal_eq :
    ∀ cell (hcell : cell ∈ activeCells),
      normal cell = source.localGrains.planeMap
        ⟨witness cell,
          ⟨sourceIndex cell, witness_mem_source cell hcell⟩⟩
  normal_unit :
    ∀ cell ∈ activeCells, ‖normal cell‖ = 1
  normal_vertical :
    ∀ cell ∈ activeCells, |normal cell (2 : Fin 3)| ≤ 1 / 2
  normal_dist :
    ∀ first ∈ activeCells, ∀ second ∈ activeCells,
      dist (normal first) (normal second) ≤
        dist (witness first) (witness second)
  fine_local_ad :
    ∀ cell ∈ activeCells,
      PureWZ2PaperADSet1
        (scalarProjection (normal cell)
          (source.shading.union ∩
            Metric.closedBall (witness cell) (Real.sqrt rho)))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss))

theorem PureWZ2OneScaleTwoScaleStickyData.coarseCellWitnesses
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) :
    Nonempty (PureWZ2CoarseCellWitnessData twoScale) := by
  have hrhoEq := twoScale.rhoRequested_eq
  let activeCells := twoScale.coarse.balanced.activeCells
  have hcellWitness :
      ∀ cell ∈ activeCells,
        (twoScale.coarse.refined.union ∩
          wz1PaperGridCube rho cell).Nonempty := by
    intro cell hcell
    have hmass :=
      twoScale.coarse.balanced.fine_cell_incidence_mass cell hcell
    have hmass' :
        (∑ sourceIndex : Fin twoScale.coarse.selected.family.card,
          MeasureTheory.volume
            (twoScale.coarse.refined.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          twoScale.coarse.balanced.incidenceMass := by
      simpa only [hrhoEq] using hmass
    have hpositive :
        0 < ∑ sourceIndex : Fin twoScale.coarse.selected.family.card,
          MeasureTheory.volume
            (twoScale.coarse.refined.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) := by
      rw [hmass']
      exact twoScale.coarse.balanced.incidenceMass_pos
    by_contra hempty
    have hinter :
        twoScale.coarse.refined.union ∩ wz1PaperGridCube rho cell = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    have hzero :
        ∀ sourceIndex : Fin twoScale.coarse.selected.family.card,
          MeasureTheory.volume
              (twoScale.coarse.refined.carrier sourceIndex ∩
                wz1PaperGridCube rho cell) = 0 := by
      intro sourceIndex
      have hsubset :
          twoScale.coarse.refined.carrier sourceIndex ∩
              wz1PaperGridCube rho cell ⊆
            twoScale.coarse.refined.union ∩
              wz1PaperGridCube rho cell := by
        rintro point ⟨hsource, hpointCell⟩
        exact ⟨⟨sourceIndex, hsource⟩, hpointCell⟩
      have :
          twoScale.coarse.refined.carrier sourceIndex ∩
              wz1PaperGridCube rho cell = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨point, hpoint⟩
        exact (Set.not_nonempty_iff_eq_empty.mpr hinter)
          ⟨point, hsubset hpoint⟩
      rw [this]
      simp
    have :
        (∑ sourceIndex : Fin twoScale.coarse.selected.family.card,
          MeasureTheory.volume
            (twoScale.coarse.refined.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) = 0 := by
      simp [hzero]
    rw [this] at hpositive
    exact (lt_irrefl 0) hpositive
  let witness : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ activeCells then
      Classical.choose (hcellWitness cell hcell)
    else 0
  have hwitness :
      ∀ cell (hcell : cell ∈ activeCells),
        witness cell ∈ twoScale.coarse.refined.union ∩
          wz1PaperGridCube rho cell := by
    intro cell hcell
    simp only [witness, dif_pos hcell]
    exact Classical.choose_spec (hcellWitness cell hcell)
  let selectedIndex : (ℤ × ℤ × ℤ) →
      Fin twoScale.coarse.selected.family.card := fun cell =>
    if hcell : cell ∈ activeCells then
      Classical.choose (hwitness cell hcell).1
    else
      ⟨0, twoScale.coarse.selected_nonempty⟩
  have hwitnessSelected :
      ∀ cell (hcell : cell ∈ activeCells),
        witness cell ∈
          twoScale.coarse.refined.carrier (selectedIndex cell) := by
    intro cell hcell
    simp only [selectedIndex, dif_pos hcell]
    exact Classical.choose_spec (hwitness cell hcell).1
  let sourceIndex : (ℤ × ℤ × ℤ) → Fin source.family.card := fun cell =>
    twoScale.coarse.selected.embedding (selectedIndex cell)
  have hwitnessSource :
      ∀ cell (hcell : cell ∈ activeCells),
        witness cell ∈ source.shading.carrier (sourceIndex cell) := by
    intro cell hcell
    exact twoScale.coarse.subshading (selectedIndex cell)
      (hwitnessSelected cell hcell)
  let normal : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ activeCells then
      source.localGrains.planeMap
        ⟨witness cell, ⟨sourceIndex cell, hwitnessSource cell hcell⟩⟩
    else 0
  have hnormalEq :
      ∀ cell (hcell : cell ∈ activeCells),
        normal cell = source.localGrains.planeMap
          ⟨witness cell, ⟨sourceIndex cell, hwitnessSource cell hcell⟩⟩ := by
    intro cell hcell
    simp [normal, hcell]
  refine
    ⟨{ activeCells := activeCells
       activeCells_eq := rfl
       witness := witness
       witness_mem_refined := fun cell hcell => (hwitness cell hcell).1
       witness_mem_cell := fun cell hcell => (hwitness cell hcell).2
       sourceIndex := sourceIndex
       witness_mem_source := hwitnessSource
       normal := normal
       normal_eq := hnormalEq
       normal_unit := ?_
       normal_vertical := ?_
       normal_dist := ?_
       fine_local_ad := ?_ }⟩
  · intro cell hcell
    rw [hnormalEq cell hcell]
    exact source.localGrains.planeMap_unit _
  · intro cell hcell
    rw [hnormalEq cell hcell]
    exact source.planeMap_vertical_bound _
  · intro first hfirst second hsecond
    rw [hnormalEq first hfirst, hnormalEq second hsecond]
    have h := source.localGrains.planeMap_lipschitz.dist_le_mul
      ⟨witness first, ⟨sourceIndex first, hwitnessSource first hfirst⟩⟩
      ⟨witness second, ⟨sourceIndex second, hwitnessSource second hsecond⟩⟩
    have hsubtype :
        dist
            (⟨witness first,
              ⟨sourceIndex first, hwitnessSource first hfirst⟩⟩ :
              {point : Point3 // point ∈ source.shading.union})
            (⟨witness second,
              ⟨sourceIndex second, hwitnessSource second hsecond⟩⟩ :
              {point : Point3 // point ∈ source.shading.union}) =
          dist (witness first) (witness second) := rfl
    simpa [hsubtype] using h
  · intro cell hcell
    rw [hnormalEq cell hcell]
    have hdeltaRho : delta ≤ rho := by
      rw [← hrhoEq]
      exact twoScale.rhoRequested.property.1
    exact source.localGrains.local_ad rho hdeltaRho
      (by rw [← hrhoEq]; exact twoScale.rhoRequested.property.2) _

end Kakeya.Assouad

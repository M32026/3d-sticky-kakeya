import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05IndexedIncidenceRestriction

/-!
# Refinement from synchronized indexed-incidence restriction

The fine shading mass is decomposed tube by tube across the actual active
coarse cells.  Applying the same identity after the synchronized restriction
turns indexed-incidence retention into ordinary shaded-mass retention.  The
families and Section 6 cover are unchanged throughout.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- If every fine cell meeting the shading is nested in an active coarse cell,
then the indexed fine mass is exactly the sum of the actual cell incidences. -/
theorem PureWZ2BalancedCoverData.fineShading_mass_eq_sum_cellIncidence
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell) :
    fineShading.mass =
      ∑ cell ∈ base.activeCells,
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell := by
  unfold Kakeya.Streamlined.Shading.mass wz2PaperCellIncidenceMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  have hcarrier :
      fineShading.carrier source =
        ⋃ cell ∈ base.activeCells,
          fineShading.carrier source ∩ wz1PaperGridCube rho cell := by
    ext point
    constructor
    · intro hpoint
      rcases fineCellNested source point hpoint with
        ⟨cell, hcell, hnested⟩
      have hpointFine :
          point ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
        (mem_wz1PaperGridCube delta _ point).mpr rfl
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint, hnested hpointFine⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_cell, _hcell, hpointCarrier, _hpointCell⟩
      exact hpointCarrier
  calc
    volume (fineShading.carrier source) =
        volume
          (⋃ cell ∈ base.activeCells,
            fineShading.carrier source ∩ wz1PaperGridCube rho cell) :=
      congrArg volume hcarrier
    _ = ∑ cell ∈ base.activeCells,
          volume (fineShading.carrier source ∩ wz1PaperGridCube rho cell) :=
      MeasureTheory.measure_biUnion_finset
        (fun first _ second _ hne =>
          (wz1PaperGridCube_disjoint hne).mono
            Set.inter_subset_right Set.inter_subset_right)
        (fun cell _ =>
          (fineShading.measurable_carrier source).inter
            (wz1PaperGridCube_measurable cell))

/-- The synchronized restricted shading has the same exact indexed
mass decomposition over its retained active cells. -/
theorem PureWZ2Node05IndexedIncidenceRestrictionData.fineRestricted_mass_eq_sum_cellIncidence
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell}
    {valueCount : ℕ}
    {exactified : PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading base.activeCells valueCount}
    (restriction : PureWZ2Node05IndexedIncidenceRestrictionData
      base fineCellNested exactified) :
    restriction.fineRestricted.mass =
      ∑ cell ∈ restriction.restrictedBase.activeCells,
        wz2PaperCellIncidenceMass
          (rho := rho) restriction.fineRestricted cell :=
  restriction.restrictedBase.fineShading_mass_eq_sum_cellIncidence
    restriction.restrictedBalanced.fine_cell_nested

/-- Indexed-incidence retention is exactly ordinary fine shaded-mass
retention after both sides are decomposed over their active cells. -/
theorem PureWZ2Node05IndexedIncidenceRestrictionData.fine_mass_le_valueCount_mul_restricted_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell}
    {valueCount : ℕ}
    {exactified : PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading base.activeCells valueCount}
    (restriction : PureWZ2Node05IndexedIncidenceRestrictionData
      base fineCellNested exactified) :
    fineShading.mass ≤
      (valueCount : ENNReal) * restriction.fineRestricted.mass := by
  rw [base.fineShading_mass_eq_sum_cellIncidence fineCellNested]
  rw [restriction.fineRestricted_mass_eq_sum_cellIncidence]
  exact restriction.indexed_mass_retention

/-- Restricting to synchronized coarse cells preserves a cubical fine
shading because every meeting fine cell is nested in one retained coarse cell. -/
theorem PureWZ2Node05IndexedIncidenceRestrictionData.fineRestricted_cubical
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell}
    {valueCount : ℕ}
    {exactified : PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading base.activeCells valueCount}
    (restriction : PureWZ2Node05IndexedIncidenceRestrictionData
      base fineCellNested exactified)
    (fineCubical : WZ1PaperIsCubicalShading fineShading) :
    WZ1PaperIsCubicalShading restriction.fineRestricted := by
  intro source point hpoint other hother
  have hpointRestricted := hpoint
  rw [restriction.fineRestricted_eq] at hpointRestricted
  have horiginal : other ∈ fineShading.carrier source :=
    fineCubical source point hpointRestricted.1 hother
  rcases restriction.restrictedBalanced.fine_cell_nested
      source point hpoint with ⟨cell, hcell, hnested⟩
  have hotherCell : other ∈ wz1PaperGridCube rho cell := hnested hother
  rw [restriction.fineRestricted_eq]
  exact
    ⟨horiginal,
      wz1PaperGridCube_subset_retainedCellRegion
        (by simpa only [restriction.restrictedBase_activeCells] using hcell)
        hotherCell⟩

/-- The synchronized restriction as a genuine paper refinement on the
definitionally unchanged fine family. -/
noncomputable def PureWZ2Node05IndexedIncidenceRestrictionData.toFineRefinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell}
    {valueCount logExponent : ℕ}
    {exactified : PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading base.activeCells valueCount}
    (restriction : PureWZ2Node05IndexedIncidenceRestrictionData
      base fineCellNested exactified)
    (hscalar :
      wz1PaperRefinementFraction delta logExponent *
          (valueCount : ENNReal) ≤ 1) :
    WZ1PaperRefinement fineShading logExponent := by
  let identitySelected : Kakeya.Streamlined.TubeSubfamily fine :=
    {
      family := fine
      embedding := Equiv.toEmbedding (Equiv.refl (Fin fine.card))
      tube_eq := fun _ => rfl
    }
  have hsubshading :
      ∀ index, restriction.fineRestricted.carrier index ⊆
        fineShading.carrier (identitySelected.embedding index) := by
    intro index point hpoint
    rw [restriction.fineRestricted_eq] at hpoint
    exact hpoint.1
  have hretained :
      wz1PaperRefinementFraction delta logExponent * fineShading.mass ≤
        restriction.fineRestricted.mass := by
    calc
      wz1PaperRefinementFraction delta logExponent * fineShading.mass ≤
          wz1PaperRefinementFraction delta logExponent *
            ((valueCount : ENNReal) * restriction.fineRestricted.mass) := by
        gcongr
        exact restriction.fine_mass_le_valueCount_mul_restricted_mass
      _ =
          (wz1PaperRefinementFraction delta logExponent *
              (valueCount : ENNReal)) * restriction.fineRestricted.mass := by
        ring
      _ ≤ 1 * restriction.fineRestricted.mass := by
        gcongr
      _ = restriction.fineRestricted.mass := one_mul _
  exact
    {
      selected := identitySelected
      refined := restriction.fineRestricted
      subshading := hsubshading
      retained_mass := hretained
    }

end Kakeya.Assouad

end

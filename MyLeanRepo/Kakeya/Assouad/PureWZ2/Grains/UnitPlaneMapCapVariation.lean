import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseFiniteLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering
import MyLeanRepo.Kakeya.Assouad.WZ1.MeasurableFiniteChoice
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseDirectionPacking.GridCounting

/-!
# One-scale variation for an arbitrary unit weak plane map

Cover the unit ball by a finite coordinate grid of diameter `rho`.  In each
active `rho`-cell, keep the plane-map cap carrying the most shaded mass.
Plane-map values in the same spatial cell then differ by at most `rho`; a
fixed 27-color refinement upgrades this to all point pairs at distance at
most `rho`.  The underlying plane-map function is unchanged.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Number of global coordinate caps used for unit vectors at diameter
`rho`. -/
def unitPlaneMapCapCount (rho : ℝ) : ℕ :=
  let N := Nat.ceil (2 * Real.sqrt 3 / rho) + 1
  Fintype.card (Fin 3 → Fin N)

/-- An arbitrary measurable unit plane map admits one-scale nearby variation
after a common spatial restriction.  The result preserves point
multiplicity at every surviving point. -/
theorem paper_unit_plane_map_cap_nearby_variation
    {delta rho incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading fine}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hrho : 0 < rho) :
    ∃ selected : WZ1PaperTubeShading fine,
      PaperIsSubshading selected S ∧
      (∀ point ∈ selected.union, ∀ other ∈ selected.union,
        dist point other ≤ rho →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ rho) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      S.mass ≤
        27 * (unitPlaneMapCapCount rho : ENNReal) * selected.mass := by
  classical
  let N : ℕ := Nat.ceil (2 * Real.sqrt 3 / rho) + 1
  have hN : 1 ≤ N := by
    dsimp only [N]
    omega
  have hceil : 2 * Real.sqrt 3 / rho ≤
      (Nat.ceil (2 * Real.sqrt 3 / rho) : ℝ) := Nat.le_ceil _
  have hNstrict : 2 * Real.sqrt 3 / rho < (N : ℝ) := by
    dsimp only [N]
    have hsucc : (Nat.ceil (2 * Real.sqrt 3 / rho) : ℝ) <
        (Nat.ceil (2 * Real.sqrt 3 / rho) + 1 : ℕ) := by
      simp
    exact hceil.trans_lt hsucc
  have hNpositive : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiam : Real.sqrt 3 * (2 * 1 / N) ≤ rho := by
    have hmul : 2 * Real.sqrt 3 < (N : ℝ) * rho := by
      calc
        2 * Real.sqrt 3 = (2 * Real.sqrt 3 / rho) * rho := by
          field_simp [hrho.ne']
        _ < (N : ℝ) * rho := by gcongr
    have hdiv : 2 * Real.sqrt 3 / (N : ℝ) < rho := by
      calc
        2 * Real.sqrt 3 / (N : ℝ) <
            ((N : ℝ) * rho) / (N : ℝ) := by gcongr
        _ = rho := by field_simp [hNpositive.ne']
    have heq : Real.sqrt 3 * (2 * 1 / (N : ℝ)) =
        2 * Real.sqrt 3 / (N : ℝ) := by ring
    rw [heq]
    exact hdiv.le
  obtain ⟨cap, hcapMeasurable, hcapCover, hcapDiameter⟩ :=
    grid_covering_cover (0 : Point3) 1 rho (by norm_num)
      N hN hrho hdiam
  let Label := Fin 3 → Fin N
  let defaultLabel : Label := fun _ => ⟨0, by omega⟩
  have hSMeasurable : MeasurableSet S.union :=
    measurableSet_shading_union S
  let P (point : Point3) (label : Label) : Prop :=
    (point ∈ S.union ∧ planeMap.planeMap point ∈ cap label) ∨
      (point ∉ S.union ∧ label = defaultLabel)
  have hPMeasurable : ∀ label : Label,
      MeasurableSet {point | P point label} := by
    intro label
    by_cases hdefault : label = defaultLabel
    · have heq : {point | P point label} =
          (S.union ∩ planeMap.planeMap ⁻¹' cap label) ∪ S.unionᶜ := by
        ext point
        simp [P, hdefault]
      rw [heq]
      exact (hSMeasurable.inter
        ((hcapMeasurable label).preimage planeMap.measurable)).union
        hSMeasurable.compl
    · have heq : {point | P point label} =
          S.union ∩ planeMap.planeMap ⁻¹' cap label := by
        ext point
        simp [P, hdefault]
      rw [heq]
      exact hSMeasurable.inter
        ((hcapMeasurable label).preimage planeMap.measurable)
  have hPNonempty : ∀ point, ∃ label : Label, P point label := by
    intro point
    by_cases hpoint : point ∈ S.union
    · have hunit := planeMap.unit point hpoint
      have hball : dist (planeMap.planeMap point) (0 : Point3) ≤ 1 := by
        simpa [dist_zero_right, hunit]
      rcases hcapCover (planeMap.planeMap point) hball with
        ⟨label, hlabel⟩
      exact ⟨label, Or.inl ⟨hpoint, hlabel⟩⟩
    · exact ⟨defaultLabel, Or.inr ⟨hpoint, rfl⟩⟩
  let labelOrder : Label ≃ Fin (Fintype.card Label) :=
    Fintype.equivFin Label
  letI : LinearOrder Label := Equiv.linearOrder labelOrder
  rcases measurableFiniteChoice hPMeasurable hPNonempty with
    ⟨label, hlabelMeasurable, hlabelSpec, _hlabelMinimal⟩
  have hlabelCap : ∀ point ∈ S.union,
      planeMap.planeMap point ∈ cap (label point) := by
    intro point hpoint
    rcases hlabelSpec point with hgood | hdefault
    · exact hgood.2
    · exact False.elim (hdefault.1 hpoint)
  let cell : Point3 → ℤ × ℤ × ℤ := wz1PaperGridIndex rho
  have hcellMeasurable : Measurable cell := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / rho⌋, ⌊point 1 / rho⌋,
          ⌊point 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [cell, wz1PaperGridIndex, gridIndex]
  let cellBound : ℕ := Nat.ceil (1 / rho)
  let cellInterval : Finset ℤ :=
    Finset.Icc (-(cellBound : ℤ)) (cellBound : ℤ)
  let activeCells : Finset (ℤ × ℤ × ℤ) :=
    cellInterval.product (cellInterval.product cellInterval)
  have hsupport : ∀ point ∈ S.union,
      cell point ∈ activeCells := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    have hwindow : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      (S.subset_body index hindex).2
    have hcoordinates :
        |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hwindow
    have h0 : ⌊point 0 / rho⌋ ∈
        Finset.Icc (-(cellBound : ℤ)) (cellBound : ℤ) := by
      rw [Finset.mem_Icc]
      exact grid1d_bounded (R := 1) (h := rho) (by norm_num) hrho
        hcoordinates.1 cellBound rfl
    have h1 : ⌊point 1 / rho⌋ ∈
        Finset.Icc (-(cellBound : ℤ)) (cellBound : ℤ) := by
      rw [Finset.mem_Icc]
      exact grid1d_bounded (R := 1) (h := rho) (by norm_num) hrho
        hcoordinates.2.1 cellBound rfl
    have h2 : ⌊point 2 / rho⌋ ∈
        Finset.Icc (-(cellBound : ℤ)) (cellBound : ℤ) := by
      rw [Finset.mem_Icc]
      exact grid1d_bounded (R := 1) (h := rho) (by norm_num) hrho
        hcoordinates.2.2 cellBound rfl
    change (⌊point 0 / rho⌋, ⌊point 1 / rho⌋, ⌊point 2 / rho⌋) ∈
      cellInterval.product (cellInterval.product cellInterval)
    exact Finset.mem_product.mpr
      ⟨h0, Finset.mem_product.mpr ⟨h1, h2⟩⟩
  have hsameLabel : ∀ point ∈ S.union, ∀ other ∈ S.union,
      cell point = cell other → label point = label other →
      dist (planeMap.planeMap point)
        (planeMap.planeMap other) ≤ rho := by
    intro point hpoint other hother _ hlabel
    apply hcapDiameter (label point)
    · exact hlabelCap point hpoint
    · rw [hlabel]
      exact hlabelCap other hother
  have hallowedNonempty : ∀ _cell ∈ activeCells,
      (Finset.univ : Finset Label).Nonempty := by
    intro _ _
    exact Finset.univ_nonempty
  have hlabelAllowed : ∀ point ∈ S.union,
      label point ∈ (Finset.univ : Finset Label) := by simp
  have hlabelBound : ∀ _cell ∈ activeCells,
      ((Finset.univ : Finset Label).card : ENNReal) ≤
        (unitPlaneMapCapCount rho : ENNReal) := by
    intro _ _
    simp [unitPlaneMapCapCount, Label, N]
  have hchosenMeasurable : ∀ chosen : (ℤ × ℤ × ℤ) → Label,
      Measurable chosen := fun _ => Measurable.of_discrete
  rcases paper_cellwise_bounded_label_variation_refinement
      S planeMap.planeMap cell hcellMeasurable activeCells
      hsupport label hlabelMeasurable (fun _ => Finset.univ)
      hallowedNonempty hlabelAllowed
      (unitPlaneMapCapCount rho : ENNReal) hlabelBound
      hchosenMeasurable hsameLabel with
    ⟨_chosen, cellSelected, _hcellSelectedEq, hcellSub, hsameCell, hcellMultiplicity,
      hcellMass⟩
  rcases paper_nearby_cell_residue_refinement
      planeMap.planeMap hrho hsameCell with
    ⟨selected, hselectedSubCell, hnearby, hselectedMultiplicityCell,
      hresidueMass⟩
  have hselectedSub : PaperIsSubshading selected S :=
    fun index => (hselectedSubCell index).trans (hcellSub index)
  have hselectedMultiplicity : ∀ point ∈ selected.union,
      selected.pointMultiplicity point = S.pointMultiplicity point := by
    intro point hpoint
    have hpointCell : point ∈ cellSelected.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hselectedSubCell index hindex⟩
    exact (hselectedMultiplicityCell point hpoint).trans
      (hcellMultiplicity point hpointCell)
  refine ⟨selected, hselectedSub, hnearby, hselectedMultiplicity, ?_⟩
  calc
    S.mass ≤ (unitPlaneMapCapCount rho : ENNReal) *
        cellSelected.mass := hcellMass
    _ ≤ (unitPlaneMapCapCount rho : ENNReal) *
        (27 * selected.mass) := by gcongr
    _ = 27 * (unitPlaneMapCapCount rho : ENNReal) *
        selected.mass := by ring

end Kakeya.Assouad.PureWZ2

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseTubeLabelRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StableVerticalNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering

/-!
# Local direction-cap refinement inside a dense cluster

The active directions in a dense branch lie in a radius-`2 kappa` Euclidean
ball around the cellwise center after orienting them by the paper line class.
Cover only this local ball by caps of diameter `eta`.  The loss is therefore
polynomial in `kappa / eta`, rather than polynomial in `1 / eta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Number of coordinate caps needed to cover a radius-`2 kappa` direction
ball by sets of diameter at most `eta`. -/
def denseLocalDirectionLabelCount (kappa eta : ℝ) : ℕ :=
  let N := Nat.ceil (4 * Real.sqrt 3 * kappa / eta) + 1
  Fintype.card (Fin 3 → Fin N)

/-- Refine a dense direction cluster to one local direction cap in each fine
cell.  The output retains a pointwise multiplicity fraction and all retained
directions through one point are `eta`-close. -/
theorem paper_dense_local_direction_refinement
    {delta kappa eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hline : WZ1PaperIsLineClass F)
    (hScubical : WZ1PaperIsCubicalShading S)
    (center : Point3 → Fin F.card)
    (hcenterMeasurable : Measurable center)
    (hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second)
    (hcluster : ∀ index point, point ∈ S.carrier index →
      ‖wz1Cross (F.tube (center point)).direction
        (F.tube index).direction‖ < kappa) :
    ∃ (selected : WZ1PaperTubeShading F)
      (newCenter : Point3 → Fin F.card),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      Measurable newCenter ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        newCenter first = newCenter second) ∧
      (∀ point ∈ selected.union,
        point ∈ selected.carrier (newCenter point)) ∧
      (∀ point ∈ selected.union, ∀ first second,
        point ∈ selected.carrier first →
        point ∈ selected.carrier second →
        ‖wz1PaperDirection (F.tube first) -
          wz1PaperDirection (F.tube second)‖ ≤ eta) ∧
      (∀ point ∈ S.union,
        S.pointMultiplicity point ≤
          denseLocalDirectionLabelCount kappa eta *
            selected.pointMultiplicity point) ∧
      S.mass ≤
        (denseLocalDirectionLabelCount kappa eta : ENNReal) *
          selected.mass := by
  classical
  let N : ℕ := Nat.ceil (4 * Real.sqrt 3 * kappa / eta) + 1
  have hN : 1 ≤ N := by
    dsimp only [N]
    omega
  have hceil : 4 * Real.sqrt 3 * kappa / eta ≤
      (Nat.ceil (4 * Real.sqrt 3 * kappa / eta) : ℝ) :=
    Nat.le_ceil _
  have hNstrict : 4 * Real.sqrt 3 * kappa / eta < (N : ℝ) := by
    dsimp only [N]
    have hsucc :
        (Nat.ceil (4 * Real.sqrt 3 * kappa / eta) : ℝ) <
          (Nat.ceil (4 * Real.sqrt 3 * kappa / eta) + 1 : ℕ) := by
      simp
    exact hceil.trans_lt hsucc
  have hNpositive : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiam : Real.sqrt 3 * (2 * (2 * kappa) / N) ≤ eta := by
    have hmul : 4 * Real.sqrt 3 * kappa < (N : ℝ) * eta := by
      calc
        4 * Real.sqrt 3 * kappa =
            (4 * Real.sqrt 3 * kappa / eta) * eta := by
          field_simp [heta.ne']
        _ < (N : ℝ) * eta := by gcongr
    have hdiv : 4 * Real.sqrt 3 * kappa / (N : ℝ) < eta := by
      calc
        4 * Real.sqrt 3 * kappa / (N : ℝ) <
            ((N : ℝ) * eta) / (N : ℝ) := by gcongr
        _ = eta := by field_simp [hNpositive.ne']
    have heq : Real.sqrt 3 * (2 * (2 * kappa) / (N : ℝ)) =
        4 * Real.sqrt 3 * kappa / (N : ℝ) := by ring
    rw [heq]
    exact hdiv.le
  let Label := Fin 3 → Fin N
  choose cap hcap using fun centerIndex : Fin F.card =>
    grid_covering_cover
      (wz1PaperDirection (F.tube centerIndex))
      (2 * kappa) eta (mul_nonneg (by norm_num) hkappaNonnegative)
      N hN heta hdiam
  let belongs (point : Point3) (index : Fin F.card)
      (label : Label) : Prop :=
    wz1PaperDirection (F.tube index) ∈ cap (center point) label
  have hbelongsMeasurable : ∀ index label,
      MeasurableSet {point | belongs point index label} := by
    intro index label
    have heq : {point | belongs point index label} =
        center ⁻¹' {centerIndex |
          wz1PaperDirection (F.tube index) ∈ cap centerIndex label} := rfl
    rw [heq]
    exact hcenterMeasurable MeasurableSet.of_discrete
  have hbelongsCover : ∀ index point, point ∈ S.carrier index →
      ∃ label, belongs point index label := by
    intro index point hpoint
    have hpaperClose : ‖wz1PaperDirection (F.tube (center point)) -
        wz1PaperDirection (F.tube index)‖ ≤ 2 * kappa := by
      apply paper_direction_sub_norm_le_of_cross_le
        (hline (center point)) (hline index)
        hkappaNonnegative hkappaHalf
      rw [← raw_cross_norm_eq_paper_cross_norm]
      exact (hcluster index point hpoint).le
    have hball : dist (wz1PaperDirection (F.tube index))
        (wz1PaperDirection (F.tube (center point))) ≤ 2 * kappa := by
      simpa [dist_eq_norm, norm_sub_rev] using hpaperClose
    rcases (hcap (center point)).2.1
        (wz1PaperDirection (F.tube index)) hball with ⟨label, hlabel⟩
    exact ⟨label, hlabel⟩
  have hbelongsConst : ∀ index label first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      (belongs first index label ↔ belongs second index label) := by
    intro index label first second hcell
    simp [belongs, hcenterCell first second hcell]
  rcases paper_fine_cell_tube_label_multiplicity_refinement
      S hScubical hdelta belongs hbelongsMeasurable
      hbelongsCover hbelongsConst with
    ⟨chosen, selected, hsub, hselectedCubical, hselectedBelongs,
      hmultiplicity, hmass⟩
  have hdirections : ∀ point ∈ selected.union, ∀ first second,
      point ∈ selected.carrier first →
      point ∈ selected.carrier second →
      ‖wz1PaperDirection (F.tube first) -
        wz1PaperDirection (F.tube second)‖ ≤ eta := by
    intro point hpoint first second hfirst hsecond
    have hfirstCap := hselectedBelongs first point hfirst
    have hsecondCap := hselectedBelongs second point hsecond
    exact (hcap (center point)).2.2 (chosen (wz1PaperGridIndex delta point))
      (wz1PaperDirection (F.tube first))
      (wz1PaperDirection (F.tube second)) hfirstCap hsecondCap
  have hcount : Fintype.card Label =
      denseLocalDirectionLabelCount kappa eta := by
    simp [Label, N, denseLocalDirectionLabelCount]
  let defaultCenter : Fin F.card := center 0
  let active (point : Point3) : Finset (Fin F.card) :=
    Finset.univ.filter fun index => point ∈ selected.carrier index
  let cellCenter (cell : ℤ × ℤ × ℤ) : Fin F.card :=
    let corner := tubeLabelCellCorner delta cell
    if hactive : (active corner).Nonempty then
      (active corner).min' hactive
    else defaultCenter
  let newCenter (point : Point3) : Fin F.card :=
    cellCenter (wz1PaperGridIndex delta point)
  have hnewCenterMeasurable : Measurable newCenter := by
    have hgrid : Measurable (wz1PaperGridIndex delta) := by
      have h : Measurable (fun point : Point3 =>
          (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
            ⌊point 2 / delta⌋)) := by fun_prop
      convert h using 1
      funext point
      simp [wz1PaperGridIndex, gridIndex]
    exact (show Measurable cellCenter from Measurable.of_discrete).comp hgrid
  have hnewCenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      newCenter first = newCenter second := by
    intro first second hcell
    simp [newCenter, hcell]
  have hnewCenterMem : ∀ point ∈ selected.union,
      point ∈ selected.carrier (newCenter point) := by
    intro point hpoint
    let currentCell := wz1PaperGridIndex delta point
    let corner := tubeLabelCellCorner delta currentCell
    have hsame : wz1PaperGridIndex delta corner =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta currentCell corner).mp
        (tubeLabelCellCorner_mem_cube hdelta currentCell)
    have hactiveNonempty : (active corner).Nonempty := by
      rcases hpoint with ⟨index, hindex⟩
      have hcorner : corner ∈ selected.carrier index :=
        (hselectedCubical.carrier_mem_iff_of_same_cell index hsame).mpr hindex
      exact ⟨index, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hcorner⟩⟩
    have hmem := Finset.min'_mem (active corner) hactiveNonempty
    have hcornerCenter : corner ∈ selected.carrier
        ((active corner).min' hactiveNonempty) :=
      (Finset.mem_filter.mp hmem).2
    have hpointCenter : point ∈ selected.carrier
        ((active corner).min' hactiveNonempty) :=
      (hselectedCubical.carrier_mem_iff_of_same_cell
        ((active corner).min' hactiveNonempty) hsame).mp <| by
        simpa only using hcornerCenter
    simpa [newCenter, cellCenter, currentCell, corner, hactiveNonempty]
      using hpointCenter
  rw [← hcount]
  exact ⟨selected, newCenter, hsub, hselectedCubical,
    hnewCenterMeasurable, hnewCenterCell, hnewCenterMem, hdirections,
    hmultiplicity, hmass⟩

end Kakeya.Assouad.PureWZ2

end

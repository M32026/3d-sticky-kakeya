import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseTubeLabelRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StableVerticalNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering

/-!
# Global cellwise direction caps and an exact-incidence plane map

Cover the complete unit direction sphere by finitely many coordinate caps.
In every active fine grid cell, retain the cap carrying the largest number of
active tube labels.  A genuine retained tube in the same cell then supplies
the center direction.  Its stable vertical normal is a unit weak plane map
whose incidence scale is exactly the cap diameter.

This construction does not assume a pre-existing dense direction cluster and
does not replace the plane map by a constant function.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Number of coordinate caps used to cover all unit paper directions by
sets of diameter at most `eta`. -/
def globalDirectionCapCount (eta : ℝ) : ℕ :=
  let N := Nat.ceil (2 * Real.sqrt 3 / eta) + 1
  Fintype.card (Fin 3 → Fin N)

/-- A global cellwise direction-cap refinement.  The center at every surviving
point is an actual retained tube through that point, so the stable-normal plane
map is geometric rather than an externally chosen constant map. -/
theorem paper_global_cellwise_direction_cap_plane_map
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hFNonempty : F.Nonempty)
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hline : WZ1PaperIsLineClass F)
    (hScubical : WZ1PaperIsCubicalShading S) :
    ∃ (selected : WZ1PaperTubeShading F)
      (center : Point3 → Fin F.card)
      (planeMap : PaperWZ1WeakPlaneMapData selected eta),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      Measurable center ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        center first = center second) ∧
      (∀ point ∈ selected.union,
        point ∈ selected.carrier (center point)) ∧
      (∀ point, planeMap.planeMap point =
        stableVerticalNormal
          (wz1PaperDirection (F.tube (center point)))) ∧
      (∀ point ∈ S.union,
        S.pointMultiplicity point ≤
          globalDirectionCapCount eta *
            selected.pointMultiplicity point) ∧
      S.mass ≤
        (globalDirectionCapCount eta : ENNReal) * selected.mass := by
  classical
  let N : ℕ := Nat.ceil (2 * Real.sqrt 3 / eta) + 1
  have hN : 1 ≤ N := by
    dsimp only [N]
    omega
  have hceil : 2 * Real.sqrt 3 / eta ≤
      (Nat.ceil (2 * Real.sqrt 3 / eta) : ℝ) :=
    Nat.le_ceil _
  have hNstrict : 2 * Real.sqrt 3 / eta < (N : ℝ) := by
    dsimp only [N]
    have hsucc :
        (Nat.ceil (2 * Real.sqrt 3 / eta) : ℝ) <
          (Nat.ceil (2 * Real.sqrt 3 / eta) + 1 : ℕ) := by
      simp
    exact hceil.trans_lt hsucc
  have hNpositive : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hdiam : Real.sqrt 3 * (2 * 1 / N) ≤ eta := by
    have hmul : 2 * Real.sqrt 3 < (N : ℝ) * eta := by
      calc
        2 * Real.sqrt 3 = (2 * Real.sqrt 3 / eta) * eta := by
          field_simp [heta.ne']
        _ < (N : ℝ) * eta := by gcongr
    have hdiv : 2 * Real.sqrt 3 / (N : ℝ) < eta := by
      calc
        2 * Real.sqrt 3 / (N : ℝ) <
            ((N : ℝ) * eta) / (N : ℝ) := by gcongr
        _ = eta := by field_simp [hNpositive.ne']
    have heq : Real.sqrt 3 * (2 * 1 / (N : ℝ)) =
        2 * Real.sqrt 3 / (N : ℝ) := by ring
    rw [heq]
    exact hdiv.le
  obtain ⟨cap, hcapMeasurable, hcapCover, hcapDiameter⟩ :=
    grid_covering_cover (0 : Point3) 1 eta (by norm_num)
      N hN heta hdiam
  let Label := Fin 3 → Fin N
  let belongs (_point : Point3) (index : Fin F.card)
      (label : Label) : Prop :=
    wz1PaperDirection (F.tube index) ∈ cap label
  have hbelongsMeasurable : ∀ index label,
      MeasurableSet {point | belongs point index label} := by
    intro index label
    by_cases hlabel : wz1PaperDirection (F.tube index) ∈ cap label
    · simpa [belongs, hlabel] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set Point3))
    · simpa [belongs, hlabel] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Point3))
  have hbelongsCover : ∀ index point, point ∈ S.carrier index →
      ∃ label, belongs point index label := by
    intro index _point _hpoint
    have hunit := wz1PaperDirection_norm (F.tube index)
    have hball : dist (wz1PaperDirection (F.tube index))
        (0 : Point3) ≤ 1 := by
      simpa [dist_zero_right, hunit]
    exact hcapCover (wz1PaperDirection (F.tube index)) hball
  have hbelongsConst : ∀ index label first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      (belongs first index label ↔ belongs second index label) := by
    intro index label first second _hcell
    rfl
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
    intro point _hpoint first second hfirst hsecond
    have hfirstCap := hselectedBelongs first point hfirst
    have hsecondCap := hselectedBelongs second point hsecond
    simpa [dist_eq_norm] using
      hcapDiameter (chosen (wz1PaperGridIndex delta point))
        (wz1PaperDirection (F.tube first))
        (wz1PaperDirection (F.tube second)) hfirstCap hsecondCap
  have hcount : Fintype.card Label = globalDirectionCapCount eta := by
    simp [Label, N, globalDirectionCapCount]
  let defaultCenter : Fin F.card := ⟨0, hFNonempty⟩
  let active (point : Point3) : Finset (Fin F.card) :=
    Finset.univ.filter fun index => point ∈ selected.carrier index
  let cellCenter (cell : ℤ × ℤ × ℤ) : Fin F.card :=
    let corner := tubeLabelCellCorner delta cell
    if hactive : (active corner).Nonempty then
      (active corner).min' hactive
    else defaultCenter
  let center (point : Point3) : Fin F.card :=
    cellCenter (wz1PaperGridIndex delta point)
  have hcenterMeasurable : Measurable center := by
    have hgrid : Measurable (wz1PaperGridIndex delta) := by
      have h : Measurable (fun point : Point3 =>
          (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
            ⌊point 2 / delta⌋)) := by fun_prop
      convert h using 1
      funext point
      simp [wz1PaperGridIndex, gridIndex]
    exact (show Measurable cellCenter from Measurable.of_discrete).comp hgrid
  have hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second := by
    intro first second hcell
    simp [center, hcell]
  have hcenterMem : ∀ point ∈ selected.union,
      point ∈ selected.carrier (center point) := by
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
    simpa [center, cellCenter, currentCell, corner, hactiveNonempty]
      using hpointCenter
  let planeMap : PaperWZ1WeakPlaneMapData selected eta :=
    { planeMap := fun point =>
        stableVerticalNormal
          (wz1PaperDirection (F.tube (center point)))
      measurable := by
        have hfinite : Measurable fun index : Fin F.card =>
            stableVerticalNormal
              (wz1PaperDirection (F.tube index)) :=
          measurable_of_finite _
        exact hfinite.comp hcenterMeasurable
      unit := by
        intro point _hpoint
        apply stableVerticalNormal_unit
        exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
          (paper_direction_cross_axis_lower (hline (center point)))
      incidence := by
        intro index point hpoint
        have hpointUnion : point ∈ selected.union := ⟨index, hpoint⟩
        have hcenterCross : 0 < ‖wz1Cross
            (wz1PaperDirection (F.tube (center point)))
            verticalNormalAxis‖ :=
          (by norm_num : (0 : ℝ) < 1 / 2).trans_le
            (paper_direction_cross_axis_lower (hline (center point)))
        have hdirection := hdirections point hpointUnion
          (center point) index (hcenterMem point hpointUnion) hpoint
        have hpaperCross : ‖wz1Cross
            (wz1PaperDirection (F.tube (center point)))
            (wz1PaperDirection (F.tube index))‖ ≤ eta := by
          let u := wz1PaperDirection (F.tube (center point))
          let v := wz1PaperDirection (F.tube index)
          have heq : wz1Cross u v = wz1Cross (u - v) v := by
            have hdecomp : u = (u - v) + v := by abel
            rw [hdecomp, wz1Cross_add_left]
            simp [wz1Cross]
          rw [heq]
          exact (wz1Cross_norm_le (u - v) v).trans <| by
            rw [wz1PaperDirection_norm, mul_one]
            exact hdirection
        rw [abs_inner_raw_eq_paperDirection]
        exact (stableVerticalNormal_incidence
          (wz1PaperDirection (F.tube (center point)))
          (wz1PaperDirection (F.tube index))
          (wz1PaperDirection_norm _) (wz1PaperDirection_norm _)
          hcenterCross).trans hpaperCross }
  rw [hcount] at hmultiplicity hmass
  exact ⟨selected, center, planeMap, hsub, hselectedCubical,
    hcenterMeasurable, hcenterCell, hcenterMem, (fun _ => rfl),
    hmultiplicity, hmass⟩

end Kakeya.Assouad.PureWZ2

end

import MyLeanRepo.Kakeya.Assouad.WZ1.PropertyPEnergySelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Property-(P) energy selection on cropped paper shadings

Choose the Property-(P) grid parameter `rho = (sqrt 3 / 2) * delta`.
Its grid side is exactly `delta`, so the occupied-region refinement is a
union of the original paper cells.  Consequently the generic multiplicity
energy selection preserves paper cubicality without intersecting with an
ordinary unit-segment carrier.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- At the canonical Property-(P) parameter, the two grid indices agree. -/
lemma property_p_grid_index_eq_paper_grid_index
    {delta : ℝ} (hdelta : 0 < delta) :
    rhoGridIndex ((Real.sqrt 3 / 2) * delta) =
      wz1PaperGridIndex delta := by
  funext point
  have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
  simp only [rhoGridIndex, wz1PaperGridIndex, gridSide]
  have hside : 2 * ((Real.sqrt 3 / 2) * delta) / Real.sqrt 3 =
      delta := by
    field_simp [hsqrt]
  rw [hside]

/-- Select a genuine distinguished paper tube by multiplicity energy.  The
selected shading is cubical on the original `delta` grid and satisfies the
literal same-cell Property (P). -/
theorem paper_property_p_energy_selection
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (hdelta : 0 < delta)
    (hfamily : family.Nonempty)
    (hcubical : WZ1PaperIsCubicalShading source) :
    ∃ (distinguished : Fin family.card)
      (selected : WZ1PaperTubeShading family),
      (∀ index, selected.carrier index ⊆ source.carrier index) ∧
      (∀ index, selected.carrier index =
        source.carrier index ∩ selected.union) ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        ∃ witness ∈ selected.carrier distinguished,
          rhoGridIndex ((Real.sqrt 3 / 2) * delta) point =
            rhoGridIndex ((Real.sqrt 3 / 2) * delta) witness) ∧
      source.mass ^ 2 ≤
        volume source.union * family.enncard * selected.mass := by
  let rho : ℝ := (Real.sqrt 3 / 2) * delta
  rcases property_p_energy_selection rho source hfamily with
    ⟨distinguished, selected, hselectedSub, hselectedCarrier,
      hpropertyP, hmass⟩
  have hgrid : rhoGridIndex rho = wz1PaperGridIndex delta := by
    simpa [rho] using property_p_grid_index_eq_paper_grid_index hdelta
  have hselectedCommon : ∀ index, selected.carrier index =
      source.carrier index ∩ selected.union := by
    intro index
    rw [hselectedCarrier index]
    ext point
    constructor
    · rintro ⟨hsource, hregion⟩
      exact ⟨hsource, ⟨index, by
        rw [hselectedCarrier index]
        exact ⟨hsource, hregion⟩⟩⟩
    · rintro ⟨hsource, witness, hwitness⟩
      rw [hselectedCarrier witness] at hwitness
      exact ⟨hsource, hwitness.2⟩
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    intro index point hpoint other hother
    have hotherSource : other ∈ source.carrier index :=
      hcubical index point (hselectedSub index hpoint) hother
    have hpaperCell : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    have hrhoCell : rhoGridIndex rho other = rhoGridIndex rho point := by
      simpa [hgrid] using hpaperCell
    have hpointRegion : point ∈
        propertyPOccupiedRegion rho source distinguished := by
      rw [hselectedCarrier index] at hpoint
      exact hpoint.2
    rcases hpointRegion with ⟨witness, hwitness, hwitnessCell⟩
    have hotherRegion : other ∈
        propertyPOccupiedRegion rho source distinguished := by
      exact ⟨witness, hwitness, hrhoCell.trans hwitnessCell⟩
    rw [hselectedCarrier index]
    exact ⟨hotherSource, hotherRegion⟩
  refine ⟨distinguished, selected, hselectedSub, hselectedCommon,
    hselectedCubical,
    hpropertyP, ?_⟩
  simpa [Kakeya.Streamlined.TubeFamily.enncard,
    wz1PaperBodyFamily] using hmass

/-- Literal Property (P) plus cubicality makes the distinguished tube carry
every retained spatial point.  The witness supplied in the same paper cell
belongs to the distinguished carrier, and the whole cell is retained in that
carrier. -/
lemma paper_property_p_union_subset_distinguished
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {selected : WZ1PaperTubeShading family}
    (distinguished : Fin family.card)
    (hcubical : WZ1PaperIsCubicalShading selected)
    (hpropertyP : ∀ point ∈ selected.union,
      ∃ witness ∈ selected.carrier distinguished,
        rhoGridIndex ((Real.sqrt 3 / 2) * delta) point =
          rhoGridIndex ((Real.sqrt 3 / 2) * delta) witness)
    (hdelta : 0 < delta) :
    selected.union ⊆ selected.carrier distinguished := by
  intro point hpoint
  rcases hpropertyP point hpoint with
    ⟨witness, hwitness, hcell⟩
  have hgrid : wz1PaperGridIndex delta point =
      wz1PaperGridIndex delta witness := by
    have heq := property_p_grid_index_eq_paper_grid_index hdelta
    simpa [heq] using hcell
  have hpointCube : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta witness) :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta witness) point).mpr hgrid
  exact hcubical distinguished witness hwitness hpointCube

end Kakeya.Assouad.PureWZ2

end

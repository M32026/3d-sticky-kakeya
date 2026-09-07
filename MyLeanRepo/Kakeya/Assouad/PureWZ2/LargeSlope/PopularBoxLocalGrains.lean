import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperPopularBox

/-!
# Whole-cell popular-box restriction with genuine local grains

The paper first restricts to one mass-popular spatial box.  A literal
intersection with that box is not cubical, so this module retains every
source `delta`-cell meeting the box.  The resulting shading is simultaneously

* a genuine common-spatial subshading of the source;
* cubical at the original scale;
* at least as massive as the literal box restriction; and
* equipped with the source local-grain field by subtype restriction.

No target normal is manufactured here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The union of all source `delta`-cells meeting `box`. -/
def pureWZ2CellsMeetingBox (delta : ℝ) (box : Set Point3) : Set Point3 :=
  (wz1PaperGridIndex delta) ⁻¹'
    {cell | (wz1PaperGridCube delta cell ∩ box).Nonempty}

theorem pureWZ2CellsMeetingBox_measurable
    (delta : ℝ) (box : Set Point3) :
    MeasurableSet (pureWZ2CellsMeetingBox delta box) := by
  have hgrid : Measurable (wz1PaperGridIndex delta) := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
          ⌊point 2 / delta⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [wz1PaperGridIndex, gridIndex]
  exact hgrid
    (DiscreteMeasurableSpace.forall_measurableSet
      {cell | (wz1PaperGridCube delta cell ∩ box).Nonempty})

theorem subset_pureWZ2CellsMeetingBox
    (delta : ℝ) (box : Set Point3) :
    box ⊆ pureWZ2CellsMeetingBox delta box := by
  intro point hpoint
  exact ⟨point,
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) point).mpr rfl,
    hpoint⟩

theorem pureWZ2CellsMeetingBox_whole_cell
    (delta : ℝ) (box : Set Point3)
    {point : Point3}
    (hpoint : point ∈ pureWZ2CellsMeetingBox delta box) :
    wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
      pureWZ2CellsMeetingBox delta box := by
  intro other hother
  have hgrid : wz1PaperGridIndex delta other =
      wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother
  change wz1PaperGridIndex delta other ∈
    {cell | (wz1PaperGridCube delta cell ∩ box).Nonempty}
  rw [hgrid]
  exact hpoint

/-- Restrict a paper shading to a common measurable ambient set. -/
def pureWZ2PaperRestrictToSet
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (set : Set Point3) (hset : MeasurableSet set) :
    WZ1PaperTubeShading family where
  carrier index := source.carrier index ∩ set
  measurable_carrier index :=
    (source.measurable_carrier index).inter hset
  subset_body index := Set.inter_subset_left.trans
    (source.subset_body index)

@[simp] theorem pureWZ2PaperRestrictToSet_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (set : Set Point3) (hset : MeasurableSet set) (index) :
    (pureWZ2PaperRestrictToSet source set hset).carrier index =
      source.carrier index ∩ set := rfl

theorem pureWZ2PaperRestrictToSet_union
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (set : Set Point3) (hset : MeasurableSet set) :
    (pureWZ2PaperRestrictToSet source set hset).union =
      source.union ∩ set := by
  ext point
  constructor
  · rintro ⟨index, hsource, hsetPoint⟩
    exact ⟨⟨index, hsource⟩, hsetPoint⟩
  · rintro ⟨⟨index, hsource⟩, hsetPoint⟩
    exact ⟨index, hsource, hsetPoint⟩

theorem pureWZ2PaperRestrictToSet_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {set : Set Point3} {hset : MeasurableSet set}
    (hcubical : WZ1PaperIsCubicalShading source)
    (hwhole : ∀ point ∈ set,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ set) :
    WZ1PaperIsCubicalShading
      (pureWZ2PaperRestrictToSet source set hset) := by
  intro index point hpoint other hother
  exact ⟨hcubical index point hpoint.1 hother,
    hwhole point hpoint.2 hother⟩

/-- The source-side output used by the affine-diagonal construction. -/
structure PureWZ2PopularBoxLocalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) (width : ℝ) where
  center : Point3
  center_mem : center ∈ wz1MildRescalingSourceWindow
  box : Set Point3
  box_eq : box = wz1MildRescalingSourceBox center
    (point3 (width / 2) (width / 2) (width / 2))
  box_measurable : MeasurableSet box
  selected : WZ1PaperTubeShading family
  selected_carrier : ∀ index, selected.carrier index =
    source.carrier index ∩ pureWZ2CellsMeetingBox delta box
  selected_subshading : ∀ index,
    selected.carrier index ⊆ source.carrier index
  selected_union : selected.union =
    source.union ∩ pureWZ2CellsMeetingBox delta box
  selected_cubical : WZ1PaperIsCubicalShading selected
  selected_local : PureWZ2LocalGrainData selected sigma C
  mass_lower : ENNReal.ofReal (width ^ 3 / 27) * source.mass ≤
    selected.mass

/-- Select a mass-popular box and retain all source cells meeting it. -/
theorem pureWZ2_popular_box_local_grains
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData source sigma C)
    (hcubical : WZ1PaperIsCubicalShading source)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty
      (PureWZ2PopularBoxLocalGrainData
        source sigma C width) := by
  rcases pureWZ2_paper_popular_box source hwidth hwidthOne with
    ⟨popular⟩
  let cells := pureWZ2CellsMeetingBox delta popular.box
  have hcellsMeasurable : MeasurableSet cells :=
    pureWZ2CellsMeetingBox_measurable delta popular.box
  let selected :=
    pureWZ2PaperRestrictToSet source cells hcellsMeasurable
  have hsub : ∀ index, selected.carrier index ⊆
      source.carrier index := by
    intro index
    exact Set.inter_subset_left
  have hcubicalSelected : WZ1PaperIsCubicalShading selected :=
    pureWZ2PaperRestrictToSet_cubical hcubical
      (fun point hpoint =>
        pureWZ2CellsMeetingBox_whole_cell delta popular.box hpoint)
  let selectedLocal := sourceLocal.restrict hsub
  have hmass :
      ENNReal.ofReal (width ^ 3 / 27) * source.mass ≤
        selected.mass := by
    calc
      ENNReal.ofReal (width ^ 3 / 27) * source.mass
          ≤ popular.restricted.mass := popular.mass_lower
      _ ≤ selected.mass := by
        change (∑ index, volume (popular.restricted.carrier index)) ≤
          ∑ index, volume (selected.carrier index)
        apply Finset.sum_le_sum
        intro index _
        rw [popular.restricted_carrier index]
        change volume (source.carrier index ∩ popular.box) ≤
          volume (source.carrier index ∩ cells)
        exact measure_mono (Set.inter_subset_inter_right _
          (subset_pureWZ2CellsMeetingBox delta popular.box))
  exact ⟨{
    center := popular.center
    center_mem := popular.center_mem
    box := popular.box
    box_eq := popular.box_eq
    box_measurable := popular.box_measurable
    selected := selected
    selected_carrier := fun _ => rfl
    selected_subshading := hsub
    selected_union := pureWZ2PaperRestrictToSet_union
      source cells hcellsMeasurable
    selected_cubical := hcubicalSelected
    selected_local := selectedLocal
    mass_lower := hmass
  }⟩

end Kakeya.Assouad

end

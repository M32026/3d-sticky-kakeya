import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Ordinary shadings inside the cropped WZ carrier model

For a family supported in the unit ball, every ordinary unit-segment tube
carrier is contained in the corresponding cropped full-line WZ carrier.
Therefore an ordinary shading can be reused without changing any shaded set,
mass, union, or point multiplicity.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The ordinary unit axis segment lies in its full coaxial line. -/
theorem wz2_paper_unitSegment_subset_axisLine
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Kakeya.unitSegment tube.base tube.direction ⊆
      tubeAxisLine tube := by
  rintro point ⟨parameter, _hparameter, rfl⟩
  exact ⟨parameter, rfl⟩

/-- The closed unit ball is contained in the fixed crop box. -/
theorem wz2_paper_unitBall_subset_axisBox :
    Kakeya.DeltaTube.unitBall ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
  intro point hpoint
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [
      Kakeya.DeltaTube.unitBall,
      Metric.mem_closedBall,
      dist_zero_right
    ] using hpoint
  simp only [
    Kakeya.Streamlined.axisBox,
    Set.mem_setOf_eq
  ]
  norm_num
  exact
    ⟨(PiLp.norm_apply_le point 0).trans hnorm,
      (PiLp.norm_apply_le point 1).trans hnorm,
      (PiLp.norm_apply_le point 2).trans hnorm⟩

/-- A supported ordinary tube lies in its corresponding cropped WZ carrier. -/
theorem wz2_paper_ordinary_carrier_subset_cropped
    {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (tube : Kakeya.DeltaTube delta)
    (hsupport :
      tube.carrier ⊆ Kakeya.DeltaTube.unitBall) :
    tube.carrier ⊆ wz1PaperTubeCarrier tube := by
  intro point hpoint
  constructor
  · exact
      Metric.cthickening_mono
        (by linarith : delta ≤ 6 * delta)
        (tubeAxisLine tube)
        (Metric.cthickening_subset_of_subset delta
          (wz2_paper_unitSegment_subset_axisLine tube)
          hpoint)
  · exact wz2_paper_unitBall_subset_axisBox (hsupport hpoint)

/-- Reuse an ordinary shading as a cropped WZ shading without changing its
carriers. -/
noncomputable def wz2PaperOrdinaryShadingToCropped
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 ≤ delta)
    (hsupport : family.IsInUnitBall)
    (shading : Kakeya.Streamlined.TubeShading family) :
    WZ1PaperTubeShading family where
  carrier := shading.carrier
  measurable_carrier := shading.measurable_carrier
  subset_body index :=
    shading.subset_body index |>.trans
      (wz2_paper_ordinary_carrier_subset_cropped
        hdelta (family.tube index) (hsupport index))

@[simp] theorem wz2PaperOrdinaryShadingToCropped_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 ≤ delta)
    (hsupport : family.IsInUnitBall)
    (shading : Kakeya.Streamlined.TubeShading family)
    (index : Fin family.card) :
    (wz2PaperOrdinaryShadingToCropped
      hdelta hsupport shading).carrier index =
      shading.carrier index := by
  rfl

@[simp] theorem wz2PaperOrdinaryShadingToCropped_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 ≤ delta)
    (hsupport : family.IsInUnitBall)
    (shading : Kakeya.Streamlined.TubeShading family) :
    (wz2PaperOrdinaryShadingToCropped
      hdelta hsupport shading).mass =
      shading.mass := by
  rfl

@[simp] theorem wz2PaperOrdinaryShadingToCropped_union
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 ≤ delta)
    (hsupport : family.IsInUnitBall)
    (shading : Kakeya.Streamlined.TubeShading family) :
    (wz2PaperOrdinaryShadingToCropped
      hdelta hsupport shading).union =
      shading.union := by
  rfl

@[simp] theorem wz2PaperOrdinaryShadingToCropped_pointMultiplicity
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 ≤ delta)
    (hsupport : family.IsInUnitBall)
    (shading : Kakeya.Streamlined.TubeShading family)
    (point : Point3) :
    (wz2PaperOrdinaryShadingToCropped
      hdelta hsupport shading).pointMultiplicity point =
      shading.pointMultiplicity point := by
  rfl

/-- Restrict a cropped shading back to the ordinary unit-segment carriers. -/
noncomputable def wz2PaperCroppedShadingToOrdinary
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    Kakeya.Streamlined.TubeShading family where
  carrier index :=
    shading.carrier index ∩ (family.tube index).carrier
  measurable_carrier index :=
    (shading.measurable_carrier index).inter
      Metric.isClosed_cthickening.measurableSet
  subset_body index := Set.inter_subset_right

@[simp] theorem wz2PaperCroppedShadingToOrdinary_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (index : Fin family.card) :
    (wz2PaperCroppedShadingToOrdinary shading).carrier index =
      shading.carrier index ∩ (family.tube index).carrier := by
  rfl

/-- Restricting cropped carriers back to ordinary carriers never increases
point multiplicity. -/
theorem wz2PaperCroppedShadingToOrdinary_pointMultiplicity_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (point : Point3) :
    (wz2PaperCroppedShadingToOrdinary shading).pointMultiplicity point ≤
      shading.pointMultiplicity point := by
  apply Finset.card_le_card
  intro index hindex
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ index,
      (Finset.mem_filter.mp hindex).2.1⟩

/-- The returned ordinary shaded union is contained in the cropped union. -/
theorem wz2PaperCroppedShadingToOrdinary_union_subset
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    (wz2PaperCroppedShadingToOrdinary shading).union ⊆
      shading.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨index, hpoint.1⟩

/-- The returned ordinary shading has no more total shaded mass. -/
theorem wz2PaperCroppedShadingToOrdinary_mass_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    (wz2PaperCroppedShadingToOrdinary shading).mass ≤
      shading.mass := by
  apply Finset.sum_le_sum
  intro index _
  exact measure_mono Set.inter_subset_left

/-- If the cropped shading already lies in the ordinary carriers, restricting
back changes nothing. -/
theorem wz2PaperCroppedShadingToOrdinary_eq_of_subset
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hsubset :
      ∀ index,
        shading.carrier index ⊆ (family.tube index).carrier) :
    (wz2PaperCroppedShadingToOrdinary shading).carrier =
      shading.carrier := by
  funext index
  exact Set.inter_eq_left.mpr (hsubset index)

/--
An ordinary Convex-Wolff count bound implies the corresponding cropped
carrier count bound on the same indexed family.
-/
theorem wz2_paper_ordinary_convexWolff_to_cropped
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hdelta : 0 ≤ delta)
    (hsupport : family.IsInUnitBall)
    (ordinary :
      WZ2PaperBodyConvexWolffBound family.toBodyFamily C) :
    WZ2PaperConvexWolffBound family C := by
  intro convexSet hconvex
  have hindices :
      (Finset.univ.filter fun index : Fin family.card =>
        wz1PaperTubeCarrier (family.tube index) ⊆ convexSet) ⊆
      (Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet) := by
    intro index hindex
    have hcropped :
        wz1PaperTubeCarrier (family.tube index) ⊆ convexSet :=
      (Finset.mem_filter.mp hindex).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ index,
        (wz2_paper_ordinary_carrier_subset_cropped
          hdelta (family.tube index) (hsupport index)).trans hcropped⟩
  have hcount :
      (wz1PaperBodyFamily family).containedCount convexSet ≤
        family.toBodyFamily.containedCount convexSet := by
    change
      ((Finset.univ.filter fun index : Fin family.card =>
        wz1PaperTubeCarrier (family.tube index) ⊆ convexSet).card :
          ENNReal) ≤
      ((Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet).card : ENNReal)
    exact_mod_cast Finset.card_le_card hindices
  exact
    hcount.trans (ordinary convexSet hconvex)

end Kakeya.Assouad

end

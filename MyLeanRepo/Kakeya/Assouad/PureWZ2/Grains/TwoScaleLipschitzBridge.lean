import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation

/-!
# Lipschitz bridge from fine constancy and one coarse variation scale

After a fixed fine-cell residue refinement, the plane map is exactly constant
for pairs at distance at most `delta`.  A one-scale estimate controls distances
up to `rho`, and unit norm controls larger distances.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The three distance regimes give the displayed global Lipschitz constant. -/
theorem paper_two_scale_lipschitz_bridge
    {delta rho coefficient : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcoefficient : 0 ≤ coefficient)
    (planeMap : Point3 → Point3)
    (hunit : ∀ point ∈ S.union, ‖planeMap point‖ = 1)
    (hfine : ∀ first ∈ S.union, ∀ second ∈ S.union,
      dist first second ≤ delta → planeMap first = planeMap second)
    (hcoarse : ∀ first ∈ S.union, ∀ second ∈ S.union,
      dist first second ≤ rho →
        dist (planeMap first) (planeMap second) ≤ coefficient * rho) :
    LipschitzWith
      (Real.toNNReal (max (coefficient * rho / delta) (2 / rho)))
      (fun point : {point : Point3 // point ∈ S.union} =>
        planeMap point) := by
  let L : ℝ := max (coefficient * rho / delta) (2 / rho)
  have hLnonnegative : 0 ≤ L := by
    exact (div_nonneg (by norm_num) hrho.le).trans (le_max_right _ _)
  have hLcoe : (Real.toNNReal L : ℝ) = L :=
    Real.coe_toNNReal _ hLnonnegative
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [hLcoe]
  let d := dist (first : Point3) (second : Point3)
  by_cases hfineDistance : d ≤ delta
  · have heq : planeMap first = planeMap second :=
      hfine first first.prop second second.prop hfineDistance
    calc
      dist (planeMap first) (planeMap second) = 0 := by rw [heq, dist_self]
      _ ≤ L * dist first second :=
        mul_nonneg hLnonnegative dist_nonneg
  · have hdeltaDistance : delta < d := lt_of_not_ge hfineDistance
    by_cases hcoarseDistance : d ≤ rho
    · have hvariation :=
        hcoarse first first.prop second second.prop hcoarseDistance
      have hratio : coefficient * rho / delta ≤ L := le_max_left _ _
      have hbound : coefficient * rho ≤ L * d := by
        have hdeltaNonnegative : 0 ≤ delta := hdelta.le
        have hcoefficientRho : 0 ≤ coefficient * rho :=
          mul_nonneg hcoefficient hrho.le
        calc
          coefficient * rho =
              (coefficient * rho / delta) * delta := by
            field_simp [hdelta.ne']
          _ ≤ L * delta := by gcongr
          _ ≤ L * d := by gcongr
      exact hvariation.trans hbound
    · have hrhoDistance : rho < d := lt_of_not_ge hcoarseDistance
      have hnorm : dist (planeMap first) (planeMap second) ≤ 2 := by
        calc
          dist (planeMap first) (planeMap second) =
              ‖planeMap first - planeMap second‖ := by rw [dist_eq_norm]
          _ ≤ ‖planeMap first‖ + ‖planeMap second‖ := norm_sub_le _ _
          _ = 2 := by
            rw [hunit first first.prop, hunit second second.prop]
            norm_num
      have hratio : 2 / rho ≤ L := le_max_right _ _
      have htwo : 2 ≤ L * d := by
        calc
          2 = (2 / rho) * rho := by field_simp [hrho.ne']
          _ ≤ L * rho := by gcongr
          _ ≤ L * d := by gcongr
      exact hnorm.trans htwo

/-- Add the fixed 27-color fine-cell refinement, preserving the supplied
coarse-scale variation estimate, and package the resulting Lipschitz map. -/
theorem paper_refine_to_two_scale_lipschitz
    {delta rho coefficient incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcoefficient : 0 ≤ coefficient)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (hcoarse : ∀ first ∈ S.union, ∀ second ∈ S.union,
      dist first second ≤ rho →
        dist (planeMap.planeMap first)
          (planeMap.planeMap second) ≤ coefficient * rho) :
    ∃ (selected : WZ1PaperTubeShading F)
      (selectedPlaneMap : PaperWZ1WeakPlaneMapData selected incidence),
      PaperIsSubshading selected S ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      S.mass ≤ 27 * selected.mass ∧
      LipschitzWith
        (Real.toNNReal (max (coefficient * rho / delta) (2 / rho)))
        (fun point : {point : Point3 // point ∈ selected.union} =>
          selectedPlaneMap.planeMap point) := by
  have hsameCell : ∀ first ∈ S.union, ∀ second ∈ S.union,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      dist (planeMap.planeMap first) (planeMap.planeMap second) ≤ 0 := by
    intro first _ second _ hgrid
    rw [hcell first second hgrid]
    simp
  rcases paper_nearby_cell_residue_refinement
      planeMap.planeMap hdelta hsameCell with
    ⟨selected, hselectedSub, hfineVariation,
      hselectedMultiplicity, hmass⟩
  let selectedPlaneMap := paperWeakPlaneMapRestrict planeMap hselectedSub
  have hfineEquality : ∀ first ∈ selected.union,
      ∀ second ∈ selected.union, dist first second ≤ delta →
      selectedPlaneMap.planeMap first = selectedPlaneMap.planeMap second := by
    intro first hfirst second hsecond hdist
    have hzero := hfineVariation first hfirst second hsecond hdist
    exact dist_eq_zero.mp (le_antisymm hzero (dist_nonneg))
  have hcoarseSelected : ∀ first ∈ selected.union,
      ∀ second ∈ selected.union, dist first second ≤ rho →
      dist (selectedPlaneMap.planeMap first)
        (selectedPlaneMap.planeMap second) ≤ coefficient * rho := by
    intro first hfirst second hsecond hdist
    have hfirstS : first ∈ S.union := by
      rcases hfirst with ⟨index, hindex⟩
      exact ⟨index, hselectedSub index hindex⟩
    have hsecondS : second ∈ S.union := by
      rcases hsecond with ⟨index, hindex⟩
      exact ⟨index, hselectedSub index hindex⟩
    exact hcoarse first hfirstS second hsecondS hdist
  have hlipschitz := paper_two_scale_lipschitz_bridge
    hdelta hrho hcoefficient selectedPlaneMap.planeMap
    selectedPlaneMap.unit hfineEquality hcoarseSelected
  exact ⟨selected, selectedPlaneMap, hselectedSub,
    hselectedMultiplicity, hmass, hlipschitz⟩

end Kakeya.Assouad.PureWZ2

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation

/-!
# Lipschitz bridge from a finite variation schedule

Lemma 16 only needs finitely many spatial scales. Once those scales cover
every distance between the fine scale and the diameter of the unit ambient
box, their one-scale variation estimates combine with a fine-cell residue
refinement to give a genuinely 1-Lipschitz plane map. No constant-map or
single-tube reduction is used.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Two points in cropped paper shadings are at distance at most four. -/
lemma paper_shading_union_dist_le_four
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (S : WZ1PaperTubeShading F)
    {first second : Point3}
    (hfirst : first ∈ S.union)
    (hsecond : second ∈ S.union) :
    dist first second ≤ 4 := by
  rcases hfirst with ⟨firstIndex, hfirstCarrier⟩
  rcases hsecond with ⟨secondIndex, hsecondCarrier⟩
  have hfirstBox : first ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    (S.subset_body firstIndex hfirstCarrier).2
  have hsecondBox : second ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    (S.subset_body secondIndex hsecondCarrier).2
  have hfirstCoordinates :
      |first 0| ≤ 1 ∧ |first 1| ≤ 1 ∧ |first 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hfirstBox
  have hsecondCoordinates :
      |second 0| ≤ 1 ∧ |second 1| ≤ 1 ∧ |second 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hsecondBox
  have hcoordinate0 : |first 0 - second 0| ≤ 2 := by
    calc
      |first 0 - second 0| ≤ |first 0| + |second 0| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hfirstCoordinates.1 hsecondCoordinates.1
      _ = 2 := by norm_num
  have hcoordinate1 : |first 1 - second 1| ≤ 2 := by
    calc
      |first 1 - second 1| ≤ |first 1| + |second 1| := abs_sub _ _
      _ ≤ 1 + 1 :=
        add_le_add hfirstCoordinates.2.1 hsecondCoordinates.2.1
      _ = 2 := by norm_num
  have hcoordinate2 : |first 2 - second 2| ≤ 2 := by
    calc
      |first 2 - second 2| ≤ |first 2| + |second 2| := abs_sub _ _
      _ ≤ 1 + 1 :=
        add_le_add hfirstCoordinates.2.2 hsecondCoordinates.2.2
      _ = 2 := by norm_num
  have hnormSquare : ‖first - second‖ ^ 2 =
      (first 0 - second 0) ^ 2 +
        (first 1 - second 1) ^ 2 +
          (first 2 - second 2) ^ 2 := by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (first - second)
    rw [h]
    simp [Fin.sum_univ_succ, sq_abs]
    ring
  have h0 : (first 0 - second 0) ^ 2 ≤ 4 := by
    nlinarith [abs_nonneg (first 0 - second 0),
      hcoordinate0, sq_abs (first 0 - second 0)]
  have h1 : (first 1 - second 1) ^ 2 ≤ 4 := by
    nlinarith [abs_nonneg (first 1 - second 1),
      hcoordinate1, sq_abs (first 1 - second 1)]
  have h2 : (first 2 - second 2) ^ 2 ≤ 4 := by
    nlinarith [abs_nonneg (first 2 - second 2),
      hcoordinate2, sq_abs (first 2 - second 2)]
  have hnorm : ‖first - second‖ ≤ 4 := by
    have hnonnegative : 0 ≤ ‖first - second‖ := norm_nonneg _
    have hsquare : ‖first - second‖ ^ 2 ≤ 12 := by
      rw [hnormSquare]
      linarith
    nlinarith [sq_nonneg (‖first - second‖ - 4)]
  simpa [dist_eq_norm] using hnorm

/-- A finite collection of variation estimates gives an arbitrary positive
Lipschitz constant `coefficient`, provided the recorded variation at the
chosen scale is at most `coefficient * d`.  The fixed residue refinement
makes the map constant below the fine scale. -/
theorem paper_finite_scale_variation_to_lipschitz
    {delta incidence coefficient diameter : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hdelta : 0 < delta)
    (hcoefficient : 0 < coefficient)
    (hcubical : WZ1PaperIsCubicalShading S)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (N : ℕ)
    (spatialScale variationScale : ℕ → ℝ)
    (hvariation : ∀ k, k < N → ∀ first ∈ S.union, ∀ second ∈ S.union,
      dist first second ≤ spatialScale k →
        dist (planeMap.planeMap first) (planeMap.planeMap second) ≤
          variationScale k)
    (hdiameter : ∀ first ∈ S.union, ∀ second ∈ S.union,
      dist first second ≤ diameter)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ diameter →
      coefficient * d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧
        variationScale k ≤ coefficient * d) :
    ∃ (selected : WZ1PaperTubeShading F)
      (selectedPlaneMap : PaperWZ1WeakPlaneMapData selected incidence),
      PaperIsSubshading selected S ∧
      selectedPlaneMap.planeMap = planeMap.planeMap ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      S.mass ≤ 27 * selected.mass ∧
      LipschitzWith (Real.toNNReal coefficient)
        (fun point : {point : Point3 // point ∈ selected.union} =>
          selectedPlaneMap.planeMap point) := by
  have hsameCell : ∀ first ∈ S.union, ∀ second ∈ S.union,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      dist (planeMap.planeMap first) (planeMap.planeMap second) ≤ 0 := by
    intro first _ second _ hgrid
    rw [hcell first second hgrid]
    simp
  rcases paper_fine_cell_residue_refinement_cubical
      (scale := 0) planeMap.planeMap hdelta hcubical hsameCell with
    ⟨selected, hselectedSub, hselectedCubical, hfineVariation,
      hselectedMultiplicity, hmass⟩
  let selectedPlaneMap := paperWeakPlaneMapRestrict planeMap hselectedSub
  have hselectedInSource : selected.union ⊆ S.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hselectedSub index hpoint⟩
  have hfineEquality : ∀ first ∈ selected.union,
      ∀ second ∈ selected.union, dist first second ≤ delta →
        selectedPlaneMap.planeMap first =
          selectedPlaneMap.planeMap second := by
    intro first hfirst second hsecond hdist
    have hzero := hfineVariation first hfirst second hsecond hdist
    exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)
  have hlipschitz : LipschitzWith (Real.toNNReal coefficient)
      (fun point : {point : Point3 // point ∈ selected.union} =>
        selectedPlaneMap.planeMap point) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [Real.coe_toNNReal _ hcoefficient.le]
    let d : ℝ := dist (first : Point3) (second : Point3)
    by_cases hnear : d ≤ delta
    · have heq := hfineEquality first first.prop second second.prop hnear
      rw [heq, dist_self]
      positivity
    · have hdeltaDistance : delta < d := lt_of_not_ge hnear
      by_cases hfar : 2 ≤ coefficient * d
      · have hunitFirst : ‖selectedPlaneMap.planeMap first‖ = 1 :=
          selectedPlaneMap.unit first first.prop
        have hunitSecond : ‖selectedPlaneMap.planeMap second‖ = 1 :=
          selectedPlaneMap.unit second second.prop
        calc
          dist (selectedPlaneMap.planeMap first)
              (selectedPlaneMap.planeMap second) =
              ‖selectedPlaneMap.planeMap first -
                selectedPlaneMap.planeMap second‖ := by rw [dist_eq_norm]
          _ ≤ ‖selectedPlaneMap.planeMap first‖ +
              ‖selectedPlaneMap.planeMap second‖ := norm_sub_le _ _
          _ = 2 := by rw [hunitFirst, hunitSecond]; norm_num
          _ ≤ coefficient * d := hfar
      · have hdiameterDistance : d ≤ diameter :=
          hdiameter first (hselectedInSource first.prop)
            second (hselectedInSource second.prop)
        rcases hcovers d hdeltaDistance hdiameterDistance
            (lt_of_not_ge hfar) with
          ⟨k, hk, hdSpatial, hvariationDistance⟩
        have hscale := hvariation k hk
          (first : Point3) (hselectedInSource first.prop)
          (second : Point3) (hselectedInSource second.prop) hdSpatial
        exact hscale.trans hvariationDistance
  exact ⟨selected, selectedPlaneMap, hselectedSub, rfl, hselectedCubical,
    hselectedMultiplicity, hmass, hlipschitz⟩

/-- A finite collection of one-scale variation estimates gives a global
1-Lipschitz map provided it covers every intermediate distance. Distances at
most delta are made constant by the fixed 27-residue refinement, while
distances at least 2 use only that both plane normals are unit vectors. -/
theorem paper_finite_scale_variation_to_lipschitz_one
    {delta incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading S)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (N : ℕ)
    (spatialScale variationScale : ℕ → ℝ)
    (hvariation : ∀ k, k < N → ∀ first ∈ S.union, ∀ second ∈ S.union,
      dist first second ≤ spatialScale k →
        dist (planeMap.planeMap first) (planeMap.planeMap second) ≤
          variationScale k)
    (hcovers : ∀ d : ℝ, delta < d → d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧ variationScale k ≤ d) :
    ∃ (selected : WZ1PaperTubeShading F)
      (selectedPlaneMap : PaperWZ1WeakPlaneMapData selected incidence),
      PaperIsSubshading selected S ∧
      selectedPlaneMap.planeMap = planeMap.planeMap ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      S.mass ≤ 27 * selected.mass ∧
      LipschitzWith 1
        (fun point : {point : Point3 // point ∈ selected.union} =>
          selectedPlaneMap.planeMap point) := by
  have hsameCell : ∀ first ∈ S.union, ∀ second ∈ S.union,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      dist (planeMap.planeMap first) (planeMap.planeMap second) ≤ 0 := by
    intro first _ second _ hgrid
    rw [hcell first second hgrid]
    simp
  rcases paper_fine_cell_residue_refinement_cubical
      (scale := 0) planeMap.planeMap hdelta hcubical hsameCell with
    ⟨selected, hselectedSub, hselectedCubical, hfineVariation,
      hselectedMultiplicity, hmass⟩
  let selectedPlaneMap := paperWeakPlaneMapRestrict planeMap hselectedSub
  have hselectedInSource : selected.union ⊆ S.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hselectedSub index hpoint⟩
  have hfineEquality : ∀ first ∈ selected.union,
      ∀ second ∈ selected.union, dist first second ≤ delta →
        selectedPlaneMap.planeMap first =
          selectedPlaneMap.planeMap second := by
    intro first hfirst second hsecond hdist
    have hzero := hfineVariation first hfirst second hsecond hdist
    exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)
  have hlipschitz : LipschitzWith 1
      (fun point : {point : Point3 // point ∈ selected.union} =>
        selectedPlaneMap.planeMap point) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simp only [NNReal.coe_one, one_mul]
    let d : ℝ := dist (first : Point3) (second : Point3)
    by_cases hnear : d ≤ delta
    · have heq := hfineEquality first first.prop second second.prop hnear
      rw [heq, dist_self]
      exact dist_nonneg
    · have hdeltaDistance : delta < d := lt_of_not_ge hnear
      by_cases hfar : 2 ≤ d
      · have hunitFirst : ‖selectedPlaneMap.planeMap first‖ = 1 :=
          selectedPlaneMap.unit first first.prop
        have hunitSecond : ‖selectedPlaneMap.planeMap second‖ = 1 :=
          selectedPlaneMap.unit second second.prop
        calc
          dist (selectedPlaneMap.planeMap first)
              (selectedPlaneMap.planeMap second) =
              ‖selectedPlaneMap.planeMap first -
                selectedPlaneMap.planeMap second‖ := by rw [dist_eq_norm]
          _ ≤ ‖selectedPlaneMap.planeMap first‖ +
              ‖selectedPlaneMap.planeMap second‖ := norm_sub_le _ _
          _ = 2 := by rw [hunitFirst, hunitSecond]; norm_num
          _ ≤ d := hfar
      · have hdTwo : d < 2 := lt_of_not_ge hfar
        rcases hcovers d hdeltaDistance hdTwo with
          ⟨k, hk, hdSpatial, hvariationDistance⟩
        have hscale := hvariation k hk
          (first : Point3) (hselectedInSource first.prop)
          (second : Point3) (hselectedInSource second.prop) hdSpatial
        exact hscale.trans hvariationDistance
  exact ⟨selected, selectedPlaneMap, hselectedSub, rfl, hselectedCubical,
    hselectedMultiplicity, hmass, hlipschitz⟩

end Kakeya.Assouad.PureWZ2

end

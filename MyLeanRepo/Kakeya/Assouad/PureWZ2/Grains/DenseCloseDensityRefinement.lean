import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseDirectionDichotomy
import Mathlib.Tactic

/-!
# Dense-close refinement paid by a cardinality density power

This replaces the dyadic upper-multiplicity payment in the dense branch.  The
trivial pointwise bound by the ambient family cardinality, together with
`densityPower * #F ≤ m`, pays the selected close cluster directly.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

theorem dense_close_plane_map_refinement_density
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF : F.Nonempty) (m : ℕ)
    (densityPower : ENNReal)
    (hdensity : densityPower * F.enncard ≤ (m : ENNReal)) :
    let dense := denseCloseCellSet S kappa m
    let hDense := denseCloseCellSet_measurable S kappa m
    let denseShading := paperRestrictShadingToSet S dense hDense
    ∃ (center : Point3 → Fin F.card)
      (selected : WZ1PaperTubeShading F)
      (planeMap : PaperWZ1WeakPlaneMapData selected kappa),
      Measurable center ∧
      PaperIsSubshading selected denseShading ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ index point, point ∈ selected.carrier index →
        ‖wz1Cross (F.tube (center point)).direction
          (F.tube index).direction‖ < kappa) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        center first = center second) ∧
      (∀ point ∈ denseShading.union,
        m < 2 * selected.pointMultiplicity point) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second) ∧
      densityPower * denseShading.mass ≤ 2 * selected.mass := by
  dsimp only
  let dense := denseCloseCellSet S kappa m
  let hDense := denseCloseCellSet_measurable S kappa m
  let denseShading := paperRestrictShadingToSet S dense hDense
  rcases dense_close_cellwise_center
      (S := S) (kappa := kappa) hcubical hF m with
    ⟨center, hcenterMeasurable, hcenterDense, hcenterCell⟩
  let selected : WZ1PaperTubeShading F :=
    { carrier := fun index =>
        {point | point ∈ denseShading.carrier index ∧
          ‖wz1Cross (F.tube (center point)).direction
            (F.tube index).direction‖ < kappa}
      measurable_carrier := fun index =>
        (denseShading.measurable_carrier index).inter
          (measurable_cellwise_close_direction
            hcenterMeasurable index)
      subset_body := fun index point hpoint =>
        denseShading.subset_body index hpoint.1 }
  have hdenseCubical : WZ1PaperIsCubicalShading denseShading :=
    paperRestrictShadingToSet_cubical hDense hcubical
      (denseCloseCellSet_cube_union hcubical kappa m)
  have hselectedSub : PaperIsSubshading selected denseShading :=
    fun _ _ hpoint => hpoint.1
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    intro index point hpoint other hother
    have hcell : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    have hcarrier : other ∈ denseShading.carrier index :=
      hdenseCubical index point hpoint.1 hother
    have hcenterEq : center other = center point :=
      hcenterCell other point hcell
    exact ⟨hcarrier, by simpa [hcenterEq] using hpoint.2⟩
  have hcluster : ∀ index point, point ∈ selected.carrier index →
      ‖wz1Cross (F.tube (center point)).direction
        (F.tube index).direction‖ < kappa :=
    fun _ _ hpoint => hpoint.2
  let planeMap : PaperWZ1WeakPlaneMapData selected kappa :=
    { planeMap := fun point =>
        orthogonalNormal (F.tube (center point)).direction
      measurable := by
        have hfinite : Measurable fun candidate : Fin F.card =>
            orthogonalNormal (F.tube candidate).direction :=
          measurable_of_finite _
        exact hfinite.comp hcenterMeasurable
      unit := by
        intro point _
        exact orthogonalNormal_unit (F.tube (center point)).direction
      incidence := by
        intro index point hpoint
        exact orthogonalNormal_incidence_of_cross_lt
          (F.tube (center point)).direction
          (F.tube index).direction
          (F.tube (center point)).direction_unit
          (F.tube index).direction_unit hpoint.2 }
  have hmultiplicity : ∀ point ∈ denseShading.union,
      m < 2 * selected.pointMultiplicity point := by
    intro point hpoint
    have hpointDense : point ∈ dense := by
      rcases hpoint with ⟨index, hindex⟩
      exact hindex.2
    have hlarge := (hcenterDense point hpoint).2
    have heq : paperCloseDirectionCount S point (center point) kappa =
        selected.pointMultiplicity point := by
      simp only [paperCloseDirectionCount,
        Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.ext
      intro index
      simp [selected, denseShading, paperRestrictShadingToSet,
        hpointDense]
    rwa [heq] at hlarge
  have hpointwise : ∀ point,
      densityPower * (denseShading.pointMultiplicity point : ENNReal) ≤
        2 * (selected.pointMultiplicity point : ENNReal) := by
    intro point
    by_cases hpoint : point ∈ denseShading.union
    · have htotal : denseShading.pointMultiplicity point ≤ F.card := by
        have htotalBody :
            denseShading.pointMultiplicity point ≤ F.toBodyFamily.card := by
          change (Finset.univ.filter
            (fun index : Fin F.toBodyFamily.card =>
              point ∈ denseShading.carrier index)).card ≤
                F.toBodyFamily.card
          calc
            (Finset.univ.filter
                (fun index : Fin F.toBodyFamily.card =>
                  point ∈ denseShading.carrier index)).card
                ≤ (Finset.univ :
                    Finset (Fin F.toBodyFamily.card)).card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
            _ = F.toBodyFamily.card := by simp
        simpa only [Kakeya.Streamlined.TubeFamily.toBodyFamily] using
          htotalBody
      have htotalENN :
          (denseShading.pointMultiplicity point : ENNReal) ≤
            F.enncard := by
        change (denseShading.pointMultiplicity point : ENNReal) ≤
          (F.card : ENNReal)
        exact_mod_cast htotal
      have hdenseTotal :
          densityPower * (denseShading.pointMultiplicity point : ENNReal) ≤
            (m : ENNReal) := by
        calc
          densityPower * (denseShading.pointMultiplicity point : ENNReal)
              ≤ densityPower * F.enncard :=
                mul_le_mul_left' htotalENN densityPower
          _ ≤ (m : ENNReal) := hdensity
      have hselectedLower :
          (m : ENNReal) ≤
            2 * (selected.pointMultiplicity point : ENNReal) := by
        exact_mod_cast (hmultiplicity point hpoint).le
      exact hdenseTotal.trans hselectedLower
    · have hzero : denseShading.pointMultiplicity point = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        exact Finset.filter_eq_empty_iff.mpr (by
          intro index _ hindex
          exact hpoint ⟨index, hindex⟩)
      simp [hzero]
  have hmono :
      (∫⁻ point, densityPower *
          (denseShading.pointMultiplicity point : ENNReal) ∂volume) ≤
        ∫⁻ point, 2 *
          (selected.pointMultiplicity point : ENNReal) ∂volume :=
    MeasureTheory.lintegral_mono hpointwise
  have hdenseMeasurable : Measurable fun point : Point3 =>
      (denseShading.pointMultiplicity point : ENNReal) :=
    (measurable_of_countable fun n : ℕ => (n : ENNReal)).comp
      (measurable_pointMultiplicity denseShading)
  have hselectedMeasurable : Measurable fun point : Point3 =>
      (selected.pointMultiplicity point : ENNReal) :=
    (measurable_of_countable fun n : ℕ => (n : ENNReal)).comp
      (measurable_pointMultiplicity selected)
  rw [MeasureTheory.lintegral_const_mul _ hdenseMeasurable,
    MeasureTheory.lintegral_const_mul _ hselectedMeasurable,
    lintegral_pointMultiplicity denseShading,
    lintegral_pointMultiplicity selected] at hmono
  have hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second := by
    intro first second hcell
    exact congrArg
      (fun index : Fin F.card =>
        orthogonalNormal (F.tube index).direction)
      (hcenterCell first second hcell)
  exact ⟨center, selected, planeMap, hcenterMeasurable,
    hselectedSub, hselectedCubical, hcluster, hcenterCell,
    hmultiplicity, hplaneCell, hmono⟩

end Kakeya.Assouad.PureWZ2

end

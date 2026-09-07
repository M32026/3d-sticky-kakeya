import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Global multiplicity from coarse and full-fiber multiplicities

The final fine point multiplicity is the sum of the multiplicities in the
unique geometric parent fibers.  Point compatibility restricts that sum to
the coarse parents whose shadings contain the point.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/--
The finite-counting form of the paper identity
`mu ≤ mu_coarse * mu_fine`.
-/
theorem WZ1PaperTubeCover.pointMultiplicity_le_coarseMultiplicity_mul_fiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (pointCompatibility :
      ∀ source point,
        point ∈ fineShading.carrier source →
          point ∈
            coarseShading.carrier (cover.parent source))
    {fiberCap : ENNReal}
    (fiberMultiplicity :
      ∀ parent point,
        (cover.fiberPointMultiplicity
            fineShading parent point : ENNReal) ≤
          fiberCap) :
    ∀ point,
      (fineShading.pointMultiplicity point : ENNReal) ≤
        (coarseShading.pointMultiplicity point : ENNReal) *
          fiberCap := by
  intro point
  let fineAtPoint : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      point ∈ fineShading.carrier source
  let coarseAtPoint : Finset (Fin coarse.card) :=
    Finset.univ.filter fun parent =>
      point ∈ coarseShading.carrier parent
  have hmaps :
      Set.MapsTo cover.parent
        (fineAtPoint : Set (Fin fine.card))
        (coarseAtPoint : Set (Fin coarse.card)) := by
    intro source hsource
    have hpoint :
        point ∈ fineShading.carrier source :=
      (Finset.mem_filter.mp hsource).2
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, pointCompatibility source point hpoint⟩
  have hfiberCard :
      ∀ parent,
        (fineAtPoint.filter fun source =>
            cover.parent source = parent).card =
          cover.fiberPointMultiplicity
            fineShading parent point := by
    intro parent
    congr 1
    ext source
    constructor
    · intro hsource
      have houter := Finset.mem_filter.mp hsource
      have hpoint :
          point ∈ fineShading.carrier source :=
        (Finset.mem_filter.mp houter.1).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, hpoint⟩
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, houter.2⟩
    · intro hsource
      have houter := Finset.mem_filter.mp hsource
      have hparent :
          cover.parent source = parent :=
        (Finset.mem_filter.mp houter.1).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, hparent⟩
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, houter.2⟩
  have hcard :
      fineAtPoint.card =
        ∑ parent ∈ coarseAtPoint,
          cover.fiberPointMultiplicity
            fineShading parent point := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro parent _
    exact hfiberCard parent
  have hdecomposition :
      (fineShading.pointMultiplicity point : ENNReal) =
        ∑ parent ∈ coarseAtPoint,
          (cover.fiberPointMultiplicity
            fineShading parent point : ENNReal) := by
    change (fineAtPoint.card : ENNReal) = _
    exact_mod_cast hcard
  have hsum :
      ∑ parent ∈ coarseAtPoint,
          (cover.fiberPointMultiplicity
            fineShading parent point : ENNReal) ≤
        (coarseAtPoint.card : ENNReal) * fiberCap := by
    calc
      ∑ parent ∈ coarseAtPoint,
          (cover.fiberPointMultiplicity
            fineShading parent point : ENNReal) ≤
          ∑ _parent ∈ coarseAtPoint, fiberCap := by
            exact Finset.sum_le_sum fun parent _ =>
              fiberMultiplicity parent point
      _ = (coarseAtPoint.card : ENNReal) * fiberCap := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hcoarse :
      (coarseAtPoint.card : ENNReal) =
        (coarseShading.pointMultiplicity point : ENNReal) := by
    rfl
  rw [hdecomposition, ← hcoarse]
  exact hsum

/--
The finite-counting form of the paper identity
`mu ≤ mu_coarse * mu_fine`, with uniform caps on both factors.
-/
theorem WZ1PaperTubeCover.pointMultiplicity_le_coarse_mul_fiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (pointCompatibility :
      ∀ source point,
        point ∈ fineShading.carrier source →
          point ∈
            coarseShading.carrier (cover.parent source))
    {coarseCap fiberCap : ENNReal}
    (coarseMultiplicity :
      ∀ point,
        (coarseShading.pointMultiplicity point : ENNReal) ≤
          coarseCap)
    (fiberMultiplicity :
      ∀ parent point,
        (cover.fiberPointMultiplicity
            fineShading parent point : ENNReal) ≤
          fiberCap) :
    ∀ point,
      (fineShading.pointMultiplicity point : ENNReal) ≤
        coarseCap * fiberCap := by
  intro point
  exact
    (cover.pointMultiplicity_le_coarseMultiplicity_mul_fiber
      fineShading coarseShading pointCompatibility
      fiberMultiplicity point).trans (by
        gcongr
        exact coarseMultiplicity point)

/--
Integrating the fiber multiplicity cap gives the aggregate paper inequality
`fine mass ≤ fiberCap * coarse mass`.
-/
theorem WZ1PaperTubeCover.fine_mass_le_fiberCap_mul_coarse_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (pointCompatibility :
      ∀ source point,
        point ∈ fineShading.carrier source →
          point ∈
            coarseShading.carrier (cover.parent source))
    {fiberCap : ENNReal}
    (fiberMultiplicity :
      ∀ parent point,
        (cover.fiberPointMultiplicity
            fineShading parent point : ENNReal) ≤
          fiberCap) :
    fineShading.mass ≤ fiberCap * coarseShading.mass := by
  have hPointwise :
      ∀ point,
        (fineShading.pointMultiplicity point : ENNReal) ≤
          fiberCap *
            (coarseShading.pointMultiplicity point : ENNReal) := by
    intro point
    simpa [mul_comm] using
      cover.pointMultiplicity_le_coarseMultiplicity_mul_fiber
        fineShading coarseShading pointCompatibility
        fiberMultiplicity point
  have hMeasurable :
      Measurable fun point =>
        (coarseShading.pointMultiplicity point : ENNReal) := by
    have hEq :
        (fun point =>
          (coarseShading.pointMultiplicity point : ENNReal)) =
            fun point =>
              ∑ index : Fin coarse.card,
                (coarseShading.carrier index).indicator
                  (fun _ : Point3 => (1 : ENNReal)) point := by
      funext point
      exact coe_pointMultiplicity_eq_sum_indicator
        coarseShading point
    rw [hEq]
    exact Finset.measurable_sum _ fun index _ =>
      measurable_const.indicator
        (coarseShading.measurable_carrier index)
  calc
    fineShading.mass =
        ∫⁻ point, (fineShading.pointMultiplicity point : ENNReal) :=
      (lintegral_pointMultiplicity fineShading).symm
    _ ≤
        ∫⁻ point,
          fiberCap *
            (coarseShading.pointMultiplicity point : ENNReal) :=
      MeasureTheory.lintegral_mono hPointwise
    _ =
        fiberCap *
          ∫⁻ point,
            (coarseShading.pointMultiplicity point : ENNReal) := by
      rw [MeasureTheory.lintegral_const_mul fiberCap hMeasurable]
    _ = fiberCap * coarseShading.mass := by
      rw [lintegral_pointMultiplicity coarseShading]

end Kakeya.Assouad

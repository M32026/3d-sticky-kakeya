import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingLineDistance
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization

/-!
# Ordinary cleanup for Proposition 6.3 mild rescaling

After restricting to the popular box, the paper associates one target tube
to each isotropically rescaled coaxial line.  At the enlarged tube radius we
must remove the bounded number of ordinary centered-containment conflicts.
This is the finite cleanup implicit in the mild-rescaling lemma; it retains
the actual shaded mass weights and never replaces the family by a singleton.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

/-- The selected family with exactly the enumeration used by the weighted
ordinary-conflict cleanup. -/
def proposition63MildRescalingSelectedSubfamily
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin family.card)) :
    Kakeya.Streamlined.TubeSubfamily family where
  family := selectedTubeFamily family selected
  embedding := selected.equivFin.symm.toEmbedding.trans
    { toFun := Subtype.val, inj' := Subtype.val_injective }
  tube_eq := fun _ => rfl

/-- Output of the paper-line cleanup on the canonical isotropic image
family. -/
structure Proposition63MildRescalingCleanupData
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center)
    (targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)) where
  selectedIndices : Finset
    (Fin (proposition63MildRescalingFamily hscale raw).card)
  ordinary_distinct : WZ2PaperOrdinaryIsEssentiallyDistinct
    (proposition63MildRescalingSelectedSubfamily
      (proposition63MildRescalingFamily hscale raw) selectedIndices).family
  line_class : WZ1PaperIsLineClass
    (proposition63MildRescalingSelectedSubfamily
      (proposition63MildRescalingFamily hscale raw) selectedIndices).family
  cubical : WZ1PaperIsCubicalShading
    (restrictPaperShading
      (proposition63MildRescalingSelectedSubfamily
        (proposition63MildRescalingFamily hscale raw) selectedIndices)
      targetShading)
  mass_retention :
    targetShading.mass ≤
      (proposition63MildRescalingConflictDegree sourceDelta scale + 1 : ℕ) *
        (restrictPaperShading
          (proposition63MildRescalingSelectedSubfamily
            (proposition63MildRescalingFamily hscale raw) selectedIndices)
          targetShading).mass

/-- Apply the five-dimensional paper-line packing bound and weighted greedy
selection to the canonical isotropic image family. -/
theorem proposition63_mild_rescaling_cleanup
    {sourceDelta scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily)
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hcenterHeight : |center 2| ≤ 2)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center)
    (hrawLine : WZ1PaperIsLineClass raw.family)
    (targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw))
    (htargetCubical : WZ1PaperIsCubicalShading targetShading) :
    Nonempty (Proposition63MildRescalingCleanupData
      hscale raw targetShading) := by
  let targetFamily := proposition63MildRescalingFamily hscale raw
  let weight : Fin targetFamily.card → ENNReal := fun index =>
    MeasureTheory.volume (targetShading.carrier index)
  let degree := proposition63MildRescalingConflictDegree sourceDelta scale
  have hdegree : ∀ reference : Fin targetFamily.card,
      ((Finset.univ : Finset (Fin targetFamily.card)).filter
        (ordinaryContainmentConflict targetFamily reference)).card ≤ degree :=
    proposition63_mild_rescaling_conflict_degree hsourceDelta hscale
      hsourceLine hsourceDistinct hcenterHeight raw hrawLine
  rcases ordinary_distinct_weighted_cleanup targetFamily weight degree hdegree
      with ⟨selected, hdistinct, hweight⟩
  let selectedSubfamily : Kakeya.Streamlined.TubeSubfamily targetFamily :=
    proposition63MildRescalingSelectedSubfamily targetFamily selected
  have hline : WZ1PaperIsLineClass selectedSubfamily.family := by
    intro index
    rw [selectedSubfamily.tube_eq]
    exact proposition63MildRescalingFamily_lineClass hscale raw hrawLine _
  have hcubical : WZ1PaperIsCubicalShading
      (restrictPaperShading selectedSubfamily targetShading) :=
    restrictPaperShading_cubical selectedSubfamily htargetCubical
  have hmass : targetShading.mass ≤ (degree + 1 : ENNReal) *
      (restrictPaperShading selectedSubfamily targetShading).mass := by
    change (∑ index : Fin targetFamily.card,
        MeasureTheory.volume (targetShading.carrier index)) ≤
      (degree + 1 : ENNReal) *
        ∑ index : Fin selected.card,
          MeasureTheory.volume
            (targetShading.carrier (selected.equivFin.symm index).1)
    have hselectedSum :
        (∑ index : Fin selected.card,
          MeasureTheory.volume
            (targetShading.carrier (selected.equivFin.symm index).1)) =
        ∑ index ∈ selected,
          MeasureTheory.volume (targetShading.carrier index) := by
      calc
        (∑ index : Fin selected.card,
            MeasureTheory.volume
              (targetShading.carrier (selected.equivFin.symm index).1)) =
            ∑ index : selected,
              MeasureTheory.volume (targetShading.carrier index.1) := by
          exact Equiv.sum_comp (M := ENNReal) selected.equivFin.symm
            (fun index : selected =>
              MeasureTheory.volume (targetShading.carrier index.1))
        _ = ∑ index ∈ selected,
              MeasureTheory.volume (targetShading.carrier index) := by
          simpa using Finset.sum_attach selected
            (fun index => MeasureTheory.volume (targetShading.carrier index))
    rw [hselectedSum]
    simpa [weight] using hweight
  exact ⟨{
    selectedIndices := selected
    ordinary_distinct := hdistinct
    line_class := by simpa [selectedSubfamily, targetFamily] using hline
    cubical := by simpa [selectedSubfamily, targetFamily] using hcubical
    mass_retention := by simpa [degree] using hmass
  }⟩

end Kakeya.Assouad.PureWZ2

end

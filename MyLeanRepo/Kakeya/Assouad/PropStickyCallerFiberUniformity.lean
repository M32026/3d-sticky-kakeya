import MyLeanRepo.Kakeya.Assouad.PropStickyCallerNestedTransitivity
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedCover

/-! # Uniform strict fibers inside one caller parent -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem parent_eq_of_scale_cast
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceScale targetScale :
      Kakeya.Streamlined.AdmissibleScale delta}
    {C : ENNReal}
    (hscale : sourceScale = targetScale)
    (data : WZ2PaperScaleCoverData family sourceScale C)
    {first second : Fin family.card}
    (hparent :
      data.cover.parent first = data.cover.parent second) :
    (hscale ▸ data).cover.parent first =
      (hscale ▸ data).cover.parent second := by
  subst targetScale
  exact hparent

private theorem parent_eq_of_scale_data_heq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceScale targetScale :
      Kakeya.Streamlined.AdmissibleScale delta}
    {C : ENNReal}
    {sourceData :
      WZ2PaperScaleCoverData family sourceScale C}
    {targetData :
      WZ2PaperScaleCoverData family targetScale C}
    (hscale : sourceScale = targetScale)
    (hdata : HEq sourceData targetData)
    {first second : Fin family.card}
    (hparent :
      sourceData.cover.parent first =
        sourceData.cover.parent second) :
    targetData.cover.parent first =
      targetData.cover.parent second := by
  subst targetScale
  have hdataEq : sourceData = targetData :=
    eq_of_heq hdata
  rwa [← hdataEq]

theorem
    WZ2PaperCallerStrictPreparationData.callerFiber_strict_uniform
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (callerParent : Fin prepared.callerStrict.coarse.card)
    (coordinate : Fin prepared.strictScaleCount) :
    let callerFiber :=
      prepared.callerStrict.cover.fullFiberSubfamily callerParent
    let coordinateCover :=
      (prepared.strictScaleData coordinate).cover
    ∀ first second :
        Fin (coordinateCover.hitParentSubfamily callerFiber).family.card,
      wz2PaperFullFiberCount
          callerFiber.family
          (coordinateCover.hitParentSubfamily callerFiber).family
          first ≤
        prepared.structuralConstant *
          wz2PaperFullFiberCount
            callerFiber.family
            (coordinateCover.hitParentSubfamily callerFiber).family
            second := by
  dsimp only
  let callerFiber :=
    prepared.callerStrict.cover.fullFiberSubfamily callerParent
  let coordinateCover :=
    (prepared.strictScaleData coordinate).cover
  apply
    coordinateCover.restrictToHitParents_fullFiber_uniform_of_subfamily
      callerFiber prepared.structuralConstant
  intro first second hfirst hsecond
  by_cases hcoarse : coordinate.val ≤ prepared.callerLevel.val
  · have hsame :
        first = second := by
      rcases Finset.card_pos.mp hfirst with
        ⟨firstLocal, hfirstLocal⟩
      rcases Finset.card_pos.mp hsecond with
        ⟨secondLocal, hsecondLocal⟩
      have hfirstParent :
          coordinateCover.parent
              (callerFiber.embedding firstLocal) =
            first :=
        (Finset.mem_filter.mp hfirstLocal).2
      have hsecondParent :
          coordinateCover.parent
              (callerFiber.embedding secondLocal) =
            second :=
        (Finset.mem_filter.mp hsecondLocal).2
      have hcallerFirst :
          prepared.callerStrict.cover.parent
              (callerFiber.embedding firstLocal) =
            callerParent :=
        (prepared.callerStrict.cover.mem_fullFiber_iff_parent
          callerParent _).mp
          (prepared.callerStrict.cover.fullFiberSubfamily_mem
            callerParent firstLocal)
      have hcallerSecond :
          prepared.callerStrict.cover.parent
              (callerFiber.embedding secondLocal) =
            callerParent :=
        (prepared.callerStrict.cover.mem_fullFiber_iff_parent
          callerParent _).mp
          (prepared.callerStrict.cover.fullFiberSubfamily_mem
            callerParent secondLocal)
      have hcoordinateSame :=
        prepared.caller_parent_nested coordinate hcoarse
          (callerFiber.embedding firstLocal)
          (callerFiber.embedding secondLocal)
          (hcallerFirst.trans hcallerSecond.symm)
      rw [hfirstParent, hsecondParent] at hcoordinateSame
      exact hcoordinateSame
    subst second
    have hOne : 1 ≤ prepared.structuralConstant :=
      prepared.cwa_nearby.1
    exact le_mul_of_one_le_left (by simp) hOne
  · have hfine :
        prepared.callerLevel.val ≤ coordinate.val := by
      omega
    let count :
        Fin (prepared.strictScaleData coordinate).coarse.card →
          ENNReal :=
      fun value =>
        ((Finset.univ :
            Finset (Fin callerFiber.family.card)).filter
          fun sourceIndex =>
            coordinateCover.parent
                (callerFiber.embedding sourceIndex) =
              value).card
    have hcount_eq :
        ∀ value,
          ((Finset.univ :
              Finset (Fin callerFiber.family.card)).filter
            fun sourceIndex =>
              coordinateCover.parent
                  (callerFiber.embedding sourceIndex) =
                value).Nonempty →
            count value =
              wz2PaperFullFiberCount
                prepared.refinement.selected.family
                (prepared.strictScaleData coordinate).coarse
                value := by
      intro value hvalue
      have hlocalNonempty :
          ((Finset.univ :
              Finset (Fin callerFiber.family.card)).filter
            fun sourceIndex =>
              coordinateCover.parent
                  (callerFiber.embedding sourceIndex) =
                value).Nonempty := by
        exact hvalue
      rcases hlocalNonempty with
        ⟨reference, hreference⟩
      have hreferenceCoordinate :
          coordinateCover.parent
              (callerFiber.embedding reference) =
            value :=
        (Finset.mem_filter.mp hreference).2
      have hreferenceCaller :
          prepared.callerStrict.cover.parent
              (callerFiber.embedding reference) =
            callerParent :=
        (prepared.callerStrict.cover.mem_fullFiber_iff_parent
          callerParent _).mp
          (prepared.callerStrict.cover.fullFiberSubfamily_mem
            callerParent reference)
      let localFiber :=
        (Finset.univ :
            Finset (Fin callerFiber.family.card)).filter
          fun sourceIndex =>
            coordinateCover.parent
                (callerFiber.embedding sourceIndex) =
              value
      let ambientFiber :=
        wz2PaperFullFiberIndices
          prepared.refinement.selected.family
          (prepared.strictScaleData coordinate).coarse
          value
      have hcard :
          localFiber.card = ambientFiber.card := by
        apply Finset.card_bij
          (fun sourceIndex _ => callerFiber.embedding sourceIndex)
        · intro sourceIndex hlocal
          have hparent :
              coordinateCover.parent
                  (callerFiber.embedding sourceIndex) =
                value :=
            (Finset.mem_filter.mp hlocal).2
          exact
            (coordinateCover.mem_fullFiber_iff_parent
              value _).mpr hparent
        · intro firstLocal _ secondLocal _ heq
          exact callerFiber.embedding.injective heq
        · intro ambient hambient
          have hambientCoordinate :
              coordinateCover.parent ambient = value :=
            (coordinateCover.mem_fullFiber_iff_parent
              value ambient).mp hambient
          have hsameCoordinate :
              coordinateCover.parent ambient =
                coordinateCover.parent
                  (callerFiber.embedding reference) := by
            rw [hambientCoordinate, hreferenceCoordinate]
          have hsameCaller :=
            prepared.parent_nested_of_le
              prepared.callerLevel coordinate hfine
              ambient (callerFiber.embedding reference)
              hsameCoordinate
          have hsameCaller' :
              prepared.callerStrict.cover.parent ambient =
                prepared.callerStrict.cover.parent
                  (callerFiber.embedding reference) := by
            exact
              parent_eq_of_scale_data_heq
                prepared.callerScale_eq
                prepared.callerScaleData_eq hsameCaller
          rw [hreferenceCaller] at hsameCaller'
          have hambientCaller :
              ambient ∈
                wz2PaperFullFiberIndices
                  prepared.refinement.selected.family
                  prepared.callerStrict.coarse callerParent :=
            (prepared.callerStrict.cover.mem_fullFiber_iff_parent
              callerParent ambient).mpr hsameCaller'
          let localIndex : Fin callerFiber.family.card :=
            ((wz2PaperFullFiberIndices
              prepared.refinement.selected.family
              prepared.callerStrict.coarse callerParent)
              |>.orderIsoOfFin rfl).symm
                ⟨ambient, hambientCaller⟩
          have hlocalAmbient :
              callerFiber.embedding localIndex = ambient := by
            exact congrArg Subtype.val
              (((wz2PaperFullFiberIndices
                prepared.refinement.selected.family
                prepared.callerStrict.coarse callerParent)
                |>.orderIsoOfFin rfl).apply_symm_apply
                  ⟨ambient, hambientCaller⟩)
          refine ⟨localIndex, ?_, hlocalAmbient⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hlocalAmbient]
          exact hambientCoordinate
      change
        (localFiber.card : ENNReal) =
          (ambientFiber.card : ENNReal)
      exact congrArg (fun value : ℕ => (value : ENNReal)) hcard
    have hfirstNonempty :
        ((Finset.univ :
            Finset (Fin callerFiber.family.card)).filter
          fun sourceIndex =>
            coordinateCover.parent
                (callerFiber.embedding sourceIndex) =
              first).Nonempty :=
      Finset.card_pos.mp hfirst
    have hsecondNonempty :
        ((Finset.univ :
            Finset (Fin callerFiber.family.card)).filter
          fun sourceIndex =>
            coordinateCover.parent
                (callerFiber.embedding sourceIndex) =
              second).Nonempty :=
      Finset.card_pos.mp hsecond
    change count first ≤
      prepared.structuralConstant * count second
    rw [hcount_eq first hfirstNonempty,
      hcount_eq second hsecondNonempty]
    exact
      (prepared.strictScaleData coordinate).full_fiber_uniform
        first second

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.Localization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ReanchoredConflictDegree

/-!
# Localized paper-distinct reanchoring

This module composes the first three geometric steps of the corrected Node 9
route:

1. choose one fixed spatial cell carrying a controlled fraction of shaded
   mass;
2. discard exactly the zero-mass cell pieces and coaxially reanchor the
   surviving tubes at the common cell center;
3. apply the bounded-conflict weighted selection to obtain a
   paper-essentially-distinct reanchored family.

The output records exact source-index, direction, axial-translation and
subshading provenance.  No parent assignment or assigned-fiber API occurs.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined
open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem tubeSubfamily_fromFinset_restrictShading_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family)
    (selected : Finset (Fin family.card)) :
    ((Kakeya.Streamlined.TubeSubfamily.fromFinset
      family selected).restrictShading shading).mass =
        ∑ index ∈ selected, volume (shading.carrier index) := by
  let equivalence : Fin selected.card ≃ selected :=
    (selected.orderIsoOfFin rfl).toEquiv
  calc
    ((Kakeya.Streamlined.TubeSubfamily.fromFinset
      family selected).restrictShading shading).mass =
        ∑ index : Fin selected.card,
          volume
            (shading.carrier
              (selected.orderEmbOfFin rfl index)) := rfl
    _ =
        ∑ index : selected,
          volume (shading.carrier index.1) := by
      exact
        Fintype.sum_equiv equivalence
          (fun index : Fin selected.card =>
            volume
              (shading.carrier
                (selected.orderEmbOfFin rfl index)))
          (fun index : selected =>
            volume (shading.carrier index.1))
          (fun _ => rfl)
    _ =
        ∑ index ∈ selected,
          volume (shading.carrier index) := by
      exact
        Finset.sum_coe_sort selected
          (fun index => volume (shading.carrier index))

private theorem sum_orderEmbedding_eq_sum_finset
    {n : ℕ}
    (selected : Finset (Fin n))
    (weight : Fin n → ENNReal) :
    (∑ index : Fin selected.card,
      weight (selected.orderEmbOfFin rfl index)) =
        ∑ index ∈ selected, weight index := by
  let equivalence : Fin selected.card ≃ selected :=
    (selected.orderIsoOfFin rfl).toEquiv
  calc
    (∑ index : Fin selected.card,
      weight (selected.orderEmbOfFin rfl index)) =
        ∑ index : selected, weight index.1 := by
      exact
        Fintype.sum_equiv equivalence
          (fun index : Fin selected.card =>
            weight (selected.orderEmbOfFin rfl index))
          (fun index : selected => weight index.1)
          (fun _ => rfl)
    _ = ∑ index ∈ selected, weight index := by
      exact Finset.sum_coe_sort selected weight

/--
One mass-retaining, paper-distinct reanchored refinement obtained from fixed
cell localization.
-/
structure PureWZ2LocalizedDistinctReanchoringData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : Kakeya.Streamlined.TubeShading source) where
  cellCount : ℕ
  cellCount_pos : 0 < cellCount
  distinctnessLoss : ℕ
  distinctnessLoss_pos : 0 < distinctnessLoss
  distinctnessLoss_le :
    distinctnessLoss ≤ pureWZ2ReanchoredPaperConflictLossBound
  center : Point3
  radius : ℝ
  radius_pos : 0 < radius
  family : Kakeya.Streamlined.TubeFamily delta
  family_nonempty : family.Nonempty
  sourceIndex : Fin family.card ↪ Fin source.card
  tube_eq_reanchored :
    ∀ index,
      family.tube index =
        pureWZ2ReanchoredTube center
          (source.tube (sourceIndex index))
  source_meets_ball :
    ∀ index,
      (sourceShading.carrier (sourceIndex index) ∩
        Metric.closedBall center radius).Nonempty
  axialShift : Fin family.card → ℝ
  direction_eq :
    ∀ index,
      (family.tube index).direction =
        (source.tube (sourceIndex index)).direction
  source_base_eq :
    ∀ index,
      (source.tube (sourceIndex index)).base =
        (family.tube index).base +
          axialShift index • (family.tube index).direction
  axialShift_bound :
    ∀ index, |axialShift index| ≤ 1
  shading : Kakeya.Streamlined.TubeShading family
  subshading :
    ∀ index,
      shading.carrier index ⊆
        sourceShading.carrier (sourceIndex index)
  paper_distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct family
  mass_retained :
    sourceShading.mass ≤
      (cellCount : ENNReal) *
        (distinctnessLoss : ENNReal) * shading.mass

/--
Fixed-cell localization followed by canonical coaxial reanchoring and
weighted paper-distinct selection.
-/
theorem pureWZ2_localized_distinct_reanchoring
    {delta R radius : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 200)
    (hR : 0 < R)
    (hradius : 0 < radius)
    (hsmall : delta + radius ≤ 1 / 2)
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceSupport :
      ∀ index,
        (source.tube index).carrier ⊆
          Metric.closedBall (0 : Point3) R)
    (sourceDistinct : source.IsEssentiallyDistinct)
    (sourceShading : Kakeya.Streamlined.TubeShading source)
    (sourceMassPos : 0 < sourceShading.mass)
    (sourceMassFinite : sourceShading.mass ≠ ⊤) :
    ∃ data :
        PureWZ2LocalizedDistinctReanchoringData sourceShading,
      data.cellCount =
        pureWZ2LocalizationCellCount R radius ∧
      data.radius = radius := by
  rcases
      pureWZ2_fixed_cell_localization
        hR hradius sourceSupport sourceShading
        sourceMassPos sourceMassFinite with
    ⟨localization⟩
  let cellWeight : Fin source.card → ENNReal := fun index =>
    volume (sourceShading.carrier index ∩ localization.cell)
  let positiveIndices : Finset (Fin source.card) :=
    Finset.univ.filter fun index => cellWeight index ≠ 0
  let positiveSource :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      source positiveIndices
  have hpositiveCell :
      ∀ index : Fin positiveSource.family.card,
        (sourceShading.carrier
          (positiveSource.embedding index) ∩ localization.cell).Nonempty := by
    intro index
    have hmember :
        positiveSource.embedding index ∈ positiveIndices := by
      exact Finset.orderEmbOfFin_mem positiveIndices rfl index
    have hvolume :
        cellWeight (positiveSource.embedding index) ≠ 0 :=
      (Finset.mem_filter.mp hmember).2
    apply Set.nonempty_iff_ne_empty.mpr
    intro hempty
    have hzero :
        cellWeight (positiveSource.embedding index) = 0 := by
      dsimp only [cellWeight]
      rw [hempty, measure_empty]
    exact hvolume hzero
  have hpositiveBall :
      ∀ index : Fin positiveSource.family.card,
        (sourceShading.carrier
          (positiveSource.embedding index) ∩
            Metric.closedBall localization.center radius).Nonempty := by
    intro index
    exact
      (hpositiveCell index).mono fun point hpoint =>
        ⟨hpoint.1, localization.cell_subset_ball hpoint.2⟩
  let reanchoring :=
    pureWZ2LocalizedReanchoring
      hdelta.le hradius.le hsmall
      sourceShading positiveSource localization.center hpositiveBall
  have hpositiveSum :
      (∑ index ∈ positiveIndices, cellWeight index) =
        ∑ index : Fin source.card, cellWeight index := by
    symm
    rw [Finset.sum_subset
      (show positiveIndices ⊆ Finset.univ from by simp)]
    intro index _ hnot
    have hzero :
        cellWeight index = 0 := by
      have :
          ¬cellWeight index ≠ 0 := by
        simpa [positiveIndices] using hnot
      exact not_ne_iff.mp this
    exact hzero
  have hlocalizedAsSum :
      localization.localizedMass =
        ∑ index : Fin source.card, cellWeight index := by
    exact localization.localizedMass_eq
  have hballSum :
      (∑ index : Fin positiveSource.family.card,
        volume
          (sourceShading.carrier
              (positiveSource.embedding index) ∩
            Metric.closedBall localization.center radius)) =
        ∑ index ∈ positiveIndices,
          volume
            (sourceShading.carrier index ∩
              Metric.closedBall localization.center radius) := by
    change
      (∑ index : Fin positiveIndices.card,
        volume
          (sourceShading.carrier
              (positiveIndices.orderEmbOfFin rfl index) ∩
            Metric.closedBall localization.center radius)) =
        _
    exact
      sum_orderEmbedding_eq_sum_finset
        positiveIndices
        (fun index =>
          volume
            (sourceShading.carrier index ∩
              Metric.closedBall localization.center radius))
  have hlocalizedLeReanchored :
      localization.localizedMass ≤ reanchoring.shading.mass := by
    calc
      localization.localizedMass =
          ∑ index ∈ positiveIndices, cellWeight index := by
        rw [hlocalizedAsSum, hpositiveSum]
      _ ≤
          ∑ index ∈ positiveIndices,
            volume
              (sourceShading.carrier index ∩
                Metric.closedBall localization.center radius) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact measure_mono fun point hpoint =>
          ⟨hpoint.1, localization.cell_subset_ball hpoint.2⟩
      _ =
          reanchoring.shading.mass := by
        rw [reanchoring.mass_eq]
        exact hballSum.symm
  let weight : Fin reanchoring.family.card → ENNReal := fun index =>
    volume (reanchoring.shading.carrier index)
  rcases
      pureWZ2_select_reanchored_paper_distinct_weighted
        hdelta hdeltaSmall
        reanchoring.sourceIndex reanchoring.axialShift
        reanchoring.direction_eq reanchoring.source_base_eq
        reanchoring.axialShift_bound sourceDistinct weight with
    ⟨loss, hloss, hlossBound,
      selected, hpaperDistinct, hselectedMass⟩
  let finalSubfamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      reanchoring.family selected
  let finalShading := finalSubfamily.restrictShading reanchoring.shading
  have hfinalMass :
      finalShading.mass =
        ∑ index ∈ selected, weight index := by
    exact
      tubeSubfamily_fromFinset_restrictShading_mass
        reanchoring.shading selected
  have hreanchoredMass :
      reanchoring.shading.mass =
        ∑ index : Fin reanchoring.family.card, weight index := by
    rfl
  have hmassChain :
      sourceShading.mass ≤
        (localization.cellCount : ENNReal) *
          (loss : ENNReal) * finalShading.mass := by
    calc
      sourceShading.mass ≤
          (localization.cellCount : ENNReal) *
            localization.localizedMass :=
        localization.mass_retained
      _ ≤
          (localization.cellCount : ENNReal) *
            reanchoring.shading.mass := by
        gcongr
      _ ≤
          (localization.cellCount : ENNReal) *
            ((loss : ENNReal) * finalShading.mass) := by
        rw [hreanchoredMass, hfinalMass]
        gcongr
      _ =
          (localization.cellCount : ENNReal) *
            (loss : ENNReal) * finalShading.mass := by ring
  have hfinalMassPos : 0 < finalShading.mass := by
    by_contra hnot
    have hzero : finalShading.mass = 0 := by
      simpa [not_lt] using hnot
    rw [hzero] at hmassChain
    simp only [mul_zero] at hmassChain
    exact (not_lt_of_ge hmassChain) sourceMassPos
  have hfinalNonempty : finalSubfamily.family.Nonempty := by
    by_contra hnot
    have hcard : finalSubfamily.family.card = 0 := by
      simpa [Kakeya.Streamlined.TubeFamily.Nonempty,
        not_lt] using hnot
    have hselectedCard : selected.card = 0 := by
      exact hcard
    have hselectedEmpty : selected = ∅ :=
      Finset.card_eq_zero.mp hselectedCard
    have hmassZero : finalShading.mass = 0 := by
      rw [hfinalMass, hselectedEmpty]
      simp
    rw [hmassZero] at hfinalMassPos
    exact (lt_irrefl 0 hfinalMassPos)
  let finalSourceIndex :
      Fin finalSubfamily.family.card ↪ Fin source.card :=
    finalSubfamily.embedding.trans reanchoring.sourceIndex
  refine
    ⟨{
      cellCount := localization.cellCount
      cellCount_pos := localization.cellCount_pos
      distinctnessLoss := loss
      distinctnessLoss_pos := hloss
      distinctnessLoss_le := hlossBound
      center := localization.center
      radius := radius
      radius_pos := hradius
      family := finalSubfamily.family
      family_nonempty := hfinalNonempty
      sourceIndex := finalSourceIndex
      tube_eq_reanchored := by
        intro index
        rw [finalSubfamily.tube_eq]
        rfl
      source_meets_ball := by
        intro index
        change
          (sourceShading.carrier
                (reanchoring.sourceIndex
                  (finalSubfamily.embedding index)) ∩
              Metric.closedBall localization.center radius).Nonempty
        exact
          hpositiveBall (finalSubfamily.embedding index)
      axialShift := fun index =>
        reanchoring.axialShift (finalSubfamily.embedding index)
      direction_eq := by
        intro index
        rw [finalSubfamily.tube_eq]
        exact reanchoring.direction_eq (finalSubfamily.embedding index)
      source_base_eq := by
        intro index
        change
          (source.tube
            (reanchoring.sourceIndex
              (finalSubfamily.embedding index))).base =
            (finalSubfamily.family.tube index).base +
              reanchoring.axialShift
                  (finalSubfamily.embedding index) •
                (finalSubfamily.family.tube index).direction
        rw [finalSubfamily.tube_eq]
        exact
          reanchoring.source_base_eq
            (finalSubfamily.embedding index)
      axialShift_bound := fun index =>
        reanchoring.axialShift_bound
          (finalSubfamily.embedding index)
      shading := finalShading
      subshading := by
        intro index point hpoint
        exact
          reanchoring.subshading
            (finalSubfamily.embedding index) hpoint
      paper_distinct := hpaperDistinct
      mass_retained := hmassChain
    }, localization.cellCount_eq, rfl⟩

end Kakeya.Assouad

end

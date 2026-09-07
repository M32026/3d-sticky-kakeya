import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberPureNearby
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ScaleChoice

/-!
# Same-scale extremal localization to one complete actual fiber

Select an actual Definition 2.12 witness at a small requested scale, then use
aggregate density to choose one complete strict parent fiber with the same
density exponent.  The complete-fiber nearby theorem restores literal pure
CWA at every scale on that whole fiber.  Since the restricted shading union is
contained in the source union, this gives a new same-`delta` extremizer at a
weaker loss.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Provenance retained by a complete-fiber same-scale extremizer. -/
structure PureWZ2CompleteFiberLocalizationData
    {sigma sourceLoss inputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta) where
  requested : WZ2PaperRequestedScale delta
  nearby :
    WZ2PaperPureNearbyScaleCoverData
      source.family requested
      (Kakeya.realRpowENN delta (-sourceLoss))
  rho_upper :
    nearby.rho < Real.rpow delta sourceLoss
  parent : Fin nearby.scaleData.coarse.card
  sourceEmbedding :
    Fin localized.family.card ↪ Fin source.family.card
  source_tube_eq :
    ∀ index,
      localized.family.tube index =
        source.family.tube (sourceEmbedding index)
  shading_eq :
    ∀ index,
      localized.shading.carrier index =
        source.shading.carrier (sourceEmbedding index)
  parent_containment :
    ∀ index,
      (localized.family.tube index).carrier ⊆
        (nearby.scaleData.coarse.tube parent).carrier

/-- The restricted complete-fiber shading union lies in the source union. -/
theorem pureWZ2_completeFiber_restrictShading_union_subset
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (shading : Kakeya.Streamlined.TubeShading fine) :
    ((wz2PaperPureFullFiberSubfamily
      fine coarse parent).restrictShading shading).union ⊆
      shading.union := by
  rintro point ⟨index, pointMem⟩
  exact
    ⟨(wz2PaperPureFullFiberSubfamily
      fine coarse parent).embedding index, pointMem⟩

/--
One fixed-source complete-fiber localization, with all scalar absorptions
stated explicitly.
-/
theorem pureWZ2_exists_completeFiber_extremal
    {sigma sourceLoss inputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (sourceLossPos : 0 < sourceLoss)
    (sourceLossLeInputLoss : sourceLoss ≤ inputLoss)
    (twoSourceLossLeOne : 2 * sourceLoss ≤ 1)
    (deltaLtOne : delta < 1)
    (outputOne :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-inputLoss))
    (fourAmbient :
      (4 : ENNReal) *
          Kakeya.realRpowENN delta (-sourceLoss) <
        Kakeya.realRpowENN delta (-inputLoss))
    (coarserAbsorption :
      ∀ actual coarser : ℝ,
        Real.rpow delta (2 * sourceLoss) ≤ actual →
        actual ≤ coarser →
        coarser ≤ 1 →
          ENNReal.ofReal (81 * (coarser / actual) ^ 2) *
              Kakeya.realRpowENN delta (-sourceLoss) ≤
            Kakeya.realRpowENN delta (-inputLoss)) :
    ∃ localized :
        PureWZ2ExtremalConfiguration sigma inputLoss delta,
      Nonempty
        (PureWZ2CompleteFiberLocalizationData source localized) := by
  rcases
      pure_wz2_scale_and_nearby_generalized
        source.extremal.delta_pos source.extremal.delta_le_one
        sourceLossPos
        (show sourceLoss ≤ 2 * sourceLoss by linarith)
        twoSourceLossLeOne rfl
        source.extremal.cwa_nearby_scales
    with
    ⟨requested, nearby, rhoUpper, rhoLeOne,
      _targetLeOne, scaleLower, rhoPos⟩
  rcases
      pureWZ2_exists_completeFiber_density_parent
        nearby.scaleData.cover rhoPos.le
        source.extremal.nonempty source.shading
        (Kakeya.realRpowENN delta sourceLoss)
        source.extremal.dense
    with
    ⟨parent, fiberDense⟩
  let fiber :=
    wz2PaperPureFullFiberSubfamily
      source.family nearby.scaleData.coarse parent
  let fiberShading := fiber.restrictShading source.shading
  have fiberNonempty : fiber.family.Nonempty := by
    exact
      nearby.scaleData.cover.fullFiber_nonempty_of_uniform
        source.extremal.nonempty
        nearby.scaleData.full_fiber_uniform parent
      |>.card_pos
  have pureCWA :
      WZ2PaperPureCWAAtNearbyScales
        (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
          nearby.scaleData.cover
          ({parent} : Finset (Fin nearby.scaleData.coarse.card))
          (Finset.singleton_nonempty parent)).selectedFine.family
        (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply
      pureWZ2_completeFiber_pureNearby
        source.extremal.cwa_nearby_scales
        source.extremal.nonempty nearby.scaleData parent
        (requested.2.1.trans nearby.requested_le)
        rhoLeOne outputOne
        (by simp [Kakeya.realRpowENN])
        fourAmbient
        (pure_wz2_rpowENN_antitone
          source.extremal.delta_pos source.extremal.delta_le_one
          (by linarith))
    intro coarser actualLe coarserLe
    exact
      coarserAbsorption nearby.rho coarser
        scaleLower actualLe coarserLe
  have indicesEq :
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        nearby.scaleData.cover
        ({parent} : Finset (Fin nearby.scaleData.coarse.card))
        (Finset.singleton_nonempty parent)).selectedFineIndices =
          wz2PaperOrdinaryFullFiberIndices
            source.family nearby.scaleData.coarse parent :=
    pureWZ2_singletonComplete_selectedFineIndices
      nearby.scaleData.cover rhoPos.le parent
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      nearby.scaleData.cover
      ({parent} : Finset (Fin nearby.scaleData.coarse.card))
      (Finset.singleton_nonempty parent)
  let localizedFamily := complete.selectedFine.family
  let localizedShading :=
    complete.selectedFine.toTubeSubfamily.restrictShading source.shading
  have localizedDense :
      localizedShading.IsLambdaDense
        (Kakeya.realRpowENN delta inputLoss) := by
    have densityLe :
        Kakeya.realRpowENN delta inputLoss ≤
          Kakeya.realRpowENN delta sourceLoss :=
      pure_wz2_rpowENN_antitone
        source.extremal.delta_pos source.extremal.delta_le_one
        sourceLossLeInputLoss
    rw [Kakeya.Streamlined.Shading.IsLambdaDense]
    calc
      Kakeya.realRpowENN delta inputLoss *
            localizedFamily.toBodyFamily.mass ≤
          Kakeya.realRpowENN delta sourceLoss *
            localizedFamily.toBodyFamily.mass := by
        gcongr
      _ ≤ localizedShading.mass := by
        change
          Kakeya.realRpowENN delta sourceLoss *
              complete.selectedFine.family.toBodyFamily.mass ≤
            (complete.selectedFine.toTubeSubfamily
              |>.restrictShading source.shading).mass
        have direct := fiberDense
        rw [tubeFamily_mass_eq_nominal] at direct ⊢
        change
          Kakeya.realRpowENN delta sourceLoss *
              ((complete.selectedFineIndices.card : ENNReal) *
                Kakeya.deltaTubeVolume delta) ≤
            ∑ index : Fin complete.selectedFineIndices.card,
              volume
                (source.shading.carrier
                  (complete.selectedFineIndices.orderEmbOfFin rfl index))
        change
          Kakeya.realRpowENN delta sourceLoss *
              (((wz2PaperOrdinaryFullFiberIndices
                source.family nearby.scaleData.coarse parent).card :
                  ENNReal) *
                Kakeya.deltaTubeVolume delta) ≤
            ∑ index :
                Fin (wz2PaperOrdinaryFullFiberIndices
                  source.family nearby.scaleData.coarse parent).card,
              volume
                (source.shading.carrier
                  ((wz2PaperOrdinaryFullFiberIndices
                    source.family nearby.scaleData.coarse parent)
                    |>.orderEmbOfFin rfl index))
          at direct
        rw [indicesEq]
        exact direct
  have localizedUnion :
      localizedShading.union ⊆ source.shading.union := by
    rintro point ⟨index, pointMem⟩
    exact ⟨complete.selectedFine.embedding index, pointMem⟩
  have localizedVolume :
      volume localizedShading.union ≤
        Kakeya.realRpowENN delta (sigma - inputLoss) := by
    calc
      volume localizedShading.union ≤ volume source.shading.union :=
        measure_mono localizedUnion
      _ ≤ Kakeya.realRpowENN delta (sigma - sourceLoss) :=
        source.extremal.volume_upper
      _ ≤ Kakeya.realRpowENN delta (sigma - inputLoss) :=
        pure_wz2_rpowENN_antitone
          source.extremal.delta_pos source.extremal.delta_le_one
          (by linarith)
  let localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta :=
    {
      family := localizedFamily
      shading := localizedShading
      extremal :=
        {
          delta_pos := source.extremal.delta_pos
          delta_le_one := source.extremal.delta_le_one
          nonempty := by
            change 0 < complete.selectedFineIndices.card
            rw [indicesEq]
            exact fiberNonempty
          cwa_nearby_scales := pureCWA
          dense := localizedDense
          volume_upper := localizedVolume
        }
    }
  exact
    ⟨localized,
      ⟨{
        requested := requested
        nearby := nearby
        rho_upper := by
          convert rhoUpper using 1 <;> ring
        parent := parent
        sourceEmbedding := complete.selectedFine.embedding
        source_tube_eq := complete.selectedFine.tube_eq
        shading_eq := fun _ => rfl
        parent_containment := fun index =>
          pureWZ2_singletonComplete_tube_subset_parent
            nearby.scaleData.cover rhoPos.le parent index
      }⟩⟩

end Kakeya.Assouad

end

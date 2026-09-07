import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredSelectedFullFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FullFiberRetentionParent
import MyLeanRepo.Kakeya.Assouad.PureWZ2.IndexedPerTubePruning
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ScaleChoice

/-!
# Canonical centered strict-fiber preparation

This is the literal Definition 2.12 frontend for the Node 1 Wolff floor.
It performs:

1. indexed per-tube shading pruning;
2. an actual nearby-scale Definition 2.12 cover;
3. selection of one complete strict full fiber retaining the global index
   fraction;
4. centered ordinary rescaling of exactly those selected strict-fiber
   members.

No assigned parent or assigned-fiber API occurs.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Canonical output of literal nearby-scale strict-fiber preparation. -/
structure PureWZ2CenteredStrictFiberData
    {delta inputEta pruneEta c : ℝ}
    {C : ENNReal}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : Kakeya.Streamlined.TubeShading family) where
  requested : WZ2PaperRequestedScale delta
  nearby :
    WZ2PaperPureNearbyScaleCoverData family requested C
  rho_upper :
    nearby.rho < Real.rpow delta (c - inputEta)
  rho_le_one : nearby.rho ≤ 1
  target_scale_le_one : delta / nearby.rho ≤ 1
  scale_lower : Real.rpow delta c ≤ nearby.rho
  selected : Finset (Fin family.card)
  selected_nonempty : selected.Nonempty
  selected_global_cardinality :
    Kakeya.realRpowENN delta pruneEta *
        family.enncard ≤
      (selected.card : ENNReal)
  selected_source_mass :
    shading.mass ≤
      2 *
        (selectedTubeShading shading selected).mass
  selected_source_per_tube :
    ∀ source ∈ selected,
      Kakeya.realRpowENN delta pruneEta *
          (family.tube source).volume ≤
        MeasureTheory.volume (shading.carrier source)
  parent : Fin nearby.scaleData.coarse.card
  parent_retention :
    Kakeya.realRpowENN delta pruneEta *
        wz2PaperOrdinaryFullFiberCount
          family nearby.scaleData.coarse parent ≤
      ((selected.filter fun source =>
        nearby.scaleData.cover.parent source = parent).card :
        ENNReal)
  centered_nonempty :
    (wz2PaperCenteredSelectedFullFiberFamily
      family nearby.scaleData.coarse parent
      nearby.scaleData.rho_pos selected).Nonempty
  centered_ball :
    (wz2PaperCenteredSelectedFullFiberFamily
      family nearby.scaleData.coarse parent
      nearby.scaleData.rho_pos selected).IsInUnitBall
  centered_cwa :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperCenteredSelectedFullFiberFamily
        family nearby.scaleData.coarse parent
        nearby.scaleData.rho_pos selected).toBodyFamily
      ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
        ((4000000 : ENNReal) * C))

namespace PureWZ2CenteredStrictFiberData

/-- The canonical centered shading on prepared selected strict-fiber tubes. -/
def centeredShading
    {delta inputEta pruneEta c : ℝ}
    {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    (data :
      PureWZ2CenteredStrictFiberData
        (inputEta := inputEta) (pruneEta := pruneEta)
        (c := c) (C := C) family shading)
    (hrhoSmall : data.nearby.rho ≤ 1 / 4) :
    Kakeya.Streamlined.TubeShading
      (wz2PaperCenteredSelectedFullFiberFamily
        family data.nearby.scaleData.coarse data.parent
        data.nearby.scaleData.rho_pos data.selected) :=
  wz2PaperCenteredSelectedFullFiberShading
    family data.nearby.scaleData.coarse data.parent
    data.nearby.scaleData.delta_pos
    data.nearby.scaleData.rho_pos data.rho_le_one
    hrhoSmall
    ((div_le_one data.nearby.scaleData.rho_pos).mp
      data.target_scale_le_one)
    data.selected shading

/-- Prepared pointwise density after exact centered rescaling. -/
theorem centeredShading_perTube
    {delta inputEta pruneEta c : ℝ}
    {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    (data :
      PureWZ2CenteredStrictFiberData
        (inputEta := inputEta) (pruneEta := pruneEta)
        (c := c) (C := C) family shading)
    (hrhoSmall : data.nearby.rho ≤ 1 / 4) :
    ∀ target,
      pureWZ2CenteredDensityConstant
            delta data.nearby.rho
            (Kakeya.realRpowENN delta pruneEta) *
          ((wz2PaperCenteredSelectedFullFiberFamily
            family data.nearby.scaleData.coarse data.parent
            data.nearby.scaleData.rho_pos
            data.selected).tube target).volume ≤
        MeasureTheory.volume
          ((data.centeredShading hrhoSmall).carrier target) := by
  exact
    wz2PaperCenteredSelectedFullFiberShading_perTube
      family data.nearby.scaleData.coarse data.parent
      data.nearby.scaleData.delta_pos
      data.nearby.scaleData.rho_pos data.rho_le_one
      hrhoSmall
      ((div_le_one data.nearby.scaleData.rho_pos).mp
        data.target_scale_le_one)
      data.selected shading
      (Kakeya.realRpowENN delta pruneEta)
      data.selected_source_per_tube

/-- The prepared centered union is an affine image subshading of the source. -/
theorem centeredShading_union_subset
    {delta inputEta pruneEta c : ℝ}
    {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    (data :
      PureWZ2CenteredStrictFiberData
        (inputEta := inputEta) (pruneEta := pruneEta)
        (c := c) (C := C) family shading)
    (hrhoSmall : data.nearby.rho ≤ 1 / 4) :
    (data.centeredShading hrhoSmall).union ⊆
      wz2PaperCenteredLiteralRescalingAffineEquiv
          (data.nearby.scaleData.coarse.tube data.parent)
          data.nearby.scaleData.rho_pos ''
        shading.union :=
  wz2PaperCenteredSelectedFullFiberShading_union_subset
    family data.nearby.scaleData.coarse data.parent
    data.nearby.scaleData.delta_pos
    data.nearby.scaleData.rho_pos data.rho_le_one
    hrhoSmall
    ((div_le_one data.nearby.scaleData.rho_pos).mp
      data.target_scale_le_one)
    data.selected shading

end PureWZ2CenteredStrictFiberData

/-- Construct the canonical centered selected strict fiber. -/
theorem pure_wz2_centered_strict_fiber_preparation
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hfamilyNonempty : family.Nonempty)
    (shading : Kakeya.Streamlined.TubeShading family)
    {inputEta pruneEta c : ℝ}
    (hinputEta : 0 < inputEta)
    (hinputC : inputEta ≤ c)
    (hcOne : c ≤ 1)
    (hdense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta inputEta))
    (hprune :
      Kakeya.realRpowENN delta pruneEta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta inputEta)
    {C : ENNReal}
    (hC : C = Kakeya.realRpowENN delta (-inputEta))
    (hCWA : WZ2PaperPureCWAAtNearbyScales family C)
    (hrhoSmall :
      Real.rpow delta (c - inputEta) ≤ 1 / 4)
    (htargetSmall :
      Real.rpow delta (1 - c) ≤ 39 / 80) :
    Nonempty
      (PureWZ2CenteredStrictFiberData
        (inputEta := inputEta) (pruneEta := pruneEta)
        (c := c) (C := C) family shading) := by
  rcases
      pure_wz2_indexed_per_tube_pruning
        hdelta hdeltaOne hfamilyNonempty shading
        hdense hprune with
    ⟨selected, hselectedNonempty, hselectedCard,
      hselectedMass, hselectedPerTube⟩
  rcases
      pure_wz2_scale_and_nearby_generalized
        hdelta hdeltaOne hinputEta hinputC hcOne
        hC hCWA with
    ⟨requested, nearby, hrhoUpper, hrhoOne,
      htargetOne, hscaleLower, hrho⟩
  have hselectedCard' :
      Kakeya.realRpowENN delta pruneEta *
          family.enncard ≤
        (selected.card : ENNReal) := by
    simpa [selectedTubeFamily,
      Kakeya.Streamlined.TubeFamily.enncard] using
      hselectedCard
  rcases
      pure_wz2_exists_full_fiber_retention_parent
        nearby.scaleData.cover hrho.le hfamilyNonempty
        selected (Kakeya.realRpowENN delta pruneEta)
        hselectedCard' with
    ⟨parent, hparentRetention⟩
  have hrhoSmall' : nearby.rho ≤ 1 / 4 :=
    hrhoUpper.le.trans hrhoSmall
  have hdeltaRho : delta ≤ nearby.rho :=
    (div_le_one hrho).mp htargetOne
  have htargetSmall' : delta / nearby.rho ≤ 39 / 80 := by
    have hdivision :
        delta / nearby.rho ≤
          Real.rpow delta (1 - c) := by
      have hpowPositive : 0 < Real.rpow delta c :=
        Real.rpow_pos_of_pos hdelta c
      calc
        delta / nearby.rho ≤
            delta / Real.rpow delta c := by
          exact
            div_le_div_of_nonneg_left
              hdelta.le hpowPositive hscaleLower
        _ = Real.rpow delta (1 - c) := by
          calc
            delta / Real.rpow delta c =
                Real.rpow delta 1 /
                  Real.rpow delta c := by
              exact congrArg
                (fun value => value / Real.rpow delta c)
                (Real.rpow_one delta).symm
            _ = Real.rpow delta (1 - c) :=
              (Real.rpow_sub hdelta 1 c).symm
    exact hdivision.trans htargetSmall
  have hfullNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        family nearby.scaleData.coarse parent).Nonempty :=
    nearby.scaleData.cover.fullFiber_nonempty_of_uniform
      hfamilyNonempty nearby.scaleData.full_fiber_uniform parent
  have hweightPositive :
      0 < Kakeya.realRpowENN delta pruneEta :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta pruneEta)
  have hfullCountPositive :
      0 <
        wz2PaperOrdinaryFullFiberCount
          family nearby.scaleData.coarse parent := by
    rw [wz2PaperOrdinaryFullFiberCount]
    exact_mod_cast hfullNonempty.card_pos
  have hselectedParentPositive :
      0 <
        ((selected.filter fun source =>
          nearby.scaleData.cover.parent source = parent).card :
          ENNReal) :=
    (ENNReal.mul_pos hweightPositive.ne'
      hfullCountPositive.ne').trans_le hparentRetention
  have hcenteredNonempty :
      (wz2PaperCenteredSelectedFullFiberFamily
        family nearby.scaleData.coarse parent
        nearby.scaleData.rho_pos selected).Nonempty := by
    rw [Kakeya.Streamlined.TubeFamily.Nonempty,
      wz2PaperCenteredSelectedFullFiberFamily_card_eq_parent_filter
        family nearby.scaleData.coarse nearby.scaleData.cover
        parent nearby.scaleData.rho_pos selected]
    exact_mod_cast hselectedParentPositive
  have hcenteredBall :
      (wz2PaperCenteredSelectedFullFiberFamily
        family nearby.scaleData.coarse parent
        nearby.scaleData.rho_pos selected).IsInUnitBall :=
    wz2PaperCenteredSelectedFullFiberFamily_isInUnitBall
      family nearby.scaleData.coarse parent hdelta hrho
      hrhoSmall' hdeltaRho htargetSmall' selected
  have hcompleteCWA :
      WZ2PaperBodyConvexWolffBound
        (wz2PaperCenteredPublicFullFiberFamily
          family nearby.scaleData.coarse parent hrho).toBodyFamily
        ((4000000 : ENNReal) * C) :=
    wz2PaperCenteredPublicFullFiber_convexWolff
      parent hdelta hrho hrhoOne hrhoSmall' hdeltaRho
      (Classical.choice (nearby.scaleData.rescaledFiber parent))
  have hweightZero :
      Kakeya.realRpowENN delta pruneEta ≠ 0 :=
    hweightPositive.ne'
  have hweightTop :
      Kakeya.realRpowENN delta pruneEta ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hcenteredRetention :
      Kakeya.realRpowENN delta pruneEta *
          (wz2PaperCenteredPublicFullFiberFamily
            family nearby.scaleData.coarse parent hrho).enncard ≤
        (wz2PaperCenteredSelectedFullFiberFamily
          family nearby.scaleData.coarse parent hrho selected).enncard := by
    change
      Kakeya.realRpowENN delta pruneEta *
          ((wz2PaperOrdinaryFullFiberIndices
            family nearby.scaleData.coarse parent).card :
            ENNReal) ≤
        ((wz2PaperCenteredSelectedFullFiberFamily
          family nearby.scaleData.coarse parent hrho selected).card :
          ENNReal)
    rw [show
      ((wz2PaperOrdinaryFullFiberIndices
        family nearby.scaleData.coarse parent).card : ENNReal) =
        wz2PaperOrdinaryFullFiberCount
          family nearby.scaleData.coarse parent by
            rfl,
      wz2PaperCenteredSelectedFullFiberFamily_card_eq_parent_filter
        family nearby.scaleData.coarse nearby.scaleData.cover
        parent hrho selected]
    exact hparentRetention
  have hcenteredCWA :=
    wz2PaperBodyConvexWolffBound_selectedTubeFamily
      hcompleteCWA
      (wz2PaperCenteredSelectedFullFiberIndices
        family nearby.scaleData.coarse parent selected)
      hweightZero hweightTop hcenteredRetention
  exact
    ⟨{
      requested := requested
      nearby := nearby
      rho_upper := hrhoUpper
      rho_le_one := hrhoOne
      target_scale_le_one := htargetOne
      scale_lower := hscaleLower
      selected := selected
      selected_nonempty := hselectedNonempty
      selected_global_cardinality := hselectedCard'
      selected_source_mass := hselectedMass
      selected_source_per_tube := hselectedPerTube
      parent := parent
      parent_retention := hparentRetention
      centered_nonempty := hcenteredNonempty
      centered_ball := hcenteredBall
      centered_cwa := hcenteredCWA
    }⟩

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMetricCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMassLedger

/-!
# Proposition 6.2 quotient final refinement

This module packages the already constructed quotient metric core as a paper
refinement.  The final shading is exactly the restriction of the original
ambient shading along the composite embedding into the original fine family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62ProxyQuotientMetricCoreOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

/-- The final metric core as a direct subfamily of the ambient fine family. -/
noncomputable def finalSubfamily :
    Kakeya.Streamlined.TubeSubfamily fine :=
  metricCore.metric.mesh.complete.selectedFine.toTubeSubfamily.comp
    metricCore.restriction.fineSelected

/--
The original shading restricted once along the complete composite embedding
to the final metric-core family.
-/
noncomputable def finalRestrictedShading
    (shading : WZ1PaperTubeShading fine) :
    WZ1PaperTubeShading
      metricCore.restriction.fineSelected.family :=
  restrictPaperShading metricCore.finalSubfamily shading

@[simp] theorem finalSubfamily_family :
    metricCore.finalSubfamily.family =
      metricCore.restriction.fineSelected.family :=
  rfl

@[simp] theorem finalSubfamily_embedding
    (source :
      Fin metricCore.restriction.fineSelected.family.card) :
    metricCore.finalSubfamily.embedding source =
      metricCore.metric.mesh.complete.selectedFine.embedding
        (metricCore.restriction.fineSelected.embedding source) :=
  rfl

@[simp] theorem finalRestrictedShading_carrier
    (shading : WZ1PaperTubeShading fine)
    (source :
      Fin metricCore.restriction.fineSelected.family.card) :
    (metricCore.finalRestrictedShading shading).carrier source =
      shading.carrier
        (metricCore.metric.mesh.complete.selectedFine.embedding
          (metricCore.restriction.fineSelected.embedding source)) :=
  rfl

theorem finalRestrictedShading_cubical
    {shading : WZ1PaperTubeShading fine}
    (cubical : WZ1PaperIsCubicalShading shading) :
    WZ1PaperIsCubicalShading
      (metricCore.finalRestrictedShading shading) :=
  restrictPaperShading_cubical
    metricCore.finalSubfamily cubical

theorem finalRestrictedShading_mass_eq_pulledBack
    (shading : WZ1PaperTubeShading fine)
    (ambientWeightEq :
      ∀ source, weight source = volume (shading.carrier source)) :
    (metricCore.finalRestrictedShading shading).mass =
      ∑ source ∈ metricCore.pulledBack,
        weight
          (metricCore.metric.mesh.complete.selectedFine.embedding
            source) := by
  have imageSum :
      (∑ ambientSource ∈
          Finset.image
            metricCore.restriction.fineSelected.embedding
            Finset.univ,
          weight
            (metricCore.metric.mesh.complete.selectedFine.embedding
              ambientSource)) =
        ∑ source :
            Fin metricCore.restriction.fineSelected.family.card,
          weight
            (metricCore.metric.mesh.complete.selectedFine.embedding
              (metricCore.restriction.fineSelected.embedding
                source)) :=
    Finset.sum_image
      metricCore.restriction.fineSelected.embedding.injective.injOn
  rw [metricCore.restriction.fine_image_univ] at imageSum
  change
    (∑ source :
        Fin metricCore.restriction.fineSelected.family.card,
        volume
          (shading.carrier
            (metricCore.finalSubfamily.embedding source))) =
      ∑ source ∈ metricCore.pulledBack,
        weight
          (metricCore.metric.mesh.complete.selectedFine.embedding
            source)
  calc
    (∑ source :
        Fin metricCore.restriction.fineSelected.family.card,
        volume
          (shading.carrier
            (metricCore.finalSubfamily.embedding source))) =
        ∑ source :
            Fin metricCore.restriction.fineSelected.family.card,
          weight
            (metricCore.metric.mesh.complete.selectedFine.embedding
              (metricCore.restriction.fineSelected.embedding
                source)) := by
      apply Finset.sum_congr rfl
      intro source _
      rw [metricCore.finalSubfamily_embedding]
      exact
        (ambientWeightEq
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding
              source))).symm
    _ =
        ∑ source ∈ metricCore.pulledBack,
          weight
            (metricCore.metric.mesh.complete.selectedFine.embedding
              source) :=
      imageSum.symm

theorem finalSubfamily_nonempty :
    metricCore.finalSubfamily.family.Nonempty := by
  change metricCore.restriction.fineSelected.family.Nonempty
  rcases metricCore.restriction.core_nonempty with
    ⟨source, sourceMem⟩
  have sourceImage :
      source ∈
        Finset.image
          metricCore.restriction.fineSelected.embedding
          Finset.univ := by
    rw [metricCore.restriction.fine_image_univ]
    exact sourceMem
  rcases Finset.mem_image.mp sourceImage with
    ⟨selectedSource, _selectedMem, _sourceEq⟩
  exact Nat.zero_lt_of_lt selectedSource.isLt

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

structure PureWZ2Prop62ProxyQuotientFinalRefinementData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (shading : WZ1PaperTubeShading fine)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight) where
  ambient_weight_eq :
    ∀ source, weight source = volume (shading.carrier source)
  refinement : WZ1PaperRefinement shading 10
  selected_eq :
    refinement.selected = metricCore.finalSubfamily
  selected_family_eq :
    refinement.selected.family =
      metricCore.restriction.fineSelected.family
  selected_embedding_eq :
    ∀ source :
        Fin metricCore.restriction.fineSelected.family.card,
      metricCore.finalSubfamily.embedding source =
        metricCore.metric.mesh.complete.selectedFine.embedding
          (metricCore.restriction.fineSelected.embedding source)
  refined_heq :
    HEq refinement.refined
      (metricCore.finalRestrictedShading shading)
  refined_carrier_eq :
    ∀ source :
        Fin metricCore.restriction.fineSelected.family.card,
      (metricCore.finalRestrictedShading shading).carrier source =
        shading.carrier
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding source))
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  selected_nonempty :
    refinement.selected.family.Nonempty

noncomputable def pureWZ2_prop62_proxy_quotient_final_refinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (shading : WZ1PaperTubeShading fine)
    (cubical : WZ1PaperIsCubicalShading shading)
    (ambientWeightEq :
      ∀ source, weight source = volume (shading.carrier source))
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (retainedMass :
      wz1PaperRefinementFraction delta 10 * shading.mass ≤
        (metricCore.finalRestrictedShading shading).mass) :
    PureWZ2Prop62ProxyQuotientFinalRefinementData
      shading metricCore := by
  let selected := metricCore.finalSubfamily
  let refined := metricCore.finalRestrictedShading shading
  let refinement : WZ1PaperRefinement shading 10 :=
    {
      selected := selected
      refined := refined
      subshading := by
        intro source
        exact Set.Subset.rfl
      retained_mass := retainedMass
    }
  exact
    {
      ambient_weight_eq := ambientWeightEq
      refinement := refinement
      selected_eq := rfl
      selected_family_eq := rfl
      selected_embedding_eq := by
        intro source
        rfl
      refined_heq := HEq.rfl
      refined_carrier_eq := by
        intro source
        rfl
      refined_cubical := by
        exact metricCore.finalRestrictedShading_cubical cubical
      selected_nonempty :=
        metricCore.finalSubfamily_nonempty
    }

noncomputable def pureWZ2_prop62_proxy_quotient_final_refinement_of_ledger
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (baseSelectedParents :
      Finset (Fin metric.metricParents.card))
    (strongUpperSelectedParents :
      Finset (Fin metric.metricParents.card))
    (completeFiber :
      Fin metric.metricParents.card →
        Finset (Fin fine.card))
    (fiberCard :
      Fin metric.metricParents.card → ℕ)
    (parentWeight :
      Fin metric.metricParents.card → ENNReal)
    (owner :
      Fin fine.card → Fin metric.metricParents.card)
    (sourceColor : Fin fine.card → Color)
    (fiberCardBound : ℕ)
    (preCore :
      PureWZ2Prop62PreCoreSelectionData
        (Fin fine.card) (Fin metric.metricParents.card) Color
        strongUpperSelectedParents completeFiber fiberCard parentWeight owner
        sourceColor weight fiberCardBound)
    (preliminarySubsetSelection :
      preCore.preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preCore.preliminary)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (ledger :
      PureWZ2Prop62ProxyQuotientMassLedger
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric baseSelectedParents
        strongUpperSelectedParents completeFiber fiberCard
        parentWeight owner sourceColor fiberCardBound preCore
        preliminarySubsetSelection receipt metricCore)
    (shading : WZ1PaperTubeShading fine)
    (cubical : WZ1PaperIsCubicalShading shading)
    (ambientWeightEq :
      ∀ source, weight source = volume (shading.carrier source))
    (absorption :
      wz1PaperRefinementFraction delta 10 *
        ledger.totalLoss ≤ 1) :
    PureWZ2Prop62ProxyQuotientFinalRefinementData
      shading metricCore := by
  have sourceMassEq :
      shading.mass =
        ∑ source : Fin fine.card, weight source := by
    apply Finset.sum_congr rfl
    intro source _
    exact (ambientWeightEq source).symm
  have finalMassEq :
      (metricCore.finalRestrictedShading shading).mass =
        ∑ source ∈ metricCore.pulledBack,
          weight
            (metricCore.metric.mesh.complete.selectedFine.embedding
              source) :=
    metricCore.finalRestrictedShading_mass_eq_pulledBack
      shading ambientWeightEq
  have retainedMass :
      wz1PaperRefinementFraction delta 10 * shading.mass ≤
        (metricCore.finalRestrictedShading shading).mass := by
    calc
      wz1PaperRefinementFraction delta 10 * shading.mass =
          wz1PaperRefinementFraction delta 10 *
            ∑ source : Fin fine.card, weight source := by
        rw [sourceMassEq]
      _ ≤
          wz1PaperRefinementFraction delta 10 *
            (ledger.totalLoss *
              ∑ source ∈ metricCore.pulledBack,
                weight
                  (metricCore.metric.mesh.complete.selectedFine.embedding
                    source)) := by
        gcongr
        exact ledger.final_mass_retention
      _ =
          (wz1PaperRefinementFraction delta 10 *
            ledger.totalLoss) *
              ∑ source ∈ metricCore.pulledBack,
                weight
                  (metricCore.metric.mesh.complete.selectedFine.embedding
                    source) := by
        ring
      _ ≤
          1 *
            ∑ source ∈ metricCore.pulledBack,
              weight
                (metricCore.metric.mesh.complete.selectedFine.embedding
                  source) := by
        gcongr
      _ =
          (metricCore.finalRestrictedShading shading).mass := by
        rw [one_mul, finalMassEq]
  exact
    pureWZ2_prop62_proxy_quotient_final_refinement
      schedule fineNonempty quotient width packetCoordinate
      strideBase weight shading cubical ambientWeightEq
      metricCore retainedMass

namespace PureWZ2Prop62ProxyQuotientFinalRefinementData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {shading : WZ1PaperTubeShading fine}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    (output :
      PureWZ2Prop62ProxyQuotientFinalRefinementData
        shading metricCore)

theorem refined_eq_restrictPaperShading :
    HEq output.refinement.refined
      (restrictPaperShading
        (metricCore.metric.mesh.complete.selectedFine.toTubeSubfamily.comp
          metricCore.restriction.fineSelected)
        shading) :=
  output.refined_heq

theorem selected_family_provenance :
    output.refinement.selected.family =
      metricCore.restriction.fineSelected.family :=
  output.selected_family_eq

end PureWZ2Prop62ProxyQuotientFinalRefinementData

end Kakeya.Assouad

end

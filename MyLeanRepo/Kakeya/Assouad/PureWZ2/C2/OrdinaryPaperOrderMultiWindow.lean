import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderAllBlockFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderOneScale

/-!
# Multi-window output of the paper-ordered ordinary construction

This module unions the original-family `Z_lin` height lifts selected from one
mod-64 class of balanced safe windows.  Their trapezoid cores are separated,
so both union volume and indexed shading mass add without overlap.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData

namespace PureWZ2OrdinaryPaperOrderBlockResidueData

/-- Finite union of the selected paper-order original-family height lifts. -/
def shading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    WZ1PaperTubeShading source.family where
  carrier sourceIndex :=
    ⋃ index : Fin residueData.selected.card,
      (data.rich
        (residueData.selectedIndex index)).heightLift.shading.carrier sourceIndex
  measurable_carrier sourceIndex := MeasurableSet.iUnion fun index =>
    (data.rich
      (residueData.selectedIndex index)).heightLift.shading.measurable_carrier
        sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact (data.rich
      (residueData.selectedIndex index)).heightLift.shading.subset_body
        sourceIndex hindex

@[simp] theorem mem_shading_carrier_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data)
    (sourceIndex : Fin source.family.card) (point : Point3) :
    point ∈ residueData.shading.carrier sourceIndex ↔
      ∃ index : Fin residueData.selected.card,
        point ∈ (data.rich
          (residueData.selectedIndex index)).heightLift.shading.carrier
            sourceIndex := by
  simp [shading]

/-- The multi-window union stays on the original source family. -/
theorem subshading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    PureWZ2PaperIsSubshading residueData.shading source.shading := by
  intro sourceIndex point hpoint
  rcases (residueData.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, hindex⟩
  exact (data.rich
    (residueData.selectedIndex index)).heightLift.subshading sourceIndex hindex

/-- The finite union is cubical because every local height lift consists of
complete original `delta` cells. -/
theorem cubical
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    WZ1PaperIsCubicalShading residueData.shading := by
  intro sourceIndex point hpoint other hother
  rcases (residueData.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, hindex⟩
  exact (residueData.mem_shading_carrier_iff sourceIndex other).mpr
    ⟨index, (data.rich
      (residueData.selectedIndex index)).heightLift.whole_cells
        sourceIndex point hindex hother⟩

theorem mem_shading_union_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data)
    (point : Point3) :
    point ∈ residueData.shading.union ↔
      ∃ index : Fin residueData.selected.card,
        point ∈ (data.rich
          (residueData.selectedIndex index)).heightLift.shading.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (residueData.mem_shading_carrier_iff
      sourceIndex point).mp hpoint with ⟨index, hindex⟩
    exact ⟨index, sourceIndex, hindex⟩
  · rintro ⟨index, sourceIndex, hpoint⟩
    exact ⟨sourceIndex,
      (residueData.mem_shading_carrier_iff sourceIndex point).mpr
        ⟨index, hpoint⟩⟩

/-- Distinct local height-lift unions are disjoint by the residue-class core
separation. -/
theorem rich_union_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    Pairwise fun first second : Fin residueData.selected.card =>
      Disjoint
        (data.rich
          (residueData.selectedIndex first)).heightLift.shading.union
        (data.rich
          (residueData.selectedIndex second)).heightLift.shading.union := by
  intro first second hne
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  let z := point (2 : Fin 3)
  have hfirstSlice : horizontalSlice
      (data.rich
        (residueData.selectedIndex first)).heightLift.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hfirst, rfl⟩
  have hsecondSlice : horizontalSlice
      (data.rich
        (residueData.selectedIndex second)).heightLift.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hsecond, rfl⟩
  have hfirstCore :=
    (data.rich
      (residueData.selectedIndex first)).heightLift.active_height_coverage
        z hfirstSlice
  have hsecondCore :=
    (data.rich
      (residueData.selectedIndex second)).heightLift.active_height_coverage
        z hsecondSlice
  have hsep := residueData.separated_cores first second hne
    z hfirstCore z hsecondCore
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    have hrho : 0 < rho :=
      (family.carrierData
        (data.safeBlock
          (residueData.selectedIndex first))).line.rho_pos
    unfold pureWZ2SourceHorizontalFinalScale
    nlinarith
  exact (not_le_of_gt (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep)

/-- Distinct selected windows are disjoint tube by tube. -/
theorem rich_carrier_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data)
    (sourceIndex : Fin source.family.card) :
    Pairwise fun first second : Fin residueData.selected.card =>
      Disjoint
        ((data.rich
          (residueData.selectedIndex first)).heightLift.shading.carrier sourceIndex)
        ((data.rich
          (residueData.selectedIndex second)).heightLift.shading.carrier
            sourceIndex) := by
  intro first second hne
  exact (residueData.rich_union_pairwise_disjoint hne).mono
    (fun point (hpoint : point ∈ (data.rich
        (residueData.selectedIndex first)).heightLift.shading.carrier
          sourceIndex) =>
      show point ∈ (data.rich
        (residueData.selectedIndex first)).heightLift.shading.union from
        ⟨sourceIndex, hpoint⟩)
    (fun point (hpoint : point ∈ (data.rich
        (residueData.selectedIndex second)).heightLift.shading.carrier
          sourceIndex) =>
      show point ∈ (data.rich
        (residueData.selectedIndex second)).heightLift.shading.union from
        ⟨sourceIndex, hpoint⟩)

/-- The indexed mass of the paper-order multi-window union is the exact sum
of the selected local masses. -/
theorem shading_mass_eq_sum
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    residueData.shading.mass =
      ∑ index : Fin residueData.selected.card,
        (data.rich
          (residueData.selectedIndex index)).heightLift.shading.mass := by
  calc
    residueData.shading.mass =
        ∑ sourceIndex : Fin source.family.card,
          volume (⋃ index : Fin residueData.selected.card,
            (data.rich (residueData.selectedIndex index)).heightLift.shading.carrier
              sourceIndex) := rfl
    _ = ∑ sourceIndex : Fin source.family.card,
          ∑ index : Fin residueData.selected.card,
            volume ((data.rich
              (residueData.selectedIndex index)).heightLift.shading.carrier
                sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_iUnion
        (residueData.rich_carrier_pairwise_disjoint sourceIndex)
        (fun index => (data.rich
          (residueData.selectedIndex index)).heightLift.shading.measurable_carrier
            sourceIndex)]
      simp [tsum_fintype]
    _ = ∑ index : Fin residueData.selected.card,
          ∑ sourceIndex : Fin source.family.card,
            volume ((data.rich
              (residueData.selectedIndex index)).heightLift.shading.carrier
                sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ index : Fin residueData.selected.card,
        (data.rich
          (residueData.selectedIndex index)).heightLift.shading.mass := rfl

/-- The all-good-block output mass is controlled by the actual selected
paper-order multi-window union. -/
theorem total_mass_le_shading_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    (∑ index : Fin data.indexCount,
        (data.rich index).heightLift.shading.mass) ≤
      64 * residueData.shading.mass := by
  rw [residueData.shading_mass_eq_sum]
  exact residueData.total_mass_le

/-- An aggregate mass bound is exactly density of the paper-order union. -/
theorem dense_of_sum_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data)
    (hbudget :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        ∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass) :
    residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
  unfold Kakeya.Streamlined.Shading.IsLambdaDense
  rwa [residueData.shading_mass_eq_sum]

/-- The finite set of trapezoids carried by the selected residue class. -/
def trapezoids
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    Finset WZ1VerticalTrapezoid :=
  Finset.univ.image fun index =>
    (data.rich
      (residueData.selectedIndex index)).richTrapezoid.trapezoid

theorem trapezoids_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data) :
    residueData.trapezoids.Nonempty := by
  let first : Fin residueData.selected.card :=
    ⟨0, Finset.card_pos.mpr residueData.selected_nonempty⟩
  exact ⟨(data.rich
      (residueData.selectedIndex first)).richTrapezoid.trapezoid,
    Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩⟩

theorem rich_scale_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data)
    (index : Fin residueData.selected.card) :
    (data.rich
      (residueData.selectedIndex index)).richTrapezoid.scale =
        pureWZ2SourceHorizontalFinalScale rho := by
  rw [(data.rich
    (residueData.selectedIndex index)).richTrapezoid.scale_eq]
  rw [(all.graphPreparation
    (data.safeBlock
      (residueData.selectedIndex index))).prep.graphScale_eq]
  simp [pureWZ2SourceHorizontalFinalScale]
  ring

/-- Apply the same-extremizer grain producer to the genuine paper-order
multi-window union and export the public scale `1280 * rho`. -/
theorem toOneScaleOfGrainProducer
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData : PureWZ2OrdinaryPaperOrderBlockResidueData data)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData targetShading sigma finalLoss))
    (hdense : residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  have hsourceStructural : WZ2PaperCroppedIsExtremal
      sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hfamilyStructural : WZ2PaperCroppedIsExtremal
      sigma structuralLoss source.family residueData.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := residueData.cubical
      dense := hdense
      volume_upper :=
        (measure_mono residueData.subshading.union_subset).trans
          hsourceStructural.volume_upper }
  rcases grainProducer source.family residueData.shading source.line_class
      hfamilyStructural with ⟨refined⟩
  have hsub : PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro sourceIndex point hpoint
    exact residueData.subshading sourceIndex
      (refined.subshading sourceIndex hpoint)
  have hconstant : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-finalLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one
      (hinputStructural.trans hstructuralFinal)
  have hconstantTop :
      Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant hsub hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict hsub hconstant hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ refined.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, hsub.union_subset point.property⟩
  let first : Fin residueData.selected.card :=
    ⟨0, Finset.card_pos.mpr residueData.selected_nonempty⟩
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    rw [← residueData.rich_scale_eq first]
    exact (data.rich
      (residueData.selectedIndex first)).richTrapezoid.scale_pos
  have hdeltaScale : delta ≤ pureWZ2SourceHorizontalFinalScale rho := by
    rw [← residueData.rich_scale_eq first]
    calc
      delta ≤ (all.graphPreparation
          (data.safeBlock
            (residueData.selectedIndex first))).prep.graphScale :=
        (all.graphPreparation
          (data.safeBlock
            (residueData.selectedIndex first))).prep.sourceScale_le_graphScale
      _ ≤ 5 * (all.graphPreparation
          (data.safeBlock
            (residueData.selectedIndex first))).prep.graphScale := by
        nlinarith [(all.graphPreparation
          (data.safeBlock
            (residueData.selectedIndex first))).prep.graphScale_pos]
      _ = (data.rich
          (residueData.selectedIndex first)).richTrapezoid.scale :=
        (data.rich
          (residueData.selectedIndex first)).richTrapezoid.scale_eq.symm
  have hscaleOne : pureWZ2SourceHorizontalFinalScale rho ≤ 1 := by
    rw [← residueData.rich_scale_eq first]
    exact (data.rich
      (residueData.selectedIndex first)).richTrapezoid.scale_le_one
  exact ⟨{
    rho_pos := hscalePos
    delta_le_rho := hdeltaScale
    rho_le_one := hscaleOne
    shading := refined.shading
    subshading := hsub
    whole_cells := refined.cubical
    extremal := refined.extremal
    volume_lower := refined.volume_lower
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    globalGrains := globalGrains
    slope_eq := rfl
    trapezoids := residueData.trapezoids
    trapezoids_nonempty := residueData.trapezoids_nonempty
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      rw [(data.rich
        (residueData.selectedIndex index)).richTrapezoid.height_eq]
      exact residueData.rich_scale_eq index
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      exact (data.rich
        (residueData.selectedIndex index)).richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      simpa [residueData.rich_scale_eq index] using
        (data.rich
          (residueData.selectedIndex index)).richTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with ⟨firstIndex, _, rfl⟩
      rcases Finset.mem_image.mp hother with ⟨secondIndex, _, rfl⟩
      have hindexNe : firstIndex ≠ secondIndex := by
        intro hindex
        subst secondIndex
        exact hne rfl
      exact residueData.separated_cores firstIndex secondIndex hindexNe
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨targetIndex, _, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ residueData.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (residueData.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨sourceIndex, hsourcePoint⟩
      have hsourceSlice : horizontalSlice
          (data.rich (residueData.selectedIndex sourceIndex)).heightLift.shading.union
            z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore := (data.rich
        (residueData.selectedIndex sourceIndex)).heightLift.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (data.rich
            (residueData.selectedIndex targetIndex)).richTrapezoid.trapezoid =
          (data.rich
            (residueData.selectedIndex sourceIndex)).richTrapezoid.trapezoid
      · rw [heq]
        change |source.globalGrains.slope z -
            (data.rich (residueData.selectedIndex sourceIndex)).richTrapezoid.trapezoid.affine z| ≤
          pureWZ2SourceHorizontalFinalScale rho
        simpa [residueData.rich_scale_eq sourceIndex] using
          (data.rich
            (residueData.selectedIndex sourceIndex)).heightLift.slope_approximation
              z hsourceSlice
      · have hsep := residueData.separated_cores targetIndex sourceIndex
          (by
            intro hindex
            subst sourceIndex
            exact heq rfl) z hz z hsourceCore
        exact False.elim ((not_le_of_gt (Real.sqrt_pos.mpr hscalePos))
          (by simpa using hsep))
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ residueData.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (residueData.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨index, hindexPoint⟩
      have hindexSlice : horizontalSlice
          (data.rich (residueData.selectedIndex index)).heightLift.shading.union
            z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hindexPoint, hpoint.2⟩
      exact ⟨(data.rich
          (residueData.selectedIndex index)).richTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩,
        (data.rich
          (residueData.selectedIndex index)).heightLift.active_height_coverage
            z hindexSlice⟩
  }⟩

end PureWZ2OrdinaryPaperOrderBlockResidueData

end PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData

end Kakeya.Assouad

end

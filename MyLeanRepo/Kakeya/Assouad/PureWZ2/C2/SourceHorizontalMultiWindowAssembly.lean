import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBudgetedProducer

/-!
# Multi-window source-horizontal Pure one-scale assembly

This module combines finitely many already-constructed local rich-height
lifts on the same source family.  The auxiliary graph shadings supply the
weighted mass lower bound, while the final union keeps every complete source
cell at the selected heights before the Node-4 refinement.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The common final trapezoid height of every local source window. -/
def pureWZ2SourceHorizontalFinalScale (rho : ℝ) : ℝ :=
  1280 * rho

/-- A finite family of local rich-window outputs with separated cores. -/
structure PureWZ2SourceHorizontalWindowFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) where
  windowCount : ℕ
  windowCount_pos : 0 < windowCount
  pipeline : Fin windowCount →
    PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale
  rich : ∀ index, PureWZ2SourceHorizontalRichPipelineData
    (finalLoss := finalLoss) (theoremEta := theoremEta) (pipeline index)
  trapezoid_injective : Function.Injective fun index =>
    (rich index).richTrapezoid.trapezoid
  separated_cores :
    ∀ first second,
      (rich first).richTrapezoid.trapezoid ≠
          (rich second).richTrapezoid.trapezoid →
        ∀ z ∈ (rich first).richTrapezoid.trapezoid.core,
          ∀ w ∈ (rich second).richTrapezoid.trapezoid.core,
            Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w|

namespace PureWZ2SourceHorizontalWindowFamilyData

/-- Finite union of all local height-only source lifts. -/
def shading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale) :
    WZ1PaperTubeShading source.family where
  carrier sourceIndex :=
    ⋃ window : Fin family.windowCount,
      (family.rich window).heightLift.shading.carrier sourceIndex
  measurable_carrier sourceIndex :=
    MeasurableSet.iUnion fun window =>
      (family.rich window).heightLift.shading.measurable_carrier sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨window, hwindow⟩
    exact (family.rich window).heightLift.shading.subset_body
      sourceIndex hwindow

@[simp] theorem mem_shading_carrier_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale)
    (sourceIndex : Fin source.family.card) (point : Point3) :
    point ∈ family.shading.carrier sourceIndex ↔
      ∃ window : Fin family.windowCount,
        point ∈ (family.rich window).heightLift.shading.carrier sourceIndex := by
  simp [shading]

/-- The finite rich union remains a subshading of the original source. -/
theorem subshading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale) :
    PureWZ2PaperIsSubshading family.shading source.shading := by
  intro sourceIndex point hpoint
  rcases (family.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨window, hwindow⟩
  exact (family.rich window).heightLift.subshading sourceIndex hwindow

/-- A finite union of whole original cells is still cubical. -/
theorem cubical
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale) :
    WZ1PaperIsCubicalShading family.shading := by
  intro sourceIndex point hpoint other hother
  rcases (family.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨window, hwindow⟩
  apply (family.mem_shading_carrier_iff sourceIndex other).mpr
  exact ⟨window,
    (family.rich window).heightLift.whole_cells
      sourceIndex point hwindow hother⟩

theorem mem_shading_union_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale)
    (point : Point3) :
    point ∈ family.shading.union ↔
      ∃ window : Fin family.windowCount,
        point ∈ (family.rich window).heightLift.shading.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (family.mem_shading_carrier_iff sourceIndex point).mp hpoint with
      ⟨window, hwindow⟩
    exact ⟨window, sourceIndex, hwindow⟩
  · rintro ⟨window, sourceIndex, hpoint⟩
    exact ⟨sourceIndex,
      (family.mem_shading_carrier_iff sourceIndex point).mpr
        ⟨window, hpoint⟩⟩

/-- Distinct local window unions are disjoint because every active height is
in its local trapezoid core and distinct cores are separated. -/
theorem rich_union_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale) :
    Pairwise fun first second : Fin family.windowCount =>
      Disjoint
        (family.rich first).heightLift.shading.union
        (family.rich second).heightLift.shading.union := by
  intro first second hne
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  let firstTrapezoid := (family.rich first).richTrapezoid.trapezoid
  let secondTrapezoid := (family.rich second).richTrapezoid.trapezoid
  have htrapezoidNe : firstTrapezoid ≠ secondTrapezoid := by
    intro heq
    exact hne (family.trapezoid_injective heq)
  let z := point (2 : Fin 3)
  have hfirstSlice : horizontalSlice
      (family.rich first).heightLift.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hfirst, rfl⟩
  have hsecondSlice : horizontalSlice
      (family.rich second).heightLift.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hsecond, rfl⟩
  have hfirstCore : z ∈ firstTrapezoid.core :=
    (family.rich first).heightLift.active_height_coverage z hfirstSlice
  have hsecondCore : z ∈ secondTrapezoid.core :=
    (family.rich second).heightLift.active_height_coverage z hsecondSlice
  have hsep := family.separated_cores first second htrapezoidNe
    z hfirstCore z hsecondCore
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    unfold pureWZ2SourceHorizontalFinalScale
    nlinarith [(family.pipeline first).line.rho_pos]
  have hsqrtPos : 0 < Real.sqrt
      (pureWZ2SourceHorizontalFinalScale rho) :=
    Real.sqrt_pos.mpr hscalePos
  exact (not_le_of_gt hsqrtPos) (by simpa using hsep)

/-- Distinct local carriers are disjoint tube by tube. -/
theorem rich_carrier_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale)
    (sourceIndex : Fin source.family.card) :
    Pairwise fun first second : Fin family.windowCount =>
      Disjoint
        ((family.rich first).heightLift.shading.carrier sourceIndex)
        ((family.rich second).heightLift.shading.carrier sourceIndex) := by
  intro first second hne
  exact (family.rich_union_pairwise_disjoint hne).mono
    (fun point (hpoint : point ∈
        (family.rich first).heightLift.shading.carrier sourceIndex) =>
      show point ∈ (family.rich first).heightLift.shading.union from
        ⟨sourceIndex, hpoint⟩)
    (fun point (hpoint : point ∈
        (family.rich second).heightLift.shading.carrier sourceIndex) =>
      show point ∈ (family.rich second).heightLift.shading.union from
        ⟨sourceIndex, hpoint⟩)

/-- Indexed mass of the finite rich union is the sum of local indexed masses. -/
theorem shading_mass_eq_sum
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale) :
    family.shading.mass =
      ∑ window : Fin family.windowCount,
        (family.rich window).heightLift.shading.mass := by
  calc
    family.shading.mass =
        ∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume (⋃ window : Fin family.windowCount,
            (family.rich window).heightLift.shading.carrier sourceIndex) := rfl
    _ = ∑ sourceIndex : Fin source.family.card,
          ∑ window : Fin family.windowCount,
            MeasureTheory.volume
              ((family.rich window).heightLift.shading.carrier sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_iUnion
        (family.rich_carrier_pairwise_disjoint sourceIndex)
        (fun window =>
          (family.rich window).heightLift.shading.measurable_carrier
            sourceIndex)]
      simp [tsum_fintype]
    _ = ∑ window : Fin family.windowCount,
          ∑ sourceIndex : Fin source.family.card,
            MeasureTheory.volume
              ((family.rich window).heightLift.shading.carrier sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ window : Fin family.windowCount,
        (family.rich window).heightLift.shading.mass := rfl

/-! ## The common-multiplicity whole-cell union

The larger `heightLift.shading` is convenient for the volume budget, but it
need not inherit the sticky multiplicity band.  Corollary 5.6 first passes to
a constant-multiplicity refinement.  Here that refinement is the finite union
of the already constructed rich whole-cell shadings.  Each local piece is a
common spatial restriction of the sticky pullback, and the separated window
cores make the local pieces disjoint.
-/

/-- Finite union of the local rich whole-cell shadings. -/
def multiplicityShading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) :
    WZ1PaperTubeShading source.family where
  carrier sourceIndex :=
    ⋃ window : Fin family.windowCount,
      (family.rich window).richShading.shading.carrier sourceIndex
  measurable_carrier sourceIndex :=
    MeasurableSet.iUnion fun window =>
      (family.rich window).richShading.shading.measurable_carrier sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨window, hwindow⟩
    exact (family.rich window).richShading.shading.subset_body
      sourceIndex hwindow

@[simp] theorem mem_multiplicityShading_carrier_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale)
    (sourceIndex : Fin source.family.card) (point : Point3) :
    point ∈ family.multiplicityShading.carrier sourceIndex ↔
      ∃ window : Fin family.windowCount,
        point ∈ (family.rich window).richShading.shading.carrier sourceIndex := by
  simp [multiplicityShading]

/-- The common-multiplicity union is still a refinement of the source. -/
theorem multiplicityShading_subshading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) :
    PureWZ2PaperIsSubshading family.multiplicityShading source.shading := by
  intro sourceIndex point hpoint
  rcases (family.mem_multiplicityShading_carrier_iff
      sourceIndex point).mp hpoint with ⟨window, hwindow⟩
  exact (family.rich window).richShading.subshading sourceIndex hwindow

/-- The finite union is cubical because every local rich shading consists of
complete original delta-cells. -/
theorem multiplicityShading_cubical
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) :
    WZ1PaperIsCubicalShading family.multiplicityShading := by
  intro sourceIndex point hpoint other hother
  rcases (family.mem_multiplicityShading_carrier_iff
      sourceIndex point).mp hpoint with ⟨window, hwindow⟩
  exact (family.mem_multiplicityShading_carrier_iff
    sourceIndex other).mpr ⟨window,
      (family.rich window).richShading.whole_cells
        sourceIndex point hwindow hother⟩

theorem mem_multiplicityShading_union_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale)
    (point : Point3) :
    point ∈ family.multiplicityShading.union ↔
      ∃ window : Fin family.windowCount,
        point ∈ (family.rich window).richShading.shading.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (family.mem_multiplicityShading_carrier_iff
        sourceIndex point).mp hpoint with ⟨window, hwindow⟩
    exact ⟨window, sourceIndex, hwindow⟩
  · rintro ⟨window, sourceIndex, hpoint⟩
    exact ⟨sourceIndex,
      (family.mem_multiplicityShading_carrier_iff
        sourceIndex point).mpr ⟨window, hpoint⟩⟩

/-- Local rich whole-cell unions are disjoint since they lie in the already
separated height-lift unions. -/
theorem multiplicity_union_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) :
    Pairwise fun first second : Fin family.windowCount =>
      Disjoint
        (family.rich first).richShading.shading.union
        (family.rich second).richShading.shading.union := by
  intro first second hne
  exact (family.rich_union_pairwise_disjoint hne).mono
    (family.rich first).heightLift.rich_subshading.union_subset
    (family.rich second).heightLift.rich_subshading.union_subset

/-- Tube-by-tube disjointness used to compute the indexed mass exactly. -/
theorem multiplicity_carrier_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale)
    (sourceIndex : Fin source.family.card) :
    Pairwise fun first second : Fin family.windowCount =>
      Disjoint
        ((family.rich first).richShading.shading.carrier sourceIndex)
        ((family.rich second).richShading.shading.carrier sourceIndex) := by
  intro first second hne
  exact (family.multiplicity_union_pairwise_disjoint hne).mono
    (fun point (hpoint : point ∈
        (family.rich first).richShading.shading.carrier sourceIndex) =>
      show point ∈ (family.rich first).richShading.shading.union from
        ⟨sourceIndex, hpoint⟩)
    (fun point (hpoint : point ∈
        (family.rich second).richShading.shading.carrier sourceIndex) =>
      show point ∈ (family.rich second).richShading.shading.union from
        ⟨sourceIndex, hpoint⟩)

/-- The indexed mass of the common-multiplicity union is the exact sum of the
local rich whole-cell masses. -/
theorem multiplicityShading_mass_eq_sum
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) :
    family.multiplicityShading.mass =
      ∑ window : Fin family.windowCount,
        (family.rich window).richShading.shading.mass := by
  calc
    family.multiplicityShading.mass =
        ∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume (⋃ window : Fin family.windowCount,
            (family.rich window).richShading.shading.carrier sourceIndex) := rfl
    _ = ∑ sourceIndex : Fin source.family.card,
          ∑ window : Fin family.windowCount,
            MeasureTheory.volume
              ((family.rich window).richShading.shading.carrier sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_iUnion
        (family.multiplicity_carrier_pairwise_disjoint sourceIndex)
        (fun window =>
          (family.rich window).richShading.shading.measurable_carrier
            sourceIndex)]
      simp [tsum_fintype]
    _ = ∑ window : Fin family.windowCount,
          ∑ sourceIndex : Fin source.family.card,
            MeasureTheory.volume
              ((family.rich window).richShading.shading.carrier sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ window : Fin family.windowCount,
        (family.rich window).richShading.shading.mass := rfl

/-- At a point in the aggregate union exactly one local window contributes, so
the point multiplicity agrees with that local rich shading. -/
theorem multiplicityShading_pointMultiplicity_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale)
    {point : Point3} (hpoint : point ∈ family.multiplicityShading.union) :
    ∃ window : Fin family.windowCount,
      point ∈ (family.rich window).richShading.shading.union ∧
      family.multiplicityShading.pointMultiplicity point =
        (family.rich window).richShading.shading.pointMultiplicity point := by
  rcases (family.mem_multiplicityShading_union_iff point).mp hpoint with
    ⟨window, hwindow⟩
  refine ⟨window, hwindow, ?_⟩
  unfold Kakeya.Streamlined.Shading.pointMultiplicity
  congr 1
  ext sourceIndex
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro haggregate
    rcases (family.mem_multiplicityShading_carrier_iff
        sourceIndex point).mp haggregate with ⟨other, hother⟩
    by_cases heq : other = window
    · subst other
      exact hother
    · have hdisjoint := Set.disjoint_left.mp
        (family.multiplicity_union_pairwise_disjoint heq)
      exact False.elim (hdisjoint
        (show point ∈ (family.rich other).richShading.shading.union from
          ⟨sourceIndex, hother⟩) hwindow)
  · intro hlocal
    exact (family.mem_multiplicityShading_carrier_iff
      sourceIndex point).mpr ⟨window, hlocal⟩

/-- The finite whole-cell union has the same common multiplicity band as every
local sticky restriction. -/
theorem multiplicityShading_constantMultiplicity
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) :
    family.multiplicityShading.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
  intro point hpoint
  rcases family.multiplicityShading_pointMultiplicity_eq hpoint with
    ⟨window, hwindow, hmultiplicity⟩
  rw [hmultiplicity]
  exact (family.rich window).richShading.constantMultiplicity point hwindow

/-- The multiplicity shading retains the aggregate rich mass budget exactly. -/
theorem multiplicityShading_dense_of_sum_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale)
    (hbudget :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        ∑ window : Fin family.windowCount,
          (family.rich window).richShading.shading.mass) :
    family.multiplicityShading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
  unfold Kakeya.Streamlined.Shading.IsLambdaDense
  rw [family.multiplicityShading_mass_eq_sum]
  exact hbudget

/-- Convert an aggregate local-window mass budget into density of the exact
finite union shading. -/
theorem dense_of_sum_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale)
    (hbudget :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        ∑ window : Fin family.windowCount,
          (family.rich window).richShading.shading.mass) :
    family.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
  apply hbudget.trans
  rw [family.shading_mass_eq_sum]
  exact Finset.sum_le_sum fun window _ =>
    (family.rich window).heightLift.mass_lower

/-- The finite set of local trapezoids, with duplicate values identified. -/
def trapezoids
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale) :
    Finset WZ1VerticalTrapezoid :=
  Finset.univ.image fun window =>
    (family.rich window).richTrapezoid.trapezoid

theorem trapezoids_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale) :
    family.trapezoids.Nonempty := by
  let first : Fin family.windowCount := ⟨0, family.windowCount_pos⟩
  exact ⟨(family.rich first).richTrapezoid.trapezoid,
    Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩⟩

theorem rich_scale_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale)
    (window : Fin family.windowCount) :
    (family.rich window).richTrapezoid.scale =
      pureWZ2SourceHorizontalFinalScale rho := by
  rw [(family.rich window).richTrapezoid.scale_eq,
    (family.pipeline window).prep.graphScale_eq]
  simp [pureWZ2SourceHorizontalFinalScale]
  ring

/--
Assemble the final same-configuration one-scale output once extremality and
the critical union-volume floor have been proved on the actual finite union
of rich height windows.  The global slope and local plane map are literal
restrictions of the Proposition 6.3 source data; no second grain construction
or independently selected analytic witness is used.
-/
theorem toOneScaleOfExtremalAndVolumeLower
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale)
    (hinputFinal : inputLoss ≤ finalLoss)
    (hfamilyFinal : WZ2PaperCroppedIsExtremal
      sigma finalLoss source.family family.shading)
    (hvolume : Kakeya.realRpowENN delta (sigma + finalLoss) ≤
      MeasureTheory.volume family.shading.union) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-finalLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputFinal
  have hconstantTop :
      Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    family.subshading hconstant hconstantTop
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      family.subshading hconstant hconstantTop
  let globalGrains :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  have hvertical :
      ∀ point : {point : Point3 // point ∈ family.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, family.subshading.union_subset point.property⟩
  let first : Fin family.windowCount := ⟨0, family.windowCount_pos⟩
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    rw [← family.rich_scale_eq first]
    exact (family.rich first).richTrapezoid.scale_pos
  have hdeltaScale :
      delta ≤ pureWZ2SourceHorizontalFinalScale rho := by
    rw [← family.rich_scale_eq first]
    calc
      delta ≤ (family.pipeline first).prep.graphScale :=
        (family.pipeline first).prep.sourceScale_le_graphScale
      _ ≤ 5 * (family.pipeline first).prep.graphScale := by
        nlinarith [(family.pipeline first).prep.graphScale_pos]
      _ = (family.rich first).richTrapezoid.scale :=
        (family.rich first).richTrapezoid.scale_eq.symm
  have hscaleOne : pureWZ2SourceHorizontalFinalScale rho ≤ 1 := by
    rw [← family.rich_scale_eq first]
    exact (family.rich first).richTrapezoid.scale_le_one
  exact ⟨{
    rho_pos := hscalePos
    delta_le_rho := hdeltaScale
    rho_le_one := hscaleOne
    shading := family.shading
    subshading := family.subshading
    whole_cells := family.cubical
    extremal := hfamilyFinal
    volume_lower := hvolume
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    globalGrains := globalGrains
    slope_eq := rfl
    trapezoids := family.trapezoids
    trapezoids_nonempty := family.trapezoids_nonempty
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      rw [(family.rich window).richTrapezoid.height_eq]
      exact family.rich_scale_eq window
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      exact (family.rich window).richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      simpa [family.rich_scale_eq window] using
        (family.rich window).richTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with
        ⟨firstWindow, _hfirstWindow, rfl⟩
      rcases Finset.mem_image.mp hother with
        ⟨secondWindow, _hsecondWindow, rfl⟩
      exact family.separated_cores firstWindow secondWindow hne
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨targetWindow, _htargetWindow, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (family.mem_shading_union_iff point).mp hpoint.1 with
        ⟨sourceWindow, hsourcePoint⟩
      have hsourceSlice :
          horizontalSlice
              (family.rich sourceWindow).heightLift.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore :=
        (family.rich sourceWindow).heightLift.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (family.rich targetWindow).richTrapezoid.trapezoid =
            (family.rich sourceWindow).richTrapezoid.trapezoid
      · rw [heq]
        change
          |source.globalGrains.slope z -
              (family.rich sourceWindow).richTrapezoid.trapezoid.affine z| ≤
            pureWZ2SourceHorizontalFinalScale rho
        simpa [family.rich_scale_eq sourceWindow] using
          (family.rich sourceWindow).heightLift.slope_approximation
            z hsourceSlice
      · have hsep := family.separated_cores targetWindow sourceWindow
          heq z hz z hsourceCore
        have hsqrtPos :
            0 < Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) :=
          Real.sqrt_pos.mpr hscalePos
        simp only [sub_self, abs_zero] at hsep
        exact False.elim ((not_le_of_gt hsqrtPos) hsep)
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (family.mem_shading_union_iff point).mp hpoint.1 with
        ⟨window, hwindowPoint⟩
      have hwindowSlice :
          horizontalSlice
              (family.rich window).heightLift.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hwindowPoint, hpoint.2⟩
      exact ⟨(family.rich window).richTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨window, Finset.mem_univ _, rfl⟩,
        (family.rich window).heightLift.active_height_coverage z hwindowSlice⟩
  }⟩

/--
Assemble the final same-configuration one-scale output from all local windows.
The only quantitative premise is density of their finite union at the
structural loss selected by the supplied same-extremizer Node-4 producer.
-/
theorem toOneScaleOfGrainProducer
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralOutput : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData
                targetShading sigma finalLoss))
    (hdense : family.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  have hsourceStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hfamilyStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss source.family family.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := family.cubical
      dense := hdense
      volume_upper :=
        (measure_mono family.subshading.union_subset).trans
          hsourceStructural.volume_upper }
  rcases grainProducer source.family family.shading source.line_class
      hfamilyStructural with ⟨refined⟩
  have hsub :
      PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro sourceIndex point hpoint
    exact family.subshading sourceIndex
      (refined.subshading sourceIndex hpoint)
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-finalLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one
      (hinputStructural.trans hstructuralOutput)
  have hconstantTop :
      Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    hsub hconstant hconstantTop
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      hsub hconstant hconstantTop
  let globalGrains :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  have hvertical :
      ∀ point : {point : Point3 // point ∈ refined.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, hsub.union_subset point.property⟩
  let first : Fin family.windowCount := ⟨0, family.windowCount_pos⟩
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    rw [← family.rich_scale_eq first]
    exact (family.rich first).richTrapezoid.scale_pos
  have hdeltaScale :
      delta ≤ pureWZ2SourceHorizontalFinalScale rho := by
    rw [← family.rich_scale_eq first]
    calc
      delta ≤ (family.pipeline first).prep.graphScale :=
        (family.pipeline first).prep.sourceScale_le_graphScale
      _ ≤ 5 * (family.pipeline first).prep.graphScale := by
        nlinarith [(family.pipeline first).prep.graphScale_pos]
      _ = (family.rich first).richTrapezoid.scale :=
        (family.rich first).richTrapezoid.scale_eq.symm
  have hscaleOne : pureWZ2SourceHorizontalFinalScale rho ≤ 1 := by
    rw [← family.rich_scale_eq first]
    exact (family.rich first).richTrapezoid.scale_le_one
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
    trapezoids := family.trapezoids
    trapezoids_nonempty := family.trapezoids_nonempty
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      rw [(family.rich window).richTrapezoid.height_eq]
      exact family.rich_scale_eq window
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      exact (family.rich window).richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      simpa [family.rich_scale_eq window] using
        (family.rich window).richTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with
        ⟨firstWindow, _hfirstWindow, rfl⟩
      rcases Finset.mem_image.mp hother with
        ⟨secondWindow, _hsecondWindow, rfl⟩
      exact family.separated_cores firstWindow secondWindow hne
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨targetWindow, _htargetWindow, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ family.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (family.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨sourceWindow, hsourcePoint⟩
      have hsourceSlice :
          horizontalSlice
              (family.rich sourceWindow).heightLift.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore :=
        (family.rich sourceWindow).heightLift.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (family.rich targetWindow).richTrapezoid.trapezoid =
            (family.rich sourceWindow).richTrapezoid.trapezoid
      · rw [heq]
        change
          |source.globalGrains.slope z -
              (family.rich sourceWindow).richTrapezoid.trapezoid.affine z| ≤
            pureWZ2SourceHorizontalFinalScale rho
        simpa [family.rich_scale_eq sourceWindow] using
          (family.rich sourceWindow).heightLift.slope_approximation
            z hsourceSlice
      · have hsep := family.separated_cores targetWindow sourceWindow
          heq z hz z hsourceCore
        have hsqrtPos :
            0 < Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) :=
          Real.sqrt_pos.mpr hscalePos
        simp only [sub_self, abs_zero] at hsep
        exact False.elim ((not_le_of_gt hsqrtPos) hsep)
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ family.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (family.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨window, hwindowPoint⟩
      have hwindowSlice :
          horizontalSlice
              (family.rich window).heightLift.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hwindowPoint, hpoint.2⟩
      exact ⟨(family.rich window).richTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨window, Finset.mem_univ _, rfl⟩,
        (family.rich window).heightLift.active_height_coverage z hwindowSlice⟩
  }⟩

end PureWZ2SourceHorizontalWindowFamilyData

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerClassScheduleRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.WZLineCoverHitRestriction

/-!
# Positive-mass support of a quotient caller cover

The quotient-net construction may retain a center whose complete actual
fibers have zero shaded mass.  Such a caller cannot be passed to the
per-caller regularizer, whose normalization weight must be positive.

This module removes exactly those zero-mass caller classes.  The restriction
keeps every fine tube assigned to a surviving caller, so it does not cut any
actual complete fiber.  The discarded caller fibers have zero total shaded
mass, hence the restricted fine shading has exactly the original selected
mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem PureWZ2ParentQuotientNetSelectionData.callerActualWeight_eq_fiber_mass
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (parent : Fin data.callerCoarse.card) :
    data.callerActualWeight parent =
      ∑ source ∈
          wz2PaperFullFiberIndices
            data.selected.family data.callerCoarse parent,
        volume (data.selectedShading.carrier source) := by
  let actualParents :=
    Finset.univ.filter fun actual =>
      data.net.center actual = data.callerCenter parent
  let callerFiber :=
    wz2PaperFullFiberIndices
      data.selected.family data.callerCoarse parent
  have actualFibersDisjoint :
      ∀ first ∈ actualParents,
        ∀ second ∈ actualParents,
          first ≠ second →
            Disjoint
              (wz2PaperOrdinaryFullFiberIndices
                fine nearby.scaleData.coarse first)
              (wz2PaperOrdinaryFullFiberIndices
                fine nearby.scaleData.coarse second) := by
    intro first _ second _ hne
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have firstParent :
        nearby.scaleData.cover.parent source = first :=
      (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
        nearby.scaleData.rho_pos.le first source).mp hfirst
    have secondParent :
        nearby.scaleData.cover.parent source = second :=
      (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
        nearby.scaleData.rho_pos.le second source).mp hsecond
    exact hne (firstParent.symm.trans secondParent)
  have imageSum :
      (∑ source ∈ callerFiber,
          volume (data.selectedShading.carrier source)) =
        ∑ ambientSource ∈
            Finset.image data.selected.embedding callerFiber,
          volume (shading.carrier ambientSource) := by
    rw [Finset.sum_image data.selected.embedding.injective.injOn]
    rw [data.selectedShading_eq]
    rfl
  have unionSum :
      (∑ ambientSource ∈
          Finset.biUnion actualParents
            (wz2PaperOrdinaryFullFiberIndices
              fine nearby.scaleData.coarse),
          volume (shading.carrier ambientSource)) =
        ∑ actualParent ∈ actualParents,
          pureWZ2ActualFiberShadedMass
            shading actualParent := by
    rw [Finset.sum_biUnion actualFibersDisjoint]
    rfl
  rw [imageSum, data.complete_actual_fiber_union parent]
  rw [unionSum]
  rfl

theorem PureWZ2ParentQuotientNetSelectionData.sum_callerActualWeight
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    (∑ parent : Fin data.callerCoarse.card,
        data.callerActualWeight parent) =
      data.selectedShading.mass := by
  have fiberEq :
      ∀ parent : Fin data.callerCoarse.card,
        wz2PaperFullFiberIndices
            data.selected.family data.callerCoarse parent =
          data.callerCover.fiberIndices parent := by
    intro parent
    ext source
    simp only [mem_wz2PaperFullFiberIndices_iff,
      WZ1PaperTubeCover.fiberIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hcovered
      exact
        (data.callerCover.parent_unique
          source parent hcovered).symm
    · intro hparent
      rw [← hparent]
      exact data.callerCover.parent_covers source
  calc
    (∑ parent : Fin data.callerCoarse.card,
        data.callerActualWeight parent) =
        ∑ parent : Fin data.callerCoarse.card,
          ∑ source ∈
              wz2PaperFullFiberIndices
                data.selected.family data.callerCoarse parent,
            volume (data.selectedShading.carrier source) := by
      apply Finset.sum_congr rfl
      intro parent _
      exact data.callerActualWeight_eq_fiber_mass parent
    _ =
        ∑ parent : Fin data.callerCoarse.card,
          ∑ source ∈ data.callerCover.fiberIndices parent,
            volume (data.selectedShading.carrier source) := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [fiberEq parent]
    _ = data.selectedShading.mass := by
      change
        (∑ parent : Fin data.callerCoarse.card,
            ∑ source ∈ Finset.univ with
                data.callerCover.parent source = parent,
              volume (data.selectedShading.carrier source)) =
          ∑ source : Fin data.selected.family.card,
            volume (data.selectedShading.carrier source)
      exact
        Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ)
          (t := Finset.univ)
          (g := data.callerCover.parent)
          (fun _ _ => Finset.mem_univ _)
          (fun source =>
            volume (data.selectedShading.carrier source))

theorem PureWZ2ParentQuotientNetSelectionData.callerActualWeight_ne_top
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (parent : Fin data.callerCoarse.card) :
    data.callerActualWeight parent ≠ ⊤ := by
  rw [data.callerActualWeight_eq_fiber_mass parent]
  apply ENNReal.sum_ne_top.mpr
  intro source _
  have hle :
      volume (data.selectedShading.carrier source) ≤
        volume (Kakeya.Streamlined.axisBox 2 2 2) :=
    measure_mono <|
      (data.selectedShading.subset_body source).trans
        Set.inter_subset_right
  have hbox :
      volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
    rw [Kakeya.Streamlined.volume_axisBox
      2 2 2 (by norm_num) (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hbox hle

/-- Caller indices carrying positive complete-actual-fiber shaded mass. -/
def PureWZ2ParentQuotientNetSelectionData.positiveCallerParents
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    Finset (Fin data.callerCoarse.card) :=
  Finset.univ.filter fun parent =>
    data.callerActualWeight parent ≠ 0

/-- Fine indices whose quotient caller has positive total shaded mass. -/
def PureWZ2ParentQuotientNetSelectionData.positiveCallerFineIndices
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    Finset (Fin data.selected.family.card) :=
  Finset.univ.filter fun source =>
    data.callerCover.parent source ∈ data.positiveCallerParents

/-- Fine subfamily obtained by retaining every complete positive caller
fiber. -/
noncomputable def
    PureWZ2ParentQuotientNetSelectionData.positiveCallerFine
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    Kakeya.Streamlined.TubeSubfamily data.selected.family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    data.selected.family data.positiveCallerFineIndices

/-- The WZ caller cover restricted to positive caller classes. -/
noncomputable def
    PureWZ2ParentQuotientNetSelectionData.positiveCallerCover
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    WZ1PaperTubeCover
      data.positiveCallerFine.family
      (data.callerCover.hitParentSubfamily
        data.positiveCallerFine).family :=
  data.callerCover.restrictToHitParents data.positiveCallerFine

theorem PureWZ2ParentQuotientNetSelectionData.hitParentIndices_positiveCallerFine
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    data.callerCover.hitParentIndices
        data.positiveCallerFine =
      data.positiveCallerParents := by
  ext parent
  constructor
  · intro hparent
    rcases Finset.mem_image.mp hparent with
      ⟨source, _, hsource⟩
    have sourceMem :
        data.positiveCallerFine.embedding source ∈
          data.positiveCallerFineIndices :=
      Finset.orderEmbOfFin_mem
        data.positiveCallerFineIndices rfl source
    have parentPositive :
        data.callerCover.parent
            (data.positiveCallerFine.embedding source) ∈
          data.positiveCallerParents :=
      (Finset.mem_filter.mp sourceMem).2
    rwa [hsource] at parentPositive
  · intro hparent
    rcases data.callerCover.parent_surjective parent with
      ⟨source, hsource⟩
    have sourceMem :
        source ∈ data.positiveCallerFineIndices := by
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, hsource ▸ hparent⟩
    let positiveSource :
        Fin data.positiveCallerFine.family.card :=
      (data.positiveCallerFineIndices.orderIsoOfFin rfl).symm
        ⟨source, sourceMem⟩
    have positiveSourceEq :
        data.positiveCallerFine.embedding positiveSource =
          source :=
      congrArg Subtype.val
        (data.positiveCallerFineIndices.orderIsoOfFin rfl
          |>.apply_symm_apply ⟨source, sourceMem⟩)
    exact
      Finset.mem_image.mpr
        ⟨positiveSource, Finset.mem_univ positiveSource,
          by rw [positiveSourceEq, hsource]⟩

theorem PureWZ2ParentQuotientNetSelectionData.sum_positive_hitParent_weight
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    (∑ parent :
        Fin (data.callerCover.hitParentSubfamily
          data.positiveCallerFine).family.card,
      data.callerActualWeight
        ((data.callerCover.hitParentSubfamily
          data.positiveCallerFine).embedding parent)) =
      data.selectedShading.mass := by
  have hitEq :=
    data.hitParentIndices_positiveCallerFine
  change
    (∑ parent :
        Fin (data.callerCover.hitParentIndices
          data.positiveCallerFine).card,
      data.callerActualWeight
        ((data.callerCover.hitParentIndices
          data.positiveCallerFine).orderEmbOfFin rfl parent)) =
      data.selectedShading.mass
  rw [hitEq]
  calc
    (∑ parent : Fin data.positiveCallerParents.card,
      data.callerActualWeight
        (data.positiveCallerParents.orderEmbOfFin rfl parent)) =
        ∑ parent ∈ data.positiveCallerParents,
          data.callerActualWeight parent := by
      let equivalence :
          Fin data.positiveCallerParents.card ≃
            data.positiveCallerParents :=
        (data.positiveCallerParents.orderIsoOfFin rfl).toEquiv
      exact
        (Fintype.sum_equiv equivalence
          (fun parent : Fin data.positiveCallerParents.card =>
            data.callerActualWeight
              (data.positiveCallerParents.orderEmbOfFin rfl parent))
          (fun parent : data.positiveCallerParents =>
            data.callerActualWeight parent.1)
          (fun _ => rfl)).trans
          (Finset.sum_coe_sort data.positiveCallerParents
            data.callerActualWeight)
    _ = data.selectedShading.mass := by
      rw [← data.sum_callerActualWeight]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro parent _ hparent
      have hzero :
          ¬data.callerActualWeight parent ≠ 0 := by
        simpa [
          PureWZ2ParentQuotientNetSelectionData.positiveCallerParents
        ] using hparent
      exact not_ne_iff.mp hzero

/--
The positive caller support is nonempty, preserves selected shaded mass
exactly, and every retained caller has positive finite class weight.
-/
structure PureWZ2PositiveCallerSupportData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) where
  positiveCallerParents_nonempty :
    quotient.positiveCallerParents.Nonempty
  positiveFine_nonempty :
    quotient.positiveCallerFine.family.Nonempty
  positiveShading :
    WZ1PaperTubeShading quotient.positiveCallerFine.family
  positiveShading_eq :
    positiveShading =
      restrictPaperShading
        quotient.positiveCallerFine quotient.selectedShading
  mass_eq :
    positiveShading.mass = quotient.selectedShading.mass
  hitParent_ambient_positive :
    ∀ parent :
        Fin (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family.card,
      quotient.callerActualWeight
          ((quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).embedding parent) ≠ 0
  hitParent_weight_ne_top :
    ∀ parent :
        Fin (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family.card,
      quotient.callerActualWeight
          ((quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).embedding parent) ≠ ⊤

theorem positive_caller_support
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (selectedMassPos : 0 < quotient.selectedShading.mass) :
    Nonempty (PureWZ2PositiveCallerSupportData quotient) := by
  let positiveParents := quotient.positiveCallerParents
  let positiveFineIndices := quotient.positiveCallerFineIndices
  let positiveFine := quotient.positiveCallerFine
  let positiveShading :=
    restrictPaperShading positiveFine quotient.selectedShading
  have positiveWeightSum :
      (∑ parent ∈ positiveParents,
          quotient.callerActualWeight parent) =
        quotient.selectedShading.mass := by
    rw [← quotient.sum_callerActualWeight]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro parent _ hparent
    have hzero :
        ¬quotient.callerActualWeight parent ≠ 0 := by
      simpa [positiveParents,
        PureWZ2ParentQuotientNetSelectionData.positiveCallerParents]
        using hparent
    exact not_ne_iff.mp hzero
  have positiveParentsNonempty :
      positiveParents.Nonempty := by
    by_contra hnonempty
    have hempty : positiveParents = ∅ := by
      simpa using hnonempty
    rw [hempty] at positiveWeightSum
    simp only [Finset.sum_empty] at positiveWeightSum
    exact
      (not_le_of_gt selectedMassPos)
        positiveWeightSum.symm.le
  have positiveFineNonempty :
      positiveFine.family.Nonempty := by
    rcases positiveParentsNonempty with
      ⟨parent, hparent⟩
    rcases quotient.callerCover.parent_surjective parent with
      ⟨source, hsource⟩
    have sourceMem :
        source ∈ positiveFineIndices := by
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, hsource ▸ hparent⟩
    let selectedSource : Fin positiveFine.family.card :=
      (positiveFineIndices.orderIsoOfFin rfl).symm
        ⟨source, sourceMem⟩
    exact Fin.pos_iff_nonempty.mpr ⟨selectedSource⟩
  have positiveMass :
      positiveShading.mass =
        quotient.selectedShading.mass := by
    rw [restrictPaperShading_mass]
    let equivalence :
        Fin positiveFine.family.card ≃ positiveFineIndices :=
      (positiveFineIndices.orderIsoOfFin rfl).toEquiv
    calc
      (∑ source : Fin positiveFine.family.card,
          volume
            (quotient.selectedShading.carrier
              (positiveFine.embedding source))) =
          ∑ source : positiveFineIndices,
            volume
              (quotient.selectedShading.carrier source.1) := by
        exact
          Fintype.sum_equiv equivalence
            (fun source : Fin positiveFine.family.card =>
              volume
                (quotient.selectedShading.carrier
                  (positiveFine.embedding source)))
            (fun source : positiveFineIndices =>
              volume
                (quotient.selectedShading.carrier source.1))
            (fun _ => rfl)
      _ =
          ∑ source ∈ positiveFineIndices,
            volume
              (quotient.selectedShading.carrier source) := by
        exact
          Finset.sum_coe_sort positiveFineIndices
            (fun source =>
              volume
                (quotient.selectedShading.carrier source))
      _ =
          ∑ source : Fin quotient.selected.family.card,
            volume
              (quotient.selectedShading.carrier source) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro source _ hsource
        have parentNotPositive :
            quotient.callerCover.parent source ∉
              positiveParents := by
          change
            source ∉
              Finset.univ.filter fun current =>
                quotient.callerCover.parent current ∈
                  positiveParents at hsource
          simpa using hsource
        have parentWeightZero :
            quotient.callerActualWeight
                (quotient.callerCover.parent source) = 0 := by
          have hnot :
              ¬quotient.callerActualWeight
                  (quotient.callerCover.parent source) ≠ 0 := by
            intro hpositive
            apply parentNotPositive
            change
              quotient.callerCover.parent source ∈
                Finset.univ.filter fun parent =>
                  quotient.callerActualWeight parent ≠ 0
            exact
              Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, hpositive⟩
          exact not_ne_iff.mp hnot
        have sourceMem :
            source ∈
              wz2PaperFullFiberIndices
                quotient.selected.family quotient.callerCoarse
                (quotient.callerCover.parent source) :=
          (mem_wz2PaperFullFiberIndices_iff
            (quotient.callerCover.parent source) source).mpr
            (quotient.callerCover.parent_covers source)
        have sourceLe :
            volume (quotient.selectedShading.carrier source) ≤
              quotient.callerActualWeight
                (quotient.callerCover.parent source) := by
          rw [quotient.callerActualWeight_eq_fiber_mass]
          exact
            Finset.single_le_sum
              (fun current _ =>
                show (0 : ENNReal) ≤
                    volume
                      (quotient.selectedShading.carrier current)
                  from zero_le)
              sourceMem
        have sourceLeZero :
            volume (quotient.selectedShading.carrier source) ≤ 0 :=
          sourceLe.trans_eq parentWeightZero
        exact nonpos_iff_eq_zero.mp sourceLeZero
      _ = quotient.selectedShading.mass := rfl
  have hitParentPositive :
      ∀ parent :
          Fin (quotient.callerCover.hitParentSubfamily
            positiveFine).family.card,
        quotient.callerActualWeight
            ((quotient.callerCover.hitParentSubfamily
              positiveFine).embedding parent) ≠ 0 := by
    intro parent
    rcases
        quotient.callerCover.hitParent_surjective
          positiveFine parent
      with
      ⟨source, hsource⟩
    have sourceMem :
        positiveFine.embedding source ∈
          positiveFineIndices :=
      Finset.orderEmbOfFin_mem positiveFineIndices rfl source
    have sourceParentPositive :
        quotient.callerCover.parent
            (positiveFine.embedding source) ∈
          positiveParents :=
      (Finset.mem_filter.mp sourceMem).2
    have ambientParent :
        (quotient.callerCover.hitParentSubfamily
          positiveFine).embedding parent =
          quotient.callerCover.parent
            (positiveFine.embedding source) := by
      rw [← quotient.callerCover.hitParent_ambient
        positiveFine source, hsource]
    rw [ambientParent]
    exact
      (Finset.mem_filter.mp sourceParentPositive).2
  exact
    ⟨{
      positiveCallerParents_nonempty :=
        positiveParentsNonempty
      positiveFine_nonempty := positiveFineNonempty
      positiveShading := positiveShading
      positiveShading_eq := rfl
      mass_eq := positiveMass
      hitParent_ambient_positive := hitParentPositive
      hitParent_weight_ne_top := fun parent =>
        quotient.callerActualWeight_ne_top
          ((quotient.callerCover.hitParentSubfamily
            positiveFine).embedding parent)
    }⟩

end Kakeya.Assouad

end

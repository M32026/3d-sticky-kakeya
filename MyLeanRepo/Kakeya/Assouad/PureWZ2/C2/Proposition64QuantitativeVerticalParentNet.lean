import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalColoredParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedRelabelParent

/-!
# Target parent nets for quantitative vertical selection

The final Proposition 6.4 family is netted directly in its paper-line metric.
The only remaining geometric input is the scale-covariant two-parameter
packing estimate for separated subsets of this exact family.  Coarse tubes,
owners, and their containment are constructed here and are not input data.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The maximal quotient-net construction also works at radius zero when the
distance between distinct indices is positive. -/
private theorem finiteMaximalQuotientNet_nonnegative
    (indexCount : ℕ)
    (indexCountPos : 0 < indexCount)
    (distance : Fin indexCount → Fin indexCount → ℝ)
    (distanceSymmetric : ∀ first second,
      distance first second = distance second first)
    (distanceSelf : ∀ index, distance index index = 0)
    (distancePositive : ∀ first second, first ≠ second →
      0 < distance first second)
    (radius : ℝ)
    (radiusNonnegative : 0 ≤ radius) :
    Nonempty (WZ2FiniteMaximalQuotientNetData
      indexCount distance radius) := by
  rcases eq_or_lt_of_le radiusNonnegative with rfl | radiusPos
  · let centers : Finset (Fin indexCount) := Finset.univ
    let centerEmbedding : Fin centers.card ↪ Fin indexCount :=
      (centers.orderEmbOfFin rfl).toEmbedding
    have centerEmbeddingSurjective : Function.Surjective centerEmbedding := by
      intro index
      let member : centers := ⟨index, Finset.mem_univ index⟩
      let source : Fin centers.card :=
        (centers.orderIsoOfFin rfl).symm member
      refine ⟨source, ?_⟩
      exact congrArg Subtype.val
        ((centers.orderIsoOfFin rfl).apply_symm_apply member)
    let center : Fin indexCount → Fin centers.card :=
      fun index => Classical.choose (centerEmbeddingSurjective index)
    have center_eq : ∀ index, centerEmbedding (center index) = index :=
      fun index => Classical.choose_spec (centerEmbeddingSurjective index)
    refine ⟨{
      centers := centers
      centers_nonempty := by
        exact ⟨⟨0, indexCountPos⟩, Finset.mem_univ _⟩
      centerEmbedding := centerEmbedding
      centerEmbedding_eq := rfl
      centers_separated := ?_
      center := center
      center_close := ?_
      center_fixed := ?_
      center_surjective := ?_
    }⟩
    · intro first second hne
      exact distancePositive _ _
        (centerEmbedding.injective.ne hne)
    · intro index
      rw [center_eq, distanceSelf]
    · intro centerIndex
      apply centerEmbedding.injective
      rw [center_eq]
    · intro centerIndex
      exact ⟨centerEmbedding centerIndex, by
        apply centerEmbedding.injective
        rw [center_eq]⟩
  · exact wz2_finite_maximal_quotient_net indexCount indexCountPos
      distance distanceSymmetric distanceSelf radius radiusPos

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

private noncomputable abbrev fineFamily :=
  (initialED quantitativeOutput geometry frostman).subfamily.family

/-- Available line-distance budget for assigning a fine tube to a parent of
radius `rho`. -/
def quantitativeVerticalParentNetRadius
    (coordinate : Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount) : ℝ :=
  (2 / 3 : ℝ) *
    (((quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).requested coordinate).1 -
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta)

/-- Missing two-dimensional geometry, stated before any net is selected:
each target tube receives a finite slope/axis bin, equal bins force line
closeness, and the number of bins has the required `rho⁻²` bound. -/
structure QuantitativeVerticalTargetTwoParameterReceipt where
  Bin :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → Type
  binFintype : ∀ coordinate, Fintype (Bin coordinate)
  binDecidableEq : ∀ coordinate, DecidableEq (Bin coordinate)
  bin :
    ∀ coordinate,
      Fin (fineFamily quantitativeOutput geometry frostman).card →
        Bin coordinate
  same_bin_close :
    ∀ coordinate first second,
      bin coordinate first = bin coordinate second →
        first = second ∨
          wz1PaperLineDistance
              ((fineFamily quantitativeOutput geometry frostman).tube first)
              ((fineFamily quantitativeOutput geometry frostman).tube second) ≤
            quantitativeVerticalParentNetRadius
              quantitativeOutput geometry floor coordinate
  packingConstant :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ENNReal
  bin_count :
    ∀ coordinate,
      (Fintype.card (Bin coordinate) : ENNReal) ≤
        packingConstant coordinate *
          (Kakeya.realRpowENN
            ((quantitativeVerticalRequestedScaleSchedule
              quantitativeOutput geometry floor).requested coordinate).1 2)⁻¹
  distinct_line :
    ∀ first second : Fin (fineFamily
      quantitativeOutput geometry frostman).card,
      first ≠ second →
        0 < wz1PaperLineDistance
          ((fineFamily quantitativeOutput geometry frostman).tube first)
          ((fineFamily quantitativeOutput geometry frostman).tube second)
  assigned_containment :
    ∀ coordinate first second,
      wz1PaperLineDistance
          ((fineFamily quantitativeOutput geometry frostman).tube first)
          ((fineFamily quantitativeOutput geometry frostman).tube second) ≤
        quantitativeVerticalParentNetRadius
          quantitativeOutput geometry floor coordinate →
      ((fineFamily quantitativeOutput geometry frostman).tube first).carrier ⊆
        (wz2PaperRelabelTube
          (targetScale :=
            ((quantitativeVerticalRequestedScaleSchedule
              quantitativeOutput geometry floor).requested coordinate).1)
          ((fineFamily quantitativeOutput geometry frostman).tube second)).carrier

/-- The sole unresolved geometric estimate: every separated subset of the
exact initial ED family obeys the two-parameter `rho⁻²` packing bound.
It contains no family construction, parent assignment, or target cover. -/
structure QuantitativeVerticalTargetLinePackingReceipt where
  packingConstant :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ENNReal
  packed :
    ∀ coordinate
      (indices : Finset (Fin (fineFamily
        quantitativeOutput geometry frostman).card)),
      (∀ first ∈ indices, ∀ second ∈ indices, first ≠ second →
        quantitativeVerticalParentNetRadius
            quantitativeOutput geometry floor coordinate <
          wz1PaperLineDistance
            ((fineFamily quantitativeOutput geometry frostman).tube first)
            ((fineFamily quantitativeOutput geometry frostman).tube second)) →
      (indices.card : ENNReal) ≤
        packingConstant coordinate *
          (Kakeya.realRpowENN
            ((quantitativeVerticalRequestedScaleSchedule
              quantitativeOutput geometry floor).requested coordinate).1 2)⁻¹
  distinct_line :
    ∀ first second : Fin (fineFamily
      quantitativeOutput geometry frostman).card,
      first ≠ second →
        0 < wz1PaperLineDistance
          ((fineFamily quantitativeOutput geometry frostman).tube first)
          ((fineFamily quantitativeOutput geometry frostman).tube second)
  assigned_containment :
    ∀ coordinate first second,
      wz1PaperLineDistance
          ((fineFamily quantitativeOutput geometry frostman).tube first)
          ((fineFamily quantitativeOutput geometry frostman).tube second) ≤
        quantitativeVerticalParentNetRadius
          quantitativeOutput geometry floor coordinate →
      ((fineFamily quantitativeOutput geometry frostman).tube first).carrier ⊆
        (wz2PaperRelabelTube
          (targetScale :=
            ((quantitativeVerticalRequestedScaleSchedule
              quantitativeOutput geometry floor).requested coordinate).1)
          ((fineFamily quantitativeOutput geometry frostman).tube second)).carrier

namespace QuantitativeVerticalTargetLinePackingReceipt

/-- A genuine two-parameter binning supplies separated-set packing without
assuming a net, parent assignment, or cover. -/
noncomputable def ofTwoParameter
    (data : QuantitativeVerticalTargetTwoParameterReceipt
      quantitativeOutput geometry frostman floor) :
    QuantitativeVerticalTargetLinePackingReceipt
      quantitativeOutput geometry frostman floor := by
  letI : ∀ coordinate, Fintype (data.Bin coordinate) :=
    data.binFintype
  letI : ∀ coordinate, DecidableEq (data.Bin coordinate) :=
    data.binDecidableEq
  refine {
    packingConstant := data.packingConstant
    packed := ?_
    distinct_line := data.distinct_line
    assigned_containment := data.assigned_containment
  }
  intro coordinate indices hseparated
  let encoding : indices ↪ data.Bin coordinate := {
    toFun := fun index => data.bin coordinate index
    inj' := by
      intro first second heq
      apply Subtype.ext
      rcases data.same_bin_close coordinate first second heq with
        hsame | hclose
      · exact hsame
      · by_contra hne
        exact (not_lt_of_ge hclose)
          (hseparated first first.property second second.property hne)
  }
  have hcard :
      indices.card ≤ Fintype.card (data.Bin coordinate) := by
    simpa using Fintype.card_le_of_injective encoding encoding.injective
  have hcardENN :
      (indices.card : ENNReal) ≤
        (Fintype.card (data.Bin coordinate) : ENNReal) := by
    exact_mod_cast hcard
  exact hcardENN.trans (data.bin_count coordinate)

/-- Construct every target parent family and owner map internally from the
maximal line net, then discharge its count using the packing receipt. -/
theorem exists_rawParentNet
    (packing : QuantitativeVerticalTargetLinePackingReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalRawParentNetReceipt
      quantitativeOutput geometry frostman floor) := by
  let schedule := quantitativeVerticalRequestedScaleSchedule
    quantitativeOutput geometry floor
  let fine := fineFamily quantitativeOutput geometry frostman
  have fineNonempty : fine.Nonempty := by
    let ed := initialED quantitativeOutput geometry frostman
    have hmass : 0 < ed.finalShading.mass := by
      have hright : 0 <
          (quantitativeVerticalPaperEDLoss quantitativeOutput geometry + 1) *
            ed.finalShading.mass :=
        geometry.cleanup_finalShading_mass_pos.trans_le ed.mass_retention
      by_contra hzero
      rw [not_lt, nonpos_iff_eq_zero] at hzero
      simp [hzero] at hright
    change 0 < ∑ index, MeasureTheory.volume (ed.finalShading.carrier index) at hmass
    rw [Finset.sum_pos_iff] at hmass
    rcases hmass with ⟨index, _, _⟩
    change 0 < ed.subfamily.family.card
    have hi := index.isLt
    exact lt_of_le_of_lt (Nat.zero_le index.val) hi
  have netRadiusNonnegative :
      ∀ coordinate, 0 ≤ quantitativeVerticalParentNetRadius
        quantitativeOutput geometry floor coordinate := by
    intro coordinate
    unfold quantitativeVerticalParentNetRadius
    have hlower := (schedule.requested coordinate).2.1
    positivity
  let net : ∀ coordinate,
      WZ2FiniteMaximalQuotientNetData fine.card
        (fun first second =>
          wz1PaperLineDistance (fine.tube first) (fine.tube second))
        (quantitativeVerticalParentNetRadius
          quantitativeOutput geometry floor coordinate) :=
    fun coordinate => Classical.choice <|
      finiteMaximalQuotientNet_nonnegative fine.card fineNonempty
        (fun first second =>
          wz1PaperLineDistance (fine.tube first) (fine.tube second))
        (fun _ _ => wz1PaperLineDistance_symm _ _)
        (fun index => by
          have directionNe : wz1PaperDirection (fine.tube index) ≠ 0 := by
            intro hzero
            have hnorm := wz1PaperDirection_norm (fine.tube index)
            rw [hzero, norm_zero] at hnorm
            norm_num at hnorm
          simp [wz1PaperLineDistance,
            InnerProductGeometry.angle_self directionNe])
        packing.distinct_line
        _ (netRadiusNonnegative coordinate)
  let coarse : ∀ coordinate,
      Kakeya.Streamlined.TubeFamily (schedule.requested coordinate).1 :=
    fun coordinate => {
      card := (net coordinate).centers.card
      tube := fun parent =>
        wz2PaperRelabelTube
          (targetScale := (schedule.requested coordinate).1)
          (fine.tube ((net coordinate).centerEmbedding parent))
    }
  refine ⟨{
    actualScale := fun coordinate => (schedule.requested coordinate).1
    actualScale_pos := fun coordinate =>
      geometry.scales.finalDelta_pos.trans_le
        (schedule.requested coordinate).2.1
    coarse := coarse
    parent := fun coordinate source => (net coordinate).center source
    parent_covers := ?_
    parentCountConstant := packing.packingConstant
    parentCount := ?_
    rounding := schedule.rounding
  }⟩
  · intro coordinate source
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact packing.assigned_containment coordinate source
      ((net coordinate).centerEmbedding ((net coordinate).center source))
      ((net coordinate).center_close source)
  · intro coordinate
    change ((net coordinate).centers.card : ENNReal) ≤ _
    apply packing.packed coordinate (net coordinate).centers
    intro first hfirst second hsecond hne
    let firstIndex : Fin (net coordinate).centers.card :=
      (net coordinate).centers.orderIsoOfFin rfl |>.symm ⟨first, hfirst⟩
    let secondIndex : Fin (net coordinate).centers.card :=
      (net coordinate).centers.orderIsoOfFin rfl |>.symm ⟨second, hsecond⟩
    have hfirst :
        (net coordinate).centerEmbedding firstIndex = first := by
      rw [(net coordinate).centerEmbedding_eq]
      exact congrArg Subtype.val
        ((net coordinate).centers.orderIsoOfFin rfl
          |>.apply_symm_apply ⟨first, hfirst⟩)
    have hsecond :
        (net coordinate).centerEmbedding secondIndex = second := by
      rw [(net coordinate).centerEmbedding_eq]
      exact congrArg Subtype.val
        ((net coordinate).centers.orderIsoOfFin rfl
          |>.apply_symm_apply ⟨second, hsecond⟩)
    have hindexNe : firstIndex ≠ secondIndex := by
      intro heq
      apply hne
      rw [← hfirst, ← hsecond, heq]
    simpa only [hfirst, hsecond] using
      (net coordinate).centers_separated firstIndex secondIndex hindexNe

/-- The geometric packing leaf now feeds the already-closed simultaneous
colored weighted selector without exposing a net, owner map, or coarse family
at the producer boundary. -/
theorem exists_jointSelection
    (packing : QuantitativeVerticalTargetLinePackingReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) := by
  rcases packing.exists_rawParentNet with ⟨net⟩
  exact QuantitativeVerticalRawColoredParentReceipt.selectOfParentNet
    quantitativeOutput geometry frostman floor net

/-- Active geometric boundary: a two-parameter target discretization closes
the parent net and the same-witness joint selection. -/
theorem exists_jointSelection_ofTwoParameter
    (data : QuantitativeVerticalTargetTwoParameterReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) :=
  exists_jointSelection quantitativeOutput geometry frostman floor
    (ofTwoParameter quantitativeOutput geometry frostman floor data)

end QuantitativeVerticalTargetLinePackingReceipt

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end

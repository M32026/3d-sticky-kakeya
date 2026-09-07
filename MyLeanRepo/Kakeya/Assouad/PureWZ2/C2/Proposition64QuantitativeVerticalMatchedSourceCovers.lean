import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalParentNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64P7ScaleSchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Matched source covers for Proposition 6.4 vertical selection

This module chooses Definition 2.12 witnesses from the quantitative source
hierarchy and restricts them to the exact source indices retained by the
initial Proposition 6.4 paper-ED family.  It deliberately stops before the
one-direction affine/retubing carrier estimate.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : Grid)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

private noncomputable abbrev schedule :=
  quantitativeVerticalRequestedScaleScheduleFor quantitativeOutput geometry floor

/-- Fixed scale distortion budget reserved for the forward affine/retubing
carrier estimate.  Keeping it explicit ensures that nearby-scale rounding,
rather than a false equality of scales, pays for transport. -/
def quantitativeVerticalSourceTransportScaleFactor : ℝ :=
  120045 * pureWZ2Proposition64Lemma35Scale

theorem quantitativeVerticalSourceTransportScaleFactor_one_le
    (hscale : 1 ≤ pureWZ2Proposition64Lemma35Scale) :
    1 ≤ quantitativeVerticalSourceTransportScaleFactor := by
  unfold quantitativeVerticalSourceTransportScaleFactor
  nlinarith

/-- Source requested scale matched to a target-net coordinate.  The maximum
with `sourceDelta` is essential near the bottom scale. -/
def quantitativeVerticalMatchedSourceRequested
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ2PaperRequestedScale sourceDelta := by
  let rho := max sourceDelta
    (((schedule quantitativeOutput geometry floor).requested coordinate).1 /
      quantitativeVerticalSourceTransportScaleFactor)
  refine ⟨rho, ?_, ?_⟩
  · exact le_max_left _ _
  · have htarget :=
      ((schedule quantitativeOutput geometry floor).requested coordinate).2.2
    have hfactor :=
      quantitativeVerticalSourceTransportScaleFactor_one_le
        geometry.scales.scale_one
    have hfactorPos : 0 < quantitativeVerticalSourceTransportScaleFactor :=
      lt_of_lt_of_le zero_lt_one hfactor
    have hquot :
        ((schedule quantitativeOutput geometry floor).requested coordinate).1 /
            quantitativeVerticalSourceTransportScaleFactor ≤ 1 := by
      apply (div_le_one hfactorPos).2
      exact htarget.trans hfactor
    exact max_le quantitativeOutput.normalized.source.extremal.delta_le_one hquot

/-- Both branches of the matched source request are bounded by the target
grid scale divided by the exact final isotropic scale factor. -/
theorem quantitativeVerticalMatchedSourceRequested_le_target
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    (quantitativeVerticalMatchedSourceRequested
        quantitativeOutput geometry floor coordinate).1 ≤
      (schedule quantitativeOutput geometry floor).requested coordinate /
        (45 * pureWZ2Proposition64Lemma35Scale) := by
  let target :=
    ((schedule quantitativeOutput geometry floor).requested coordinate).1
  have hscalePos : 0 < pureWZ2Proposition64Lemma35Scale :=
    pureWZ2Proposition64Lemma35Scale_pos
  have hfinalFactorPos :
      0 < 45 * pureWZ2Proposition64Lemma35Scale := by positivity
  have htransportFactorPos :
      0 < quantitativeVerticalSourceTransportScaleFactor := by
    unfold quantitativeVerticalSourceTransportScaleFactor
    positivity
  have htargetPos : 0 < target :=
    lt_of_lt_of_le geometry.scales.finalDelta_pos
      ((schedule quantitativeOutput geometry floor).requested coordinate).2.1
  have hsource :
      sourceDelta ≤ target /
        (45 * pureWZ2Proposition64Lemma35Scale) := by
    rw [le_div_iff₀ hfinalFactorPos]
    simpa [target, pureWZ2Proposition64Lemma35FinalDelta, mul_assoc,
      mul_left_comm, mul_comm] using
      ((schedule quantitativeOutput geometry floor).requested coordinate).2.1
  have hquotient :
      target / quantitativeVerticalSourceTransportScaleFactor ≤
        target / (45 * pureWZ2Proposition64Lemma35Scale) := by
    rw [div_le_div_iff₀ htransportFactorPos hfinalFactorPos]
    unfold quantitativeVerticalSourceTransportScaleFactor
    nlinarith [geometry.scales.scale_one]
  change max sourceDelta
      (target / quantitativeVerticalSourceTransportScaleFactor) ≤ _
  exact max_le hsource hquotient

/-- The actual nearby source witness selected by the hierarchy ledger. -/
noncomputable def quantitativeVerticalMatchedSourceNearby
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ2PaperPureNearbyScaleCoverData
      quantitativeOutput.normalized.source.family
      (quantitativeVerticalMatchedSourceRequested
        quantitativeOutput geometry floor coordinate)
      (Kakeya.realRpowENN sourceDelta
        (-quantitativeOutput.normalized.inputLoss)) :=
  Classical.choice
    (quantitativeOutput.normalized.source.extremal.cwa_nearby_scales.2.2.2
      (quantitativeVerticalMatchedSourceRequested
        quantitativeOutput geometry floor coordinate))

/-- The actual source witness remains below the target grid scale with only
the original source nearby-CWA power loss. -/
theorem quantitativeVerticalMatchedSourceNearby_rho_lt_target
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    (quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor coordinate).rho <
      Real.rpow sourceDelta (-quantitativeOutput.normalized.inputLoss) *
        ((schedule quantitativeOutput geometry floor).requested coordinate /
          (45 * pureWZ2Proposition64Lemma35Scale)) := by
  let nearby :=
    quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate
  let requested :=
    quantitativeVerticalMatchedSourceRequested
      quantitativeOutput geometry floor coordinate
  have hrightTop :
      Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss) *
          ENNReal.ofReal requested.1 ≠ ⊤ :=
    ENNReal.mul_ne_top
      (by simp [Kakeya.realRpowENN])
      ENNReal.ofReal_ne_top
  have hreal :=
    (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hrightTop).mpr
      nearby.within_factor
  have hsourceRho : 0 < nearby.rho := nearby.scaleData.rho_pos
  have hrequestedPos : 0 < requested.1 :=
    lt_of_lt_of_le
      quantitativeOutput.normalized.source.extremal.delta_pos requested.2.1
  rw [ENNReal.toReal_mul,
    Subunit.realRpowENN_toReal
      quantitativeOutput.normalized.source.extremal.delta_pos] at hreal
  have hreal' :
      nearby.rho <
        Real.rpow sourceDelta (-quantitativeOutput.normalized.inputLoss) *
          requested.1 := by
    simpa [nearby, requested, Kakeya.realRpowENN,
      ENNReal.toReal_ofReal, hsourceRho.le, hrequestedPos.le,
      Real.rpow_pos_of_pos
        quantitativeOutput.normalized.source.extremal.delta_pos] using hreal
  exact hreal'.trans_le <|
    mul_le_mul_of_nonneg_left
      (quantitativeVerticalMatchedSourceRequested_le_target
        quantitativeOutput geometry floor coordinate)
      (Real.rpow_nonneg
        quantitativeOutput.normalized.source.extremal.delta_pos.le _)

/-- Exact source packet indexed by the same indices as the initial paper-ED
family; its embedding is the construction-aware final source embedding. -/
noncomputable def quantitativeVerticalExactSourcePacket :
    WZ2PaperPureTubeSubfamily
      quantitativeOutput.normalized.source.family where
  family := {
    card := (initialED quantitativeOutput geometry frostman).subfamily.family.card
    tube := fun index =>
      quantitativeOutput.normalized.source.family.tube
        (geometry.finalSourceEmbedding
          (initialED quantitativeOutput geometry frostman) index)
  }
  embedding :=
    geometry.finalSourceEmbedding
      (initialED quantitativeOutput geometry frostman)
  tube_eq := fun _ => rfl

/-- Restrict the chosen source cover to exactly the retained source packet.
Its parent type is definitionally the finite hit-parent subtype, with the
embedding back to the hierarchy coarse family retained by the construction. -/
noncomputable def quantitativeVerticalRestrictedSourceCover
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ2PaperPurePartitioningCover
      (quantitativeVerticalExactSourcePacket
        quantitativeOutput geometry frostman).family
      ((quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor coordinate).scaleData.cover
          |>.hitParentSubfamily
            (quantitativeVerticalExactSourcePacket
              quantitativeOutput geometry frostman)).family :=
  (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate).scaleData.cover
    |>.restrictToHitParents
      (quantitativeVerticalExactSourcePacket
        quantitativeOutput geometry frostman)

/-- The source-side datum absent from `WZ2PaperPureScaleCoverData`: a
cardinality estimate for the *ambient source coarse family*.  This is
strictly upstream of target transport, coloring, and selection. -/
structure QuantitativeVerticalSourceParentPackingReceipt : Prop where
  parentCount :
    ∀ coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount,
      (quantitativeVerticalMatchedSourceNearby
          quantitativeOutput geometry floor coordinate).scaleData.coarse.enncard ≤
        Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss) *
          (Kakeya.realRpowENN
            (quantitativeVerticalMatchedSourceNearby
              quantitativeOutput geometry floor coordinate).rho 2)⁻¹

/-- Restriction cannot create parents, so a source-side packing theorem
immediately transfers to the exact hit-parent subtype. -/
theorem quantitativeVertical_restrictedSource_parentCount
    (packing : QuantitativeVerticalSourceParentPackingReceipt
      quantitativeOutput geometry floor)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    (((quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor coordinate).scaleData.cover
          |>.hitParentSubfamily
            (quantitativeVerticalExactSourcePacket
              quantitativeOutput geometry frostman)).family.enncard) ≤
      Kakeya.realRpowENN sourceDelta
          (-quantitativeOutput.normalized.inputLoss) *
        (Kakeya.realRpowENN
          (quantitativeVerticalMatchedSourceNearby
            quantitativeOutput geometry floor coordinate).rho 2)⁻¹ := by
  let nearby :=
    quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate
  let packet :=
    quantitativeVerticalExactSourcePacket
      quantitativeOutput geometry frostman
  have hcard :
      (nearby.scaleData.cover.hitParentSubfamily packet).family.card ≤
        nearby.scaleData.coarse.card :=
    by
      simpa using Fintype.card_le_of_injective
        (nearby.scaleData.cover.hitParentSubfamily packet).embedding
        (nearby.scaleData.cover.hitParentSubfamily packet).embedding.injective
  have henncard :
      (nearby.scaleData.cover.hitParentSubfamily packet).family.enncard ≤
        nearby.scaleData.coarse.enncard := by
    change
      ((nearby.scaleData.cover.hitParentSubfamily packet).family.card : ENNReal) ≤
        (nearby.scaleData.coarse.card : ENNReal)
    exact_mod_cast hcard
  exact henncard.trans (packing.parentCount coordinate)

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end

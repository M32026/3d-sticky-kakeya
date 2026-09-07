import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64LocalizedEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64OuterJohnInverseVolume

/-!
# Actual-John fiber CWA from target top-level CWA

For a uniform public partitioning cover, the number of coarse parents and
the parent outer-John Jacobian carry reciprocal `rho^2` factors.  They cancel,
leaving a dimensionless parentwise actual-John CWA constant.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Convert top-level normalized CWA into canonical actual-John CWA on one
complete strict full fiber. -/
theorem pureWZ2Proposition64_pure_fullFiber_cwa_of_topLevel
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hfineNonempty : fine.Nonempty)
    (hrho : 0 < rho)
    {topConstant fiberConstant parentCountConstant
      johnVolumeConstant envelopeConstant outputConstant : ENNReal}
    (htop : WZ2PaperConvexWolffBound fine topConstant)
    (huniform : WZ2PaperPureFullFibersAreCUniform
      fine coarse fiberConstant)
    (hparentCount :
      coarse.enncard ≤ parentCountConstant *
        (Kakeya.realRpowENN rho 2)⁻¹)
    (hjohnVolume :
      ∀ parent : Fin coarse.card,
        let normalization :=
          WZ2PaperAssouadUnitRescalingData.ofTube
            (coarse.tube parent) hrho
        ∀ targetSet : Set Point3,
          volume (normalization.map.symm '' targetSet) ≤
            johnVolumeConstant * Kakeya.realRpowENN rho 2 *
              volume targetSet)
    (commonEnvelope :
      ∀ parent : Fin coarse.card,
        ∀ sourceSet : Set Point3, Convex ℝ sourceSet →
          ∃ paperSet : Set Point3,
            Convex ℝ paperSet ∧
              volume paperSet ≤
                envelopeConstant * volume sourceSet ∧
              ∀ source : Fin fine.card,
                source ∈
                    wz2PaperOrdinaryFullFiberIndices fine coarse parent →
                  (fine.tube source).carrier ⊆ sourceSet →
                    wz1PaperTubeCarrier (fine.tube source) ⊆ paperSet)
    (hbudget : fiberConstant * parentCountConstant *
        johnVolumeConstant * envelopeConstant * topConstant ≤
          outputConstant)
    (parent : Fin coarse.card) :
    Nonempty (WZ2PaperPureUnitRescaledFullFiberData
      (fine := fine) (coarse := coarse) parent outputConstant) := by
  let normalization := WZ2PaperAssouadUnitRescalingData.ofTube
    (coarse.tube parent) hrho
  let bodyFamily := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := fine) (coarse := coarse) parent normalization
  have hparentNonempty :
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent).Nonempty :=
    cover.fullFiber_nonempty_of_uniform hfineNonempty huniform parent
  have hfiberPos : 0 < wz2PaperOrdinaryFullFiberCount fine coarse parent := by
    rw [wz2PaperOrdinaryFullFiberCount]
    exact_mod_cast Finset.card_pos.mpr hparentNonempty
  have hfiberTop : wz2PaperOrdinaryFullFiberCount fine coarse parent ≠ ⊤ := by
    simp [wz2PaperOrdinaryFullFiberCount]
  have htotal : fine.enncard ≤
      coarse.enncard * fiberConstant *
        wz2PaperOrdinaryFullFiberCount fine coarse parent := by
    have hsum := cover.sum_fullFiberCount hrho.le
    calc
      fine.enncard = ∑ other : Fin coarse.card,
          wz2PaperOrdinaryFullFiberCount fine coarse other := hsum.symm
      _ ≤ ∑ _other : Fin coarse.card,
          fiberConstant *
            wz2PaperOrdinaryFullFiberCount fine coarse parent := by
        exact Finset.sum_le_sum fun other _ => huniform other parent
      _ = coarse.enncard * fiberConstant *
          wz2PaperOrdinaryFullFiberCount fine coarse parent := by
        simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
        ring
  refine ⟨{ normalization := normalization, convex_wolff := ?_ }⟩
  intro targetSet htargetConvex
  let sourceSet := normalization.map.symm '' targetSet
  have hsourceConvex : Convex ℝ sourceSet :=
    Convex.affine_image normalization.map.symm.toAffineMap htargetConvex
  obtain ⟨paperSet, hpaperConvex, hpaperVolume, hpaperCarrier⟩ :=
    commonEnvelope parent sourceSet hsourceConvex
  let targetContained := bodyFamily.containedIndices targetSet
  let ambientContained := (wz1PaperBodyFamily fine).containedIndices paperSet
  let fiberIndex := wz2PaperOrdinaryFullFiberIndexEquiv
    (fine := fine) (coarse := coarse) parent
  have himage : Finset.image (fun target => (fiberIndex target).1)
      targetContained ⊆ ambientContained := by
    intro source hsource
    rcases Finset.mem_image.mp hsource with ⟨target, htarget, rfl⟩
    have htargetCarrier :
        normalization.map ''
            (fine.tube (fiberIndex target).1).carrier ⊆ targetSet := by
      exact (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
        htarget
    have hsourceCarrier :
        (fine.tube (fiberIndex target).1).carrier ⊆ sourceSet := by
      intro point hpoint
      exact
        ⟨normalization.map point,
          htargetCarrier ⟨point, hpoint, rfl⟩,
          normalization.map.symm_apply_apply point⟩
    apply (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
    exact hpaperCarrier (fiberIndex target).1 (fiberIndex target).2
      hsourceCarrier
  have hinjective : Function.Injective
      (fun target : Fin bodyFamily.card => (fiberIndex target).1) := by
    intro first second heq
    exact fiberIndex.injective (Subtype.ext heq)
  have hcount : bodyFamily.containedCount targetSet ≤
      (wz1PaperBodyFamily fine).containedCount paperSet := by
    change (targetContained.card : ENNReal) ≤ (ambientContained.card : ENNReal)
    exact_mod_cast (calc
      targetContained.card =
          (Finset.image (fun target => (fiberIndex target).1)
            targetContained).card :=
        (Finset.card_image_of_injective targetContained hinjective).symm
      _ ≤ ambientContained.card := Finset.card_le_card himage)
  have htopAt := htop paperSet hpaperConvex
  have hvolume := hjohnVolume parent targetSet
  have hscalePos : 0 < Kakeya.realRpowENN rho 2 :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho 2)
  have hscaleTop : Kakeya.realRpowENN rho 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hnormalized :
      topConstant * volume paperSet * fine.enncard ≤
        (fiberConstant * parentCountConstant * johnVolumeConstant *
          envelopeConstant * topConstant) * volume targetSet *
            wz2PaperOrdinaryFullFiberCount fine coarse parent := by
    calc
      topConstant * volume paperSet * fine.enncard ≤
          topConstant * (envelopeConstant * volume sourceSet) *
            fine.enncard := by
        gcongr
      _ ≤ topConstant *
            (envelopeConstant *
              (johnVolumeConstant * Kakeya.realRpowENN rho 2 *
                volume targetSet)) *
            (coarse.enncard * fiberConstant *
              wz2PaperOrdinaryFullFiberCount fine coarse parent) := by
        gcongr
      _ ≤ topConstant *
            (envelopeConstant *
              (johnVolumeConstant * Kakeya.realRpowENN rho 2 *
                volume targetSet)) *
            ((parentCountConstant * (Kakeya.realRpowENN rho 2)⁻¹) *
              fiberConstant *
              wz2PaperOrdinaryFullFiberCount fine coarse parent) := by
        gcongr
      _ = (fiberConstant * parentCountConstant * johnVolumeConstant *
            envelopeConstant * topConstant) * volume targetSet *
              bodyFamily.enncard := by
        have hcancel : Kakeya.realRpowENN rho 2 *
            (Kakeya.realRpowENN rho 2)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hscalePos.ne' hscaleTop
        change
          topConstant *
            (envelopeConstant *
              (johnVolumeConstant * Kakeya.realRpowENN rho 2 *
                volume targetSet)) *
            ((parentCountConstant * (Kakeya.realRpowENN rho 2)⁻¹) *
              fiberConstant *
              wz2PaperOrdinaryFullFiberCount fine coarse parent) =
            (fiberConstant * parentCountConstant * johnVolumeConstant *
              envelopeConstant * topConstant) * volume targetSet *
              ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card :
                ENNReal)
        calc
          topConstant *
                (envelopeConstant *
                  (johnVolumeConstant * Kakeya.realRpowENN rho 2 *
                    volume targetSet)) *
                ((parentCountConstant * (Kakeya.realRpowENN rho 2)⁻¹) *
                  fiberConstant *
                  wz2PaperOrdinaryFullFiberCount fine coarse parent) =
              (Kakeya.realRpowENN rho 2 *
                (Kakeya.realRpowENN rho 2)⁻¹) *
                ((fiberConstant * parentCountConstant * johnVolumeConstant *
                  envelopeConstant * topConstant) * volume targetSet *
                  wz2PaperOrdinaryFullFiberCount fine coarse parent) := by ring
          _ = (fiberConstant * parentCountConstant * johnVolumeConstant *
                envelopeConstant * topConstant) * volume targetSet *
              wz2PaperOrdinaryFullFiberCount fine coarse parent := by
            rw [hcancel, one_mul]
          _ = (fiberConstant * parentCountConstant * johnVolumeConstant *
                envelopeConstant * topConstant) * volume targetSet *
              ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card :
                ENNReal) := by
            rw [wz2PaperOrdinaryFullFiberCount]
  calc
    bodyFamily.containedCount targetSet ≤
        (wz1PaperBodyFamily fine).containedCount paperSet := hcount
    _ ≤ topConstant * volume paperSet * fine.enncard := htopAt
    _ ≤ (fiberConstant * parentCountConstant * johnVolumeConstant *
          envelopeConstant * topConstant) * volume targetSet *
            bodyFamily.enncard := hnormalized
    _ ≤ outputConstant * volume targetSet * bodyFamily.enncard := by gcongr

/-- The production form of the top-level-to-fiber bridge for localized
line-class families.  Both the ordinary-to-cropped common envelope and the
canonical outer-John inverse Jacobian are generated internally. -/
theorem pureWZ2Proposition64_pure_fullFiber_cwa_of_localized_topLevel
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hfineNonempty : fine.Nonempty)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 10)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hline : WZ1PaperIsLineClass fine)
    (hlocal : ∀ source,
      ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 3)
    {topConstant fiberConstant parentCountConstant
      outputConstant : ENNReal}
    (htop : WZ2PaperConvexWolffBound fine topConstant)
    (huniform : WZ2PaperPureFullFibersAreCUniform
      fine coarse fiberConstant)
    (hparentCount :
      coarse.enncard ≤ parentCountConstant *
        (Kakeya.realRpowENN rho 2)⁻¹)
    (hbudget : fiberConstant * parentCountConstant *
        324 * 212776173 * topConstant ≤ outputConstant)
    (parent : Fin coarse.card) :
    Nonempty (WZ2PaperPureUnitRescaledFullFiberData
      (fine := fine) (coarse := coarse) parent outputConstant) := by
  apply pureWZ2Proposition64_pure_fullFiber_cwa_of_topLevel
      cover hfineNonempty hrho htop huniform hparentCount
      (johnVolumeConstant := 324)
      (envelopeConstant := 212776173)
  · intro coarseParent
    dsimp only
    intro targetSet
    exact pureWZ2Proposition64_outerJohn_inverse_volume_le
      hrho hrhoOne (coarse.tube coarseParent)
        (WZ2PaperAssouadUnitRescalingData.ofTube
          (coarse.tube coarseParent) hrho) targetSet
  · intro _coarseParent sourceSet hsourceConvex
    rcases pureWZ2Proposition64_localized_common_cropped_envelope
        hdelta hdeltaSmall hline hlocal sourceSet hsourceConvex with
      ⟨paperSet, hpaperConvex, hpaperVolume, hpaperCarrier⟩
    exact ⟨paperSet, hpaperConvex, hpaperVolume,
      fun source _hsource hcarrier => hpaperCarrier source hcarrier⟩
  · exact hbudget

/-- The localized production bridge on the fixed high-scale root range
`rho <= 4`.  This is the same actual-John construction as above, with the
scale-four capsule determinant budget. -/
theorem pureWZ2Proposition64_pure_fullFiber_cwa_of_localized_topLevel_le_four
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hfineNonempty : fine.Nonempty)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 10)
    (hrho : 0 < rho)
    (hrhoFour : rho ≤ 4)
    (hline : WZ1PaperIsLineClass fine)
    (hlocal : ∀ source,
      ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 3)
    {topConstant fiberConstant parentCountConstant
      outputConstant : ENNReal}
    (htop : WZ2PaperConvexWolffBound fine topConstant)
    (huniform : WZ2PaperPureFullFibersAreCUniform
      fine coarse fiberConstant)
    (hparentCount :
      coarse.enncard ≤ parentCountConstant *
        (Kakeya.realRpowENN rho 2)⁻¹)
    (hbudget : fiberConstant * parentCountConstant *
        972 * 212776173 * topConstant ≤ outputConstant)
    (parent : Fin coarse.card) :
    Nonempty (WZ2PaperPureUnitRescaledFullFiberData
      (fine := fine) (coarse := coarse) parent outputConstant) := by
  apply pureWZ2Proposition64_pure_fullFiber_cwa_of_topLevel
      cover hfineNonempty hrho htop huniform hparentCount
      (johnVolumeConstant := 972)
      (envelopeConstant := 212776173)
  · intro coarseParent
    dsimp only
    intro targetSet
    exact pureWZ2Proposition64_outerJohn_inverse_volume_le_of_le_four
      hrho hrhoFour (coarse.tube coarseParent)
        (WZ2PaperAssouadUnitRescalingData.ofTube
          (coarse.tube coarseParent) hrho) targetSet
  · intro _coarseParent sourceSet hsourceConvex
    rcases pureWZ2Proposition64_localized_common_cropped_envelope
        hdelta hdeltaSmall hline hlocal sourceSet hsourceConvex with
      ⟨paperSet, hpaperConvex, hpaperVolume, hpaperCarrier⟩
    exact ⟨paperSet, hpaperConvex, hpaperVolume,
      fun source _hsource hcarrier => hpaperCarrier source hcarrier⟩
  · exact hbudget

end Kakeya.Assouad

end

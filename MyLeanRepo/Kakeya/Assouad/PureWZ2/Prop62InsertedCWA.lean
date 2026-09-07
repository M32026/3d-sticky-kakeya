import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62InsertedCWASum
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ActualJohnToCallerLiteralCWA

/-!
# Proposition 6.2 metric parents: inserted-level CWA

This proves equation `prop62-inserted-cwa`.  Each complete old strict packet
is transported from its actual outer-John chart to the literal chart of its
assigned radius-`rho` metric parent, paying the quadratic scale ratio.  The
complete packets are then summed exactly.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62InsertedCWALoss
    (rho scale : ℝ) (C : ENNReal) : ENNReal :=
  ENNReal.ofReal (4000000 * (rho / scale) ^ 2) * C

namespace PureWZ2Prop62MetricPacketCoverInput

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {oldData :
      WZ2PaperPureScaleCoverData fine scale ambientConstant}
    {M meshWidth : ℝ}
    (data :
      PureWZ2Prop62MetricPacketCoverInput
        (rho := rho) oldData M meshWidth)

/-- Literal caller images of one complete old strict packet. -/
noncomputable def callerPacketBodyFamily
    (oldParent : Fin oldData.coarse.card) :
    Kakeya.Streamlined.BodyFamily where
  card :=
    (wz2PaperOrdinaryFullFiberIndices
      fine oldData.coarse oldParent).card
  body target :=
    ⟨wz2PaperLiteralUnitRescalingMap
        (data.coarse.tube (data.packetParent oldParent))
        data.rho_pos ''
      (fine.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv
          (fine := fine) (coarse := oldData.coarse)
          oldParent) target).1).carrier⟩

/--
One complete old packet in its assigned caller-literal chart satisfies CWA
with the genuine quadratic `rho / scale` loss.
-/
theorem callerPacketBodyCWA
    (oldParent : Fin oldData.coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (data.callerPacketBodyFamily oldParent)
      (pureWZ2Prop62InsertedCWALoss
        rho scale ambientConstant) := by
  let oldFiber :=
    Classical.choice (oldData.rescaledFiber oldParent)
  let sourceBody :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := oldData.coarse)
      oldParent oldFiber.normalization
  let targetBody :=
    data.callerPacketBodyFamily oldParent
  have transported :
      WZ2PaperBodyConvexWolffBound targetBody
        (ENNReal.ofReal (4000000 * (rho / scale) ^ 2) *
          ambientConstant) := by
    apply
      wz2PaperBodyConvexWolffBound_of_actualJohnToCallerLiteral
        (source := sourceBody) (target := targetBody)
        oldData.rho_pos data.rho_pos
        (oldData.coarse.tube oldParent)
        (data.coarse.tube (data.packetParent oldParent))
        oldFiber.normalization
        (Equiv.refl _)
    · intro target
      dsimp only [sourceBody, targetBody,
        callerPacketBodyFamily,
        wz2PaperPureUnitRescaledFullFiberBodyFamily]
      change
        wz2PaperActualJohnToCallerLiteralCoordinateChange
              (data.coarse.tube (data.packetParent oldParent))
              data.rho_pos oldFiber.normalization ''
            (oldFiber.normalization.map ''
              (fine.tube
                ((wz2PaperOrdinaryFullFiberIndexEquiv
                  (fine := fine) (coarse := oldData.coarse)
                  oldParent) target).1).carrier) ⊆
          wz2PaperLiteralUnitRescalingMap
              (data.coarse.tube (data.packetParent oldParent))
              data.rho_pos ''
            (fine.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv
                (fine := fine) (coarse := oldData.coarse)
                oldParent) target).1).carrier
      rw [
        wz2PaperActualJohnToCallerLiteralCoordinateChange_image
      ]
    · exact oldFiber.convex_wolff
  exact transported

/-- Raw ambient indices in one old packet whose caller image lies in `W`. -/
def callerPacketContainedIndices
    (oldParent : Fin oldData.coarse.card)
    (convexSet : Set Point3) :
    Finset (Fin fine.card) :=
  (wz2PaperOrdinaryFullFiberIndices
    fine oldData.coarse oldParent).filter fun source =>
      wz2PaperLiteralUnitRescalingMap
          (data.coarse.tube (data.packetParent oldParent))
          data.rho_pos ''
        (fine.tube source).carrier ⊆ convexSet

theorem callerPacket_containedCount_eq
    (oldParent : Fin oldData.coarse.card)
    (convexSet : Set Point3) :
    (data.callerPacketBodyFamily oldParent).containedCount
        convexSet =
      (data.callerPacketContainedIndices
        oldParent convexSet).card := by
  let fiber :=
    wz2PaperOrdinaryFullFiberIndices
      fine oldData.coarse oldParent
  let equivalence :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := oldData.coarse) oldParent
  let contained :
      Finset
        (Fin (data.callerPacketBodyFamily oldParent).card) :=
    (data.callerPacketBodyFamily oldParent).containedIndices
      convexSet
  have himage :
      Finset.image
          (fun target => (equivalence target).1)
          contained =
        data.callerPacketContainedIndices oldParent convexSet := by
    ext source
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨target, htarget, rfl⟩
      have hcontained :
          ((data.callerPacketBodyFamily oldParent).body target).carrier ⊆
            convexSet :=
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
          htarget
      exact Finset.mem_filter.mpr
        ⟨(equivalence target).2, hcontained⟩
    · intro hsource
      rcases Finset.mem_filter.mp hsource with
        ⟨hsourceFiber, hsourceContained⟩
      let member : {source : Fin fine.card // source ∈ fiber} :=
        ⟨source, hsourceFiber⟩
      let target := equivalence.symm member
      refine Finset.mem_image.mpr
        ⟨target, ?_, ?_⟩
      · apply
          (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        change
          wz2PaperLiteralUnitRescalingMap
              (data.coarse.tube (data.packetParent oldParent))
              data.rho_pos ''
            (fine.tube (equivalence target).1).carrier ⊆ convexSet
        simpa [target, member] using hsourceContained
      · exact congrArg Subtype.val
          (equivalence.apply_symm_apply member)
  change (contained.card : ENNReal) =
    ((data.callerPacketContainedIndices
      oldParent convexSet).card : ENNReal)
  exact_mod_cast
    (Finset.card_image_of_injective contained (by
      intro first second heq
      exact equivalence.injective (Subtype.ext heq))).symm.trans
        (congrArg Finset.card himage)

/-- Equation `prop62-inserted-cwa` on one new metric parent. -/
theorem insertedFiberCWA
    (parent : Fin data.coarse.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((wz2PaperFullFiberIndices
        fine data.coarse parent).filter fun source =>
          wz2PaperLiteralUnitRescalingMap
              (data.coarse.tube parent) data.rho_pos ''
            (fine.tube source).carrier ⊆ convexSet).card :
      ENNReal) ≤
      pureWZ2Prop62InsertedCWALoss
          rho scale ambientConstant *
        volume convexSet *
        ((wz2PaperFullFiberIndices
          fine data.coarse parent).card : ENNReal) := by
  let active : Finset (Fin oldData.coarse.card) :=
    Finset.univ.filter fun oldParent =>
      data.packetParent oldParent = parent
  let predicate : Fin fine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (data.coarse.tube parent) data.rho_pos ''
        (fine.tube source).carrier ⊆ convexSet
  have localBound :
      ∀ oldParent ∈ active,
        (((Finset.univ.filter fun source =>
            oldData.cover.parent source = oldParent ∧
              predicate source).card : ENNReal)) ≤
          pureWZ2Prop62InsertedCWALoss
              rho scale ambientConstant *
            volume convexSet *
            (((Finset.univ.filter fun source =>
              oldData.cover.parent source = oldParent).card :
              ENNReal)) := by
    intro oldParent holdParent
    have hpacketParent :
        data.packetParent oldParent = parent :=
      (Finset.mem_filter.mp holdParent).2
    have hfiber :
        Finset.univ.filter (fun source =>
            oldData.cover.parent source = oldParent) =
          wz2PaperOrdinaryFullFiberIndices
            fine oldData.coarse oldParent := by
      ext source
      rw [oldData.cover.mem_fullFiber_iff_parent_eq
        oldData.rho_pos.le]
      simp
    have hcontained :
        Finset.univ.filter (fun source =>
            oldData.cover.parent source = oldParent ∧
              predicate source) =
          data.callerPacketContainedIndices
            oldParent convexSet := by
      ext source
      simp only [callerPacketContainedIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [oldData.cover.mem_fullFiber_iff_parent_eq
        oldData.rho_pos.le oldParent source]
      dsimp only [predicate]
      rw [hpacketParent]
    rw [hcontained, hfiber,
      ← data.callerPacket_containedCount_eq
        oldParent convexSet]
    exact data.callerPacketBodyCWA oldParent convexSet convex
  have hsum :=
    pureWZ2_prop62_sum_packet_cwa
      oldData.cover.parent active predicate
      (pureWZ2Prop62InsertedCWALoss
        rho scale ambientConstant)
      (volume convexSet) localBound
  have hactive :
      ∀ source,
        oldData.cover.parent source ∈ active ↔
          data.packetParent
              (oldData.cover.parent source) = parent := by
    intro source
    simp [active]
  have hfiber :=
    data.metricFiber_eq_assignedPackets parent
  rw [hfiber]
  simpa only [predicate, hactive, Finset.filter_filter] using hsum

end PureWZ2Prop62MetricPacketCoverInput

namespace PureWZ2Prop62ProxyMetricPacketCoverInput

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {oldData :
      WZ2PaperPureScaleCoverData fine scale ambientConstant}
    {packetRadius : ℝ}
    (data :
      PureWZ2Prop62ProxyMetricPacketCoverInput
        (rho := rho) oldData packetRadius)

noncomputable def callerPacketBodyFamily
    (oldParent : Fin oldData.coarse.card) :
    Kakeya.Streamlined.BodyFamily where
  card :=
    (wz2PaperOrdinaryFullFiberIndices
      fine oldData.coarse oldParent).card
  body target :=
    ⟨wz2PaperLiteralUnitRescalingMap
        (data.coarse.tube (data.packetParent oldParent))
        data.rho_pos ''
      (fine.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv
          (fine := fine) (coarse := oldData.coarse)
          oldParent) target).1).carrier⟩

theorem callerPacketBodyCWA
    (oldParent : Fin oldData.coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (data.callerPacketBodyFamily oldParent)
      (pureWZ2Prop62InsertedCWALoss
        rho scale ambientConstant) := by
  let oldFiber :=
    Classical.choice (oldData.rescaledFiber oldParent)
  let sourceBody :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := oldData.coarse)
      oldParent oldFiber.normalization
  let targetBody :=
    data.callerPacketBodyFamily oldParent
  have transported :
      WZ2PaperBodyConvexWolffBound targetBody
        (ENNReal.ofReal (4000000 * (rho / scale) ^ 2) *
          ambientConstant) := by
    apply
      wz2PaperBodyConvexWolffBound_of_actualJohnToCallerLiteral
        (source := sourceBody) (target := targetBody)
        oldData.rho_pos data.rho_pos
        (oldData.coarse.tube oldParent)
        (data.coarse.tube (data.packetParent oldParent))
        oldFiber.normalization
        (Equiv.refl _)
    · intro target
      dsimp only [sourceBody, targetBody,
        callerPacketBodyFamily,
        wz2PaperPureUnitRescaledFullFiberBodyFamily]
      change
        wz2PaperActualJohnToCallerLiteralCoordinateChange
              (data.coarse.tube (data.packetParent oldParent))
              data.rho_pos oldFiber.normalization ''
            (oldFiber.normalization.map ''
              (fine.tube
                ((wz2PaperOrdinaryFullFiberIndexEquiv
                  (fine := fine) (coarse := oldData.coarse)
                  oldParent) target).1).carrier) ⊆
          wz2PaperLiteralUnitRescalingMap
              (data.coarse.tube (data.packetParent oldParent))
              data.rho_pos ''
            (fine.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv
                (fine := fine) (coarse := oldData.coarse)
                oldParent) target).1).carrier
      rw [
        wz2PaperActualJohnToCallerLiteralCoordinateChange_image
      ]
    · exact oldFiber.convex_wolff
  exact transported

def callerPacketContainedIndices
    (oldParent : Fin oldData.coarse.card)
    (convexSet : Set Point3) :
    Finset (Fin fine.card) :=
  (wz2PaperOrdinaryFullFiberIndices
    fine oldData.coarse oldParent).filter fun source =>
      wz2PaperLiteralUnitRescalingMap
          (data.coarse.tube (data.packetParent oldParent))
          data.rho_pos ''
        (fine.tube source).carrier ⊆ convexSet

theorem callerPacket_containedCount_eq
    (oldParent : Fin oldData.coarse.card)
    (convexSet : Set Point3) :
    (data.callerPacketBodyFamily oldParent).containedCount
        convexSet =
      (data.callerPacketContainedIndices
        oldParent convexSet).card := by
  let fiber :=
    wz2PaperOrdinaryFullFiberIndices
      fine oldData.coarse oldParent
  let equivalence :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := oldData.coarse) oldParent
  let contained :
      Finset
        (Fin (data.callerPacketBodyFamily oldParent).card) :=
    (data.callerPacketBodyFamily oldParent).containedIndices
      convexSet
  have himage :
      Finset.image
          (fun target => (equivalence target).1)
          contained =
        data.callerPacketContainedIndices oldParent convexSet := by
    ext source
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨target, htarget, rfl⟩
      have hcontained :
          ((data.callerPacketBodyFamily oldParent).body target).carrier ⊆
            convexSet :=
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
          htarget
      exact Finset.mem_filter.mpr
        ⟨(equivalence target).2, hcontained⟩
    · intro hsource
      rcases Finset.mem_filter.mp hsource with
        ⟨hsourceFiber, hsourceContained⟩
      let member : {source : Fin fine.card // source ∈ fiber} :=
        ⟨source, hsourceFiber⟩
      let target := equivalence.symm member
      refine Finset.mem_image.mpr
        ⟨target, ?_, ?_⟩
      · apply
          (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        change
          wz2PaperLiteralUnitRescalingMap
              (data.coarse.tube (data.packetParent oldParent))
              data.rho_pos ''
            (fine.tube (equivalence target).1).carrier ⊆ convexSet
        simpa [target, member] using hsourceContained
      · exact congrArg Subtype.val
          (equivalence.apply_symm_apply member)
  change (contained.card : ENNReal) =
    ((data.callerPacketContainedIndices
      oldParent convexSet).card : ENNReal)
  exact_mod_cast
    (Finset.card_image_of_injective contained (by
      intro first second heq
      exact equivalence.injective (Subtype.ext heq))).symm.trans
        (congrArg Finset.card himage)

theorem insertedFiberCWA
    (parent : Fin data.coarse.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((wz2PaperFullFiberIndices
        fine data.coarse parent).filter fun source =>
          wz2PaperLiteralUnitRescalingMap
              (data.coarse.tube parent) data.rho_pos ''
            (fine.tube source).carrier ⊆ convexSet).card :
      ENNReal) ≤
      pureWZ2Prop62InsertedCWALoss
          rho scale ambientConstant *
        volume convexSet *
        ((wz2PaperFullFiberIndices
          fine data.coarse parent).card : ENNReal) := by
  let active : Finset (Fin oldData.coarse.card) :=
    Finset.univ.filter fun oldParent =>
      data.packetParent oldParent = parent
  let predicate : Fin fine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (data.coarse.tube parent) data.rho_pos ''
        (fine.tube source).carrier ⊆ convexSet
  have localBound :
      ∀ oldParent ∈ active,
        (((Finset.univ.filter fun source =>
            oldData.cover.parent source = oldParent ∧
              predicate source).card : ENNReal)) ≤
          pureWZ2Prop62InsertedCWALoss
              rho scale ambientConstant *
            volume convexSet *
            (((Finset.univ.filter fun source =>
              oldData.cover.parent source = oldParent).card :
              ENNReal)) := by
    intro oldParent holdParent
    have hpacketParent :
        data.packetParent oldParent = parent :=
      (Finset.mem_filter.mp holdParent).2
    have hfiber :
        Finset.univ.filter (fun source =>
            oldData.cover.parent source = oldParent) =
          wz2PaperOrdinaryFullFiberIndices
            fine oldData.coarse oldParent := by
      ext source
      rw [oldData.cover.mem_fullFiber_iff_parent_eq
        oldData.rho_pos.le]
      simp
    have hcontained :
        Finset.univ.filter (fun source =>
            oldData.cover.parent source = oldParent ∧
              predicate source) =
          data.callerPacketContainedIndices
            oldParent convexSet := by
      ext source
      simp only [callerPacketContainedIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [oldData.cover.mem_fullFiber_iff_parent_eq
        oldData.rho_pos.le oldParent source]
      dsimp only [predicate]
      rw [hpacketParent]
    rw [hcontained, hfiber,
      ← data.callerPacket_containedCount_eq
        oldParent convexSet]
    exact data.callerPacketBodyCWA oldParent convexSet convex
  have hsum :=
    pureWZ2_prop62_sum_packet_cwa
      oldData.cover.parent active predicate
      (pureWZ2Prop62InsertedCWALoss
        rho scale ambientConstant)
      (volume convexSet) localBound
  have hactive :
      ∀ source,
        oldData.cover.parent source ∈ active ↔
          data.packetParent
              (oldData.cover.parent source) = parent := by
    intro source
    simp [active]
  have hfiber :=
    data.metricFiber_eq_assignedPackets parent
  rw [hfiber]
  simpa only [predicate, hactive, Finset.filter_filter] using hsum

end PureWZ2Prop62ProxyMetricPacketCoverInput

end Kakeya.Assouad

end

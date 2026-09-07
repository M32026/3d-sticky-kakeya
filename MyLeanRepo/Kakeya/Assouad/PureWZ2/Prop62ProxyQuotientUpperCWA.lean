import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPrefixBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPreCoreAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperUniformity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GeneralJohnToJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CleanupReceipt
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62InsertedCWASum
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperMetricFiberEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperParentCWA

/-!
# Proposition 6.2 quotient-prefix upper CWA

This module isolates the upper-parent argument after the metric parents,
upper-envelope colors, the pre-core `D_-` band, and the one-pass cleanup have
already been chosen.  All selection data enter as explicit hypotheses.

The density loss `Λ` is paid exactly once: the ambient quotient-prefix CWA is
transferred to its core intersection, while the pre-core `D_-` lower bound
and factor-two upper bound are used directly in the final cancellation.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62UpperEnvelopeJohnLoss : ENNReal :=
  27 * ENNReal.ofReal (pureWZ2Prop62UpperEnvelopeFactor ^ 3)

def pureWZ2Prop62UpperEnvelopeGeometricLoss : ENNReal :=
  pureWZ2Prop62UpperEnvelopeJohnLoss * 212776173

/--
Transport one actual-packet body CWA to the John chart of its fixed
`F = 600002` quotient envelope.
-/
theorem pureWZ2_prop62_actualPacket_to_upperEnvelope_cwa
    {sourceScale : ℝ}
    (sourceScalePos : 0 < sourceScale)
    (sourceParent : Kakeya.DeltaTube sourceScale)
    (targetParent :
      Kakeya.DeltaTube
        (pureWZ2Prop62UpperEnvelopeFactor * sourceScale))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    {source target : Kakeya.Streamlined.BodyFamily}
    {sourceConstant : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrier_containment :
      ∀ targetIndex,
        wz2PaperGeneralJohnToJohnCoordinateChange
              sourceJohn targetJohn ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (sourceCWA :
      WZ2PaperBodyConvexWolffBound source sourceConstant) :
    WZ2PaperBodyConvexWolffBound target
      (pureWZ2Prop62UpperEnvelopeJohnLoss * sourceConstant) := by
  simpa [pureWZ2Prop62UpperEnvelopeJohnLoss] using
    wz2PaperBodyConvexWolffBound_of_factorJohnTransport
      sourceScalePos
      (by
        norm_num [pureWZ2Prop62UpperEnvelopeFactor] :
        (1 : ℝ) ≤ pureWZ2Prop62UpperEnvelopeFactor)
      sourceParent targetParent sourceJohn targetJohn
      indexEquiv carrier_containment sourceCWA

/--
Absorb the common physical-envelope loss after the fixed-factor John
transport.
-/
theorem pureWZ2_prop62_upperEnvelope_volume_absorption
    (sourceConstant targetVolume envelopeVolume : ENNReal)
    (envelopeVolumeBound :
      envelopeVolume ≤
        (212776173 : ENNReal) * targetVolume) :
    sourceConstant * pureWZ2Prop62UpperEnvelopeJohnLoss *
        envelopeVolume ≤
      sourceConstant * pureWZ2Prop62UpperEnvelopeGeometricLoss *
        targetVolume := by
  calc
    sourceConstant * pureWZ2Prop62UpperEnvelopeJohnLoss *
          envelopeVolume ≤
        sourceConstant * pureWZ2Prop62UpperEnvelopeJohnLoss *
          ((212776173 : ENNReal) * targetVolume) := by
      gcongr
    _ =
        sourceConstant * pureWZ2Prop62UpperEnvelopeGeometricLoss *
          targetVolume := by
      simp [pureWZ2Prop62UpperEnvelopeGeometricLoss]
      ring

/--
Finite upper-parent counting with one explicit node-density loss.

`preCoreLeaves` is the pre-cleanup quotient-prefix class and `coreLeaves` is
its surviving core intersection.  The lower `D_-` band is imposed on the
pre-core metric fibers.  The sole `Λ` occurs in `ambient_to_core`; it is not
used again in the packet floor.
-/
theorem pureWZ2_prop62_upper_parent_cwa_single_density
    {Leaf Child : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Child] [DecidableEq Child]
    (owner : Leaf → Child)
    (preCoreLeaves coreLeaves : Finset Leaf)
    (activeChildren containedChildren : Finset Child)
    (containedLeaves : Finset Leaf)
    (DMinus : ℕ)
    (DMinus_pos : 0 < DMinus)
    (contained_subset :
      containedChildren ⊆ activeChildren)
    (preCore_fiber_lower :
      ∀ child ∈ activeChildren,
        DMinus ≤
          (preCoreLeaves.filter fun leaf =>
            owner leaf = child).card)
    (contained_packet :
      ∀ child ∈ containedChildren,
        preCoreLeaves.filter (fun leaf => owner leaf = child) ⊆
          containedLeaves)
    (sourceConstant envelopeVolumeFactor
      ambientLeaves Λ : ENNReal)
    (containedLeaves_cwa :
      (containedLeaves.card : ENNReal) ≤
        sourceConstant * envelopeVolumeFactor * ambientLeaves)
    (ambient_to_core :
      ambientLeaves ≤ Λ * (coreLeaves.card : ENNReal))
    (core_partition :
      coreLeaves ⊆ preCoreLeaves)
    (core_owner_active :
      ∀ leaf ∈ coreLeaves, owner leaf ∈ activeChildren)
    (preCore_fiber_upper :
      ∀ child ∈ activeChildren,
        (preCoreLeaves.filter fun leaf =>
          owner leaf = child).card < 2 * DMinus) :
    (containedChildren.card : ENNReal) ≤
      (Λ * sourceConstant) * envelopeVolumeFactor * 2 *
        (activeChildren.card : ENNReal) := by
  let preCoreInContained : Finset Leaf :=
    preCoreLeaves.filter fun leaf =>
      owner leaf ∈ containedChildren
  have preCoreInContained_subset :
      preCoreInContained ⊆ containedLeaves := by
    intro leaf leafMem
    have leafData := Finset.mem_filter.mp leafMem
    exact
      contained_packet (owner leaf) leafData.2 <|
        Finset.mem_filter.mpr ⟨leafData.1, rfl⟩
  have preCoreFiberSum :
      ∑ child ∈ containedChildren,
          (preCoreLeaves.filter fun leaf =>
            owner leaf = child).card =
        preCoreInContained.card := by
    simpa only [preCoreInContained] using
      Finset.sum_card_fiberwise_eq_card_filter
        preCoreLeaves containedChildren owner
  have lowerCountNat :
      DMinus * containedChildren.card ≤
        containedLeaves.card := by
    calc
      DMinus * containedChildren.card =
          ∑ _child ∈ containedChildren, DMinus := by
        simp [Finset.sum_const, mul_comm]
      _ ≤
          ∑ child ∈ containedChildren,
            (preCoreLeaves.filter fun leaf =>
              owner leaf = child).card := by
        exact Finset.sum_le_sum fun child childMem =>
          preCore_fiber_lower child (contained_subset childMem)
      _ = preCoreInContained.card := preCoreFiberSum
      _ ≤ containedLeaves.card :=
        Finset.card_le_card preCoreInContained_subset
  have lowerCount :
      (DMinus : ENNReal) *
          (containedChildren.card : ENNReal) ≤
        (containedLeaves.card : ENNReal) := by
    exact_mod_cast lowerCountNat
  have coreSubsetActive :
      coreLeaves =
        coreLeaves.filter fun leaf =>
          owner leaf ∈ activeChildren := by
    exact (Finset.filter_true_of_mem core_owner_active).symm
  have coreFiberSum :
      ∑ child ∈ activeChildren,
          (coreLeaves.filter fun leaf =>
            owner leaf = child).card =
        coreLeaves.card := by
    have fiberSum :=
      Finset.sum_card_fiberwise_eq_card_filter
        coreLeaves activeChildren owner
    exact
      fiberSum.trans (congrArg Finset.card coreSubsetActive.symm)
  have coreFiberUpper :
      ∀ child ∈ activeChildren,
        (coreLeaves.filter fun leaf =>
          owner leaf = child).card ≤
          2 * DMinus := by
    intro child childMem
    have subset :
        coreLeaves.filter (fun leaf => owner leaf = child) ⊆
          preCoreLeaves.filter fun leaf => owner leaf = child := by
      intro leaf leafMem
      have leafData := Finset.mem_filter.mp leafMem
      exact
        Finset.mem_filter.mpr
          ⟨core_partition leafData.1, leafData.2⟩
    exact
      (Finset.card_le_card subset).trans <|
        Nat.le_of_lt (preCore_fiber_upper child childMem)
  have coreUpperNat :
      coreLeaves.card ≤
        2 * DMinus * activeChildren.card := by
    rw [← coreFiberSum]
    calc
      (∑ child ∈ activeChildren,
          (coreLeaves.filter fun leaf =>
            owner leaf = child).card) ≤
          ∑ _child ∈ activeChildren, 2 * DMinus := by
        exact Finset.sum_le_sum coreFiberUpper
      _ = 2 * DMinus * activeChildren.card := by
        simp [Finset.sum_const, mul_comm]
  have coreUpper :
      (coreLeaves.card : ENNReal) ≤
        2 * (DMinus : ENNReal) *
          (activeChildren.card : ENNReal) := by
    exact_mod_cast coreUpperNat
  have scaled :
      (containedChildren.card : ENNReal) * (DMinus : ENNReal) ≤
        ((Λ * sourceConstant) * envelopeVolumeFactor * 2 *
          (activeChildren.card : ENNReal)) *
            (DMinus : ENNReal) := by
    calc
      (containedChildren.card : ENNReal) * (DMinus : ENNReal) =
          (DMinus : ENNReal) *
            (containedChildren.card : ENNReal) := by ring
      _ ≤ (containedLeaves.card : ENNReal) :=
        lowerCount
      _ ≤ sourceConstant * envelopeVolumeFactor * ambientLeaves :=
        containedLeaves_cwa
      _ ≤
          sourceConstant * envelopeVolumeFactor *
            (Λ * (coreLeaves.card : ENNReal)) := by
        gcongr
      _ ≤
          sourceConstant * envelopeVolumeFactor *
            (Λ *
              (2 * (DMinus : ENNReal) *
                (activeChildren.card : ENNReal))) := by
        gcongr
      _ =
          ((Λ * sourceConstant) * envelopeVolumeFactor * 2 *
            (activeChildren.card : ENNReal)) *
              (DMinus : ENNReal) := by ring
  exact
    (ENNReal.mul_le_mul_iff_right
      (show (DMinus : ENNReal) ≠ 0 by
        exact_mod_cast DMinus_pos.ne')
      (by simp)).mp <| by
        simpa [mul_comm] using scaled

/--
Summing actual-packet CWA over one quotient prefix does not introduce a copy
factor.  Every packet has the same constant, and the right-hand cardinalities
sum to the cardinality of the prefix.
-/
theorem pureWZ2_prop62_quotientPrefix_packet_sum
    {Leaf Packet : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Packet] [DecidableEq Packet]
    (parent : Leaf → Packet)
    (activePackets : Finset Packet)
    (prefixLeaves containedLeaves : Finset Leaf)
    (predicate : Leaf → Prop)
    (sourceConstant volumeFactor : ENNReal)
    (prefix_eq :
      prefixLeaves =
        Finset.univ.filter fun leaf =>
          parent leaf ∈ activePackets)
    (contained_eq :
      containedLeaves =
        Finset.univ.filter fun leaf =>
          parent leaf ∈ activePackets ∧ predicate leaf)
    (packet_cwa :
      ∀ packet ∈ activePackets,
        (((Finset.univ.filter fun leaf =>
          parent leaf = packet ∧ predicate leaf).card : ENNReal)) ≤
          sourceConstant * volumeFactor *
            (((Finset.univ.filter fun leaf =>
              parent leaf = packet).card : ENNReal))) :
    (containedLeaves.card : ENNReal) ≤
      sourceConstant * volumeFactor *
        (prefixLeaves.card : ENNReal) := by
  rw [prefix_eq, contained_eq]
  exact
    pureWZ2_prop62_sum_packet_cwa
      parent activePackets predicate sourceConstant volumeFactor
      packet_cwa

/--
The fixed geometric loss in the quotient upper-parent argument is exactly
the factor-John loss times the common physical-envelope loss.
-/
theorem pureWZ2_prop62_upperEnvelope_geometricLoss_eq :
    pureWZ2Prop62UpperEnvelopeGeometricLoss =
      ((27 : ENNReal) *
          ENNReal.ofReal
            (pureWZ2Prop62UpperEnvelopeFactor ^ 3)) *
        212776173 := by
  rfl

/--
Explicit-hypothesis quotient-prefix upper CWA wrapper.

The packetwise transport and sum are represented by `ambient_cwa`; callers
obtain that premise using `wz2PaperBodyConvexWolffBound_of_factorJohnTransport`,
`pureWZ2_prop62_quotientPrefix_packet_sum`, and the common-envelope volume
bound.  The conclusion contains `Λ` exactly once.
-/
theorem pureWZ2_prop62_quotientPrefix_upper_parent_cwa
    {Leaf Child : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Child] [DecidableEq Child]
    (owner : Leaf → Child)
    (preCoreLeaves coreLeaves : Finset Leaf)
    (activeChildren containedChildren : Finset Child)
    (containedLeafSet : Finset Leaf)
    (DMinus : ℕ)
    (DMinus_pos : 0 < DMinus)
    (contained_subset :
      containedChildren ⊆ activeChildren)
    (preCore_fiber_band :
      ∀ child ∈ activeChildren,
        DMinus ≤
            (preCoreLeaves.filter fun leaf =>
              owner leaf = child).card ∧
          (preCoreLeaves.filter fun leaf =>
            owner leaf = child).card < 2 * DMinus)
    (contained_packet :
      ∀ child ∈ containedChildren,
        preCoreLeaves.filter (fun leaf => owner leaf = child) ⊆
          containedLeafSet)
    (core_subset : coreLeaves ⊆ preCoreLeaves)
    (core_owner_active :
      ∀ leaf ∈ coreLeaves, owner leaf ∈ activeChildren)
    (ambientPrefixCard corePrefixCard : ℕ)
    (core_card :
      coreLeaves.card = corePrefixCard)
    (Λ sourceConstant volumeFactor : ENNReal)
    (node_density :
      (ambientPrefixCard : ENNReal) ≤
        Λ * (corePrefixCard : ENNReal))
    (ambient_cwa :
      (containedLeafSet.card : ENNReal) ≤
        sourceConstant *
          (pureWZ2Prop62UpperEnvelopeGeometricLoss * volumeFactor) *
          (ambientPrefixCard : ENNReal)) :
    (containedChildren.card : ENNReal) ≤
      (Λ * sourceConstant) *
        pureWZ2Prop62UpperEnvelopeGeometricLoss *
        volumeFactor * 2 *
        (activeChildren.card : ENNReal) := by
  have ambientToCore :
      (ambientPrefixCard : ENNReal) ≤
        Λ * (coreLeaves.card : ENNReal) := by
    rwa [core_card]
  have cwa :=
    pureWZ2_prop62_upper_parent_cwa_single_density
      owner preCoreLeaves coreLeaves activeChildren
      containedChildren containedLeafSet DMinus DMinus_pos
      contained_subset
      (fun child childMem =>
        (preCore_fiber_band child childMem).1)
      contained_packet sourceConstant
      (pureWZ2Prop62UpperEnvelopeGeometricLoss * volumeFactor)
      (ambientPrefixCard : ENNReal) Λ ambient_cwa ambientToCore
      core_subset core_owner_active
      (fun child childMem =>
        (preCore_fiber_band child childMem).2)
  simpa [mul_assoc] using cwa

/--
Body-family form of the quotient-prefix upper-parent estimate.

All geometric construction is external: for each test convex set the caller
supplies the relevant upper children, the fine leaves captured by the common
envelope, and the packet-summed ambient CWA bound.  The result pays one `Λ`.
-/
theorem pureWZ2_prop62_quotientPrefix_upper_parent_body_cwa
    {Leaf Child : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Child] [DecidableEq Child]
    (target : Kakeya.Streamlined.BodyFamily)
    (owner : Leaf → Child)
    (preCoreLeaves coreLeaves : Finset Leaf)
    (activeChildren : Finset Child)
    (DMinus : ℕ)
    (DMinus_pos : 0 < DMinus)
    (preCore_fiber_band :
      ∀ child ∈ activeChildren,
        DMinus ≤
            (preCoreLeaves.filter fun leaf =>
              owner leaf = child).card ∧
          (preCoreLeaves.filter fun leaf =>
            owner leaf = child).card < 2 * DMinus)
    (core_subset : coreLeaves ⊆ preCoreLeaves)
    (core_owner_active :
      ∀ leaf ∈ coreLeaves, owner leaf ∈ activeChildren)
    (ambientPrefixCard corePrefixCard : ℕ)
    (core_card :
      coreLeaves.card = corePrefixCard)
    (Λ sourceConstant : ENNReal)
    (node_density :
      (ambientPrefixCard : ENNReal) ≤
        Λ * (corePrefixCard : ENNReal))
    (containedChildren : Set Point3 → Finset Child)
    (containedLeafSet : Set Point3 → Finset Leaf)
    (contained_subset :
      ∀ convexSet,
        containedChildren convexSet ⊆ activeChildren)
    (target_count :
      ∀ convexSet,
        target.containedCount convexSet =
          (containedChildren convexSet).card)
    (target_card :
      target.enncard = (activeChildren.card : ENNReal))
    (contained_packet :
      ∀ convexSet,
        ∀ child ∈ containedChildren convexSet,
          preCoreLeaves.filter (fun leaf => owner leaf = child) ⊆
            containedLeafSet convexSet)
    (ambient_cwa :
      ∀ convexSet, Convex ℝ convexSet →
        ((containedLeafSet convexSet).card : ENNReal) ≤
          sourceConstant *
            (pureWZ2Prop62UpperEnvelopeGeometricLoss *
              volume convexSet) *
            (ambientPrefixCard : ENNReal)) :
    WZ2PaperBodyConvexWolffBound target
      ((Λ * sourceConstant) *
        pureWZ2Prop62UpperEnvelopeGeometricLoss * 2) := by
  intro convexSet convex
  rw [target_count convexSet, target_card]
  have bound :=
    pureWZ2_prop62_quotientPrefix_upper_parent_cwa
      owner preCoreLeaves coreLeaves activeChildren
      (containedChildren convexSet)
      (containedLeafSet convexSet) DMinus DMinus_pos
      (contained_subset convexSet)
      preCore_fiber_band
      (contained_packet convexSet)
      core_subset core_owner_active
      ambientPrefixCard corePrefixCard core_card
      Λ sourceConstant (volume convexSet) node_density
      (ambient_cwa convexSet convex)
  calc
    ((containedChildren convexSet).card : ENNReal) ≤
        (Λ * sourceConstant) *
          pureWZ2Prop62UpperEnvelopeGeometricLoss *
          volume convexSet * 2 *
          (activeChildren.card : ENNReal) :=
      bound
    _ =
        ((Λ * sourceConstant) *
          pureWZ2Prop62UpperEnvelopeGeometricLoss * 2) *
          volume convexSet *
          (activeChildren.card : ENNReal) := by
      ring

/--
Exact contained-count description for the genuine rescaled strict fiber used
by the quotient upper cover.  This local version keeps the quotient route
independent of the legacy ancestry upper-parent module.
-/
theorem pureWZ2_prop62_quotientUpperFullFiber_containedCount_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (normalization :
      WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
    (convexSet : Set Point3) :
    (wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse)
      parent normalization).containedCount convexSet =
      (((wz2PaperOrdinaryFullFiberIndices fine coarse parent).filter
        fun source =>
          normalization.map '' (fine.tube source).carrier ⊆
            convexSet).card : ENNReal) := by
  let fiber :=
    wz2PaperOrdinaryFullFiberIndices fine coarse parent
  let equivalence :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := coarse) parent
  let bodyFamily :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse)
      parent normalization
  have imageEq :
      Finset.image
          (fun target => (equivalence target).1)
          (bodyFamily.containedIndices convexSet) =
        fiber.filter fun source =>
          normalization.map '' (fine.tube source).carrier ⊆
            convexSet := by
    ext source
    constructor
    · intro sourceImage
      rcases Finset.mem_image.mp sourceImage with
        ⟨target, targetMem, rfl⟩
      have contained :=
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
          targetMem
      exact
        Finset.mem_filter.mpr
          ⟨(equivalence target).2, contained⟩
    · intro sourceMem
      rcases Finset.mem_filter.mp sourceMem with
        ⟨sourceFiber, sourceContained⟩
      let member : {source : Fin fine.card // source ∈ fiber} :=
        ⟨source, sourceFiber⟩
      let target := equivalence.symm member
      refine
        Finset.mem_image.mpr
          ⟨target, ?_, congrArg Subtype.val
            (equivalence.apply_symm_apply member)⟩
      apply
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
      change
        normalization.map ''
            (fine.tube (equivalence target).1).carrier ⊆
          convexSet
      simpa [target, member] using sourceContained
  unfold Kakeya.Streamlined.BodyFamily.containedCount
  rw [← imageEq]
  norm_cast
  exact
    (Finset.card_image_of_injective
      (bodyFamily.containedIndices convexSet)
      (by
        intro first second equality
        exact equivalence.injective (Subtype.ext equality))).symm

/--
The ambient metric-parent indices represented by one exact upper-cover
strict fiber.
-/
def pureWZ2Prop62UpperCoverAmbientFiber
    {rho upper : ℝ}
    {children : Kakeya.Streamlined.TubeFamily rho}
    (selectedChildren : WZ2PaperPureTubeSubfamily children)
    (upperParents : Kakeya.Streamlined.TubeFamily upper)
    (parent : Fin upperParents.card) :
    Finset (Fin children.card) :=
  Finset.image selectedChildren.embedding
    (wz2PaperOrdinaryFullFiberIndices
      selectedChildren.family upperParents parent)

/--
The ambient metric-parent indices in one exact upper-cover strict fiber whose
normalized bodies are contained in a test convex set.
-/
def pureWZ2Prop62UpperCoverContainedAmbientFiber
    {rho upper : ℝ}
    {children : Kakeya.Streamlined.TubeFamily rho}
    (selectedChildren : WZ2PaperPureTubeSubfamily children)
    (upperParents : Kakeya.Streamlined.TubeFamily upper)
    (parent : Fin upperParents.card)
    (normalization :
      WZ2PaperAssouadUnitRescalingData
        (upperParents.tube parent))
    (convexSet : Set Point3) :
    Finset (Fin children.card) :=
  Finset.image selectedChildren.embedding <|
    (wz2PaperOrdinaryFullFiberIndices
      selectedChildren.family upperParents parent).filter
        fun child =>
          normalization.map ''
              (selectedChildren.family.tube child).carrier ⊆
            convexSet

/--
`Bcopy` converts old actual-packet uniformity into ambient quotient-prefix
uniformity.  This is independent of the CWA estimate and introduces no
additional node-density factor.
-/
theorem pureWZ2_prop62_quotientPrefix_ambient_uniformity
    (firstPrefixCard secondPrefixCard
      firstPacketCard secondPacketCard Bcopy : ℕ)
    (ambientConstant : ENNReal)
    (first_prefix_upper :
      firstPrefixCard ≤ Bcopy * firstPacketCard)
    (second_packet_lower :
      secondPacketCard ≤ secondPrefixCard)
    (packet_uniform :
      (firstPacketCard : ENNReal) ≤
        ambientConstant * (secondPacketCard : ENNReal)) :
    (firstPrefixCard : ENNReal) ≤
      (Bcopy : ENNReal) * ambientConstant *
        (secondPrefixCard : ENNReal) := by
  have firstUpper :
      (firstPrefixCard : ENNReal) ≤
        (Bcopy : ENNReal) * (firstPacketCard : ENNReal) := by
    exact_mod_cast first_prefix_upper
  have secondLower :
      (secondPacketCard : ENNReal) ≤
        (secondPrefixCard : ENNReal) := by
    exact_mod_cast second_packet_lower
  calc
    (firstPrefixCard : ENNReal) ≤
        (Bcopy : ENNReal) * (firstPacketCard : ENNReal) :=
      firstUpper
    _ ≤
        (Bcopy : ENNReal) *
          (ambientConstant * (secondPacketCard : ENNReal)) := by
      gcongr
    _ ≤
        (Bcopy : ENNReal) *
          (ambientConstant * (secondPrefixCard : ENNReal)) := by
      gcongr
    _ =
        (Bcopy : ENNReal) * ambientConstant *
          (secondPrefixCard : ENNReal) := by ring

/--
Restrict the ambient `Bcopy * C` quotient-prefix comparison through one
cleanup receipt.  Only the second prefix uses node density, so the result has
one copy of the receipt loss.
-/
theorem pureWZ2_prop62_receipt_upper_prefix_uniformity
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected : Finset Leaf)
    (receipt : PureWZ2Prop62CleanupReceipt tree selected)
    (level : ℕ)
    (levelLe : level ≤ depth)
    (firstNode secondNode : Node)
    (secondCoreNonempty :
      (receipt.core ∩ tree.fiber level secondNode).Nonempty)
    (Bcopy : ℕ)
    (ambientConstant : ENNReal)
    (ambient_uniform :
      ((tree.fiber level firstNode).card : ENNReal) ≤
        (Bcopy : ENNReal) * ambientConstant *
          ((tree.fiber level secondNode).card : ENNReal)) :
    ((receipt.core ∩ tree.fiber level firstNode).card : ENNReal) ≤
      ((Bcopy : ENNReal) * ambientConstant *
        ((2 ^ depth : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹)) *
        ((receipt.core ∩ tree.fiber level secondNode).card :
          ENNReal) := by
  have firstCoreSubset :
      receipt.core ∩ tree.fiber level firstNode ⊆
        tree.fiber level firstNode :=
    Finset.inter_subset_right
  have firstCoreLe :
      ((receipt.core ∩ tree.fiber level firstNode).card : ENNReal) ≤
        ((tree.fiber level firstNode).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card firstCoreSubset
  have secondDensity :=
      receipt.node_density level levelLe secondNode
        secondCoreNonempty
  have selectedPos : 0 < selected.card := by
    rcases secondCoreNonempty with ⟨leaf, leafMem⟩
    exact
      Finset.card_pos.mpr
        ⟨leaf, receipt.core_subset (Finset.mem_inter.mp leafMem).1⟩
  have secondDensityENN :
      ((tree.fiber level secondNode).card : ENNReal) ≤
        ((2 ^ depth : ENNReal) *
            (Fintype.card Leaf : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
          ((receipt.core ∩ tree.fiber level secondNode).card :
            ENNReal) := by
    have density :
        (selected.card : ENNReal) *
            ((tree.fiber level secondNode).card : ENNReal) ≤
          (2 ^ depth : ENNReal) *
            ((receipt.core ∩ tree.fiber level secondNode).card : ENNReal) *
            (Fintype.card Leaf : ENNReal) := by
      exact_mod_cast secondDensity
    calc
      ((tree.fiber level secondNode).card : ENNReal) =
          ((selected.card : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
              ((tree.fiber level secondNode).card : ENNReal) := by
        rw [ENNReal.mul_inv_cancel
          (by exact_mod_cast selectedPos.ne') (by simp)]
        simp
      _ =
          ((selected.card : ENNReal) *
            ((tree.fiber level secondNode).card : ENNReal)) *
              (selected.card : ENNReal)⁻¹ := by ring
      _ ≤
          ((2 ^ depth : ENNReal) *
            ((receipt.core ∩ tree.fiber level secondNode).card : ENNReal) *
            (Fintype.card Leaf : ENNReal)) *
              (selected.card : ENNReal)⁻¹ := by
        gcongr
      _ = _ := by ring
  calc
    ((receipt.core ∩ tree.fiber level firstNode).card : ENNReal) ≤
        ((tree.fiber level firstNode).card : ENNReal) :=
      firstCoreLe
    _ ≤
        (Bcopy : ENNReal) * ambientConstant *
          ((tree.fiber level secondNode).card : ENNReal) :=
      ambient_uniform
    _ ≤
        (Bcopy : ENNReal) * ambientConstant *
          (((2 ^ depth : ENNReal) *
              (Fintype.card Leaf : ENNReal) *
              (selected.card : ENNReal)⁻¹) *
            ((receipt.core ∩ tree.fiber level secondNode).card :
              ENNReal)) := by
      gcongr
    _ =
        ((Bcopy : ENNReal) * ambientConstant *
          ((2 ^ depth : ENNReal) *
            (Fintype.card Leaf : ENNReal) *
            (selected.card : ENNReal)⁻¹)) *
          ((receipt.core ∩ tree.fiber level secondNode).card :
            ENNReal) := by
      ring

/--
Apply one cleanup receipt to an upper prefix node.  This is the only place
where the quotient-prefix CWA wrapper pays the density factor `Λ`.
-/
theorem pureWZ2_prop62_receipt_upper_prefix_density
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected : Finset Leaf)
    (receipt : PureWZ2Prop62CleanupReceipt tree selected)
    (level : ℕ)
    (levelLe : level ≤ depth)
    (node : Node)
    (coreNonempty :
      (receipt.core ∩ tree.fiber level node).Nonempty) :
    ((tree.fiber level node).card : ENNReal) ≤
      ((2 ^ depth : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹) *
        ((receipt.core ∩ tree.fiber level node).card : ENNReal) := by
  have densityNat :=
    receipt.node_density level levelLe node coreNonempty
  have density :
      (selected.card : ENNReal) *
          ((tree.fiber level node).card : ENNReal) ≤
        (2 ^ depth : ENNReal) *
          ((receipt.core ∩ tree.fiber level node).card : ENNReal) *
          (Fintype.card Leaf : ENNReal) := by
    exact_mod_cast densityNat
  have selectedPos : 0 < selected.card := by
    rcases coreNonempty with ⟨leaf, leafMem⟩
    exact
      Finset.card_pos.mpr
        ⟨leaf, receipt.core_subset (Finset.mem_inter.mp leafMem).1⟩
  calc
    ((tree.fiber level node).card : ENNReal) =
        ((selected.card : ENNReal) *
          (selected.card : ENNReal)⁻¹) *
            ((tree.fiber level node).card : ENNReal) := by
      rw [ENNReal.mul_inv_cancel
        (by exact_mod_cast selectedPos.ne') (by simp)]
      simp
    _ =
        ((selected.card : ENNReal) *
          ((tree.fiber level node).card : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by ring
    _ ≤
        ((2 ^ depth : ENNReal) *
          ((receipt.core ∩ tree.fiber level node).card : ENNReal) *
          (Fintype.card Leaf : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by
      gcongr
    _ =
        ((2 ^ depth : ENNReal) *
            (Fintype.card Leaf : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
          ((receipt.core ∩ tree.fiber level node).card : ENNReal) := by
      ring

namespace PureWZ2Prop62UpperEnvelopeCenterColoringData

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
    {packetCoordinate : Fin schedule.levelCount}
    (coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)

def pureWZ2Prop62ReceiptDensityLoss
    (depth leafCard selectedCard : ℕ) : ENNReal :=
  (2 ^ depth : ENNReal) *
    (leafCard : ENNReal) * (selectedCard : ENNReal)⁻¹

/-- An equality after intersecting with `U0` remains valid on any subset of `U0`. -/
theorem pureWZ2_prop62_inter_eq_of_selected_inter_eq
    {α : Type*}
    [DecidableEq α]
    (U0 core first second : Finset α)
    (coreSubset : core ⊆ U0)
    (selectedIntersection :
      U0 ∩ first = U0 ∩ second) :
    core ∩ first = core ∩ second := by
  ext element
  constructor
  · intro elementMem
    have data := Finset.mem_inter.mp elementMem
    have selectedMem :
        element ∈ U0 ∩ first :=
      Finset.mem_inter.mpr
        ⟨coreSubset data.1, data.2⟩
    rw [selectedIntersection] at selectedMem
    exact
      Finset.mem_inter.mpr
        ⟨data.1, (Finset.mem_inter.mp selectedMem).2⟩
  · intro elementMem
    have data := Finset.mem_inter.mp elementMem
    have selectedMem :
        element ∈ U0 ∩ second :=
      Finset.mem_inter.mpr
        ⟨coreSubset data.1, data.2⟩
    rw [← selectedIntersection] at selectedMem
    exact
      Finset.mem_inter.mpr
        ⟨data.1, (Finset.mem_inter.mp selectedMem).2⟩

/--
The one-pass receipt density at a true quotient-prefix node, rewritten as a
density estimate for the corresponding quotient-center class inside the
globally monochromatic complete-fiber set `wholeLeaves`.

The cleanup receipt is taken on the later leaf-selected set `preliminary`.
Only the inclusion `preliminary ⊆ wholeLeaves` is used; the two sets are not
identified.
-/
theorem receipt_centerPacket_density
    {width : ℝ}
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (wholeLeaves preliminary : Finset (Fin fine.card))
    (preliminary_subset_wholeLeaves :
      preliminary ⊆ wholeLeaves)
    (selectedColor :
      ∀ _coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
    (monochromatic :
      ∀ source ∈ wholeLeaves,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor coordinate source =
            selectedColor coordinate)
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)
    (receipt :
      PureWZ2Prop62CleanupReceipt auxiliary.tree preliminary)
    (anchor : Fin fine.card)
    (anchorMem : anchor ∈ wholeLeaves)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (coreCenterNonempty :
      (receipt.core ∩
        quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 anchor)).Nonempty) :
    ((auxiliary.prefixNodeAt
      (coordinate.1.1 + 1) anchor).card : ENNReal) ≤
      pureWZ2Prop62ReceiptDensityLoss
          (schedule.levelCount + 1) fine.card preliminary.card *
        ((receipt.core ∩
          quotient.centerPacketIndices coordinate.1
            (quotient.leafCenter coordinate.1 anchor)).card :
          ENNReal) := by
  have selectedIntersection :
      wholeLeaves ∩
          quotient.centerPacketIndices coordinate.1
            (quotient.leafCenter coordinate.1 anchor) =
        wholeLeaves ∩
          auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor :=
    coloring.monochromatic_centerPacket_inter_prefixNode
      fineLine fineBase wholeLeaves selectedColor monochromatic
      auxiliary anchor anchorMem coordinate
  have coreSubsetWholeLeaves :
      receipt.core ⊆ wholeLeaves :=
    receipt.core_subset.trans preliminary_subset_wholeLeaves
  have coreIntersection :
      receipt.core ∩
          quotient.centerPacketIndices coordinate.1
            (quotient.leafCenter coordinate.1 anchor) =
        receipt.core ∩
          auxiliary.prefixNodeAt
            (coordinate.1.1 + 1) anchor := by
    exact
      pureWZ2_prop62_inter_eq_of_selected_inter_eq
        wholeLeaves receipt.core
        (quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 anchor))
        (auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) anchor)
        coreSubsetWholeLeaves selectedIntersection
  have treeFiber :
      auxiliary.tree.fiber (coordinate.1.1 + 1)
          (auxiliary.nodeAt (coordinate.1.1 + 1) anchor) =
        auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) anchor :=
    auxiliary.tree_fiber_upperCoordinate_prefix_eq coordinate anchor
  have treeCoreNonempty :
      (receipt.core ∩
        auxiliary.tree.fiber (coordinate.1.1 + 1)
          (auxiliary.nodeAt
            (coordinate.1.1 + 1) anchor)).Nonempty := by
    rw [treeFiber, ← coreIntersection]
    exact coreCenterNonempty
  have densityRaw :=
    pureWZ2_prop62_receipt_upper_prefix_density
      auxiliary.tree preliminary receipt
      (coordinate.1.1 + 1)
      (by omega)
      (auxiliary.nodeAt (coordinate.1.1 + 1) anchor)
      treeCoreNonempty
  have density :
      ((auxiliary.tree.fiber (coordinate.1.1 + 1)
        (auxiliary.nodeAt
          (coordinate.1.1 + 1) anchor)).card : ENNReal) ≤
        ((2 ^ (schedule.levelCount + 1) : ENNReal) *
            (fine.card : ENNReal) * (preliminary.card : ENNReal)⁻¹) *
          ((receipt.core ∩
            auxiliary.tree.fiber (coordinate.1.1 + 1)
              (auxiliary.nodeAt
                (coordinate.1.1 + 1) anchor)).card : ENNReal) := by
    simpa only [Fintype.card_fin] using densityRaw
  rw [treeFiber, ← coreIntersection] at density
  simpa [pureWZ2Prop62ReceiptDensityLoss,
    Fintype.card_fin, mul_assoc] using density

/--
Quotient-specific upper-parent body CWA.

The stronger upper-envelope coloring and its global monochromaticity on
`wholeLeaves` are explicit inputs.  They identify the complete-fiber center
class with the true prefix node.  The cleanup receipt is taken only on
`preliminary`, with `preliminary ⊆ wholeLeaves`; consequently the `D_-` band
is used on complete fibers while the receipt density factor occurs exactly
once in the output constant.
-/
theorem quotientPrefix_upper_parent_body_cwa
    {width : ℝ}
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (wholeLeaves preliminary : Finset (Fin fine.card))
    (preliminary_subset_wholeLeaves :
      preliminary ⊆ wholeLeaves)
    (selectedColor :
      ∀ _coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
    (monochromatic :
      ∀ source ∈ wholeLeaves,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor coordinate source =
            selectedColor coordinate)
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)
    (receipt :
      PureWZ2Prop62CleanupReceipt auxiliary.tree preliminary)
    (anchor : Fin fine.card)
    (anchorMem : anchor ∈ wholeLeaves)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (target : Kakeya.Streamlined.BodyFamily)
    {Child : Type}
    [Fintype Child] [DecidableEq Child]
    (owner : Fin fine.card → Child)
    (activeChildren : Finset Child)
    (DMinus : ℕ)
    (DMinus_pos : 0 < DMinus)
    (preCore_fiber_band :
      ∀ child ∈ activeChildren,
        DMinus ≤
            ((wholeLeaves ∩
              quotient.centerPacketIndices coordinate.1
                (quotient.leafCenter coordinate.1 anchor)).filter
              fun leaf => owner leaf = child).card ∧
          (((wholeLeaves ∩
              quotient.centerPacketIndices coordinate.1
                (quotient.leafCenter coordinate.1 anchor)).filter
              fun leaf => owner leaf = child).card <
            2 * DMinus))
    (core_owner_active :
      ∀ leaf ∈
          receipt.core ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 anchor),
        owner leaf ∈ activeChildren)
    (coreCenterNonempty :
      (receipt.core ∩
        quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 anchor)).Nonempty)
    (containedChildren : Set Point3 → Finset Child)
    (containedLeafSet : Set Point3 → Finset (Fin fine.card))
    (contained_subset :
      ∀ convexSet,
        containedChildren convexSet ⊆ activeChildren)
    (target_count :
      ∀ convexSet,
        target.containedCount convexSet =
          (containedChildren convexSet).card)
    (target_card :
      target.enncard = (activeChildren.card : ENNReal))
    (contained_packet :
      ∀ convexSet,
        ∀ child ∈ containedChildren convexSet,
          ((wholeLeaves ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 anchor)).filter
            fun leaf => owner leaf = child) ⊆
              containedLeafSet convexSet)
    (sourceConstant : ENNReal)
    (ambient_cwa :
      ∀ convexSet, Convex ℝ convexSet →
        ((containedLeafSet convexSet).card : ENNReal) ≤
          sourceConstant *
            (pureWZ2Prop62UpperEnvelopeGeometricLoss *
              volume convexSet) *
            ((auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) anchor).card : ENNReal)) :
    WZ2PaperBodyConvexWolffBound target
      ((pureWZ2Prop62ReceiptDensityLoss
          (schedule.levelCount + 1) fine.card preliminary.card *
        sourceConstant) *
        pureWZ2Prop62UpperEnvelopeGeometricLoss * 2) := by
  have centerPrefix :
      wholeLeaves ∩
          quotient.centerPacketIndices coordinate.1
            (quotient.leafCenter coordinate.1 anchor) =
        wholeLeaves ∩
          auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor :=
    coloring.monochromatic_centerPacket_inter_prefixNode
      fineLine fineBase wholeLeaves selectedColor monochromatic
      auxiliary anchor anchorMem coordinate
  let preCoreLeaves :=
    wholeLeaves ∩
      auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor
  let coreLeaves :=
    receipt.core ∩
      quotient.centerPacketIndices coordinate.1
        (quotient.leafCenter coordinate.1 anchor)
  have coreSubset :
      coreLeaves ⊆ preCoreLeaves := by
    intro leaf leafMem
    have leafData := Finset.mem_inter.mp leafMem
    change
      leaf ∈
        wholeLeaves ∩
          auxiliary.prefixNodeAt (coordinate.1.1 + 1) anchor
    rw [← centerPrefix]
    exact
      Finset.mem_inter.mpr
        ⟨preliminary_subset_wholeLeaves
            (receipt.core_subset leafData.1),
          leafData.2⟩
  have density :=
    coloring.receipt_centerPacket_density
      fineLine fineBase wholeLeaves preliminary
      preliminary_subset_wholeLeaves selectedColor monochromatic
      auxiliary receipt anchor anchorMem coordinate coreCenterNonempty
  exact
    pureWZ2_prop62_quotientPrefix_upper_parent_body_cwa
      target owner preCoreLeaves coreLeaves activeChildren
      DMinus DMinus_pos
      (by
        intro child childMem
        change
          DMinus ≤
              ((wholeLeaves ∩
                auxiliary.prefixNodeAt
                  (coordinate.1.1 + 1) anchor).filter
                fun leaf => owner leaf = child).card ∧
            (((wholeLeaves ∩
                auxiliary.prefixNodeAt
                  (coordinate.1.1 + 1) anchor).filter
                fun leaf => owner leaf = child).card <
              2 * DMinus)
        rw [← centerPrefix]
        exact preCore_fiber_band child childMem)
      coreSubset
      (by simpa only [coreLeaves] using core_owner_active)
      (auxiliary.prefixNodeAt
        (coordinate.1.1 + 1) anchor).card
      coreLeaves.card rfl
      (pureWZ2Prop62ReceiptDensityLoss
        (schedule.levelCount + 1) fine.card preliminary.card)
      sourceConstant density
      containedChildren containedLeafSet contained_subset
      target_count target_card
      (by
        intro convexSet child childMem
        change
          ((wholeLeaves ∩
            auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) anchor).filter
            fun leaf => owner leaf = child) ⊆
              containedLeafSet convexSet
        rw [← centerPrefix]
        exact contained_packet convexSet child childMem)
      ambient_cwa

/--
Concrete per-coordinate CWA for one parent of the exact monochromatic upper
cover.

The active and contained children are the ambient images of the genuine
strict fiber of `coverData`.  The `DMinus` band is used on `wholeLeaves`,
whereas `receipt.node_density` is used on `preliminary`.  The hypotheses
`preliminary_subset_wholeLeaves` and `core_parent_selected` are the only
bridges between those two stages.  In particular, the conclusion contains
one receipt-density factor and no copy-packing factor.
-/
theorem quotientUpperCover_parent_body_cwa
    {width : ℝ}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (wholeLeaves preliminary : Finset (Fin fine.card))
    (preliminary_subset_wholeLeaves :
      preliminary ⊆ wholeLeaves)
    (selectedColor :
      ∀ _coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
    (monochromatic :
      ∀ source ∈ wholeLeaves,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor coordinate source =
            selectedColor coordinate)
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)
    (receipt :
      PureWZ2Prop62CleanupReceipt auxiliary.tree preliminary)
    (output :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (selectedChildren :
      WZ2PaperPureTubeSubfamily output.metricParents)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (coverData :
      (output.upperEnvelopeScaleInput
        fineLine fineBase rhoPos coordinate).MonochromaticCoverData
          (coloring.toUpperEnvelopeColoring
            output fineLine fineBase rhoPos coordinate)
          selectedChildren)
    (parent : Fin coverData.selectedParents.family.card)
    (normalization :
      WZ2PaperAssouadUnitRescalingData
        (coverData.selectedParents.family.tube parent))
    (anchor : Fin fine.card)
    (anchorMem : anchor ∈ receipt.core)
    (anchor_owner :
      (output.upperEnvelopeScaleInput
        fineLine fineBase rhoPos coordinate).owner
          (output.ambientMetricParentOf anchor) =
        coverData.selectedParents.embedding parent)
    (core_parent_selected :
      ∀ leaf ∈ receipt.core,
        output.ambientMetricParentOf leaf ∈
          Finset.image selectedChildren.embedding Finset.univ)
    (leafCenter_eq_upperCenter :
      ∀ leaf ∈ wholeLeaves,
        quotient.leafCenter coordinate.1 leaf =
          output.upperQuotientCenter coordinate
            (output.ambientMetricParentOf leaf))
    (DMinus : ℕ)
    (DMinus_pos : 0 < DMinus)
    (wholeMetricFiber_band :
      ∀ child ∈
          pureWZ2Prop62UpperCoverAmbientFiber
            selectedChildren coverData.selectedParents.family parent,
        DMinus ≤
            (wholeLeaves.filter fun leaf =>
              output.ambientMetricParentOf leaf = child).card ∧
          (wholeLeaves.filter fun leaf =>
            output.ambientMetricParentOf leaf = child).card <
              2 * DMinus)
    (containedLeafSet :
      Set Point3 → Finset (Fin fine.card))
    (contained_packet :
      ∀ convexSet,
        ∀ child ∈
            pureWZ2Prop62UpperCoverContainedAmbientFiber
              selectedChildren coverData.selectedParents.family
              parent normalization convexSet,
          ((wholeLeaves ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 anchor)).filter
            fun leaf =>
              output.ambientMetricParentOf leaf = child) ⊆
                containedLeafSet convexSet)
    (sourceConstant : ENNReal)
    (ambient_cwa :
      ∀ convexSet, Convex ℝ convexSet →
        ((containedLeafSet convexSet).card : ENNReal) ≤
          sourceConstant *
            (pureWZ2Prop62UpperEnvelopeGeometricLoss *
              volume convexSet) *
            ((auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) anchor).card : ENNReal)) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := selectedChildren.family)
        (coarse := coverData.selectedParents.family)
        parent normalization)
      ((pureWZ2Prop62ReceiptDensityLoss
          (schedule.levelCount + 1) fine.card preliminary.card *
        sourceConstant) *
        pureWZ2Prop62UpperEnvelopeGeometricLoss * 2) := by
  let activeChildren :=
    pureWZ2Prop62UpperCoverAmbientFiber
      selectedChildren coverData.selectedParents.family parent
  let containedChildren :=
    fun convexSet =>
      pureWZ2Prop62UpperCoverContainedAmbientFiber
        selectedChildren coverData.selectedParents.family
        parent normalization convexSet
  change
    output.upperEnvelopeOwner coordinate
        (output.ambientMetricParentOf anchor) =
      coverData.selectedParents.embedding parent at anchor_owner
  have anchorWhole : anchor ∈ wholeLeaves :=
    preliminary_subset_wholeLeaves
      (receipt.core_subset anchorMem)
  have active_center :
      ∀ child ∈ activeChildren,
        output.upperQuotientCenter coordinate child =
          quotient.leafCenter coordinate.1 anchor := by
    intro child childMem
    rcases Finset.mem_image.mp childMem with
      ⟨selectedChild, selectedChildMem, rfl⟩
    have childOwner :
        (output.upperEnvelopeScaleInput
          fineLine fineBase rhoPos coordinate).owner
            (selectedChildren.embedding selectedChild) =
          coverData.selectedParents.embedding parent := by
      have filteredMem :
          selectedChild ∈
            Finset.univ.filter fun current =>
              (output.upperEnvelopeScaleInput
                fineLine fineBase rhoPos coordinate).owner
                  (selectedChildren.embedding current) =
                coverData.selectedParents.embedding parent := by
        rw [← coverData.fullFiberIndices_eq_owner parent]
        exact selectedChildMem
      exact (Finset.mem_filter.mp filteredMem).2
    change
      output.upperEnvelopeOwner coordinate
          (selectedChildren.embedding selectedChild) =
        coverData.selectedParents.embedding parent at childOwner
    calc
      output.upperQuotientCenter coordinate
          (selectedChildren.embedding selectedChild) =
          (output.upperCenters coordinate).embedding
            (output.upperEnvelopeOwner coordinate
              (selectedChildren.embedding selectedChild)) :=
        (output.upperEnvelopeOwner_ambient coordinate _).symm
      _ =
          (output.upperCenters coordinate).embedding
            (output.upperEnvelopeOwner coordinate
              (output.ambientMetricParentOf anchor)) := by
        rw [childOwner, anchor_owner]
      _ =
          output.upperQuotientCenter coordinate
            (output.ambientMetricParentOf anchor) :=
        output.upperEnvelopeOwner_ambient coordinate _
      _ = quotient.leafCenter coordinate.1 anchor :=
        (leafCenter_eq_upperCenter anchor anchorWhole).symm
  have centeredFiber_eq :
      ∀ child ∈ activeChildren,
        (wholeLeaves ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 anchor)).filter
            (fun leaf =>
              output.ambientMetricParentOf leaf = child) =
          wholeLeaves.filter fun leaf =>
            output.ambientMetricParentOf leaf = child := by
    intro child childMem
    ext leaf
    simp only [Finset.mem_filter, Finset.mem_inter,
      PureWZ2Prop62ProxyQuotientScheduleData.centerPacketIndices,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨leafWhole, _leafCenter⟩, leafOwner⟩
      exact ⟨leafWhole, leafOwner⟩
    · rintro ⟨leafWhole, leafOwner⟩
      refine ⟨⟨leafWhole, ?_⟩, leafOwner⟩
      rw [leafCenter_eq_upperCenter leaf leafWhole, leafOwner]
      exact active_center child childMem
  have preCoreFiberBand :
      ∀ child ∈ activeChildren,
        DMinus ≤
            ((wholeLeaves ∩
              quotient.centerPacketIndices coordinate.1
                (quotient.leafCenter coordinate.1 anchor)).filter
              fun leaf =>
                output.ambientMetricParentOf leaf = child).card ∧
          (((wholeLeaves ∩
              quotient.centerPacketIndices coordinate.1
                (quotient.leafCenter coordinate.1 anchor)).filter
              fun leaf =>
                output.ambientMetricParentOf leaf = child).card <
            2 * DMinus) := by
    intro child childMem
    rw [centeredFiber_eq child childMem]
    exact wholeMetricFiber_band child childMem
  have coreOwnerActive :
      ∀ leaf ∈
          receipt.core ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 anchor),
        output.ambientMetricParentOf leaf ∈ activeChildren := by
    intro leaf leafMem
    have leafCore := (Finset.mem_inter.mp leafMem).1
    have leafCenter := (Finset.mem_inter.mp leafMem).2
    rcases Finset.mem_image.mp
        (core_parent_selected leaf leafCore) with
      ⟨selectedChild, _selectedChildMem, childEq⟩
    refine Finset.mem_image.mpr ⟨selectedChild, ?_, childEq⟩
    rw [coverData.fullFiberIndices_eq_owner]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ selectedChild, ?_⟩
    change
      (output.upperEnvelopeScaleInput
        fineLine fineBase rhoPos coordinate).owner
          (selectedChildren.embedding selectedChild) =
        coverData.selectedParents.embedding parent
    have selectedCenterEq :
        output.upperQuotientCenter coordinate
            (selectedChildren.embedding selectedChild) =
          output.upperQuotientCenter coordinate
            (output.ambientMetricParentOf anchor) := by
      rw [childEq]
      rw [← leafCenter_eq_upperCenter leaf <|
        preliminary_subset_wholeLeaves
          (receipt.core_subset leafCore)]
      rw [← leafCenter_eq_upperCenter anchor anchorWhole]
      simpa [
        PureWZ2Prop62ProxyQuotientScheduleData.centerPacketIndices
      ] using leafCenter
    have ownerEq :
        output.upperEnvelopeOwner coordinate
            (selectedChildren.embedding selectedChild) =
          output.upperEnvelopeOwner coordinate
            (output.ambientMetricParentOf anchor) := by
      apply (output.upperCenters coordinate).embedding.injective
      rw [output.upperEnvelopeOwner_ambient,
        output.upperEnvelopeOwner_ambient]
      exact selectedCenterEq
    exact ownerEq.trans anchor_owner
  have coreCenterNonempty :
      (receipt.core ∩
        quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 anchor)).Nonempty := by
    refine ⟨anchor, Finset.mem_inter.mpr ⟨anchorMem, ?_⟩⟩
    simp [PureWZ2Prop62ProxyQuotientScheduleData.centerPacketIndices]
  have containedSubset :
      ∀ convexSet,
        containedChildren convexSet ⊆ activeChildren := by
    intro convexSet child childMem
    rcases Finset.mem_image.mp childMem with
      ⟨selectedChild, selectedChildMem, rfl⟩
    exact Finset.mem_image.mpr
      ⟨selectedChild, (Finset.mem_filter.mp selectedChildMem).1, rfl⟩
  have targetCount :
      ∀ convexSet,
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := selectedChildren.family)
          (coarse := coverData.selectedParents.family)
          parent normalization).containedCount convexSet =
            (containedChildren convexSet).card := by
    intro convexSet
    rw [pureWZ2_prop62_quotientUpperFullFiber_containedCount_eq]
    change
      (((wz2PaperOrdinaryFullFiberIndices
        selectedChildren.family coverData.selectedParents.family
        parent).filter fun source =>
          normalization.map ''
              (selectedChildren.family.tube source).carrier ⊆
            convexSet).card : ENNReal) =
        ((Finset.image selectedChildren.embedding
          ((wz2PaperOrdinaryFullFiberIndices
            selectedChildren.family coverData.selectedParents.family
            parent).filter fun source =>
              normalization.map ''
                  (selectedChildren.family.tube source).carrier ⊆
                convexSet)).card : ℕ)
    exact_mod_cast
      (Finset.card_image_of_injective _
        selectedChildren.embedding.injective).symm
  have targetCard :
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := selectedChildren.family)
        (coarse := coverData.selectedParents.family)
        parent normalization).enncard =
          (activeChildren.card : ENNReal) := by
    change
      ((wz2PaperOrdinaryFullFiberIndices
        selectedChildren.family coverData.selectedParents.family
        parent).card : ENNReal) =
        ((Finset.image selectedChildren.embedding
          (wz2PaperOrdinaryFullFiberIndices
            selectedChildren.family coverData.selectedParents.family
            parent)).card : ℕ)
    exact_mod_cast
      (Finset.card_image_of_injective _
        selectedChildren.embedding.injective).symm
  exact
    coloring.quotientPrefix_upper_parent_body_cwa
      fineLine fineBase wholeLeaves preliminary
      preliminary_subset_wholeLeaves selectedColor monochromatic
      auxiliary receipt anchor anchorWhole coordinate
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := selectedChildren.family)
        (coarse := coverData.selectedParents.family)
        parent normalization)
      output.ambientMetricParentOf activeChildren DMinus DMinus_pos
      preCoreFiberBand coreOwnerActive coreCenterNonempty
      containedChildren containedLeafSet containedSubset
      targetCount targetCard contained_packet sourceConstant ambient_cwa

/--
Joint wrapper exposing both conclusions needed at an upper level.  `Bcopy`
appears only in prefix-fiber uniformity; the CWA component still pays exactly
one receipt density factor.
-/
theorem quotientPrefix_upper_parent_cwa_and_uniformity
    {width : ℝ}
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (wholeLeaves preliminary : Finset (Fin fine.card))
    (preliminary_subset_wholeLeaves :
      preliminary ⊆ wholeLeaves)
    (selectedColor :
      ∀ _coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
    (monochromatic :
      ∀ source ∈ wholeLeaves,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor coordinate source =
            selectedColor coordinate)
    (auxiliary :
      PureWZ2Prop62ProxyQuotientAuxiliaryLevel
        schedule fineNonempty quotient rho width packetCoordinate)
    (receipt :
      PureWZ2Prop62CleanupReceipt auxiliary.tree preliminary)
    (firstAnchor secondAnchor : Fin fine.card)
    (firstAnchorMem : firstAnchor ∈ wholeLeaves)
    (secondAnchorMem : secondAnchor ∈ wholeLeaves)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (target : Kakeya.Streamlined.BodyFamily)
    {Child : Type}
    [Fintype Child] [DecidableEq Child]
    (owner : Fin fine.card → Child)
    (activeChildren : Finset Child)
    (DMinus Bcopy : ℕ)
    (DMinus_pos : 0 < DMinus)
    (preCore_fiber_band :
      ∀ child ∈ activeChildren,
        DMinus ≤
            ((wholeLeaves ∩
              quotient.centerPacketIndices coordinate.1
                (quotient.leafCenter coordinate.1 firstAnchor)).filter
              fun leaf => owner leaf = child).card ∧
          (((wholeLeaves ∩
              quotient.centerPacketIndices coordinate.1
                (quotient.leafCenter coordinate.1 firstAnchor)).filter
              fun leaf => owner leaf = child).card <
            2 * DMinus))
    (core_owner_active :
      ∀ leaf ∈
          receipt.core ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 firstAnchor),
        owner leaf ∈ activeChildren)
    (firstCoreNonempty :
      (receipt.core ∩
        quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 firstAnchor)).Nonempty)
    (secondCoreNonempty :
      (receipt.core ∩
        quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 secondAnchor)).Nonempty)
    (containedChildren : Set Point3 → Finset Child)
    (containedLeafSet : Set Point3 → Finset (Fin fine.card))
    (contained_subset :
      ∀ convexSet,
        containedChildren convexSet ⊆ activeChildren)
    (target_count :
      ∀ convexSet,
        target.containedCount convexSet =
          (containedChildren convexSet).card)
    (target_card :
      target.enncard = (activeChildren.card : ENNReal))
    (contained_packet :
      ∀ convexSet,
        ∀ child ∈ containedChildren convexSet,
          ((wholeLeaves ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 firstAnchor)).filter
            fun leaf => owner leaf = child) ⊆
              containedLeafSet convexSet)
    (sourceConstant ambientConstant : ENNReal)
    (ambient_cwa :
      ∀ convexSet, Convex ℝ convexSet →
        ((containedLeafSet convexSet).card : ENNReal) ≤
          sourceConstant *
            (pureWZ2Prop62UpperEnvelopeGeometricLoss *
              volume convexSet) *
            ((auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) firstAnchor).card : ENNReal))
    (firstPacketCard secondPacketCard : ℕ)
    (first_prefix_upper :
      (auxiliary.prefixNodeAt
        (coordinate.1.1 + 1) firstAnchor).card ≤
          Bcopy * firstPacketCard)
    (second_packet_lower :
      secondPacketCard ≤
        (auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) secondAnchor).card)
    (packet_uniform :
      (firstPacketCard : ENNReal) ≤
        ambientConstant * (secondPacketCard : ENNReal)) :
    WZ2PaperBodyConvexWolffBound target
        ((pureWZ2Prop62ReceiptDensityLoss
            (schedule.levelCount + 1) fine.card preliminary.card *
          sourceConstant) *
          pureWZ2Prop62UpperEnvelopeGeometricLoss * 2) ∧
      (((receipt.core ∩
        quotient.centerPacketIndices coordinate.1
          (quotient.leafCenter coordinate.1 firstAnchor)).card :
          ENNReal) ≤
        ((Bcopy : ENNReal) * ambientConstant *
          pureWZ2Prop62ReceiptDensityLoss
            (schedule.levelCount + 1) fine.card preliminary.card) *
          ((receipt.core ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 secondAnchor)).card :
            ENNReal)) := by
  constructor
  · exact
      coloring.quotientPrefix_upper_parent_body_cwa
        fineLine fineBase wholeLeaves preliminary
        preliminary_subset_wholeLeaves selectedColor monochromatic
        auxiliary receipt firstAnchor firstAnchorMem coordinate
        target owner activeChildren DMinus DMinus_pos
        preCore_fiber_band core_owner_active firstCoreNonempty
        containedChildren containedLeafSet contained_subset
        target_count target_card contained_packet sourceConstant
        ambient_cwa
  · have ambientUniform :=
      pureWZ2_prop62_quotientPrefix_ambient_uniformity
        (auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) firstAnchor).card
        (auxiliary.prefixNodeAt
          (coordinate.1.1 + 1) secondAnchor).card
        firstPacketCard secondPacketCard Bcopy ambientConstant
        first_prefix_upper second_packet_lower packet_uniform
    have treeFirst :=
      auxiliary.tree_fiber_upperCoordinate_prefix_eq
        coordinate firstAnchor
    have treeSecond :=
      auxiliary.tree_fiber_upperCoordinate_prefix_eq
        coordinate secondAnchor
    have selectedFirst :=
      coloring.monochromatic_centerPacket_inter_prefixNode
        fineLine fineBase wholeLeaves selectedColor monochromatic
        auxiliary firstAnchor firstAnchorMem coordinate
    have selectedSecond :=
      coloring.monochromatic_centerPacket_inter_prefixNode
        fineLine fineBase wholeLeaves selectedColor monochromatic
        auxiliary secondAnchor secondAnchorMem coordinate
    have coreSubsetWholeLeaves :
        receipt.core ⊆ wholeLeaves :=
      receipt.core_subset.trans preliminary_subset_wholeLeaves
    have coreFirst :
        receipt.core ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 firstAnchor) =
          receipt.core ∩
            auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) firstAnchor := by
      exact
        pureWZ2_prop62_inter_eq_of_selected_inter_eq
          wholeLeaves receipt.core
          (quotient.centerPacketIndices coordinate.1
            (quotient.leafCenter coordinate.1 firstAnchor))
          (auxiliary.prefixNodeAt
            (coordinate.1.1 + 1) firstAnchor)
          coreSubsetWholeLeaves selectedFirst
    have coreSecond :
        receipt.core ∩
            quotient.centerPacketIndices coordinate.1
              (quotient.leafCenter coordinate.1 secondAnchor) =
          receipt.core ∩
            auxiliary.prefixNodeAt
              (coordinate.1.1 + 1) secondAnchor := by
      exact
        pureWZ2_prop62_inter_eq_of_selected_inter_eq
          wholeLeaves receipt.core
          (quotient.centerPacketIndices coordinate.1
            (quotient.leafCenter coordinate.1 secondAnchor))
          (auxiliary.prefixNodeAt
            (coordinate.1.1 + 1) secondAnchor)
          coreSubsetWholeLeaves selectedSecond
    have secondTreeCoreNonempty :
        (receipt.core ∩
          auxiliary.tree.fiber (coordinate.1.1 + 1)
            (auxiliary.nodeAt
              (coordinate.1.1 + 1) secondAnchor)).Nonempty := by
      rw [treeSecond, ← coreSecond]
      exact secondCoreNonempty
    have uniformity :=
      pureWZ2_prop62_receipt_upper_prefix_uniformity
        auxiliary.tree preliminary receipt
        (coordinate.1.1 + 1) (by omega)
        (auxiliary.nodeAt
          (coordinate.1.1 + 1) firstAnchor)
        (auxiliary.nodeAt
          (coordinate.1.1 + 1) secondAnchor)
        secondTreeCoreNonempty Bcopy ambientConstant <| by
          rw [treeFirst, treeSecond]
          exact ambientUniform
    rw [treeFirst, treeSecond, ← coreFirst, ← coreSecond]
      at uniformity
    simpa [pureWZ2Prop62ReceiptDensityLoss,
      Fintype.card_fin, mul_assoc] using uniformity

end PureWZ2Prop62UpperEnvelopeCenterColoringData

end Kakeya.Assouad

end

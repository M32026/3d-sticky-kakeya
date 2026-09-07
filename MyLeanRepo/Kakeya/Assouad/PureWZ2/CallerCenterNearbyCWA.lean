import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParentQuotientNetSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryEnvelopeContainment

/-!
# Caller-center envelope cover at one scheduled scale

For each quotient caller, use its stored ambient center source as a common
ordinary child of the caller tube and one scheduled Definition 2.12 parent.
The caller tube is therefore contained in the factor-`19` envelope of that
scheduled parent.

A proper coloring of the envelope conflict graph is kept as an explicit
input.  Any later monochromatic caller subfamily inherits a literal pure
partitioning cover whose strict full fibers are exactly the scheduled-owner
classes.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

noncomputable def pureWZ2CallerCenterScheduledOwner
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant)
    (caller :
      Fin quotient.callerCoarse.card) :
    Fin scheduled.scaleData.coarse.card :=
  scheduled.scaleData.cover.parent
    (quotient.representative
      (quotient.net.centerEmbedding
        (quotient.callerCenter caller)))

theorem pureWZ2CallerCenterScheduledOwner_containment
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant)
    (hcallerScheduled : callerRequested.1 ≤ scheduled.rho)
    (caller :
      Fin quotient.callerCoarse.card) :
    (quotient.callerCoarse.tube caller).carrier ⊆
      ((wz2PaperOrdinaryEnvelopeFamily
        scheduled.scaleData.coarse).tube
          (pureWZ2CallerCenterScheduledOwner
            quotient scheduled caller)).carrier := by
  let source :=
    quotient.representative
      (quotient.net.centerEmbedding
        (quotient.callerCenter caller))
  have hsourceCaller :
      (fine.tube source).carrier ⊆
        (quotient.callerCoarse.tube caller).carrier := by
    exact quotient.callerCenterSource_carrier_subset caller
  have hsourceScheduled :
      (fine.tube source).carrier ⊆
        (scheduled.scaleData.coarse.tube
          (pureWZ2CallerCenterScheduledOwner
            quotient scheduled caller)).carrier := by
    have hmember :=
      scheduled.scaleData.cover.parent_mem_fullFiber source
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hmember
    exact hmember
  exact
    wz2_paper_ordinary_middle_carrier_subset_envelope
      scheduled.scaleData.delta_pos
      (scheduled.scaleData.delta_pos.trans_le callerRequested.2.1)
      scheduled.scaleData.rho_pos
      hcallerScheduled
      (fine.tube source)
      (quotient.callerCoarse.tube caller)
      (scheduled.scaleData.coarse.tube
        (pureWZ2CallerCenterScheduledOwner
          quotient scheduled caller))
      hsourceCaller hsourceScheduled

structure PureWZ2CallerCenterEnvelopeColoringData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant)
    (callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (Color : Type*) where
  color :
    Fin scheduled.scaleData.coarse.card → Color
  proper :
    ∀ first second,
      first ≠ second →
      (wz2PaperOrdinaryDilatedFiberIndices
          2 callerBase.family
          (wz2PaperOrdinaryEnvelopeFamily
            scheduled.scaleData.coarse) first ∩
        wz2PaperOrdinaryDilatedFiberIndices
          2 callerBase.family
          (wz2PaperOrdinaryEnvelopeFamily
            scheduled.scaleData.coarse) second).Nonempty →
      color first ≠ color second

/--
Produce a proper coloring once a uniform degree bound for the actual
centered-doubled envelope conflict graph has been proved.
-/
theorem pureWZ2_caller_center_envelope_coloring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant)
    (callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (degree : ℕ)
    (conflictDegree :
      ∀ fixed : Fin scheduled.scaleData.coarse.card,
        (Finset.univ.filter fun other =>
          other ≠ fixed ∧
            (wz2PaperOrdinaryDilatedFiberIndices
                2 callerBase.family
                (wz2PaperOrdinaryEnvelopeFamily
                  scheduled.scaleData.coarse) fixed ∩
              wz2PaperOrdinaryDilatedFiberIndices
                2 callerBase.family
                (wz2PaperOrdinaryEnvelopeFamily
                  scheduled.scaleData.coarse) other).Nonempty).card ≤
          degree) :
    Nonempty
      (PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase (Fin (degree + 1))) := by
  let conflict :
      Fin scheduled.scaleData.coarse.card →
        Fin scheduled.scaleData.coarse.card → Prop :=
    fun first second =>
      second ≠ first ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 callerBase.family
            (wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse) first ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 callerBase.family
            (wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse) second).Nonempty
  have conflictSymmetric :
      ∀ first second,
        conflict first second →
          conflict second first := by
    intro first second hconflict
    exact
      ⟨hconflict.1.symm, by
        simpa [Finset.inter_comm] using hconflict.2⟩
  have conflictIrreflexive :
      ∀ parent, ¬conflict parent parent := by
    intro parent hconflict
    exact hconflict.1 rfl
  rcases
      pureWZ2_greedy_proper_coloring
        (D := degree)
        conflictSymmetric conflictIrreflexive
        (fun parent => by
          rw [Finset.filter_congr_decidable]
          exact conflictDegree parent)
    with
    ⟨color, proper⟩
  exact
    ⟨{
      color := color
      proper := by
        intro first second hne hoverlap
        exact proper first second ⟨hne.symm, hoverlap⟩
    }⟩

structure PureWZ2CallerCenterMonochromaticEnvelopeCoverData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {scheduledRequested : WZ2PaperRequestedScale delta}
    {scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant}
    {callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse}
    {Color : Type*}
    (coloring :
      PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase Color)
    (selected :
      WZ2PaperPureTubeSubfamily callerBase.family) where
  selectedCoarse :
    WZ2PaperPureTubeSubfamily
      (wz2PaperOrdinaryEnvelopeFamily
        scheduled.scaleData.coarse)
  cover :
    WZ2PaperPurePartitioningCover
      selected.family selectedCoarse.family
  parent_owner_eq :
    ∀ index,
      selectedCoarse.embedding (cover.parent index) =
        pureWZ2CallerCenterScheduledOwner
          quotient scheduled
          (callerBase.embedding (selected.embedding index))
  fullFiberIndices_eq_owner :
    ∀ parent,
      wz2PaperOrdinaryFullFiberIndices
          selected.family selectedCoarse.family parent =
        Finset.univ.filter fun index =>
          pureWZ2CallerCenterScheduledOwner
              quotient scheduled
              (callerBase.embedding
                (selected.embedding index)) =
            selectedCoarse.embedding parent
  full_fiber_nonempty :
    ∀ parent,
      (wz2PaperOrdinaryFullFiberIndices
        selected.family selectedCoarse.family parent).Nonempty

namespace PureWZ2CallerCenterMonochromaticEnvelopeCoverData

/--
Complete one-scale assembly after the two quantitative inputs have been
proved: strict-fiber cardinality uniformity and parentwise actual Body CWA.
-/
noncomputable def toPureScaleData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {scheduledRequested : WZ2PaperRequestedScale delta}
    {scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant}
    {callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse}
    {Color : Type*}
    {coloring :
      PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase Color}
    {selected :
      WZ2PaperPureTubeSubfamily callerBase.family}
    (data :
      PureWZ2CallerCenterMonochromaticEnvelopeCoverData
        coloring selected)
    (coverConstant bodyConstant : ENNReal)
    (fullFiberUniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family data.selectedCoarse.family coverConstant)
    (normalization :
      ∀ parent : Fin data.selectedCoarse.family.card,
        WZ2PaperAssouadUnitRescalingData
          (data.selectedCoarse.family.tube parent))
    (fiberCWA :
      ∀ parent : Fin data.selectedCoarse.family.card,
        WZ2PaperBodyConvexWolffBound
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := selected.family)
            (coarse := data.selectedCoarse.family)
            parent (normalization parent))
          bodyConstant) :
    WZ2PaperPureScaleCoverData
      selected.family (19 * scheduled.rho)
      (max coverConstant bodyConstant) where
  delta_pos :=
    scheduled.scaleData.delta_pos.trans_le
      callerRequested.2.1
  rho_pos := mul_pos (by norm_num) scheduled.scaleData.rho_pos
  coarse := data.selectedCoarse.family
  cover := data.cover
  full_fiber_uniform first second :=
    (fullFiberUniform first second).trans <| by
      gcongr
      exact le_max_left _ _
  rescaledFiber parent :=
    ⟨{
      normalization := normalization parent
      convex_wolff := fun convexSet hconvex =>
        (fiberCWA parent convexSet hconvex).trans <| by
          gcongr
          exact le_max_right coverConstant bodyConstant
    }⟩

end PureWZ2CallerCenterMonochromaticEnvelopeCoverData

theorem PureWZ2CallerCenterEnvelopeColoringData.monochromatic_cover
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {scheduledRequested : WZ2PaperRequestedScale delta}
    {scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant}
    {callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse}
    {Color : Type*}
    (coloring :
      PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase Color)
    (selected :
      WZ2PaperPureTubeSubfamily callerBase.family)
    (selectedColor : Color)
    (monochromatic :
      ∀ index,
        coloring.color
            (pureWZ2CallerCenterScheduledOwner
              quotient scheduled
              (callerBase.embedding
                (selected.embedding index))) =
          selectedColor)
    (hcallerScheduled : callerRequested.1 ≤ scheduled.rho) :
    Nonempty
      (PureWZ2CallerCenterMonochromaticEnvelopeCoverData
        coloring selected) := by
  let owner :
      Fin selected.family.card →
        Fin scheduled.scaleData.coarse.card :=
    fun index =>
      pureWZ2CallerCenterScheduledOwner
        quotient scheduled
        (callerBase.embedding (selected.embedding index))
  let parentIndices :
      Finset (Fin scheduled.scaleData.coarse.card) :=
    Finset.univ.image owner
  let selectedCoarse :
      WZ2PaperPureTubeSubfamily
        (wz2PaperOrdinaryEnvelopeFamily
          scheduled.scaleData.coarse) :=
    WZ2PaperPureTubeSubfamily.fromFinset
      (wz2PaperOrdinaryEnvelopeFamily
        scheduled.scaleData.coarse)
      parentIndices
  let parentEquiv :
      Fin parentIndices.card ≃ parentIndices :=
    (parentIndices.orderIsoOfFin rfl).toEquiv
  have ownerMem :
      ∀ index, owner index ∈ parentIndices := by
    intro index
    exact Finset.mem_image.mpr
      ⟨index, Finset.mem_univ index, rfl⟩
  let parent :
      Fin selected.family.card →
        Fin selectedCoarse.family.card :=
    fun index =>
      parentEquiv.symm ⟨owner index, ownerMem index⟩
  have parentAmbient :
      ∀ index,
        selectedCoarse.embedding (parent index) =
          owner index := by
    intro index
    exact congrArg Subtype.val
      (parentEquiv.apply_symm_apply
        ⟨owner index, ownerMem index⟩)
  have ownerContainment :
      ∀ index,
        (selected.family.tube index).carrier ⊆
          (selectedCoarse.family.tube
            (parent index)).carrier := by
    intro index
    rw [selected.tube_eq, callerBase.tube_eq,
      selectedCoarse.tube_eq, parentAmbient]
    exact
      pureWZ2CallerCenterScheduledOwner_containment
        quotient scheduled hcallerScheduled
        (callerBase.embedding (selected.embedding index))
  have coverExistence :
      ∀ index,
        ∃ coarseIndex,
          index ∈
            wz2PaperOrdinaryFullFiberIndices
              selected.family selectedCoarse.family
              coarseIndex := by
    intro index
    refine ⟨parent index, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact ownerContainment index
  have coarseColor :
      ∀ parentIndex,
        coloring.color
            (selectedCoarse.embedding parentIndex) =
          selectedColor := by
    intro parentIndex
    have hparent :
        selectedCoarse.embedding parentIndex ∈
          parentIndices :=
      Finset.orderEmbOfFin_mem parentIndices rfl parentIndex
    rcases Finset.mem_image.mp hparent with
      ⟨index, _, hindex⟩
    rw [← hindex]
    exact monochromatic index
  have doubledDisjoint :
      ∀ first second : Fin selectedCoarse.family.card,
        first ≠ second →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices
            2 selected.family selectedCoarse.family first)
          (wz2PaperOrdinaryDilatedFiberIndices
            2 selected.family selectedCoarse.family second) := by
    intro first second hne
    rw [Finset.disjoint_left]
    intro index hfirst hsecond
    have hbaseFirst :
        selected.embedding index ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 callerBase.family
            (wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse)
            (selectedCoarse.embedding first) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq, selectedCoarse.tube_eq
      ] using hfirst
    have hbaseSecond :
        selected.embedding index ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 callerBase.family
            (wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse)
            (selectedCoarse.embedding second) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq, selectedCoarse.tube_eq
      ] using hsecond
    have hambientNe :
        selectedCoarse.embedding first ≠
          selectedCoarse.embedding second :=
      selectedCoarse.embedding.injective.ne hne
    have hcolorNe :=
      coloring.proper
        (selectedCoarse.embedding first)
        (selectedCoarse.embedding second)
        hambientNe
        ⟨selected.embedding index,
          Finset.mem_inter.mpr
            ⟨hbaseFirst, hbaseSecond⟩⟩
    exact hcolorNe
      ((coarseColor first).trans
        (coarseColor second).symm)
  let cover :
      WZ2PaperPurePartitioningCover
        selected.family selectedCoarse.family :=
    {
      covers := coverExistence
      doubled_fibers_disjoint := doubledDisjoint
    }
  have fullFiberIndices :
      ∀ parentIndex,
        wz2PaperOrdinaryFullFiberIndices
            selected.family selectedCoarse.family parentIndex =
          Finset.univ.filter fun index =>
            owner index =
              selectedCoarse.embedding parentIndex := by
    intro parentIndex
    ext index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    constructor
    · intro hstrict
      by_contra hne
      have hownerDoubled :
          selected.embedding index ∈
            wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse)
              (owner index) := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        rw [← selected.tube_eq]
        have hparentEq :
            selectedCoarse.family.tube (parent index) =
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse).tube
                (owner index) := by
          rw [selectedCoarse.tube_eq, parentAmbient]
        have hownerContainment := ownerContainment index
        rw [hparentEq] at hownerContainment
        exact
          hownerContainment.trans
            (wz2_paper_carrier_subset_centeredDilatedTwo
              ((wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse).tube
                  (owner index))
              (mul_nonneg (by norm_num)
                scheduled.scaleData.rho_pos.le))
      have hcandidateDoubled :
          selected.embedding index ∈
            wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse)
              (selectedCoarse.embedding parentIndex) := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        simpa only [selected.tube_eq, selectedCoarse.tube_eq] using
          hstrict.trans
            (wz2_paper_carrier_subset_centeredDilatedTwo
              (selectedCoarse.family.tube parentIndex)
              (mul_nonneg (by norm_num)
                scheduled.scaleData.rho_pos.le))
      have hcolorNe :=
        coloring.proper
          (owner index)
          (selectedCoarse.embedding parentIndex)
          hne
          ⟨selected.embedding index,
            Finset.mem_inter.mpr
              ⟨hownerDoubled, hcandidateDoubled⟩⟩
      exact hcolorNe
        ((monochromatic index).trans
          (coarseColor parentIndex).symm)
    · intro howner
      rw [selected.tube_eq, selectedCoarse.tube_eq,
        ← howner]
      rw [callerBase.tube_eq]
      exact
        pureWZ2CallerCenterScheduledOwner_containment
          quotient scheduled hcallerScheduled
          (callerBase.embedding (selected.embedding index))
  have fullFiberNonempty :
      ∀ parentIndex,
        (wz2PaperOrdinaryFullFiberIndices
          selected.family selectedCoarse.family
          parentIndex).Nonempty := by
    intro parentIndex
    have hparent :
        selectedCoarse.embedding parentIndex ∈
          parentIndices :=
      Finset.orderEmbOfFin_mem parentIndices rfl parentIndex
    rcases Finset.mem_image.mp hparent with
      ⟨index, _, hindex⟩
    refine ⟨index, ?_⟩
    rw [fullFiberIndices parentIndex]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ index, hindex⟩
  have parentOwner :
      ∀ index,
        selectedCoarse.embedding (cover.parent index) =
          owner index := by
    intro index
    have hmember :=
      cover.parent_mem_fullFiber index
    rw [fullFiberIndices (cover.parent index)] at hmember
    exact (Finset.mem_filter.mp hmember).2.symm
  exact
    ⟨{
      selectedCoarse := selectedCoarse
      cover := cover
      parent_owner_eq := parentOwner
      fullFiberIndices_eq_owner := fullFiberIndices
      full_fiber_nonempty := fullFiberNonempty
    }⟩

end Kakeya.Assouad

end

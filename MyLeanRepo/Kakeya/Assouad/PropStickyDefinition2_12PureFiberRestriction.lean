import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Restriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OneScaleRescaling
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteFiberRatio

/-!
# Restrict canonical outer-John full-fiber data

An arbitrary subfamily does not preserve a normalized Convex-Wolff bound
with the same constant.  This module proves the exact safe statement needed
after preparation:

* the selected strict full fiber embeds into the ambient strict full fiber;
* both are normalized by the same parent outer-John map;
* an explicit ambient/selected fiber-cardinality ratio pays the change in the
  normalized denominator.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable
open MeasureTheory

/-- Forget the narrow pure subfamily wrapper while retaining tube identities. -/
def WZ2PaperPureTubeSubfamily.toTubeSubfamily
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (selected : WZ2PaperPureTubeSubfamily ambient) :
    Kakeya.Streamlined.TubeSubfamily ambient where
  family := selected.family
  embedding := selected.embedding
  tube_eq := selected.tube_eq

/-- Assouad normalization data is heterogeneously unique after identifying
the parent tube. -/
theorem WZ2PaperAssouadUnitRescalingData.heq_of_parent_eq
    {rho : ℝ}
    {firstParent secondParent : Kakeya.DeltaTube rho}
    (hparent : firstParent = secondParent)
    (first :
      WZ2PaperAssouadUnitRescalingData firstParent)
    (second :
      WZ2PaperAssouadUnitRescalingData secondParent) :
    HEq first second := by
  subst secondParent
  exact heq_of_eq (first.unique second)

/-- Restrict one canonical actual-John full fiber with an explicit cardinality
loss. -/
noncomputable def WZ2PaperPureUnitRescaledFullFiberData.restrict
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientParent : Fin coarse.card}
    {C K : ENNReal}
    (data :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse) ambientParent C)
    (selectedFine : Kakeya.Streamlined.TubeSubfamily fine)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse)
    (parent : Fin selectedCoarse.family.card)
    (hparent : selectedCoarse.embedding parent = ambientParent)
    (hrho : 0 < rho)
    (hcardinality :
      wz2PaperOrdinaryFullFiberCount fine coarse ambientParent ≤
        K *
          wz2PaperOrdinaryFullFiberCount
            selectedFine.family selectedCoarse.family parent) :
    WZ2PaperPureUnitRescaledFullFiberData
      (fine := selectedFine.family)
      (coarse := selectedCoarse.family)
      parent (K * C) := by
  have hparentTube :
      selectedCoarse.family.tube parent =
        coarse.tube ambientParent := by
    rw [selectedCoarse.tube_eq, hparent]
  let selectedNormalization :
      WZ2PaperAssouadUnitRescalingData
        (selectedCoarse.family.tube parent) :=
    hparentTube.symm ▸ data.normalization
  have hnormalization :
      HEq selectedNormalization data.normalization :=
    WZ2PaperAssouadUnitRescalingData.heq_of_parent_eq
      hparentTube selectedNormalization data.normalization
  have hnormalizationMap :
      selectedNormalization.map = data.normalization.map := by
    apply AffineEquiv.ext
    intro point
    simp only [WZ2PaperAssouadUnitRescalingData.map]
    congr
  let selectedFamily :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := selectedFine.family)
      (coarse := selectedCoarse.family)
      parent selectedNormalization
  let ambientFamily :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse)
      ambientParent data.normalization
  let selectedIndex :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := selectedFine.family)
      (coarse := selectedCoarse.family)
      parent
  let ambientIndex :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := coarse)
      ambientParent
  let embedding : Fin selectedFamily.card → Fin ambientFamily.card :=
    fun target => by
      let source := (selectedIndex target).1
      have hsourceSelected :
          source ∈
            wz2PaperOrdinaryFullFiberIndices
              selectedFine.family selectedCoarse.family parent :=
        (selectedIndex target).2
      have hsourceAmbient :
          selectedFine.embedding source ∈
            wz2PaperOrdinaryFullFiberIndices
              fine coarse ambientParent := by
        rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hsourceSelected ⊢
        rw [← hparent]
        simpa only [selectedFine.tube_eq, selectedCoarse.tube_eq] using
          hsourceSelected
      exact ambientIndex.symm
        ⟨selectedFine.embedding source, hsourceAmbient⟩
  have hembeddingInjective : Function.Injective embedding := by
    intro first second heq
    apply selectedIndex.injective
    apply Subtype.ext
    apply selectedFine.embedding.injective
    have hsource :=
      congrArg
        (fun target : Fin ambientFamily.card =>
          (ambientIndex target).1)
        heq
    simpa [embedding] using hsource
  have hcarrier :
      ∀ target,
        (selectedFamily.body target).carrier =
          (ambientFamily.body (embedding target)).carrier := by
    intro target
    have hsource :
        (ambientIndex (embedding target)).1 =
          selectedFine.embedding (selectedIndex target).1 := by
      simp [embedding]
    change
      selectedNormalization.map ''
          (selectedFine.family.tube (selectedIndex target).1).carrier =
        data.normalization.map ''
          (fine.tube (ambientIndex (embedding target)).1).carrier
    rw [hsource, ← selectedFine.tube_eq]
    rw [hnormalizationMap]
  have hcount :
      ∀ region,
        selectedFamily.containedCount region ≤
          ambientFamily.containedCount region := by
    intro region
    let selectedContained := selectedFamily.containedIndices region
    let ambientContained := ambientFamily.containedIndices region
    have himage :
        Finset.image embedding selectedContained ⊆ ambientContained := by
      intro ambientTarget hambientTarget
      rcases Finset.mem_image.mp hambientTarget with
        ⟨target, htarget, rfl⟩
      rw [Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff]
      rw [← hcarrier target]
      exact
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
          htarget
    change (selectedContained.card : ENNReal) ≤
      (ambientContained.card : ENNReal)
    exact_mod_cast
      (calc
        selectedContained.card =
            (Finset.image embedding selectedContained).card :=
          (Finset.card_image_of_injective
            selectedContained hembeddingInjective).symm
        _ ≤ ambientContained.card := Finset.card_le_card himage)
  have henncard :
      ambientFamily.enncard ≤ K * selectedFamily.enncard := by
    change
      ((wz2PaperOrdinaryFullFiberIndices
        fine coarse ambientParent).card : ENNReal) ≤
        K *
          ((wz2PaperOrdinaryFullFiberIndices
            selectedFine.family selectedCoarse.family parent).card :
            ENNReal)
    simpa only [
      wz2PaperOrdinaryFullFiberCount
    ] using hcardinality
  refine
    {
      normalization := selectedNormalization
      convex_wolff := ?_
    }
  intro convexSet hconvex
  calc
    selectedFamily.containedCount convexSet ≤
        ambientFamily.containedCount convexSet :=
      hcount convexSet
    _ ≤ C * volume convexSet * ambientFamily.enncard :=
      data.convex_wolff convexSet hconvex
    _ ≤ C * volume convexSet *
          (K * selectedFamily.enncard) := by
      gcongr
    _ = (K * C) * volume convexSet *
          selectedFamily.enncard := by
      ring

/--
Restrict one complete pure scale witness after the geometric public cover and
the selected fiber ratios have been established.

This is the pure analogue of the historical selected-hit-parent restriction.
All actual outer-John fiber CWA fields are transported by `restrict`; no WZ
target family is used as a substitute.
-/
noncomputable def WZ2PaperPureScaleCoverData.restrict
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C K selectedConstant : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine rho C)
    (selectedFine : WZ2PaperPureTubeSubfamily fine)
    (selectedCoarse : WZ2PaperPureTubeSubfamily data.coarse)
    (restrictedCover :
      WZ2PaperPurePartitioningCover
        selectedFine.family selectedCoarse.family)
    (selectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        selectedFine.family selectedCoarse.family
        selectedConstant)
    (fiberRatio :
      ∀ parent : Fin selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
            fine data.coarse (selectedCoarse.embedding parent) ≤
          K *
            wz2PaperOrdinaryFullFiberCount
              selectedFine.family selectedCoarse.family parent) :
    WZ2PaperPureScaleCoverData
      selectedFine.family rho
      (max selectedConstant (K * C)) where
  delta_pos := data.delta_pos
  rho_pos := data.rho_pos
  coarse := selectedCoarse.family
  cover := restrictedCover
  full_fiber_uniform first second :=
    (selectedUniform first second).trans (by
      gcongr
      exact le_max_left _ _)
  rescaledFiber parent := by
    rcases data.rescaledFiber (selectedCoarse.embedding parent) with
      ⟨ambientFiber⟩
    let restricted :=
      ambientFiber.restrict
        selectedFine.toTubeSubfamily
        selectedCoarse.toTubeSubfamily
        parent rfl data.rho_pos
        (fiberRatio parent)
    exact
      ⟨{
        normalization := restricted.normalization
        convex_wolff := fun convexSet hconvex =>
          (restricted.convex_wolff convexSet hconvex).trans (by
            gcongr
            · exact le_max_right selectedConstant (K * C)
            · exact le_rfl)
      }⟩

/--
The ambient strict fibers over an arbitrary selected coarse subfamily have
total cardinality at most the ambient fine cardinality.
-/
theorem WZ2PaperPureScaleCoverData.sum_selectedCoarse_fullFiberCount_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine rho C)
    (selectedCoarse : WZ2PaperPureTubeSubfamily data.coarse) :
    (∑ parent : Fin selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
          fine data.coarse (selectedCoarse.embedding parent)) ≤
      fine.enncard := by
  let indices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      data.cover.parent source ∈
        Finset.image selectedCoarse.embedding Finset.univ
  have hsum :
      (∑ parent : Fin selectedCoarse.family.card,
          (Finset.univ.filter fun source : Fin fine.card =>
            data.cover.parent source =
              selectedCoarse.embedding parent).card) =
        indices.card := by
    let selectedParents : Finset (Fin data.coarse.card) :=
      Finset.image selectedCoarse.embedding Finset.univ
    have hraw :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        selectedParents data.cover.parent
    have hselectedParentSum :
        (∑ ambientParent ∈ selectedParents,
            (Finset.univ.filter fun source : Fin fine.card =>
              data.cover.parent source = ambientParent).card) =
          ∑ parent : Fin selectedCoarse.family.card,
            (Finset.univ.filter fun source : Fin fine.card =>
              data.cover.parent source =
                selectedCoarse.embedding parent).card := by
      rw [Finset.sum_image (fun _ _ _ _ heq =>
        selectedCoarse.embedding.injective heq)]
    rw [hselectedParentSum] at hraw
    exact hraw
  have hsumENN :
      (∑ parent : Fin selectedCoarse.family.card,
          (((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            data.cover.parent source =
              selectedCoarse.embedding parent).card : ENNReal)) =
        (indices.card : ENNReal) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hsum
  calc
    (∑ parent : Fin selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
          fine data.coarse (selectedCoarse.embedding parent)) =
        ∑ parent : Fin selectedCoarse.family.card,
          (((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            data.cover.parent source =
              selectedCoarse.embedding parent).card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [wz2PaperOrdinaryFullFiberCount]
      have hindices :
          wz2PaperOrdinaryFullFiberIndices
              fine data.coarse (selectedCoarse.embedding parent) =
            Finset.univ.filter fun source : Fin fine.card =>
              data.cover.parent source =
                selectedCoarse.embedding parent := by
        ext source
        rw [data.cover.mem_fullFiber_iff_parent_eq data.rho_pos.le]
        simp
      rw [hindices]
    _ = (indices.card : ENNReal) := hsumENN
    _ ≤ (fine.card : ENNReal) := by
      exact_mod_cast
        (show indices.card ≤ fine.card by
          simpa using Finset.card_le_univ indices)
    _ = fine.enncard := rfl

/-- The strict fibers of a pure partitioning cover partition its fine index
set, including any empty coarse fibers. -/
theorem WZ2PaperPurePartitioningCover.sum_fullFiberCount
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho) :
    (∑ parent : Fin coarse.card,
        wz2PaperOrdinaryFullFiberCount
          fine coarse parent) =
      fine.enncard := by
  calc
    (∑ parent : Fin coarse.card,
        wz2PaperOrdinaryFullFiberCount
          fine coarse parent) =
        ∑ parent : Fin coarse.card,
          (((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            cover.parent source = parent).card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [wz2PaperOrdinaryFullFiberCount]
      have hindices :
          wz2PaperOrdinaryFullFiberIndices fine coarse parent =
            Finset.univ.filter fun source : Fin fine.card =>
              cover.parent source = parent := by
        ext source
        rw [cover.mem_fullFiber_iff_parent_eq hrho]
        simp
      rw [hindices]
    _ = (fine.card : ENNReal) := by
      rw [← Nat.cast_sum]
      exact_mod_cast
        ((Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin fine.card))
          (Finset.univ : Finset (Fin coarse.card))
          cover.parent).trans (by simp))
    _ = fine.enncard := rfl

/--
Ratio-based pure restriction with the same loss as the historical selected
hit-parent theorem.

The selected coarse family may be any nonempty subfamily.  Cover provenance
and centered doubled-fiber disjointness are supplied by `restrictedCover`.
-/
noncomputable def WZ2PaperPureScaleCoverData.restrictOfWeightedRetention
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant weight selectedConstant retentionConstant : ENNReal}
    (data :
      WZ2PaperPureScaleCoverData fine rho ambientConstant)
    (selectedFine : WZ2PaperPureTubeSubfamily fine)
    (selectedCoarse : WZ2PaperPureTubeSubfamily data.coarse)
    (selectedCoarseNonempty : selectedCoarse.family.Nonempty)
    (restrictedCover :
      WZ2PaperPurePartitioningCover
        selectedFine.family selectedCoarse.family)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * fine.enncard ≤
        retentionConstant * selectedFine.family.enncard)
    (selectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        selectedFine.family selectedCoarse.family selectedConstant) :
    let fiberRatioConstant :=
      ambientConstant * retentionConstant * selectedConstant
    let selectedToAmbientRatio :=
      weight⁻¹ * fiberRatioConstant
    WZ2PaperPureScaleCoverData
      selectedFine.family rho
      (max selectedConstant
        (selectedToAmbientRatio * ambientConstant)) := by
  let ambientFiberCount :
      Fin selectedCoarse.family.card → ENNReal :=
    fun parent =>
      wz2PaperOrdinaryFullFiberCount
        fine data.coarse (selectedCoarse.embedding parent)
  let selectedFiberCount :
      Fin selectedCoarse.family.card → ENNReal :=
    fun parent =>
      wz2PaperOrdinaryFullFiberCount
        selectedFine.family selectedCoarse.family parent
  let fiberRatioConstant :=
    ambientConstant * retentionConstant * selectedConstant
  let selectedToAmbientRatio :=
    weight⁻¹ * fiberRatioConstant
  let outputConstant :=
    max selectedConstant
      (selectedToAmbientRatio * ambientConstant)
  letI : Nonempty (Fin selectedCoarse.family.card) :=
    ⟨⟨0, selectedCoarseNonempty⟩⟩
  have hambientUniform :
      ∀ first second,
        ambientFiberCount first ≤
          ambientConstant * ambientFiberCount second := by
    intro first second
    exact data.full_fiber_uniform
      (selectedCoarse.embedding first)
      (selectedCoarse.embedding second)
  have hselectedUniform :
      ∀ first second,
        selectedFiberCount first ≤
          selectedConstant * selectedFiberCount second :=
    selectedUniform
  have hretainedSums :
      weight * (∑ parent, ambientFiberCount parent) ≤
        retentionConstant * ∑ parent, selectedFiberCount parent := by
    calc
      weight * (∑ parent, ambientFiberCount parent) ≤
          weight * fine.enncard := by
        gcongr
        exact data.sum_selectedCoarse_fullFiberCount_le selectedCoarse
      _ ≤ retentionConstant * selectedFine.family.enncard :=
        hglobalRetention
      _ =
          retentionConstant * ∑ parent, selectedFiberCount parent := by
        rw [restrictedCover.sum_fullFiberCount data.rho_pos.le]
  have hweightedRatio :
      ∀ parent,
        weight * ambientFiberCount parent ≤
          fiberRatioConstant * selectedFiberCount parent := by
    intro parent
    simpa [fiberRatioConstant] using
      finite_uniform_weighted_fiber_ratio
        ambientFiberCount selectedFiberCount
        weight ambientConstant selectedConstant retentionConstant
        hambientUniform hselectedUniform hretainedSums parent
  have hratio :
      ∀ parent,
        ambientFiberCount parent ≤
          selectedToAmbientRatio * selectedFiberCount parent := by
    intro parent
    calc
      ambientFiberCount parent =
          weight⁻¹ * (weight * ambientFiberCount parent) := by
        rw [← mul_assoc,
          ENNReal.inv_mul_cancel hweightZero hweightTop,
          one_mul]
      _ ≤ weight⁻¹ *
          (fiberRatioConstant * selectedFiberCount parent) := by
        exact mul_le_mul_left' (hweightedRatio parent) weight⁻¹
      _ =
          selectedToAmbientRatio * selectedFiberCount parent := by
        simp [selectedToAmbientRatio]
        ring
  exact
    data.restrict selectedFine selectedCoarse restrictedCover
      selectedUniform hratio

end Kakeya.Assouad

end

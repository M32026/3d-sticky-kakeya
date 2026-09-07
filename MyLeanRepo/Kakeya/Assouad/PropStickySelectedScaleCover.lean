import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyWeakening

/-!
# Restrict one exact paper scale witness to a selected family

The selected fine family keeps exactly the coarse parents it hits.  For each
such parent, its full geometric fiber embeds canonically into the
corresponding ambient full fiber.  This is the source-side indexing needed
to restrict the ambient unit-rescaled fiber without changing tube axes.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

noncomputable def WZ2PaperUnitRescaledFamilyData.monoENNReal
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C₁ C₂ : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperUnitRescaledFamilyData
      cover parent hrho C₂ where
  targetFamily := data.targetFamily
  sourceIndex := data.sourceIndex
  sourceIndex_mem := data.sourceIndex_mem
  sourceIndex_injective := data.sourceIndex_injective
  sourceIndex_surjective := data.sourceIndex_surjective
  target_axis := data.target_axis
  target_line_class := data.target_line_class
  convex_wolff convexSet hconvex :=
    (data.convex_wolff convexSet hconvex).trans (by
      gcongr)

/--
One selected full fiber, viewed as a genuine subfamily of the corresponding
ambient full fiber.
-/
def WZ2PaperPartitioningCover.selectedFullFiberInAmbient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent :
      Fin (cover.hitParentSubfamily selected).family.card) :
    Kakeya.Streamlined.TubeSubfamily
      (cover.fullFiberSubfamily
        ((cover.hitParentSubfamily selected).embedding parent)).family := by
  let restricted := cover.restrictToHitParents selected
  let selectedFiber := restricted.fullFiberSubfamily parent
  let ambientParent :=
    (cover.hitParentSubfamily selected).embedding parent
  let ambientIndices :=
    wz2PaperFullFiberIndices fine coarse ambientParent
  let ambientEnumeration : Fin ambientIndices.card ≃ ambientIndices :=
    (ambientIndices.orderIsoOfFin rfl).toEquiv
  let ambientIndex :
      Fin selectedFiber.family.card →
        Fin (cover.fullFiberSubfamily ambientParent).family.card :=
    fun index =>
      ambientEnumeration.symm
        ⟨selected.embedding (selectedFiber.embedding index), by
          apply
            (cover.mem_fullFiber_iff_parent
              ambientParent
              (selected.embedding
                (selectedFiber.embedding index))).mpr
          have hrestricted :
              restricted.parent
                  (selectedFiber.embedding index) =
                parent :=
            (restricted.mem_fullFiber_iff_parent
              parent (selectedFiber.embedding index)).mp
              (restricted.fullFiberSubfamily_mem parent index)
          have hambient :=
            congrArg
              (cover.hitParentSubfamily selected).embedding
              hrestricted
          simpa [restricted,
            WZ2PaperPartitioningCover.restrictToHitParents] using
            hambient⟩
  refine
    { family := selectedFiber.family
      embedding :=
        { toFun := ambientIndex
          inj' := ?_ }
      tube_eq := ?_ }
  · intro first second heq
    apply selectedFiber.embedding.injective
    apply selected.embedding.injective
    have hambientValues :
        selected.embedding (selectedFiber.embedding first) =
          selected.embedding (selectedFiber.embedding second) := by
      have hsubtype :=
        congrArg ambientEnumeration heq
      have hfirst :
          ambientEnumeration (ambientIndex first) =
            ⟨selected.embedding (selectedFiber.embedding first),
              by
                apply
                  (cover.mem_fullFiber_iff_parent
                    ambientParent
                    (selected.embedding
                      (selectedFiber.embedding first))).mpr
                have hrestricted :
                    restricted.parent
                        (selectedFiber.embedding first) =
                      parent :=
                  (restricted.mem_fullFiber_iff_parent
                    parent (selectedFiber.embedding first)).mp
                    (restricted.fullFiberSubfamily_mem parent first)
                have hambient :=
                  congrArg
                    (cover.hitParentSubfamily selected).embedding
                    hrestricted
                simpa [restricted,
                  WZ2PaperPartitioningCover.restrictToHitParents] using
                  hambient⟩ :=
        ambientEnumeration.apply_symm_apply _
      have hsecond :
          ambientEnumeration (ambientIndex second) =
            ⟨selected.embedding (selectedFiber.embedding second),
              by
                apply
                  (cover.mem_fullFiber_iff_parent
                    ambientParent
                    (selected.embedding
                      (selectedFiber.embedding second))).mpr
                have hrestricted :
                    restricted.parent
                        (selectedFiber.embedding second) =
                      parent :=
                  (restricted.mem_fullFiber_iff_parent
                    parent (selectedFiber.embedding second)).mp
                    (restricted.fullFiberSubfamily_mem parent second)
                have hambient :=
                  congrArg
                    (cover.hitParentSubfamily selected).embedding
                    hrestricted
                simpa [restricted,
                  WZ2PaperPartitioningCover.restrictToHitParents] using
                  hambient⟩ :=
        ambientEnumeration.apply_symm_apply _
      rw [hfirst, hsecond] at hsubtype
      exact congrArg Subtype.val hsubtype
    exact hambientValues
  · intro index
    have hambientIndex :
        (cover.fullFiberSubfamily ambientParent).embedding
            (ambientIndex index) =
          selected.embedding (selectedFiber.embedding index) := by
      change
        (ambientIndices.orderEmbOfFin rfl)
            (ambientEnumeration.symm
              ⟨selected.embedding (selectedFiber.embedding index), _⟩) =
          selected.embedding (selectedFiber.embedding index)
      exact congrArg Subtype.val
        (ambientEnumeration.apply_symm_apply
          ⟨selected.embedding (selectedFiber.embedding index), by
            apply
              (cover.mem_fullFiber_iff_parent
                ambientParent
                (selected.embedding
                  (selectedFiber.embedding index))).mpr
            have hrestricted :
                restricted.parent
                    (selectedFiber.embedding index) =
                  parent :=
              (restricted.mem_fullFiber_iff_parent
                parent (selectedFiber.embedding index)).mp
                (restricted.fullFiberSubfamily_mem parent index)
            have hambient :=
              congrArg
                (cover.hitParentSubfamily selected).embedding
                hrestricted
            simpa [restricted,
              WZ2PaperPartitioningCover.restrictToHitParents] using
              hambient⟩)
    rw [selectedFiber.tube_eq index,
      selected.tube_eq (selectedFiber.embedding index),
      (cover.fullFiberSubfamily ambientParent).tube_eq]
    change
      fine.tube
          (selected.embedding (selectedFiber.embedding index)) =
        fine.tube
          ((cover.fullFiberSubfamily ambientParent).embedding
            (ambientIndex index))
    rw [hambientIndex]

@[simp] theorem
    WZ2PaperPartitioningCover.selectedFullFiberInAmbient_family
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent :
      Fin (cover.hitParentSubfamily selected).family.card) :
    (cover.selectedFullFiberInAmbient selected parent).family =
      ((cover.restrictToHitParents selected).fullFiberSubfamily
        parent).family :=
  rfl

@[simp] theorem
    WZ2PaperPartitioningCover.selectedFullFiberInAmbient_ambient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent :
      Fin (cover.hitParentSubfamily selected).family.card)
    (index :
      Fin ((cover.restrictToHitParents selected).fullFiberSubfamily
        parent).family.card) :
    (cover.fullFiberSubfamily
        ((cover.hitParentSubfamily selected).embedding parent)).embedding
        ((cover.selectedFullFiberInAmbient
          selected parent).embedding index) =
      selected.embedding
        (((cover.restrictToHitParents selected).fullFiberSubfamily
          parent).embedding index) := by
  let ambientParent :=
    (cover.hitParentSubfamily selected).embedding parent
  let ambientIndices :=
    wz2PaperFullFiberIndices fine coarse ambientParent
  let ambientEnumeration : Fin ambientIndices.card ≃ ambientIndices :=
    (ambientIndices.orderIsoOfFin rfl).toEquiv
  change
    (ambientIndices.orderEmbOfFin rfl)
        (ambientEnumeration.symm
          ⟨selected.embedding
              (((cover.restrictToHitParents selected).fullFiberSubfamily
                parent).embedding index), _⟩) =
      selected.embedding
        (((cover.restrictToHitParents selected).fullFiberSubfamily
          parent).embedding index)
  exact congrArg Subtype.val
    (ambientEnumeration.apply_symm_apply _)

/--
Restrict one ambient exact unit-rescaled fiber to the selected source fiber.

The weighted cardinality hypothesis records the density/polylogarithmic loss
that will be inverted in the normalized Convex-Wolff constant.
-/
def WZ2PaperUnitRescaledFamilyData.restrictToSelectedHitFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {ambientParent : Fin coarse.card}
    {hrho : 0 < rho}
    {C weight K : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover ambientParent hrho C)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent :
      Fin (cover.hitParentSubfamily selected).family.card)
    (hparent :
      (cover.hitParentSubfamily selected).embedding parent =
        ambientParent)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight *
          (cover.fullFiberSubfamily ambientParent).family.enncard ≤
        K *
          ((cover.restrictToHitParents selected).fullFiberSubfamily
            parent).family.enncard) :
    WZ2PaperUnitRescaledFamilyData
      (cover.restrictToHitParents selected)
      parent hrho ((weight⁻¹ * K) * C) := by
  subst ambientParent
  let ambientParent :=
    (cover.hitParentSubfamily selected).embedding parent
  let sourceSelected :=
    cover.selectedFullFiberInAmbient selected parent
  let targetSelected :=
    data.targetSubfamilyForSource sourceSelected
  have hsourceCardinality :
      weight *
          (cover.fullFiberSubfamily ambientParent).family.enncard ≤
        K * sourceSelected.family.enncard := by
    change
      weight *
          (cover.fullFiberSubfamily ambientParent).family.enncard ≤
        K *
          ((cover.restrictToHitParents selected).fullFiberSubfamily
            parent).family.enncard
    simpa [ambientParent] using hcardinality
  have htargetCWA :
      WZ2PaperConvexWolffBound targetSelected.family
        ((weight⁻¹ * K) * C) :=
    data.targetSubfamily_convex_wolff_of_weighted_source_ratio
      sourceSelected hweightZero hweightTop hsourceCardinality
  refine
    { targetFamily := targetSelected.family
      sourceIndex := fun index =>
        ((cover.restrictToHitParents selected).fullFiberSubfamily
          parent).embedding index
      sourceIndex_mem := ?_
      sourceIndex_injective :=
        ((cover.restrictToHitParents selected).fullFiberSubfamily
          parent).embedding.injective
      sourceIndex_surjective := ?_
      target_axis := ?_
      target_line_class :=
        data.target_line_class.subfamily targetSelected
      convex_wolff := htargetCWA }
  · intro index
    exact
      (cover.restrictToHitParents selected).fullFiberSubfamily_mem
        parent index
  · intro source hsource
    let indices :=
      wz2PaperFullFiberIndices
        selected.family
        (cover.hitParentSubfamily selected).family
        parent
    let enumeration : Fin indices.card ≃ indices :=
      (indices.orderIsoOfFin rfl).toEquiv
    let index : Fin indices.card :=
      enumeration.symm ⟨source, hsource⟩
    refine ⟨index, ?_⟩
    exact congrArg Subtype.val
      (enumeration.apply_symm_apply ⟨source, hsource⟩)
  · intro index
    let sourceIndex : Fin sourceSelected.family.card :=
      ⟨index.1, by
        simpa [targetSelected,
          WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource] using
          index.2⟩
    let restrictedIndex :
        Fin ((cover.restrictToHitParents selected).fullFiberSubfamily
          parent).family.card :=
      ⟨sourceIndex.1, by
        simpa [sourceSelected] using sourceIndex.2⟩
    change
      tubeAxisLine
          ((data.targetSubfamilyForSource sourceSelected).family.tube
            index) =
        wz1PaperUnitRescalingMap
            ((cover.hitParentSubfamily selected).family.tube parent)
            hrho ''
          tubeAxisLine
            (selected.family.tube
              (((cover.restrictToHitParents selected).fullFiberSubfamily
                parent).embedding restrictedIndex))
    have haxis :=
      data.targetSubfamilyForSource_axis sourceSelected sourceIndex
    calc
      tubeAxisLine
          ((data.targetSubfamilyForSource sourceSelected).family.tube
            index) =
          wz1PaperUnitRescalingMap
              (coarse.tube ambientParent) hrho ''
            tubeAxisLine
              ((cover.fullFiberSubfamily ambientParent).family.tube
                (sourceSelected.embedding sourceIndex)) := by
        simpa [sourceIndex, targetSelected,
          WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource] using
          haxis
      _ =
          wz1PaperUnitRescalingMap
              ((cover.hitParentSubfamily selected).family.tube parent)
              hrho ''
            tubeAxisLine
              (selected.family.tube
                (((cover.restrictToHitParents selected).fullFiberSubfamily
                  parent).embedding restrictedIndex)) := by
        rw [(cover.hitParentSubfamily selected).tube_eq]
        congr 1
        calc
          tubeAxisLine
              ((cover.fullFiberSubfamily ambientParent).family.tube
                (sourceSelected.embedding sourceIndex)) =
              tubeAxisLine
                (sourceSelected.family.tube sourceIndex) := by
            rw [sourceSelected.tube_eq sourceIndex]
          _ =
              tubeAxisLine
                (((cover.restrictToHitParents selected).fullFiberSubfamily
                  parent).family.tube restrictedIndex) := by
            rfl
          _ =
              tubeAxisLine
                (selected.family.tube
                  (((cover.restrictToHitParents selected).fullFiberSubfamily
                    parent).embedding restrictedIndex)) := by
            rw [
              ((cover.restrictToHitParents selected).fullFiberSubfamily
                parent).tube_eq
            ]

theorem WZ2PaperPartitioningCover.sum_fullFiberCount_subfamily_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse) :
    (∑ parent : Fin selectedCoarse.family.card,
        wz2PaperFullFiberCount
          fine coarse (selectedCoarse.embedding parent)) ≤
      fine.enncard := by
  let indices : Finset (Fin coarse.card) :=
    Finset.univ.map selectedCoarse.embedding
  have hsum :
      (∑ parent : Fin selectedCoarse.family.card,
          wz2PaperFullFiberCount
            fine coarse (selectedCoarse.embedding parent)) =
        ∑ parent ∈ indices,
          ((cover.fiberIndices parent).card : ENNReal) := by
    simp_rw [wz2PaperFullFiberCount, cover.fullFiberIndices_eq]
    rw [Finset.sum_map]
  rw [hsum]
  have hcount :
      ∑ parent ∈ indices,
          (cover.fiberIndices parent).card ≤
        fine.card := by
    change
      ∑ parent ∈ indices,
          (Finset.univ.filter fun source =>
            cover.parent source = parent).card ≤
        fine.card
    have heq :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        indices cover.parent
    rw [heq]
    simpa only [Fintype.card_fin] using
      Finset.card_le_univ
        (Finset.univ.filter fun source : Fin fine.card =>
          cover.parent source ∈ indices)
  have hcountENN :
      (∑ parent ∈ indices,
          ((cover.fiberIndices parent).card : ENNReal)) ≤
        (fine.card : ENNReal) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hcount
  exact hcountENN

/--
Restrict one exact-scale ambient witness to a selected fine family.

The ambient fibers are `ambientConstant`-uniform, the selected hit fibers
are `selectedConstant`-uniform, and the global weighted cardinality
retention has factor `retentionConstant`.  Hence every selected rescaled
fiber inherits normalized CWA with the explicit combined loss.
-/
def WZ2PaperScaleCoverData.restrictToSelectedHitParents
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {ambientConstant weight selectedConstant retentionConstant : ENNReal}
    (data :
      WZ2PaperScaleCoverData family rho ambientConstant)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * family.enncard ≤
        retentionConstant * selected.family.enncard)
    (hselectedUniform :
      ∀ first second :
          Fin (data.cover.hitParentSubfamily selected).family.card,
        wz2PaperFullFiberCount
            selected.family
            (data.cover.hitParentSubfamily selected).family
            first ≤
          selectedConstant *
            wz2PaperFullFiberCount
              selected.family
              (data.cover.hitParentSubfamily selected).family
              second) :
    let fiberRatioConstant :=
      ambientConstant * retentionConstant * selectedConstant
    let rescaledConstant :=
      (weight⁻¹ * fiberRatioConstant) * ambientConstant
    WZ2PaperScaleCoverData selected.family rho
      (max selectedConstant rescaledConstant) := by
  let hitCoarse := data.cover.hitParentSubfamily selected
  let restrictedCover := data.cover.restrictToHitParents selected
  let fiberRatioConstant :=
    ambientConstant * retentionConstant * selectedConstant
  let rescaledConstant :=
    (weight⁻¹ * fiberRatioConstant) * ambientConstant
  let outputConstant := max selectedConstant rescaledConstant
  have hcoarseLine :
      WZ1PaperIsLineClass hitCoarse.family :=
    data.coarse_line_class.subfamily hitCoarse
  have hcoarseDistinct :
      WZ1PaperIsEssentiallyDistinct hitCoarse.family :=
    data.coarse_essentially_distinct.subfamily hitCoarse
  have hambientSumLe :
      (∑ parent : Fin hitCoarse.family.card,
          wz2PaperFullFiberCount
            family data.coarse (hitCoarse.embedding parent)) ≤
        family.enncard :=
    data.cover.sum_fullFiberCount_subfamily_le hitCoarse
  have hselectedSum :
      ∑ parent : Fin hitCoarse.family.card,
          wz2PaperFullFiberCount
            selected.family hitCoarse.family parent =
        selected.family.enncard := by
    change
      (∑ parent : Fin hitCoarse.family.card,
          ((wz2PaperFullFiberIndices
            selected.family hitCoarse.family parent).card : ENNReal)) =
        (selected.family.card : ENNReal)
    rw [show
      (∑ parent : Fin hitCoarse.family.card,
          ((wz2PaperFullFiberIndices
            selected.family hitCoarse.family parent).card : ENNReal)) =
        ∑ parent : Fin hitCoarse.family.card,
          ((restrictedCover.fiberIndices parent).card : ENNReal) by
      apply Finset.sum_congr rfl
      intro parent _
      rw [restrictedCover.fullFiberIndices_eq parent]]
    change
      (∑ parent : Fin hitCoarse.family.card,
          ((restrictedCover.fiberIndices parent).card : ENNReal)) =
        (selected.family.card : ENNReal)
    rw [← Nat.cast_sum]
    exact_mod_cast
      ((Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin selected.family.card))
        (Finset.univ : Finset (Fin hitCoarse.family.card))
        restrictedCover.parent).trans (by simp))
  refine
    { rho_pos := data.rho_pos
      coarse := hitCoarse.family
      cover := restrictedCover
      coarse_line_class := hcoarseLine
      coarse_essentially_distinct := hcoarseDistinct
      full_fiber_uniform := ?_
      rescaledFiber := ?_ }
  · intro first second
    exact (hselectedUniform first second).trans (by
      gcongr
      exact le_max_left _ _)
  · intro parent
    let ambientParent := hitCoarse.embedding parent
    rcases data.rescaledFiber ambientParent with ⟨ambientFiber⟩
    have hweightedFiber :
        weight *
            wz2PaperFullFiberCount
              family data.coarse ambientParent ≤
          fiberRatioConstant *
            wz2PaperFullFiberCount
              selected.family hitCoarse.family parent := by
      let ambientFiberCount : Fin hitCoarse.family.card → ENNReal :=
        fun index =>
          wz2PaperFullFiberCount
            family data.coarse (hitCoarse.embedding index)
      let selectedFiberCount : Fin hitCoarse.family.card → ENNReal :=
        fun index =>
          wz2PaperFullFiberCount
            selected.family hitCoarse.family index
      have hambientUniformHit :
          ∀ first second,
            ambientFiberCount first ≤
              ambientConstant * ambientFiberCount second := by
        intro first second
        exact data.full_fiber_uniform
          (hitCoarse.embedding first) (hitCoarse.embedding second)
      have hretainedSums :
          weight * (∑ index, ambientFiberCount index) ≤
            retentionConstant * ∑ index, selectedFiberCount index := by
        calc
          weight * (∑ index, ambientFiberCount index) ≤
              weight * family.enncard := by
            gcongr
          _ ≤ retentionConstant * selected.family.enncard :=
            hglobalRetention
          _ = retentionConstant *
              ∑ index, selectedFiberCount index := by
            rw [hselectedSum]
      letI : Nonempty (Fin hitCoarse.family.card) := ⟨parent⟩
      have hratio :=
        finite_uniform_weighted_fiber_ratio
          ambientFiberCount selectedFiberCount
          weight ambientConstant selectedConstant retentionConstant
          hambientUniformHit hselectedUniform hretainedSums
          parent
      simpa [fiberRatioConstant, ambientFiberCount,
        selectedFiberCount, ambientParent] using hratio
    have hfiberCardinality :
        weight *
            (data.cover.fullFiberSubfamily ambientParent).family.enncard ≤
          fiberRatioConstant *
            (restrictedCover.fullFiberSubfamily parent).family.enncard := by
      change
        weight *
            ((wz2PaperFullFiberIndices
              family data.coarse ambientParent).card : ENNReal) ≤
          fiberRatioConstant *
            ((wz2PaperFullFiberIndices
              selected.family hitCoarse.family parent).card : ENNReal)
      simpa [wz2PaperFullFiberCount] using hweightedFiber
    let restrictedFiber :
        WZ2PaperUnitRescaledFamilyData
          restrictedCover parent data.rho_pos rescaledConstant :=
      ambientFiber.restrictToSelectedHitFiber
        selected parent rfl hweightZero hweightTop
        hfiberCardinality
    exact
      ⟨restrictedFiber.monoENNReal
        (le_max_right selectedConstant rescaledConstant)⟩

end Kakeya.Assouad

end

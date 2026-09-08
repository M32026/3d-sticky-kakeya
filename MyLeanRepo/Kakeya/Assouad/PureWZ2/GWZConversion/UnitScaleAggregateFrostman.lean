import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AxialReanchoringEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ReanchoredParentVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.UnitScaleCompleteFiberOverlap
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Aggregate Frostman transfer at the top scale

At exact GWZ scale one, assign each selected reanchored tube to any complete
GWZ parent containing its source tube.  For a convex test set, one common
axial-reanchoring envelope works for every owner class.  Summing the input
complete-fiber Frostman inequalities and using the unit-scale overlap bound
produces a Frostman estimate for the entire final family, without any extra
top-scale selection.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Common geometric loss in the top-scale aggregate Frostman estimate. -/
def pureWZ2UnitScaleAggregateFrostmanConstant
    (inputConstant overlapConstant globalRetention : ENNReal) : ENNReal :=
  212776173 * 1280 * inputConstant * overlapConstant * globalRetention

private theorem pureWZ2_tubeFamily_containedMass_eq_card_mul
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (convexSet : Set Point3) :
    family.toBodyFamily.containedMass convexSet =
      ((Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet).card : ENNReal) *
        Kakeya.deltaTubeVolume delta := by
  change
    (∑ index ∈
      (Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet),
      (family.toBodyFamily.body index).volume) = _
  have hvolume :
      ∀ index : Fin family.card,
        (family.toBodyFamily.body index).volume =
          Kakeya.deltaTubeVolume delta := by
    intro index
    let canonical : Kakeya.DeltaTube delta :=
      {
        base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    exact
      Kakeya.Streamlined.tube_volume_eq
        (family.tube index) canonical
  simp only [hvolume]
  rw [Finset.sum_const]
  simp

/--
Aggregate all exact scale-one complete-fiber Frostman inequalities into one
Frostman inequality for the entire reanchored family.
-/
theorem pureWZ2_unit_scale_aggregate_frostman
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source reanchored : Kakeya.Streamlined.TubeFamily delta}
    (sourceIndex : Fin reanchored.card ↪ Fin source.card)
    (axialShift : Fin reanchored.card → ℝ)
    (direction_eq :
      ∀ index,
        (reanchored.tube index).direction =
          (source.tube (sourceIndex index)).direction)
    (source_base_eq :
      ∀ index,
        (source.tube (sourceIndex index)).base =
          (reanchored.tube index).base +
            axialShift index •
              (reanchored.tube index).direction)
    (axialShift_bound :
      ∀ index, |axialShift index| ≤ 1)
    {inputConstant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData
        (A := A) source scale inputConstant)
    (hscale : scale.1 = 1)
    (globalRetention : ENNReal)
    (global_cardinality_ratio :
      source.enncard ≤ globalRetention * reanchored.enncard)
    (topParent : Kakeya.DeltaTube (8 * A))
    (top_parent_volume_ratio :
      ∀ parent : Fin scaleData.coarse.card,
        volume topParent.carrier ≤
          (1280 : ENNReal) *
            volume
              (wz2PaperCenteredDilatedCarrier A
                (scaleData.coarse.tube parent))) :
    ∀ convexSet : Set Point3,
      Convex ℝ convexSet →
      convexSet ⊆ topParent.carrier →
        reanchored.toBodyFamily.containedMass convexSet *
            volume topParent.carrier ≤
          pureWZ2UnitScaleAggregateFrostmanConstant
              inputConstant
              (pureWZ2UnitScaleCompleteFiberOverlapBound A)
              globalRetention *
            reanchored.toBodyFamily.mass *
            volume convexSet := by
  let owner : Fin reanchored.card →
      Fin scaleData.coarse.card := fun index =>
    Classical.choose
      (scaleData.full_fibers_cover (sourceIndex index))
  have howner :
      ∀ index,
        sourceIndex index ∈
          scaleData.fullFiberIndices (owner index) := by
    intro index
    exact
      Classical.choose_spec
        (scaleData.full_fibers_cover (sourceIndex index))
  have hoverlap :=
    pureWZ2_unit_scale_complete_fiber_overlap
      hdelta hA scaleData hscale
  intro convexSet hconvex _hconvexTop
  let selectedContained : Finset (Fin reanchored.card) :=
    Finset.univ.filter fun index =>
      (reanchored.tube index).carrier ⊆ convexSet
  by_cases hselectedEmpty : selectedContained = ∅
  · have hcontainedMass :
        reanchored.toBodyFamily.containedMass convexSet = 0 := by
      rw [pureWZ2_tubeFamily_containedMass_eq_card_mul]
      change (selectedContained.card : ENNReal) *
          Kakeya.deltaTubeVolume delta = 0
      rw [hselectedEmpty]
      simp
    rw [hcontainedMass, zero_mul]
    positivity
  · have hselectedNonempty :
        selectedContained.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hselectedEmpty
    rcases
        pureWZ2_bounded_axial_reanchoring_common_envelope
          hdelta sourceIndex axialShift direction_eq
          source_base_eq axialShift_bound
          selectedContained hselectedNonempty
          convexSet hconvex
          (by
            intro index hindex
            exact (Finset.mem_filter.mp hindex).2) with
      ⟨envelope, henvelopeConvex, henvelopeVolume,
        hsourceEnvelope⟩
    let ownerClass :
        Fin scaleData.coarse.card →
          Finset (Fin reanchored.card) := fun parent =>
      selectedContained.filter fun index => owner index = parent
    let completeSub :
        Fin scaleData.coarse.card →
          Kakeya.Streamlined.TubeSubfamily source := fun parent =>
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        source (scaleData.fullFiberIndices parent)
    let clippedEnvelope :
        Fin scaleData.coarse.card → Set Point3 := fun parent =>
      envelope ∩
        wz2PaperCenteredDilatedCarrier A
          (scaleData.coarse.tube parent)
    have hclippedConvex :
        ∀ parent, Convex ℝ (clippedEnvelope parent) := by
      intro parent
      exact henvelopeConvex.inter
        (Convex.affine_image
          (AffineMap.homothety
            (wz2PaperTubeMidpoint
              (scaleData.coarse.tube parent)) A)
          (wz2_paper_ordinary_tube_carrier_convex
            (scaleData.coarse.tube parent)))
    have hclassCard :
        ∀ parent,
          (ownerClass parent).card ≤
            ((Finset.univ :
              Finset (Fin (completeSub parent).family.card)).filter
                fun index =>
                  ((completeSub parent).family.tube index).carrier ⊆
                    clippedEnvelope parent).card := by
      intro parent
      have hownerParent :
          ∀ index : {index // index ∈ ownerClass parent},
            sourceIndex index.1 ∈
              scaleData.fullFiberIndices parent := by
        intro index
        have hindex :
            owner index.1 = parent :=
          (Finset.mem_filter.mp index.2).2
        exact
          Eq.mp
            (congrArg
              (fun targetParent =>
                sourceIndex index.1 ∈
                  scaleData.fullFiberIndices targetParent)
              hindex)
            (howner index.1)
      let target :
          {index // index ∈ ownerClass parent} →
            Fin (completeSub parent).family.card := fun index =>
        (scaleData.fullFiberIndices parent).orderIsoOfFin rfl |>.symm
          ⟨sourceIndex index.1, hownerParent index⟩
      have htargetInjective : Function.Injective target := by
        intro first second heq
        have hambient :=
          congrArg
            (fun index : Fin (completeSub parent).family.card =>
              (completeSub parent).embedding index)
            heq
        have hfirst :
            (completeSub parent).embedding (target first) =
              sourceIndex first.1 := by
          exact congrArg Subtype.val
            ((scaleData.fullFiberIndices parent).orderIsoOfFin rfl
              |>.apply_symm_apply
                ⟨sourceIndex first.1, hownerParent first⟩)
        have hsecond :
            (completeSub parent).embedding (target second) =
              sourceIndex second.1 := by
          exact congrArg Subtype.val
            ((scaleData.fullFiberIndices parent).orderIsoOfFin rfl
              |>.apply_symm_apply
                ⟨sourceIndex second.1, hownerParent second⟩)
        apply Subtype.ext
        exact sourceIndex.injective
          (hfirst.symm.trans (hambient.trans hsecond))
      let embedding :
          {index // index ∈ ownerClass parent} ↪
            Fin (completeSub parent).family.card :=
        ⟨target, htargetInjective⟩
      have himage :
          Finset.image embedding Finset.univ ⊆
            (Finset.univ :
              Finset (Fin (completeSub parent).family.card)).filter
                fun index =>
                  ((completeSub parent).family.tube index).carrier ⊆
                    clippedEnvelope parent := by
        intro targetIndex htargetIndex
        rcases Finset.mem_image.mp htargetIndex with
          ⟨index, _, rfl⟩
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · have hselected :
              index.1 ∈ selectedContained :=
            (Finset.mem_filter.mp index.2).1
          have henvelope :
              (source.tube (sourceIndex index.1)).carrier ⊆ envelope :=
            hsourceEnvelope index.1 hselected
          have hcomplete :
              (source.tube (sourceIndex index.1)).carrier ⊆
                wz2PaperCenteredDilatedCarrier A
                  (scaleData.coarse.tube parent) := by
            have hmember :
                sourceIndex index.1 ∈
                  scaleData.fullFiberIndices parent :=
              hownerParent index
            rw [scaleData.fullFiberIndices_eq] at hmember
            exact (Finset.mem_filter.mp hmember).2
          rw [(completeSub parent).tube_eq]
          change
            (source.tube
              ((completeSub parent).embedding
                (target index))).carrier ⊆
              clippedEnvelope parent
          have htarget :
              (completeSub parent).embedding (target index) =
                sourceIndex index.1 := by
            exact congrArg Subtype.val
              ((scaleData.fullFiberIndices parent).orderIsoOfFin rfl
                |>.apply_symm_apply
                  ⟨sourceIndex index.1, hownerParent index⟩)
          rw [htarget]
          exact Set.subset_inter henvelope hcomplete
      calc
        (ownerClass parent).card =
            (Finset.univ :
              Finset {index // index ∈ ownerClass parent}).card := by
          simp
        _ =
            (Finset.image embedding
              (Finset.univ :
                Finset {index // index ∈ ownerClass parent})).card := by
          rw [Finset.card_image_of_injective
            _ embedding.injective]
        _ ≤ _ := Finset.card_le_card himage
    have hselectedPartition :
        ∑ parent : Fin scaleData.coarse.card,
            (ownerClass parent).card =
          selectedContained.card := by
      have hsum :=
        Finset.sum_card_fiberwise_eq_card_filter
          selectedContained
          (Finset.univ : Finset (Fin scaleData.coarse.card))
          owner
      simpa [ownerClass] using hsum
    have hcontainedMassLe :
        reanchored.toBodyFamily.containedMass convexSet ≤
          ∑ parent : Fin scaleData.coarse.card,
            (completeSub parent).family.toBodyFamily.containedMass
              (clippedEnvelope parent) := by
      rw [pureWZ2_tubeFamily_containedMass_eq_card_mul]
      have hselectedCast :
          (selectedContained.card : ENNReal) =
            ∑ parent : Fin scaleData.coarse.card,
              ((ownerClass parent).card : ENNReal) := by
        rw [← Nat.cast_sum, hselectedPartition]
      rw [hselectedCast, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro parent _
      rw [pureWZ2_tubeFamily_containedMass_eq_card_mul]
      exact mul_le_mul_right'
        (by exact_mod_cast hclassCard parent)
        (Kakeya.deltaTubeVolume delta)
    have hparentFrostman :
        ∀ parent,
          (completeSub parent).family.toBodyFamily.containedMass
                (clippedEnvelope parent) *
              volume topParent.carrier ≤
            (212776173 * 1280 * inputConstant) *
              (completeSub parent).family.toBodyFamily.mass *
              volume convexSet := by
      intro parent
      have hfrost :=
        scaleData.full_fiber_frostman parent
          (clippedEnvelope parent)
          (hclippedConvex parent)
          Set.inter_subset_right
      calc
        (completeSub parent).family.toBodyFamily.containedMass
                (clippedEnvelope parent) *
              volume topParent.carrier
            ≤
          (completeSub parent).family.toBodyFamily.containedMass
                (clippedEnvelope parent) *
              ((1280 : ENNReal) *
                volume
                  (wz2PaperCenteredDilatedCarrier A
                    (scaleData.coarse.tube parent))) := by
          gcongr
          exact top_parent_volume_ratio parent
        _ =
          (1280 : ENNReal) *
            ((completeSub parent).family.toBodyFamily.containedMass
                (clippedEnvelope parent) *
              volume
                (wz2PaperCenteredDilatedCarrier A
                  (scaleData.coarse.tube parent))) := by
          ring
        _ ≤
          (1280 : ENNReal) *
            (inputConstant *
              (completeSub parent).family.toBodyFamily.mass *
              volume (clippedEnvelope parent)) := by
          gcongr
        _ ≤
          (1280 : ENNReal) *
            (inputConstant *
              (completeSub parent).family.toBodyFamily.mass *
              ((212776173 : ENNReal) * volume convexSet)) := by
          gcongr
          exact
            (measure_mono Set.inter_subset_left).trans
              henvelopeVolume
        _ =
          (212776173 * 1280 * inputConstant) *
            (completeSub parent).family.toBodyFamily.mass *
            volume convexSet := by
          ring
    have hcompleteMassSum :
        (∑ parent : Fin scaleData.coarse.card,
            (completeSub parent).family.toBodyFamily.mass) ≤
          (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
            source.toBodyFamily.mass := by
      have hincidence :
          (∑ parent : Fin scaleData.coarse.card,
              (scaleData.fullFiberIndices parent).card) ≤
            pureWZ2UnitScaleCompleteFiberOverlapBound A *
              source.card := by
        calc
          (∑ parent : Fin scaleData.coarse.card,
              (scaleData.fullFiberIndices parent).card) =
              ∑ index : Fin source.card,
                (Finset.univ.filter fun parent :
                  Fin scaleData.coarse.card =>
                    index ∈
                      scaleData.fullFiberIndices parent).card := by
            calc
              (∑ parent : Fin scaleData.coarse.card,
                  (scaleData.fullFiberIndices parent).card) =
                  ∑ parent : Fin scaleData.coarse.card,
                    ∑ index : Fin source.card,
                      if index ∈ scaleData.fullFiberIndices parent
                        then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro parent _
                simpa using
                  (Finset.sum_boole
                    (fun index : Fin source.card =>
                      index ∈ scaleData.fullFiberIndices parent)
                    Finset.univ).symm
              _ =
                  ∑ index : Fin source.card,
                    ∑ parent : Fin scaleData.coarse.card,
                      if index ∈ scaleData.fullFiberIndices parent
                        then 1 else 0 := by
                rw [Finset.sum_comm]
              _ =
                  ∑ index : Fin source.card,
                    (Finset.univ.filter fun parent :
                      Fin scaleData.coarse.card =>
                        index ∈
                          scaleData.fullFiberIndices parent).card := by
                apply Finset.sum_congr rfl
                intro index _
                simpa using
                  (Finset.sum_boole
                    (fun parent : Fin scaleData.coarse.card =>
                      index ∈ scaleData.fullFiberIndices parent)
                    Finset.univ)
          _ ≤
              ∑ _index : Fin source.card,
                pureWZ2UnitScaleCompleteFiberOverlapBound A := by
            exact Finset.sum_le_sum fun index _ => hoverlap index
          _ = _ := by simp [Nat.mul_comm]
      have hmass :
          ∀ parent,
            (completeSub parent).family.toBodyFamily.mass =
              ((scaleData.fullFiberIndices parent).card : ENNReal) *
                Kakeya.deltaTubeVolume delta := by
        intro parent
        rw [tubeFamily_mass_eq_nominal]
        rfl
      have hincidenceENN :
          ((∑ parent : Fin scaleData.coarse.card,
            (scaleData.fullFiberIndices parent).card : ℕ) : ENNReal) ≤
            ((pureWZ2UnitScaleCompleteFiberOverlapBound A *
              source.card : ℕ) : ENNReal) := by
        exact_mod_cast hincidence
      calc
        (∑ parent : Fin scaleData.coarse.card,
            (completeSub parent).family.toBodyFamily.mass) =
            ((∑ parent : Fin scaleData.coarse.card,
              (scaleData.fullFiberIndices parent).card : ℕ) : ENNReal) *
              Kakeya.deltaTubeVolume delta := by
          simp_rw [hmass]
          rw [← Finset.sum_mul]
          congr 1
          rw [Nat.cast_sum]
        _ ≤
            ((pureWZ2UnitScaleCompleteFiberOverlapBound A *
              source.card : ℕ) : ENNReal) *
              Kakeya.deltaTubeVolume delta :=
          mul_le_mul_right'
            hincidenceENN (Kakeya.deltaTubeVolume delta)
        _ =
            (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
              source.toBodyFamily.mass := by
          rw [Nat.cast_mul, tubeFamily_mass_eq_nominal]
          change
            (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
                source.enncard * Kakeya.deltaTubeVolume delta =
              (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
                (source.enncard * Kakeya.deltaTubeVolume delta)
          ring
    have hsourceMass :
        source.toBodyFamily.mass ≤
          globalRetention * reanchored.toBodyFamily.mass := by
      rw [tubeFamily_mass_eq_nominal,
        tubeFamily_mass_eq_nominal]
      change
        source.enncard * Kakeya.deltaTubeVolume delta ≤
          globalRetention *
            (reanchored.enncard * Kakeya.deltaTubeVolume delta)
      simpa [mul_assoc] using
        mul_le_mul_right'
          global_cardinality_ratio
          (Kakeya.deltaTubeVolume delta)
    calc
      reanchored.toBodyFamily.containedMass convexSet *
            volume topParent.carrier
          ≤
        (∑ parent : Fin scaleData.coarse.card,
          (completeSub parent).family.toBodyFamily.containedMass
            (clippedEnvelope parent)) *
          volume topParent.carrier := by
        gcongr
      _ =
        ∑ parent : Fin scaleData.coarse.card,
          ((completeSub parent).family.toBodyFamily.containedMass
              (clippedEnvelope parent) *
            volume topParent.carrier) := by
        rw [Finset.sum_mul]
      _ ≤
        ∑ parent : Fin scaleData.coarse.card,
          ((212776173 * 1280 * inputConstant) *
            (completeSub parent).family.toBodyFamily.mass *
            volume convexSet) := by
        exact Finset.sum_le_sum fun parent _ =>
          hparentFrostman parent
      _ =
        (212776173 * 1280 * inputConstant) *
          (∑ parent : Fin scaleData.coarse.card,
            (completeSub parent).family.toBodyFamily.mass) *
          volume convexSet := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤
        (212776173 * 1280 * inputConstant) *
          ((pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
            source.toBodyFamily.mass) *
          volume convexSet := by
        gcongr
      _ ≤
        (212776173 * 1280 * inputConstant) *
          ((pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
            (globalRetention * reanchored.toBodyFamily.mass)) *
          volume convexSet := by
        gcongr
      _ =
        pureWZ2UnitScaleAggregateFrostmanConstant
              inputConstant
              (pureWZ2UnitScaleCompleteFiberOverlapBound A)
              globalRetention *
            reanchored.toBodyFamily.mass *
            volume convexSet := by
        simp [pureWZ2UnitScaleAggregateFrostmanConstant]
        ring

end Kakeya.Assouad

end

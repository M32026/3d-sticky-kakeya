import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# Pointwise multiplicity cap for a pure sticky refinement

This is the finite identity `mu_fine <= mu_coarse * mu_fiber` applied to the
canonical parent map recovered from the parent-free pure Section-6 cover.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Extending a selected shading by zero only reindexes its active carriers,
so it preserves point multiplicity exactly. -/
theorem WZ2PaperSubfamilyZeroExtensionData.pointMultiplicity_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {selected : Kakeya.Streamlined.TubeSubfamily family}
    {shading : WZ1PaperTubeShading selected.family}
    (data : WZ2PaperSubfamilyZeroExtensionData selected shading)
    (point : Point3) :
    data.ambientShading.pointMultiplicity point =
      shading.pointMultiplicity point := by
  let ambientActive : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      point ∈ data.ambientShading.carrier index
  let selectedActive : Finset (Fin selected.family.card) :=
    Finset.univ.filter fun index => point ∈ shading.carrier index
  have hcard : ambientActive.card = selectedActive.card := by
    apply Finset.card_bij
      (fun ambient hambient =>
        Classical.choose
          (data.carrier_support ambient point
            (Finset.mem_filter.mp hambient).2))
    · intro ambient hambient
      have hspec := Classical.choose_spec
        (data.carrier_support ambient point
          (Finset.mem_filter.mp hambient).2)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspec.2⟩
    · intro first hfirst second hsecond heq
      let firstIndex := Classical.choose
        (data.carrier_support first point
          (Finset.mem_filter.mp hfirst).2)
      let secondIndex := Classical.choose
        (data.carrier_support second point
          (Finset.mem_filter.mp hsecond).2)
      have hfirstSpec : selected.embedding firstIndex = first ∧
          point ∈ shading.carrier firstIndex :=
        Classical.choose_spec
          (data.carrier_support first point
            (Finset.mem_filter.mp hfirst).2)
      have hsecondSpec : selected.embedding secondIndex = second ∧
          point ∈ shading.carrier secondIndex :=
        Classical.choose_spec
          (data.carrier_support second point
            (Finset.mem_filter.mp hsecond).2)
      have hindexEq : firstIndex = secondIndex := heq
      exact hfirstSpec.1.symm.trans
        ((congrArg selected.embedding hindexEq).trans hsecondSpec.1)
    · intro index hindex
      have hambient : selected.embedding index ∈ ambientActive := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [data.carrier_embedding index]
        exact (Finset.mem_filter.mp hindex).2
      refine ⟨selected.embedding index, hambient, ?_⟩
      apply selected.embedding.injective
      have hspec := Classical.choose_spec
        (data.carrier_support (selected.embedding index) point
          (Finset.mem_filter.mp hambient).2)
      exact hspec.1
  exact hcard

/-- Zero extension preserves a factor-two point-multiplicity band. -/
theorem WZ2PaperSubfamilyZeroExtensionData.constantMultiplicity
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {selected : Kakeya.Streamlined.TubeSubfamily family}
    {shading : WZ1PaperTubeShading selected.family}
    (data : WZ2PaperSubfamilyZeroExtensionData selected shading)
    {multiplicity : ℕ}
    (hband : shading.HasConstantMultiplicity
      multiplicity (2 * multiplicity)) :
    data.ambientShading.HasConstantMultiplicity
      multiplicity (2 * multiplicity) := by
  intro point hpoint
  have hselected : point ∈ shading.union := by
    rw [← data.union_eq]
    exact hpoint
  rw [data.pointMultiplicity_eq point]
  exact hband point hselected

theorem PureWZ2PropStickyData.refined_pointMultiplicity_upper
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        sourceShading rho logExponent) :
    ∀ point,
      (data.refined.pointMultiplicity point : ENNReal) ≤
        (Kakeya.realRpowENN rho.1
            (2 - sigma - outputLoss) *
          data.coarse.enncard) *
        (Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - outputLoss) *
          data.selected.family.enncard) := by
  let cover := data.cover.toWZ1PaperTubeCover
  have hcompatibility :
      ∀ sourceIndex point,
        point ∈ data.refined.carrier sourceIndex →
          point ∈
            data.croppedCoarseShading.carrier
              (cover.parent sourceIndex) := by
    intro sourceIndex point hpoint
    exact data.balanced.point_compatibility sourceIndex
      (cover.parent sourceIndex)
      (cover.parent_covers sourceIndex) point hpoint
  have hfiber :
      ∀ parent point,
        (cover.fiberPointMultiplicity
            data.refined parent point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - outputLoss) *
            data.selected.family.enncard := by
    intro parent point
    have hraw := data.fiber_multiplicity_upper parent point
    have hindices :
        wz2PaperFullFiberIndices
            data.selected.family data.coarse parent =
          cover.fiberIndices parent :=
      data.cover.c2_fullFiberIndices_eq parent
    have hcap :
        (cover.fiberPointMultiplicity
            data.refined parent point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - outputLoss) *
            ((cover.fiberIndices parent).card : ENNReal) := by
      simpa [WZ1PaperTubeCover.fiberPointMultiplicity, hindices] using hraw
    exact hcap.trans (by
      gcongr
      change ((cover.fiberIndices parent).card : ENNReal) ≤
        (data.selected.family.card : ENNReal)
      exact_mod_cast
        (show (cover.fiberIndices parent).card ≤
            data.selected.family.card by
          simpa using Finset.card_le_univ (cover.fiberIndices parent)))
  exact
    cover.pointMultiplicity_le_coarse_mul_fiber
      data.refined data.croppedCoarseShading hcompatibility
      data.coarse_multiplicity_upper hfiber

/-- Convert the exact pointwise cap into a same-configuration volume floor. -/
theorem PureWZ2PropStickyData.refined_mass_le_cap_mul_volume
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        sourceShading rho logExponent) :
    data.refined.mass ≤
      ((Kakeya.realRpowENN rho.1
            (2 - sigma - outputLoss) *
          data.coarse.enncard) *
        (Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - outputLoss) *
          data.selected.family.enncard)) *
        MeasureTheory.volume data.refined.union := by
  apply mass_le_of_pointMultiplicity_le
  intro point _
  exact data.refined_pointMultiplicity_upper point

/--
The uniform full-fiber comparison controls one fiber by the average fiber,
up to the prescribed power loss.  This is the cardinality cancellation used
in Proposition 5 and avoids replacing one fiber by the whole fine family.
-/
theorem PureWZ2Node5StickyData.coarse_mul_fiberCard_le
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2Node5StickyData
        (sigma := sigma) (outputLoss := outputLoss)
        sourceShading rho logExponent)
    (parent : Fin data.coarse.card) :
    data.coarse.enncard *
        ((wz2PaperFullFiberIndices
          data.selected.family data.coarse parent).card : ENNReal) ≤
      Kakeya.realRpowENN rho.1 (-outputLoss) *
        data.selected.family.enncard := by
  let cover := data.cover.toWZ1PaperTubeCover
  have hsum :
      data.selected.family.enncard =
        ∑ other : Fin data.coarse.card,
          ((wz2PaperFullFiberIndices
            data.selected.family data.coarse other).card : ENNReal) := by
    change (data.selected.family.card : ENNReal) = _
    have hcard :
        data.selected.family.card =
          ∑ other : Fin data.coarse.card,
            (cover.fiberIndices other).card := by
      have hmaps :
          Set.MapsTo cover.parent
            (Finset.univ : Finset (Fin data.selected.family.card))
            (Finset.univ : Finset (Fin data.coarse.card)) :=
        fun _ _ => Finset.mem_univ _
      have hraw := Finset.card_eq_sum_card_fiberwise (H := hmaps)
      simpa [WZ1PaperTubeCover.fiberIndices] using hraw
    exact_mod_cast (by
      simpa [data.cover.c2_fullFiberIndices_eq] using hcard)
  have hpointwise :
      ∀ other : Fin data.coarse.card,
        ((wz2PaperFullFiberIndices
            data.selected.family data.coarse parent).card : ENNReal) ≤
          Kakeya.realRpowENN rho.1 (-outputLoss) *
            ((wz2PaperFullFiberIndices
              data.selected.family data.coarse other).card : ENNReal) :=
    data.full_fiber_uniform parent
  calc
    data.coarse.enncard *
          ((wz2PaperFullFiberIndices
            data.selected.family data.coarse parent).card : ENNReal) =
        ∑ _other : Fin data.coarse.card,
          ((wz2PaperFullFiberIndices
            data.selected.family data.coarse parent).card : ENNReal) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
    _ ≤
        ∑ other : Fin data.coarse.card,
          Kakeya.realRpowENN rho.1 (-outputLoss) *
            ((wz2PaperFullFiberIndices
              data.selected.family data.coarse other).card : ENNReal) := by
      exact Finset.sum_le_sum fun other _ => hpointwise other
    _ =
        Kakeya.realRpowENN rho.1 (-outputLoss) *
          ∑ other : Fin data.coarse.card,
            ((wz2PaperFullFiberIndices
              data.selected.family data.coarse other).card : ENNReal) := by
      rw [Finset.mul_sum]
    _ =
        Kakeya.realRpowENN rho.1 (-outputLoss) *
          data.selected.family.enncard := by rw [← hsum]

/-- Sharp pointwise cap retaining the actual parent fiber cardinality. -/
theorem PureWZ2PropStickyData.refined_pointMultiplicity_upper_sharp
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        sourceShading rho logExponent) :
    ∀ point,
      (data.refined.pointMultiplicity point : ENNReal) ≤
        (Kakeya.realRpowENN rho.1
            (2 - sigma - outputLoss) *
          data.coarse.enncard) *
        (Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - outputLoss) *
          (Finset.univ.sup fun parent : Fin data.coarse.card =>
            ((wz2PaperFullFiberIndices
              data.selected.family data.coarse parent).card : ENNReal))) := by
  let cover := data.cover.toWZ1PaperTubeCover
  have hcompatibility :
      ∀ sourceIndex point,
        point ∈ data.refined.carrier sourceIndex →
          point ∈
            data.croppedCoarseShading.carrier
              (cover.parent sourceIndex) := by
    intro sourceIndex point hpoint
    exact data.balanced.point_compatibility sourceIndex
      (cover.parent sourceIndex)
      (cover.parent_covers sourceIndex) point hpoint
  have hfiber :
      ∀ parent point,
        (cover.fiberPointMultiplicity
            data.refined parent point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - outputLoss) *
            (Finset.univ.sup fun candidate : Fin data.coarse.card =>
              ((wz2PaperFullFiberIndices
                data.selected.family data.coarse candidate).card : ENNReal)) := by
    intro parent point
    have hraw := data.fiber_multiplicity_upper parent point
    have hindices := data.cover.c2_fullFiberIndices_eq parent
    have hcap :
        (cover.fiberPointMultiplicity
            data.refined parent point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - outputLoss) *
            ((wz2PaperFullFiberIndices
              data.selected.family data.coarse parent).card : ENNReal) := by
      simpa [WZ1PaperTubeCover.fiberPointMultiplicity, hindices] using hraw
    exact hcap.trans (by
      gcongr
      exact
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin data.coarse.card)))
          (f := fun candidate : Fin data.coarse.card =>
            ((wz2PaperFullFiberIndices
              data.selected.family data.coarse candidate).card : ENNReal))
          (Finset.mem_univ parent)))
  exact
    cover.pointMultiplicity_le_coarse_mul_fiber
      data.refined data.croppedCoarseShading hcompatibility
      data.coarse_multiplicity_upper hfiber

/--
Summing the per-parent fiber caps over the complete parent partition gives
the sharp global cap used by Lemma 24.  No maximum-fiber or coarse-cardinality
loss is introduced.
-/
theorem PureWZ2PropStickyData.refined_pointMultiplicity_upper_by_fiber_sum
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        sourceShading rho logExponent) :
    ∀ point,
      (data.refined.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - outputLoss) *
          data.selected.family.enncard := by
  let cover := data.cover.toWZ1PaperTubeCover
  intro point
  let fineAtPoint : Finset (Fin data.selected.family.card) :=
    Finset.univ.filter fun sourceIndex =>
      point ∈ data.refined.carrier sourceIndex
  have hmaps :
      Set.MapsTo cover.parent
        (fineAtPoint : Set (Fin data.selected.family.card))
        ((Finset.univ : Finset (Fin data.coarse.card)) :
          Set (Fin data.coarse.card)) := by
    intro sourceIndex _
    exact Finset.mem_univ (cover.parent sourceIndex)
  have hdecompositionNat :
      fineAtPoint.card =
        ∑ parent : Fin data.coarse.card,
          (fineAtPoint.filter fun sourceIndex =>
            cover.parent sourceIndex = parent).card := by
    simpa using Finset.card_eq_sum_card_fiberwise (H := hmaps)
  have hfiberEq :
      ∀ parent : Fin data.coarse.card,
        (fineAtPoint.filter fun sourceIndex =>
            cover.parent sourceIndex = parent).card =
          (cover.fiberIndices parent |>.filter fun sourceIndex =>
            point ∈ data.refined.carrier sourceIndex).card := by
    intro parent
    congr 1
    ext sourceIndex
    constructor
    · intro h
      have houter := Finset.mem_filter.mp h
      have hpoint := (Finset.mem_filter.mp houter.1).2
      have hparent := houter.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparent⟩, hpoint⟩
    · intro h
      have houter := Finset.mem_filter.mp h
      have hparent := (Finset.mem_filter.mp houter.1).2
      have hpoint := houter.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoint⟩, hparent⟩
  have hdecomposition :
      (data.refined.pointMultiplicity point : ENNReal) =
        ∑ parent : Fin data.coarse.card,
          (((cover.fiberIndices parent).filter fun sourceIndex =>
            point ∈ data.refined.carrier sourceIndex).card : ENNReal) := by
    change (fineAtPoint.card : ENNReal) = _
    exact_mod_cast (by
      simpa [hfiberEq] using hdecompositionNat)
  have hfiber :
      ∀ parent : Fin data.coarse.card,
        (((cover.fiberIndices parent).filter fun sourceIndex =>
            point ∈ data.refined.carrier sourceIndex).card : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - outputLoss) *
            ((cover.fiberIndices parent).card : ENNReal) := by
    intro parent
    have hraw := data.fiber_multiplicity_upper parent point
    simpa [data.cover.c2_fullFiberIndices_eq] using hraw
  have hsumCard :
      (∑ parent : Fin data.coarse.card,
          ((cover.fiberIndices parent).card : ENNReal)) =
        data.selected.family.enncard := by
    have hmapsAll :
        Set.MapsTo cover.parent
          (Finset.univ : Finset (Fin data.selected.family.card))
          (Finset.univ : Finset (Fin data.coarse.card)) :=
      fun _ _ => Finset.mem_univ _
    have hraw := Finset.card_eq_sum_card_fiberwise (H := hmapsAll)
    have hrawNat :
        ∑ parent : Fin data.coarse.card,
            (cover.fiberIndices parent).card =
          data.selected.family.card := by
      simpa [WZ1PaperTubeCover.fiberIndices] using hraw.symm
    have hcast :=
      congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) hrawNat
    simpa [Nat.cast_sum, Kakeya.Streamlined.TubeFamily.enncard] using hcast
  rw [hdecomposition]
  calc
    (∑ parent : Fin data.coarse.card,
        (((cover.fiberIndices parent).filter fun sourceIndex =>
          point ∈ data.refined.carrier sourceIndex).card : ENNReal)) ≤
      ∑ parent : Fin data.coarse.card,
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - outputLoss) *
          ((cover.fiberIndices parent).card : ENNReal) := by
      exact Finset.sum_le_sum fun parent _ => hfiber parent
    _ =
      Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - outputLoss) *
        ∑ parent : Fin data.coarse.card,
          ((cover.fiberIndices parent).card : ENNReal) := by
      rw [Finset.mul_sum]
    _ =
      Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - outputLoss) *
        data.selected.family.enncard := by rw [hsumCard]

theorem PureWZ2PropStickyData.refined_mass_le_fiberSumCap_mul_volume
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        sourceShading rho logExponent) :
    data.refined.mass ≤
      (Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - outputLoss) *
        data.selected.family.enncard) *
        MeasureTheory.volume data.refined.union := by
  apply mass_le_of_pointMultiplicity_le
  intro point _
  exact data.refined_pointMultiplicity_upper_by_fiber_sum point

/-- The paper body family has the canonical quadratic mass lower bound. -/
theorem pureWZ2_paperBody_mass_lower
    {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 12)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family) :
    family.enncard * Kakeya.realRpowENN delta 2 ≤
      (wz1PaperBodyFamily family).mass := by
  calc
    family.enncard * Kakeya.realRpowENN delta 2 =
        ∑ _index : Fin family.card,
          Kakeya.realRpowENN delta 2 := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
    _ ≤ ∑ index : Fin family.card,
        MeasureTheory.volume
          (wz1PaperTubeCarrier (family.tube index)) := by
      apply Finset.sum_le_sum
      intro index _
      simpa [Kakeya.realRpowENN, Real.rpow_two] using
        (canonical_volume_lower hdelta).trans
          (wz2PaperTubeCarrier_volume_lower
            hdelta hdeltaSmall (family.tube index) (hline index))
    _ = (wz1PaperBodyFamily family).mass := rfl

/-- Density gives an indexed shaded-mass floor on a cropped extremizer. -/
theorem WZ2PaperCroppedIsExtremal.mass_lower
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hline : WZ1PaperIsLineClass family) :
    Kakeya.realRpowENN delta loss *
        family.enncard * Kakeya.realRpowENN delta 2 ≤
      shading.mass := by
  calc
    Kakeya.realRpowENN delta loss *
          family.enncard * Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN delta loss *
          (family.enncard * Kakeya.realRpowENN delta 2) := by ring
    _ ≤ Kakeya.realRpowENN delta loss *
        (wz1PaperBodyFamily family).mass := by
      gcongr
      exact pureWZ2_paperBody_mass_lower
        extremal.delta_pos hdeltaSmall hline
    _ ≤ shading.mass := extremal.dense

end Kakeya.Assouad

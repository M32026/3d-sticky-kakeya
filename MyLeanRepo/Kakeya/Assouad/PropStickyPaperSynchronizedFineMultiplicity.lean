import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberwiseMultiplicityBands
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteCoarseSelectionPullback
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.HeavyColorClass

/-!
# Synchronize the fine multiplicity level across complete parent fibers

After choosing the best dyadic point-multiplicity band independently in each
complete fiber, pigeonhole the parent fibers by that local level, weighted by
their retained shaded mass.  Keep all fine tubes in every selected parent.
The selected complete fibers have one common `mu_fine` band and retain a
uniform logarithmic source-density floor.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperSynchronizedFineMultiplicityData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (sourceDensity : ENNReal) where
  fiberwise :
    WZ2PaperFiberwiseMultiplicityBandsData cover fineShading
  levelCount : ℕ
  levelCount_eq : levelCount = Nat.log 2 fine.card + 1
  commonLevel : Fin levelCount
  selectedParents : Finset (Fin coarse.card)
  selectedParents_eq :
    selectedParents =
      Finset.univ.filter fun parent =>
        (fiberwise.localBand parent).level = commonLevel.val
  selectedParents_nonempty : selectedParents.Nonempty
  selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse
  selectedCoarse_eq :
    selectedCoarse =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse selectedParents
  pullback :
    WZ2PaperCompleteCoarseSelectionPullbackData
      cover fiberwise.refined coarseShading selectedCoarse
  selected_mass_retention :
    fiberwise.refined.mass ≤
      (levelCount : ENNReal) * pullback.selectedFineShading.mass
  selectedDensity : ENNReal
  selectedDensity_eq :
    selectedDensity = sourceDensity / (levelCount : ENNReal)
  fiber_mass_lower :
    ∀ parent,
      selectedDensity *
            (pullback.restrictedCover.fullFiberSubfamily
              parent).family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (pullback.restrictedCover.fullFiberSubfamily parent)
          pullback.selectedFineShading).mass
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).union →
        (2 ^ commonLevel.val : ENNReal) ≤
            ((restrictPaperShading
              (pullback.restrictedCover.fullFiberSubfamily parent)
              pullback.selectedFineShading).pointMultiplicity point :
                ENNReal) ∧
          ((restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).pointMultiplicity point :
              ENNReal) <
            (2 ^ (commonLevel.val + 1) : ENNReal)

theorem wz2_paper_synchronized_fine_multiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (hdelta : 0 < delta)
    (hCoarseNonempty : coarse.Nonempty)
    (hFineCubical : WZ1PaperIsCubicalShading fineShading)
    (hCoarseCubical : WZ1PaperIsCubicalShading coarseShading)
    (hCompatibility :
      ∀ source point,
        point ∈ fineShading.carrier source →
          point ∈ coarseShading.carrier (cover.parent source))
    (sourceDensity : ENNReal)
    (hSourceDensity : 0 < sourceDensity)
    (hFiberMass :
      ∀ parent,
        sourceDensity *
              (cover.fullFiberSubfamily parent).family.enncard *
              Kakeya.realRpowENN delta 2 ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) fineShading).mass) :
    Nonempty
      (WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity) := by
  have hFiberMassPos :
      ∀ parent,
        0 <
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) fineShading).mass := by
    intro parent
    have hFiberCardPos :
        0 < (cover.fullFiberSubfamily parent).family.card := by
      rcases cover.parent_surjective parent with ⟨source, hsource⟩
      have hmem :
          source ∈ wz2PaperFullFiberIndices fine coarse parent :=
        (cover.mem_fullFiber_iff_parent parent source).mpr hsource
      exact Finset.card_pos.mpr ⟨source, hmem⟩
    have hFiberCard :
        0 < (cover.fullFiberSubfamily parent).family.enncard := by
      change
        0 <
          ((cover.fullFiberSubfamily parent).family.card : ENNReal)
      exact_mod_cast hFiberCardPos
    have hScale :
        0 < Kakeya.realRpowENN delta 2 := by
      exact ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta 2)
    exact
      (ENNReal.mul_pos
        (ENNReal.mul_pos hSourceDensity.ne' hFiberCard.ne').ne'
        hScale.ne').trans_le (hFiberMass parent)
  rcases
      wz2_paper_fiberwise_multiplicity_bands
        cover fineShading hFineCubical hFiberMassPos
    with ⟨fiberwise⟩
  let levelCount := Nat.log 2 fine.card + 1
  have hLevelCount : 0 < levelCount := by
    simp [levelCount]
  have hFiberCardLe :
      ∀ parent,
        (cover.fullFiberSubfamily parent).family.card ≤ fine.card := by
    intro parent
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        (cover.fullFiberSubfamily parent).embedding
        (cover.fullFiberSubfamily parent).embedding.injective
  have hLocalLevel :
      ∀ parent, (fiberwise.localBand parent).level < levelCount := by
    intro parent
    have hlog :
        Nat.log 2
            (cover.fullFiberSubfamily parent).family.card ≤
          Nat.log 2 fine.card :=
      Nat.log_mono_right (hFiberCardLe parent)
    exact (fiberwise.local_level_lt parent).trans_le (by
      dsimp only [levelCount]
      omega)
  let color : Fin coarse.card → Fin levelCount :=
    fun parent =>
      ⟨(fiberwise.localBand parent).level, hLocalLevel parent⟩
  let weight : Fin coarse.card → ENNReal :=
    fun parent => (fiberwise.localBand parent).band.mass
  rcases
      exists_heavy_color_class
        (Finset.univ : Finset (Fin coarse.card))
        levelCount hLevelCount color weight
    with ⟨commonLevel, hHeavy⟩
  let selectedParents : Finset (Fin coarse.card) :=
    Finset.univ.filter fun parent =>
      color parent = commonLevel
  have hTotalWeightPos :
      0 < ∑ parent : Fin coarse.card, weight parent := by
    let parent : Fin coarse.card :=
      ⟨0, hCoarseNonempty⟩
    exact
      (fiberwise.local_band_mass_pos parent).trans_le
        (Finset.single_le_sum (f := weight)
          (fun _ _ => by positivity)
          (Finset.mem_univ parent))
  have hSelectedWeightPos :
      0 < ∑ parent ∈ selectedParents, weight parent := by
    by_contra hzero
    have hsumZero :
        ∑ parent ∈ selectedParents, weight parent = 0 := by
      simpa using hzero
    have hle :
        (∑ parent : Fin coarse.card, weight parent) ≤ 0 := by
      have hHeavy' :
          (∑ parent : Fin coarse.card, weight parent) ≤
            (levelCount : ENNReal) *
              ∑ parent ∈ selectedParents, weight parent := by
        simpa [selectedParents] using hHeavy
      rw [hsumZero, mul_zero] at hHeavy'
      exact hHeavy'
    exact (not_le.mpr hTotalWeightPos) hle
  have hSelectedParentsNonempty : selectedParents.Nonempty := by
    by_contra hempty
    have heq : selectedParents = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [heq] at hSelectedWeightPos
    simp at hSelectedWeightPos
  let selectedCoarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse selectedParents
  rcases
      wz2_paper_complete_coarse_selection_pullback
        cover fiberwise.refined coarseShading
        fiberwise.refined_cubical hCoarseCubical
        (by
          intro source point hpoint
          exact hCompatibility source point
            (fiberwise.refined_subshading source hpoint))
        selectedCoarse
    with ⟨pullback⟩
  have hFiberwiseMass :
      fiberwise.refined.mass =
        ∑ parent : Fin coarse.card, weight parent := by
    calc
      fiberwise.refined.mass =
          ∑ parent : Fin coarse.card,
            (restrictPaperShading
              (cover.fullFiberSubfamily parent)
              fiberwise.refined).mass :=
        (cover.sum_fullFiberShading_mass fiberwise.refined).symm
      _ =
          ∑ parent : Fin coarse.card, weight parent := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [fiberwise.local_mass_eq parent]
  have hSelectedMass :
      pullback.selectedFineShading.mass =
        ∑ parent ∈ selectedParents, weight parent := by
    calc
      pullback.selectedFineShading.mass =
          ∑ parent : Fin selectedCoarse.family.card,
            (restrictPaperShading
              (pullback.restrictedCover.fullFiberSubfamily parent)
              pullback.selectedFineShading).mass :=
        (pullback.restrictedCover
          |>.sum_fullFiberShading_mass
            pullback.selectedFineShading).symm
      _ =
          ∑ parent : Fin selectedCoarse.family.card,
            weight (selectedCoarse.embedding parent) := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [pullback.full_fiber_mass_eq parent]
        rw [fiberwise.local_mass_eq (selectedCoarse.embedding parent)]
      _ =
          ∑ parent ∈ selectedParents, weight parent := by
        exact
          Fintype.sum_equiv
            (selectedParents.orderIsoOfFin rfl).toEquiv
            (fun parent : Fin selectedCoarse.family.card =>
              weight (selectedCoarse.embedding parent))
            (fun parent : selectedParents => weight parent.1)
            (fun _ => rfl) |>.trans <|
              Finset.sum_coe_sort selectedParents weight
  have hSelectedRetention :
      fiberwise.refined.mass ≤
        (levelCount : ENNReal) * pullback.selectedFineShading.mass := by
    rw [hFiberwiseMass, hSelectedMass]
    simpa [selectedParents] using hHeavy
  let selectedDensity :=
    sourceDensity / (levelCount : ENNReal)
  have hGlobalDenomZero :
      (levelCount : ENNReal) ≠ 0 := by
    exact_mod_cast hLevelCount.ne'
  have hGlobalDenomTop :
      (levelCount : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hFiberMassLower :
      ∀ parent,
        selectedDensity *
              (pullback.restrictedCover.fullFiberSubfamily
                parent).family.enncard *
              Kakeya.realRpowENN delta 2 ≤
          (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).mass := by
    intro parent
    let ambientParent := selectedCoarse.embedding parent
    let reindex :
        WZ2PaperCompleteFiberReindexData
          cover pullback.selectedFine pullback.restrictedCover
          parent ambientParent
          (pullback.full_fiber_complete parent) :=
      Classical.choice <|
        wz2_paper_complete_fiber_reindex
          cover pullback.selectedFine pullback.restrictedCover
          parent ambientParent
          (pullback.full_fiber_complete parent)
    have hFiberCardEq :
        (pullback.restrictedCover.fullFiberSubfamily
            parent).family.enncard =
          (cover.fullFiberSubfamily ambientParent).family.enncard := by
      have hCardNat :
          (pullback.restrictedCover.fullFiberSubfamily
              parent).family.card =
            (cover.fullFiberSubfamily ambientParent).family.card := by
        simpa only [Fintype.card_fin] using
          Fintype.card_congr
            (Equiv.ofBijective reindex.localIndex
              reindex.localIndex_bijective)
      change
        ((pullback.restrictedCover.fullFiberSubfamily
            parent).family.card : ENNReal) =
          ((cover.fullFiberSubfamily ambientParent).family.card : ENNReal)
      exact congrArg (fun value : ℕ => (value : ENNReal)) hCardNat
    let localDenominator : ENNReal :=
      ((Nat.log 2
          (cover.fullFiberSubfamily ambientParent).family.card +
        1 : ℕ) : ENNReal)
    have hDenominator :
        localDenominator ≤ (levelCount : ENNReal) := by
      have hDenominatorNat :
          Nat.log 2
                (cover.fullFiberSubfamily ambientParent).family.card +
              1 ≤
            levelCount := by
        dsimp only [levelCount]
        exact Nat.add_le_add_right
          (Nat.log_mono_right (hFiberCardLe ambientParent)) 1
      dsimp only [localDenominator]
      exact_mod_cast hDenominatorNat
    have hOriginal :
        sourceDensity *
              (cover.fullFiberSubfamily ambientParent).family.enncard *
              Kakeya.realRpowENN delta 2 ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent) fineShading).mass :=
      hFiberMass ambientParent
    have hDivOriginal :
        (sourceDensity *
              (cover.fullFiberSubfamily ambientParent).family.enncard *
              Kakeya.realRpowENN delta 2) /
              (levelCount : ENNReal) ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent) fineShading).mass /
              (levelCount : ENNReal) :=
      ENNReal.div_le_div_right hOriginal _
    have hDivDenominator :
        (restrictPaperShading
              (cover.fullFiberSubfamily ambientParent) fineShading).mass /
              (levelCount : ENNReal) ≤
          (restrictPaperShading
              (cover.fullFiberSubfamily ambientParent) fineShading).mass /
              localDenominator :=
      ENNReal.div_le_div_left hDenominator _
    calc
      selectedDensity *
            (pullback.restrictedCover.fullFiberSubfamily
              parent).family.enncard *
            Kakeya.realRpowENN delta 2 =
          (sourceDensity *
              (cover.fullFiberSubfamily ambientParent).family.enncard *
              Kakeya.realRpowENN delta 2) /
            (levelCount : ENNReal) := by
        rw [hFiberCardEq]
        dsimp only [selectedDensity]
        simp only [div_eq_mul_inv]
        ring
      _ ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent) fineShading).mass /
              (levelCount : ENNReal) :=
        hDivOriginal
      _ ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent) fineShading).mass /
              localDenominator :=
        hDivDenominator
      _ ≤
          (fiberwise.localBand ambientParent).band.mass := by
        simpa [localDenominator] using
          (fiberwise.localBand ambientParent).band_mass_retention
      _ =
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent)
            fiberwise.refined).mass :=
        (fiberwise.local_mass_eq ambientParent).symm
      _ =
          (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).mass :=
        (pullback.full_fiber_mass_eq parent).symm
  have hFiberBand :
      ∀ parent point,
        point ∈
            (restrictPaperShading
              (pullback.restrictedCover.fullFiberSubfamily parent)
              pullback.selectedFineShading).union →
          (2 ^ commonLevel.val : ENNReal) ≤
              ((restrictPaperShading
                (pullback.restrictedCover.fullFiberSubfamily parent)
                pullback.selectedFineShading).pointMultiplicity point :
                  ENNReal) ∧
            ((restrictPaperShading
              (pullback.restrictedCover.fullFiberSubfamily parent)
              pullback.selectedFineShading).pointMultiplicity point :
                ENNReal) <
              (2 ^ (commonLevel.val + 1) : ENNReal) := by
    intro parent point hpoint
    let ambientParent := selectedCoarse.embedding parent
    have hParentMem :
        ambientParent ∈ selectedParents :=
      Finset.orderEmbOfFin_mem selectedParents rfl parent
    have hLevel :
        (fiberwise.localBand ambientParent).level =
          commonLevel.val := by
      have hcolor :
          color ambientParent = commonLevel :=
        (Finset.mem_filter.mp hParentMem).2
      exact congrArg Fin.val hcolor
    have hPointAmbient :
        point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent)
            fiberwise.refined).union := by
      rcases hpoint with ⟨index, hindex⟩
      let reindex :
          WZ2PaperCompleteFiberReindexData
            cover pullback.selectedFine pullback.restrictedCover
            parent ambientParent
            (pullback.full_fiber_complete parent) :=
        Classical.choice <|
          wz2_paper_complete_fiber_reindex
            cover pullback.selectedFine pullback.restrictedCover
            parent ambientParent
            (pullback.full_fiber_complete parent)
      let ambientIndex := reindex.localIndex index
      refine ⟨ambientIndex, ?_⟩
      rw [pullback.selectedFineShading_eq] at hindex
      change
        point ∈ fiberwise.refined.carrier
          (pullback.selectedFine.embedding
            ((pullback.restrictedCover.fullFiberSubfamily
              parent).embedding index)) at hindex
      rw [reindex.ambient_eq index] at hindex
      exact hindex
    have hBand :=
      fiberwise.fiber_multiplicity_band
        ambientParent point hPointAmbient
    have hMultiplicity :=
      pullback.full_fiber_pointMultiplicity_eq parent point
    rw [hMultiplicity, ← hLevel]
    simpa using hBand
  exact
    ⟨{
      fiberwise := fiberwise
      levelCount := levelCount
      levelCount_eq := rfl
      commonLevel := commonLevel
      selectedParents := selectedParents
      selectedParents_eq := by
        dsimp only [selectedParents, color]
        apply Finset.filter_congr
        intro parent _
        constructor
        · intro h
          exact congrArg Fin.val h
        · intro h
          exact Fin.ext h
      selectedParents_nonempty := hSelectedParentsNonempty
      selectedCoarse := selectedCoarse
      selectedCoarse_eq := rfl
      pullback := pullback
      selected_mass_retention := hSelectedRetention
      selectedDensity := selectedDensity
      selectedDensity_eq := rfl
      fiber_mass_lower := hFiberMassLower
      fiber_multiplicity_band := hFiberBand
    }⟩

end Kakeya.Assouad

end

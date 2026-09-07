import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12InternalBridge
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickySelectedHitCover

/-!
# Public and internal cover synchronization

The public Assouad cover and the internal cropped WZ cover need not be chosen
independently and then identified after the fact.  This record is the minimal
provenance certificate for a cover constructed jointly: both covers use the
same coarse family and their uniquely determined parent maps agree.

All three fiber descriptions used downstream are derived from this one field:

* the public ordinary strict full fiber;
* the internal assigned fiber;
* the cropped literal strict full fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Minimal synchronization certificate between one public pure cover and one
internal cropped WZ cover on the same indexed families.
-/
structure WZ2PaperPureInternalCoverSynchronization
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (internalCover : WZ2PaperPartitioningCover fine coarse) : Prop where
  publicCover : WZ2PaperPurePartitioningCover fine coarse
  parent_eq :
    ∀ source,
      publicCover.parent source = internalCover.parent source

namespace WZ2PaperPureInternalCoverSynchronization

/-- Transport synchronization across an equality of dependent exact-scale
cover records. -/
noncomputable def ofScaleDataHEq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {firstScale secondScale :
      Kakeya.Streamlined.AdmissibleScale delta}
    {C : ENNReal}
    {firstData :
      WZ2PaperScaleCoverData fine firstScale C}
    {secondData :
      WZ2PaperScaleCoverData fine secondScale C}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine firstData.coarse firstData.cover)
    (hscale : firstScale = secondScale)
    (hdata : HEq firstData secondData) :
    WZ2PaperPureInternalCoverSynchronization
      fine secondData.coarse secondData.cover := by
  subst secondScale
  have hdata' : firstData = secondData :=
    eq_of_heq hdata
  subst secondData
  exact sync

/-- The public ordinary strict fiber is the internal assigned fiber. -/
theorem ordinaryFullFiberIndices_eq_assigned
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices fine coarse parent =
      internalCover.fiberIndices parent := by
  ext source
  rw [
    sync.publicCover.mem_fullFiber_iff_parent_eq
      hrho parent source
  ]
  simp only [
    WZ1PaperTubeCover.fiberIndices,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ]
  exact
    ⟨fun h => (sync.parent_eq source).symm.trans h,
      fun h => (sync.parent_eq source).trans h⟩

/-- The cropped literal strict fiber is the internal assigned fiber. -/
theorem croppedFullFiberIndices_eq_assigned
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (_sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (parent : Fin coarse.card) :
    wz2PaperLiteralFullFiberIndices fine coarse parent =
      internalCover.fiberIndices parent :=
  internalCover.literalFullFiberIndices_eq parent

/-- Public ordinary and cropped literal strict fibers are the same retained
indexed fiber. -/
theorem ordinaryFullFiberIndices_eq_cropped
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices fine coarse parent =
      wz2PaperLiteralFullFiberIndices fine coarse parent := by
  rw [
    sync.ordinaryFullFiberIndices_eq_assigned hrho parent,
    sync.croppedFullFiberIndices_eq_assigned parent
  ]

/-- The public ordinary strict fiber is also the historical WZ full fiber
used by the closed analysis pipeline. -/
theorem ordinaryFullFiberIndices_eq_internalFullFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices fine coarse parent =
      wz2PaperFullFiberIndices fine coarse parent := by
  rw [
    sync.ordinaryFullFiberIndices_eq_assigned hrho parent,
    internalCover.fullFiberIndices_eq parent
  ]

/-- The public ordinary count agrees with the internal cropped full-fiber
count used by the existing Section 6 proof. -/
theorem ordinaryFullFiberCount_eq_internal
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberCount fine coarse parent =
      wz2PaperFullFiberCount fine coarse parent := by
  rw [
    wz2PaperOrdinaryFullFiberCount,
    wz2PaperFullFiberCount,
    sync.ordinaryFullFiberIndices_eq_assigned hrho parent,
    internalCover.fullFiberIndices_eq parent
  ]

/-- Internal full-fiber uniformity is therefore genuine public strict-fiber
uniformity. -/
theorem public_full_fiber_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    {C : ENNReal}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (internalUniform :
      ∀ first second,
        wz2PaperFullFiberCount fine coarse first ≤
          C * wz2PaperFullFiberCount fine coarse second) :
    WZ2PaperPureFullFibersAreCUniform fine coarse C := by
  intro first second
  rw [
    sync.ordinaryFullFiberCount_eq_internal hrho first,
    sync.ordinaryFullFiberCount_eq_internal hrho second
  ]
  exact internalUniform first second

/--
Transport synchronization to an already constructed fine restriction whose
parent map agrees with the ambient parent map along the fine embedding.
-/
noncomputable def restrictFineOfParentEq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (restrictedInternal :
      WZ2PaperPartitioningCover selected.family coarse)
    (restrictedParentEq :
      ∀ source,
        restrictedInternal.parent source =
          internalCover.parent (selected.embedding source)) :
    WZ2PaperPureInternalCoverSynchronization
      selected.family coarse restrictedInternal := by
  have selected_mem_public_fullFiber :
      ∀ source : Fin selected.family.card,
        source ∈
          wz2PaperOrdinaryFullFiberIndices
            selected.family coarse
            (restrictedInternal.parent source) := by
    intro source
    have hambient :
        selected.embedding source ∈
          wz2PaperOrdinaryFullFiberIndices fine coarse
            (internalCover.parent (selected.embedding source)) := by
      rw [← sync.parent_eq]
      exact
        sync.publicCover.parent_mem_fullFiber
          (selected.embedding source)
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hambient ⊢
    rw [selected.tube_eq]
    rw [restrictedParentEq]
    exact hambient
  let restrictedPublic :
      WZ2PaperPurePartitioningCover selected.family coarse :=
    {
      covers := fun source =>
        ⟨restrictedInternal.parent source,
          selected_mem_public_fullFiber source⟩
      doubled_fibers_disjoint := by
        intro first second hne
        rw [Finset.disjoint_left]
        intro source hfirst hsecond
        have hambientFirst :
            selected.embedding source ∈
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine coarse first := by
          simpa only [
            mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
            selected.tube_eq
          ] using hfirst
        have hambientSecond :
            selected.embedding source ∈
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine coarse second := by
          simpa only [
            mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
            selected.tube_eq
          ] using hsecond
        exact
          ((Finset.disjoint_left.mp
              (sync.publicCover.doubled_fibers_disjoint
                first second hne))
            hambientFirst) hambientSecond
    }
  refine
    {
      publicCover := restrictedPublic
      parent_eq := ?_
    }
  intro source
  exact
    (restrictedPublic.mem_fullFiber_iff_parent_eq
      hrho (restrictedInternal.parent source) source).mp
      (selected_mem_public_fullFiber source)

/-- Restrict only the fine family while retaining every coarse parent. -/
noncomputable def restrictFine
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parentSurjective :
      Function.Surjective fun index =>
        internalCover.parent (selected.embedding index)) :
    WZ2PaperPureInternalCoverSynchronization
      selected.family coarse
      (internalCover.restrictFine selected parentSurjective) :=
  sync.restrictFineOfParentEq hrho selected
    (internalCover.restrictFine selected parentSurjective)
    (fun _ => rfl)

/--
Restrict both fine and coarse families when the new internal parent map agrees
with the ambient parent map after applying the two embeddings.
-/
noncomputable def restrictFineCoarseOfParentEq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (selectedFine : Kakeya.Streamlined.TubeSubfamily fine)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse)
    (restrictedInternal :
      WZ2PaperPartitioningCover
        selectedFine.family selectedCoarse.family)
    (parentAmbientEq :
      ∀ source,
        selectedCoarse.embedding (restrictedInternal.parent source) =
          internalCover.parent (selectedFine.embedding source)) :
    WZ2PaperPureInternalCoverSynchronization
      selectedFine.family selectedCoarse.family restrictedInternal := by
  have selected_mem_public_fullFiber :
      ∀ source : Fin selectedFine.family.card,
        source ∈
          wz2PaperOrdinaryFullFiberIndices
            selectedFine.family selectedCoarse.family
            (restrictedInternal.parent source) := by
    intro source
    have hambient :
        selectedFine.embedding source ∈
          wz2PaperOrdinaryFullFiberIndices fine coarse
            (selectedCoarse.embedding
              (restrictedInternal.parent source)) := by
      rw [parentAmbientEq, ← sync.parent_eq]
      exact
        sync.publicCover.parent_mem_fullFiber
          (selectedFine.embedding source)
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hambient ⊢
    simpa only [
      selectedFine.tube_eq,
      selectedCoarse.tube_eq
    ] using hambient
  let restrictedPublic :
      WZ2PaperPurePartitioningCover
        selectedFine.family selectedCoarse.family :=
    {
      covers := fun source =>
        ⟨restrictedInternal.parent source,
          selected_mem_public_fullFiber source⟩
      doubled_fibers_disjoint := by
        intro first second hne
        rw [Finset.disjoint_left]
        intro source hfirst hsecond
        have hambientNe :
            selectedCoarse.embedding first ≠
              selectedCoarse.embedding second :=
          selectedCoarse.embedding.injective.ne hne
        have hambientFirst :
            selectedFine.embedding source ∈
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine coarse (selectedCoarse.embedding first) := by
          simpa only [
            mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
            selectedFine.tube_eq,
            selectedCoarse.tube_eq
          ] using hfirst
        have hambientSecond :
            selectedFine.embedding source ∈
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine coarse (selectedCoarse.embedding second) := by
          simpa only [
            mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
            selectedFine.tube_eq,
            selectedCoarse.tube_eq
          ] using hsecond
        exact
          ((Finset.disjoint_left.mp
              (sync.publicCover.doubled_fibers_disjoint
                (selectedCoarse.embedding first)
                (selectedCoarse.embedding second)
                hambientNe))
            hambientFirst) hambientSecond
    }
  refine
    {
      publicCover := restrictedPublic
      parent_eq := ?_
    }
  intro source
  exact
    (restrictedPublic.mem_fullFiber_iff_parent_eq
      hrho (restrictedInternal.parent source) source).mp
      (selected_mem_public_fullFiber source)

/--
Restrict synchronized covers to a selected fine family and exactly the coarse
parents still hit by that family.

The public cover is restricted geometrically, while the internal cover uses
the existing hit-parent construction.  Equality of the ambient parent maps
then makes the two restricted parent maps agree.
-/
noncomputable def restrictToHitParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {internalCover : WZ2PaperPartitioningCover fine coarse}
    (sync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (hrho : 0 ≤ rho)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    WZ2PaperPureInternalCoverSynchronization
      selected.family
      (internalCover.hitParentSubfamily selected).family
      (internalCover.restrictToHitParents selected) := by
  let hitCoarse := internalCover.hitParentSubfamily selected
  let restrictedInternal :=
    internalCover.restrictToHitParents selected
  have selected_mem_restricted_fullFiber :
      ∀ source : Fin selected.family.card,
        source ∈
          wz2PaperOrdinaryFullFiberIndices
            selected.family hitCoarse.family
            (internalCover.hitParent selected source) := by
    intro source
    have hambient :
        selected.embedding source ∈
          wz2PaperOrdinaryFullFiberIndices fine coarse
            (internalCover.parent (selected.embedding source)) := by
      rw [← sync.parent_eq (selected.embedding source)]
      exact
        sync.publicCover.parent_mem_fullFiber
          (selected.embedding source)
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hambient ⊢
    rw [
      selected.tube_eq,
      hitCoarse.tube_eq,
      internalCover.hitParent_ambient
    ]
    exact hambient
  let restrictedPublic :
      WZ2PaperPurePartitioningCover
        selected.family hitCoarse.family :=
    {
      covers := fun source =>
        ⟨internalCover.hitParent selected source,
          selected_mem_restricted_fullFiber source⟩
      doubled_fibers_disjoint := by
        intro first second hne
        rw [Finset.disjoint_left]
        intro source hfirst hsecond
        have hambientNe :
            hitCoarse.embedding first ≠
              hitCoarse.embedding second :=
          hitCoarse.embedding.injective.ne hne
        have hambientFirst :
            selected.embedding source ∈
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine coarse (hitCoarse.embedding first) := by
          simpa only [
            mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
            selected.tube_eq,
            hitCoarse.tube_eq
          ] using hfirst
        have hambientSecond :
            selected.embedding source ∈
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine coarse (hitCoarse.embedding second) := by
          simpa only [
            mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
            selected.tube_eq,
            hitCoarse.tube_eq
          ] using hsecond
        exact
          ((Finset.disjoint_left.mp
              (sync.publicCover.doubled_fibers_disjoint
                (hitCoarse.embedding first)
                (hitCoarse.embedding second)
                hambientNe))
            hambientFirst) hambientSecond
    }
  refine
    {
      publicCover := restrictedPublic
      parent_eq := ?_
    }
  intro source
  apply
    (restrictedPublic.mem_fullFiber_iff_parent_eq
      hrho (restrictedInternal.parent source) source).mp
  have hrestrictedParent :
      restrictedInternal.parent source =
        internalCover.hitParent selected source := by
    rfl
  rw [hrestrictedParent]
  exact selected_mem_restricted_fullFiber source

/-- One public tree edge obtained from the synchronized internal WZ covers. -/
theorem fullFiber_tree_edge
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    {internalRho : WZ2PaperPartitioningCover fine coarseRho}
    {internalSigma : WZ2PaperPartitioningCover fine coarseSigma}
    (rhoSync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarseRho internalRho)
    (sigmaSync :
      WZ2PaperPureInternalCoverSynchronization
        fine coarseSigma internalSigma)
    (hrho : 0 ≤ rho)
    (hsigma : 0 ≤ sigma)
    (hscale : 2 * rho ≤ sigma)
    (parentRho : Fin coarseRho.card) :
    ∃ parentSigma : Fin coarseSigma.card,
      ∀ sourceIndex,
        sourceIndex ∈
            wz2PaperOrdinaryFullFiberIndices
              fine coarseRho parentRho →
          sourceIndex ∈
            wz2PaperOrdinaryFullFiberIndices
              fine coarseSigma parentSigma := by
  rcases internalRho.parent_surjective parentRho with
    ⟨anchor, hanchorParent⟩
  let parentSigma := internalSigma.parent anchor
  refine ⟨parentSigma, ?_⟩
  intro sourceIndex hsource
  have hsourceRho :
      internalRho.parent sourceIndex = parentRho := by
    have hmem :
        sourceIndex ∈ internalRho.fiberIndices parentRho := by
      rw [← rhoSync.ordinaryFullFiberIndices_eq_assigned
        hrho parentRho]
      exact hsource
    exact (Finset.mem_filter.mp hmem).2
  have hparentSigma :
      internalSigma.parent sourceIndex =
        internalSigma.parent anchor :=
    internalRho.fiber_parent_stable
      internalSigma hscale parentRho
      hsourceRho hanchorParent
  have hassigned :
      sourceIndex ∈ internalSigma.fiberIndices parentSigma := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ sourceIndex,
        by simpa [parentSigma] using hparentSigma⟩
  rw [
    sigmaSync.ordinaryFullFiberIndices_eq_assigned
      hsigma parentSigma
  ]
  exact hassigned

end WZ2PaperPureInternalCoverSynchronization

end Kakeya.Assouad

end

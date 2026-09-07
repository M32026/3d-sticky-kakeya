import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CoverSynchronization
import MyLeanRepo.Kakeya.Assouad.PropStickyNestedQuotientCover

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperPureQuotientCoverData
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal : WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal : WZ2PaperPartitioningCover fine actualCoarse}
    {C : ENNReal}
    (callerSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine callerCoarse callerInternal)
    (actualSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine actualCoarse actualInternal)
    (quotient :
      WZ2PaperNestedQuotientCoverData
        callerInternal actualInternal C) : Prop where
  publicCover :
    WZ2PaperPurePartitioningCover callerCoarse actualCoarse
  parent_eq :
    ∀ callerIndex,
      publicCover.parent callerIndex = quotient.parent callerIndex

namespace WZ2PaperPureQuotientCoverData

theorem ordinary_parent_containment
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal : WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal : WZ2PaperPartitioningCover fine actualCoarse}
    {C : ENNReal}
    {callerSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine callerCoarse callerInternal}
    {actualSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine actualCoarse actualInternal}
    {quotient :
      WZ2PaperNestedQuotientCoverData
        callerInternal actualInternal C}
    (data :
      WZ2PaperPureQuotientCoverData
        callerSynchronization actualSynchronization quotient)
    (callerIndex : Fin callerCoarse.card) :
    (callerCoarse.tube callerIndex).carrier ⊆
      (actualCoarse.tube (quotient.parent callerIndex)).carrier := by
  have hmember :=
    data.publicCover.parent_mem_fullFiber callerIndex
  rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hmember
  rw [data.parent_eq callerIndex] at hmember
  exact hmember

theorem ordinaryFullFiberIndices_eq_assigned
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal : WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal : WZ2PaperPartitioningCover fine actualCoarse}
    {C : ENNReal}
    {callerSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine callerCoarse callerInternal}
    {actualSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine actualCoarse actualInternal}
    {quotient :
      WZ2PaperNestedQuotientCoverData
        callerInternal actualInternal C}
    (data :
      WZ2PaperPureQuotientCoverData
        callerSynchronization actualSynchronization quotient)
    (hactual : 0 ≤ actual)
    (actualIndex : Fin actualCoarse.card) :
    wz2PaperOrdinaryFullFiberIndices
        callerCoarse actualCoarse actualIndex =
      quotient.cover.fiberIndices actualIndex := by
  ext callerIndex
  rw [
    data.publicCover.mem_fullFiber_iff_parent_eq
      hactual actualIndex callerIndex
  ]
  simp only [
    WZ2PaperDilatedTubeCover.fiberIndices,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ]
  rw [data.parent_eq callerIndex, quotient.cover_parent_eq]

theorem ordinaryFullFiberCount_eq_assigned
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal : WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal : WZ2PaperPartitioningCover fine actualCoarse}
    {C : ENNReal}
    {callerSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine callerCoarse callerInternal}
    {actualSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine actualCoarse actualInternal}
    {quotient :
      WZ2PaperNestedQuotientCoverData
        callerInternal actualInternal C}
    (data :
      WZ2PaperPureQuotientCoverData
        callerSynchronization actualSynchronization quotient)
    (hactual : 0 ≤ actual)
    (actualIndex : Fin actualCoarse.card) :
    wz2PaperOrdinaryFullFiberCount
        callerCoarse actualCoarse actualIndex =
      quotient.cover.fiberCount actualIndex := by
  rw [
    wz2PaperOrdinaryFullFiberCount,
    WZ2PaperDilatedTubeCover.fiberCount,
    data.ordinaryFullFiberIndices_eq_assigned hactual actualIndex
  ]

end WZ2PaperPureQuotientCoverData

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Internal ordinary-cover bridge to Assouad Definition 2.12

This module forgets the assigned parent map of the historical ordinary-tube
`WZ2GeometricPartitioningCertificate` and exposes its paper-semantic
parent-map-free cover.  The reverse direction is intentionally not claimed.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

@[simp] theorem wz2PaperCenteredDilatedCarrier_eq_wz1DilatedTubeCarrier
    {rho factor : ℝ} (tube : Kakeya.DeltaTube rho) :
    wz2PaperCenteredDilatedCarrier factor tube =
      wz1DilatedTubeCarrier factor tube := by
  rfl

@[simp] theorem wz2PaperOrdinaryFullFiberIndices_eq_wz2FullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices fine coarse parent =
      wz2FullFiberIndices fine coarse parent := by
  rfl

@[simp] theorem
    wz2PaperOrdinaryDilatedFiberIndices_two_eq_wz2DoubledFullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse parent =
      wz2DoubledFullFiberIndices fine coarse parent := by
  rfl

/-- Forget the internal assigned parent while retaining the literal paper
partitioning cover. -/
noncomputable def WZ2GeometricPartitioningCertificate.toPure
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : Kakeya.Streamlined.TubeCover fine coarse}
    (geometric : WZ2GeometricPartitioningCertificate cover) :
    WZ2PaperPurePartitioningCover fine coarse where
  covers source := by
    refine ⟨cover.parent source, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact cover.nested source
  doubled_fibers_disjoint first second hne := by
    simpa only [
      wz2PaperOrdinaryDilatedFiberIndices_two_eq_wz2DoubledFullFiberIndices
    ] using geometric.doubled_fibers_disjoint first second hne

namespace WZ2GeometricPartitioningCertificate

/-- The parent derived from the paper relation is the internal assigned parent. -/
theorem toPure_parent_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : Kakeya.Streamlined.TubeCover fine coarse}
    (geometric : WZ2GeometricPartitioningCertificate cover)
    (hrho : 0 ≤ rho)
    (source : Fin fine.card) :
    geometric.toPure.parent source = cover.parent source := by
  apply
    (geometric.toPure.mem_fullFiber_iff_parent_eq
      hrho (cover.parent source) source).mp
  rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
  exact cover.nested source

/-- The internal assigned fiber is exactly the public strict full fiber. -/
theorem toPure_fullFiberIndices_eq_assigned
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : Kakeya.Streamlined.TubeCover fine coarse}
    (geometric : WZ2GeometricPartitioningCertificate cover)
    (hrho : 0 ≤ rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices fine coarse parent =
      cover.toFactoring.fiberIndices parent := by
  ext source
  rw [
    geometric.toPure.mem_fullFiber_iff_parent_eq hrho parent source
  ]
  constructor
  · intro hparent
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    change cover.parent source = parent
    rw [← geometric.toPure_parent_eq hrho source]
    exact hparent
  · intro hsource
    have hparent :
        cover.parent source = parent :=
      (Finset.mem_filter.mp hsource).2
    rw [geometric.toPure_parent_eq hrho source]
    exact hparent

/-- The public full-fiber count agrees with the internal assigned count. -/
theorem toPure_fullFiberCount_eq_assigned
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : Kakeya.Streamlined.TubeCover fine coarse}
    (geometric : WZ2GeometricPartitioningCertificate cover)
    (hrho : 0 ≤ rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberCount fine coarse parent =
      ((cover.toFactoring.fiberIndices parent).card : ENNReal) := by
  rw [wz2PaperOrdinaryFullFiberCount, geometric.toPure_fullFiberIndices_eq_assigned hrho]
  rfl

end WZ2GeometricPartitioningCertificate

namespace WZ2PaperPurePartitioningCover

/-- Build the internal ordinary `TubeCover` from the uniquely derived literal
parent.  Finite uniformity excludes empty parents and supplies surjectivity. -/
noncomputable def toTubeCover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (pure : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (fine_nonempty : fine.Nonempty)
    {C : ENNReal}
    (uniform :
      WZ2PaperPureFullFibersAreCUniform fine coarse C) :
    Kakeya.Streamlined.TubeCover fine coarse where
  parent := pure.parent
  parent_surjective :=
    pure.parent_surjective_of_uniform
      hrho fine_nonempty uniform
  nested source := by
    exact
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        (pure.parent source) source).mp
        (pure.parent_mem_fullFiber source)

/-- The derived ordinary assigned cover carries exactly the historical
geometric partitioning certificate. -/
noncomputable def toGeometricPartitioningCertificate
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (pure : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (fine_nonempty : fine.Nonempty)
    {C : ENNReal}
    (uniform :
      WZ2PaperPureFullFibersAreCUniform fine coarse C) :
    WZ2GeometricPartitioningCertificate
      (pure.toTubeCover hrho fine_nonempty uniform) where
  parent_unique source candidate hcandidate := by
    apply pure.fullFiber_parent_unique hrho
      (by
        rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
        exact hcandidate)
      (pure.parent_mem_fullFiber source)
  doubled_fibers_disjoint first second hne := by
    simpa only [
      ← wz2PaperOrdinaryDilatedFiberIndices_two_eq_wz2DoubledFullFiberIndices
    ] using pure.doubled_fibers_disjoint first second hne

/-- The assigned parent of the derived cover is definitionally the parent
derived from the public full-fiber relation. -/
@[simp] theorem toTubeCover_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (pure : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (fine_nonempty : fine.Nonempty)
    {C : ENNReal}
    (uniform :
      WZ2PaperPureFullFibersAreCUniform fine coarse C)
    (source : Fin fine.card) :
    (pure.toTubeCover hrho fine_nonempty uniform).parent source =
      pure.parent source := by
  rfl

end WZ2PaperPurePartitioningCover

end Kakeya.Assouad

end

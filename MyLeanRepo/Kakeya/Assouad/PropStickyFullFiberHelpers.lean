import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Full geometric fiber helpers for WZ2 `prop: sticky`

The unique parent map of a paper partitioning cover is definitionally
equivalent to the full geometric cover relation.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

@[simp] theorem mem_wz2PaperFullFiberIndices_iff
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈ wz2PaperFullFiberIndices fine coarse parent ↔
      WZ1PaperTubeCovers
        (fine.tube source) (coarse.tube parent) := by
  simp [wz2PaperFullFiberIndices]

@[simp] theorem WZ2PaperPartitioningCover.mem_fullFiber_iff_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈ wz2PaperFullFiberIndices fine coarse parent ↔
      cover.parent source = parent := by
  constructor
  · intro h
    exact (cover.parent_unique source parent
      ((mem_wz2PaperFullFiberIndices_iff parent source).mp h)).symm
  · intro h
    rw [← h]
    exact
      (mem_wz2PaperFullFiberIndices_iff
        (cover.parent source) source).mpr
        (cover.parent_covers source)

@[simp] theorem
    WZ2PaperPartitioningCover.mem_literalFullFiber_iff_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈ wz2PaperLiteralFullFiberIndices fine coarse parent ↔
      cover.parent source = parent := by
  constructor
  · intro h
    have hcovered :
        WZ2PaperTubeCarrierCovers
          (fine.tube source) (coarse.tube parent) := by
      simpa [wz2PaperLiteralFullFiberIndices] using h
    exact
      (cover.literal_parent_unique source parent hcovered).symm
  · intro h
    rw [← h]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ source,
        cover.parent_carrier_covers source⟩

theorem WZ2PaperPartitioningCover.literalFullFiberIndices_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperLiteralFullFiberIndices fine coarse parent =
      cover.fiberIndices parent := by
  ext source
  simp [cover.mem_literalFullFiber_iff_parent,
    WZ1PaperTubeCover.fiberIndices]

theorem WZ2PaperPartitioningCover.literalFullFiber_eq_fullFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperLiteralFullFiberIndices fine coarse parent =
      wz2PaperFullFiberIndices fine coarse parent := by
  ext source
  rw [cover.mem_literalFullFiber_iff_parent,
    cover.mem_fullFiber_iff_parent]

theorem WZ2PaperPartitioningCover.literalFullFiberCount_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperLiteralFullFiberCount fine coarse parent =
      wz2PaperFullFiberCount fine coarse parent := by
  rw [wz2PaperLiteralFullFiberCount, wz2PaperFullFiberCount,
    cover.literalFullFiber_eq_fullFiber parent]

theorem WZ2PaperPartitioningCover.fullFiberIndices_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperFullFiberIndices fine coarse parent =
      cover.fiberIndices parent := by
  ext source
  simp [cover.mem_fullFiber_iff_parent,
    WZ1PaperTubeCover.fiberIndices]

theorem WZ2PaperPartitioningCover.fullFiberCount_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperFullFiberCount fine coarse parent =
      (cover.fiberIndices parent).card := by
  rw [wz2PaperFullFiberCount, cover.fullFiberIndices_eq parent]

theorem WZ2PaperPartitioningCover.fullFiberPointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) (point : Point3) :
    wz2PaperFullFiberPointMultiplicity
        coarse shading parent point =
      cover.fiberPointMultiplicity shading parent point := by
  simp only [wz2PaperFullFiberPointMultiplicity,
    WZ1PaperTubeCover.fiberPointMultiplicity]
  rw [cover.fullFiberIndices_eq parent]

theorem WZ2PaperPartitioningCover.fullFiber_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    (wz2PaperFullFiberIndices fine coarse parent).Nonempty := by
  rcases cover.parent_surjective parent with ⟨source, hsource⟩
  exact
    ⟨source,
      (cover.mem_fullFiber_iff_parent parent source).mpr hsource⟩

@[simp] theorem
    WZ2PaperLiteralDilatedPartitioningCover.mem_literalFullFiber_iff_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse)
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈ wz2PaperLiteralFullFiberIndices fine coarse parent ↔
      cover.parent source = parent := by
  constructor
  · intro h
    have hcovered :
        WZ2PaperTubeCarrierCovers
          (fine.tube source) (coarse.tube parent) := by
      simpa [wz2PaperLiteralFullFiberIndices] using h
    exact
      (cover.literal_parent_unique source parent hcovered).symm
  · intro h
    rw [← h]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ source,
        cover.parent_carrier_covers source⟩

/-- The auxiliary assigned fibers of a carrier-faithful recursive cover are
exactly the paper's strict full fibers. -/
theorem
    WZ2PaperLiteralDilatedPartitioningCover.literalFullFiberIndices_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperLiteralFullFiberIndices fine coarse parent =
      cover.fiberIndices parent := by
  ext source
  simp [cover.mem_literalFullFiber_iff_parent,
    WZ2PaperLiteralDilatedPartitioningCover.fiberIndices,
    WZ2PaperDilatedTubeCover.fiberIndices]

theorem
    WZ2PaperLiteralDilatedPartitioningCover.literalFullFiberCount_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperLiteralFullFiberCount fine coarse parent =
      cover.fiberCount parent := by
  rw [wz2PaperLiteralFullFiberCount,
    cover.literalFullFiberIndices_eq parent]
  rfl

/-- Triangle inequality for the paper coaxial-line distance. -/
theorem wz1PaperLineDistance_triangle
    {δ1 δ2 δ3 : ℝ}
    (t1 : Kakeya.DeltaTube δ1)
    (t2 : Kakeya.DeltaTube δ2)
    (t3 : Kakeya.DeltaTube δ3) :
    wz1PaperLineDistance t1 t3 ≤
      wz1PaperLineDistance t1 t2 + wz1PaperLineDistance t2 t3 := by
  have h1 : dist (wz1TubeAxisZeroPoint t1) (wz1TubeAxisZeroPoint t3) ≤
      dist (wz1TubeAxisZeroPoint t1) (wz1TubeAxisZeroPoint t2) +
      dist (wz1TubeAxisZeroPoint t2) (wz1TubeAxisZeroPoint t3) :=
    dist_triangle _ _ _
  have h2 : InnerProductGeometry.angle
        (wz1PaperDirection t1) (wz1PaperDirection t3) ≤
      InnerProductGeometry.angle
        (wz1PaperDirection t1) (wz1PaperDirection t2) +
      InnerProductGeometry.angle
        (wz1PaperDirection t2) (wz1PaperDirection t3) :=
    InnerProductGeometry.angle_le_angle_add_angle _ _ _
  have h_main : wz1PaperLineDistance t1 t3 ≤
      wz1PaperLineDistance t1 t2 + wz1PaperLineDistance t2 t3 := by
    dsimp only [wz1PaperLineDistance]
    linarith
  exact h_main

/-- Symmetry of the paper coaxial-line distance. -/
theorem wz1PaperLineDistance_symm
    {δ1 δ2 : ℝ}
    (t1 : Kakeya.DeltaTube δ1)
    (t2 : Kakeya.DeltaTube δ2) :
    wz1PaperLineDistance t1 t2 = wz1PaperLineDistance t2 t1 := by
  simp [wz1PaperLineDistance, dist_comm, InnerProductGeometry.angle_comm]

/--
Given partitioning covers at scales `rho` and `sigma` with `2 * rho ≤ sigma`,
all fine tubes in the same `rho`-parent fiber have the same `sigma`-parent.

Proof: if `t1, t2` are in `rho`-parent `p` but have distinct `sigma`-parents
`S1 ≠ S2`, then by the triangle inequality
`d(t1, S2) ≤ d(t1, p) + d(p, t2) + d(t2, S2) ≤ rho/2 + rho/2 + sigma/2 ≤ sigma`,
so `t1` lies in the doubled fibers of both `S1` and `S2`, contradicting
`doubled_fibers_disjoint`.
-/
theorem WZ2PaperPartitioningCover.fiber_parent_stable
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse_rho : Kakeya.Streamlined.TubeFamily rho}
    {coarse_sigma : Kakeya.Streamlined.TubeFamily sigma}
    (cover_rho : WZ2PaperPartitioningCover fine coarse_rho)
    (cover_sigma : WZ2PaperPartitioningCover fine coarse_sigma)
    (hscale : 2 * rho ≤ sigma)
    (p : Fin coarse_rho.card)
    {t1 t2 : Fin fine.card}
    (h1 : cover_rho.parent t1 = p)
    (h2 : cover_rho.parent t2 = p) :
    cover_sigma.parent t1 = cover_sigma.parent t2 := by
  by_contra hne
  set S1 := cover_sigma.parent t1 with hS1
  set S2 := cover_sigma.parent t2 with hS2
  have hS1neS2 : S1 ≠ S2 := hne
  have d1 : wz1PaperLineDistance (fine.tube t1) (coarse_rho.tube p) ≤ rho / 2 := by
    rw [← h1]
    exact cover_rho.parent_covers t1
  have d2 : wz1PaperLineDistance (fine.tube t2) (coarse_rho.tube p) ≤ rho / 2 := by
    rw [← h2]
    exact cover_rho.parent_covers t2
  have d3 : wz1PaperLineDistance (fine.tube t2) (coarse_sigma.tube S2) ≤ sigma / 2 :=
    cover_sigma.parent_covers t2
  have h4 : wz1PaperLineDistance (fine.tube t1) (coarse_sigma.tube S2) ≤
      wz1PaperLineDistance (fine.tube t1) (coarse_rho.tube p) +
      wz1PaperLineDistance (coarse_rho.tube p) (fine.tube t2) +
      wz1PaperLineDistance (fine.tube t2) (coarse_sigma.tube S2) := by
    have h41 := wz1PaperLineDistance_triangle
      (fine.tube t1) (coarse_rho.tube p) (coarse_sigma.tube S2)
    have h42 := wz1PaperLineDistance_triangle
      (coarse_rho.tube p) (fine.tube t2) (coarse_sigma.tube S2)
    linarith
  have h5 : wz1PaperLineDistance (coarse_rho.tube p) (fine.tube t2) =
      wz1PaperLineDistance (fine.tube t2) (coarse_rho.tube p) :=
    wz1PaperLineDistance_symm (coarse_rho.tube p) (fine.tube t2)
  rw [h5] at h4
  have h6 : wz1PaperLineDistance (fine.tube t1) (coarse_sigma.tube S2) ≤ sigma := by
    linarith [hscale, d1, d2, d3]
  have h_in_S2 : t1 ∈ wz2PaperDoubledFiberIndices fine coarse_sigma S2 := by
    simpa [wz2PaperDoubledFiberIndices, Finset.mem_filter, Finset.mem_univ] using h6
  have hsigma_nonneg : 0 ≤ sigma := by
    have h_pos : 0 ≤ wz1PaperLineDistance
        (fine.tube t1) (coarse_sigma.tube (cover_sigma.parent t1)) := by
      dsimp only [wz1PaperLineDistance]
      exact add_nonneg dist_nonneg (InnerProductGeometry.angle_nonneg _ _)
    have h : wz1PaperLineDistance
        (fine.tube t1) (coarse_sigma.tube (cover_sigma.parent t1)) ≤ sigma / 2 :=
      cover_sigma.parent_covers t1
    linarith
  have h71 : wz1PaperLineDistance (fine.tube t1) (coarse_sigma.tube S1) ≤ sigma / 2 := by
    have h : WZ1PaperTubeCovers
        (fine.tube t1) (coarse_sigma.tube (cover_sigma.parent t1)) :=
      cover_sigma.parent_covers t1
    have h_eq : coarse_sigma.tube (cover_sigma.parent t1) =
        coarse_sigma.tube S1 := by
      rw [hS1.symm]
    rw [h_eq] at h
    exact h
  have h7 : wz1PaperLineDistance (fine.tube t1) (coarse_sigma.tube S1) ≤ sigma := by
    linarith [hsigma_nonneg]
  have h_in_S1 : t1 ∈ wz2PaperDoubledFiberIndices fine coarse_sigma S1 := by
    simpa [wz2PaperDoubledFiberIndices, Finset.mem_filter, Finset.mem_univ] using h7
  have h_disjoint := cover_sigma.doubled_fibers_disjoint S1 S2 hS1neS2
  exact Finset.disjoint_left.mp h_disjoint h_in_S1 h_in_S2

end Kakeya.Assouad

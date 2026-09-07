import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers

/-!
# Source-parent geometry along one paper fiber-tree edge

Two parents that share a source child need not satisfy the undilated cover
threshold.  Triangle inequality gives exactly the paper's doubled-parent
relation.
-/

noncomputable section

namespace Kakeya.Assouad

theorem WZ2PaperPartitioningCover.parents_dilated_cover_of_common_source
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (hscale : rho ≤ sigma)
    (source : Fin fine.card)
    (parentRho : Fin coarseRho.card)
    (parentSigma : Fin coarseSigma.card)
    (hparentRho : coverRho.parent source = parentRho)
    (hparentSigma : coverSigma.parent source = parentSigma) :
    WZ2PaperDilatedTubeCovers 2
      (coarseRho.tube parentRho)
      (coarseSigma.tube parentSigma) := by
  have hrho :
      wz1PaperLineDistance
          (fine.tube source) (coarseRho.tube parentRho) ≤
        rho / 2 := by
    rw [← hparentRho]
    exact coverRho.parent_covers source
  have hsigma :
      wz1PaperLineDistance
          (fine.tube source) (coarseSigma.tube parentSigma) ≤
        sigma / 2 := by
    rw [← hparentSigma]
    exact coverSigma.parent_covers source
  have htriangle :=
    wz1PaperLineDistance_triangle
      (coarseRho.tube parentRho)
      (fine.tube source)
      (coarseSigma.tube parentSigma)
  have hsymm :
      wz1PaperLineDistance
          (coarseRho.tube parentRho) (fine.tube source) =
        wz1PaperLineDistance
          (fine.tube source) (coarseRho.tube parentRho) :=
    wz1PaperLineDistance_symm _ _
  rw [hsymm] at htriangle
  unfold WZ2PaperDilatedTubeCovers
  linarith

end Kakeya.Assouad

end

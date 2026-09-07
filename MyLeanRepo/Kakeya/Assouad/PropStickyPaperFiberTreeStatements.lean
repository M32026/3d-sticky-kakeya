import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers

/-!
# One edge of the paper multiscale fiber tree

Paper root:

> “if the intersection contains at least one tube ... then
> `T[T_{tau_i}] subset T[T_{tau_j}]`.”

For two exact-scale partitioning covers with `2 * rho ≤ sigma`, every source
tube in one `rho`-fiber has the same `sigma`-parent.  Thus that entire
`rho`-fiber is contained in one `sigma`-fiber.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperFiberTreeEdgeStatement : Prop :=
  ∀ {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma},
    2 * rho ≤ sigma →
    ∀ (coverRho :
        WZ2PaperPartitioningCover fine coarseRho),
      ∀ (coverSigma :
          WZ2PaperPartitioningCover fine coarseSigma),
        ∀ parentRho : Fin coarseRho.card,
          ∃ parentSigma : Fin coarseSigma.card,
            ∀ source,
              source ∈
                  wz2PaperFullFiberIndices
                    fine coarseRho parentRho →
                source ∈
                  wz2PaperFullFiberIndices
                    fine coarseSigma parentSigma

end Kakeya.Assouad

end

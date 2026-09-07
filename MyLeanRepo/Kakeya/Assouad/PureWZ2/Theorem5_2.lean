import MyLeanRepo.Kakeya.Assouad.PureWZ2.TwistedProjection

/-!
# Pure WZ2 Theorem 5.2 assembly

This is the final WZ2-internal dependency boundary.  The conclusion is the
paper theorem in `PureWZ2Theorem5_2Statement`.  The Section 7
parameter-Frostman projection estimate is already available through a
sorry-free proof route and is a closed proof dependency, not a new node.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Node 8 in the serial heavy-task chain.

The proof may use the already closed theorem
`twisted_projection_parameter_frostman_estimate`, including its sorry-free
spacing/pruning and projected-fiber OS dependencies.  Node 8 itself has only
one open conclusion: the pure paper theorem.
-/
def PureWZ2Theorem5_2AssemblyStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    PureWZ2CriticalExtractionStatement →
      PureWZ2PropStickyStatement →
        PureWZ2GrainsStatement →
          PureWZ2C2GrainsStatement →
            PureWZ2LargeSlopeStatement →
              PureWZ2SmallTwistedProjectionStatement →
                PureWZ2Theorem5_2Statement

end Kakeya.Assouad

end

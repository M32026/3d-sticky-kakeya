import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Frostman transfer to a parent-compatible restricted factoring

Restricting a fine family and its active coarse parents decreases every
fiber-contained mass.  If the original fiber mass is bounded by a fixed
multiple of the restricted fiber mass, the original fiber Frostman estimate
therefore transfers with exactly that multiplicative loss.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/--
Transfer fiberwise Frostman control from a factoring to a compatible
restricted factoring.

The compatibility equation uses the actual selected fine and coarse
embeddings.  It is sufficient for contained-mass monotonicity; no full-preimage
assumption is made.  The only loss is the supplied fiber-mass comparison.
-/
def RestrictedFiberFrostmanTransferStatement : Prop :=
  ∀ {fine coarse : BodyFamily},
    ∀ (P : Factoring fine coarse),
    ∀ (fineSel : Subfamily fine)
      (coarseSel : Subfamily coarse),
    ∀ (Q : Factoring fineSel.family coarseSel.family),
      (∀ i,
        coarseSel.embedding (Q.parent i) =
          P.parent (fineSel.embedding i)) →
    ∀ C L : ENNReal,
      P.FibersAreCFrostman C →
      (∀ j,
        P.fiberMass (coarseSel.embedding j) ≤
          L * Q.fiberMass j) →
      Q.FibersAreCFrostman (L * C)

end Kakeya.Streamlined.RandomTranslation.WithShading

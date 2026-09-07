import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Cardinality floor from the normalized Convex-Wolff inequality

This isolates the finite core of the paper remark:

> “If the elements of `S` are convex, then
> `#S ≥ C⁻¹ (inf_{S ∈ S} |S|)⁻¹`.”

For the cropped paper tubes used here, the geometric input is supplied as a
uniform carrier-volume upper bound `V`.  Applying the normalized
Convex-Wolff inequality to the carrier of one member gives
`1 ≤ C * V * #family`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def WZ2PaperConvexWolffCardinalityCoreStatement : Prop :=
  ∀ {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C V : ENNReal},
    family.Nonempty →
    WZ2PaperConvexWolffBound family C →
    (∀ index, Convex ℝ
      (wz1PaperTubeCarrier (family.tube index))) →
    (∀ index,
      volume (wz1PaperTubeCarrier (family.tube index)) ≤ V) →
      1 ≤ C * V * family.enncard

end Kakeya.Assouad

end

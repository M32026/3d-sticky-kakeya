module

public import Kakeya.DimensionThree.MainLemma1.NodeFamilies
public import Kakeya.DimensionThree.MainLemma1.Setup

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W51RawMiddleBlock

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/- The block's node Frostman clause, exposed without the legacy B3 umbrella. -/
theorem caseTwoRawMid_of_block_upstream_w51 [Nontrivial E] {p : Params} {eps : ℝ}
    (heps : 0 < eps) (Cds : NNReal) (Kds cds : ℕ) :
    ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s' : Finset ι}
        (T : ι → ShadedTube delta E)
        (U : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen delta) Cds)
        (a b m : ℕ),
        StickyKakeya.IsFrostmanDividingBlock U Cds Kds cds p.η p.ε a b m p.N →
        ∀ l ∈ U.cover.indexSet a,
          frostmanConstIn
              (familyIn (U.cover.indexSet b)
                (fun k => (U.cover.tube b k).toConvexSpaceBody)
                (U.cover.tube a l).toConvexSpaceBody)
              (fun k => (U.cover.tube b k).toConvexSpaceBody)
              (U.cover.tube a l).toConvexSpaceBody
            ≤ (delta : ENNReal) ^ (-eps) *
                ((Tube.gridScale delta (Tube.ssfGridLen delta) a /
                  Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : ENNReal)
                  ^ p.η m := by
  have hdelta0event : ∀ᶠ (delta : NNReal) in 𝓝[>] 0, 0 < delta := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact hdelta
  filter_upwards [eventually_dichotomyLoss_le Cds Kds cds heps, hdelta0event]
    with delta hdeltaloss hdelta0
  intro ι _i s' T U a b m hblock l hl
  have haPos : (0 : ℝ) < (Tube.gridScale delta (Tube.ssfGridLen delta) a : ℝ) := by
    exact_mod_cast (Tube.gridScale_pos hdelta0 (Tube.ssfGridLen delta) a)
  have hbPos : (0 : ℝ) < (Tube.gridScale delta (Tube.ssfGridLen delta) b : ℝ) := by
    exact_mod_cast (Tube.gridScale_pos hdelta0 (Tube.ssfGridLen delta) b)
  have hdivR : 0 < ((Tube.gridScale delta (Tube.ssfGridLen delta) a /
      Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : ℝ) := by
    rw [NNReal.coe_div]
    exact div_pos haPos hbPos
  rw [familyIn_indexSet_eq_nodesIn U b ((U.cover.tube a l).toConvexSpaceBody)]
  rw [ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant]
  rw [Kakeya.ennreal_coe_nnreal_rpow hdivR (p.η m), NNReal.coe_div]
  let L : ENNReal := (Cds : ENNReal) * StickyKakeya.totalLoss Cds Kds cds delta
  let X : ENNReal := ConvexSpaceBody.frostmanConstant
      (U.nodesIn b ((U.cover.tube a l).toConvexSpaceBody))
      (fun k => (U.cover.tube b k).toConvexSpaceBody)
      ((U.cover.tube a l).toConvexSpaceBody)
  have hraw : X ≤ L * ENNReal.ofReal
      (((Tube.gridScale delta (Tube.ssfGridLen delta) a : ℝ) /
        (Tube.gridScale delta (Tube.ssfGridLen delta) b : ℝ)) ^ p.η m) := by
    simpa [L, X, Tube.UniformTubeSet.nodesUnder] using hblock.frostman_nodes l hl
  exact hraw.trans (mul_le_mul_left hdeltaloss _)

#print axioms caseTwoRawMid_of_block_upstream_w51

end Kakeya.ml1Boot.W51RawMiddleBlock

end

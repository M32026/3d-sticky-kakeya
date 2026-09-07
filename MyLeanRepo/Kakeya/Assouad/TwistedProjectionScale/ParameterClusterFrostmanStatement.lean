import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterProjectionFiberBound
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters

/-!
# Replication-invariant collapsed parameter regularization

Raw exact-fiber dyadic regularization loses `log #active`, which is not
uniform under replication of indexed tubes.  The Section 7 producer instead
clusters the collapsed `(a,b,d)` parameters at scale `w`, discards the
low-mass tube tail, and regularizes cluster weights relative to their average.
The resulting loss is controlled by a geometric imbalance parameter rather
than the ambient indexed cardinality.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Frostman constant produced by weighted collapsed-parameter clustering. -/
def tubeParameterClusterFrostmanConstant
    (C regularizationLoss lambda : ENNReal) : ENNReal :=
  100000 * C * regularizationLoss * lambda⁻¹

/-- Total shaded mass assigned to one collapsed-parameter center. -/
def tubeParameterAssignedClusterMass
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : Kakeya.Streamlined.TubeShading F)
    (assign : Fin F.card → Point 3)
    (p : Point 3) : ENNReal :=
  ∑ i : Fin F.card,
    if assign i = p then MeasureTheory.volume (Z.carrier i) else 0

/--
The replication-invariant unweighted parameter set and its retained
same-family shading.

`imbalance` compares the largest geometric cluster with the average cluster.
Its explicit bound depends only on `C`, `lambda`, and `w`, so uniform
replication of all indexed tubes leaves the interface unchanged.
-/
structure TubeParameterClusterFrostmanData
    {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (C lambda : ENNReal) (w : ℝ) where
  regularizationLoss : ENNReal
  regularizationLoss_one : 1 ≤ regularizationLoss
  regularizationLoss_ne_top : regularizationLoss ≠ ⊤
  imbalance : ℕ
  imbalance_pos : 0 < imbalance
  imbalance_bound :
    (imbalance : ENNReal) ≤
      1000000 * C * lambda⁻¹ *
          Kakeya.realRpowENN w (-1) + 1
  regularizationLoss_eq :
    regularizationLoss =
      4 * (Nat.log 2 (2 * imbalance) + 1 : ENNReal)
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  whole_tube : IsWholeTubeSubshading shading Y
  mass_retention :
    (2 * regularizationLoss)⁻¹ * Y.mass ≤
      shading.mass
  points : DiscreteSet 3
  points_nonempty : points.Nonempty
  points_in_unitBall : points.IsInUnitBall
  points_separated : points.IsDeltaSeparated w
  points_card_upper :
    points.enncard ≤
      100000 * Kakeya.realRpowENN w (-3)
  frostmanConstant_one :
    1 ≤
      tubeParameterClusterFrostmanConstant
        C regularizationLoss lambda
  frostmanConstant_ne_top :
    tubeParameterClusterFrostmanConstant
      C regularizationLoss lambda ≠ ⊤
  points_frostman :
    points.IsFrostman w 1
      (tubeParameterClusterFrostmanConstant
        C regularizationLoss lambda)
  points_card_lower :
    lambda ≤
      100000 * regularizationLoss *
        (C * Kakeya.realRpowENN w 2) * points.enncard
  assign : Fin F.card → Point 3
  assign_mem :
    ∀ i, shading.carrier i ≠ ∅ → assign i ∈ points
  assign_close :
    ∀ i, shading.carrier i ≠ ∅ →
      dist (tubeParameterPoint3 i) (assign i) ≤ w
  clusterMass : ENNReal
  clusterMass_pos : 0 < clusterMass
  clusterMass_ne_top : clusterMass ≠ ⊤
  cluster_mass_lower :
    ∀ p ∈ points,
      clusterMass ≤
        tubeParameterAssignedClusterMass shading assign p
  cluster_mass_upper :
    ∀ p ∈ points,
      tubeParameterAssignedClusterMass shading assign p ≤
        2 * clusterMass
  point_source :
    ∀ p ∈ points,
      ∃ i : Fin F.card,
        shading.carrier i ≠ ∅ ∧
          assign i = p ∧
          tubeParameterPoint3 i = p

/--
Produce the replication-invariant collapsed parameter package.

The proof should:

1. discard tubes whose shaded mass is below a fixed `lambda` fraction of one
   tube volume only if useful; this is not required by the interface;
2. form a maximal `w`-separated cover of the positive-mass collapsed
   parameters and assign every active tube to a nearby center;
3. weight each center by the total shaded mass of its assigned tubes;
4. use indexed parameter Frostman control to bound the largest cluster mass
   and Euclidean packing to prove the explicit `O(w⁻³)` center bound;
5. discard clusters below half the average mass, then dyadically regularize
   the remaining cluster masses; the number of levels is bounded by
   `Nat.log 2 (2 * imbalance) + 1`;
6. restrict the shading to the selected clusters and prove the displayed
   mass retention, two-sided cluster-mass comparability, Frostman bound,
   cardinality bounds, and source assignment.
-/
def TubeParameterClusterFrostmanStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      F.Nonempty →
      (∀ i : Fin F.card,
        |(tubeParams i).a| ≤ 12 ∧
          |(tubeParams i).b| ≤ 12 ∧
          |(tubeParams i).c| ≤ 2 ∧
          |(tubeParams i).d| ≤ 2) →
      ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
        TubeParameterFrostmanBound F C →
        ∀ w : ℝ, 0 < w → delta ≤ w → 100 * w ≤ 1 →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ c0 : ℝ,
              (∀ i, Y.carrier i ≠ ∅ →
                |(tubeParams i).c - c0| ≤ w / 2) →
              ∀ lambda : ENNReal,
                lambda ≠ 0 → lambda ≠ ⊤ →
                Y.IsLambdaDense lambda →
                  Nonempty
                    (TubeParameterClusterFrostmanData
                      F Y C lambda w)

end Kakeya.Assouad

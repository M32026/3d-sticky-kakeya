import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement

/-!
# A full local parameter block

The Section 7 spacing lemma is not merely a global Katz--Tao extraction.
After uniformizing the collapsed `(a,b,d)` centers across nested cubes, it
selects a scale and one spatial block containing the full expected number of
centers.  Since the weighted cluster masses are comparable, retaining every
tube assigned to that block also retains a quantitative amount of the
original shading.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Tube indices whose assigned collapsed-parameter center lies in a block. -/
def parameterLocalBlockIndices
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta)
    (localPoints : DiscreteSet 3) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    clustered.assign i ∈ localPoints

/-- Reindexed tube family belonging to one local parameter block. -/
def parameterLocalBlockFamily
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta)
    (localPoints : DiscreteSet 3) :
    Kakeya.Streamlined.TubeFamily delta :=
  selectedTubeFamily F
    (parameterLocalBlockIndices clustered localPoints)

/-- Reindexed source shading belonging to one local parameter block. -/
def parameterLocalBlockShading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta)
    (localPoints : DiscreteSet 3) :
    Kakeya.Streamlined.TubeShading
      (parameterLocalBlockFamily clustered localPoints) :=
  selectedTubeShading clustered.shading
    (parameterLocalBlockIndices clustered localPoints)

/-- Recenter one source parameter block at the origin before amplification. -/
def centeredParameterSet
    (points : DiscreteSet 3) (center : Point 3) :
    DiscreteSet 3 :=
  points.image fun p => p - center

/--
The output of the spacing lemma together with its source shading.

`blockScale / 10` is the geometric radius of the selected block.  The factor
ten matches the already proved amplification interface.  The exponent
`1 - 20 * epsilon²` leaves room for uniformization, Katz--Tao extraction, and
logarithmic losses.
-/
structure ParameterLocalFullBlockData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta)
    (epsilon : ℝ) where
  blockScale : ℝ
  blockScale_pos : 0 < blockScale
  fine_le_block : delta ≤ blockScale
  blockScale_small : 100 * blockScale ≤ 1
  separated_scale :
    Real.rpow delta (1 - epsilon ^ 2) <
      blockScale / 10
  localCenter : Point 3
  sourcePoints : DiscreteSet 3
  sourcePoints_nonempty : sourcePoints.Nonempty
  sourcePoints_subset : sourcePoints ⊆ clustered.points
  source_containment :
    ∀ p ∈ sourcePoints,
      dist p localCenter ≤ blockScale / 10
  centeredPoints : DiscreteSet 3
  centeredPoints_eq :
    centeredPoints =
      centeredParameterSet sourcePoints localCenter
  centeredPoints_nonempty : centeredPoints.Nonempty
  centered_containment :
    ∀ p ∈ centeredPoints,
      dist p 0 ≤ blockScale / 10
  windowCenter : ℝ
  local_window :
    ∀ i,
      (parameterLocalBlockShading
        clustered sourcePoints).carrier i ≠ ∅ →
        |(tubeParams
            ((parameterLocalBlockIndices
              clustered sourcePoints).equivFin.symm i).1).c -
          windowCenter| ≤ delta / 2
  local_katzTao :
    centeredPoints.IsKatzTao delta
      (1 - epsilon ^ 2) 100
  local_cardinality :
    Kakeya.realRpowENN
        (blockScale / delta)
        (1 - 20 * epsilon ^ 2) ≤
      100000 * centeredPoints.enncard
  local_mass_lower :
    sourcePoints.enncard * clustered.clusterMass ≤
      (parameterLocalBlockShading clustered sourcePoints).mass

namespace ParameterLocalFullBlockData

/-- The selected local block is an actual subshading of the source shading. -/
lemma local_union_subset
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (data : ParameterLocalFullBlockData clustered epsilon) :
    (parameterLocalBlockShading
      clustered data.sourcePoints).union ⊆ Y.union :=
  fun p hp => by
    have hpClustered :
        p ∈ clustered.shading.union :=
      selectedTubeShading_union_subset
        clustered.shading
        (parameterLocalBlockIndices
          clustered data.sourcePoints) hp
    rcases hpClustered with ⟨i, hi⟩
    exact ⟨i, clustered.subshading i hi⟩

end ParameterLocalFullBlockData

/--
Paper spacing lemma with weighted-shading retention.

The displayed cardinality bound is the exact quantitative consequence needed
from the preceding weighted cluster regularization.  The target performs the
nested-cube uniformization, applies `scale_profile_crossing`, extracts the full
local Katz--Tao pattern, and retains all source tubes assigned to that pattern.

No global upper bound on `tubeParameterClusterFrostmanConstant` is assumed.
After selecting a `delta`-width `c`-window, that normalized constant can lose
one full power of `delta`; the paper's spacing argument does not absorb this
constant globally.  Instead it uses the near-one-dimensional cardinality and
the multiscale branching profile to obtain a good local block.
-/
def ParameterLocalFullBlockSelectionStatement : Prop :=
  ScaleProfileCrossingStatement →
    ∀ epsilon : ℝ,
      0 < epsilon → epsilon < 1 / 10 →
        ∃ etaMax delta₀ : ℝ,
          0 < etaMax ∧ etaMax ≤ epsilon ^ 2 / 1000 ∧
          0 < delta₀ ∧ delta₀ < 1 ∧
          ∀ eta : ℝ, 0 < eta → eta ≤ etaMax →
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  ∀ C lambda : ENNReal,
                    ∀ clustered :
                        TubeParameterClusterFrostmanData
                          F Y C lambda delta,
                      ∀ c0 : ℝ,
                        (∀ i, clustered.shading.carrier i ≠ ∅ →
                          |(tubeParams i).c - c0| ≤ delta / 2) →
                      Kakeya.realRpowENN
                          delta (-1 + eta) ≤
                        100000 * clustered.points.enncard →
                        Nonempty
                          (ParameterLocalFullBlockData
                            clustered epsilon)

end Kakeya.Assouad

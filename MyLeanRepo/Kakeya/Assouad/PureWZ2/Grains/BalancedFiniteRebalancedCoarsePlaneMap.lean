import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BalancedFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RebalancedSourceWitnessCoarsePlaneMap
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers

/-!
# Exact rebalancing after balanced finite planiness

This module is the structural front end of the sampled-coarse route.  It
takes either branch of the balanced high-multiplicity finite-Lipschitz
construction, restores an exact balanced cover by whole-cell rebalancing,
and samples the resulting fine plane map on honest coarse source witnesses.
The full fine shaded-mass account is recorded without hiding any logarithmic
or boundary loss.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

/-- Logarithmic price of the auxiliary global multiplicity band used before
exact whole-cell balancing. -/
def rebalancedFiniteBandLoss (card : ℕ) : ENNReal :=
  ((Nat.log 2 card + 1 : ℕ) : ENNReal)

/-- Total exact-balancing loss after one global multiplicity band, boundary
pruning, and equal-cell balancing. -/
def rebalancedFiniteExactLoss
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {hdelta : 0 < delta}
    (rebalanced : PureWZ2RebalancedFiniteRefinementData
      original candidate hdelta) : ENNReal :=
  rebalancedFiniteBandLoss fine.card * 2 *
    ((4 : ENNReal) *
      ((Nat.log 2
        (∑ coarseCell ∈ rebalanced.pruning.coarseCells,
          (rebalanced.pruning.availableFineCells coarseCell).card) + 1 : ℕ) :
        ENNReal))

/-- A balanced finite weak map after exact fine rebalancing and honest
coarse source-witness sampling. -/
structure BalancedFiniteRebalancedCoarsePlaneMapData
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading)
    (hdelta : 0 < delta) where
  rebalanced : PureWZ2RebalancedFiniteRefinementData
    original finite.refinement.shading hdelta
  sourceWitness : PureWZ2SourceWitnessCoarseShadingData rebalanced.balanced
  sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
    (target := target) sourceWitness
  fine_mass_retention :
    finite.leftFactor * fineShading.mass ≤
      (finite.rightFactor * rebalancedFiniteExactLoss rebalanced) *
        rebalanced.balancing.refined.mass

/-- Restore exact balancing and sample the finite weak plane map at the
coarse scale. -/
theorem balanced_finite_rebalanced_coarse_plane_map
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading)
    (hdelta : 0 < delta)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hboundary : ∀ bandData :
      WZ2PaperGlobalMultiplicityBandData finite.refinement.shading,
      let cap : ENNReal := (2 ^ (bandData.level + 1) : ENNReal)
      2 * (cap * ENNReal.ofReal (1000 * delta / rho)) <
        bandData.band.mass)
    (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ 1 / 5)
    (hbudget :
      finite.incidence + coefficient * (rho * Real.sqrt 3) + rho / 2 ≤
        target) :
    Nonempty (BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite hdelta) := by
  rcases rebalanced_finite_refinement original
      finite.refinement.subshading finite.refinement.cubical hdelta
      hdeltaRho hrho hrhoOne hboundary with ⟨rebalanced⟩
  have hcoefficientNN :
      ((Real.toNNReal coefficient : NNReal) : ℝ) ≤ 1 / 5 := by
    rw [Real.coe_toNNReal _ hcoefficientNonnegative]
    exact hcoefficient
  rcases rebalanced_source_witness_coarse_plane_map_lipschitz_one
      (target := target) original hdelta rebalanced finite.refinement.planeMap
      finite.refinement.lipschitz hrho hcoefficientNN
      (by simpa only [Real.coe_toNNReal _ hcoefficientNonnegative] using
        hbudget) with
    ⟨sourceWitness, ⟨sampled⟩⟩
  let bandLoss : ENNReal := rebalancedFiniteBandLoss fine.card
  let exactLoss : ENNReal :=
    (4 : ENNReal) *
      ((Nat.log 2
        (∑ coarseCell ∈ rebalanced.pruning.coarseCells,
          (rebalanced.pruning.availableFineCells coarseCell).card) + 1 : ℕ) :
        ENNReal)
  have hbandLossPos : 0 < bandLoss := by
    dsimp only [bandLoss, rebalancedFiniteBandLoss]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 fine.card)
  have hbandLossTop : bandLoss ≠ ⊤ := by
    simp [bandLoss, rebalancedFiniteBandLoss]
  have hcandidateBand : finite.refinement.shading.mass ≤
      bandLoss * rebalanced.bandData.band.mass := by
    have hdiv := rebalanced.bandData.band_mass_retention
    change finite.refinement.shading.mass / bandLoss ≤
      rebalanced.bandData.band.mass at hdiv
    rw [ENNReal.div_le_iff hbandLossPos.ne' hbandLossTop] at hdiv
    simpa [mul_comm] using hdiv
  have hbandRefined : rebalanced.bandData.band.mass ≤
      (2 * exactLoss) * rebalanced.balancing.refined.mass := by
    calc
      rebalanced.bandData.band.mass ≤ 2 * rebalanced.pruning.pruned.mass :=
        rebalanced.band_mass_le_two_pruned
      _ ≤ 2 * (exactLoss * rebalanced.balancing.refined.mass) := by
        gcongr
        simpa [exactLoss] using rebalanced.exactRetention.mass_retention
      _ = (2 * exactLoss) * rebalanced.balancing.refined.mass := by ring
  have hcandidateRefined : finite.refinement.shading.mass ≤
      (bandLoss * 2 * exactLoss) * rebalanced.balancing.refined.mass := by
    calc
      finite.refinement.shading.mass ≤
          bandLoss * rebalanced.bandData.band.mass := hcandidateBand
      _ ≤ bandLoss *
          ((2 * exactLoss) * rebalanced.balancing.refined.mass) := by gcongr
      _ = (bandLoss * 2 * exactLoss) *
          rebalanced.balancing.refined.mass := by ring
  have hmass : finite.leftFactor * fineShading.mass ≤
      (finite.rightFactor * rebalancedFiniteExactLoss rebalanced) *
        rebalanced.balancing.refined.mass := by
    calc
      finite.leftFactor * fineShading.mass ≤
          finite.rightFactor * finite.refinement.shading.mass :=
        finite.refinement.mass_retention
      _ ≤ finite.rightFactor *
          ((bandLoss * 2 * exactLoss) *
            rebalanced.balancing.refined.mass) := by gcongr
      _ = (finite.rightFactor * rebalancedFiniteExactLoss rebalanced) *
          rebalanced.balancing.refined.mass := by
        simp only [rebalancedFiniteExactLoss, bandLoss, exactLoss]
        ring
  exact ⟨{
    rebalanced := rebalanced
    sourceWitness := sourceWitness
    sampled := sampled
    fine_mass_retention := hmass
  }⟩

/-- The integer-aligned version of exact rebalancing and coarse source
witness sampling.  Alignment removes the boundary-pruning loss entirely; all
remaining band and exact-balancing losses are identical to the general
producer. -/
theorem aligned_balanced_finite_rebalanced_coarse_plane_map
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading)
    (hfiniteMass : 0 < finite.refinement.shading.mass)
    (hdelta : 0 < delta)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho = (K : ℝ) * delta)
    (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ 1 / 5)
    (hbudget :
      finite.incidence + coefficient * (rho * Real.sqrt 3) + rho / 2 ≤
        target) :
    Nonempty (BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite hdelta) := by
  rcases aligned_rebalanced_finite_refinement original
      finite.refinement.subshading finite.refinement.cubical hfiniteMass
      hdelta hdeltaRho hrho hrhoOne K hK hrhoAligned with
    ⟨rebalanced⟩
  have hcoefficientNN :
      ((Real.toNNReal coefficient : NNReal) : ℝ) ≤ 1 / 5 := by
    rw [Real.coe_toNNReal _ hcoefficientNonnegative]
    exact hcoefficient
  rcases rebalanced_source_witness_coarse_plane_map_lipschitz_one
      (target := target) original hdelta rebalanced finite.refinement.planeMap
      finite.refinement.lipschitz hrho hcoefficientNN
      (by simpa only [Real.coe_toNNReal _ hcoefficientNonnegative] using
        hbudget) with
    ⟨sourceWitness, ⟨sampled⟩⟩
  let bandLoss : ENNReal := rebalancedFiniteBandLoss fine.card
  let exactLoss : ENNReal :=
    (4 : ENNReal) *
      ((Nat.log 2
        (∑ coarseCell ∈ rebalanced.pruning.coarseCells,
          (rebalanced.pruning.availableFineCells coarseCell).card) + 1 : ℕ) :
        ENNReal)
  have hbandLossPos : 0 < bandLoss := by
    dsimp only [bandLoss, rebalancedFiniteBandLoss]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 fine.card)
  have hbandLossTop : bandLoss ≠ ⊤ := by
    simp [bandLoss, rebalancedFiniteBandLoss]
  have hcandidateBand : finite.refinement.shading.mass ≤
      bandLoss * rebalanced.bandData.band.mass := by
    have hdiv := rebalanced.bandData.band_mass_retention
    change finite.refinement.shading.mass / bandLoss ≤
      rebalanced.bandData.band.mass at hdiv
    rw [ENNReal.div_le_iff hbandLossPos.ne' hbandLossTop] at hdiv
    simpa [mul_comm] using hdiv
  have hbandRefined : rebalanced.bandData.band.mass ≤
      (2 * exactLoss) * rebalanced.balancing.refined.mass := by
    calc
      rebalanced.bandData.band.mass ≤ 2 * rebalanced.pruning.pruned.mass :=
        rebalanced.band_mass_le_two_pruned
      _ ≤ 2 * (exactLoss * rebalanced.balancing.refined.mass) := by
        gcongr
        simpa [exactLoss] using rebalanced.exactRetention.mass_retention
      _ = (2 * exactLoss) * rebalanced.balancing.refined.mass := by ring
  have hcandidateRefined : finite.refinement.shading.mass ≤
      (bandLoss * 2 * exactLoss) * rebalanced.balancing.refined.mass := by
    calc
      finite.refinement.shading.mass ≤
          bandLoss * rebalanced.bandData.band.mass := hcandidateBand
      _ ≤ bandLoss *
          ((2 * exactLoss) * rebalanced.balancing.refined.mass) := by gcongr
      _ = (bandLoss * 2 * exactLoss) *
          rebalanced.balancing.refined.mass := by ring
  have hmass : finite.leftFactor * fineShading.mass ≤
      (finite.rightFactor * rebalancedFiniteExactLoss rebalanced) *
        rebalanced.balancing.refined.mass := by
    calc
      finite.leftFactor * fineShading.mass ≤
          finite.rightFactor * finite.refinement.shading.mass :=
        finite.refinement.mass_retention
      _ ≤ finite.rightFactor *
          ((bandLoss * 2 * exactLoss) *
            rebalanced.balancing.refined.mass) := by gcongr
      _ = (finite.rightFactor * rebalancedFiniteExactLoss rebalanced) *
          rebalanced.balancing.refined.mass := by
        simp only [rebalancedFiniteExactLoss, bandLoss, exactLoss]
        ring
  exact ⟨{
    rebalanced := rebalanced
    sourceWitness := sourceWitness
    sampled := sampled
    fine_mass_retention := hmass
  }⟩

/-- Restore exact balancing from a branch-independent incidence budget. -/
theorem bounded_balanced_finite_rebalanced_coarse_plane_map
    {delta rho target coefficient incidenceBudget : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (finite : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) fineShading incidenceBudget)
    (hdelta : 0 < delta)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hboundary : ∀ bandData :
      WZ2PaperGlobalMultiplicityBandData finite.data.refinement.shading,
      let cap : ENNReal := (2 ^ (bandData.level + 1) : ENNReal)
      2 * (cap * ENNReal.ofReal (1000 * delta / rho)) <
        bandData.band.mass)
    (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ 1 / 5)
    (hbudget :
      incidenceBudget + coefficient * (rho * Real.sqrt 3) + rho / 2 ≤
        target) :
    Nonempty (BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite.data hdelta) := by
  apply balanced_finite_rebalanced_coarse_plane_map original finite.data
    hdelta hdeltaRho hrho hrhoOne hboundary hcoefficientNonnegative
    hcoefficient
  calc
    finite.data.incidence + coefficient * (rho * Real.sqrt 3) + rho / 2 ≤
        incidenceBudget + coefficient * (rho * Real.sqrt 3) + rho / 2 := by
      linarith [finite.incidence_le]
    _ ≤ target := hbudget

/-- Integer-aligned exact rebalancing from a branch-independent incidence
budget. -/
theorem aligned_bounded_balanced_finite_rebalanced_coarse_plane_map
    {delta rho target coefficient incidenceBudget : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (finite : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) fineShading incidenceBudget)
    (hfiniteMass : 0 < finite.data.refinement.shading.mass)
    (hdelta : 0 < delta)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho = (K : ℝ) * delta)
    (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ 1 / 5)
    (hbudget :
      incidenceBudget + coefficient * (rho * Real.sqrt 3) + rho / 2 ≤
        target) :
    Nonempty (BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite.data hdelta) := by
  apply aligned_balanced_finite_rebalanced_coarse_plane_map original
    finite.data hfiniteMass hdelta hdeltaRho hrho hrhoOne K hK
    hrhoAligned hcoefficientNonnegative hcoefficient
  calc
    finite.data.incidence + coefficient * (rho * Real.sqrt 3) + rho / 2 ≤
        incidenceBudget + coefficient * (rho * Real.sqrt 3) + rho / 2 := by
      linarith [finite.incidence_le]
    _ ≤ target := hbudget

/-- A uniform full-fiber point-multiplicity cap converts the retained
rebalanced fine mass into sampled coarse mass.  The only additional cost is
the fixed 27-residue loss used to make the sampled map Lipschitz. -/
theorem BalancedFiniteRebalancedCoarsePlaneMapData.fine_to_sampled_mass
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    (data : BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite hdelta)
    (fiberCap : ENNReal)
    (hfiberCap : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          data.rebalanced.balancing.refined parent point : ENNReal) ≤
        fiberCap) :
    finite.leftFactor * fineShading.mass ≤
      ((finite.rightFactor * rebalancedFiniteExactLoss data.rebalanced) *
        (fiberCap * 27)) * data.sampled.selected.mass := by
  have hfineCoarse : data.rebalanced.balancing.refined.mass ≤
      fiberCap * data.sourceWitness.shading.mass :=
    cover.toPaperTubeCover.fine_mass_le_fiberCap_mul_coarse_mass
      data.rebalanced.balancing.refined data.sourceWitness.shading
      (fun source point hpoint =>
        data.sourceWitness.balanced.point_compatibility source
          (cover.toPaperTubeCover.parent source)
          (cover.toPaperTubeCover.parent_covers source) point hpoint)
      hfiberCap
  calc
    finite.leftFactor * fineShading.mass ≤
        (finite.rightFactor *
          rebalancedFiniteExactLoss data.rebalanced) *
            data.rebalanced.balancing.refined.mass :=
      data.fine_mass_retention
    _ ≤ (finite.rightFactor *
          rebalancedFiniteExactLoss data.rebalanced) *
        (fiberCap * data.sourceWitness.shading.mass) := by gcongr
    _ ≤ (finite.rightFactor *
          rebalancedFiniteExactLoss data.rebalanced) *
        (fiberCap * (27 * data.sampled.selected.mass)) := by
      gcongr
      exact data.sampled.mass_retention
    _ = ((finite.rightFactor *
          rebalancedFiniteExactLoss data.rebalanced) *
        (fiberCap * 27)) * data.sampled.selected.mass := by ring

end Kakeya.Assouad.PureWZ2

end

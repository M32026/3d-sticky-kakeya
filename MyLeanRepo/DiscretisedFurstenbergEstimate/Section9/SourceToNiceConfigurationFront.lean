module

/-
  Source-to-NiceConfiguration bridge — canonical, exact contract.

  This is the geometric front-end extraction from continuous source data
  (point set P, tube family T, per-point tube families Tp) to a
  NiceConfiguration at a dyadic scale near δ.

  Exact contract matches bacon's scratch theorem in
  `.scratch/bacon/SourceToNiceConfiguration_hmass2.lean`.

  Outputs:
  - n : dyadic scale with DiscretisedFurstenbergEstimate.dyadicDelta n ≤ δ < 2·DiscretisedFurstenbergEstimate.dyadicDelta n
  - M : common number of tubes per square
  - config : NiceConfiguration at scale n
  - P_ret : retained subset of P (after logarithmic-band trimming)
  - P_oriented : P_ret or swapCoords '' P_ret, depending on orientation
  - T_oriented : T or swapLine '' T, depending on orientation
  - swapped : whether coordinates were swapped (steep case)
  - ρ_mass, ρ_M, ρ_T : loss exponents summing ≤ reserved_budget

  Geometric bounds:
  - Mass: Ncover(config.pointSet) ≥ (DiscretisedFurstenbergEstimate.dyadicDelta n)^ρ_mass · Ncover(P)
  - M lower bound: M ≥ (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-s + lam + ρ_M)
  - Tube: config.T₀.card ≤ (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-ρ_T) · Ncover(T)
  - Occupied cells: ∀ q ∈ config.P₀, (q.toSet ∩ P_oriented).Nonempty
    AND P_oriented ⊆ config.pointSet (both directions, modulo P_ret retention)

  NOT included (must be supplied separately by Step 5):
  - B1BridgeHypotheses (square/tube index bounds from unit-square chart)
  - CombiningExtraHypotheses_v2 (analytic data: t_j bounds, incidence,
    exponent condition — assembled from MultiscaleToCombining)
  - Full exact occupied-cell iff: we have q ∈ P₀ → square meets P_oriented,
    and P_oriented ⊆ pointSet, but not the converse (a square meeting P_oriented
    may be dropped during retention trimming)
  - Exact-scale obligation: this bridge only gives dyadicDelta n ≤ δ < 2*dyadicDelta n.
    This is NOT sufficient for exact occupied-cell transfer. The exact-scale
    δ_d = Δ^m obligation must be handled separately by section9_main.

  Whiteprint node: section9 / source_to_nice_configuration
  Status: PROVED — delegates to ImprovedIncidenceGeneral.Section9.source_to_nice_configuration_impl
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Section9.SourceToNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.Ncover
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open CoordinatePartition
open DyadicCardToNcover (toAffineLine)

/-- Canonical geometric bridge: continuous source → NiceConfiguration with
    orientation data and loss exponents.

    Exact contract matches bacon's scratch theorem.
    Proof delegates to ImprovedIncidenceGeneral.Section9.source_to_nice_configuration. -/
theorem source_to_nice_configuration
    (reserved_budget : ℝ) (hbudget_pos : 0 < reserved_budget)
    (lam : ℝ) (hlam_pos : 0 < lam)
    (ε_tube : ℝ) (hε_tube_pos : 0 < ε_tube) (hε_tube_lt_lam : ε_tube < lam) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∀ (s t : ℝ), 0 < s → s < 1 → s < t →
          ∀ (C_P C_T : ℝ), 0 < C_P → 0 < C_T →
            C_T ≤ δ ^ (-ε_tube) →
              ∀ (P : Set EuclideanPlane), P ⊆ Metric.closedBall 0 1 →
                IsDeltaSSet δ t C_P P →
                  ∀ (T : Set AffineLine), Bornology.IsBounded T →
                    ∀ (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine),
                      (∀ p hp, Tp p hp ⊆ T) →
                      (∀ p hp, IsDeltaSSet δ s C_T (Tp p hp)) →
                      (∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1) →
                      (∀ p hp, ∀ ℓ ∈ Tp p hp, ℓ.offset ∈ Metric.closedBall 0 2) →
                        ∃ (n : ℕ) (M : ℕ)
                          (config : CTNiceConfiguration n s ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-lam)) M)
                          (P_ret P_oriented : Set EuclideanPlane)
                          (T_oriented : Set AffineLine)
                          (swapped : Bool)
                          (ρ_mass ρ_M ρ_T : ℝ),
                          DiscretisedFurstenbergEstimate.dyadicDelta n ≤ δ ∧ δ < 2 * DiscretisedFurstenbergEstimate.dyadicDelta n ∧
                          0 ≤ ρ_mass ∧ 0 ≤ ρ_M ∧ 0 ≤ ρ_T ∧
                          ρ_mass + ρ_M + ρ_T ≤ reserved_budget ∧
                          0 < M ∧
                          (∃ (k : ℕ), M = 2^k) ∧
                          P_ret ⊆ P ∧
                          (swapped = false → P_oriented ⊆ P_ret ∧ T_oriented = T) ∧
                          (swapped = true →
                            P_oriented ⊆ swapCoords '' P_ret ∧ T_oriented = swapLine '' T) ∧
                          Ncover δ T_oriented = Ncover δ T ∧
                          -- Every config square contains a point of P_oriented
                          (∀ q ∈ config.P₀, (q.toSet ∩ P_oriented).Nonempty) ∧
                          P_oriented ⊆ config.pointSet ∧
                          Ncover (DiscretisedFurstenbergEstimate.dyadicDelta n) config.pointSet ≥
                            ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^ ρ_mass) *
                              Ncover (DiscretisedFurstenbergEstimate.dyadicDelta n) P ∧
                          (M : ℝ) ≥ (DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-s + lam + ρ_M) ∧
                          (M : ℝ) ≤ 28 * (DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-s) ∧
                          (config.T₀.card : ENNReal) ≤
                            ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-ρ_T)) * Ncover δ T ∧
                          (∀ T ∈ config.T₀, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) ∧
                          (∀ q (hq : q ∈ config.P₀) T, T ∈ config.tubeFamily q hq → |T.intercept| ≤ 3) ∧
                          Finset.card config.T₀ ≤ 12 * 16 ^ n ∧
                          (∀ (U : DiscretisedFurstenbergEstimate.DyadicTube n), U ∈ config.T₀ →
                            ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
                              dist (DyadicCardToNcover.toAffineLine U) ℓ ≤ 7 * δ) :=
  DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.source_to_nice_configuration_impl
    reserved_budget hbudget_pos lam hlam_pos ε_tube hε_tube_pos hε_tube_lt_lam

end DirecretisedFurstenbergEstimate.Section9

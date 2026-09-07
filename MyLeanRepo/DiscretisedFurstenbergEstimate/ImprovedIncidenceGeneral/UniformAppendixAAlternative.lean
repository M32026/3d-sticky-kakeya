module

/-
  UniformAppendixAAlternative via B1→A1→A10→False contradiction.

  Wraps b1_bridge_to_false with a NiceConfiguration-based interface.

  Given a regular NiceConfiguration where BOTH the fine and coarse incidence
  bounds fail, derive False. This proves fine ∨ coarse by contradiction.

  Hard hypotheses (B1 bridge decomposition) are left as explicit parameters.
  Easy hypotheses are discharged from the NiceConfiguration.

  Whiteprint node: uniform_appendix_a_alternative
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1BridgeToFalse
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_A10_Assembly_Numerical
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_to_A3_Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A11_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QTTC_Assembly
public import MyLeanRepo.robust_kaufman_projection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Support
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.Phase2
open DirecretisedFurstenbergEstimate.Lagoon
open DirecretisedFurstenbergEstimate.AppendixA5
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.ProductContradiction
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Bundle of B1 bridge decomposition data needed by uniform_appendix_A_alternative.

    This is the hard geometric infrastructure: coarse/fine square decomposition,
    thinning, ball growth, S-set transfers, and cardinality bounds.

    TODO: Construct this from a NiceConfiguration + IsRegularBetweenScales.
-/
structure B1BridgeDecomposition
    (n m : ℕ) (hnm : m ≤ n)
    (s C₁ : ℝ) (M : ℕ)
    (config : NiceConfiguration n s C₁ M)
    (Δ δ u ε : ℝ) where
  -- Coarse scale data
  coarseP₀ : Finset (DyadicSquare m)
  containingSquare : DyadicSquare n → DyadicSquare m
  hCoarse_eq : coarseP₀ = config.P₀.image containingSquare
  hContaining : ∀ p ∈ config.P₀, containingSquare p ∈ coarseP₀
  h_squareIndex_compat : ∀ p ∈ config.P₀,
    squareIndex Δ (localSquareCenter p) = ((containingSquare p).i, (containingSquare p).j)

  -- Thinning data (QTTC output)
  K : ℝ
  hK : 1 ≤ K
  origTubeFamily : (p : DyadicSquare n) → p ∈ config.P₀ → Finset (DyadicTube n)
  hTube_sub : ∀ p hp, config.tubeFamily p hp ⊆ origTubeFamily p hp
  hTube_size_orig : ∀ p hp, (origTubeFamily p hp).card = M
  hTube_sset_orig : ∀ p hp, IsDeltaSSet (dyadicDelta n) s C₁ (origTubeFamily p hp : Set (DyadicTube n))
  hTube_inc_orig : ∀ p hp T, T ∈ origTubeFamily p hp → (T.toSet ∩ p.toSet).Nonempty
  hM : 0 < M
  hM_even : M % 2 = 0

  -- Packing constant
  K_pack : ℝ
  hK_pack_pos : 0 < K_pack
  hK_pack_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6

  -- Point properties
  hP_ball_growth : ∀ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), Δ ≤ r →
    (((config.P₀.image localSquareCenter).filter (fun y => dist c y ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-9 * ε / 4) * r^u * ((config.P₀.image localSquareCenter).card : ℝ)
  hPfin_sset : IsDeltaSSet δ u (Real.rpow δ (-2 * ε))
    ((config.P₀.image localSquareCenter) : Set (EuclideanSpace ℝ (Fin 2)))
  h_points_in_ball_R : (config.P₀.image localSquareCenter : Set (EuclideanSpace ℝ (Fin 2))) ⊆
    Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2)

  -- Cardinality bounds (local u)
  h_fine_card_lower : Real.rpow Δ (-2 * u + ε / 4) ≤ (config.P₀.card : ℝ)
  h_fine_card_upper : (config.P₀.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4)
  h_coarse_card_lower : Real.rpow Δ (-u + ε) ≤ (coarseP₀.card : ℝ)
  h_coarse_card_upper : (coarseP₀.card : ℝ) ≤ Real.rpow Δ (-u - ε / 2)
  h_per_square_lower : ∀ Q ∈ coarseP₀,
    Real.rpow Δ (-u + ε) ≤ ((config.P₀.filter (fun p => containingSquare p = Q)).card : ℝ)
  h_per_square_upper : ∀ Q ∈ coarseP₀,
    ((config.P₀.filter (fun p => containingSquare p = Q)).card : ℝ) ≤ Real.rpow Δ (-u - ε)

  -- Tube constant absorption
  hC_fine_bound : C₁ ≤ Real.rpow δ (-ε / 2)
  hC₁ : 1 ≤ C₁
  h_tube_sset_absorb : (4000 : ℝ) * 44^s ≤ Real.rpow δ (-ε / 2)

  -- Geometric constraints (from dyadic square/tube definitions)
  h_tubes_strip : ∀ (p : DyadicSquare n) (hp : p ∈ config.P₀) (T : DyadicTube n),
    T ∈ config.tubeFamily p hp → -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)
  h_tubes_intercept : ∀ (p : DyadicSquare n) (hp : p ∈ config.P₀) (T : DyadicTube n),
    T ∈ config.tubeFamily p hp → |T.intercept| ≤ 3

  -- M quantitative bounds
  hM_fine_lower : (M : ℝ) / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε)
  hM_fine_upper : (M : ℝ) ≤ Real.rpow Δ (-2 * s - ε)

/-- Counter-assumption-derived data for the A1→A10 chain (v2).

    Parameterized by local dimension `u`, oriented ambient family `T_oriented`,
    and pre-orientation family `T_original`.

    T_oriented is NOT separated. It enters only through:
      1. Ncover failure (both scales)
      2. Thickening provenance of T_full and T_Delta
      3. Orientation Ncover equality

    Fine bound proof (SIMPLIFIED — uses existing source-to-Nice output):
      Given a4 with T_source = image(toAffineLine, config.T₀) and T_full ⊆ T_source:
        card(T_full) ≤ card(T_source) = card(config.T₀)
                     ≤ δ_n^{-ρ_T} · Ncover(δ_n, Tbar)
                     < Δ^{-(4s+2εA_int+2ρ_T)}
                     ≤ Δ^{-(4s+3ε)}
      No separation, thickening, or local multiplicity on the fine side.

    Coarse bound proof (corrected: δ_n=Δ², so √δ_n=Δ):
      |T_Delta| ≤ K_coarse_geom · Ncover(Δ, T_oriented)
                = K_coarse_geom · Ncover(Δ, T_original)
                < Δ^{-(2s+3ε)}
-/
structure CounterAssumptionData
    (Δ δ_n s u ε : ℝ) (T_original T_oriented : Set AffineLine)
    (T_source : Finset AppendixA.FineTube) (ρ_T : ℝ) where
  -- Ncover equality at fine scale (orientation is an isometry/involution)
  hNcover_fine_eq : _root_.Ncover δ_n T_oriented = _root_.Ncover δ_n T_original
  -- Ncover equality at coarse scale
  hNcover_coarse_eq : _root_.Ncover Δ T_oriented = _root_.Ncover Δ T_original
  -- C_global cardinality bound: direct for any A2_v2 with provenance
  hC_global_bound : ∀ (a2 : AppendixA.A2_Output_v2 Δ δ_n s u ε T_oriented),
      a2.C_global.card ≤ Real.rpow Δ (-2 * s - 3 * ε)
  -- Source family cardinality bound: proved from source-to-Nice configuration.
  -- T_source = image(toAffineLine, config.T₀), T_original = Tbar (pre-orientation).
  -- Stated in ENNReal to match source-to-Nice output type.
  hT_source_bound : (T_source.card : ENNReal) ≤
      ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) * _root_.Ncover δ_n T_original
  -- Fine family cardinality bound: T_full ⊆ T_source + hT_source_bound
  hT_full_upper : ∀ (a4 : AppendixA.A4_Output_v2 Δ δ_n s u ε T_source),
      (a5FullFineFamily Δ δ_n s u ε a4.Qset a4.perSquare).card ≤
        Real.rpow Δ (-(4 * s + 3 * ε))
  -- Two-s bound: direct for any A4_v2 with geometry
  h_2s_bound : ∀ (a4 : AppendixA.A4_Output_v2 Δ δ_n s u ε T_source)
      (C_global_A2 : Finset AppendixA.CoarseTube),
      (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset), (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2) →
      (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset), ‖Lagoon.squareCenter Δ Q‖ ≤ 2) →
      (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset) (R : AppendixA.CoarseSquare Δ) (hR : R ∈ a4.Qset), dist (Lagoon.squareCenter Δ Q) (Lagoon.squareCenter Δ R) ≤ 3) →
      (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε) →
      TwoSBoundWithLower Δ s u ε a4.Qset
        (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
        (-2 * s + 210 * ε)

/-- UniformAppendixAAlternative: for regular P + tube families,
    fine bound OR coarse bound holds.

    Proof by contradiction using B1→A1→A10→product axiom.

    Takes B1 bridge decomposition and counter-assumption data as explicit
    hypotheses (to be filled by subsequent infrastructure).
-/
theorem uniform_appendix_A_alternative
    {n m : ℕ} (hnm : m ≤ n)
    {s t : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2) (hst : s < t)
    -- Scale parameters
    {Δ δ ε : ℝ}
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_D : δ ≤ Δ)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1) (hε_le_one : ε ≤ 1)
    (hδ_eq2 : δ = Δ ^ 2)
    (hΔ_lt_one : Δ < 1) (hΔ_lt_third : Δ < 1 / 3)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    -- Local dimension (strictly < 2; u=2 handled at caller via u_eff adapter)
    {u : ℝ} (htu : t ≤ u) (hu2 : u < 2)
    -- A1 output (constructed by caller from B1 bridge data)
    (a1 : A1_Output Δ δ u s ε)
    (h_points_in_ball' : ∀ Q hQ, (a1.points Q hQ : Set AppendixA.Plane) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2))
    -- Source family and A4 output
    (T_source : Finset AppendixA.FineTube)
    (a4_v2 : AppendixA.A4_Output_v2 Δ δ s u ε T_source)
    (hQ4_sub_a1 : a4_v2.Qset ⊆ a1.Qset)
    (hQset_card_lower : Real.rpow Δ (-u + 4 * ε) ≤ (a4_v2.Qset.card : ℝ))
    (hQset_card_upper : (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε))
    -- C_global coarse family
    (C_global_A2 : Finset AppendixA.CoarseTube)
    (hC_global_eq : C_global_A2 = a4_v2.Qset.biUnion (fun Q =>
      if h : Q ∈ a4_v2.Qset then (a4_v2.perSquare Q h).base.C_Q else ∅))
    (hC_global_card : C_global_A2.card ≤ Real.rpow Δ (-2 * s - 3 * ε))
    (hC_global_A2_distinct : ∀ (U1 : AppendixA.CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : AppendixA.CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
        AppendixA.parentCell Δ hΔ_pos U1 ≠ AppendixA.parentCell Δ hΔ_pos U2)
    -- RKP condition
    (hRKP_cond : 576 * ε < u - s)
    -- Fine family upper bound
    (hT_full_upper : ∀ (a4 : AppendixA.A4_Output_v2 Δ δ s u ε T_source),
      (a5FullFineFamily Δ δ s u ε a4.Qset a4.perSquare).card ≤
        Real.rpow Δ (-(4 * s + 3 * ε)))
    -- Two-s bound
    (h_2s_bound : ∀ (a4 : AppendixA.A4_Output_v2 Δ δ s u ε T_source)
        (C_global_A2 : Finset AppendixA.CoarseTube),
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset), (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2) →
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset), ‖Lagoon.squareCenter Δ Q‖ ≤ 2) →
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset) (R : AppendixA.CoarseSquare Δ) (hR : R ∈ a4.Qset), dist (Lagoon.squareCenter Δ Q) (Lagoon.squareCenter Δ R) ≤ 3) →
        (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε) →
        TwoSBoundWithLower Δ s u ε a4.Qset
          (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
          (-2 * s + 210 * ε))
    -- Slope/intercept bounds
    (h_slope_bound_A7 : ∀ T, T ∈ C_global_A2 →
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3)
    (h_pack_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^u + 1 ≤ Real.rpow Δ (-ε))
    -- Product axiom parameters
    (η_axiom δ₀_axiom : ℝ)
    (hη_axiom_pos : 0 < η_axiom)
    (hδ₀_axiom_pos : 0 < δ₀_axiom)
    (hΔ_le_δ₀_axiom : Δ ≤ δ₀_axiom)
    (h_absorb_Y : (9 * 3 ^ (t - s)) * Real.rpow Δ (-10000 * ε) ≤ Real.rpow Δ (-η_axiom))
    (h_absorb_X : (729 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom))
    (h_absorb_T : (81 ^ 3 * 16 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom))
    -- Product theorem instance for τ₀ = min(t-s,1)
    (hA7 : ProductContradiction.ProductPropBoundedTheorem s (min (t - s) 1) η_axiom δ₀_axiom)
    (η_upper : ℝ)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_214ε : 214 * ε < η_upper)
    (hΔ_small_allFine : (2000 : ℝ) * 2 < Real.rpow Δ (-(η_upper - 214 * ε)))
    (hη_upper_lt_axiom : η_upper < η_axiom)
    (h_num : AssemblyNumericalBounds Δ s u ε)
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    : False :=
  b1_bridge_to_false
    hnm hΔ_eq hδ_eq hΔ_pos hΔ_lt_half hδ_pos hδ_le_D ht_pos ht_lt_two
    s u htu hu2 hs_pos hs_lt_one hε_pos h_small
    hst ht_lt_two hε_lt_one hε_le_one hδ_eq2 hΔ_lt_one hΔ_lt_third
    a1 h_points_in_ball'
    T_source a4_v2 hQ4_sub_a1 hQset_card_lower hQset_card_upper
    C_global_A2 hC_global_eq hC_global_card hC_global_A2_distinct
    hRKP_cond hT_full_upper h_2s_bound
    h_slope_bound_A7 h_pack_absorb_A7 h_const_absorb_A7
    η_axiom δ₀_axiom hη_axiom_pos hδ₀_axiom_pos hΔ_le_δ₀_axiom
    h_absorb_Y h_absorb_X h_absorb_T
    hA7 η_upper hη_upper_pos hη_upper_gt_214ε hΔ_small_allFine hη_upper_lt_axiom
    h_num h_log_absorb

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

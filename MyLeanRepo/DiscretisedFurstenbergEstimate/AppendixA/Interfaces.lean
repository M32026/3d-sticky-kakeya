module

/-
  Canonical Appendix A interfaces: A1_Output through A10_Output.

  This module is the SOLE definition site for all Appendix A output structures.
  Every stage consumes the literal output type of the preceding stage.

  Key corrections per UPDATED_SOURCE_PAPER_ROUTE_CORRECTION.md:
  - A2: per-square QTTC with H2 incidence lower bound, C_Q as (Δ,s,C₂)-set
  - A4: RKP tied to C_Q directions (C_Q^pi), projected X_Q
  - A5: global C_global, uniform N, G1-G4 quantitative bounds
  - A6: QUANTITATIVE I ≳ Δ^{-(s+t)+O(ε)}, E ≲ Δ^{-2t+O(ε)}, L ≲ Δ^{-2s+O(ε)}
  - A7: T0, Q0 with |Q0| ≳ Δ^{s-t+O(ε)}, Q0 is (Δ,t-s,Δ^{-O(ε)})-set
  - A8: |P'_Q| ≈ Δ^{-t}, |T(p)∩T0| ≈ Δ^{-s} (H2 fiber data)
  - A9: affine shear F(x,y)=(x-σ₀y-h₀,y), actual dyadic Δ-square/δ-tube data
  - A10: Δ⁻¹ dual dilation, Y from y_Q with bounded-fiber injectivity, X_y=Δ⁻¹Π_Q

  Whiteprint node: appendix_a_alternative / interfaces
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)
open CoordinatePartition (swapLine)

abbrev Plane := EuclideanPlane
abbrev CoarseSquare (Δ : ℝ) := ℤ × ℤ
abbrev CoarseTube := AffineLine
abbrev FineTube := AffineLine

/-! ========================================================================
   Shared helper definitions
   ======================================================================== -/

/-- A set P is a "rescalable" (δ,Δ,s,C)-set if covering at scale δ of
    P ∩ B(x, Δ*r) is bounded by C * r^s * covering_δ(P). -/
def IsRescalableDeltaSet {X : Type*} [PseudoMetricSpace X]
    (δ Δ s C : ℝ) (P : Set X) : Prop :=
  P.Nonempty ∧ 0 < δ ∧ 0 < Δ ∧ 0 < C ∧ 0 ≤ s ∧
    ∀ x : X, ∀ r : ℝ, Δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal
          (P ∩ Metric.closedBall x (Δ * r)) : ℝ≥0∞) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞)

/-- A fine tube is assigned to a coarse tube if their AffineLine distance
    is at most Δ. -/
def InCoarseTube (Δ : ℝ) (T_fine T_coarse : FineTube) : Prop :=
  dist T_fine T_coarse ≤ Δ

/-- Slope parameter of an affine line (a in x = a*y + b). -/
def tubeSlope (T : AffineLine) : ℝ :=
  (LemmaE.affineLineParams T).1

/-- Intercept parameter of an affine line (b in x = a*y + b). -/
def tubeIntercept (T : AffineLine) : ℝ :=
  (LemmaE.affineLineParams T).2

/-- Coarse square region in the plane. -/
def squareSet (Δ : ℝ) (Q : CoarseSquare Δ) : Set Plane :=
  {p | p 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) ∧
       p 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1))}

/-- x-coordinate of coarse square's lower-left corner. -/
def squareX (Δ : ℝ) (Q : CoarseSquare Δ) : ℝ := Δ * (Q.1 : ℝ)

/-- y-coordinate of coarse square's lower-left corner. -/
def squareY (Δ : ℝ) (Q : CoarseSquare Δ) : ℝ := Δ * (Q.2 : ℝ)

/-- Dyadic tube parameter cell at scale r:
    [a*r, (a+1)*r) × [b*r, (b+1)*r) in (slope, intercept) space. -/
abbrev DyadicTubeCell (r : ℝ) := ℤ × ℤ

/-- The dyadic δ-cell containing a parameter pair (a,b). -/
def dyadicCellOfParams (δ : ℝ) (hδ_pos : 0 < δ) (params : ℝ × ℝ) :
    DyadicTubeCell δ :=
  (⌊params.1 / δ⌋, ⌊params.2 / δ⌋)

/-- Metric assigned count: number of fine tubes in T(p) within distance Δ of c.
    Geometric packing use only. For combinatorial counting with disjoint fibers,
    use `assignedCountDyadic`. -/
def assignedCountMetric (Δ : ℝ) (T : Plane → Finset FineTube)
    (p : Plane) (c : CoarseTube) : ℕ :=
  (T p).filter (fun T_fine => InCoarseTube Δ T_fine c) |>.card

/-- Deprecated alias for `assignedCountMetric`. -/
abbrev assignedCount (Δ : ℝ) (T : Plane → Finset FineTube)
    (p : Plane) (c : CoarseTube) : ℕ :=
  assignedCountMetric Δ T p c

/-- The dyadic Δ-parent cell of a tube, using floor (integer division).
    This matches `dyadicCellOfParams` and `coarseTubeToM`/`sourceParent`:
    for exact grid parameters, floor gives the coarse parent index. -/
def parentCell (Δ : ℝ) (hΔ_pos : 0 < Δ) (T : FineTube) : DyadicTubeCell Δ :=
  (⌊tubeSlope T / Δ⌋, ⌊tubeIntercept T / Δ⌋)

/-- Exact parent relation: fine tube T and coarse tube U share the same Δ-cell.
    Gives DISJOINT fibers, unlike metric `InCoarseTube`. -/
def InParent (Δ : ℝ) (hΔ_pos : 0 < Δ) (T_fine : FineTube) (U_coarse : CoarseTube) : Prop :=
  parentCell Δ hΔ_pos T_fine = parentCell Δ hΔ_pos U_coarse

/-- Assigned count via exact dyadic parent relation (disjoint fibers). -/
def assignedCountDyadic (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T : Plane → Finset FineTube) (p : Plane) (U : CoarseTube) : ℕ :=
  (T p).filter (fun T_fine => InParent Δ hΔ_pos T_fine U) |>.card

/-- Per-point incidence fiber: fine tubes at point p that share parent cell with U.
    This is the H2 incidence counting object. Distinct from globalFiber.

    Typed canonical version: `TypedDyadicInfrastructure.pointFiber` using `sourceParent`.
    This AffineLine version uses `InParent` (parameter cell equality) and is needed
    at the A2 boundary where fine tubes are AffineLines. -/
def pointFiber (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T_Q : Plane → Finset FineTube) (p : Plane) (U : CoarseTube) : Finset FineTube :=
  (T_Q p).filter (fun T => InParent Δ hΔ_pos T U)

/-- Distinct global fiber: all fine tubes in the global union that share parent
    cell with U. This is the disjoint-partition object for A5/formA42.
    Σ_U |globalFiber U| = |T_global|.

    Typed canonical version: `TypedDyadicInfrastructure.globalFiber` using `sourceParent`.
    This AffineLine version uses `InParent` for structure-level compatibility. -/
def globalFiber (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T_global : Finset FineTube) (U : CoarseTube) : Finset FineTube :=
  T_global.filter (fun T => InParent Δ hΔ_pos T U)

/-- Coarse membership count: number of squares Q for which U ∈ C_Q(Q).

    Typed version: `popularParents` / per-square coarseFamily in
    `TypedDyadicInfrastructure`. -/
def coarseMembership (Δ : ℝ) (Qset : Finset (CoarseSquare Δ))
    (C_Q_family : CoarseSquare Δ → Finset CoarseTube) (U : CoarseTube) : ℕ :=
  (Qset.filter (fun Q => U ∈ C_Q_family Q)).card

/-- The parameter set corresponding to a dyadic tube cell. -/
def tubeCellSet (r : ℝ) (cell : DyadicTubeCell r) : Set (ℝ × ℝ) :=
  Set.Ico (r * (cell.1 : ℝ)) (r * ((cell.1 : ℝ) + 1)) ×ˢ
  Set.Ico (r * (cell.2 : ℝ)) (r * ((cell.2 : ℝ) + 1))

/-- A representative parameter point in the dyadic cell (lower-left corner). -/
def paramsOfDyadicCell (δ : ℝ) (cell : DyadicTubeCell δ) : ℝ × ℝ :=
  (δ * (cell.1 : ℝ), δ * (cell.2 : ℝ))

/-- Affine projection onto direction perpendicular to slope σ:
    p ↦ p 0 - σ * p 1 (signed distance from line through origin). -/
def affineProj (σ : ℝ) (p : Plane) : ℝ := p 0 - σ * p 1

/-! ========================================================================
   A1: Heavy-square refinement  (OS Section A.1)
   ======================================================================== -/

structure A1_Output (Δ δ t s ε : ℝ) where
  Qset : Finset (CoarseSquare Δ)
  points : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset Plane
  tubes : Plane → Finset FineTube
  M : ℝ
  K_pack : ℝ
  hK_pack_pos : 0 < K_pack
  hQset_sset : IsDeltaSSet Δ t (Real.rpow Δ (-15 * ε)) (Qset : Set (CoarseSquare Δ))
  -- Physical ball-growth for square centers: |{Q ∈ Qset | center Q ∈ B(c,r)}| ≤ Δ^{-11ε} · r^t · |Qset|
  -- (Relaxed from Δ^{-9ε} to accommodate relaxed ball-growth constant Δ^{-9ε/4})
  hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
    ((Qset.filter (fun Q => dist (DirecretisedFurstenbergEstimate.Lagoon.squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-11 * ε) * r^t * (Qset.card : ℝ)
  hQset_card_lower : Real.rpow Δ (-t + 3 * ε) ≤ (Qset.card : ℝ)
  hQset_card_upper : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε)
  h_points_in_square : ∀ Q hQ p, p ∈ points Q hQ → p ∈ squareSet Δ Q
  h_points_in_ball : ∀ Q hQ, (points Q hQ : Set Plane) ⊆ Metric.closedBall 0 (Real.sqrt 2)
  h_points_y_bound : ∀ Q hQ p, p ∈ points Q hQ → |p 1| ≤ Real.sqrt 2
  h_points_card_lower : ∀ Q hQ, Real.rpow Δ (-t + 3 * ε) ≤ (points Q hQ).card
  h_points_card_lower_strong : ∀ Q hQ, Real.rpow Δ (-t + 3 * ε) ≤ (points Q hQ).card
  h_points_card_upper : ∀ Q hQ, (points Q hQ).card ≤ Real.rpow Δ (-t - 3 * ε)
  hM_pos : 0 < M
  hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack
  hM_upper : M ≤ 2 * Real.rpow Δ (-2 * s - ε)
  h_tubes_card : ∀ Q hQ p, p ∈ points Q hQ →
    (M / 2 : ℝ) ≤ (tubes p).card ∧ (tubes p).card ≤ M
  h_slope_bound : ∀ Q hQ p, p ∈ points Q hQ → ∀ T ∈ tubes p,
    (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3
  h_tubes_sset : ∀ Q hQ p, p ∈ points Q hQ →
    IsDeltaSSet δ s (max 1 (K_pack * Real.rpow δ (-ε))) (tubes p : Set FineTube)
  h_separated : ∀ Q hQ, SeparatedAt δ (points Q hQ : Set Plane)
  P_all : Finset Plane
  hP_all_card_upper : (P_all.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4)
  hP_all_sset : IsDeltaSSet δ t (Real.rpow δ (-2 * ε)) (P_all : Set Plane)
  h_points_sub_all : ∀ Q hQ, (points Q hQ : Set Plane) ⊆ (P_all : Set Plane)
  h_tubes_separated : ∀ Q hQ p, p ∈ points Q hQ →
    SeparatedAt (δ / 2) (tubes p : Set FineTube)
  h_inc : ∀ Q hQ p, p ∈ points Q hQ → ∀ T ∈ tubes p,
    p ∈ Metric.cthickening (2 * δ) T.1

/-! ========================================================================
   A2: Per-square QTTC + H2  (OS (A.6)-(A.14))
   ======================================================================== -/

structure A2_SquareData (Δ δ s t ε : ℝ) (Q : CoarseSquare Δ) where
  hΔ_pos : 0 < Δ
  P_Q : Finset Plane
  T_Q : Plane → Finset FineTube
  C_Q : Finset CoarseTube
  K_Q : ℝ
  C2_Q : ℝ
  H_Q : ℝ
  origPointsCard : ℝ
  M : ℝ
  hM_upper : M ≤ 2 * Real.rpow Δ (-2 * s - ε)
  -- QTTC refinement bounds
  hP_Q_refine : origPointsCard ≤ K_Q * (P_Q.card : ℝ)
  hT_Q_refine : ∀ p ∈ P_Q, (M : ℝ) ≤ K_Q * (T_Q p).card
  -- C_Q is a (Δ, s, C2_Q)-set
  hC_Q_sset : IsDeltaSSet Δ s C2_Q (C_Q : Set CoarseTube)
  -- H2 incidence lower bound: Σ_p |pointFiber(p, boldT)| ≥ H_Q
  -- This is the PER-POINT INCIDENCE sum, NOT the distinct global fiber count.
  hH2 : ∀ boldT ∈ C_Q,
    H_Q ≤ ∑ p ∈ P_Q, (pointFiber Δ hΔ_pos T_Q p boldT).card
  -- Two-sided balance
  h_balance_lower : (M : ℝ) * origPointsCard ≤ K_Q * H_Q * (C_Q.card : ℝ)
  h_balance_upper : H_Q * (C_Q.card : ℝ) ≤
    K_Q ^ 3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ)
  -- Loss bounds
  hK_Q_pos : 0 < K_Q
  hK_Q_loss : K_Q ≤ Real.rpow Δ (-ε)
  hC2_Q_loss : C2_Q ≤ Real.rpow Δ (-10 * ε)
  hH_Q_pos : 0 < H_Q
  hH_Q_ge_one : H_Q ≥ 1
  hH_Q_upper : H_Q ≤ Real.rpow Δ (-t - s - 10 * ε)
  -- K_Q lower bound (polylog ≥ 1)
  hK_Q_lower : Real.rpow Δ (2 * ε) ≤ K_Q
  -- C_Q cardinality bounds
  hC_card_lower : Real.rpow Δ (-s + 11 * ε) ≤ (C_Q.card : ℝ)
  -- Geometric properties
  hP_Q_card_upper : (P_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε)
  hP_Q_in_square : (P_Q : Set Plane) ⊆ squareSet Δ Q
  hP_Q_in_ball : (P_Q : Set Plane) ⊆ Metric.closedBall 0 (Real.sqrt 2)
  h_slope_bound : ∀ p ∈ P_Q, ∀ T ∈ T_Q p,
    (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3
  h_inc : ∀ p ∈ P_Q, ∀ T ∈ T_Q p, p ∈ Metric.cthickening (2 * δ) T.1
  hT_Q_separated : ∀ p ∈ P_Q, SeparatedAt (δ / 2) (T_Q p : Set FineTube)
  hT_Q_per_coarse_upper : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
    assignedCountMetric Δ T_Q p boldT ≤ Real.rpow Δ (-s - 6 * ε)
  -- PointFiber upper bound: |pointFiber(p,U)| ≤ Δ^{-s-7ε}
  -- Derived from S-set + parent cell adapter (InParent → dist < 10Δ);
  -- geometric constant 10^s absorbed into one extra ε (h10_loss).
  h_pointFiber_upper : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
    (pointFiber Δ hΔ_pos T_Q p boldT).card ≤ Real.rpow Δ (-s - 7 * ε)
  -- Weak bounds for A3 binning (strip packing + A1 data)
  K_pack : ℝ
  hKpack_pos : 0 < K_pack
  hKpack_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6
  hKpack_le_ε : K_pack ≤ Real.rpow Δ (-ε)
  -- T_Q inherits δ-scale S-set from original tube family (via subset + packing)
  hT_Q_sset : ∀ p ∈ P_Q,
    IsDeltaSSet δ s
      (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * (DirecretisedFurstenbergEstimate.MainAppendix.affineLine_packing_constant : ℝ))
      (T_Q p : Set FineTube)
  -- Cardinality upper bound inherited from original tube family
  hT_Q_card_upper : ∀ p ∈ P_Q, (T_Q p).card ≤ M
  -- P_Q separation and S-set (needed by A4)
  hP_Q_card_lower : (P_Q.card : ℝ) ≥ Real.rpow Δ (-t + 5 * ε)
  hP_Q_separated : SeparatedAt δ (P_Q : Set Plane)
  hP_Q_sset : IsDeltaSSet δ t (Real.rpow Δ (-t - 10 * ε)) (P_Q : Set Plane)
  -- C_Q separation and slope properties (needed by A4)
  hC_Q_separated : SeparatedAt Δ (C_Q : Set CoarseTube)
  hC_Q_v : ∀ boldT ∈ C_Q, (LemmaE.getDirV boldT) 1 ≠ 0
  hC_Q_slope_bound : ∀ boldT ∈ C_Q, |tubeSlope boldT| ≤ 1
  hC_Q_b : ∀ boldT ∈ C_Q, |tubeIntercept boldT| ≤ 3
  hC_Q_slope_sset : IsDeltaSSet Δ s (Real.rpow Δ (-25 * ε)) (tubeSlope '' (C_Q : Set CoarseTube))
  hC_Q_slope_cover_lower : ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) ≤
    Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube))
  hC_Q_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) : ENNReal) ≤
    ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube))
  -- Global dyadic coarse cover (shared across all squares)
  T_Delta : Finset CoarseTube
  -- C_Q is selected from the global T_Delta cover
  hC_Q_sub_TDelta : C_Q ⊆ T_Delta
  -- Weak bounds for A3 binning (rest)
  hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack
  horigPointsCard_lower : Real.rpow Δ (-t + 3 * ε) ≤ origPointsCard
  hC_card_upper_weak : (C_Q.card : ℝ) ≤ Real.rpow Δ (-1 - 5 * ε)
  -- Original tube family (before QTTC thinning) and subset relation
  T_original : Plane → Finset FineTube
  hT_Q_sub_original : ∀ p ∈ P_Q, T_Q p ⊆ T_original p
  -- T_Q is empty outside P_Q (restricted in a2_per_square)
  hT_Q_empty_outside : ∀ p, p ∉ P_Q → T_Q p = ∅

structure A2_Output (Δ δ s t ε : ℝ) where
  Qset : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Qset, A2_SquareData Δ δ s t ε Q
  C_global : Finset CoarseTube
  -- Global dyadic coarse cover (one per source-parent cell of global tube family)
  T_Delta : Finset CoarseTube
  -- C_global is the union of per-square C_Q
  hC_global_eq : C_global = Qset.biUnion (fun Q =>
    if h : Q ∈ Qset then (perSquare Q h).C_Q else ∅)
  -- Physical ball-growth bound for Qset centers (passed through from A1 at -11ε)
  hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
    ((Qset.filter (fun Q => dist (DirecretisedFurstenbergEstimate.Lagoon.squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-11 * ε) * r^t * (Qset.card : ℝ)
  -- All per-square T_Delta fields are the same global cover
  hT_Delta_eq : ∀ Q hQ, (perSquare Q hQ).T_Delta = T_Delta
  -- Global coarse family cardinality upper bound (from counter-assumption)
  hC_global_card_upper : (C_global.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε)

/-! ========================================================================
   A3: Uniformize local outputs  (OS (A.15)-(A.20))
   ======================================================================== -/

structure A3_Output (Δ δ s t ε : ℝ) where
  Qset : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Qset, A2_SquareData Δ δ s t ε Q
  hQset_sset : IsDeltaSSet Δ t (Real.rpow Δ (-25 * ε)) (Qset : Set (CoarseSquare Δ))
  hQset_card_lower : Real.rpow Δ (-t + 4 * ε) ≤ (Qset.card : ℝ)
  hQset_card_upper : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε)
  K_uniform : ℝ
  H_uniform : ℝ
  C2_uniform : ℝ
  C_card_uniform : ℝ
  hK_uniform : ∀ Q hQ,
    (perSquare Q hQ).K_Q ∈ Set.Icc (K_uniform / 2) (2 * K_uniform)
  hH_uniform : ∀ Q hQ,
    (perSquare Q hQ).H_Q ∈ Set.Icc (H_uniform / 2) (2 * H_uniform)
  hH_uniform_lower : H_uniform ≥ Real.rpow Δ (-(s + t) + 37 * ε)
  hC2_uniform : ∀ Q hQ, (perSquare Q hQ).C2_Q ≤ C2_uniform
  hC_card_uniform : ∀ Q hQ,
    ((perSquare Q hQ).C_Q.card : ℝ) ∈ Set.Icc (C_card_uniform / 2) (2 * C_card_uniform)
  hK_loss : K_uniform ≤ Real.rpow Δ (-ε)
  hC2_loss : C2_uniform ≤ Real.rpow Δ (-10 * ε)
  hC_card_exp_lower : Real.rpow Δ (-s + 12 * ε) ≤ C_card_uniform
  hC_card_exp_upper : C_card_uniform ≤ Real.rpow Δ (-s - 29 * ε)
  -- Global G3 bounds (proved via 2s incidence + counter-assumption)
  hC_card_upper : ∀ Q hQ, ((perSquare Q hQ).C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε)
  hC_Q_slope_cover_upper : ∀ Q hQ,
    Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' ((perSquare Q hQ).C_Q : Set CoarseTube)) ≤
      ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε))
  hH_Q_lower : ∀ Q hQ, (perSquare Q hQ).H_Q ≥ Real.rpow Δ (-(s + t) + 36 * ε)
  -- Physical ball-growth bound for Qset centers (A3 subset: constant degraded by Δ^{-ε})
  hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
    ((Qset.filter (fun Q => dist (DirecretisedFurstenbergEstimate.Lagoon.squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-20 * ε) * r^t * (Qset.card : ℝ)

/-! ========================================================================
   A4: Robust Kaufman refinement tied to C_Q  (OS (A.21)-(A.30))
   ======================================================================== -/

/-- Basic projected S-set data from RKP (non-recursive). -/
structure BasicProjectionData (Δ s ε : ℝ) (P_norm : Finset Plane) (boldT : CoarseTube) where
  σ : ℝ
  hσ_eq : σ = tubeSlope boldT
  projFun : Plane → ℝ
  hprojFun : projFun = affineProj σ
  Pi : Set ℝ
  hPi_sset : IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) Pi
  hPi_lower : ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤
    Metric.externalCoveringNumber Δ.toNNReal Pi
  witness : ℝ → Plane
  h_witness_mem : ∀ x ∈ Pi, witness x ∈ P_norm
  h_witness_proj : ∀ x ∈ Pi, projFun (witness x) = x
  hPi_sub : Pi ⊆ projFun '' (P_norm : Set Plane)

/-- Full projection data with robustness clause. -/
structure ProjectionData (Δ s ε : ℝ) (P_norm : Finset Plane) (boldT : CoarseTube)
  extends BasicProjectionData Δ s ε P_norm boldT where
  h_robust : ∀ (P' : Finset Plane), P' ⊆ P_norm →
    Metric.externalCoveringNumber Δ.toNNReal (P_norm : Set Plane) ≤
      ENNReal.ofReal (Real.rpow Δ (-48 * ε)) *
        Metric.externalCoveringNumber Δ.toNNReal (P' : Set Plane) →
    BasicProjectionData Δ s ε P' boldT

structure A4_SquareData (Δ δ s t ε : ℝ) (Q : CoarseSquare Δ) where
  base : A2_SquareData Δ δ s t ε Q
  -- Normalization center
  z_Q : Plane
  -- Normalized point set: P_norm = (P_Q - z_Q) / Δ, in unit square
  P_norm : Finset Plane
  hP_norm_card : (P_norm.card : ℝ) = (base.P_Q.card : ℝ)
  hP_norm_separated : SeparatedAt Δ (P_norm : Set Plane)
  hP_norm_bounded : ∀ p ∈ P_norm, p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1
  hP_norm_unnormalize : ∀ p ∈ P_norm, Δ • p + z_Q ∈ base.P_Q
  -- Good directions: subset of C_Q whose slopes pass RKP
  C_Q_pi : Finset CoarseTube
  hC_Q_pi_sub : C_Q_pi ⊆ base.C_Q
  hC_Q_pi_sset : IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) (C_Q_pi : Set CoarseTube)
  hC_Q_pi_card : (base.C_Q.card : ℝ) ≤
    Real.rpow Δ (-ε) * (C_Q_pi.card : ℝ)
  -- RKP projection data for each good direction
  projData : ∀ boldT ∈ C_Q_pi, ProjectionData Δ s ε P_norm boldT
  -- Global G3 bounds (inherited from A3)
  hC_card_upper : (base.C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε)
  hC_Q_slope_cover_upper : Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (base.C_Q : Set CoarseTube)) ≤
    ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε))
  hH_Q_lower : base.H_Q ≥ Real.rpow Δ (-(s + t) + 36 * ε)

/-- Total incidence sum over all squares and points for coarse tube U.
    This counts with multiplicity (same fine tube can appear at multiple points/squares).
    Distinct from `globalFiber` which counts distinct tubes. -/
def incidenceSum (Δ δ s t ε : ℝ) (hΔ_pos : 0 < Δ)
    (Qset : Finset (CoarseSquare Δ))
    (perSquare : ∀ Q ∈ Qset, A4_SquareData Δ δ s t ε Q)
    (U : CoarseTube) : ℕ :=
  ∑ Q' ∈ Qset.attach,
    ∑ p ∈ (perSquare Q'.val Q'.property).base.P_Q,
      assignedCountDyadic Δ hΔ_pos (perSquare Q'.val Q'.property).base.T_Q p U

structure A4_Output (Δ δ s t ε : ℝ) where
  Qset : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Qset, A4_SquareData Δ δ s t ε Q
  hQset_sset : IsDeltaSSet Δ t (Real.rpow Δ (-25 * ε)) (Qset : Set (CoarseSquare Δ))
  K_uniform : ℝ
  H_uniform : ℝ
  C2_uniform : ℝ
  C_card_uniform : ℝ
  hK_loss : K_uniform ≤ Real.rpow Δ (-ε)
  hC2_loss : C2_uniform ≤ Real.rpow Δ (-10 * ε)
  hH_uniform_lower : H_uniform ≥ Real.rpow Δ (-(s + t) + 37 * ε)
  hH_uniform : ∀ Q hQ,
    (perSquare Q hQ).base.H_Q ∈ Set.Icc (H_uniform / 2) (2 * H_uniform)
  hC_card_lower : Real.rpow Δ (-s + 12 * ε) ≤ C_card_uniform
  hC_card_upper : C_card_uniform ≤ Real.rpow Δ (-s - 29 * ε)
  hC_card_uniform : ∀ Q hQ,
    C_card_uniform / 2 ≤ ((perSquare Q hQ).base.C_Q.card : ℝ) ∧
    ((perSquare Q hQ).base.C_Q.card : ℝ) ≤ 2 * C_card_uniform
  -- Physical ball-growth bound for Qset centers (same Qset as A3)
  hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
    ((Qset.filter (fun Q => dist (DirecretisedFurstenbergEstimate.Lagoon.squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-20 * ε) * r^t * (Qset.card : ℝ)

/-! ========================================================================
   A5: Freeze global fine-child multiplicities  (OS G1-G4, (A.31))

   Uses DISTINCT global fiber counts via sourceParent (floor) relation.
   T_full = actual global fine family from counterexample.
   C_global = selected dyadic bin of parent tubes with frozen fiber size.
   T_global = T_full restricted to parents in C_global.
   Two-sided bound: N/2 ≤ |globalFiber(U)| ≤ N for U ∈ C_global.
   ======================================================================== -/

/-- The actual global fine tube family: union of all T_Q(p) across Qset. -/
def a5FullFineFamily (Δ δ s t ε : ℝ)
    (Qset : Finset (CoarseSquare Δ))
    (perSquare : ∀ Q ∈ Qset, A4_SquareData Δ δ s t ε Q) : Finset FineTube :=
  Qset.attach.biUnion (fun Q' =>
    (perSquare Q'.val Q'.property).base.P_Q.biUnion (fun p =>
      (perSquare Q'.val Q'.property).base.T_Q p))

structure A5_Output (Δ δ s t ε : ℝ) where
  hΔ_pos : 0 < Δ
  Qset : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Qset, A4_SquareData Δ δ s t ε Q
  hQset_sset : IsDeltaSSet Δ t (Real.rpow Δ (-75 * ε)) (Qset : Set (CoarseSquare Δ))
  hQset_card_lower : Real.rpow Δ (-t + 50 * ε) ≤ (Qset.card : ℝ)
  hQset_card_upper : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε)
  -- Global coarse family (selected parent layer)
  C_global : Finset CoarseTube
  C_global_input : Finset CoarseTube
  hC_global_sub : C_global ⊆ C_global_input
  -- Full global fine family from counterexample
  T_full : Finset FineTube
  -- Local fine families (from perSquare) are subsets of the global T_full
  h_local_sub_T_full : a5FullFineFamily Δ δ s t ε Qset perSquare ⊆ T_full
  -- Selected fine family: tubes whose parent is in C_global
  T_global : Finset FineTube
  hT_selected_eq : T_global =
    T_full.filter (fun T => parentCell Δ hΔ_pos T ∈ C_global.image (parentCell Δ hΔ_pos))
  -- Every tube in T_global has exactly one parent in C_global
  h_parent_unique : ∀ T ∈ T_global,
    ∃! (U : CoarseTube), U ∈ C_global ∧ InParent Δ hΔ_pos T U
  -- Uniform distinct fine-child count (two-sided)
  N : ℝ
  hN_pos : 0 < N
  hN_upper_core : N ≤ Real.rpow Δ (-2 * s - 214 * ε)
  hN_upper : N ≤ Real.rpow Δ (-2 * s - 214 * ε)
  -- G1: global coarse family size bound
  hG1_Cglobal_size : (C_global.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε)
  -- G2: each Q has many tubes in C_Q_pi
  hG2_local_size : ∀ Q hQ,
    Real.rpow Δ (-s + 13 * ε) ≤ ((perSquare Q hQ).C_Q_pi.card : ℝ)
  -- G3: each Q has many tubes in C_global (intersection lower bound)
  hG3_intersection : ∀ Q hQ,
    Real.rpow Δ (-s + 23 * ε) ≤ (((perSquare Q hQ).C_Q_pi ∩ C_global).card : ℝ)
  -- G4: two-sided uniform DISTINCT fine-child count
  -- N/2 ≤ |globalFiber(T_global, U)| ≤ N for all U ∈ C_global
  hG4_uniform : ∀ boldT ∈ C_global,
    N / 2 ≤ (globalFiber Δ hΔ_pos T_global boldT).card
  hG4_upper : ∀ boldT ∈ C_global,
    ((globalFiber Δ hΔ_pos T_global boldT).card : ℝ) ≤ N
  -- Disjoint partition: sum of distinct fibers = |T_global|
  h_partition : ∑ U ∈ C_global, (globalFiber Δ hΔ_pos T_global U).card = T_global.card
  -- Uniform H bound carried through from A3
  H_uniform : ℝ
  hH_uniform_lower : H_uniform ≥ Real.rpow Δ (-(s + t) + 37 * ε)
  hH_uniform : ∀ Q hQ,
    (perSquare Q hQ).base.H_Q ∈ Set.Icc (H_uniform / 2) (2 * H_uniform)
  -- Physical ball-growth bound for Qset centers
  hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
    ((Qset.filter (fun Q => dist (DirecretisedFurstenbergEstimate.Lagoon.squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-80 * ε) * r^t * (Qset.card : ℝ)

/-! ========================================================================
   A6: Intersection bound + total energy  (OS (A.32)-(A.41))
   QUANTITATIVE: I ≳ Δ^{-(s+t)+O(ε)}, E ≲ Δ^{-2t+O(ε)}, L ≲ Δ^{-2s+O(ε)}
   ======================================================================== -/

structure A6_Output (Δ δ s t ε : ℝ) (a5 : A5_Output Δ δ s t ε) where
  -- Total coarse incidence: I = Σ_Q |Cπ(Q)|
  I : ℝ
  hI_lower : Real.rpow Δ (-(s + t) + 73 * ε) ≤ I
  hI_upper : I ≤ Real.rpow Δ (-(s + t) - 26 * ε)
  -- Total pair energy: E = Σ_{Q,Q'} |Cπ(Q) ∩ Cπ(Q')|
  E : ℝ
  hE_upper : E ≤ Real.rpow Δ (-2 * t - 270 * ε)
  -- Global coarse family size
  L : ℝ
  hL_upper : L ≤ Real.rpow Δ (-2 * s - 3 * ε)
  hL_eq : L = (a5.C_global.card : ℝ)
  -- Point energy bound for use in A7
  pointEnergy_bound : ℝ
  h_pointEnergy : ∀ (Q : CoarseSquare Δ), Q ∈ a5.Qset →
    pointEnergy (t - s) a5.Qset Q ≤ pointEnergy_bound

/-! ========================================================================
   A7: Common tube extraction  (OS (A.42))
   ======================================================================== -/

structure A7_Output (Δ δ s t ε : ℝ) where
  a5 : A5_Output Δ δ s t ε
  T0 : CoarseTube
  Q0 : Finset (CoarseSquare Δ)
  hQ0_sub : Q0 ⊆ a5.Qset
  hT0_in_Cpi : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
    T0 ∈ (a5.perSquare Q (hQ0_sub hQ)).C_Q_pi
  -- T0 is in the global coarse family (needed for A5 hG4_upper)
  hT0_in_Cglobal : T0 ∈ a5.C_global
  -- |Q0| ≳ Δ^{s-t+O(ε)}
  hQ0_card_lower : Real.rpow Δ (s - t + 78 * ε) ≤ (Q0.card : ℝ)
  -- Q0 is a (Δ, t-s, Δ^{-O(ε)})-set
  hQ0_sset : IsDeltaSSet Δ (t - s) (Real.rpow Δ (-389 * ε)) (Q0 : Set (CoarseSquare Δ))
  -- Point energy / ball growth
  h_pointEnergy_bound : ℝ
  h_pointEnergy : ∀ q ∈ Q0,
    pointEnergy (t - s) Q0 q ≤ h_pointEnergy_bound
  h_ballGrowth : ∀ q ∈ Q0, ∀ r : ℝ, Δ ≤ r →
    ((Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤
      1 + h_pointEnergy_bound * Real.rpow r (t - s)
  -- T0 parameter bounds
  hT0_slope_bound : |tubeSlope T0| ≤ 1
  hT0_intercept_bound : |tubeIntercept T0| ≤ 3
  hT0_dirV_nonzero : (LemmaE.getDirV T0) 1 ≠ 0
  -- Physical square-center set (ε-only S-set constant, no dimensional loss)
  Q0_phys : Finset Plane
  hQ0_phys_eq : Q0_phys = Q0.image (squareCenter Δ)
  hQ0_phys_sset : IsDeltaSSet Δ (t - s) (Real.rpow Δ (-377 * ε)) (Q0_phys : Set Plane)

/-! ========================================================================
   A8: Fine-fiber popularity from H2  (OS (A.43)-(A.46))
   |P'_Q| ≈ Δ^{-t}, |T(p)∩T0| ≈ Δ^{-s} for each p
   ======================================================================== -/

structure A8_SquareData (Δ δ s t ε : ℝ) (T0 : CoarseTube) (Q : CoarseSquare Δ) where
  a4 : A4_SquareData Δ δ s t ε Q
  -- Popular points
  P'_Q : Finset Plane
  hP'_Q_sub : P'_Q ⊆ a4.P_norm
  -- |P'_Q| ≈ Δ^{-t}
  hP'_Q_card_lower : Real.rpow Δ (-t + 44 * ε) ≤ (P'_Q.card : ℝ)
  hP'_Q_card_upper : (P'_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε)
  -- Inverse normalization
  originalOfNorm : Plane → Plane
  h_originalOfNorm : ∀ p ∈ P'_Q, originalOfNorm p ∈ a4.base.P_Q
  h_norm_formula : ∀ p ∈ P'_Q, originalOfNorm p = Δ • p + a4.z_Q
  -- Fine tubes near T0 for each popular point (EXACT pointFiber, not metric)
  fineTubes : Plane → Finset FineTube
  hfine_eq_pointFiber : ∀ p ∈ P'_Q,
    fineTubes p = pointFiber Δ (a4.base.hΔ_pos) a4.base.T_Q (originalOfNorm p) T0
  hfine_inc : ∀ p ∈ P'_Q, ∀ T ∈ fineTubes p,
    originalOfNorm p ∈ Metric.cthickening (2 * δ) T.1
  -- |T(p) ∩ T0| ≈ Δ^{-s}
  hfine_card_lower : ∀ p ∈ P'_Q,
    Real.rpow Δ (-s + 40 * ε) ≤ (fineTubes p).card
  hfine_card_upper : ∀ p ∈ P'_Q,
    (fineTubes p).card ≤ Real.rpow Δ (-s - 7 * ε)
  hfine_tubes_separated : ∀ p ∈ P'_Q,
    SeparatedAt (δ / 2) (fineTubes p : Set FineTube)
  -- fineTubes inherits δ-scale S-set from T_Q (via subset + cardinality ratio)
  hfine_tubes_sset : ∀ p ∈ P'_Q,
    IsDeltaSSet δ s
      ((max 1 (a4.base.K_pack * Real.rpow δ (-ε)) * a4.base.K_Q *
        (DirecretisedFurstenbergEstimate.MainAppendix.affineLine_packing_constant : ℝ)) *
        a4.base.M *
        (DirecretisedFurstenbergEstimate.MainAppendix.affineLine_packing_constant : ℝ) *
        Real.rpow Δ (s - 40 * ε))
      (fineTubes p : Set FineTube)
  -- Tube parameter bounds
  h_dirV_nonzero : ∀ p ∈ P'_Q, ∀ T ∈ fineTubes p, (LemmaE.getDirV T) 1 ≠ 0
  h_tube_param_bounds : ∀ p ∈ P'_Q, ∀ T ∈ fineTubes p,
    |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3
  -- fineTubes is a subset of T_Q at the original point
  hfine_sub_TQ : ∀ p ∈ P'_Q,
    (fineTubes p : Set FineTube) ⊆ (a4.base.T_Q (originalOfNorm p) : Set FineTube)
  -- Projection data for T0 (from A4 RKP, restricted to P'_Q)
  proj : BasicProjectionData Δ s ε P'_Q T0

structure A8_Output (Δ δ s t ε : ℝ) where
  a7 : A7_Output Δ δ s t ε
  T0_norm : CoarseTube
  hT0_norm_eq : T0_norm = a7.T0
  Q0 : Finset (CoarseSquare Δ)
  hQ0_eq : Q0 = a7.Q0
  perSquare : ∀ Q ∈ Q0, A8_SquareData Δ δ s t ε T0_norm Q
  -- Compatibility: A8's a4 data is exactly A5's perSquare data on Q0
  h_perSquare_a4 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a7.Q0),
      (perSquare Q (show Q ∈ Q0 from hQ0_eq.symm ▸ hQ)).a4 =
        a7.a5.perSquare Q (a7.hQ0_sub hQ)

/-! ========================================================================
   A9: Affine normalization with dyadic data  (OS (A.47)-(A.48))

   Applies shear F(x,y) = (x - σ₀*y - h₀, y) so T0 becomes vertical.
   Outputs actual dyadic Δ-square and δ-tube cell data for A10.
   ======================================================================== -/

/-- Normalized square data after affine shear.
    The T0 context is provided by the parent A9_Output. -/
structure A9_SquareData (Δ δ s t ε : ℝ) (Q : CoarseSquare Δ) where
  -- Physical square coordinates
  x_Q : ℝ
  y_Q : ℝ
  hx_Q_eq : x_Q = squareX Δ Q
  hy_Q_eq : y_Q = squareY Δ Q
  hy_Q_bounds : y_Q ∈ Set.Icc (-2 : ℝ) 2
  -- Unnormalization map from A4: p_norm ↦ Δ•p_norm + z_Q
  unnormalize : Plane → Plane
  -- Pre-shear physical points: unnormalize(P'_Q)
  P_phys : Finset Plane
  hP_phys_sub : (P_phys : Set Plane) ⊆ Metric.cthickening (2 * Δ) (squareSet Δ Q)
  hP_phys_card : Real.rpow Δ (-t + 44 * ε) ≤ (P_phys.card : ℝ)
  -- Post-shear points after F(x,y) = (x - σ₀*y - h₀, y)
  P_norm_Q : Finset Plane
  hP_norm_Q_card : (P_norm_Q.card : ℝ) = (P_phys.card : ℝ)
  hP_norm_Q_card_upper : (P_norm_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε)
  -- Dyadic Δ-square containing post-shear points
  squareIndex : CoarseSquare Δ
  hP_in_square : (P_norm_Q : Set Plane) ⊆ Metric.cthickening (2 * Δ) (squareSet Δ squareIndex)
  -- Fine tubes near vertical T0, as dyadic δ-cells in parameter space
  fineTubes_norm : Plane → Finset (DyadicTubeCell δ)
  -- Each cell corresponds to an actual fine tube from A8
  fineTubeOfCell : (p : Plane) → DyadicTubeCell δ → FineTube
  -- |fine tubes| ≈ Δ^{-s}
  hfine_card_lower : ∀ p ∈ P_norm_Q,
    Real.rpow Δ (-s + 50 * ε) ≤ (fineTubes_norm p).card
  hfine_card_upper : ∀ p ∈ P_norm_Q,
    (fineTubes_norm p).card ≤ Real.rpow Δ (-s - 7 * ε)
  -- Projected set Π_Q at scale Δ (physical projection after shear)
  Pi_Q : Set ℝ
  hPi_Q_sset : IsDeltaSSet Δ s (Real.rpow Δ (-s - 49 * ε)) Pi_Q
  hPi_Q_bounds : ∀ x ∈ Pi_Q, x ∈ Set.Icc (-6 : ℝ) 6
  hPi_Q_delta_bounds : Pi_Q ⊆ Set.Icc (-50 * Δ) (50 * Δ)
  -- Normalized projection (genuine S-set, no -s dilation loss)
  Pi_Q_norm : Set ℝ
  hPi_Q_norm_sset : IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) Pi_Q_norm
  -- Translation constant: Pi_Q = {Δ * x + c_Q | x ∈ Pi_Q_norm}
  c_Q : ℝ
  hPi_Q_rel : Pi_Q = (fun x => Δ * x + c_Q) '' Pi_Q_norm
  -- Coarse tube parameters (slope, intercept) for C_Q_pi, with S-set
  coarseParams : Set (ℝ × ℝ)
  hcoarseParams_sset : IsDeltaSSet Δ s (Real.rpow Δ (-60 * ε)) coarseParams
  -- Witness: each projected point comes from a post-shear point
  witness : ℝ → Plane
  h_witness : ∀ x ∈ Pi_Q, witness x ∈ P_norm_Q ∧ (witness x) 0 = x
  -- Witness y-coordinate is close to physical square y_Q (shear preserves y)
  h_witness_y_close : ∀ x ∈ Pi_Q,
    |(witness x) 1 - y_Q| ≤ 3 * Δ
  -- Residual incidence: for witness x and fine tube cell,
  -- |x - slope*y - intercept| ≤ 6δ
  h_residual : ∀ x ∈ Pi_Q, ∀ cell ∈ fineTubes_norm (witness x),
    let T := fineTubeOfCell (witness x) cell
    |x - tubeSlope T * (witness x) 1 - tubeIntercept T| ≤ 6 * δ
  -- Cell parameter bounds: representative params are within 7Δ of origin
  hfine_cell_bounds : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
    |(paramsOfDyadicCell δ cell).1| ≤ 7 * Δ ∧ |(paramsOfDyadicCell δ cell).2| ≤ 7 * Δ
  -- fineTubeOfCell results satisfy standard tube conditions
  hfineTube_cond : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
    (LemmaE.getDirV (fineTubeOfCell p cell)) 1 ≠ 0 ∧
    |tubeSlope (fineTubeOfCell p cell)| ≤ 1 ∧
    |tubeIntercept (fineTubeOfCell p cell)| ≤ 3
  -- fineTubeOfCell uses exactly the dyadic cell representative parameters
  hfineTube_params : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
    tubeSlope (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).1 ∧
    tubeIntercept (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).2
  -- Fine tube cell params form a rescalable S-set at δ→Δ (for A10 product witness)
  C_fine_resc : ℝ
  hC_fine_resc_pos : 0 < C_fine_resc
  hC_fine_resc_le_499 : 16 * C_fine_resc ≤ Real.rpow Δ (-501 * ε)
  hfine_rescalable_prod : ∀ p ∈ P_norm_Q,
    IsRescalableDeltaSet δ Δ s C_fine_resc
      ((fun cell => paramsOfDyadicCell δ cell) '' (fineTubes_norm p : Set (DyadicTubeCell δ)))
  -- For global cardinality bound: underlying T_Q function and T0
  a4 : A4_SquareData Δ δ s t ε Q
  T_Q : Plane → Finset FineTube
  T0 : CoarseTube
  hΔ_pos : 0 < Δ
  hδ_pos : 0 < δ
  -- Shear parameters used for cell mapping
  σ₀ : ℝ
  h₀ : ℝ
  -- Consistency proofs for global cardinality bound
  hT_Q_eq : T_Q = a4.base.T_Q
  hσ₀_eq_T0 : σ₀ = tubeSlope T0
  hh₀_eq_T0 : h₀ = tubeIntercept T0
  -- Each normalized point's unnormalization is in the underlying A4 P_Q
  hunnormalize_in_a4PQ : ∀ p ∈ P_norm_Q, unnormalize p ∈ a4.base.P_Q
  hfine_sum_le : ∑ p ∈ P_norm_Q, (fineTubes_norm p).card ≤
    ∑ p_orig ∈ P_phys, assignedCountDyadic Δ hΔ_pos T_Q p_orig T0
  -- Each cell originates from a fine tube in the pointFiber of T0
  hfine_cell_origin : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
    ∃ (T : FineTube), T ∈ T_Q (unnormalize p) ∧ InParent Δ hΔ_pos T T0 ∧
      dyadicCellOfParams δ hδ_pos (tubeSlope T - σ₀, tubeIntercept T - h₀) = cell

structure A9_Output (Δ δ s t ε : ℝ) where
  -- Source A8 output (contains T0 and per-square data)
  a8 : A8_Output Δ δ s t ε
  Q0 : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Q0, A9_SquareData Δ δ s t ε Q
  -- Affine shear parameters: F(x,y) = (x - σ₀*y - h₀, y)
  σ₀ : ℝ
  h₀ : ℝ
  hσ₀_eq : σ₀ = tubeSlope a8.T0_norm
  h₀_eq : h₀ = tubeIntercept a8.T0_norm
  -- Explicit shear map F(p) = (p₀ - σ₀*p₁ - h₀, p₁)
  shear : Plane → Plane
  hshear_eq : ∀ p, (shear p) 0 = p 0 - σ₀ * p 1 - h₀ ∧ (shear p) 1 = p 1
  -- τ for Y S-set exponent
  τ : ℝ
  hτ_pos : 0 < τ
  hτ_le_one : τ ≤ 1
  hτ_le_t_sub_s : τ ≤ t - s
  -- Q0 S-set
  hQ0_sset : IsDeltaSSet Δ (t - s) (Real.rpow Δ (-389 * ε)) (Q0 : Set (CoarseSquare Δ))
  -- Y = {y_Q} with bounded-fiber injectivity (vertical tube geometry)
  hY_bounded_fiber : ∀ y : ℝ,
    (Q0.attach.filter fun Q' => (perSquare Q'.val Q'.property).y_Q = y).card ≤ 120
  -- Y S-set using physical→Y projection (ε-only constant, no fixed dimensional exponent)
  hY_sset : IsDeltaSSet Δ τ (Real.rpow Δ (-378 * ε))
    (⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0), {(perSquare Q hQ).y_Q})
  -- Total fine tube upper bound (for contradiction)
  h_total_fine_upper : Metric.externalCoveringNumber Δ.toNNReal
    (↑(Q0.attach.biUnion (fun Q' =>
      let hQ := Q'.property
      let sq := perSquare Q'.val hQ
      sq.P_norm_Q.biUnion (fun p =>
        sq.fineTubes_norm p |>.image (sq.fineTubeOfCell p)))) : Set FineTube) <
    ENNReal.ofReal (Real.rpow Δ (-2 * s - ε))
  -- Near-line condition: all Q ∈ Q0 lie within 59Δ of the line x = σ₀*y + h₀
  h_near : ∀ Q ∈ Q0,
    |Δ * ((Q.1 : ℝ) + 1 / 2) - σ₀ * Δ * ((Q.2 : ℝ) + 1 / 2) - h₀| ≤ 59 * Δ
  -- Metric transfer between AffineLine and parameter space
  h_metric_transfer : ∀ (T1 T2 : FineTube),
    ((LemmaE.getDirV T1) 1 ≠ 0 ∧ |tubeSlope T1| ≤ 1 ∧ |tubeIntercept T1| ≤ 3) →
    ((LemmaE.getDirV T2) 1 ≠ 0 ∧ |tubeSlope T2| ≤ 1 ∧ |tubeIntercept T2| ≤ 3) →
    dist (tubeSlope T1, tubeIntercept T1) (tubeSlope T2, tubeIntercept T2) ≤
      8 * dist T1 T2
  -- Total fine cell cardinality ≤ sum of dyadic assignedCounts over Q0 and P_phys
  h_total_fine_cells :
    (Q0.attach.biUnion (fun Q' =>
      let sq := perSquare Q'.val Q'.property
      sq.P_norm_Q.biUnion (fun p => sq.fineTubes_norm p))).card ≤
    ∑ Q' ∈ Q0.attach,
      ∑ p ∈ (perSquare Q'.val Q'.property).P_phys,
        assignedCountDyadic Δ (perSquare Q'.val Q'.property).hΔ_pos
          (perSquare Q'.val Q'.property).T_Q p
          (perSquare Q'.val Q'.property).T0
  -- Improved cardinal bound: |allCells| ≤ 2·Δ^{-(2s+214ε)}
  -- Proved via distinct globalFiber(T0) subset: allCells ⊆ g '' globalFiber(T0)
  h_allCells_card_upper :
    (Q0.attach.biUnion (fun Q' =>
      let sq := perSquare Q'.val Q'.property
      sq.P_norm_Q.biUnion (fun p => sq.fineTubes_norm p))).card ≤
    2 * Real.rpow Δ (-(2 * s + 214 * ε))

/-! ========================================================================
   A10: Product witness assembly with Δ⁻¹ dual dilation  (OS (A.48)-(A.53))

   Spatial map: A(x,y) = (Δ⁻¹ x, y)
   Dual parameter map: (σ,h) ↦ (Δ⁻¹ σ, Δ⁻¹ h)
   δ×δ dual cell → Δ×Δ cell (since δ=Δ²)
   X_y = Δ⁻¹ Π_Q
   ======================================================================== -/

structure A10_Output (Δ s t ε : ℝ) where
  -- Relaxed upper-bound exponent: ε < η_upper < η_axiom needed for A11 contradiction.
  -- Counter-assumption at scale δ=Δ² gives N_δ < Δ^{-(4s+2ε)}, which suffices
  -- for any η_upper < 2s+2ε.
  η_upper : ℝ
  hη_upper_pos : 0 < η_upper
  hη_upper_gt_ε : ε < η_upper
  τ : ℝ
  hτ_pos : 0 < τ
  hτ_le_one : τ ≤ 1
  hτ_le_t_sub_s : τ ≤ t - s
  -- Y = {witness_y(x) | Q ∈ Q0, x ∈ Pi_Q}
  Y : Set ℝ
  hY_bounds : Y ⊆ Set.Icc (-3 : ℝ) 3
  hY_sset : IsDeltaSSet Δ τ (Real.rpow Δ (-10000 * ε)) Y
  -- X_y = Δ⁻¹ • Pi_Q (genuine projection S-set, no -s factor)
  X : (y : ℝ) → y ∈ Y → Set ℝ
  hX_bounds : ∀ y hy, X y hy ⊆ Set.Icc (-50 : ℝ) 50
  hX_sset : ∀ y hy, IsDeltaSSet Δ s (Real.rpow Δ (-600 * ε)) (X y hy)
  -- Product set Z = ⋃_{y∈Y} X_y × {y}
  Z : Set (ℝ × ℝ)
  hZ_def : Z = ⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y}
  -- Tube families at each z ∈ Z, using Δ⁻¹ dual dilation
  -- Each fine δ-tube cell (σ,h) maps to Δ-tube cell (Δ⁻¹σ, Δ⁻¹h)
  T_coarse : (z : ℝ × ℝ) → z ∈ Z → Set (ℝ × ℝ)
  hT_bounds : ∀ z hz, T_coarse z hz ⊆ Set.Icc (-10 : ℝ) 10 ×ˢ Set.Icc (-10 : ℝ) 10
  hT_sset : ∀ z hz,
    IsDeltaSSet Δ s (Real.rpow Δ (-600 * ε)) (T_coarse z hz)
  -- Incidence: |p₁*z₂ + p₂ - z₁| ≤ 27Δ (A9 residual 6δ=6Δ², scaled by Δ⁻¹,
  -- plus shear/slope correction up to 21Δ; fixed-dilation map uses full 27Δ)
  h_inc : ∀ z hz, ∀ p ∈ T_coarse z hz,
    |p.1 * z.2 + p.2 - z.1| ≤ 27 * Δ
  -- Covering-number upper bound on T_union, proved from A9's distinct-fiber
  -- cardinal bound |allCells| ≤ 2·Δ^{-(2s+209ε)} via allFineUpper_from_cells.
  h_upper : (Metric.externalCoveringNumber Δ.toNNReal
      (⋃ (z : ℝ × ℝ) (hz : z ∈ Z), T_coarse z hz) : ENNReal) <
    ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper)))

/-! ========================================================================
   v2 Output structures: local u, T_oriented provenance, global separation

   These are used by the engine-generalized CounterAssumptionData.
   Existing A2_Output/A4_Output remain for the A2-A9 construction chain.
   ======================================================================== -/

/-- A2 output with global coarse family from config.T₀ parent image (v2.4). -/
structure A2_Output_v2
    (Δ δ s u ε : ℝ) (T_oriented : Set AffineLine) where
  Qset : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Qset, A2_SquareData Δ δ s u ε Q
  C_global : Finset CoarseTube
  T_Delta : Finset CoarseTube
  hC_global_eq : C_global = Qset.biUnion (fun Q =>
    if h : Q ∈ Qset then (perSquare Q h).C_Q else ∅)
  hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
    ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-11 * ε) * r^u * (Qset.card : ℝ)
  hT_Delta_eq : ∀ Q hQ, (perSquare Q hQ).T_Delta = T_Delta
  -- Ambient provenance from fine snapping + coarse parent movement
  hT_Delta_provenance : (T_Delta : Set CoarseTube) ⊆ Metric.cthickening (17 * Δ) (swapLine '' T_oriented)
  -- Every per-square C_Q is a subset of the global T_Delta
  hC_Q_sub_T_Delta : ∀ Q hQ, (perSquare Q hQ).C_Q ⊆ T_Delta

/-- Linked pair of A2 outputs (old + v2) sharing the same per-square data.

    This is the canonical boundary between the A1→A2 construction and the
    A2→A10 assembly. The QTTC stage must construct C_Q against the fixed
    global T_Delta and T_Q against the fixed T_source, providing the
    structural inclusion witnesses here.

    - `old` is consumed by A3–A10 (expects A2_Output interface)
    - `v2` is consumed by counter-assumption callbacks (expects A2_Output_v2)
    - Same Qset/perSquare identity is guaranteed structurally
    - `h_parent_injective` is needed by A5 freeze multiplicities -/
structure LinkedA2Outputs (Δ δ s t ε : ℝ) (T_oriented : Set AffineLine) (T_source : Finset FineTube) where
  Qset : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Qset, A2_SquareData Δ δ s t ε Q
  -- Old A2 output (for A3-A10 consumption)
  old : A2_Output Δ δ s t ε
  -- v2 A2 output (for counter-assumption callbacks)
  v2 : A2_Output_v2 Δ δ s t ε T_oriented
  -- Structural identity guarantees
  h_same_Qset : old.Qset = Qset
  h_same_perSquare : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset),
    old.perSquare Q (by rwa [h_same_Qset]) = perSquare Q hQ
  h_v2_same_Qset : v2.Qset = Qset
  h_v2_same_perSquare : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset),
    v2.perSquare Q (by rwa [h_v2_same_Qset]) = perSquare Q hQ
  -- Per-square coarse family inclusion in global T_Delta
  hC_Q_sub_TDelta : ∀ Q hQ, (perSquare Q hQ).C_Q ⊆ v2.T_Delta
  -- Per-square fine family inclusion in fixed source T_source
  hT_Q_sub_Tsource : ∀ Q hQ p, (perSquare Q hQ).T_Q p ⊆ T_source
  -- Parent cell injectivity on the global C_global
  h_parent_injective : ∀ (hΔ_pos : 0 < Δ),
    ∀ (U1 : CoarseTube), U1 ∈ old.C_global →
      ∀ (U2 : CoarseTube), U2 ∈ old.C_global → U1 ≠ U2 →
        parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2

/-- A4 output with local u and source-family witness.

    v2.5: T_source is a STRUCTURE PARAMETER, not a field.
    This prevents an arbitrary a4 from choosing an arbitrarily large T_source.
    The fixed T_source = image(toAffineLine, config.T₀) is supplied by the
    front-end (BridgeInner), and CounterAssumptionData carries the proved bound
    `hT_source_bound` on this SAME fixed source.

    Fine side is SIMPLIFIED: no separation, thickening, or local multiplicity.
    A4 only needs to witness `T_full ⊆ T_source`. The cardinality bound follows from
    source-to-Nice: card(T_source) ≤ δ^{-ρ_T} · Ncover(δ, Tbar).

    T_oriented is NOT a parameter of A4; it belongs to the coarse side
    (A2_Output_v2) and to CounterAssumptionData for Ncover equality. -/
structure A4_Output_v2
    (Δ δ s u ε : ℝ) (T_source : Finset FineTube) where
  Qset : Finset (CoarseSquare Δ)
  perSquare : ∀ Q ∈ Qset, A4_SquareData Δ δ s u ε Q
  hQset_sset : IsDeltaSSet Δ u (Real.rpow Δ (-25 * ε)) (Qset : Set (CoarseSquare Δ))
  K_uniform : ℝ
  H_uniform : ℝ
  C2_uniform : ℝ
  C_card_uniform : ℝ
  hK_loss : K_uniform ≤ Real.rpow Δ (-ε)
  hC2_loss : C2_uniform ≤ Real.rpow Δ (-10 * ε)
  hH_uniform_lower : H_uniform ≥ Real.rpow Δ (-(s + u) + 37 * ε)
  hH_uniform : ∀ Q hQ,
    (perSquare Q hQ).base.H_Q ∈ Set.Icc (H_uniform / 2) (2 * H_uniform)
  hC_card_lower : Real.rpow Δ (-s + 12 * ε) ≤ C_card_uniform
  hC_card_upper : C_card_uniform ≤ Real.rpow Δ (-s - 29 * ε)
  hC_card_uniform : ∀ Q hQ,
    C_card_uniform / 2 ≤ ((perSquare Q hQ).base.C_Q.card : ℝ) ∧
    ((perSquare Q hQ).base.C_Q.card : ℝ) ≤ 2 * C_card_uniform
  hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
    ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-20 * ε) * r^u * (Qset.card : ℝ)
  -- Fine family is a subset of the fixed source family (parameter, not field).
  hT_full_subset_source :
    a5FullFineFamily Δ δ s u ε Qset perSquare ⊆ T_source

end DirecretisedFurstenbergEstimate.AppendixA

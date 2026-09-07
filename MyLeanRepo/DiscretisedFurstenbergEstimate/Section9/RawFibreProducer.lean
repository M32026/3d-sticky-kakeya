module

/-
  Raw fibre producer: cover a point set by dyadic squares, choose representative
  points, and snap each finite fibre to dyadic tubes through its representative.

  Outputs exactly the data structure consumed by `fibre_uniformization_step`:
  - squares : Finset (DyadicSquare n) covering P
  - rawTubes : per-square Finset (DyadicTube n)
  - C_raw : S-set constant for raw tubes (with exact formula)
  - K : ℕ = 2*n+7, card bound exponent
  - All geometric properties: S-set, card bound, intersection, provenance,
    slope, intercept, strip

  This is a thin wrapper around `cover_by_dyadic_squares` + `snap_transfer_all`
  plus the point-indexed to square-indexed lifting used in BridgeInner.

  Whiteprint node: section9 / raw_fibre_producer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.SnapTransferAll
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.BoundedDyadicTubesCard
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate (AffineLine)
open DirecretisedFurstenbergEstimate.MainAppendix (affineLine_packing_constant)
open DirecretisedFurstenbergEstimate.MainAppendix (affineLine_packing_constant_pos)
open DyadicCardToNcover (toAffineLine)

abbrev RawPlane := Plane

/-- Raw fibre producer: cover P by dyadic squares, pick representatives,
    snap finite fibres to dyadic tubes.

    Inputs are oriented finite fibre data (Fp : Finset AffineLine per point).
    Outputs raw tube families per square with all properties needed by
    `fibre_uniformization_step`. -/
lemma raw_fibre_producer
    {n : ℕ} {δ s : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδn_pos : 0 < dyadicDelta n)
    (hδn_leδ : dyadicDelta n ≤ δ)
    (hδ_le2δn : δ ≤ 2 * dyadicDelta n)
    (hs_nonneg : 0 ≤ s)
    (P : Set RawPlane) (hP_bdd : P ⊆ Metric.closedBall 0 1)
    (hP_nonempty : P.Nonempty)
    (Fp : ∀ (p : RawPlane), p ∈ P → Finset AffineLine)
    (C_in : ℝ) (hC_in_pos : 0 < C_in)
    (hF_sset : ∀ p hp, IsDeltaSSet δ s C_in (Fp p hp : Set AffineLine))
    (hF_v0 : ∀ p hp, ∀ ℓ ∈ Fp p hp, (LemmaE.getDirV ℓ) 0 ≠ 0)
    (hF_slope : ∀ p hp, ∀ ℓ ∈ Fp p hp, |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (hF_near : ∀ p hp, ∀ ℓ ∈ Fp p hp, p ∈ Metric.cthickening δ ℓ.1)
    (T_oriented : Set AffineLine)
    (hF_sub : ∀ p hp, (Fp p hp : Set AffineLine) ⊆ T_oriented) :
    ∃ (squares : Finset (DyadicSquare n))
      (rawTubes : ∀ (q : DyadicSquare n), q ∈ squares → Finset (DyadicTube n))
      (C_raw : ℝ) (K : ℕ),
      squares.Nonempty ∧
      P ⊆ ⋃ q ∈ (squares : Set (DyadicSquare n)), DyadicSquare.toSet q ∧
      0 < C_raw ∧
      C_raw = 3721 * (affineLine_packing_constant : ℝ)^5 * (58 : ℝ)^s * C_in ∧
      K = 2 * n + 7 ∧
      (∀ q hq, IsDeltaSSet (dyadicDelta n) s C_raw (rawTubes q hq : Set (DyadicTube n))) ∧
      (∀ q hq, (rawTubes q hq).card ≤ 2^K) ∧
      (∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
          (U.toSet ∩ DyadicSquare.toSet q).Nonempty) ∧
      (∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
          ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
            dist (toAffineLine U) ℓ ≤ 7 * δ) ∧
      (∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.slope| ≤ 3 / 2) ∧
      (∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.intercept| ≤ 3) ∧
      (∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
          -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ)) ∧
      (∀ q, q ∈ squares → (P ∩ DyadicSquare.toSet q).Nonempty) := by
  let Kpack : ℝ := (affineLine_packing_constant : ℝ)
  have hKpack_pos : 0 < Kpack := by
    dsimp only [Kpack]
    exact Nat.cast_pos.mpr affineLine_packing_constant_pos

  have hP_isBdd : Bornology.IsBounded P :=
    Bornology.IsBounded.subset Metric.isBounded_closedBall hP_bdd

  rcases cover_by_dyadic_squares hP_isBdd with ⟨squares_raw, hcover_raw⟩

  let pred (q : DyadicSquare n) : Prop := (P ∩ DyadicSquare.toSet q).Nonempty
  let squares : Finset (DyadicSquare n) := squares_raw.filter pred

  have hcover : P ⊆ ⋃ q ∈ (squares : Set (DyadicSquare n)), DyadicSquare.toSet q := by
    intro p hp
    have h1 : p ∈ ⋃ q ∈ (squares_raw : Set (DyadicSquare n)), DyadicSquare.toSet q := hcover_raw hp
    rcases Set.mem_iUnion₂.mp h1 with ⟨q, hq, hq2⟩
    have h_inter : pred q := ⟨p, hp, hq2⟩
    have hq' : q ∈ squares := by
      rw [Finset.mem_filter]
      exact ⟨hq, h_inter⟩
    exact Set.mem_iUnion₂.mpr ⟨q, hq', hq2⟩

  have hsquares_nonempty : squares.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    have h1 := hcover hp
    rcases Set.mem_iUnion₂.mp h1 with ⟨q, hq, _⟩
    exact ⟨q, hq⟩

  choose rep hrep using fun (q : DyadicSquare n) (hq : q ∈ squares) =>
    show pred q from by
      have h : q ∈ squares := hq
      rw [Finset.mem_filter] at h
      exact h.2

  let rep' (q : DyadicSquare n) (hq : q ∈ squares) : RawPlane := rep q hq
  have hrep' : ∀ q hq, rep' q hq ∈ P ∩ DyadicSquare.toSet q := by
    intro q hq
    exact hrep q hq

  rcases snap_transfer_all
      (hδ_pos := hδ_pos) (hδ_le_one := hδ_le_one)
      (hδn_pos := hδn_pos) (hδn_leδ := hδn_leδ) (hδ_le2δn := hδ_le2δn)
      (hs_nonneg := hs_nonneg) (hC_in_pos := hC_in_pos)
      (P' := P) (F' := Fp)
      (hF'_sset := hF_sset) (hF'_v0 := hF_v0)
      (hF'_slope := hF_slope) (hF'_near := hF_near)
      (hP'_bdd := hP_bdd)
    with ⟨rawTubes_point, hraw_eq, hraw_sset, hraw_prov, hraw_intersect, hraw_slope, hraw_intercept, hraw_strip⟩

  let rawTubes (q : DyadicSquare n) (hq : q ∈ squares) : Finset (DyadicTube n) :=
    rawTubes_point (rep' q hq) (hrep' q hq).1

  let K_snap : ℝ := 3721 * Kpack^5 * (58 : ℝ)^s
  let C_raw : ℝ := K_snap * C_in
  have hC_raw_pos : 0 < C_raw := by positivity

  let K : ℕ := 2 * n + 7

  have hraw_square_sset : ∀ q hq, IsDeltaSSet (dyadicDelta n) s C_raw (rawTubes q hq : Set (DyadicTube n)) := by
    intro q hq
    dsimp only [rawTubes, C_raw, K_snap]
    exact hraw_sset (rep' q hq) (hrep' q hq).1

  have hraw_square_card : ∀ q hq, (rawTubes q hq).card ≤ 2^K := by
    intro q hq
    have h_bound : (rawTubes q hq).card ≤ 2 ^ (2 * n + 7) :=
      bounded_dyadic_tubes_card
        (fun U hU => hraw_slope (rep' q hq) (hrep' q hq).1 U hU)
        (fun U hU => hraw_intercept (rep' q hq) (hrep' q hq).1 U hU)
    simpa [K] using h_bound

  have hraw_square_intersect : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      (U.toSet ∩ DyadicSquare.toSet q).Nonempty := by
    intro q hq U hU
    let p := rep' q hq
    have hp_in_P : p ∈ P := (hrep' q hq).1
    have hp_in_Q : p ∈ DyadicSquare.toSet q := (hrep' q hq).2
    have h_eq : (rawTubes q hq : Set (DyadicTube n)) =
        (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) '' (Fp p hp_in_P : Set AffineLine) := by
      exact hraw_eq p hp_in_P
    have hT' : U ∈ (rawTubes q hq : Set (DyadicTube n)) := hU
    rw [h_eq] at hT'
    rcases hT' with ⟨ℓ, hℓ, rfl⟩
    have h1 : p ∈ (LegacyRound.snapToTubeThroughPoint n ℓ p).toSet :=
      LegacyRound.snapToTubeThroughPoint_incidence (n := n) (ℓ := ℓ) (p := p)
    exact ⟨p, h1, hp_in_Q⟩

  have hraw_square_prov : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧ dist (toAffineLine U) ℓ ≤ 7 * δ := by
    intro q hq U hU
    rcases hraw_prov (rep' q hq) (hrep' q hq).1 U hU with ⟨ℓ, hℓ_in_F, hdist⟩
    have hℓ_in_T : ℓ ∈ T_oriented := hF_sub (rep' q hq) (hrep' q hq).1 hℓ_in_F
    have h_eq : AffineLine.dist ℓ (toAffineLine U) = dist (toAffineLine U) ℓ := by
      rw [← dist_comm] <;> rfl
    exact ⟨ℓ, hℓ_in_T, h_eq ▸ hdist⟩

  have hraw_square_slope : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.slope| ≤ 3 / 2 := by
    intro q hq U hU
    exact hraw_slope (rep' q hq) (hrep' q hq).1 U hU

  have hraw_square_intercept : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.intercept| ≤ 3 := by
    intro q hq U hU
    exact hraw_intercept (rep' q hq) (hrep' q hq).1 U hU

  have hraw_square_strip : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ) := by
    intro q hq U hU
    exact hraw_strip (rep' q hq) (hrep' q hq).1 U hU

  have hC_raw_eq : C_raw = 3721 * Kpack^5 * (58 : ℝ)^s * C_in := by
    dsimp only [C_raw, K_snap]
    <;> ring

  have h_occupancy : ∀ q, q ∈ squares → (P ∩ DyadicSquare.toSet q).Nonempty := by
    intro q hq
    have h : q ∈ squares := hq
    rw [Finset.mem_filter] at h
    exact h.2

  exact ⟨squares, rawTubes, C_raw, K,
    hsquares_nonempty, hcover, hC_raw_pos, hC_raw_eq, rfl,
    hraw_square_sset, hraw_square_card, hraw_square_intersect,
    hraw_square_prov, hraw_square_slope, hraw_square_intercept, hraw_square_strip,
    h_occupancy⟩

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

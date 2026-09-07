module

/-
  B1 Bridge Wiring Helpers.

  Standalone lemmas for constructing the B1BridgeDecomposition in
  FrontEndComposition.lean. These handle:

  1. Swap-aware reference set construction (Ref_fin from Pbar)
  2. Fine card upper bound via injection into Ref_fin
  3. Fine card lower bound wrapper (DeltasSet ledger, εA)
  4. S-set absorption (point-ledger, point_int_run)
  5. Ball growth wrapper
  6. Endpoint exponent identity (u_run/2 + εA_run = u/2 + εA)
  7. Ncover transfer from √δ to Δ (point-ledger, εA_run)
  8. Matching at modified scale
  9. Coarse K absorption (endpoint-margin aware)
  10. Ncover restriction and swap transport
  11. Generalized coarse card upper with constant K

  Key design: all numerical helpers use CONSERVATIVE INEQUALITIES on εA_run
  and point_int_run, not exact equalities. This ensures validity at the u=2 endpoint.

  Split ledger:
  - Fine card lower: stronger DeltasSet εA
  - Coarse card upper: point-ledger εA_run
  - S-set absorption: point_int_run

  Dependencies:
  - Base (EuclideanPlane, IsDeltaSSet, Ncover)
  - CoordinatePartition (swapCoords, externalCoveringNumber_image_of_involutive_isometry)
  - DeltasSetTreeExtractionCore (dyadicSquare_toSet_disjoint)
  - DyadicBridge (dyadicSquareCenter, dyadicSquare_subset_centerBall)
  - B1FineCardLower (b1_fine_card_lower)
  - B1HardFields (b1_hP_ball_growth)
  - RegularB1Bounds (coarse_card_upper)
  - RegularIncidence.Definitions (Ncover)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.DeltasSetTreeExtractionCore
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.ScaleConversionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1FineCardLower
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1HardFields
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.RegularB1Bounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.B1BridgeWiring

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open CoordinatePartition

/-! ### 0. Ref_fin inclusion helper (P_ret → Pbar chain)

    Section 9 gives P_ret : Set EuclideanPlane with P_ret ⊆ (Pbar : Set Plane).
    The swapped hypothesis gives P_oriented ⊆ swapCoords '' P_ret (or P_ret).
    We need P_oriented ⊆ Ref_fin where Ref_fin is based on Pbar (the Finset).

    Chain:
      swapped=false: P_oriented ⊆ P_ret ⊆ Pbar = Ref_fin
      swapped=true:  P_oriented ⊆ swapCoords '' P_ret ⊆ swapCoords '' Pbar = Ref_fin
-/

/-- Construct P_oriented ⊆ Ref_fin from the P_ret → Pbar inclusion chain. -/
lemma wire_Ref_inclusion
    {Pbar : Finset EuclideanPlane}
    {P_ret P_oriented : Set EuclideanPlane}
    (swapped : Bool)
    (hP_ret_subset_Pbar : P_ret ⊆ (Pbar : Set EuclideanPlane))
    (hP_oriented_sub_Pret : P_oriented ⊆
      (if swapped then CoordinatePartition.swapCoords '' P_ret else P_ret)) :
    P_oriented ⊆
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
       else (Pbar : Set EuclideanPlane)) := by
  by_cases h_sw : swapped
  · -- swapped = true
    have h1 : P_oriented ⊆ CoordinatePartition.swapCoords '' P_ret := by
      simpa [h_sw] using hP_oriented_sub_Pret
    have h2 : CoordinatePartition.swapCoords '' P_ret ⊆
        CoordinatePartition.swapCoords '' (Pbar : Set EuclideanPlane) := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, hP_ret_subset_Pbar hy, rfl⟩
    have h3 : (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane) =
        CoordinatePartition.swapCoords '' (Pbar : Set EuclideanPlane) := by simp
    simpa [h_sw, h3] using Set.Subset.trans h1 h2
  · -- swapped = false
    have h1 : P_oriented ⊆ P_ret := by simpa [h_sw] using hP_oriented_sub_Pret
    simpa [h_sw] using Set.Subset.trans h1 hP_ret_subset_Pbar

/-! ### 1. h_fine_card_upper (swap-aware)

    Correct proof:
    1. Define Ref_fin : Finset EuclideanPlane :=
         if swapped then Pbar.image swapCoords else Pbar
    2. Ref_fin.card = Pbar.card (swapCoordsLI is injective)
    3. Each occupied fine square contains a point of P_oriented ⊆ Ref_fin
    4. The point-selection map is injective (distinct dyadic squares are disjoint)
    5. Therefore |P₀| ≤ |Ref_fin| = |Pbar| ≤ 100 · δ_n^{-u} = 100 · Δ^{-2u}
    6. Absorb 100 into Δ^{-ε/4} using h_small_eps
-/

/-- Swap-aware fine card upper bound: |P₀| ≤ Δ^{-2u-ε/4}. -/
lemma wire_h_fine_card_upper
    {n : ℕ} {Δ δ_n u ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n) (hδ_n_eq2 : δ_n = Δ^2)
    (hε_pos : 0 < ε)
    {Pbar : Finset EuclideanPlane}
    {P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    {P_oriented : Set EuclideanPlane}
    (hPbar_card : (Pbar.card : ℝ) ≤ 100 * Real.rpow δ_n (-u))
    (h_squares_meet : ∀ q ∈ P₀, ((q.toSet : Set EuclideanPlane) ∩ P_oriented).Nonempty)
    (swapped : Bool)
    (hP_oriented_sub_Ref : P_oriented ⊆
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
       else (Pbar : Set EuclideanPlane)))
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (P₀.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4) := by
  classical
  let Ref_fin : Finset EuclideanPlane :=
    if swapped then Pbar.image CoordinatePartition.swapCoords else Pbar

  have hRef_coe : (Ref_fin : Set EuclideanPlane) =
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
       else (Pbar : Set EuclideanPlane)) := by
    simp [Ref_fin] <;> aesop

  have hP_oriented_sub_Ref_fin : P_oriented ⊆ (Ref_fin : Set EuclideanPlane) := by
    rw [hRef_coe]
    exact hP_oriented_sub_Ref

  have hRef_card : Ref_fin.card = Pbar.card := by
    unfold Ref_fin
    split_ifs with h
    · have h_inj : Function.Injective CoordinatePartition.swapCoords :=
        CoordinatePartition.swapCoords_invol.injective
      have h_goal : (Pbar.image CoordinatePartition.swapCoords).card = Pbar.card := by
        rw [Finset.card_image_iff]
        <;> exact fun x _ y _ hxy => h_inj hxy
      exact h_goal
    · rfl

  -- For each occupied square, choose a witness point in P_oriented
  let choose_point (q : DiscretisedFurstenbergEstimate.DyadicSquare n) (hq : q ∈ P₀) : EuclideanPlane :=
    Classical.choose (h_squares_meet q hq)

  have hchoose1 : ∀ (q : DiscretisedFurstenbergEstimate.DyadicSquare n) (hq : q ∈ P₀),
      choose_point q hq ∈ (q.toSet : Set EuclideanPlane) := by
    intro q hq
    exact (Classical.choose_spec (h_squares_meet q hq)).1

  have hchoose2 : ∀ (q : DiscretisedFurstenbergEstimate.DyadicSquare n) (hq : q ∈ P₀),
      choose_point q hq ∈ P_oriented := by
    intro q hq
    exact (Classical.choose_spec (h_squares_meet q hq)).2

  -- Image of P₀.attach under choose_point
  let S : Finset EuclideanPlane :=
    P₀.attach.image (fun q : {q // q ∈ P₀} => choose_point q.val q.property)

  have hS_sub_Ref : S ⊆ Ref_fin := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, _, rfl⟩
    have h1 : choose_point q.val q.property ∈ P_oriented := hchoose2 q.val q.property
    exact hP_oriented_sub_Ref_fin h1

  have hS_inj : Set.InjOn (fun q : {q // q ∈ P₀} => choose_point q.val q.property)
      (Set.univ : Set {q // q ∈ P₀}) := by
    intro q1 _ q2 _ h_eq
    have h4 : choose_point q1.val q1.property = choose_point q2.val q2.property := h_eq
    have h5 : choose_point q2.val q2.property ∈ (q1.val.toSet : Set EuclideanPlane) := by
      have h51 : choose_point q1.val q1.property ∈ (q1.val.toSet : Set EuclideanPlane) :=
        hchoose1 q1.val q1.property
      rw [h4] at h51
      exact h51
    have h6 : choose_point q2.val q2.property ∈ (q2.val.toSet : Set EuclideanPlane) :=
      hchoose1 q2.val q2.property
    have h7 : ((q1.val.toSet : Set EuclideanPlane) ∩ (q2.val.toSet : Set EuclideanPlane)).Nonempty :=
      ⟨choose_point q2.val q2.property, h5, h6⟩
    have h8 : q1.val = q2.val := by
      by_contra hne
      have h9 : Disjoint (q1.val.toSet : Set EuclideanPlane) (q2.val.toSet : Set EuclideanPlane) :=
        dyadicSquare_toSet_disjoint hne
      have h10 : (q1.val.toSet : Set EuclideanPlane) ∩ (q2.val.toSet : Set EuclideanPlane) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h9
      simpa [h10] using h7
    exact Subtype.ext h8

  have hS_card : S.card = P₀.card := by
    have h_inj : Function.Injective (fun q : {q // q ∈ P₀} => choose_point q.val q.property) := by
      intro a b h
      exact hS_inj (Set.mem_univ a) (Set.mem_univ b) h
    rw [Finset.card_image_of_injective _ h_inj]
    simp [S]

  have h_main : P₀.card ≤ Ref_fin.card := by
    have h10 : S.card ≤ Ref_fin.card := Finset.card_le_card hS_sub_Ref
    rw [hS_card] at h10
    exact h10

  have h11 : (P₀.card : ℝ) ≤ (Ref_fin.card : ℝ) := by exact_mod_cast h_main
  have h12 : (Ref_fin.card : ℝ) = (Pbar.card : ℝ) := by exact_mod_cast hRef_card
  rw [h12] at h11

  have h13 : (Pbar.card : ℝ) ≤ 100 * Real.rpow δ_n (-u) := hPbar_card
  have h14 : Real.rpow δ_n (-u) = Real.rpow Δ (-2 * u) := by
    rw [hδ_n_eq2]
    have h_rpow2 : Real.rpow Δ (2 : ℝ) = (Δ^2 : ℝ) := by
      exact Real.rpow_two Δ
    have h21 : Real.rpow (Δ^2) (-u) = Real.rpow Δ (2 * (-u)) := by
      have h_mul : Real.rpow (Real.rpow Δ (2 : ℝ)) (-u) = Real.rpow Δ ((2 : ℝ) * (-u)) :=
        (Real.rpow_mul hΔ_pos.le (2 : ℝ) (-u)).symm
      rw [h_rpow2] at h_mul
      exact h_mul
    rw [h21]
    have h22 : 2 * (-u) = -2 * u := by ring
    rw [h22]
  rw [h14] at h13

  have h15 : (100 : ℝ) * Real.rpow Δ (-2 * u) ≤ Real.rpow Δ (-2 * u - ε / 4) := by
    have h16 : (100 : ℝ) ≤ Real.rpow Δ (-ε / 4) := by
      have h17 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small_eps
      have h_pos_eps : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos (ε / 4)
      have h18 : Real.rpow Δ (-ε / 4) = (Real.rpow Δ (ε / 4))⁻¹ := by
        have h_eq : -ε / 4 = -(ε / 4) := by ring
        rw [h_eq]
        exact Real.rpow_neg hΔ_pos.le (ε / 4)
      rw [h18]
      have h19 : (Real.rpow Δ (ε / 4))⁻¹ ≥ (1 / 100 : ℝ)⁻¹ := by
        gcongr
      have h20 : (1 / 100 : ℝ)⁻¹ = 100 := by norm_num
      rw [h20] at h19
      exact h19
    have h21 : Real.rpow Δ (-2 * u - ε / 4) =
        Real.rpow Δ (-2 * u) * Real.rpow Δ (-ε / 4) := by
      have h_add : Real.rpow Δ ((-2 * u) + (-ε / 4)) =
          Real.rpow Δ (-2 * u) * Real.rpow Δ (-ε / 4) :=
        Real.rpow_add hΔ_pos (-2 * u) (-ε / 4)
      have h_eq : (-2 * u) + (-ε / 4) = -2 * u - ε / 4 := by ring
      calc Real.rpow Δ (-2 * u - ε / 4)
        = Real.rpow Δ ((-2 * u) + (-ε / 4)) := by rw [h_eq]
      _ = Real.rpow Δ (-2 * u) * Real.rpow Δ (-ε / 4) := h_add
    rw [h21]
    have h22 : 0 ≤ Real.rpow Δ (-2 * u) := Real.rpow_nonneg hΔ_pos.le (-2 * u)
    nlinarith

  calc (P₀.card : ℝ)
    ≤ (Pbar.card : ℝ) := h11
  _ ≤ 100 * Real.rpow Δ (-2 * u) := h13
  _ ≤ Real.rpow Δ (-2 * u - ε / 4) := h15

/-! ### 2. h_fine_card_lower (uses stronger DeltasSet εA, NOT εA_run)

    This lemma is parameterized by εA (the original public exponent from DeltasSet).
    It does NOT need to be weakened to εA_run. The coarse-card upper route separately
    uses εA_run from the sqrt-cover hypothesis. These are independent parameters.
-/

/-- Fine card lower bound wrapper: Δ^{-2u+ε/4} ≤ |P₀|. -/
lemma wire_h_fine_card_lower
    {n : ℕ} {Δ δ_n δ u ε εA ρ_mass : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n) (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n) (hδ_n_eq2 : δ_n = Δ^2)
    (hδ_ge : δ_n / 4 ≤ δ)
    (hε_pos : 0 < ε) (hεA_pos : 0 < εA) (hρ_mass_nonneg : 0 ≤ ρ_mass)
    (hu_nonneg : 0 ≤ u)
    {Pbar : Finset EuclideanPlane}
    {P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    {pointSet : Set EuclideanPlane}
    (hpointSet_sub : pointSet ⊆ ⋃ p ∈ (P₀ : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)), (p.toSet : Set EuclideanPlane))
    (hPbar_ncover_lower : Ncover δ_n (Pbar : Set EuclideanPlane) ≥
        ENNReal.ofReal ((1 / 10000 : ℝ) * (81 * Real.rpow δ (-εA))⁻¹ * Real.rpow δ_n (-u)))
    (hNcover_pointSet_lower : Ncover δ_n pointSet ≥
        ENNReal.ofReal (Real.rpow δ_n ρ_mass) * Ncover δ_n (Pbar : Set EuclideanPlane))
    (h_exponent : 2 * εA + 2 * ρ_mass < ε / 4)
    (hΔ_small : (1 / 810000 : ℝ) * Real.rpow 4 (-εA) ≥
        Real.rpow Δ (ε / 4 - 2 * εA - 2 * ρ_mass)) :
    Real.rpow Δ (-2 * u + ε / 4) ≤ (P₀.card : ℝ) :=
  b1_fine_card_lower hΔ_pos hΔ_lt_one hδ_n_pos hδ_n_eq hδ_n_eq2 hδ_ge
    hε_pos hεA_pos hρ_mass_nonneg hu_nonneg
    hpointSet_sub hPbar_ncover_lower hNcover_pointSet_lower
    rfl h_exponent hΔ_small

/-! ### 3. hPfin_sset absorption (endpoint-margin aware)

    Uses conservative uniform bounds:
    - point_int_run ≤ 401ε/10000
    - ρ_mass ≤ ε/20 = 500ε/10000
    - Therefore β := ε - ρ_mass - point_int_run ≥ 9099ε/10000 > ε/2
    - From Δ^(ε/4) ≤ 1/100, get Δ^(2β) ≤ Δ^ε ≤ 10^-8
    - 15625 * 2^u ≤ 62500, so product ≤ 62500 * 10^-8 < 1
-/

/-- S-set absorption: 15625 · 2^u · (Δ²)^{ε-ρ_mass-point_int_run} ≤ 1. -/
lemma wire_hPfin_sset_absorption
    {Δ ε point_int_run ρ_mass u : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (hpoint_int_run_pos : 0 < point_int_run)
    (hpoint_int_run_le : point_int_run ≤ 401 * ε / 10000)
    (hρ_mass_nonneg : 0 ≤ ρ_mass)
    (hρ_mass_le : ρ_mass ≤ ε / 20)
    (hu_le_two : u ≤ 2)
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (15625 : ℝ) * (2 : ℝ)^u * Real.rpow (Δ^2) (ε - ρ_mass - point_int_run) ≤ 1 := by
  set β : ℝ := ε - ρ_mass - point_int_run with hβ_def
  have hβ_pos : 0 < β := by
    have h1 : ρ_mass ≤ 500 * ε / 10000 := by linarith
    have h2 : point_int_run ≤ 401 * ε / 10000 := hpoint_int_run_le
    linarith
  have hβ_ge_half : β ≥ ε / 2 := by
    have h1 : ρ_mass ≤ 500 * ε / 10000 := by linarith
    have h2 : point_int_run ≤ 401 * ε / 10000 := hpoint_int_run_le
    linarith
  have h2β_ge_ε : 2 * β ≥ ε := by linarith
  have hΔ2β_le : Real.rpow Δ (2 * β) ≤ Real.rpow Δ ε :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h2β_ge_ε
  have hΔε_le : Real.rpow Δ ε ≤ (1 / 100 : ℝ)^4 := by
    have h_rpow_eps4_pos : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
    have h1 : Real.rpow Δ ε = (Real.rpow Δ (ε / 4)).rpow 4 := by
      have h2 : (Real.rpow Δ (ε / 4)).rpow 4 = Real.rpow Δ ((ε / 4) * 4) :=
        (Real.rpow_mul hΔ_pos.le (ε / 4) (4 : ℝ)).symm
      have h3 : (ε / 4) * 4 = ε := by ring
      rw [h2, h3]
    rw [h1]
    have h2 : (Real.rpow Δ (ε / 4)).rpow 4 ≤ (1 / 100 : ℝ).rpow 4 :=
      Real.rpow_le_rpow h_rpow_eps4_pos h_small_eps (by norm_num)
    have h3 : (1 / 100 : ℝ).rpow 4 = (1 / 100 : ℝ)^4 := by simp
    rw [h3] at h2
    exact h2
  have h_const_le : (15625 : ℝ) * (2 : ℝ)^u ≤ 62500 := by
    have h1 : (2 : ℝ)^u ≤ 4 := by
      have h2 : u ≤ 2 := hu_le_two
      have h3 : (2 : ℝ)^u ≤ (2 : ℝ)^(2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      have h4 : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
      rw [h4] at h3
      exact h3
    calc (15625 : ℝ) * (2 : ℝ)^u ≤ 15625 * 4 := by gcongr
    _ = 62500 := by norm_num
  have h_rpow2 : Real.rpow (Δ^2) β = Real.rpow Δ (2 * β) := by
    have h_rpow2' : Real.rpow Δ (2 : ℝ) = (Δ^2 : ℝ) := by
      exact Real.rpow_two Δ
    have h : Real.rpow (Real.rpow Δ (2 : ℝ)) β = Real.rpow Δ ((2 : ℝ) * β) :=
      (Real.rpow_mul hΔ_pos.le (2 : ℝ) β).symm
    rw [h_rpow2'] at h
    exact h
  rw [h_rpow2]
  have h_rpow2β_pos : 0 ≤ Real.rpow Δ (2 * β) := Real.rpow_nonneg hΔ_pos.le _
  have h_main : (62500 : ℝ) * Real.rpow Δ (2 * β) ≤ 1 := by
    calc (62500 : ℝ) * Real.rpow Δ (2 * β)
      ≤ (62500 : ℝ) * Real.rpow Δ ε := by gcongr
    _ ≤ (62500 : ℝ) * (1 / 100 : ℝ)^4 := by gcongr
    _ = 1 / 1600 := by norm_num
    _ ≤ 1 := by norm_num
  calc (15625 : ℝ) * (2 : ℝ)^u * Real.rpow Δ (2 * β)
    ≤ (62500 : ℝ) * Real.rpow Δ (2 * β) := by gcongr
  _ ≤ 1 := h_main

/-! ### 4. hP_ball_growth wrapper -/

/-- Ball growth bound wrapper on dyadic square centers. -/
lemma wire_hP_ball_growth
    {n : ℕ} {δ_n Δ u ε : ℝ}
    (hδ_n_pos : 0 < δ_n) (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hu_nonneg : 0 ≤ u) (hε_pos : 0 < ε)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_le_Δ : δ_n ≤ Δ)
    {config_P0 : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    (hcenters_sset_strong : IsDeltaSSet δ_n u (Real.rpow δ_n (-ε))
        (config_P0.image dyadicSquareCenter : Set EuclideanPlane))
    (h_absorb : (25 : ℝ) * Real.rpow δ_n (-ε) ≤ Real.rpow Δ (-9 * ε / 4)) :
    ∀ (c : EuclideanPlane) (r : ℝ), Δ ≤ r →
      ((config_P0.image dyadicSquareCenter).filter (fun y => dist c y ≤ r)).card ≤
        Real.rpow Δ (-9 * ε / 4) * r^u * (config_P0.image dyadicSquareCenter).card :=
  B1HardFields.b1_hP_ball_growth hδ_n_pos hδ_n_eq hu_nonneg hε_pos hΔ_pos hΔ_lt_one
    hδ_n_le_Δ hcenters_sset_strong h_absorb

/-! ### 5. Endpoint exponent identity

    Public hypothesis is δ^{-(u/2 + εA)}; point-ledger needs δ^{-(u_run/2 + εA_run)}.
    The EndpointAdapter guarantees u_run/2 + εA_run = u/2 + εA exactly.
    When u < 2: trivial (u_run=u, εA_run=εA).
    When u=2: u_run=2-2ρ, εA_run=εA+ρ, so u_run/2+εA_run = 1-ρ+εA+ρ = 1+εA = u/2+εA.
-/

/-- Endpoint exponent identity: u_run/2 + εA_run = u/2 + εA. -/
lemma wire_endpoint_exponent_identity
    (u u_run εA εA_run ρ_endpoint : ℝ)
    (h_case : (u < 2 ∧ u_run = u ∧ εA_run = εA) ∨
              (u = 2 ∧ u_run = 2 - 2 * ρ_endpoint ∧ εA_run = εA + ρ_endpoint)) :
    u_run / 2 + εA_run = u / 2 + εA := by
  rcases h_case with (h | h)
  · rcases h with ⟨_, rfl, rfl⟩ <;> ring
  · rcases h with ⟨rfl, rfl, rfl⟩ <;> ring

/-! ### 6. Ncover transfer from √δ to Δ (point-ledger: uses εA_run)

    Note: h_delta_le_delta_n is an independent dyadic normalization hypothesis,
    NOT derived from δ_n ≤ 4δ. The latter is used only for factor-four exponent conversion.
-/

/-- Transfer Ncover bound from √δ to Δ with factor-4 loss.

    Thin wrapper around `ScaleConversionHelpers.sqrt_cover_to_delta_cover`.
    Requires `0 < u` (always true in B1 since `u ≥ t > s > 0`). -/
lemma wire_ncover_transfer
    {Δ δ δ_n u εA_run : ℝ} (hΔ_pos : 0 < Δ)
    (hδ_pos : 0 < δ) (hδ_n_eq2 : δ_n = Δ^2)
    (h_delta_le_delta_n : δ ≤ δ_n)
    (hδ_n_le_4δ : δ_n ≤ 4 * δ)
    (hu_pos : 0 < u) (hεA_run_pos : 0 < εA_run)
    {P : Set EuclideanPlane}
    (hNcover_sqrt : Ncover (Real.sqrt δ) P ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA_run)))) :
    Ncover Δ P ≤ ENNReal.ofReal (4^(u / 2 + εA_run) * Real.rpow Δ (-(u + 2 * εA_run))) := by
  have hδ_n_pos : 0 < δ_n := by
    rw [hδ_n_eq2] <;> positivity
  exact DirecretisedFurstenbergEstimate.FrontEndLemmas.sqrt_cover_to_delta_cover
    hδ_pos hδ_n_pos hΔ_pos hδ_n_eq2 h_delta_le_delta_n hδ_n_le_4δ hu_pos hεA_run_pos hNcover_sqrt

/-! ### 7. Matching at modified scale δ' = δ_n * √2 / 2

    Uses dyadicSquare_subset_centerBall from DyadicBridge.
-/

/-- For each fine square center, find a point in P within δ_n·√2/2. -/
lemma wire_matching
    {n : ℕ} {δ_n : ℝ}
    {P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    {P_oriented : Set EuclideanPlane}
    {P : Set EuclideanPlane}
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (h_squares_meet : ∀ q ∈ P₀, ((q.toSet : Set EuclideanPlane) ∩ P_oriented).Nonempty)
    (hP_oriented_sub_P : P_oriented ⊆ P) :
    ∀ (q : EuclideanPlane), q ∈ P₀.image dyadicSquareCenter →
      ∃ (p : EuclideanPlane), p ∈ P ∧ dist q p ≤ δ_n * Real.sqrt 2 / 2 := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨square, hsquare, h_eq⟩
  rcases h_squares_meet square hsquare with ⟨p, hp_square, hp_oriented⟩
  have hp_P : p ∈ P := hP_oriented_sub_P hp_oriented
  have h_sub : (square.toSet : Set EuclideanPlane) ⊆
      Metric.closedBall (dyadicSquareCenter square) (DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2) :=
    dyadicSquare_subset_centerBall square
  have h_in : p ∈ Metric.closedBall (dyadicSquareCenter square) (DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2) :=
    h_sub hp_square
  have h_dist : dist (dyadicSquareCenter square) p ≤ DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2 := by
    have h_dist' : dist p (dyadicSquareCenter square) ≤ DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2 := by
      simpa [Metric.mem_closedBall] using h_in
    rw [dist_comm] at h_dist'
    exact h_dist'
  have h_final : dist q p ≤ δ_n * Real.sqrt 2 / 2 := by
    have h_eq2 : dyadicSquareCenter square = q := h_eq
    have h_dist2 : dist q p ≤ DiscretisedFurstenbergEstimate.dyadicDelta n * Real.sqrt 2 / 2 := by
      rw [←h_eq2]
      exact h_dist
    rw [hδ_n_eq]
    exact h_dist2
  exact ⟨p, hp_P, h_final⟩

/-! ### 8. K absorption for coarse card upper (endpoint-margin aware)

    εA_run ≤ 201ε/10000, so u/2 + εA_run < 2 for ε < 1, hence K ≤ 16
    α := ε/2 - 2*εA_run ≥ 4598ε/10000 > 9ε/20
    From h_small_eps: Δ^(ε/4) ≤ 1/100
    Δ^α = (Δ^(ε/4))^(α/(ε/4)) ≤ (1/100)^(9/5) < (1/100)^(7/4) < 1/1296
-/

/-- Coarse K absorption: 81 · 4^{u/2+εA_run} ≤ Δ^{-(ε/2-2εA_run)}. -/
lemma wire_coarse_K_absorb
    {Δ ε εA_run u : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hεA_run_pos : 0 < εA_run)
    (hεA_run_le : εA_run ≤ 201 * ε / 10000)
    (hu_le_two : u ≤ 2)
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (81 : ℝ) * (4 : ℝ)^(u / 2 + εA_run) ≤ Real.rpow Δ (-(ε / 2 - 2 * εA_run)) := by
  set α : ℝ := ε / 2 - 2 * εA_run with hα_def
  have hα_pos : 0 < α := by
    have h1 : εA_run ≤ 201 * ε / 10000 := hεA_run_le
    linarith
  have hα_ge : α ≥ 9 * ε / 20 := by
    have h1 : εA_run ≤ 201 * ε / 10000 := hεA_run_le
    linarith
  have hK_le : (4 : ℝ)^(u / 2 + εA_run) ≤ 16 := by
    have h1 : u / 2 + εA_run ≤ 2 := by
      have h2 : εA_run < 1 := by linarith
      linarith
    have h3 : (4 : ℝ)^(u / 2 + εA_run) ≤ (4 : ℝ)^(2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    have h4 : (4 : ℝ)^(2 : ℝ) = 16 := by norm_num
    rw [h4] at h3
    exact h3
  have h81K : (81 : ℝ) * (4 : ℝ)^(u / 2 + εA_run) ≤ 1296 := by
    calc (81 : ℝ) * (4 : ℝ)^(u / 2 + εA_run) ≤ 81 * 16 := by gcongr
    _ = 1296 := by norm_num
  have h_ratio : α / (ε / 4) ≥ 9 / 5 := by
    have h1 : α ≥ 9 * ε / 20 := hα_ge
    have h2 : 0 < ε / 4 := by linarith
    have h3 : α / (ε / 4) ≥ (9 * ε / 20) / (ε / 4) := by gcongr
    have h4 : (9 * ε / 20) / (ε / 4) = 9 / 5 := by
      field_simp [hε_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3
  have h_main : Real.rpow Δ α ≤ 1 / 1296 := by
    have h_rpow_nonneg : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
    have h3 : Real.rpow (Real.rpow Δ (ε / 4)) (α / (ε / 4)) =
        Real.rpow Δ α := by
      have h : Real.rpow (Real.rpow Δ (ε / 4)) (α / (ε / 4)) =
          Real.rpow Δ ((ε / 4) * (α / (ε / 4))) :=
        (Real.rpow_mul hΔ_pos.le (ε / 4) (α / (ε / 4))).symm
      rw [h]
      have h2 : (ε / 4) * (α / (ε / 4)) = α := by
        field_simp [hε_pos.ne'] <;> ring
      rw [h2]
    have h4 : Real.rpow Δ α ≤ Real.rpow (1 / 100 : ℝ) (α / (ε / 4)) := by
      rw [← h3]
      exact Real.rpow_le_rpow (by positivity) h_small_eps (by positivity)
    have h5 : Real.rpow (1 / 100 : ℝ) (α / (ε / 4)) ≤
        Real.rpow (1 / 100 : ℝ) (9 / 5 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      exact h_ratio
    have h6 : Real.rpow (1 / 100 : ℝ) (9 / 5 : ℝ) ≤
        Real.rpow (1 / 100 : ℝ) (7 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      norm_num
    have h7 : Real.rpow (1 / 100 : ℝ) (7 / 4 : ℝ) < 1 / 1296 := by
      have h71 : Real.rpow (1 / 100 : ℝ) (7 / 4 : ℝ) <
          Real.rpow (1 / 81 : ℝ) (7 / 4 : ℝ) :=
        Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      have h72 : Real.rpow (1 / 81 : ℝ) (7 / 4 : ℝ) = (1 / 3 : ℝ) ^ 7 := by
        have h_eq1 : (1 / 81 : ℝ) = Real.rpow (1 / 3 : ℝ) (4 : ℝ) := by norm_num
        rw [h_eq1]
        have h_pos : 0 ≤ (1 / 3 : ℝ) := by norm_num
        have h_mul : Real.rpow (Real.rpow (1 / 3 : ℝ) (4 : ℝ)) (7 / 4 : ℝ) =
            Real.rpow (1 / 3 : ℝ) ((4 : ℝ) * (7 / 4 : ℝ)) := by
          exact (Real.rpow_mul h_pos (4 : ℝ) (7 / 4 : ℝ)).symm
        rw [h_mul]
        have h_eq2 : (4 : ℝ) * (7 / 4 : ℝ) = (7 : ℝ) := by ring
        rw [h_eq2]
        have h_eq3 : Real.rpow (1 / 3 : ℝ) (7 : ℝ) = (1 / 3 : ℝ) ^ 7 := by simp
        rw [h_eq3]
      rw [h72] at h71
      have h74 : (1 / 3 : ℝ) ^ 7 = 1 / 2187 := by norm_num
      rw [h74] at h71
      have h73 : (1 / 2187 : ℝ) < 1 / 1296 := by norm_num
      exact lt_trans h71 h73
    exact le_trans h4 (le_trans h5 (le_trans h6 h7.le))
  have h_pos : 0 < Real.rpow Δ α := Real.rpow_pos_of_pos hΔ_pos _
  have h9 : Real.rpow Δ (-α) = (Real.rpow Δ α)⁻¹ :=
    Real.rpow_neg (by linarith) _
  have h10 : -α = -(ε / 2 - 2 * εA_run) := by
    simp [hα_def] <;> ring
  rw [h10, h9]
  have h11 : (Real.rpow Δ α)⁻¹ ≥ (1 / 1296 : ℝ)⁻¹ := by gcongr
  have h12 : (1 / 1296 : ℝ)⁻¹ = 1296 := by norm_num
  rw [h12] at h11
  linarith

/-! ### 9. Ncover restriction and swap transport for coarse upper

    To get a sqrt-cover bound on Ref:
    1. Restrict public bound from P to Pbar (Pbar ⊆ P)
    2. If swapped, transport across swapCoords isometry
       (isometries preserve external covering numbers)
-/

/-- Restrict Ncover bound from a superset P to Pbar. -/
lemma wire_ncover_restrict
    {δ C : ℝ} {P Pbar : Set EuclideanPlane}
    (hPbar_sub : Pbar ⊆ P)
    (hNcover : Ncover δ P ≤ ENNReal.ofReal C) :
    Ncover δ Pbar ≤ ENNReal.ofReal C := by
  have h1 : Ncover δ Pbar ≤ Ncover δ P := by
    simpa [Ncover] using Metric.externalCoveringNumber_mono_set hPbar_sub
  exact le_trans h1 hNcover

/-- Transport Ncover across swapCoords isometry.

    Since swapCoords is an involutive isometry, it preserves external covering numbers:
    Ncover δ (swapCoords '' Pbar) = Ncover δ Pbar. -/
lemma wire_ncover_swap
    {δ : ℝ} {Pbar : Set EuclideanPlane} :
    Ncover δ (CoordinatePartition.swapCoords '' Pbar) = Ncover δ Pbar := by
  simpa [Ncover] using
    CoordinatePartition.externalCoveringNumber_image_of_involutive_isometry
      CoordinatePartition.swapCoords_isometry CoordinatePartition.swapCoords_invol
      δ.toNNReal Pbar

/-- Combined: get Ncover bound on Ref from public bound on P.

    If not swapped: Ref = Pbar, just restrict.
    If swapped: Ref = swapCoords '' Pbar, restrict then transport. -/
lemma wire_ncover_to_Ref
    {δ C : ℝ} {P : Set EuclideanPlane} {Pbar : Finset EuclideanPlane}
    (swapped : Bool)
    (hPbar_sub : (Pbar : Set EuclideanPlane) ⊆ P)
    (hNcover : Ncover δ P ≤ ENNReal.ofReal C) :
    Ncover δ (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
              else (Pbar : Set EuclideanPlane)) ≤ ENNReal.ofReal C := by
  have h1 : Ncover δ (Pbar : Set EuclideanPlane) ≤ ENNReal.ofReal C :=
    wire_ncover_restrict hPbar_sub hNcover
  split_ifs with h
  · -- swapped = true
    have h2 : (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane) =
        CoordinatePartition.swapCoords '' (Pbar : Set EuclideanPlane) := by
      simp
    rw [h2]
    rw [wire_ncover_swap]
    exact h1
  · -- swapped = false
    exact h1

/-! ### 10. Generalized coarse card upper bound with multiplicative constant K

    This extends b1_coarse_card_upper to handle the factor-4 loss from
    transferring Ncover from √δ to Δ when δ_n ≤ 4δ.

    Key idea: if Ncover Δ P ≤ K · Δ^{-(t+2εA)} and 81·K ≤ Δ^{-(ε/2-2εA)},
    then coarse card ≤ Δ^{-t-ε/2}.

    Typical K = 4^{t/2+εA} ≤ 16 (since t ≤ 2, εA < 1), so 81·K ≤ 1296,
    which is absorbed by Δ^{23ε/50} ≤ 1/1296 from h_small_eps.
-/

/-- Generalized coarse card upper bound with multiplicative constant K.

    If Ncover Δ P ≤ K · Δ^{-(t+2εA)} and 81·K ≤ Δ^{-(ε/2-2εA)},
    then |coarseP₀| ≤ Δ^{-t-ε/2}. -/
lemma b1_coarse_card_upper_K
    {m : ℕ} {Δ δ t ε εA K : ℝ}
    (hΔ_eq : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (ht_pos : 0 < t) (hε_pos : 0 < ε) (hεA_pos : 0 < εA)
    (hεA_lt : 2 * εA < ε / 2)
    (hK_nonneg : 0 ≤ K)
    (hK_absorb : (81 : ℝ) * K ≤ Real.rpow Δ (-(ε / 2 - 2 * εA)))
    {P : Set EuclideanPlane} {Pfin : Finset EuclideanPlane}
    {coarseP₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare m)}
    (h_match_backward : ∀ q ∈ Pfin, ∃ p ∈ P, dist q p ≤ δ)
    (h_intersect : ∀ Q ∈ coarseP₀,
      ((Pfin : Set EuclideanPlane) ∩ (Q.toSet : Set EuclideanPlane)).Nonempty)
    (h_sqrt_reg : Metric.externalCoveringNumber Δ.toNNReal P ≤
        ENNReal.ofReal (K * Real.rpow Δ (-(t + 2 * εA)))) :
    (coarseP₀.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2) := by
  have h_a_pos : 0 < ε / 2 - 2 * εA := by linarith
  have h1 : (coarseP₀.card : ℕ∞) ≤
      81 * Metric.externalCoveringNumber Δ.toNNReal P :=
    coarse_card_upper hΔ_eq hΔ_pos hδ_pos hδ_le_Δ h_match_backward h_intersect
  have h2 : (coarseP₀.card : ENNReal) ≤
      (81 : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal P := by
    exact_mod_cast h1
  have h3 : (coarseP₀.card : ENNReal) ≤
      (81 : ENNReal) * ENNReal.ofReal (K * Real.rpow Δ (-(t + 2 * εA))) := by
    calc (coarseP₀.card : ENNReal)
      ≤ (81 : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal P := h2
    _ ≤ (81 : ENNReal) * ENNReal.ofReal (K * Real.rpow Δ (-(t + 2 * εA))) := by gcongr
  have h_rhs_nonneg : 0 ≤ K * Real.rpow Δ (-(t + 2 * εA)) := by
    have h_pos : 0 ≤ Real.rpow Δ (-(t + 2 * εA)) := Real.rpow_nonneg hΔ_pos.le _
    exact mul_nonneg hK_nonneg h_pos
  have h3' : (81 : ENNReal) * ENNReal.ofReal (K * Real.rpow Δ (-(t + 2 * εA))) =
      ENNReal.ofReal ((81 : ℝ) * K * Real.rpow Δ (-(t + 2 * εA))) := by
    have h_assoc : (81 : ℝ) * K * Real.rpow Δ (-(t + 2 * εA)) =
        (81 : ℝ) * (K * Real.rpow Δ (-(t + 2 * εA))) := by ring
    have h_mul : ENNReal.ofReal ((81 : ℝ) * (K * Real.rpow Δ (-(t + 2 * εA)))) =
        ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (K * Real.rpow Δ (-(t + 2 * εA))) :=
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 81 by norm_num)
    have h_coe : (ENNReal.ofReal (81 : ℝ)) = (81 : ENNReal) := by simp
    rw [h_assoc, h_mul, h_coe] <;> rfl
  rw [h3'] at h3
  have h_card_real : (coarseP₀.card : ENNReal) = ENNReal.ofReal (↑(coarseP₀.card : ℝ)) := by simp
  rw [h_card_real] at h3
  have h81_rhs_nonneg : 0 ≤ (81 : ℝ) * K * Real.rpow Δ (-(t + 2 * εA)) :=
    mul_nonneg (mul_nonneg (by norm_num) hK_nonneg) (Real.rpow_nonneg hΔ_pos.le _)
  have h4 : (↑(coarseP₀.card : ℝ)) ≤ (81 : ℝ) * K * Real.rpow Δ (-(t + 2 * εA)) :=
    (ENNReal.ofReal_le_ofReal_iff h81_rhs_nonneg).mp h3
  have h_pos2 : 0 ≤ Real.rpow Δ (-(t + 2 * εA)) := Real.rpow_nonneg hΔ_pos.le _
  have h12 : (81 : ℝ) * K * Real.rpow Δ (-(t + 2 * εA)) ≤
      Real.rpow Δ (-(ε / 2 - 2 * εA)) * Real.rpow Δ (-(t + 2 * εA)) :=
    mul_le_mul_of_nonneg_right hK_absorb h_pos2
  have h_rpow_add : Real.rpow Δ (-(ε / 2 - 2 * εA)) * Real.rpow Δ (-(t + 2 * εA)) =
      Real.rpow Δ ((-(ε / 2 - 2 * εA)) + (-(t + 2 * εA))) :=
    (Real.rpow_add hΔ_pos _ _).symm
  have h11 : (-(ε / 2 - 2 * εA)) + (-(t + 2 * εA)) = -t - ε / 2 := by ring
  rw [h_rpow_add, h11] at h12
  exact le_trans h4 h12

end DirecretisedFurstenbergEstimate.FrontEndLemmas.B1BridgeWiring

end

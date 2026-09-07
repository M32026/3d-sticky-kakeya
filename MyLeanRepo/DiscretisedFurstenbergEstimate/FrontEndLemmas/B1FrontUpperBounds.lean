module

/-
  B1 Front Upper Bounds — Three standalone lemmas deriving the upper bounds
  that b1_assembly needs, directly from Front data.

  These replace the timing-out b1_assembly_from_front wrapper.

  1. fine_card_upper_from_front    — |P₀| ≤ Δ^{-2u-ε/4}
  2. coarse_card_upper_from_front  — |coarseP₀| ≤ Δ^{-u-ε/2}
  3. per_square_upper_from_front   — ∀ Q, fibre(Q) ≤ Δ^{-u-3ε/5}
     (Ref_fin injection route, per operator correction)

  Whiteprint node: b1_front_upper_bounds
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1BridgeWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1CardBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1PerSquareViaRef
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.ScaleConversionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.SquareGeometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.SsetExtractionBounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.B1FrontUpperBounds

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.CombiningTheorem
open InductionConfigurations
open SquareGeometry

abbrev DSquare n := DiscretisedFurstenbergEstimate.DyadicSquare n
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev NiceConfig n s C₁ M := CombiningTheorem.NiceConfiguration n s C₁ M

/-! ### Lemma 1: Fine card upper from Front Pbar bound -/

/-- Derive `config.P₀.card ≤ Δ^{-2u-ε/4}` from Front Pbar card bound
    and square-meeting property. Swap-aware via Ref_fin. -/
lemma fine_card_upper_from_front
    {n m : ℕ} {hnm : m ≤ n}
    {Δ δ_n u ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n) (hδ_n_eq2 : δ_n = Δ^2)
    (hε_pos : 0 < ε)
    {Pbar : Finset Plane}
    {P₀ : Finset (DSquare n)}
    {P_oriented : Set Plane}
    (hPbar_card : (Pbar.card : ℝ) ≤ 100 * Real.rpow δ_n (-u))
    (h_squares_meet : ∀ q ∈ P₀, ((q.toSet : Set Plane) ∩ P_oriented).Nonempty)
    (swapped : Bool)
    (hP_oriented_sub_Ref : P_oriented ⊆
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set Plane)
       else (Pbar : Set Plane)))
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (P₀.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4) :=
  B1BridgeWiring.wire_h_fine_card_upper
    hΔ_pos hΔ_lt_one hδ_n_pos hδ_n_eq2 hε_pos
    (hPbar_card := hPbar_card)
    (h_squares_meet := h_squares_meet)
    swapped hP_oriented_sub_Ref h_small_eps

/-! ### Lemma 2: Coarse card upper from sqrt-cover bound -/

/-- Derive `coarseP₀.card ≤ Δ^{-u-ε/2}` from Front sqrt-cover bound.
    Uses identity transfer √δ → Δ with factor K = 4^(u/2+εA_run),
    then absorbs 81·K. -/
lemma coarse_card_upper_from_front
    {n m : ℕ} {hnm : m ≤ n}
    {Δ δ_n δ u ε εA_run : ℝ}
    (hΔ_eq : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_pos : 0 < δ) (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq2 : δ_n = Δ^2)
    (hδ_leδn : δ ≤ δ_n) (hδ_n_le_4δ : δ_n ≤ 4 * δ)
    (hu_pos : 0 < u) (hu_le_two : u ≤ 2)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hεA_run_pos : 0 < εA_run)
    (hεA_run_le : εA_run ≤ 201 * ε / 10000)
    {P : Set Plane} {Pbar : Finset Plane}
    {Pfin : Finset Plane}
    {coarseP₀ : Finset (DSquare m)}
    (hPbar_sub_P : (Pbar : Set Plane) ⊆ P)
    (hNcover_sqrt : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA_run))))
    (swapped : Bool)
    (h_match_backward : ∀ q ∈ Pfin, ∃ p ∈
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set Plane)
       else (Pbar : Set Plane)), dist q p ≤ δ_n)
    (h_intersect : ∀ Q ∈ coarseP₀,
      ((Pfin : Set Plane) ∩ (Q.toSet : Set Plane)).Nonempty)
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (coarseP₀.card : ℝ) ≤ Real.rpow Δ (-u - ε / 2) := by
  let K : ℝ := (4 : ℝ)^(u / 2 + εA_run)
  have hK_nonneg : 0 ≤ K := by positivity
  have h_sqrt_reg_P : Metric.externalCoveringNumber Δ.toNNReal P ≤
      ENNReal.ofReal (K * Real.rpow Δ (-(u + 2 * εA_run))) :=
    sqrt_cover_to_delta_cover hδ_pos hδ_n_pos hΔ_pos hδ_n_eq2 hδ_leδn hδ_n_le_4δ hu_pos hεA_run_pos hNcover_sqrt
  let Ref_fin : Set Plane :=
    if swapped then (Pbar.image CoordinatePartition.swapCoords : Set Plane) else (Pbar : Set Plane)
  have h_sqrt_reg_Ref : Metric.externalCoveringNumber Δ.toNNReal Ref_fin ≤
      ENNReal.ofReal (K * Real.rpow Δ (-(u + 2 * εA_run))) :=
    B1BridgeWiring.wire_ncover_to_Ref swapped hPbar_sub_P h_sqrt_reg_P
  have hK_absorb : (81 : ℝ) * K ≤ Real.rpow Δ (-(ε / 2 - 2 * εA_run)) :=
    B1BridgeWiring.wire_coarse_K_absorb hΔ_pos hΔ_lt_one hε_pos hε_lt_one
      hεA_run_pos hεA_run_le hu_le_two h_small_eps
  have hεA_lt : 2 * εA_run < ε / 2 := by
    have h1 : εA_run ≤ 201 * ε / 10000 := hεA_run_le
    linarith
  exact B1BridgeWiring.b1_coarse_card_upper_K hΔ_eq hΔ_pos hΔ_lt_one hδ_n_pos (by rw [hδ_n_eq2] <;> nlinarith)
    hu_pos hε_pos hεA_run_pos hεA_lt hK_nonneg hK_absorb
    (h_match_backward := h_match_backward)
    (h_intersect := h_intersect)
    h_sqrt_reg_Ref

/-! ### Lemma 3: Per-square upper via Ref_fin injection (thin wrapper)

    Delegates to `b1_per_square_upper_via_ref`, constructing the swap-aware
    `Ref_fin` Finset from `Pbar` and `swapped`. -/

/-- Derive per-square upper bound `fibre(Q).card ≤ Δ^{-u-3ε/5}` by delegating
    to `b1_per_square_upper_via_ref`. Constructs swap-aware Ref_fin from Pbar. -/
lemma per_square_upper_from_front
    {n m : ℕ} {hnm : m ≤ n}
    {s C₁ : ℝ} {M : ℕ}
    (config : NiceConfig n s C₁ M)
    {Δ δ_n u ε εA_int : ℝ}
    (hΔ_eq : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hδ_n_eq2 : δ_n = Δ^2)
    (hε_pos : 0 < ε)
    (hεA_int_pos : 0 < εA_int)
    (hεA_int_le : εA_int ≤ 401 * ε / 10000)
    {Pbar : Finset Plane}
    {P_oriented : Set Plane}
    (hPbar_card : (Pbar.card : ℝ) ≤ 100 * Real.rpow δ_n (-u))
    (h_squares_meet : ∀ (q : DSquare n), q ∈ config.P₀ →
        ((q.toSet : Set Plane) ∩ P_oriented).Nonempty)
    (swapped : Bool)
    (hP_oriented_sub_Ref : P_oriented ⊆
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set Plane)
       else (Pbar : Set Plane)))
    (hRef_sset : IsDeltaSSet δ_n u (Real.rpow δ_n (-εA_int))
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set Plane)
       else (Pbar : Set Plane)))
    (hRef_sep : Set.Pairwise
      (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set Plane)
       else (Pbar : Set Plane))
      (fun p q => δ_n ≤ dist p q))
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    ∀ (Q : DSquare m), Q ∈ config.P₀.image (InductionConfigurations.containingSquare hnm) →
      ((config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) ≤
        Real.rpow Δ (-u - 3 * ε / 5) := by
  let csq := InductionConfigurations.containingSquare hnm
  by_cases h_nonempty : config.P₀.Nonempty
  · -- Nonempty case: delegate to b1_per_square_upper_via_ref
    let Ref_fin_finset : Finset Plane :=
      if swapped then Pbar.image CoordinatePartition.swapCoords else Pbar
    let Ref_fin : Set Plane := (Ref_fin_finset : Set Plane)
    have hRef_eq : Ref_fin =
        (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set Plane) else (Pbar : Set Plane)) := by
      simp [Ref_fin, Ref_fin_finset, Finset.coe_image] <;> aesop
    have hRef_card : Ref_fin_finset.card = Pbar.card := by
      unfold Ref_fin_finset
      split_ifs with h
      · exact Finset.card_image_of_injective _ CoordinatePartition.swapCoords_invol.injective
      · rfl
    have hP_oriented_sub_Ref' : P_oriented ⊆ Ref_fin := by
      rw [hRef_eq]; exact hP_oriented_sub_Ref
    have hRef_sset' : IsDeltaSSet δ_n u (Real.rpow δ_n (-εA_int)) Ref_fin := by
      rw [hRef_eq]; exact hRef_sset
    have hRef_sep' : Set.Pairwise Ref_fin (fun p q => δ_n ≤ dist p q) := by
      rw [hRef_eq]; exact hRef_sep
    let C_Pbar : ℝ := Real.rpow δ_n (-εA_int)
    have hC_Pbar_bound : C_Pbar ≤ Real.rpow δ_n (-εA_int) := by rfl
    have hpoint_int_run_gap : 2 * εA_int + ε / 4 ≤ 7 * ε / 20 := by
      have h1 : εA_int ≤ 401 * ε / 10000 := hεA_int_le
      linarith
    exact b1_per_square_upper_via_ref hnm config
      hΔ_pos hΔ_lt_one hδ_n_pos hδ_n_eq hδ_n_eq2 hΔ_eq
      (hRef_card := hRef_card) (hPbar_card := hPbar_card)
      (hRef_sset := hRef_sset') (hRef_sep := hRef_sep')
      (hP_oriented_sub_Ref := hP_oriented_sub_Ref')
      (h_squares_meet := h_squares_meet)
      (hC_Pbar_bound := hC_Pbar_bound)
      (hpoint_int_run_gap := hpoint_int_run_gap)
      (h_small := h_small_eps)
      (hconfig_P0_nonempty := h_nonempty)
  · -- Empty P₀: the image is empty, so the conclusion is vacuous
    intro Q hQ
    exfalso
    have h1 : Q ∈ config.P₀.image csq := hQ
    rcases Finset.mem_image.mp h1 with ⟨p, hp, _⟩
    exact h_nonempty ⟨p, hp⟩

end DirecretisedFurstenbergEstimate.FrontEndLemmas.B1FrontUpperBounds

module

/-
  NiceConfigToA1: Bridge from B1BridgeDecomposition to A1_Output.

  Consumes the fully-specified `B1BridgeDecomposition` package and
  delegates to the already-proved `b1_output_to_a1_output_exists`.

  This is a thin wrapper: every hypothesis of `b1_output_to_a1_output_exists`
  is extracted directly from a field of `b1` or from the NiceConfiguration.

  Whiteprint node: appendix_a_alternative / b1_to_a1_bridge
  Status: COMPLETE — no sorrys, conditional on B1BridgeDecomposition
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.UniformAppendixAAlternative
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Support
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA.NiceConfigToA1

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.CombiningTheorem (NiceConfiguration)
open DirecretisedFurstenbergEstimate.Phase2 (squareIndex)

abbrev Plane := EuclideanPlane

/-- Bridge: B1BridgeDecomposition → A1_Output.

    Unpacks the `B1BridgeDecomposition` package and calls
    `b1_output_to_a1_output_exists`. Every quantitative hypothesis
    (cardinality bounds, ball-growth, S-set transfers, absorption,
    geometry) is a field of `b1`.

    Inputs beyond `b1`:
    - Scale equalities and positivity
    - Exponent positivity/bounds
    - h_small numerical condition

    Note: requires `t < 2` (inherited from `b1_output_to_a1_output_exists`).
    The t=2 endpoint would require weakening the downstream theorem.
-/
def niceConfig_to_a1_output
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    {config : NiceConfiguration n s C₁ M}
    {Δ δ t ε : ℝ}
    (b1 : B1BridgeDecomposition n m hnm s C₁ M config Δ δ t ε)
    -- Scale equalities
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ)
    -- Exponents
    (ht : 0 < t) (ht_lt_two : t < 2)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    :
    A1_Output Δ δ t s ε := by
  have hδ_le_D : δ ≤ Δ := by
    rw [hδ_eq, hΔ_eq]
    have h_pos1 : 1 ≤ (2 : ℝ) := by norm_num
    have h1 : (2 : ℝ)^m ≤ (2 : ℝ)^n := by gcongr
    have h2 : 1 / (2 : ℝ)^n ≤ 1 / (2 : ℝ)^m := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact h1
    simpa [dyadicDelta] using h2

  -- Fine configuration: use config.tubeFamily directly
  -- (b1's geometric bounds are stated about config.tubeFamily)
  let fineP₀ := config.P₀
  let fineTubeFamily := config.tubeFamily

  have h_fine_sset' : ∀ p hp,
      IsDeltaSSet δ s C₁ (fineTubeFamily p hp : Set (DyadicTube n)) := by
    intro p hp
    have h : IsDeltaSSet (dyadicDelta n) s C₁ (fineTubeFamily p hp : Set (DyadicTube n)) :=
      config.h_delta_s_set p hp
    simpa [hδ_eq] using h

  have h_fine_size : ∀ p hp,
      (M / 2 : ℕ) ≤ (fineTubeFamily p hp).card ∧ (fineTubeFamily p hp).card ≤ M := by
    intro p hp
    have h_card : (fineTubeFamily p hp).card = M := config.h_size p hp
    rw [h_card]
    constructor
    · exact Nat.div_le_self M 2
    · linarith

  -- b1.hP_ball_growth already has constant Δ^{-9ε/4}, which is what we need.
  have h_ball_growth_weaken : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      (((config.P₀.image localSquareCenter).filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * ((config.P₀.image localSquareCenter).card : ℝ) := by
    intro c r hr
    exact b1.hP_ball_growth c r hr

  -- b1.hPfin_sset already has constant δ^{-2ε}, which is what we need.
  have hPfin_sset' : IsDeltaSSet δ t (Real.rpow δ (-2 * ε))
      ((config.P₀.image localSquareCenter) : Set Plane) :=
    b1.hPfin_sset

  -- Call the fully-proved bridge with all data extracted from b1
  exact b1_output_to_a1_output_exists
    (hnm := hnm)
    (hΔ_eq := hΔ_eq)
    (hδ_eq := hδ_eq)
    (hΔ_pos := hΔ_pos)
    (hΔ_lt_half := hΔ_lt_half)
    (hδ_pos := hδ_pos)
    (hδ_le_D := hδ_le_D)
    (ht := ht)
    (ht_lt_two := ht_lt_two)
    (hs := hs_pos)
    (hs_lt_one := hs_lt_one)
    (hε_pos := hε_pos)
    (h_small := h_small)
    (fineP₀ := fineP₀)
    (fineTubeFamily := fineTubeFamily)
    (C_fine := C₁)
    (hC_fine := b1.hC₁)
    (hC_fine_bound := b1.hC_fine_bound)
    (h_tube_sset_absorb := b1.h_tube_sset_absorb)
    (M_fine := M)
    (hM_fine := b1.hM)
    (hM_fine_even := b1.hM_even)
    (hM_fine_lower := b1.hM_fine_lower)
    (hM_fine_upper := b1.hM_fine_upper)
    (h_fine_sset := h_fine_sset')
    (h_fine_size := h_fine_size)
    (h_fine_inc := config.h_intersect)
    (coarseP₀ := b1.coarseP₀)
    (h_coarse_card_upper := b1.h_coarse_card_upper)
    (containingSquare := b1.containingSquare)
    (h_containing := b1.hContaining)
    (h_squareIndex_compat := b1.h_squareIndex_compat)
    (h_points_in_ball_R := b1.h_points_in_ball_R)
    (h_tubes_strip := b1.h_tubes_strip)
    (h_tubes_intercept := b1.h_tubes_intercept)
    (h_fine_card_lower := b1.h_fine_card_lower)
    (h_fine_card_upper := b1.h_fine_card_upper)
    (K_pack := b1.K_pack)
    (hK_pack_pos := b1.hK_pack_pos)
    (hK_pack_bound := b1.hK_pack_bound)
    (hP_ball_growth_data := h_ball_growth_weaken)
    (hPfin_sset := hPfin_sset')


/-- Equality: `P_all` of the A1 output equals the swapped centers from the nice configuration.

    This is the key identity needed for `h_points_in_ball'`: the ball bound
    on `config.P₀.image localSquareCenter` transfers to `a1.P_all` via
    `swapCoords` being an isometry. -/
lemma niceConfig_to_a1_output_P_all
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    {config : NiceConfiguration n s C₁ M}
    {Δ δ t ε : ℝ}
    (b1 : B1BridgeDecomposition n m hnm s C₁ M config Δ δ t ε)
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) (hδ_pos : 0 < δ)
    (ht : 0 < t) (ht_lt_two : t < 2)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (niceConfig_to_a1_output (hnm := hnm) (b1 := b1) hΔ_eq hδ_eq hΔ_pos hΔ_lt_half
       hδ_pos ht ht_lt_two hs_pos hs_lt_one hε_pos h_small).P_all =
    config.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) := by
  unfold niceConfig_to_a1_output b1_output_to_a1_output_exists A1_Assembly.a1_stage
  dsimp only
  rw [Finset.image_image]
  <;> rfl

/-- Projection: points from `niceConfig_to_a1_output` are subset of
    `config.P₀.image (swapCoords ∘ localSquareCenter)`. -/
lemma niceConfig_to_a1_output_points_subset
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    {config : NiceConfiguration n s C₁ M}
    {Δ δ t ε : ℝ}
    (b1 : B1BridgeDecomposition n m hnm s C₁ M config Δ δ t ε)
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) (hδ_pos : 0 < δ)
    (ht : 0 < t) (ht_lt_two : t < 2)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    ∀ (Q : CoarseSquare Δ)
      (hQ : Q ∈ (niceConfig_to_a1_output (hnm := hnm) (b1 := b1) hΔ_eq hδ_eq hΔ_pos hΔ_lt_half
         hδ_pos ht ht_lt_two hs_pos hs_lt_one hε_pos h_small).Qset),
      ((niceConfig_to_a1_output (hnm := hnm) (b1 := b1) hΔ_eq hδ_eq hΔ_pos hΔ_lt_half
         hδ_pos ht ht_lt_two hs_pos hs_lt_one hε_pos h_small).points Q hQ : Set Plane)
      ⊆ (config.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set Plane) := by
  let a1 := niceConfig_to_a1_output (hnm := hnm) (b1 := b1) hΔ_eq hδ_eq hΔ_pos hΔ_lt_half
    hδ_pos ht ht_lt_two hs_pos hs_lt_one hε_pos h_small
  have h_sub : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆ (a1.P_all : Set Plane) := a1.h_points_sub_all
  have h_eq : a1.P_all = config.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) :=
    niceConfig_to_a1_output_P_all (hnm := hnm) (b1 := b1) hΔ_eq hδ_eq hΔ_pos hΔ_lt_half
      hδ_pos ht ht_lt_two hs_pos hs_lt_one hε_pos h_small
  intro Q hQ
  have h := h_sub Q hQ
  rw [h_eq] at h
  exact h

end DirecretisedFurstenbergEstimate.AppendixA.NiceConfigToA1

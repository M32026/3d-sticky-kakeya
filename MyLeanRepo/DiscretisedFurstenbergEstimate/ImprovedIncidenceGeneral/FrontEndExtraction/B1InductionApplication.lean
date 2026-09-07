module

/-
  B1 Induction Application — Construct B1BridgeDecomposition.

  Applies the B1 induction-on-scales bridge to a NiceConfiguration and
  packages the output into the B1BridgeDecomposition structure.

  Key proved fields:
  - h_squareIndex_compat: floor((i+1/2)/r) = floor(i/r) for r ≥ 1
  - origTubeFamily := config.tubeFamily (no thinning)
  - All structural fields from explicit hypotheses

  Quantitative bounds (cardinality, ball growth, M bounds, K absorption)
  are taken as explicit hypotheses since they require the multiscale
  decomposition and uniformization infrastructure.

  Whiteprint node: b1_induction_application
  Dependencies: B1Integration, UniformAppendixAAlternative
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.UniformAppendixAAlternative
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Support
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.Phase2
open InductionConfigurations

/-- Prove h_squareIndex_compat: floor((i+1/2)/r) = i/r (integer division) for r ≥ 1.

    Uses integer division: for any `a : ℤ` and positive `r : ℕ`,
    `floor((a + 1/2) / r) = a / r` because the remainder `a % r` satisfies
    `0 ≤ a % r < r`, so `(a % r + 1/2) / r ∈ (0, 1)`. -/
lemma square_index_compat_lemma {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) :
    squareIndex (dyadicDelta m) (localSquareCenter p) =
      ((InductionConfigurations.containingSquare hnm p).i,
       (InductionConfigurations.containingSquare hnm p).j) := by
  let r : ℕ := InductionConfigurations.refinementFactor n m
  have hr_pos : 0 < r := by
    dsimp only [r, InductionConfigurations.refinementFactor]
    positivity
  have hr_pos_int : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr_pos
  -- Key identity: floor((a + 1/2) / r) = a / r for integer a, positive r
  have h_main : ∀ (a : ℤ), ⌊((a : ℝ) + 1 / 2) / (r : ℝ)⌋ = a / r := by
    intro a
    set q : ℤ := a / r with hq_def
    set rem : ℤ := a % r with hrem_def
    have hrem_nonneg : 0 ≤ rem := Int.emod_nonneg a hr_pos_int.ne'
    have hrem_lt : rem < (r : ℤ) := Int.emod_lt_of_pos a hr_pos_int
    have hrem_le : rem ≤ (r : ℤ) - 1 := by omega
    have h_eq : (a : ℝ) = (q : ℝ) * (r : ℝ) + (rem : ℝ) := by
      have h : a = q * r + rem := by
        dsimp only [q, rem]
        have h' : (a / (r : ℤ)) * (r : ℤ) + (a % (r : ℤ)) = a :=
          Int.ediv_mul_add_emod a (r : ℤ)
        exact h'.symm
      exact_mod_cast h
    have hpos : 0 < (r : ℝ) := by exact_mod_cast hr_pos
    have h_lower : (q : ℝ) ≤ (((a : ℝ) + 1 / 2) / (r : ℝ)) := by
      rw [h_eq]
      have h : (((q : ℝ) * (r : ℝ) + (rem : ℝ) + 1 / 2) / (r : ℝ)) =
          (q : ℝ) + (((rem : ℝ) + 1 / 2) / (r : ℝ)) := by
        field_simp [hpos.ne'] <;> ring
      rw [h]
      have h2 : 0 ≤ ((rem : ℝ) + 1 / 2) / (r : ℝ) := by positivity
      linarith
    have hrem_real_lt : (rem : ℝ) + 1 / 2 < (r : ℝ) := by
      have h4 : (rem : ℝ) ≤ ((r : ℤ) - 1 : ℝ) := by exact_mod_cast hrem_le
      simp at h4 ⊢ <;> linarith
    have h_upper : (((a : ℝ) + 1 / 2) / (r : ℝ)) < (q : ℝ) + 1 := by
      rw [h_eq]
      have h : (((q : ℝ) * (r : ℝ) + (rem : ℝ) + 1 / 2) / (r : ℝ)) =
          (q : ℝ) + (((rem : ℝ) + 1 / 2) / (r : ℝ)) := by
        field_simp [hpos.ne'] <;> ring
      rw [h]
      have h3 : ((rem : ℝ) + 1 / 2) / (r : ℝ) < 1 := by
        calc ((rem : ℝ) + 1 / 2) / (r : ℝ)
          < (r : ℝ) / (r : ℝ) := by gcongr
          _ = 1 := by field_simp [hpos.ne'] <;> ring
      linarith
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast h_lower, by exact_mod_cast h_upper⟩
  have h_r_eq : (r : ℝ) = (2 : ℝ) ^ (n - m) := by
    simp [r, InductionConfigurations.refinementFactor]
  have hnm' : (n : ℤ) = (m : ℤ) + ((n - m : ℕ) : ℤ) := by omega
  have hδ_n : dyadicDelta n = dyadicDelta m / (r : ℝ) := by
    have h1 : dyadicDelta n = (2 : ℝ) ^ (-(n : ℤ)) := by simp [dyadicDelta]
    have h2 : dyadicDelta m = (2 : ℝ) ^ (-(m : ℤ)) := by simp [dyadicDelta]
    rw [h1, h2, h_r_eq]
    let k : ℕ := n - m
    have hk : n = m + k := by omega
    have hk' : (n : ℤ) = (m : ℤ) + (k : ℤ) := by exact_mod_cast hk
    have h3 : (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-(m : ℤ)) / (2 : ℝ) ^ (k : ℤ) := by
      rw [hk']
      have h4 : -((m : ℤ) + (k : ℤ)) = (-(m : ℤ)) - (k : ℤ) := by ring
      rw [h4, zpow_sub₀] <;> norm_num
    exact h3
  have h0 : (localSquareCenter p) 0 = ((p.i : ℝ) + 1 / 2) * dyadicDelta n := by
    simp [localSquareCenter] <;> norm_num
  have h1 : (localSquareCenter p) 1 = ((p.j : ℝ) + 1 / 2) * dyadicDelta n := by
    simp [localSquareCenter] <;> norm_num
  have h2 : ((localSquareCenter p) 0) / dyadicDelta m = ((p.i : ℝ) + 1 / 2) / (r : ℝ) := by
    rw [h0, hδ_n] <;> field_simp [dyadicDelta_pos m |>.ne'] <;> ring
  have h3 : ((localSquareCenter p) 1) / dyadicDelta m = ((p.j : ℝ) + 1 / 2) / (r : ℝ) := by
    rw [h1, hδ_n] <;> field_simp [dyadicDelta_pos m |>.ne'] <;> ring
  have h4 : (InductionConfigurations.containingSquare hnm p).i = p.i / r := by
    simp [InductionConfigurations.containingSquare, r,
      InductionConfigurations.refinementFactor]
    <;> rfl
  have h5 : (InductionConfigurations.containingSquare hnm p).j = p.j / r := by
    simp [InductionConfigurations.containingSquare, r,
      InductionConfigurations.refinementFactor]
    <;> rfl
  simp only [squareIndex, h2, h3]
  rw [h_main p.i, h_main p.j, h4, h5]

/-- Construct B1BridgeDecomposition from explicit data.

    This packages the B1 bridge structural output with quantitative bounds
    from the multiscale decomposition into the B1BridgeDecomposition
    structure required by uniform_appendix_A_alternative. -/
def b1_induction_application
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C₁ M)
    {Δ δ t ε : ℝ}
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    -- Geometric hypotheses
    (h_points_in_ball_R : (config.P₀.image localSquareCenter : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2))
    (h_tubes_strip : ∀ (T : DyadicTube n), T ∈ config.T₀ →
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16 ^ n)
    -- hM_even
    (hM_even : M % 2 = 0)
    -- Quantitative hypotheses (from multiscale decomposition)
    (hP_ball_growth : ∀ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), Δ ≤ r →
      (((config.P₀.image localSquareCenter).filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * ((config.P₀.image localSquareCenter).card : ℝ))
    (hPfin_sset : IsDeltaSSet δ t (Real.rpow δ (-2 * ε))
      ((config.P₀.image localSquareCenter) : Set (EuclideanSpace ℝ (Fin 2))))
    (h_fine_card_lower : Real.rpow Δ (-2 * t + ε / 4) ≤ (config.P₀.card : ℝ))
    (h_fine_card_upper : (config.P₀.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4))
    (hC_fine_bound : C₁ ≤ Real.rpow δ (-ε / 2))
    (hC₁ : 1 ≤ C₁)
    (h_tube_sset_absorb : (4000 : ℝ) * 44^s ≤ Real.rpow δ (-ε / 2))
    (hM_fine_lower : (M : ℝ) / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε))
    (hM_fine_upper : (M : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    -- K_pack
    (K_pack : ℝ) (hK_pack_pos : 0 < K_pack)
    (hK_pack_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    -- Coarse/per-square structural data
    (coarseP₀ : Finset (DyadicSquare m))
    (containingSquare : DyadicSquare n → DyadicSquare m)
    (hCoarse_eq : coarseP₀ = config.P₀.image containingSquare)
    (hContaining : ∀ p ∈ config.P₀, containingSquare p ∈ coarseP₀)
    (h_containingSquare_eq : containingSquare = InductionConfigurations.containingSquare hnm)
    (h_coarse_card_lower : Real.rpow Δ (-t + ε) ≤ (coarseP₀.card : ℝ))
    (h_coarse_card_upper : (coarseP₀.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2))
    (h_per_square_lower : ∀ Q ∈ coarseP₀,
      Real.rpow Δ (-t + ε) ≤ ((config.P₀.filter (fun p => containingSquare p = Q)).card : ℝ))
    (h_per_square_upper : ∀ Q ∈ coarseP₀,
      ((config.P₀.filter (fun p => containingSquare p = Q)).card : ℝ) ≤ Real.rpow Δ (-t - ε))
    -- Tube intercept bound
    (h_tubes_intercept : ∀ (p : DyadicSquare n) (hp : p ∈ config.P₀) (T : DyadicTube n),
      T ∈ config.tubeFamily p hp → |T.intercept| ≤ 3) :
    B1BridgeDecomposition n m hnm s C₁ M config Δ δ t ε := by
  have hM_pos : 0 < M := by
    have hΔ_pos : 0 < Δ := by
      rw [hΔ_eq]
      exact dyadicDelta_pos m
    have h_card_pos : 0 < (config.P₀.card : ℝ) := by
      have h_pos : 0 < Real.rpow Δ (-2 * t + ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
      exact lt_of_lt_of_le h_pos h_fine_card_lower
    have h : 0 < config.P₀.card := by exact_mod_cast h_card_pos
    have hP_nonempty : config.P₀.Nonempty := Finset.card_pos.mp h
    rcases hP_nonempty with ⟨p, hp⟩
    have h_ds : IsDeltaSSet (dyadicDelta n) s C₁ (config.tubeFamily p hp : Set (DyadicTube n)) :=
      config.h_delta_s_set p hp
    have h_tube_nonempty : (config.tubeFamily p hp : Set (DyadicTube n)).Nonempty := h_ds.1
    have h_finset_nonempty : (config.tubeFamily p hp).Nonempty := by
      simpa [Finset.Nonempty] using h_tube_nonempty
    have h_card_pos2 : 0 < (config.tubeFamily p hp).card := Finset.Nonempty.card_pos h_finset_nonempty
    have h_size_eq : (config.tubeFamily p hp).card = M := config.h_size p hp
    rw [h_size_eq] at h_card_pos2
    exact h_card_pos2
  exact {
    coarseP₀ := coarseP₀
    containingSquare := containingSquare
    hCoarse_eq := hCoarse_eq
    hContaining := hContaining
    h_squareIndex_compat := fun p _ => by
      have h := square_index_compat_lemma hnm p
      simpa [hΔ_eq, h_containingSquare_eq] using h
    K := 1
    hK := by norm_num
    origTubeFamily := config.tubeFamily
    hTube_sub := fun _ _ => by rfl
    hTube_size_orig := config.h_size
    hTube_sset_orig := config.h_delta_s_set
    hTube_inc_orig := config.h_intersect
    hM := hM_pos
    hM_even := hM_even
    K_pack := K_pack
    hK_pack_pos := hK_pack_pos
    hK_pack_bound := hK_pack_bound
    hP_ball_growth := hP_ball_growth
    hPfin_sset := hPfin_sset
    h_fine_card_lower := h_fine_card_lower
    h_fine_card_upper := h_fine_card_upper
    h_coarse_card_lower := h_coarse_card_lower
    h_coarse_card_upper := h_coarse_card_upper
    h_per_square_lower := h_per_square_lower
    h_per_square_upper := h_per_square_upper
    hC_fine_bound := hC_fine_bound
    hC₁ := hC₁
    h_tube_sset_absorb := h_tube_sset_absorb
    h_points_in_ball_R := h_points_in_ball_R
    h_tubes_strip := fun p hp T hT => h_tubes_strip T (config.h_subset p hp hT)
    h_tubes_intercept := h_tubes_intercept
    hM_fine_lower := hM_fine_lower
    hM_fine_upper := hM_fine_upper
  }

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

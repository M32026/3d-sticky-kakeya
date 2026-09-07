module

/-
  Same-Q Chain Cancellation Helper (CLEAN)

  Provides the factor-9 cancellation lemma WITHOUT Prop73 contamination.
  Uses only RetainedRegularityClean.lean, GeometricIntersection.lean, and
  RegularIncidence.Definitions.

  Main lemma: coarse_card_delta_m_u_cancellation_clean
    card(P_coarse) * δ_m^u ≤ 9 * K_P

  Proof route:
  1. finset_intersecting_squares_bound_clean: |P_coarse| ≤ 9 * Ncover(δ_m, E)
     whenever every square in P_coarse intersects E
  2. Apply with E = config.pointSet (each coarse square contains a fine square
     from config.P₀, hence intersects config.pointSet)
  3. Even scale: δ_m = √δ_n
  4. IsSquareRootRegular: Ncover(√δ_n, pointSet) ≤ K_P * δ_n^{-u/2} = K_P * δ_m^{-u}
  5. Multiply by δ_m^u

  Whiteprint node: c_ret_cancellation_clean
  Status: IMPLEMENTED (no Prop73 imports)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.RetainedRegularityClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open InductionConfigurations

/-- Factor-9 cancellation (CLEAN): in the even-scale case, the coarse parent
    count times δ_m^u is bounded by 9 * K_P, given square-root regularity
    with exponent u on the original config.pointSet.

    Uses only clean modules (no Prop73 contamination).

    P_coarse need only be a subset of config.P₀.image(containingSquare). -/
lemma coarse_card_delta_m_u_cancellation_clean
    {n m : ℕ} (hnm : n = 2 * m)
    {s C₁ : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C₁ M)
    {u C_P K_P : ℝ}
    (hReg : IsSquareRootRegular (dyadicDelta n) u C_P K_P config.pointSet)
    (hK_P_pos : 0 < K_P)
    {P_coarse : Finset (DyadicSquare m)}
    (h_coarse_sub : P_coarse ⊆
        config.P₀.image (InductionConfigurations.containingSquare (by omega))) :
    (P_coarse.card : ℝ) * (dyadicDelta m)^u ≤ 9 * K_P := by
  let δ_n := dyadicDelta n
  let δ_m := dyadicDelta m
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδm_pos : 0 < δ_m := dyadicDelta_pos m
  have hnm' : m ≤ n := by omega

  -- Each coarse square in P_coarse intersects config.pointSet
  have h_intersect : ∀ (p : DyadicSquare m), p ∈ P_coarse →
      ((p.toSet : Set Plane) ∩ config.pointSet).Nonempty := by
    intro p hp
    have h1 : p ∈ config.P₀.image (InductionConfigurations.containingSquare hnm') :=
      h_coarse_sub hp
    rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
    let Q := InductionConfigurations.containingSquare hnm' q
    have h_cont : squareContained hnm' q Q :=
      (InductionConfigurations.containingSquare_iff hnm' q Q).mp rfl
    have hq_sub : (q.toSet : Set Plane) ⊆ (Q.toSet : Set Plane) :=
      DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm' h_cont
    have hq_in_pointSet : (q.toSet : Set Plane) ⊆ config.pointSet := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨q, hq, hx⟩
    have hq_nonempty : (q.toSet : Set Plane).Nonempty := DyadicSquare.toSet_nonempty q
    exact hq_nonempty.mono (fun x hx => ⟨hq_sub hx, hq_in_pointSet hx⟩)

  -- Step 1: |P_coarse| ≤ 9 * Ncover(δ_m, config.pointSet)
  have h_card_bound : (P_coarse.card : ENNReal) ≤
      (9 : ENNReal) * Ncover δ_m config.pointSet :=
    finset_intersecting_squares_bound_clean h_intersect

  -- Step 2: δ_n = δ_m^2
  have hδ_n_eq : δ_n = δ_m^2 := by
    dsimp only [δ_n, δ_m, dyadicDelta]
    have h2 : n = 2 * m := hnm
    have h3 : (2 : ℝ)^n = (2 : ℝ)^(2 * m) := by rw [h2]
    have h4 : (2 : ℝ)^(2 * m) = ((2 : ℝ)^m)^2 := by
      rw [show (2 * m) = m + m by ring, pow_add] <;> ring
    have h5 : (1 : ℝ) / (2 : ℝ)^n = (1 : ℝ) / (((2 : ℝ)^m)^2) := by rw [h3, h4]
    simpa using h5

  -- Step 3: δ_m = √δ_n
  have hδ_m_eq_sqrt : δ_m = Real.sqrt δ_n := by
    rw [hδ_n_eq]
    rw [Real.sqrt_sq (by positivity)]

  -- Step 4: δ_n^{-u/2} = δ_m^{-u}
  have h_rpow_eq : Real.rpow δ_n (-u / 2) = Real.rpow δ_m (-u) := by
    have h1 : δ_n = δ_m^2 := hδ_n_eq
    rw [h1]
    have h2 : Real.rpow (δ_m^2) (-u / 2) = Real.rpow δ_m (-u) := by
      have h3 : ∀ (x : ℝ), 0 < x → Real.rpow (x^2) (-u / 2) = Real.rpow x (-u) := by
        intro x hx
        have h4 : Real.rpow (x^2) (-u / 2) = Real.rpow x ((2 : ℝ) * (-u / 2)) := by
          have h5 : (x^2 : ℝ) = x ^ (2 : ℝ) := by norm_cast
          rw [h5]
          exact (Real.rpow_mul hx.le (2 : ℝ) (-u / 2)).symm
        rw [h4]
        have h6 : (2 : ℝ) * (-u / 2) = -u := by ring
        rw [h6]
      exact h3 δ_m hδm_pos
    exact h2

  -- Step 5: Ncover(δ_m, pointSet) ≤ K_P * δ_m^{-u}
  have h_sqrt_eq : Real.sqrt δ_n = δ_m := hδ_m_eq_sqrt.symm
  have h_ncover_bound : Ncover δ_m config.pointSet ≤
      ENNReal.ofReal (K_P * Real.rpow δ_m (-u)) := by
    have h1 : Ncover (Real.sqrt δ_n) config.pointSet ≤
        ENNReal.ofReal (K_P * Real.rpow δ_n (-u / 2)) := hReg.2
    have h2 : K_P * Real.rpow δ_n (-u / 2) = K_P * Real.rpow δ_m (-u) := by
      rw [h_rpow_eq]
    rw [h2] at h1
    have h4 : K_P * Real.rpow (Real.sqrt δ_n) (-u) = K_P * Real.rpow δ_m (-u) := by
      rw [h_sqrt_eq]
    have h5 : Ncover (Real.sqrt δ_n) config.pointSet ≤
        ENNReal.ofReal (K_P * Real.rpow (Real.sqrt δ_n) (-u)) := by
      rw [h4]; exact h1
    have h6 : δ_m = Real.sqrt δ_n := hδ_m_eq_sqrt
    rw [h6]
    exact h5

  -- Step 6: combine to get card ≤ 9 * K_P * δ_m^{-u}
  have h_rpow_nonneg : 0 ≤ Real.rpow δ_m (-u) := Real.rpow_nonneg hδm_pos.le _
  have h_KP_nonneg : 0 ≤ K_P := hK_P_pos.le
  have h_pos3 : 0 ≤ 9 * K_P * Real.rpow δ_m (-u) :=
    mul_nonneg (mul_nonneg (by norm_num) h_KP_nonneg) h_rpow_nonneg

  have h9 : (P_coarse.card : ENNReal) ≤
      ENNReal.ofReal (9 * K_P * Real.rpow δ_m (-u)) := by
    calc (P_coarse.card : ENNReal)
      ≤ (9 : ENNReal) * Ncover δ_m config.pointSet := h_card_bound
    _ ≤ (9 : ENNReal) * ENNReal.ofReal (K_P * Real.rpow δ_m (-u)) := by gcongr
    _ = ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal (K_P * Real.rpow δ_m (-u)) := by
      norm_cast
    _ = ENNReal.ofReal ((9 : ℝ) * (K_P * Real.rpow δ_m (-u))) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
    _ = ENNReal.ofReal (9 * K_P * Real.rpow δ_m (-u)) := by
      have h_eq : (9 : ℝ) * (K_P * Real.rpow δ_m (-u)) = 9 * K_P * Real.rpow δ_m (-u) := by ring
      rw [h_eq]

  have h10 : (P_coarse.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top P_coarse.card
  have h11 : ENNReal.ofReal (9 * K_P * Real.rpow δ_m (-u)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h12 : ((P_coarse.card : ENNReal).toReal) ≤
      (ENNReal.ofReal (9 * K_P * Real.rpow δ_m (-u))).toReal :=
    ENNReal.toReal_le_toReal h10 h11 |>.mpr h9
  have h13 : ((P_coarse.card : ENNReal).toReal) = (P_coarse.card : ℝ) := by simp
  have h14 : (ENNReal.ofReal (9 * K_P * Real.rpow δ_m (-u))).toReal =
      9 * K_P * Real.rpow δ_m (-u) := by
    rw [ENNReal.toReal_ofReal h_pos3]
  rw [h13, h14] at h12

  -- Step 7: multiply by δ_m^u
  have h_rpow_pos_u : 0 < Real.rpow δ_m u := Real.rpow_pos_of_pos hδm_pos u
  have h15 : Real.rpow δ_m (-u) * Real.rpow δ_m u = 1 := by
    have h_add : Real.rpow δ_m ((-u : ℝ) + u) = Real.rpow δ_m (-u) * Real.rpow δ_m u :=
      Real.rpow_add hδm_pos (-u) u
    have h_eq : Real.rpow δ_m (-u) * Real.rpow δ_m u = Real.rpow δ_m ((-u : ℝ) + u) := h_add.symm
    rw [h_eq]
    have h16 : (-u : ℝ) + u = 0 := by ring
    rw [h16]
    exact Real.rpow_zero δ_m
  calc (P_coarse.card : ℝ) * Real.rpow δ_m u
    ≤ (9 * K_P * Real.rpow δ_m (-u)) * Real.rpow δ_m u := by gcongr
  _ = 9 * K_P * (Real.rpow δ_m (-u) * Real.rpow δ_m u) := by ring
  _ = 9 * K_P := by rw [h15] <;> ring

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end

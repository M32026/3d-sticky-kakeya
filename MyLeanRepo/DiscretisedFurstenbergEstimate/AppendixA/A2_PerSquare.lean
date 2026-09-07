module

/-
  A2 Per-Square: Per-square QTTC + H2.

  Extracts the large `a2_per_square` definition from A2_Main to avoid
  an isDefEq timeout when compiling the entire module.

  Whiteprint node: appendix_a_alternative / A2_Main
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_TypedQTTC_Adapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_PointFiberUpper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_StripPacking
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Gaps
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Main
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA.A2

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.QTTC_Assembly
open DirecretisedFurstenbergEstimate.AppendixA.A2_RemainingGaps
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
open DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
open DirecretisedFurstenbergEstimate.AppendixA4

/-- Apply QTTC to a single square's configuration and produce A2_SquareData. -/
def a2_per_square
    {Δ δ s t ε M K_pack : ℝ}
    {Q : CoarseSquare Δ}
    {P : Finset Plane} {T : Plane → Finset FineTube}
    {A : ℝ}
    (n m0 : ℕ)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_eq : Δ = dyadicDelta m0)
    (hnm : m0 ≤ n)
    (hm_pos : 1 ≤ m0)
    (hQTTC : ∀ {n m : ℕ} {δ Δ C₁ : ℝ} {M : ℕ}
      {P : Finset Plane} {T : Plane → Finset AffineLine},
      (hδ_eq : δ = dyadicDelta n) →
      (hΔ_eq : Δ = dyadicDelta m) →
      (hnm : m ≤ n) → (hm_pos : 1 ≤ m) →
      1 ≤ C₁ → P.Nonempty → 0 < M →
      (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
      (∀ p ∈ P, BallGrowth δ s C₁ (T p)) →
      (∀ p ∈ P, SeparatedAt (δ / 2) ((T p) : Set AffineLine)) →
      (∀ p ∈ P, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3) →
      (R : ℝ) →
      (hR : R ≤ Real.sqrt 2) →
      (∀ p ∈ P, |p 1| ≤ R) →
      (hδ_le_quarter_Delta : δ ≤ Δ / 4) →
      (∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) →
      ∃ (P' : Finset Plane) (T' : Plane → Finset AffineLine)
        (C' : Finset AffineLine) (K C₂ : ℝ) (H : ℕ),
        1 ≤ K ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
        1 ≤ C₂ ∧ 0 < H ∧
        P' ⊆ P ∧
        (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
        (∀ p ∈ P', T' p ⊆ T p) ∧
        (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
        _root_.IsFiniteDeltaSSet Δ s C₂ C' ∧
        IsDeltaSSet Δ s (max 1 (C_PACK * C₂)) (C' : Set AffineLine) ∧
        C₂ ≤ A * Real.rpow K A * C₁ ∧
        (∀ c ∈ C', |tubeSlope c| ≤ 1) ∧
        (∀ c ∈ C', (LemmaE.getDirV c) 1 ≠ 0) ∧
        (∀ c ∈ C', |tubeIntercept c| ≤ 3) ∧
        (∀ c ∈ C', ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ) ∧
        -- Exact-parent provenance via composite:
        -- ell → snapTube n ell → sp hnm → dyadicTubeToA2 = c
        (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
          (hell : ell ∈ T' p) (U : DyadicTube m),
          sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C',
          (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T' p c).card) ∧
        (∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C',
          (pointFiber Δ hΔ_pos T' p c).card ≤
            C₁ * (6 : ℝ)^s * (T p).card * Δ^s) ∧
        (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'.card : ℝ) ∧
        (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ))
    (h_small : A2_Smallness Δ δ s t ε A K_pack M)
    (hP_nonempty : P.Nonempty)
    (hP_in_square : (P : Set Plane) ⊆ squareSet Δ Q)
    (R : ℝ)
    (hR : R ≤ Real.sqrt 2)
    (hP_in_ball : (P : Set Plane) ⊆ Metric.closedBall 0 R)
    (hP_separated : SeparatedAt δ (P : Set Plane))
    (hP_card_lower : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ))
    (hP_card_lower_strong : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ))
    (hP_card_upper : (P.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε))
    (C_P : ℝ)
    (hP_sset : IsDeltaSSet δ t C_P (P : Set Plane))
    (hC_P_bound : C_P * 81 ≤ Real.rpow Δ (-t - 8 * ε))
    (hs_pos : 0 < s)
    (hs1 : s < 1)
    (hM_pos : 0 < M)
    (hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack)
    (hM_upper : M ≤ 2 * Real.rpow Δ (-2 * s - ε))
    (h_tubes_card : ∀ p ∈ P, (M / 2 : ℝ) ≤ (T p).card ∧ (T p).card ≤ M)
    (h_tubes_sset : ∀ p ∈ P,
      IsDeltaSSet δ s (max 1 (K_pack * Real.rpow δ (-ε))) (T p : Set FineTube))
    (h_tubes_separated : ∀ p ∈ P, SeparatedAt (δ / 2) (T p : Set FineTube))
    (h_slope_bound : ∀ p ∈ P, ∀ ℓ ∈ T p,
      (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3)
    (h_inc : ∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1)
    (hδ_le_quarter_Delta : δ ≤ Δ / 4)
    -- Global coarse cover and proof that QTTC output C' is contained in it
    (T_Delta_global : Finset CoarseTube)
    (h_prove_sub : ∀ (P' : Finset Plane) (T' : Plane → Finset AffineLine) (C' : Finset AffineLine),
      P' ⊆ P →
      (∀ p ∈ P', T' p ⊆ T p) →
      (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
        (hell : ell ∈ T' p) (U : DyadicTube m0),
        sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) →
      (C' : Set CoarseTube) ⊆ (T_Delta_global : Set CoarseTube))
    (hδ_pos : 0 < δ) :
    A2_SquareData Δ δ s t ε Q := by
  -- Step 1: Dyadic refinement to satisfy strict M/2 < card
  let m_ceil : ℕ := Nat.ceil M
  have hm_ge2 : 2 ≤ m_ceil := by
    have h1 : 2 ≤ M := by linarith [hM_lower, h_small.hM_large]
    have h2 : (M : ℝ) ≤ (m_ceil : ℝ) := Nat.le_ceil M
    have h3 : (2 : ℝ) ≤ (m_ceil : ℝ) := by linarith
    exact_mod_cast h3
  have hM_gt_m_minus1 : (m_ceil : ℝ) - 1 < M := by
    by_contra h2
    have h3 : M ≤ (m_ceil : ℝ) - 1 := by linarith
    have h4 : 1 ≤ m_ceil := by linarith [hm_ge2]
    have h5 : ((m_ceil - 1 : ℕ) : ℝ) = (m_ceil : ℝ) - 1 := by
      rw [Nat.cast_sub h4] <;> simp
    have h6 : M ≤ ((m_ceil - 1 : ℕ) : ℝ) := by
      rw [h5] <;> exact h3
    have h7 : m_ceil ≤ m_ceil - 1 := Nat.ceil_le.mpr h6
    omega
  let P_hi := P.filter (fun p => (T p).card > m_ceil / 2)
  let P_lo := P.filter (fun p => (T p).card ≤ m_ceil / 2)
  have hP_union : P_hi ∪ P_lo = P := by
    ext x
    simp only [P_hi, P_lo, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      by_cases h : (T x).card > m_ceil / 2
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, by omega⟩
  have hP_disj : Disjoint P_hi P_lo := by
    simp [P_hi, P_lo, Finset.disjoint_left] <;> omega
  have h_card_split : P_hi.card + P_lo.card = P.card := by
    rw [← Finset.card_union_of_disjoint hP_disj, hP_union]
  -- Key fact: for p ∈ P_lo, (T p).card = m_ceil / 2
  have h_lo_card : ∀ p ∈ P_lo, (T p).card = m_ceil / 2 := by
    intro p hp
    have h_in_P : p ∈ P := (Finset.mem_filter.mp hp).1
    have h_le : (T p).card ≤ m_ceil / 2 := (Finset.mem_filter.mp hp).2
    have h_ge : (M / 2 : ℝ) ≤ ((T p).card : ℝ) := by
      exact_mod_cast (h_tubes_card p h_in_P).1
    have h4 : ((m_ceil : ℝ) - 1) / 2 < M / 2 := by
      have h41 : (m_ceil : ℝ) - 1 < M := hM_gt_m_minus1
      have h42 : ((m_ceil : ℝ) - 1) / 2 < M / 2 := by
        gcongr <;> norm_num
      exact h42
    have h5 : ((m_ceil : ℝ) - 1) / 2 < ((T p).card : ℝ) := by
      calc ((m_ceil : ℝ) - 1) / 2 < M / 2 := h4
        _ ≤ ((T p).card : ℝ) := h_ge
    by_cases h_even : m_ceil % 2 = 0
    · -- m_ceil even
      have hmk : m_ceil = 2 * (m_ceil / 2) := by omega
      have h6 : ((m_ceil / 2 : ℕ) : ℝ) - 1 / 2 < ((T p).card : ℝ) := by
        have h_eq : ((m_ceil : ℝ) - 1) / 2 = ((m_ceil / 2 : ℕ) : ℝ) - 1 / 2 := by
          rw [show (m_ceil : ℝ) = 2 * ((m_ceil / 2 : ℕ) : ℝ) from by exact_mod_cast hmk]
          <;> ring_nf <;> field_simp <;> ring
        rw [h_eq] at h5
        exact h5
      have h7 : m_ceil / 2 ≤ (T p).card := by
        by_contra h8
        have h9 : (T p).card + 1 ≤ m_ceil / 2 := by omega
        have h10 : ((T p).card : ℝ) + 1 ≤ ((m_ceil / 2 : ℕ) : ℝ) := by
          exact_mod_cast h9
        linarith
      omega
    · -- m_ceil odd
      have hmk : m_ceil = 2 * (m_ceil / 2) + 1 := by omega
      have h_eq : ((m_ceil : ℝ) - 1) / 2 = ((m_ceil / 2 : ℕ) : ℝ) := by
        rw [show (m_ceil : ℝ) = 2 * ((m_ceil / 2 : ℕ) : ℝ) + 1 from by exact_mod_cast hmk]
        <;> ring_nf <;> field_simp <;> ring
      rw [h_eq] at h5
      have h6 : ((m_ceil / 2 : ℕ) : ℝ) < ((T p).card : ℝ) := h5
      have h7 : m_ceil / 2 < (T p).card := by exact_mod_cast h6
      omega
  by_cases hP_hi_large : P_hi.card * 2 ≥ P.card
  · -- Case P_hi is large enough
    have hP_hi_nonempty : P_hi.Nonempty := by
      by_contra h
      have h_empty : P_hi = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [h_empty] at hP_hi_large
      have h0 : P.card = 0 := by simpa using hP_hi_large
      have h1 : P = ∅ := by
        simpa [Finset.card_eq_zero] using h0
      exact Finset.nonempty_iff_ne_empty.mp hP_nonempty h1
    let M_qttc : ℕ := m_ceil
    have hM_qttc_pos : 0 < M_qttc := by linarith
    have h_lower : ∀ p ∈ P_hi, M_qttc / 2 < (T p).card := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have h_upper : ∀ p ∈ P_hi, (T p).card ≤ M_qttc := by
      intro p hp
      have h_in_P : p ∈ P := (Finset.mem_filter.mp hp).1
      have h5 : (T p).card ≤ M := (h_tubes_card p h_in_P).2
      have h6 : (M : ℝ) ≤ (m_ceil : ℝ) := Nat.le_ceil M
      have h7 : ((T p).card : ℝ) ≤ (m_ceil : ℝ) := by linarith
      exact_mod_cast h7
    let C₁ := max 1 ((MainAppendix.affineLine_packing_constant : ℝ) *
      max 1 (K_pack * Real.rpow δ (-ε)))
    have hC1_one : 1 ≤ C₁ := by apply le_max_left
    have h_finite_sset : ∀ p ∈ P_hi, BallGrowth δ s C₁ (T p) := by
      intro p hp
      exact IsDeltaSSet.to_ball_growth_half_separated
        (h_tubes_sset p (Finset.mem_filter.mp hp).1)
        (h_tubes_separated p (Finset.mem_filter.mp hp).1)
    have h_size : ∀ p ∈ P_hi, M_qttc / 2 < (T p).card ∧ (T p).card ≤ M_qttc :=
      fun p hp => ⟨h_lower p hp, h_upper p hp⟩
    have h_slope' : ∀ p ∈ P_hi, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 :=
      fun p hp ℓ hℓ => h_slope_bound p (Finset.mem_filter.mp hp).1 ℓ hℓ
    have h_ball : ∀ p ∈ P_hi, |p 1| ≤ R :=
      fun p hp => by
        have h1 : p ∈ P := (Finset.mem_filter.mp hp).1
        have h2 : p ∈ Metric.closedBall (0 : Plane) R := hP_in_ball h1
        have h3 : ‖p‖ ≤ R := by simpa [Metric.mem_closedBall] using h2
        have h4 : |p 1| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 1
        exact le_trans h4 h3
    have h_inc_hi : ∀ p ∈ P_hi, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1 :=
      fun p hp ℓ hℓ => h_inc p (Finset.mem_filter.mp hp).1 ℓ hℓ
    let h_main := @hQTTC n m0 δ Δ C₁ M_qttc P_hi T
        hδ_eq hΔ_eq hnm hm_pos
        hC1_one hP_hi_nonempty hM_qttc_pos
        h_size h_finite_sset (fun p hp => h_tubes_separated p (Finset.mem_filter.mp hp).1) h_slope' R hR h_ball hδ_le_quarter_Delta h_inc_hi
    choose P_Q T_Q C_Q K C₂ H_nat
      hK_one hK_bound hC2_one hH_pos
      hP_Q_sub hP_card hT_Q_sub hT_Q_size
      hC'_sset hC'_delta_sset hC2_bound
      hC'_slope hC'_v hC'_b hC'_near
      h_parent_witness
      h_pointFiber_inc h_pointFiber_upper_raw
      h_avg_lower h_avg_upper using h_main
    let K_Q : ℝ := 6 * K
    let C2_Q : ℝ := max 1 (C_PACK * C₂)
    let H_Q : ℝ := (H_nat : ℝ)
    have hH_Q_pos : 0 < H_Q := by
      have h : (0 : ℝ) < (H_nat : ℝ) := by exact_mod_cast hH_pos
      simpa [H_Q] using h
    have hH_Q_one : 1 ≤ H_Q := by
      have h : 1 ≤ H_nat := Nat.succ_le_iff.mpr hH_pos
      have h' : (1 : ℝ) ≤ (H_nat : ℝ) := by exact_mod_cast h
      simpa [H_Q] using h'
    have hK_Q_pos : 0 < K_Q := by positivity
    have hK_Q_one : 1 ≤ K := hK_one
    have hK_Q_loss : K_Q ≤ Real.rpow Δ (-ε) := by
      have h1 : K ≤ A * Real.rpow (Real.log (2 / Δ)) A := hK_bound
      have h2 : K_Q ≤ 6 * A * Real.rpow (Real.log (2 / Δ)) A := by
        dsimp only [K_Q] <;> linarith
      exact h2.trans h_small.hK_loss
    have hK_Q_loss_strong : K_Q ≤ Real.rpow Δ (-2 * ε) := by
      have h1 : K ≤ A * Real.rpow (Real.log (2 / Δ)) A := hK_bound
      have h2 : K_Q ≤ 6 * A * Real.rpow (Real.log (2 / Δ)) A := by
        dsimp only [K_Q] <;> linarith
      exact h2.trans h_small.hK_loss_strong
    have hC2_Q_loss : C2_Q ≤ Real.rpow Δ (-10 * ε) := by
      let Kpc : ℝ := (MainAppendix.affineLine_packing_constant : ℝ)
      have hKpc_ge1 : 1 ≤ Kpc := h_small.hKpack_const_ge1
      have hX_ge1 : 1 ≤ max 1 (K_pack * Real.rpow δ (-ε)) := by apply le_max_left
      have hProd_ge1 : 1 ≤ Kpc * max 1 (K_pack * Real.rpow δ (-ε)) := by
        have h : 1 ≤ Kpc := hKpc_ge1
        have h' : 1 ≤ max 1 (K_pack * Real.rpow δ (-ε)) := hX_ge1
        nlinarith
      have hC1_eq : C₁ = Kpc * max 1 (K_pack * Real.rpow δ (-ε)) := by
        dsimp only [C₁]
        rw [max_eq_right hProd_ge1]
      have hCP_ge1 : 1 ≤ C_PACK := by
        have h : C_PACK = Kpc := by rfl
        rw [h]
        exact hKpc_ge1
      have hC2_ge1 : 1 ≤ C₂ := hC2_one
      have h_eq : C2_Q = C_PACK * C₂ := by
        dsimp only [C2_Q]
        have h : 1 ≤ C_PACK * C₂ := by nlinarith
        rw [max_eq_right h]
      rw [h_eq]
      have h1 : C₂ ≤ A * Real.rpow K A * C₁ := hC2_bound
      have h2 : K ≤ A * Real.rpow (Real.log (2 / Δ)) A := hK_bound
      have hA_pos : 0 < A := h_small.hA_pos
      have hK_pos : 0 < K := by linarith [hK_one]
      have hLog_pos : 0 < Real.log (2 / Δ) := by
        have h1 : 2 / Δ ≥ 4 := by
          have h2 : 0 < Δ := h_small.hΔ_pos
          have h3 : Δ ≤ 1 / 2 := h_small.hΔ_lt_half
          calc 2 / Δ ≥ 2 / (1 / 2) := by gcongr
          _ = 4 := by norm_num
        have h4 : (1 : ℝ) < 2 / Δ := by linarith
        exact Real.log_pos h4
      have hBase_pos : 0 < A * Real.rpow (Real.log (2 / Δ)) A :=
        mul_pos hA_pos (Real.rpow_pos_of_pos hLog_pos A)
      have h3 : Real.rpow K A ≤ Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A :=
        Real.rpow_le_rpow hK_pos.le h2 hA_pos.le
      have h4 : C₂ ≤ A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * C₁ := by
        have hC1_nonneg : 0 ≤ C₁ := by positivity
        have h41 : A * Real.rpow K A ≤ A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A :=
          mul_le_mul_of_nonneg_left h3 hA_pos.le
        have h42 : A * Real.rpow K A * C₁ ≤ A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * C₁ :=
          mul_le_mul_of_nonneg_right h41 hC1_nonneg
        exact h1.trans h42
      rw [hC1_eq] at h4
      have h6 : C_PACK = Kpc := by rfl
      rw [h6]
      have hKpc_nonneg : 0 ≤ Kpc := by linarith
      have h7 : Kpc * C₂ ≤
          A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * Kpc^2 *
          max 1 (K_pack * Real.rpow δ (-ε)) := by
        calc Kpc * C₂
          ≤ Kpc * (A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A *
              (Kpc * max 1 (K_pack * Real.rpow δ (-ε)))) :=
            mul_le_mul_of_nonneg_left h4 hKpc_nonneg
        _ = A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * Kpc^2 *
              max 1 (K_pack * Real.rpow δ (-ε)) := by ring
      exact h7.trans h_small.hC2_loss
    -- Common derived bounds
    have hP_Q_refine : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ) := by
      have h1 : (P.card : ℝ) ≤ 2 * (P_hi.card : ℝ) := by
        have h2 : P.card ≤ 2 * P_hi.card := by omega
        exact_mod_cast h2
      have h2 : (P_hi.card : ℝ) ≤ K * (P_Q.card : ℝ) := hP_card
      calc (P.card : ℝ)
        ≤ 2 * (P_hi.card : ℝ) := h1
      _ ≤ 2 * (K * (P_Q.card : ℝ)) := by gcongr
      _ ≤ K_Q * (P_Q.card : ℝ) := by
        have h3 : 0 ≤ (P_Q.card : ℝ) := Nat.cast_nonneg _
        have h4 : 2 * K ≤ K_Q := by
          have h5 : K_Q = 6 * K := by rfl
          rw [h5]
          have h6 : 0 ≤ K := by linarith [hK_one]
          linarith
        have h_goal : 2 * (K * (P_Q.card : ℝ)) ≤ K_Q * (P_Q.card : ℝ) := by
          have h9 : 2 * (K * (P_Q.card : ℝ)) = (2 * K) * (P_Q.card : ℝ) := by ring
          rw [h9]
          exact mul_le_mul_of_nonneg_right h4 h3
        exact h_goal
    have hT_Q_refine : ∀ p ∈ P_Q, (M : ℝ) ≤ K_Q * (T_Q p).card := by
      intro p hp
      have h1 : (M_qttc : ℝ) ≤ K * ((T_Q p).card : ℝ) := hT_Q_size p hp
      have h2 : (M : ℝ) ≤ (M_qttc : ℝ) := by
        have h3 : M ≤ (m_ceil : ℝ) := Nat.le_ceil M
        simpa [M_qttc] using h3
      calc (M : ℝ) ≤ (M_qttc : ℝ) := h2
        _ ≤ K * ((T_Q p).card : ℝ) := h1
        _ ≤ K_Q * ((T_Q p).card : ℝ) := by
          have h3 : 0 ≤ ((T_Q p).card : ℝ) := Nat.cast_nonneg _
          have h4 : K ≤ K_Q := by
            have h5 : K_Q = 6 * K := by rfl
            rw [h5]
            have h6 : 0 ≤ K := by linarith [hK_one]
            linarith
          exact mul_le_mul_of_nonneg_right h4 h3
    have h_balance_lower : (M : ℝ) * (P.card : ℝ) ≤ K_Q * H_Q * (C_Q.card : ℝ) := by
      have h1 : (P.card : ℝ) ≤ 2 * (P_hi.card : ℝ) := by
        have h2 : P.card ≤ 2 * P_hi.card := by omega
        exact_mod_cast h2
      have h2 : (M : ℝ) ≤ (M_qttc : ℝ) := by have h3 : M ≤ (m_ceil : ℝ) := Nat.le_ceil M; simpa [M_qttc] using h3
      have h3 : (M : ℝ) * (P.card : ℝ) ≤ (M_qttc : ℝ) * (2 * (P_hi.card : ℝ)) := by gcongr
      have h4 : (M_qttc : ℝ) * (P_hi.card : ℝ) ≤ K * H_Q * (C_Q.card : ℝ) := by
        simpa [H_Q] using h_avg_lower
      calc (M : ℝ) * (P.card : ℝ)
        ≤ (M_qttc : ℝ) * (2 * (P_hi.card : ℝ)) := h3
      _ = 2 * ((M_qttc : ℝ) * (P_hi.card : ℝ)) := by ring
      _ ≤ 2 * (K * H_Q * (C_Q.card : ℝ)) := by gcongr
      _ ≤ K_Q * H_Q * (C_Q.card : ℝ) := by
        have h7 : 2 * K ≤ K_Q := by
          have h8 : K_Q = 6 * K := by rfl
          rw [h8]
          have h9 : 0 ≤ K := by linarith [hK_one]
          linarith
        have h10 : 0 ≤ H_Q * (C_Q.card : ℝ) := by
          have h10a : 0 ≤ H_Q := Nat.cast_nonneg H_nat
          have h10b : 0 ≤ (C_Q.card : ℝ) := Nat.cast_nonneg _
          exact mul_nonneg h10a h10b
        have h11 : 2 * (K * H_Q * (C_Q.card : ℝ)) = (2 * K) * (H_Q * (C_Q.card : ℝ)) := by ring
        have h12 : K_Q * H_Q * (C_Q.card : ℝ) = K_Q * (H_Q * (C_Q.card : ℝ)) := by ring
        rw [h11, h12]
        exact mul_le_mul_of_nonneg_right h7 h10
    have h_sum_lower : (M : ℝ) * (P.card : ℝ) ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
      have h1 : ∀ p ∈ P_Q, (M_qttc : ℝ) ≤ K * ((T_Q p).card : ℝ) := hT_Q_size
      have h2 : (M_qttc : ℝ) * (P_Q.card : ℝ) ≤ K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have h3 : (∑ p ∈ P_Q, (M_qttc : ℝ)) = (M_qttc : ℝ) * (P_Q.card : ℝ) := by
          rw [Finset.sum_const] <;> ring
        have h4 : (∑ p ∈ P_Q, (M_qttc : ℝ)) ≤ ∑ p ∈ P_Q, K * ((T_Q p).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact h1 p hp
        have h5 : (∑ p ∈ P_Q, K * ((T_Q p).card : ℝ)) = K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
          rw [Finset.mul_sum]
        rw [← h3]
        exact h4.trans (by rw [h5])
      have h4 : (P.card : ℝ) ≤ 2 * (P_hi.card : ℝ) := by
        have h5 : P.card ≤ 2 * P_hi.card := by omega
        exact_mod_cast h5
      have h5 : (P_hi.card : ℝ) ≤ K * (P_Q.card : ℝ) := hP_card
      have h6 : (M : ℝ) ≤ (M_qttc : ℝ) := by have h7 : M ≤ (m_ceil : ℝ) := Nat.le_ceil M; simpa [M_qttc] using h7
      have hK_ge1 : 1 ≤ K := hK_one
      have h_nonneg : 0 ≤ (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        apply Finset.sum_nonneg
        intro p _
        exact Nat.cast_nonneg _
      calc (M : ℝ) * (P.card : ℝ)
        ≤ (M_qttc : ℝ) * (2 * (P_hi.card : ℝ)) := by gcongr
      _ ≤ (M_qttc : ℝ) * (2 * (K * (P_Q.card : ℝ))) := by gcongr
      _ = 2 * K * ((M_qttc : ℝ) * (P_Q.card : ℝ)) := by ring
      _ ≤ 2 * K * (K * (∑ p ∈ P_Q, (T_Q p).card : ℝ)) := by gcongr
      _ = 2 * K^2 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by ring
      _ ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have h9 : 2 * K^2 ≤ K_Q^3 := by
          have h10 : K_Q = 6 * K := by rfl
          have h11 : 1 ≤ K := hK_one
          rw [h10]
          have h12 : 0 ≤ K := by linarith
          have h13 : K^2 ≤ K^3 := by
            calc K^2 = K^2 * 1 := by ring
              _ ≤ K^2 * K := by gcongr <;> linarith
              _ = K^3 := by ring
          calc 2 * K^2 ≤ 2 * K^3 := by gcongr
            _ ≤ 216 * K^3 := by gcongr <;> linarith
            _ = (6 * K)^3 := by ring
        have h10 : 0 ≤ (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
          apply Finset.sum_nonneg
          intro p _
          exact Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right h9 h10
    have h_balance_upper : H_Q * (C_Q.card : ℝ) ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
      have h1 : H_Q * (C_Q.card : ℝ) ≤ K * (M_qttc : ℝ) * (P_hi.card : ℝ) := by
        simpa [H_Q] using h_avg_upper
      have h2 : (M_qttc : ℝ) * (P_Q.card : ℝ) ≤ K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have h3 : (∑ p ∈ P_Q, (M_qttc : ℝ)) = (M_qttc : ℝ) * (P_Q.card : ℝ) := by
          rw [Finset.sum_const] <;> ring
        have h4 : K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) = ∑ p ∈ P_Q, K * ((T_Q p).card : ℝ) := by
          rw [Finset.mul_sum]
        rw [← h3, h4]
        apply Finset.sum_le_sum
        intro p hp
        exact hT_Q_size p hp
      have h3 : (P_hi.card : ℝ) ≤ K * (P_Q.card : ℝ) := hP_card
      have h_sum_nonneg : 0 ≤ (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        apply Finset.sum_nonneg; intro p _; exact Nat.cast_nonneg _
      have h4 : K * (M_qttc : ℝ) * (P_hi.card : ℝ) ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have h_pos1 : 0 ≤ K * (M_qttc : ℝ) := by
          have hK_nonneg : 0 ≤ K := by linarith [hK_one]
          have hMqttc_nonneg : 0 ≤ (M_qttc : ℝ) := Nat.cast_nonneg _
          exact mul_nonneg hK_nonneg hMqttc_nonneg
        have h_pos2 : 0 ≤ K^2 := by positivity
        have h5 : K^3 ≤ K_Q^3 := by
          have h6 : K ≤ K_Q := by
            have h7 : K_Q = 6 * K := by rfl
            rw [h7]
            have h8 : 0 ≤ K := by linarith [hK_one]
            linarith
          have hK_nonneg : 0 ≤ K := by linarith [hK_one]
          gcongr <;> linarith
        calc K * (M_qttc : ℝ) * (P_hi.card : ℝ)
          ≤ K * (M_qttc : ℝ) * (K * (P_Q.card : ℝ)) := mul_le_mul_of_nonneg_left h3 h_pos1
          _ = K^2 * ((M_qttc : ℝ) * (P_Q.card : ℝ)) := by ring
          _ ≤ K^2 * (K * (∑ p ∈ P_Q, (T_Q p).card : ℝ)) := mul_le_mul_of_nonneg_left h2 h_pos2
          _ = K^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by ring
          _ ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := mul_le_mul_of_nonneg_right h5 h_sum_nonneg
      exact h1.trans h4
    have hH2 : ∀ boldT ∈ C_Q,
        H_Q ≤ ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card := by
      intro boldT hboldT
      have h : (H_nat : ℝ) ≤ ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card :=
        h_pointFiber_inc h_small.hΔ_pos boldT hboldT
      simpa [H_Q] using h
    have hC_Q_sset : IsDeltaSSet Δ s C2_Q (C_Q : Set CoarseTube) := by
      exact hC'_delta_sset
    have hK_Q_lower : Real.rpow Δ (2 * ε) ≤ K_Q :=
      a2_K_Q_lower h_small.hΔ_pos h_small.hΔ_lt_half h_small.hstrip_loss hK_one (by rfl)
    have hP_Q_card_upper : (P_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := by
      have h1 : P_Q ⊆ P_hi := hP_Q_sub
      have h2 : P_hi ⊆ P := Finset.filter_subset (fun p => (T p).card > m_ceil / 2) P
      have h3 : P_Q ⊆ P := h1.trans h2
      have h4 : (P_Q.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Finset.card_le_card h3
      exact h4.trans hP_card_upper
    have hP_Q_in_square : (P_Q : Set Plane) ⊆ squareSet Δ Q := by
      have h1 : P_Q ⊆ P_hi := hP_Q_sub
      have h2 : P_hi ⊆ P := Finset.filter_subset (fun p => (T p).card > m_ceil / 2) P
      have h3 : (P_Q : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast h1.trans h2
      exact h3.trans hP_in_square
    have hP_Q_in_ball : (P_Q : Set Plane) ⊆ Metric.closedBall 0 (Real.sqrt 2) := by
      have h1 : P_Q ⊆ P_hi := hP_Q_sub
      have h2 : P_hi ⊆ P := Finset.filter_subset (fun p => (T p).card > m_ceil / 2) P
      have h3 : (P_Q : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast h1.trans h2
      have h4 : (P : Set Plane) ⊆ Metric.closedBall 0 R := hP_in_ball
      have h5 : Metric.closedBall (0 : Plane) R ⊆ Metric.closedBall (0 : Plane) (Real.sqrt 2) :=
        Metric.closedBall_subset_closedBall hR
      exact Set.Subset.trans h3 (Set.Subset.trans h4 h5)
    have hP_hi_sub : P_hi ⊆ P := Finset.filter_subset (fun p => (T p).card > m_ceil / 2) P
    have h_slope_bound' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 := by
      intro p hp ℓ hℓ
      have h1 : ℓ ∈ T p := hT_Q_sub p hp hℓ
      have h2 : p ∈ P := hP_hi_sub (hP_Q_sub hp)
      exact h_slope_bound p h2 ℓ h1
    have h_inc' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q p, p ∈ Metric.cthickening (2 * δ) ℓ.1 := by
      intro p hp ℓ hℓ
      have h1 : ℓ ∈ T p := hT_Q_sub p hp hℓ
      have h2 : p ∈ P := hP_hi_sub (hP_Q_sub hp)
      exact h_inc p h2 ℓ h1
    have hT_Q_separated' : ∀ p ∈ P_Q, SeparatedAt (δ / 2) (T_Q p : Set FineTube) := by
      intro p hp
      have h1 : (T_Q p : Set FineTube) ⊆ (T p : Set FineTube) := by exact_mod_cast hT_Q_sub p hp
      have h2 : p ∈ P := hP_hi_sub (hP_Q_sub hp)
      exact (h_tubes_separated p h2).mono h1
    have hT_Q_per_coarse_upper :=
      a2_get_per_coarse_upper δ Δ s ε C₁ M P_Q T_Q C_Q T P_hi P
        hP_Q_sub hP_hi_sub h_finite_sset hT_Q_sub h_tubes_card
        h_small.hδ_le_Δ h_small.hΔ_pos h_small.hM_upper
    have hε_pos : 0 < ε := a2_eps_pos h_small.hΔ_pos h_small.hΔ_lt_half h_small.hstrip_loss
    have hP_hi_in_square : (P_hi : Set Plane) ⊆ squareSet Δ Q := by
      have h1 : (P_hi : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast hP_hi_sub
      exact h1.trans hP_in_square
    have hP_hi_in_ball : (P_hi : Set Plane) ⊆ Metric.closedBall 0 (Real.sqrt 2) := by
      have h1 : (P_hi : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast hP_hi_sub
      have h2 : (P : Set Plane) ⊆ Metric.closedBall 0 R := hP_in_ball
      have h3 : Metric.closedBall (0 : Plane) R ⊆ Metric.closedBall (0 : Plane) (Real.sqrt 2) :=
        Metric.closedBall_subset_closedBall hR
      exact (h1.trans h2).trans h3
    have h_slope_bound_hi : ∀ p ∈ P_hi, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 :=
      fun p hp ℓ hℓ => h_slope_bound p (hP_hi_sub hp) ℓ hℓ
    have h_inc_hi2 : ∀ p ∈ P_hi, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1 :=
      fun p hp ℓ hℓ => h_inc p (hP_hi_sub hp) ℓ hℓ
    have hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube) := hC'_sset.2.2.2.2.1
    have hK_pos : 0 < K := by linarith [hK_one]
    have hM_le_mqttc : (M : ℝ) ≤ (M_qttc : ℝ) := by
      have h5 : M ≤ (m_ceil : ℝ) := Nat.le_ceil M
      simpa [M_qttc] using h5
    have hKpack_pos : 0 < K_pack := by
      by_contra h
      have h' : K_pack ≤ 0 := by exact le_of_not_gt h
      have h_rpow_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos h_small.hΔ_pos _
      have h_div_nonpos : Real.rpow Δ (-2 * s + 2 * ε) / K_pack ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos h_rpow_pos.le h'
      have h_contra : (2 : ℝ) ≤ Real.rpow Δ (-2 * s + 2 * ε) / K_pack := h_small.hM_large
      have h6 : (2 : ℝ) ≤ 0 := le_trans h_contra h_div_nonpos
      norm_num at h6
    have hKpack : K_pack ≤ Real.rpow Δ (-2 * ε) / 6 := by
      have h_rpow_neg_eps_pos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos h_small.hΔ_pos _
      have h : 6 * K_pack * Real.rpow Δ (-ε) ≤ Real.rpow Δ (-3 * ε) := h_small.hKpack_loss
      have h3 : Real.rpow Δ (-3 * ε) = Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε) := by
        have h_sum : (-2 * ε) + (-ε) = -3 * ε := by ring
        have h_add : Real.rpow Δ ((-2 * ε) + (-ε)) = Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε) := by
          simpa using Real.rpow_add h_small.hΔ_pos (-2 * ε) (-ε)
        rw [h_sum] at h_add
        exact h_add
      rw [h3] at h
      have h4 : 6 * K_pack ≤ Real.rpow Δ (-2 * ε) :=
        le_of_mul_le_mul_right h h_rpow_neg_eps_pos
      have h5 : K_pack ≤ Real.rpow Δ (-2 * ε) / 6 := by
        calc K_pack
          = (6 * K_pack) / 6 := by ring
        _ ≤ (Real.rpow Δ (-2 * ε)) / 6 := by gcongr
      exact h5
    have hKpack_strong : K_pack ≤ Real.rpow Δ (-ε) / 6 := by
      have h : 6 * K_pack ≤ Real.rpow Δ (-ε) := h_small.hKpack_loss_strong
      calc K_pack
        = (6 * K_pack) / 6 := by ring
      _ ≤ (Real.rpow Δ (-ε)) / 6 := by gcongr
    have hKpack_le_ε : K_pack ≤ Real.rpow Δ (-ε) := by
      have hpos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos h_small.hΔ_pos _
      linarith [hKpack_strong]
    have h6_loss : (6 : ℝ) ≤ Real.rpow Δ (-ε) := by
      have h1 : 1 ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
        have hK_pos : 0 < K := by linarith [hK_one]
        linarith [hK_bound]
      have h2 : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε) := h_small.hK_loss
      have h3 : (6 : ℝ) ≤ 6 * A * Real.rpow (Real.log (2 / Δ)) A := by
        have h4 : 1 ≤ A * Real.rpow (Real.log (2 / Δ)) A := h1
        nlinarith
      linarith
    have h_absorb_5 : (6 : ℝ)^s ≤ Real.rpow Δ (-ε) :=
      absorb_6_pow_s Δ s ε h_small.hΔ_pos hε_pos (by linarith [hs_pos]) hs1 h6_loss
    have h_pointFiber_upper_local : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
        (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card ≤ Real.rpow Δ (-s - 7 * ε) := by
      intro p hp boldT hboldT
      have h_raw : (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card ≤
          C₁ * (6 : ℝ)^s * (T p).card * Δ^s :=
        h_pointFiber_upper_raw h_small.hΔ_pos p hp boldT hboldT
      have h_card : ((T p).card : ℝ) ≤ M :=
        (h_tubes_card p (hP_hi_sub (hP_Q_sub hp))).2
      have h_C1M : C₁ * M ≤ Real.rpow Δ (-2 * s - 6 * ε) := h_small.hM_upper
      have h_main : ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ) ≤
          (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := by
        calc ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ)
          ≤ C₁ * (6 : ℝ)^s * ((T p).card : ℝ) * Δ^s := by exact_mod_cast h_raw
        _ ≤ C₁ * (6 : ℝ)^s * M * Δ^s := by
          have hpos : 0 ≤ C₁ * (6 : ℝ)^s * Δ^s := by
            have h1 : 0 ≤ C₁ := by linarith [hC1_one]
            have h2 : 0 < (6 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) s
            have h3 : 0 < Δ^s := Real.rpow_pos_of_pos h_small.hΔ_pos s
            positivity
          have h_eq1 : C₁ * (6 : ℝ)^s * ((T p).card : ℝ) * Δ^s = (C₁ * (6 : ℝ)^s * Δ^s) * ((T p).card : ℝ) := by ring
          have h_eq2 : C₁ * (6 : ℝ)^s * M * Δ^s = (C₁ * (6 : ℝ)^s * Δ^s) * M := by ring
          rw [h_eq1, h_eq2]
          exact mul_le_mul_of_nonneg_left h_card hpos
        _ = (6 : ℝ)^s * (C₁ * M) * Δ^s := by ring
        _ ≤ (6 : ℝ)^s * Real.rpow Δ (-2 * s - 6 * ε) * Δ^s := by
          have hpos : 0 ≤ (6 : ℝ)^s * Δ^s := by
            have h1 : 0 < (6 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) s
            have h2 : 0 < Δ^s := Real.rpow_pos_of_pos h_small.hΔ_pos s
            positivity
          have h_eq1 : (6 : ℝ)^s * (C₁ * M) * Δ^s = ((6 : ℝ)^s * Δ^s) * (C₁ * M) := by ring
          have h_eq2 : (6 : ℝ)^s * Real.rpow Δ (-2 * s - 6 * ε) * Δ^s = ((6 : ℝ)^s * Δ^s) * Real.rpow Δ (-2 * s - 6 * ε) := by ring
          rw [h_eq1, h_eq2]
          exact mul_le_mul_of_nonneg_left h_C1M hpos
        _ = (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := by
          have h_add : Real.rpow Δ (-2 * s - 6 * ε) * Δ^s = Real.rpow Δ (-s - 6 * ε) := by
            have h1 : Δ^s = Real.rpow Δ s := by rfl
            rw [h1]
            have h2 := Real.rpow_add h_small.hΔ_pos (-2 * s - 6 * ε) s
            have h3 : (-2 * s - 6 * ε) + s = -s - 6 * ε := by ring
            rw [h3] at h2; exact h2.symm
          have h_goal : (6 : ℝ)^s * Real.rpow Δ (-2 * s - 6 * ε) * Δ^s = (6 : ℝ)^s * (Real.rpow Δ (-2 * s - 6 * ε) * Δ^s) := by ring
          rw [h_goal, h_add] <;> ring
      have h_final : ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ) ≤
          Real.rpow Δ (-s - 7 * ε) := by
        calc ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ)
          ≤ (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := h_main
        _ ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) := by
          have hpos : 0 ≤ Real.rpow Δ (-s - 6 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
          exact mul_le_mul_of_nonneg_right h_absorb_5 hpos
        _ = Real.rpow Δ (-s - 7 * ε) := by
          have h_add := Real.rpow_add h_small.hΔ_pos (-ε) (-s - 6 * ε)
          have h4 : (-ε) + (-s - 6 * ε) = -s - 7 * ε := by ring
          rw [h4] at h_add; exact h_add.symm
      exact_mod_cast h_final
    have hH_Q_coarse_upper : H_Q ≤ (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by
      have h1 : ∃ c ∈ C_Q, True := by
        have h2 : C_Q.Nonempty := hC'_sset.1
        rcases h2 with ⟨c, hc⟩
        exact ⟨c, hc, trivial⟩
      rcases h1 with ⟨c, hc, _⟩
      have h2 : H_Q ≤ ∑ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ) := by
        have hH2' : H_Q ≤ ↑(∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p c).card) := hH2 c hc
        rw [Nat.cast_sum] at hH2'
        exact hH2'
      have h3 : ∑ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ) ≤ (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by
        have h4 : ∀ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ) ≤ Real.rpow Δ (-s - 7 * ε) :=
          fun p hp => h_pointFiber_upper_local p hp c hc
        calc ∑ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ)
          ≤ ∑ p ∈ P_Q, Real.rpow Δ (-s - 7 * ε) := Finset.sum_le_sum h4
        _ = (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by
          rw [Finset.sum_const] <;> ring
      exact h2.trans h3
    have hH_Q_upper : H_Q ≤ Real.rpow Δ (-t - s - 10 * ε) := by
      have h5 : (P_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := hP_Q_card_upper
      have h_rpow7_nonneg : 0 ≤ Real.rpow Δ (-s - 7 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
      have h_rpow_sum : Real.rpow Δ (-t - 3 * ε) * Real.rpow Δ (-s - 7 * ε) = Real.rpow Δ (-t - s - 10 * ε) := by
        have h_sum : (-t - 3 * ε) + (-s - 7 * ε) = -t - s - 10 * ε := by ring
        have h_add : Real.rpow Δ ((-t - 3 * ε) + (-s - 7 * ε)) = Real.rpow Δ (-t - 3 * ε) * Real.rpow Δ (-s - 7 * ε) := by
          simpa using Real.rpow_add h_small.hΔ_pos (-t - 3 * ε) (-s - 7 * ε)
        rw [h_sum] at h_add
        exact h_add.symm
      calc H_Q
        ≤ (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := hH_Q_coarse_upper
      _ ≤ Real.rpow Δ (-t - 3 * ε) * Real.rpow Δ (-s - 7 * ε) := by
        have h_rpow1_nonneg : 0 ≤ Real.rpow Δ (-t - 3 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
        have h_rpow2_nonneg : 0 ≤ Real.rpow Δ (-s - 7 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
        exact mul_le_mul hP_Q_card_upper (le_refl _) h_rpow2_nonneg h_rpow1_nonneg
      _ = Real.rpow Δ (-t - s - 10 * ε) := h_rpow_sum
    have hC_card_lower : Real.rpow Δ (-s + 11 * ε) ≤ (C_Q.card : ℝ) :=
      a2_C_card_lower Δ s ε M P.card P_Q.card C_Q.card K_Q H_Q K_pack
        h_small.hΔ_pos h_balance_lower hH_Q_coarse_upper
        (Finset.card_le_card (hP_Q_sub.trans hP_hi_sub))
        hM_lower hK_Q_loss hKpack_strong hKpack_pos hK_Q_pos
        hH_Q_pos (hP_nonempty.card_pos)
    have hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube) := hC'_sset.2.2.2.2.1
    -- New fields for A4
    have hP_Q_card_lower : (P_Q.card : ℝ) ≥ Real.rpow Δ (-t + 5 * ε) := by
      have h_posK : 0 < K_Q := hK_Q_pos
      have h1 : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ) := hP_Q_refine
      have h5 : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ) := hP_card_lower_strong
      have h7 : K_Q ≤ Real.rpow Δ (-2 * ε) := hK_Q_loss_strong
      have h_nneg : 0 ≤ Real.rpow Δ (-t + 5 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
      have h_rpow_sum : Real.rpow Δ (-t + 5 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ (-t + 3 * ε) := by
        have h_add : Real.rpow Δ ((-t + 5 * ε) + (-2 * ε)) =
            Real.rpow Δ (-t + 5 * ε) * Real.rpow Δ (-2 * ε) :=
          Real.rpow_add h_small.hΔ_pos (-t + 5 * ε) (-2 * ε)
        have h_eq : (-t + 5 * ε) + (-2 * ε) = -t + 3 * ε := by ring
        rw [h_eq] at h_add
        exact h_add.symm
      have h9 : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ Real.rpow Δ (-t + 5 * ε) * Real.rpow Δ (-2 * ε) :=
        mul_le_mul_of_nonneg_left h7 h_nneg
      have h9' : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ Real.rpow Δ (-t + 3 * ε) := by
        rw [h_rpow_sum] at * <;> exact h9
      have h10 : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ K_Q * (P_Q.card : ℝ) := by
        have h101 : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ Real.rpow Δ (-t + 3 * ε) := h9'
        have h102 : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ) := h5
        have h103 : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ) := h1
        exact le_trans h101 (le_trans h102 h103)
      have h13 : K_Q * (P_Q.card : ℝ) = (P_Q.card : ℝ) * K_Q := by ring
      rw [h13] at h10
      exact le_of_mul_le_mul_right h10 h_posK
    have hP_Q_separated : SeparatedAt δ (P_Q : Set Plane) := by
      have h1 : (P_Q : Set Plane) ⊆ (P : Set Plane) := by
        exact_mod_cast hP_Q_sub.trans hP_hi_sub
      exact hP_separated.mono h1
    have hP_Q_sset : IsDeltaSSet δ t (Real.rpow Δ (-t - 10 * ε)) (P_Q : Set Plane) := by
      have h_sset_constraint : C_P * K_Q * 81 ≤ Real.rpow Δ (-t - 10 * ε) := by
        have h1 : C_P * 81 ≤ Real.rpow Δ (-t - 8 * ε) := hC_P_bound
        have h2 : K_Q ≤ Real.rpow Δ (-2 * ε) := hK_Q_loss_strong
        have h3 : C_P * K_Q * 81 = (C_P * 81) * K_Q := by ring
        rw [h3]
        have h4 : 0 ≤ Real.rpow Δ (-t - 8 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
        have h5 : 0 ≤ Real.rpow Δ (-2 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
        have h6 : (C_P * 81) * K_Q ≤ (Real.rpow Δ (-t - 8 * ε)) * (Real.rpow Δ (-2 * ε)) :=
          mul_le_mul h1 h2 (by positivity) h4
        have h7 : (Real.rpow Δ (-t - 8 * ε)) * (Real.rpow Δ (-2 * ε)) = Real.rpow Δ (-t - 10 * ε) := by
          have h8 := Real.rpow_add h_small.hΔ_pos (-t - 8 * ε) (-2 * ε)
          have h9 : (-t - 8 * ε) + (-2 * ε) = -t - 10 * ε := by ring
          rw [h9] at h8; exact h8.symm
        rw [h7] at h6; exact h6
      exact gap3_hP_Q_sset hP_sset (hP_Q_sub.trans hP_hi_sub) hP_Q_separated hδ_pos
        hP_Q_refine hK_Q_pos h_sset_constraint
    have hC_Q_slope_bound : ∀ boldT ∈ C_Q, |tubeSlope boldT| ≤ 1 :=
      hC'_slope
    have hC_Q_v : ∀ ℓ ∈ C_Q, (LemmaE.getDirV ℓ) 1 ≠ 0 :=
      hC'_v
    have hC_Q_b : ∀ ℓ ∈ C_Q, |tubeIntercept ℓ| ≤ 3 :=
      hC'_b
    have h_strip : ∀ ℓ ∈ C_Q, ∃ (p : Plane), p ∈ squareSet Δ Q ∧ |p 1| ≤ Real.sqrt 2 ∧
        |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ := by
      intro ℓ hℓ
      rcases hC'_near ℓ hℓ with ⟨p, hp, h_near⟩
      have hp_in_P : p ∈ P := hP_hi_sub (hP_Q_sub hp)
      have hp_square : p ∈ squareSet Δ Q := hP_in_square hp_in_P
      have h_p1_sqrt2 : |p 1| ≤ Real.sqrt 2 := by
        have h1 : p ∈ Metric.closedBall (0 : Plane) R := hP_in_ball hp_in_P
        have h2 : ‖p‖ ≤ R := by simpa [Metric.mem_closedBall] using h1
        have h3 : |p 1| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 1
        have h4 : R ≤ Real.sqrt 2 := hR
        linarith
      have h_final : |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ := h_near
      exact ⟨p, hp_square, h_p1_sqrt2, h_final⟩
    have hΔ_lt_one : Δ < 1 := by linarith [h_small.hΔ_lt_half]
    have hC_Q_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)) :=
      hC_Q_cover_transfer_main h_small.hΔ_pos h_small.hΔ_lt_half hC_Q_sep hC_Q_v hC_Q_slope_bound hC_Q_b h_strip
    have hC_card_upper_weak : (C_Q.card : ℝ) ≤ Real.rpow Δ (-1 - 5 * ε) := by
      have h1 : (C_Q.card : ℝ) ≤ (42 : ℝ) * (40 * (4 : ℝ) + 110) / Δ :=
        affineLine_strip_packing h_small.hΔ_pos hΔ_lt_one 4 (by norm_num) C_Q
          hC_Q_sep hC_Q_v hC_Q_slope_bound hC_Q_b Q h_strip
      have h2 : (42 : ℝ) * (40 * (4 : ℝ) + 110) ≤ Real.rpow Δ (-5 * ε) := h_small.hstrip_loss
      have h3 : (C_Q.card : ℝ) ≤ Real.rpow Δ (-5 * ε) / Δ := by
        calc (C_Q.card : ℝ)
          ≤ (42 : ℝ) * (40 * (4 : ℝ) + 110) / Δ := h1
        _ ≤ Real.rpow Δ (-5 * ε) / Δ := by gcongr; exact h_small.hΔ_pos.le
      have h4 : Real.rpow Δ (-5 * ε) / Δ = Real.rpow Δ (-1 - 5 * ε) := by
        have h5 : Real.rpow Δ (-5 * ε) / Δ = Real.rpow Δ (-5 * ε) * Δ⁻¹ := by ring
        rw [h5]
        have h6 : Δ⁻¹ = Real.rpow Δ (-1 : ℝ) := by
          simp [Real.rpow_neg h_small.hΔ_pos.le]
          <;> field_simp [h_small.hΔ_pos.ne'] <;> ring
        rw [h6]
        have h7 : Real.rpow Δ (-5 * ε) * Real.rpow Δ (-1 : ℝ) = Real.rpow Δ ((-5 * ε) + (-1 : ℝ)) :=
          (Real.rpow_add h_small.hΔ_pos (-5 * ε) (-1 : ℝ)).symm
        rw [h7]
        have h8 : (-5 * ε) + (-1 : ℝ) = -1 - 5 * ε := by ring
        rw [h8]
      rw [h4] at h3
      exact h3
    have hC_Q_slope_sset : IsDeltaSSet Δ s (Real.rpow Δ (-25 * ε)) (tubeSlope '' (C_Q : Set CoarseTube)) :=
      hC_Q_slope_sset_main h_small.hΔ_pos hε_pos hΔ_lt_one hs_pos hs1
        hC'_delta_sset hC_Q_sep hC_Q_v hC_Q_slope_bound hC_Q_b hC2_Q_loss h_small.hslope_sset_const hC_Q_cover_transfer h_strip
    have hC_Q_slope_cover_lower : ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) ≤
        Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)) :=
      hC_Q_slope_cover_lower_main h_small.hΔ_pos hε_pos hΔ_lt_one hs_pos
        hC_Q_sep hC_card_lower h_small.hcover_lower_pack hC_Q_cover_transfer
    have hT_Q_sset : ∀ p ∈ P_Q,
        IsDeltaSSet δ s
          (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * (MainAppendix.affineLine_packing_constant : ℝ))
          (T_Q p : Set FineTube) := by
      intro p hp
      let C := max 1 (K_pack * Real.rpow δ (-ε))
      have hC_pos : 0 < C := by positivity
      have h_pack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) :=
        lt_of_lt_of_le zero_lt_one h_small.hKpack_const_ge1
      have hP_in_P : p ∈ P := hP_hi_sub (hP_Q_sub hp)
      exact a2_transfer_tube_sset hδ_pos hC_pos hK_Q_pos hM_pos h_pack_pos
        (h_tubes_sset p hP_in_P)
        (hT_Q_sub p hp)
        (hT_Q_separated' p hp)
        (h_tubes_card p hP_in_P).2
        (hT_Q_refine p hp)
    have hT_Q_card_upper : ∀ p ∈ P_Q, (T_Q p).card ≤ M := by
      intro p hp
      have h1 : (T_Q p : Set FineTube) ⊆ (T p : Set FineTube) := by exact_mod_cast hT_Q_sub p hp
      have h2 : (↑(T_Q p).card : ℝ) ≤ ↑(T p).card := by exact_mod_cast Finset.card_le_card h1
      have h3 : p ∈ P := hP_hi_sub (hP_Q_sub hp)
      have h4 : (↑(T p).card : ℝ) ≤ M := (h_tubes_card p h3).2
      exact le_trans h2 h4
    -- Restrict T_Q to P_Q so that T_Q p = ∅ for p ∉ P_Q.
    -- This is needed for downstream hT_Q_sub_Tsource (all p, not just p ∈ P_Q).
    let T_Q' : Plane → Finset FineTube := fun p => if h : p ∈ P_Q then T_Q p else ∅
    have hT_Q'_eq : ∀ p ∈ P_Q, T_Q' p = T_Q p := by
      intro p hp; simp [T_Q', hp]
    have hT_Q_refine' : ∀ p ∈ P_Q, (M : ℝ) ≤ K_Q * (T_Q' p).card := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_refine p hp
    have hH2' : ∀ boldT ∈ C_Q, H_Q ≤ ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card := by
      intro boldT hboldT
      have h_sum : ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card =
          ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card := by
        apply Finset.sum_congr rfl
        intro p hp
        have h_eq1 : T_Q' p = T_Q p := hT_Q'_eq p hp
        have h_pf_eq : pointFiber Δ h_small.hΔ_pos T_Q' p boldT = pointFiber Δ h_small.hΔ_pos T_Q p boldT := by
          unfold pointFiber
          rw [h_eq1]
        rw [h_pf_eq]
      rw [h_sum]; exact hH2 boldT hboldT
    have h_balance_upper' : H_Q * (C_Q.card : ℝ) ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q' p).card : ℝ) := by
      have h_sum : (∑ p ∈ P_Q, (T_Q' p).card : ℝ) = (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        apply Finset.sum_congr rfl; intro p hp; rw [hT_Q'_eq p hp]
      rw [h_sum]; exact h_balance_upper
    have h_slope_bound'' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q' p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 := by
      intro p hp ℓ hℓ; rw [hT_Q'_eq p hp] at hℓ; exact h_slope_bound' p hp ℓ hℓ
    have h_inc'' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q' p, p ∈ Metric.cthickening (2 * δ) ℓ.1 := by
      intro p hp ℓ hℓ; rw [hT_Q'_eq p hp] at hℓ; exact h_inc' p hp ℓ hℓ
    have hT_Q_separated'' : ∀ p ∈ P_Q, SeparatedAt (δ / 2) (T_Q' p : Set FineTube) := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_separated' p hp
    have hT_Q_per_coarse_upper' : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
        assignedCountMetric Δ T_Q' p boldT ≤ Real.rpow Δ (-s - 6 * ε) := by
      intro p hp boldT hboldT
      have h_eq : assignedCountMetric Δ T_Q' p boldT = assignedCountMetric Δ T_Q p boldT := by
        simp [assignedCountMetric, hT_Q'_eq p hp]
      rw [h_eq]
      exact hT_Q_per_coarse_upper p hp boldT hboldT
    have h_pointFiber_upper' : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
        (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card ≤ Real.rpow Δ (-s - 7 * ε) := by
      intro p hp boldT hboldT
      have h_eq : (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card = (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card := by
        simp only [pointFiber]
        <;> rw [hT_Q'_eq p hp]
      rw [h_eq]
      exact h_pointFiber_upper_local p hp boldT hboldT
    have hT_Q_sset' : ∀ p ∈ P_Q,
        IsDeltaSSet δ s (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * (MainAppendix.affineLine_packing_constant : ℝ))
          (T_Q' p : Set FineTube) := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_sset p hp
    have hT_Q_card_upper' : ∀ p ∈ P_Q, (T_Q' p).card ≤ M := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_card_upper p hp
    have hT_Q_sub' : ∀ p ∈ P_Q, T_Q' p ⊆ T p := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_sub p hp
    have hT_Q_empty_outside : ∀ p, p ∉ P_Q → T_Q' p = ∅ := by
      intro p hp
      simp [T_Q', hp]
    exact ⟨h_small.hΔ_pos, P_Q, T_Q', C_Q, K_Q, C2_Q, H_Q, (P.card : ℝ), M, hM_upper,
      hP_Q_refine, hT_Q_refine', hC_Q_sset, hH2', h_balance_lower, h_balance_upper',
      hK_Q_pos, hK_Q_loss, hC2_Q_loss, hH_Q_pos, hH_Q_one, hH_Q_upper, hK_Q_lower,
      hC_card_lower, hP_Q_card_upper, hP_Q_in_square, hP_Q_in_ball,
      h_slope_bound'', h_inc'', hT_Q_separated'', hT_Q_per_coarse_upper',
      h_pointFiber_upper',
      K_pack, hKpack_pos, hKpack, hKpack_le_ε, hT_Q_sset', hT_Q_card_upper',
      hP_Q_card_lower, hP_Q_separated, hP_Q_sset,
      hC_Q_sep, hC_Q_v, hC_Q_slope_bound, hC_Q_b, hC_Q_slope_sset, hC_Q_slope_cover_lower, hC_Q_cover_transfer,
      T_Delta_global, h_prove_sub P_Q T_Q C_Q (hP_Q_sub.trans (Finset.filter_subset _ _)) hT_Q_sub h_parent_witness,
      hM_lower, hP_card_lower_strong, hC_card_upper_weak,
      T, hT_Q_sub', hT_Q_empty_outside⟩
  · -- Case P_lo is large enough
    have hP_lo_large : P_lo.card * 2 ≥ P.card := by omega
    have hP_lo_nonempty : P_lo.Nonempty := by
      by_contra h
      have h_empty : P_lo = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [h_empty] at hP_lo_large
      have h0 : P.card = 0 := by simpa using hP_lo_large
      have h1 : P = ∅ := by simpa [Finset.card_eq_zero] using h0
      exact Finset.nonempty_iff_ne_empty.mp hP_nonempty h1
    have hP_lo_sub : P_lo ⊆ P := Finset.filter_subset (fun p => (T p).card ≤ m_ceil / 2) P
    let k : ℕ := m_ceil / 2
    have hk_pos : 0 < k := by
      have h1 : 2 ≤ m_ceil := hm_ge2
      omega
    let M_qttc : ℕ := 2 * k - 1
    have hM_qttc_pos : 0 < M_qttc := by omega
    have h_lower : ∀ p ∈ P_lo, M_qttc / 2 < (T p).card := by
      intro p hp
      have h_eq : (T p).card = k := h_lo_card p hp
      rw [h_eq]
      have h9 : M_qttc / 2 < k := by
        simp [M_qttc, Nat.mul_sub_left_distrib] <;> omega
      exact h9
    have h_upper : ∀ p ∈ P_lo, (T p).card ≤ M_qttc := by
      intro p hp
      have h_eq : (T p).card = k := h_lo_card p hp
      rw [h_eq]
      have h_k_pos : 1 ≤ k := hk_pos
      omega
    let C₁ := max 1 ((MainAppendix.affineLine_packing_constant : ℝ) *
      max 1 (K_pack * Real.rpow δ (-ε)))
    have hC1_one : 1 ≤ C₁ := by apply le_max_left
    have h_finite_sset : ∀ p ∈ P_lo, BallGrowth δ s C₁ (T p) := by
      intro p hp
      exact IsDeltaSSet.to_ball_growth_half_separated
        (h_tubes_sset p (hP_lo_sub hp))
        (h_tubes_separated p (hP_lo_sub hp))
    have h_slope_lo : ∀ p ∈ P_lo, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 :=
      fun p hp ℓ hℓ => h_slope_bound p (hP_lo_sub hp) ℓ hℓ
    have h_ball_lo : ∀ p ∈ P_lo, |p 1| ≤ R :=
      fun p hp => by
        have h1 : p ∈ P := hP_lo_sub hp
        have h2 : p ∈ Metric.closedBall (0 : Plane) R := hP_in_ball h1
        have h3 : ‖p‖ ≤ R := by simpa [Metric.mem_closedBall] using h2
        have h4 : |p 1| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 1
        exact le_trans h4 h3
    have h_inc_lo : ∀ p ∈ P_lo, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1 :=
      fun p hp ℓ hℓ => h_inc p (hP_lo_sub hp) ℓ hℓ
    let h_main := @hQTTC n m0 δ Δ C₁ M_qttc P_lo T
        hδ_eq hΔ_eq hnm hm_pos
        hC1_one hP_lo_nonempty hM_qttc_pos
        (fun p hp => ⟨h_lower p hp, h_upper p hp⟩)
        h_finite_sset (fun p hp => h_tubes_separated p (hP_lo_sub hp)) h_slope_lo R hR h_ball_lo hδ_le_quarter_Delta h_inc_lo
    choose P_Q T_Q C_Q K C₂ H_nat
      hK_one hK_bound hC2_one hH_pos
      hP_Q_sub hP_card hT_Q_sub hT_Q_size
      hC'_sset hC'_delta_sset hC2_bound
      hC'_slope hC'_v hC'_b hC'_near
      h_parent_witness
      h_pointFiber_inc h_pointFiber_upper_raw
      h_avg_lower h_avg_upper using h_main
    let K_Q := 6 * K
    let C2_Q := max 1 (C_PACK * C₂)
    let H_Q : ℝ := (H_nat : ℝ)
    have hH_Q_pos : 0 < H_Q := by
      have h : (0 : ℝ) < (H_nat : ℝ) := by exact_mod_cast hH_pos
      simpa [H_Q] using h
    have hH_Q_one : 1 ≤ H_Q := by
      have h : 1 ≤ H_nat := Nat.succ_le_iff.mpr hH_pos
      have h' : (1 : ℝ) ≤ (H_nat : ℝ) := by exact_mod_cast h
      simpa [H_Q] using h'
    have hK_Q_pos : 0 < K_Q := by positivity
    have hK_Q_loss : K_Q ≤ Real.rpow Δ (-ε) := by
      have h1 : K ≤ A * Real.rpow (Real.log (2 / Δ)) A := hK_bound
      have h2 : K_Q ≤ 6 * A * Real.rpow (Real.log (2 / Δ)) A := by
        dsimp only [K_Q] <;> linarith
      exact h2.trans h_small.hK_loss
    have hK_Q_loss_strong : K_Q ≤ Real.rpow Δ (-2 * ε) := by
      have h1 : K ≤ A * Real.rpow (Real.log (2 / Δ)) A := hK_bound
      have h2 : K_Q ≤ 6 * A * Real.rpow (Real.log (2 / Δ)) A := by
        dsimp only [K_Q] <;> linarith
      exact h2.trans h_small.hK_loss_strong
    have hC2_Q_loss : C2_Q ≤ Real.rpow Δ (-10 * ε) := by
      -- same proof as P_hi branch
      have hKpc_ge1 : 1 ≤ (MainAppendix.affineLine_packing_constant : ℝ) := h_small.hKpack_const_ge1
      have hKpack_const_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := by linarith [hKpc_ge1]
      let Kpc := (MainAppendix.affineLine_packing_constant : ℝ)
      have h_max_ge1 : 1 ≤ max 1 (K_pack * Real.rpow δ (-ε)) := by apply le_max_left
      have hProd_ge1 : 1 ≤ Kpc * max 1 (K_pack * Real.rpow δ (-ε)) := by
        have hKpc_pos : 0 < Kpc := by linarith [hKpc_ge1]
        nlinarith
      have hC1_eq : C₁ = Kpc * max 1 (K_pack * Real.rpow δ (-ε)) := by
        dsimp only [C₁]
        rw [max_eq_right hProd_ge1]
      have hCP_ge1 : 1 ≤ C_PACK := by simpa [C_PACK] using hKpc_ge1
      have hC2_ge1 : 1 ≤ C₂ := hC2_one
      have h_eq : C2_Q = C_PACK * C₂ := by
        dsimp only [C2_Q]
        have h : 1 ≤ C_PACK * C₂ := by nlinarith
        rw [max_eq_right h]
      rw [h_eq]
      have h1 : C₂ ≤ A * Real.rpow K A * C₁ := hC2_bound
      have h2 : K ≤ A * Real.rpow (Real.log (2 / Δ)) A := hK_bound
      have hA_pos : 0 < A := h_small.hA_pos
      have h3 : Real.rpow K A ≤ Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A := by
        apply Real.rpow_le_rpow
        · linarith [hK_one]
        · linarith
        · linarith
      have h4 : C₂ ≤ A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * C₁ := by
        have h41 : A * Real.rpow K A * C₁ ≤ A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * C₁ := by
          have h_pos1 : 0 ≤ C₁ := by positivity
          gcongr <;> linarith
        exact h1.trans h41
      rw [hC1_eq] at h4
      have h6 : C_PACK = Kpc := by rfl
      rw [h6]
      have h7 : Kpc * C₂ ≤
          A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * Kpc^2 *
          max 1 (K_pack * Real.rpow δ (-ε)) := by
        calc Kpc * C₂
          ≤ Kpc * (A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A *
              (Kpc * max 1 (K_pack * Real.rpow δ (-ε)))) :=
            mul_le_mul_of_nonneg_left h4 (by linarith)
        _ = A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * Kpc^2 *
              max 1 (K_pack * Real.rpow δ (-ε)) := by ring
      exact h7.trans h_small.hC2_loss
    have hM_le_3Mqttc : (M : ℝ) ≤ 3 * (M_qttc : ℝ) := by
      have h1 : (M : ℝ) ≤ (m_ceil : ℝ) := Nat.le_ceil M
      have h2 : m_ceil ≤ 2 * k + 1 := by
        omega
      have h3 : (m_ceil : ℝ) ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast h2
      have h4 : (M_qttc : ℝ) = 2 * (k : ℝ) - 1 := by
        have h5 : 1 ≤ k := hk_pos
        have h6 : (M_qttc : ℝ) = ((2 * k - 1 : ℕ) : ℝ) := by rfl
        rw [h6]
        have h7 : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
          <;> simp [Nat.cast_mul] <;> ring
        exact h7
      rw [h4]
      have h5 : (k : ℝ) ≥ 1 := by exact_mod_cast hk_pos
      linarith
    -- Common derived bounds (same structure as P_hi, with M ≤ 3*M_qttc)
    have hP_Q_refine : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ) := by
      have h : (P_lo.card : ℝ) ≤ K * (P_Q.card : ℝ) := hP_card
      have h2 : (P.card : ℝ) ≤ 2 * (P_lo.card : ℝ) := by
        have h3 : P.card ≤ 2 * P_lo.card := by omega
        exact_mod_cast h3
      calc (P.card : ℝ)
        ≤ 2 * (P_lo.card : ℝ) := h2
      _ ≤ 2 * (K * (P_Q.card : ℝ)) := by gcongr
      _ ≤ K_Q * (P_Q.card : ℝ) := by
        have h3 : 0 ≤ (P_Q.card : ℝ) := Nat.cast_nonneg _
        have h4 : 2 * K ≤ K_Q := by
          have h5 : K_Q = 6 * K := by rfl
          rw [h5]
          have h6 : 0 ≤ K := by linarith [hK_one]
          linarith
        have h_goal : 2 * (K * (P_Q.card : ℝ)) ≤ K_Q * (P_Q.card : ℝ) := by
          have h9 : 2 * (K * (P_Q.card : ℝ)) = (2 * K) * (P_Q.card : ℝ) := by ring
          rw [h9]
          exact mul_le_mul_of_nonneg_right h4 h3
        exact h_goal
    have hT_Q_refine : ∀ p ∈ P_Q, (M : ℝ) ≤ K_Q * (T_Q p).card := by
      intro p hp
      have h1 : (M_qttc : ℝ) ≤ K * ((T_Q p).card : ℝ) := hT_Q_size p hp
      calc (M : ℝ)
        ≤ 3 * (M_qttc : ℝ) := hM_le_3Mqttc
      _ ≤ 3 * (K * ((T_Q p).card : ℝ)) := by gcongr
      _ ≤ K_Q * ((T_Q p).card : ℝ) := by
        have h3 : 0 ≤ ((T_Q p).card : ℝ) := Nat.cast_nonneg _
        have h4 : 3 * K ≤ K_Q := by
          have h5 : K_Q = 6 * K := by rfl
          have h6 : 0 ≤ K := by linarith [hK_one]
          rw [h5]
          <;> linarith
        have h4' : 3 * (K * ((T_Q p).card : ℝ)) = (3 * K) * ((T_Q p).card : ℝ) := by ring
        rw [h4']
        exact mul_le_mul_of_nonneg_right h4 h3
    have h_balance_lower : (M : ℝ) * (P.card : ℝ) ≤ K_Q * H_Q * (C_Q.card : ℝ) := by
      have h1 : (P.card : ℝ) ≤ 2 * (P_lo.card : ℝ) := by
        have h2 : P.card ≤ 2 * P_lo.card := by omega
        exact_mod_cast h2
      have h2 : (M : ℝ) ≤ 3 * (M_qttc : ℝ) := hM_le_3Mqttc
      have h3 : (M : ℝ) * (P.card : ℝ) ≤ (3 * (M_qttc : ℝ)) * (2 * (P_lo.card : ℝ)) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
      have h3' : (3 * (M_qttc : ℝ)) * (2 * (P_lo.card : ℝ)) = 6 * (M_qttc : ℝ) * (P_lo.card : ℝ) := by ring
      have h4 : (M_qttc : ℝ) * (P_lo.card : ℝ) ≤ K * H_Q * (C_Q.card : ℝ) := by
        simpa [H_Q] using h_avg_lower
      calc (M : ℝ) * (P.card : ℝ)
        ≤ (3 * (M_qttc : ℝ)) * (2 * (P_lo.card : ℝ)) := h3
      _ = 6 * (M_qttc : ℝ) * (P_lo.card : ℝ) := h3'
      _ = 6 * ((M_qttc : ℝ) * (P_lo.card : ℝ)) := by ring
      _ ≤ 6 * (K * H_Q * (C_Q.card : ℝ)) := by gcongr
      _ = K_Q * H_Q * (C_Q.card : ℝ) := by
        have h5 : K_Q = 6 * K := by rfl
        rw [h5] <;> ring
    have h_sum_lower : (M : ℝ) * (P.card : ℝ) ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
      have h1 : ∀ p ∈ P_Q, (M_qttc : ℝ) ≤ K * ((T_Q p).card : ℝ) := hT_Q_size
      have h2 : (M_qttc : ℝ) * (P_Q.card : ℝ) ≤ K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have h3 : (∑ p ∈ P_Q, (M_qttc : ℝ)) = (M_qttc : ℝ) * (P_Q.card : ℝ) := by
          rw [Finset.sum_const] <;> ring
        have h4 : (∑ p ∈ P_Q, (M_qttc : ℝ)) ≤ ∑ p ∈ P_Q, K * ((T_Q p).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact h1 p hp
        have h5 : (∑ p ∈ P_Q, K * ((T_Q p).card : ℝ)) = K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
          rw [Finset.mul_sum]
        rw [← h3]
        exact h4.trans (by rw [h5])
      have h4 : (P.card : ℝ) ≤ 2 * (P_lo.card : ℝ) := by
        have h41 : P.card ≤ 2 * P_lo.card := by omega
        exact_mod_cast h41
      have h5 : (P_lo.card : ℝ) ≤ K * (P_Q.card : ℝ) := hP_card
      have h6 : (M : ℝ) ≤ 3 * (M_qttc : ℝ) := hM_le_3Mqttc
      have hK_ge1 : 1 ≤ K := hK_one
      have h_nonneg : 0 ≤ (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        apply Finset.sum_nonneg
        intro p _
        exact Nat.cast_nonneg _
      calc (M : ℝ) * (P.card : ℝ)
        ≤ 3 * (M_qttc : ℝ) * (2 * (P_lo.card : ℝ)) := by gcongr
      _ ≤ 3 * (M_qttc : ℝ) * (2 * (K * (P_Q.card : ℝ))) := by gcongr
      _ = 6 * K * ((M_qttc : ℝ) * (P_Q.card : ℝ)) := by ring
      _ ≤ 6 * K * (K * (∑ p ∈ P_Q, (T_Q p).card : ℝ)) := by gcongr
      _ = 6 * K^2 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by ring
      _ ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have h9 : 6 * K^2 ≤ K_Q^3 := by
          have h10 : K_Q = 6 * K := by rfl
          have h11 : 1 ≤ K := hK_one
          rw [h10]
          have h12 : 0 ≤ K := by linarith
          have h13 : K^2 ≤ K^3 := by
            calc K^2 = K^2 * 1 := by ring
              _ ≤ K^2 * K := by gcongr <;> linarith
              _ = K^3 := by ring
          calc 6 * K^2 ≤ 6 * K^3 := by gcongr
            _ ≤ 216 * K^3 := by gcongr <;> linarith
            _ = (6 * K)^3 := by ring
        have h10 : 0 ≤ (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
          apply Finset.sum_nonneg
          intro p _
          exact Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right h9 h10
    have h_balance_upper : H_Q * (C_Q.card : ℝ) ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
      have h1 : H_Q * (C_Q.card : ℝ) ≤ K * (M_qttc : ℝ) * (P_lo.card : ℝ) := by
        simpa [H_Q] using h_avg_upper
      have h2 : (P_lo.card : ℝ) ≤ K * (P_Q.card : ℝ) := hP_card
      have h3 : (M_qttc : ℝ) * (P_Q.card : ℝ) ≤ K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have h4 : (∑ p ∈ P_Q, (M_qttc : ℝ)) = (M_qttc : ℝ) * (P_Q.card : ℝ) := by
          rw [Finset.sum_const] <;> ring
        have h5 : (∑ p ∈ P_Q, (M_qttc : ℝ)) ≤ ∑ p ∈ P_Q, K * ((T_Q p).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hT_Q_size p hp
        have h6 : (∑ p ∈ P_Q, K * ((T_Q p).card : ℝ)) = K * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
          rw [Finset.mul_sum]
        rw [← h4]
        exact h5.trans (by rw [h6])
      have hK_nonneg : 0 ≤ K := by linarith [hK_one]
      have h_sum_nonneg : 0 ≤ (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        apply Finset.sum_nonneg; intro p _; exact Nat.cast_nonneg _
      calc H_Q * (C_Q.card : ℝ)
        ≤ K * (M_qttc : ℝ) * (P_lo.card : ℝ) := h1
      _ ≤ K * (M_qttc : ℝ) * (K * (P_Q.card : ℝ)) := by gcongr
      _ = K^2 * ((M_qttc : ℝ) * (P_Q.card : ℝ)) := by ring
      _ ≤ K^2 * (K * (∑ p ∈ P_Q, (T_Q p).card : ℝ)) := by gcongr
      _ = K^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by ring
      _ ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        have hK_nonneg2 : 0 ≤ K := by linarith [hK_one]
        have h8 : K ≤ K_Q := by
          have h9 : K_Q = 6 * K := by rfl
          rw [h9]
          <;> linarith
        have h7 : K^3 ≤ K_Q^3 := by gcongr
        exact mul_le_mul_of_nonneg_right h7 h_sum_nonneg
    have hH2 : ∀ boldT ∈ C_Q,
        H_Q ≤ ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card := by
      intro boldT hboldT
      have h : (H_nat : ℝ) ≤ ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card :=
        h_pointFiber_inc h_small.hΔ_pos boldT hboldT
      simpa [H_Q] using h
    have hC_Q_sset : IsDeltaSSet Δ s C2_Q (C_Q : Set CoarseTube) := by
      exact hC'_delta_sset
    have hK_Q_lower : Real.rpow Δ (2 * ε) ≤ K_Q :=
      a2_K_Q_lower h_small.hΔ_pos h_small.hΔ_lt_half h_small.hstrip_loss hK_one (by rfl)
    have hP_Q_card_upper : (P_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := by
      have h3 : P_Q ⊆ P := hP_Q_sub.trans hP_lo_sub
      have h4 : (P_Q.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Finset.card_le_card h3
      exact h4.trans hP_card_upper
    have hP_Q_in_square : (P_Q : Set Plane) ⊆ squareSet Δ Q := by
      have h3 : (P_Q : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast hP_Q_sub.trans hP_lo_sub
      exact h3.trans hP_in_square
    have hP_Q_in_ball : (P_Q : Set Plane) ⊆ Metric.closedBall 0 (Real.sqrt 2) := by
      have h3 : (P_Q : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast hP_Q_sub.trans hP_lo_sub
      have h4 : (P : Set Plane) ⊆ Metric.closedBall 0 R := hP_in_ball
      have h5 : Metric.closedBall (0 : Plane) R ⊆ Metric.closedBall (0 : Plane) (Real.sqrt 2) :=
        Metric.closedBall_subset_closedBall hR
      exact Set.Subset.trans h3 (Set.Subset.trans h4 h5)
    have h_slope_bound' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 := by
      intro p hp ℓ hℓ
      have h1 : ℓ ∈ T p := hT_Q_sub p hp hℓ
      have h2 : p ∈ P := hP_lo_sub (hP_Q_sub hp)
      exact h_slope_bound p h2 ℓ h1
    have h_inc' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q p, p ∈ Metric.cthickening (2 * δ) ℓ.1 := by
      intro p hp ℓ hℓ
      have h1 : ℓ ∈ T p := hT_Q_sub p hp hℓ
      have h2 : p ∈ P := hP_lo_sub (hP_Q_sub hp)
      exact h_inc p h2 ℓ h1
    have hT_Q_separated' : ∀ p ∈ P_Q, SeparatedAt (δ / 2) (T_Q p : Set FineTube) := by
      intro p hp
      have h1 : (T_Q p : Set FineTube) ⊆ (T p : Set FineTube) := by exact_mod_cast hT_Q_sub p hp
      have h2 : p ∈ P := hP_lo_sub (hP_Q_sub hp)
      exact (h_tubes_separated p h2).mono h1
    have hT_Q_per_coarse_upper :=
      a2_get_per_coarse_upper δ Δ s ε C₁ M P_Q T_Q C_Q T P_lo P
        hP_Q_sub hP_lo_sub h_finite_sset hT_Q_sub h_tubes_card
        h_small.hδ_le_Δ h_small.hΔ_pos h_small.hM_upper
    have hε_pos : 0 < ε := a2_eps_pos h_small.hΔ_pos h_small.hΔ_lt_half h_small.hstrip_loss
    have hP_lo_in_square : (P_lo : Set Plane) ⊆ squareSet Δ Q := by
      have h1 : (P_lo : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast hP_lo_sub
      exact h1.trans hP_in_square
    have hP_lo_in_ball : (P_lo : Set Plane) ⊆ Metric.closedBall (0 : Plane) (Real.sqrt 2) := by
      have h1 : (P_lo : Set Plane) ⊆ (P : Set Plane) := by exact_mod_cast hP_lo_sub
      have h2 : (P : Set Plane) ⊆ Metric.closedBall (0 : Plane) R := hP_in_ball
      have h3 : Metric.closedBall (0 : Plane) R ⊆ Metric.closedBall (0 : Plane) (Real.sqrt 2) :=
        Metric.closedBall_subset_closedBall hR
      exact (h1.trans h2).trans h3
    have h_slope_bound_lo : ∀ p ∈ P_lo, ∀ ℓ ∈ T p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 :=
      fun p hp ℓ hℓ => h_slope_bound p (hP_lo_sub hp) ℓ hℓ
    have h_inc_lo : ∀ p ∈ P_lo, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1 :=
      fun p hp ℓ hℓ => h_inc p (hP_lo_sub hp) ℓ hℓ
    have hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube) := hC'_sset.2.2.2.2.1
    have hKpack : K_pack ≤ Real.rpow Δ (-2 * ε) / 6 := by
      have h_rpow_neg_eps_pos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos h_small.hΔ_pos _
      have h : 6 * K_pack * Real.rpow Δ (-ε) ≤ Real.rpow Δ (-3 * ε) := h_small.hKpack_loss
      have h3 : Real.rpow Δ (-3 * ε) = Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε) := by
        have h_sum : (-2 * ε) + (-ε) = -3 * ε := by ring
        have h_add : Real.rpow Δ ((-2 * ε) + (-ε)) = Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε) := by
          simpa using Real.rpow_add h_small.hΔ_pos (-2 * ε) (-ε)
        rw [h_sum] at h_add
        exact h_add
      rw [h3] at h
      have h4 : 6 * K_pack ≤ Real.rpow Δ (-2 * ε) :=
        le_of_mul_le_mul_right h h_rpow_neg_eps_pos
      have h5 : K_pack ≤ Real.rpow Δ (-2 * ε) / 6 := by
        calc K_pack
          = (6 * K_pack) / 6 := by ring
        _ ≤ (Real.rpow Δ (-2 * ε)) / 6 := by gcongr
      exact h5
    have hKpack_strong : K_pack ≤ Real.rpow Δ (-ε) / 6 := by
      have h : 6 * K_pack ≤ Real.rpow Δ (-ε) := h_small.hKpack_loss_strong
      calc K_pack
        = (6 * K_pack) / 6 := by ring
      _ ≤ (Real.rpow Δ (-ε)) / 6 := by gcongr
    have hKpack_le_ε : K_pack ≤ Real.rpow Δ (-ε) := by
      have h6 : K_pack ≤ Real.rpow Δ (-ε) / 6 := hKpack_strong
      have h7 : Real.rpow Δ (-ε) / 6 ≤ Real.rpow Δ (-ε) := by
        have h8 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos h_small.hΔ_pos _
        linarith
      linarith [hKpack_strong]
    have hKpack_pos : 0 < K_pack := by
      by_contra h
      have h' : K_pack ≤ 0 := by exact le_of_not_gt h
      have h_rpow_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos h_small.hΔ_pos _
      have h_div_nonpos : Real.rpow Δ (-2 * s + 2 * ε) / K_pack ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos h_rpow_pos.le h'
      have h_contra : (2 : ℝ) ≤ Real.rpow Δ (-2 * s + 2 * ε) / K_pack := h_small.hM_large
      have h6 : (2 : ℝ) ≤ 0 := le_trans h_contra h_div_nonpos
      norm_num at h6
    have h6_loss : (6 : ℝ) ≤ Real.rpow Δ (-ε) := by
      have h1 : 1 ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
        have hK_pos : 0 < K := by linarith [hK_one]
        linarith [hK_bound]
      have h2 : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε) := h_small.hK_loss
      have h3 : (6 : ℝ) ≤ 6 * A * Real.rpow (Real.log (2 / Δ)) A := by
        have h4 : 1 ≤ A * Real.rpow (Real.log (2 / Δ)) A := h1
        nlinarith
      linarith
    have h_absorb_5 : (6 : ℝ)^s ≤ Real.rpow Δ (-ε) :=
      absorb_6_pow_s Δ s ε h_small.hΔ_pos hε_pos (by linarith [hs_pos]) hs1 h6_loss
    have h_pointFiber_upper_local : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
        (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card ≤ Real.rpow Δ (-s - 7 * ε) := by
      intro p hp boldT hboldT
      have h_raw : (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card ≤
          C₁ * (6 : ℝ)^s * (T p).card * Δ^s :=
        h_pointFiber_upper_raw h_small.hΔ_pos p hp boldT hboldT
      have h_card : ((T p).card : ℝ) ≤ M :=
        (h_tubes_card p (hP_lo_sub (hP_Q_sub hp))).2
      have h_C1M : C₁ * M ≤ Real.rpow Δ (-2 * s - 6 * ε) := h_small.hM_upper
      have h_main : ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ) ≤
          (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := by
        calc ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ)
          ≤ C₁ * (6 : ℝ)^s * ((T p).card : ℝ) * Δ^s := by exact_mod_cast h_raw
        _ ≤ C₁ * (6 : ℝ)^s * M * Δ^s := by
          have hpos : 0 ≤ C₁ * (6 : ℝ)^s * Δ^s := by
            have h1 : 0 ≤ C₁ := by linarith [hC1_one]
            have h2 : 0 < (6 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) s
            have h3 : 0 < Δ^s := Real.rpow_pos_of_pos h_small.hΔ_pos s
            positivity
          have h_eq1 : C₁ * (6 : ℝ)^s * ((T p).card : ℝ) * Δ^s = (C₁ * (6 : ℝ)^s * Δ^s) * ((T p).card : ℝ) := by ring
          have h_eq2 : C₁ * (6 : ℝ)^s * M * Δ^s = (C₁ * (6 : ℝ)^s * Δ^s) * M := by ring
          rw [h_eq1, h_eq2]
          exact mul_le_mul_of_nonneg_left h_card hpos
        _ = (6 : ℝ)^s * (C₁ * M) * Δ^s := by ring
        _ ≤ (6 : ℝ)^s * Real.rpow Δ (-2 * s - 6 * ε) * Δ^s := by
          have hpos : 0 ≤ (6 : ℝ)^s * Δ^s := by
            have h1 : 0 < (6 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) s
            have h2 : 0 < Δ^s := Real.rpow_pos_of_pos h_small.hΔ_pos s
            positivity
          have h_eq1 : (6 : ℝ)^s * (C₁ * M) * Δ^s = ((6 : ℝ)^s * Δ^s) * (C₁ * M) := by ring
          have h_eq2 : (6 : ℝ)^s * Real.rpow Δ (-2 * s - 6 * ε) * Δ^s = ((6 : ℝ)^s * Δ^s) * Real.rpow Δ (-2 * s - 6 * ε) := by ring
          rw [h_eq1, h_eq2]
          exact mul_le_mul_of_nonneg_left h_C1M hpos
        _ = (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := by
          have h_add : Real.rpow Δ (-2 * s - 6 * ε) * Δ^s = Real.rpow Δ (-s - 6 * ε) := by
            have h1 : Δ^s = Real.rpow Δ s := by rfl
            rw [h1]
            have h2 := Real.rpow_add h_small.hΔ_pos (-2 * s - 6 * ε) s
            have h3 : (-2 * s - 6 * ε) + s = -s - 6 * ε := by ring
            rw [h3] at h2; exact h2.symm
          have h_goal : (6 : ℝ)^s * Real.rpow Δ (-2 * s - 6 * ε) * Δ^s = (6 : ℝ)^s * (Real.rpow Δ (-2 * s - 6 * ε) * Δ^s) := by ring
          rw [h_goal, h_add] <;> ring
      have h_final : ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ) ≤
          Real.rpow Δ (-s - 7 * ε) := by
        calc ((pointFiber Δ h_small.hΔ_pos T_Q p boldT).card : ℝ)
          ≤ (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := h_main
        _ ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) := by
          have hpos : 0 ≤ Real.rpow Δ (-s - 6 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
          exact mul_le_mul_of_nonneg_right h_absorb_5 hpos
        _ = Real.rpow Δ (-s - 7 * ε) := by
          have h_add := Real.rpow_add h_small.hΔ_pos (-ε) (-s - 6 * ε)
          have h4 : (-ε) + (-s - 6 * ε) = -s - 7 * ε := by ring
          rw [h4] at h_add; exact h_add.symm
      exact_mod_cast h_final
    have hH_Q_coarse_upper : H_Q ≤ (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by
      have h1 : ∃ c ∈ C_Q, True := by
        have h2 : C_Q.Nonempty := hC'_sset.1
        rcases h2 with ⟨c, hc⟩
        exact ⟨c, hc, trivial⟩
      rcases h1 with ⟨c, hc, _⟩
      have h2 : H_Q ≤ ∑ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ) := by
        have hH2' : H_Q ≤ ↑(∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p c).card) := hH2 c hc
        rw [Nat.cast_sum] at hH2'
        exact hH2'
      have h3 : ∑ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ) ≤ (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by
        have h4 : ∀ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ) ≤ Real.rpow Δ (-s - 7 * ε) :=
          fun p hp => h_pointFiber_upper_local p hp c hc
        calc ∑ p ∈ P_Q, ((pointFiber Δ h_small.hΔ_pos T_Q p c).card : ℝ)
          ≤ ∑ p ∈ P_Q, Real.rpow Δ (-s - 7 * ε) := Finset.sum_le_sum h4
        _ = (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by
          rw [Finset.sum_const] <;> ring
      exact h2.trans h3
    have hH_Q_upper : H_Q ≤ Real.rpow Δ (-t - s - 10 * ε) := by
      have h5 : (P_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := hP_Q_card_upper
      have h_rpow_sum : Real.rpow Δ (-t - 3 * ε) * Real.rpow Δ (-s - 7 * ε) = Real.rpow Δ (-t - s - 10 * ε) := by
        have h_sum : (-t - 3 * ε) + (-s - 7 * ε) = -t - s - 10 * ε := by ring
        have h_add : Real.rpow Δ ((-t - 3 * ε) + (-s - 7 * ε)) = Real.rpow Δ (-t - 3 * ε) * Real.rpow Δ (-s - 7 * ε) := by
          simpa using Real.rpow_add h_small.hΔ_pos (-t - 3 * ε) (-s - 7 * ε)
        rw [h_sum] at h_add
        exact h_add.symm
      calc H_Q
        ≤ (P_Q.card : ℝ) * Real.rpow Δ (-s - 7 * ε) := hH_Q_coarse_upper
      _ ≤ Real.rpow Δ (-t - 3 * ε) * Real.rpow Δ (-s - 7 * ε) := by
        have h_rpow1_nonneg : 0 ≤ Real.rpow Δ (-t - 3 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
        have h_rpow2_nonneg : 0 ≤ Real.rpow Δ (-s - 7 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
        exact mul_le_mul hP_Q_card_upper (le_refl _) h_rpow2_nonneg h_rpow1_nonneg
      _ = Real.rpow Δ (-t - s - 10 * ε) := h_rpow_sum
    have hC_card_lower : Real.rpow Δ (-s + 11 * ε) ≤ (C_Q.card : ℝ) :=
      a2_C_card_lower Δ s ε M P.card P_Q.card C_Q.card K_Q H_Q K_pack
        h_small.hΔ_pos h_balance_lower hH_Q_coarse_upper
        (Finset.card_le_card (hP_Q_sub.trans hP_lo_sub))
        hM_lower hK_Q_loss hKpack_strong hKpack_pos hK_Q_pos
        hH_Q_pos (hP_nonempty.card_pos)
    -- New fields for A4
    have hP_Q_card_lower : (P_Q.card : ℝ) ≥ Real.rpow Δ (-t + 5 * ε) := by
      have h_posK : 0 < K_Q := hK_Q_pos
      have h1 : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ) := hP_Q_refine
      have h5 : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ) := hP_card_lower_strong
      have h7 : K_Q ≤ Real.rpow Δ (-2 * ε) := hK_Q_loss_strong
      have h_nneg : 0 ≤ Real.rpow Δ (-t + 5 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
      have h_rpow_sum : Real.rpow Δ (-t + 5 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ (-t + 3 * ε) := by
        have h_add : Real.rpow Δ ((-t + 5 * ε) + (-2 * ε)) =
            Real.rpow Δ (-t + 5 * ε) * Real.rpow Δ (-2 * ε) :=
          Real.rpow_add h_small.hΔ_pos (-t + 5 * ε) (-2 * ε)
        have h_eq : (-t + 5 * ε) + (-2 * ε) = -t + 3 * ε := by ring
        rw [h_eq] at h_add
        exact h_add.symm
      have h9 : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ Real.rpow Δ (-t + 5 * ε) * Real.rpow Δ (-2 * ε) :=
        mul_le_mul_of_nonneg_left h7 h_nneg
      have h9' : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ Real.rpow Δ (-t + 3 * ε) := by
        rw [h_rpow_sum] at * <;> exact h9
      have h10 : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ K_Q * (P_Q.card : ℝ) := by
        have h101 : Real.rpow Δ (-t + 5 * ε) * K_Q ≤ Real.rpow Δ (-t + 3 * ε) := h9'
        have h102 : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ) := h5
        have h103 : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ) := h1
        exact le_trans h101 (le_trans h102 h103)
      have h13 : K_Q * (P_Q.card : ℝ) = (P_Q.card : ℝ) * K_Q := by ring
      rw [h13] at h10
      exact le_of_mul_le_mul_right h10 h_posK
    have hP_Q_separated : SeparatedAt δ (P_Q : Set Plane) := by
      have h1 : (P_Q : Set Plane) ⊆ (P : Set Plane) := by
        exact_mod_cast hP_Q_sub.trans hP_lo_sub
      exact hP_separated.mono h1
    have hP_Q_sset : IsDeltaSSet δ t (Real.rpow Δ (-t - 10 * ε)) (P_Q : Set Plane) := by
      have h_sset_constraint : C_P * K_Q * 81 ≤ Real.rpow Δ (-t - 10 * ε) := by
        have h1 : C_P * 81 ≤ Real.rpow Δ (-t - 8 * ε) := hC_P_bound
        have h2 : K_Q ≤ Real.rpow Δ (-2 * ε) := hK_Q_loss_strong
        have h3 : C_P * K_Q * 81 = (C_P * 81) * K_Q := by ring
        rw [h3]
        have h4 : 0 ≤ Real.rpow Δ (-t - 8 * ε) := Real.rpow_nonneg h_small.hΔ_pos.le _
        have h6 : (C_P * 81) * K_Q ≤ (Real.rpow Δ (-t - 8 * ε)) * (Real.rpow Δ (-2 * ε)) :=
          mul_le_mul h1 h2 (by positivity) h4
        have h7 : (Real.rpow Δ (-t - 8 * ε)) * (Real.rpow Δ (-2 * ε)) = Real.rpow Δ (-t - 10 * ε) := by
          have h8 := Real.rpow_add h_small.hΔ_pos (-t - 8 * ε) (-2 * ε)
          have h9 : (-t - 8 * ε) + (-2 * ε) = -t - 10 * ε := by ring
          rw [h9] at h8; exact h8.symm
        rw [h7] at h6; exact h6
      exact gap3_hP_Q_sset hP_sset (hP_Q_sub.trans hP_lo_sub) hP_Q_separated hδ_pos
        hP_Q_refine hK_Q_pos h_sset_constraint
    have hC_Q_slope_bound : ∀ boldT ∈ C_Q, |tubeSlope boldT| ≤ 1 :=
      hC'_slope
    have hC_Q_v : ∀ ℓ ∈ C_Q, (LemmaE.getDirV ℓ) 1 ≠ 0 :=
      hC'_v
    have hC_Q_b : ∀ ℓ ∈ C_Q, |tubeIntercept ℓ| ≤ 3 :=
      hC'_b
    have h_strip : ∀ ℓ ∈ C_Q, ∃ (p : Plane), p ∈ squareSet Δ Q ∧ |p 1| ≤ Real.sqrt 2 ∧
        |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ := by
      intro ℓ hℓ
      rcases hC'_near ℓ hℓ with ⟨p, hp, h_near⟩
      have hp_in_P : p ∈ P := hP_lo_sub (hP_Q_sub hp)
      have hp_square : p ∈ squareSet Δ Q := hP_in_square hp_in_P
      have h_p1_sqrt2 : |p 1| ≤ Real.sqrt 2 := by
        have h1 : p ∈ Metric.closedBall (0 : Plane) R := hP_in_ball hp_in_P
        have h2 : ‖p‖ ≤ R := by simpa [Metric.mem_closedBall] using h1
        have h3 : |p 1| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 1
        have h4 : R ≤ Real.sqrt 2 := hR
        linarith
      have h_final : |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ := h_near
      exact ⟨p, hp_square, h_p1_sqrt2, h_final⟩
    have hΔ_lt_one : Δ < 1 := by linarith [h_small.hΔ_lt_half]
    have hC_Q_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)) :=
      hC_Q_cover_transfer_main h_small.hΔ_pos h_small.hΔ_lt_half hC_Q_sep hC_Q_v hC_Q_slope_bound hC_Q_b h_strip
    have hC_Q_slope_sset : IsDeltaSSet Δ s (Real.rpow Δ (-25 * ε)) (tubeSlope '' (C_Q : Set CoarseTube)) :=
      hC_Q_slope_sset_main h_small.hΔ_pos hε_pos hΔ_lt_one hs_pos hs1
        hC'_delta_sset hC_Q_sep hC_Q_v hC_Q_slope_bound hC_Q_b hC2_Q_loss h_small.hslope_sset_const hC_Q_cover_transfer h_strip
    have hC_Q_slope_cover_lower : ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) ≤
        Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)) :=
      hC_Q_slope_cover_lower_main h_small.hΔ_pos hε_pos hΔ_lt_one hs_pos
        hC_Q_sep hC_card_lower h_small.hcover_lower_pack hC_Q_cover_transfer
    have hC_card_upper_weak : (C_Q.card : ℝ) ≤ Real.rpow Δ (-1 - 5 * ε) := by
      have h1 : (C_Q.card : ℝ) ≤ (42 : ℝ) * (40 * (4 : ℝ) + 110) / Δ :=
        affineLine_strip_packing h_small.hΔ_pos hΔ_lt_one 4 (by norm_num) C_Q
          hC_Q_sep hC_Q_v hC_Q_slope_bound hC_Q_b Q h_strip
      have h2 : (42 : ℝ) * (40 * (4 : ℝ) + 110) ≤ Real.rpow Δ (-5 * ε) := h_small.hstrip_loss
      have h3 : (C_Q.card : ℝ) ≤ Real.rpow Δ (-5 * ε) / Δ := by
        calc (C_Q.card : ℝ)
          ≤ (42 : ℝ) * (40 * (4 : ℝ) + 110) / Δ := h1
        _ ≤ Real.rpow Δ (-5 * ε) / Δ := by gcongr; exact h_small.hΔ_pos.le
      have h4 : Real.rpow Δ (-5 * ε) / Δ = Real.rpow Δ (-1 - 5 * ε) := by
        have h5 : Real.rpow Δ (-5 * ε) / Δ = Real.rpow Δ (-5 * ε) * Δ⁻¹ := by ring
        rw [h5]
        have h6 : Δ⁻¹ = Real.rpow Δ (-1 : ℝ) := by
          simp [Real.rpow_neg h_small.hΔ_pos.le]
          <;> field_simp [h_small.hΔ_pos.ne'] <;> ring
        rw [h6]
        have h7 : Real.rpow Δ (-5 * ε) * Real.rpow Δ (-1 : ℝ) = Real.rpow Δ ((-5 * ε) + (-1 : ℝ)) :=
          (Real.rpow_add h_small.hΔ_pos (-5 * ε) (-1 : ℝ)).symm
        rw [h7]
        have h8 : (-5 * ε) + (-1 : ℝ) = -1 - 5 * ε := by ring
        rw [h8]
      rw [h4] at h3
      exact h3
    have hT_Q_sset : ∀ p ∈ P_Q,
        IsDeltaSSet δ s
          (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * (MainAppendix.affineLine_packing_constant : ℝ))
          (T_Q p : Set FineTube) := by
      intro p hp
      let C := max 1 (K_pack * Real.rpow δ (-ε))
      have hC_pos : 0 < C := by positivity
      have h_pack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) :=
        lt_of_lt_of_le zero_lt_one h_small.hKpack_const_ge1
      have hP_in_P : p ∈ P := hP_lo_sub (hP_Q_sub hp)
      exact a2_transfer_tube_sset hδ_pos hC_pos hK_Q_pos hM_pos h_pack_pos
        (h_tubes_sset p hP_in_P)
        (hT_Q_sub p hp)
        (hT_Q_separated' p hp)
        (h_tubes_card p hP_in_P).2
        (hT_Q_refine p hp)
    have hT_Q_card_upper : ∀ p ∈ P_Q, (T_Q p).card ≤ M := by
      intro p hp
      have h1 : (T_Q p : Set FineTube) ⊆ (T p : Set FineTube) := by exact_mod_cast hT_Q_sub p hp
      have h2 : (↑(T_Q p).card : ℝ) ≤ ↑(T p).card := by exact_mod_cast Finset.card_le_card h1
      have h3 : p ∈ P := hP_lo_sub (hP_Q_sub hp)
      have h4 : (↑(T p).card : ℝ) ≤ M := (h_tubes_card p h3).2
      exact le_trans h2 h4
    -- Restrict T_Q to P_Q (see branch 1 for explanation)
    let T_Q' : Plane → Finset FineTube := fun p => if h : p ∈ P_Q then T_Q p else ∅
    have hT_Q'_eq : ∀ p ∈ P_Q, T_Q' p = T_Q p := by
      intro p hp; simp [T_Q', hp]
    have hT_Q_refine' : ∀ p ∈ P_Q, (M : ℝ) ≤ K_Q * (T_Q' p).card := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_refine p hp
    have hH2' : ∀ boldT ∈ C_Q, H_Q ≤ ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card := by
      intro boldT hboldT
      have h_sum : ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card =
          ∑ p ∈ P_Q, (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card := by
        apply Finset.sum_congr rfl
        intro p hp
        have h_eq1 : T_Q' p = T_Q p := hT_Q'_eq p hp
        have h_pf_eq : pointFiber Δ h_small.hΔ_pos T_Q' p boldT = pointFiber Δ h_small.hΔ_pos T_Q p boldT := by
          unfold pointFiber
          rw [h_eq1]
        rw [h_pf_eq]
      rw [h_sum]; exact hH2 boldT hboldT
    have h_balance_upper' : H_Q * (C_Q.card : ℝ) ≤ K_Q^3 * (∑ p ∈ P_Q, (T_Q' p).card : ℝ) := by
      have h_sum : (∑ p ∈ P_Q, (T_Q' p).card : ℝ) = (∑ p ∈ P_Q, (T_Q p).card : ℝ) := by
        apply Finset.sum_congr rfl; intro p hp; rw [hT_Q'_eq p hp]
      rw [h_sum]; exact h_balance_upper
    have h_slope_bound'' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q' p,
        (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3 := by
      intro p hp ℓ hℓ; rw [hT_Q'_eq p hp] at hℓ; exact h_slope_bound' p hp ℓ hℓ
    have h_inc'' : ∀ p ∈ P_Q, ∀ ℓ ∈ T_Q' p, p ∈ Metric.cthickening (2 * δ) ℓ.1 := by
      intro p hp ℓ hℓ; rw [hT_Q'_eq p hp] at hℓ; exact h_inc' p hp ℓ hℓ
    have hT_Q_separated'' : ∀ p ∈ P_Q, SeparatedAt (δ / 2) (T_Q' p : Set FineTube) := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_separated' p hp
    have hT_Q_per_coarse_upper' : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
        assignedCountMetric Δ T_Q' p boldT ≤ Real.rpow Δ (-s - 6 * ε) := by
      intro p hp boldT hboldT
      have h_eq : assignedCountMetric Δ T_Q' p boldT = assignedCountMetric Δ T_Q p boldT := by
        simp [assignedCountMetric, hT_Q'_eq p hp]
      rw [h_eq]
      exact hT_Q_per_coarse_upper p hp boldT hboldT
    have h_pointFiber_upper' : ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
        (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card ≤ Real.rpow Δ (-s - 7 * ε) := by
      intro p hp boldT hboldT
      have h_eq : (pointFiber Δ h_small.hΔ_pos T_Q' p boldT).card = (pointFiber Δ h_small.hΔ_pos T_Q p boldT).card := by
        simp only [pointFiber]
        <;> rw [hT_Q'_eq p hp]
      rw [h_eq]
      exact h_pointFiber_upper_local p hp boldT hboldT
    have hT_Q_sset' : ∀ p ∈ P_Q,
        IsDeltaSSet δ s (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * (MainAppendix.affineLine_packing_constant : ℝ))
          (T_Q' p : Set FineTube) := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_sset p hp
    have hT_Q_card_upper' : ∀ p ∈ P_Q, (T_Q' p).card ≤ M := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_card_upper p hp
    have hT_Q_sub' : ∀ p ∈ P_Q, T_Q' p ⊆ T p := by
      intro p hp; rw [hT_Q'_eq p hp]; exact hT_Q_sub p hp
    have hT_Q_empty_outside : ∀ p, p ∉ P_Q → T_Q' p = ∅ := by
      intro p hp
      simp [T_Q', hp]
    exact ⟨h_small.hΔ_pos, P_Q, T_Q', C_Q, K_Q, C2_Q, H_Q, (P.card : ℝ), M, hM_upper,
      hP_Q_refine, hT_Q_refine', hC_Q_sset, hH2', h_balance_lower, h_balance_upper',
      hK_Q_pos, hK_Q_loss, hC2_Q_loss, hH_Q_pos, hH_Q_one, hH_Q_upper, hK_Q_lower,
      hC_card_lower, hP_Q_card_upper, hP_Q_in_square, hP_Q_in_ball,
      h_slope_bound'', h_inc'', hT_Q_separated'', hT_Q_per_coarse_upper',
      h_pointFiber_upper',
      K_pack, hKpack_pos, hKpack, hKpack_le_ε, hT_Q_sset', hT_Q_card_upper',
      hP_Q_card_lower, hP_Q_separated, hP_Q_sset,
      hC_Q_sep, hC_Q_v, hC_Q_slope_bound, hC_Q_b, hC_Q_slope_sset, hC_Q_slope_cover_lower, hC_Q_cover_transfer,
      T_Delta_global, h_prove_sub P_Q T_Q C_Q (hP_Q_sub.trans hP_lo_sub) hT_Q_sub h_parent_witness,
      hM_lower, hP_card_lower_strong, hC_card_upper_weak,
      T, hT_Q_sub', hT_Q_empty_outside⟩

end DirecretisedFurstenbergEstimate.AppendixA.A2

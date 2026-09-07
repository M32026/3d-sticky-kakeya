module

/-
  Base Case Uniform with Data — COMPLETE

  Implements the n=1 base case for the restructured Prop73 induction
  with CombiningExtraHypotheses_v2 (caller-supplied ε_inc / incidence gain).

  Branches:
  - bad: base_case_bad_branch (trivial bound)
  - normal: base_case_normal_branch (prop5, v2 wrapper)
  - good: base_case_good_uniform_v2 (prop5 + ε_inc incidence, adapted)

  Whiteprint: combining_theorem_genuine / base_case_uniform_with_data
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BaseBad
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BaseNormal
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BaseGood
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BetweenScalesConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSourceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseIncidenceGeometricBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.IncidenceHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseIncidenceWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RealAnalysis

@[expose] public section

open scoped ENNReal NNReal

set_option maxHeartbeats 500000

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73BaseCase

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DirecretisedFurstenbergEstimate.RegularIncidence

/-! ### Good branch v2 (adapted for ε_inc) -/

/-- Good scale branch with CombiningExtraHypotheses_v2 (ε_inc exponent).

    Large M: uniform_prop5 at exponent u = min(t,1), log absorption.
    Small M: improved incidence bound with ε_inc + new exponent condition. -/
lemma base_case_good_uniform_v2
    {s t τ ε_G η ε_N C_P lam C C' ε_inc C_point : ℝ} {k M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
    {C_between : Fin 1 → ℝ} {t_j : ℝ}
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (hextra_v2 : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc 1 lam k M config Δ scaleClass)
    (hP_set_tj : IsFinsetDeltaSSet (dyadicDelta k) (min t_j 1) C_point
        (finsetDyadicToDSquare config.P₀))
    (hC_point_pos : 0 < C_point)
    (hC_point_ge1 : 1 ≤ C_point)
    (hC_point_bound : C_point ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_G))
    (h_improved_incidence : (config.T₀.card : ENNReal) ≥ ENNReal.ofReal (Real.rpow (dyadicDelta k) (-(2 * s + ε_inc))))
    (u : ℝ) (hu_eq : u = min t 1)
    (K_good : ℝ) (hK_pos : 0 < K_good)
    (hK_spec_u : KSpec s u K_good)
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hus : s < u) (hu1 : u ≤ 1)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (hεN : 0 < ε_N)
    (hCP : 1 ≤ C_P)
    (hlam : 0 < lam)
    (h_log_ge : Real.log (1 / dyadicDelta k) ≥ K_good * conversionKGeo t_j * 13 * Real.rpow 2 s)
    (hk_ge_2 : 2 ≤ k)
    (h_good : scaleClass 0 = ScaleClass.good t_j)
    (hC_ge : K_good + C_P + 1 ≤ C) (hC'_ge : 1 ≤ C') :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C'
        lam s ε_N η 1 Δ scaleClass) := by
  classical
  have h1s : 0 < 1 - s := by linarith
  have h_us_pos : 0 < u - s := by linarith

  let δ : ℝ := dyadicDelta k
  let C₁ : ℝ := Real.rpow δ (-lam)
  let L : ℝ := Real.log (1 / δ)
  let δEI : ℝ := DiscretisedFurstenbergEstimate.δ k

  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδEI_pos : 0 < δEI := DiscretisedFurstenbergEstimate.δ_pos k
  have hδ_eq : δ = δEI := by
    simp [δ, δEI, dyadicDelta, DiscretisedFurstenbergEstimate.δ] <;> ring
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    have h1 : (k : ℕ) ≥ 2 := hk_ge_2
    have h2 : δ = ((2 : ℝ)^k)⁻¹ := by simp [δ, dyadicDelta] <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^k ≥ 4 := by
      have h4 : (2 : ℝ)^k ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢; exact h4
    have h5 : 0 < (2 : ℝ)^k := by positivity
    have h6 : ((2 : ℝ)^k)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
    norm_num at h6 ⊢; exact h6
  have hδ_lt_one : δ < 1 := by linarith
  have hδ_le_one : δ ≤ 1 := by linarith

  have hC₁_pos : 0 < C₁ := Real.rpow_pos_of_pos hδ_pos _
  have hC₁_ge1 : 1 ≤ C₁ := by
    have h1 : 0 < Real.rpow δ lam := Real.rpow_pos_of_pos hδ_pos lam
    have h2 : Real.rpow δ lam < 1 := Real.rpow_lt_one (by linarith) (by linarith) hlam
    have h3 : C₁ = (Real.rpow δ lam)⁻¹ := by
      simp [C₁, Real.rpow_neg hδ_pos.le] <;> field_simp <;> ring
    rw [h3]
    have h4 : 1 ≤ (Real.rpow δ lam)⁻¹ := by
      have h5 : Real.rpow δ lam ≤ 1 := h2.le
      exact (one_le_inv₀ h1).mpr h5
    exact h4

  have hCP_pos : 0 < C_P := by linarith
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hM_pos : 0 < M := hcfg.hM_pos

  have h_u_le_min_tj : u ≤ min t_j 1 := by
    have h1 : t ≤ t_j := hextra_v2.h_tj_ge_t 0 t_j h_good
    have h2 : u ≤ t := by rw [hu_eq] <;> exact min_le_left t 1
    have h3 : u ≤ 1 := hu1
    exact le_min (le_trans h2 h1) h3

  have hP_set_u : IsFinsetDeltaSSet (dyadicDelta k) u C_point
      (finsetDyadicToDSquare config.P₀) :=
    finset_deltaSSet_weaken_exponent hP_set_tj (by linarith) h_u_le_min_tj hC_point_ge1

  have hP_nonempty : config.P₀.Nonempty := by
    have h1 : (finsetDyadicToDSquare config.P₀ : Set (DSquare k)).Nonempty := hP_set_u.1
    rcases h1 with ⟨p', hp'⟩
    have h2 : p' ∈ finsetDyadicToDSquare config.P₀ := by exact_mod_cast hp'
    have h3 : ∃ (p : DyadicSquare k), p ∈ config.P₀ ∧ dyadicSquareToDSquare p = p' := by
      simpa [finsetDyadicToDSquare, Finset.mem_image] using h2
    rcases h3 with ⟨p, hp, _⟩
    exact ⟨p, hp⟩

  have h_mem_iff : ∀ (p' : DSquare k),
      p' ∈ finsetDyadicToDSquare config.P₀ ↔
      dSquareToDyadicSquare p' ∈ config.P₀ := by
    intro p'
    simp [finsetDyadicToDSquare, Finset.mem_image]
    constructor
    · rintro ⟨p_dy, hpin, rfl⟩
      have h_rt : dSquareToDyadicSquare (dyadicSquareToDSquare p_dy) = p_dy := by
        cases p_dy
        rfl
      rw [h_rt] <;> exact hpin
    · intro hpin
      refine' ⟨dSquareToDyadicSquare p', hpin, _⟩
      cases p'
      rfl

  have hδ_pow_eq : δ = 1 / (2 : ℝ)^k := by
    simp [δ, dyadicDelta] <;> ring

  have h_index_bounds : ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ) := by
    intro p hp
    let p_dy := dSquareToDyadicSquare p
    have hpin : p_dy ∈ config.P₀ := (h_mem_iff p).mp hp
    exact hB1.h_squares_unit p_dy hpin

  have h_diam : ∀ (p q : DSquare k),
      p ∈ finsetDyadicToDSquare config.P₀ →
      q ∈ finsetDyadicToDSquare config.P₀ → dist p q ≤ 3 := by
    intro p q hp hq
    have hpb := h_index_bounds p hp
    have hqb := h_index_bounds q hq
    have hpi1 : 0 ≤ (p.i : ℝ) := by exact_mod_cast hpb.1
    have hpi2 : (p.i : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hpb.2.1
    have hpj1 : 0 ≤ (p.j : ℝ) := by exact_mod_cast hpb.2.2.1
    have hpj2 : (p.j : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hpb.2.2.2
    have hqi1 : 0 ≤ (q.i : ℝ) := by exact_mod_cast hqb.1
    have hqi2 : (q.i : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hqb.2.1
    have hqj1 : 0 ≤ (q.j : ℝ) := by exact_mod_cast hqb.2.2.1
    have hqj2 : (q.j : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hqb.2.2.2
    have h1 : |(p.i : ℝ) - (q.i : ℝ)| < (2 ^ k : ℝ) := by rw [abs_lt]; constructor <;> linarith
    have h2 : |(p.j : ℝ) - (q.j : ℝ)| < (2 ^ k : ℝ) := by rw [abs_lt]; constructor <;> linarith
    have h3 : |(p.i : ℝ) - (q.i : ℝ)| * δ < 1 := by
      have h4 : |(p.i : ℝ) - (q.i : ℝ)| * δ < ((2 ^ k : ℝ) * δ) := by gcongr
      have h5 : ((2 ^ k : ℝ) * δ) = 1 := by rw [hδ_pow_eq] <;> field_simp <;> ring
      linarith
    have h6 : |(p.j : ℝ) - (q.j : ℝ)| * δ < 1 := by
      have h7 : |(p.j : ℝ) - (q.j : ℝ)| * δ < ((2 ^ k : ℝ) * δ) := by gcongr
      have h8 : ((2 ^ k : ℝ) * δ) = 1 := by rw [hδ_pow_eq] <;> field_simp <;> ring
      linarith
    have h9 : dist p q = dist p.toPoint q.toPoint := rfl
    rw [h9]
    have h10 : dist p.toPoint q.toPoint ≤ 1 := by
      simp only [DSquare.toPoint, Prod.dist_eq, Real.dist_eq]
      apply max_le
      · have h11 : |(p.i : ℝ) * δEI - (q.i : ℝ) * δEI| = |(p.i : ℝ) - (q.i : ℝ)| * δEI := by
          have h_eq : (p.i : ℝ) * δEI - (q.i : ℝ) * δEI = ((p.i : ℝ) - (q.i : ℝ)) * δEI := by ring
          rw [h_eq, abs_mul, abs_of_pos hδEI_pos]
        exact h11 ▸ (hδ_eq ▸ h3.le)
      · have h12 : |(p.j : ℝ) * δEI - (q.j : ℝ) * δEI| = |(p.j : ℝ) - (q.j : ℝ)| * δEI := by
          have h_eq : (p.j : ℝ) * δEI - (q.j : ℝ) * δEI = ((p.j : ℝ) - (q.j : ℝ)) * δEI := by ring
          rw [h_eq, abs_mul, abs_of_pos hδEI_pos]
        exact h12 ▸ (hδ_eq ▸ h6.le)
    linarith

  have h_unit : ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 := by
    intro p hp x hx
    have hpb := h_index_bounds p hp
    have hpi1 : 0 ≤ (p.i : ℝ) := by exact_mod_cast hpb.1
    have hpi2 : (p.i : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hpb.2.1
    have hx1 : (p.i : ℝ) * δEI ≤ x.1 := hx.1
    have hx2 : x.1 < ((p.i : ℝ) + 1) * δEI := hx.2.1
    have h_nonneg : 0 ≤ x.1 := by
      have h : 0 ≤ (p.i : ℝ) * δEI := mul_nonneg hpi1 hδEI_pos.le
      linarith
    have h_lt_one : x.1 < 1 := by
      have h51 : p.i + 1 ≤ (2 ^ k : ℤ) := by
        have h52 : p.i < (2 ^ k : ℤ) := hpb.2.1
        linarith
      have h5 : (p.i : ℝ) + 1 ≤ (2 ^ k : ℝ) := by exact_mod_cast h51
      have h6 : ((p.i : ℝ) + 1) * δEI ≤ ((2 ^ k : ℝ) * δEI) := by gcongr
      have h7 : ((2 ^ k : ℝ) * δEI) = 1 := by
        have h8 : (2 ^ k : ℝ) * δEI = (2 ^ k : ℝ) * δ := by rw [hδ_eq]
        rw [h8, hδ_pow_eq] <;> field_simp <;> ring
      linarith
    rw [abs_le]
    constructor <;> linarith

  let γ : ℝ := (η + 2 * ε_G) * (1 - s) / (u - s)
  have hγ_pos : 0 < γ := by
    have h1 : 0 < η + 2 * ε_G := by linarith
    have h2 : 0 < 1 - s := by linarith
    have h3 : 0 < u - s := h_us_pos
    positivity
  let α : ℝ := (u - s) / (1 - s)
  have hα_nonneg : 0 ≤ α := by
    have h1 : 0 ≤ u - s := by linarith
    have h2 : 0 < 1 - s := by linarith
    exact div_nonneg h1 (by linarith)
  have hγ_α_eq : γ * α = η + 2 * ε_G := by
    simp only [γ, α]
    field_simp [h1s.ne', h_us_pos.ne'] <;> ring

  have hL_gt_one : 1 < L := by
    have h3 : 1 / δ ≥ 4 := by
      have h4 : δ ≤ 1 / 4 := hδ_le_quarter
      have h5 : 0 < δ := hδ_pos
      calc 1 / δ ≥ 1 / (1 / 4) := by gcongr
      _ = 4 := by norm_num
    have h4 : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    have h5 : (1 : ℝ) < Real.log 4 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h8] at h7; exact h7
    linarith
  have hL_pos : 0 < L := by linarith
  have hL_ge_one : 1 ≤ L := by linarith

  have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
  have hΔ1 : Δ 1 = δ := hcfg.hΔ_end

  let K_geo : ℝ := conversionKGeo t_j
  have hK_geo_pos : 0 < K_geo := by
    dsimp only [K_geo, conversionKGeo]
    have h : 0 < Real.rpow 2 t_j := Real.rpow_pos_of_pos (by norm_num) t_j
    positivity
  let K_geo' : ℝ := K_good * K_geo * 13 * Real.rpow 2 s
  have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have hK_geo'pos : 0 < K_geo' := by
    dsimp only [K_geo']; positivity

  have h_inv_bound : 1 / C_point ≥ Real.rpow δ ε_G / (K_geo * L ^ C_P) := by
    have h1 : 0 < K_geo * L ^ C_P := by positivity
    have h2 : 1 / C_point ≥ 1 / (K_geo * L ^ C_P * Real.rpow δ (-ε_G)) := by gcongr
    have h3 : 1 / (K_geo * L ^ C_P * Real.rpow δ (-ε_G)) = Real.rpow δ ε_G / (K_geo * L ^ C_P) := by
      have h4 : 0 < Real.rpow δ (-ε_G) := Real.rpow_pos_of_pos hδ_pos _
      have h51 : Real.rpow δ (-ε_G) = (Real.rpow δ ε_G)⁻¹ := Real.rpow_neg hδ_pos.le ε_G
      have h5 : (Real.rpow δ (-ε_G))⁻¹ = Real.rpow δ ε_G := by
        rw [h51]
        field_simp
      have h6 : 1 / (K_geo * L ^ C_P * Real.rpow δ (-ε_G)) =
          (1 / (K_geo * L ^ C_P)) * (Real.rpow δ (-ε_G))⁻¹ := by
        field_simp [h4.ne'] <;> ring
      rw [h6, h5] <;> ring
    rw [h3] at h2; exact h2

  have hC_K_C_P_ge_one : 1 ≤ C - K_good - C_P := by linarith

  have h_key : L ^ (C - K_good - C_P) ≥ K_geo' * Real.rpow δ ε_N := by
    have h1 : L ^ (C - K_good - C_P) ≥ L := by
      have h2 : 1 ≤ L := hL_ge_one
      have h3 : 1 ≤ C - K_good - C_P := hC_K_C_P_ge_one
      have h4 : L ^ (1 : ℝ) ≤ L ^ (C - K_good - C_P) := by exact (Real.rpow_le_rpow_left_iff hL_gt_one).mpr hC_K_C_P_ge_one
      have h5 : L ^ (1 : ℝ) = L := by simp
      rw [h5] at h4; exact h4
    have h4 : L ≥ K_geo' := h_log_ge
    have h5 : K_geo' * Real.rpow δ ε_N ≤ K_geo' := by
      have h6 : Real.rpow δ ε_N ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hεN.le
      have h7 : 0 ≤ K_geo' := by positivity
      exact (mul_le_mul_of_nonneg_left h6 h7).trans_eq (by ring)
    linarith

  have h_absorb : (1 / K_geo') * L ^ (-K_good - C_P) ≥ L ^ (-C) * Real.rpow δ ε_N := by
    have h15 : L ^ (-K_good - C_P) = L ^ (C - K_good - C_P) * L ^ (-C) := by
      rw [← Real.rpow_add hL_pos] <;> ring_nf
    rw [h15]
    have h16 : 0 < L ^ (-C) := Real.rpow_pos_of_pos hL_pos _
    have h17 : L ^ (C - K_good - C_P) ≥ K_geo' * Real.rpow δ ε_N := h_key
    calc
      (1 / K_geo') * (L ^ (C - K_good - C_P) * L ^ (-C))
        = L ^ (-C) * ((1 / K_geo') * L ^ (C - K_good - C_P)) := by ring
      _ ≥ L ^ (-C) * ((1 / K_geo') * (K_geo' * Real.rpow δ ε_N)) := by gcongr
      _ = L ^ (-C) * Real.rpow δ ε_N := by
        field_simp [hK_geo'pos.ne'] <;> ring

  have hγ_η_le : γ + η ≤ ε_inc := by
    have h_denom : u - s = min t 1 - s := by
      have h9 : u = min t 1 := hu_eq
      rw [h9] <;> ring
    have h : γ = (η + 2 * ε_G) * (1 - s) / (min t 1 - s) := by
      simp only [γ, h_denom]
    rw [h]
    exact hextra_v2.h_exp_condition

  by_cases hM_large : (M : ℝ) ≥ Real.rpow δ (-s - γ)
  · -- LARGE M CASE
    have h_wrapper := uniform_prop5_wrapper_with_K
      (t := u) (hK_pos := hK_pos) (hK_spec := hK_spec_u)
      (config := config) (hn_ge_2 := hk_ge_2) (hM_pos := hM_pos)
      (hP_nonempty := hP_nonempty) (hCP := hC_point_pos) (hCP_ge1 := hC_point_ge1)
      (hC₁ := hC₁_pos) (hC1_ge1 := hC₁_ge1)
      (hs_nonneg := hs_nonneg) (hP_set := hP_set_u)
      (h_slope := hextra_v2.h_slope)
      (h_diam := h_diam) (h_unit := h_unit)

    have h_main_raw : (config.T₀.card : ℝ) ≥
        (1 / K_good) * L ^ (-K_good) *
          (1 / (C_point * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by
      simpa [L, δ, α, C₁] using h_wrapper

    have h_inv_C1 : (1 : ℝ) / C₁ = Real.rpow δ lam := by
      have h_pos1 : 0 < Real.rpow δ (-lam) := Real.rpow_pos_of_pos hδ_pos (-lam)
      have h_eq : Real.rpow δ (-lam) * Real.rpow δ lam = 1 := by
        have h := Real.rpow_add hδ_pos (-lam) lam
        have h5 : -lam + lam = 0 := by ring
        rw [h5] at h; simpa using h.symm
      have h_goal : (1 : ℝ) / Real.rpow δ (-lam) = Real.rpow δ lam := by
        field_simp [h_pos1.ne'] <;> linarith
      exact h_goal

    have h_simp_coeff : (1 / K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s))) ≥
        (1 / K_geo') * L ^ (-C_P) * Real.rpow δ (ε_G + lam) := by
      have h1 : (1 / K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s))) =
          (1 / K_good) * (1 / C_point) * (1 / (13 * Real.rpow 2 s)) * (1 / C₁) := by
        field_simp [hC_point_pos.ne', hC₁_pos.ne'] <;> ring
      rw [h1]
      have h2 : (1 / C_point) ≥ Real.rpow δ ε_G / (K_geo * L ^ C_P) := h_inv_bound
      have h3 : (1 / K_good) * (1 / C_point) * (1 / (13 * Real.rpow 2 s)) * (1 / C₁) ≥
          (1 / K_good) * (Real.rpow δ ε_G / (K_geo * L ^ C_P)) * (1 / (13 * Real.rpow 2 s)) * (1 / C₁) := by
        gcongr
      have h4 : (1 / K_good) * (Real.rpow δ ε_G / (K_geo * L ^ C_P)) * (1 / (13 * Real.rpow 2 s)) * (1 / C₁) =
          (1 / K_geo') * L ^ (-C_P) * Real.rpow δ (ε_G + lam) := by
        dsimp only [K_geo']
        have h5 : L ^ (-C_P) = 1 / (L ^ C_P) := by
          have h51 : L ^ (-C_P) = (L ^ C_P)⁻¹ := Real.rpow_neg hL_pos.le C_P
          rw [h51] <;> ring
        rw [h5, h_inv_C1]
        field_simp [hK_geo_pos.ne', hL_pos.ne']
        have h6 : Real.rpow δ ε_G * Real.rpow δ lam = Real.rpow δ (ε_G + lam) :=
          (Real.rpow_add hδ_pos ε_G lam).symm
        rw [h6] <;> ring
      have h_goal : (1 / K_good) * (1 / C_point) * (1 / (13 * Real.rpow 2 s)) * (1 / C₁) ≥
          (1 / K_geo') * L ^ (-C_P) * Real.rpow δ (ε_G + lam) := by
        calc
          (1 / K_good) * (1 / C_point) * (1 / (13 * Real.rpow 2 s)) * (1 / C₁)
            ≥ (1 / K_good) * (Real.rpow δ ε_G / (K_geo * L ^ C_P)) * (1 / (13 * Real.rpow 2 s)) * (1 / C₁) := h3
          _ = (1 / K_geo') * L ^ (-C_P) * Real.rpow δ (ε_G + lam) := h4
      exact h_goal

    have hδs_nonneg : 0 ≤ Real.rpow δ s := Real.rpow_nonneg hδ_pos.le s
    have hMδs : (M : ℝ) * Real.rpow δ s ≥ Real.rpow δ (-γ) := by
      have h1 : (M : ℝ) ≥ Real.rpow δ (-s - γ) := hM_large
      have h2 : (M : ℝ) * Real.rpow δ s ≥ Real.rpow δ (-s - γ) * Real.rpow δ s :=
        mul_le_mul_of_nonneg_right h1 hδs_nonneg
      have h3 : Real.rpow δ (-s - γ) * Real.rpow δ s = Real.rpow δ (-γ) := by
        have h4 := Real.rpow_add hδ_pos (-s - γ) s
        have h5 : (-s - γ) + s = -γ := by ring
        rw [h5] at h4; exact h4.symm
      rw [h3] at h2; exact h2

    have h5 : (Real.rpow δ (-γ)) ^ α = Real.rpow δ (-γ * α) := by
      have h_pos : 0 ≤ δ := by linarith
      exact (Real.rpow_mul h_pos (-γ) α).symm
    have h_base_nonneg : 0 ≤ Real.rpow δ (-γ) := Real.rpow_nonneg hδ_pos.le _
    have hMδs_nonneg : 0 ≤ (M : ℝ) * Real.rpow δ s := by positivity
    have h_factor : ((M : ℝ) * Real.rpow δ s) ^ α ≥ Real.rpow δ (-γ * α) := by
      have h_ineq2 : ((M : ℝ) * Real.rpow δ s) ^ α ≥ (Real.rpow δ (-γ)) ^ α := by
        exact Real.rpow_le_rpow h_base_nonneg hMδs hα_nonneg
      rw [h5] at h_ineq2; exact h_ineq2
    have h_neg_γ_α : -γ * α = -(η + 2 * ε_G) := by
      have h9 : -γ * α = -(γ * α) := by ring
      rw [h9, hγ_α_eq] <;> ring
    have h_factor2 : ((M : ℝ) * Real.rpow δ s) ^ α ≥ Real.rpow δ (-(η + 2 * ε_G)) := by
      rw [h_neg_γ_α] at h_factor; exact h_factor

    have h_coeff : (1 / K_good) * L ^ (-K_good) *
          (1 / (C_point * (13 * C₁ * Real.rpow 2 s))) ≥
        (1 / K_geo') * L ^ (-K_good - C_P) * Real.rpow δ (ε_G + lam) := by
      have h : (1 / K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s))) ≥
          (1 / K_geo') * L ^ (-C_P) * Real.rpow δ (ε_G + lam) := h_simp_coeff
      calc
        (1 / K_good) * L ^ (-K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s)))
          = L ^ (-K_good) * ((1 / K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s)))) := by ring
        _ ≥ L ^ (-K_good) * ((1 / K_geo') * L ^ (-C_P) * Real.rpow δ (ε_G + lam)) := by gcongr
        _ = (1 / K_geo') * (L ^ (-K_good) * L ^ (-C_P)) * Real.rpow δ (ε_G + lam) := by ring
        _ = (1 / K_geo') * L ^ (-K_good - C_P) * Real.rpow δ (ε_G + lam) := by
          have h6 : L ^ (-K_good) * L ^ (-C_P) = L ^ (-K_good - C_P) := by
            have h61 : L ^ (-K_good) * L ^ (-C_P) = L ^ ((-K_good) + (-C_P)) :=
              (Real.rpow_add hL_pos (-K_good) (-C_P)).symm
            have h62 : (-K_good) + (-C_P) = -K_good - C_P := by ring
            rw [h61, h62]
          rw [h6] <;> ring

    have h_bound_full : (config.T₀.card : ℝ) ≥
        (1 / K_geo') * L ^ (-K_good - C_P) * (M : ℝ) * Real.rpow δ (ε_G + lam) *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by
      calc
        (config.T₀.card : ℝ)
          ≥ (1 / K_good) * L ^ (-K_good) *
              (1 / (C_point * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
              Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := h_main_raw
        _ ≥ ((1 / K_geo') * L ^ (-K_good - C_P) * Real.rpow δ (ε_G + lam)) *
              ((M : ℝ) * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by
          have h_pos2 : 0 ≤ (M : ℝ) * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by
            have h1 : 0 ≤ (M : ℝ) := by positivity
            have h2 : 0 ≤ Real.rpow δ (-s) := Real.rpow_nonneg hδ_pos.le _
            have h3 : 0 ≤ ((M : ℝ) * Real.rpow δ s) ^ α := Real.rpow_nonneg (by positivity) _
            positivity
          have h_ineq : ((1 / K_good) * L ^ (-K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s)))) *
              ((M : ℝ) * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) ≥
            ((1 / K_geo') * L ^ (-K_good - C_P) * Real.rpow δ (ε_G + lam)) *
              ((M : ℝ) * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) :=
            mul_le_mul_of_nonneg_right h_coeff h_pos2
          have h_eq : (1 / K_good) * L ^ (-K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
              Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α =
            ((1 / K_good) * L ^ (-K_good) * (1 / (C_point * (13 * C₁ * Real.rpow 2 s)))) *
              ((M : ℝ) * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by ring
          rw [h_eq]
          exact h_ineq
        _ = (1 / K_geo') * L ^ (-K_good - C_P) * (M : ℝ) * Real.rpow δ (ε_G + lam) *
              Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by ring

    have h_pos_factor : 0 ≤ (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s) *
        ((M : ℝ) * Real.rpow δ s) ^ α := by
      have h1 : 0 ≤ (M : ℝ) := by positivity
      have h2 : 0 ≤ Real.rpow δ (ε_G + lam) := Real.rpow_nonneg hδ_pos.le _
      have h3 : 0 ≤ Real.rpow δ (-s) := Real.rpow_nonneg hδ_pos.le _
      have h4 : 0 ≤ ((M : ℝ) * Real.rpow δ s) ^ α := Real.rpow_nonneg (by positivity) _
      positivity

    have h9 : (1 / K_geo') * L ^ (-K_good - C_P) * (M : ℝ) * Real.rpow δ (ε_G + lam) *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α ≥
        L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) *
          ((M : ℝ) * Real.rpow δ s) ^ α := by
      have h10 : Real.rpow δ ε_N * Real.rpow δ (-s) = Real.rpow δ (-s + ε_N) := by
        have h11 : Real.rpow δ (ε_N + (-s)) = Real.rpow δ ε_N * Real.rpow δ (-s) :=
          Real.rpow_add hδ_pos ε_N (-s)
        have h12 : ε_N + (-s) = -s + ε_N := by ring
        rw [h12] at h11
        exact h11.symm
      calc
        (1 / K_geo') * L ^ (-K_good - C_P) * (M : ℝ) * Real.rpow δ (ε_G + lam) *
            Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α
          = ((1 / K_geo') * L ^ (-K_good - C_P)) *
              ((M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by ring
        _ ≥ (L ^ (-C) * Real.rpow δ ε_N) *
              ((M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by
          exact mul_le_mul_of_nonneg_right h_absorb h_pos_factor
        _ = L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) *
              (Real.rpow δ ε_N * Real.rpow δ (-s)) * ((M : ℝ) * Real.rpow δ s) ^ α := by ring
        _ = L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) *
              ((M : ℝ) * Real.rpow δ s) ^ α := by rw [h10] <;> ring

    have h12 : 0 ≤ L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) := by
      have h121 : 0 ≤ L ^ (-C) := Real.rpow_nonneg hL_pos.le _
      have h122 : 0 ≤ (M : ℝ) := by positivity
      have h123 : 0 ≤ Real.rpow δ (ε_G + lam) := Real.rpow_nonneg hδ_pos.le _
      have h124 : 0 ≤ Real.rpow δ (-s + ε_N) := Real.rpow_nonneg hδ_pos.le _
      positivity

    have h11 : L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) *
          ((M : ℝ) * Real.rpow δ s) ^ α ≥
        L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) *
          Real.rpow δ (-(η + 2 * ε_G)) := by
      exact mul_le_mul_of_nonneg_left h_factor2 h12

    have h13 : Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) * Real.rpow δ (-(η + 2 * ε_G)) =
        Real.rpow δ (lam - s + ε_N - η - ε_G) := by
      have h14 : Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) =
          Real.rpow δ ((ε_G + lam) + (-s + ε_N)) := by
        exact (Real.rpow_add hδ_pos (ε_G + lam) (-s + ε_N)).symm
      have h15 : Real.rpow δ ((ε_G + lam) + (-s + ε_N)) * Real.rpow δ (-(η + 2 * ε_G)) =
          Real.rpow δ (((ε_G + lam) + (-s + ε_N)) + (-(η + 2 * ε_G))) := by
        exact (Real.rpow_add hδ_pos ((ε_G + lam) + (-s + ε_N)) (-(η + 2 * ε_G))).symm
      rw [h14, h15] <;> ring_nf

    have h16 : Real.rpow δ (lam - s + ε_N - η - ε_G) ≥
        Real.rpow δ (lam - s + ε_N - η) := by
      have h17 : lam - s + ε_N - η - ε_G ≤ lam - s + ε_N - η := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h17

    have h_main_good : (config.T₀.card : ℝ) ≥
        L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
      calc (config.T₀.card : ℝ)
        ≥ (1 / K_geo') * L ^ (-K_good - C_P) * (M : ℝ) * Real.rpow δ (ε_G + lam) *
            Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := h_bound_full
        _ ≥ L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) *
              ((M : ℝ) * Real.rpow δ s) ^ α := h9
        _ ≥ L ^ (-C) * (M : ℝ) * Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) *
              Real.rpow δ (-(η + 2 * ε_G)) := h11
        _ = L ^ (-C) * (M : ℝ) *
              (Real.rpow δ (ε_G + lam) * Real.rpow δ (-s + ε_N) * Real.rpow δ (-(η + 2 * ε_G))) := by ring
        _ = L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η - ε_G) := by rw [h13]
        _ ≥ L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
          have h18 : 0 ≤ L ^ (-C) * (M : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left h16 h18

    have h_bound1 : combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass =
        L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) :=
      combiningLowerBound_good_cprime1 hδ_pos hδ_le_one h_good hΔ0 hΔ1 (fun _ => rfl)

    have h20 : ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) ≤
        (config.T₀.card : ENNReal) := by
      rw [h_bound1]
      simpa using ENNReal.ofReal_le_ofReal h_main_good

    have hΔ_pos : ∀ i, 0 < Δ i := by
      intro i; fin_cases i <;> simp [hΔ0, hΔ1, hδ_pos] <;> linarith
    have h_antitone : combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass ≤
        combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass :=
      combiningLowerBound_antitone hδ_pos hδ_lt_one hlam (by positivity) hΔ_pos hL_ge_one (by linarith) hC'_ge
    have h_final : ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass) ≤
        ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) :=
      ENNReal.ofReal_le_ofReal h_antitone
    have h20' : ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) ≤
        (config.T₀.card : ENNReal) := by
      convert h20 using 1 <;> rfl
    exact le_trans h_final h20'

  · -- SMALL M CASE (adapted for ε_inc)
    have hM_small : (M : ℝ) < Real.rpow δ (-s - γ) := by
      exact lt_of_not_ge hM_large

    have hT_lower_real : (config.T₀.card : ℝ) ≥ Real.rpow δ (-(2 * s + ε_inc)) := by
      have h : (config.T₀.card : ENNReal) ≥ ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_inc))) :=
        h_improved_incidence
      have h_nonneg : 0 ≤ Real.rpow δ (-(2 * s + ε_inc)) := Real.rpow_nonneg hδ_pos.le _
      exact ENNReal.ofReal_le_natCast.mp h_improved_incidence

    have hL_neg_C_le_one : L ^ (-C) ≤ 1 := by
      have h1 : 1 ≤ L := by linarith
      have h2 : -C ≤ 0 := by linarith
      have h3 : L ^ (-C) ≤ L ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 h2
      have h4 : L ^ (0 : ℝ) = 1 := by simp
      rw [h4] at h3; exact h3

    have h_exp_ge : lam - 2 * s - γ + ε_N - η ≥ -(2 * s + ε_inc) := by
      have h1 : γ ≤ ε_inc - η := by linarith [hγ_η_le]
      linarith

    have h_rpow_combine : Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
        Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
      have h10 := Real.rpow_add hδ_pos (-s - γ) (lam - s + ε_N - η)
      have h11 : (-s - γ) + (lam - s + ε_N - η) = lam - 2 * s - γ + ε_N - η := by ring
      rw [h11] at h10; exact h10.symm

    have h_posL : 0 < L ^ (-C) := Real.rpow_pos_of_pos hL_pos (-C)
    have h_pos_exp : 0 < Real.rpow δ (lam - s + ε_N - η) :=
      Real.rpow_pos_of_pos hδ_pos (lam - s + ε_N - η)

    have h7 : L ^ (-C) * (M : ℝ) < L ^ (-C) * Real.rpow δ (-s - γ) :=
      mul_lt_mul_of_pos_left hM_small h_posL

    have h8 : L ^ (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
        L ^ (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
      have h81 : L ^ (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
          L ^ (-C) * (Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η)) := by ring
      rw [h81, h_rpow_combine]

    have h11 : L ^ (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) ≤
        Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
      have h12 : 0 ≤ Real.rpow δ (lam - 2 * s - γ + ε_N - η) := Real.rpow_nonneg hδ_pos.le _
      have h13 : L ^ (-C) ≤ 1 := hL_neg_C_le_one
      exact mul_le_of_le_one_left h12 h13

    have h14 : Real.rpow δ (lam - 2 * s - γ + ε_N - η) ≤
        Real.rpow δ (-(2 * s + ε_inc)) := by
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h_exp_ge

    have h6 : L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) <
        Real.rpow δ (-(2 * s + ε_inc)) := by
      calc
        L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η)
          < L ^ (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) := by
            exact mul_lt_mul_of_pos_right h7 h_pos_exp
        _ = L ^ (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) := h8
        _ ≤ Real.rpow δ (lam - 2 * s - γ + ε_N - η) := h11
        _ ≤ Real.rpow δ (-(2 * s + ε_inc)) := h14

    have h_main_real : (config.T₀.card : ℝ) ≥
        L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
      exact le_trans (le_of_lt h6) hT_lower_real

    have h_bound1 : combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass =
        L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) :=
      combiningLowerBound_good_cprime1 hδ_pos hδ_le_one h_good hΔ0 hΔ1 (fun _ => rfl)

    have h20 : ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) ≤
        (config.T₀.card : ENNReal) := by
      rw [h_bound1]
      simpa using ENNReal.ofReal_le_ofReal h_main_real

    have hΔ_pos : ∀ i, 0 < Δ i := by
      intro i; fin_cases i <;> simp [hΔ0, hΔ1, hδ_pos] <;> linarith
    have h_antitone : combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass ≤
        combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass :=
      combiningLowerBound_antitone hδ_pos hδ_lt_one hlam (by positivity) hΔ_pos hL_ge_one (by linarith) hC'_ge
    have h_final : ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass) ≤
        ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) :=
      ENNReal.ofReal_le_ofReal h_antitone
    have h20' : ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) ≤
        (config.T₀.card : ENNReal) := by
      convert h20 using 1 <;> rfl
    exact le_trans h_final h20'

/-! ### Normal branch v2 (no sorry) -/

/-- Normal branch with v2 hypotheses. Takes hP_set and h_slope directly. -/
lemma base_case_normal_branch_v2
    {s t τ ε_G η ε_N C_P lam C C' C_point : ℝ} {k M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
    {C_between : Fin 1 → ℝ}
    (K : ℝ) (hK_pos : 0 < K)
    (hK_spec : KSpec s s K)
    (hs : 0 < s) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (hεN : 0 < ε_N) (hεN_le : ε_N ≤ ε_G)
    (hCP : 1 ≤ C_P)
    (hlam : 0 < lam)
    (h_log_ge_A : Real.log (1 / dyadicDelta k) ≥ K * conversionKGeo s * 13 * Real.rpow 2 s)
    (hk_ge_2 : 2 ≤ k)
    (h_normal : scaleClass 0 = ScaleClass.normal)
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (hP_set : IsFinsetDeltaSSet (dyadicDelta k) s C_point (finsetDyadicToDSquare config.P₀))
    (hC_point_pos : 0 < C_point)
    (hC_point_bound : C_point ≤ conversionKGeo s * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N))
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1)
    (hC_ge : K + C_P + 1 ≤ C) (hC'_ge : 1 ≤ C') :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C'
        lam s ε_N η 1 Δ scaleClass) := by
  classical
  let δ : ℝ := dyadicDelta k
  let C₁ : ℝ := Real.rpow δ (-lam)
  let L : ℝ := Real.log (1 / δ)
  let δEI : ℝ := DiscretisedFurstenbergEstimate.δ k

  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδEI_pos : 0 < δEI := DiscretisedFurstenbergEstimate.δ_pos k
  have hδ_eq : δ = δEI := by
    simp [δ, δEI, dyadicDelta, DiscretisedFurstenbergEstimate.δ] <;> ring
  have hδ_lt_one : δ < 1 := by
    have h2 : (2 : ℝ)^k ≥ 4 := by
      have h3 : k ≥ 2 := hk_ge_2
      have h4 : ∃ m : ℕ, k = m + 2 := by refine' ⟨k - 2, _⟩; omega
      rcases h4 with ⟨m, hm⟩
      rw [hm]
      have h5 : (2 : ℝ)^(m + 2) = (2 : ℝ)^m * 4 := by
        rw [pow_add, pow_two] <;> ring
      rw [h5]
      have h6 : (2 : ℝ)^m ≥ 1 := by
        have h7 : (2 : ℕ)^m ≥ 1 := by apply Nat.one_le_pow <;> norm_num
        exact_mod_cast h7
      nlinarith
    have h5 : δ = 1 / (2 : ℝ)^k := by simp [δ, dyadicDelta] <;> ring
    rw [h5]
    have h6 : (1 : ℝ) < (2 : ℝ)^k := by linarith
    exact (div_lt_one (by positivity)).mpr h6

  have hC₁_pos : 0 < C₁ := Real.rpow_pos_of_pos hδ_pos _
  have hC₁_ge1 : 1 ≤ C₁ := by
    have h1 : 0 < Real.rpow δ lam := Real.rpow_pos_of_pos hδ_pos lam
    have h2 : Real.rpow δ lam < 1 := Real.rpow_lt_one (by linarith) (by linarith) hlam
    have h3 : C₁ = (Real.rpow δ lam)⁻¹ := by
      simp [C₁, Real.rpow_neg hδ_pos.le] <;> field_simp <;> ring
    rw [h3]
    have h4 : 1 ≤ (Real.rpow δ lam)⁻¹ := by
      have h5 : Real.rpow δ lam ≤ 1 := h2.le
      exact (one_le_inv₀ h1).mpr h5
    exact h4

  have hCP_pos : 0 < C_P := by linarith
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hM_pos : 0 < M := hcfg.hM_pos
  have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s

  have h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ) := by
    convert hB1.h_squares_unit using 1 <;> rfl

  have hP_nonempty : config.P₀.Nonempty := by
    have h1 : (finsetDyadicToDSquare config.P₀ : Set (DSquare k)).Nonempty := hP_set.1
    rcases h1 with ⟨p', hp'⟩
    have h2 : p' ∈ finsetDyadicToDSquare config.P₀ := by exact_mod_cast hp'
    have h3 : ∃ (p : DyadicSquare k), p ∈ config.P₀ ∧ dyadicSquareToDSquare p = p' := by
      simpa [finsetDyadicToDSquare, Finset.mem_image] using h2
    rcases h3 with ⟨p, hp, _⟩
    exact ⟨p, hp⟩

  have h_mem_iff : ∀ (p' : DSquare k),
      p' ∈ finsetDyadicToDSquare config.P₀ ↔
      dSquareToDyadicSquare p' ∈ config.P₀ := by
    intro p'
    simp [finsetDyadicToDSquare, Finset.mem_image]
    constructor
    · rintro ⟨p_dy, hpin, rfl⟩
      have h_rt : dSquareToDyadicSquare (dyadicSquareToDSquare p_dy) = p_dy := by
        cases p_dy
        rfl
      rw [h_rt] <;> exact hpin
    · intro hpin
      refine' ⟨dSquareToDyadicSquare p', hpin, _⟩
      cases p'
      rfl

  have hδ_pow_eq : δ = 1 / (2 : ℝ)^k := by simp [δ, dyadicDelta] <;> ring

  have h_index_bounds : ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ) := by
    intro p hp
    let p_dy := dSquareToDyadicSquare p
    have hpin : p_dy ∈ config.P₀ := (h_mem_iff p).mp hp
    exact h_squares_unit p_dy hpin

  have h_diam : ∀ (p q : DSquare k),
      p ∈ finsetDyadicToDSquare config.P₀ →
      q ∈ finsetDyadicToDSquare config.P₀ → dist p q ≤ 3 := by
    intro p q hp hq
    have hpb := h_index_bounds p hp
    have hqb := h_index_bounds q hq
    have hpi1 : 0 ≤ (p.i : ℝ) := by exact_mod_cast hpb.1
    have hpi2 : (p.i : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hpb.2.1
    have hpj1 : 0 ≤ (p.j : ℝ) := by exact_mod_cast hpb.2.2.1
    have hpj2 : (p.j : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hpb.2.2.2
    have hqi1 : 0 ≤ (q.i : ℝ) := by exact_mod_cast hqb.1
    have hqi2 : (q.i : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hqb.2.1
    have hqj1 : 0 ≤ (q.j : ℝ) := by exact_mod_cast hqb.2.2.1
    have hqj2 : (q.j : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hqb.2.2.2
    have h1 : |(p.i : ℝ) - (q.i : ℝ)| < (2 ^ k : ℝ) := by rw [abs_lt]; constructor <;> linarith
    have h2 : |(p.j : ℝ) - (q.j : ℝ)| < (2 ^ k : ℝ) := by rw [abs_lt]; constructor <;> linarith
    have h3 : |(p.i : ℝ) - (q.i : ℝ)| * δ < 1 := by
      have h4 : |(p.i : ℝ) - (q.i : ℝ)| * δ < ((2 ^ k : ℝ) * δ) := by gcongr
      have h5 : ((2 ^ k : ℝ) * δ) = 1 := by rw [hδ_pow_eq] <;> field_simp <;> ring
      linarith
    have h6 : |(p.j : ℝ) - (q.j : ℝ)| * δ < 1 := by
      have h7 : |(p.j : ℝ) - (q.j : ℝ)| * δ < ((2 ^ k : ℝ) * δ) := by gcongr
      have h8 : ((2 ^ k : ℝ) * δ) = 1 := by rw [hδ_pow_eq] <;> field_simp <;> ring
      linarith
    have h9 : dist p q = dist p.toPoint q.toPoint := rfl
    rw [h9]
    have h10 : dist p.toPoint q.toPoint ≤ 1 := by
      simp only [DSquare.toPoint, Prod.dist_eq, Real.dist_eq]
      apply max_le
      · have h11 : |(p.i : ℝ) * δEI - (q.i : ℝ) * δEI| = |(p.i : ℝ) - (q.i : ℝ)| * δEI := by
          have h_eq : (p.i : ℝ) * δEI - (q.i : ℝ) * δEI = ((p.i : ℝ) - (q.i : ℝ)) * δEI := by ring
          rw [h_eq, abs_mul, abs_of_pos hδEI_pos]
        exact h11 ▸ (hδ_eq ▸ h3.le)
      · have h12 : |(p.j : ℝ) * δEI - (q.j : ℝ) * δEI| = |(p.j : ℝ) - (q.j : ℝ)| * δEI := by
          have h_eq : (p.j : ℝ) * δEI - (q.j : ℝ) * δEI = ((p.j : ℝ) - (q.j : ℝ)) * δEI := by ring
          rw [h_eq, abs_mul, abs_of_pos hδEI_pos]
        exact h12 ▸ (hδ_eq ▸ h6.le)
    linarith

  have h_unit : ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 := by
    intro p hp x hx
    have hpb := h_index_bounds p hp
    have hpi1 : 0 ≤ (p.i : ℝ) := by exact_mod_cast hpb.1
    have hpi2 : (p.i : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast hpb.2.1
    have hx1 : (p.i : ℝ) * δEI ≤ x.1 := hx.1
    have hx2 : x.1 < ((p.i : ℝ) + 1) * δEI := hx.2.1
    have h_nonneg : 0 ≤ x.1 := by
      have h : 0 ≤ (p.i : ℝ) * δEI := mul_nonneg hpi1 hδEI_pos.le
      linarith
    have h_lt_one : x.1 < 1 := by
      have h51 : p.i + 1 ≤ (2 ^ k : ℤ) := by
        have h52 : p.i < (2 ^ k : ℤ) := hpb.2.1
        linarith
      have h5 : (p.i : ℝ) + 1 ≤ (2 ^ k : ℝ) := by exact_mod_cast h51
      have h6 : ((p.i : ℝ) + 1) * δEI ≤ ((2 ^ k : ℝ) * δEI) := by gcongr
      have h7 : ((2 ^ k : ℝ) * δEI) = 1 := by
        have h8 : (2 ^ k : ℝ) * δEI = (2 ^ k : ℝ) * δ := by rw [hδ_eq]
        rw [h8, hδ_pow_eq] <;> field_simp <;> ring
      linarith
    rw [abs_le]
    constructor <;> linarith

  have hL_ge_one : 1 ≤ L := by
    have h1 : (1 : ℝ) / δ = (2 : ℝ)^k := by
      simp [δ, dyadicDelta] <;> field_simp <;> ring
    have h2 : (2 : ℝ)^k ≥ 4 := by
      have h3 : k ≥ 2 := hk_ge_2
      have h4 : ∃ m : ℕ, k = m + 2 := by refine' ⟨k - 2, _⟩; omega
      rcases h4 with ⟨m, hm⟩
      rw [hm]
      have h5 : (2 : ℝ)^(m + 2) = (2 : ℝ)^m * 4 := by
        rw [pow_add, pow_two] <;> ring
      rw [h5]
      have h6 : (2 : ℝ)^m ≥ 1 := by
        have h7 : (2 : ℕ)^m ≥ 1 := by apply Nat.one_le_pow <;> norm_num
        exact_mod_cast h7
      nlinarith
    have h3 : (1 : ℝ) / δ ≥ 4 := by rw [h1] <;> exact h2
    have h4 : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    have h5 : (1 : ℝ) < Real.log 4 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_three]
      have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      have h8 : Real.log (Real.exp 1) = 1 := by simp
      rw [h8] at h7; exact h7
    have h9 : Real.log (1 / δ) ≥ 1 := by linarith
    simpa [L] using h9

  let K_geo : ℝ := conversionKGeo s
  let C_point' : ℝ := max C_point 1
  have hC_point'_pos : 0 < C_point' := by positivity
  have hC_point'_ge1 : 1 ≤ C_point' := le_max_right _ _
  have hC_point'_ge : C_point ≤ C_point' := le_max_left _ _
  have hK_geo_pos : 0 < K_geo := by
    dsimp only [K_geo, conversionKGeo]
    positivity

  have hC_point'_bound : C_point' ≤ K_geo * L ^ C_P * δ ^ (-ε_N) := by
    by_cases h : C_point ≥ 1
    · have h2 : C_point' = C_point := by
        dsimp only [C_point']
        rw [max_eq_left h]
      rw [h2]; exact hC_point_bound
    · have h2 : C_point' = 1 := by
        dsimp only [C_point']
        rw [max_eq_right (by linarith)]
      rw [h2]
      have h3 : (1 : ℝ) ≤ K_geo := by
        dsimp only [K_geo, conversionKGeo]
        have h4 : (1 : ℝ) ≤ Real.rpow 2 s := by
          have h41 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
          have h42 : 0 ≤ s := by linarith
          exact Real.one_le_rpow h41 h42
        nlinarith
      have h5 : (1 : ℝ) ≤ L ^ C_P := by
        have h6 : 1 ≤ L := hL_ge_one
        have h7 : 0 ≤ C_P := by linarith
        exact Real.one_le_rpow h6 h7
      have h8 : (1 : ℝ) ≤ δ ^ (-ε_N) := by
        have h9 : -ε_N < 0 := by linarith
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos hδ_lt_one.le (by linarith)
      have h9 : (1 : ℝ) ≤ K_geo * (L ^ C_P) * (δ ^ (-ε_N)) := by
        have h10 : (1 : ℝ) ≤ K_geo * (L ^ C_P) := by
          have h101 : 0 ≤ K_geo := by linarith
          nlinarith
        have h102 : 0 ≤ K_geo * (L ^ C_P) := by positivity
        nlinarith
      exact h9

  have hP_set' : IsFinsetDeltaSSet δ s C_point' (finsetDyadicToDSquare config.P₀) :=
    IsDeltaSSet.weaken_constant' hP_set hC_point'_ge hC_point'_pos

  have h_inv_bound : 1 / C_point' ≥ δ ^ ε_N / (K_geo * L ^ C_P) := by
    have h1 : 0 < K_geo * L ^ C_P := by positivity
    have h2 : 1 / C_point' ≥ 1 / (K_geo * L ^ C_P * δ ^ (-ε_N)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact hC_point'_bound
    have h3 : 1 / (K_geo * L ^ C_P * δ ^ (-ε_N)) = δ ^ ε_N / (K_geo * L ^ C_P) := by
      have h_pos1 : 0 < K_geo * L ^ C_P := h1
      have h_pos2 : 0 < δ ^ (-ε_N) := by positivity
      have h6 : 1 / δ ^ (-ε_N) = δ ^ ε_N := by
        have h7 : δ ^ (-ε_N) = (δ ^ ε_N)⁻¹ := Real.rpow_neg hδ_pos.le ε_N
        rw [h7] <;> field_simp
      calc
        1 / (K_geo * L ^ C_P * δ ^ (-ε_N))
          = (1 / (K_geo * L ^ C_P)) * (1 / δ ^ (-ε_N)) := by
            field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
        _ = (1 / (K_geo * L ^ C_P)) * δ ^ ε_N := by rw [h6]
        _ = δ ^ ε_N / (K_geo * L ^ C_P) := by ring
    rw [h3] at h2; exact h2

  have h_wrapper := uniform_prop5_wrapper_with_K
    (t := s) (hK_pos := hK_pos) (hK_spec := hK_spec)
    (config := config) (hn_ge_2 := hk_ge_2) (hM_pos := hM_pos)
    (hP_nonempty := hP_nonempty) (hCP := hC_point'_pos) (hCP_ge1 := hC_point'_ge1)
    (hC₁ := hC₁_pos) (hC1_ge1 := hC₁_ge1)
    (hs_nonneg := hs_nonneg) (hP_set := hP_set')
    (h_slope := h_slope) (h_diam := h_diam) (h_unit := h_unit)

  have h_main_real : (config.T₀.card : ℝ) ≥
      (1 / K) * L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) * (M : ℝ) * δ ^ (-s) := by
    have h_raw : (config.T₀.card : ℝ) ≥
        (1 / K) * L ^ (-K) * (1 / (C_point' * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) * δ ^ (-s) := by
      convert h_wrapper using 1 <;> simp [C₁, L, δ] <;> ring
    have h_eq : (1 / (C_point' * (13 * C₁ * Real.rpow 2 s))) =
        (1 / C_point') * (1 / (13 * C₁ * Real.rpow 2 s)) := by
      field_simp [hC_point'_pos.ne', hC₁_pos.ne'] <;> ring
    have h_pos : 0 ≤ (1 / K) * L ^ (-K) * (M : ℝ) * δ ^ (-s) := by positivity
    have h_raw2 : (config.T₀.card : ℝ) ≥
        (1 / K) * L ^ (-K) * (1 / C_point') * (1 / (13 * C₁ * Real.rpow 2 s)) * (M : ℝ) * δ ^ (-s) := by
      calc (config.T₀.card : ℝ)
        ≥ (1 / K) * L ^ (-K) * (1 / (C_point' * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) * δ ^ (-s) := h_raw
      _ = (1 / K) * L ^ (-K) * (1 / C_point') * (1 / (13 * C₁ * Real.rpow 2 s)) * (M : ℝ) * δ ^ (-s) := by
        rw [h_eq] <;> ring
    calc
      (config.T₀.card : ℝ)
        ≥ (1 / K) * L ^ (-K) * (1 / C_point') * (1 / (13 * C₁ * Real.rpow 2 s)) * (M : ℝ) * δ ^ (-s) := h_raw2
      _ ≥ (1 / K) * L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) * (M : ℝ) * δ ^ (-s) := by
          have h_ineq : (1 / C_point') ≥ δ ^ ε_N / (K_geo * L ^ C_P) := h_inv_bound
          have h_all_pos : 0 ≤ (1 / K) * L ^ (-K) * (1 / (13 * C₁ * Real.rpow 2 s)) * (M : ℝ) * δ ^ (-s) := by positivity
          nlinarith

  have hC_K_C_P_ge_one : 1 ≤ C - K - C_P := by linarith
  have hL_pos : 0 < L := by linarith
  have hA'_pos : 0 < K * K_geo * 13 * Real.rpow 2 s := by positivity

  have h_key : L ^ (C - K - C_P) ≥ (K * K_geo * 13 * Real.rpow 2 s) * δ ^ ((C' - 1) * lam) := by
    have h1 : L ^ (C - K - C_P) ≥ L := by
      have h2 : 1 ≤ L := hL_ge_one
      have h3 : 1 ≤ C - K - C_P := hC_K_C_P_ge_one
      have h4 : L ^ (1 : ℝ) ≤ L ^ (C - K - C_P) := by exact Real.rpow_le_rpow_of_exponent_le hL_ge_one hC_K_C_P_ge_one
      have h5 : L ^ (1 : ℝ) = L := by simp
      rw [h5] at h4; exact h4
    have h4 : L ≥ K * K_geo * 13 * Real.rpow 2 s := h_log_ge_A
    have h5 : 0 ≤ (C' - 1) * lam := by
      have h6 : 0 ≤ C' - 1 := by linarith
      exact mul_nonneg h6 (by linarith)
    have h6 : δ ^ ((C' - 1) * lam) ≤ 1 := by
      apply Real.rpow_le_one <;> linarith
    have h7 : (K * K_geo * 13 * Real.rpow 2 s) * δ ^ ((C' - 1) * lam) ≤ K * K_geo * 13 * Real.rpow 2 s := by
      have h8 : 0 < K * K_geo * 13 * Real.rpow 2 s := hA'_pos
      nlinarith
    linarith

  have hC₁_eq : C₁ = δ ^ (-lam) := by simp [C₁] <;> rfl

  have h17 : (1 / K) * L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) ≥
      L ^ (-C) * δ ^ (C' * lam + ε_N) := by
    have h_goal : L ^ (C - K - C_P) ≥ (K * K_geo * 13 * Real.rpow 2 s) * δ ^ ((C' - 1) * lam) := h_key
    have h2 : L ^ (-K) / L ^ C_P = L ^ (-K - C_P) := by
      have h22 : (L ^ C_P)⁻¹ = L ^ (-C_P) := (Real.rpow_neg hL_pos.le C_P).symm
      have h21 : L ^ (-K) / L ^ C_P = L ^ (-K) * L ^ (-C_P) := by
        have h_div : L ^ (-K) / L ^ C_P = L ^ (-K) * (L ^ C_P)⁻¹ := by
          field_simp
        rw [h_div, h22]
      rw [h21]
      have h23 : L ^ (-K) * L ^ (-C_P) = L ^ ((-K) + (-C_P)) :=
        (Real.rpow_add hL_pos (-K) (-C_P)).symm
      have h24 : (-K) + (-C_P) = -K - C_P := by ring
      rw [h23, h24]
    have h22' : (L ^ C_P)⁻¹ = L ^ (-C_P) := (Real.rpow_neg hL_pos.le C_P).symm
    have h10 : L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) =
        (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * L ^ (-K - C_P) * (1 / C₁) := by
      have h_pos1 : 0 < K_geo * L ^ C_P := by positivity
      have h_pos2 : 0 < 13 * C₁ * Real.rpow 2 s := by positivity
      have h_step1 : L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) =
          L ^ (-K) * L ^ (-C_P) * (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * (1 / C₁) := by
        have h_div1 : δ ^ ε_N / (K_geo * L ^ C_P) = (δ ^ ε_N / K_geo) * L ^ (-C_P) := by
          have h : δ ^ ε_N / (K_geo * L ^ C_P) = (δ ^ ε_N / K_geo) * (L ^ C_P)⁻¹ := by
            field_simp [h_pos1.ne'] <;> ring
          rw [h, h22'] <;> ring
        have h_div2 : 1 / (13 * C₁ * Real.rpow 2 s) = (1 / (13 * Real.rpow 2 s)) * (1 / C₁) := by
          field_simp [h_pos2.ne', hC₁_pos.ne'] <;> ring
        rw [h_div1, h_div2] <;> ring
      rw [h_step1]
      have h_step2 : L ^ (-K) * L ^ (-C_P) = L ^ (-K - C_P) := by
        have h : L ^ (-K) * L ^ (-C_P) = L ^ ((-K) + (-C_P)) :=
          (Real.rpow_add hL_pos (-K) (-C_P)).symm
        rw [h]
        have h2 : (-K) + (-C_P) = -K - C_P := by ring
        rw [h2]
      have h_final_eq : L ^ (-K - C_P) * (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * (1 / C₁) =
          (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * L ^ (-K - C_P) * (1 / C₁) := by ring
      rw [h_step2]
      exact h_final_eq
    have h11 : 1 / C₁ = δ ^ lam := by
      rw [hC₁_eq]
      have h13 : (δ ^ (-lam))⁻¹ = δ ^ lam := by
        have h14 : δ ^ (-lam) = (δ ^ lam)⁻¹ := Real.rpow_neg hδ_pos.le lam
        rw [h14] <;> field_simp
      have h15 : 1 / δ ^ (-lam) = (δ ^ (-lam))⁻¹ := by field_simp
      rw [h15, h13]
    have h14 : L ^ (-K - C_P) = L ^ (C - K - C_P) * L ^ (-C) := by
      have h141 : L ^ (C - K - C_P) * L ^ (-C) = L ^ ((C - K - C_P) + (-C)) :=
        (Real.rpow_add hL_pos (C - K - C_P) (-C)).symm
      have h142 : (C - K - C_P) + (-C) = -K - C_P := by ring
      have h143 : L ^ (C - K - C_P) * L ^ (-C) = L ^ (-K - C_P) := by
        rw [h141, h142]
      exact h143.symm
    have h17_pos : 0 < K_geo * 13 * Real.rpow 2 s := by positivity
    have h18 : (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * L ^ (C - K - C_P) * δ ^ lam ≥
        K * δ ^ (C' * lam + ε_N) := by
      have h19 : L ^ (C - K - C_P) ≥ (K * K_geo * 13 * Real.rpow 2 s) * δ ^ ((C' - 1) * lam) := h_goal
      have h20 : δ ^ ε_N * δ ^ ((C' - 1) * lam) * δ ^ lam = δ ^ (C' * lam + ε_N) := by
        have h21 : δ ^ ε_N * δ ^ ((C' - 1) * lam) = δ ^ (ε_N + (C' - 1) * lam) :=
          (Real.rpow_add hδ_pos ε_N ((C' - 1) * lam)).symm
        have h22 : δ ^ (ε_N + (C' - 1) * lam) * δ ^ lam = δ ^ (ε_N + (C' - 1) * lam + lam) :=
          (Real.rpow_add hδ_pos (ε_N + (C' - 1) * lam) lam).symm
        have h23 : ε_N + (C' - 1) * lam + lam = C' * lam + ε_N := by ring
        rw [h21, h22, h23]
      calc
        (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * L ^ (C - K - C_P) * δ ^ lam
          ≥ (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) *
              ((K * K_geo * 13 * Real.rpow 2 s) * δ ^ ((C' - 1) * lam)) * δ ^ lam := by gcongr
        _ = K * δ ^ ε_N * δ ^ ((C' - 1) * lam) * δ ^ lam := by
          field_simp [h17_pos.ne'] <;> ring
        _ = K * δ ^ (C' * lam + ε_N) := by
          have h_ring : K * δ ^ ε_N * δ ^ ((C' - 1) * lam) * δ ^ lam = K * (δ ^ ε_N * δ ^ ((C' - 1) * lam) * δ ^ lam) := by ring
          rw [h_ring, h20]
    have h9 : L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) ≥
        K * L ^ (-C) * δ ^ (C' * lam + ε_N) := by
      rw [h10, h11, h14]
      have h15 : 0 < L ^ (-C) := by positivity
      calc
        (δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * (L ^ (C - K - C_P) * L ^ (-C)) * δ ^ lam
          = ((δ ^ ε_N / (K_geo * 13 * Real.rpow 2 s)) * L ^ (C - K - C_P) * δ ^ lam) * L ^ (-C) := by ring
        _ ≥ (K * δ ^ (C' * lam + ε_N)) * L ^ (-C) := by gcongr
        _ = K * L ^ (-C) * δ ^ (C' * lam + ε_N) := by ring
    have hK_pos' : 0 < K := hK_pos
    have h_final : (1 / K) * (L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s))) ≥
        (1 / K) * (K * L ^ (-C) * δ ^ (C' * lam + ε_N)) := by
      exact mul_le_mul_of_nonneg_left h9 (by positivity)
    have h_simp : (1 / K) * (K * L ^ (-C) * δ ^ (C' * lam + ε_N)) = L ^ (-C) * δ ^ (C' * lam + ε_N) := by
      field_simp [hK_pos'.ne'] <;> ring
    rw [h_simp] at h_final
    have h_eq : (1 / K) * (L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s))) =
        (1 / K) * L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) := by ring
    rw [h_eq] at h_final
    exact h_final

  have h_final_real : (config.T₀.card : ℝ) ≥
      L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N) := by
    calc
      (config.T₀.card : ℝ)
        ≥ (1 / K) * L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s)) * (M : ℝ) * δ ^ (-s) := h_main_real
      _ = ((1 / K) * L ^ (-K) * (δ ^ ε_N / (K_geo * L ^ C_P)) * (1 / (13 * C₁ * Real.rpow 2 s))) * ((M : ℝ) * δ ^ (-s)) := by ring
      _ ≥ (L ^ (-C) * δ ^ (C' * lam + ε_N)) * ((M : ℝ) * δ ^ (-s)) := by gcongr
      _ = L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N) := by
        have h_exp1 : δ ^ (C' * lam + ε_N) * δ ^ (-s) = δ ^ (C' * lam - s + ε_N) := by
          have h : δ ^ (C' * lam + ε_N) * δ ^ (-s) = δ ^ ((C' * lam + ε_N) + (-s)) :=
            (Real.rpow_add hδ_pos (C' * lam + ε_N) (-s)).symm
          have h2 : (C' * lam + ε_N) + (-s) = C' * lam - s + ε_N := by ring
          rw [h, h2]
        have h_exp2 : δ ^ (C' * lam) * δ ^ (-s + ε_N) = δ ^ (C' * lam - s + ε_N) := by
          have h : δ ^ (C' * lam) * δ ^ (-s + ε_N) = δ ^ (C' * lam + (-s + ε_N)) :=
            (Real.rpow_add hδ_pos (C' * lam) (-s + ε_N)).symm
          have h2 : C' * lam + (-s + ε_N) = C' * lam - s + ε_N := by ring
          rw [h, h2]
        calc
          (L ^ (-C) * δ ^ (C' * lam + ε_N)) * ((M : ℝ) * δ ^ (-s))
            = L ^ (-C) * (M : ℝ) * (δ ^ (C' * lam + ε_N) * δ ^ (-s)) := by ring
          _ = L ^ (-C) * (M : ℝ) * δ ^ (C' * lam - s + ε_N) := by rw [h_exp1]
          _ = L ^ (-C) * (M : ℝ) * (δ ^ (C' * lam) * δ ^ (-s + ε_N)) := by rw [← h_exp2]
          _ = L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N) := by ring

  have hG_empty : (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isGood)) = ∅ := by
    ext x
    have hx0 : x = 0 := by
      have hval : x.val = 0 := by omega
      have : x = 0 := by
        apply Fin.ext
        exact hval
      exact this
    simp [hx0, h_normal, ScaleClass.isGood]
  have hB_empty : (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isBad)) = ∅ := by
    ext x
    have hx0 : x = 0 := by
      have hval : x.val = 0 := by omega
      have : x = 0 := by
        apply Fin.ext
        exact hval
      exact this
    simp [hx0, h_normal, ScaleClass.isBad]

  have h_clb_eq : combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass =
      L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N) := by
    rw [combiningLowerBound, hG_empty, hB_empty]
    simp [L, δ] <;> ring

  have h_ennreal : ENNReal.ofReal (L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N)) ≤
      (config.T₀.card : ENNReal) := by
    have h := ENNReal.ofReal_le_ofReal h_final_real
    simpa using h

  have h_final : (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass) := by
    rw [h_clb_eq]
    exact h_ennreal
  exact h_final

/-! ### Main theorem -/

/-- Base case n=1 with CombiningExtraHypotheses_v2. -/
lemma base_case_uniform_with_data
    (s t τ ε_inc : ℝ)
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε_inc_pos : 0 < ε_inc) :
    CombiningInductionUniform_with_data s t τ ε_inc 1 := by
  let u : ℝ := min t 1
  have hu_le_one : u ≤ 1 := min_le_right _ _
  have hs_lt_u : s < u := lt_min hst hs1
  have h_u_sub_s_pos : 0 < u - s := by linarith
  have h_one_sub_s_pos : 0 < 1 - s := by linarith

  let ratio : ℝ := (1 - s) / (u - s)
  have hratio_ge_one : 1 ≤ ratio := by
    dsimp only [ratio]
    apply (one_le_div h_u_sub_s_pos).mpr
    linarith [hu_le_one]

  let ε_G0 : ℝ := ε_inc / (4 * ratio + 4)
  let η0 : ℝ := ε_inc / (4 * ratio + 4)
  have hεG0_pos : 0 < ε_G0 := by dsimp only [ε_G0]; positivity
  have hη0_pos : 0 < η0 := by dsimp only [η0]; positivity

  have hsmall : ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → 0 < η → η ≤ η0 →
      (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc := by
    intro ε_G η hεG hεG_le hη hη_le
    have h_denom : min t 1 - s = u - s := by
      have h7 : min t 1 = u := by simp [u]
      rw [h7] <;> ring
    have h_main : (η + 2 * ε_G) * ratio + η ≤ ε_inc := by
      have hεG_bound : ε_G ≤ ε_inc / (4 * ratio + 4) := by simpa [ε_G0] using hεG_le
      have hη_bound : η ≤ ε_inc / (4 * ratio + 4) := by simpa [η0] using hη_le
      have h1 : (η + 2 * ε_G) * ratio + η ≤
          (ε_inc / (4 * ratio + 4) + 2 * (ε_inc / (4 * ratio + 4))) * ratio + ε_inc / (4 * ratio + 4) := by
        gcongr <;> linarith
      have h2 : (ε_inc / (4 * ratio + 4) + 2 * (ε_inc / (4 * ratio + 4))) * ratio + ε_inc / (4 * ratio + 4) =
          ε_inc * (3 * ratio + 1) / (4 * ratio + 4) := by
        field_simp <;> ring
      rw [h2] at h1
      have h3 : ε_inc * (3 * ratio + 1) / (4 * ratio + 4) ≤ ε_inc := by
        have h4 : 0 < 4 * ratio + 4 := by positivity
        have h5 : 3 * ratio + 1 ≤ 4 * ratio + 4 := by linarith [hratio_ge_one]
        have h6 : ε_inc * (3 * ratio + 1) / (4 * ratio + 4) ≤ ε_inc * (4 * ratio + 4) / (4 * ratio + 4) := by gcongr
        have h7 : ε_inc * (4 * ratio + 4) / (4 * ratio + 4) = ε_inc := by
          field_simp [h4.ne'] <;> ring
        rw [h7] at h6
        exact h6
      exact le_trans h1 h3
    have h4 : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) = (η + 2 * ε_G) * ratio := by
      rw [h_denom] <;> simp [ratio] <;> ring
    rw [h4]
    exact h_main

  let lam_0 : ℝ := min 1 ε_inc
  let C' : ℝ := 1
  have hlam0_pos : 0 < lam_0 := by
    dsimp only [lam_0]
    exact lt_min (by norm_num) hε_inc_pos
  have hC'_pos : 0 < C' := by norm_num

  refine' ⟨ε_G0, η0, lam_0, C', hεG0_pos, hη0_pos, hlam0_pos, hC'_pos, hsmall, _⟩

  intro C_P hCP

  rcases uniform_prop5 s hs hs1 with ⟨K, hK_pos, hK_spec_all⟩
  let C : ℝ := K + C_P + 1
  have hC_pos : 0 < C := by linarith

  refine' ⟨C, hC_pos, _⟩

  intro ε_G η ε_N lam hεG hεG_le hη hη_le hεN hεN_le hlam hlam_le

  -- δ₀ ensures log(1/δ) ≥ K*conversionKGeo(2)*13*2^s (uniform bound for both branches)
  let A_log : ℝ := K * conversionKGeo 2 * 13 * Real.rpow 2 s
  have hA_log_nonneg : 0 ≤ A_log := by
    dsimp only [A_log, conversionKGeo]
    have h1 : 0 ≤ K := by linarith
    have h2 : 0 ≤ Real.rpow 2 s := Real.rpow_nonneg (by norm_num) s
    have h3 : 0 ≤ Real.rpow 2 2 := Real.rpow_nonneg (by norm_num) 2
    have h4 : 0 ≤ (2000 : ℝ) * Real.rpow 2 2 := by positivity
    have h5 : 0 ≤ K * ((2000 : ℝ) * Real.rpow 2 2) := mul_nonneg h1 h4
    have h6 : 0 ≤ K * ((2000 : ℝ) * Real.rpow 2 2) * 13 := by positivity
    exact mul_nonneg h6 h2

  intro h_uniform

  -- Absorption threshold: log(1/δ)^C_P ≤ δ^{-(ε_inc - ε_G)} for δ < δ_abs
  have hεG_lt_εinc : ε_G < ε_inc := by
    have h_small_raw := hsmall ε_G η hεG hεG_le hη hη_le
    have h_denom : min t 1 - s = u - s := by
      have h7 : min t 1 = u := by simp [u]
      rw [h7] <;> ring
    have h1 : (η + 2 * ε_G) * ratio + η ≤ ε_inc := by
      have h_us_pos : 0 < u - s := by linarith [hs_lt_u]
      have h_conv : (η + 2 * ε_G) * (1 - s) / (u - s) = (η + 2 * ε_G) * ratio := by
        simp [ratio]
        field_simp [h_us_pos.ne'] <;> ring
      rw [h_conv] at h_small_raw
      exact h_small_raw
    have h2 : 0 ≤ η := by linarith [hη]
    have h3 : 1 ≤ ratio := hratio_ge_one
    have h4 : (η + 2 * ε_G) * ratio ≥ η + 2 * ε_G := by
      have h5 : 0 ≤ η + 2 * ε_G := by linarith
      nlinarith
    have h6 : η + 2 * ε_G ≤ ε_inc := by linarith
    have h7 : 0 < η := hη
    linarith
  have h_diff_pos : 0 < ε_inc - ε_G := by linarith
  rcases DirecretisedFurstenbergEstimate.RealAnalysis.log_pow_le_rpow_neg C_P (ε_inc - ε_G) h_diff_pos with ⟨δ_abs, hδ_abs_pos, hδ_abs_iff⟩
  let δ_abs' : ℝ := δ_abs / 2
  have hδ_abs'_pos : 0 < δ_abs' := by positivity
  have hδ_abs'_lt : δ_abs' < δ_abs := by
    dsimp only [δ_abs']
    have h_pos2 : 0 < δ_abs := hδ_abs_pos
    have h : δ_abs / 2 < δ_abs := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      have h3 : δ_abs / 2 < δ_abs := by
        calc δ_abs / 2
          = (1 / 2 : ℝ) * δ_abs := by ring
        _ < δ_abs := by
          apply mul_lt_of_lt_one_left h_pos2
          norm_num
      exact h3
    exact h

  let δ₀ : ℝ := min (min (1 / 4) (Real.exp (-A_log))) (min h_uniform.δR δ_abs')
  have hδ₀_pos : 0 < δ₀ := by
    dsimp only [δ₀]
    apply lt_min
    · apply lt_min
      · norm_num
      · positivity
    · apply lt_min
      · exact h_uniform.hδR_pos
      · exact hδ_abs'_pos
  have hδ₀_le_quarter : δ₀ ≤ 1 / 4 := by
    dsimp only [δ₀]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀_le_exp : δ₀ ≤ Real.exp (-A_log) := by
    dsimp only [δ₀]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀_le_δR : δ₀ ≤ h_uniform.δR := by
    dsimp only [δ₀]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀_le_abs : δ₀ < δ_abs := by
    dsimp only [δ₀]
    have h : δ₀ ≤ δ_abs' := le_trans (min_le_right _ _) (min_le_right _ _)
    exact lt_of_le_of_lt h hδ_abs'_lt

  refine' ⟨δ₀, hδ₀_pos, _⟩

  intro k hk M config Δ scaleClass N C_between hcfg hB1 hextra

  have hδ_le_δ₀ : dyadicDelta k ≤ δ₀ := hk
  have hδ_le_quarter : dyadicDelta k ≤ 1 / 4 :=
    le_trans hδ_le_δ₀ hδ₀_le_quarter
  have hδ_le_δR : dyadicDelta k ≤ h_uniform.δR :=
    le_trans hδ_le_δ₀ hδ₀_le_δR
  have hδ_lt_δ_abs : dyadicDelta k < δ_abs :=
    lt_of_le_of_lt hδ_le_δ₀ hδ₀_le_abs
  have h_absorption : (Real.log (1 / dyadicDelta k)) ^ C_P ≤
      Real.rpow (dyadicDelta k) (-(ε_inc - ε_G)) :=
    hδ_abs_iff (dyadicDelta k) (dyadicDelta_pos k) hδ_lt_δ_abs
  have hk_ge_2 : 2 ≤ k := by
    by_contra h9
    have h10 : k < 2 := by omega
    have h11 : k = 0 ∨ k = 1 := by omega
    rcases h11 with (rfl | rfl)
    · norm_num [dyadicDelta] at hδ_le_quarter <;> linarith
    · norm_num [dyadicDelta] at hδ_le_quarter <;> linarith
  have hδ_pos : 0 < dyadicDelta k := dyadicDelta_pos k
  have hδ_lt_one : dyadicDelta k < 1 := by
    have h1 : (k : ℕ) ≥ 2 := hk_ge_2
    have h2 : dyadicDelta k = ((2 : ℝ)^k)⁻¹ := by
      simp [dyadicDelta, zpow_neg, zpow_ofNat] <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^k > 1 := by
      have h4 : (2 : ℝ)^k ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢ <;> linarith
    have h5 : 0 < (2 : ℝ)^k := by positivity
    have h6 : ((2 : ℝ)^k)⁻¹ < 1 := by
      have h7 : 1 < (2 : ℝ)^k := h3
      have h8 : 0 < (2 : ℝ)^k := by positivity
      calc ((2 : ℝ)^k)⁻¹
        = 1 / (2 : ℝ)^k := by simp
      _ < 1 := by apply (div_lt_one h8).mpr; exact h7
    exact h6
  have hδ_le_one : dyadicDelta k ≤ 1 := by linarith

  have h_log_ge_A : Real.log (1 / dyadicDelta k) ≥ A_log := by
    have h1 : dyadicDelta k ≤ Real.exp (-A_log) :=
      le_trans hδ_le_δ₀ hδ₀_le_exp
    have h2 : 0 < dyadicDelta k := hδ_pos
    have h3 : 1 / dyadicDelta k ≥ Real.exp A_log := by
      have h4 : dyadicDelta k ≤ Real.exp (-A_log) := h1
      have h5 : 0 < Real.exp (-A_log) := Real.exp_pos _
      have h6 : 1 / dyadicDelta k ≥ 1 / Real.exp (-A_log) := one_div_le_one_div_of_le h2 h4
      have h7 : 1 / Real.exp (-A_log) = Real.exp A_log := by
        have h8 : Real.exp (-A_log) * Real.exp A_log = 1 := by
          have h9 : Real.exp (-A_log) * Real.exp A_log = Real.exp ((-A_log) + A_log) := by
            rw [← Real.exp_add]
          rw [h9]
          have h10 : (-A_log) + A_log = 0 := by ring
          rw [h10, Real.exp_zero]
        field_simp [(Real.exp_pos (-A_log)).ne'] <;> linarith
      rw [h7] at h6
      exact h6
    have h9 : Real.log (1 / dyadicDelta k) ≥ Real.log (Real.exp A_log) :=
      Real.log_le_log (by positivity) h3
    have h10 : Real.log (Real.exp A_log) = A_log := Real.log_exp A_log
    rw [h10] at h9
    exact h9

  have hL_ge_one : 1 ≤ Real.log (1 / dyadicDelta k) := by
    have h1 : dyadicDelta k ≤ 1 / 4 := hδ_le_quarter
    have h2 : 0 < dyadicDelta k := hδ_pos
    have h3 : 1 / dyadicDelta k ≥ 4 := by
      calc 1 / dyadicDelta k ≥ 1 / (1 / 4) := by gcongr
      _ = 4 := by norm_num
    have h4 : Real.log (1 / dyadicDelta k) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    have h5 : (1 : ℝ) < Real.log 4 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h8] at h7; exact h7
    linarith

  cases h_sc0 : scaleClass 0 with
  | normal =>
    have hK_spec_s : KSpec s s K := hK_spec_all s (by linarith) (by linarith)
    -- Phase 2: derive global S-set from single block between-scales property
    let C_point : ℝ := conversionKGeo s * (C_between 0)
    have h_normal_raw := hcfg.h_normal 0 h_sc0
    have hC_between_pos : 0 < C_between 0 := h_normal_raw.2.2.2.2.1
    have hKgeo_pos : 0 < conversionKGeo s := by
      dsimp only [conversionKGeo]
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) s)
    have hC_point_pos : 0 < C_point := by
      dsimp only [C_point]
      exact mul_pos hKgeo_pos hC_between_pos
    have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
    have hΔ1 : Δ 1 = dyadicDelta k := hcfg.hΔ_end
    have h_normal : IsSetBetweenScales config.pointSet (dyadicDelta k) 1 s (C_between 0) := by
      have h1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
      have h2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
      simpa [h1, h2, hΔ1, hΔ0] using h_normal_raw
    have hC_point_bound : C_point ≤ conversionKGeo s * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N) := by
      have h1_raw : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P * (1 / dyadicDelta k) ^ ε_N := by
        have h2 := hcfg.h_C_between_normal 0 h_sc0
        have hfi1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
        have hfi2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
        simpa [hfi1, hfi2, hΔ1, hΔ0] using h2
      have h_rpow_eq : (1 / dyadicDelta k) ^ ε_N = Real.rpow (dyadicDelta k) (-ε_N) := by
        have h_pos : 0 < dyadicDelta k := dyadicDelta_pos k
        have h_inv : (1 / dyadicDelta k) = Real.rpow (dyadicDelta k) (-1 : ℝ) := by
          have h71 : Real.rpow (dyadicDelta k) (-1 : ℝ) = (Real.rpow (dyadicDelta k) (1 : ℝ))⁻¹ :=
            Real.rpow_neg h_pos.le (1 : ℝ)
          have h72 : Real.rpow (dyadicDelta k) (1 : ℝ) = dyadicDelta k := by simp
          rw [h72] at h71
          have h73 : (1 / dyadicDelta k) = (dyadicDelta k)⁻¹ := by
            field_simp [h_pos.ne'] <;> ring
          rw [h73]
          exact h71.symm
        rw [h_inv]
        have h8 := Real.rpow_mul h_pos.le (-1 : ℝ) ε_N
        have h9 : (-1 : ℝ) * ε_N = -ε_N := by ring
        rw [h9] at h8
        exact h8.symm
      have h1 : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N) := by
        rw [h_rpow_eq] at h1_raw
        exact h1_raw
      have hKgeo_nonneg : 0 ≤ conversionKGeo s := hKgeo_pos.le
      have h2 : conversionKGeo s * C_between 0 ≤
          conversionKGeo s * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N) := by
        have h3 : conversionKGeo s * C_between 0 ≤
            conversionKGeo s * ((Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N)) :=
          mul_le_mul_of_nonneg_left h1 hKgeo_nonneg
        have h4 : conversionKGeo s * ((Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N)) =
            conversionKGeo s * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N) := by ring
        rw [h4] at h3
        exact h3
      dsimp only [C_point]
      exact h2
    have hP_nonempty_dispatch : config.P₀.Nonempty := by
      have h1 : config.pointSet.Nonempty := hcfg.h_uniform.1
      rcases h1 with ⟨x, hx⟩
      simp only [NiceConfiguration.pointSet, Set.mem_iUnion] at hx
      rcases hx with ⟨p, hp, _⟩
      exact ⟨p, hp⟩
    have hP_set_base : IsFinsetDeltaSSet (dyadicDelta k) s C_point
        (finsetDyadicToDSquare config.P₀) :=
      isSetBetweenScales_to_isFinsetDeltaSSet hP_nonempty_dispatch hs.le h_normal
    have hK_geo_s_le_2 : conversionKGeo s ≤ conversionKGeo 2 := by
      dsimp only [conversionKGeo]
      have h1 : s ≤ 2 := by linarith
      have h2 : 0 ≤ s := by linarith
      have h3 : Real.rpow 2 s ≤ Real.rpow 2 2 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      have h4 : (2000 : ℝ) * Real.rpow 2 s ≤ (2000 : ℝ) * Real.rpow 2 2 :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      exact h4
    have h_log_ge_normal : Real.log (1 / dyadicDelta k) ≥ K * conversionKGeo s * 13 * Real.rpow 2 s := by
      have h_rpow_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
      have h_pos : 0 ≤ K * 13 * Real.rpow 2 s := by positivity
      have h_ineq : K * conversionKGeo 2 * 13 * Real.rpow 2 s ≥ K * conversionKGeo s * 13 * Real.rpow 2 s := by
        have h : K * 13 * Real.rpow 2 s * conversionKGeo 2 ≥ K * 13 * Real.rpow 2 s * conversionKGeo s :=
          mul_le_mul_of_nonneg_left hK_geo_s_le_2 h_pos
        ring_nf at h ⊢
        exact h
      calc Real.log (1 / dyadicDelta k)
        ≥ K * conversionKGeo 2 * 13 * Real.rpow 2 s := h_log_ge_A
      _ ≥ K * conversionKGeo s * 13 * Real.rpow 2 s := h_ineq
    exact base_case_normal_branch_v2 K hK_pos hK_spec_s hs hs1 hτ hτ1 hεG hη hεN hεN_le hCP hlam
      h_log_ge_normal hk_ge_2 h_sc0 hcfg hB1 hP_set_base hC_point_pos hC_point_bound hextra.h_slope
      (by linarith) (by norm_num)

  | good t_j =>
    have hK_spec_u : KSpec s u K := hK_spec_all u (by linarith) hu_le_one
    -- Phase 2: derive global S-set from single block between-scales property
    have hP_nonempty_dispatch : config.P₀.Nonempty := by
      have h1 : config.pointSet.Nonempty := hcfg.h_uniform.1
      rcases h1 with ⟨x, hx⟩
      simp only [NiceConfiguration.pointSet, Set.mem_iUnion] at hx
      rcases hx with ⟨p, hp, _⟩
      exact ⟨p, hp⟩
    have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
    have hΔ1 : Δ 1 = dyadicDelta k := hcfg.hΔ_end
    have h_good_raw := hcfg.h_good 0 t_j h_sc0
    have h_good_scaled : IsRegularBetweenScales config.pointSet (dyadicDelta k) 1 t_j (C_between 0) (C_between 0) := by
      have h1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
      have h2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
      simpa [h1, h2, hΔ1, hΔ0] using h_good_raw
    let C_point_raw : ℝ := conversionKGeo t_j * (C_between 0)
    let C_point : ℝ := max C_point_raw 1
    have hC_point_pos : 0 < C_point := by positivity
    have hC_point_ge1 : 1 ≤ C_point := le_max_right _ _
    have h_tj_pos : 0 < t_j := by
      have h1 : s < t_j := by
        have h2 : s < t := hst
        have h3 : t ≤ t_j := hextra.h_tj_ge_t 0 t_j h_sc0
        linarith
      linarith
    have hP_set_tj_raw : IsFinsetDeltaSSet (dyadicDelta k) t_j C_point_raw
        (finsetDyadicToDSquare config.P₀) :=
      isSetBetweenScales_to_isFinsetDeltaSSet hP_nonempty_dispatch h_tj_pos.le
        h_good_scaled.1
    have hP_set_tj_const : IsFinsetDeltaSSet (dyadicDelta k) t_j C_point
        (finsetDyadicToDSquare config.P₀) :=
      IsDeltaSSet.weaken_constant' hP_set_tj_raw (le_max_left _ _) hC_point_pos
    have h_min_tj_pos : 0 ≤ min t_j 1 := by positivity
    have h_min_le_tj : min t_j 1 ≤ t_j := min_le_left _ _
    have hP_set_tj_base : IsFinsetDeltaSSet (dyadicDelta k) (min t_j 1) C_point
        (finsetDyadicToDSquare config.P₀) :=
      finset_deltaSSet_weaken_exponent hP_set_tj_const h_min_tj_pos h_min_le_tj hC_point_ge1
    have hC_between_bound : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P *
        Real.rpow (dyadicDelta k) (-ε_G) := by
      have h1 := hcfg.h_C_between_good 0 t_j h_sc0
      have hfi1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
      have hfi2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
      have h4 : (1 / dyadicDelta k) ^ ε_G = Real.rpow (dyadicDelta k) (-ε_G) := by
        have h51 : (1 / dyadicDelta k) = (dyadicDelta k)⁻¹ := by ring
        rw [h51]
        have h52 : (dyadicDelta k)⁻¹ ^ ε_G = (Real.rpow (dyadicDelta k) ε_G)⁻¹ := Real.inv_rpow hδ_pos.le ε_G
        have h53 : (Real.rpow (dyadicDelta k) ε_G)⁻¹ = Real.rpow (dyadicDelta k) (-ε_G) := (Real.rpow_neg hδ_pos.le ε_G).symm
        rw [h52, h53]
      have h1' : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P * (1 / dyadicDelta k) ^ ε_G := by
        simpa [hfi1, hfi2, hΔ1, hΔ0] using h1
      have h1'' : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_G) := by
        rw [h4] at h1'
        exact h1'
      exact h1''
    have hC_point_bound : C_point ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P *
        Real.rpow (dyadicDelta k) (-ε_G) := by
      by_cases h : C_point_raw ≥ 1
      · have h4 : C_point = C_point_raw := by
          dsimp only [C_point]
          rw [max_eq_left h]
        rw [h4]
        dsimp only [C_point_raw]
        have h_pos : 0 ≤ conversionKGeo t_j := by
          dsimp only [conversionKGeo]
          have h1 : 0 < Real.rpow 2 t_j := Real.rpow_pos_of_pos (by norm_num) t_j
          exact mul_nonneg (by norm_num) h1.le
        have h5 : conversionKGeo t_j * C_between 0 ≤
            conversionKGeo t_j * ((Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_G)) :=
          mul_le_mul_of_nonneg_left hC_between_bound h_pos
        linarith
      · have h4 : C_point = 1 := by
          dsimp only [C_point]
          have h' : C_point_raw ≤ 1 := by linarith [h]
          rw [max_eq_right h']
        rw [h4]
        have h5 : (1 : ℝ) ≤ conversionKGeo t_j := by
          dsimp only [conversionKGeo]
          have h6 : (1 : ℝ) ≤ Real.rpow 2 t_j := by
            have h61 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
            have h62 : 0 ≤ t_j := by linarith
            exact Real.one_le_rpow h61 h62
          nlinarith
        have h7 : (1 : ℝ) ≤ (Real.log (1 / dyadicDelta k)) ^ C_P := by
          have h8 : 1 ≤ Real.log (1 / dyadicDelta k) := hL_ge_one
          have h9 : 0 ≤ C_P := by linarith
          exact Real.one_le_rpow h8 h9
        have h10 : (1 : ℝ) ≤ Real.rpow (dyadicDelta k) (-ε_G) := by
          have h1 : Real.rpow (dyadicDelta k) ε_G ≤ 1 :=
            Real.rpow_le_one (by linarith) (by linarith) (by linarith)
          have h2 : 0 < Real.rpow (dyadicDelta k) ε_G := Real.rpow_pos_of_pos hδ_pos ε_G
          have h3 : Real.rpow (dyadicDelta k) (-ε_G) = (Real.rpow (dyadicDelta k) ε_G)⁻¹ := by
            exact Real.rpow_neg hδ_pos.le ε_G
          rw [h3]
          have h4 : (Real.rpow (dyadicDelta k) ε_G)⁻¹ ≥ 1 := by
            calc (Real.rpow (dyadicDelta k) ε_G)⁻¹
              ≥ (1 : ℝ)⁻¹ := by gcongr
            _ = 1 := by norm_num
          exact h4
        have h_mul1 : (1 : ℝ) ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P := by
          have h : (1 : ℝ) * (1 : ℝ) ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P :=
            mul_le_mul h5 h7 (by linarith) (by linarith)
          simpa using h
        have h_final : (1 : ℝ) ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_G) := by
          have h : (1 : ℝ) * (1 : ℝ) ≤ (conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P) * Real.rpow (dyadicDelta k) (-ε_G) :=
            mul_le_mul h_mul1 h10 (by linarith) (by linarith)
          simpa [mul_assoc] using h
        exact h_final
    have h_tj_le_two : t_j ≤ 2 := hextra.h_tj_le_two 0 t_j h_sc0
    have hK_geo_mono : conversionKGeo t_j ≤ conversionKGeo 2 := by
      dsimp only [conversionKGeo]
      have h1 : t_j ≤ 2 := h_tj_le_two
      have h2 : 0 ≤ t_j := by linarith
      have h3 : Real.rpow 2 t_j ≤ Real.rpow 2 2 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      have h4 : (2000 : ℝ) * Real.rpow 2 t_j ≤ (2000 : ℝ) * Real.rpow 2 2 :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      exact h4
    have h_log_ge_good : Real.log (1 / dyadicDelta k) ≥ K * conversionKGeo t_j * 13 * Real.rpow 2 s := by
      have h_factor : 0 ≤ K * (13 : ℝ) * Real.rpow 2 s := by
        have hK_nonneg : 0 ≤ K := by linarith [hK_pos]
        have h13_pos : (0 : ℝ) < 13 := by norm_num
        have hrp_nonneg : 0 ≤ Real.rpow 2 s := Real.rpow_nonneg (by norm_num) s
        exact mul_nonneg (mul_nonneg hK_nonneg h13_pos.le) hrp_nonneg
      have h5 : K * conversionKGeo t_j * 13 * Real.rpow 2 s ≤ K * conversionKGeo 2 * 13 * Real.rpow 2 s := by
        have h6 : K * conversionKGeo t_j * 13 * Real.rpow 2 s = K * (13 : ℝ) * Real.rpow 2 s * conversionKGeo t_j := by ring
        have h7 : K * conversionKGeo 2 * 13 * Real.rpow 2 s = K * (13 : ℝ) * Real.rpow 2 s * conversionKGeo 2 := by ring
        rw [h6, h7]
        exact mul_le_mul_of_nonneg_left hK_geo_mono h_factor
      calc Real.log (1 / dyadicDelta k)
        ≥ K * conversionKGeo 2 * 13 * Real.rpow 2 s := h_log_ge_A
      _ ≥ K * conversionKGeo t_j * 13 * Real.rpow 2 s := h5
    have h_improved_incidence : (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow (dyadicDelta k) (-(2 * s + ε_inc))) := by
      let δ : ℝ := dyadicDelta k
      have hδ_pos' : 0 < δ := dyadicDelta_pos k
      have hδ_lt_one' : δ < 1 := hδ_lt_one
      have hδ_le_R' : δ ≤ h_uniform.δR := hδ_le_δR
      have hlam_le_εinc : lam ≤ ε_inc := by
        have h1 : lam ≤ lam_0 := hlam_le
        have h2 : lam_0 ≤ ε_inc := by
          dsimp only [lam_0]
          exact min_le_right _ _
        linarith
      -- Good between-scales regularity
      have h_good_reg : IsRegularBetweenScales config.pointSet δ 1 t_j (C_between 0) (C_between 0) := by
        have h := hcfg.h_good 0 t_j h_sc0
        have h1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
        have h2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
        have hδ_eq : δ = dyadicDelta k := by rfl
        simpa [h1, h2, hΔ1, hΔ0, hδ_eq] using h
      -- Unit square containment
      have h_config_unit : config.pointSet ⊆ dyadicSquare 1 0 0 :=
        pointSet_sub_dyadicSquare1 hB1.h_squares_unit
      -- Nonempty
      have hP_nonempty : config.pointSet.Nonempty := hcfg.h_uniform.1
      -- Convert to square-root regular
      have h_sqrt_reg : IsSquareRootRegular δ t_j (C_between 0) (C_between 0) config.pointSet :=
        square_root_regular_from_unit_between_scales h_good_reg h_config_unit hP_nonempty
      -- Absorption: C_between 0 ≤ δ^{-ε_inc}
      have hCb_bound : C_between 0 ≤ Real.log (1 / δ) ^ C_P * Real.rpow δ (-ε_G) := by
        have h_eq : Real.log (1 / dyadicDelta k) = Real.log (1 / δ) := by rfl
        simpa [h_eq] using hC_between_bound
      have hCb_abs : C_between 0 ≤ Real.rpow δ (-ε_inc) := by
        calc C_between 0
          ≤ Real.log (1 / δ) ^ C_P * Real.rpow δ (-ε_G) := hCb_bound
        _ = Real.rpow δ (-ε_G) * Real.log (1 / δ) ^ C_P := by ring
        _ ≤ Real.rpow δ (-ε_G) * Real.rpow δ (-(ε_inc - ε_G)) := by
          have h_nonneg : 0 ≤ Real.rpow δ (-ε_G) := Real.rpow_nonneg hδ_pos'.le (-ε_G)
          exact mul_le_mul_of_nonneg_left h_absorption h_nonneg
        _ = Real.rpow δ (-ε_inc) := by
          have h_rpow : Real.rpow δ (-ε_G) * Real.rpow δ (-(ε_inc - ε_G)) =
              Real.rpow δ ((-ε_G) + (-(ε_inc - ε_G))) :=
            (Real.rpow_add hδ_pos' (-ε_G) (-(ε_inc - ε_G))).symm
          have h_sum : (-ε_G) + (-(ε_inc - ε_G)) = -ε_inc := by ring
          rw [h_rpow, h_sum]
      -- Weaken square-root regular constants
      have h_reg_final : IsSquareRootRegular δ t_j
          (Real.rpow δ (-ε_inc)) (Real.rpow δ (-ε_inc)) config.pointSet :=
        IsSquareRootRegular.weaken_CK h_sqrt_reg hCb_abs hCb_abs
          (Real.rpow_pos_of_pos hδ_pos' _) (Real.rpow_pos_of_pos hδ_pos' _)
      -- Translate point set
      let P_orig : Set DirecretisedFurstenbergEstimate.EuclideanPlane := translationEquiv centerTranslation '' config.pointSet
      have hP_orig_regular : IsSquareRootRegular δ t_j
          (Real.rpow δ (-ε_inc)) (Real.rpow δ (-ε_inc)) P_orig :=
        isSquareRootRegular_translate h_reg_final
      have hP_orig_ball : P_orig ⊆ Metric.closedBall 0 1 :=
        unit_square_translate_sub_ball h_config_unit
      have hP_orig_sub : P_orig ⊆ translatedCoarsePointSet config := by
        simp [P_orig, translatedCoarsePointSet]
      -- Tube S-set constant weakening: δ^{-lam} ≤ δ^{-ε_inc} since lam ≤ ε_inc and 0 < δ < 1
      have hCΔ_weaken : Real.rpow δ (-lam) ≤ Real.rpow δ (-ε_inc) := by
        have h_exp : -ε_inc ≤ -lam := by linarith
        exact Real.rpow_le_rpow_of_exponent_ge (by linarith [hδ_pos']) (by linarith [hδ_lt_one']) h_exp
      -- Slope condition
      have h_slope_coarse : ∀ T ∈ config.T₀, |T.slope| ≤ 1 := hextra.h_slope
      -- Apply geometric bridge
      have h_bridge : (config.T₀.card : ENNReal) ≥
          ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_inc))) :=
        coarse_incidence_geometric_bridge
          (coarseConfig := config)
          (h_slope_coarse := h_slope_coarse)
          (hεReg_pos := hextra.hε_inc_pos)
          (hη_pos := hextra.hε_inc_pos)
          (δ := δ)
          (hδ_pos := hδ_pos')
          (h_est_body := h_uniform.h_body k hδ_le_R')
          (hu_t := by exact hextra.h_tj_ge_t 0 t_j h_sc0)
          (hu_two := h_tj_le_two)
          (hδ_eq := by rfl)
          (P_orig := P_orig)
          (hP_sub := hP_orig_sub)
          (hP_ball := hP_orig_ball)
          (hP_regular := hP_orig_regular)
          (hCΔ_weaken := hCΔ_weaken)
      exact h_bridge
    exact base_case_good_uniform_v2 hcfg hB1 hextra hP_set_tj_base hC_point_pos hC_point_ge1
      hC_point_bound h_improved_incidence
      u rfl K hK_pos hK_spec_u hs hst hs1 hs_lt_u hu_le_one hεG hη hεN hCP hlam
      h_log_ge_good hk_ge_2 h_sc0 (by linarith) (by norm_num)

  | bad =>
    exact base_case_bad_branch hs1 hlam hεN hk_ge_2 h_sc0 hcfg hL_ge_one (by linarith) (by norm_num)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73BaseCase

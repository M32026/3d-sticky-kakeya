module

/-
  Prop73 BaseNormal — Normal scale branch lemma (n=1)

  For normal scales, C'=1 and C≥K+1 where K comes from uniform_prop5
  (lam-independent). Uses uniform_prop5_wrapper_with_K t=s.

  Whiteprint node: combining_theorem_genuine / base_normal
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Normal scale branch: proves the lower bound for a single normal scale block
    with arbitrary C≥K+1, C'≥1, where K is from uniform_prop5. -/
lemma base_case_normal_branch
    {s t τ ε_G η ε_N C_P lam C C' : ℝ} {k M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
    {C_between : Fin 1 → ℝ}
    (K : ℝ) (hK_pos : 0 < K)
    (hK_spec : ∀ {n : ℕ} (C_P C_T M : ℝ),
      0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ n →
      ∀ (P : Finset (DSquare n)), P.Nonempty →
        IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ n) s C_P P →
        (∀ (x y : DSquare n), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : TubeFamily n),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ n) s C_T (Tp p)) →
          (∀ p ∈ P, M / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
            let T := P.biUnion fun p => Tp p
            (T.card : ℝ) ≥ (1 / K) * Real.log (1 / DiscretisedFurstenbergEstimate.δ n) ^ (-K) *
              (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ n) ^ (-s) *
                (M * (DiscretisedFurstenbergEstimate.δ n) ^ s) ^ ((s - s) / (1 - s)))
    (hs : 0 < s) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (hεN : 0 < ε_N) (hεN_le : ε_N ≤ ε_G)
    (hCP : 1 ≤ C_P)
    (hlam : 0 < lam)
    (h_log_ge_A : Real.log (1 / dyadicDelta k) ≥ K * C_P * 13 * Real.rpow 2 s)
    (hk_ge_2 : 2 ≤ k)
    (h_normal : scaleClass 0 = ScaleClass.normal)
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (hextra : CombiningExtraHypotheses s t ε_G η ε_N C_P 1 lam k M config Δ scaleClass)
    (hC_ge : K + 1 ≤ C) (hC'_ge : 1 ≤ C') :
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
    have h1 : 0 < δ ^ lam := Real.rpow_pos_of_pos hδ_pos lam
    have h2 : δ ^ lam < 1 := Real.rpow_lt_one (by linarith) (by linarith) hlam
    have h3 : C₁ = 1 / δ ^ lam := by
      simp [C₁, Real.rpow_neg hδ_pos.le] <;> ring
    rw [h3]
    have h4 : (1 : ℝ) ≤ 1 / δ ^ lam := by
      have h5 : δ ^ lam ≤ 1 := h2.le
      have h6 : 0 < δ ^ lam := h1
      exact (one_le_div h6).mpr h5
    exact h4

  have hCP_pos : 0 < C_P := by linarith
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hM_pos : 0 < M := hcfg.hM_pos
  have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s

  -- Extract fields using convert
  have h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ) := by
    convert hB1.h_squares_unit using 1 <;> rfl
  have hP_set_extra : IsFinsetDeltaSSet δ s C_P (finsetDyadicToDSquare config.P₀) := by
    convert hextra.hP_set using 1 <;> simp [hδ_eq] <;> rfl
  have h_slope_extra : ∀ T ∈ config.T₀, |T.slope| ≤ 1 := by
    convert hextra.h_slope using 1 <;> rfl

  have hP_nonempty : config.P₀.Nonempty := by
    have h1 : (finsetDyadicToDSquare config.P₀ : Set (DSquare k)).Nonempty := hP_set_extra.1
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

  have h_main_real : (config.T₀.card : ℝ) ≥
      (1 / K) * L ^ (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) * δ ^ (-s) := by
    have h_wrapper := uniform_prop5_wrapper_with_K
      (t := s) (hK_pos := hK_pos) (hK_spec := hK_spec)
      (config := config) (hn_ge_2 := hk_ge_2) (hM_pos := hM_pos)
      (hP_nonempty := hP_nonempty) (hCP := hCP_pos) (hCP_ge1 := hCP)
      (hC₁ := hC₁_pos) (hC1_ge1 := hC₁_ge1)
      (hs_nonneg := hs_nonneg) (hP_set := hP_set_extra)
      (h_slope := h_slope_extra) (h_diam := h_diam) (h_unit := h_unit)
    convert h_wrapper using 1 <;> simp [C₁, L, δ] <;> ring

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
    have h3 : (1 : ℝ) / δ ≥ 4 := by
      rw [h1] <;> exact h2
    have h4 : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    have h5 : (1 : ℝ) < Real.log 4 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_three]
      have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      have h8 : Real.log (Real.exp 1) = 1 := by simp
      rw [h8] at h7 <;> exact h7
    have h9 : Real.log (1 / δ) ≥ 1 := by linarith
    simpa [L] using h9

  have hC_K_ge_one : 1 ≤ C - K := by linarith

  let A : ℝ := K * C_P * 13 * Real.rpow 2 s
  have hA_pos : 0 < A := by
    have h1 : 0 < K := hK_pos
    have h2 : 0 < C_P := hCP_pos
    have h3 : (0 : ℝ) < 13 := by norm_num
    have h4 : 0 < Real.rpow 2 s := h2s_pos
    positivity

  let α : ℝ := (C' - 1) * lam + ε_N
  have hα_pos : 0 < α := by
    have h1 : 0 ≤ (C' - 1) * lam := by
      have h2 : 0 ≤ C' - 1 := by linarith
      have h3 : 0 ≤ lam := by linarith
      exact mul_nonneg h2 h3
    linarith

  have hδ_pow_lt_one : δ ^ α < 1 := Real.rpow_lt_one (by linarith) (by linarith) hα_pos
  have hC₁_eq : C₁ = δ ^ (-lam) := by simp [C₁] <;> rfl

  have h_key : L ^ (C - K) ≥ A * δ ^ α := by
    have h1 : L ^ (C - K) ≥ L := by
      have h2 : 1 ≤ L := hL_ge_one
      have h3 : 1 ≤ C - K := hC_K_ge_one
      have h4 : L ^ (1 : ℝ) ≤ L ^ (C - K) := by exact Real.rpow_le_rpow_of_exponent_le hL_ge_one hC_K_ge_one
      have h5 : L ^ (1 : ℝ) = L := by simp
      rw [h5] at h4
      exact h4
    have h4 : L ≥ A := h_log_ge_A
    have h5 : A * δ ^ α < A := by have h6 : δ ^ α < 1 := hδ_pow_lt_one; nlinarith
    have h7 : L ≥ A * δ ^ α := by linarith
    linarith

  have h_goal : L ^ (C - K) ≥ (K * C_P * 13 * C₁ * Real.rpow 2 s) * δ ^ (C' * lam + ε_N) := by
    have h11 : C₁ * δ ^ (C' * lam + ε_N) = δ ^ α := by
      rw [hC₁_eq]
      have h12 : δ ^ (-lam) * δ ^ (C' * lam + ε_N) = δ ^ ((-lam) + (C' * lam + ε_N)) := by
        rw [← Real.rpow_add hδ_pos] <;> ring
      rw [h12]
      have h13 : (-lam) + (C' * lam + ε_N) = α := by simp [α] <;> ring
      rw [h13]
    calc
      L ^ (C - K) ≥ A * δ ^ α := h_key
      _ = (K * C_P * 13 * Real.rpow 2 s) * (C₁ * δ ^ (C' * lam + ε_N)) := by rw [h11] <;> ring
      _ = (K * C_P * 13 * C₁ * Real.rpow 2 s) * δ ^ (C' * lam + ε_N) := by ring

  have hL_pos : 0 < L := by linarith

  have h14 : L ^ (-K) ≥ (K * C_P * 13 * C₁ * Real.rpow 2 s) * L ^ (-C) * δ ^ (C' * lam + ε_N) := by
    have h15 : L ^ (-K) = L ^ (C - K) * L ^ (-C) := by rw [← Real.rpow_add hL_pos] <;> ring_nf
    rw [h15]
    have h16 : 0 < L ^ (-C) := Real.rpow_pos_of_pos hL_pos _
    nlinarith

  have h_pos_factor : 0 < K * C_P * (13 * C₁ * Real.rpow 2 s) := by
    have h1 : 0 < K := hK_pos
    have h2 : 0 < C_P := hCP_pos
    have h3 : (0 : ℝ) < 13 := by norm_num
    have h4 : 0 < C₁ := hC₁_pos
    have h5 : 0 < Real.rpow 2 s := h2s_pos
    positivity

  have h17 : (1 / K) * L ^ (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) ≥
      L ^ (-C) * δ ^ (C' * lam + ε_N) := by
    have h_goal : (1 / (K * C_P * (13 * C₁ * Real.rpow 2 s))) * L ^ (-K) ≥
        L ^ (-C) * δ ^ (C' * lam + ε_N) := by
      calc
        (1 / (K * C_P * (13 * C₁ * Real.rpow 2 s))) * L ^ (-K)
          ≥ (1 / (K * C_P * (13 * C₁ * Real.rpow 2 s))) *
              ((K * C_P * 13 * C₁ * Real.rpow 2 s) * L ^ (-C) * δ ^ (C' * lam + ε_N)) := by gcongr
        _ = L ^ (-C) * δ ^ (C' * lam + ε_N) := by field_simp [h_pos_factor.ne'] <;> ring
    have h_eq : (1 / K) * L ^ (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
        (1 / (K * C_P * (13 * C₁ * Real.rpow 2 s))) * L ^ (-K) := by ring
    rw [h_eq]
    exact h_goal

  have h_final_real : (config.T₀.card : ℝ) ≥
      L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N) := by
    calc
      (config.T₀.card : ℝ)
        ≥ (1 / K) * L ^ (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) * δ ^ (-s) := h_main_real
      _ = ((1 / K) * L ^ (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s)))) * ((M : ℝ) * δ ^ (-s)) := by ring
      _ ≥ (L ^ (-C) * δ ^ (C' * lam + ε_N)) * ((M : ℝ) * δ ^ (-s)) := by gcongr
      _ = L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N) := by
        have h_exp1 : δ ^ (C' * lam + ε_N) * δ ^ (-s) = δ ^ (C' * lam - s + ε_N) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
        have h_exp2 : δ ^ (C' * lam) * δ ^ (-s + ε_N) = δ ^ (C' * lam - s + ε_N) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
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
      exact Fin.fin_one_eq_zero x
    simp [hx0, h_normal, ScaleClass.isGood]
  have hB_empty : (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isBad)) = ∅ := by
    ext x
    have hx0 : x = 0 := by
      have hval : x.val = 0 := by omega
      exact Fin.fin_one_eq_zero x
    simp [hx0, h_normal, ScaleClass.isBad]

  have h_clb_eq : combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass =
      L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N) := by
    rw [combiningLowerBound, hG_empty, hB_empty]
    simp [L, δ] <;> ring

  have h_ennreal : ENNReal.ofReal (L ^ (-C) * (M : ℝ) * δ ^ (C' * lam) * δ ^ (-s + ε_N)) ≤
      (config.T₀.card : ENNReal) := by
    have h := ENNReal.ofReal_le_ofReal h_final_real
    simpa using h

  -- cfg = hcfg.config is definitionally equal to the lemma's implicit config
  have h_final : (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass) := by
    rw [h_clb_eq]
    exact h_ennreal

  exact_mod_cast h_final

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

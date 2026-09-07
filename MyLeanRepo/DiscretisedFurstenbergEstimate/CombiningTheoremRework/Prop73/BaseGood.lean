module

/-
  Prop73 BaseGood — Good scale branch lemma (n=1)

  Uses uniform_prop5 at exponent u = min(t,1), with K uniform for all u ∈ [s,1].
  The caller (Main.lean) extracts K from uniform_prop5 s, specializes at u,
  and passes the specialized KSpec here.

  Large-M: uniform incidence bound at exponent u, log absorption with C ≥ K+1.
  Small-M: improved incidence bound from Appendix A chain.
  C' handled via combiningLowerBound_antitone (prove for C'=1, weaken).

  Whiteprint node: combining_theorem_genuine / base_good
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseGood
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.ExponentWeakening
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

section BaseGoodUniform

variable {s t τ ε_G η ε_N C_P lam C C' : ℝ} {k M : ℕ}
variable {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
variable {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
variable {C_between : Fin 1 → ℝ} {t_j : ℝ}

/-- S-set exponent weakening for IsFinsetDeltaSSet. -/
lemma finset_deltaSSet_weaken_exponent
    {X : Type*} [MetricSpace X] {δ t t' C : ℝ} {P : Finset X}
    (h : IsFinsetDeltaSSet δ t' C P) (ht : 0 ≤ t) (hle : t ≤ t') (hC : 1 ≤ C) :
    IsFinsetDeltaSSet δ t C P :=
  IsDeltaSSet.cap_exponent h ht hle hC

/-- Specialized K specification at exponent t. -/
abbrev KSpec (s t K : ℝ) : Prop :=
  ∀ {n : ℕ} (C_P C_T M : ℝ),
    0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ n →
    ∀ (P : Finset (DSquare n)), P.Nonempty →
      IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ n) t C_P P →
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
              (M * (DiscretisedFurstenbergEstimate.δ n) ^ s) ^ ((t - s) / (1 - s))

/-- Good scale branch: proves the lower bound for a single good scale block
    with C ≥ K+1, C' ≥ 1. K is uniform for all u ∈ [s,1] from uniform_prop5.
    The caller specializes K at u = min(t,1). -/
lemma base_case_good_uniform
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (hextra : CombiningExtraHypotheses s t ε_G η ε_N C_P 1 lam k M config Δ scaleClass)
    (u : ℝ) (hu_eq : u = min t 1)
    (K_good : ℝ) (hK_pos : 0 < K_good)
    (hK_spec_u : ∀ {n : ℕ} (C_P C_T M : ℝ),
      0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ n →
      ∀ (P : Finset (DSquare n)), P.Nonempty →
        IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ n) u C_P P →
        (∀ (x y : DSquare n), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : TubeFamily n),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ n) s C_T (Tp p)) →
          (∀ p ∈ P, M / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
            let T := P.biUnion fun p => Tp p
            (T.card : ℝ) ≥ (1 / K_good) * Real.log (1 / DiscretisedFurstenbergEstimate.δ n) ^ (-K_good) *
              (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ n) ^ (-s) *
                (M * (DiscretisedFurstenbergEstimate.δ n) ^ s) ^ ((u - s) / (1 - s)))
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hus : s < u) (hu1 : u ≤ 1)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (hεN : 0 < ε_N)
    (hCP : 1 ≤ C_P)
    (hlam : 0 < lam)
    (h_log_ge : Real.log (1 / dyadicDelta k) ≥ K_good * C_P * 13 * Real.rpow 2 s)
    (hk_ge_2 : 2 ≤ k)
    (h_good : scaleClass 0 = ScaleClass.good t_j)
    (hC_ge : K_good + 1 ≤ C) (hC'_ge : 1 ≤ C') :
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
  have hδ_def : δ = dyadicDelta k := rfl
  have hC₁_def : C₁ = Real.rpow δ (-lam) := rfl
  have hL_def : L = Real.log (1 / δ) := rfl
  have hδEI_def : δEI = DiscretisedFurstenbergEstimate.δ k := rfl

  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδEI_pos : 0 < δEI := DiscretisedFurstenbergEstimate.δ_pos k
  have hδ_eq : δ = δEI := by
    simp [hδ_def, hδEI_def, dyadicDelta, DiscretisedFurstenbergEstimate.δ] <;> ring
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    have h1 : (k : ℕ) ≥ 2 := hk_ge_2
    have h2 : δ = ((2 : ℝ)^k)⁻¹ := by simp [δ, dyadicDelta] <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^k ≥ 4 := by
      have h4 : (2 : ℝ)^k ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢ <;> exact h4
    have h5 : 0 < (2 : ℝ)^k := by positivity
    have h6 : ((2 : ℝ)^k)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
    norm_num at h6 ⊢ <;> exact h6
  have hδ_lt_one : δ < 1 := by linarith
  have hδ_le_one : δ ≤ 1 := by linarith

  have hC₁_pos : 0 < C₁ := Real.rpow_pos_of_pos hδ_pos _
  have hC₁_ge1 : 1 ≤ C₁ := by
    have h1 : 0 < Real.rpow δ lam := Real.rpow_pos_of_pos hδ_pos lam
    have h2 : Real.rpow δ lam < 1 := Real.rpow_lt_one (by linarith) (by linarith) hlam
    have h3 : C₁ = (Real.rpow δ lam)⁻¹ := by
      simp [hC₁_def, Real.rpow_neg hδ_pos.le] <;> field_simp <;> ring
    rw [h3]
    have h4 : 1 ≤ (Real.rpow δ lam)⁻¹ := by
      have h5 : Real.rpow δ lam ≤ 1 := h2.le
      exact (one_le_inv₀ h1).mpr h5
    exact h4

  have hCP_pos : 0 < C_P := by linarith
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hM_pos : 0 < M := hcfg.hM_pos

  -- u ≤ min(t_j,1) since u ≤ t ≤ t_j and u ≤ 1
  have h_u_le_min_tj : u ≤ min t_j 1 := by
    have h1 : t ≤ t_j := hextra.h_tj_ge_t 0 t_j h_good
    have h2 : u ≤ t := by rw [hu_eq] <;> exact min_le_left t 1
    have h3 : u ≤ 1 := hu1
    exact le_min (le_trans h2 h1) h3

  have hP_set_tj : IsFinsetDeltaSSet (dyadicDelta k) (min t_j 1) C_P
      (finsetDyadicToDSquare config.P₀) := by
    exact hextra.hP_set_tj 0 t_j h_good

  have hP_set_u : IsFinsetDeltaSSet (dyadicDelta k) u C_P
      (finsetDyadicToDSquare config.P₀) :=
    finset_deltaSSet_weaken_exponent hP_set_tj (by linarith) h_u_le_min_tj hCP

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
    simp [hδ_def, dyadicDelta] <;> ring

  have h_index_bounds : ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ) := by
    intro p hp
    let p_dy := dSquareToDyadicSquare p
    have hpin : p_dy ∈ config.P₀ := (h_mem_iff p).mp hp
    have h_sq : ∀ (p : DyadicSquare k), p ∈ config.P₀ →
        0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ) := by
      exact hB1.h_squares_unit
    exact h_sq p_dy hpin

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
  have hγ_def : γ = (η + 2 * ε_G) * (1 - s) / (u - s) := rfl
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; have h1 : 0 < η + 2 * ε_G := by linarith
    have h2 : 0 < 1 - s := by linarith
    have h3 : 0 < u - s := h_us_pos
    positivity
  let α : ℝ := (u - s) / (1 - s)
  have hα_def : α = (u - s) / (1 - s) := rfl
  have hα_nonneg : 0 ≤ α := by
    have h1 : 0 ≤ u - s := by linarith
    have h2 : 0 < 1 - s := by linarith
    exact div_nonneg h1 (by linarith)
  have hγ_α_eq : γ * α = η + 2 * ε_G := by
    rw [hγ_def, hα_def]
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

  let KCT' : ℝ := K_good * C_P * 13 * Real.rpow 2 s
  have hKCT'def : KCT' = K_good * C_P * 13 * Real.rpow 2 s := rfl
  have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have hKCT'pos : 0 < KCT' := by
    dsimp only [KCT']
    have h13_pos : (0 : ℝ) < 13 := by norm_num
    exact mul_pos (mul_pos (mul_pos hK_pos hCP_pos) h13_pos) h2s_pos

  have hC_K_ge_one : 1 ≤ C - K_good := by linarith

  have h_key : L ^ (C - K_good) ≥ KCT' * Real.rpow δ ε_N := by
    have h1 : L ^ (C - K_good) ≥ L := by
      have h2 : 1 ≤ L := hL_ge_one
      have h3 : 1 ≤ C - K_good := hC_K_ge_one
      have h4 : L ^ (1 : ℝ) ≤ L ^ (C - K_good) := by exact (Real.rpow_le_rpow_left_iff hL_gt_one).mpr hC_K_ge_one
      have h5 : L ^ (1 : ℝ) = L := by simp
      rw [h5] at h4; exact h4
    have h4 : L ≥ KCT' := h_log_ge
    have h5 : KCT' * Real.rpow δ ε_N < KCT' := by
      have h6 : Real.rpow δ ε_N < 1 := Real.rpow_lt_one (by linarith) (by linarith) hεN
      nlinarith
    have h7 : L ≥ KCT' * Real.rpow δ ε_N := by linarith
    linarith

  have h_absorb : (1 / KCT') * L ^ (-K_good) ≥ L ^ (-C) * Real.rpow δ ε_N := by
    have h15 : L ^ (-K_good) = L ^ (C - K_good) * L ^ (-C) := by
      rw [← Real.rpow_add hL_pos] <;> ring_nf
    rw [h15]
    have h16 : 0 < L ^ (-C) := Real.rpow_pos_of_pos hL_pos _
    have h17 : L ^ (C - K_good) ≥ KCT' * Real.rpow δ ε_N := h_key
    calc
      (1 / KCT') * (L ^ (C - K_good) * L ^ (-C))
        = L ^ (-C) * ((1 / KCT') * L ^ (C - K_good)) := by ring
      _ ≥ L ^ (-C) * ((1 / KCT') * (KCT' * Real.rpow δ ε_N)) := by gcongr
      _ = L ^ (-C) * Real.rpow δ ε_N := by
        field_simp [hKCT'pos.ne'] <;> ring

  have hγ_le : γ ≤ ε_G + lam + ε_N - η := by
    rw [hγ_def, hu_eq]
    exact hextra.h_exp_condition

  by_cases hM_large : (M : ℝ) ≥ Real.rpow δ (-s - γ)
  · -- LARGE M CASE
    have h_wrapper := uniform_prop5_wrapper_with_K
      (t := u) (hK_pos := hK_pos) (hK_spec := hK_spec_u)
      (config := config) (hn_ge_2 := hk_ge_2) (hM_pos := hM_pos)
      (hP_nonempty := hP_nonempty) (hCP := hCP_pos) (hCP_ge1 := hCP)
      (hC₁ := hC₁_pos) (hC1_ge1 := hC₁_ge1)
      (hs_nonneg := hs_nonneg) (hP_set := hP_set_u)
      (h_slope := hextra.h_slope)
      (h_diam := h_diam) (h_unit := h_unit)

    have h_main_real : (config.T₀.card : ℝ) ≥
        (1 / K_good) * L ^ (-K_good) *
          (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by
      simpa [hL_def, hδ_def, hα_def, hC₁_def] using h_wrapper

    have h_inv_C1 : (1 : ℝ) / C₁ = Real.rpow δ lam := by
      have h_pos1 : 0 < Real.rpow δ (-lam) := Real.rpow_pos_of_pos hδ_pos (-lam)
      have h_eq : Real.rpow δ (-lam) * Real.rpow δ lam = 1 := by
        have h := Real.rpow_add hδ_pos (-lam) lam
        have h5 : -lam + lam = 0 := by ring
        rw [h5] at h; simpa using h.symm
      have h_goal : (1 : ℝ) / Real.rpow δ (-lam) = Real.rpow δ lam := by
        field_simp [h_pos1.ne'] <;> linarith
      exact h_goal

    have h_simp_coeff : (1 / K_good) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
        (1 / KCT') * Real.rpow δ lam := by
      have h1 : (1 / K_good) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
          (1 / KCT') * (1 / C₁) := by
        simp only [hKCT'def] <;> ring
      rw [h1, h_inv_C1]

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
          (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
        (1 / KCT') * L ^ (-K_good) * Real.rpow δ lam := by
      have h : (1 / K_good) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
          (1 / KCT') * Real.rpow δ lam := h_simp_coeff
      calc
        (1 / K_good) * L ^ (-K_good) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s)))
          = L ^ (-K_good) * ((1 / K_good) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s)))) := by ring
        _ = L ^ (-K_good) * ((1 / KCT') * Real.rpow δ lam) := by rw [h]
        _ = (1 / KCT') * L ^ (-K_good) * Real.rpow δ lam := by ring

    have h_bound_full : (config.T₀.card : ℝ) ≥
        (1 / KCT') * L ^ (-K_good) * (M : ℝ) * Real.rpow δ lam *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by
      rw [h_coeff] at h_main_real
      have h_comm : (1 / KCT') * L ^ (-K_good) * Real.rpow δ lam * (M : ℝ) *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α =
        (1 / KCT') * L ^ (-K_good) * (M : ℝ) * Real.rpow δ lam *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by
        have h_mul : Real.rpow δ lam * (M : ℝ) = (M : ℝ) * Real.rpow δ lam := mul_comm _ _
        have h1 : (1 / KCT') * L ^ (-K_good) * Real.rpow δ lam * (M : ℝ) =
            (1 / KCT') * L ^ (-K_good) * (M : ℝ) * Real.rpow δ lam := by
          calc
            (1 / KCT') * L ^ (-K_good) * Real.rpow δ lam * (M : ℝ)
              = (1 / KCT') * L ^ (-K_good) * (Real.rpow δ lam * (M : ℝ)) := by ring
            _ = (1 / KCT') * L ^ (-K_good) * ((M : ℝ) * Real.rpow δ lam) := by rw [h_mul]
            _ = (1 / KCT') * L ^ (-K_good) * (M : ℝ) * Real.rpow δ lam := by ring
        have h2 : (1 / KCT') * L ^ (-K_good) * Real.rpow δ lam * (M : ℝ) *
              Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α =
            ((1 / KCT') * L ^ (-K_good) * Real.rpow δ lam * (M : ℝ)) *
              Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by ring
        rw [h2, h1] <;> ring
      rw [h_comm] at h_main_real
      exact h_main_real

    have h_pos_factor : 0 ≤ (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) *
        ((M : ℝ) * Real.rpow δ s) ^ α := by
      have h1 : 0 ≤ (M : ℝ) := by positivity
      have h2 : 0 ≤ Real.rpow δ lam := Real.rpow_nonneg hδ_pos.le _
      have h3 : 0 ≤ Real.rpow δ (-s) := Real.rpow_nonneg hδ_pos.le _
      have h4 : 0 ≤ (M : ℝ) * Real.rpow δ s := mul_nonneg h1 (Real.rpow_nonneg hδ_pos.le s)
      have h5 : 0 ≤ ((M : ℝ) * Real.rpow δ s) ^ α := Real.rpow_nonneg h4 α
      positivity

    have h9 : (1 / KCT') * L ^ (-K_good) * (M : ℝ) * Real.rpow δ lam *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α ≥
        L ^ (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
          ((M : ℝ) * Real.rpow δ s) ^ α := by
      have h10 : Real.rpow δ ε_N * Real.rpow δ (-s) = Real.rpow δ (-s + ε_N) := by
        have h11 : Real.rpow δ (ε_N + (-s)) = Real.rpow δ ε_N * Real.rpow δ (-s) :=
          Real.rpow_add hδ_pos ε_N (-s)
        have h12 : ε_N + (-s) = -s + ε_N := by ring
        rw [h12] at h11
        exact h11.symm
      calc
        (1 / KCT') * L ^ (-K_good) * (M : ℝ) * Real.rpow δ lam *
            Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α
          = ((1 / KCT') * L ^ (-K_good)) *
              ((M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by ring
        _ ≥ (L ^ (-C) * Real.rpow δ ε_N) *
              ((M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by
          exact mul_le_mul_of_nonneg_right h_absorb h_pos_factor
        _ = L ^ (-C) * (M : ℝ) * Real.rpow δ lam *
              (Real.rpow δ ε_N * Real.rpow δ (-s)) * ((M : ℝ) * Real.rpow δ s) ^ α := by ring
        _ = L ^ (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
              ((M : ℝ) * Real.rpow δ s) ^ α := by rw [h10] <;> ring

    have h12 : 0 ≤ L ^ (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) := by
      have h121 : 0 ≤ L ^ (-C) := Real.rpow_nonneg hL_pos.le _
      have h122 : 0 ≤ (M : ℝ) := by positivity
      have h123 : 0 ≤ Real.rpow δ lam := Real.rpow_nonneg hδ_pos.le _
      have h124 : 0 ≤ Real.rpow δ (-s + ε_N) := Real.rpow_nonneg hδ_pos.le _
      positivity

    have h11 : L ^ (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
          ((M : ℝ) * Real.rpow δ s) ^ α ≥
        L ^ (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
          Real.rpow δ (-(η + 2 * ε_G)) := by
      exact mul_le_mul_of_nonneg_left h_factor2 h12

    have h13 : Real.rpow δ lam * Real.rpow δ (-s + ε_N) * Real.rpow δ (-(η + 2 * ε_G)) =
        Real.rpow δ (lam - s + ε_N - η - 2 * ε_G) := by
      have h14 : Real.rpow δ lam * Real.rpow δ (-s + ε_N) =
          Real.rpow δ (lam + (-s + ε_N)) := by
        exact (Real.rpow_add hδ_pos lam (-s + ε_N)).symm
      have h15 : Real.rpow δ (lam + (-s + ε_N)) * Real.rpow δ (-(η + 2 * ε_G)) =
          Real.rpow δ ((lam + (-s + ε_N)) + (-(η + 2 * ε_G))) := by
        exact (Real.rpow_add hδ_pos (lam + (-s + ε_N)) (-(η + 2 * ε_G))).symm
      rw [h14, h15] <;> ring_nf

    have h16 : Real.rpow δ (lam - s + ε_N - η - 2 * ε_G) ≥
        Real.rpow δ (lam - s + ε_N - η) := by
      have h17 : lam - s + ε_N - η - 2 * ε_G ≤ lam - s + ε_N - η := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h17

    have h_main_good : (config.T₀.card : ℝ) ≥
        L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
      calc (config.T₀.card : ℝ)
        ≥ (1 / KCT') * L ^ (-K_good) * (M : ℝ) * Real.rpow δ lam *
            Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := h_bound_full
        _ ≥ L ^ (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
              ((M : ℝ) * Real.rpow δ s) ^ α := h9
        _ ≥ L ^ (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
              Real.rpow δ (-(η + 2 * ε_G)) := h11
        _ = L ^ (-C) * (M : ℝ) *
              (Real.rpow δ lam * Real.rpow δ (-s + ε_N) * Real.rpow δ (-(η + 2 * ε_G))) := by ring
        _ = L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η - 2 * ε_G) := by rw [h13]
        _ ≥ L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
          have h18 : 0 ≤ L ^ (-C) * (M : ℝ) := by
            have h181 : 0 ≤ L ^ (-C) := Real.rpow_nonneg hL_pos.le _
            have h182 : 0 ≤ (M : ℝ) := by positivity
            positivity
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

  · -- SMALL M CASE
    have hM_small : (M : ℝ) < Real.rpow δ (-s - γ) := by
      exact lt_of_not_ge hM_large

    have hT_lower_real : (config.T₀.card : ℝ) ≥ Real.rpow δ (-(2 * s + ε_G)) := by
      have h : (config.T₀.card : ENNReal) ≥ ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) := by
        have h' := hextra.h_improved_incidence
        exact h'
      have h_nonneg : 0 ≤ Real.rpow δ (-(2 * s + ε_G)) := Real.rpow_nonneg hδ_pos.le _
      exact ENNReal.ofReal_le_natCast.mp h

    have hL_neg_C_le_one : L ^ (-C) ≤ 1 := by
      have h1 : 1 ≤ L := by linarith
      have h2 : -C ≤ 0 := by linarith
      have h3 : L ^ (-C) ≤ L ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 h2
      have h4 : L ^ (0 : ℝ) = 1 := by simp
      rw [h4] at h3; exact h3

    have h_exp_ge : lam - 2 * s - γ + ε_N - η ≥ -(2 * s + ε_G) := by
      have h : γ ≤ ε_G + lam + ε_N - η := hγ_le
      calc
        lam - 2 * s - γ + ε_N - η
          ≥ lam - 2 * s - (ε_G + lam + ε_N - η) + ε_N - η := by gcongr
        _ = -(2 * s + ε_G) := by ring

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

    have h81 : L ^ (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
        L ^ (-C) * (Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η)) := by ring
    have h8 : L ^ (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
        L ^ (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
      rw [h81, h_rpow_combine]

    have h11 : L ^ (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) ≤
        Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
      have h12 : 0 ≤ Real.rpow δ (lam - 2 * s - γ + ε_N - η) := Real.rpow_nonneg hδ_pos.le _
      have h13 : L ^ (-C) ≤ 1 := hL_neg_C_le_one
      exact mul_le_of_le_one_left h12 h13

    have h14 : Real.rpow δ (lam - 2 * s - γ + ε_N - η) ≤
        Real.rpow δ (-(2 * s + ε_G)) := by
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h_exp_ge

    have h6 : L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) <
        Real.rpow δ (-(2 * s + ε_G)) := by
      calc
        L ^ (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η)
          < L ^ (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) := by
            exact mul_lt_mul_of_pos_right h7 h_pos_exp
        _ = L ^ (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) := h8
        _ ≤ Real.rpow δ (lam - 2 * s - γ + ε_N - η) := h11
        _ ≤ Real.rpow δ (-(2 * s + ε_G)) := h14

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

end BaseGoodUniform

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

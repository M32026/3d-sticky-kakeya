module

/-
  UniformFurstenberg.lean

  Extract a uniform Furstenberg estimate valid for all σ in [β, 1-ε].

  Uses partition + IsDeltaSet.mono_s to convert σ → σ_j (subinterval endpoint),
  then applies the Furstenberg axiom at (σ_j, 1).

  Main result: `uniform_furstenberg`
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.FurstenbergBridge
public import MyLeanRepo.RadialBootstrapping.FurstenbergLowerBound
public import MyLeanRepo.discretised_furstenberg_estimate
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

open DirecretisedFurstenbergEstimate

/-- **Monotonicity in s**: If `P` is a `(δ, s, C)`-set and `s' ≥ s`,
    then `P` is a `(δ, s', C · δ^{-(s'-s)})`-set. -/
lemma IsDeltaSet.mono_s {X : Type*} [PseudoMetricSpace X] {δ s C : ℝ}
    {hδ : 0 < δ} {hs : 0 ≤ s} {hC : 0 ≤ C} {P : Set X}
    (h : IsDeltaSet δ s C hδ hs hC P)
    {s' : ℝ} (hs' : 0 ≤ s') (hss' : s ≤ s') :
    IsDeltaSet δ s' (C * Real.rpow δ (-(s' - s))) hδ hs'
      (mul_nonneg hC (Real.rpow_nonneg (by linarith) _)) P := by
  let C' : ℝ := C * Real.rpow δ (-(s' - s))
  have hC'_nonneg : 0 ≤ C' := mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  intro x r hr
  have hr_pos : 0 < r := lt_of_lt_of_le hδ hr
  set e : ℝ := -(s' - s) with he_def
  set e' : ℝ := -e with he'_def
  have he'_nonneg : 0 ≤ e' := by linarith
  have h_rpow_decr : Real.rpow r e ≤ Real.rpow δ e := by
    have h1 : Real.rpow δ e' ≤ Real.rpow r e' := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have h2 : Real.rpow δ e = (Real.rpow δ e')⁻¹ := by
      have h3 : e = -e' := by ring
      rw [h3]; exact Real.rpow_neg (by linarith) e'
    have h4 : Real.rpow r e = (Real.rpow r e')⁻¹ := by
      have h5 : e = -e' := by ring
      rw [h5]; exact Real.rpow_neg (by linarith) e'
    rw [h2, h4]
    have h6 : 0 < Real.rpow δ e' := Real.rpow_pos_of_pos hδ e'
    have h7 : 0 < Real.rpow r e' := Real.rpow_pos_of_pos hr_pos e'
    have h8 : (Real.rpow r e')⁻¹ ≤ (Real.rpow δ e')⁻¹ := by
      gcongr
      <;> linarith
    exact h8
  have h1 : C * Real.rpow r s ≤ C' * Real.rpow r s' := by
    have h2 : Real.rpow r s = Real.rpow r s' * Real.rpow r e := by
      have h4 : s = s' + e := by simp [he_def] <;> ring
      rw [h4]; exact Real.rpow_add (by linarith) s' e
    rw [h2]
    have h4 : Real.rpow r e ≤ Real.rpow δ e := h_rpow_decr
    have h5 : 0 ≤ Real.rpow r s' := Real.rpow_nonneg (by linarith) s'
    have h6 : C * (Real.rpow r s' * Real.rpow r e) ≤ C * (Real.rpow r s' * Real.rpow δ e) := by gcongr
    have h7 : C * (Real.rpow r s' * Real.rpow δ e) = C' * Real.rpow r s' := by
      dsimp only [C']; ring
    calc
      C * (Real.rpow r s' * Real.rpow r e)
        ≤ C * (Real.rpow r s' * Real.rpow δ e) := h6
      _ = C' * Real.rpow r s' := h7
  have h9 : ENNReal.ofReal (C * Real.rpow r s) ≤ ENNReal.ofReal (C' * Real.rpow r s') :=
    ENNReal.ofReal_le_ofReal h1
  calc
    (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ (P ∩ ball x r) : ENNReal)
      ≤ ENNReal.ofReal (C * Real.rpow r s) *
          (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ P : ENNReal) := h.spec x r hr
    _ ≤ ENNReal.ofReal (C' * Real.rpow r s') *
          (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ P : ENNReal) := by
      gcongr <;> exact h9

/-- Generalized scale lemma: for δ ≤ 2^(-K/(ε_a - ε_F)),
    δ^(-ε_F) * 2^K ≤ δ^(-ε_a). -/
lemma scale_lemma_general (δ K ε_a ε_F : ℝ)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hεa : 0 < ε_a) (hεF : 0 < ε_F) (hεF_lt : ε_F < ε_a)
    (h : δ ≤ Real.rpow 2 (-(K / (ε_a - ε_F)))) :
    Real.rpow δ (-ε_F) * Real.rpow 2 K ≤ Real.rpow δ (-ε_a) := by
  set d : ℝ := ε_a - ε_F with hd_def
  have hd_pos : 0 < d := by linarith
  have h_nonneg2 : 0 ≤ (2 : ℝ) := by norm_num
  have h_rpow_mul : Real.rpow (Real.rpow 2 (-(K / d))) d = Real.rpow 2 (-K) := by
    have h_eq : ∀ (x y z : ℝ), 0 ≤ x → Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) := by
      intro x y z hx
      have h : Real.rpow x (y * z) = Real.rpow (Real.rpow x y) z := Real.rpow_mul hx y z
      exact h.symm
    have h3 := h_eq 2 (-(K / d)) d h_nonneg2
    rw [h3]
    have h4 : (-(K / d)) * d = -K := by field_simp [hd_pos.ne'] <;> ring
    rw [h4] <;> ring
  have h1 : Real.rpow δ d ≤ Real.rpow 2 (-K) := by
    have h5 : Real.rpow δ d ≤ Real.rpow (Real.rpow 2 (-(K / d))) d :=
      Real.rpow_le_rpow (by positivity) h (by linarith)
    rw [h_rpow_mul] at h5
    exact h5
  have h_pos1 : 0 < Real.rpow δ d := Real.rpow_pos_of_pos hδ d
  have h_pos2 : 0 < Real.rpow 2 K := Real.rpow_pos_of_pos (by norm_num) K
  have h_rpow_neg_d : Real.rpow δ (-d) = (Real.rpow δ d)⁻¹ := by
    exact Real.rpow_neg (show 0 ≤ δ by linarith) d
  have h_rpow_neg_K : Real.rpow 2 (-K) = (Real.rpow 2 K)⁻¹ := by
    exact Real.rpow_neg (show 0 ≤ (2 : ℝ) by norm_num) K
  rw [h_rpow_neg_K] at h1
  have h6 : (Real.rpow δ d)⁻¹ ≥ Real.rpow 2 K := by
    have h7 : Real.rpow δ d ≤ (Real.rpow 2 K)⁻¹ := h1
    have h8 : 0 < Real.rpow δ d := h_pos1
    have h9 : 0 < (Real.rpow 2 K)⁻¹ := by positivity
    have h10 : 1 / (Real.rpow 2 K)⁻¹ ≤ 1 / Real.rpow δ d := one_div_le_one_div_of_le h_pos1 h7
    have h11 : 1 / (Real.rpow 2 K)⁻¹ = Real.rpow 2 K := by
      field_simp [h_pos2.ne'] <;> ring
    have h12 : 1 / Real.rpow δ d = (Real.rpow δ d)⁻¹ := by ring
    rw [h11, h12] at h10
    exact h10
  have h10 : Real.rpow 2 K ≤ Real.rpow δ (-d) := by
    rw [h_rpow_neg_d]
    exact h6
  have h13 : Real.rpow δ (-ε_a) = Real.rpow δ (-ε_F) * Real.rpow δ (-d) := by
    have h14 : -ε_a = -ε_F + -d := by simp [hd_def] <;> ring
    have h15 : Real.rpow δ (-ε_a) = Real.rpow δ (-ε_F + -d) := by rw [h14]
    rw [h15]
    have h16 : Real.rpow δ (-ε_F + -d) = Real.rpow δ (-ε_F) * Real.rpow δ (-d) := by
      have h17 : Real.rpow δ (-ε_F + -d) = Real.rpow δ (-ε_F) * Real.rpow δ (-d) := by
        exact Real.rpow_add (by linarith) (-ε_F) (-d)
      exact h17
    exact h16
  rw [h13]
  have h18 : 0 ≤ Real.rpow δ (-ε_F) := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_left h10 h18

/-- Uniform Furstenberg estimate.

    Produces ε_F > 0 and δ* > 0 such that for every σ ∈ [β, 1-ε],
    the Furstenberg lower bound holds with constant δ^(-ε_F) and
    LHS δ^(-2σ-ε_F), for all δ ≤ δ*. -/
lemma uniform_furstenberg
    (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) (hβ_lt : β < 1 - ε) :
    ∃ (ε_F δ_star : ℝ),
      0 < ε_F ∧ 0 < δ_star ∧
      ∀ (σ : ℝ) (hσ : σ ∈ Set.Icc β (1 - ε)),
        (∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ_star →
          ∀ (X : Set Point) (T : Point → Set Line2),
            X.Nonempty → X ⊆ closedBall 0 1 →
            IsDeltaSet δ 1 (Real.rpow δ (-ε_F)) hδ (by norm_num) (Real.rpow_nonneg hδ.le _) X →
            (∀ x ∈ X, (T x).Nonempty ∧
              IsDeltaSet δ σ (Real.rpow δ (-ε_F)) hδ (show 0 ≤ σ from by linarith [hσ.1, hβ]) (Real.rpow_nonneg hδ.le _) (T x) ∧
              ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
            Set.Finite (⋃ x ∈ X, T x) →
            (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * σ - ε_F))) := by
  rcases discretised_furstenberg_estimate with ⟨ε_axiom, hε_pos, hcompact, h_main_axiom⟩
  let A : Set (ℝ × ℝ) := Set.Icc β (1 - ε) ×ˢ {1}
  have hA_compact : IsCompact A := by
    have h1 : IsCompact (Set.Icc β (1 - ε) : Set ℝ) := isCompact_Icc
    have h2 : IsCompact ({(1 : ℝ)} : Set ℝ) := by exact isCompact_singleton
    exact IsCompact.prod h1 h2
  have hA_range : A ⊆ parameterRange := by
    intro p hp
    have h1 : p.1 ∈ Set.Icc β (1 - ε) := hp.1
    have h2 : p.2 = 1 := hp.2
    simp only [parameterRange, Set.mem_setOf_eq]
    constructor
    · exact ⟨by linarith [hβ, h1.1], by linarith [hε, h1.2]⟩
    · rw [h2]
      constructor
      · linarith [h1.2, hε]
      · norm_num
  rcases hcompact A hA_compact hA_range with ⟨ε₀, hε₀_pos, hε₀_lower⟩
  let ε_F : ℝ := ε₀ / 3
  have hεF_pos : 0 < ε_F := by positivity
  let L : ℝ := 1 - ε - β
  have hL_pos : 0 < L := by linarith
  let J : ℕ := Nat.ceil (4 * L / ε_F)
  have hJ_pos : 0 < J := Nat.ceil_pos.mpr (by positivity)
  let step : ℝ := L / (J : ℝ)
  have hstep_pos : 0 < step := by positivity
  have hstep_le : step ≤ ε_F / 4 := by
    have h1 : (J : ℝ) ≥ 4 * L / ε_F := Nat.le_ceil _
    dsimp only [step]
    calc L / (J : ℝ) ≤ L / (4 * L / ε_F) := by gcongr <;> linarith
      _ = ε_F / 4 := by field_simp [hL_pos.ne'] <;> ring
  let σ_j : ℕ → ℝ := fun k => β + (k : ℝ) * step
  have hσ_j_range : ∀ k ∈ Finset.Icc 1 J, σ_j k ∈ Set.Icc β (1 - ε) := by
    intro k hk
    have h1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have h2 : k ≤ J := (Finset.mem_Icc.mp hk).2
    constructor
    · dsimp only [σ_j]
      have h_nonneg : 0 ≤ (k : ℝ) * step := by positivity
      linarith
    · dsimp only [σ_j]
      have h4 : (k : ℝ) ≤ (J : ℝ) := by exact_mod_cast h2
      have h5 : (k : ℝ) * step ≤ L := by
        calc (k : ℝ) * step ≤ (J : ℝ) * step := by gcongr
          _ = L := by dsimp only [step]; field_simp [hJ_pos.ne'] <;> ring
      linarith
  have hσ_j_in_range : ∀ k ∈ Finset.Icc 1 J, (σ_j k, (1 : ℝ)) ∈ parameterRange := by
    intro k hk
    have h1 := hσ_j_range k hk
    simp only [parameterRange, Set.mem_setOf_eq]
    constructor
    · exact ⟨by linarith [hβ, h1.1], by linarith [hε, h1.2]⟩
    · exact ⟨by linarith [h1.2], by norm_num⟩
  choose δ₀_k hδ₀_k_pos hδ₀_k_axiom using fun k (hk : k ∈ Finset.Icc 1 J) =>
    h_main_axiom (σ_j k) 1 (hσ_j_in_range k hk)
  let ε_a_k : ℕ → ℝ := fun k => ε_axiom (σ_j k, 1)
  have hε_a_k_lower : ∀ k ∈ Finset.Icc 1 J, ε₀ ≤ ε_a_k k := by
    intro k hk
    have h1 : (σ_j k, (1 : ℝ)) ∈ A := by
      simp only [A, Set.mem_setOf_eq]; exact ⟨hσ_j_range k hk, by norm_num⟩
    exact hε₀_lower (σ_j k, 1) h1
  have hε_a_k_pos : ∀ k ∈ Finset.Icc 1 J, 0 < ε_a_k k := by
    intro k hk; linarith [hε₀_pos, hε_a_k_lower k hk]
  have hε_a_k_gt : ∀ k ∈ Finset.Icc 1 J, 5 * ε_F / 4 < ε_a_k k := by
    intro k hk
    have h1 : ε₀ ≤ ε_a_k k := hε_a_k_lower k hk
    have h2 : ε_F = ε₀ / 3 := by rfl
    linarith
  let δ_scale_k : ℕ → ℝ := fun k => Real.rpow 2 (-(1 / (ε_a_k k - 5 * ε_F / 4)))
  have hδ_scale_k_pos : ∀ k ∈ Finset.Icc 1 J, 0 < δ_scale_k k := by
    intro k hk; exact Real.rpow_pos_of_pos (by norm_num) _
  let δ₀'_k : ℕ → ℝ := fun k => if h : k ∈ Finset.Icc 1 J then min (δ₀_k k h) (δ_scale_k k) else 1
  have hδ₀'_k_pos : ∀ k ∈ Finset.Icc 1 J, 0 < δ₀'_k k := by
    intro k hk
    have h_eq : δ₀'_k k = min (δ₀_k k hk) (δ_scale_k k) := by
      dsimp only [δ₀'_k]
      exact dif_pos hk
    rw [h_eq]
    have h1 : 0 < δ₀_k k hk := hδ₀_k_pos k hk
    have h2 : 0 < δ_scale_k k := hδ_scale_k_pos k hk
    exact lt_min h1 h2
  let s_finset : Finset ℕ := Finset.Icc 1 J
  let im : Finset ℝ := Finset.image δ₀'_k s_finset
  have him_nonempty : im.Nonempty :=
    Finset.image_nonempty.mpr (Finset.nonempty_Icc.mpr (by omega))
  let δ_star : ℝ := im.min' him_nonempty
  have hδ_star_mem : δ_star ∈ im := by
    exact Finset.min'_mem im him_nonempty
  have hδ_star_le' : ∀ (x : ℝ), x ∈ im → δ_star ≤ x := fun x hx => Finset.min'_le _ x hx
  have hδ_star_pos : 0 < δ_star := by
    rcases Finset.mem_image.mp hδ_star_mem with ⟨k, hk, h_eq⟩
    have h_goal : 0 < δ₀'_k k := hδ₀'_k_pos k hk
    rwa [h_eq] at h_goal
  have hδ_star_le : ∀ k ∈ Finset.Icc 1 J, δ_star ≤ δ₀'_k k := by
    intro k hk
    have h_in : δ₀'_k k ∈ im := Finset.mem_image.mpr ⟨k, hk, rfl⟩
    exact hδ_star_le' (δ₀'_k k) h_in
  refine' ⟨ε_F, δ_star, hεF_pos, hδ_star_pos, _⟩
  intro σ hσ
  have hσ1 : β ≤ σ := hσ.1
  have hσ2 : σ ≤ 1 - ε := hσ.2
  let k : ℕ := Nat.ceil ((σ - β) / step)
  let k' : ℕ := if k = 0 then 1 else k
  have h_k_le_J : k ≤ J := by
    have h1 : (σ - β) / step ≤ (J : ℝ) := by
      have h2 : σ - β ≤ L := by linarith
      have h3 : (σ - β) / step ≤ L / step := by gcongr
      have h4 : L / step = (J : ℝ) := by
        dsimp only [step]; field_simp [hJ_pos.ne'] <;> ring
      linarith
    exact Nat.ceil_le.mpr h1
  have hk'_in : k' ∈ Finset.Icc 1 J := by
    simp only [k', Finset.mem_Icc]
    split_ifs <;> constructor <;> omega
  have hσ_le_j : σ ≤ σ_j k' := by
    dsimp only [σ_j, k']
    split_ifs with h
    · -- k = 0, k' = 1
      have h_ceil : Nat.ceil ((σ - β) / step) ≤ 0 := by
        exact le_of_eq h
      have h_k0 : (σ - β) / step ≤ 0 := by
        have h' : (σ - β) / step ≤ ↑(0 : ℕ) := (Nat.ceil_le (n := 0)).mp h_ceil
        simpa using h'
      have h_nonpos : σ - β ≤ 0 := by
        have h_mul : ((σ - β) / step) * step ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h_k0 hstep_pos.le
        have h_eq : ((σ - β) / step) * step = σ - β := by
          field_simp [hstep_pos.ne'] <;> ring
        rw [h_eq] at h_mul
        exact h_mul
      have h_nonneg : 0 ≤ σ - β := by linarith
      have h_sigma_eq : σ = β := by linarith
      rw [h_sigma_eq] <;> simp [σ_j] <;> linarith
    · -- k ≠ 0, k' = k
      have h : (σ - β) / step ≤ (k : ℝ) := Nat.le_ceil _
      have h' : σ - β ≤ (k : ℝ) * step := by
        calc σ - β = ((σ - β) / step) * step := by field_simp [hstep_pos.ne'] <;> ring
          _ ≤ (k : ℝ) * step := by gcongr
      simpa [h] using by linarith
  have hσ_j_minus : σ_j k' - σ ≤ ε_F / 4 := by
    by_cases h : k = 0
    · -- k = 0
      have h_ceil : Nat.ceil ((σ - β) / step) ≤ 0 := by
        exact le_of_eq h
      have h_k0 : (σ - β) / step ≤ 0 := by
        exact_mod_cast (Nat.ceil_le (n := 0)).mp h_ceil
      have h_nonpos : σ - β ≤ 0 := by
        have h_mul : ((σ - β) / step) * step ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h_k0 hstep_pos.le
        have h_eq : ((σ - β) / step) * step = σ - β := by
          field_simp [hstep_pos.ne'] <;> ring
        rw [h_eq] at h_mul
        exact h_mul
      have h_nonneg : 0 ≤ σ - β := by linarith
      have h_eq : σ = β := by linarith
      have h_k'_eq : k' = 1 := by
        simp [k', h]
      have h_goal : σ_j k' - σ ≤ ε_F / 4 := by
        rw [h_eq, h_k'_eq]
        simp [σ_j, hstep_le] <;> linarith
      exact h_goal
    · -- k ≠ 0
      have h_k_pos : 0 < k := by omega
      have h_k_ge_one : 1 ≤ k := by omega
      have h2' : (k - 1 : ℕ) < Nat.ceil ((σ - β) / step) := by
        simpa [k] using show (k - 1 : ℕ) < k from by omega
      have h3 : ((k - 1 : ℕ) : ℝ) < (σ - β) / step := by
        have h4 : (k - 1 : ℕ) < Nat.ceil ((σ - β) / step) := h2'
        exact Nat.lt_ceil.mp h2'
      have h4 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub h_k_ge_one] <;> norm_num
      have h1 : (k : ℝ) - 1 < (σ - β) / step := by
        rw [←h4]; exact h3
      have h_k'_eq : k' = k := by
        simp [k', h]
      have h_id : σ_j k' - σ = ((k : ℝ) - (σ - β) / step) * step := by
        rw [h_k'_eq]
        dsimp only [σ_j]
        field_simp [hstep_pos.ne'] <;> ring
      have h5 : (k : ℝ) - (σ - β) / step < 1 := by linarith [h1]
      have h6 : 0 ≤ (k : ℝ) - (σ - β) / step := by
        have h7 : (σ - β) / step ≤ (k : ℝ) := Nat.le_ceil _
        linarith
      have h2 : σ_j k' - σ < step := by
        rw [h_id]; nlinarith
      have h_le : σ_j k' - σ ≤ step := le_of_lt h2
      have h_final : σ_j k' - σ ≤ ε_F / 4 := by
        calc σ_j k' - σ ≤ step := h_le
          _ ≤ ε_F / 4 := hstep_le
      exact h_final
  have hσ_j_pos : 0 < σ_j k' := by
    have h1 : β ≤ σ_j k' := (hσ_j_range k' hk'_in).1
    linarith
  have hσ_j_lt_one : σ_j k' < 1 := by
    have h1 : σ_j k' ≤ 1 - ε := (hσ_j_range k' hk'_in).2
    linarith
  intro δ hδ hδ_star X T hX_nonempty hX_ball hX_delta hT hfin
  have hδ₀'_eq : δ₀'_k k' = min (δ₀_k k' hk'_in) (δ_scale_k k') := by
    dsimp only [δ₀'_k]
    exact dif_pos hk'_in
  have hδ_le_axiom : δ ≤ δ₀_k k' hk'_in := by
    have h1 : δ_star ≤ δ₀'_k k' := hδ_star_le k' hk'_in
    have h2 : δ₀'_k k' ≤ δ₀_k k' hk'_in := by
      rw [hδ₀'_eq] <;> exact min_le_left _ _
    exact le_trans hδ_star (le_trans h1 h2)
  have hδ_le_scale : δ ≤ δ_scale_k k' := by
    have h1 : δ_star ≤ δ₀'_k k' := hδ_star_le k' hk'_in
    have h2 : δ₀'_k k' ≤ δ_scale_k k' := by
      rw [hδ₀'_eq] <;> exact min_le_right _ _
    exact le_trans hδ_star (le_trans h1 h2)
  let ε_a : ℝ := ε_a_k k'
  have hεa_pos : 0 < ε_a := hε_a_k_pos k' hk'_in
  have hεa_gt : 5 * ε_F / 4 < ε_a := hε_a_k_gt k' hk'_in
  have h_eps_diff_pos : 0 < ε_a - 5 * ε_F / 4 := by linarith [hεa_gt]
  have hδ_scale_lt_one : δ_scale_k k' < 1 := by
    dsimp only [δ_scale_k]
    have h_exp_neg : -(1 / (ε_a - 5 * ε_F / 4)) < 0 := by
      have h_pos : 0 < 1 / (ε_a - 5 * ε_F / 4) := by positivity
      linarith
    have h : Real.rpow 2 (-(1 / (ε_a - 5 * ε_F / 4))) < Real.rpow 2 0 :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_exp_neg
    simpa using h
  have hδ_lt_one : δ < 1 := lt_of_le_of_lt hδ_le_scale hδ_scale_lt_one
  have h_eps_diff2_pos : 0 < ε_a - ε_F := by linarith
  have h_scale_X_bound : δ_scale_k k' ≤ Real.rpow 2 (-(1 / (ε_a - ε_F))) := by
    dsimp only [δ_scale_k]
    have h_ineq : 1 / (ε_a - 5 * ε_F / 4) ≥ 1 / (ε_a - ε_F) := by
      gcongr
      <;> linarith [hεa_gt]
    have h_exp : -(1 / (ε_a - 5 * ε_F / 4)) ≤ -(1 / (ε_a - ε_F)) := by linarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp
  have hδ_le_scale_X : δ ≤ Real.rpow 2 (-(1 / (ε_a - ε_F))) :=
    le_trans hδ_le_scale h_scale_X_bound
  have h_scale_X : Real.rpow δ (-ε_F) * Real.rpow 2 1 ≤ Real.rpow δ (-ε_a) :=
    scale_lemma_general δ 1 ε_a ε_F hδ (by norm_num) hεa_pos hεF_pos (by linarith) hδ_le_scale_X
  have h_scale_T : Real.rpow δ (-(5 * ε_F / 4)) * Real.rpow 2 (σ_j k') ≤ Real.rpow δ (-ε_a) := by
    have hK_le : σ_j k' ≤ 1 := by
      have h1 : σ_j k' ≤ 1 - ε := (hσ_j_range k' hk'_in).2
      linarith
    have h2 : Real.rpow 2 (σ_j k') ≤ Real.rpow 2 1 := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num) hK_le
    have h_pos_rpow : 0 ≤ Real.rpow δ (-(5 * ε_F / 4)) := Real.rpow_nonneg (by linarith) _
    have h3 : Real.rpow δ (-(5 * ε_F / 4)) * Real.rpow 2 (σ_j k') ≤
        Real.rpow δ (-(5 * ε_F / 4)) * Real.rpow 2 1 := by
      gcongr
      <;> linarith
    have h4 := scale_lemma_general δ 1 ε_a (5 * ε_F / 4) hδ (by norm_num) hεa_pos (by positivity) (by linarith) hδ_le_scale
    exact le_trans h3 h4
  have hX_sset : IsDeltaSSet δ 1 (Real.rpow δ (-ε_a)) X := by
    have h1 : IsDeltaSSet δ 1 (Real.rpow δ (-ε_F) * Real.rpow 2 1) X :=
      IsDeltaSet.toIsDeltaSSet_same hX_delta hX_nonempty (Real.rpow_pos_of_pos hδ _)
    have h2 : Real.rpow δ (-ε_F) * Real.rpow 2 1 ≤ Real.rpow δ (-ε_a) := h_scale_X
    exact FurstenbergEstimate.IsDeltaSSet.mono_C h1 (Real.rpow_pos_of_pos hδ _) h2
  have hT_sset : ∀ (x : Point) (hx : x ∈ X),
      IsDeltaSSet δ (σ_j k') (Real.rpow δ (-ε_a)) (line2EquivAffineLine '' (T x)) := by
    intro x hx
    have hT_x := hT x hx
    have hT_nonempty : (T x).Nonempty := hT_x.1
    have hT_delta := hT_x.2.1
    have hC_mono : 0 ≤ Real.rpow δ (-ε_F) * Real.rpow δ (-(σ_j k' - σ)) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
    have h_mono_s : IsDeltaSet δ (σ_j k')
        (Real.rpow δ (-ε_F) * Real.rpow δ (-(σ_j k' - σ))) hδ (by linarith) hC_mono (T x) :=
      IsDeltaSet.mono_s hT_delta (by linarith) (by linarith)
    have h_const_le : Real.rpow δ (-ε_F) * Real.rpow δ (-(σ_j k' - σ)) ≤ Real.rpow δ (-(5 * ε_F / 4)) := by
      have h_exp : -ε_F + (-(σ_j k' - σ)) = -(ε_F + (σ_j k' - σ)) := by ring
      have h5 : Real.rpow δ (-ε_F) * Real.rpow δ (-(σ_j k' - σ)) =
          Real.rpow δ (-ε_F + (-(σ_j k' - σ))) :=
        (Real.rpow_add hδ (-ε_F) (-(σ_j k' - σ))).symm
      have h5' : Real.rpow δ (-ε_F) * Real.rpow δ (-(σ_j k' - σ)) =
          Real.rpow δ (-(ε_F + (σ_j k' - σ))) := by
        rw [h5, h_exp]
      rw [h5']
      have h6 : ε_F + (σ_j k' - σ) ≤ 5 * ε_F / 4 := by linarith [hσ_j_minus]
      exact Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
    have hC5 : 0 ≤ Real.rpow δ (-(5 * ε_F / 4)) := Real.rpow_nonneg (by linarith) _
    have h_mono_C : IsDeltaSet δ (σ_j k') (Real.rpow δ (-(5 * ε_F / 4))) hδ (by linarith) hC5 (T x) :=
      IsDeltaSet.mono_C h_mono_s hC5 h_const_le
    have h1 : IsDeltaSSet δ (σ_j k') (Real.rpow δ (-(5 * ε_F / 4)) * Real.rpow 2 (σ_j k')) (T x) :=
      IsDeltaSet.toIsDeltaSSet_same h_mono_C hT_nonempty (Real.rpow_pos_of_pos hδ _)
    have h2 : Real.rpow δ (-(5 * ε_F / 4)) * Real.rpow 2 (σ_j k') ≤ Real.rpow δ (-ε_a) := h_scale_T
    have h3 : IsDeltaSSet δ (σ_j k') (Real.rpow δ (-ε_a)) (T x) :=
      FurstenbergEstimate.IsDeltaSSet.mono_C h1 (Real.rpow_pos_of_pos hδ _) h2
    exact IsDeltaSSet.image_equiv line2EquivAffineLine h3
  have h_tube : ∀ (x : Point) (hx : x ∈ X),
      ∀ (ℓ : AffineLine), ℓ ∈ line2EquivAffineLine '' (T x) →
        x ∈ Metric.cthickening δ ℓ.1 := by
    intro x hx ℓ hℓ
    rcases hℓ with ⟨L, hL, rfl⟩
    have h4 : x ∈ tube δ L := (hT x hx).2.2 L hL
    exact tube_subset_cthickening h4
  let 𝓣 : ∀ (x : Point), x ∈ X → Set AffineLine :=
    fun x hx => line2EquivAffineLine '' (T x)
  have h_lower := hδ₀_k_axiom k' hk'_in δ ⟨hδ, hδ_le_axiom⟩ X hX_ball hX_sset 𝓣 hT_sset h_tube
  let S : Set Line2 := ⋃ x ∈ X, T x
  let S' : Set AffineLine := ⋃ (x : Point) (hx : x ∈ X), 𝓣 x hx
  have h_image : S' = line2EquivAffineLine '' S := by
    ext z
    simp only [S', S, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨x, hx, ℓ, hℓ, rfl⟩; exact ⟨ℓ, ⟨x, hx, hℓ⟩, rfl⟩
    · rintro ⟨ℓ, ⟨x, hx, hℓ⟩, rfl⟩; exact ⟨x, hx, ℓ, hℓ, rfl⟩
  have h_cov_transfer : (Metric.externalCoveringNumber δ.toNNReal S' : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
    rw [h_image]
    exact_mod_cast IsometryEquiv.externalCoveringNumber_image line2EquivAffineLine (S := S)
  have h_main1 : ENNReal.ofReal (Real.rpow δ (-(2 * (σ_j k') + ε_a))) ≤
      (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
    rw [← h_cov_transfer]
    exact h_lower
  have h1 : Metric.externalCoveringNumber δ.toNNReal S ≤ S.encard :=
    Metric.externalCoveringNumber_le_encard_self (A := S)
  have h_encard : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ (S.encard : ENNReal) := by
    exact_mod_cast h1
  have h_fin_encard : S.encard = ↑S.ncard := Set.Finite.encard_eq_coe hfin
  have h4 : ENNReal.ofReal (Real.rpow δ (-(2 * (σ_j k') + ε_a))) ≤ (↑S.ncard : ENNReal) := by
    rw [h_fin_encard] at h_encard
    exact le_trans h_main1 h_encard
  have h5 : Real.rpow δ (-(2 * σ + ε_F)) ≤ Real.rpow δ (-(2 * (σ_j k') + ε_a)) := by
    have h6 : -(2 * (σ_j k') + ε_a) ≤ -(2 * σ + ε_F) := by
      have h7 : σ ≤ σ_j k' := hσ_le_j
      have h8 : ε_F < ε_a := by linarith
      linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) h6
  have h7 : ENNReal.ofReal (Real.rpow δ (-(2 * σ + ε_F))) ≤ (↑S.ncard : ENNReal) :=
    le_trans (ENNReal.ofReal_le_ofReal h5) h4
  have h_pos : 0 ≤ Real.rpow δ (-(2 * σ + ε_F)) := Real.rpow_nonneg (by linarith) _
  have h8 : Real.rpow δ (-(2 * σ + ε_F)) ≤ (S.ncard : ℝ) :=
    FurstenbergEstimate.enreal_ofReal_le_coe_nat h_pos h7
  have h9 : Real.rpow δ (-2 * σ - ε_F) = Real.rpow δ (-(2 * σ + ε_F)) := by ring_nf
  have h10 : (S.ncard : ℝ) = ((⋃ x ∈ X, T x).ncard : ℝ) := by congr <;> rfl
  have h_final : Real.rpow δ (-2 * σ - ε_F) ≤ ((⋃ x ∈ X, T x).ncard : ℝ) := by
    rw [h9, ←h10]; exact h8
  exact Nat.ceil_le.mpr h_final

end RadialBootstrapping

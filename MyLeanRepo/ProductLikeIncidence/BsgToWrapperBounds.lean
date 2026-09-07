module

/-
# BSG Output → Wrapper Bounds Helper

Takes the output of `bsg_corollary` (or equivalent BSG extraction) plus
A1/A2 comparability, and produces the exact `K_BSG : ℝ` and difference
bounds required by `sector_ring_lemma51_wrapper`.

## Usage

Copy this entire file (or just the main lemma) into your module.
Dependencies: `MyLeanRepo.BsgDifferenceBounds`, `MyLeanRepo.ProjectionBasic`,
`MyLeanRepo.ProductLikeBasic`, `MyLeanRepo.SetDiscretizationBridge`, `Mathlib`.

## Main lemma

`bsg_to_wrapper_bounds` — given B1, B2 with sumset/retention/comparability,
returns `K_BSG : ℝ` and:
  h_diff1 : N(B1-B1) ≤ ofReal(K_BSG) * N(B1)
  h_diff2 : N(B2-B1) ≤ ofReal(K_BSG) * N(B1)

Also returns all sector-ready and denominator bounds for downstream use.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.BsgDifferenceBounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence

/-- Nreal of a bounded set is finite. -/
private lemma bsg_helper_nreal_ne_top {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : Bornology.IsBounded A) : Nreal δ A ≠ ⊤ := by
  have hA'_bdd : Bornology.IsBounded (realLineCopy A) :=
    SetDiscretizationBridge.realLineCopy_bounded_iff.mpr hA_bdd
  have h1 : (dyadicCubesMeeting δ (realLineCopy A)).Finite :=
    ProductLikeIncidence.dyadicCubesMeeting_finite hδ hA'_bdd
  have h2 : (dyadicCoveringNumber δ (realLineCopy A)) < ⊤ :=
    Set.encard_lt_top_iff.mpr h1
  have h3 : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by rfl
  rw [h3]; exact_mod_cast (ne_of_lt h2)

/-- Nreal of a bounded nonempty set is positive. -/
private lemma bsg_helper_nreal_pos {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : Bornology.IsBounded A) (hA_nonempty : A.Nonempty) : 0 < Nreal δ A := by
  rcases hA_nonempty with ⟨x, hx⟩
  let g : Fin 1 → ℝ := fun (_ : Fin 1) => x
  let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm g
  have h_p0 : p 0 = x := by simp [p, g]
  have hp : p ∈ realLineCopy A := by
    have h : p 0 ∈ A := by rw [h_p0] <;> exact hx
    simpa [realLineCopy] using h
  have h1 : (realLineCopy A).Nonempty := ⟨p, hp⟩
  have h2 : 0 < dyadicCoveringNumber δ (realLineCopy A) :=
    robust_projection.dyadic_covering_number_pos hδ h1
  have h3 : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by rfl
  rw [h3]; exact_mod_cast h2

/-- Covering number monotone under subset. -/
private lemma bsg_helper_nreal_mono {δ : ℝ} {A B : Set ℝ} (hδ : 0 < δ)
    (hA_bdd : Bornology.IsBounded A) (hB_bdd : Bornology.IsBounded B)
    (h : A ⊆ B) : Nreal δ A ≤ Nreal δ B := by
  have h1 : realLineCopy A ⊆ realLineCopy B := by
    intro x hx; simpa [realLineCopy] using h (by simpa [realLineCopy] using hx)
  have h2 : dyadicCubesMeeting δ (realLineCopy A) ⊆ dyadicCubesMeeting δ (realLineCopy B) := by
    intro Q hQ
    rcases hQ with ⟨hQ1, hQ2⟩
    have h3 : Q ∩ realLineCopy A ⊆ Q ∩ realLineCopy B := Set.inter_subset_inter_right Q h1
    exact ⟨hQ1, Set.Nonempty.mono h3 hQ2⟩
  have h3 : (dyadicCubesMeeting δ (realLineCopy A)).encard ≤
      (dyadicCubesMeeting δ (realLineCopy B)).encard := Set.encard_mono h2
  exact ENat.toENNReal_mono h3

/-- **BSG to wrapper bounds — full sector ledger**.

    From BSG-extracted B1, B2 with sumset bound, retention, and A1/A2
    comparability, produce the complete difference-bound ledger needed for
    all four sectors of the Ring expansion.

    ## Outputs

    **ENNReal constants:**
    - `K_eff = C / c` — effective BSG constant
    - `K_ratio = K_A / c` — B1/B2 comparability ratio
    - `K_sector` — all four bounds normalized by N(B1)
    - `K_sector_B1 = K_sector` — denominator constant for B1-first sectors
    - `K_sector_B2 = K_sector * K_ratio` — denominator constant for B2-first sectors

    **Real constants for `sector_ring_lemma51_wrapper`:**
    - `K_BSG_B1` — for sectors where Ring input = B1 (sectors 1, 3)
    - `K_BSG_B2` — for sectors where Ring input = B2 (sectors 0, 2)

    ## Sector mapping

    | Sector | Ring input | Other coord | K_BSG | Key bounds |
    |--------|-----------|-------------|-------|------------|
    | 0      | B2        | B1          | K_BSG_B2 | h_r4, h_r5 |
    | 1      | B1        | B2          | K_BSG_B1 | h_r1, h_r2 |
    | 2      | -B2       | -B1         | K_BSG_B2 | h_r4, h_r6 |
    | 3      | -B1       | -B2         | K_BSG_B1 | h_r1, h_r3 |

    Negation preserves covering numbers, so bounds on S-S and S+T
    transfer directly to (-S)-(-S) and (-S)+(-T).
-/
lemma bsg_to_wrapper_bounds
    {δ : ℝ} (hδ : 0 < δ)
    {A1 A2 B1 B2 : Set ℝ}
    (hA1_bdd : Bornology.IsBounded A1) (hA2_bdd : Bornology.IsBounded A2)
    (hB1_bdd : Bornology.IsBounded B1) (hB2_bdd : Bornology.IsBounded B2)
    (hB1_nonempty : B1.Nonempty) (hB2_nonempty : B2.Nonempty)
    (hB1_grid : B1 ⊆ productLikeIntegerGrid δ)
    (hB2_grid : B2 ⊆ productLikeIntegerGrid δ)
    (hB1_sub_A1 : B1 ⊆ A1) (hB2_sub_A2 : B2 ⊆ A2)
    {C c K_A : ENNReal}
    (hC_ne_top : C ≠ ⊤) (hc_ne_top : c ≠ ⊤)
    (hc_pos : 0 < c) (hC_pos : 0 < C)
    (hK_A_ne_top : K_A ≠ ⊤)
    (hK_A_ge_one : 1 ≤ K_A)
    (hC_ge_one : 1 ≤ C)
    (hc_le_one : c ≤ 1)
    (h_ret1 : c * Nreal δ A1 ≤ Nreal δ B1)
    (h_ret2 : c * Nreal δ A2 ≤ Nreal δ B2)
    (h_sum : Nreal δ (Set.image2 (· + ·) B1 B2) ≤
        C * ENNReal.ofReal (Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)))
    (hA1_le_A2 : Nreal δ A1 ≤ K_A * Nreal δ A2)
    (hA2_le_A1 : Nreal δ A2 ≤ K_A * Nreal δ A1) :
    ∃ (K_eff K_ratio K_sector K_sector_B1 K_sector_B2 : ENNReal)
      (K_BSG_B1 K_BSG_B2 K_BSG_all : ℝ),
      K_eff = C / c ∧
      K_ratio = K_A / c ∧
      -- Sector-ready bounds (all normalized by N(B1))
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector * Nreal δ B1 ∧
      K_sector ≠ ⊤ ∧ K_sector ≠ 0 ∧
      -- Denominator bounds (B1-normalized, K_B1 = K_sector)
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B1 * Nreal δ B1 ∧
      -- Denominator bounds (B2-normalized, K_B2 = K_sector * K_ratio)
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B2 * Nreal δ B2 ∧
      -- Real conversions for wrapper
      0 < K_BSG_B1 ∧
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_BSG_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG_B1 * Nreal δ B1 ∧
      0 < K_BSG_B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      -- Unified constant valid for both normalizations
      0 < K_BSG_all ∧
      K_BSG_B1 ≤ K_BSG_all ∧
      K_BSG_B2 ≤ K_BSG_all ∧
      ENNReal.ofReal K_BSG_all ≥ K_sector_B1 ∧
      ENNReal.ofReal K_BSG_all ≥ K_sector_B2 ∧
      -- V3 exponent tracking bound
      ENNReal.ofReal K_BSG_all ≤ 81 * K_eff ^ 3 * K_ratio ^ 2 := by
  set K_eff : ENNReal := C / c with hK_eff_def
  set S : ENNReal := ENNReal.ofReal (Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)) with hS

  have hc0 : c ≠ 0 := hc_pos.ne'
  have hC0 : C ≠ 0 := hC_pos.ne'

  have hK_eff_ge_one : 1 ≤ K_eff := by
    rw [hK_eff_def]
    have h1 : C ≤ C / c := by
      calc C
        = C * 1 := by ring
      _ ≤ C * (1 / c) := by gcongr <;> simpa [one_le_div] using hc_le_one
      _ = C / c := by simp [div_eq_mul_inv] <;> ring
    exact le_trans hC_ge_one h1

  have hN_A1_ne_top : Nreal δ A1 ≠ ⊤ := bsg_helper_nreal_ne_top hδ hA1_bdd
  have hN_A2_ne_top : Nreal δ A2 ≠ ⊤ := bsg_helper_nreal_ne_top hδ hA2_bdd

  -- S² = N(A1) * N(A2)
  have hS2 : S ^ 2 = Nreal δ A1 * Nreal δ A2 := by
    have h_nonneg : 0 ≤ (Nreal δ A1).toReal * (Nreal δ A2).toReal := by positivity
    have h_sqrt_nonneg : 0 ≤ Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal) :=
      Real.sqrt_nonneg _
    have h1 : S ^ 2 = ENNReal.ofReal ((Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)) ^ 2) := by
      rw [pow_two]
      have h_mul : S * S = ENNReal.ofReal ((Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)) *
          (Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal))) := by
        rw [hS, ← ENNReal.ofReal_mul h_sqrt_nonneg] <;> rfl
      have h_pow : (Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)) *
          (Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)) =
          (Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)) ^ 2 := by
        rw [pow_two]
      rw [h_pow] at h_mul
      exact h_mul
    rw [h1]
    have h2 : (Real.sqrt ((Nreal δ A1).toReal * (Nreal δ A2).toReal)) ^ 2 =
        (Nreal δ A1).toReal * (Nreal δ A2).toReal := Real.sq_sqrt h_nonneg
    rw [h2]
    have h3 : ENNReal.ofReal ((Nreal δ A1).toReal * (Nreal δ A2).toReal) =
        ENNReal.ofReal (Nreal δ A1).toReal * ENNReal.ofReal (Nreal δ A2).toReal := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ (Nreal δ A1).toReal from by positivity)]
    rw [h3]
    have h4 : ENNReal.ofReal (Nreal δ A1).toReal = Nreal δ A1 :=
      ENNReal.ofReal_toReal hN_A1_ne_top
    have h5 : ENNReal.ofReal (Nreal δ A2).toReal = Nreal δ A2 :=
      ENNReal.ofReal_toReal hN_A2_ne_top
    rw [h4, h5]

  -- h_sum_sq
  have h_sum_sq : Nreal δ (Set.image2 (· + ·) B1 B2) ^ 2 ≤
      K_eff * K_eff * Nreal δ B1 * Nreal δ B2 := by
    have h1 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ C * S := h_sum
    have h2 : Nreal δ (Set.image2 (· + ·) B1 B2) ^ 2 ≤ (C * S) ^ 2 := by gcongr
    have h3 : (C * S) ^ 2 = C * C * S ^ 2 := by simp [pow_two] <;> ring
    have h4 : Nreal δ (Set.image2 (· + ·) B1 B2) ^ 2 ≤ C * C * (Nreal δ A1 * Nreal δ A2) := by
      calc Nreal δ (Set.image2 (· + ·) B1 B2) ^ 2
        ≤ (C * S) ^ 2 := h2
      _ = C * C * S ^ 2 := h3
      _ = C * C * (Nreal δ A1 * Nreal δ A2) := by rw [hS2]
    have h41 : Nreal δ A1 * c ≤ Nreal δ B1 := by
      have h : c * Nreal δ A1 ≤ Nreal δ B1 := h_ret1
      have h' : Nreal δ A1 * c = c * Nreal δ A1 := by ring
      rw [h'] at *; exact h
    have h42 : Nreal δ A2 * c ≤ Nreal δ B2 := by
      have h : c * Nreal δ A2 ≤ Nreal δ B2 := h_ret2
      have h' : Nreal δ A2 * c = c * Nreal δ A2 := by ring
      rw [h'] at *; exact h
    have h51 : Nreal δ A1 ≤ Nreal δ B1 / c :=
      (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hc_ne_top)).mpr h41
    have h52 : Nreal δ A2 ≤ Nreal δ B2 / c :=
      (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hc_ne_top)).mpr h42
    calc Nreal δ (Set.image2 (· + ·) B1 B2) ^ 2
      ≤ C * C * (Nreal δ A1 * Nreal δ A2) := h4
    _ ≤ C * C * ((Nreal δ B1 / c) * (Nreal δ B2 / c)) := by gcongr
    _ = K_eff * K_eff * Nreal δ B1 * Nreal δ B2 := by
      simp [hK_eff_def, div_eq_mul_inv, mul_comm, mul_left_comm] <;> ring

  have hK_eff_ne_top : K_eff ≠ ⊤ := by
    rw [hK_eff_def]; exact ENNReal.div_ne_top hC_ne_top hc0

  let K_ratio : ENNReal := K_A / c
  have hK_ratio_ne_top : K_ratio ≠ ⊤ := ENNReal.div_ne_top hK_A_ne_top hc0
  have hK_ratio_ge_one : 1 ≤ K_ratio := by
    have h1 : 1 ≤ K_A := hK_A_ge_one
    have h2 : c ≤ 1 := hc_le_one
    have h3 : 1 ≤ K_A / c := by
      calc (1 : ENNReal)
        ≤ K_A := h1
      _ ≤ K_A / c := by
        have h4 : K_A ≤ K_A / c := by
          calc K_A
            = K_A * 1 := by ring
          _ ≤ K_A * (1 / c) := by
            gcongr <;> simpa [one_le_div] using h2
          _ = K_A / c := by simp [div_eq_mul_inv] <;> ring
        exact h4
    simpa [K_ratio] using h3

  have hN_B1_le_A1 : Nreal δ B1 ≤ Nreal δ A1 :=
    bsg_helper_nreal_mono hδ hB1_bdd hA1_bdd hB1_sub_A1
  have hN_B2_le_A2 : Nreal δ B2 ≤ Nreal δ A2 :=
    bsg_helper_nreal_mono hδ hB2_bdd hA2_bdd hB2_sub_A2

  have hA2_le_B2div : Nreal δ A2 ≤ Nreal δ B2 / c :=
    (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hc_ne_top)).mpr
      (by have h : c * Nreal δ A2 ≤ Nreal δ B2 := h_ret2
          have h' : Nreal δ A2 * c = c * Nreal δ A2 := by ring
          rw [h'] at *; exact h)
  have hA1_le_B1div : Nreal δ A1 ≤ Nreal δ B1 / c :=
    (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hc_ne_top)).mpr
      (by have h : c * Nreal δ A1 ≤ Nreal δ B1 := h_ret1
          have h' : Nreal δ A1 * c = c * Nreal δ A1 := by ring
          rw [h'] at *; exact h)

  have hB1_le_B2 : Nreal δ B1 ≤ K_ratio * Nreal δ B2 := by
    calc Nreal δ B1
      ≤ Nreal δ A1 := hN_B1_le_A1
    _ ≤ K_A * Nreal δ A2 := hA1_le_A2
    _ ≤ K_A * (Nreal δ B2 / c) := by exact mul_le_mul_of_nonneg_left hA2_le_B2div (by positivity)
    _ = K_ratio * Nreal δ B2 := by
      simp [K_ratio, div_eq_mul_inv, mul_comm, mul_left_comm] <;> ring

  have hB2_le_B1 : Nreal δ B2 ≤ K_ratio * Nreal δ B1 := by
    calc Nreal δ B2
      ≤ Nreal δ A2 := hN_B2_le_A2
    _ ≤ K_A * Nreal δ A1 := hA2_le_A1
    _ ≤ K_A * (Nreal δ B1 / c) := by exact mul_le_mul_of_nonneg_left hA1_le_B1div (by positivity)
    _ = K_ratio * Nreal δ B1 := by
      simp [K_ratio, div_eq_mul_inv, mul_comm, mul_left_comm] <;> ring

  rcases Phase2Bsg.bsg_sector_ready_package hδ hB1_bdd hB2_bdd hB1_nonempty hB2_nonempty
    hB1_grid hB2_grid h_sum_sq hB1_le_B2 hB2_le_B1 hK_ratio_ge_one hK_eff_ge_one
    hK_eff_ne_top hK_ratio_ne_top with ⟨K_sector, h1, h2, h3, h4, hK_sector_def, hK_sector_le, hK_sector_ne_top, hK_sector_ne_zero, _, _, _, _⟩

  have hK_sector_le : K_sector ≤ 81 * K_eff ^ 3 * K_ratio := by
    rw [hK_sector_def]
    have h1 : (9 * K_eff * K_eff * K_ratio) ≤ 81 * K_eff ^ 3 * K_ratio := by
      have h_eff2 : K_eff * K_eff ≤ K_eff ^ 3 := by
        have h_pos : (0 : ENNReal) ≤ K_eff * K_eff := by positivity
        have h : K_eff * K_eff ≤ (K_eff * K_eff) * K_eff := le_mul_of_one_le_right h_pos hK_eff_ge_one
        have h_eq : (K_eff * K_eff) * K_eff = K_eff ^ 3 := by
          simp [pow_succ] <;> rfl
        rw [h_eq] at h
        exact h
      have h9 : (9 : ENNReal) ≤ 81 := by norm_num
      have h_step : (9 : ENNReal) * (K_eff * K_eff) ≤ (81 : ENNReal) * (K_eff ^ 3) :=
        mul_le_mul h9 h_eff2 (by positivity) (by positivity)
      have h : (9 : ENNReal) * (K_eff * K_eff) * K_ratio ≤ (81 : ENNReal) * (K_eff ^ 3) * K_ratio :=
        mul_le_mul_of_nonneg_right h_step (by positivity)
      calc (9 * K_eff * K_eff * K_ratio)
        = (9 : ENNReal) * (K_eff * K_eff) * K_ratio := by ring
      _ ≤ (81 : ENNReal) * (K_eff ^ 3) * K_ratio := h
      _ = 81 * K_eff ^ 3 * K_ratio := by ring
    have h2 : (K_eff * K_ratio) ≤ 81 * K_eff ^ 3 * K_ratio := by
      have h_one : (1 : ENNReal) ≤ K_eff * K_eff := by
        have h_pos : (0 : ENNReal) ≤ (1 : ENNReal) := by positivity
        have h : (1 : ENNReal) ≤ (1 : ENNReal) * K_eff := le_mul_of_one_le_right h_pos hK_eff_ge_one
        simpa using h
      have h81 : (1 : ENNReal) ≤ 81 * (K_eff * K_eff) := by
        calc (1 : ENNReal)
          ≤ K_eff * K_eff := h_one
        _ = (1 : ENNReal) * (K_eff * K_eff) := by ring
        _ ≤ (81 : ENNReal) * (K_eff * K_eff) := by exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      have h_eff : K_eff ≤ 81 * K_eff ^ 3 := by
        calc K_eff
          = K_eff * 1 := by ring
        _ ≤ K_eff * (81 * (K_eff * K_eff)) := by exact mul_le_mul_of_nonneg_left h81 (by positivity)
        _ = 81 * K_eff ^ 3 := by
          have h_eq : K_eff * (81 * (K_eff * K_eff)) = 81 * K_eff ^ 3 := by
            have h1 : K_eff * (81 * (K_eff * K_eff)) = 81 * (K_eff * K_eff * K_eff) := by ring
            rw [h1]
            have h2 : K_eff * K_eff * K_eff = K_eff ^ 3 := by simp [pow_three] <;> ring
            rw [h2] <;> ring
          exact h_eq
      calc K_eff * K_ratio
        ≤ (81 * K_eff ^ 3) * K_ratio := mul_le_mul_of_nonneg_right h_eff (by positivity)
      _ = 81 * K_eff ^ 3 * K_ratio := by ring
    have h3 : max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio) ≤
        81 * K_eff ^ 3 * K_ratio := by
      have h4 : 81 * K_eff * K_eff * K_eff * K_ratio = 81 * K_eff ^ 3 * K_ratio := by
        simp [pow_three] <;> ring
      rw [h4]
      apply max_le <;> [exact le_refl _; exact h2]
    have h5 : max (9 * K_eff * K_eff * K_ratio)
        (max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio)) ≤
          81 * K_eff ^ 3 * K_ratio := by
      apply max_le <;> [exact h1; exact h3]
    exact h5

  -- Denominator constants
  let K_sector_B1 : ENNReal := K_sector
  let K_sector_B2 : ENNReal := K_sector * K_ratio

  -- B1-normalized denominator bounds (K_B1 = K_sector)
  have h_d1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector_B1 * Nreal δ B1 := h1
  have h_d2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B1 * Nreal δ B1 := h3
  have h_d3 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B1 * Nreal δ B1 := h4

  -- B2-normalized denominator bounds (K_B2 = K_sector * K_ratio)
  have h_d4 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector_B2 * Nreal δ B2 := by
    calc Nreal δ (Set.image2 (· - ·) B2 B2)
      ≤ K_sector * Nreal δ B1 := h2
    _ ≤ K_sector * (K_ratio * Nreal δ B2) := by gcongr
    _ = K_sector_B2 * Nreal δ B2 := by
      simp [K_sector_B2] <;> ring
  have h_d5 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B2 * Nreal δ B2 := by
    calc Nreal δ (Set.image2 (· - ·) B2 B1)
      ≤ K_sector * Nreal δ B1 := h3
    _ ≤ K_sector * (K_ratio * Nreal δ B2) := by gcongr
    _ = K_sector_B2 * Nreal δ B2 := by
      simp [K_sector_B2] <;> ring
  have h_d6 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B2 * Nreal δ B2 := by
    calc Nreal δ (Set.image2 (· + ·) B1 B2)
      ≤ K_sector * Nreal δ B1 := h4
    _ ≤ K_sector * (K_ratio * Nreal δ B2) := by gcongr
    _ = K_sector_B2 * Nreal δ B2 := by
      simp [K_sector_B2] <;> ring

  have hK_B2_ne_top : K_sector_B2 ≠ ⊤ :=
    ENNReal.mul_ne_top hK_sector_ne_top hK_ratio_ne_top
  have hK_B2_ne_zero : K_sector_B2 ≠ 0 := by
    have h1 : K_sector ≠ 0 := hK_sector_ne_zero
    have h2 : K_ratio ≠ 0 := by
      have h3 : 0 < K_ratio := lt_of_lt_of_le (by positivity) hK_ratio_ge_one
      exact h3.ne'
    exact mul_ne_zero h1 h2

  -- Real conversions
  let K_BSG_B1 : ℝ := K_sector_B1.toReal
  let K_BSG_B2 : ℝ := K_sector_B2.toReal
  have h_eq_B1 : ENNReal.ofReal K_BSG_B1 = K_sector_B1 := ENNReal.ofReal_toReal hK_sector_ne_top
  have h_eq_B2 : ENNReal.ofReal K_BSG_B2 = K_sector_B2 := ENNReal.ofReal_toReal hK_B2_ne_top
  have hK_BSG_B1_pos : 0 < K_BSG_B1 := ENNReal.toReal_pos hK_sector_ne_zero hK_sector_ne_top
  have hK_BSG_B2_pos : 0 < K_BSG_B2 := ENNReal.toReal_pos hK_B2_ne_zero hK_B2_ne_top

  -- B1-normalized real bounds
  have h_r1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_BSG_B1 * Nreal δ B1 := by
    rw [h_eq_B1]; exact h_d1
  have h_r2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG_B1 * Nreal δ B1 := by
    rw [h_eq_B1]; exact h_d2
  have h_r3 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG_B1 * Nreal δ B1 := by
    rw [h_eq_B1]; exact h_d3

  -- B2-normalized real bounds
  have h_r4 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 := by
    rw [h_eq_B2]; exact h_d4
  have h_r5 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 := by
    rw [h_eq_B2]; exact h_d5
  have h_r6 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 := by
    rw [h_eq_B2]; exact h_d6

  -- Unified real constant valid for both normalizations
  let K_BSG_all : ℝ := max K_BSG_B1 K_BSG_B2
  have hK_BSG_all_pos : 0 < K_BSG_all := by
    apply lt_max_of_lt_left
    exact hK_BSG_B1_pos
  have h_all_ge_B1 : K_BSG_B1 ≤ K_BSG_all := le_max_left _ _
  have h_all_ge_B2 : K_BSG_B2 ≤ K_BSG_all := le_max_right _ _
  have hK_BSG_all_B1 : ENNReal.ofReal K_BSG_all ≥ K_sector_B1 := by
    have h : ENNReal.ofReal K_BSG_B1 ≤ ENNReal.ofReal K_BSG_all := by
      exact ENNReal.ofReal_le_ofReal h_all_ge_B1
    rw [h_eq_B1] at *; exact h
  have hK_BSG_all_B2 : ENNReal.ofReal K_BSG_all ≥ K_sector_B2 := by
    have h : ENNReal.ofReal K_BSG_B2 ≤ ENNReal.ofReal K_BSG_all := by
      exact ENNReal.ofReal_le_ofReal h_all_ge_B2
    rw [h_eq_B2] at *; exact h

  -- V3 bound: K_BSG_all ≤ 81 * K_eff^3 * K_ratio^2
  have hK_sector_B2_eq : K_sector_B2 = K_sector * K_ratio := by rfl
  have hK_sector_B2_le : K_sector_B2 ≤ 81 * K_eff ^ 3 * K_ratio ^ 2 := by
    rw [hK_sector_B2_eq]
    calc K_sector * K_ratio
      ≤ (81 * K_eff ^ 3 * K_ratio) * K_ratio := by gcongr
    _ = 81 * K_eff ^ 3 * K_ratio ^ 2 := by
      simp [pow_two] <;> ring

  have hK_BSG_B1_le_B2 : K_BSG_B1 ≤ K_BSG_B2 := by
    have h1 : K_sector_B1 ≤ K_sector_B2 := by
      have h2 : K_sector_B1 = K_sector := by rfl
      have h3 : K_sector_B2 = K_sector * K_ratio := by rfl
      rw [h2, h3]
      have h4 : K_sector ≤ K_sector * K_ratio := by
        calc K_sector
          = K_sector * 1 := by ring
        _ ≤ K_sector * K_ratio := by gcongr <;> exact hK_ratio_ge_one
      exact h4
    have h5 : K_sector_B1.toReal ≤ K_sector_B2.toReal :=
      (ENNReal.toReal_le_toReal hK_sector_ne_top hK_B2_ne_top).mpr h1
    simpa [K_BSG_B1, K_BSG_B2] using h5

  have hK_BSG_all_eq : K_BSG_all = K_BSG_B2 := by
    have h1 : K_BSG_all = max K_BSG_B1 K_BSG_B2 := by rfl
    rw [h1]
    rw [max_eq_right hK_BSG_B1_le_B2]

  have hK_BSG_all_le : ENNReal.ofReal K_BSG_all ≤ 81 * K_eff ^ 3 * K_ratio ^ 2 := by
    rw [hK_BSG_all_eq]
    have h_eq : ENNReal.ofReal K_BSG_B2 = K_sector_B2 := h_eq_B2
    rw [h_eq]
    exact hK_sector_B2_le

  exact ⟨K_eff, K_ratio, K_sector, K_sector_B1, K_sector_B2, K_BSG_B1, K_BSG_B2, K_BSG_all,
    rfl, rfl, h1, h2, h3, h4, hK_sector_ne_top, hK_sector_ne_zero,
    h_d1, h_d2, h_d3, h_d4, h_d5, h_d6,
    hK_BSG_B1_pos, h_r1, h_r2, h_r3,
    hK_BSG_B2_pos, h_r4, h_r5, h_r6,
    hK_BSG_all_pos, h_all_ge_B1, h_all_ge_B2, hK_BSG_all_B1, hK_BSG_all_B2, hK_BSG_all_le⟩

/--
Derive two-sided comparability `N(A1) ~ N(A2)` from matching upper and lower
bounds.  If both `N(A1)` and `N(A2)` lie in `[L, U]` with `L > 0`, then
`K_A := U / L` satisfies `N(A1) ≤ K_A * N(A2)` and `N(A2) ≤ K_A * N(A1)`.

This is used to obtain the `K_A` hypothesis of `bsg_to_wrapper_bounds` from
projection upper bounds and mass-capture lower bounds.
-/
lemma comparability_from_bounds
    {δ : ℝ} {A1 A2 : Set ℝ} {U L : ENNReal}
    (hU1 : Nreal δ A1 ≤ U) (hL1 : L ≤ Nreal δ A1)
    (hU2 : Nreal δ A2 ≤ U) (hL2 : L ≤ Nreal δ A2)
    (hL_ne_zero : L ≠ 0) (hL_ne_top : L ≠ ⊤)
    (hU_ne_top : U ≠ ⊤) :
    ∃ (K_A : ENNReal),
      (1 ≤ K_A) ∧ (K_A ≠ ⊤) ∧
      (Nreal δ A1 ≤ K_A * Nreal δ A2) ∧
      (Nreal δ A2 ≤ K_A * Nreal δ A1) := by
  let K_A : ENNReal := U / L
  have hK_A_ne_top : K_A ≠ ⊤ := ENNReal.div_ne_top hU_ne_top hL_ne_zero
  have hK_A_ge_one : 1 ≤ K_A := by
    have h1 : L ≤ U := le_trans hL1 hU1
    have hL_inv_mul_L : L * L⁻¹ = 1 := by
      rw [mul_comm]
      exact ENNReal.inv_mul_cancel hL_ne_zero hL_ne_top
    have h2 : L * L⁻¹ ≤ U * L⁻¹ := by gcongr
    have h3 : U * L⁻¹ = U / L := by
      simp [div_eq_mul_inv] <;> ring
    rw [hL_inv_mul_L] at h2
    rw [h3] at *
    exact h2
  have hUL : U / L * L = U := ENNReal.div_mul_cancel hL_ne_zero hL_ne_top
  have h1 : Nreal δ A1 ≤ K_A * Nreal δ A2 := by
    calc Nreal δ A1
      ≤ U := hU1
    _ = U / L * L := hUL.symm
    _ ≤ U / L * Nreal δ A2 := by gcongr
    _ = K_A * Nreal δ A2 := by rfl
  have h2 : Nreal δ A2 ≤ K_A * Nreal δ A1 := by
    calc Nreal δ A2
      ≤ U := hU2
    _ = U / L * L := hUL.symm
    _ ≤ U / L * Nreal δ A1 := by gcongr
    _ = K_A * Nreal δ A1 := by rfl
  exact ⟨K_A, hK_A_ge_one, hK_A_ne_top, h1, h2⟩

end ProductLikeIncidence

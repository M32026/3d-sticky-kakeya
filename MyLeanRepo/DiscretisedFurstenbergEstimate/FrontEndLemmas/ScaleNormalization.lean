module

/-
  Front-end extraction foundational lemmas.

  ## Lemma 1: Scale normalization (NEW)
  `IsDeltaSSet.coarsen_scale`: If `IsDeltaSSet δ s C P` and `δ ≤ δ' ≤ 2δ`,
  then `IsDeltaSSet δ' s (9*C) P`.

  Generalizes `IsDeltaSSet.coarsen_double_plane` (which handles the exact
  case δ' = 2δ) to arbitrary intermediate scales.

  Proof: uses the plane doubling property
  `Ncover(δ, P) ≤ 9 * Ncover(2δ, P) ≤ 9 * Ncover(δ', P)`.

  ## Lemma 2: Even dyadic scale selection
  `exists_even_dyadic_scale`: For `0 < δ ≤ 1`, find even `n` with
  `dyadicDelta n / 2 < δ ≤ 2 * dyadicDelta n`.

  ## Lemma 3: Square-root regularity transfer
  `sqrt_regularity_transfer`: Transfer `Ncover(√δ, P) ≤ δ^{-(u/2+εA)}`
  to `Ncover(√δ_n, P) ≤ C · δ_n^{-(u/2+εA)}` when `δ_n/2 < δ ≤ 2δ_n`.

  Whiteprint node: front_end_lemmas / scale_normalization
  Dependencies: robust_kaufman_projection (doubling property)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.robust_kaufman_projection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate

/-- Generalized scale normalization: coarsen from δ to δ' where δ ≤ δ' ≤ 2δ.
    A `(δ, s, C)`-set is a `(δ', s, 9*C)`-set.

    Uses the plane doubling property:
    `Ncover(δ, P) ≤ 9 * Ncover(2δ, P) ≤ 9 * Ncover(δ', P)`. -/
lemma IsDeltaSSet.coarsen_scale
    {δ δ' s C : ℝ} {P : Set EuclideanPlane}
    (hP : IsDeltaSSet δ s C P)
    (hδ_pos : 0 < δ) (hδ'_pos : 0 < δ')
    (h_le : δ ≤ δ') (h_double : δ' ≤ 2 * δ) :
    IsDeltaSSet δ' s (9 * C) P := by
  rcases hP with ⟨hP_nonempty, _, hC_pos, hs_nonneg, h_main⟩
  have h9C_pos : 0 < 9 * C := by positivity
  refine' ⟨hP_nonempty, hδ'_pos, h9C_pos, hs_nonneg, _⟩
  intro x r hr
  have hδ_le_r : δ ≤ r := by linarith
  have h_anti1 : (Metric.externalCoveringNumber δ'.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := by
    have h : δ.toNNReal ≤ δ'.toNNReal := by exact Real.toNNReal_mono h_le
    exact_mod_cast Metric.externalCoveringNumber_anti h
  have h2 := h_main x r hδ_le_r
  have h_half : (2 * δ).toNNReal / 2 = δ.toNNReal := by
    apply NNReal.coe_injective
    simp [NNReal.coe_div, show 0 ≤ δ by linarith, show 0 ≤ 2 * δ by linarith] <;> ring
  have h3 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (9 : ENNReal) * (Metric.externalCoveringNumber (2 * δ).toNNReal P : ENNReal) := by
    have h4 : Metric.externalCoveringNumber ((2 * δ).toNNReal / 2) P ≤
        9 * Metric.externalCoveringNumber (2 * δ).toNNReal P :=
      externalCoveringNumber_half_le_plane P (2 * δ).toNNReal
    rw [h_half] at h4
    exact_mod_cast h4
  have h_anti2 : (Metric.externalCoveringNumber (2 * δ).toNNReal P : ENNReal) ≤
      (Metric.externalCoveringNumber δ'.toNNReal P : ENNReal) := by
    have h : δ'.toNNReal ≤ (2 * δ).toNNReal := by exact Real.toNNReal_mono h_double
    exact_mod_cast Metric.externalCoveringNumber_anti h
  calc
    (Metric.externalCoveringNumber δ'.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := h_anti1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((9 : ENNReal) * (Metric.externalCoveringNumber (2 * δ).toNNReal P : ENNReal)) := by gcongr
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((9 : ENNReal) * (Metric.externalCoveringNumber δ'.toNNReal P : ENNReal)) := by gcongr
    _ = ENNReal.ofReal (9 * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ'.toNNReal P : ENNReal) := by
      have h5 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            ((9 : ENNReal) * (Metric.externalCoveringNumber δ'.toNNReal P : ENNReal)) =
          (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ'.toNNReal P : ENNReal) := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
      rw [h5]
      have h6 : (9 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal (9 * C) := by
        have h7 : 0 ≤ C := by linarith
        have h8 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast
        rw [h8]
        have h9 : ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((9 : ℝ) * C) := by
          rw [← ENNReal.ofReal_mul (by norm_num)] <;> ring
        rw [h9] <;> norm_num
      rw [h6] <;> ring

/-! ### Even dyadic scale selection -/

/-- Recurrence: `dyadicDelta (m + 2) = dyadicDelta m / 4`. -/
lemma dyadicDelta_add_two (m : ℕ) :
    dyadicDelta (m + 2) = dyadicDelta m / 4 := by
  simp [dyadicDelta, pow_add] <;> field_simp <;> ring

/-- Choose an even natural number `n` such that
    `dyadicDelta n / 2 < δ ≤ 2 * dyadicDelta n`.

    For `0 < δ ≤ 1`, such an even `n` always exists.
    Pick the least `k` with `dyadicDelta (2k) / 2 < δ`; minimality gives
    `δ ≤ dyadicDelta (2(k-1)) / 2 = 2 * dyadicDelta (2k)`. -/
lemma exists_even_dyadic_scale (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ (n : ℕ), n % 2 = 0 ∧ dyadicDelta n / 2 < δ ∧ δ ≤ 2 * dyadicDelta n := by
  let Q : ℕ → Prop := fun k => dyadicDelta (2 * k) / 2 < δ
  have h_exists : ∃ k : ℕ, Q k := by
    have h1 : ∃ k : ℕ, (4 : ℝ)^k > 1 / (2 * δ) := by
      obtain ⟨m, hm⟩ := exists_nat_gt (1 / (2 * δ))
      have h2 : ∀ n : ℕ, (n : ℝ) ≤ (4 : ℝ)^n := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          calc (n.succ : ℝ)
            = (n : ℝ) + 1 := by simp
          _ ≤ (4 : ℝ)^n + 1 := by linarith [ih]
          _ ≤ (4 : ℝ)^n + (4 : ℝ)^n := by
            have h3 : (1 : ℝ) ≤ (4 : ℝ)^n := by
              have h4 : ∀ k : ℕ, (1 : ℝ) ≤ (4 : ℝ)^k := by
                intro k; induction k with
                | zero => norm_num
                | succ k ih => simp [pow_succ, ih] <;> norm_num <;> linarith
              exact h4 n
            linarith
          _ ≤ (4 : ℝ)^(n + 1) := by simp [pow_succ] <;> ring_nf <;> norm_num
      exact ⟨m, by linarith [h2 m]⟩
    rcases h1 with ⟨k, hk⟩
    have h4 : dyadicDelta (2 * k) = 1 / (4 : ℝ)^k := by
      simp [dyadicDelta, pow_mul] <;> ring
    have h5 : 1 / (2 * (4 : ℝ)^k) < δ := by
      have h6 : 0 < 2 * δ := by positivity
      have h7 : (4 : ℝ)^k > 1 / (2 * δ) := hk
      have h8 : 0 < (4 : ℝ)^k := by positivity
      calc 1 / (2 * (4 : ℝ)^k)
        < 1 / (2 * (1 / (2 * δ))) := by gcongr
      _ = δ := by field_simp [h6.ne'] <;> ring
    have h9 : dyadicDelta (2 * k) / 2 < δ := by
      rw [h4]
      have h10 : (1 / (4 : ℝ)^k) / 2 = 1 / (2 * (4 : ℝ)^k) := by field_simp <;> ring
      rw [h10]
      exact h5
    exact ⟨k, h9⟩
  let k := Nat.find h_exists
  have hQk : Q k := Nat.find_spec h_exists
  set n : ℕ := 2 * k with hn_def
  have h_even : n % 2 = 0 := by
    simp [hn_def, Nat.mul_mod]
  have h_lower : dyadicDelta n / 2 < δ := by
    simpa [hn_def] using hQk
  have h_upper : δ ≤ 2 * dyadicDelta n := by
    by_cases hk : k = 0
    · have h_n0 : n = 0 := by simp [hn_def, hk]
      rw [h_n0]
      simp [dyadicDelta] <;> linarith
    · have h_k_pos : 0 < k := by omega
      have hQ_prev : ¬ Q (k - 1) := Nat.find_min h_exists (by omega)
      have h10 : δ ≤ dyadicDelta (2 * (k - 1)) / 2 := by
        have h11 : ¬(dyadicDelta (2 * (k - 1)) / 2 < δ) := by simpa [Q] using hQ_prev
        linarith
      have h12 : 2 * (k - 1) + 2 = n := by omega
      have h13 : dyadicDelta (2 * (k - 1)) = 4 * dyadicDelta n := by
        have h14 := dyadicDelta_add_two (2 * (k - 1))
        rw [h12] at h14
        linarith
      rw [h13] at h10
      linarith
  exact ⟨n, h_even, h_lower, h_upper⟩

/-- Choose an even natural number `n` such that
    `δ ≤ dyadicDelta n ≤ 4 * δ`.

    For `0 < δ ≤ 1`, such an even `n` always exists.
    Uses `exists_even_dyadic_scale`; if the resulting scale is below δ,
    moves up by two dyadic levels (factor 4). -/
lemma exists_even_dyadic_scale_above (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ (n : ℕ), n % 2 = 0 ∧ δ ≤ dyadicDelta n ∧ dyadicDelta n ≤ 4 * δ := by
  rcases exists_even_dyadic_scale δ hδ_pos hδ_le_one with
    ⟨n, hn_even, hδ_n_half_lt, hδ_le_2δ_n⟩
  let δ_n := dyadicDelta n
  by_cases h : δ ≤ δ_n
  · -- δ_n is already at or above δ
    have h4 : δ_n ≤ 4 * δ := by
      have h5 : δ_n ≤ 2 * δ := by linarith
      linarith
    exact ⟨n, hn_even, h, h4⟩
  · -- δ_n < δ: move up by two dyadic levels (n ↦ n - 2)
    have hδ_n_lt_delta : δ_n < δ := by linarith
    have h_n_pos : 0 < n := by
      by_contra h6
      have h7 : n = 0 := by omega
      have h8 : dyadicDelta n = 1 := by
        rw [h7]
        simp [dyadicDelta] <;> norm_num
      have h9 : δ_n = 1 := by simpa [δ_n] using h8
      have h10 : (1 : ℝ) < δ := h9 ▸ hδ_n_lt_delta
      linarith
    let n' := n - 2
    have hn'_even : n' % 2 = 0 := by omega
    have hδ_n'_eq : dyadicDelta n' = 4 * δ_n := by
      have h9 : n' + 2 = n := by omega
      have h10 := dyadicDelta_add_two n'
      rw [h9] at h10
      linarith
    have h11 : δ ≤ dyadicDelta n' := by
      rw [hδ_n'_eq]
      linarith
    have h12 : dyadicDelta n' ≤ 4 * δ := by
      rw [hδ_n'_eq]
      linarith
    exact ⟨n', hn'_even, h11, h12⟩

/-! ### Real.rpow helper lemmas -/

private lemma rpow_div_pos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.rpow (x / y) z = Real.rpow x z / Real.rpow y z := by
  have h_posx : 0 ≤ x := by linarith
  have h_posy : 0 ≤ y := by linarith
  have h_posy_inv : 0 ≤ y⁻¹ := by positivity
  have h_inv_rpow : Real.rpow y⁻¹ z = (Real.rpow y z)⁻¹ := by
    have h1 : y⁻¹ = Real.rpow y (-1 : ℝ) := by
      have h11 : Real.rpow y (-1 : ℝ) = (Real.rpow y (1 : ℝ))⁻¹ := Real.rpow_neg h_posy (1 : ℝ)
      have h12 : Real.rpow y (1 : ℝ) = y := by simp
      rw [h12] at h11
      exact h11.symm
    rw [h1]
    have h2 : Real.rpow (Real.rpow y (-1 : ℝ)) z = Real.rpow y ((-1 : ℝ) * z) :=
      (Real.rpow_mul h_posy (-1 : ℝ) z).symm
    rw [h2]
    have h3 : (-1 : ℝ) * z = -z := by ring
    rw [h3]
    have h_rpow_neg : Real.rpow y (-z) = (Real.rpow y z)⁻¹ := Real.rpow_neg h_posy z
    rw [h_rpow_neg] <;> field_simp
  have h4 : x / y = x * y⁻¹ := by ring
  rw [h4]
  have h5 : Real.rpow (x * y⁻¹) z = Real.rpow x z * Real.rpow y⁻¹ z :=
    Real.mul_rpow h_posx h_posy_inv
  rw [h5, h_inv_rpow] <;> field_simp

private lemma rpow_rpow_pos {x y z : ℝ} (hx : 0 < x) :
    Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) := by
  have h_pos : 0 ≤ x := by linarith
  exact (Real.rpow_mul h_pos y z).symm

/-- Transfer square-root regularity UPWARD from δ to δ_n where δ ≤ δ_n ≤ 4δ.

    Since √δ ≤ √δ_n, anti-monotonicity gives Ncover(√δ_n) ≤ Ncover(√δ).
    The exponent conversion loses a factor 4^{u/2+εA}. -/
lemma sqrt_regularity_transfer_above
    {δ δ_n u εA : ℝ} {P : Set EuclideanPlane}
    (hδ_pos : 0 < δ) (hδ_n_pos : 0 < δ_n)
    (hδ_le_Delta_n : δ ≤ δ_n) (hDelta_n_le_4δ : δ_n ≤ 4 * δ)
    (hu_nonneg : 0 ≤ u) (hεA_pos : 0 < εA)
    (hcover : Ncover (Real.sqrt δ) P ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA)))) :
    Ncover (Real.sqrt δ_n) P ≤
      ENNReal.ofReal (Real.rpow 4 (u / 2 + εA) * Real.rpow δ_n (-(u / 2 + εA))) := by
  set e : ℝ := u / 2 + εA with he_def
  have he_pos : 0 < e := by linarith
  -- Anti-monotonicity: √δ ≤ √δ_n implies Ncover(√δ_n) ≤ Ncover(√δ)
  have h_sqrt_le : Real.sqrt δ ≤ Real.sqrt δ_n := Real.sqrt_le_sqrt hδ_le_Delta_n
  have h_toNNReal_le : (Real.sqrt δ).toNNReal ≤ (Real.sqrt δ_n).toNNReal := by
    have h_nonneg1 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
    have h_nonneg2 : 0 ≤ Real.sqrt δ_n := Real.sqrt_nonneg δ_n
    have h_coe1 : ((Real.sqrt δ).toNNReal : ℝ) = Real.sqrt δ :=
      Real.coe_toNNReal _ (Real.sqrt_nonneg δ)
    have h_coe2 : ((Real.sqrt δ_n).toNNReal : ℝ) = Real.sqrt δ_n :=
      Real.coe_toNNReal _ (Real.sqrt_nonneg δ_n)
    exact NNReal.coe_le_coe.mp (by rw [h_coe1, h_coe2]; exact h_sqrt_le)
  have h1 : Ncover (Real.sqrt δ_n) P ≤ Ncover (Real.sqrt δ) P := by
    simpa [Ncover] using Metric.externalCoveringNumber_anti h_toNNReal_le (A := P)
  -- Exponent conversion: δ^{-e} ≤ 4^e * δ_n^{-e}
  have h51_pos : 0 < δ_n / 4 := by linarith
  have h52 : δ_n / 4 ≤ δ := by linarith
  have h53 : Real.rpow (δ_n / 4) e ≤ Real.rpow δ e :=
    Real.rpow_le_rpow (by linarith) h52 (by linarith)
  have h54 : 0 < Real.rpow (δ_n / 4) e := Real.rpow_pos_of_pos h51_pos e
  have h55 : 0 < Real.rpow δ e := Real.rpow_pos_of_pos hδ_pos e
  have h56 : 1 / Real.rpow δ e ≤ 1 / Real.rpow (δ_n / 4) e :=
    one_div_le_one_div_of_le h54 h53
  have h57 : Real.rpow δ (-e) = 1 / Real.rpow δ e := by
    have h571 : Real.rpow δ (-e) = (Real.rpow δ e)⁻¹ := Real.rpow_neg hδ_pos.le e
    rw [h571]
    <;> field_simp
  have h58 : Real.rpow (δ_n / 4) (-e) = 1 / Real.rpow (δ_n / 4) e := by
    have h581 : Real.rpow (δ_n / 4) (-e) = (Real.rpow (δ_n / 4) e)⁻¹ := Real.rpow_neg h51_pos.le e
    rw [h581] <;> field_simp
  have h59 : Real.rpow δ (-e) ≤ Real.rpow (δ_n / 4) (-e) := by
    rw [h57, h58]
    exact h56
  have h60 : Real.rpow (δ_n / 4) (-e) = Real.rpow 4 e * Real.rpow δ_n (-e) := by
    have h61 : (δ_n / 4 : ℝ) = δ_n * (4 : ℝ)⁻¹ := by ring
    rw [h61]
    have h62 : Real.rpow (δ_n * (4 : ℝ)⁻¹) (-e) =
        Real.rpow δ_n (-e) * Real.rpow ((4 : ℝ)⁻¹) (-e) :=
      Real.mul_rpow (by linarith) (by positivity)
    rw [h62]
    have h63 : Real.rpow ((4 : ℝ)⁻¹) (-e) = Real.rpow (4 : ℝ) e := by
      have h631 : (4 : ℝ)⁻¹ = Real.rpow 4 (-1 : ℝ) := by
        have h_pos4 : (0 : ℝ) ≤ 4 := by norm_num
        have h : Real.rpow 4 (-1 : ℝ) = (Real.rpow 4 (1 : ℝ))⁻¹ := Real.rpow_neg h_pos4 (1 : ℝ)
        have h2 : Real.rpow 4 (1 : ℝ) = (4 : ℝ) := Real.rpow_one 4
        have h3 : Real.rpow 4 (-1 : ℝ) = (4 : ℝ)⁻¹ := by
          rw [h, h2] <;> simp
        exact h3.symm
      rw [h631]
      have h632 : Real.rpow (Real.rpow 4 (-1 : ℝ)) (-e) = Real.rpow 4 ((-1 : ℝ) * (-e)) :=
        (Real.rpow_mul (by norm_num) (-1 : ℝ) (-e)).symm
      rw [h632] <;> ring_nf
    rw [h63] <;> ring
  have h4 : Real.rpow δ (-e) ≤ Real.rpow 4 e * Real.rpow δ_n (-e) := by
    calc Real.rpow δ (-e)
      ≤ Real.rpow (δ_n / 4) (-e) := h59
    _ = Real.rpow 4 e * Real.rpow δ_n (-e) := h60
  calc Ncover (Real.sqrt δ_n) P
    ≤ Ncover (Real.sqrt δ) P := h1
  _ ≤ ENNReal.ofReal (Real.rpow δ (-e)) := hcover
  _ ≤ ENNReal.ofReal (Real.rpow 4 e * Real.rpow δ_n (-e)) := ENNReal.ofReal_le_ofReal h4
  _ = ENNReal.ofReal (Real.rpow 4 (u / 2 + εA) * Real.rpow δ_n (-(u / 2 + εA))) := by
    congr 1 <;> simp [he_def] <;> ring

/-- Transfer square-root regularity from non-dyadic scale `√δ` to dyadic
    coarse scale `Δ = √δ_n`.

    Given `Ncover(√δ, P) ≤ δ^{-(u/2+εA)}` and `δ_n/2 < δ ≤ 2δ_n`,
    produces `Ncover(√δ_n, P) ≤ C · δ_n^{-(u/2+εA)}`
    with `C = 9 * 2^{u/2+εA}`.

    Uses plane doubling: since `√δ ≤ √2·Δ < 2Δ`,
    `Ncover(Δ) ≤ 9·Ncover(2Δ) ≤ 9·Ncover(√δ)`. -/
lemma sqrt_regularity_transfer
    {δ δ_n u εA : ℝ} {P : Set EuclideanPlane}
    (hδ_pos : 0 < δ) (hδ_n_pos : 0 < δ_n)
    (hδ_n_half_lt_delta : δ_n / 2 < δ)
    (hδ_le_2δ_n : δ ≤ 2 * δ_n)
    (hu_nonneg : 0 ≤ u) (hεA_pos : 0 < εA)
    (hcover : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P : ENNReal) ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA)))) :
    (Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal P : ENNReal) ≤
      ENNReal.ofReal (9 * Real.rpow 2 (u / 2 + εA) * Real.rpow δ_n (-(u / 2 + εA))) := by
  set Δ : ℝ := Real.sqrt δ_n with hΔ_def
  have hΔ_pos : 0 < Δ := Real.sqrt_pos.mpr hδ_n_pos
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have h_sqrt_le : Real.sqrt δ ≤ Real.sqrt 2 * Δ := by
    have h1 : δ ≤ 2 * δ_n := hδ_le_2δ_n
    have h2 : Real.sqrt δ ≤ Real.sqrt (2 * δ_n) := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (2 * δ_n) = Real.sqrt 2 * Δ := by
      rw [Real.sqrt_mul (by norm_num)] <;> ring
    rw [h3] at h2
    exact h2
  have h_sqrt_lt_2Δ : Real.sqrt δ < 2 * Δ := by
    have h4 : Real.sqrt 2 < (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [h_sqrt_le, hΔ_pos]
  have h_half : (2 * Δ).toNNReal / 2 = Δ.toNNReal := by
    apply NNReal.coe_injective
    simp [NNReal.coe_div, show 0 ≤ Δ by linarith, show 0 ≤ 2 * Δ by linarith] <;> ring
  have h_double : (Metric.externalCoveringNumber Δ.toNNReal P : ENNReal) ≤
      (9 : ENNReal) * (Metric.externalCoveringNumber (2 * Δ).toNNReal P : ENNReal) := by
    have h13 := externalCoveringNumber_half_le_plane P (2 * Δ).toNNReal
    rw [h_half] at h13
    exact_mod_cast h13
  have h14 : (Metric.externalCoveringNumber (2 * Δ).toNNReal P : ENNReal) ≤
      (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P : ENNReal) := by
    have h15 : (Real.sqrt δ).toNNReal ≤ (2 * Δ).toNNReal := by
      apply NNReal.coe_le_coe.mp
      have h16 : ((Real.sqrt δ).toNNReal : ℝ) = Real.sqrt δ :=
        Real.coe_toNNReal _ (Real.sqrt_nonneg δ)
      have h17 : ((2 * Δ).toNNReal : ℝ) = 2 * Δ :=
        Real.coe_toNNReal _ (by linarith)
      rw [h16, h17]
      exact h_sqrt_lt_2Δ.le
    exact_mod_cast Metric.externalCoveringNumber_anti h15
  have h_exp_nonneg : 0 ≤ u / 2 + εA := by linarith
  have h16 : Real.rpow δ (-(u / 2 + εA)) ≤
      Real.rpow 2 (u / 2 + εA) * Real.rpow δ_n (-(u / 2 + εA)) := by
    have h17 : δ_n / 2 < δ := hδ_n_half_lt_delta
    have h_e_pos : 0 < u / 2 + εA := by linarith
    have h181 : 0 < δ_n / 2 := by linarith
    have h182 : Real.rpow (δ_n / 2) (u / 2 + εA) ≤ Real.rpow δ (u / 2 + εA) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have h183 : 0 < Real.rpow (δ_n / 2) (u / 2 + εA) := Real.rpow_pos_of_pos h181 _
    have h184 : 0 < Real.rpow δ (u / 2 + εA) := Real.rpow_pos_of_pos hδ_pos _
    have h18 : Real.rpow δ (-(u / 2 + εA)) ≤
        Real.rpow (δ_n / 2) (-(u / 2 + εA)) := by
      have h185 : Real.rpow δ (-(u / 2 + εA)) = (Real.rpow δ (u / 2 + εA))⁻¹ :=
        Real.rpow_neg hδ_pos.le (u / 2 + εA)
      have h186 : Real.rpow (δ_n / 2) (-(u / 2 + εA)) = (Real.rpow (δ_n / 2) (u / 2 + εA))⁻¹ :=
        Real.rpow_neg h181.le (u / 2 + εA)
      rw [h185, h186]
      gcongr
    have h19 : Real.rpow (δ_n / 2) (-(u / 2 + εA)) =
        Real.rpow 2 (u / 2 + εA) * Real.rpow δ_n (-(u / 2 + εA)) := by
      rw [rpow_div_pos hδ_n_pos h_two_pos]
      have h20 : Real.rpow 2 (-(u / 2 + εA)) = (Real.rpow 2 (u / 2 + εA))⁻¹ :=
        Real.rpow_neg (by norm_num) (u / 2 + εA)
      rw [h20]
      <;> field_simp [Real.rpow_pos_of_pos h_two_pos (u / 2 + εA)] <;> ring
    rw [h19] at h18
    exact h18
  have h21 : (9 : ENNReal) * ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA))) ≤
      ENNReal.ofReal (9 * Real.rpow 2 (u / 2 + εA) * Real.rpow δ_n (-(u / 2 + εA))) := by
    have h22 : (9 : ENNReal) * ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA))) =
        ENNReal.ofReal (9 * Real.rpow δ (-(u / 2 + εA))) := by
      have h221 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast
      rw [h221]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      <;> norm_cast
    rw [h22]
    apply ENNReal.ofReal_le_ofReal
    have h23 : 0 ≤ 9 := by norm_num
    nlinarith
  calc (Metric.externalCoveringNumber Δ.toNNReal P : ENNReal)
    ≤ (9 : ENNReal) * (Metric.externalCoveringNumber (2 * Δ).toNNReal P : ENNReal) := h_double
  _ ≤ (9 : ENNReal) * (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P : ENNReal) :=
    mul_le_mul_left' h14 (9 : ENNReal)
  _ ≤ (9 : ENNReal) * ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA))) :=
    mul_le_mul_left' hcover (9 : ENNReal)
  _ ≤ ENNReal.ofReal (9 * Real.rpow 2 (u / 2 + εA) * Real.rpow δ_n (-(u / 2 + εA))) := h21

/-- Absorb the transfer constant into a worse exponent.

    Given `sqrt_regularity_transfer`, for any `εA' > εA` and `δ_n` small enough,
    `Ncover(√δ_n, P) ≤ δ_n^{-(u/2+εA')}`.

    Note: the exponent gets WORSE (`εA' > εA`), not better. This is the only
    direction possible when absorbing a constant `C > 1` for `δ_n < 1`. -/
lemma sqrt_regularity_transfer_absorbed
    {δ δ_n u εA εA' : ℝ} {P : Set EuclideanPlane}
    (hδ_pos : 0 < δ) (hδ_n_pos : 0 < δ_n)
    (hδ_n_half_lt_delta : δ_n / 2 < δ)
    (hδ_le_2δ_n : δ ≤ 2 * δ_n)
    (hu_nonneg : 0 ≤ u) (hεA_pos : 0 < εA)
    (hεA'_pos : 0 < εA') (hεA_lt : εA < εA')
    (hcover : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P : ENNReal) ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA))))
    (h_small : δ_n ≤ (9 * Real.rpow 2 (u / 2 + εA)) ^ (-(1 / (εA' - εA)))) :
    (Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal P : ENNReal) ≤
      ENNReal.ofReal (Real.rpow δ_n (-(u / 2 + εA'))) := by
  set C : ℝ := 9 * Real.rpow 2 (u / 2 + εA) with hC_def
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have hC_pos : 0 < C := by
    have h1 : 0 < Real.rpow 2 (u / 2 + εA) := Real.rpow_pos_of_pos h_two_pos (u / 2 + εA)
    positivity
  set d : ℝ := εA' - εA with hd_def
  have hd_pos : 0 < d := by linarith
  have h1 := sqrt_regularity_transfer hδ_pos hδ_n_pos hδ_n_half_lt_delta hδ_le_2δ_n hu_nonneg hεA_pos hcover
  -- Prove C ≤ δ_n^{-d} from δ_n ≤ C^{-1/d}
  have h4 : C ≤ Real.rpow δ_n (-d) := by
    have hC_neg_inv_d_pos : 0 < Real.rpow C (-(1 / d)) := Real.rpow_pos_of_pos hC_pos (-(1 / d))
    have h_small' : δ_n ≤ Real.rpow C (-(1 / d)) := by
      simpa [hC_def] using h_small
    have h52 : Real.rpow δ_n d ≤ Real.rpow (Real.rpow C (-(1 / d))) d :=
      Real.rpow_le_rpow hδ_n_pos.le h_small' hd_pos.le
    have h53 : Real.rpow (Real.rpow C (-(1 / d))) d = 1 / C := by
      rw [rpow_rpow_pos hC_pos]
      have h54 : (-(1 / d)) * d = -1 := by
        field_simp [hd_pos.ne'] <;> ring
      rw [h54]
      have h55 : Real.rpow C (-1) = 1 / C := by
        have h551 : Real.rpow C (-1) = (Real.rpow C 1)⁻¹ := Real.rpow_neg hC_pos.le 1
        have h552 : Real.rpow C 1 = C := by simp
        rw [h551, h552]
        <;> field_simp [hC_pos.ne'] <;> ring
      exact h55
    rw [h53] at h52
    have h55 : Real.rpow δ_n d ≤ 1 / C := h52
    have h56 : 0 < Real.rpow δ_n d := Real.rpow_pos_of_pos hδ_n_pos d
    have h57 : C ≤ 1 / Real.rpow δ_n d := by
      calc C
        ≤ 1 / (1 / C) := by field_simp [hC_pos.ne'] <;> linarith
      _ ≤ 1 / Real.rpow δ_n d := by gcongr
    have h58 : 1 / Real.rpow δ_n d = Real.rpow δ_n (-d) := by
      have h59 : Real.rpow δ_n (-d) = (Real.rpow δ_n d)⁻¹ := Real.rpow_neg hδ_n_pos.le d
      have h60 : (Real.rpow δ_n d)⁻¹ = 1 / Real.rpow δ_n d := by
        field_simp [h56.ne'] <;> ring
      have h61 : Real.rpow δ_n (-d) = 1 / Real.rpow δ_n d := by
        rw [h59, h60]
      exact h61.symm
    rw [h58] at h57
    exact h57
  have h_exp_sum : -d + (-(u / 2 + εA)) = -(u / 2 + εA') := by
    simp [hd_def] <;> ring
  have h_rpow_nonneg2 : 0 ≤ Real.rpow δ_n (-(u / 2 + εA)) :=
    Real.rpow_nonneg hδ_n_pos.le _
  have h7 : C * Real.rpow δ_n (-(u / 2 + εA)) ≤
      Real.rpow δ_n (-d) * Real.rpow δ_n (-(u / 2 + εA)) :=
    mul_le_mul_of_nonneg_right h4 h_rpow_nonneg2
  have h8 : Real.rpow δ_n (-d) * Real.rpow δ_n (-(u / 2 + εA)) =
      Real.rpow δ_n (-(u / 2 + εA')) := by
    have h9 : Real.rpow δ_n (-d + (-(u / 2 + εA))) =
        Real.rpow δ_n (-d) * Real.rpow δ_n (-(u / 2 + εA)) :=
      Real.rpow_add hδ_n_pos (-d) (-(u / 2 + εA))
    have h10 : Real.rpow δ_n (-d) * Real.rpow δ_n (-(u / 2 + εA)) =
        Real.rpow δ_n (-d + (-(u / 2 + εA))) := h9.symm
    rw [h10, h_exp_sum]
  have h2 : C * Real.rpow δ_n (-(u / 2 + εA)) ≤ Real.rpow δ_n (-(u / 2 + εA')) := by
    calc C * Real.rpow δ_n (-(u / 2 + εA))
      ≤ Real.rpow δ_n (-d) * Real.rpow δ_n (-(u / 2 + εA)) := h7
    _ = Real.rpow δ_n (-(u / 2 + εA')) := h8
  calc (Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal P : ENNReal)
    ≤ ENNReal.ofReal (C * Real.rpow δ_n (-(u / 2 + εA))) := h1
  _ ≤ ENNReal.ofReal (Real.rpow δ_n (-(u / 2 + εA'))) := by
    exact ENNReal.ofReal_le_ofReal h2

end DirecretisedFurstenbergEstimate.FrontEndLemmas

module

/-
# Strong Ring Theorem — Steps 9–12

Proof skeletons for `step9_11_triangle_correct` and `step12_diff_to_sum_correct`
from `StrongRingTheorem_Corrected.lean`.

## Proof route

### Steps 9–11 (iterated Ruzsa triangle)
Factor `y = w₁···w_N`, apply sub-sub-sub Ruzsa triangle iteratively,
telescoping product + pigeonhole yields `w ∈ {1}∪K` with gain
`δ^{(cN-α)/(2N+1)}`.

### Step 12 (difference to sumset)
Case `w ∈ K`: Corollary 2.4 reverse, cubic loss, exponent `β < -4c` ensures
final gain `δ^{-c}` for small δ.
Case `w = 1`: Corollary 2.3 + sum-to-diff.

## Status
- Steps 9–11: proved
- Step 12 w∈K case: proved
- Step 12 w=1 case: resolved via normalization hypothesis `h1_in_K : 1 ∈ K`
- Constant absorption: `ennreal_absorb_constant` helper provided for dilation bounds
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSW.RuzsaCorollaries
public import MyLeanRepo.StrongRingHelpers
public import MyLeanRepo.StrongRingNormalize
public import MyLeanRepo.StrongRingStep6
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Classical Set ENNReal BigOperators
open scoped Pointwise

namespace WeakTwoEndsSumProduct

noncomputable section

/-- ENNReal power reflection: `a^n ≤ b^n` implies `a ≤ b` for `n > 0`. -/
lemma ennreal_pow_le_imp_le {n : ℕ} (hn : 0 < n) {a b : ENNReal} (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_contra h'
  have h'' : b < a := lt_of_not_ge h'
  have hne : n ≠ 0 := by linarith
  have : b ^ n < a ^ n := (ENNReal.pow_lt_pow_left_iff hne).mpr h''
  exact not_le.mpr this h

/-! ## Steps 9–11: Iterated Ruzsa triangle -/

/-- **Steps 9–11**: Iterated Ruzsa triangle along factorization `y = w_1···w_N`.

Exact paper iteration (Section 4.5, lines 617–636):

Let `B = t^{-1}A`, `z_j = w_1···w_j` (z_0 = 1), `α = (1-s)/(24k)`.

**First triangle** (for each j): Ruzsa triangle gives
  `N(B - z_j A) · N(z_{j-1} A) ≤ C · N(B - z_{j-1} A) · N(z_{j-1} A - z_j A)`.
Since `z_{j-1} ~ 1` (K ⊆ [2^{-1/κ}, 1]), scaling bounds give
  `N(B - z_j A) · N(A) ≤ C₁ · N(B - z_{j-1} A) · N(A - w_j A)`.

**Multiply** j=1..N and telescope:
  `N(B - yA) · N(A)^N ≤ C₁^N · N(B - A) · ∏_{j=1}^N N(A - w_j A)`.

**Second triangle** (for each j): Ruzsa triangle gives
  `N(A - w_j A) · N(B) ≤ C · N(A - B) · N(B - w_j A)`.
Since `N(A-B) = N(B-A)`:
  `N(A - w_j A) ≤ C₂ · N(B - A) · N(B - w_j A) / N(B)`.

**Combine**:
  `N(B - yA) · N(A)^N ≤ C₃ · N(B - A)^{N+1} · (∏ N(B - w_j A)) / N(B)^N`.

**Scaling comparison**: Since `t ≥ δ^c`, `N(A) ≥ C₄ · δ^c · N(B)`.
Thus `N(A)^{-N} ≤ C₄^{-N} · δ^{-cN} · N(B)^{-N}`, so:
  `N(B - yA) ≤ C₅ · N(B - A)^{N+1} · (∏ N(B - w_j A)) · δ^{-cN} · N(B)^{-2N}`.

**Pigeonhole**: Let `M = max(N(B-A), N(B-w_1A), ..., N(B-w_NA))`.
There are N+1 terms, with total exponent 2N+1:
  `N(B - yA) ≤ C₅ · M^{2N+1} · δ^{-cN} · N(B)^{-2N}`.
Given `N(B - yA) ≥ δ^{-α} N(B)`:
  `M^{2N+1} ≥ C₅^{-1} · δ^{cN-α} · N(B)^{2N+1}`.
So some `w ∈ {1, w_1, ..., w_N}` satisfies
  `N(B - wA) ≥ C₅^{-1/(2N+1)} · δ^{(cN-α)/(2N+1)} · N(B)`.

For small δ, the constant is absorbed into the δ exponent.
-/
lemma step9_11_triangle_correct
    {A K : Set ℝ} {N0 : ℕ} (hN_pos : 0 < N0)
    {δ δ₀ t c κ ε_abs α_in : ℝ} (hδ_pos : 0 < δ) (ht_pos : 0 < t) (ht_le_one : t ≤ 1)
    (hc_pos : 0 < c) (hκ_pos : 0 < κ) (hε_abs_pos : 0 < ε_abs)
    {y : ℝ} (hy : y ∈ productSetN K N0)
    (h_y_expansion : ENNReal.ofReal (δ ^ α_in) *
        Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet t⁻¹ A) (scaleSet y A)))
    (hK_bounds : K ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1)
    (h_t_lower : δ ^ c ≤ t)
    (hδ_small : δ ≤ δ₀) (hδ₀_le_one : δ₀ ≤ 1)
    (hδ_absorb : δ ^ ε_abs ≤ (46656 : ℝ)^ (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1)) *
        (2 : ℝ)^ (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1))))
    (hK_bdd : Bornology.IsBounded K) (hA_bdd : Bornology.IsBounded A)
    (hA_nonempty : A.Nonempty) (hK_nonempty : K.Nonempty) :
    ∃ (w : ℝ), (w = 1 ∨ w ∈ K) ∧
      ENNReal.ofReal (δ ^ (c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) +
        α_in / (2 * (N0 : ℝ) + 1) + ε_abs)) *
      Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet t⁻¹ A) (scaleSet w A)) := by
  have hδ_le_one : δ ≤ 1 := le_trans hδ_small hδ₀_le_one
  let B := scaleSet t⁻¹ A
  let α : ℝ := -α_in
  let β : ℝ := c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) - α / (2 * (N0 : ℝ) + 1)
  let NA := Nreal δ A
  let NB := Nreal δ B
  rcases hy with ⟨f, hf, rfl⟩
  let w : Fin N0 → ℝ := f
  have hw_in_K : ∀ i : Fin N0, w i ∈ K := hf
  let z : ℕ → ℝ := fun j =>
    Finset.prod (Finset.range j) (fun i => if h : i < N0 then w ⟨i, h⟩ else 1)
  have z_zero : z 0 = 1 := by simp [z]
  have z_succ : ∀ (j : ℕ) (hj : j < N0), z (j + 1) = z j * w ⟨j, hj⟩ := by
    intro j hj
    have h_j_lt : j < N0 := hj
    simp [z, Finset.prod_range_succ, h_j_lt] <;> ring
  have z_bounds : ∀ (j : ℕ), j ≤ N0 → (2 : ℝ)^(-(j : ℝ)/κ) ≤ z j ∧ z j ≤ 1 := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [z_zero] <;> positivity
    | succ j ih =>
      intro hj
      have h_j_lt_N0 : j < N0 := by linarith
      have ih' := ih (by linarith)
      have h_w : (2 : ℝ)^(-(1/κ)) ≤ w ⟨j, h_j_lt_N0⟩ ∧ w ⟨j, h_j_lt_N0⟩ ≤ 1 :=
        ⟨(hK_bounds (hw_in_K _)).1, (hK_bounds (hw_in_K _)).2⟩
      have h_z_succ : z (j + 1) = z j * w ⟨j, h_j_lt_N0⟩ := z_succ j h_j_lt_N0
      rw [h_z_succ]
      have h_zj_pos : 0 < z j := by
        have h_pos : 0 < (2 : ℝ)^(-(j : ℝ)/κ) := by positivity
        linarith [ih'.1]
      have h1 : (2 : ℝ)^(-((j + 1 : ℕ) : ℝ)/κ) ≤ z j * w ⟨j, h_j_lt_N0⟩ := by
        have h2 : (2 : ℝ)^(-((j + 1 : ℕ) : ℝ)/κ) = (2 : ℝ)^(-(j : ℝ)/κ) * (2 : ℝ)^(-(1/κ)) := by
          rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by simp]
          rw [← Real.rpow_add (by norm_num)] <;> ring_nf
        rw [h2]
        exact mul_le_mul ih'.1 h_w.1 (by positivity) (by linarith)
      have h3 : z j * w ⟨j, h_j_lt_N0⟩ ≤ 1 := by
        have h4 : z j ≤ 1 := ih'.2
        have h5 : w ⟨j, h_j_lt_N0⟩ ≤ 1 := h_w.2
        have h61 : 0 < (2 : ℝ)^(-(1/κ)) := by positivity
        have h6 : 0 ≤ w ⟨j, h_j_lt_N0⟩ := by linarith [h_w.1, h61]
        have h7 : 0 ≤ z j := by
          have h8 : 0 < (2 : ℝ)^(-(j : ℝ)/κ) := by positivity
          linarith [ih'.1]
        nlinarith
      exact ⟨h1, h3⟩
  have hB_bdd : Bornology.IsBounded B := scaleSet_bounded hA_bdd
  have hB_nonempty : B.Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    have h : t⁻¹ * a ∈ B := by
      simp only [B, scaleSet, Set.mem_image]
      exact ⟨a, ha, by ring⟩
    exact ⟨t⁻¹ * a, h⟩
  let D : ℕ → ENNReal := fun j => Nreal δ (Set.image2 (· - ·) B (scaleSet (z j) A))
  let E : Fin N0 → ENNReal := fun i => Nreal δ (Set.image2 (· - ·) A (scaleSet (w i) A))
  let F : Fin N0 → ENNReal := fun i => Nreal δ (Set.image2 (· - ·) B (scaleSet (w i) A))
  let Enat : ℕ → ENNReal := fun j => if h : j < N0 then E ⟨j, h⟩ else 0
  let Fnat : ℕ → ENNReal := fun j => if h : j < N0 then F ⟨j, h⟩ else 0
  have hEnat_eq : ∀ (j : ℕ) (hj : j < N0), Enat j = E ⟨j, hj⟩ := by
    intro j hj; simp [Enat, hj]
  have hFnat_eq : ∀ (j : ℕ) (hj : j < N0), Fnat j = F ⟨j, hj⟩ := by
    intro j hj; simp [Fnat, hj]
  by_cases hNB : NB = 0
  · have h_main_zero : ENNReal.ofReal (δ ^ (c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) +
          α_in / (2 * (N0 : ℝ) + 1) + ε_abs)) * NB = 0 := by
      rw [hNB] <;> simp
    have h_goal : ENNReal.ofReal (δ ^ (c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) +
            α_in / (2 * (N0 : ℝ) + 1) + ε_abs)) * NB ≤
          Nreal δ (Set.image2 (· - ·) (scaleSet t⁻¹ A) (scaleSet (1 : ℝ) A)) := by
      rw [h_main_zero]
      simp
    exact ⟨1, Or.inl rfl, h_goal⟩
  -- First Ruzsa: D(j+1)*NA ≤ (216/z_j)*D(j)*E(j)
  have h_step1 : ∀ (j : ℕ) (hj : j < N0),
      D (j + 1) * NA ≤ (ENNReal.ofReal (216 / z j)) * D j * E ⟨j, hj⟩ := by
    intro j hj
    have h_j_le_N0 : j ≤ N0 := by linarith
    have h_zj_pos : 0 < z j := by
      have h := (z_bounds j h_j_le_N0).1
      have h_pos : 0 < (2 : ℝ)^(-(j : ℝ)/κ) := by positivity
      linarith
    have h_zj_le_one : z j ≤ 1 := (z_bounds j h_j_le_N0).2
    let zjA := scaleSet (z j) A
    let zj1A := scaleSet (z (j + 1)) A
    have h_zjA_bdd : Bornology.IsBounded zjA := scaleSet_bounded hA_bdd
    have h_zj1A_bdd : Bornology.IsBounded zj1A := scaleSet_bounded hA_bdd
    have h_zjA_nonempty : zjA.Nonempty := by
      rcases hA_nonempty with ⟨a, ha⟩
      have h : z j * a ∈ zjA := by
        simp only [zjA, scaleSet, Set.mem_image]
        exact ⟨a, ha, by ring⟩
      exact ⟨z j * a, h⟩
    have h1 : D (j + 1) * Nreal δ zjA ≤ 36 * D j * Nreal δ (Set.image2 (· - ·) zjA zj1A) :=
      ruzsa_triangle_sub_sub_sub hδ_pos hB_bdd h_zjA_bdd h_zj1A_bdd h_zjA_nonempty
    have h_scale : Nreal δ zjA = Nreal (δ / z j) A := covering_scaling hδ_pos h_zj_pos hA_bdd
    have h_coarse : ENNReal.ofReal (z j / 3) * NA ≤ Nreal (δ / z j) A := by
      have h := covering_coarsening (div_pos hδ_pos h_zj_pos) h_zj_pos h_zj_le_one hA_bdd
      have h_mul : (δ / z j) * z j = δ := by field_simp [h_zj_pos.ne'] <;> ring
      rw [h_mul] at h
      exact h
    have h2 : ENNReal.ofReal (z j / 3) * NA ≤ Nreal δ zjA := by
      rw [h_scale]; exact h_coarse
    have h2' : NA ≤ ENNReal.ofReal (3 / z j) * Nreal δ zjA := by
      have h_pos : 0 < z j := h_zj_pos
      have h_pos1 : 0 ≤ 3 / z j := by positivity
      have h_mul_eq : ENNReal.ofReal (3 / z j) * ENNReal.ofReal (z j / 3) = 1 := by
        have h' : ENNReal.ofReal (3 / z j) * ENNReal.ofReal (z j / 3) =
            ENNReal.ofReal ((3 / z j) * (z j / 3)) := by
          exact Eq.symm (ofReal_mul h_pos1)
        rw [h']
        have h'' : (3 / z j) * (z j / 3) = 1 := by field_simp [h_pos.ne'] <;> ring
        rw [h''] <;> simp
      have h_mul1 : ENNReal.ofReal (3 / z j) * (ENNReal.ofReal (z j / 3) * NA) ≤
          ENNReal.ofReal (3 / z j) * Nreal δ zjA := by gcongr
      have h_mul2 : ENNReal.ofReal (3 / z j) * (ENNReal.ofReal (z j / 3) * NA) = NA := by
        rw [← mul_assoc, h_mul_eq, one_mul]
      rw [h_mul2] at h_mul1; exact h_mul1
    have h3 : z (j + 1) = z j * w ⟨j, hj⟩ := z_succ j hj
    have h4 : Set.image2 (· - ·) zjA zj1A = scaleSet (z j) (Set.image2 (· - ·) A (scaleSet (w ⟨j, hj⟩) A)) := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hx with ⟨a, ha, b, hb, hx_eq⟩
        rcases ha with ⟨a1, ha1, ha_eq⟩
        rcases hb with ⟨b1, hb1, hb_eq⟩
        have h_zj1 : z (j + 1) = z j * w ⟨j, hj⟩ := h3
        have h_b_eq : b = z j * (w ⟨j, hj⟩ * b1) := by
          have h : z (j + 1) * b1 = b := hb_eq
          rw [h_zj1] at h
          ring_nf at h ⊢; exact h.symm
        have h_y_mem : a1 - w ⟨j, hj⟩ * b1 ∈ Set.image2 (· - ·) A (scaleSet (w ⟨j, hj⟩) A) := by
          exact ⟨a1, ha1, w ⟨j, hj⟩ * b1, ⟨b1, hb1, by ring⟩, by ring⟩
        have h_eq : z j * (a1 - w ⟨j, hj⟩ * b1) = x := by
          have h1 : z j * (a1 - w ⟨j, hj⟩ * b1) = z j * a1 - z j * (w ⟨j, hj⟩ * b1) := by ring
          have h2 : z j * a1 - z j * (w ⟨j, hj⟩ * b1) = a - b := by
            rw [← ha_eq, ← h_b_eq] <;> ring
          exact Eq.trans (Eq.trans h1 h2) hx_eq
        exact ⟨a1 - w ⟨j, hj⟩ * b1, h_y_mem, h_eq⟩
      · intro x hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨a1, ha1, c, hc, rfl⟩
        rcases hc with ⟨b1, hb1, hc_eq⟩
        have h_zj1 : z (j + 1) = z j * w ⟨j, hj⟩ := h3
        have h_c_eq : c = w ⟨j, hj⟩ * b1 := hc_eq.symm
        have h_b_mem : z j * c ∈ zj1A := by
          have h1 : z j * c = z (j + 1) * b1 := by
            rw [h_c_eq, h_zj1] <;> ring
          rw [h1]
          exact ⟨b1, hb1, rfl⟩
        have h_a_mem : z j * a1 ∈ zjA := ⟨a1, ha1, by ring⟩
        have h_final : z j * a1 - z j * c = x := by
          have h1 : z j * a1 - z j * c = z j * (a1 - c) := by ring
          rw [h1]
          exact hxy
        exact ⟨z j * a1, h_a_mem, z j * c, h_b_mem, h_final⟩
    have h5 : Nreal δ (Set.image2 (· - ·) zjA zj1A) ≤ 2 * E ⟨j, hj⟩ := by
      rw [h4]
      let S := Set.image2 (· - ·) A (scaleSet (w ⟨j, hj⟩) A)
      have hS_bdd : Bornology.IsBounded S := by
        rcases hA_nonempty with ⟨a0, ha0⟩
        rcases Metric.isBounded_iff.mp hA_bdd with ⟨C, hC⟩
        have hA_bound : ∀ a ∈ A, |a| ≤ |a0| + C := by
          intro a ha
          have h : dist a a0 ≤ C := hC ha ha0
          have h' : |a - a0| ≤ C := by simpa [Real.dist_eq] using h
          have h4 : |a| ≤ |a0| + |a - a0| := by
            have h5 : |a| = |a0 + (a - a0)| := by ring_nf
            rw [h5]
            simpa [Real.norm_eq_abs] using norm_add_le a0 (a - a0)
          linarith
        have h_w_le_one : w ⟨j, hj⟩ ≤ 1 := (hK_bounds (hw_in_K _)).2
        have h_w_nonneg : 0 ≤ w ⟨j, hj⟩ := by
          have h_low : (2 : ℝ)^(-(1/κ)) ≤ w ⟨j, hj⟩ := (hK_bounds (hw_in_K _)).1
          have h_pos : 0 < (2 : ℝ)^(-(1/κ)) := by positivity
          linarith
        let M := |a0| + C
        have h_w_abs_le : |w ⟨j, hj⟩| ≤ 1 := by
          rw [abs_of_nonneg h_w_nonneg] <;> linarith
        have h4 : ∀ x ∈ S, |x| ≤ 2 * M := by
          intro x hx
          rcases hx with ⟨a, ha, b, hb, rfl⟩
          rcases hb with ⟨c, hc, rfl⟩
          have ha' : |a| ≤ M := hA_bound a ha
          have hc' : |c| ≤ M := hA_bound c hc
          have h51 : |w ⟨j, hj⟩ * c| = |w ⟨j, hj⟩| * |c| := by rw [abs_mul]
          have h52 : |w ⟨j, hj⟩ * c| ≤ M := by
            rw [h51]
            calc |w ⟨j, hj⟩| * |c| ≤ 1 * |c| := by gcongr
              _ ≤ 1 * M := by gcongr
              _ = M := by ring
          have h6 : |a - w ⟨j, hj⟩ * c| ≤ |a| + |w ⟨j, hj⟩ * c| := by
            simpa [Real.norm_eq_abs] using norm_sub_le a (w ⟨j, hj⟩ * c)
          linarith
        rw [Metric.isBounded_iff]
        refine ⟨4 * M + 1, fun x hx y hy => ?_⟩
        have hx' : |x| ≤ 2 * M := h4 x hx
        have hy' : |y| ≤ 2 * M := h4 y hy
        have h_dist : dist x y ≤ |x| + |y| := by
          have h : dist x y = |x - y| := by simp [Real.dist_eq]
          rw [h]
          have h2 : |x - y| ≤ |x| + |y| := by
            simpa [Real.norm_eq_abs] using norm_sub_le x y
          exact h2
        linarith
      exact covering_scale_down_le_two hδ_pos h_zj_pos h_zj_le_one hS_bdd
    calc D (j + 1) * NA
      ≤ D (j + 1) * (ENNReal.ofReal (3 / z j) * Nreal δ zjA) := by gcongr
    _ = (ENNReal.ofReal (3 / z j)) * (D (j + 1) * Nreal δ zjA) := by ring
    _ ≤ (ENNReal.ofReal (3 / z j)) * (36 * D j * Nreal δ (Set.image2 (· - ·) zjA zj1A)) := by gcongr
    _ ≤ (ENNReal.ofReal (3 / z j)) * (36 * D j * (2 * E ⟨j, hj⟩)) := by gcongr
    _ = (ENNReal.ofReal (216 / z j)) * D j * E ⟨j, hj⟩ := by
      have h_pos : 0 ≤ 3 / z j := by positivity
      have h1 : (36 : ENNReal) * D j * (2 * E ⟨j, hj⟩) = (72 : ENNReal) * D j * E ⟨j, hj⟩ := by ring
      rw [h1]
      have h2 : ENNReal.ofReal (3 / z j) * ((72 : ENNReal) * D j * E ⟨j, hj⟩) =
          (ENNReal.ofReal (3 / z j) * (72 : ENNReal)) * D j * E ⟨j, hj⟩ := by ring
      rw [h2]
      have h72 : (72 : ENNReal) = ENNReal.ofReal (72 : ℝ) := by simp
      have h3 : ENNReal.ofReal (3 / z j) * (72 : ENNReal) = ENNReal.ofReal ((3 / z j) * 72) := by
        rw [h72]
        have h_pos72 : 0 ≤ (72 : ℝ) := by norm_num
        rw [← ENNReal.ofReal_mul h_pos]
        <;> norm_cast
      rw [h3]
      have h4 : (3 / z j) * 72 = 216 / z j := by ring
      rw [h4] <;> ring
  -- Second Ruzsa: E(i)*NB ≤ 72*D(0)*F(i)
  have h_step2 : ∀ i : Fin N0, E i * NB ≤ (72 : ENNReal) * D 0 * F i := by
    intro i
    let wiA := scaleSet (w i) A
    have h_wiA_bdd : Bornology.IsBounded wiA := scaleSet_bounded hA_bdd
    have h1 : E i * NB ≤ 36 * Nreal δ (Set.image2 (· - ·) A B) * F i :=
      ruzsa_triangle_sub_sub_sub hδ_pos hA_bdd hB_bdd h_wiA_bdd hB_nonempty
    have hAB_eq : Set.image2 (· - ·) A B = negSet (Set.image2 (· - ·) B A) := by
      ext z; simp only [negSet, Set.mem_image2, Set.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b - a, ⟨b, hb, a, ha, rfl⟩, by ring⟩
      · rintro ⟨w, ⟨b, hb, a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, b, hb, by ring⟩
    have h2 : Nreal δ (Set.image2 (· - ·) A B) ≤ 2 * D 0 := by
      rw [hAB_eq]
      have h_bdd : Bornology.IsBounded (Set.image2 (· - ·) B A) :=
        hB_bdd.sub hA_bdd
      have h_scale1 : scaleSet (1 : ℝ) A = A := by
        ext x; simp [scaleSet]
      have hD0 : D 0 = Nreal δ (Set.image2 (· - ·) B A) := by
        have h_z0 : z 0 = 1 := z_zero
        simp [D, h_z0, h_scale1]
      rw [hD0]
      exact covering_negation_le_two hδ_pos h_bdd
    calc E i * NB
      ≤ 36 * Nreal δ (Set.image2 (· - ·) A B) * F i := h1
    _ ≤ 36 * (2 * D 0) * F i := by gcongr
    _ = (72 : ENNReal) * D 0 * F i := by simp [mul_assoc] <;> ring
  -- Telescope by induction
  have h_telescope : ∀ m : ℕ, m ≤ N0 →
      D m * NA ^ m ≤ (∏ j ∈ Finset.range m, ENNReal.ofReal (216 / z j)) * D 0 *
        (∏ j ∈ Finset.range m, Enat j) := by
    intro m hm; induction m with
    | zero => simp
    | succ m ih =>
      have h_m_lt_N0 : m < N0 := by linarith
      have h_step1' := h_step1 m h_m_lt_N0
      have ih' := ih (by linarith)
      have h_Enat_m : Enat m = E ⟨m, h_m_lt_N0⟩ := hEnat_eq m h_m_lt_N0
      calc D (m + 1) * NA ^ (m + 1)
        = (D (m + 1) * NA) * NA ^ m := by ring
      _ ≤ (ENNReal.ofReal (216 / z m) * D m * E ⟨m, h_m_lt_N0⟩) * NA ^ m := by gcongr
      _ = ENNReal.ofReal (216 / z m) * E ⟨m, h_m_lt_N0⟩ * (D m * NA ^ m) := by ring
      _ = ENNReal.ofReal (216 / z m) * Enat m * (D m * NA ^ m) := by rw [h_Enat_m] <;> ring
      _ ≤ ENNReal.ofReal (216 / z m) * Enat m *
            ((∏ j ∈ Finset.range m, ENNReal.ofReal (216 / z j)) * D 0 *
             (∏ j ∈ Finset.range m, Enat j)) := by gcongr
      _ = (∏ j ∈ Finset.range (m + 1), ENNReal.ofReal (216 / z j)) * D 0 *
            (∏ j ∈ Finset.range (m + 1), Enat j) := by
        simp [Finset.prod_range_succ, mul_assoc] <;> ring
  have h_tel_N0 := h_telescope N0 (by linarith)
  have h_prod_Enat_eq : (∏ j ∈ Finset.range N0, Enat j) = (∏ i : Fin N0, E i) := by
    apply Finset.prod_bij (s := Finset.range N0) (t := Finset.univ) (f := Enat) (g := E)
      (fun j hj => ⟨j, Finset.mem_range.mp hj⟩)
    · intro j hj; exact Finset.mem_univ _
    · intro j1 hj1 j2 hj2 h_eq; simpa using h_eq
    · intro i _; exact ⟨i.val, Finset.mem_range.mpr i.isLt, by simp⟩
    · intro j hj; exact hEnat_eq j (Finset.mem_range.mp hj)
  have h_prod_Fnat_eq : (∏ j ∈ Finset.range N0, Fnat j) = (∏ i : Fin N0, F i) := by
    apply Finset.prod_bij (s := Finset.range N0) (t := Finset.univ) (f := Fnat) (g := F)
      (fun j hj => ⟨j, Finset.mem_range.mp hj⟩)
    · intro j hj; exact Finset.mem_univ _
    · intro j1 hj1 j2 hj2 h_eq; simpa using h_eq
    · intro i _; exact ⟨i.val, Finset.mem_range.mpr i.isLt, by simp⟩
    · intro j hj; exact hFnat_eq j (Finset.mem_range.mp hj)
  have h_step2_prod : (∏ i : Fin N0, E i) * NB ^ N0 ≤
      (72 : ENNReal) ^ N0 * D 0 ^ N0 * (∏ i : Fin N0, F i) := by
    have h : ∀ i : Fin N0, E i * NB ≤ (72 : ENNReal) * D 0 * F i := h_step2
    have h' := Finset.prod_le_prod (s := Finset.univ) (fun _ _ => by positivity) (fun i _ => h i)
    have h_eq1 : ∏ i : Fin N0, (E i * NB) = (∏ i : Fin N0, E i) * NB ^ N0 := by
      simp [Finset.prod_mul_distrib] <;> ring
    have h_eq2 : ∏ i : Fin N0, ((72 : ENNReal) * D 0 * F i) =
        (72 : ENNReal) ^ N0 * D 0 ^ N0 * (∏ i : Fin N0, F i) := by
      simp [Finset.prod_mul_distrib] <;> ring
    rw [h_eq1, h_eq2] at h'; exact h'
  have h_combine : D N0 * NA ^ N0 * NB ^ N0 ≤
      (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) * (72 : ENNReal) ^ N0 *
      D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i) := by
    have h_tel' : D N0 * NA ^ N0 ≤ (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) * D 0 * (∏ i : Fin N0, E i) := by
      rw [h_prod_Enat_eq] at h_tel_N0; exact h_tel_N0
    calc D N0 * NA ^ N0 * NB ^ N0
      = (D N0 * NA ^ N0) * NB ^ N0 := by ring
    _ ≤ ((∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) * D 0 * (∏ i : Fin N0, E i)) * NB ^ N0 := by gcongr
    _ = (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) * D 0 * ((∏ i : Fin N0, E i) * NB ^ N0) := by ring
    _ ≤ (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) * D 0 *
          ((72 : ENNReal) ^ N0 * D 0 ^ N0 * (∏ i : Fin N0, F i)) := by gcongr
    _ = (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) * (72 : ENNReal) ^ N0 *
          D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i) := by ring
  -- Bound ∏(216/z_j) ≤ 216^N * 2^{N(N-1)/(2κ)}
  have h_z_prod_bound : (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) ≤
      (216 : ENNReal) ^ N0 * ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) := by
    have h1 : ∀ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j) ≤
        (216 : ENNReal) * ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ)) := by
      intro j hj
      have h_j_lt_N0 : j < N0 := Finset.mem_range.mp hj
      have h_j_le_N0 : j ≤ N0 := by linarith
      have h_zj_pos : 0 < z j := by
        have h := (z_bounds j h_j_le_N0).1
        have h_pos : 0 < (2 : ℝ)^(-(j : ℝ)/κ) := by positivity
        linarith
      have h_ineq : 216 / z j ≤ 216 * (2 : ℝ)^((j : ℝ)/κ) := by
        have h2 : 1 / z j ≤ (2 : ℝ)^((j : ℝ)/κ) := by
          have h3 : (2 : ℝ)^(-(j : ℝ)/κ) ≤ z j := (z_bounds j h_j_le_N0).1
          have h4 : 1 / z j ≤ 1 / (2 : ℝ)^(-(j : ℝ)/κ) := by gcongr
          have h5 : 1 / (2 : ℝ)^(-(j : ℝ)/κ) = (2 : ℝ)^((j : ℝ)/κ) := by
            have h_neg : (-(j : ℝ)/κ) = -((j : ℝ)/κ) := by ring
            rw [h_neg]
            rw [Real.rpow_neg (by norm_num)]
            field_simp
          rw [h5] at h4; exact h4
        calc 216 / z j = 216 * (1 / z j) := by ring
        _ ≤ 216 * (2 : ℝ)^((j : ℝ)/κ) := by gcongr
      have h_pos2 : 0 ≤ 216 * (2 : ℝ)^((j : ℝ)/κ) := by positivity
      have h_ofReal : ENNReal.ofReal (216 / z j) ≤ ENNReal.ofReal (216 * (2 : ℝ)^((j : ℝ)/κ)) :=
        ENNReal.ofReal_le_ofReal_iff h_pos2 |>.mpr h_ineq
      have h_mul : ENNReal.ofReal (216 * (2 : ℝ)^((j : ℝ)/κ)) =
          (216 : ENNReal) * ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ)) := by
        have h216 : (216 : ENNReal) = ENNReal.ofReal (216 : ℝ) := by simp
        rw [h216]
        have h : ENNReal.ofReal (216 * (2 : ℝ)^((j : ℝ)/κ)) =
            ENNReal.ofReal (216 : ℝ) * ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [h]
      rw [h_mul] at h_ofReal; exact h_ofReal
    have h_prod_ineq := Finset.prod_le_prod (fun _ _ => by positivity) h1
    have h_prod2 : ∏ j ∈ Finset.range N0, ((216 : ENNReal) * ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ))) =
        (216 : ENNReal) ^ N0 * ∏ j ∈ Finset.range N0, ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ)) := by
      have h_dist : ∏ j ∈ Finset.range N0, ((216 : ENNReal) * ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ))) =
          (∏ j ∈ Finset.range N0, (216 : ENNReal)) * (∏ j ∈ Finset.range N0, ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ))) := by
        rw [Finset.prod_mul_distrib]
      rw [h_dist]
      have h_const : ∏ j ∈ Finset.range N0, (216 : ENNReal) = (216 : ENNReal) ^ N0 := by
        simp
      rw [h_const] <;> ring
    have h_sum : ∑ j ∈ Finset.range N0, (j : ℝ)/κ = (N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ) := by
      have h1 : ∑ j ∈ Finset.range N0, (j : ℝ)/κ = (1 / κ) * ∑ j ∈ Finset.range N0, (j : ℝ) := by
        have h_eq : ∑ j ∈ Finset.range N0, (j : ℝ)/κ = ∑ j ∈ Finset.range N0, ((1 / κ) * (j : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [h_eq, Finset.mul_sum]
      rw [h1]
      have h2 : ∀ n : ℕ, ∑ j ∈ Finset.range n, (j : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          <;> simp [Nat.cast_add, Nat.cast_one] <;> ring
      rw [h2 N0] <;> ring
    have h_rpow_prod : ∏ j ∈ Finset.range N0, (2 : ℝ)^((j : ℝ)/κ) = (2 : ℝ)^(∑ j ∈ Finset.range N0, (j : ℝ)/κ) := by
      have h3 : ∀ (s : Finset ℕ), ∏ j ∈ s, (2 : ℝ)^((j : ℝ)/κ) = (2 : ℝ)^(∑ j ∈ s, (j : ℝ)/κ) := by
        intro s
        induction s using Finset.induction with
        | empty => norm_num
        | @insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
          rw [← Real.rpow_add (by norm_num)] <;> ring
      exact h3 (Finset.range N0)
    have h_nonneg : ∀ j ∈ Finset.range N0, 0 ≤ (2 : ℝ)^((j : ℝ)/κ) := by intro j _; positivity
    have h_ofReal_prod : ∏ j ∈ Finset.range N0, ENNReal.ofReal ((2 : ℝ)^((j : ℝ)/κ)) =
        ENNReal.ofReal (∏ j ∈ Finset.range N0, (2 : ℝ)^((j : ℝ)/κ)) := by
      rw [ENNReal.ofReal_prod_of_nonneg h_nonneg]
    rw [h_prod2, h_ofReal_prod, h_rpow_prod, h_sum] at h_prod_ineq
    exact h_prod_ineq
  -- Scaling and expansion
  have h_scaling : ENNReal.ofReal (δ ^ c / 3) * NB ≤ NA :=
    covering_NA_ge_NB hδ_pos hc_pos ht_pos ht_le_one h_t_lower hA_bdd
  have h_scaling_pow : (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ N0 ≤ NA ^ N0 := by
    have h : (ENNReal.ofReal (δ ^ c / 3) * NB) ^ N0 ≤ NA ^ N0 := by gcongr
    have h_expand : (ENNReal.ofReal (δ ^ c / 3) * NB) ^ N0 =
        (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ N0 := by rw [mul_pow]
    rw [h_expand] at h; exact h
  have h_zN_eq_y : z N0 = ∏ i : Fin N0, w i := by
    dsimp only [z]
    apply Finset.prod_bij (s := Finset.range N0) (t := Finset.univ)
      (f := fun i => if h : i < N0 then w ⟨i, h⟩ else 1) (g := w)
      (fun i hi => ⟨i, Finset.mem_range.mp hi⟩)
    · intro i hi; exact Finset.mem_univ _
    · intro i1 hi1 i2 hi2 h_eq; simpa using h_eq
    · intro i _; exact ⟨i.val, Finset.mem_range.mpr i.isLt, by simp⟩
    · intro i hi
      have h_i_lt : i < N0 := Finset.mem_range.mp hi
      simp [h_i_lt]
  have hD_N0 : D N0 = Nreal δ (Set.image2 (· - ·) B (scaleSet (∏ i : Fin N0, w i) A)) := by
    simpa [D, h_zN_eq_y] using rfl
  have h_expansion : ENNReal.ofReal (δ ^ (-α)) * NB ≤ D N0 := by
    have hα : α = -α_in := by rfl
    have h_eq1 : δ ^ (-α) = δ ^ α_in := by
      rw [hα] <;> ring_nf
    have h_DN0 : D N0 = Nreal δ (Set.image2 (· - ·) B (scaleSet (∏ i : Fin N0, w i) A)) := by
      dsimp only [D]
      rw [h_zN_eq_y]
    rw [h_eq1, h_DN0]
    exact h_y_expansion
  have h_mult3 : (3 : ENNReal) ^ N0 * (ENNReal.ofReal (δ ^ c / 3)) ^ N0 =
      ENNReal.ofReal (δ ^ (c * (N0 : ℝ))) := by
    have h1 : (3 : ENNReal) * ENNReal.ofReal (δ ^ c / 3) = ENNReal.ofReal (δ ^ c) := by
      have h3 : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by simp
      rw [h3]
      have h_pos3 : 0 ≤ (3 : ℝ) := by norm_num
      have h : ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal (δ ^ c / 3) = ENNReal.ofReal ((3 : ℝ) * (δ ^ c / 3)) := by
        rw [ENNReal.ofReal_mul h_pos3]
      rw [h]
      have h2 : (3 : ℝ) * (δ ^ c / 3) = δ ^ c := by ring
      rw [h2]
    have h2 : (3 : ENNReal) ^ N0 * (ENNReal.ofReal (δ ^ c / 3)) ^ N0 =
        ((3 : ENNReal) * ENNReal.ofReal (δ ^ c / 3)) ^ N0 := by rw [← mul_pow] <;> ring
    rw [h2, h1]
    have h3 : (ENNReal.ofReal (δ ^ c)) ^ N0 = ENNReal.ofReal (δ ^ (c * (N0 : ℝ))) := by
      have h_posδc : 0 ≤ δ ^ c := by positivity
      rw [← ENNReal.ofReal_pow h_posδc N0]
      have h4 : (δ ^ c) ^ N0 = δ ^ (c * (N0 : ℝ)) := by
        have h1 : (δ ^ c) ^ N0 = (δ ^ c) ^ ((N0 : ℕ) : ℝ) := by
          exact (Real.rpow_natCast _ _).symm
        rw [h1]
        have hδ_le : 0 ≤ δ := by linarith
        rw [← Real.rpow_mul hδ_le]
        <;> ring
      rw [h4]
    exact h3
  -- Main inequality
  have h_main : ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1) ≤
      (3 : ENNReal) ^ N0 * (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) *
      (72 : ENNReal) ^ N0 * D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i) := by
    have h61 : ENNReal.ofReal (δ ^ (-α)) * (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ (2 * N0 + 1) =
        (ENNReal.ofReal (δ ^ (-α)) * NB) * ((ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ N0) * NB ^ N0 := by
      have h_pow : NB ^ (2 * N0 + 1) = NB * NB ^ N0 * NB ^ N0 := by
        rw [show 2 * N0 + 1 = N0 + (N0 + 1) by ring]
        rw [pow_add, pow_succ] <;> ring
      rw [h_pow] <;> ring
    have h6 : ENNReal.ofReal (δ ^ (-α)) * (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ (2 * N0 + 1) ≤
        D N0 * NA ^ N0 * NB ^ N0 := by
      rw [h61]
      have h62 : (ENNReal.ofReal (δ ^ (-α)) * NB) ≤ D N0 := h_expansion
      have h63 : (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ N0 ≤ NA ^ N0 := h_scaling_pow
      gcongr
    have h7 : (3 : ENNReal) ^ N0 * (ENNReal.ofReal (δ ^ (-α)) * (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ (2 * N0 + 1)) ≤
        (3 : ENNReal) ^ N0 * (D N0 * NA ^ N0 * NB ^ N0) := by gcongr
    have h8 : (3 : ENNReal) ^ N0 * (ENNReal.ofReal (δ ^ (-α)) * (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ (2 * N0 + 1)) =
        ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1) := by
      have h9 : 0 ≤ δ ^ (-α) := by positivity
      calc (3 : ENNReal) ^ N0 * (ENNReal.ofReal (δ ^ (-α)) * (ENNReal.ofReal (δ ^ c / 3)) ^ N0 * NB ^ (2 * N0 + 1))
        = ENNReal.ofReal (δ ^ (-α)) * ((3 : ENNReal) ^ N0 * (ENNReal.ofReal (δ ^ c / 3)) ^ N0) * NB ^ (2 * N0 + 1) := by ring
      _ = ENNReal.ofReal (δ ^ (-α)) * ENNReal.ofReal (δ ^ (c * (N0 : ℝ))) * NB ^ (2 * N0 + 1) := by rw [h_mult3]
      _ = ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1) := by
        rw [← ENNReal.ofReal_mul h9]
        have h10 : δ ^ (-α) * δ ^ (c * (N0 : ℝ)) = δ ^ (c * (N0 : ℝ) - α) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
        rw [h10]
    rw [h8] at h7
    calc ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1)
      ≤ (3 : ENNReal) ^ N0 * (D N0 * NA ^ N0 * NB ^ N0) := h7
    _ ≤ (3 : ENNReal) ^ N0 * ((∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) *
          (72 : ENNReal) ^ N0 * D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i)) := by gcongr
    _ = (3 : ENNReal) ^ N0 * (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) *
        (72 : ENNReal) ^ N0 * D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i) := by ring
  -- Pigeonhole
  let M : ENNReal := max (D 0) (Finset.univ.sup F)
  have hD0_le_M : D 0 ≤ M := le_max_left _ _
  have hF_le_M : ∀ i : Fin N0, F i ≤ M := by
    intro i; have h : F i ≤ Finset.univ.sup F := Finset.le_sup (Finset.mem_univ i)
    exact le_trans h (le_max_right _ _)
  have h_pigeon : D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i) ≤ M ^ (2 * N0 + 1) := by
    have h1 : D 0 ^ (N0 + 1) ≤ M ^ (N0 + 1) := by gcongr
    have h2 : (∏ i : Fin N0, F i) ≤ M ^ N0 := by
      have h4 := Finset.prod_le_prod (s := Finset.univ) (fun _ _ => by positivity) (fun i _ => hF_le_M i)
      simpa using h4
    calc D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i)
      ≤ M ^ (N0 + 1) * M ^ N0 := by gcongr
    _ = M ^ (2 * N0 + 1) := by rw [← pow_add] <;> ring
  have h_const_mul : (216 : ENNReal) ^ N0 * (72 : ENNReal) ^ N0 * (3 : ENNReal) ^ N0 = (46656 : ENNReal) ^ N0 := by
    have h : (216 : ENNReal) * (72 : ENNReal) * (3 : ENNReal) = (46656 : ENNReal) := by norm_num
    have h2 : (216 : ENNReal) ^ N0 * (72 : ENNReal) ^ N0 * (3 : ENNReal) ^ N0 =
        ((216 : ENNReal) * (72 : ENNReal) * (3 : ENNReal)) ^ N0 := by
      rw [← mul_pow, ← mul_pow] <;> ring
    rw [h2, h]
  have h_main2 : ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1) ≤
      (46656 : ENNReal) ^ N0 * ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) * M ^ (2 * N0 + 1) := by
    calc ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1)
      ≤ (3 : ENNReal) ^ N0 * (∏ j ∈ Finset.range N0, ENNReal.ofReal (216 / z j)) *
          (72 : ENNReal) ^ N0 * D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i) := h_main
    _ ≤ (3 : ENNReal) ^ N0 * ((216 : ENNReal) ^ N0 * ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ)))) *
          (72 : ENNReal) ^ N0 * D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i) := by gcongr
    _ = (216 : ENNReal) ^ N0 * (72 : ENNReal) ^ N0 * (3 : ENNReal) ^ N0 *
          ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) *
          (D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i)) := by ring
    _ = (46656 : ENNReal) ^ N0 * ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) *
          (D 0 ^ (N0 + 1) * (∏ i : Fin N0, F i)) := by rw [h_const_mul] <;> ring
    _ ≤ (46656 : ENNReal) ^ N0 * ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) * M ^ (2 * N0 + 1) := by gcongr
  let C_ruz1 : ℝ := (46656 : ℝ)^ (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1))
  let C_ruz2 : ℝ := (2 : ℝ)^ (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1)))
  let C_ruz : ENNReal := ENNReal.ofReal C_ruz1 * ENNReal.ofReal C_ruz2
  have h_pos1 : 0 ≤ C_ruz1 := by positivity
  have h_pos2 : 0 ≤ C_ruz2 := by positivity
  have h_C_ruz_pow : C_ruz ^ (2 * N0 + 1) =
      ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * ENNReal.ofReal ((2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) := by
    simp only [C_ruz]
    rw [mul_pow]
    have h_pow1 : (ENNReal.ofReal C_ruz1) ^ (2 * N0 + 1) = ENNReal.ofReal (C_ruz1 ^ (2 * N0 + 1)) := by
      rw [← ENNReal.ofReal_pow h_pos1 (2 * N0 + 1)]
    have h_pow2 : (ENNReal.ofReal C_ruz2) ^ (2 * N0 + 1) = ENNReal.ofReal (C_ruz2 ^ (2 * N0 + 1)) := by
      rw [← ENNReal.ofReal_pow h_pos2 (2 * N0 + 1)]
    rw [h_pow1, h_pow2]
    have h_real1 : C_ruz1 ^ (2 * N0 + 1) = (46656 : ℝ)^ (-(N0 : ℝ)) := by
      simp only [C_ruz1]
      have h_base : (0 : ℝ) ≤ (46656 : ℝ) := by norm_num
      have h_exp : ((2 * N0 + 1 : ℕ) : ℝ) = 2 * (N0 : ℝ) + 1 := by
        simp [Nat.cast_add, Nat.cast_mul] <;> ring
      have h1 : ((46656 : ℝ)^ (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1))) ^ (2 * N0 + 1) =
          ((46656 : ℝ)^ (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1))) ^ ((2 * N0 + 1 : ℕ) : ℝ) := by
        exact (Real.rpow_natCast _ _).symm
      rw [h1]
      have h2 : ((46656 : ℝ)^ (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1))) ^ ((2 * N0 + 1 : ℕ) : ℝ) =
          (46656 : ℝ)^ ((-(N0 : ℝ)/(2 * (N0 : ℝ) + 1)) * ((2 * N0 + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_mul h_base]
      rw [h2, h_exp]
      have h3 : (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1)) * (2 * (N0 : ℝ) + 1) = -(N0 : ℝ) := by
        have h_ne : (2 * (N0 : ℝ) + 1) ≠ 0 := by positivity
        field_simp [h_ne] <;> ring
      rw [h3]
    have h_real2 : C_ruz2 ^ (2 * N0 + 1) = (2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ)) := by
      simp only [C_ruz2]
      have h_base : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h_exp : ((2 * N0 + 1 : ℕ) : ℝ) = 2 * (N0 : ℝ) + 1 := by
        simp [Nat.cast_add, Nat.cast_mul] <;> ring
      have h1 : ((2 : ℝ)^ (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1)))) ^ (2 * N0 + 1) =
          ((2 : ℝ)^ (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1)))) ^ ((2 * N0 + 1 : ℕ) : ℝ) := by
        exact (Real.rpow_natCast _ _).symm
      rw [h1]
      have h2 : ((2 : ℝ)^ (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1)))) ^ ((2 * N0 + 1 : ℕ) : ℝ) =
          (2 : ℝ)^ ((-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1))) * ((2 * N0 + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_mul h_base]
      rw [h2, h_exp]
      have h3 : (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1))) * (2 * (N0 : ℝ) + 1) =
          -(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ) := by
        have h_ne : (2 * (N0 : ℝ) + 1) ≠ 0 := by positivity
        field_simp [h_ne] <;> ring
      rw [h3]
    rw [h_real1, h_real2]
  have hβ_eq : β = (c * (N0 : ℝ) - α) / (2 * (N0 : ℝ) + 1) := by dsimp only [β] <;> ring
  have h_posβ : 0 ≤ δ ^ β := by positivity
  have h_rpowβ : (ENNReal.ofReal (δ ^ β)) ^ (2 * N0 + 1) =
      ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) := by
    rw [← ENNReal.ofReal_pow h_posβ (2 * N0 + 1)]
    have h : (δ ^ β) ^ (2 * N0 + 1) = δ ^ (c * (N0 : ℝ) - α) := by
      have h_exp : ((2 * N0 + 1 : ℕ) : ℝ) = 2 * (N0 : ℝ) + 1 := by
        simp [Nat.cast_add, Nat.cast_mul] <;> ring
      have h1 : (δ ^ β) ^ (2 * N0 + 1) = (δ ^ β) ^ ((2 * N0 + 1 : ℕ) : ℝ) := by
        exact (Real.rpow_natCast _ _).symm
      rw [h1, h_exp]
      have hδ_le : 0 ≤ δ := by linarith
      rw [← Real.rpow_mul hδ_le]
      rw [hβ_eq]
      have h2 : ((c * (N0 : ℝ) - α) / (2 * (N0 : ℝ) + 1)) * (2 * (N0 : ℝ) + 1) = c * (N0 : ℝ) - α := by
        have h_ne : (2 * (N0 : ℝ) + 1) ≠ 0 := by positivity
        field_simp [h_ne] <;> ring
      rw [h2]
    rw [h]
  have h_cancel1 : ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * (46656 : ENNReal) ^ N0 = 1 := by
    have h_pos : 0 ≤ (46656 : ℝ) := by norm_num
    have h1 : (46656 : ENNReal) ^ N0 = ENNReal.ofReal ((46656 : ℝ) ^ N0) := by
      rw [ENNReal.ofReal_pow h_pos N0] <;> simp
    rw [h1]
    have h2 : ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * ENNReal.ofReal ((46656 : ℝ) ^ N0) =
        ENNReal.ofReal (((46656 : ℝ)^ (-(N0 : ℝ))) * ((46656 : ℝ) ^ N0)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h2]
    have h3 : ((46656 : ℝ)^ (-(N0 : ℝ))) * ((46656 : ℝ) ^ N0) = 1 := by
      have h4 : ((46656 : ℝ)^ (-(N0 : ℝ))) = ((46656 : ℝ)^ (N0 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (by norm_num)]
      have h5 : (46656 : ℝ)^ (N0 : ℝ) = (46656 : ℝ) ^ N0 := by rw [Real.rpow_natCast]
      rw [h4, h5]
      field_simp
    rw [h3] <;> simp
  have h_cancel2 : ENNReal.ofReal ((2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) *
      ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) = 1 := by
    have h_pos : 0 ≤ (2 : ℝ) := by norm_num
    let e1 := -(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ)
    let e2 := (N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ)
    have h_e : e1 + e2 = 0 := by
      dsimp only [e1, e2] <;> ring
    have h_mul : ENNReal.ofReal ((2 : ℝ)^e1) * ENNReal.ofReal ((2 : ℝ)^e2) =
        ENNReal.ofReal (((2 : ℝ)^e1) * ((2 : ℝ)^e2)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h_mul]
    have h5 : ((2 : ℝ)^e1) * ((2 : ℝ)^e2) = (2 : ℝ)^(e1 + e2) := by
      have h6 : (2 : ℝ)^(e1 + e2) = (2 : ℝ)^e1 * (2 : ℝ)^e2 := by
        rw [Real.rpow_add (by norm_num)]
      exact h6.symm
    rw [h5, h_e] <;> simp
  have h10 : (C_ruz * ENNReal.ofReal (δ ^ β) * NB) ^ (2 * N0 + 1) ≤ M ^ (2 * N0 + 1) := by
    have h_mul_pow : (C_ruz * ENNReal.ofReal (δ ^ β) * NB) ^ (2 * N0 + 1) =
        C_ruz ^ (2 * N0 + 1) * (ENNReal.ofReal (δ ^ β)) ^ (2 * N0 + 1) * NB ^ (2 * N0 + 1) := by
      simp [mul_pow] <;> ring
    rw [h_mul_pow, h_rpowβ, h_C_ruz_pow]
    have h : ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * ENNReal.ofReal ((2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) *
        ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1) ≤ M ^ (2 * N0 + 1) := by
      calc ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * ENNReal.ofReal ((2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) *
          ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1)
        = ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * ENNReal.ofReal ((2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) *
          (ENNReal.ofReal (δ ^ (c * (N0 : ℝ) - α)) * NB ^ (2 * N0 + 1)) := by ring
      _ ≤ ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * ENNReal.ofReal ((2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) *
          ((46656 : ENNReal) ^ N0 * ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) * M ^ (2 * N0 + 1)) := by gcongr
      _ = (ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ))) * (46656 : ENNReal) ^ N0) *
          (ENNReal.ofReal ((2 : ℝ)^(-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ))) * ENNReal.ofReal ((2 : ℝ)^((N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ)))) *
          M ^ (2 * N0 + 1) := by ring
      _ = 1 * 1 * M ^ (2 * N0 + 1) := by rw [h_cancel1, h_cancel2] <;> ring
      _ = M ^ (2 * N0 + 1) := by ring
    exact h
  have h11 : C_ruz * ENNReal.ofReal (δ ^ β) * NB ≤ M := ennreal_pow_le_imp_le (by positivity) h10
  -- Absorb constant via ε
  have h_absorb : ENNReal.ofReal (δ ^ ε_abs) ≤ C_ruz := by
    have h_pos2 : 0 ≤ (46656 : ℝ)^ (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1)) *
        (2 : ℝ)^ (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1))) := by positivity
    have h_C_ruz_eq : C_ruz = ENNReal.ofReal ((46656 : ℝ)^ (-(N0 : ℝ)/(2 * (N0 : ℝ) + 1)) *
        (2 : ℝ)^ (-(N0 : ℝ) * ((N0 : ℝ) - 1) / (2 * κ * (2 * (N0 : ℝ) + 1)))) := by
      simp only [C_ruz]
      have h : ENNReal.ofReal C_ruz1 * ENNReal.ofReal C_ruz2 = ENNReal.ofReal (C_ruz1 * C_ruz2) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [h]
      <;> rfl
    rw [h_C_ruz_eq]
    exact ENNReal.ofReal_le_ofReal_iff h_pos2 |>.mpr hδ_absorb
  have h_final : ENNReal.ofReal (δ ^ (β + ε_abs)) * NB ≤ M := by
    have h_pos : 0 ≤ δ ^ (β + ε_abs) := by positivity
    have h_add : δ ^ (β + ε_abs) = δ ^ β * δ ^ ε_abs := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    rw [h_add]
    have h_mul : ENNReal.ofReal (δ ^ β * δ ^ ε_abs) =
        ENNReal.ofReal (δ ^ β) * ENNReal.ofReal (δ ^ ε_abs) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h_mul]
    calc ENNReal.ofReal (δ ^ β) * ENNReal.ofReal (δ ^ ε_abs) * NB
      = ENNReal.ofReal (δ ^ ε_abs) * ENNReal.ofReal (δ ^ β) * NB := by ring
    _ ≤ C_ruz * ENNReal.ofReal (δ ^ β) * NB := by
      have h6 : ENNReal.ofReal (δ ^ ε_abs) * (ENNReal.ofReal (δ ^ β) * NB) ≤
          C_ruz * (ENNReal.ofReal (δ ^ β) * NB) := by
        exact mul_le_mul_of_nonneg_right h_absorb (by positivity)
      simpa [mul_assoc] using h6
    _ ≤ M := h11
  -- Witness extraction
  have h_witness : ∃ (w0 : ℝ), (w0 = 1 ∨ w0 ∈ K) ∧
      Nreal δ (Set.image2 (· - ·) B (scaleSet w0 A)) = M := by
    by_cases h_le : D 0 ≤ Finset.univ.sup F
    · -- Case D 0 ≤ sup F, so M = sup F
      have h_sup : Finset.univ.sup F = M := by
        have h' : max (D 0) (Finset.univ.sup F) = M := rfl
        rw [max_eq_right h_le] at h'
        exact h'
      haveI : Nonempty (Fin N0) := Fin.pos_iff_nonempty.mp hN_pos
      have h_exists : ∃ (i : Fin N0), i ∈ Finset.univ ∧ Finset.univ.sup F = F i :=
        Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty F
      rcases h_exists with ⟨i, _, hi⟩
      refine ⟨w i, Or.inr (hw_in_K i), ?_⟩
      have hF_eq : F i = Nreal δ (Set.image2 (· - ·) B (scaleSet (w i) A)) := by
        simp [F] <;> rfl
      have h_goal : Nreal δ (Set.image2 (· - ·) B (scaleSet (w i) A)) = M := by
        calc Nreal δ (Set.image2 (· - ·) B (scaleSet (w i) A))
          = F i := hF_eq.symm
        _ = Finset.univ.sup F := hi.symm
        _ = M := h_sup
      exact h_goal
    · -- Case ¬(D 0 ≤ sup F), so sup F < D 0, hence M = D 0
      have h_lt : Finset.univ.sup F < D 0 := not_le.mp h_le
      have hM : M = D 0 := by
        have h_def : M = max (D 0) (Finset.univ.sup F) := rfl
        rw [h_def]
        rw [max_eq_left (le_of_lt h_lt)]
      refine ⟨1, Or.inl rfl, ?_⟩
      have hD0_eq : D 0 = Nreal δ (Set.image2 (· - ·) B (scaleSet (1 : ℝ) A)) := by
        dsimp only [D]
        have h_z0 : z 0 = 1 := z_zero
        rw [h_z0]
      have h_goal : Nreal δ (Set.image2 (· - ·) B (scaleSet (1 : ℝ) A)) = M := by
        rw [← hD0_eq, hM]
      exact h_goal
  rcases h_witness with ⟨w0, hw0_cases, hM_eq⟩
  refine ⟨w0, hw0_cases, ?_⟩
  have hβ_exp : β + ε_abs = c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) +
      α_in / (2 * (N0 : ℝ) + 1) + ε_abs := by
    have hβ : β = c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) - α / (2 * (N0 : ℝ) + 1) := by rfl
    have hα : α = -α_in := by rfl
    rw [hβ, hα] <;> ring
  have h_exp : δ ^ (β + ε_abs) = δ ^ (c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) +
      α_in / (2 * (N0 : ℝ) + 1) + ε_abs) := by
    rw [hβ_exp]
  have h_eq : ENNReal.ofReal (δ ^ (β + ε_abs)) = ENNReal.ofReal (δ ^ (c * (N0 : ℝ) / (2 * (N0 : ℝ) + 1) +
      α_in / (2 * (N0 : ℝ) + 1) + ε_abs)) := by
    rw [h_exp]
  have h_rhs : Nreal δ (Set.image2 (· - ·) (scaleSet t⁻¹ A) (scaleSet w0 A)) = M := by
    have hB : (scaleSet t⁻¹ A) = B := by rfl
    rw [hB]
    exact hM_eq
  rw [h_rhs]
  simpa [NB, h_exp] using h_final

/-! ## Step 12: Convert difference-set expansion to sumset expansion -/

/-- **Step 12**: Convert difference-set expansion to sumset expansion.

Case `w ∈ K` (main case):
  Let `B = t^{-1}A`, `β = (cN-α)/(2N+1)`.
  Given `N(B - wA) ≥ δ^β N(B)`.
  Scaling bound gives `N(wA) ≥ C * δ^c * N(B)`.
  Corollary 2.4: `N(B-wA) * N(B) * N(wA) ≤ 81 * N(B+wA)^3`.
  So `N(B+wA)^3 ≥ (C/81) * δ^{β+c} * N(B)^3`.
  Thus `N(B+wA) ≥ (C/81)^{1/3} * δ^{(β+c)/3} * N(B)`.
  Exponent check: `β + 4c < 0` (from `c = (1-s)/(400k(2N+1))`,
  `α = (1-s)/(24k)`), so `(β+c)/3 < -c`.
  For sufficiently small `δ`, `(C/81)^{1/3} * δ^{(β+c)/3} ≥ δ^{-c}`,
  giving the conclusion with `x = w`.

Case `w = 1`:
  Pick `w1 ∈ K`. Use Corollary 2.3 and sum-to-diff to find `x ∈ K`.
  (More involved — left as sorry.)

δ-smallness: The constant absorption requires δ below a threshold determined
by `C`, `β`, `c`. The strong ring theorem chooses δ₀ accordingly.
-/
lemma step12_diff_to_sum_correct
    {A K : Set ℝ}
    {δ δ₀ t c κ β_in : ℝ} (hδ_pos : 0 < δ) (ht_pos : 0 < t) (ht_le_one : t ≤ 1)
    (hc_pos : 0 < c) (hκ_pos : 0 < κ)
    {w : ℝ} (hw_cases : w = 1 ∨ w ∈ K)
    (h1_in_K : 1 ∈ K)
    (hβ_in_neg : β_in + 4 * c < 0)
    (h_expansion : ENNReal.ofReal (δ ^ β_in) *
      Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet t⁻¹ A) (scaleSet w A)))
    (hK_bounds : K ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1)
    (h_t_lower : δ ^ c ≤ t)
    (hδ_small : δ ≤ δ₀) (hδ₀_le_one : δ₀ ≤ 1)
    (hδ_absorb : δ ^ (-(β_in + 4 * c)) ≤
        (2 : ℝ)^(-(1/κ)) / 729)
    (hK_bdd : Bornology.IsBounded K) (hA_bdd : Bornology.IsBounded A)
    (hK_nonempty : K.Nonempty) (hA_nonempty : A.Nonempty) :
    ∃ (x : ℝ), x ∈ K ∧
      ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet t⁻¹ A) ≤
        Nreal δ (Set.image2 (fun a b => a + x * b) (scaleSet t⁻¹ A) A) := by
  have hδ_le_one : δ ≤ 1 := le_trans hδ_small hδ₀_le_one
  let B := scaleSet t⁻¹ A
  let β : ℝ := β_in
  have h_beta4c_neg : β + 4 * c < 0 := hβ_in_neg
  have h_w_in_K : w ∈ K := by
    rcases hw_cases with (h_w_eq_one | h)
    · rw [h_w_eq_one] <;> exact h1_in_K
    · exact h
  -- Case w ∈ K (now covers both branches since 1 ∈ K)
  have h_w_pos : 0 < w := by
    have h1 : (2 : ℝ)^(-(1/κ)) ≤ w := (hK_bounds h_w_in_K).1
    have h2 : 0 < (2 : ℝ)^(-(1/κ)) := by positivity
    linarith
  have h_wA_bdd : Bornology.IsBounded (scaleSet w A) :=
    scaleSet_bounded hA_bdd
  have hB_bdd : Bornology.IsBounded B :=
    scaleSet_bounded hA_bdd
  have hB_nonempty : B.Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    exact ⟨t⁻¹ * a, ⟨a, ha, rfl⟩⟩
  -- Scaling lower bound for N(wA)
  have h_w_le_one : w ≤ 1 := (hK_bounds h_w_in_K).2
  have h_scale1 : Nreal δ (scaleSet w A) = Nreal (δ / w) A :=
    covering_scaling hδ_pos h_w_pos hA_bdd
  have h_div_mul : (δ / w) * w = δ := by
    field_simp [h_w_pos.ne'] <;> ring
  have h_coarse_raw := covering_coarsening (div_pos hδ_pos h_w_pos) h_w_pos h_w_le_one hA_bdd
  have h_coarse : ENNReal.ofReal (w / 3) * Nreal δ A ≤ Nreal (δ / w) A := by
    have h : Nreal ((δ / w) * w) A = Nreal δ A := by rw [h_div_mul]
    rw [h] at h_coarse_raw
    exact h_coarse_raw
  have h_NA : ENNReal.ofReal (δ ^ c / 3) * Nreal δ B ≤ Nreal δ A :=
    covering_NA_ge_NB hδ_pos hc_pos ht_pos ht_le_one h_t_lower hA_bdd
  have h_N_wA : ENNReal.ofReal ((w / 9) * δ ^ c) * Nreal δ B ≤ Nreal δ (scaleSet w A) := by
    have h_mul : ENNReal.ofReal ((w / 9) * δ ^ c) =
        ENNReal.ofReal (w / 3) * ENNReal.ofReal (δ ^ c / 3) := by
      have h1 : 0 ≤ w / 3 := by positivity
      have h2 : 0 ≤ δ ^ c / 3 := by positivity
      rw [← ENNReal.ofReal_mul h1]
      have h3 : (w / 3) * (δ ^ c / 3) = (w / 9) * δ ^ c := by ring
      rw [h3]
    have h_first : ENNReal.ofReal ((w / 9) * δ ^ c) * Nreal δ B =
        ENNReal.ofReal (w / 3) * (ENNReal.ofReal (δ ^ c / 3) * Nreal δ B) := by
      rw [h_mul, mul_assoc]
    rw [h_first]
    calc ENNReal.ofReal (w / 3) * (ENNReal.ofReal (δ ^ c / 3) * Nreal δ B)
      ≤ ENNReal.ofReal (w / 3) * Nreal δ A := by gcongr
    _ ≤ Nreal (δ / w) A := h_coarse
    _ = Nreal δ (scaleSet w A) := h_scale1.symm
  -- Apply Corollary 2.4
  have h_wA_nonempty : (scaleSet w A).Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    exact ⟨w * a, ⟨a, ha, rfl⟩⟩
  have h_cor24 := ProductLikeIncidence.OSW.corollary2_4 hδ_pos hB_bdd h_wA_bdd hB_nonempty h_wA_nonempty
  -- Main conclusion (constant absorption)
  have h_final : ENNReal.ofReal (δ ^ (-c)) * Nreal δ B ≤
      Nreal δ (Set.image2 (· + ·) B (scaleSet w A)) := by
    -- Real inequality: δ^{-(β+4c)} ≤ w/729
    have h_w_lower : (2 : ℝ)^(-(1/κ)) ≤ w := (hK_bounds h_w_in_K).1
    have h_absorb1 : δ ^ (-(β + 4 * c)) ≤ (2 : ℝ)^(-(1/κ)) / 729 := hδ_absorb
    have h_absorb2 : δ ^ (-(β + 4 * c)) ≤ w / 729 := by
      calc δ ^ (-(β + 4 * c))
        ≤ (2 : ℝ)^(-(1/κ)) / 729 := h_absorb1
      _ ≤ w / 729 := by
        have h : (2 : ℝ)^(-(1/κ)) / 729 ≤ w / 729 := by gcongr
        exact h
    -- Convert to: δ^{-3c} ≤ (w/729) * δ^{β+c}
    have h_exp_eq : -(β + 4 * c) = -3 * c - (β + c) := by ring
    have h1 : δ ^ (-(β + 4 * c)) = δ ^ (-3 * c) / δ ^ (β + c) := by
      rw [h_exp_eq]
      have h2 : δ ^ (-3 * c - (β + c)) = δ ^ (-3 * c) / δ ^ (β + c) := by
        rw [Real.rpow_sub (by positivity)] <;> ring
      exact h2
    have h2 : δ ^ (-3 * c) / δ ^ (β + c) ≤ w / 729 := by
      rw [←h1]
      exact h_absorb2
    have hpos : 0 < δ ^ (β + c) := by positivity
    have h_eq_div : δ ^ (-3 * c) = (δ ^ (-3 * c) / δ ^ (β + c)) * δ ^ (β + c) := by
      have h : (δ ^ (-3 * c) / δ ^ (β + c)) * δ ^ (β + c) = δ ^ (-3 * c) := by
        rw [div_mul_cancel₀ _ hpos.ne']
      exact h.symm
    have h_real1 : δ ^ (-3 * c) ≤ (w / 729) * δ ^ (β + c) := by
      calc δ ^ (-3 * c)
        = (δ ^ (-3 * c) / δ ^ (β + c)) * δ ^ (β + c) := h_eq_div
      _ ≤ (w / 729) * δ ^ (β + c) := by gcongr
    -- ENNReal version
    have h_pos1 : 0 ≤ δ ^ (-3 * c) := by positivity
    have h_pos2 : 0 ≤ w / 729 := by positivity
    have h_pos3 : 0 ≤ δ ^ (β + c) := by positivity
    have h_mul : ENNReal.ofReal ((w / 729) * δ ^ (β + c)) =
        ENNReal.ofReal (w / 729) * ENNReal.ofReal (δ ^ (β + c)) := by
      rw [← ENNReal.ofReal_mul h_pos2]
    have h_ennreal1 : ENNReal.ofReal (δ ^ (-3 * c)) ≤
        ENNReal.ofReal (w / 729) * ENNReal.ofReal (δ ^ (β + c)) := by
      have h_step : ENNReal.ofReal (δ ^ (-3 * c)) ≤
          ENNReal.ofReal ((w / 729) * δ ^ (β + c)) := by
        exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h_real1
      rw [h_mul] at h_step
      exact h_step
    -- Multiply by N(B)^3
    let NB := Nreal δ B
    have h4 : (ENNReal.ofReal (δ ^ (-c)) * NB) ^ 3 =
        ENNReal.ofReal (δ ^ (-3 * c)) * NB ^ 3 := by
      have h5 : 0 ≤ δ ^ (-c) := by positivity
      have h_pow : (ENNReal.ofReal (δ ^ (-c))) ^ 3 = ENNReal.ofReal (δ ^ (-3 * c)) := by
        have h_eq1 : (ENNReal.ofReal (δ ^ (-c))) ^ 3 = ENNReal.ofReal ((δ ^ (-c)) ^ 3) := by
          rw [ENNReal.ofReal_pow h5]
        rw [h_eq1]
        have h_posδ : 0 < δ := hδ_pos
        have h1 : (δ ^ (-c)) ^ 2 = δ ^ (-2 * c) := by
          calc (δ ^ (-c)) ^ 2
            = δ ^ (-c) * δ ^ (-c) := by ring
          _ = δ ^ (-c + -c) := by rw [← Real.rpow_add h_posδ]
          _ = δ ^ (-2 * c) := by ring_nf
        have h_eq2 : (δ ^ (-c)) ^ 3 = δ ^ (-3 * c) := by
          calc (δ ^ (-c)) ^ 3
            = (δ ^ (-c)) ^ 2 * δ ^ (-c) := by ring
          _ = δ ^ (-2 * c) * δ ^ (-c) := by rw [h1]
          _ = δ ^ (-2 * c + -c) := by rw [← Real.rpow_add h_posδ]
          _ = δ ^ (-3 * c) := by ring_nf
        rw [h_eq2]
      rw [mul_pow, h_pow]
    have h3 : (ENNReal.ofReal (δ ^ (-c)) * NB) ^ 3 ≤
        (ENNReal.ofReal (w / 729) * ENNReal.ofReal (δ ^ (β + c))) * NB ^ 3 := by
      rw [h4]
      gcongr
    -- From Corollary 2.4: (w/9) * δ^{β+c} * NB^3 ≤ 81 * N(B+wA)^3
    have h_cor24' : Nreal δ (Set.image2 (· - ·) B (scaleSet w A)) * NB * Nreal δ (scaleSet w A) ≤
        81 * (Nreal δ (Set.image2 (· + ·) B (scaleSet w A))) ^ 3 := by
      let S := Nreal δ (Set.image2 (· + ·) B (scaleSet w A))
      have h_expand : 81 * S ^ 3 = 81 * S * S * S := by
        simp [pow_succ, mul_assoc]
        <;> ring
      rw [h_expand]
      exact h_cor24
    have h6 : ENNReal.ofReal (δ ^ β) * NB ≤
        Nreal δ (Set.image2 (· - ·) B (scaleSet w A)) := h_expansion
    have h7 : ENNReal.ofReal ((w / 9) * δ ^ c) * NB ≤ Nreal δ (scaleSet w A) := h_N_wA
    have h8 : (ENNReal.ofReal (δ ^ β) * NB) * NB * (ENNReal.ofReal ((w / 9) * δ ^ c) * NB) ≤
        (Nreal δ (Set.image2 (· - ·) B (scaleSet w A))) * NB * (Nreal δ (scaleSet w A)) := by
      gcongr <;> assumption
    have h_pos1 : 0 ≤ δ ^ β := by positivity
    have h_pos2 : 0 ≤ (w / 9) * δ ^ c := by positivity
    have h_mul1 : ENNReal.ofReal (δ ^ β) * ENNReal.ofReal ((w / 9) * δ ^ c) =
        ENNReal.ofReal ((w / 9) * δ ^ (β + c)) := by
      rw [← ENNReal.ofReal_mul h_pos1]
      have h_rpow : δ ^ β * δ ^ c = δ ^ (β + c) := by
        rw [← Real.rpow_add hδ_pos] <;> ring
      have h : δ ^ β * ((w / 9) * δ ^ c) = (w / 9) * (δ ^ β * δ ^ c) := by ring
      rw [h, h_rpow]
      <;> ring
    have h_rearrange : (ENNReal.ofReal (δ ^ β) * NB) * NB * (ENNReal.ofReal ((w / 9) * δ ^ c) * NB) =
        ENNReal.ofReal (δ ^ β) * ENNReal.ofReal ((w / 9) * δ ^ c) * NB ^ 3 := by
      let a := ENNReal.ofReal (δ ^ β)
      let b := NB
      let c' := ENNReal.ofReal ((w / 9) * δ ^ c)
      have h : (a * b) * b * (c' * b) = a * c' * b ^ 3 := by
        simp [pow_succ, mul_assoc]
        <;> ac_rfl
      exact h
    have h9 : (ENNReal.ofReal (δ ^ β) * NB) * NB * (ENNReal.ofReal ((w / 9) * δ ^ c) * NB) =
        ENNReal.ofReal ((w / 9) * δ ^ (β + c)) * NB ^ 3 := by
      rw [h_rearrange, h_mul1]
    have h10 : ENNReal.ofReal ((w / 9) * δ ^ (β + c)) * NB ^ 3 ≤
        81 * (Nreal δ (Set.image2 (· + ·) B (scaleSet w A))) ^ 3 := by
      rw [←h9]
      exact h8.trans h_cor24'
    have h_pos4 : 0 ≤ (w / 729) * δ ^ (β + c) := by positivity
    have h_div729 : ENNReal.ofReal ((w / 729) * δ ^ (β + c)) =
        ENNReal.ofReal (1 / 81) * ENNReal.ofReal ((w / 9) * δ ^ (β + c)) := by
      have h_pos5 : 0 ≤ (1 / 81 : ℝ) := by positivity
      rw [← ENNReal.ofReal_mul h_pos5]
      have h : (1 / 81 : ℝ) * ((w / 9) * δ ^ (β + c)) = (w / 729) * δ ^ (β + c) := by ring
      rw [h]
    have h5 : (ENNReal.ofReal (w / 729) * ENNReal.ofReal (δ ^ (β + c))) * NB ^ 3 ≤
        (Nreal δ (Set.image2 (· + ·) B (scaleSet w A))) ^ 3 := by
      let S := Nreal δ (Set.image2 (· + ·) B (scaleSet w A))
      have h_combine : ENNReal.ofReal (w / 729) * ENNReal.ofReal (δ ^ (β + c)) =
          ENNReal.ofReal ((w / 729) * δ ^ (β + c)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have h_main : ENNReal.ofReal (1 / 81) * (ENNReal.ofReal ((w / 9) * δ ^ (β + c)) * NB ^ 3) ≤
          ENNReal.ofReal (1 / 81) * (81 * S ^ 3) := by gcongr
      have h_assoc : ENNReal.ofReal (1 / 81) * (ENNReal.ofReal ((w / 9) * δ ^ (β + c)) * NB ^ 3) =
          (ENNReal.ofReal (1 / 81) * ENNReal.ofReal ((w / 9) * δ ^ (β + c))) * NB ^ 3 := by
        rw [mul_assoc]
      have h_final_eq : ENNReal.ofReal (1 / 81) * (81 * S ^ 3) = S ^ 3 := by
        have h2 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by
          norm_cast
        have h1 : ENNReal.ofReal (1 / 81) * (81 : ENNReal) = 1 := by
          rw [h2]
          have h3 : ENNReal.ofReal (1 / 81) * ENNReal.ofReal (81 : ℝ) =
              ENNReal.ofReal ((1 / 81 : ℝ) * (81 : ℝ)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
          rw [h3]
          have h4 : (1 / 81 : ℝ) * (81 : ℝ) = 1 := by norm_num
          rw [h4]
          <;> simp
        calc ENNReal.ofReal (1 / 81) * (81 * S ^ 3)
          = (ENNReal.ofReal (1 / 81) * (81 : ENNReal)) * S ^ 3 := by rw [mul_assoc]
        _ = (1 : ENNReal) * S ^ 3 := by rw [h1]
        _ = S ^ 3 := by simp
      rw [h_combine, h_div729]
      rw [←h_assoc]
      exact h_main.trans_eq h_final_eq
    -- Combine: (δ^{-c} * NB)^3 ≤ N(B+wA)^3, then take cube root
    let a := ENNReal.ofReal (δ ^ (-c)) * NB
    let b := Nreal δ (Set.image2 (· + ·) B (scaleSet w A))
    have h10 : a ^ 3 ≤ b ^ 3 := by
      calc a ^ 3
        ≤ (ENNReal.ofReal (w / 729) * ENNReal.ofReal (δ ^ (β + c))) * NB ^ 3 := h3
      _ ≤ b ^ 3 := h5
    have h11 : a ≤ b := by
      by_cases hb : b = ⊤
      · rw [hb]
        exact le_top
      · by_cases ha : a = ⊤
        · have h_a3 : a ^ 3 = ⊤ := by rw [ha] <;> simp
          rw [h_a3] at h10
          have h_b3 : b ^ 3 = ⊤ := by simpa using h10
          have h : b ^ 3 < ⊤ := pow_lt_top (lt_top_iff_ne_top.mpr hb)
          rw [h_b3] at h
          exact False.elim (not_top_lt h)
        · have h_a3_ne_top : a ^ 3 ≠ ⊤ := pow_ne_top ha
          have h_b3_ne_top : b ^ 3 ≠ ⊤ := pow_ne_top hb
          have h_real_ineq : (a ^ 3).toReal ≤ (b ^ 3).toReal :=
            (ENNReal.toReal_le_toReal h_a3_ne_top h_b3_ne_top).mpr h10
          have h_to_real3 : (a ^ 3).toReal = a.toReal ^ 3 := by simp [ENNReal.toReal_pow]
          have h_to_real3' : (b ^ 3).toReal = b.toReal ^ 3 := by simp [ENNReal.toReal_pow]
          rw [h_to_real3, h_to_real3'] at h_real_ineq
          have h_real_le : a.toReal ≤ b.toReal := by
            let x := a.toReal
            let y := b.toReal
            have h_ineq : x ^ 3 ≤ y ^ 3 := h_real_ineq
            by_contra h
            have h' : y < x := by linarith
            have h_pos1 : 0 < x - y := by linarith
            have h_nonneg : 0 ≤ x^2 + x*y + y^2 := by
              have h_eq : x^2 + x*y + y^2 = (x + y/2)^2 + 3*y^2/4 := by ring
              rw [h_eq] <;> positivity
            have h_pos2 : 0 < x^2 + x*y + y^2 := by
              by_contra h2
              have h_le : x^2 + x*y + y^2 ≤ 0 := by linarith
              have h_eq0 : x^2 + x*y + y^2 = 0 := by linarith [h_nonneg]
              have h_sum : (x+y)^2 + x^2 + y^2 = 0 := by
                calc (x+y)^2 + x^2 + y^2
                  = 2 * (x^2 + x*y + y^2) := by ring
                _ = 0 := by rw [h_eq0] <;> ring
              have h_x2 : x^2 = 0 := by
                have h1 : (x+y)^2 ≥ 0 := by positivity
                have h2 : y^2 ≥ 0 := by positivity
                have h3 : x^2 ≤ 0 := by linarith [h_sum]
                have h4 : x^2 ≥ 0 := by positivity
                exact le_antisymm h3 h4
              have h_y2 : y^2 = 0 := by
                have h1 : (x+y)^2 ≥ 0 := by positivity
                have h2 : x^2 ≥ 0 := by positivity
                have h3 : y^2 ≤ 0 := by linarith [h_sum]
                have h4 : y^2 ≥ 0 := by positivity
                exact le_antisymm h3 h4
              have hx : x = 0 := by simpa using h_x2
              have hy : y = 0 := by simpa using h_y2
              rw [hx, hy] at h' <;> linarith
            have h6 : x^3 - y^3 = (x - y) * (x^2 + x*y + y^2) := by ring
            have h7 : 0 < x^3 - y^3 := by
              rw [h6] <;> exact mul_pos h_pos1 h_pos2
            have h9 : x^3 - y^3 ≤ 0 := by linarith [h_ineq]
            exact False.elim (not_le.mpr h7 h9)
          exact (ENNReal.toReal_le_toReal ha hb).mp h_real_le
    exact h11
  refine ⟨w, h_w_in_K, ?_⟩
  have h_set_eq : Set.image2 (fun a b => a + w * b) B A =
      Set.image2 (· + ·) B (scaleSet w A) := by
    ext z
    simp only [Set.mem_image2, scaleSet]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, w * b, ⟨b, hb, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  rw [h_set_eq]
  exact h_final

/-! ## Constant absorption for dilation bounds -/

/-- Absorb a positive real constant `C` into the exponent.

    If `δ^{-c} * X ≤ C * Y` and `δ^ε ≤ 1/C`, then
    `δ^{-(c-ε)} * X ≤ Y`.

    This is used to absorb the `2 * C_κ` factor from `covering_dilation_bounds`
    when translating expansion from the normalized (dilated) world back to the
    original world.  Choose `ε > 0` small and `δ₀` so that
    `δ^ε ≤ 1/(2*C_κ)` for all `δ ≤ δ₀`. -/
lemma ennreal_absorb_constant {δ c ε C : ℝ} (hδ_pos : 0 < δ)
    (hc_pos : 0 < c) (hε_pos : 0 < ε) (hε_lt_c : ε < c)
    (hC_pos : 0 < C) (hδ_absorb : δ ^ ε ≤ C⁻¹)
    {X Y : ENNReal}
    (h : ENNReal.ofReal (δ ^ (-c)) * X ≤ ENNReal.ofReal C * Y) :
    ENNReal.ofReal (δ ^ (-(c - ε))) * X ≤ Y := by
  have h1 : 0 ≤ δ ^ (-c) := by positivity
  have h_csub_pos : 0 < c - ε := by linarith
  have h4 : δ ^ (-(c - ε)) = δ ^ (-c) * δ ^ ε := by
    have h5 : -(c - ε) = -c + ε := by ring
    rw [h5, ← Real.rpow_add hδ_pos] <;> ring
  have h6 : ENNReal.ofReal (δ ^ (-(c - ε))) ≤
      ENNReal.ofReal (δ ^ (-c)) * ENNReal.ofReal (C⁻¹) := by
    rw [h4]
    have h7 : ENNReal.ofReal (δ ^ (-c) * δ ^ ε) =
        ENNReal.ofReal (δ ^ (-c)) * ENNReal.ofReal (δ ^ ε) := by
      rw [← ENNReal.ofReal_mul h1]
    rw [h7]
    have h_ineq : ENNReal.ofReal (δ ^ ε) ≤ ENNReal.ofReal (C⁻¹) :=
      ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr hδ_absorb
    exact mul_le_mul_of_nonneg_left h_ineq (by positivity)
  have h8 : ENNReal.ofReal (C⁻¹) * ENNReal.ofReal C = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have h9 : C⁻¹ * C = 1 := by
      field_simp [hC_pos.ne'] <;> ring
    rw [h9] <;> simp
  calc
    ENNReal.ofReal (δ ^ (-(c - ε))) * X
      ≤ (ENNReal.ofReal (δ ^ (-c)) * ENNReal.ofReal (C⁻¹)) * X := by gcongr
    _ = ENNReal.ofReal (C⁻¹) * (ENNReal.ofReal (δ ^ (-c)) * X) := by ring
    _ ≤ ENNReal.ofReal (C⁻¹) * (ENNReal.ofReal C * Y) := by gcongr
    _ = (ENNReal.ofReal (C⁻¹) * ENNReal.ofReal C) * Y := by ring
    _ = 1 * Y := by rw [h8]
    _ = Y := by simp

/-- **Covering-number dilation bounds**.

For `b ∈ [2^{-1/κ}, 1]`, scaling a bounded set `S` by `b⁻¹` gives:
- `N(b⁻¹ S) ≤ C_κ · N(S)` where `C_κ = ⌈2^{1/κ}⌉ + 2`
- `N(S) ≤ 2 · N(b⁻¹ S)`

These follow from `covering_scale_down_ge` and `covering_scale_down_le_two`
applied with scaling factor `b` to the set `b⁻¹ S`. -/
lemma covering_dilation_bounds {δ κ : ℝ} (hδ : 0 < δ) (hκ_pos : 0 < κ)
    {b : ℝ} (hb_pos : 0 < b) (hb_le_one : b ≤ 1)
    (hb_ge_a : (2 : ℝ)^(-(1/κ)) ≤ b)
    {S : Set ℝ} (hS : Bornology.IsBounded S) :
    Nreal δ (scaleSet b⁻¹ S) ≤ ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal)) * Nreal δ S ∧
    Nreal δ S ≤ 2 * Nreal δ (scaleSet b⁻¹ S) := by
  let a : ℝ := (2 : ℝ)^(-(1/κ))
  have ha_pos : 0 < a := by positivity
  have h1a : 1 / a = (2 : ℝ)^(1/κ) := by
    have h_pos2 : 0 < (2 : ℝ) := by positivity
    have h : a * (2 : ℝ)^(1/κ) = 1 := by
      rw [show a = (2 : ℝ)^(-(1/κ)) from rfl]
      rw [← Real.rpow_add h_pos2]
      have h2 : (-(1/κ)) + (1/κ) = 0 := by ring
      rw [h2, Real.rpow_zero]
    have h_a_ne_zero : a ≠ 0 := ha_pos.ne'
    have h9 : a * (1 / a) = 1 := by field_simp [h_a_ne_zero]
    have h10 : a * (1 / a) = a * ((2 : ℝ)^(1/κ)) := by
      exact Eq.trans h9 h.symm
    exact (mul_right_inj' h_a_ne_zero).mp h10
  let C_κ : ENNReal := (Nat.ceil (1 / a) + 2 : ENNReal)
  have hC_κ_eq : C_κ = (Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal) := by
    have h4 : (Nat.ceil (1 / a) : ENNReal) = (Nat.ceil ((2 : ℝ)^(1/κ)) : ENNReal) := by
      congr <;> exact h1a
    have h5 : C_κ = (Nat.ceil (1 / a) + 2 : ENNReal) := by rfl
    rw [h5]
    have h6 : ((Nat.ceil (1 / a) + 2 : ENNReal)) = ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal)) := by
      rw [h4]
    exact h6
  have h_bS_bdd : Bornology.IsBounded (scaleSet b⁻¹ S) := scaleSet_bounded hS
  -- Upper bound: N(b⁻¹ S) ≤ C_κ * N(S)
  have h_upper : Nreal δ (scaleSet b⁻¹ S) ≤ C_κ * Nreal δ (scaleSet b (scaleSet b⁻¹ S)) :=
    covering_scale_down_ge (hδ := hδ) (hc_pos := ha_pos) (hr_ge_c := hb_ge_a)
      (hr_le_one := hb_le_one) (hS := h_bS_bdd)
  have h_compose : scaleSet b (scaleSet b⁻¹ S) = S := by
    ext x
    simp only [scaleSet, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      have h : b * (b⁻¹ * z) = z := by field_simp [hb_pos.ne'] <;> ring
      rw [h] <;> exact hz
    · intro hx
      refine ⟨b⁻¹ * x, ⟨x, hx, rfl⟩, ?_⟩
      field_simp [hb_pos.ne'] <;> ring
  rw [h_compose] at h_upper
  -- Lower bound: N(S) ≤ 2 * N(b⁻¹ S)
  have h_lower : Nreal δ (scaleSet b (scaleSet b⁻¹ S)) ≤ 2 * Nreal δ (scaleSet b⁻¹ S) :=
    covering_scale_down_le_two (hδ := hδ) (hr_pos := hb_pos) (hr_le_one := hb_le_one)
      (hS := h_bS_bdd)
  rw [h_compose] at h_lower
  have h_upper' : Nreal δ (scaleSet b⁻¹ S) ≤
      ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal)) * Nreal δ S := by
    have h3 : C_κ = ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal)) := by
      simp [C_κ, h1a]
    rw [h3] at h_upper
    exact h_upper
  exact ⟨h_upper', h_lower⟩

/-- **Translate expansion inequality back from normalized world**.

Given `δ^{-c} · N(b⁻¹ T) ≤ N(b⁻¹ S)`, derive
`δ^{-c} · N(T) ≤ 2·C_κ · N(S)`, where `C_κ = ⌈2^{1/κ}⌉ + 2`.

Uses `covering_dilation_bounds` for the two-sided covering estimates. -/
lemma expansion_translate_back {δ κ c : ℝ} (hδ : 0 < δ) (hκ_pos : 0 < κ)
    (hc_pos : 0 < c)
    {b : ℝ} (hb_pos : 0 < b) (hb_le_one : b ≤ 1)
    (hb_ge_a : (2 : ℝ)^(-(1/κ)) ≤ b)
    {S T : Set ℝ} (hS : Bornology.IsBounded S) (hT : Bornology.IsBounded T)
    (h_exp : ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet b⁻¹ T) ≤
             Nreal δ (scaleSet b⁻¹ S)) :
    ENNReal.ofReal (δ ^ (-c)) * Nreal δ T ≤
      (2 * ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal))) * Nreal δ S := by
  let C_κ : ENNReal := (Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal)
  have h_bounds_S := covering_dilation_bounds hδ hκ_pos hb_pos hb_le_one hb_ge_a hS
  have h_bounds_T := covering_dilation_bounds hδ hκ_pos hb_pos hb_le_one hb_ge_a hT
  have h1 : Nreal δ (scaleSet b⁻¹ S) ≤ C_κ * Nreal δ S := h_bounds_S.1
  have h2 : Nreal δ T ≤ 2 * Nreal δ (scaleSet b⁻¹ T) := h_bounds_T.2
  calc
    ENNReal.ofReal (δ ^ (-c)) * Nreal δ T
      ≤ ENNReal.ofReal (δ ^ (-c)) * (2 * Nreal δ (scaleSet b⁻¹ T)) := by gcongr
    _ = 2 * (ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet b⁻¹ T)) := by ring
    _ ≤ 2 * Nreal δ (scaleSet b⁻¹ S) := by gcongr
    _ ≤ 2 * (C_κ * Nreal δ S) := by gcongr
    _ = (2 * C_κ) * Nreal δ S := by ring

/-- **Step 12 with normalization translation**.

Given a normalization scaling `b` (from `normalize_support_contains_one`),
run the diff-to-sum argument in the normalized world (`K' = K/b`, `t' = bt`)
and translate the expansion back to the original sets using
`expansion_translate_back`.

The constant loss `2 * C_κ` depends only on `κ` and can be absorbed into `δ₀`
using `ennreal_absorb_constant`. -/
lemma step12_diff_to_sum_normalized
    {A K : Set ℝ}
    {δ δ₀ t c κ β_in : ℝ} (hδ_pos : 0 < δ) (ht_pos : 0 < t) (ht_le_one : t ≤ 1)
    (hc_pos : 0 < c) (hκ_pos : 0 < κ)
    {b : ℝ} (hb_pos : 0 < b) (hb_le_one : b ≤ 1)
    (hb_ge_a : (2 : ℝ)^(-(1/κ)) ≤ b)
    (hb_in_K : b ∈ K) (hb_max : ∀ x ∈ K, x ≤ b)
    {w : ℝ} (hw_cases : w = 1 ∨ w ∈ scaleSet b⁻¹ K)
    (hβ_in_neg : β_in + 4 * c < 0)
    (h_expansion : ENNReal.ofReal (δ ^ β_in) *
      Nreal δ (scaleSet (b * t)⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet (b * t)⁻¹ A) (scaleSet w A)))
    (hK_bounds : K ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1)
    (h_t_lower : δ ^ c ≤ b * t)
    (hδ_small : δ ≤ δ₀) (hδ₀_le_one : δ₀ ≤ 1)
    (hδ_absorb : δ ^ (-(β_in + 4 * c)) ≤
        (2 : ℝ)^(-(1/κ)) / 729)
    (hK_bdd : Bornology.IsBounded K) (hA_bdd : Bornology.IsBounded A)
    (hK_nonempty : K.Nonempty) (hA_nonempty : A.Nonempty) :
    ∃ (x : ℝ), x ∈ K ∧
      ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet t⁻¹ A) ≤
      (2 * ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal))) *
        Nreal δ (Set.image2 (fun a b => a + x * b) (scaleSet t⁻¹ A) A) := by
  let K' : Set ℝ := scaleSet b⁻¹ K
  let t' : ℝ := b * t
  let B : Set ℝ := scaleSet t⁻¹ A
  let B' : Set ℝ := scaleSet (t')⁻¹ A
  -- 1 ∈ K' because b ∈ K and b/b = 1
  have h1_in_K' : 1 ∈ K' := by
    refine ⟨b, hb_in_K, ?_⟩
    field_simp [hb_pos.ne'] <;> ring
  -- K' ⊆ [2^{-1/κ}, 1]
  have hK'_bounds : K' ⊆ Set.Icc ((2 : ℝ)^(-(1/κ))) 1 := by
    intro y hy
    rcases hy with ⟨x, hxK, rfl⟩
    have hxa : (2 : ℝ)^(-(1/κ)) ≤ x := (hK_bounds hxK).1
    have hxb : x ≤ b := hb_max x hxK
    have h_div_eq : b⁻¹ * x = x / b := by
      field_simp [hb_pos.ne'] <;> ring
    have h1 : (2 : ℝ)^(-(1/κ)) ≤ b⁻¹ * x := by
      rw [h_div_eq]
      have h2 : (2 : ℝ)^(-(1/κ)) / b ≤ x / b := by gcongr
      have h3 : (2 : ℝ)^(-(1/κ)) ≤ (2 : ℝ)^(-(1/κ)) / b := by
        have h4 : 0 < (2 : ℝ)^(-(1/κ)) := by positivity
        calc (2 : ℝ)^(-(1/κ))
          ≤ (2 : ℝ)^(-(1/κ)) / 1 := by simp
        _ ≤ (2 : ℝ)^(-(1/κ)) / b := by gcongr
      linarith
    have h4 : b⁻¹ * x ≤ 1 := by
      rw [h_div_eq]
      apply (div_le_one hb_pos).mpr
      exact hxb
    exact ⟨h1, h4⟩
  have hK'_bdd : Bornology.IsBounded K' := scaleSet_bounded hK_bdd
  have hK'_nonempty : K'.Nonempty := ⟨1, h1_in_K'⟩
  have ht'_pos : 0 < t' := mul_pos hb_pos ht_pos
  have ht'_le_one : t' ≤ 1 := by
    calc t' = b * t := by rfl
      _ ≤ 1 * 1 := by gcongr <;> linarith
      _ = 1 := by ring
  -- B' = b⁻¹ B
  have hB'_eq : B' = scaleSet b⁻¹ B := by
    ext z
    simp only [B', B, scaleSet, Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨t⁻¹ * a, ⟨a, ha, rfl⟩, ?_⟩
      field_simp [hb_pos.ne'] <;> ring
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      field_simp [hb_pos.ne'] <;> ring
  -- Call step12 in normalized world
  have h_step12 := step12_diff_to_sum_correct
    (hδ_pos := hδ_pos) (ht_pos := ht'_pos) (ht_le_one := ht'_le_one)
    (hc_pos := hc_pos) (hκ_pos := hκ_pos)
    (hw_cases := hw_cases) (h1_in_K := h1_in_K')
    (hβ_in_neg := hβ_in_neg)
    (h_expansion := h_expansion) (hK_bounds := hK'_bounds)
    (h_t_lower := h_t_lower) (hδ_small := hδ_small) (hδ₀_le_one := hδ₀_le_one)
    (hδ_absorb := hδ_absorb) (hK_bdd := hK'_bdd) (hA_bdd := hA_bdd)
    (hK_nonempty := hK'_nonempty) (hA_nonempty := hA_nonempty)
  rcases h_step12 with ⟨x', hx'_in_K', h_exp'⟩
  -- x' ∈ K' means x' = b⁻¹ * x for some x ∈ K
  rcases hx'_in_K' with ⟨x, hx_in_K, hx'_eq⟩
  -- S = B + xA, T = B; then b⁻¹S = B' + x'A
  let S : Set ℝ := Set.image2 (fun a b => a + x * b) B A
  let T : Set ℝ := B
  have hB_bdd : Bornology.IsBounded B := scaleSet_bounded hA_bdd
  have hS_eq : S = B + scaleSet x A := by
    ext z
    simp only [S, Set.mem_image2, scaleSet, Set.mem_add]
    constructor
    · rintro ⟨a, ha, c, hc, rfl⟩
      exact ⟨a, ha, x * c, ⟨c, hc, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨a, ha, c, hc, rfl⟩
  have hS_bdd : Bornology.IsBounded S := by
    rw [hS_eq]
    exact hB_bdd.add (scaleSet_bounded hA_bdd)
  have hT_bdd : Bornology.IsBounded T := hB_bdd
  have h_scale_S : scaleSet b⁻¹ S = Set.image2 (fun a' c => a' + x' * c) B' A := by
    apply Set.ext
    intro z
    constructor
    · intro hz
      rcases hz with ⟨y, hyS, rfl⟩
      rcases hyS with ⟨a, haB, c, hcA, rfl⟩
      have ha'_in_B' : b⁻¹ * a ∈ B' := by
        rw [hB'_eq]
        exact ⟨a, haB, by field_simp [hb_pos.ne'] <;> ring⟩
      have h_eq1 : b⁻¹ * (a + x * c) = b⁻¹ * a + x' * c := by
        have h2 : x' = b⁻¹ * x := Eq.symm hx'_eq
        rw [h2]
        field_simp [hb_pos.ne'] <;> ring
      exact ⟨b⁻¹ * a, ha'_in_B', c, hcA, Eq.symm h_eq1⟩
    · intro hz
      rcases hz with ⟨a', ha'_in_B', c, hcA, rfl⟩
      rw [hB'_eq] at ha'_in_B'
      rcases ha'_in_B' with ⟨a, haB, h_eq : b⁻¹ * a = a'⟩
      have h_eq2 : b⁻¹ * (a + x * c) = a' + x' * c := by
        have h2 : x' = b⁻¹ * x := Eq.symm hx'_eq
        calc
          b⁻¹ * (a + x * c) = b⁻¹ * a + b⁻¹ * x * c := by field_simp [hb_pos.ne'] <;> ring
          _ = a' + b⁻¹ * x * c := by rw [h_eq]
          _ = a' + x' * c := by rw [←h2] <;> ring
      exact ⟨a + x * c, ⟨a, haB, c, hcA, rfl⟩, h_eq2⟩
  have h_scale_T : scaleSet b⁻¹ T = B' := by
    rw [hB'_eq] <;> rfl
  have h_exp'' : ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet b⁻¹ T) ≤
      Nreal δ (scaleSet b⁻¹ S) := by
    rw [h_scale_T, h_scale_S]
    exact h_exp'
  have h_translate := expansion_translate_back
    (hδ := hδ_pos) (hκ_pos := hκ_pos) (hc_pos := hc_pos)
    (hb_pos := hb_pos) (hb_le_one := hb_le_one) (hb_ge_a := hb_ge_a)
    (hS := hS_bdd) (hT := hT_bdd) (h_exp := h_exp'')
  exact ⟨x, hx_in_K, h_translate⟩

end

end WeakTwoEndsSumProduct

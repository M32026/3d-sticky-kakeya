module

/-
# Step 6-8: Multi-set Plünnecke-Ruzsa Extraction (SUM conclusion)

Proves `step6_8_multiset_pr` with SUM conclusion.

## Proof route

Apply multi-set PR directly to the family `{x_i A}_{i=1}^m`:
1. Let X = t^{-1}A, Y_i = x_i A.
2. weightedSumset = familySum Y.
3. If N(X + Y_i) ≤ α·N(X) for all i, multi-set PR gives
   N(weightedSumset) ≤ m·(2mα)^m·N(X).
4. Bound N(X) ≤ 3·δ^{-(1+3s)/4}.
5. Exponent gap with α = δ^{-(1-s)/(24mN0)} and εm < (1-s)/2 ensures
   the PR bound is strictly less than δ^{-1+εm} for small δ.
6. Contrapositive gives some i with N(X + x_i A) ≥ α·N(X).
7. x_i ∈ expansionSet K N0 by hypothesis.

## Dependencies

- `MyLeanRepo.MultiSetPR` — `discretized_multiset_pr_general`
- `MyLeanRepo.StrongRingHelpers` — covering scaling/coarsening lemmas
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.MultiSetPR
public import MyLeanRepo.StrongRingHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators Pointwise

namespace WeakTwoEndsSumProduct

noncomputable section

/-- Polynomial constant for the step6 multi-set PR contrapositive. -/
def step6_full_C (m N0 : ℕ) (κ : ℝ) : ℝ :=
  let k : ℕ := 2 * m * N0
  let C_p : ℝ := (2 : ℝ) ^ ((N0 : ℝ) / κ) + 2
  (k : ℝ) * (486 * (k : ℝ) * C_p) ^ k

/-- N-fold product set A^(N). -/
def productSetN (A : Set ℝ) (N : ℕ) : Set ℝ :=
  {x | ∃ (f : Fin N → ℝ), (∀ i, f i ∈ A) ∧ x = ∏ i : Fin N, f i}

/-- N-fold sumset N·A. -/
def sumSetN (A : Set ℝ) : ℕ → Set ℝ
  | 0 => {0}
  | n + 1 => Set.image2 (· + ·) A (sumSetN A n)

/-- Weighted sumset x₁·A + ... + xₘ·A. -/
def weightedSumset {m : ℕ} (x : Fin m → ℝ) (A : Set ℝ) : Set ℝ :=
  {z | ∃ (a : Fin m → ℝ), (∀ i, a i ∈ A) ∧ z = ∑ i : Fin m, x i * a i}

/-- Expansion set X = N·K^(N) - N·K^(N). -/
def expansionSet (K : Set ℝ) (N : ℕ) : Set ℝ :=
  Set.image2 (· - ·) (sumSetN (productSetN K N) N) (sumSetN (productSetN K N) N)

/-- Polynomial constant for step6 smallness condition: 3·m·(2m)^m. -/
def step6_poly_C (m : ℕ) : ℝ :=
  3 * (m : ℝ) * (2 * (m : ℝ)) ^ m

/-! ## Helper lemmas -/

/-- Nreal and Nreal' are definitionally equal. -/
lemma Nreal_eq_Nreal' {δ : ℝ} {A : Set ℝ} :
    Nreal δ A = ProductLikeIncidence.Nreal' δ A := by
  rfl

/-- Recursive decomposition of weightedSumset at m+1. -/
lemma weightedSumset_succ {m : ℕ} (x : Fin (m + 1) → ℝ) (A : Set ℝ) :
    weightedSumset x A = Set.image2 (· + ·) (scaleSet (x 0) A)
        (weightedSumset (x ∘ Fin.succ) A) := by
  ext z
  simp only [weightedSumset, Set.mem_image2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨x 0 * a 0, ⟨a 0, ha 0, rfl⟩,
      ∑ i : Fin m, x i.succ * a i.succ, ⟨fun i => a i.succ, fun i => ha i.succ, rfl⟩, ?_⟩
    rw [Fin.sum_univ_succ] <;> ring
  · rintro ⟨y, ⟨a0, ha0, rfl⟩, w, ⟨a', ha', rfl⟩, rfl⟩
    let b : Fin (m + 1) → ℝ := Fin.cons a0 a'
    have hb : ∀ i, b i ∈ A := by
      intro i
      by_cases h : i = 0
      · rw [h]
        simpa [b, Fin.cons_zero] using ha0
      · let j : Fin m := i.pred h
        have h_eq : j.succ = i := Fin.succ_pred i h
        rw [← h_eq]
        simpa [b, Fin.cons_succ] using ha' j
    refine ⟨b, hb, ?_⟩
    rw [Fin.sum_univ_succ]
    <;> simp [b, Fin.cons_zero, Fin.cons_succ] <;> ring

/-- weightedSumset x A equals the Minkowski family sum of {x_i A}. -/
lemma weightedSumset_eq_familySum {m : ℕ} (x : Fin m → ℝ) (A : Set ℝ) :
    weightedSumset x A = ProductLikeIncidence.familySum (fun i : Fin m => scaleSet (x i) A) := by
  have h_main : ∀ (k : ℕ) (y : Fin k → ℝ),
      weightedSumset y A = ProductLikeIncidence.familySum (fun i : Fin k => scaleSet (y i) A) := by
    intro k
    induction k with
    | zero =>
      intro y
      have h1 : weightedSumset y A = {0} := by
        ext z
        simp [weightedSumset]
        <;> constructor <;> intro h <;> simpa using h
      have h2 : ProductLikeIncidence.familySum (fun i : Fin 0 => scaleSet (y i) A) = {0} := by
        simp [ProductLikeIncidence.familySum]
      rw [h1, h2]
    | succ k ih =>
      intro y
      have h1 := weightedSumset_succ y A
      rw [h1]
      have h2 := ih (y ∘ Fin.succ)
      rw [h2] <;> rfl
  exact h_main m x

/-- Covering number bound for scaled set:
    N(t⁻¹A) ≤ 3·δ^{-(1+3s)/4}. -/
lemma covering_scaled_bound
    {δ t s : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (ht_pos : 0 < t) (h_t_lower : δ ^ ((1 - s) / 4) ≤ t)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    {A : Set ℝ} (hA_bdd : Bornology.IsBounded A)
    (hA_size : Nreal δ A ≤ ENNReal.ofReal (δ ^ (-s))) :
    Nreal δ (scaleSet t⁻¹ A) ≤ ENNReal.ofReal (3 * δ ^ (-(1 + 3 * s) / 4)) := by
  have hδ_nonneg : 0 ≤ δ := by linarith
  by_cases h_t_le_one : t ≤ 1
  · -- Case t ≤ 1: use scaling + coarsening
    have h_tinv_pos : 0 < t⁻¹ := by positivity
    have h1 : Nreal δ (scaleSet t⁻¹ A) = Nreal (δ * t) A := by
      rw [covering_scaling hδ h_tinv_pos hA_bdd]
      have h2 : δ / t⁻¹ = δ * t := by
        field_simp [ht_pos.ne'] <;> ring
      rw [h2]
    rw [h1]
    have h_coarse : ENNReal.ofReal (t / 3) * Nreal (δ * t) A ≤ Nreal δ A :=
      covering_coarsening hδ ht_pos h_t_le_one hA_bdd
    have h5 : ENNReal.ofReal (3 / t) * ENNReal.ofReal (t / 3) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h6 : (3 / t) * (t / 3) = 1 := by
        field_simp [ht_pos.ne'] <;> ring
      rw [h6] <;> simp
    have h3 : Nreal (δ * t) A ≤ ENNReal.ofReal (3 / t) * Nreal δ A := by
      have h4 : ENNReal.ofReal (3 / t) * ENNReal.ofReal (t / 3) * Nreal (δ * t) A ≤
          ENNReal.ofReal (3 / t) * Nreal δ A := by
        have h41 : ENNReal.ofReal (t / 3) * Nreal (δ * t) A ≤ Nreal δ A := h_coarse
        have h : ENNReal.ofReal (3 / t) * (ENNReal.ofReal (t / 3) * Nreal (δ * t) A) ≤
            ENNReal.ofReal (3 / t) * Nreal δ A := mul_le_mul_left' h41 _
        simpa [mul_assoc] using h
      rw [h5] at h4
      simpa using h4
    have h7 : (3 / t) * δ ^ (-s) ≤ 3 * δ ^ (-(1 + 3 * s) / 4) := by
      have h81 : 0 < δ ^ ((1 - s) / 4) := by positivity
      have h82 : 1 / t ≤ 1 / δ ^ ((1 - s) / 4) := by gcongr
      have h83 : 1 / δ ^ ((1 - s) / 4) = δ ^ (-(1 - s) / 4) := by
        have h_pos : 0 < δ ^ ((1 - s) / 4) := by positivity
        have h9 : (δ ^ ((1 - s) / 4))⁻¹ = δ ^ (-(1 - s) / 4) := by
          rw [← Real.rpow_neg hδ.le] <;> ring_nf
        simpa [one_div] using h9
      have h84 : 1 / t ≤ δ ^ (-(1 - s) / 4) := by
        calc 1 / t ≤ 1 / δ ^ ((1 - s) / 4) := h82
          _ = δ ^ (-(1 - s) / 4) := h83
      have h10 : δ ^ (-(1 - s) / 4) * δ ^ (-s) = δ ^ (-(1 - s) / 4 + (-s)) := by
        rw [← Real.rpow_add hδ] <;> ring
      have h11 : -(1 - s) / 4 + (-s) = -(1 + 3 * s) / 4 := by ring
      calc (3 / t) * δ ^ (-s)
        = 3 * (1 / t) * δ ^ (-s) := by ring
      _ ≤ 3 * δ ^ (-(1 - s) / 4) * δ ^ (-s) := by gcongr
      _ = 3 * (δ ^ (-(1 - s) / 4) * δ ^ (-s)) := by ring
      _ = 3 * δ ^ (-(1 - s) / 4 + (-s)) := by rw [h10]
      _ = 3 * δ ^ (-(1 + 3 * s) / 4) := by rw [h11]
    have h_bound1 : ENNReal.ofReal (3 / t) * Nreal δ A ≤
        ENNReal.ofReal ((3 / t) * δ ^ (-s)) := by
      have h : ENNReal.ofReal (3 / t) * Nreal δ A ≤
          ENNReal.ofReal (3 / t) * ENNReal.ofReal (δ ^ (-s)) := mul_le_mul_left' hA_size _
      have h2 : ENNReal.ofReal (3 / t) * ENNReal.ofReal (δ ^ (-s)) =
          ENNReal.ofReal ((3 / t) * δ ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      rw [h2] at h
      exact h
    calc Nreal (δ * t) A
      ≤ ENNReal.ofReal (3 / t) * Nreal δ A := h3
    _ ≤ ENNReal.ofReal ((3 / t) * δ ^ (-s)) := h_bound1
    _ ≤ ENNReal.ofReal (3 * δ ^ (-(1 + 3 * s) / 4)) := by
      exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h7

  · -- Case t > 1: use scale-down bound
    have h_t_gt_one : 1 < t := by linarith
    have h_t_inv_pos : 0 < t⁻¹ := by positivity
    have h_t_inv_le_one : t⁻¹ ≤ 1 := by
      have h : 1 / t < 1 := by
        apply (div_lt_one (by positivity)).mpr
        exact h_t_gt_one
      have h2 : t⁻¹ = 1 / t := by simp
      rw [h2]; exact h.le
    have h1 : Nreal δ (scaleSet t⁻¹ A) ≤ 2 * Nreal δ A :=
      covering_scale_down_le_two hδ h_t_inv_pos h_t_inv_le_one hA_bdd
    have h8 : -(1 + 3 * s) / 4 ≤ -s := by linarith [hs_lt_one]
    have h9 : δ ^ (-s) ≤ δ ^ (-(1 + 3 * s) / 4) := by
      by_cases hδ_eq_one : δ = 1
      · rw [hδ_eq_one] <;> norm_num
      · have hδ_lt_one : δ < 1 := lt_of_le_of_ne hδ_le_one hδ_eq_one
        exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ hδ_lt_one).mpr h8
    have h7 : 2 * δ ^ (-s) ≤ 3 * δ ^ (-(1 + 3 * s) / 4) := by
      have h10 : 0 ≤ δ ^ (-s) := by positivity
      have h11 : 2 * δ ^ (-s) ≤ 3 * δ ^ (-s) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) h10
      calc 2 * δ ^ (-s)
        ≤ 3 * δ ^ (-s) := h11
      _ ≤ 3 * δ ^ (-(1 + 3 * s) / 4) := by
        exact mul_le_mul_of_nonneg_left h9 (by norm_num)
    have h_bound2 : 2 * Nreal δ A ≤ ENNReal.ofReal (2 * δ ^ (-s)) := by
      have h : 2 * Nreal δ A ≤ 2 * ENNReal.ofReal (δ ^ (-s)) := mul_le_mul_left' hA_size _
      have h2 : 2 * ENNReal.ofReal (δ ^ (-s)) = ENNReal.ofReal (2 * δ ^ (-s)) := by
        rw [ENNReal.ofReal_mul (by positivity)] <;> norm_cast
      rw [h2] at h
      exact h
    calc Nreal δ (scaleSet t⁻¹ A)
      ≤ 2 * Nreal δ A := h1
    _ ≤ ENNReal.ofReal (2 * δ ^ (-s)) := h_bound2
    _ ≤ ENNReal.ofReal (3 * δ ^ (-(1 + 3 * s) / 4)) := by
      exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h7

/-! ## Main step -/

/-- **Steps 6–8**: Multi-set PR extraction with sumset gain. -/
lemma step6_8_multiset_pr
    {A K : Set ℝ} {N0 m : ℕ}
    {δ t s ε : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hδ_pos : 0 < δ) (ht_pos : 0 < t) (hε_pos : 0 < ε)
    {x : Fin m → ℝ} (hx_in_X : ∀ i, x i ∈ expansionSet K N0)
    (h_sumset_large : ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) ≤
        Nreal δ (weightedSumset x A))
    (h_εm : ε * (m : ℝ) < (1 - s) / 2)
    (h_t_lower : δ ^ ((1 - s) / 4) ≤ t)
    (hA_size : Nreal δ A ≤ ENNReal.ofReal (δ ^ (-s)))
    (δ₀ : ℝ) (hδ_small : δ ≤ δ₀) (hδ₀_le_one : δ₀ ≤ 1)
    (hδ_poly : δ ^ (5 * (1 - s) / 24) ≤ (step6_poly_C m)⁻¹)
    (hK_bdd : Bornology.IsBounded K) (hA_bdd : Bornology.IsBounded A) :
    ∃ (x' : ℝ), x' ∈ expansionSet K N0 ∧
      ENNReal.ofReal (δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)))) *
        Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (Set.image2 (· + ·) (scaleSet t⁻¹ A) (scaleSet x' A)) := by
  have hδ_le_one : δ ≤ 1 := le_trans hδ_small hδ₀_le_one
  have hδ_nonneg : 0 ≤ δ := by linarith

  by_cases hm : m = 0
  · -- m = 0: hδ_poly is contradictory since step6_poly_C 0 = 0
    subst hm
    have hC_zero : step6_poly_C 0 = 0 := by
      simp [step6_poly_C] <;> norm_num
    rw [hC_zero] at hδ_poly
    have h_exp_pos : 0 < 5 * (1 - s) / 24 := by linarith [hs_pos, hs_lt_one]
    have h_pos : 0 < δ ^ (5 * (1 - s) / 24) := Real.rpow_pos_of_pos hδ_pos _
    linarith

  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    let X := scaleSet t⁻¹ A
    let Y : Fin m → Set ℝ := fun i => scaleSet (x i) A
    let α : ℝ := δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)))
    let γ : ℝ := 3 * (1 - s) / 4 - ε * (m : ℝ) - (1 - s) / (24 * (N0 : ℝ))

    have hα_pos : 0 < α := by positivity
    have hα_nonneg : 0 ≤ α := by positivity

    have hX_bdd : Bornology.IsBounded X := scaleSet_bounded hA_bdd
    have hY_bdd : ∀ i, Bornology.IsBounded (Y i) := fun _ => scaleSet_bounded hA_bdd

    have hA_nonempty : A.Nonempty := by
      by_contra h
      have h' : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have h_empty : weightedSumset x A = ∅ := by
        ext z
        simp only [weightedSumset, Set.mem_empty_iff_false, Set.mem_setOf_eq, iff_false]
        rintro ⟨a, ha, rfl⟩
        let i : Fin m := ⟨0, hm_pos⟩
        have h_contra : a i ∈ A := ha i
        rw [h'] at h_contra
        simpa [h'] using h_contra
      rw [h_empty] at h_sumset_large
      have hN_empty : Nreal δ (∅ : Set ℝ) = 0 := by
        have h1 : realLineCopy (∅ : Set ℝ) = (∅ : Set (EuclideanSpace ℝ (Fin 1))) := by
          ext x
          simp [realLineCopy]
        simp [Nreal, dyadicCoveringNumber, dyadicCubesMeeting, h1]
      rw [hN_empty] at h_sumset_large
      have h_pos' : 0 < ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) := by positivity
      have h_cont : ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) ≤ 0 := h_sumset_large
      have h_eq : ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) = 0 := by
        simpa using h_cont
      rw [h_eq] at h_pos'
      simpa using h_pos'

    have hX_nonempty : X.Nonempty := by
      rcases hA_nonempty with ⟨a, ha⟩
      have h_mem : t⁻¹ * a ∈ scaleSet t⁻¹ A := by
        exact ⟨a, ha, rfl⟩
      exact ⟨t⁻¹ * a, h_mem⟩

    have hX_bound : Nreal δ X ≤ ENNReal.ofReal (3 * δ ^ (-(1 + 3 * s) / 4)) :=
      covering_scaled_bound hδ_pos hδ_le_one ht_pos h_t_lower hs_pos hs_lt_one hA_bdd hA_size

    -- Exponent gap: γ > 5(1-s)/24
    have h1_N0 : (1 - s) / (24 * (N0 : ℝ)) ≤ (1 - s) / 24 := by
      by_cases hN0 : N0 = 0
      · rw [hN0]
        simp [div_zero]
        <;> linarith [hs_lt_one]
      · have hN0_pos : (N0 : ℝ) ≥ 1 := by exact_mod_cast Nat.pos_of_ne_zero hN0
        have h24 : 24 ≤ 24 * (N0 : ℝ) := by linarith
        have h_pos : 0 < 1 - s := by linarith [hs_lt_one]
        gcongr
    have hγ_gt : 5 * (1 - s) / 24 < γ := by
      simp only [γ]
      linarith [h_εm, hs_lt_one, h1_N0]

    have hC_pos : 0 < step6_poly_C m := by
      simp [step6_poly_C, hm_pos] <;> positivity

    have h_gt_one : 1 < step6_poly_C m := by
      have hm_ge_one : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
      have h2 : (2 * (m : ℝ)) ^ m ≥ 2 := by
        have h3 : 2 * (m : ℝ) ≥ 2 := by linarith
        have h41 : (2 * (m : ℝ)) ^ m ≥ (2 : ℝ) ^ m := by gcongr
        have h42 : (2 : ℝ) ^ m ≥ 2 := by
          have h43 : m ≥ 1 := by exact_mod_cast hm_pos
          have h44 : (2 : ℝ) ^ m ≥ (2 : ℝ) ^ 1 := by
            gcongr
            <;> linarith
          simpa using h44
        linarith
      have h_main : step6_poly_C m ≥ 6 := by
        simp [step6_poly_C]
        have h9 : 3 * (m : ℝ) * (2 * (m : ℝ)) ^ m ≥ 3 * 1 * 2 := by
          gcongr <;> linarith
        linarith
      linarith

    have h_inv_lt_one : (step6_poly_C m)⁻¹ < 1 := by
      calc (step6_poly_C m)⁻¹ < 1⁻¹ := by gcongr
        _ = 1 := by norm_num

    have hδ_lt_one : δ < 1 := by
      have h4 : δ ^ (5 * (1 - s) / 24) < 1 := by
        calc δ ^ (5 * (1 - s) / 24) ≤ (step6_poly_C m)⁻¹ := hδ_poly
          _ < 1 := h_inv_lt_one
      have h_exp_pos : 0 < 5 * (1 - s) / 24 := by linarith [hs_pos, hs_lt_one]
      by_contra hδ_ge_one
      have hδ_ge_one' : δ ≥ 1 := by linarith
      have h9 : δ ^ (5 * (1 - s) / 24) ≥ 1 := by
        have h10 : δ ^ (5 * (1 - s) / 24) ≥ (1 : ℝ) ^ (5 * (1 - s) / 24) := by gcongr
        simpa using h10
      linarith

    have h5 : δ ^ γ < δ ^ (5 * (1 - s) / 24) := by
      have h_strict : 5 * (1 - s) / 24 < γ := hγ_gt
      exact Real.rpow_lt_rpow_of_exponent_gt hδ_pos hδ_lt_one hγ_gt

    have h6 : δ ^ γ < (step6_poly_C m)⁻¹ := by
      calc δ ^ γ < δ ^ (5 * (1 - s) / 24) := h5
        _ ≤ (step6_poly_C m)⁻¹ := hδ_poly

    have h7 : (step6_poly_C m) * δ ^ γ < 1 := by
      have h_pos1 : 0 < δ ^ γ := by positivity
      have hC_ne_zero : (step6_poly_C m) ≠ 0 := hC_pos.ne'
      have h' : (step6_poly_C m) * δ ^ γ < (step6_poly_C m) * (step6_poly_C m)⁻¹ :=
        mul_lt_mul_of_pos_left h6 hC_pos
      have h'' : (step6_poly_C m) * (step6_poly_C m)⁻¹ = 1 := by
        field_simp [hC_ne_zero] <;> ring
      rw [h''] at h'
      exact h'

    let a : ℝ := -(1 - s) / (24 * (N0 : ℝ))
    let b : ℝ := -(1 + 3 * s) / 4
    let c : ℝ := -1 + ε * (m : ℝ)

    have h8 : c - (a + b) = -γ := by
      simp only [a, b, c, γ] <;> ring

    have h11 : (step6_poly_C m) < δ ^ (-γ) := by
      have h_pos1 : 0 < δ ^ γ := by positivity
      have h12 : (step6_poly_C m) * δ ^ γ < 1 := h7
      have h13 : (step6_poly_C m) < (δ ^ γ)⁻¹ := by
        have h14 : δ ^ γ ≠ 0 := h_pos1.ne'
        have h15 : (step6_poly_C m) = (step6_poly_C m) * δ ^ γ * (δ ^ γ)⁻¹ := by
          field_simp [h14] <;> ring
        rw [h15]
        have h16 : (step6_poly_C m) * δ ^ γ * (δ ^ γ)⁻¹ < 1 * (δ ^ γ)⁻¹ := by
          exact mul_lt_mul_of_pos_right h12 (by positivity)
        simpa using h16
      have h14 : (δ ^ γ)⁻¹ = δ ^ (-γ) := by
        rw [← Real.rpow_neg hδ_pos.le] <;> ring
      rw [h14] at h13
      exact h13

    have h10 : 0 < δ ^ a * δ ^ b := by positivity

    have h16 : δ ^ (-γ) * (δ ^ a * δ ^ b) = δ ^ c := by
      have h17 : δ ^ a * δ ^ b = δ ^ (a + b) := by
        rw [← Real.rpow_add hδ_pos] <;> ring
      rw [h17]
      have h18 : δ ^ (-γ) * δ ^ (a + b) = δ ^ (-γ + (a + b)) := by
        rw [← Real.rpow_add hδ_pos] <;> ring
      rw [h18]
      have h19 : -γ + (a + b) = c := by linarith [h8]
      rw [h19]

    have h_real_ineq :
        (step6_poly_C m) * δ ^ a * δ ^ b < δ ^ c := by
      have h15 : (step6_poly_C m) * (δ ^ a * δ ^ b) < δ ^ (-γ) * (δ ^ a * δ ^ b) := by
        gcongr
      rw [h16] at h15
      simpa [mul_assoc] using h15

    -- Main argument: by contradiction, assume all N(X + Y_i) ≤ α * N(X)
    by_cases h_main : ∃ (i : Fin m), ¬(Nreal δ (Set.image2 (· + ·) X (Y i)) ≤
        ENNReal.ofReal α * Nreal δ X)
    · rcases h_main with ⟨i, hi⟩
      refine ⟨x i, hx_in_X i, ?_⟩
      have h_gt : ENNReal.ofReal α * Nreal δ X < Nreal δ (Set.image2 (· + ·) X (Y i)) :=
        not_le.mp hi
      exact h_gt.le

    · push Not at h_main
      have h_all : ∀ (i : Fin m), Nreal δ (Set.image2 (· + ·) X (Y i)) ≤
          ENNReal.ofReal α * Nreal δ X := h_main

      have h_all' : ∀ (i : Fin m), ProductLikeIncidence.Nreal' δ (Set.image2 (· + ·) X (Y i)) ≤
          ENNReal.ofReal α * ProductLikeIncidence.Nreal' δ X := by
        intro i
        have h_i := h_all i
        simpa [Nreal_eq_Nreal'] using h_i

      have hPR_raw := ProductLikeIncidence.discretized_multiset_pr_general
        hδ_pos hm_pos hX_bdd hY_bdd hX_nonempty (fun _ => hα_nonneg) h_all'

      have h_sum_alpha : (∑ i : Fin m, α) = (m : ℝ) * α := by
        simp [Finset.sum_const] <;> ring

      rw [h_sum_alpha] at hPR_raw

      have hPR' : Nreal δ (ProductLikeIncidence.familySum Y) ≤
          ENNReal.ofReal ((m : ℝ) * (2 * (m : ℝ) * α) ^ m) * Nreal δ X := by
        have h_eq : (2 * ((m : ℝ) * α)) = (2 * (m : ℝ) * α) := by ring
        have h_raw : ProductLikeIncidence.Nreal' δ (ProductLikeIncidence.familySum Y) ≤
            ENNReal.ofReal ((m : ℝ) * (2 * (m : ℝ) * α) ^ m) * ProductLikeIncidence.Nreal' δ X := by
          rw [h_eq] at hPR_raw
          exact hPR_raw
        have h1 : Nreal δ (ProductLikeIncidence.familySum Y) = ProductLikeIncidence.Nreal' δ (ProductLikeIncidence.familySum Y) := Nreal_eq_Nreal'
        have h2 : Nreal δ X = ProductLikeIncidence.Nreal' δ X := Nreal_eq_Nreal'
        rw [h1, h2]
        exact h_raw

      rw [weightedSumset_eq_familySum x A] at h_sumset_large

      have hα_m : α ^ m = δ ^ (-(1 - s) / (24 * (N0 : ℝ))) := by
        have h1 : α = δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ))) := by rfl
        rw [h1]
        have h2 : (δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)))) ^ m =
            δ ^ ((-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ))) * (m : ℝ)) := by
          have h3 : ∀ (x : ℝ) (n : ℕ), (x ^ n) = x ^ (n : ℝ) := by
            intro x n
            exact Eq.symm (Real.rpow_natCast x n)
          rw [h3]
          rw [Real.rpow_mul hδ_nonneg] <;> ring
        rw [h2]
        have h4 : (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ))) * (m : ℝ) =
            -(1 - s) / (24 * (N0 : ℝ)) := by
          field_simp [hm_pos.ne'] <;> ring
        rw [h4]

      have h_combined : Nreal δ (ProductLikeIncidence.familySum Y) ≤
          ENNReal.ofReal ((step6_poly_C m) * α ^ m * δ ^ (-(1 + 3 * s) / 4)) := by
        calc Nreal δ (ProductLikeIncidence.familySum Y)
          ≤ ENNReal.ofReal ((m : ℝ) * (2 * (m : ℝ) * α) ^ m) * Nreal δ X := hPR'
        _ ≤ ENNReal.ofReal ((m : ℝ) * (2 * (m : ℝ) * α) ^ m) *
              ENNReal.ofReal (3 * δ ^ (-(1 + 3 * s) / 4)) := by
          exact mul_le_mul_left' hX_bound _
        _ = ENNReal.ofReal (((m : ℝ) * (2 * (m : ℝ) * α) ^ m) * (3 * δ ^ (-(1 + 3 * s) / 4))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal ((step6_poly_C m) * α ^ m * δ ^ (-(1 + 3 * s) / 4)) := by
            congr 1
            simp [step6_poly_C] <;> ring

      rw [hα_m] at h_combined

      have h_contra : ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) ≤
          ENNReal.ofReal ((step6_poly_C m) * δ ^ (-(1 - s) / (24 * (N0 : ℝ))) * δ ^ (-(1 + 3 * s) / 4)) :=
        le_trans h_sumset_large h_combined

      have h_real_le : δ ^ (-1 + ε * (m : ℝ)) ≤
          (step6_poly_C m) * δ ^ (-(1 - s) / (24 * (N0 : ℝ))) * δ ^ (-(1 + 3 * s) / 4) :=
        ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h_contra

      exact False.elim (not_le.mpr h_real_ineq h_real_le)

end

/-! ## Steps 7-8: Unpacking and Sum-to-Difference Conversion -/

/-- Unpack an element of `sumSetN A N` into a list of `N` elements of `A`. -/
lemma sumSetN_unpack {A : Set ℝ} {N : ℕ} {x : ℝ} (hx : x ∈ sumSetN A N) :
    ∃ (f : Fin N → ℝ), (∀ i, f i ∈ A) ∧ x = ∑ i : Fin N, f i := by
  have h_main : ∀ (n : ℕ) (z : ℝ), z ∈ sumSetN A n →
      ∃ (f : Fin n → ℝ), (∀ i, f i ∈ A) ∧ z = ∑ i : Fin n, f i := by
    intro n
    induction n with
    | zero =>
      intro z hz
      have h_z_eq : z = 0 := by simpa [sumSetN] using hz
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i; fin_cases i
      · simp [h_z_eq]
    | succ n ih =>
      intro z hz
      rcases hz with ⟨a0, ha0, y, hy, h_eq⟩
      rcases ih y hy with ⟨f, hf, h_sum⟩
      refine ⟨Fin.cons a0 f, ?_, ?_⟩
      · intro i
        exact Fin.cases ha0 hf i
      · have h_sum2 : ∑ i : Fin (n + 1), Fin.cons a0 f i = a0 + ∑ i : Fin n, f i := by
          rw [Fin.sum_univ_succ]
          <;> simp [Fin.cons_zero, Fin.cons_succ]
          <;> ring
        calc z
          = a0 + y := h_eq.symm
        _ = a0 + ∑ i : Fin n, f i := by rw [h_sum]
        _ = ∑ i : Fin (n + 1), Fin.cons a0 f i := h_sum2.symm
  exact h_main N x hx

/-- Unpack an element of `expansionSet K N` into two lists of `N` elements
    from `productSetN K N`. -/
lemma expansionSet_unpack {K : Set ℝ} {N : ℕ} {x : ℝ}
    (hx : x ∈ expansionSet K N) :
    ∃ (a b : Fin N → ℝ), (∀ i, a i ∈ productSetN K N) ∧
      (∀ i, b i ∈ productSetN K N) ∧
      x = ∑ i : Fin N, a i - ∑ i : Fin N, b i := by
  rcases hx with ⟨u, hu, v, hv, h_eq⟩
  have h1 := sumSetN_unpack (A := productSetN K N) (N := N) (x := u) hu
  have h2 := sumSetN_unpack (A := productSetN K N) (N := N) (x := v) hv
  rcases h1 with ⟨a, ha, h_ua⟩
  rcases h2 with ⟨b, hb, h_vb⟩
  refine ⟨a, b, ha, hb, ?_⟩
  have h3 : u - v = (∑ i, a i) - (∑ i, b i) := by
    rw [h_ua, h_vb] <;> ring
  have h4 : x = u - v := h_eq.symm
  rw [h4, h3]

/-- If `f i ∈ Y i` for all `i`, then `∑ f i ∈ familySum Y`. -/
lemma familySum_mem {k : ℕ} {Y : Fin k → Set ℝ} {f : Fin k → ℝ}
    (hf : ∀ i, f i ∈ Y i) : ∑ i : Fin k, f i ∈ ProductLikeIncidence.familySum Y := by
  induction k with
  | zero =>
    simp [ProductLikeIncidence.familySum]
  | succ k ih =>
    have h_ih : ∑ i : Fin k, f i.succ ∈ ProductLikeIncidence.familySum (fun i => Y i.succ) :=
      ih (fun i => hf i.succ)
    have h_eq : (∑ i : Fin (k + 1), f i) = f 0 + ∑ i : Fin k, f i.succ := by
      rw [Fin.sum_univ_succ] <;> ring
    rw [h_eq]
    exact ⟨f 0, hf 0, _, h_ih, rfl⟩

/-- Helper: for i : Fin (N+N) with ¬(i.val < N), we have i.val - N < N. -/
lemma fin_sub_lt {N : ℕ} {i : Fin (N + N)} (h : ¬i.val < N) : i.val - N < N := by
  have h1 : i.val < N + N := i.prop
  have h2 : N ≤ i.val := by omega
  omega

/-- Indexed family of ±scaled product sets for expansion unpacking. -/
def expansionFamily (A : Set ℝ) (N : ℕ) (a b : Fin N → ℝ) :
    Fin (N + N) → Set ℝ :=
  fun i =>
    if h : i.val < N then scaleSet (a ⟨i.val, h⟩) A
    else scaleSet (-(b ⟨i.val - N, fin_sub_lt h⟩)) A

/-- Point value corresponding to expansionFamily. -/
def expansionFamilyVal (N : ℕ) (a b : Fin N → ℝ) (a_val : ℝ) :
    Fin (N + N) → ℝ :=
  fun i =>
    if h : i.val < N then a ⟨i.val, h⟩ * a_val
    else -b ⟨i.val - N, fin_sub_lt h⟩ * a_val

/-- Containment: `x'A ⊆ familySum of ±product terms`. -/
lemma scaleSet_expansion_subset {A : Set ℝ} {N : ℕ} {x' : ℝ}
    (a b : Fin N → ℝ) (h_eq : x' = ∑ i, a i - ∑ i, b i) :
    scaleSet x' A ⊆ ProductLikeIncidence.familySum (expansionFamily A N a b) := by
  intro w hw
  rcases hw with ⟨a_val, ha, rfl⟩
  let f := expansionFamilyVal N a b a_val
  have hf : ∀ i, f i ∈ expansionFamily A N a b i := by
    intro i
    by_cases h : i.val < N
    · have h_set : expansionFamily A N a b i = scaleSet (a ⟨i.val, h⟩) A := by
        simp [expansionFamily, h]
      rw [h_set]
      have hfi : f i = a ⟨i.val, h⟩ * a_val := by
        simp [f, expansionFamilyVal, h]
      rw [hfi]
      exact ⟨a_val, ha, by ring⟩
    · have h_set : expansionFamily A N a b i =
          scaleSet (-(b ⟨i.val - N, fin_sub_lt h⟩)) A := by
        simp [expansionFamily, h]
      rw [h_set]
      have hfi : f i = -b ⟨i.val - N, fin_sub_lt h⟩ * a_val := by
        simp [f, expansionFamilyVal, h]
      rw [hfi]
      exact ⟨a_val, ha, by ring⟩
  have h_sum1 : ∑ i : Fin (N + N), f i =
      (∑ i : Fin N, a i * a_val) + ∑ i : Fin N, (-b i * a_val) := by
    rw [Fin.sum_univ_add]
    <;> congr <;> ext i <;> simp [f, expansionFamilyVal] <;> ring
  have h2 : ∑ i : Fin N, (-b i * a_val) = -∑ i : Fin N, (b i * a_val) := by
    have h4 : ∀ i : Fin N, -b i * a_val = -(b i * a_val) := by intro i; ring
    have h_sum_eq : ∑ i : Fin N, (-b i * a_val) = ∑ i : Fin N, (-(b i * a_val)) := by
      congr with i
      exact h4 i
    rw [h_sum_eq, Finset.sum_neg_distrib]
  have h_sum : ∑ i : Fin (N + N), f i = x' * a_val := by
    have h5 : (∑ i : Fin N, a i * a_val) = (∑ i : Fin N, a i) * a_val := by
      exact Eq.symm (Finset.sum_mul Finset.univ a a_val)
    have h6 : (∑ i : Fin N, b i * a_val) = (∑ i : Fin N, b i) * a_val := by
      exact Eq.symm (Finset.sum_mul Finset.univ b a_val)
    calc ∑ i : Fin (N + N), f i
      = (∑ i : Fin N, a i * a_val) + ∑ i : Fin N, (-b i * a_val) := h_sum1
    _ = (∑ i : Fin N, a i * a_val) - ∑ i : Fin N, (b i * a_val) := by rw [h2] <;> ring
    _ = (∑ i : Fin N, a i) * a_val - (∑ i : Fin N, b i) * a_val := by rw [h5, h6] <;> ring
    _ = ((∑ i : Fin N, a i) - (∑ i : Fin N, b i)) * a_val := by ring
    _ = x' * a_val := by rw [h_eq] <;> ring
  have h_final : x' * a_val ∈ ProductLikeIncidence.familySum (expansionFamily A N a b) := by
    rw [←h_sum]
    exact familySum_mem (Y := expansionFamily A N a b) hf
  exact h_final

/-- **Sum-to-difference lower bound** (from Ruzsa triangle + PR):
    `N(X+Y) * N(X) * N(Y) ≤ 162 * N(X-Y)^3`. -/
lemma sum_to_diff_lower {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hX_nonempty : X.Nonempty) (hY_nonempty : Y.Nonempty) :
    Nreal δ (Set.image2 (· + ·) X Y) * Nreal δ X * Nreal δ Y ≤
      162 * Nreal δ (Set.image2 (· - ·) X Y) *
        Nreal δ (Set.image2 (· - ·) X Y) *
        Nreal δ (Set.image2 (· - ·) X Y) := by
  let Y' := Set.image (fun x : ℝ => -x) Y
  have h_cont : Continuous (fun x : ℝ => -x) := by fun_prop
  have hY'_bdd : Bornology.IsBounded Y' := by
    have h_neg_lipschitz : LipschitzWith 1 (fun x : ℝ => -x) := by
      intro x y
      simp [Real.dist_eq, abs_neg]
      <;> ring_nf <;> exact le_refl _
    have h : Bornology.IsBounded ((fun x : ℝ => -x) '' Y) :=
      h_neg_lipschitz.isBounded_image hY
    simpa [Y'] using h
  have hY'_nonempty : Y'.Nonempty := by
    rcases hY_nonempty with ⟨y, hy⟩
    exact ⟨-y, y, hy, rfl⟩
  have h_eq_add : Set.image2 (· + ·) X Y' = Set.image2 (· - ·) X Y := by
    ext z
    simp only [Y', Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨x, hx, y', ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, by ring⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, -y, ⟨y, hy, rfl⟩, by ring⟩
  have h_eq_sub : Set.image2 (· - ·) X Y' = Set.image2 (· + ·) X Y := by
    ext z
    simp only [Y', Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨x, hx, y', ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, by ring⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, -y, ⟨y, hy, rfl⟩, by ring⟩
  -- Step 1: Ruzsa triangle with U=X, V=Y', W=X:
  -- N(X+Y) * N(X) ≤ 9 * N(X+X) * N(X-Y)
  have h1 : Nreal δ (Set.image2 (· + ·) X Y) * Nreal δ X ≤
      9 * Nreal δ (Set.image2 (· + ·) X X) *
        Nreal δ (Set.image2 (· - ·) X Y) := by
    have h_rt := ProductLikeIncidence.discretized_ruzsa_triangle hδ hX hY'_bdd hX hX_nonempty
    have h : Nreal δ (Set.image2 (· - ·) X Y') * Nreal δ X ≤
        9 * Nreal δ (Set.image2 (· + ·) X X) *
          Nreal δ (Set.image2 (· + ·) X Y') := h_rt
    rw [h_eq_sub, h_eq_add] at h
    exact h
  -- Step 2: PR with X=X, Y=Y':
  -- N(X+X) * N(Y') ≤ 9 * N(X-Y)^2
  have h2 : Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y' ≤
      9 * Nreal δ (Set.image2 (· - ·) X Y) *
        Nreal δ (Set.image2 (· - ·) X Y) := by
    have h_pr := ProductLikeIncidence.discretized_pluennecke_ruzsa_sum hδ hX hY'_bdd hY'_nonempty
    simpa [Nreal, h_eq_add] using h_pr
  -- Step 3: N(Y) ≤ 2 * N(Y') (double negation)
  have h3 : Nreal δ Y ≤ 2 * Nreal δ Y' := by
    have h4 : Nreal δ Y = Nreal δ (Set.image (fun x : ℝ => -x) Y') := by
      congr with z
      simp [Y']
      <;> constructor <;> rintro ⟨w, hw, rfl⟩ <;> exact ⟨-w, ⟨w, hw, rfl⟩, by ring⟩
    rw [h4]
    exact covering_negation_le_two hδ hY'_bdd
  -- Step 4: N(X+X) * N(Y) ≤ 18 * N(X-Y)^2
  have h4 : Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y ≤
      18 * Nreal δ (Set.image2 (· - ·) X Y) *
        Nreal δ (Set.image2 (· - ·) X Y) := by
    have h5 : Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y ≤
        2 * (Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y') := by
      calc Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y
        ≤ Nreal δ (Set.image2 (· + ·) X X) * (2 * Nreal δ Y') := by gcongr
      _ = 2 * (Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y') := by ring
    calc Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y
      ≤ 2 * (Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y') := h5
    _ ≤ 2 * (9 * Nreal δ (Set.image2 (· - ·) X Y) *
               Nreal δ (Set.image2 (· - ·) X Y)) := by gcongr
    _ = 18 * Nreal δ (Set.image2 (· - ·) X Y) *
          Nreal δ (Set.image2 (· - ·) X Y) := by ring
  -- Combine
  calc Nreal δ (Set.image2 (· + ·) X Y) * Nreal δ X * Nreal δ Y
    = (Nreal δ (Set.image2 (· + ·) X Y) * Nreal δ X) * Nreal δ Y := by ring
  _ ≤ (9 * Nreal δ (Set.image2 (· + ·) X X) *
          Nreal δ (Set.image2 (· - ·) X Y)) * Nreal δ Y := by gcongr
  _ = 9 * (Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y) *
        Nreal δ (Set.image2 (· - ·) X Y) := by ring
  _ ≤ 9 * (18 * Nreal δ (Set.image2 (· - ·) X Y) *
               Nreal δ (Set.image2 (· - ·) X Y)) *
        Nreal δ (Set.image2 (· - ·) X Y) := by gcongr
  _ = 162 * Nreal δ (Set.image2 (· - ·) X Y) *
        Nreal δ (Set.image2 (· - ·) X Y) *
        Nreal δ (Set.image2 (· - ·) X Y) := by ring

/-- Bounds on elements of `productSetN K N` when `K ⊆ [2^{-1/κ}, 1]`. -/
lemma productSetN_bounds {κ : ℝ} {K : Set ℝ} {N : ℕ} {z : ℝ}
    (hκ_pos : 0 < κ) (hK_bounds : K ⊆ Set.Icc ((2 : ℝ)^(-(1/κ))) 1)
    (hz : z ∈ productSetN K N) :
    (2 : ℝ)^(-(N : ℝ)/κ) ≤ z ∧ z ≤ 1 := by
  rcases hz with ⟨f, hf, rfl⟩
  have h1 : ∀ i : Fin N, (2 : ℝ)^(-(1/κ)) ≤ f i ∧ f i ≤ 1 := by
    intro i
    have h2 : f i ∈ K := hf i
    have h3 : f i ∈ Set.Icc ((2 : ℝ)^(-(1/κ))) 1 := hK_bounds h2
    exact ⟨h3.1, h3.2⟩
  have h_pos : ∀ i : Fin N, 0 < f i := by
    intro i
    have h4 : 0 < (2 : ℝ)^(-(1/κ)) := by positivity
    have h5 : (2 : ℝ)^(-(1/κ)) ≤ f i := (h1 i).1
    linarith
  have h_lower : (2 : ℝ)^(-(N : ℝ)/κ) ≤ ∏ i : Fin N, f i := by
    have h6 : ∏ i : Fin N, (2 : ℝ)^(-(1/κ)) ≤ ∏ i : Fin N, f i := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; exact (h1 i).1
    have h7 : ∏ i : Fin N, (2 : ℝ)^(-(1/κ)) = ((2 : ℝ)^(-(1/κ))) ^ N := by simp
    have h81 : ((2 : ℝ)^(-(1/κ))) ^ N = (2 : ℝ)^((-(1/κ)) * (N : ℝ)) := by
      have h_a : ((2 : ℝ)^(-(1/κ))) ^ N = ((2 : ℝ)^(-(1/κ))) ^ (N : ℝ) := by
        rw [← Real.rpow_natCast]
      rw [h_a, Real.rpow_mul (by norm_num)] <;> ring
    have h82 : (-(1/κ)) * (N : ℝ) = (-(N : ℝ)/κ) := by ring
    calc (2 : ℝ)^(-(N : ℝ)/κ)
      = (2 : ℝ)^((-(1/κ)) * (N : ℝ)) := by rw [h82]
    _ = ((2 : ℝ)^(-(1/κ))) ^ N := h81.symm
    _ = ∏ i : Fin N, (2 : ℝ)^(-(1/κ)) := h7.symm
    _ ≤ ∏ i : Fin N, f i := h6
  have h_upper : ∏ i : Fin N, f i ≤ 1 := by
    have h9 : ∏ i : Fin N, f i ≤ ∏ i : Fin N, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _; exact (h_pos i).le
      · intro i _; exact (h1 i).2
    simpa using h9
  exact ⟨h_lower, h_upper⟩

/-- Monotonicity of `Nreal` with respect to set inclusion. -/
lemma Nreal_mono {δ : ℝ} {A B : Set ℝ} (h : A ⊆ B) : Nreal δ A ≤ Nreal δ B := by
  simp only [Nreal, dyadicCoveringNumber]
  apply ENat.toENNReal_mono
  apply Set.encard_mono
  intro Q hQ
  have hQ1 : Q ∈ dyadicCubes 1 δ := hQ.1
  have hQ2 : (Q ∩ realLineCopy A).Nonempty := hQ.2
  have hAB : realLineCopy A ⊆ realLineCopy B := by
    intro x hx
    simpa [realLineCopy] using h (by simpa [realLineCopy] using hx)
  have hQ3 : (Q ∩ realLineCopy B).Nonempty := by
    have h_sub : Q ∩ realLineCopy A ⊆ Q ∩ realLineCopy B := by
      exact Set.inter_subset_inter_right Q hAB
    exact hQ2.mono h_sub
  exact ⟨hQ1, hQ3⟩

/-! ## Full Step 6-8: Product-set + DIFFERENCE conclusion via negated-family PR -/

/-- Lower bound for the scaling ratio constant: for `z ∈ productSetN K N0`,
    `N(zA) ≥ c_ratio * t * N(t⁻¹A)` where `c_ratio = 1/(3*C_p)` and
    `C_p = ceil(2^{N0/κ}) + 2`. -/
lemma step6_scaling_ratio {δ t : ℝ} (hδ : 0 < δ) (ht_pos : 0 < t) (ht_le_one : t ≤ 1)
    {A K : Set ℝ} (hA_bdd : Bornology.IsBounded A)
    {κ : ℝ} (hκ_pos : 0 < κ) {N0 : ℕ}
    {z : ℝ} (hz : z ∈ productSetN K N0)
    (hK_bounds : K ⊆ Set.Icc ((2 : ℝ)^ (-(1/κ))) 1) :
    Nreal δ (scaleSet z A) ≥
      ENNReal.ofReal ((1 : ℝ) / (3 * ((2 : ℝ)^((N0 : ℝ)/κ) + 3)) * t) *
      Nreal δ (scaleSet t⁻¹ A) := by
  have hz_bounds : (2 : ℝ)^(-(N0 : ℝ)/κ) ≤ z ∧ z ≤ 1 :=
    productSetN_bounds hκ_pos hK_bounds hz
  let c_p : ℝ := (2 : ℝ)^(-(N0 : ℝ)/κ)
  let C_p : ℕ := Nat.ceil (1 / c_p) + 2
  have hC_p_pos : 0 < (C_p : ℝ) := by positivity
  have h1 : Nreal δ A ≤ (C_p : ENNReal) * Nreal δ (scaleSet z A) := by
    simpa [C_p, c_p] using covering_scale_down_ge hδ (by positivity) hz_bounds.1 hz_bounds.2 hA_bdd
  have h_cp_bound : (C_p : ℝ) ≤ (2 : ℝ)^((N0 : ℝ)/κ) + 3 := by
    have h2 : (C_p : ℝ) = Nat.ceil (1 / c_p) + 2 := by simp [C_p]
    rw [h2]
    have h3 : 1 / c_p = (2 : ℝ)^((N0 : ℝ)/κ) := by
      have h_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
      have h_pos2 : 0 < (2 : ℝ)^((N0 : ℝ)/κ) := by positivity
      have h_cp : c_p = (2 : ℝ)^(-(N0 : ℝ)/κ) := by rfl
      rw [h_cp]
      have h5 : (2 : ℝ)^(-(N0 : ℝ)/κ) = ((2 : ℝ)^((N0 : ℝ)/κ))⁻¹ := by
        have h6 : (-(N0 : ℝ)/κ) = -((N0 : ℝ)/κ) := by ring
        rw [h6]
        have h7 : (2 : ℝ) ^ (-((N0 : ℝ)/κ)) = ((2 : ℝ) ^ ((N0 : ℝ)/κ))⁻¹ :=
          Real.rpow_neg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ((N0 : ℝ)/κ)
        exact h7
      rw [h5]
      field_simp [h_pos2.ne'] <;> ring
    rw [h3]
    let x := (2 : ℝ)^((N0 : ℝ)/κ)
    have hx_pos : 0 < x := by positivity
    have h4 : (Nat.ceil x : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (ha := hx_pos.le)).le
    linarith
  let c_ratio : ℝ := 1 / (3 * ((C_p : ℝ)))
  have hcr_pos : 0 < c_ratio := by positivity
  have h_scaling_eq : Nreal δ (scaleSet t⁻¹ A) = Nreal (δ * t) A := by
    have h1 : Nreal δ (scaleSet t⁻¹ A) = Nreal (δ / t⁻¹) A :=
      covering_scaling hδ (by positivity) hA_bdd
    have h2 : δ / t⁻¹ = δ * t := by
      field_simp [ht_pos.ne'] <;> ring
    rw [h1, h2]
  have h_coarse : ENNReal.ofReal (t / 3) * Nreal (δ * t) A ≤ Nreal δ A :=
    covering_coarsening hδ ht_pos ht_le_one hA_bdd
  have h2 : ENNReal.ofReal (t / 3) * Nreal δ (scaleSet t⁻¹ A) ≤ Nreal δ A := by
    rw [h_scaling_eq]
    exact h_coarse
  have h3 : ENNReal.ofReal (t / 3) * Nreal δ (scaleSet t⁻¹ A) ≤
      (C_p : ENNReal) * Nreal δ (scaleSet z A) :=
    le_trans h2 h1
  have h4 : ENNReal.ofReal (c_ratio * t) * Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (scaleSet z A) := by
    set Y := ENNReal.ofReal (c_ratio * t) * Nreal δ (scaleSet t⁻¹ A) with hY_def
    have h9 : (C_p : ENNReal) * Y = ENNReal.ofReal (t / 3) * Nreal δ (scaleSet t⁻¹ A) := by
      simp only [hY_def]
      have h10 : (C_p : ℝ) * (c_ratio * t) = t / 3 := by
        dsimp only [c_ratio]
        field_simp [hC_p_pos.ne'] <;> ring
      have h12 : (C_p : ENNReal) * Y =
          ((C_p : ENNReal) * ENNReal.ofReal (c_ratio * t)) * Nreal δ (scaleSet t⁻¹ A) := by
        simp only [hY_def] <;> ring
      rw [h12]
      have h131 : (C_p : ENNReal) = ENNReal.ofReal (C_p : ℝ) := by exact Eq.symm (ENNReal.ofReal_natCast C_p)
      have h13 : (C_p : ENNReal) * ENNReal.ofReal (c_ratio * t) =
          ENNReal.ofReal ((C_p : ℝ) * (c_ratio * t)) := by
        rw [h131, ← ENNReal.ofReal_mul (by positivity)]
      rw [h13, h10]
    have h10 : (C_p : ENNReal) * Y ≤ (C_p : ENNReal) * Nreal δ (scaleSet z A) := by
      rw [h9]
      exact h3
    have h_cp_ne_zero : (C_p : ENNReal) ≠ 0 := by exact_mod_cast hC_p_pos.ne'
    have h_cp_lt_top : (C_p : ENNReal) ≠ ⊤ := by simp
    have h_div1 : ((C_p : ENNReal) * Y) / (C_p : ENNReal) = Y := by
      have h_comm : (C_p : ENNReal) * Y = Y * (C_p : ENNReal) := mul_comm _ _
      rw [h_comm]
      exact ENNReal.mul_div_cancel_right h_cp_ne_zero h_cp_lt_top
    have h : ((C_p : ENNReal) * Y) / (C_p : ENNReal) ≤
        ((C_p : ENNReal) * Nreal δ (scaleSet z A)) / (C_p : ENNReal) := by
      gcongr
    have h2 : ((C_p : ENNReal) * Nreal δ (scaleSet z A)) / (C_p : ENNReal) =
        Nreal δ (scaleSet z A) := by
      have h_comm : (C_p : ENNReal) * Nreal δ (scaleSet z A) =
          Nreal δ (scaleSet z A) * (C_p : ENNReal) := mul_comm _ _
      rw [h_comm]
      exact ENNReal.mul_div_cancel_right h_cp_ne_zero h_cp_lt_top
    rw [h_div1] at h
    rw [h2] at h
    exact h
  have h_main : Nreal δ (scaleSet z A) ≥
      ENNReal.ofReal (c_ratio * t) * Nreal δ (scaleSet t⁻¹ A) := h4
  have h_bound : c_ratio ≥ 1 / (3 * ((2 : ℝ)^((N0 : ℝ)/κ) + 3)) := by
    simp [c_ratio] <;> gcongr <;> linarith
  have h_final : ENNReal.ofReal (c_ratio * t) * Nreal δ (scaleSet t⁻¹ A) ≥
      ENNReal.ofReal ((1 : ℝ) / (3 * ((2 : ℝ)^((N0 : ℝ)/κ) + 3)) * t) * Nreal δ (scaleSet t⁻¹ A) := by
    gcongr <;> linarith
  exact le_trans h_final h_main

/-- Witness that every member of expansionFamily comes from productSetN. -/
lemma expansionFamily_member_witness {A K : Set ℝ} {N0 : ℕ}
    (a b : Fin N0 → ℝ) (ha : ∀ i, a i ∈ productSetN K N0)
    (hb : ∀ i, b i ∈ productSetN K N0)
    (idx : Fin (N0 + N0)) :
    ∃ (z : ℝ), z ∈ productSetN K N0 ∧
      (expansionFamily A N0 a b idx = scaleSet z A ∨
       expansionFamily A N0 a b idx = scaleSet (-z) A) := by
  by_cases h : idx.val < N0
  · refine ⟨a ⟨idx.val, h⟩, ha ⟨idx.val, h⟩, Or.inl ?_⟩
    simp [expansionFamily, h]
  · refine ⟨b ⟨idx.val - N0, fin_sub_lt h⟩, hb ⟨idx.val - N0, fin_sub_lt h⟩, Or.inr ?_⟩
    simp [expansionFamily, h] <;> ring

/-- If `f i ∈ Y i` for all `i`, then `∑ i, f i ∈ familySum Y`. -/
lemma sum_in_familySum {k : ℕ} {Y : Fin k → Set ℝ} {f : Fin k → ℝ}
    (hf : ∀ i, f i ∈ Y i) : (∑ i : Fin k, f i) ∈ ProductLikeIncidence.familySum Y := by
  induction k with
  | zero =>
    simp [ProductLikeIncidence.familySum]
  | succ k ih =>
    have h_sum : (∑ i : Fin (k + 1), f i) = f 0 + ∑ i : Fin k, f i.succ := by
      rw [Fin.sum_univ_succ] <;> ring
    rw [h_sum]
    exact ⟨f 0, hf 0, ∑ i : Fin k, f i.succ, ih (fun i => hf i.succ), by ring⟩

/-- Every element of `familySum Y` is a sum of choices from each `Y i`. -/
lemma familySum_is_sum {k : ℕ} {Y : Fin k → Set ℝ} {z : ℝ}
    (hz : z ∈ ProductLikeIncidence.familySum Y) :
    ∃ (f : Fin k → ℝ), (∀ i, f i ∈ Y i) ∧ z = ∑ i : Fin k, f i := by
  have h_main : ∀ (n : ℕ) (Y' : Fin n → Set ℝ) (w : ℝ),
      w ∈ ProductLikeIncidence.familySum Y' →
      ∃ (f : Fin n → ℝ), (∀ i, f i ∈ Y' i) ∧ w = ∑ i : Fin n, f i := by
    intro n
    induction n with
    | zero =>
      intro Y' w hw
      simp [ProductLikeIncidence.familySum] at hw
      refine ⟨fun _ => 0, by simp, by simp [hw]⟩
    | succ n ih =>
      intro Y' w hw
      have h_def : ProductLikeIncidence.familySum Y' =
          Set.image2 (· + ·) (Y' 0) (ProductLikeIncidence.familySum (Y' ∘ Fin.succ)) := by
        simp [ProductLikeIncidence.familySum] <;> rfl
      rw [h_def] at hw
      rcases hw with ⟨a, ha, w', hw', rfl⟩
      rcases ih (Y' ∘ Fin.succ) w' hw' with ⟨f, hf, rfl⟩
      refine ⟨Fin.cons a f, ?_, ?_⟩
      · intro i; exact Fin.cases ha hf i
      · have h_sum2 : ∑ i : Fin (n + 1), Fin.cons a f i = a + ∑ i : Fin n, f i := by
          rw [Fin.sum_univ_succ] <;> simp [Fin.cons_zero, Fin.cons_succ] <;> ring
        rw [h_sum2]
  exact h_main k Y z hz

/-- Minkowski sum associativity for familySum. -/
lemma familySum_append {k1 k2 : ℕ} {Y1 : Fin k1 → Set ℝ} {Y2 : Fin k2 → Set ℝ} :
    Set.image2 (· + ·) (ProductLikeIncidence.familySum Y1)
      (ProductLikeIncidence.familySum Y2) =
    ProductLikeIncidence.familySum (Fin.append Y1 Y2) := by
  ext z
  constructor
  · rintro ⟨w1, hw1, w2, hw2, rfl⟩
    rcases familySum_is_sum hw1 with ⟨f1, hf1, rfl⟩
    rcases familySum_is_sum hw2 with ⟨f2, hf2, rfl⟩
    let f : Fin (k1 + k2) → ℝ := Fin.append f1 f2
    have hf : ∀ i, f i ∈ Fin.append Y1 Y2 i := by
      intro i
      exact Fin.addCases
        (fun a => by simp [f, Fin.append]; exact hf1 a)
        (fun b => by simp [f, Fin.append]; exact hf2 b) i
    have hsum : ∑ i : Fin (k1 + k2), f i = (∑ i, f1 i) + (∑ i, f2 i) := by
      rw [Fin.sum_univ_add] <;> congr <;> funext i <;> simp [f, Fin.append]
    have h_goal : ∑ i : Fin (k1 + k2), f i ∈ ProductLikeIncidence.familySum (Fin.append Y1 Y2) :=
      sum_in_familySum hf
    rwa [hsum] at h_goal
  · intro hz
    rcases familySum_is_sum hz with ⟨f, hf, rfl⟩
    let f1 : Fin k1 → ℝ := fun i => f (Fin.castAdd k2 i)
    let f2 : Fin k2 → ℝ := fun i => f (Fin.natAdd k1 i)
    have hf1 : ∀ i, f1 i ∈ Y1 i := by
      intro i; have h := hf (Fin.castAdd k2 i); simpa [f1, Fin.append] using h
    have hf2 : ∀ i, f2 i ∈ Y2 i := by
      intro i; have h := hf (Fin.natAdd k1 i); simpa [f2, Fin.append] using h
    have hsum : ∑ i : Fin (k1 + k2), f i = (∑ i, f1 i) + (∑ i, f2 i) := by
      rw [Fin.sum_univ_add] <;> congr <;> funext i <;> rfl
    rw [hsum]
    exact ⟨∑ i, f1 i, sum_in_familySum hf1, ∑ i, f2 i, sum_in_familySum hf2, by ring⟩

/-- familySum is invariant under reindexing by an equivalence. -/
lemma familySum_reindex {n m : ℕ} (e : Fin n ≃ Fin m) (Y : Fin n → Set ℝ) :
    ProductLikeIncidence.familySum (Y ∘ e.symm) = ProductLikeIncidence.familySum Y := by
  ext z
  constructor
  · intro hz
    rcases familySum_is_sum hz with ⟨f, hf, rfl⟩
    let g : Fin n → ℝ := f ∘ e
    have hg : ∀ i, g i ∈ Y i := by
      intro i
      simpa [g] using hf (e i)
    have h_sum : ∑ i : Fin n, g i = ∑ i : Fin m, f i :=
      Fintype.sum_equiv e g f (fun i => by simp [g])
    have h_goal : ∑ i : Fin n, g i ∈ ProductLikeIncidence.familySum Y := familySum_mem hg
    rw [h_sum] at h_goal
    exact h_goal
  · intro hz
    rcases familySum_is_sum hz with ⟨g, hg, rfl⟩
    let f : Fin m → ℝ := g ∘ e.symm
    have hf : ∀ j, f j ∈ (Y ∘ e.symm) j := by
      intro j
      simpa [f] using hg (e.symm j)
    have h_sum : ∑ j : Fin m, f j = ∑ i : Fin n, g i :=
      Fintype.sum_equiv e.symm f g (fun j => by simp [f])
    have h_goal : ∑ j : Fin m, f j ∈ ProductLikeIncidence.familySum (Y ∘ e.symm) := familySum_mem hf
    rw [h_sum] at h_goal
    exact h_goal

/-- Negating every set in a family negates the familySum. -/
lemma familySum_neg {k : ℕ} {Y : Fin k → Set ℝ} :
    ProductLikeIncidence.familySum (fun i => scaleSet (-1 : ℝ) (Y i)) =
      Set.image (fun x : ℝ => -x) (ProductLikeIncidence.familySum Y) := by
  induction k with
  | zero =>
    have h0 : ProductLikeIncidence.familySum (fun i : Fin 0 => scaleSet (-1) (Y i)) = ({0} : Set ℝ) := by
      simp [ProductLikeIncidence.familySum]
    have h1 : ProductLikeIncidence.familySum Y = ({0} : Set ℝ) := by
      simp [ProductLikeIncidence.familySum]
    rw [h0, h1]
    <;> simp
  | succ k ih =>
    let Y' : Fin k → Set ℝ := Y ∘ Fin.succ
    let Z : Fin (k + 1) → Set ℝ := fun i => scaleSet (-1) (Y i)
    let Z' : Fin k → Set ℝ := fun i => scaleSet (-1) (Y' i)
    have h_def : ProductLikeIncidence.familySum Z =
        Set.image2 (· + ·) (Z 0) (ProductLikeIncidence.familySum Z') := by
      simp [ProductLikeIncidence.familySum, Z, Z'] <;> rfl
    have hY_def : ProductLikeIncidence.familySum Y =
        Set.image2 (· + ·) (Y 0) (ProductLikeIncidence.familySum Y') := by
      simp [ProductLikeIncidence.familySum, Y'] <;> rfl
    rw [h_def, hY_def]
    rw [ih (Y := Y')]
    ext z
    simp only [Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨a, ha, w, ⟨s, hs, rfl⟩, rfl⟩
      rcases ha with ⟨b, hb, h_eq⟩
      have h_a_eq : a = -b := by
        have h : a = (-1 : ℝ) * b := h_eq.symm
        rw [h] <;> ring
      refine ⟨b + s, ⟨b, hb, s, hs, rfl⟩, ?_⟩
      rw [h_a_eq] <;> ring
    · rintro ⟨t, ⟨b, hb, s, hs, rfl⟩, rfl⟩
      have h1 : -b ∈ scaleSet (-1 : ℝ) (Y 0) := by
        exact ⟨b, hb, by simp [scaleSet] <;> ring⟩
      exact ⟨-b, h1, -s, ⟨s, hs, rfl⟩, by ring⟩

/-- familySum of bounded sets is bounded. -/
lemma familySum_bounded {k : ℕ} {Y : Fin k → Set ℝ}
    (h : ∀ i, Bornology.IsBounded (Y i)) :
    Bornology.IsBounded (ProductLikeIncidence.familySum Y) := by
  induction k with
  | zero =>
    have h0 : ProductLikeIncidence.familySum Y = ({0} : Set ℝ) := by
      simp [ProductLikeIncidence.familySum] <;> rfl
    rw [h0]
    exact Bornology.isBounded_singleton
  | succ k ih =>
    have h1 : ProductLikeIncidence.familySum Y =
        Set.image2 (· + ·) (Y 0) (ProductLikeIncidence.familySum (Y ∘ Fin.succ)) := by
      simp [ProductLikeIncidence.familySum] <;> rfl
    rw [h1]
    have h2 := ih (fun i => h i.succ)
    have h3 : Bornology.IsBounded (Y 0) := h 0
    exact h3.add h2

/-- Build the signed family for all m expansion elements and show containment. -/
lemma weightedSumset_subset_fullFamily {m N0 : ℕ} (x : Fin m → ℝ) (A K : Set ℝ)
    (u v : Fin m → Fin N0 → ℝ)
    (hu : ∀ i j, u i j ∈ productSetN K N0)
    (hv : ∀ i j, v i j ∈ productSetN K N0)
    (h_unpack : ∀ i, x i = (∑ j, u i j) - (∑ j, v i j)) :
    ∃ (Y : Fin (2 * m * N0) → Set ℝ),
      weightedSumset x A ⊆ ProductLikeIncidence.familySum Y ∧
      (∀ (idx : Fin (2 * m * N0)), ∃ (z : ℝ), z ∈ productSetN K N0 ∧
        (Y idx = scaleSet z A ∨ Y idx = scaleSet (-z) A)) := by
  have h_main : ∀ (k : ℕ) (y : Fin k → ℝ)
      (u v : Fin k → Fin N0 → ℝ)
      (hu : ∀ i j, u i j ∈ productSetN K N0)
      (hv : ∀ i j, v i j ∈ productSetN K N0),
      (∀ i, y i = (∑ j, u i j) - (∑ j, v i j)) →
      ∃ (Y : Fin (2 * k * N0) → Set ℝ),
        weightedSumset y A ⊆ ProductLikeIncidence.familySum Y ∧
        (∀ idx, ∃ (z : ℝ), z ∈ productSetN K N0 ∧
          (Y idx = scaleSet z A ∨ Y idx = scaleSet (-z) A)) := by
    intro k
    induction k with
    | zero =>
      intro y u v hu hv h
      refine ⟨fun _ => ∅, ?_, ?_⟩
      · have h_eq : 2 * 0 * N0 = 0 := by ring
        have h_base : ProductLikeIncidence.familySum (fun _ : Fin 0 => ∅) = ({0} : Set ℝ) := by
          simp [ProductLikeIncidence.familySum]
        have h2 : ProductLikeIncidence.familySum (fun _ : Fin (2 * 0 * N0) => ∅) = ({0} : Set ℝ) :=
          h_eq.symm ▸ h_base
        have h1 : weightedSumset y A = ({0} : Set ℝ) := by
          ext z; simp [weightedSumset, Fin.sum_univ_zero]
        rw [h1, h2]
      · intro idx
        have h_eq : 2 * 0 * N0 = 0 := by ring
        exact Fin.elim0 (h_eq ▸ idx)
    | succ k ih =>
      intro y u v hu hv h_unpack
      let y0 := y 0
      let y_rest := y ∘ Fin.succ
      let u0 := u 0
      let v0 := v 0
      let u_rest := u ∘ Fin.succ
      let v_rest := v ∘ Fin.succ
      have h0 : y0 = (∑ j, u0 j) - (∑ j, v0 j) := h_unpack 0
      have h_rest_unpack : ∀ i, y_rest i = (∑ j, u_rest i j) - (∑ j, v_rest i j) :=
        fun i => h_unpack i.succ
      have hu_rest : ∀ i j, u_rest i j ∈ productSetN K N0 := fun i j => hu i.succ j
      have hv_rest : ∀ i j, v_rest i j ∈ productSetN K N0 := fun i j => hv i.succ j
      rcases ih y_rest u_rest v_rest hu_rest hv_rest h_rest_unpack with ⟨Y_rest, h_sub_rest, h_wit_rest⟩
      let Y0 := expansionFamily A N0 u0 v0
      let Y_raw : Fin (N0 + N0 + 2 * k * N0) → Set ℝ := Fin.append Y0 Y_rest
      have h_eq : 2 * (k + 1) * N0 = N0 + N0 + 2 * k * N0 := by ring
      let e : Fin (2 * (k + 1) * N0) ≃ Fin (N0 + N0 + 2 * k * N0) :=
        h_eq ▸ Equiv.refl (Fin (2 * (k + 1) * N0))
      let Y : Fin (2 * (k + 1) * N0) → Set ℝ := Y_raw ∘ e
      have h_cast_family : ProductLikeIncidence.familySum Y = ProductLikeIncidence.familySum Y_raw :=
        familySum_reindex e.symm Y_raw
      have h1 : weightedSumset y A ⊆
          Set.image2 (· + ·) (ProductLikeIncidence.familySum Y0)
            (ProductLikeIncidence.familySum Y_rest) := by
        rw [weightedSumset_succ y A]
        intro z hz
        rcases hz with ⟨w1, hw1, w2, hw2, rfl⟩
        have h_w1 : w1 ∈ ProductLikeIncidence.familySum Y0 :=
          scaleSet_expansion_subset u0 v0 h0 hw1
        exact ⟨w1, h_w1, w2, h_sub_rest hw2, rfl⟩
      have h2 : Set.image2 (· + ·) (ProductLikeIncidence.familySum Y0)
            (ProductLikeIncidence.familySum Y_rest) =
          ProductLikeIncidence.familySum Y_raw := familySum_append
      have h3 : weightedSumset y A ⊆ ProductLikeIncidence.familySum Y := by
        calc weightedSumset y A
          ⊆ Set.image2 (· + ·) (ProductLikeIncidence.familySum Y0) (ProductLikeIncidence.familySum Y_rest) := h1
        _ = ProductLikeIncidence.familySum Y_raw := h2
        _ = ProductLikeIncidence.familySum Y := h_cast_family.symm
      refine ⟨Y, h3, ?_⟩
      intro idx
      let idx' : Fin (N0 + N0 + 2 * k * N0) := e idx
      have hY : Y idx = Y_raw idx' := by rfl
      exact Fin.addCases
        (motive := fun (i : Fin (N0 + N0 + 2 * k * N0)) =>
          ∃ (z : ℝ), z ∈ productSetN K N0 ∧
            (Y_raw i = scaleSet z A ∨ Y_raw i = scaleSet (-z) A))
        (fun a => by
          have hY0 : Y_raw (Fin.castAdd _ a) = Y0 a := by
            simp [Y_raw, Fin.append]
          rcases expansionFamily_member_witness u0 v0 (hu 0) (hv 0) a with ⟨z, hz, h_case⟩
          refine ⟨z, hz, ?_⟩
          rw [hY0]
          exact h_case)
        (fun b => by
          have hYrest : Y_raw (Fin.natAdd _ b) = Y_rest b := by
            simp [Y_raw, Fin.append]
          rcases h_wit_rest b with ⟨z, hz, h_case⟩
          refine ⟨z, hz, ?_⟩
          rw [hYrest]
          exact h_case)
        idx'
  exact h_main m x u v hu hv h_unpack

set_option maxHeartbeats 500000

/-- **Full Steps 6–8**: Extract `y ∈ productSetN K N0` with DIFFERENCE gain.

Uses multi-set PR on the **negated** signed family. If the bad term in the
negated family corresponds to a positive original term, we get a direct
difference. If it corresponds to a negative original term, we apply the
cubic sum-to-difference inequality.

The cubic case requires `h_cubic_absorb` to absorb the scaling constant. -/
lemma step6_8_full_difference
    {A K : Set ℝ} {N0 m : ℕ}
    {δ t s ε κ : ℝ} (hκ_pos : 0 < κ) (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hδ_pos : 0 < δ) (ht_pos : 0 < t) (ht_le_one : t ≤ 1) (hε_pos : 0 < ε)
    {x : Fin m → ℝ} (hx_in_X : ∀ i, x i ∈ expansionSet K N0)
    (h_sumset_large : ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) ≤
        Nreal δ (weightedSumset x A))
    (h_εm : ε * (m : ℝ) < (1 - s) / 2)
    (h_t_lower : δ ^ ((1 - s) / 4) ≤ t)
    (hA_size : Nreal δ A ≤ ENNReal.ofReal (δ ^ (-s)))
    (hK_bounds : K ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1)
    (ε_tloss : ℝ) (hε_tloss_pos : 0 < ε_tloss)
    (γ : ℝ) (hγ_pos : 0 < γ)
    (hγ_eq : γ = (1 - s) / 2 - ε * (m : ℝ) - 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss)
    (hδ_poly : δ ^ γ ≤ (step6_full_C m N0 κ)⁻¹)
    (h_tloss : t ^ (2 / 3 : ℝ) ≥ δ ^ ε_tloss)
    (h_cubic_absorb : δ ^ (3 * ε_tloss) ≤
        1 / (486 * ((2 : ℝ)^((N0 : ℝ)/κ) + 3)))
    (δ₀ : ℝ) (hδ_small : δ ≤ δ₀) (hδ₀_le_one : δ₀ ≤ 1)
    (hK_bdd : Bornology.IsBounded K) (hA_bdd : Bornology.IsBounded A) :
    ∃ (y : ℝ), y ∈ productSetN K N0 ∧
      ENNReal.ofReal (δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss)) *
        Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet t⁻¹ A) (scaleSet y A)) := by
  have hδ_le_one : δ ≤ 1 := le_trans hδ_small hδ₀_le_one
  have hδ_nonneg : 0 ≤ δ := by linarith
  set k : ℕ := 2 * m * N0 with hk_def

  -- Edge cases
  by_cases hm : m = 0
  · subst hm
    have hC_zero : step6_full_C 0 N0 κ = 0 := by
      simp [step6_full_C] <;> norm_num
    rw [hC_zero] at hδ_poly
    have h_exp_pos : 0 < γ := hγ_pos
    have h_pos : 0 < δ ^ γ := Real.rpow_pos_of_pos hδ_pos _
    linarith
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm

  by_cases hN0 : N0 = 0
  · subst hN0
    have hC_zero : step6_full_C m 0 κ = 0 := by
      simp [step6_full_C] <;> norm_num
    rw [hC_zero] at hδ_poly
    have h_exp_pos : 0 < γ := hγ_pos
    have h_pos : 0 < δ ^ γ := Real.rpow_pos_of_pos hδ_pos _
    linarith
  have hN0_pos : 0 < N0 := Nat.pos_of_ne_zero hN0

  have hk_pos : 0 < k := by
    simp [hk_def, hm_pos, hN0_pos] <;> omega

  -- A nonempty
  have hA_nonempty : A.Nonempty := by
    by_contra h
    have h' : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_empty : weightedSumset x A = ∅ := by
      ext z
      simp only [weightedSumset, Set.mem_empty_iff_false, Set.mem_setOf_eq, iff_false]
      rintro ⟨a, ha, rfl⟩
      let i : Fin m := ⟨0, hm_pos⟩
      have h_contra : a i ∈ A := ha i
      rw [h'] at h_contra
      simpa [h'] using h_contra
    rw [h_empty] at h_sumset_large
    have hN_empty : Nreal δ (∅ : Set ℝ) = 0 := by
      have h1 : realLineCopy (∅ : Set ℝ) = (∅ : Set (EuclideanSpace ℝ (Fin 1))) := by
        ext x; simp [realLineCopy]
      simp [Nreal, dyadicCoveringNumber, dyadicCubesMeeting, h1]
    rw [hN_empty] at h_sumset_large
    have h_pos' : 0 < ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) := by positivity
    have h_cont : ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) ≤ 0 := h_sumset_large
    have h_eq : ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) = 0 := by simpa using h_cont
    rw [h_eq] at h_pos'; simpa using h_pos'

  let X := scaleSet t⁻¹ A
  have hX_bdd : Bornology.IsBounded X := scaleSet_bounded hA_bdd
  have hX_nonempty : X.Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    exact ⟨t⁻¹ * a, ⟨a, ha, rfl⟩⟩
  have hX_bound : Nreal δ X ≤ ENNReal.ofReal (3 * δ ^ (-(1 + 3 * s) / 4)) :=
    covering_scaled_bound hδ_pos hδ_le_one ht_pos h_t_lower hs_pos hs_lt_one hA_bdd hA_size

  -- Unpack all x_i
  choose u v hu hv h_unpack using fun i => expansionSet_unpack (hx_in_X i)

  -- Build signed family
  rcases weightedSumset_subset_fullFamily x A K u v hu hv h_unpack with ⟨Y, h_contain, h_wit⟩

  -- Negated family
  let negY : Fin (2 * m * N0) → Set ℝ := fun idx => scaleSet (-1 : ℝ) (Y idx)
  have hY_bdd : ∀ i, Bornology.IsBounded (Y i) := by
    intro i
    rcases h_wit i with ⟨z, _, h_case⟩
    rcases h_case with (h | h)
    · rw [h]; exact scaleSet_bounded hA_bdd
    · rw [h]; exact scaleSet_bounded hA_bdd
  have h_familyY_bdd : Bornology.IsBounded (ProductLikeIncidence.familySum Y) :=
    familySum_bounded hY_bdd
  have h_negY_familySum : ProductLikeIncidence.familySum negY =
      Set.image (fun x : ℝ => -x) (ProductLikeIncidence.familySum Y) :=
    familySum_neg
  have h_negY_size : Nreal δ (ProductLikeIncidence.familySum negY) ≥
      ENNReal.ofReal (1 / 2 : ℝ) * Nreal δ (ProductLikeIncidence.familySum Y) := by
    rw [h_negY_familySum]
    set S := ProductLikeIncidence.familySum Y with hS
    set S' := Set.image (fun x : ℝ => -x) S with hS'
    have hS'_bdd : Bornology.IsBounded S' := by
      have h_neg_lipschitz : LipschitzWith 1 (fun x : ℝ => -x) := by
        intro x y
        simp [Real.dist_eq, abs_neg] <;> ring_nf <;> exact le_refl _
      exact h_neg_lipschitz.isBounded_image h_familyY_bdd
    have h1 : Nreal δ S' ≤ 2 * Nreal δ S :=
      covering_negation_le_two hδ_pos h_familyY_bdd
    have h2 : Nreal δ S ≤ 2 * Nreal δ S' := by
      have h3 : S = Set.image (fun x : ℝ => -x) S' := by
        ext z; simp [hS', Set.image_image] <;> ring
      rw [h3]
      exact covering_negation_le_two hδ_pos hS'_bdd
    have h5 : ENNReal.ofReal (1 / 2 : ℝ) * (2 * Nreal δ S') = Nreal δ S' := by
      have h6 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by exact Eq.symm (ENNReal.ofReal_ofNat 2)
      have h7 : ENNReal.ofReal (1 / 2 : ℝ) * (2 : ENNReal) = 1 := by
        rw [h6, ← ENNReal.ofReal_mul (by positivity)]
        <;> norm_num
      calc
        ENNReal.ofReal (1 / 2 : ℝ) * (2 * Nreal δ S')
          = (ENNReal.ofReal (1 / 2 : ℝ) * (2 : ENNReal)) * Nreal δ S' := by ring
        _ = (1 : ENNReal) * Nreal δ S' := by rw [h7]
        _ = Nreal δ S' := by simp
    have h4 : ENNReal.ofReal (1 / 2 : ℝ) * Nreal δ S ≤ Nreal δ S' := by
      calc ENNReal.ofReal (1 / 2 : ℝ) * Nreal δ S
        ≤ ENNReal.ofReal (1 / 2 : ℝ) * (2 * Nreal δ S') := by gcongr <;> exact h2
      _ = Nreal δ S' := h5
    exact h4

  have h_familyY_large : Nreal δ (ProductLikeIncidence.familySum Y) ≥
      ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) := by
    have h : Nreal δ (weightedSumset x A) ≤ Nreal δ (ProductLikeIncidence.familySum Y) :=
      Nreal_mono h_contain
    exact le_trans h_sumset_large h

  have h_familyNegY_large : Nreal δ (ProductLikeIncidence.familySum negY) ≥
      ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ (-1 + ε * (m : ℝ))) := by
    calc
      Nreal δ (ProductLikeIncidence.familySum negY)
        ≥ ENNReal.ofReal (1 / 2 : ℝ) * Nreal δ (ProductLikeIncidence.familySum Y) := h_negY_size
      _ ≥ ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (δ ^ (-1 + ε * (m : ℝ))) := by
          gcongr <;> exact h_familyY_large
      _ = ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ (-1 + ε * (m : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> ring

  -- PR exponent
  let a : ℝ := (3 * (1 - s) / 4 - ε * (m : ℝ) - γ) / (k : ℝ)
  have ha_pos : 0 < a := by
    have h_expand : 3 * (1 - s) / 4 - ε * (m : ℝ) - γ =
        (1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss := by
      rw [hγ_eq] <;> ring
    have h_pos1 : 0 < (1 - s) / 4 := by linarith
    have h_pos2 : 0 < 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss := by positivity
    have h1 : 0 < 3 * (1 - s) / 4 - ε * (m : ℝ) - γ := by
      rw [h_expand] <;> linarith
    have hk_pos' : 0 < (k : ℝ) := by exact_mod_cast hk_pos
    exact div_pos h1 hk_pos'
  let α : ℝ := δ ^ (-a)

  have h_ak : a * (k : ℝ) = 3 * (1 - s) / 4 - ε * (m : ℝ) - γ := by
    dsimp only [a]
    field_simp [hk_pos.ne'] <;> ring

  -- PR constant check
  have hC_full_pos : 0 < step6_full_C m N0 κ := by
    have h_k_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
    have h_cp_pos : 0 < (2 : ℝ) ^ ((N0 : ℝ) / κ) + 2 := by positivity
    have h : 0 < (486 * (k : ℝ) * ((2 : ℝ) ^ ((N0 : ℝ) / κ) + 2)) ^ k := by positivity
    have h' : 0 < (k : ℝ) * (486 * (k : ℝ) * ((2 : ℝ) ^ ((N0 : ℝ) / κ) + 2)) ^ k := mul_pos h_k_pos h
    have h_unfold : step6_full_C m N0 κ = (k : ℝ) * (486 * (k : ℝ) * ((2 : ℝ) ^ ((N0 : ℝ) / κ) + 2)) ^ k := by
      simp [step6_full_C, hk_def] <;> rfl
    rw [h_unfold]
    exact h'
  have h_PR_const : 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ < 1 := by
    let C_p : ℝ := (2 : ℝ) ^ ((N0 : ℝ) / κ) + 2
    have hC_p_gt_two : C_p > 2 := by simp [C_p] <;> positivity
    have hk_pos' : 0 < (k : ℝ) := by exact_mod_cast hk_pos
    have h_k_ge_one : 1 ≤ k := by omega
    have h_gt : 486 * (k : ℝ) * C_p > 12 * (k : ℝ) := by nlinarith
    have h_pow_gt : (486 * (k : ℝ) * C_p) ^ k > (12 * (k : ℝ)) ^ k := by
      gcongr <;> linarith
    have h12 : (12 * (k : ℝ)) ^ k ≥ 6 * (2 * (k : ℝ)) ^ k := by
      have h_eq : (12 * (k : ℝ)) = 6 * (2 * (k : ℝ)) := by ring
      rw [h_eq]
      have h : (6 * (2 * (k : ℝ))) ^ k = (6 ^ k : ℝ) * ((2 * (k : ℝ)) ^ k) := by
        rw [mul_pow] <;> ring
      rw [h]
      have h6k : (6 ^ k : ℝ) ≥ 6 := by
        have h_k_ge_one' : 1 ≤ k := h_k_ge_one
        have h : 6 ^ 1 ≤ 6 ^ k := by gcongr <;> omega
        have h' : (6 ^ k : ℝ) ≥ (6 ^ 1 : ℝ) := by exact_mod_cast h
        simpa using h'
      have h2k_pos : 0 ≤ (2 * (k : ℝ)) ^ k := by positivity
      have h_goal : (6 ^ k : ℝ) * ((2 * (k : ℝ)) ^ k) ≥ 6 * ((2 * (k : ℝ)) ^ k) := by
        exact mul_le_mul_of_nonneg_right h6k h2k_pos
      exact h_goal
    have h_ineq : (486 * (k : ℝ) * C_p) ^ k > 6 * (2 * (k : ℝ)) ^ k := by
      calc
        (486 * (k : ℝ) * C_p) ^ k > (12 * (k : ℝ)) ^ k := h_pow_gt
        _ ≥ 6 * (2 * (k : ℝ)) ^ k := h12
    have h_final : 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k < (k : ℝ) * (486 * (k : ℝ) * C_p) ^ k := by
      have h_ineq' : 6 * (2 * (k : ℝ)) ^ k < (486 * (k : ℝ) * C_p) ^ k := h_ineq
      have h : (k : ℝ) * (6 * (2 * (k : ℝ)) ^ k) < (k : ℝ) * ((486 * (k : ℝ) * C_p) ^ k) :=
        mul_lt_mul_of_pos_left h_ineq' hk_pos'
      have h' : 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k = (k : ℝ) * (6 * (2 * (k : ℝ)) ^ k) := by ring
      rw [h']
      exact h
    have h_unfold : step6_full_C m N0 κ = (k : ℝ) * (486 * (k : ℝ) * C_p) ^ k := by
      simp only [step6_full_C]
      <;> rfl
    have h1 : 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k < step6_full_C m N0 κ := by
      rw [h_unfold]
      exact h_final
    have h2 : δ ^ γ ≤ (step6_full_C m N0 κ)⁻¹ := hδ_poly
    have h_pos1 : 0 < δ ^ γ := Real.rpow_pos_of_pos hδ_pos _
    have h_pos2 : 0 < (step6_full_C m N0 κ)⁻¹ := by positivity
    have h3 : 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ <
        (step6_full_C m N0 κ) * (step6_full_C m N0 κ)⁻¹ := by
      calc
        6 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ
          ≤ 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k * (step6_full_C m N0 κ)⁻¹ := by gcongr
        _ < (step6_full_C m N0 κ) * (step6_full_C m N0 κ)⁻¹ := by
          apply mul_lt_mul_of_pos_right h1
          positivity
    have h4 : (step6_full_C m N0 κ) * (step6_full_C m N0 κ)⁻¹ = 1 := by
      field_simp [hC_full_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3

  -- Boundedness of negY terms
  have hY_bdd : ∀ i, Bornology.IsBounded (Y i) := by
    intro i
    rcases h_wit i with ⟨z, hz, (h | h)⟩
    · rw [h]; exact scaleSet_bounded hA_bdd
    · rw [h]; exact scaleSet_bounded hA_bdd
  have h_negY_bdd : ∀ i, Bornology.IsBounded (negY i) := fun i => scaleSet_bounded (hY_bdd i)

  -- PR contrapositive on negY
  by_cases h_main : ∃ (i : Fin (2 * m * N0)), ¬(Nreal δ (Set.image2 (· + ·) X (negY i)) ≤
      ENNReal.ofReal α * Nreal δ X)
  · rcases h_main with ⟨i, hi⟩
    have h_gt : ENNReal.ofReal α * Nreal δ X < Nreal δ (Set.image2 (· + ·) X (negY i)) :=
      not_le.mp hi
    rcases h_wit i with ⟨z, hz, h_case⟩
    -- Determine sign of negY i
    by_cases h_sign : Y i = scaleSet z A
    · -- Case 1: Y i = zA, so negY i = -zA, direct difference
      have h_negY : negY i = scaleSet (-z) A := by
        have h1 : negY i = scaleSet (-1) (Y i) := by rfl
        rw [h1, h_sign]
        ext y
        simp only [scaleSet, Set.mem_image]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rcases hx with ⟨a, ha, rfl⟩
          exact ⟨a, ha, by ring⟩
        · rintro ⟨a, ha, rfl⟩
          have hxa : z * a ∈ scaleSet z A := ⟨a, ha, by ring⟩
          exact ⟨z * a, hxa, by ring⟩
      rw [h_negY] at h_gt
      have h_final : ENNReal.ofReal (δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss)) *
          Nreal δ X ≤ Nreal δ (Set.image2 (· - ·) X (scaleSet z A)) := by
        have h_ak2 : a * (k : ℝ) = (1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss := by
          rw [h_ak, hγ_eq] <;> ring
        have hk_pos' : 0 < (k : ℝ) := by exact_mod_cast hk_pos
        have h_a_lower : a ≥ (1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) - ε_tloss := by
          have h_k_def : (k : ℝ) = 2 * (m : ℝ) * (N0 : ℝ) := by
            exact_mod_cast hk_def
          have h_pos_mn : 0 < 2 * (m : ℝ) * (N0 : ℝ) := by positivity
          have h9 : a * (2 * (m : ℝ) * (N0 : ℝ)) = (1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss := by
            rw [← h_k_def]
            exact h_ak2
          have h10 : a * (2 * (m : ℝ) * (N0 : ℝ)) ≥
              (2 * (m : ℝ) * (N0 : ℝ)) * ((1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) - ε_tloss) := by
            rw [h9]
            have h_pos1 : 0 < (m : ℝ) := by exact_mod_cast hm_pos
            have h_pos2 : 0 < (N0 : ℝ) := by exact_mod_cast hN0_pos
            set d := 2 * (m : ℝ) * (N0 : ℝ) with hd
            have h_eq : d * ((1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) - ε_tloss) =
                (1 - s) / 12 - d * ε_tloss := by
              simp [hd, h_pos1.ne', h_pos2.ne'] <;> field_simp <;> ring
            rw [h_eq]
            have h3 : (1 - s) / 4 ≥ (1 - s) / 12 := by
              apply div_le_div_of_nonneg_left <;> linarith
            have h4 : 0 ≤ d * ε_tloss := by positivity
            have h5 : 0 ≤ (m : ℝ) * (N0 : ℝ) * ε_tloss := by positivity
            nlinarith
          have h11 : (2 * (m : ℝ) * (N0 : ℝ)) * a ≥ (2 * (m : ℝ) * (N0 : ℝ)) * ((1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) - ε_tloss) := by
            have h_comm : a * (2 * (m : ℝ) * (N0 : ℝ)) = (2 * (m : ℝ) * (N0 : ℝ)) * a := by ring
            rw [h_comm] at h10
            exact h10
          have h12 : a ≥ (1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) - ε_tloss := by
            have h_pos : 0 < 2 * (m : ℝ) * (N0 : ℝ) := h_pos_mn
            nlinarith
          exact h12
        have h5 : -a ≤ -((1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) - ε_tloss) := by linarith
        have h6 : δ ^ (-a) ≥ δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss) := by
          have h7 : -a ≤ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss) := by
            have h8 : -((1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) - ε_tloss) =
                (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss) := by ring
            rw [h8] at h5
            exact h5
          have h9 : 0 < δ := hδ_pos
          have h10 : δ ≤ 1 := hδ_le_one
          exact Real.rpow_le_rpow_of_exponent_ge h9 h10 h7
        have h7 : ENNReal.ofReal (δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss)) * Nreal δ X ≤
            ENNReal.ofReal α * Nreal δ X := by
          have h8 : α = δ ^ (-a) := by rfl
          have h10 : ENNReal.ofReal (δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss)) ≤ ENNReal.ofReal α := by
            rw [h8]
            exact ENNReal.ofReal_le_ofReal h6
          have h11 : ENNReal.ofReal (δ ^ (-(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss)) * Nreal δ X ≤
              ENNReal.ofReal α * Nreal δ X := by
            exact mul_le_mul_of_nonneg_right h10 (by positivity)
          exact h11
        have h_set_eq : Set.image2 (· + ·) X (scaleSet (-z) A) = Set.image2 (· - ·) X (scaleSet z A) := by
          apply Set.ext
          intro y
          constructor
          · rintro ⟨x, hx, w, hw, rfl⟩
            rcases hw with ⟨a, ha, rfl⟩
            exact ⟨x, hx, z * a, ⟨a, ha, by ring⟩, by ring⟩
          · rintro ⟨x, hx, w, hw, rfl⟩
            rcases hw with ⟨a, ha, rfl⟩
            exact ⟨x, hx, -z * a, ⟨a, ha, by ring⟩, by ring⟩
        rw [h_set_eq] at h_gt
        exact le_trans h7 h_gt.le
      exact ⟨z, hz, h_final⟩
    · -- Case 2: Y i = -zA, so negY i = zA, need cubic sum-to-diff
      have hY2 : Y i = scaleSet (-z) A := by
        rcases h_case with (h | h)
        · contradiction
        · exact h
      have h_negY : negY i = scaleSet z A := by
        simp [negY, hY2] <;> ext y; simp [scaleSet] <;> ring
      rw [h_negY] at h_gt
      -- Cubic sum-to-diff
      have hz_bounds : (2 : ℝ)^(-(N0 : ℝ)/κ) ≤ z ∧ z ≤ 1 :=
        productSetN_bounds hκ_pos hK_bounds hz
      have hz_pos : 0 < z := by
        have h_lower : (2 : ℝ)^(-(N0 : ℝ)/κ) ≤ z := hz_bounds.1
        have h_pos_lower : 0 < (2 : ℝ)^(-(N0 : ℝ)/κ) := Real.rpow_pos_of_pos (by norm_num) _
        exact h_pos_lower.trans_le h_lower
      let N_sum := Nreal δ (Set.image2 (· + ·) X (scaleSet z A))
      let N_diff := Nreal δ (Set.image2 (· - ·) X (scaleSet z A))
      let N_zA := Nreal δ (scaleSet z A)
      let N_X := Nreal δ X
      let c_ratio : ℝ := 1 / (3 * ((2 : ℝ)^((N0 : ℝ)/κ) + 3))
      have h_scaling : N_zA ≥ ENNReal.ofReal (c_ratio * t) * N_X :=
        step6_scaling_ratio hδ_pos ht_pos ht_le_one hA_bdd hκ_pos hz hK_bounds
      have h_sum_to_diff_raw : N_sum * N_X * N_zA ≤
          162 * N_diff * N_diff * N_diff :=
        sum_to_diff_lower hδ_pos hX_bdd (scaleSet_bounded hA_bdd) hX_nonempty
          (show (scaleSet z A).Nonempty from by
            rcases hA_nonempty with ⟨a, ha⟩; exact ⟨z * a, ⟨a, ha, rfl⟩⟩)
      have h_sum_to_diff : N_sum * N_X * N_zA ≤ (162 : ENNReal) * N_diff ^ 3 := by
        have h_eq : 162 * N_diff * N_diff * N_diff = (162 : ENNReal) * N_diff ^ 3 := by
          simp [pow_succ] <;> ring
        rw [h_eq] at h_sum_to_diff_raw
        exact h_sum_to_diff_raw
      have h10 : N_sum ≥ ENNReal.ofReal α * N_X := h_gt.le
      have h11 : N_zA ≥ ENNReal.ofReal (c_ratio * t) * N_X := h_scaling
      -- Lower bound the product
      have h_product : N_sum * N_X * N_zA ≥
          (ENNReal.ofReal α * N_X) * N_X * (ENNReal.ofReal (c_ratio * t) * N_X) := by
        calc
          N_sum * N_X * N_zA
            = N_X * (N_sum * N_zA) := by ring
          _ ≥ N_X * ((ENNReal.ofReal α * N_X) * (ENNReal.ofReal (c_ratio * t) * N_X)) := by gcongr
          _ = (ENNReal.ofReal α * N_X) * N_X * (ENNReal.ofReal (c_ratio * t) * N_X) := by ring
      -- Divide by 162
      have h_div_le : (N_sum * N_X * N_zA) / 162 ≤ N_diff ^ 3 := by
        have h : N_sum * N_X * N_zA ≤ (162 : ENNReal) * N_diff ^ 3 := h_sum_to_diff
        have h2 : (N_sum * N_X * N_zA) / 162 ≤ ((162 : ENNReal) * N_diff ^ 3) / 162 := by gcongr
        have h3 : ((162 : ENNReal) * N_diff ^ 3) / 162 = N_diff ^ 3 := by
          have h_div : ((162 : ENNReal) * N_diff ^ 3) / 162 =
              N_diff ^ 3 * ((162 : ENNReal) / 162) := by
            simp only [div_eq_mul_inv] <;> ring
          rw [h_div]
          have h6 : (162 : ENNReal) / 162 = 1 := by
            have h7 : (162 : ENNReal) / 162 = (162 : ENNReal) * (162 : ENNReal)⁻¹ := by rfl
            rw [h7]
            have h8 : (162 : ENNReal) * (162 : ENNReal)⁻¹ = (162 : ENNReal)⁻¹ * (162 : ENNReal) := by ring
            rw [h8]
            exact ENNReal.inv_mul_cancel (by simp) (by simp)
          rw [h6, mul_one]
        rw [h3] at h2; exact h2
      have h_div_ge : (N_sum * N_X * N_zA) / 162 ≥
          ((ENNReal.ofReal α * N_X) * N_X * (ENNReal.ofReal (c_ratio * t) * N_X)) / 162 := by
        gcongr
      -- Simplify RHS to C_enn * N_X^3
      let C_enn : ENNReal := ENNReal.ofReal (δ ^ (-a) * c_ratio * t / 162)
      have hα_def : α = δ ^ (-a) := by rfl
      have h9_rhs : ((ENNReal.ofReal α * N_X) * N_X * (ENNReal.ofReal (c_ratio * t) * N_X)) / 162 =
          C_enn * N_X ^ 3 := by
        have h_pos1 : 0 ≤ α := by positivity
        have h_pos2 : 0 ≤ c_ratio * t := by positivity
        have h_pos3 : 0 ≤ α * c_ratio * t := by positivity
        have h1 : (ENNReal.ofReal α * N_X) * N_X * (ENNReal.ofReal (c_ratio * t) * N_X) =
            ENNReal.ofReal (α * c_ratio * t) * N_X ^ 3 := by
          have h21 : ENNReal.ofReal (α * (c_ratio * t)) =
              ENNReal.ofReal α * ENNReal.ofReal (c_ratio * t) := ENNReal.ofReal_mul h_pos1
          have h22 : α * (c_ratio * t) = α * c_ratio * t := by ring
          rw [h22] at h21
          calc
            (ENNReal.ofReal α * N_X) * N_X * (ENNReal.ofReal (c_ratio * t) * N_X)
              = ENNReal.ofReal α * ENNReal.ofReal (c_ratio * t) * (N_X * N_X * N_X) := by ring
            _ = ENNReal.ofReal (α * c_ratio * t) * (N_X * N_X * N_X) := by
              rw [h21.symm] <;> ring
            _ = ENNReal.ofReal (α * c_ratio * t) * N_X ^ 3 := by
              simp [pow_succ] <;> ring
        rw [h1]
        have h4 : (ENNReal.ofReal (α * c_ratio * t) * N_X ^ 3) / 162 =
            (ENNReal.ofReal (α * c_ratio * t) / 162) * N_X ^ 3 := by
          simp only [div_eq_mul_inv] <;> ring
        rw [h4]
        have h_pos4 : 0 ≤ α * c_ratio * t := h_pos3
        have h5 : ENNReal.ofReal (α * c_ratio * t) / 162 = ENNReal.ofReal ((α * c_ratio * t) / 162) := by
          have h9 : (162 : ENNReal)⁻¹ = ENNReal.ofReal ((1 / 162 : ℝ)) := by simp
          have h10 : ENNReal.ofReal (α * c_ratio * t) / 162 =
              ENNReal.ofReal (α * c_ratio * t) * (162 : ENNReal)⁻¹ := by rfl
          rw [h10, h9]
          have h11 : ENNReal.ofReal (α * c_ratio * t) * ENNReal.ofReal (1 / 162 : ℝ) =
              ENNReal.ofReal ((α * c_ratio * t) * (1 / 162 : ℝ)) := by
            exact (ENNReal.ofReal_mul h_pos4).symm
          rw [h11]
          have h12 : (α * c_ratio * t) * (1 / 162 : ℝ) = (α * c_ratio * t) / 162 := by ring
          rw [h12]
          <;> rfl
        rw [h5]
        <;> rfl
      have h9 : C_enn * N_X ^ 3 ≤ N_diff ^ 3 := by
        calc
          C_enn * N_X ^ 3
            = ((ENNReal.ofReal α * N_X) * N_X * (ENNReal.ofReal (c_ratio * t) * N_X)) / 162 := h9_rhs.symm
          _ ≤ (N_sum * N_X * N_zA) / 162 := h_div_ge
          _ ≤ N_diff ^ 3 := h_div_le
      -- Exponent arithmetic
      set b : ℝ := (1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) with hb_def
      have h_ak2' : a * (k : ℝ) = (1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss := by
        rw [h_ak, hγ_eq] <;> ring
      have h_k_def : (k : ℝ) = 2 * (m : ℝ) * (N0 : ℝ) := by
        exact_mod_cast hk_def
      have h_a3b : a - 3 * b = 3 * ε_tloss / 2 := by
        have h_pos_mn : 0 < (m : ℝ) * (N0 : ℝ) := by positivity
        have h_posk : (k : ℝ) ≠ 0 := by exact_mod_cast hk_pos.ne'
        have h_a_eq : a = ((1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss) / (k : ℝ) := by
          calc
            a = (a * (k : ℝ)) / (k : ℝ) := by field_simp [h_posk] <;> ring
            _ = ((1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss) / (k : ℝ) := by rw [h_ak2']
        have h_k_real : (k : ℝ) = 2 * (m : ℝ) * (N0 : ℝ) := h_k_def
        have h_a_expand : a = ((1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss) / (2 * (m : ℝ) * (N0 : ℝ)) := by
          rw [h_a_eq, h_k_real]
        have h_b_expand : 3 * b = (1 - s) / (8 * (m : ℝ) * (N0 : ℝ)) := by
          rw [hb_def]
          field_simp [h_pos_mn.ne'] <;> ring
        rw [h_a_expand, h_b_expand]
        have h_expand2 : (((1 - s) / 4 + 3 * (m : ℝ) * (N0 : ℝ) * ε_tloss) / (2 * (m : ℝ) * (N0 : ℝ))) -
            (1 - s) / (8 * (m : ℝ) * (N0 : ℝ)) = 3 * ε_tloss / 2 := by
          field_simp [h_pos_mn.ne'] <;> ring
        exact h_expand2
      have h1_nonneg : 0 ≤ t := by linarith
      have h_tloss' : t ≥ δ ^ (3 * ε_tloss / 2) := by
        have h2 : (t ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = t := by
          rw [← Real.rpow_mul h1_nonneg] <;> ring_nf <;> rw [Real.rpow_one]
        have h4 : (δ ^ ε_tloss) ^ (3 / 2 : ℝ) = δ ^ (3 * ε_tloss / 2) := by
          rw [← Real.rpow_mul hδ_nonneg] <;> ring_nf
        have h5 : 0 ≤ t ^ (2 / 3 : ℝ) := by positivity
        have h6 : 0 ≤ δ ^ ε_tloss := by positivity
        have h7 : (t ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≥ (δ ^ ε_tloss) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow h6 h_tloss (by norm_num)
        calc
          t = (t ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := h2.symm
          _ ≥ (δ ^ ε_tloss) ^ (3 / 2 : ℝ) := h7
          _ = δ ^ (3 * ε_tloss / 2) := h4
      have h_absorb : c_ratio / 162 ≥ δ ^ (3 * ε_tloss) := by
        have h_eq : c_ratio / 162 = 1 / (486 * ((2 : ℝ)^((N0 : ℝ)/κ) + 3)) := by
          dsimp only [c_ratio]
          field_simp
          <;> ring
        rw [h_eq]
        exact h_cubic_absorb
      have h_real_ineq : δ ^ (-a) * c_ratio * t / 162 ≥ δ ^ (-3 * b + 3 * ε_tloss) := by
        have h41 : δ ^ (-a) * c_ratio * t / 162 ≥
            δ ^ (-a) * (c_ratio / 162) * δ ^ (3 * ε_tloss / 2) := by
          have h_eq : δ ^ (-a) * c_ratio * t / 162 = (δ ^ (-a) * (c_ratio / 162)) * t := by
            have h_div_mul : ∀ (x y : ℝ), x * y / 162 = (x / 162) * y := by
              intro x y
              have h1 : x * y / 162 = x * y * (162 : ℝ)⁻¹ := by
                rw [div_eq_mul_inv]
              rw [h1]
              have h2 : x * y * (162 : ℝ)⁻¹ = (x * (162 : ℝ)⁻¹) * y := by
                rw [mul_assoc x y (162 : ℝ)⁻¹, mul_comm y (162 : ℝ)⁻¹, ←mul_assoc]
              rw [h2]
              have h3 : x * (162 : ℝ)⁻¹ = x / 162 := by
                rw [←div_eq_mul_inv]
              rw [h3]
            have h_first : δ ^ (-a) * c_ratio * t / 162 = ((δ ^ (-a) * c_ratio) / 162) * t :=
              h_div_mul (δ ^ (-a) * c_ratio) t
            rw [h_first]
            have h_second : (δ ^ (-a) * c_ratio) / 162 = δ ^ (-a) * (c_ratio / 162) := by
              rw [mul_div_assoc]
            rw [h_second]
          rw [h_eq]
          have h_pos : 0 ≤ δ ^ (-a) * (c_ratio / 162) := by positivity
          exact mul_le_mul_of_nonneg_left h_tloss' h_pos
        have h5 : δ ^ (-a) * (c_ratio / 162) * δ ^ (3 * ε_tloss / 2) ≥
            δ ^ (-a) * δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2) := by
          set a' := δ ^ (-a)
          set b' := c_ratio / 162
          set c' := δ ^ (3 * ε_tloss / 2)
          set e' := δ ^ (3 * ε_tloss)
          have ha : 0 ≤ a' := by positivity
          have hc : 0 ≤ c' := by positivity
          have h_abs : b' ≥ e' := h_absorb
          have h_inner : b' * c' ≥ e' * c' := mul_le_mul_of_nonneg_right h_abs hc
          have h_outer : a' * (b' * c') ≥ a' * (e' * c') := mul_le_mul_of_nonneg_left h_inner ha
          have h1 : a' * b' * c' = a' * (b' * c') := by
            exact mul_assoc a' b' c'
          have h2 : a' * (e' * c') = a' * e' * c' := by
            exact (mul_assoc a' e' c').symm
          calc
            a' * b' * c'
              = a' * (b' * c') := h1
            _ ≥ a' * (e' * c') := h_outer
            _ = a' * e' * c' := h2
        have h6 : δ ^ (-a) * δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2) =
            δ ^ (-a + 3 * ε_tloss + 3 * ε_tloss / 2) := by
          have h21 : δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2) = δ ^ (3 * ε_tloss + 3 * ε_tloss / 2) :=
            (Real.rpow_add hδ_pos (3 * ε_tloss) (3 * ε_tloss / 2)).symm
          have h22 : δ ^ (-a) * (δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2)) =
              δ ^ (-a) * δ ^ (3 * ε_tloss + 3 * ε_tloss / 2) := by rw [h21]
          have h23 : δ ^ (-a) * δ ^ (3 * ε_tloss + 3 * ε_tloss / 2) =
              δ ^ (-a + (3 * ε_tloss + 3 * ε_tloss / 2)) :=
            (Real.rpow_add hδ_pos (-a) (3 * ε_tloss + 3 * ε_tloss / 2)).symm
          have h_assoc : δ ^ (-a) * δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2) =
              δ ^ (-a) * (δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2)) := by
            simp only [mul_assoc]
          have h_exp : -a + (3 * ε_tloss + 3 * ε_tloss / 2) = -a + 3 * ε_tloss + 3 * ε_tloss / 2 := by
            simp [add_assoc]
          calc
            δ ^ (-a) * δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2)
              = δ ^ (-a) * (δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2)) := h_assoc
            _ = δ ^ (-a) * δ ^ (3 * ε_tloss + 3 * ε_tloss / 2) := h22
            _ = δ ^ (-a + (3 * ε_tloss + 3 * ε_tloss / 2)) := h23
            _ = δ ^ (-a + 3 * ε_tloss + 3 * ε_tloss / 2) := by rw [h_exp]
        have h7 : -a + 3 * ε_tloss + 3 * ε_tloss / 2 = -3 * b + 3 * ε_tloss := by
          have h8 : a - 3 * b = 3 * ε_tloss / 2 := h_a3b
          have h9 : a = 3 * b + 3 * ε_tloss / 2 := by
            have h_gen : ∀ (x y z : ℝ), x - y = z → x = y + z := by
              intro x y z h
              have h1 : x - y + y = x := sub_add_cancel x y
              have h2 : x = (x - y) + y := h1.symm
              rw [h2, h]
              <;> exact add_comm z y
            exact h_gen a (3 * b) (3 * ε_tloss / 2) h8
          have h13 : -(3 * b + 3 * ε_tloss / 2) + 3 * ε_tloss + 3 * ε_tloss / 2 = -3 * b + 3 * ε_tloss := by
            ring
          calc
            -a + 3 * ε_tloss + 3 * ε_tloss / 2
              = -(3 * b + 3 * ε_tloss / 2) + 3 * ε_tloss + 3 * ε_tloss / 2 := by rw [h9]
            _ = -3 * b + 3 * ε_tloss := h13
        calc
          δ ^ (-a) * c_ratio * t / 162
            ≥ δ ^ (-a) * (c_ratio / 162) * δ ^ (3 * ε_tloss / 2) := h41
          _ ≥ δ ^ (-a) * δ ^ (3 * ε_tloss) * δ ^ (3 * ε_tloss / 2) := h5
          _ = δ ^ (-a + 3 * ε_tloss + 3 * ε_tloss / 2) := h6
          _ = δ ^ (-3 * b + 3 * ε_tloss) := by rw [h7]
      have h_pos2 : 0 ≤ δ ^ (-3 * b + 3 * ε_tloss) := by positivity
      have h10 : C_enn ≥ ENNReal.ofReal (δ ^ (-3 * b + 3 * ε_tloss)) :=
        ENNReal.ofReal_le_ofReal h_real_ineq
      have h11 : (ENNReal.ofReal (δ ^ (-b + ε_tloss)) * N_X) ^ 3 =
          ENNReal.ofReal (δ ^ (-3 * b + 3 * ε_tloss)) * N_X ^ 3 := by
        have h12 : (δ ^ (-b + ε_tloss)) ^ 3 = δ ^ (-3 * b + 3 * ε_tloss) := by
          have h_pos : 0 < δ := hδ_pos
          have h_exp : (δ ^ (-b + ε_tloss)) ^ 3 =
              δ ^ (-b + ε_tloss) * δ ^ (-b + ε_tloss) * δ ^ (-b + ε_tloss) := by
            have h : ∀ (x : ℝ), x ^ 3 = x * x * x := by
              intro x; simp [pow_succ] <;> ring
            exact h (δ ^ (-b + ε_tloss))
          rw [h_exp]
          have h_add1 : δ ^ (-b + ε_tloss) * δ ^ (-b + ε_tloss) =
              δ ^ ((-b + ε_tloss) + (-b + ε_tloss)) := by
            rw [← Real.rpow_add h_pos]
          have h_add2 : δ ^ ((-b + ε_tloss) + (-b + ε_tloss)) * δ ^ (-b + ε_tloss) =
              δ ^ (((-b + ε_tloss) + (-b + ε_tloss)) + (-b + ε_tloss)) := by
            rw [← Real.rpow_add h_pos]
          have h_exp_sum : ((-b + ε_tloss) + (-b + ε_tloss)) + (-b + ε_tloss) = -3 * b + 3 * ε_tloss := by
            have h_gen : ∀ (x y : ℝ), ((-x + y) + (-x + y)) + (-x + y) = -3 * x + 3 * y := by
              intro x y
              ring
            exact h_gen b ε_tloss
          calc
            δ ^ (-b + ε_tloss) * δ ^ (-b + ε_tloss) * δ ^ (-b + ε_tloss)
              = (δ ^ (-b + ε_tloss) * δ ^ (-b + ε_tloss)) * δ ^ (-b + ε_tloss) := by rw [mul_assoc]
            _ = δ ^ ((-b + ε_tloss) + (-b + ε_tloss)) * δ ^ (-b + ε_tloss) := by rw [h_add1]
            _ = δ ^ (((-b + ε_tloss) + (-b + ε_tloss)) + (-b + ε_tloss)) := h_add2
            _ = δ ^ (-3 * b + 3 * ε_tloss) := by rw [h_exp_sum]
        have h13 : 0 ≤ δ ^ (-b + ε_tloss) := by positivity
        have h14 : (ENNReal.ofReal (δ ^ (-b + ε_tloss)) * N_X) ^ 3 =
            (ENNReal.ofReal (δ ^ (-b + ε_tloss))) ^ 3 * N_X ^ 3 := by
          rw [mul_pow]
        rw [h14]
        have h15 : (ENNReal.ofReal (δ ^ (-b + ε_tloss))) ^ 3 =
            ENNReal.ofReal ((δ ^ (-b + ε_tloss)) ^ 3) := by
          rw [← ENNReal.ofReal_pow h13] <;> rfl
        rw [h15, h12]
      have h13 : (ENNReal.ofReal (δ ^ (-b + ε_tloss)) * N_X) ^ 3 ≤ N_diff ^ 3 := by
        rw [h11]
        calc
          ENNReal.ofReal (δ ^ (-3 * b + 3 * ε_tloss)) * N_X ^ 3
            ≤ C_enn * N_X ^ 3 := by gcongr
          _ ≤ N_diff ^ 3 := h9
      have h14 : ENNReal.ofReal (δ ^ (-b + ε_tloss)) * N_X ≤ N_diff := by
        have h15 : ∀ (x y : ENNReal), x ^ 3 ≤ y ^ 3 → x ≤ y := by
          intro x y h
          by_contra h16
          have h17 : y < x := lt_of_not_ge h16
          have h18 : y ^ 3 < x ^ 3 := by gcongr
          exact not_le.mpr h18 h
        exact h15 _ _ h13
      have h15 : -b + ε_tloss = -(1 - s) / (24 * (m : ℝ) * (N0 : ℝ)) + ε_tloss := by
        simp [hb_def] <;> ring
      rw [h15] at h14
      exact ⟨z, hz, h14⟩

  · -- All terms small: contradiction via PR
    push Not at h_main
    have h_all : ∀ (i : Fin (2 * m * N0)), Nreal δ (Set.image2 (· + ·) X (negY i)) ≤
        ENNReal.ofReal α * Nreal δ X := h_main
    have h_all' : ∀ (i : Fin (2 * m * N0)), ProductLikeIncidence.Nreal' δ (Set.image2 (· + ·) X (negY i)) ≤
        ENNReal.ofReal α * ProductLikeIncidence.Nreal' δ X := by
      intro i; simpa [Nreal_eq_Nreal'] using h_all i
    have hPR := ProductLikeIncidence.discretized_multiset_pr_general
      hδ_pos hk_pos hX_bdd h_negY_bdd hX_nonempty (fun _ => by positivity) h_all'
    have h_sum_alpha : (∑ i : Fin (2 * m * N0), α) = (k : ℝ) * α := by
      rw [Finset.sum_const, Finset.card_fin]
      <;> simp [hk_def] <;> ring
    rw [h_sum_alpha] at hPR
    have hPR' : Nreal δ (ProductLikeIncidence.familySum negY) ≤
        ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ) * α) ^ k) * Nreal δ X := by
      have h_eq : (2 * ((k : ℝ) * α)) = (2 * (k : ℝ) * α) := by ring
      rw [h_eq] at hPR
      simpa [Nreal_eq_Nreal'] using hPR
    have h_bound : Nreal δ (ProductLikeIncidence.familySum negY) ≤
        ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ) * α) ^ k * (3 * δ ^ (-(1 + 3 * s) / 4))) := by
      calc
        Nreal δ (ProductLikeIncidence.familySum negY)
          ≤ ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ) * α) ^ k) * Nreal δ X := hPR'
        _ ≤ ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ) * α) ^ k) *
              ENNReal.ofReal (3 * δ ^ (-(1 + 3 * s) / 4)) := by gcongr <;> exact hX_bound
        _ = ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ) * α) ^ k * (3 * δ ^ (-(1 + 3 * s) / 4))) := by
            have h_pos1 : 0 ≤ (k : ℝ) * (2 * (k : ℝ) * α) ^ k := by positivity
            rw [← ENNReal.ofReal_mul h_pos1]
    have hα_k : α ^ k = δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) := by
      have h1 : α = δ ^ (-a) := by rfl
      rw [h1]
      have h21 : (δ ^ (-a)) ^ k = (δ ^ (-a)) ^ (k : ℝ) := by exact Eq.symm (Real.rpow_natCast (δ ^ (-a)) k)
      rw [h21]
      have h22 : (δ ^ (-a)) ^ (k : ℝ) = δ ^ ((-a) * (k : ℝ)) := by
        rw [Real.rpow_mul hδ_nonneg]
      rw [h22]
      have h23 : (-a) * (k : ℝ) = -(3 * (1 - s) / 4 - ε * (m : ℝ) - γ) := by
        have h24 : a * (k : ℝ) = 3 * (1 - s) / 4 - ε * (m : ℝ) - γ := h_ak
        linarith
      rw [h23]
    have h_expand : (k : ℝ) * (2 * (k : ℝ) * α) ^ k =
        (k : ℝ) * (2 * (k : ℝ)) ^ k * α ^ k := by
      have h : (2 * (k : ℝ) * α) ^ k = (2 * (k : ℝ)) ^ k * α ^ k := by
        rw [mul_pow]
      rw [h] <;> ring
    rw [h_expand] at h_bound
    rw [hα_k] at h_bound
    have h_exp_sum : -(3 * (1 - s) / 4 - ε * (m : ℝ) - γ) + (-(1 + 3 * s) / 4) =
        -1 + ε * (m : ℝ) + γ := by ring
    have h_combine : δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * δ ^ (-(1 + 3 * s) / 4) =
        δ ^ (-1 + ε * (m : ℝ) + γ) := by
      have h1 : δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ) + (-(1 + 3 * s) / 4)) =
          δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * δ ^ (-(1 + 3 * s) / 4) :=
        Real.rpow_add hδ_pos _ _
      have h2 : -(3 * (1 - s) / 4 - ε * (m : ℝ) - γ) + (-(1 + 3 * s) / 4) = -1 + ε * (m : ℝ) + γ := h_exp_sum
      rw [h2] at h1
      exact h1.symm
    have h4 : (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) *
        (3 * δ ^ (-(1 + 3 * s) / 4)) =
        3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-1 + ε * (m : ℝ) + γ) := by
      have h5 : δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * (3 * δ ^ (-(1 + 3 * s) / 4)) =
          3 * δ ^ (-1 + ε * (m : ℝ) + γ) := by
        calc
          δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * (3 * δ ^ (-(1 + 3 * s) / 4))
            = 3 * (δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * δ ^ (-(1 + 3 * s) / 4)) := by ring
          _ = 3 * δ ^ (-1 + ε * (m : ℝ) + γ) := by rw [h_combine]
      calc
        (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * (3 * δ ^ (-(1 + 3 * s) / 4))
          = (k : ℝ) * (2 * (k : ℝ)) ^ k * (δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * (3 * δ ^ (-(1 + 3 * s) / 4))) := by ring
        _ = (k : ℝ) * (2 * (k : ℝ)) ^ k * (3 * δ ^ (-1 + ε * (m : ℝ) + γ)) := by rw [h5]
        _ = 3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-1 + ε * (m : ℝ) + γ) := by ring
    have h_bound2 : Nreal δ (ProductLikeIncidence.familySum negY) ≤
        ENNReal.ofReal (3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-1 + ε * (m : ℝ) + γ)) := by
      have h_eq : ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-(3 * (1 - s) / 4 - ε * (m : ℝ) - γ)) * (3 * δ ^ (-(1 + 3 * s) / 4))) =
          ENNReal.ofReal (3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-1 + ε * (m : ℝ) + γ)) := by
        rw [h4]
      rw [h_eq] at h_bound
      exact h_bound
    have h_contra_enn : ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ (-1 + ε * (m : ℝ))) ≤
        ENNReal.ofReal (3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-1 + ε * (m : ℝ) + γ)) :=
      le_trans h_familyNegY_large h_bound2
    have h_pos1 : 0 ≤ (1 / 2 : ℝ) * δ ^ (-1 + ε * (m : ℝ)) := by positivity
    have h_k_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
    have h_2k_pos : 0 < (2 * (k : ℝ)) := by linarith
    have h_2k_pow_pos : 0 < (2 * (k : ℝ)) ^ k := by positivity
    have h_delta_pos : 0 < δ ^ (-1 + ε * (m : ℝ) + γ) := Real.rpow_pos_of_pos hδ_pos _
    have h_pos2 : 0 ≤ 3 * (k : ℝ) * ((2 * (k : ℝ)) ^ k) * δ ^ (-1 + ε * (m : ℝ) + γ) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)) (by positivity)
    have h_contra_real : (1 / 2 : ℝ) * δ ^ (-1 + ε * (m : ℝ)) ≤
        3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-1 + ε * (m : ℝ) + γ) :=
      (ENNReal.ofReal_le_ofReal_iff h_pos2).mp h_contra_enn
    have h_div_pos : 0 < δ ^ (-1 + ε * (m : ℝ)) := Real.rpow_pos_of_pos hδ_pos _
    set x : ℝ := δ ^ (-1 + ε * (m : ℝ)) with hx_def
    have hx_pos : 0 < x := h_div_pos
    have h53 : δ ^ (-1 + ε * (m : ℝ) + γ) = x * δ ^ γ := by
      simp only [hx_def]
      have h6 : δ ^ (-1 + ε * (m : ℝ) + γ) = δ ^ (-1 + ε * (m : ℝ)) * δ ^ γ := by
        rw [← Real.rpow_add hδ_pos] <;> ring
      exact h6
    have h54 : (1 / 2 : ℝ) ≤ 3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ := by
      have h51 : (1 / 2 : ℝ) * x ≤ 3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ (-1 + ε * (m : ℝ) + γ) :=
        h_contra_real
      rw [h53] at h51
      have h55 : (1 / 2 : ℝ) * x ≤ (3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ) * x := by
        have h_rearr : 3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * (x * δ ^ γ) =
            (3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ) * x := by ring
        rw [h_rearr] at h51
        exact h51
      calc (1 / 2 : ℝ)
        = ((1 / 2 : ℝ) * x) / x := by field_simp [hx_pos.ne'] <;> ring
      _ ≤ ((3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ) * x) / x := by gcongr
      _ = (3 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ) := by field_simp [hx_pos.ne'] <;> ring
    have h_final : (1 : ℝ) ≤ 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ := by
      linarith [h54]
    have h_contra' : 6 * (k : ℝ) * (2 * (k : ℝ)) ^ k * δ ^ γ < 1 := h_PR_const
    linarith

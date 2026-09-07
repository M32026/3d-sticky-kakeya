import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators NNReal

namespace Kakeya.CV

/-- Triple Hölder inequality for finite sums of nonnegative reals. -/
lemma triple_holder {ι : Type*} (s : Finset ι) (f g h : ι → NNReal) :
    ∑ i ∈ s, f i * g i * h i ≤
      (∑ i ∈ s, f i ^ 3) ^ (1 / 3 : ℝ) *
      (∑ i ∈ s, g i ^ 3) ^ (1 / 3 : ℝ) *
      (∑ i ∈ s, h i ^ 3) ^ (1 / 3 : ℝ) := by
  have h12 : (3 / 2 : ℝ).HolderConjugate (3 : ℝ) := by
    refine' { inv_add_inv_eq_inv := _, left_pos := _, right_pos := _ } <;> norm_num
  have h22 : (2 : ℝ).HolderConjugate (2 : ℝ) := Real.HolderConjugate.two_two
  have h_main1 : ∑ i ∈ s, (f i * g i) * h i ≤
      (∑ i ∈ s, (f i * g i) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
      (∑ i ∈ s, h i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
    have h := NNReal.inner_le_Lp_mul_Lq s (fun i => f i * g i) h h12
    simpa [one_div] using h
  have h_main2 : ∑ i ∈ s, f i ^ (3 / 2 : ℝ) * g i ^ (3 / 2 : ℝ) ≤
      (∑ i ∈ s, (f i ^ (3 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      (∑ i ∈ s, (g i ^ (3 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    NNReal.inner_le_Lp_mul_Lq s
      (fun i => f i ^ (3 / 2 : ℝ)) (fun i => g i ^ (3 / 2 : ℝ)) h22
  have h_mul_rpow : ∀ i ∈ s, (f i * g i) ^ (3 / 2 : ℝ) =
      f i ^ (3 / 2 : ℝ) * g i ^ (3 / 2 : ℝ) := by
    intro i _; exact NNReal.mul_rpow
  have h_rpow3 : ∀ (x : NNReal), (x ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = x ^ (3 : ℝ) := by
    intro x
    have h : (x ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = x ^ ((3 / 2 : ℝ) * (2 : ℝ)) :=
      Eq.symm (NNReal.rpow_mul x (3 / 2 : ℝ) (2 : ℝ))
    rw [h]
    have h2 : (3 / 2 : ℝ) * (2 : ℝ) = (3 : ℝ) := by norm_num
    rw [h2]
  have h_nat_to_real : ∀ (x : NNReal), x ^ (3 : ℝ) = x ^ 3 := by
    intro x
    have h1 : x ^ (3 : ℝ) = x ^ (3 : ℤ) := NNReal.rpow_intCast x (3 : ℤ)
    rw [h1] <;> rfl
  have h_sum1 : ∑ i ∈ s, (f i * g i) ^ (3 / 2 : ℝ) =
      ∑ i ∈ s, f i ^ (3 / 2 : ℝ) * g i ^ (3 / 2 : ℝ) := by
    apply Finset.sum_congr rfl; intro i hi; exact h_mul_rpow i hi
  have h_sum_f : ∑ i ∈ s, (f i ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = ∑ i ∈ s, f i ^ (3 : ℝ) := by
    apply Finset.sum_congr rfl; intro i _; exact h_rpow3 (f i)
  have h_sum_g : ∑ i ∈ s, (g i ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = ∑ i ∈ s, g i ^ (3 : ℝ) := by
    apply Finset.sum_congr rfl; intro i _; exact h_rpow3 (g i)
  have h_algebra : ∀ (A B : NNReal),
      (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) =
      A ^ (1 / 3 : ℝ) * B ^ (1 / 3 : ℝ) := by
    intro A B
    rw [NNReal.mul_rpow]
    have hA : (A ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) = A ^ (1 / 3 : ℝ) := by
      rw [← NNReal.rpow_mul A (1 / 2 : ℝ) (2 / 3 : ℝ)]
      have h2 : (1 / 2 : ℝ) * (2 / 3 : ℝ) = (1 / 3 : ℝ) := by norm_num
      rw [h2]
    have hB : (B ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) = B ^ (1 / 3 : ℝ) := by
      rw [← NNReal.rpow_mul B (1 / 2 : ℝ) (2 / 3 : ℝ)]
      have h2 : (1 / 2 : ℝ) * (2 / 3 : ℝ) = (1 / 3 : ℝ) := by norm_num
      rw [h2]
    rw [hA, hB]
  have h_main2' : ∑ i ∈ s, f i ^ (3 / 2 : ℝ) * g i ^ (3 / 2 : ℝ) ≤
      (∑ i ∈ s, f i ^ (3 : ℝ)) ^ (1 / 2 : ℝ) * (∑ i ∈ s, g i ^ (3 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [h_sum_f, h_sum_g] at h_main2
    exact h_main2
  calc
    ∑ i ∈ s, f i * g i * h i
      = ∑ i ∈ s, (f i * g i) * h i := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ (∑ i ∈ s, (f i * g i) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
           (∑ i ∈ s, h i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := h_main1
    _ = (∑ i ∈ s, f i ^ (3 / 2 : ℝ) * g i ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
           (∑ i ∈ s, h i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by rw [h_sum1]
    _ ≤ ((∑ i ∈ s, f i ^ (3 : ℝ)) ^ (1 / 2 : ℝ) *
             (∑ i ∈ s, g i ^ (3 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
           (∑ i ∈ s, h i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by gcongr
    _ = (∑ i ∈ s, f i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) *
           (∑ i ∈ s, g i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) *
           (∑ i ∈ s, h i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        rw [h_algebra (∑ i ∈ s, f i ^ (3 : ℝ)) (∑ i ∈ s, g i ^ (3 : ℝ))]
    _ = (∑ i ∈ s, f i ^ 3) ^ (1 / 3 : ℝ) *
           (∑ i ∈ s, g i ^ 3) ^ (1 / 3 : ℝ) *
           (∑ i ∈ s, h i ^ 3) ^ (1 / 3 : ℝ) := by
        have hf : ∑ i ∈ s, f i ^ (3 : ℝ) = ∑ i ∈ s, f i ^ 3 := by
          apply Finset.sum_congr rfl; intro i _; exact h_nat_to_real (f i)
        have hg : ∑ i ∈ s, g i ^ (3 : ℝ) = ∑ i ∈ s, g i ^ 3 := by
          apply Finset.sum_congr rfl; intro i _; exact h_nat_to_real (g i)
        have hh : ∑ i ∈ s, h i ^ (3 : ℝ) = ∑ i ∈ s, h i ^ 3 := by
          apply Finset.sum_congr rfl; intro i _; exact h_nat_to_real (h i)
        rw [hf, hg, hh]

theorem multilinear_kakeya_preliminary_reduction :
    PreliminaryReductionStatement := by
  intro Cube T₁ T₂ T₃ _ _ _ _ weight h
  let W : Cube → NNReal := fun q => ∑ t₁, ∑ t₂, ∑ t₃, weight q t₁ t₂ t₃
  let A : NNReal := ∑ q, NNReal.sqrt (W q)
  by_cases hA : A = 0
  · -- Case A = 0
    have hLHS : (∑ q, NNReal.sqrt (W q)) = 0 := hA
    rw [hLHS]
    <;> simp
  · -- Case A > 0
    have hA_ne : A ≠ 0 := hA
    have hA_pos : 0 < A := pos_iff_ne_zero.mpr hA_ne
    let M : Cube → NNReal := fun q => (NNReal.sqrt (W q) / A) ^ (1 / 3 : ℝ)
    have hM3 : ∀ q, M q ^ 3 = NNReal.sqrt (W q) / A := by
      intro q
      simp only [M]
      have h_cast : (1 / 3 : ℝ) * (↑3 : ℕ) = 1 := by norm_num
      have h : ((NNReal.sqrt (W q) / A) ^ (1 / 3 : ℝ)) ^ 3 =
          (NNReal.sqrt (W q) / A) ^ ((1 / 3 : ℝ) * (↑3 : ℕ)) := by
        exact Eq.symm (NNReal.rpow_mul_natCast (NNReal.sqrt (W q) / A) (1 / 3 : ℝ) 3)
      rw [h, h_cast, NNReal.rpow_one]
    have hsumM : ∑ q, M q ^ 3 = 1 := by
      have h : ∑ q, M q ^ 3 = ∑ q, (NNReal.sqrt (W q) / A) := by
        apply Finset.sum_congr rfl; intro q _; exact hM3 q
      rw [h]
      have h2 : ∑ q, (NNReal.sqrt (W q) / A) = (∑ q, NNReal.sqrt (W q)) / A := by
        rw [Finset.sum_div]
      rw [h2]
      have h3 : (∑ q, NNReal.sqrt (W q)) = A := rfl
      rw [h3]
      exact div_self hA_ne
    rcases h M hsumM with ⟨S₁, S₂, S₃, hpoint, hcol₁, hcol₂, hcol₃⟩
    let a : Cube → NNReal := fun q => ∑ t₁, S₁ q t₁
    let b : Cube → NNReal := fun q => ∑ t₂, S₂ q t₂
    let c : Cube → NNReal := fun q => ∑ t₃, S₃ q t₃
    -- Helper: triple sum factorization
    have h_factor3 : ∀ (f : T₁ → NNReal) (g : T₂ → NNReal) (k : T₃ → NNReal),
        ∑ t₁, ∑ t₂, ∑ t₃, f t₁ * g t₂ * k t₃ = (∑ t₁, f t₁) * (∑ t₂, g t₂) * (∑ t₃, k t₃) := by
      intro f g k
      have h1 : ∑ t₁, ∑ t₂, ∑ t₃, f t₁ * g t₂ * k t₃ =
          ∑ t₁, ∑ t₂, (f t₁ * g t₂) * (∑ t₃, k t₃) := by
        apply Finset.sum_congr rfl
        intro t₁ _
        apply Finset.sum_congr rfl
        intro t₂ _
        have h_inner : ∑ t₃, f t₁ * g t₂ * k t₃ = (f t₁ * g t₂) * ∑ t₃, k t₃ := by
          have h : ∑ t₃, f t₁ * g t₂ * k t₃ = ∑ t₃, (f t₁ * g t₂) * k t₃ := by
            apply Finset.sum_congr rfl; intro t₃ _; ring
          rw [h, Finset.mul_sum]
        exact h_inner
      rw [h1]
      have h2 : ∑ t₁, ∑ t₂, (f t₁ * g t₂) * (∑ t₃, k t₃) =
          (∑ t₁, ∑ t₂, f t₁ * g t₂) * (∑ t₃, k t₃) := by
        have h21 : ∑ t₁, ∑ t₂, (f t₁ * g t₂) * (∑ t₃, k t₃) =
            ∑ t₁, ((∑ t₂, f t₁ * g t₂) * (∑ t₃, k t₃)) := by
          apply Finset.sum_congr rfl; intro t₁ _
          rw [← Finset.sum_mul]
        rw [h21, ← Finset.sum_mul]
      rw [h2]
      have h3 : ∑ t₁, ∑ t₂, f t₁ * g t₂ = (∑ t₁, f t₁) * (∑ t₂, g t₂) := by
        rw [← Fintype.sum_mul_sum f g]
      rw [h3] <;> ring
    -- Step 4: sum pointwise inequality
    have hsum_ineq : ∀ q, W q * M q ^ 3 ≤ a q * b q * c q := by
      intro q
      have h1 : ∑ t₁, ∑ t₂, ∑ t₃, (weight q t₁ t₂ t₃ * M q ^ 3) ≤
               ∑ t₁, ∑ t₂, ∑ t₃, (S₁ q t₁ * S₂ q t₂ * S₃ q t₃) := by
        apply Finset.sum_le_sum; intro t₁ _
        apply Finset.sum_le_sum; intro t₂ _
        apply Finset.sum_le_sum; intro t₃ _
        exact hpoint q t₁ t₂ t₃
      have h2 : ∑ t₁, ∑ t₂, ∑ t₃, (weight q t₁ t₂ t₃ * M q ^ 3) = W q * M q ^ 3 := by
        have h22 : ∀ (t₁ : T₁) (t₂ : T₂),
            ∑ t₃, (weight q t₁ t₂ t₃ * M q ^ 3) = (∑ t₃, weight q t₁ t₂ t₃) * M q ^ 3 := by
          intro t₁ t₂
          have h : ∑ t₃, weight q t₁ t₂ t₃ * M q ^ 3 = (∑ t₃, weight q t₁ t₂ t₃) * M q ^ 3 := by
            rw [Finset.sum_mul]
          exact h
        have h23 : ∑ t₁, ∑ t₂, ∑ t₃, (weight q t₁ t₂ t₃ * M q ^ 3) =
            ∑ t₁, ∑ t₂, ((∑ t₃, weight q t₁ t₂ t₃) * M q ^ 3) := by
          apply Finset.sum_congr rfl; intro t₁ _
          apply Finset.sum_congr rfl; intro t₂ _; exact h22 t₁ t₂
        rw [h23]
        have h24 : ∑ t₁, ∑ t₂, ((∑ t₃, weight q t₁ t₂ t₃) * M q ^ 3) =
            ∑ t₁, ((∑ t₂, ∑ t₃, weight q t₁ t₂ t₃) * M q ^ 3) := by
          apply Finset.sum_congr rfl; intro t₁ _; rw [Finset.sum_mul]
        rw [h24, Finset.sum_mul] <;> rfl
      have h3 : ∑ t₁, ∑ t₂, ∑ t₃, (S₁ q t₁ * S₂ q t₂ * S₃ q t₃) = a q * b q * c q := by
        rw [h_factor3 (S₁ q) (S₂ q) (S₃ q)]
        <;> simp [a, b, c] <;> ring
      rw [h2, h3] at h1; exact h1
    -- Step 5: substitute and get (sqrt(W q))^3 ≤ A * a q * b q * c q
    have hmain : ∀ q, (NNReal.sqrt (W q)) ^ 3 ≤ A * a q * b q * c q := by
      intro q
      have h4 : W q * M q ^ 3 ≤ a q * b q * c q := hsum_ineq q
      rw [hM3 q] at h4
      have h5 : W q * (NNReal.sqrt (W q) / A) ≤ a q * b q * c q := h4
      have h6 : (W q * (NNReal.sqrt (W q) / A)) * A ≤ (a q * b q * c q) * A := by gcongr
      have h7 : (W q * (NNReal.sqrt (W q) / A)) * A = W q * NNReal.sqrt (W q) := by
        have h71 : (W q * (NNReal.sqrt (W q) / A)) * A = W q * ((NNReal.sqrt (W q) / A) * A) := by ring
        rw [h71]
        have h72 : (NNReal.sqrt (W q) / A) * A = NNReal.sqrt (W q) := div_mul_cancel₀ (NNReal.sqrt (W q)) hA_ne
        rw [h72] <;> ring
      rw [h7] at h6
      have h8 : W q * NNReal.sqrt (W q) = (NNReal.sqrt (W q)) ^ 3 := by
        have h9 : (NNReal.sqrt (W q)) ^ 2 = W q := NNReal.sq_sqrt (W q)
        calc
          W q * NNReal.sqrt (W q)
            = (NNReal.sqrt (W q)) ^ 2 * NNReal.sqrt (W q) := by rw [h9]
          _ = (NNReal.sqrt (W q)) ^ 3 := by ring
      rw [h8] at h6
      have h10 : (a q * b q * c q) * A = A * a q * b q * c q := by ring
      rw [h10] at h6; exact h6
    -- Step 6: take cube roots
    have hroot : ∀ q, NNReal.sqrt (W q) ≤
        A ^ (1 / 3 : ℝ) * (a q) ^ (1 / 3 : ℝ) * (b q) ^ (1 / 3 : ℝ) * (c q) ^ (1 / 3 : ℝ) := by
      intro q
      have h9 : (NNReal.sqrt (W q)) ^ 3 ≤ A * a q * b q * c q := hmain q
      have h9_real : (NNReal.sqrt (W q)) ^ (3 : ℝ) ≤ A * a q * b q * c q := by
        have h_eq : (NNReal.sqrt (W q)) ^ (3 : ℝ) = (NNReal.sqrt (W q)) ^ 3 := by
          have h1 : (NNReal.sqrt (W q)) ^ (3 : ℝ) = (NNReal.sqrt (W q)) ^ (3 : ℤ) :=
            NNReal.rpow_intCast (NNReal.sqrt (W q)) (3 : ℤ)
          rw [h1] <;> rfl
        rw [h_eq]
        exact h9
      have h10 : NNReal.sqrt (W q) ≤ (A * a q * b q * c q) ^ (1 / 3 : ℝ) := by
        have h10' : NNReal.sqrt (W q) ≤ (A * a q * b q * c q) ^ (3 : ℝ)⁻¹ :=
          (NNReal.le_rpow_inv_iff (hz := by norm_num)).mpr h9_real
        have h_inv : (3 : ℝ)⁻¹ = (1 / 3 : ℝ) := by norm_num
        rw [h_inv] at h10'
        exact h10'
      have h11 : (A * a q * b q * c q) ^ (1 / 3 : ℝ) =
          A ^ (1 / 3 : ℝ) * (a q) ^ (1 / 3 : ℝ) * (b q) ^ (1 / 3 : ℝ) * (c q) ^ (1 / 3 : ℝ) := by
        rw [NNReal.mul_rpow, NNReal.mul_rpow, NNReal.mul_rpow] <;> ring
      calc
        NNReal.sqrt (W q) ≤ (A * a q * b q * c q) ^ (1 / 3 : ℝ) := h10
        _ = A ^ (1 / 3 : ℝ) * (a q) ^ (1 / 3 : ℝ) * (b q) ^ (1 / 3 : ℝ) * (c q) ^ (1 / 3 : ℝ) := h11
    -- Step 7: sum over q
    let S : NNReal := ∑ q, ((a q) ^ (1 / 3 : ℝ) * (b q) ^ (1 / 3 : ℝ) * (c q) ^ (1 / 3 : ℝ))
    have hsum2 : A ≤ A ^ (1 / 3 : ℝ) * S := by
      have h12 : ∑ q, NNReal.sqrt (W q) ≤ ∑ q, (A ^ (1 / 3 : ℝ) * ((a q) ^ (1 / 3 : ℝ) * (b q) ^ (1 / 3 : ℝ) * (c q) ^ (1 / 3 : ℝ))) := by
        apply Finset.sum_le_sum; intro q _
        have h := hroot q
        convert h using 1
        <;> ring
      have h14 : ∑ q, (A ^ (1 / 3 : ℝ) * ((a q) ^ (1 / 3 : ℝ) * (b q) ^ (1 / 3 : ℝ) * (c q) ^ (1 / 3 : ℝ))) =
          A ^ (1 / 3 : ℝ) * S := by
        rw [Finset.mul_sum] <;> rfl
      rw [h14] at h12; exact h12
    -- Step 8: triple Hölder
    let f : Cube → NNReal := fun q => (a q) ^ (1 / 3 : ℝ)
    let g : Cube → NNReal := fun q => (b q) ^ (1 / 3 : ℝ)
    let hfunc : Cube → NNReal := fun q => (c q) ^ (1 / 3 : ℝ)
    have h_rpow3 : ∀ (x : NNReal), (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
      intro x
      rw [← NNReal.rpow_mul_natCast x (1 / 3 : ℝ) 3]
      have h_cast : (1 / 3 : ℝ) * (↑3 : ℕ) = 1 := by norm_num
      rw [h_cast, NNReal.rpow_one]
    have h_sum_a : ∑ q, (f q) ^ 3 = ∑ q, a q := by
      apply Finset.sum_congr rfl; intro q _; exact h_rpow3 (a q)
    have h_sum_b : ∑ q, (g q) ^ 3 = ∑ q, b q := by
      apply Finset.sum_congr rfl; intro q _; exact h_rpow3 (b q)
    have h_sum_c : ∑ q, (hfunc q) ^ 3 = ∑ q, c q := by
      apply Finset.sum_congr rfl; intro q _; exact h_rpow3 (c q)
    have hholder : S ≤ (∑ q, a q) ^ (1 / 3 : ℝ) * (∑ q, b q) ^ (1 / 3 : ℝ) * (∑ q, c q) ^ (1 / 3 : ℝ) := by
      have h := triple_holder (Finset.univ) f g hfunc
      rw [h_sum_a, h_sum_b, h_sum_c] at h
      exact h
    -- Step 9: column sum bounds
    have hcol_sum1 : ∑ q, a q ≤ (Fintype.card T₁ : NNReal) := by
      calc
        ∑ q, a q = ∑ (t₁ : T₁), ∑ (q : Cube), S₁ q t₁ := by
          dsimp only [a]
          rw [Finset.sum_comm]
        _ ≤ ∑ (t₁ : T₁), (1 : NNReal) := by
          apply Finset.sum_le_sum; intro t₁ _; exact hcol₁ t₁
        _ = (Fintype.card T₁ : NNReal) := by simp
    have hcol_sum2 : ∑ q, b q ≤ (Fintype.card T₂ : NNReal) := by
      calc
        ∑ q, b q = ∑ (t₂ : T₂), ∑ (q : Cube), S₂ q t₂ := by
          dsimp only [b]
          rw [Finset.sum_comm]
        _ ≤ ∑ (t₂ : T₂), (1 : NNReal) := by
          apply Finset.sum_le_sum; intro t₂ _; exact hcol₂ t₂
        _ = (Fintype.card T₂ : NNReal) := by simp
    have hcol_sum3 : ∑ q, c q ≤ (Fintype.card T₃ : NNReal) := by
      calc
        ∑ q, c q = ∑ (t₃ : T₃), ∑ (q : Cube), S₃ q t₃ := by
          dsimp only [c]
          rw [Finset.sum_comm]
        _ ≤ ∑ (t₃ : T₃), (1 : NNReal) := by
          apply Finset.sum_le_sum; intro t₃ _; exact hcol₃ t₃
        _ = (Fintype.card T₃ : NNReal) := by simp
    -- Step 10-11: combine and cube
    have h_cube_prod : ∀ (x y z w : NNReal),
        (x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) * w ^ (1 / 3 : ℝ)) ^ 3 = x * y * z * w := by
      intro x y z w
      have h1 : ∀ (u : NNReal), (u ^ (1 / 3 : ℝ)) ^ 3 = u := h_rpow3
      have h2 : (x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) * w ^ (1 / 3 : ℝ)) ^ 3 =
          ((x ^ (1 / 3 : ℝ)) ^ 3) * ((y ^ (1 / 3 : ℝ)) ^ 3) * ((z ^ (1 / 3 : ℝ)) ^ 3) * ((w ^ (1 / 3 : ℝ)) ^ 3) := by
        rw [mul_pow, mul_pow, mul_pow] <;> ring
      rw [h2]
      rw [h1 x, h1 y, h1 z, h1 w] <;> ring
    have hfinal1 : A ≤ A ^ (1 / 3 : ℝ) * (∑ q, a q) ^ (1 / 3 : ℝ) * (∑ q, b q) ^ (1 / 3 : ℝ) * (∑ q, c q) ^ (1 / 3 : ℝ) := by
      calc
        A ≤ A ^ (1 / 3 : ℝ) * S := hsum2
        _ ≤ A ^ (1 / 3 : ℝ) * ((∑ q, a q) ^ (1 / 3 : ℝ) * (∑ q, b q) ^ (1 / 3 : ℝ) * (∑ q, c q) ^ (1 / 3 : ℝ)) := by gcongr
        _ = A ^ (1 / 3 : ℝ) * (∑ q, a q) ^ (1 / 3 : ℝ) * (∑ q, b q) ^ (1 / 3 : ℝ) * (∑ q, c q) ^ (1 / 3 : ℝ) := by ring
    have hcube : A ^ 3 ≤ A * (∑ q, a q) * (∑ q, b q) * (∑ q, c q) := by
      have h : A ^ 3 ≤ (A ^ (1 / 3 : ℝ) * (∑ q, a q) ^ (1 / 3 : ℝ) * (∑ q, b q) ^ (1 / 3 : ℝ) * (∑ q, c q) ^ (1 / 3 : ℝ)) ^ 3 := by gcongr
      rw [h_cube_prod A (∑ q, a q) (∑ q, b q) (∑ q, c q)] at h
      exact h
    -- Step 12: divide by A
    have hdiv : A ^ 2 ≤ (∑ q, a q) * (∑ q, b q) * (∑ q, c q) := by
      have h : A ^ 3 = A ^ 2 * A := by simp [pow_three] <;> ring
      rw [h] at hcube
      have h_eq : A * (∑ q, a q) * (∑ q, b q) * (∑ q, c q) = ((∑ q, a q) * (∑ q, b q) * (∑ q, c q)) * A := by ring
      rw [h_eq] at hcube
      have h_real : (A ^ 2 : ℝ) * (A : ℝ) ≤ (((∑ q, a q) * (∑ q, b q) * (∑ q, c q)) : ℝ) * (A : ℝ) := by
        exact_mod_cast hcube
      have hA_real : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA_pos
      have h : (A ^ 2 : ℝ) ≤ (((∑ q, a q) * (∑ q, b q) * (∑ q, c q)) : ℝ) := by
        nlinarith
      exact_mod_cast h
    -- Step 13: column sum bounds
    have hprod : (∑ q, a q) * (∑ q, b q) * (∑ q, c q) ≤
        (Fintype.card T₁ : NNReal) * (Fintype.card T₂ : NNReal) * (Fintype.card T₃ : NNReal) := by
      gcongr <;> tauto
    have hfinal2 : A ^ 2 ≤ (Fintype.card T₁ : NNReal) * (Fintype.card T₂ : NNReal) * (Fintype.card T₃ : NNReal) := by
      calc
        A ^ 2 ≤ (∑ q, a q) * (∑ q, b q) * (∑ q, c q) := hdiv
        _ ≤ (Fintype.card T₁ : NNReal) * (Fintype.card T₂ : NNReal) * (Fintype.card T₃ : NNReal) := hprod
    have hcard : (Fintype.card T₁ : NNReal) * (Fintype.card T₂ : NNReal) * (Fintype.card T₃ : NNReal) =
        ((Fintype.card T₁ * Fintype.card T₂ * Fintype.card T₃ : ℕ) : NNReal) := by
      simp [Nat.cast_mul] <;> ring
    rw [hcard] at hfinal2
    -- Step 14: take square root
    have hsqrt : A ≤ NNReal.sqrt (((Fintype.card T₁ * Fintype.card T₂ * Fintype.card T₃ : ℕ) : NNReal)) := by
      have h : A ^ 2 ≤ ((Fintype.card T₁ * Fintype.card T₂ * Fintype.card T₃ : ℕ) : NNReal) := hfinal2
      have h4 : NNReal.sqrt (A ^ 2) ≤ NNReal.sqrt (((Fintype.card T₁ * Fintype.card T₂ * Fintype.card T₃ : ℕ) : NNReal)) :=
        NNReal.sqrt_le_sqrt.mpr h
      have h5 : NNReal.sqrt (A ^ 2) = A := NNReal.sqrt_sq A
      rw [h5] at h4
      exact h4
    exact hsqrt

end Kakeya.CV

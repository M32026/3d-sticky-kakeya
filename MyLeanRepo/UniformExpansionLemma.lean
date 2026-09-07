module

/-
# Uniform Expansion Lemma

Provides `expansion_lemma_uniform`, a version of the Expansion Lemma
where the iteration count N depends only on bounds on the diameter
and scaled-sumset volume, not on the specific set A.

## Proof route

1. Choose N_pigeon and R explicitly based on n, d_max, lam_min.
2. For any A satisfying the bounds, verify the pigeonhole and Blichfeldt
   inequalities with these explicit values.
3. Run the same geometric argument as `expansion_lemma`.
4. Bound the resulting N' using the lattice spacing and box size.
5. Upgrade from N' to N_max using monotonicity of `iteratedDifference`.
-/

public import MyLeanRepo.ExpansionLemma
public import MyLeanRepo.ExpansionTheoremAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Metric Classical
open scoped Pointwise BigOperators

set_option maxHeartbeats 500000

namespace ExpansionLemma

/-! ## Monotonicity lemmas -/

/-- Monotonicity of iteratedSumset in the iteration count when 0 ∈ S. -/
lemma iteratedSumset_mono_N {S : Set ℝ} (h0 : 0 ∈ S) {N M : ℕ} (h : N ≤ M) :
    iteratedSumset S N ⊆ iteratedSumset S M := by
  induction' h with M h ih
  · exact subset_refl _
  · have h1 : iteratedSumset S M ⊆ iteratedSumset S (M + 1) := by
      intro x hx
      exact ⟨0, h0, x, hx, by ring⟩
    exact ih.trans h1

/-- Monotonicity of iteratedDifference for productSet A 2. -/
lemma iteratedDifference_productSet_mono {A : Set ℝ} (hA_nonempty : A.Nonempty)
    {N M : ℕ} (h : N ≤ M) :
    iteratedDifference (productSet A 2) N ⊆ iteratedDifference (productSet A 2) M := by
  have h_eq : productSet2 A = productSet A 2 := productSet2_eq
  have h0 : 0 ∈ (productSet A 2) - (productSet A 2) := by
    have h0' : 0 ∈ productSet2 A - productSet2 A := zero_in_productDiff hA_nonempty
    rw [h_eq] at h0'
    exact h0'
  have h1 : iteratedSumset ((productSet A 2) - (productSet A 2)) N ⊆
      iteratedSumset ((productSet A 2) - (productSet A 2)) M :=
    iteratedSumset_mono_N h0 h
  have h_eq1 : iteratedDifference (productSet A 2) N =
      iteratedSumset ((productSet A 2) - (productSet A 2)) N :=
    Eq.symm (iteratedDifference_eq (A := A) (N := N))
  have h_eq2 : iteratedDifference (productSet A 2) M =
      iteratedSumset ((productSet A 2) - (productSet A 2)) M :=
    Eq.symm (iteratedDifference_eq (A := A) (N := M))
  rw [h_eq1, h_eq2]
  exact h1

/-- Version of `main_containment` taking the lattice coordinates `m` explicitly,
    so the returned `N'` is visibly `2 + 4 * M`. -/
lemma main_containment_explicit {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    {n : ℕ} (a b z' : Fin n → ℝ) (d : ℝ)
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A)
    (k : Fin n) (ℓ_vec : Fin n → ℝ)
    (hz' : ∀ i, z' i = b i + ℓ_vec i) (hd : d = z' k - a k)
    (m : Fin n → ℤ) (hm : ∀ i, ℓ_vec i = 2 * diam A * (m i : ℝ))
    (h_diam_in_diff : diam A ∈ A - A) :
    ∃ (N' : ℕ), N' = 2 + 4 * Finset.sup Finset.univ (fun i : Fin n => (m i).natAbs) ∧
      0 < N' ∧
      (∀ (i : {i : Fin n // i ≠ k}),
        ((a i - z' i) • A) + (d • A) ⊆
          iteratedSumset ((productSet A 2) - (productSet A 2)) N') ∧
      iteratedSumset ((productSet A 2) - (productSet A 2)) N' =
        iteratedDifference (productSet A 2) N' := by
  let c := diam A
  let M : ℕ := Finset.sup Finset.univ (fun i : Fin n => (m i).natAbs)
  let N' : ℕ := 2 + 4 * M
  have hN'_pos : 0 < N' := by dsimp only [N'] <;> omega
  have hM_ge : ∀ i, (m i).natAbs ≤ M := by
    intro i
    exact Finset.le_sup (f := fun j : Fin n => (m j).natAbs) (Finset.mem_univ i)
  let Sdiff2 := productSet2 A - productSet2 A
  have h0_in_Sdiff2 : (0 : ℝ) ∈ Sdiff2 := zero_in_productDiff hA_nonempty
  have h_mono : ∀ (k l : ℕ), k ≤ l → iteratedSumsetFin Sdiff2 k ⊆ iteratedSumsetFin Sdiff2 l :=
    fun k l h => iteratedSumsetFin_mono h h0_in_Sdiff2
  have h_pset_eq : productSet2 A = productSet A 2 := productSet2_eq
  have h_main_goal : ∀ (i : {i : Fin n // i ≠ k}),
      ((a i - z' i) • A) + (d • A) ⊆ iteratedSumsetFin Sdiff2 N' := by
    intro i w hw
    have h_add : ∃ (u : ℝ), u ∈ ((a i - z' i) • A) ∧ ∃ (v : ℝ), v ∈ (d • A) ∧ u + v = w := by
      simpa [Set.mem_add] using hw
    rcases h_add with ⟨u, hu, v, hv, h_uv⟩
    have h_smul1 : ∃ (x : ℝ), x ∈ A ∧ (a i - z' i) * x = u := by
      simpa [Set.mem_smul_set] using hu
    rcases h_smul1 with ⟨x, hx, h_ux⟩
    have h_eq2 : u = (a i - z' i) * x := h_ux.symm
    have h_smul2 : ∃ (y : ℝ), y ∈ A ∧ d * y = v := by
      simpa [Set.mem_smul_set] using hv
    rcases h_smul2 with ⟨y, hy, h_vy⟩
    have h_eq3 : v = d * y := h_vy.symm
    have h_eq1 : w = u + v := h_uv.symm
    rw [h_eq1, h_eq2, h_eq3]
    have h_expand : (a i - z' i) * x + d * y =
        (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x + ℓ_vec k * y := by
      simp [hz', hd] <;> ring
    rw [h_expand]
    have h1 : (a i - b i) * x ∈ Sdiff2 := diff_smul_in_productDiff (ha i) (hb i) hx
    have h2 : (b k - a k) * y ∈ Sdiff2 := diff_smul_in_productDiff (hb k) (ha k) hy
    have h12 : (a i - b i) * x + (b k - a k) * y ∈ iteratedSumsetFin Sdiff2 2 :=
      iteratedSumsetFin_add (single_in_iteratedFin h1) (single_in_iteratedFin h2)
    have h3 : -ℓ_vec i * x ∈ iteratedSumsetFin Sdiff2 (2 * (m i).natAbs) := by
      have h31 : ℓ_vec i * x ∈ iteratedSumsetFin Sdiff2 (2 * (m i).natAbs) := by
        rw [hm i]; exact int_multiple_in_iteratedFin h_diam_in_diff hx
      rcases h31 with ⟨f, hf, hsum⟩
      let g : Fin (2 * (m i).natAbs) → ℝ := fun j => -(f j)
      have hg1 : ∀ j, g j ∈ Sdiff2 := by intro j; exact productDiff_neg_closed (hf j)
      have hg2 : ∑ j, g j = -ℓ_vec i * x := by
        have h : ∑ j, g j = -(∑ j, f j) := by rw [Finset.sum_neg_distrib] <;> rfl
        rw [h, hsum] <;> ring
      exact ⟨g, hg1, hg2⟩
    have h4 : ℓ_vec k * y ∈ iteratedSumsetFin Sdiff2 (2 * (m k).natAbs) := by
      rw [hm k]; exact int_multiple_in_iteratedFin h_diam_in_diff hy
    have h123 : (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x ∈
        iteratedSumsetFin Sdiff2 (2 + 2 * (m i).natAbs) := by
      have h_eq : (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x =
          ((a i - b i) * x + (b k - a k) * y) + (-ℓ_vec i * x) := by ring
      rw [h_eq]; exact iteratedSumsetFin_add h12 h3
    have h_final : (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x + ℓ_vec k * y ∈
        iteratedSumsetFin Sdiff2 (2 + 2 * (m i).natAbs + 2 * (m k).natAbs) :=
      iteratedSumsetFin_add h123 h4
    have h_le : 2 + 2 * (m i).natAbs + 2 * (m k).natAbs ≤ N' := by
      dsimp only [N']; have h5 : (m i).natAbs ≤ M := hM_ge i
      have h6 : (m k).natAbs ≤ M := hM_ge k; omega
    exact h_mono _ _ h_le h_final
  have h_fin_eq1 : iteratedSumsetFin Sdiff2 N' =
      iteratedSumset ((productSet A 2) - (productSet A 2)) N' := by
    have hSdiff_eq : Sdiff2 = (productSet A 2) - (productSet A 2) := by
      have h1 : Sdiff2 = productSet2 A - productSet2 A := rfl
      rw [h1]; exact congr_arg (fun x => x - x) h_pset_eq
    rw [hSdiff_eq, iteratedSumsetFin_eq_recursive]
  have h_fin_eq2 : iteratedSumsetFin (productSet2 A) N' = iteratedSumset (productSet A 2) N' := by
    rw [h_pset_eq, iteratedSumsetFin_eq_recursive]
  have h_ideq : iteratedSumset ((productSet A 2) - (productSet A 2)) N' =
      iteratedDifference (productSet A 2) N' := by
    have h := iteratedDifferenceFin_eq (A := A) (N := N')
    have h5 : iteratedSumsetFin (productSet2 A - productSet2 A) N' =
        iteratedSumset ((productSet A 2) - (productSet A 2)) N' := h_fin_eq1
    have h6 : iteratedSumsetFin (productSet2 A) N' = iteratedSumset (productSet A 2) N' := h_fin_eq2
    have h7 : iteratedSumset ((productSet A 2) - (productSet A 2)) N' =
        Set.image2 (· - ·) (iteratedSumset (productSet A 2) N') (iteratedSumset (productSet A 2) N') := by
      rw [←h5, h]
      congr <;> exact h6
    simpa [iteratedDifference] using h7
  refine ⟨N', rfl, hN'_pos, ?_, h_ideq⟩
  intro i
  have h := h_main_goal i
  have h_eq : iteratedSumsetFin Sdiff2 N' = iteratedSumset ((productSet A 2) - (productSet A 2)) N' := by
    have hSdiff_eq : Sdiff2 = (productSet A 2) - (productSet A 2) := by
      have h1 : Sdiff2 = productSet2 A - productSet2 A := rfl
      rw [h1]; exact congr_arg (fun x => x - x) h_pset_eq
    rw [hSdiff_eq, iteratedSumsetFin_eq_recursive]
  rw [h_eq] at h
  exact h

/-- Extracts the sumset containment step from the expansion lemma proof. -/
lemma expansion_containment_step {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    {n : ℕ} (v : Fin n → ℝ) (k : Fin n)
    (a z' : Fin n → ℝ) (d : ℝ) (N' : ℕ)
    (hN'_contain : ∀ (i : {i : Fin n // i ≠ k}),
      ((a i - z' i) • A) + (d • A) ⊆
        iteratedSumset ((productSet A 2) - (productSet A 2)) N')
    (hN'_eq : iteratedSumset ((productSet A 2) - (productSet A 2)) N' =
      iteratedDifference (productSet A 2) N')
    (h_id : v k * d = ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i))
    (S : Set ℝ) (hS : S = scaledSumset v A) :
    d • S ⊆ scaledSumsetExcept v k (iteratedDifference (productSet A 2) N') := by
  intro x hx
  rcases hx with ⟨s, hs, rfl⟩
  have hs' : s ∈ scaledSumset v A := by
    rw [hS] at hs; exact hs
  rcases hs' with ⟨a', ha', h_s_eq⟩
  let t : {i : Fin n // i ≠ k} → ℝ := fun i => (a i - z' i) * a' k + d * a' i
  have h_t_in : ∀ i : {i : Fin n // i ≠ k}, t i ∈ iteratedDifference (productSet A 2) N' := by
    intro i
    have h1 : (a i - z' i) * a' k ∈ (a i - z' i) • A := ⟨a' k, ha' k, rfl⟩
    have h2 : d * a' i ∈ d • A := ⟨a' i, ha' i, rfl⟩
    have h3 : (a i - z' i) * a' k + d * a' i ∈ ((a i - z' i) • A) + (d • A) :=
      ⟨(a i - z' i) * a' k, h1, d * a' i, h2, by ring⟩
    have h4 := hN'_contain i h3
    rw [hN'_eq] at h4
    exact h4
  have h_sum_eq : d * s = ∑ i : {i : Fin n // i ≠ k}, v i * t i := by
    have h_s_eq' : s = ∑ i : Fin n, v i * a' i := h_s_eq
    rw [h_s_eq']
    have h_split1 : ∑ i : Fin n, v i * a' i = v k * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * a' i :=
      sum_fin_split k (fun i => v i * a' i)
    rw [h_split1]
    have h_distrib : d * (v k * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * a' i) =
        v k * d * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * (d * a' i) := by
      have h1 : d * (v k * a' k) = v k * d * a' k := by ring
      have h2 : d * (∑ i : {i : Fin n // i ≠ k}, v i * a' i) =
          ∑ i : {i : Fin n // i ≠ k}, d * (v i * a' i) := by
        rw [Finset.mul_sum]
      have h3 : ∑ i : {i : Fin n // i ≠ k}, d * (v i * a' i) =
          ∑ i : {i : Fin n // i ≠ k}, v i * (d * a' i) := by
        apply Finset.sum_congr rfl
        intro i _
        have h4 : d * (v i * a' i) = v i * (d * a' i) := by
          ring
        exact h4
      calc d * (v k * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * a' i)
        = d * (v k * a' k) + d * (∑ i : {i : Fin n // i ≠ k}, v i * a' i) := by rw [mul_add]
      _ = v k * d * a' k + ∑ i : {i : Fin n // i ≠ k}, d * (v i * a' i) := by rw [h1, h2]
      _ = v k * d * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * (d * a' i) := by rw [h3]
    rw [h_distrib]
    have h3 : v k * d * a' k = (∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i)) * a' k := by
      rw [h_id] <;> ring
    rw [h3]
    have h4 : (∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i)) * a' k =
        ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) * a' k := by
      rw [Finset.sum_mul] <;> rfl
    rw [h4]
    have h5 : ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) * a' k +
        ∑ i : {i : Fin n // i ≠ k}, v i * (d * a' i) =
        ∑ i : {i : Fin n // i ≠ k}, v i * t i := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have h6 : v i * (a i - z' i) * a' k + v i * (d * a' i) = v i * t i := by
        dsimp only [t]
        have h7 : v i * (a i - z' i) * a' k + v i * (d * a' i) =
            v i * ((a i - z' i) * a' k + d * a' i) := by ring
        rw [h7] <;> rfl
      exact h6
    exact h5
  have h_member : (∑ i : {i : Fin n // i ≠ k}, v i * t i) ∈
      scaledSumsetExcept v k (iteratedDifference (productSet A 2) N') :=
    ⟨t, h_t_in, rfl⟩
  exact Eq.subst h_sum_eq.symm h_member

/-- The absolute value of any coordinate of a Euclidean space vector is bounded by its norm. -/
lemma euclidean_coord_abs_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h1 : (x i)^2 ≤ ∑ j : Fin n, (x j)^2 := by
    apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : ‖x‖ ^ 2 = ∑ j : Fin n, (x j)^2 := EuclideanSpace.real_norm_sq_eq x
  have h3 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    calc |x i| ^ 2
      = (x i)^2 := by rw [sq_abs]
    _ ≤ ∑ j : Fin n, (x j)^2 := h1
    _ = ‖x‖ ^ 2 := h2.symm
  have h4 : 0 ≤ |x i| := by positivity
  have h5 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-- Norm bound for points in `boxC`. -/
lemma boxC_norm_bound {n : ℕ} (hn : 0 < n) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ boxC (n := n) hn R) :
    ‖x‖ ≤ Real.sqrt (1 + (n : ℝ) * R^2) := by
  let i0 : Fin n := ⟨0, hn⟩
  have h1 : |x i0| ≤ 1 := hx.1
  have h2 : ∀ i, i ≠ i0 → |x i| ≤ R := hx.2
  have h3 : ∑ i : Fin n, (x i)^2 ≤ 1 + (n : ℝ) * R^2 := by
    have h4 : ∑ i : Fin n, (x i)^2 = (x i0)^2 + ∑ i ∈ Finset.univ.erase i0, (x i)^2 := by
      have h5 : insert i0 (Finset.univ.erase i0) = (Finset.univ : Finset (Fin n)) := by
        ext y; simp
      have h6 : ∑ i : Fin n, (x i)^2 = ∑ i ∈ insert i0 (Finset.univ.erase i0), (x i)^2 := by
        rw [h5]
      rw [h6, Finset.sum_insert (by simp)] <;> ring
    rw [h4]
    have h7 : (x i0)^2 ≤ 1 := by
      have h71 : -1 ≤ x i0 ∧ x i0 ≤ 1 := abs_le.mp h1
      nlinarith
    have h8 : ∑ i ∈ Finset.univ.erase i0, (x i)^2 ≤ ((n : ℝ) - 1) * R^2 := by
      have h9 : ∑ i ∈ Finset.univ.erase i0, (x i)^2 ≤ ∑ i ∈ Finset.univ.erase i0, R^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h10 : i ≠ i0 := (Finset.mem_erase.mp hi).1
        have h11 : |x i| ≤ R := h2 i h10
        have h12 : (x i)^2 ≤ R^2 := by nlinarith [abs_le.mp h11]
        exact h12
      have h_card : (Finset.univ.erase i0).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i0)]
        simp
      have h_sum_const : ∑ i ∈ Finset.univ.erase i0, R^2 =
          ((Finset.univ.erase i0).card : ℝ) * R^2 := by
        simp [Finset.sum_const]
        <;> ring
      have h13 : ∑ i ∈ Finset.univ.erase i0, R^2 = ((n : ℝ) - 1) * R^2 := by
        rw [h_sum_const, h_card]
        cases n with
        | zero => contradiction
        | succ n' => simp [Nat.cast_add] <;> ring
      rw [h13] at h9
      exact h9
    have h10 : 0 ≤ R^2 := by positivity
    linarith
  have h4 : ‖x‖ ^ 2 = ∑ i : Fin n, (x i)^2 := EuclideanSpace.real_norm_sq_eq x
  have h5 : ‖x‖ ^ 2 ≤ 1 + (n : ℝ) * R^2 := by
    rw [h4] <;> exact h3
  have h6 : 0 ≤ ‖x‖ := by positivity
  have h7 : 0 ≤ 1 + (n : ℝ) * R^2 := by positivity
  nlinarith [Real.sqrt_nonneg (1 + (n : ℝ) * R^2), Real.sq_sqrt (show 0 ≤ 1 + (n : ℝ) * R^2 by positivity)]

/-! ## Uniform expansion theorem -/

/-- **Uniform Expansion Lemma**.

Given bounds `d_max` on the diameter and `lam_min` on the volume of the
scaled sumset, there exists `N_max` depending ONLY on `n, d_max, lam_min`
such that the expansion lemma conclusion holds with `N = N_max` for
every set A and weights v satisfying the bounds. -/
theorem expansion_lemma_uniform {n : ℕ} (hn : 2 ≤ n)
    {d_max lam_min : ℝ} (hd_max_pos : 0 < d_max) (hlam_min_pos : 0 < lam_min) :
    ∃ (N_max : ℕ), 0 < N_max ∧
      ∀ (A : Set ℝ), IsCompact A → A.Nonempty →
        diam A ≤ d_max →
        ∀ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
          ENNReal.ofReal lam_min ≤ volume (scaledSumset v A) →
            ∃ (j : Fin n),
              volume (scaledSumsetExcept v j
                (iteratedDifference (productSet A 2) N_max)) ≥
              ENNReal.ofReal (diam A) * volume (scaledSumset v A) := by
  let v_norm_max : ℝ := Real.sqrt (n : ℝ)
  let C_val_max : ℝ := (n : ℝ) * d_max + 2 * v_norm_max

  let N_pigeon : ℕ := Nat.ceil (C_val_max / lam_min) + 1
  have hN_pigeon_pos : 0 < N_pigeon := by simp [N_pigeon] <;> omega

  let target_uniform : ENNReal := ENNReal.ofReal ((N_pigeon : ℝ) * (2 * d_max)^n)
  have htarget_lt_top : target_uniform < ⊤ := ENNReal.ofReal_lt_top
  have hR : ∃ (R : ℝ), 1 ≤ R ∧ target_uniform < volume (boxC (n := n) (by linarith) R) :=
    boxC_volume_grows (n := n) (by linarith) target_uniform htarget_lt_top
  rcases hR with ⟨R, hR1, hR_vol_uniform⟩

  let δ_min : ℝ := 2 * lam_min / (n : ℝ)
  have hδ_min_pos : 0 < δ_min := by positivity

  let N_max : ℕ := 2 + 4 * Nat.ceil (2 * Real.sqrt (1 + (n : ℝ) * R^2) / δ_min)
  have hN_max_pos : 0 < N_max := by simp [N_max] <;> omega

  refine ⟨N_max, hN_max_pos, ?_⟩
  intro A hA hA_nonempty h_diam_max v hv h_vol_min

  let S := scaledSumset v A
  let π : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i : Fin n, v i * x i
  let volS : ENNReal := volume S
  have h_vol_pos : 0 < volS :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hlam_min_pos) h_vol_min
  have hS_compact : IsCompact S := scaledSumset_compact hA
  have hS_meas : MeasurableSet S := hS_compact.measurableSet
  have hS_nonempty : S.Nonempty := by
    obtain ⟨a, ha⟩ := hA_nonempty
    exact ⟨∑ i : Fin n, v i * a, ⟨fun _ => a, fun _ => ha, rfl⟩⟩
  have hvolS_lt_top : volS < ⊤ := hS_compact.measure_lt_top

  have h_diam_pos : 0 < diam A := diam_pos hA hA_nonempty (hpos := h_vol_pos)
  let c := diam A
  have h_diam_in_diff : c ∈ A - A := diam_in_difference hA hA_nonempty

  let v_eucl : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm v
  let i0 : Fin n := ⟨0, by linarith⟩
  have h_v_norm_pos : 0 < ‖v_eucl‖ := by
    have h1 : v_eucl i0 = v i0 := by simp [v_eucl] <;> rfl
    have h2 : 0 < v i0 := by have h := (hv i0).1; linarith
    have h3 : 0 < |v_eucl i0| := by
      rw [h1]; exact abs_pos.mpr (ne_of_gt h2)
    have h4 : 0 < ‖v_eucl i0‖ := by simpa [Real.norm_eq_abs] using h3
    have h5 : 0 < ‖v_eucl‖ := by
      have h6 : ‖v_eucl i0‖ ≤ ‖v_eucl‖ := PiLp.norm_apply_le v_eucl i0
      exact lt_of_lt_of_le h4 h6
    exact h5
  let v_norm := ‖v_eucl‖
  let C_val : ℝ := (n : ℝ) * c + 2 * v_norm

  have h_v_norm_le : ‖v_eucl‖ ≤ v_norm_max := by
    have h1 : ‖v_eucl‖ = Real.sqrt (∑ i : Fin n, |v_eucl i| ^ 2) := EuclideanSpace.norm_eq v_eucl
    rw [h1]
    have h2 : ∑ i : Fin n, |v_eucl i| ^ 2 = ∑ i : Fin n, (v i)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      have h4 : v_eucl i = v i := by simp [v_eucl] <;> rfl
      have h5 : |v_eucl i| ^ 2 = (v i)^2 := by
        rw [h4]
        have h6 : 0 ≤ v i := by
          have h7 : v i ∈ Set.Icc (1 / 2 : ℝ) 1 := hv i
          linarith [h7.1]
        rw [abs_of_nonneg h6] <;> ring
      exact h5
    rw [h2]
    have h3 : ∀ i : Fin n, (v i)^2 ≤ 1 := by
      intro i
      have h4 : v i ∈ Set.Icc (1 / 2 : ℝ) 1 := hv i
      have h5 : 0 ≤ v i := by linarith [h4.1]
      have h6 : v i ≤ 1 := h4.2
      nlinarith
    have h7 : ∑ i : Fin n, (v i)^2 ≤ (n : ℝ) := by
      calc ∑ i : Fin n, (v i)^2
        ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h3 i)
      _ = (n : ℝ) := by simp
    have h8 : Real.sqrt (∑ i : Fin n, (v i)^2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h7
    exact h8

  have hC_val_le : C_val ≤ C_val_max := by
    dsimp only [C_val, C_val_max]
    have h1 : (n : ℝ) * diam A ≤ (n : ℝ) * d_max := by gcongr
    have h2 : 2 * ‖v_eucl‖ ≤ 2 * v_norm_max := by gcongr
    linarith

  have hS_diam_le : volS ≤ ENNReal.ofReal ((n : ℝ) * diam A) := by
    have hS_compact' : IsCompact S := hS_compact
    have hBdd : Bornology.IsBounded S := hS_compact'.isBounded
    have h_diamS : diam S ≤ (n : ℝ) * diam A :=
      Metric.diam_le_of_forall_dist_le_of_nonempty hS_nonempty
        (fun x hx y hy => scaledSumset_diam_bound hA hv x y hx hy)
    have h : volS ≤ ENNReal.ofReal (diam S) := by
      have hS_bdd : Bornology.IsBounded S := hS_compact.isBounded
      let a := sInf S
      let b := sSup S
      have h_bddBelow : BddBelow S := hS_compact.bddBelow
      have h_sub : S ⊆ Set.Icc a b := by
        intro x hx
        have h1 : a ≤ x := csInf_le h_bddBelow hx
        have h2 : x ≤ b := le_csSup hS_compact.bddAbove hx
        exact ⟨h1, h2⟩
      have h_vol : volS ≤ volume (Set.Icc a b) := measure_mono h_sub
      have h_diam : diam S = b - a := Real.diam_eq hS_bdd
      rw [h_diam] at *
      simpa [Real.volume_Icc] using h_vol
    exact le_trans h (ENNReal.ofReal_le_ofReal h_diamS)

  have h_diam_lower : lam_min ≤ (n : ℝ) * diam A := by
    have h1 : ENNReal.ofReal lam_min ≤ volS := h_vol_min
    have h2 : volS ≤ ENNReal.ofReal ((n : ℝ) * diam A) := hS_diam_le
    have h3 : ENNReal.ofReal lam_min ≤ ENNReal.ofReal ((n : ℝ) * diam A) := le_trans h1 h2
    have h_nonneg : 0 ≤ (n : ℝ) * diam A := by positivity
    have h4 : (lam_min : ℝ) ≤ (n : ℝ) * diam A :=
      (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h3
    exact h4

  have hδ_lower : δ_min ≤ 2 * diam A := by
    dsimp only [δ_min]
    have h4 : lam_min ≤ (n : ℝ) * diam A := h_diam_lower
    have h_n_pos : (n : ℝ) > 0 := by exact_mod_cast (show 0 < n from by linarith)
    have h5 : 2 * lam_min / (n : ℝ) ≤ 2 * diam A := by
      have h7 : 2 * lam_min ≤ 2 * (n : ℝ) * diam A := by
        calc 2 * lam_min
          ≤ 2 * ((n : ℝ) * diam A) := by gcongr
        _ = 2 * (n : ℝ) * diam A := by ring
      calc 2 * lam_min / (n : ℝ)
        ≤ (2 * (n : ℝ) * diam A) / (n : ℝ) := by gcongr
      _ = 2 * diam A := by
        field_simp [h_n_pos.ne'] <;> ring
    exact h5

  have hN_pigeon_ineq : (N_pigeon + 1 : ENNReal) * volS > ENNReal.ofReal C_val := by
    have h1 : (N_pigeon : ℝ) ≥ C_val_max / lam_min := by
      have h2 : (N_pigeon : ℝ) = (Nat.ceil (C_val_max / lam_min) : ℝ) + 1 := by
        simp [N_pigeon] <;> norm_cast
      rw [h2]
      have h3 : (Nat.ceil (C_val_max / lam_min) : ℝ) ≥ C_val_max / lam_min := Nat.le_ceil _
      linarith
    have h2 : ((N_pigeon + 1 : ℝ) * ENNReal.toReal volS) > C_val := by
      have h3 : ENNReal.toReal volS ≥ lam_min := by
        have h4 : ENNReal.ofReal lam_min ≤ volS := h_vol_min
        have h5 : (ENNReal.ofReal lam_min).toReal ≤ ENNReal.toReal volS := by
          exact ENNReal.toReal_mono hvolS_lt_top.ne h4
        have h6 : (ENNReal.ofReal lam_min).toReal = lam_min :=
          ENNReal.toReal_ofReal (by linarith)
        rw [h6] at h5
        exact h5
      have h5 : (N_pigeon + 1 : ℝ) * ENNReal.toReal volS ≥ (N_pigeon + 1 : ℝ) * lam_min := by gcongr
      have h6 : (N_pigeon + 1 : ℝ) * lam_min > C_val_max := by
        have h7 : (N_pigeon : ℝ) ≥ C_val_max / lam_min := h1
        have h8 : (N_pigeon + 1 : ℝ) * lam_min > C_val_max := by
          have h9 : (N_pigeon + 1 : ℝ) * lam_min > (N_pigeon : ℝ) * lam_min := by
            have h10 : 0 < lam_min := hlam_min_pos
            nlinarith
          have h11 : (N_pigeon : ℝ) * lam_min ≥ (C_val_max / lam_min) * lam_min := by
            gcongr
          have h12 : (C_val_max / lam_min) * lam_min = C_val_max := by
            field_simp [hlam_min_pos.ne'] <;> ring
          nlinarith
        exact h8
      have h9 : C_val ≤ C_val_max := hC_val_le
      linarith
    have h10 : ENNReal.ofReal ((N_pigeon + 1 : ℝ) * ENNReal.toReal volS) =
        (N_pigeon + 1 : ENNReal) * volS := by
      have h11 : ENNReal.ofReal (ENNReal.toReal volS) = volS :=
        ENNReal.ofReal_toReal hvolS_lt_top.ne
      have h12 : ENNReal.ofReal ((N_pigeon + 1 : ℝ) * ENNReal.toReal volS) =
          ENNReal.ofReal (N_pigeon + 1 : ℝ) * ENNReal.ofReal (ENNReal.toReal volS) := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h12, h11] <;> norm_cast
    rw [←h10]
    have h13 : ENNReal.ofReal C_val < ENNReal.ofReal ((N_pigeon + 1 : ℝ) * ENNReal.toReal volS) := by
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr h2
    exact h13

  have hR_vol : ENNReal.ofReal ((N_pigeon : ℝ) * (2 * diam A)^n) <
      @volume (EuclideanSpace ℝ (Fin n)) _ (boxC (n := n) (by linarith) R) := by
    have h13 : (2 * diam A)^n ≤ (2 * d_max)^n := by gcongr
    have h14 : (N_pigeon : ℝ) * (2 * diam A)^n ≤ (N_pigeon : ℝ) * ((2 * d_max)^n) := by gcongr
    have h15 : ENNReal.ofReal ((N_pigeon : ℝ) * (2 * diam A)^n) ≤
        ENNReal.ofReal ((N_pigeon : ℝ) * ((2 * d_max)^n)) := by
      exact ENNReal.ofReal_le_ofReal h14
    have h16 : target_uniform = ENNReal.ofReal ((N_pigeon : ℝ) * ((2 * d_max)^n)) := by rfl
    rw [h16] at hR_vol_uniform
    exact lt_of_le_of_lt h15 hR_vol_uniform

  let δ := 2 * c
  have hδ_pos : 0 < δ := by positivity

  let w : EuclideanSpace ℝ (Fin n) := (1 / v_norm) • v_eucl
  have hw_norm : ‖w‖ = 1 := by
    have h1 : ‖w‖ = |(1 / v_norm : ℝ)| * ‖v_eucl‖ := norm_smul (1 / v_norm) v_eucl
    rw [h1]
    have h2 : |(1 / v_norm : ℝ)| = 1 / v_norm := by
      have h_pos2 : 0 < (1 / v_norm : ℝ) := by positivity
      rw [abs_of_pos h_pos2]
    rw [h2]
    have h3 : (1 / v_norm) * ‖v_eucl‖ = 1 := by
      have h4 : ‖v_eucl‖ = v_norm := rfl
      rw [h4]
      have h5 : (1 / v_norm) * v_norm = 1 := by
        have hnz : v_norm ≠ 0 := h_v_norm_pos.ne'
        field_simp [hnz] <;> ring
      exact h5
    exact h3

  rcases exists_orthogonal_map_first (by linarith) w hw_norm with ⟨U, e0, he0, hUe0, h_e0_coord⟩

  let V := U '' (boxC (n := n) (by linarith) R)
  have hboxC_meas : MeasurableSet (boxC (n := n) (by linarith) R) := by
    have h_closed1 : IsClosed {x : EuclideanSpace ℝ (Fin n) | |x i0| ≤ 1} := by
      exact isClosed_le (continuous_abs.comp (by fun_prop)) continuous_const
    let s : Finset (Fin n) := Finset.univ.erase i0
    have h_closed2 : IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, i ≠ i0 → |x i| ≤ R} := by
      have h_eq : {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, i ≠ i0 → |x i| ≤ R} =
          ⋂ i ∈ s, {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ R} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_coe]
        constructor
        · intro h i hi
          have hni : i ≠ i0 := by simpa [s, Finset.mem_erase] using hi
          exact h i hni
        · intro h i hni
          have hi : i ∈ s := by simp [s, Finset.mem_erase, hni]
          exact h i hi
      rw [h_eq]
      exact isClosed_biInter (h := fun i _ =>
        isClosed_le (continuous_abs.comp (by fun_prop)) continuous_const)
    have h_box_eq : boxC (n := n) (by linarith) R =
        {x : EuclideanSpace ℝ (Fin n) | |x i0| ≤ 1} ∩
        {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, i ≠ i0 → |x i| ≤ R} := by
      ext x; simp [boxC] <;> tauto
    have h_closed : IsClosed (boxC (n := n) (by linarith) R) := by
      rw [h_box_eq]; exact h_closed1.inter h_closed2
    exact h_closed.measurableSet
  have hU_meas : Measurable U := U.continuous.measurable
  have hU_symm_meas : Measurable U.symm := U.symm.continuous.measurable
  have hV_preimage : V = U.symm ⁻¹' (boxC (n := n) (by linarith) R) := by
    ext y
    simp only [V, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h : U.symm (U x) = x := U.symm_apply_apply x
      rw [h] <;> exact hx
    · intro hy
      refine ⟨U.symm y, hy, ?_⟩
      exact U.apply_symm_apply y
  have hV_meas : MeasurableSet V := by
    rw [hV_preimage]
    exact hboxC_meas.preimage hU_symm_meas
  have hU_mp : MeasurePreserving U volume volume := LinearIsometryEquiv.measurePreserving U
  have hV_vol : @volume (EuclideanSpace ℝ (Fin n)) _ V =
      @volume (EuclideanSpace ℝ (Fin n)) _ (boxC (n := n) (by linarith) R) := by
    have h3 : U ⁻¹' V = boxC (n := n) (by linarith) R := by ext x; simp [V]
    have h4 : volume (U ⁻¹' V) = volume V := hU_mp.measure_preimage hV_meas.nullMeasurableSet
    rw [h3] at h4
    exact h4.symm

  have hπV : ∀ y ∈ V, |π y| ≤ v_norm := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_symm : U.symm v_eucl = v_norm • e0 := by
      have h3 : U e0 = (1 / v_norm) • v_eucl := hUe0
      have h4 : U.symm (U e0) = e0 := U.symm_apply_apply e0
      have h5 : U.symm ((1 / v_norm) • v_eucl) = e0 := by rw [←h3] <;> exact h4
      have h6 : (1 / v_norm) • U.symm v_eucl = e0 := by simpa [map_smul] using h5
      have h9 : v_norm • ((1 / v_norm) • U.symm v_eucl) = U.symm v_eucl := by
        rw [smul_smul]
        have h10 : v_norm * (1 / v_norm) = 1 := by
          have hnz : v_norm ≠ 0 := h_v_norm_pos.ne'
          field_simp [hnz] <;> ring
        rw [h10, one_smul]
      have h11 : v_norm • ((1 / v_norm) • U.symm v_eucl) = v_norm • e0 := by rw [h6]
      rw [h9] at h11
      exact h11
    have h_inner_eq : ∀ (a b : EuclideanSpace ℝ (Fin n)), inner ℝ a b = ∑ i : Fin n, a i * b i := by
      intro a b
      have h1 : inner ℝ a b = ∑ i : Fin n, inner ℝ (a i) (b i) := by
        exact PiLp.inner_apply (𝕜 := ℝ) a b
      rw [h1]
      apply Finset.sum_congr rfl
      intro i _
      have h2 : inner ℝ (a i) (b i) = a i * b i := Real.inner_apply (a i) (b i)
      exact h2
    have h1 : π (U x) = inner ℝ v_eucl (U x) := by
      have h2 : inner ℝ v_eucl (U x) = ∑ i : Fin n, v_eucl i * (U x) i := h_inner_eq v_eucl (U x)
      rw [h2]
      have h3 : ∑ i : Fin n, v_eucl i * (U x) i = ∑ i : Fin n, v i * (U x) i := by
        apply Finset.sum_congr rfl
        intro i _
        have h4 : v_eucl i = v i := by simp [v_eucl] <;> rfl
        rw [h4]
      rw [h3] <;> rfl
    rw [h1]
    have h3 : inner ℝ v_eucl (U x) = inner ℝ (U (U.symm v_eucl)) (U x) := by
      have h_eq : U (U.symm v_eucl) = v_eucl := U.apply_symm_apply v_eucl
      rw [h_eq]
    rw [h3]
    have h4 : inner ℝ (U (U.symm v_eucl)) (U x) = inner ℝ (U.symm v_eucl) x :=
      LinearIsometryEquiv.inner_map_map U (U.symm v_eucl) x
    rw [h4, h_symm]
    have h5 : inner ℝ (v_norm • e0) x = v_norm * inner ℝ e0 x := by
      simp [inner_smul_left]
    rw [h5]
    have h6 : inner ℝ e0 x = x i0 := by
      have h7 : inner ℝ e0 x = ∑ i : Fin n, e0 i * x i := h_inner_eq e0 x
      rw [h7]
      have h8 : ∀ j, e0 j * x j = if j = i0 then x j else 0 := by
        intro j
        by_cases hj : j = i0
        · rw [hj, h_e0_coord i0, if_pos rfl] <;> simp
        · have hz : e0 j = 0 := by
            rw [h_e0_coord j]
            have hif : (if j = i0 then (1 : ℝ) else 0) = 0 := by simp [hj]
            rw [hif] <;> rfl
          rw [hz, if_neg hj] <;> ring
      have h9 : ∑ i : Fin n, e0 i * x i = ∑ i : Fin n, (if i = i0 then x i else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h8 i
      rw [h9]
      simp
    rw [h6]
    have h7 : |x i0| ≤ 1 := hx.1
    have h8 : |v_norm * x i0| = v_norm * |x i0| := by
      rw [abs_mul, abs_of_pos h_v_norm_pos]
    rw [h8]
    have h9 : v_norm * |x i0| ≤ v_norm := by
      have h10 : |x i0| ≤ 1 := h7
      have h11 : v_norm * |x i0| ≤ v_norm * 1 := by gcongr
      linarith
    exact h9

  have hBlich : ENNReal.ofReal ((N_pigeon : ℝ) * δ^n) < volume V := by
    rw [hV_vol]; exact hR_vol
  rcases blichfeldt_n_dim (by linarith) hδ_pos hV_meas hBlich with ⟨p, hp_inj, hp_in_V, hp_lattice⟩

  let S_k : Fin (N_pigeon + 1) → Set ℝ := fun k => S + {π (p k)}
  have hSk_meas : ∀ k, MeasurableSet (S_k k) := by
    intro k
    have h_cont : Continuous (fun x : ℝ => x + π (p k)) := by continuity
    have h_compact : IsCompact (S_k k) := by
      have h_eq2 : S_k k = (fun x : ℝ => x + π (p k)) '' S := by
        ext z; simp [S_k, Set.mem_add, Set.mem_image] <;> aesop
      rw [h_eq2]
      exact hS_compact.image h_cont
    exact h_compact.measurableSet
  have hSk_vol : ∀ k, volume (S_k k) = volS := by
    intro k
    have h_eq : S_k k = (fun x : ℝ => x + π (p k)) '' S := by
      ext z
      simp [S_k, Set.mem_add, Set.mem_image]
      <;> aesop
    rw [h_eq]
    have h_trans : MeasurePreserving (fun x : ℝ => x + π (p k)) volume volume :=
      measurePreserving_add_right volume (π (p k))
    have h : volume ((fun x : ℝ => x + π (p k)) '' S) = volS := by
      have h_preimage : (fun x : ℝ => x + π (p k)) ⁻¹' ((fun x : ℝ => x + π (p k)) '' S) = S := by
        ext z; simp
      have h_image_meas : MeasurableSet ((fun x : ℝ => x + π (p k)) '' S) := by
        rw [←h_eq]
        exact hSk_meas k
      have h4 : volume ((fun x : ℝ => x + π (p k)) ⁻¹' ((fun x : ℝ => x + π (p k)) '' S)) =
          volume ((fun x : ℝ => x + π (p k)) '' S) :=
        h_trans.measure_preimage (s := (fun x : ℝ => x + π (p k)) '' S) h_image_meas.nullMeasurableSet
      rw [h_preimage] at h4
      exact h4.symm
    exact h
  have hSk_vol' : ∀ k, volume (S_k k) ≥ volS := by intro k; rw [hSk_vol k]

  let minS := sInf S
  let maxS := sSup S
  have hS_subset : S ⊆ Set.Icc minS maxS := by
    intro x hx
    have h_bdd_below : BddBelow S := hS_compact.bddBelow
    have h_bdd_above : BddAbove S := hS_compact.bddAbove
    have h1 : minS ≤ x := by exact (csInf_le_iff h_bdd_below hS_nonempty).mpr fun b a => a hx
    have h2 : x ≤ maxS := le_csSup h_bdd_above hx
    exact ⟨h1, h2⟩

  have hS_diam : maxS - minS ≤ (n : ℝ) * c := by
    have hBdd : Bornology.IsBounded S := hS_compact.isBounded
    have h_diam_eq : diam S = maxS - minS := Real.diam_eq hBdd
    have h_diam_le : diam S ≤ (n : ℝ) * c :=
      Metric.diam_le_of_forall_dist_le_of_nonempty hS_nonempty
        (fun x hx y hy => scaledSumset_diam_bound hA hv x y hx hy)
    linarith [h_diam_eq, h_diam_le]

  have hSk_subset : ∀ k, S_k k ⊆ Set.Icc (minS - v_norm) (maxS + v_norm) := by
    intro k z hz
    rcases Set.mem_add.mp hz with ⟨s, hs, t, ht, rfl⟩
    have h_t_eq : t = π (p k) := Set.mem_singleton_iff.mp ht
    rw [h_t_eq]
    have h1 : minS ≤ s := (hS_subset hs).1
    have h2 : s ≤ maxS := (hS_subset hs).2
    have h3 : |π (p k)| ≤ v_norm := hπV (p k) (hp_in_V k)
    have h4 : -v_norm ≤ π (p k) := by linarith [abs_le.mp h3]
    have h5 : π (p k) ≤ v_norm := by linarith [abs_le.mp h3]
    constructor <;> linarith

  have hUnion_bound : volume (⋃ k, S_k k) ≤ ENNReal.ofReal C_val := by
    have h_sub : (⋃ k, S_k k) ⊆ Set.Icc (minS - v_norm) (maxS + v_norm) := by
      intro z hz
      have h_exists : ∃ (k : Fin (N_pigeon + 1)), z ∈ S_k k := Set.mem_iUnion.mp hz
      rcases h_exists with ⟨k, hk⟩
      exact hSk_subset k hk
    have h_bdd_below : BddBelow S := hS_compact.bddBelow
    have h_bdd_above : BddAbove S := hS_compact.bddAbove
    have h_min_le_max : minS ≤ maxS := csInf_le_csSup hS_nonempty (hb := h_bdd_below) (ha := h_bdd_above)
    have h_len : minS - v_norm ≤ maxS + v_norm := by
      have h_vnorm_nonneg : 0 ≤ v_norm := by positivity
      linarith
    have h_vol_Icc : volume (Set.Icc (minS - v_norm) (maxS + v_norm)) =
        ENNReal.ofReal ((maxS + v_norm) - (minS - v_norm)) := by
      rw [Real.volume_Icc] <;> linarith
    calc volume (⋃ k, S_k k)
      ≤ volume (Set.Icc (minS - v_norm) (maxS + v_norm)) := measure_mono h_sub
    _ = ENNReal.ofReal ((maxS + v_norm) - (minS - v_norm)) := h_vol_Icc
    _ ≤ ENNReal.ofReal C_val := by
      have h : (maxS + v_norm) - (minS - v_norm) ≤ C_val := by
        have h2 : maxS - minS ≤ (n : ℝ) * c := hS_diam
        have h3 : (maxS + v_norm) - (minS - v_norm) = (maxS - minS) + 2 * v_norm := by ring
        rw [h3]
        have h4 : C_val = (n : ℝ) * c + 2 * v_norm := by
          simp [C_val] <;> ring
        rw [h4]
        linarith
      exact ENNReal.ofReal_le_ofReal h

  have h_card : Fintype.card (Fin (N_pigeon + 1)) = N_pigeon + 1 := by simp
  have h_cast : (↑(N_pigeon + 1) : ENNReal) = (↑N_pigeon + 1 : ENNReal) := by norm_cast
  have hN_ineq' : (↑(Fintype.card (Fin (N_pigeon + 1))) : ENNReal) * volS > ENNReal.ofReal C_val := by
    rw [h_card, h_cast]
    exact hN_pigeon_ineq
  have h_collision : ∃ (i j : Fin (N_pigeon + 1)), i ≠ j ∧ (S_k i ∩ S_k j).Nonempty :=
    measure_pigeonhole (μ := volume) (S := S_k) hSk_meas hSk_vol' hUnion_bound hN_ineq'

  rcases h_collision with ⟨i, j, hne, h_inter⟩
  have h_main_extract : ∃ (a b : Fin n → ℝ), (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ A) ∧
      (∑ k : Fin n, v k * a k) + π (p i) = (∑ k : Fin n, v k * b k) + π (p j) := by
    rcases h_inter with ⟨z, hzi, hzj⟩
    rcases Set.mem_add.mp hzi with ⟨s1, hs1, t1, ht1, hz1⟩
    rcases Set.mem_add.mp hzj with ⟨s2, hs2, t2, ht2, hz2⟩
    have ht1 : t1 = π (p i) := Set.mem_singleton_iff.mp ht1
    have ht2 : t2 = π (p j) := Set.mem_singleton_iff.mp ht2
    have h_eq : s1 + t1 = s2 + t2 := by
      rw [hz1, hz2]
    rcases hs1 with ⟨a, ha, rfl⟩
    rcases hs2 with ⟨b, hb, rfl⟩
    refine ⟨a, b, ha, hb, ?_⟩
    simpa [ht1, ht2] using h_eq
  rcases h_main_extract with ⟨a, b, ha, hb, h_eq⟩

  let ℓ_vec := p j - p i
  have hℓ_nonzero : ℓ_vec ≠ 0 := by
    intro h; have h' : p j = p i := by
      have h1 : p j - p i = 0 := h
      exact sub_eq_zero.mp h1
    have h2 : j = i := hp_inj h'
    exact hne h2.symm
  let z' := b + ℓ_vec

  rcases hp_lattice j i with ⟨m, hm⟩
  have hℓ_coord : ∀ k : Fin n, ∃ (mi : ℤ), ℓ_vec k = δ * (mi : ℝ) := by
    intro k
    refine ⟨m k, ?_⟩
    have h5 := congr_fun (congr_arg (EuclideanSpace.equiv (Fin n) ℝ) hm) k
    simpa [ℓ_vec] using h5

  have h_coord : ∃ (k : Fin n), ℓ_vec k ≠ 0 := by
    by_contra h; push Not at h
    have h7 : ℓ_vec = 0 := by ext k; exact h k
    exact hℓ_nonzero h7
  rcases h_coord with ⟨k, hk_nonzero⟩

  have hℓ_k_bound : |ℓ_vec k| ≥ δ := by
    rcases hℓ_coord k with ⟨mi, hmi⟩
    have hmi_ne_zero : (mi : ℝ) ≠ 0 := by
      intro h
      have h' : ℓ_vec k = 0 := by rw [hmi, h] <;> ring
      exact hk_nonzero h'
    have h_abs_one : 1 ≤ |(mi : ℝ)| := by
      have h : (mi : ℤ) ≠ 0 := by exact_mod_cast hmi_ne_zero
      have h' : 1 ≤ |mi| := Int.one_le_abs h
      exact_mod_cast h'
    calc |ℓ_vec k|
      = |δ * (mi : ℝ)| := by rw [hmi]
    _ = |δ| * |(mi : ℝ)| := by rw [abs_mul]
    _ = δ * |(mi : ℝ)| := by rw [abs_of_pos hδ_pos]
    _ ≥ δ * 1 := by gcongr
    _ = δ := by ring

  let d := (z' k - a k)
  have hd_bound : |d| ≥ c := by
    have h_d_eq : d = b k + ℓ_vec k - a k := by
      simp [d, z'] <;> ring
    rw [h_d_eq]
    set e := b k - a k with he
    have h_abs_e : |e| ≤ c := by
      have hBdd : Bornology.IsBounded A := hA.isBounded
      have h : dist (b k) (a k) ≤ diam A := Metric.dist_le_diam_of_mem hBdd (hb k) (ha k)
      simpa [dist_eq_norm, Real.norm_eq_abs, he] using h
    have h_rev : |e + ℓ_vec k| ≥ |ℓ_vec k| - |e| := by
      have h : |ℓ_vec k| ≤ |e + ℓ_vec k| + |e| := by
        calc |ℓ_vec k|
          = |(e + ℓ_vec k) - e| := by ring_nf
        _ ≤ |e + ℓ_vec k| + |e| := by exact abs_sub _ _
      linarith
    have h_final : |ℓ_vec k| - |e| ≥ c := by
      have hδ2c : δ = 2 * c := by simp [δ, c]
      rw [hδ2c] at hℓ_k_bound
      linarith
    have h_d_eq3 : d = e + ℓ_vec k := by
      simp [e, d, z'] <;> ring
    have h_rev' : |ℓ_vec k| - |e| ≤ |d| := by
      rw [h_d_eq3]
      exact h_rev
    exact le_trans h_final h_rev'

  have hd_ne_zero : d ≠ 0 := by
    have h : |d| ≥ c := hd_bound
    have hc_pos : 0 < c := h_diam_pos
    have h' : 0 < |d| := by linarith
    exact abs_ne_zero.mp (ne_of_gt h')

  have hℓ_sum : ∑ idx : Fin n, v idx * ℓ_vec idx = π (p j) - π (p i) := by
    have h2 : ℓ_vec = p j - p i := by simp [ℓ_vec]
    have h3 : ∑ idx : Fin n, v idx * ℓ_vec idx = ∑ idx : Fin n, v idx * ((p j - p i) idx) := by
      apply Finset.sum_congr rfl
      intro idx _
      rw [h2]
    rw [h3]
    have h4 : ∑ idx : Fin n, v idx * ((p j - p i) idx) = ∑ idx : Fin n, v idx * ((p j) idx - (p i) idx) := by
      apply Finset.sum_congr rfl
      intro idx _
      rfl
    rw [h4]
    have h5 : ∑ idx : Fin n, v idx * ((p j) idx - (p i) idx) = π (p j) - π (p i) := by
      have h6 : ∑ idx : Fin n, v idx * ((p j) idx - (p i) idx) = ∑ idx : Fin n, (v idx * (p j) idx - v idx * (p i) idx) := by
        apply Finset.sum_congr rfl; intro idx _; ring
      rw [h6, Finset.sum_sub_distrib]
      <;> rfl
    exact h5
  have h1 : ∑ idx : Fin n, v idx * (a idx - z' idx) = 0 := by
    have h2 : (∑ idx : Fin n, v idx * a idx) + π (p i) = (∑ idx : Fin n, v idx * b idx) + π (p j) := h_eq
    have h3 : ∑ idx : Fin n, v idx * (a idx - z' idx) = (∑ idx : Fin n, v idx * a idx) - (∑ idx : Fin n, v idx * z' idx) := by
      have h4 : ∑ idx : Fin n, v idx * (a idx - z' idx) = ∑ idx : Fin n, (v idx * a idx - v idx * z' idx) := by
        apply Finset.sum_congr rfl; intro idx _; ring
      rw [h4, Finset.sum_sub_distrib]
    rw [h3]
    have h4 : ∑ idx : Fin n, v idx * z' idx = ∑ idx : Fin n, v idx * (b idx + ℓ_vec idx) := by
      apply Finset.sum_congr rfl
      intro idx _
      have h5 : z' idx = b idx + ℓ_vec idx := by simp [z'] <;> ring
      rw [h5]
    rw [h4]
    have h5 : ∑ idx : Fin n, v idx * (b idx + ℓ_vec idx) = (∑ idx : Fin n, v idx * b idx) + ∑ idx : Fin n, v idx * ℓ_vec idx := by
      have h6 : ∑ idx : Fin n, v idx * (b idx + ℓ_vec idx) = ∑ idx : Fin n, (v idx * b idx + v idx * ℓ_vec idx) := by
        apply Finset.sum_congr rfl; intro idx _; ring
      rw [h6, Finset.sum_add_distrib]
    rw [h5]
    rw [hℓ_sum]
    have h7 : (∑ idx : Fin n, v idx * a idx) + π (p i) = (∑ idx : Fin n, v idx * b idx) + π (p j) := h2
    have h8 : (∑ idx : Fin n, v idx * a idx) - ((∑ idx : Fin n, v idx * b idx) + (π (p j) - π (p i))) = 0 := by
      linarith
    exact h8
  let X : ℝ := ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i)
  have h_split : ∑ i : Fin n, v i * (a i - z' i) = v k * (a k - z' k) + X :=
    sum_fin_split k (fun i => v i * (a i - z' i))
  rw [h_split] at h1
  have h6 : v k * (a k - z' k) + X = 0 := h1
  have h7 : v k * (a k - z' k) = -X := by linarith
  have h8 : a k - z' k = -d := by
    simp [d, z'] <;> ring
  have h9 : v k * d = X := by
    have h10 : v k * (a k - z' k) = v k * (-d) := by rw [h8]
    rw [h10] at h7
    have h11 : v k * (-d) = -X := h7
    have h12 : -v k * d = -X := by
      have h13 : v k * (-d) = -v k * d := by ring
      rw [h13] at h11
      exact h11
    have h14 : v k * d = X := by
      have h15 : -v k * d = -X := h12
      have h16 : (-v k * d : ℝ) = (-X : ℝ) := h15
      have h17 : v k * d = X := by
        apply_fun fun x : ℝ => -x at h16
        simpa using h16
      exact h17
    exact h14
  have h_id : v k * d = ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) := h9

  choose m hm using hℓ_coord
  have h_contain := main_containment_explicit hA hA_nonempty a b z' d ha hb k ℓ_vec
    (fun i => rfl) (by simp [d]) m hm h_diam_in_diff
  rcases h_contain with ⟨N', hN'_eq2, hN'_pos, hN'_contain, hN'_eq⟩

  have h_main_set : d • S ⊆ scaledSumsetExcept v k (iteratedDifference (productSet A 2) N') :=
    expansion_containment_step hA hA_nonempty v k a z' d N' hN'_contain hN'_eq h_id S rfl

  have h_vol_scale : volume (d • S) = ENNReal.ofReal (|d|) * volS :=
    volume_smul_set hd_ne_zero hS_meas

  have h_final : volume (scaledSumsetExcept v k (iteratedDifference (productSet A 2) N')) ≥
      ENNReal.ofReal c * volS := by
    have h9 : |d| ≥ c := hd_bound
    have h10 : ENNReal.ofReal c ≤ ENNReal.ofReal (|d|) := ENNReal.ofReal_le_ofReal h9
    have h11 : ENNReal.ofReal c * volS ≤ ENNReal.ofReal (|d|) * volS :=
      mul_le_mul_right' h10 volS
    calc
      volume (scaledSumsetExcept v k (iteratedDifference (productSet A 2) N'))
        ≥ volume (d • S) := measure_mono h_main_set
    _ = ENNReal.ofReal (|d|) * volS := h_vol_scale
    _ ≥ ENNReal.ofReal c * volS := h11

  -- Bound N' ≤ N_max
  have h_box_norm : ∀ (x : EuclideanSpace ℝ (Fin n)), x ∈ boxC (n := n) (by linarith) R →
      ‖x‖ ≤ Real.sqrt (1 + (n : ℝ) * R^2) :=
    fun x hx => boxC_norm_bound (by linarith) R x hx

  have h_lattice_bound : ∀ (idx : Fin n), |ℓ_vec idx| ≤ 2 * Real.sqrt (1 + (n : ℝ) * R^2) := by
    intro idx
    have hpi : p i ∈ V := hp_in_V i
    have hpj : p j ∈ V := hp_in_V j
    rcases hpi with ⟨xi, hxi, h_eqi⟩
    rcases hpj with ⟨xj, hxj, h_eqj⟩
    have h_norm_i : ‖p i‖ ≤ Real.sqrt (1 + (n : ℝ) * R^2) := by
      have h : p i = U xi := h_eqi.symm
      rw [h, U.norm_map xi]
      exact h_box_norm xi hxi
    have h_norm_j : ‖p j‖ ≤ Real.sqrt (1 + (n : ℝ) * R^2) := by
      have h : p j = U xj := h_eqj.symm
      rw [h, U.norm_map xj]
      exact h_box_norm xj hxj
    have h_coord_i : |(p i) idx| ≤ ‖p i‖ := euclidean_coord_abs_le_norm (p i) idx
    have h_coord_j : |(p j) idx| ≤ ‖p j‖ := euclidean_coord_abs_le_norm (p j) idx
    have h_final : |ℓ_vec idx| = |(p j) idx - (p i) idx| := by
      simp [ℓ_vec] <;> rfl
    rw [h_final]
    have h : |(p j) idx - (p i) idx| ≤ |(p j) idx| + |(p i) idx| := abs_sub _ _
    calc |(p j) idx - (p i) idx|
      ≤ |(p j) idx| + |(p i) idx| := h
    _ ≤ ‖p j‖ + ‖p i‖ := by gcongr
    _ ≤ 2 * Real.sqrt (1 + (n : ℝ) * R^2) := by linarith

  have hM_bound : ∀ (idx : Fin n), (m idx).natAbs ≤ Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c) := by
    intro idx
    have h1 : ℓ_vec idx = δ * (m idx : ℝ) := hm idx
    have h2 : |(m idx : ℝ)| ≤ Real.sqrt (1 + (n : ℝ) * R^2) / c := by
      have h3 : |ℓ_vec idx| ≤ 2 * Real.sqrt (1 + (n : ℝ) * R^2) := h_lattice_bound idx
      have h4 : |ℓ_vec idx| = |δ| * |(m idx : ℝ)| := by
        rw [h1, abs_mul]
      rw [h4] at h3
      have h5 : |δ| = δ := abs_of_pos hδ_pos
      rw [h5] at h3
      have h6 : δ * |(m idx : ℝ)| ≤ 2 * Real.sqrt (1 + (n : ℝ) * R^2) := h3
      have h7 : δ = 2 * c := by simp [δ, c]
      rw [h7] at h6
      have h8 : (2 * c) * |(m idx : ℝ)| ≤ 2 * Real.sqrt (1 + (n : ℝ) * R^2) := h6
      have h9 : |(m idx : ℝ)| ≤ Real.sqrt (1 + (n : ℝ) * R^2) / c := by
        have h_posc : 0 < c := h_diam_pos
        have h_div : (2 * c) * |(m idx : ℝ)| ≤ 2 * Real.sqrt (1 + (n : ℝ) * R^2) := h8
        have h91 : ((2 * c) * |(m idx : ℝ)|) / (2 * c) ≤
            (2 * Real.sqrt (1 + (n : ℝ) * R^2)) / (2 * c) := by
          gcongr
        have h_left : ((2 * c) * |(m idx : ℝ)|) / (2 * c) = |(m idx : ℝ)| := by
          field_simp [h_posc.ne'] <;> ring
        have h_right : (2 * Real.sqrt (1 + (n : ℝ) * R^2)) / (2 * c) =
            Real.sqrt (1 + (n : ℝ) * R^2) / c := by
          field_simp [h_posc.ne'] <;> ring
        rw [h_left, h_right] at h91
        exact h91
      exact h9
    have h10 : (m idx).natAbs ≤ Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c) := by
      have h11 : ((m idx).natAbs : ℝ) = |(m idx : ℝ)| := by
        have h_sq : ((m idx).natAbs : ℤ)^2 = (m idx)^2 := by
          have h_pos : ((m idx).natAbs : ℤ) = |m idx| := by exact Int.natCast_natAbs (m idx)
          rw [h_pos, sq_abs]
        have h_sq' : ((m idx).natAbs : ℝ)^2 = (m idx : ℝ)^2 := by
          have h_cast1 : ((m idx).natAbs : ℝ)^2 = ↑(((m idx).natAbs : ℤ)^2) := by
            simp [pow_two] <;> norm_cast
          have h_cast2 : (m idx : ℝ)^2 = ↑((m idx)^2) := by
            simp [pow_two] <;> norm_cast
          rw [h_cast1, h_cast2]
          rw [h_sq]
        have h_abs_sq : |(m idx : ℝ)|^2 = (m idx : ℝ)^2 := by
          rw [sq_abs]
        have h_nonneg1 : 0 ≤ ((m idx).natAbs : ℝ) := by positivity
        have h_nonneg2 : 0 ≤ |(m idx : ℝ)| := by positivity
        nlinarith
      have h12 : ((m idx).natAbs : ℝ) ≤ Real.sqrt (1 + (n : ℝ) * R^2) / c := by
        rw [h11] <;> exact h2
      have h13 : Real.sqrt (1 + (n : ℝ) * R^2) / c ≤ ↑(Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c)) :=
        Nat.le_ceil _
      have h14 : ((m idx).natAbs : ℝ) ≤ ↑(Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c)) :=
        le_trans h12 h13
      exact_mod_cast h14
    exact h10

  let M : ℕ := Finset.sup Finset.univ (fun i : Fin n => (m i).natAbs)
  have hM_le : M ≤ Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c) := by
    apply Finset.sup_le
    intro i _
    exact hM_bound i

  have hN'_le : N' ≤ N_max := by
    rw [hN'_eq2]
    have h1 : 2 + 4 * M ≤ 2 + 4 * Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c) := by
      gcongr
    have h2 : 2 + 4 * Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c) ≤ N_max := by
      dsimp only [N_max, δ_min]
      have h3 : Real.sqrt (1 + (n : ℝ) * R^2) / c ≤ 2 * Real.sqrt (1 + (n : ℝ) * R^2) / δ_min := by
        set a := Real.sqrt (1 + (n : ℝ) * R^2) with ha
        have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
        have h4 : δ_min ≤ 2 * c := hδ_lower
        have h7 : a * δ_min ≤ 2 * a * c := by
          have h5 : a * δ_min ≤ a * (2 * c) := mul_le_mul_of_nonneg_left h4 ha_nonneg
          have h6 : a * (2 * c) = 2 * a * c := by ring
          rw [h6] at h5
          exact h5
        have h_posc : 0 < c := h_diam_pos
        have h_posδ : 0 < δ_min := hδ_min_pos
        have h_step1 : a / c = (a * δ_min) / (c * δ_min) := by
          field_simp [h_posc.ne', h_posδ.ne'] <;> ring
        have h_step2 : (a * δ_min) / (c * δ_min) ≤ (2 * a * c) / (c * δ_min) := by
          apply div_le_div_of_nonneg_right h7
          positivity
        have h_step3 : (2 * a * c) / (c * δ_min) = 2 * a / δ_min := by
          field_simp [h_posc.ne', h_posδ.ne'] <;> ring
        calc a / c
          = (a * δ_min) / (c * δ_min) := h_step1
        _ ≤ (2 * a * c) / (c * δ_min) := h_step2
        _ = 2 * a / δ_min := h_step3
      have h5 : Nat.ceil (Real.sqrt (1 + (n : ℝ) * R^2) / c) ≤
          Nat.ceil (2 * Real.sqrt (1 + (n : ℝ) * R^2) / δ_min) := Nat.ceil_le_ceil h3
      gcongr
    exact le_trans h1 h2

  have hS_nonempty : (productSet A 2).Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    refine ⟨a * a, ?_⟩
    simp only [productSet, Set.mem_setOf_eq]
    refine ⟨fun (_ : Fin 2) => a, fun (_ : Fin 2) => ha, ?_⟩
    simp [Fin.prod_univ_succ]
    <;> ring
  have h_mono : iteratedDifference (productSet A 2) N' ⊆
      iteratedDifference (productSet A 2) N_max :=
    WeakTwoEndsSumProduct.iteratedDifference_mono hS_nonempty hN'_le

  have h_scaled_mono : scaledSumsetExcept v k
        (iteratedDifference (productSet A 2) N') ⊆
      scaledSumsetExcept v k
        (iteratedDifference (productSet A 2) N_max) := by
    intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨a, fun i => h_mono (ha i), rfl⟩

  have h_final_max : volume (scaledSumsetExcept v k
        (iteratedDifference (productSet A 2) N_max)) ≥
      volume (scaledSumsetExcept v k
        (iteratedDifference (productSet A 2) N')) :=
    measure_mono h_scaled_mono

  have h_goal : volume (scaledSumsetExcept v k
        (iteratedDifference (productSet A 2) N_max)) ≥
      ENNReal.ofReal (diam A) * volume (scaledSumset v A) := by
    have h10 : volume (scaledSumsetExcept v k
          (iteratedDifference (productSet A 2) N_max)) ≥
        ENNReal.ofReal c * volS := le_trans h_final h_final_max
    simpa [c, volS, S] using h10

  exact ⟨k, h_goal⟩

end ExpansionLemma

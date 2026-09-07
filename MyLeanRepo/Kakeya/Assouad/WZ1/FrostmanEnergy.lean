import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Frostman energy bound

For a finite δ-separated Frostman set A ⊂ ℝ², the γ-energy
`Σ_{x,y∈A} dist(x,y)^(-γ)` is bounded by `C(α,γ) * (1+C) * |A|²`, independent of δ.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

lemma nat_le_pow_two (n : ℕ) : (n : ℝ) ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc (n.succ : ℝ) = (n : ℝ) + 1 := by simp
      _ ≤ (2 : ℝ)^n + 1 := by linarith
      _ ≤ (2 : ℝ)^n + (2 : ℝ)^n := by
        have h : (1 : ℝ) ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
        linarith
      _ = (2 : ℝ)^(n + 1) := by rw [pow_succ] <;> ring

lemma frostman_real_bound {A : DiscreteSet 2} {δ C α : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hFrost : A.IsFrostman δ α (ENNReal.ofReal C))
    {x : Point2} {r : ℝ} (hδr : δ ≤ r) (hr1 : r ≤ 1) :
    ((A.filter (fun y => dist y x ≤ r)).card : ℝ) ≤ C * r^α * (A.card : ℝ) := by
  have h8 : A.ballCount x r ≤ ENNReal.ofReal C * Kakeya.realRpowENN r α * A.enncard :=
    hFrost x r hδr hr1
  have h10 : Kakeya.realRpowENN r α = ENNReal.ofReal (r^α) := by
    simp [Kakeya.realRpowENN]
  have h11 : A.enncard = (A.card : ENNReal) := by
    simp [DiscreteSet.enncard]
  rw [h10, h11] at h8
  have hA : (A.card : ENNReal) = ENNReal.ofReal (A.card : ℝ) := by
    have hA1 : (A.card : ENNReal) = ↑(A.card) := by rfl
    rw [hA1]; norm_cast
  rw [hA] at h8
  have hr_nonneg : 0 ≤ r := by linarith
  have hrα_nonneg : 0 ≤ r^α := Real.rpow_nonneg hr_nonneg α
  have h12 : ENNReal.ofReal C * ENNReal.ofReal (r^α) * ENNReal.ofReal (A.card : ℝ) =
      ENNReal.ofReal (C * r^α * (A.card : ℝ)) := by
    have h121 : ENNReal.ofReal C * ENNReal.ofReal (r^α) = ENNReal.ofReal (C * r^α) := by
      rw [←ENNReal.ofReal_mul hC]
    rw [h121]
    rw [←ENNReal.ofReal_mul (mul_nonneg hC hrα_nonneg)] <;> ring_nf
  rw [h12] at h8
  have h14 : 0 ≤ C * r^α * (A.card : ℝ) := by positivity
  have h_ne_top : ENNReal.ofReal (C * r^α * (A.card : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h15 : (A.ballCount x r).toReal ≤ (ENNReal.ofReal (C * r^α * (A.card : ℝ))).toReal :=
    ENNReal.toReal_mono h_ne_top h8
  have h16 : (A.ballCount x r).toReal = ((A.filter (fun y => dist y x ≤ r)).card : ℝ) := by
    simp [DiscreteSet.ballCount] <;> norm_cast
  have h17 : (ENNReal.ofReal (C * r^α * (A.card : ℝ))).toReal = C * r^α * (A.card : ℝ) := by
    rw [ENNReal.toReal_ofReal h14]
  rw [h16, h17] at h15
  exact h15

lemma shell_term_identity (k : ℕ) (δ α γ : ℝ) (hδ : 0 < δ) (hα : 0 < α) (hγ : 0 < γ) :
    (((2 : ℝ)^(k+1) * δ)^α) * (((2 : ℝ)^k * δ)^(-γ)) =
    (2 : ℝ)^α * δ^(α - γ) * ((2 : ℝ)^(α - γ))^k := by
  have h_two_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have h_two_nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have h1 : ((2 : ℝ)^(k+1) * δ)^α = ((2 : ℝ)^(k+1))^α * δ^α := by
    rw [Real.mul_rpow (by positivity) (by linarith)]
  have h2 : ((2 : ℝ)^k * δ)^(-γ) = ((2 : ℝ)^k)^(-γ) * δ^(-γ) := by
    rw [Real.mul_rpow (by positivity) (by linarith)]
  have h3 : ((2 : ℝ)^(k+1))^α = (2 : ℝ)^(((k+1 : ℕ) : ℝ) * α) := by
    have h31 : (2 : ℝ)^(k+1) = (2 : ℝ)^(((k+1 : ℕ) : ℝ)) := by
      exact (Real.rpow_natCast (2 : ℝ) (k+1)).symm
    rw [h31, ←Real.rpow_mul h_two_nonneg] <;> ring
  have h4 : ((2 : ℝ)^k)^(-γ) = (2 : ℝ)^(-(k : ℝ) * γ) := by
    have h41 : (2 : ℝ)^k = (2 : ℝ)^((k : ℝ)) := by
      exact (Real.rpow_natCast (2 : ℝ) k).symm
    rw [h41, ←Real.rpow_mul h_two_nonneg] <;> ring
  set a : ℝ := ((k+1 : ℕ) : ℝ) * α with ha
  set b : ℝ := -(k : ℝ) * γ with hb
  have h_exp : a + b = α + (k : ℝ) * (α - γ) := by
    simp [ha, hb] <;> ring
  have h5 : (2 : ℝ)^a * (2 : ℝ)^b = (2 : ℝ)^(a + b) := by
    exact (Real.rpow_add h_two_pos a b).symm
  have h6 : (2 : ℝ)^(a + b) = (2 : ℝ)^(α + (k : ℝ) * (α - γ)) := by rw [h_exp]
  have h7 : (2 : ℝ)^(α + (k : ℝ) * (α - γ)) =
      (2 : ℝ)^α * (2 : ℝ)^((k : ℝ) * (α - γ)) := by
    exact Real.rpow_add h_two_pos α ((k : ℝ) * (α - γ))
  have h8 : (2 : ℝ)^((k : ℝ) * (α - γ)) = ((2 : ℝ)^(α - γ))^k := by
    have h_comm : (k : ℝ) * (α - γ) = (α - γ) * (k : ℝ) := by ring
    rw [h_comm]
    exact Real.rpow_mul_natCast h_two_nonneg (α - γ) k
  have h9 : δ^α * δ^(-γ) = δ^(α - γ) := by
    have h91 : δ^α * δ^(-γ) = δ^(α + (-γ)) := by
      exact (Real.rpow_add hδ α (-γ)).symm
    rw [h91]
    have h92 : α + (-γ) = α - γ := by ring
    rw [h92]
  have h10 : (2 : ℝ)^a * (2 : ℝ)^b * (δ^α * δ^(-γ)) =
      (2 : ℝ)^α * δ^(α - γ) * ((2 : ℝ)^(α - γ))^k := by
    calc
      (2 : ℝ)^a * (2 : ℝ)^b * (δ^α * δ^(-γ))
        = (2 : ℝ)^(a + b) * (δ^α * δ^(-γ)) := by rw [h5]
      _ = (2 : ℝ)^(a + b) * δ^(α - γ) := by rw [h9]
      _ = (2 : ℝ)^(α + (k : ℝ) * (α - γ)) * δ^(α - γ) := by rw [h6]
      _ = ((2 : ℝ)^α * (2 : ℝ)^((k : ℝ) * (α - γ))) * δ^(α - γ) := by rw [h7]
      _ = (2 : ℝ)^α * δ^(α - γ) * ((2 : ℝ)^(α - γ))^k := by rw [h8] <;> ring
  calc
    (((2 : ℝ)^(k+1) * δ)^α) * (((2 : ℝ)^k * δ)^(-γ))
      = ((2 : ℝ)^(k+1))^α * δ^α * (((2 : ℝ)^k)^(-γ) * δ^(-γ)) := by rw [h1, h2] <;> ring
    _ = (2 : ℝ)^a * δ^α * ((2 : ℝ)^b * δ^(-γ)) := by rw [h3, h4] <;> ring
    _ = (2 : ℝ)^a * (2 : ℝ)^b * (δ^α * δ^(-γ)) := by ring
    _ = (2 : ℝ)^α * δ^(α - γ) * ((2 : ℝ)^(α - γ))^k := h10

lemma at_most_three_powers (δ : ℝ) (hδ : 0 < δ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, (1 : ℝ) / (2 * δ) < (2 : ℝ)^k ∧ (2 : ℝ)^k ≤ 2 / δ) :
    S.card ≤ 3 := by
  by_contra h
  have h4 : 4 ≤ S.card := by omega
  let e : Fin S.card ≃o {x // x ∈ S} := Finset.orderIsoOfFin S rfl
  have h5 : 3 < S.card := by omega
  let i0 : Fin S.card := ⟨0, by omega⟩
  let i1 : Fin S.card := ⟨1, by omega⟩
  let i2 : Fin S.card := ⟨2, by omega⟩
  let i3 : Fin S.card := ⟨3, h5⟩
  let k1 : ℕ := (e i0).val
  let k2 : ℕ := (e i1).val
  let k3 : ℕ := (e i2).val
  let k4 : ℕ := (e i3).val
  have hk1 : k1 ∈ S := (e i0).property
  have hk2 : k2 ∈ S := (e i1).property
  have hk3 : k3 ∈ S := (e i2).property
  have hk4 : k4 ∈ S := (e i3).property
  have h12 : k1 < k2 := e.strictMono (by simp [i0, i1] <;> omega)
  have h23 : k2 < k3 := e.strictMono (by simp [i1, i2] <;> omega)
  have h34 : k3 < k4 := e.strictMono (by simp [i2, i3] <;> omega)
  have h_gt1 : (2 : ℝ)^k1 > 1 / (2 * δ) := (hS k1 hk1).1
  have h_le4 : (2 : ℝ)^k4 ≤ 2 / δ := (hS k4 hk4).2
  have h_k4_ge : k1 + 3 ≤ k4 := by
    have h41 : k1 + 1 ≤ k2 := Nat.succ_le_iff.mpr h12
    have h42 : k2 + 1 ≤ k3 := Nat.succ_le_iff.mpr h23
    have h43 : k3 + 1 ≤ k4 := Nat.succ_le_iff.mpr h34
    linarith
  have h10 : (2 : ℝ)^k4 ≥ (2 : ℝ)^(k1 + 3) := by
    exact pow_le_pow_right₀ (by norm_num) h_k4_ge
  have h11 : (2 : ℝ)^(k1 + 3) = 8 * (2 : ℝ)^k1 := by
    simp [pow_add] <;> ring
  have h12' : (2 : ℝ)^k4 > 4 / δ := by
    calc (2 : ℝ)^k4 ≥ (2 : ℝ)^(k1 + 3) := h10
      _ = 8 * (2 : ℝ)^k1 := h11
      _ > 8 * (1 / (2 * δ)) := by gcongr
      _ = 4 / δ := by ring
  have h13 : (4 : ℝ) / δ > 2 / δ := by
    apply div_lt_div_of_pos_right; norm_num; exact hδ
  linarith

/--
Frostman energy bound.
-/
lemma frostman_energy_bound
    {A : DiscreteSet 2} {δ C α γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hα : 0 < α) (hγ : 0 < γ) (hγ_lt_alpha : γ < α)
    (hC : 0 ≤ C)
    (hFrost : A.IsFrostman δ α (ENNReal.ofReal C))
    (hsep : A.IsDeltaSeparated δ)
    (hball : A.IsInUnitBall) :
    ∑ x ∈ A, ∑ y ∈ A, (dist x y)^(-γ) ≤
    ((2 : ℝ)^α / ((2 : ℝ)^(α-γ) - 1) + 3 * (2 : ℝ)^γ) * (1 + C) * (A.card : ℝ)^2 := by
  classical
  set r : ℝ := (2 : ℝ)^(α-γ) with hr_def
  have h1_pos : 0 < α - γ := by linarith
  have hr_gt_one : (1 : ℝ) < r := by
    rw [hr_def]
    exact Real.one_lt_rpow (by norm_num) h1_pos
  have hr_sub_pos : 0 < r - 1 := by linarith
  set K_const : ℝ := (2 : ℝ)^α / (r - 1) + 3 * (2 : ℝ)^γ with hK_def

  -- Get K with 2^K * δ ≥ 2
  have hK_exists : ∃ (K : ℕ), (2 : ℝ)^K * δ ≥ 2 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / δ)
    have h2 : (2 / δ : ℝ) < (K : ℝ) := hK
    have h3 : (K : ℝ) ≤ (2 : ℝ)^K := nat_le_pow_two K
    have h4 : (2 / δ : ℝ) < (2 : ℝ)^K := by linarith
    have h5 : (2 : ℝ)^K * δ > 2 := by
      calc (2 : ℝ)^K * δ > (2 / δ) * δ := by gcongr
        _ = 2 := by field_simp [hδ.ne'] <;> ring
    exact ⟨K, by linarith⟩
  rcases hK_exists with ⟨K, hK_ge⟩

  let shell (x : Point2) (k : ℕ) : Finset Point2 :=
    A.filter (fun y => (2 : ℝ)^k * δ ≤ dist x y ∧ dist x y < (2 : ℝ)^(k+1) * δ)

  -- Shell empty when 2^k * δ > 2
  have h_empty : ∀ (k : ℕ), (2 : ℝ)^k * δ > 2 → ∀ (x : Point2), x ∈ A → shell x k = ∅ := by
    intro k hk x hx
    have h : ∀ y, y ∉ shell x k := by
      intro y hy
      have h_yA : y ∈ A := (Finset.mem_filter.mp hy).1
      have h1 : (2 : ℝ)^k * δ ≤ dist x y := (Finset.mem_filter.mp hy).2.1
      have h2 : dist x 0 ≤ 1 := hball x hx
      have h3 : dist y 0 ≤ 1 := hball y h_yA
      have h4 : dist x y ≤ 2 := by
        calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
          _ = dist x 0 + dist y 0 := by rw [dist_comm y 0]
          _ ≤ 2 := by linarith
      linarith
    exact Finset.eq_empty_of_forall_notMem h

  -- Every y ≠ x in A is in some shell k ≤ K
  have h_cover : ∀ (x : Point2), x ∈ A →
      (A.erase x) ⊆ Finset.biUnion (Finset.range (K + 1)) (shell x) := by
    intro x hx y hy
    have h_yA : y ∈ A := (Finset.mem_erase.mp hy).2
    have h_yne : y ≠ x := (Finset.mem_erase.mp hy).1
    have h_dsep : δ ≤ dist x y := hsep hx h_yA (Ne.symm h_yne)
    have h_dle2 : dist x y ≤ 2 := by
      have h3 : dist x 0 ≤ 1 := hball x hx
      have h4 : dist y 0 ≤ 1 := hball y h_yA
      calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
        _ = dist x 0 + dist y 0 := by rw [dist_comm y 0]
        _ ≤ 2 := by linarith
    have h_exists_k : ∃ (k : ℕ), dist x y < (2 : ℝ)^(k+1) * δ := by
      refine ⟨K, ?_⟩
      have h7 : (2 : ℝ)^(K+1) * δ > 2 := by
        have h8 : (2 : ℝ)^(K+1) > (2 : ℝ)^K := by gcongr <;> norm_num
        nlinarith
      linarith
    let k := Nat.find h_exists_k
    have h_k_spec : dist x y < (2 : ℝ)^(k+1) * δ := Nat.find_spec h_exists_k
    have h_k_ge : (2 : ℝ)^k * δ ≤ dist x y := by
      by_cases h_k0 : k = 0
      · rw [h_k0]; simpa using h_dsep
      · have h_pos : 0 < k := Nat.pos_of_ne_zero h_k0
        have h_prev : ¬(dist x y < (2 : ℝ)^((k - 1) + 1) * δ) :=
          Nat.find_min h_exists_k (by omega)
        have h9 : (k - 1) + 1 = k := by omega
        rw [h9] at h_prev
        by_contra h
        have h' : dist x y < (2 : ℝ)^k * δ := by linarith
        exact h_prev h'
    have h_k_le_K : k ≤ K := by
      by_contra h
      have h12 : k > K := by omega
      have h13 : k ≥ K + 1 := Nat.succ_le_iff.mpr h12
      have h14 : (2 : ℝ)^k * δ ≥ (2 : ℝ)^(K+1) * δ := by gcongr <;> linarith
      have h15 : (2 : ℝ)^(K+1) * δ > 2 := by
        have h16 : (2 : ℝ)^(K+1) > (2 : ℝ)^K := by gcongr <;> norm_num
        nlinarith
      have h17 : (2 : ℝ)^k * δ > 2 := by linarith
      linarith [h_k_ge, h_dle2]
    have h_in_shell : y ∈ shell x k := by
      apply Finset.mem_filter.mpr
      exact ⟨h_yA, ⟨h_k_ge, h_k_spec⟩⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), h_in_shell⟩

  -- Shell Frostman bound
  have h_shell_frost : ∀ (x : Point2), x ∈ A → ∀ (k : ℕ),
      (2 : ℝ)^(k+1) * δ ≤ 1 →
      ((shell x k).card : ℝ) ≤ C * ((2 : ℝ)^(k+1) * δ)^α * (A.card : ℝ) := by
    intro x hx k h_le1
    let B := A.filter (fun y => dist y x ≤ (2 : ℝ)^(k+1) * δ)
    have h1 : shell x k ⊆ B := by
      intro y hy
      have h2 : y ∈ A := (Finset.mem_filter.mp hy).1
      have h3 : dist x y < (2 : ℝ)^(k+1) * δ := (Finset.mem_filter.mp hy).2.2
      apply Finset.mem_filter.mpr
      exact ⟨h2, by linarith [dist_comm x y]⟩
    have h4 : ((shell x k).card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h1
    have h6 : δ ≤ (2 : ℝ)^(k+1) * δ := by
      have h7 : (1 : ℝ) ≤ (2 : ℝ)^(k+1) := one_le_pow₀ (by norm_num)
      nlinarith
    have h9 : (B.card : ℝ) ≤ C * ((2 : ℝ)^(k+1) * δ)^α * (A.card : ℝ) :=
      frostman_real_bound hδ hC hFrost h6 h_le1
    exact le_trans h4 h9

  -- Per-point energy bound
  have h_main : ∀ (x : Point2), x ∈ A →
      ∑ y ∈ A, (dist x y)^(-γ) ≤ K_const * (1 + C) * (A.card : ℝ) := by
    intro x hx
    have h_diag : (dist x x)^(-γ) = 0 := by
      simp [Real.zero_rpow (show (-γ) ≠ 0 by linarith)]
    have h_notin : x ∉ A.erase x := by simp
    have h_sum_erase : ∑ y ∈ A, (dist x y)^(-γ) = ∑ y ∈ A.erase x, (dist x y)^(-γ) := by
      have h4 : A = insert x (A.erase x) := by rw [Finset.insert_erase hx]
      have h5 : ∑ y ∈ A, (dist x y)^(-γ) = ∑ y ∈ insert x (A.erase x), (dist x y)^(-γ) := by
        congr
        <;> exact h4
      rw [h5]
      have h6 : ∑ y ∈ insert x (A.erase x), (dist x y)^(-γ) =
          (dist x x)^(-γ) + ∑ y ∈ A.erase x, (dist x y)^(-γ) :=
        Finset.sum_insert h_notin
      rw [h6]
      rw [h_diag]
      <;> simp
    rw [h_sum_erase]

    let K1 : Finset ℕ := (Finset.range (K + 1)).filter (fun k => (2 : ℝ)^(k+1) * δ ≤ 1)
    let K2 : Finset ℕ := (Finset.range (K + 1)).filter (fun k => (2 : ℝ)^(k+1) * δ > 1)

    have h_disj : Disjoint K1 K2 := by
      simp [K1, K2, Finset.disjoint_left] <;> intro k _ h1 h2; linarith
    have h_union : K1 ∪ K2 = Finset.range (K + 1) := by
      ext k
      simp only [K1, K2, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (h | h) <;> tauto
      · intro h
        by_cases h' : (2 : ℝ)^(k+1) * δ ≤ 1
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, by linarith⟩

    have h_bound_shell : ∀ k ∈ Finset.range (K + 1),
        ∑ y ∈ shell x k, (dist x y)^(-γ) ≤
        (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) := by
      intro k _
      have h : ∀ y ∈ shell x k, (dist x y)^(-γ) ≤ ((2 : ℝ)^k * δ)^(-γ) := by
        intro y hy
        have h2 : (2 : ℝ)^k * δ ≤ dist x y := (Finset.mem_filter.mp hy).2.1
        have h3 : 0 < (2 : ℝ)^k * δ := by positivity
        have h4 : 0 < dist x y := by
          have h5 : y ∈ A := (Finset.mem_filter.mp hy).1
          have h6 : y ≠ x := by
            intro h7; rw [h7] at h2; simp at h2 <;> linarith
          have h6' : x ≠ y := Ne.symm h6
          exact dist_pos.mpr h6'
        have h5 : (dist x y)^(-γ) ≤ ((2 : ℝ)^k * δ)^(-γ) := by
          have h7 : ((2 : ℝ)^k * δ)^γ ≤ (dist x y)^γ := by
            apply Real.rpow_le_rpow <;> linarith
          have h_pos_a : 0 < ((2 : ℝ)^k * δ)^γ := by positivity
          have h8 : ((dist x y)^γ)⁻¹ ≤ (((2 : ℝ)^k * δ)^γ)⁻¹ := by
            gcongr
          have h9 : (dist x y)^(-γ) = ((dist x y)^γ)⁻¹ := by
            rw [Real.rpow_neg] <;> positivity
          have h10 : ((2 : ℝ)^k * δ)^(-γ) = (((2 : ℝ)^k * δ)^γ)⁻¹ := by
            rw [Real.rpow_neg] <;> positivity
          rw [h9, h10]; exact h8
        exact h5
      calc
        ∑ y ∈ shell x k, (dist x y)^(-γ)
          ≤ ∑ y ∈ shell x k, ((2 : ℝ)^k * δ)^(-γ) := Finset.sum_le_sum h
        _ = (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) := by
          rw [Finset.sum_const] <;> ring

    have h_nonneg_energy : ∀ (y : Point2), 0 ≤ (dist x y)^(-γ) := by
      intro y; exact Real.rpow_nonneg (by positivity) _

    have h_disj_shells : ∀ k1 ∈ Finset.range (K + 1), ∀ k2 ∈ Finset.range (K + 1),
        k1 ≠ k2 → Disjoint (shell x k1) (shell x k2) := by
      intro k1 _ k2 _ hne
      simp only [shell, Finset.disjoint_left, Finset.mem_filter]
      intro y hy1 hy2
      have h1 : (2 : ℝ)^k1 * δ ≤ dist x y := hy1.2.1
      have h2 : dist x y < (2 : ℝ)^(k1+1) * δ := hy1.2.2
      have h3 : (2 : ℝ)^k2 * δ ≤ dist x y := hy2.2.1
      have h4 : dist x y < (2 : ℝ)^(k2+1) * δ := hy2.2.2
      by_cases h : k1 < k2
      · have h5 : k1 + 1 ≤ k2 := by omega
        have h6 : (2 : ℝ)^(k1+1) ≤ (2 : ℝ)^k2 := pow_le_pow_right₀ (by norm_num) h5
        have h7 : (2 : ℝ)^(k1+1) * δ ≤ (2 : ℝ)^k2 * δ := by gcongr
        linarith
      · have h5 : k2 < k1 := by omega
        have h5' : k2 + 1 ≤ k1 := by omega
        have h6 : (2 : ℝ)^(k2+1) ≤ (2 : ℝ)^k1 := pow_le_pow_right₀ (by norm_num) h5'
        have h7 : (2 : ℝ)^(k2+1) * δ ≤ (2 : ℝ)^k1 * δ := by gcongr
        linarith

    have h_biUnion_sum : ∑ k ∈ Finset.range (K + 1), ∑ y ∈ shell x k, (dist x y)^(-γ) =
        ∑ y ∈ Finset.biUnion (Finset.range (K + 1)) (shell x), (dist x y)^(-γ) := by
      rw [Finset.sum_biUnion h_disj_shells]

    have h_bound1 : ∑ y ∈ A.erase x, (dist x y)^(-γ) ≤
        ∑ k ∈ Finset.range (K + 1), (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) := by
      calc
        ∑ y ∈ A.erase x, (dist x y)^(-γ)
          ≤ ∑ y ∈ Finset.biUnion (Finset.range (K + 1)) (shell x), (dist x y)^(-γ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (h_cover x hx) (fun y _ _ => h_nonneg_energy y)
        _ = ∑ k ∈ Finset.range (K + 1), ∑ y ∈ shell x k, (dist x y)^(-γ) := h_biUnion_sum.symm
        _ ≤ ∑ k ∈ Finset.range (K + 1), (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) := by
            apply Finset.sum_le_sum
            intro k hk; exact h_bound_shell k hk

    have h_sum_split : ∑ k ∈ Finset.range (K + 1), (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) =
        ∑ k ∈ K1, (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) +
        ∑ k ∈ K2, (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) := by
      rw [←Finset.sum_union h_disj, h_union]

    rw [h_sum_split] at h_bound1

    -- Bound K1 sum
    have h_K1 : ∑ k ∈ K1, (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) ≤
        C * (A.card : ℝ) * (2 : ℝ)^α / (r - 1) := by
      by_cases hK1_empty : K1 = ∅
      · rw [hK1_empty]; simp; positivity
      · let k_max := K1.max' (Finset.nonempty_iff_ne_empty.mpr hK1_empty)
        have h_kmax_in : k_max ∈ K1 := Finset.max'_mem K1 _
        have h_kmax_le1 : (2 : ℝ)^(k_max + 1) * δ ≤ 1 :=
          (Finset.mem_filter.mp h_kmax_in).2
        have hK1_sub : K1 ⊆ Finset.range (k_max + 1) := by
          intro k hk
          have h_k_le : k ≤ k_max := Finset.le_max' K1 k hk
          exact Finset.mem_range.mpr (by omega)
        have h_geom : ∑ k ∈ K1, r^k ≤ ∑ k ∈ Finset.range (k_max + 1), r^k :=
          Finset.sum_le_sum_of_subset_of_nonneg hK1_sub (fun _ _ _ => by positivity)
        have h_geom2 : ∑ k ∈ Finset.range (k_max + 1), r^k = (r^(k_max + 1) - 1) / (r - 1) := by
          have h1 : r - 1 ≠ 0 := by linarith
          induction k_max with
          | zero => simp [h1] <;> field_simp [h1] <;> ring
          | succ n ih =>
            rw [Finset.sum_range_succ, ih]
            field_simp [h1] <;> ring
        have h_rpow_bound : r^(k_max + 1) ≤ (1 / δ)^(α - γ) := by
          rw [hr_def]
          have h21 : ((2 : ℝ)^(α - γ))^(k_max + 1) = ((2 : ℝ)^(α - γ))^(((k_max + 1 : ℕ) : ℝ)) := by
            exact (Real.rpow_natCast ((2 : ℝ)^(α - γ)) (k_max + 1)).symm
          rw [h21]
          have h2 : ((2 : ℝ)^(α - γ))^(((k_max + 1 : ℕ) : ℝ)) =
              (2 : ℝ)^(((k_max + 1 : ℕ) : ℝ) * (α - γ)) := by
            rw [←Real.rpow_mul (by positivity)] <;> ring
          rw [h2]
          have h3 : (2 : ℝ)^(k_max + 1) ≤ 1 / δ := by
            have h4 : (2 : ℝ)^(k_max + 1) * δ ≤ 1 := h_kmax_le1
            calc (2 : ℝ)^(k_max + 1)
              = ((2 : ℝ)^(k_max + 1) * δ) / δ := by field_simp [hδ.ne'] <;> ring
            _ ≤ 1 / δ := by gcongr
          have h7 : (2 : ℝ)^(((k_max + 1 : ℕ) : ℝ) * (α - γ)) ≤ (1 / δ)^(α - γ) := by
            have h_step1 : (2 : ℝ)^(((k_max + 1 : ℕ) : ℝ) * (α - γ)) =
                ((2 : ℝ)^((k_max + 1 : ℕ) : ℝ))^(α - γ) := by
              rw [Real.rpow_mul (by positivity)]
            rw [h_step1]
            have h_step2 : ((2 : ℝ)^((k_max + 1 : ℕ) : ℝ)) = (2 : ℝ)^(k_max + 1) := by
              exact Real.rpow_natCast (2 : ℝ) (k_max + 1)
            rw [h_step2]
            exact Real.rpow_le_rpow (by positivity) h3 (by linarith)
          exact h7
        have h_sum_bound : ∑ k ∈ K1, r^k ≤ 1 / (r - 1) * (1 / δ)^(α - γ) := by
          have h_step1 : ∑ k ∈ K1, r^k ≤ (r^(k_max + 1) - 1) / (r - 1) := by
            calc
              ∑ k ∈ K1, r^k ≤ ∑ k ∈ Finset.range (k_max + 1), r^k := h_geom
              _ = (r^(k_max + 1) - 1) / (r - 1) := h_geom2
          calc
            ∑ k ∈ K1, r^k ≤ (r^(k_max + 1) - 1) / (r - 1) := h_step1
            _ ≤ r^(k_max + 1) / (r - 1) := by
              have h_num : r^(k_max + 1) - 1 ≤ r^(k_max + 1) := by
                have h_pos : 0 ≤ r^(k_max + 1) := by positivity
                linarith
              have h_denom : 0 ≤ r - 1 := by linarith
              exact div_le_div_of_nonneg_right h_num h_denom
            _ ≤ (1 / δ)^(α - γ) / (r - 1) := by
              apply div_le_div_of_nonneg_right; exact h_rpow_bound; linarith
            _ = 1 / (r - 1) * (1 / δ)^(α - γ) := by ring
        have h_main_bound : ∑ k ∈ K1, (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) ≤
            ∑ k ∈ K1, (C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * r^k) := by
          apply Finset.sum_le_sum
          intro k hk
          have h_le1 : (2 : ℝ)^(k+1) * δ ≤ 1 := (Finset.mem_filter.mp hk).2
          have h_shell : ((shell x k).card : ℝ) ≤ C * ((2 : ℝ)^(k+1) * δ)^α * (A.card : ℝ) :=
            h_shell_frost x hx k h_le1
          have h_pos : 0 ≤ ((2 : ℝ)^k * δ)^(-γ) := by positivity
          calc
            ((shell x k).card : ℝ) * ((2 : ℝ)^k * δ)^(-γ)
              ≤ (C * ((2 : ℝ)^(k+1) * δ)^α * (A.card : ℝ)) * ((2 : ℝ)^k * δ)^(-γ) :=
                mul_le_mul_of_nonneg_right h_shell h_pos
            _ = C * (A.card : ℝ) * (((2 : ℝ)^(k+1) * δ)^α * ((2 : ℝ)^k * δ)^(-γ)) := by ring
            _ = C * (A.card : ℝ) * ((2 : ℝ)^α * δ^(α - γ) * r^k) := by
              rw [shell_term_identity k δ α γ hδ hα hγ] <;> ring
            _ = C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * r^k := by ring
        have h_factor : ∑ k ∈ K1, (C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * r^k) =
            C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * ∑ k ∈ K1, r^k := by
          rw [Finset.mul_sum] <;> ring
        calc
          ∑ k ∈ K1, (shell x k).card * ((2 : ℝ)^k * δ)^(-γ)
            ≤ ∑ k ∈ K1, (C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * r^k) := h_main_bound
          _ = C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * ∑ k ∈ K1, r^k := h_factor
          _ ≤ C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * (1 / (r - 1) * (1 / δ)^(α - γ)) := by
              gcongr
          _ = C * (A.card : ℝ) * (2 : ℝ)^α / (r - 1) := by
              have h7 : δ^(α - γ) * (1 / δ)^(α - γ) = 1 := by
                have hδ_nonneg : 0 ≤ δ := by linarith
                have h_inv_nonneg : 0 ≤ (1 / δ) := by positivity
                have h8 : δ^(α - γ) * (1 / δ)^(α - γ) = (δ * (1 / δ))^(α - γ) := by
                  rw [←Real.mul_rpow hδ_nonneg h_inv_nonneg]
                rw [h8]
                have h9 : δ * (1 / δ) = 1 := by field_simp [hδ.ne'] <;> ring
                rw [h9]; simp
              have h10 : C * (A.card : ℝ) * (2 : ℝ)^α * δ^(α - γ) * (1 / (r - 1) * (1 / δ)^(α - γ)) =
                  C * (A.card : ℝ) * (2 : ℝ)^α * (δ^(α - γ) * (1 / δ)^(α - γ)) * (1 / (r - 1)) := by ring
              rw [h10, h7] <;> ring

    -- Bound K2 sum
    let K2' : Finset ℕ := K2.filter (fun k => (2 : ℝ)^k * δ ≤ 2)
    have h_K2'_def : ∀ k ∈ K2, (2 : ℝ)^k * δ > 2 → shell x k = ∅ := by
      intro k hk h
      exact h_empty k h x hx
    have h_K2_sum : ∑ k ∈ K2, (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) =
        ∑ k ∈ K2', (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) := by
      have h : ∀ k ∈ K2, k ∉ K2' → (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) = 0 := by
        intro k hk hnk
        have h9 : ¬((2 : ℝ)^k * δ ≤ 2) := by
          by_contra h10
          have h11 : k ∈ K2' := by
            rw [Finset.mem_filter]
            exact ⟨hk, h10⟩
          exact hnk h11
        have h10 : (2 : ℝ)^k * δ > 2 := by linarith
        have h11 : shell x k = ∅ := h_K2'_def k hk h10
        rw [h11] <;> simp
      rw [Finset.sum_subset (show K2' ⊆ K2 from Finset.filter_subset _ _) h]
    have h_K2'_cond : ∀ k ∈ K2', (1 : ℝ) / (2 * δ) < (2 : ℝ)^k ∧ (2 : ℝ)^k ≤ 2 / δ := by
      intro k hk
      have h_inK2 : k ∈ K2 := (Finset.mem_filter.mp hk).1
      have h_gt1 : (2 : ℝ)^(k+1) * δ > 1 := (Finset.mem_filter.mp h_inK2).2
      have h_le2 : (2 : ℝ)^k * δ ≤ 2 := (Finset.mem_filter.mp hk).2
      constructor
      · have h_eq : (2 : ℝ)^k = ((2 : ℝ)^(k+1) * δ) / (2 * δ) := by
          rw [pow_succ]; field_simp [hδ.ne'] <;> ring
        rw [h_eq]; gcongr
      · have h_eq2 : (2 : ℝ)^k = ((2 : ℝ)^k * δ) / δ := by
          field_simp [hδ.ne'] <;> ring
        rw [h_eq2]; gcongr
    have h_K2'_card : K2'.card ≤ 3 := at_most_three_powers δ hδ K2' h_K2'_cond
    have h_K2_bound : ∑ k ∈ K2', (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) ≤
        3 * (A.card : ℝ) * (2 : ℝ)^γ := by
      have h1 : ∀ k ∈ K2', (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) ≤ (A.card : ℝ) * (2 : ℝ)^γ := by
        intro k hk
        have h_card : (shell x k).card ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)
        have h_gt : (2 : ℝ)^k * δ > 1 / 2 := by
          have h2 : (2 : ℝ)^(k+1) * δ > 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
          have h_eq : (2 : ℝ)^k * δ = ((2 : ℝ)^(k+1) * δ) / 2 := by
            rw [pow_succ]; field_simp [hδ.ne'] <;> ring
          rw [h_eq]; gcongr
        have h3 : ((2 : ℝ)^k * δ)^(-γ) ≤ (2 : ℝ)^γ := by
          have h4 : 0 < (2 : ℝ)^k * δ := by positivity
          have h51 : (1 / 2 : ℝ)^γ ≤ ((2 : ℝ)^k * δ)^γ := by
            apply Real.rpow_le_rpow <;> linarith
          have h52 : (((2 : ℝ)^k * δ)^γ)⁻¹ ≤ ((1 / 2 : ℝ)^γ)⁻¹ := by gcongr
          have h53 : ((2 : ℝ)^k * δ)^(-γ) = (((2 : ℝ)^k * δ)^γ)⁻¹ := Real.rpow_neg (by positivity) γ
          have h55 : ((1 / 2 : ℝ)^γ)⁻¹ = (2 : ℝ)^γ := by
            have h7 : (1 / 2 : ℝ)^γ * (2 : ℝ)^γ = 1 := by
              rw [←Real.mul_rpow] <;> norm_num
            exact inv_eq_of_mul_eq_one_right h7
          rw [h53]
          calc (((2 : ℝ)^k * δ)^γ)⁻¹
            ≤ ((1 / 2 : ℝ)^γ)⁻¹ := h52
          _ = (2 : ℝ)^γ := h55
        calc
          (shell x k).card * ((2 : ℝ)^k * δ)^(-γ)
            ≤ (A.card : ℝ) * ((2 : ℝ)^k * δ)^(-γ) := by gcongr
          _ ≤ (A.card : ℝ) * (2 : ℝ)^γ := by gcongr
      calc
        ∑ k ∈ K2', (shell x k).card * ((2 : ℝ)^k * δ)^(-γ)
          ≤ ∑ k ∈ K2', (A.card : ℝ) * (2 : ℝ)^γ := Finset.sum_le_sum h1
        _ = K2'.card * (A.card : ℝ) * (2 : ℝ)^γ := by
          rw [Finset.sum_const] <;> ring
        _ ≤ 3 * (A.card : ℝ) * (2 : ℝ)^γ := by
          have h_le : (K2'.card : ℝ) ≤ 3 := by exact_mod_cast h_K2'_card
          have h_nonneg : 0 ≤ (A.card : ℝ) * (2 : ℝ)^γ := by positivity
          have h : (K2'.card : ℝ) * ((A.card : ℝ) * (2 : ℝ)^γ) ≤ 3 * ((A.card : ℝ) * (2 : ℝ)^γ) :=
            mul_le_mul_of_nonneg_right h_le h_nonneg
          have h_eq : K2'.card * (A.card : ℝ) * (2 : ℝ)^γ = (K2'.card : ℝ) * ((A.card : ℝ) * (2 : ℝ)^γ) := by ring
          rw [h_eq]; linarith

    rw [h_K2_sum] at h_bound1
    have h_final : ∑ k ∈ K1, (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) +
        ∑ k ∈ K2', (shell x k).card * ((2 : ℝ)^k * δ)^(-γ) ≤
        K_const * (1 + C) * (A.card : ℝ) := by
      have h_pos1 : 0 ≤ (2 : ℝ)^α / (r - 1) := by positivity
      have h_pos2 : 0 ≤ C * (2 : ℝ)^γ := by positivity
      calc
        _ ≤ C * (A.card : ℝ) * (2 : ℝ)^α / (r - 1) + 3 * (A.card : ℝ) * (2 : ℝ)^γ := by gcongr
        _ = (C * (2 : ℝ)^α / (r - 1) + 3 * (2 : ℝ)^γ) * (A.card : ℝ) := by ring
        _ ≤ K_const * (1 + C) * (A.card : ℝ) := by
          rw [hK_def]
          have h9 : (C * (2 : ℝ)^α / (r - 1) + 3 * (2 : ℝ)^γ) ≤
              ((2 : ℝ)^α / (r - 1) + 3 * (2 : ℝ)^γ) * (1 + C) := by
            have h10 : ((2 : ℝ)^α / (r - 1) + 3 * (2 : ℝ)^γ) * (1 + C) =
                (2 : ℝ)^α / (r - 1) + 3 * (2 : ℝ)^γ + C * (2 : ℝ)^α / (r - 1) + 3 * C * (2 : ℝ)^γ := by ring
            rw [h10]; linarith [h_pos1, h_pos2]
          have h_nonneg : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg A.card
          exact mul_le_mul_of_nonneg_right h9 h_nonneg
    exact le_trans h_bound1 h_final

  -- Sum over all x
  calc
    ∑ x ∈ A, ∑ y ∈ A, (dist x y)^(-γ)
      ≤ ∑ x ∈ A, (K_const * (1 + C) * (A.card : ℝ)) :=
        Finset.sum_le_sum (fun x hx => h_main x hx)
    _ = K_const * (1 + C) * (A.card : ℝ)^2 := by
      have h2 : ∑ x ∈ A, (K_const * (1 + C) * (A.card : ℝ)) =
          (K_const * (1 + C)) * ∑ x ∈ A, (A.card : ℝ) := by
        rw [←Finset.mul_sum] <;> rfl
      rw [h2]
      have h3 : ∑ x ∈ A, (A.card : ℝ) = (A.card : ℝ) * (A.card : ℝ) := by
        rw [Finset.sum_const] <;> ring
      rw [h3] <;> ring

end Kakeya.Assouad

module

public import MyLeanRepo.robust_kaufman_projection.Packing
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Riesz energy bound for finite separated sets in the Euclidean plane

Provides:
- `planeKernel` and `planeEnergy` definitions
- `finite_set_energy_bound`: bounded s-Riesz energy for a finite δ-separated set
  with ball-growth, for s < t

Whiteprint node: plane_energy
Dependencies: packing
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Metric Set Finset Classical

/-! ### Riesz energy definitions -/

/-- The plane Riesz kernel: `‖x - y‖^(-s)` for `x ≠ y`, 0 otherwise. -/
noncomputable def planeKernel (s : ℝ) (x y : EuclideanPlane) : ENNReal :=
  if x = y then 0 else ENNReal.ofReal (‖x - y‖ ^ (-s))

/-- The s-Riesz energy of a measure on the Euclidean plane. -/
noncomputable def planeEnergy (μ : Measure EuclideanPlane) (s : ℝ) : ENNReal :=
  ∫⁻ x, ∫⁻ y, planeKernel s x y ∂μ ∂μ

/-! ### Helper lemmas -/

lemma ennreal_ofReal_rpow {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    (ENNReal.ofReal d)^s = ENNReal.ofReal (d ^ s) := by
  have h_nonneg : 0 ≤ d := by linarith
  have h_ne_top : (ENNReal.ofReal d)^s ≠ ⊤ := by
    simp [ENNReal.rpow_eq_top_iff, hs, h_nonneg]
  have h2 : ((ENNReal.ofReal d)^s).toReal = (ENNReal.ofReal d).toReal ^ s := by exact Eq.symm (ENNReal.toReal_rpow (ENNReal.ofReal d) s)
  have h3 : (ENNReal.ofReal d).toReal = d := by
    rw [ENNReal.toReal_ofReal h_nonneg]
  have h4 : ((ENNReal.ofReal d)^s).toReal = d ^ s := by
    rw [h2, h3]
  have h5 : (ENNReal.ofReal d)^s = ENNReal.ofReal (((ENNReal.ofReal d)^s).toReal) :=
    (ENNReal.ofReal_toReal h_ne_top).symm
  rw [h5, h4]

lemma ennreal_ofReal_inv {x : ℝ} (hx : 0 < x) :
    (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal (x⁻¹) := by
  have h_nonneg : 0 ≤ x := by linarith
  have h_ne_zero : ENNReal.ofReal x ≠ 0 := by
    intro h4
    have h5 : x ≤ 0 := ENNReal.ofReal_eq_zero.mp h4
    linarith
  have h_ne_top : (ENNReal.ofReal x)⁻¹ ≠ ⊤ := by
    exact mt ENNReal.inv_eq_top.mp h_ne_zero
  have h2 : ((ENNReal.ofReal x)⁻¹).toReal = ((ENNReal.ofReal x).toReal)⁻¹ := by
    rw [ENNReal.toReal_inv] <;> simp [hx.ne']
  have h3 : (ENNReal.ofReal x).toReal = x := by
    rw [ENNReal.toReal_ofReal h_nonneg]
  have h4 : ((ENNReal.ofReal x)⁻¹).toReal = x⁻¹ := by rw [h2, h3]
  have h5 : (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal (((ENNReal.ofReal x)⁻¹).toReal) :=
    (ENNReal.ofReal_toReal h_ne_top).symm
  rw [h5, h4]

lemma planeKernel_ofReal {s : ℝ} {x y : EuclideanPlane} (hne : x ≠ y) (hs : 0 ≤ s) :
    planeKernel s x y = ENNReal.ofReal (‖x - y‖ ^ (-s)) := by
  rw [planeKernel, if_neg hne]

lemma exists_annulus_index {d : ℝ} (hpos : 0 < d) (hle : d ≤ 1) :
    ∃ (k : ℕ), (2 : ℝ)^(-(k + 1 : ℝ)) < d ∧ d ≤ (2 : ℝ)^(-(k : ℝ)) := by
  let x : ℝ := Real.logb 2 (1 / d)
  have h1pos : 0 < 1 / d := by positivity
  have h1div : 1 ≤ 1 / d := by
    apply one_le_one_div <;> linarith
  have hx_nonneg : 0 ≤ x := Real.logb_nonneg (by norm_num) h1div
  let k : ℕ := Nat.floor x
  have hk1 : (k : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hk2 : x < (k : ℝ) + 1 := Nat.lt_floor_add_one x
  have h_rpow_logb : (2 : ℝ)^x = 1 / d := by
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h_eq : x * Real.log 2 = Real.log (1 / d) := by
      simp only [x, Real.logb]
      field_simp [h_log2_pos.ne'] <;> ring
    have h1 : (2 : ℝ)^x = Real.exp (Real.log 2 * x) :=
      (Real.rpow_def_of_pos (show (0 : ℝ) < 2 from by norm_num)) x
    have h_comm : Real.log 2 * x = x * Real.log 2 := by ring
    calc
      (2 : ℝ)^x
        = Real.exp (Real.log 2 * x) := h1
      _ = Real.exp (x * Real.log 2) := by rw [h_comm]
      _ = Real.exp (Real.log (1 / d)) := by rw [h_eq]
      _ = 1 / d := by rw [Real.exp_log (by positivity)]
  have h3 : (2 : ℝ)^(k : ℝ) ≤ 1 / d := by
    have h4 : (2 : ℝ)^(k : ℝ) ≤ (2 : ℝ)^x := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact hk1
    rw [h_rpow_logb] at h4
    exact h4
  have h6 : 1 / d < (2 : ℝ)^((k : ℝ) + 1) := by
    have h7 : (2 : ℝ)^x < (2 : ℝ)^((k : ℝ) + 1) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      exact hk2
    rw [h_rpow_logb] at h7
    exact h7
  have h9 : (2 : ℝ)^(-(k + 1 : ℝ)) < d := by
    have h10 : (2 : ℝ)^(-(k + 1 : ℝ)) = ((2 : ℝ)^((k : ℝ) + 1))⁻¹ := by
      rw [show (-(k + 1 : ℝ)) = -((k : ℝ) + 1) by simp]
      rw [Real.rpow_neg (by norm_num)] <;> ring
    rw [h10]
    have h11 : ((2 : ℝ)^((k : ℝ) + 1))⁻¹ < (1 / d)⁻¹ := by gcongr
    have h12 : (1 / d)⁻¹ = d := by
      field_simp [hpos.ne'] <;> ring
    rw [h12] at h11
    exact h11
  have h14 : d ≤ (2 : ℝ)^(-(k : ℝ)) := by
    have h15 : (2 : ℝ)^(-(k : ℝ)) = ((2 : ℝ)^(k : ℝ))⁻¹ := by
      rw [Real.rpow_neg (by norm_num)] <;> ring
    rw [h15]
    have h16 : d ≤ ((2 : ℝ)^(k : ℝ))⁻¹ := by
      have h17 : (1 / d)⁻¹ = d := by field_simp [hpos.ne'] <;> ring
      rw [← h17]
      gcongr
    exact h16
  exact ⟨k, h9, h14⟩

/-! ### Energy bound for finite δ-separated sets -/

/-- Bound on the s-Riesz energy of the uniform measure on a finite δ-separated set
with ball-growth.

Given a finite set `S` that is δ-separated and satisfies the ball-growth condition
`|S ∩ B(p,r)| ≤ C * r^t * |S|` for all `r ≥ δ`, the uniform probability measure on
`S` has finite s-Riesz energy for any `0 < s < t`.

The explicit bound is `M0 = 1 + C * 2^s / (1 - 2^(s-t))`. -/
theorem finite_set_energy_bound_explicit {S : Finset EuclideanPlane} {s t C δ : ℝ}
    (hs_pos : 0 < s) (hst : s < t) (hδ_pos : 0 < δ) (hC_pos : 0 < C)
    (hS_nonempty : S.Nonempty)
    (hS_sep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖)
    (hS_ball : ∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun q => ‖p - q‖ ≤ r)).card ≤ C * r^t * S.card) :
    planeEnergy ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)) s
      ≤ ENNReal.ofReal (1 + C * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t))) := by
  let ratio : ℝ := (2 : ℝ) ^ (s - t)
  have h_ratio_lt_one : ratio < 1 := by
    have h2 : s - t < 0 := by linarith
    have h3 : (2 : ℝ) ^ (s - t) < (2 : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      exact h2
    norm_num at h3 ⊢
    exact h3
  have h_ratio_pos : 0 < ratio := by positivity
  have h_geom_sum : ∀ (N : ℕ), ∑ k ∈ Finset.range N, ratio ^ k ≤ 1 / (1 - ratio) := by
    have h_formula : ∀ N, ∑ k ∈ Finset.range N, ratio ^ k = (1 - ratio ^ N) / (1 - ratio) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp [h_ratio_pos.ne', (show (1 - ratio : ℝ) ≠ 0 by linarith)] <;> ring
    intro N
    rw [h_formula N]
    have h_pos : 0 < 1 - ratio := by linarith
    have h_nonneg : 0 ≤ ratio ^ N := by positivity
    have h : (1 - ratio ^ N) / (1 - ratio) ≤ 1 / (1 - ratio) := by
      apply div_le_div_of_nonneg_right <;> linarith
    exact h
  let M0 : ℝ := 1 + C * (2 : ℝ) ^ s / (1 - ratio)
  have hM0_pos : 0 < M0 := by positivity

  have hK_exists : ∃ (K : ℕ), (2 : ℝ)^(-(K : ℝ)) < δ := by
    have h1pos2 : 0 < 1 / δ := by positivity
    have h1 : ∃ (n : ℕ), (n : ℝ) > Real.logb 2 (1 / δ) := exists_nat_gt (Real.logb 2 (1 / δ))
    rcases h1 with ⟨K, hK⟩
    have h2 : (K : ℝ) > Real.logb 2 (1 / δ) := by exact_mod_cast hK
    have h3 : -(K : ℝ) < Real.logb 2 δ := by
      have h4 : Real.logb 2 (1 / δ) = -Real.logb 2 δ := by
        simp [Real.logb, Real.log_div (by positivity) (by positivity)] <;> ring
      linarith
    have h5 : (2 : ℝ)^(-(K : ℝ)) < (2 : ℝ)^(Real.logb 2 δ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      exact h3
    have h6 : (2 : ℝ)^(Real.logb 2 δ) = δ := by
      have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h_eq : Real.logb 2 δ * Real.log 2 = Real.log δ := by
        simp only [Real.logb]
        field_simp [h_log2_pos.ne'] <;> ring
      have h1 : (2 : ℝ)^(Real.logb 2 δ) = Real.exp (Real.log 2 * Real.logb 2 δ) :=
        (Real.rpow_def_of_pos (show (0 : ℝ) < 2 from by norm_num)) (Real.logb 2 δ)
      have h_comm : Real.log 2 * Real.logb 2 δ = Real.logb 2 δ * Real.log 2 := by ring
      calc
        (2 : ℝ)^(Real.logb 2 δ)
          = Real.exp (Real.log 2 * Real.logb 2 δ) := h1
        _ = Real.exp (Real.logb 2 δ * Real.log 2) := by rw [h_comm]
        _ = Real.exp (Real.log δ) := by rw [h_eq]
        _ = δ := by rw [Real.exp_log hδ_pos]
    rw [h6] at h5
    exact ⟨K, h5⟩
  rcases hK_exists with ⟨K, hK2⟩

  have h_point_bound : ∀ p ∈ S,
      ∑ q ∈ S.erase p, (‖p - q‖ ^ (-s) : ℝ) ≤ M0 * (S.card : ℝ) := by
    intro p hp
    let A (k : ℕ) := S.filter (fun q =>
      (2 : ℝ)^(-(k+1 : ℝ)) < ‖p - q‖ ∧ ‖p - q‖ ≤ (2 : ℝ)^(-(k : ℝ)))
    let Binf := S.filter (fun q => 1 < ‖p - q‖)

    have hA_card : ∀ k : ℕ, ((A k).card : ℝ) ≤ C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ) := by
      intro k
      by_cases h : δ ≤ (2 : ℝ)^(-(k : ℝ))
      · have h1 : A k ⊆ S.filter (fun q => ‖p - q‖ ≤ (2 : ℝ)^(-(k : ℝ))) := by
          intro q hq
          simp only [A, Finset.mem_filter] at hq ⊢
          exact ⟨hq.1, hq.2.2⟩
        have h2 : (A k).card ≤ (S.filter (fun q => ‖p - q‖ ≤ (2 : ℝ)^(-(k : ℝ)))).card :=
          Finset.card_le_card h1
        have h3 : ((A k).card : ℝ) ≤ ↑((S.filter (fun q => ‖p - q‖ ≤ (2 : ℝ)^(-(k : ℝ)))).card) := by
          exact_mod_cast h2
        have h4 := hS_ball p hp ((2 : ℝ)^(-(k : ℝ))) h
        exact le_trans h3 h4
      · have h' : (2 : ℝ)^(-(k : ℝ)) < δ := by linarith
        have h3 : A k = ∅ := by
          have h4 : (A k).card = 0 := by
            by_contra h5
            have h6 : 0 < (A k).card := Nat.pos_of_ne_zero h5
            rcases Finset.card_pos.mp h6 with ⟨q, hq⟩
            rcases Finset.mem_filter.mp hq with ⟨hqS, h_aj1, h_aj2⟩
            have h5' : ‖p - q‖ < δ := lt_of_le_of_lt h_aj2 h'
            have h6' : p ≠ q := by
              intro h7
              rw [h7] at h_aj1
              have h_cont : (2 : ℝ)^(-(k + 1 : ℝ)) < 0 := by simpa using h_aj1
              have h_pos : 0 < (2 : ℝ)^(-(k + 1 : ℝ)) := by positivity
              exact False.elim (lt_irrefl 0 (h_pos.trans h_cont))
            have h7 : δ ≤ ‖p - q‖ := hS_sep p hp q hqS h6'
            have h_cont : δ < δ := h7.trans_lt h5'
            exact False.elim (lt_irrefl δ h_cont)
          exact Finset.card_eq_zero.mp h4
        rw [h3]
        simp <;> positivity

    have h_cover : ∀ q ∈ S.erase p, q ∈ Binf ∨ ∃ k < K, q ∈ A k := by
      intro q hq
      have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
      have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
      have hpos : 0 < ‖p - q‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hqne.symm)
      by_cases hbig : 1 < ‖p - q‖
      · left; simp only [Binf, Finset.mem_filter]; exact ⟨hqS, hbig⟩
      · have hle : ‖p - q‖ ≤ 1 := by linarith
        rcases exists_annulus_index hpos hle with ⟨j, h_aj1, h_aj2⟩
        have h_j_lt_K : j < K := by
          by_contra h
          have h9 : j ≥ K := by omega
          have h10 : (2 : ℝ)^(-(j : ℝ)) ≤ (2 : ℝ)^(-(K : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have h11 : -(j : ℝ) ≤ -(K : ℝ) := by
              have h12 : (K : ℝ) ≤ (j : ℝ) := by exact_mod_cast h9
              linarith
            exact h11
          have h11 : ‖p - q‖ < δ := by linarith [h_aj2, h10, hK2]
          have h12 : δ ≤ ‖p - q‖ := hS_sep p hp q hqS hqne.symm
          linarith
        right; refine ⟨j, h_j_lt_K, ?_⟩
        simp only [A, Finset.mem_filter]; exact ⟨hqS, h_aj1, h_aj2⟩

    have hBinf_sum : ∑ q ∈ Binf, (‖p - q‖ ^ (-s) : ℝ) ≤ (Binf.card : ℝ) := by
      have h9 : ∀ q ∈ Binf, (‖p - q‖ ^ (-s) : ℝ) ≤ 1 := by
        intro q hq
        have h10 : 1 < ‖p - q‖ := (Finset.mem_filter.mp hq).2
        have h11 : 1 ≤ ‖p - q‖ := by linarith
        have h12 : 0 ≤ s := by linarith
        have h13 : 1 ≤ ‖p - q‖ ^ s := by
          have h14 : (1 : ℝ) ^ s ≤ ‖p - q‖ ^ s := Real.rpow_le_rpow (by norm_num) h11 (by linarith)
          simpa using h14
        have h14 : (‖p - q‖ ^ s)⁻¹ ≤ 1 := by
          have h15 : 0 < ‖p - q‖ ^ s := by positivity
          calc
            (‖p - q‖ ^ s)⁻¹ ≤ (1 : ℝ)⁻¹ := by gcongr
            _ = 1 := by norm_num
        have h15 : ‖p - q‖ ^ (-s) = (‖p - q‖ ^ s)⁻¹ := by
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h15]
        exact h14
      calc
        ∑ q ∈ Binf, (‖p - q‖ ^ (-s) : ℝ)
          ≤ ∑ q ∈ Binf, (1 : ℝ) := Finset.sum_le_sum h9
        _ = (Binf.card : ℝ) := by simp

    have hA_sum : ∀ k : ℕ, ∑ q ∈ A k, (‖p - q‖ ^ (-s) : ℝ) ≤
        (A k).card * (2 : ℝ)^((k + 1 : ℝ) * s) := by
      intro k
      have h9 : ∀ q ∈ A k, (‖p - q‖ ^ (-s) : ℝ) ≤ (2 : ℝ)^((k + 1 : ℝ) * s) := by
        intro q hq
        have h10 : (2 : ℝ)^(-(k + 1 : ℝ)) < ‖p - q‖ := (Finset.mem_filter.mp hq).2.1
        have ha : 0 < (2 : ℝ)^(-(k + 1 : ℝ)) := by positivity
        have hle : (2 : ℝ)^(-(k + 1 : ℝ)) ≤ ‖p - q‖ := h10.le
        have h1 : (((2 : ℝ)^(-(k + 1 : ℝ))) ^ s) ≤ ‖p - q‖ ^ s := by
          have hbase1 : 0 ≤ (2 : ℝ)^(-(k + 1 : ℝ)) := by positivity
          have h_exp : 0 ≤ s := by linarith
          exact Real.rpow_le_rpow hbase1 hle h_exp
        have h2 : ‖p - q‖ ^ (-s) = (‖p - q‖ ^ s)⁻¹ := by
          rw [Real.rpow_neg (by positivity)] <;> ring
        have h3 : ((2 : ℝ)^(-(k + 1 : ℝ))) ^ (-s) = (((2 : ℝ)^(-(k + 1 : ℝ))) ^ s)⁻¹ := by
          rw [Real.rpow_neg (by positivity)] <;> ring
        have h4 : ‖p - q‖ ^ (-s) ≤ ((2 : ℝ)^(-(k + 1 : ℝ))) ^ (-s) := by
          rw [h2, h3]
          gcongr
        have h13 : ((2 : ℝ)^(-(k + 1 : ℝ))) ^ (-s) = (2 : ℝ)^((k + 1 : ℝ) * s) := by
          rw [← Real.rpow_mul (by norm_num)] <;> ring_nf
        rw [h13] at h4
        exact h4
      calc
        ∑ q ∈ A k, (‖p - q‖ ^ (-s) : ℝ)
          ≤ ∑ q ∈ A k, (2 : ℝ)^((k + 1 : ℝ) * s) := Finset.sum_le_sum h9
        _ = (A k).card * (2 : ℝ)^((k + 1 : ℝ) * s) := by
          rw [Finset.sum_const] <;> ring

    let U := Binf ∪ Finset.biUnion (Finset.range K) A

    have h_disj_A : ∀ (i j : ℕ), i ≠ j → Disjoint (A i) (A j) := by
      intro i j hne
      wlog h : i < j generalizing i j
      · exact (this j i hne.symm (hne.lt_or_gt.resolve_left h)).symm
      simp only [A, Finset.disjoint_left]
      intro q hi hj
      have h_i_mem := Finset.mem_filter.mp hi
      have h_j_mem := Finset.mem_filter.mp hj
      have h_i1 : (2 : ℝ)^(-(i+1 : ℝ)) < ‖p - q‖ := h_i_mem.2.1
      have h_j2 : ‖p - q‖ ≤ (2 : ℝ)^(-(j : ℝ)) := h_j_mem.2.2
      have h_ij : (2 : ℝ)^(-(j : ℝ)) ≤ (2 : ℝ)^(-(i+1 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h_i1_le_j : (i + 1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h
        linarith
      linarith

    have h_disj1 : Disjoint Binf (Finset.biUnion (Finset.range K) A) := by
      simp only [Binf, A, Finset.disjoint_left]
      intro q hq1 hq2
      have h1 : 1 < ‖p - q‖ := (Finset.mem_filter.mp hq1).2
      rcases Finset.mem_biUnion.mp hq2 with ⟨k, _, hq3⟩
      have h2 : ‖p - q‖ ≤ (2 : ℝ)^(-(k : ℝ)) := (Finset.mem_filter.mp hq3).2.2
      have h3 : (2 : ℝ)^(-(k : ℝ)) ≤ 1 := by
        have h4 : -(k : ℝ) ≤ 0 := by simp
        have h5 : (2 : ℝ)^(-(k : ℝ)) ≤ (2 : ℝ)^(0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
        simpa using h5
      linarith

    have h_sum_U : ∑ q ∈ U, (‖p - q‖ ^ (-s) : ℝ) =
        ∑ q ∈ Binf, (‖p - q‖ ^ (-s) : ℝ) +
        ∑ q ∈ Finset.biUnion (Finset.range K) A, (‖p - q‖ ^ (-s) : ℝ) :=
      Finset.sum_union h_disj1

    have h_sum_biUnion : ∑ q ∈ Finset.biUnion (Finset.range K) A, (‖p - q‖ ^ (-s) : ℝ) =
        ∑ k ∈ Finset.range K, ∑ q ∈ A k, (‖p - q‖ ^ (-s) : ℝ) :=
      Finset.sum_biUnion (fun i _ j _ hne => h_disj_A i j hne)

    have hU_cover : S.erase p ⊆ U := by
      intro q hq
      rcases h_cover q hq with (h | ⟨k, hk, hqA⟩)
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, hqA⟩)

    calc
      ∑ q ∈ S.erase p, (‖p - q‖ ^ (-s) : ℝ)
        ≤ ∑ q ∈ U, (‖p - q‖ ^ (-s) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hU_cover (fun _ _ _ => by positivity)
      _ = ∑ q ∈ Binf, (‖p - q‖ ^ (-s) : ℝ) +
            ∑ k ∈ Finset.range K, ∑ q ∈ A k, (‖p - q‖ ^ (-s) : ℝ) := by
          rw [h_sum_U, h_sum_biUnion]
      _ ≤ (Binf.card : ℝ) + ∑ k ∈ Finset.range K,
            (A k).card * (2 : ℝ)^((k + 1 : ℝ) * s) := by
          have h_left : ∑ q ∈ Binf, (‖p - q‖ ^ (-s) : ℝ) ≤ (Binf.card : ℝ) := hBinf_sum
          have h_right : ∑ k ∈ Finset.range K, ∑ q ∈ A k, (‖p - q‖ ^ (-s) : ℝ) ≤
              ∑ k ∈ Finset.range K, (A k).card * (2 : ℝ)^((k + 1 : ℝ) * s) := by
            apply Finset.sum_le_sum
            intro k _
            exact hA_sum k
          exact add_le_add h_left h_right
      _ ≤ (S.card : ℝ) + ∑ k ∈ Finset.range K,
            (C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ)) * (2 : ℝ)^((k + 1 : ℝ) * s) := by
          have h_left2 : (Binf.card : ℝ) ≤ (S.card : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          have h_right2 : ∑ k ∈ Finset.range K, (A k).card * (2 : ℝ)^((k + 1 : ℝ) * s) ≤
              ∑ k ∈ Finset.range K, (C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ)) * (2 : ℝ)^((k + 1 : ℝ) * s) := by
            apply Finset.sum_le_sum
            intro k _
            have h5 : ((A k).card : ℝ) ≤ C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ) := hA_card k
            exact mul_le_mul_of_nonneg_right h5 (by positivity)
          exact add_le_add h_left2 h_right2
      _ = (S.card : ℝ) + C * (2 : ℝ)^s * (S.card : ℝ) *
            ∑ k ∈ Finset.range K, ratio ^ k := by
          have h3 : ∀ k : ℕ, (C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ)) *
              (2 : ℝ)^((k + 1 : ℝ) * s) = C * (2 : ℝ)^s * (S.card : ℝ) * ratio ^ k := by
            intro k
            have h4 : ((2 : ℝ)^(-(k : ℝ)))^t = (2 : ℝ)^(-(k : ℝ) * t) := by
              rw [← Real.rpow_mul (by norm_num)] <;> ring
            have h5 : ratio ^ k = (2 : ℝ)^((k : ℝ) * (s - t)) := by
              have h51 : ratio = (2 : ℝ)^(s - t) := by rfl
              rw [h51]
              have h52 : ((2 : ℝ)^(s - t)) ^ k = (2 : ℝ)^((k : ℝ) * (s - t)) := by
                have h53 : ((2 : ℝ)^(s - t)) ^ k = ((2 : ℝ)^(s - t)) ^ (k : ℝ) := by norm_cast
                rw [h53, ← Real.rpow_mul (by norm_num)] <;> ring_nf
              exact h52
            calc
              (C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ)) * (2 : ℝ)^((k + 1 : ℝ) * s)
                = C * (S.card : ℝ) * (((2 : ℝ)^(-(k : ℝ)))^t * (2 : ℝ)^((k + 1 : ℝ) * s)) := by ring
              _ = C * (S.card : ℝ) * ((2 : ℝ)^(-(k : ℝ) * t) * (2 : ℝ)^((k + 1 : ℝ) * s)) := by rw [h4]
              _ = C * (S.card : ℝ) * (2 : ℝ)^(-(k : ℝ) * t + (k + 1 : ℝ) * s) := by
                  rw [← Real.rpow_add (by norm_num)] <;> ring
              _ = C * (S.card : ℝ) * (2 : ℝ)^(s + (k : ℝ) * (s - t)) := by
                  have h8 : -(k : ℝ) * t + (k + 1 : ℝ) * s = s + (k : ℝ) * (s - t) := by ring
                  rw [h8]
              _ = C * (S.card : ℝ) * ((2 : ℝ)^s * (2 : ℝ)^((k : ℝ) * (s - t))) := by
                  rw [← Real.rpow_add (by norm_num)] <;> ring
              _ = C * (2 : ℝ)^s * (S.card : ℝ) * ratio ^ k := by
                  rw [h5] <;> ring
          have h_sum_factor : ∑ k ∈ Finset.range K, C * (2 : ℝ)^s * (S.card : ℝ) * ratio ^ k =
              C * (2 : ℝ)^s * (S.card : ℝ) * ∑ k ∈ Finset.range K, ratio ^ k := by
            rw [Finset.mul_sum] <;> ring
          have h_sum_eq : ∑ k ∈ Finset.range K, (C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ)) * (2 : ℝ)^((k + 1 : ℝ) * s) =
              C * (2 : ℝ)^s * (S.card : ℝ) * ∑ k ∈ Finset.range K, ratio ^ k := by
            have h3' : ∑ k ∈ Finset.range K, (C * ((2 : ℝ)^(-(k : ℝ)))^t * (S.card : ℝ)) * (2 : ℝ)^((k + 1 : ℝ) * s) =
                ∑ k ∈ Finset.range K, C * (2 : ℝ)^s * (S.card : ℝ) * ratio ^ k :=
              Finset.sum_congr rfl (fun k _ => h3 k)
            rw [h3', h_sum_factor]
          rw [h_sum_eq]
      _ ≤ (S.card : ℝ) + C * (2 : ℝ)^s * (S.card : ℝ) * (1 / (1 - ratio)) := by
          gcongr; exact h_geom_sum K
      _ = M0 * (S.card : ℝ) := by
          simp only [M0] <;> ring

  let μ : Measure EuclideanPlane := (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)
  have hS_card_pos : 0 < S.card := Finset.card_pos.mpr hS_nonempty

  have h_lintegral_finset : ∀ (f : EuclideanPlane → ENNReal),
      ∫⁻ x, f x ∂(Measure.count.restrict (S : Set EuclideanPlane)) = ∑ x ∈ S, f x := by
    have h_main : ∀ (T : Finset EuclideanPlane), ∀ (f : EuclideanPlane → ENNReal),
        ∫⁻ x, f x ∂(Measure.count.restrict (T : Set EuclideanPlane)) = ∑ x ∈ T, f x := by
      intro T
      induction T using Finset.induction with
      | empty =>
        intro f
        have h_zero : Measure.count.restrict (∅ : Set EuclideanPlane) = 0 := by
          ext A _
          simp
        have h : ∫⁻ x, f x ∂(Measure.count.restrict (∅ : Set EuclideanPlane)) = 0 := by
          rw [h_zero] <;> simp
        simpa using h
      | @insert x T hx ih =>
        intro f
        have h_meas_eq : Measure.count.restrict (insert x T : Set EuclideanPlane) =
            Measure.dirac x + Measure.count.restrict (T : Set EuclideanPlane) := by
          ext A hA
          have h_fin : (A ∩ (T : Set EuclideanPlane)).Finite := by
            apply Set.Finite.subset (Finset.finite_toSet T)
            simp
          have hs_mble : MeasurableSet (A ∩ (T : Set EuclideanPlane)) := hA.inter (Finset.measurableSet T)
          have h_xnotin : x ∉ (A ∩ (T : Set EuclideanPlane)) := by
            intro h
            exact hx h.2
          by_cases hxA : x ∈ A
          · have h_set : A ∩ (insert x T : Set EuclideanPlane) = insert x (A ∩ (T : Set EuclideanPlane)) := by
              ext y
              simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert, Set.mem_insert_iff]
              constructor
              · rintro ⟨hyA, (rfl | hyT)⟩
                · exact Or.inl rfl
                · exact Or.inr ⟨hyA, hyT⟩
              · rintro (rfl | ⟨hyA, hyT⟩)
                · exact ⟨hxA, Or.inl rfl⟩
                · exact ⟨hyA, Or.inr hyT⟩
            have h_fin2 : (insert x (A ∩ (T : Set EuclideanPlane))).Finite := h_fin.insert x
            have h_mble2 : MeasurableSet (A ∩ (insert x T : Set EuclideanPlane)) :=
              hA.inter (by simpa using Finset.measurableSet (insert x T))
            have h_mble2' : MeasurableSet (insert x (A ∩ (T : Set EuclideanPlane))) := by
              rw [← h_set] <;> exact h_mble2
            let s' : Finset EuclideanPlane := h_fin.toFinset
            have h_xnotin_s' : x ∉ s' := by
              simpa [s'] using h_xnotin
            have h_fin2_eq : h_fin2.toFinset = insert x s' := by
              ext z
              simp [h_fin2, s', Set.Finite.mem_toFinset, h_xnotin_s'] <;> tauto
            have h_card2 : Measure.count (insert x (A ∩ (T : Set EuclideanPlane))) =
                ↑(insert x s').card := by
              have h_tmp := MeasureTheory.Measure.count_apply_finite' h_fin2 h_mble2'
              rw [h_tmp, h_fin2_eq]
            have h_card : Measure.count (A ∩ (T : Set EuclideanPlane)) = ↑(s'.card) :=
              MeasureTheory.Measure.count_apply_finite' h_fin hs_mble
            have h_indicator : A.indicator 1 x = 1 := by
              simp [Set.indicator_apply, hxA]
            simp only [Measure.restrict_apply hA, Measure.add_apply]
            rw [h_set, h_card2, h_card]
            have h_dirac : (Measure.dirac x) A = (1 : ENNReal) := by
              have h : (Measure.dirac x) A = Set.indicator A (1 : EuclideanPlane → ENNReal) x :=
                Measure.dirac_apply' x hA
              rw [h]
              simp [Set.indicator_apply, hxA] <;> norm_num
            rw [h_dirac]
            have h_card_eq : (insert x s').card = s'.card + 1 := by
              simp [h_xnotin_s'] <;> omega
            rw [h_card_eq] <;> norm_cast <;> ring
          · have h_set : A ∩ (insert x T : Set EuclideanPlane) = A ∩ (T : Set EuclideanPlane) := by
              ext y
              simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert]
              constructor
              · rintro ⟨hyA, rfl | hyT⟩
                · exact False.elim (hxA hyA)
                · exact ⟨hyA, hyT⟩
              · rintro ⟨hyA, hyT⟩
                exact ⟨hyA, Or.inr hyT⟩
            simp only [Measure.restrict_apply hA, Measure.add_apply]
            rw [h_set]
            have h_dirac : (Measure.dirac x) A = (0 : ENNReal) := by
              have h : (Measure.dirac x) A = Set.indicator A (1 : EuclideanPlane → ENNReal) x :=
                Measure.dirac_apply' x hA
              rw [h]
              simp [Set.indicator_apply, hxA] <;> norm_num
            rw [h_dirac] <;> simp
        have h_goal : ∫⁻ y, f y ∂(Measure.count.restrict (insert x T : Set EuclideanPlane)) =
            ∑ y ∈ insert x T, f y := by
          rw [h_meas_eq]
          rw [lintegral_add_measure]
          rw [ih f]
          have h_dirac : ∫⁻ y, f y ∂(Measure.dirac x) = f x := by
            rw [lintegral_dirac]
          rw [h_dirac, Finset.sum_insert hx] <;> ring
        simpa using h_goal
    exact h_main S

  have h1 : ∀ (x : EuclideanPlane), ∫⁻ y, planeKernel s x y ∂μ =
      (S.card : ENNReal)⁻¹ * ∑ y ∈ S, planeKernel s x y := by
    intro x
    have h_main : ∫⁻ y, planeKernel s x y ∂μ =
        (S.card : ENNReal)⁻¹ * ∫⁻ y, planeKernel s x y ∂(Measure.count.restrict (S : Set EuclideanPlane)) := by
      rw [lintegral_smul_measure] <;> rfl
    rw [h_main, h_lintegral_finset (planeKernel s x)]

  have h2 : planeEnergy μ s =
      (S.card : ENNReal)⁻¹ * ∑ x ∈ S, ∫⁻ y, planeKernel s x y ∂μ := by
    have h_main : planeEnergy μ s =
        (S.card : ENNReal)⁻¹ * ∫⁻ x, ∫⁻ y, planeKernel s x y ∂μ ∂(Measure.count.restrict (S : Set EuclideanPlane)) := by
      simp [planeEnergy, μ, lintegral_smul_measure] <;> rfl
    rw [h_main, h_lintegral_finset (fun x => ∫⁻ y, planeKernel s x y ∂μ)]
  rw [h2]
  have h3 : ∑ x ∈ S, ∫⁻ y, planeKernel s x y ∂μ =
      (S.card : ENNReal)⁻¹ * ∑ x ∈ S, ∑ y ∈ S, planeKernel s x y := by
    rw [Finset.sum_congr rfl (fun x _ => h1 x)]
    <;> rw [Finset.mul_sum] <;> ring
  rw [h3]
  have h4 : ∀ x ∈ S, ∑ y ∈ S, planeKernel s x y =
      ENNReal.ofReal (∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) := by
    intro x hx
    have h5 : ∑ y ∈ S, planeKernel s x y = ∑ y ∈ S.erase x, planeKernel s x y := by
      have h51 : insert x (S.erase x) = S := by
        rw [Finset.insert_erase hx]
      have h53 : x ∉ S.erase x := by simp
      have h2 : ∑ y ∈ insert x (S.erase x), planeKernel s x y =
          planeKernel s x x + ∑ y ∈ S.erase x, planeKernel s x y := by
        rw [Finset.sum_insert h53]
      have h52 : planeKernel s x x = 0 := by
        rw [planeKernel, if_pos rfl]
      have h4 : ∑ y ∈ S, planeKernel s x y = ∑ y ∈ insert x (S.erase x), planeKernel s x y := by
        congr
        <;> exact h51.symm
      rw [h4, h2, h52] <;> ring
    rw [h5]
    have h_eq : ∀ y ∈ S.erase x, planeKernel s x y = ENNReal.ofReal (‖x - y‖ ^ (-s)) := by
      intro y hy
      have h6 : y ≠ x := by
        simp only [Finset.mem_erase] at hy; exact hy.1
      exact planeKernel_ofReal h6.symm (by linarith)
    have h_sum : ∑ y ∈ S.erase x, planeKernel s x y =
        ∑ y ∈ S.erase x, ENNReal.ofReal (‖x - y‖ ^ (-s)) :=
      Finset.sum_congr rfl h_eq
    rw [h_sum]
    have h_nonneg : ∀ y ∈ S.erase x, 0 ≤ ‖x - y‖ ^ (-s) := by
      intro y _; positivity
    have h_ofReal_sum : ENNReal.ofReal (∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) =
        ∑ y ∈ S.erase x, ENNReal.ofReal (‖x - y‖ ^ (-s) : ℝ) := by
      exact ENNReal.ofReal_sum_of_nonneg h_nonneg
    rw [h_ofReal_sum]
  have h5 : ∑ x ∈ S, ∑ y ∈ S, planeKernel s x y =
      ENNReal.ofReal (∑ x ∈ S, ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) := by
    rw [Finset.sum_congr rfl h4]
    have h_nonneg2 : ∀ x ∈ S, 0 ≤ ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ) := by
      intro x _
      apply Finset.sum_nonneg
      intro y _
      positivity
    have h_ofReal_sum2 : ENNReal.ofReal (∑ x ∈ S, ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) =
        ∑ x ∈ S, ENNReal.ofReal (∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) := by
      exact ENNReal.ofReal_sum_of_nonneg (fun x _ => h_nonneg2 x ‹_›)
    rw [h_ofReal_sum2]
  rw [h5]
  have h6 : ∑ x ∈ S, ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ) ≤ M0 * (S.card : ℝ)^2 := by
    calc
      ∑ x ∈ S, ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)
        ≤ ∑ x ∈ S, M0 * (S.card : ℝ) := by
          gcongr; exact h_point_bound x ‹_›
      _ = (S.card : ℝ) * (M0 * (S.card : ℝ)) := by
          rw [Finset.sum_const] <;> ring
      _ = M0 * (S.card : ℝ)^2 := by ring
  have h7 : ENNReal.ofReal (∑ x ∈ S, ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) ≤
      ENNReal.ofReal (M0 * (S.card : ℝ)^2) := by
    exact ENNReal.ofReal_le_ofReal h6
  have h8 : (S.card : ENNReal) ≠ 0 := by exact_mod_cast hS_card_pos.ne'
  have h9 : (S.card : ENNReal) ≠ ⊤ := by exact_mod_cast (by simp)
  have h10 : (S.card : ENNReal)⁻¹ * ((S.card : ENNReal)⁻¹ *
          ENNReal.ofReal (M0 * (S.card : ℝ)^2)) = ENNReal.ofReal M0 := by
    have h11 : ENNReal.ofReal (M0 * (S.card : ℝ)^2) =
          ENNReal.ofReal M0 * (S.card : ENNReal)^2 := by
      have h_pos1 : 0 ≤ M0 := by linarith
      have h_pos2 : 0 ≤ (S.card : ℝ)^2 := by positivity
      have h11a : ENNReal.ofReal (M0 * (S.card : ℝ)^2) =
          ENNReal.ofReal M0 * ENNReal.ofReal ((S.card : ℝ)^2) := by
        rw [ENNReal.ofReal_mul h_pos1]
      have h11b : ENNReal.ofReal ((S.card : ℝ)^2) = (S.card : ENNReal)^2 := by
        norm_cast
      rw [h11a, h11b]
    rw [h11]
    have h12 : (S.card : ENNReal)⁻¹ * ((S.card : ENNReal)⁻¹ * (ENNReal.ofReal M0 * (S.card : ENNReal)^2)) =
        ENNReal.ofReal M0 := by
      have h13 : (S.card : ENNReal)⁻¹ * (S.card : ENNReal) = 1 := ENNReal.inv_mul_cancel h8 h9
      have h14 : (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ * (S.card : ENNReal)^2 = 1 := by
        have h15 : (S.card : ENNReal)^2 = (S.card : ENNReal) * (S.card : ENNReal) := by simp [pow_two]
        rw [h15]
        calc
          (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ * ((S.card : ENNReal) * (S.card : ENNReal))
            = ((S.card : ENNReal)⁻¹ * (S.card : ENNReal)) * ((S.card : ENNReal)⁻¹ * (S.card : ENNReal)) := by
              simp [mul_assoc, mul_comm, mul_left_comm]
          _ = 1 * 1 := by rw [h13]
          _ = 1 := by simp
      have h15 : (S.card : ENNReal)⁻¹ * ((S.card : ENNReal)⁻¹ * (ENNReal.ofReal M0 * (S.card : ENNReal)^2)) =
          ENNReal.ofReal M0 * ((S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ * (S.card : ENNReal)^2) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h15, h14] <;> simp
    exact h12
  have h_final : (S.card : ENNReal)⁻¹ * ((S.card : ENNReal)⁻¹ *
        ENNReal.ofReal (∑ x ∈ S, ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ))) ≤
      ENNReal.ofReal M0 := by
    calc
      (S.card : ENNReal)⁻¹ * ((S.card : ENNReal)⁻¹ *
          ENNReal.ofReal (∑ x ∈ S, ∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)))
        ≤ (S.card : ENNReal)⁻¹ * ((S.card : ENNReal)⁻¹ *
            ENNReal.ofReal (M0 * (S.card : ℝ)^2)) := by gcongr
      _ = ENNReal.ofReal M0 := h10
  exact h_final

/-- Existence form of the energy bound: there exists a real bound M.
This is a corollary of `finite_set_energy_bound_explicit`. -/
theorem finite_set_energy_bound {S : Finset EuclideanPlane} {s t C δ : ℝ}
    (hs_pos : 0 < s) (hst : s < t) (hδ_pos : 0 < δ) (hC_pos : 0 < C)
    (hS_nonempty : S.Nonempty)
    (hS_sep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖)
    (hS_ball : ∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun q => ‖p - q‖ ≤ r)).card ≤ C * r^t * S.card) :
    ∃ (M : ℝ), planeEnergy ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)) s
      ≤ ENNReal.ofReal M :=
  ⟨1 + C * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)),
    finite_set_energy_bound_explicit hs_pos hst hδ_pos hC_pos hS_nonempty hS_sep hS_ball⟩

end

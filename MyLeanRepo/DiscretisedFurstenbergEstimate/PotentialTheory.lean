module

/-
  Potential theory infrastructure for the Kaufman projection lemma.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open Classical

namespace DiscretisedFurstenbergEstimate.PotentialTheory

open MeasureTheory Metric Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ### Riesz energy -/

noncomputable def rieszKernel (s : ℝ) (x y : Plane) : ENNReal :=
  if x = y then 0 else ((edist x y)^s)⁻¹

noncomputable def rieszEnergy (μ : Measure Plane) (s : ℝ) : ENNReal :=
  ∫⁻ x, ∫⁻ y, rieszKernel s x y ∂μ ∂μ

lemma rieszKernel_symm (s : ℝ) (x y : Plane) :
    rieszKernel s x y = rieszKernel s y x := by
  have h1 : x = y ↔ y = x := ⟨Eq.symm, Eq.symm⟩
  simp [rieszKernel, edist_comm, h1]

lemma rieszEnergy_restrict_le (μ : Measure Plane) (s : ℝ) (A : Set Plane) :
    rieszEnergy (μ.restrict A) s ≤ rieszEnergy μ s := by
  have h1 : ∀ x, ∫⁻ y, rieszKernel s x y ∂(μ.restrict A) ≤
                  ∫⁻ y, rieszKernel s x y ∂μ := by
    intro x
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  calc
    rieszEnergy (μ.restrict A) s
      = ∫⁻ x, ∫⁻ y, rieszKernel s x y ∂(μ.restrict A) ∂(μ.restrict A) := by rfl
    _ ≤ ∫⁻ x, ∫⁻ y, rieszKernel s x y ∂μ ∂(μ.restrict A) := by
        apply lintegral_mono; intro x; exact h1 x
    _ ≤ ∫⁻ x, ∫⁻ y, rieszKernel s x y ∂μ ∂μ := by
        exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ = rieszEnergy μ s := by rfl

/-- Helper: (ENNReal.ofReal d)^s = ENNReal.ofReal (d^s) for d > 0, s ≥ 0. -/
lemma ennreal_ofReal_rpow {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    (ENNReal.ofReal d)^s = ENNReal.ofReal (d ^ s) := by
  have h_nonneg : 0 ≤ d := by linarith
  have h_ne_top : (ENNReal.ofReal d)^s ≠ ⊤ := by
    simp [ENNReal.rpow_eq_top_iff, hs, h_nonneg]
  have h2 : ((ENNReal.ofReal d)^s).toReal = (ENNReal.ofReal d).toReal ^ s := by
    exact Eq.symm (ENNReal.toReal_rpow (ENNReal.ofReal d) s)
  have h3 : (ENNReal.ofReal d).toReal = d := by
    rw [ENNReal.toReal_ofReal h_nonneg]
  have h4 : ((ENNReal.ofReal d)^s).toReal = d ^ s := by
    rw [h2, h3]
  have h5 : (ENNReal.ofReal d)^s = ENNReal.ofReal (((ENNReal.ofReal d)^s).toReal) :=
    (ENNReal.ofReal_toReal h_ne_top).symm
  rw [h5, h4]

/-- Helper: (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal (x⁻¹) for x > 0. -/
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

lemma rieszKernel_ofReal {s : ℝ} {x y : Plane} (hne : x ≠ y) (hs : 0 ≤ s) :
    rieszKernel s x y = ENNReal.ofReal (‖x - y‖ ^ (-s)) := by
  have hpos : 0 < ‖x - y‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h1 : edist x y = ENNReal.ofReal ‖x - y‖ := by
    rw [edist_dist] <;> rfl
  rw [rieszKernel, if_neg hne]
  have h2 : (edist x y)^s = ENNReal.ofReal (‖x - y‖ ^ s) := by
    rw [h1]
    exact ennreal_ofReal_rpow hpos hs
  rw [h2]
  have hpos2 : 0 < ‖x - y‖ ^ s := by positivity
  rw [ennreal_ofReal_inv hpos2]
  have h4 : (‖x - y‖ ^ s)⁻¹ = ‖x - y‖ ^ (-s) := by
    rw [Real.rpow_neg (by positivity)] <;> ring
  rw [h4]

/-! ### Annulus index lemma -/

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
    have h11 : ((2 : ℝ)^((k : ℝ) + 1))⁻¹ < (1 / d)⁻¹ := by
      gcongr
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

theorem finite_set_energy_bound {S : Finset Plane} {s t C δ : ℝ}
    (hs_pos : 0 < s) (hst : s < t) (hδ_pos : 0 < δ) (hC_pos : 0 < C)
    (hS_nonempty : S.Nonempty)
    (hS_sep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖)
    (hS_ball : ∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun q => ‖p - q‖ ≤ r)).card ≤ C * r^t * S.card) :
    ∃ (M : ℝ), 0 < M ∧
      rieszEnergy ((S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set Plane)) s
      ≤ ENNReal.ofReal M := by
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
      apply div_le_div_of_nonneg_right
      <;> linarith
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
        have h11 : 0 < ‖p - q‖ := by
          have h12 : 0 < (2 : ℝ)^(-(k + 1 : ℝ)) := by positivity
          linarith
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
          rw [Finset.sum_congr rfl (fun k _ => h3 k), h_sum_factor]
      _ ≤ (S.card : ℝ) + C * (2 : ℝ)^s * (S.card : ℝ) * (1 / (1 - ratio)) := by
          gcongr; exact h_geom_sum K
      _ = M0 * (S.card : ℝ) := by
          simp only [M0] <;> ring

  let μ : Measure Plane := (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set Plane)
  have hS_card_pos : 0 < S.card := Finset.card_pos.mpr hS_nonempty

  have h_lintegral_finset : ∀ (f : Plane → ENNReal),
      ∫⁻ x, f x ∂(Measure.count.restrict (S : Set Plane)) = ∑ x ∈ S, f x := by
    have h_main : ∀ (T : Finset Plane), ∀ (f : Plane → ENNReal),
        ∫⁻ x, f x ∂(Measure.count.restrict (T : Set Plane)) = ∑ x ∈ T, f x := by
      intro T
      induction T using Finset.induction with
      | empty =>
        intro f
        have h_zero : Measure.count.restrict (∅ : Set Plane) = 0 := by
          ext A _
          simp
        have h : ∫⁻ x, f x ∂(Measure.count.restrict (∅ : Set Plane)) = 0 := by
          rw [h_zero]
          <;> simp
        simpa using h
      | @insert x T hx ih =>
        intro f
        have h_meas_eq : Measure.count.restrict (insert x T : Set Plane) =
            Measure.dirac x + Measure.count.restrict (T : Set Plane) := by
          ext A hA
          have h_fin : (A ∩ (T : Set Plane)).Finite := by
            apply Set.Finite.subset (Finset.finite_toSet T)
            simp
          have hs_mble : MeasurableSet (A ∩ (T : Set Plane)) := hA.inter (Finset.measurableSet T)
          have h_xnotin : x ∉ (A ∩ (T : Set Plane)) := by
            intro h
            exact hx h.2
          by_cases hxA : x ∈ A
          · have h_set : A ∩ (insert x T : Set Plane) = insert x (A ∩ (T : Set Plane)) := by
              ext y
              simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert, Set.mem_insert_iff]
              constructor
              · rintro ⟨hyA, (rfl | hyT)⟩
                · exact Or.inl rfl
                · exact Or.inr ⟨hyA, hyT⟩
              · rintro (rfl | ⟨hyA, hyT⟩)
                · exact ⟨hxA, Or.inl rfl⟩
                · exact ⟨hyA, Or.inr hyT⟩
            have h_fin2 : (insert x (A ∩ (T : Set Plane))).Finite := h_fin.insert x
            have h_mble2 : MeasurableSet (A ∩ (insert x T : Set Plane)) :=
              hA.inter (by simpa using Finset.measurableSet (insert x T))
            have h_mble2' : MeasurableSet (insert x (A ∩ (T : Set Plane))) := by
              rw [← h_set] <;> exact h_mble2
            let s' : Finset Plane := h_fin.toFinset
            have h_xnotin_s' : x ∉ s' := by
              simpa [s'] using h_xnotin
            have h_fin2_eq : h_fin2.toFinset = insert x s' := by
              ext z
              simp [h_fin2, s', Set.Finite.mem_toFinset, h_xnotin_s']
              <;> tauto
            have h_card2 : Measure.count (insert x (A ∩ (T : Set Plane))) =
                ↑(insert x s').card := by
              have h_tmp := MeasureTheory.Measure.count_apply_finite' h_fin2 h_mble2'
              rw [h_tmp, h_fin2_eq]
            have h_card : Measure.count (A ∩ (T : Set Plane)) = ↑(s'.card) :=
              MeasureTheory.Measure.count_apply_finite' h_fin hs_mble
            have h_indicator : A.indicator 1 x = 1 := by
              simp [Set.indicator_apply, hxA]
            simp only [Measure.restrict_apply hA, Measure.add_apply]
            rw [h_set, h_card2, h_card]
            have h_dirac : (Measure.dirac x) A = (1 : ENNReal) := by
              have h : (Measure.dirac x) A = Set.indicator A (1 : Plane → ENNReal) x :=
                Measure.dirac_apply' x hA
              rw [h]
              simp [Set.indicator_apply, hxA] <;> norm_num
            rw [h_dirac]
            have h_card_eq : (insert x s').card = s'.card + 1 := by
              simp [h_xnotin_s'] <;> omega
            rw [h_card_eq] <;> norm_cast <;> ring
          · have h_set : A ∩ (insert x T : Set Plane) = A ∩ (T : Set Plane) := by
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
              have h : (Measure.dirac x) A = Set.indicator A (1 : Plane → ENNReal) x :=
                Measure.dirac_apply' x hA
              rw [h]
              simp [Set.indicator_apply, hxA] <;> norm_num
            rw [h_dirac] <;> simp
        have h_goal : ∫⁻ y, f y ∂(Measure.count.restrict (insert x T : Set Plane)) =
            ∑ y ∈ insert x T, f y := by
          rw [h_meas_eq]
          rw [lintegral_add_measure]
          rw [ih f]
          have h_dirac : ∫⁻ y, f y ∂(Measure.dirac x) = f x := by
            rw [lintegral_dirac]
          rw [h_dirac, Finset.sum_insert hx] <;> ring
        simpa using h_goal
    exact h_main S

  have h1 : ∀ (x : Plane), ∫⁻ y, rieszKernel s x y ∂μ =
      (S.card : ENNReal)⁻¹ * ∑ y ∈ S, rieszKernel s x y := by
    intro x
    have h_main : ∫⁻ y, rieszKernel s x y ∂μ =
        (S.card : ENNReal)⁻¹ * ∫⁻ y, rieszKernel s x y ∂(Measure.count.restrict (S : Set Plane)) := by
      rw [lintegral_smul_measure] <;> rfl
    rw [h_main, h_lintegral_finset (rieszKernel s x)]

  have h2 : rieszEnergy μ s =
      (S.card : ENNReal)⁻¹ * ∑ x ∈ S, ∫⁻ y, rieszKernel s x y ∂μ := by
    have h_main : rieszEnergy μ s =
        (S.card : ENNReal)⁻¹ * ∫⁻ x, ∫⁻ y, rieszKernel s x y ∂μ ∂(Measure.count.restrict (S : Set Plane)) := by
      simp [rieszEnergy, μ, lintegral_smul_measure] <;> rfl
    rw [h_main, h_lintegral_finset (fun x => ∫⁻ y, rieszKernel s x y ∂μ)]
  rw [h2]
  have h3 : ∑ x ∈ S, ∫⁻ y, rieszKernel s x y ∂μ =
      (S.card : ENNReal)⁻¹ * ∑ x ∈ S, ∑ y ∈ S, rieszKernel s x y := by
    rw [Finset.sum_congr rfl (fun x _ => h1 x)]
    <;> rw [Finset.mul_sum] <;> ring
  rw [h3]
  have h4 : ∀ x ∈ S, ∑ y ∈ S, rieszKernel s x y =
      ENNReal.ofReal (∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) := by
    intro x hx
    have h5 : ∑ y ∈ S, rieszKernel s x y = ∑ y ∈ S.erase x, rieszKernel s x y := by
      have h51 : insert x (S.erase x) = S := by
        rw [Finset.insert_erase hx]
      have h53 : x ∉ S.erase x := by simp
      have h2 : ∑ y ∈ insert x (S.erase x), rieszKernel s x y =
          rieszKernel s x x + ∑ y ∈ S.erase x, rieszKernel s x y := by
        rw [Finset.sum_insert h53]
      have h52 : rieszKernel s x x = 0 := by
        rw [rieszKernel, if_pos rfl]
      have h4 : ∑ y ∈ S, rieszKernel s x y = ∑ y ∈ insert x (S.erase x), rieszKernel s x y := by
        congr
        <;> exact h51.symm
      rw [h4, h2, h52] <;> ring
    rw [h5]
    have h_eq : ∀ y ∈ S.erase x, rieszKernel s x y = ENNReal.ofReal (‖x - y‖ ^ (-s)) := by
      intro y hy
      have h6 : y ≠ x := by
        simp only [Finset.mem_erase] at hy; exact hy.1
      exact rieszKernel_ofReal h6.symm (by linarith)
    have h_sum : ∑ y ∈ S.erase x, rieszKernel s x y =
        ∑ y ∈ S.erase x, ENNReal.ofReal (‖x - y‖ ^ (-s)) :=
      Finset.sum_congr rfl h_eq
    rw [h_sum]
    have h_nonneg : ∀ y ∈ S.erase x, 0 ≤ ‖x - y‖ ^ (-s) := by
      intro y _; positivity
    have h_ofReal_sum : ENNReal.ofReal (∑ y ∈ S.erase x, (‖x - y‖ ^ (-s) : ℝ)) =
        ∑ y ∈ S.erase x, ENNReal.ofReal (‖x - y‖ ^ (-s) : ℝ) := by
      exact ENNReal.ofReal_sum_of_nonneg h_nonneg
    rw [h_ofReal_sum]
  have h5 : ∑ x ∈ S, ∑ y ∈ S, rieszKernel s x y =
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
  exact ⟨M0, hM0_pos, h_final⟩

/-! ### Content to δ-S set via Frostman + dyadic selection -/

/-- From a Frostman probability measure with ball growth, the dyadic cubes
    intersecting the support form a weighted set with the same ball growth
    property (up to an additive δ in the radius).

    This is the core of `content_to_delta_set`:
    positive Hausdorff content → Frostman measure → weighted dyadic δ-S set.
-/
theorem frostman_to_dyadic_weighted {n : ℕ} {P : Set Plane} {C s : ℝ}
    (hP_bounded : Bornology.IsBounded P)
    (hP_meas : MeasurableSet P)
    (μ : Measure Plane) (hμ_univ : μ Set.univ = 1)
    (hμ_support : μ Pᶜ = 0)
    (hs_nonneg : 0 ≤ s) (hC_nonneg : 0 ≤ C)
    (h_ball : ∀ (x : Plane) (r : ℝ), 0 < r →
      μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ s)) :
    ∃ (Q : Finset (DyadicCubes.DyadicCube n)),
      (∑ q ∈ Q, μ q.toSet = 1) ∧
      ∀ (x : Plane) (r : ℝ), DyadicCubes.dyadicDelta n ≤ r →
        ∑ q ∈ Q.filter (fun q => q.center ∈ closedBall x r), μ q.toSet
        ≤ ENNReal.ofReal (C * (r + DyadicCubes.dyadicDelta n) ^ s) := by
  let δ := DyadicCubes.dyadicDelta n
  let Q : Finset (DyadicCubes.DyadicCube n) :=
    DyadicCubes.D_nFinset n P hP_bounded
  have hδ_pos : 0 < δ := DyadicCubes.dyadicDelta_pos n
  have h_disj : ∀ (q1 q2 : DyadicCubes.DyadicCube n), q1 ≠ q2 →
      Disjoint (q1.toSet) (q2.toSet) := by
    intro q1 q2 hne
    exact DyadicCubes.DyadicCube.disjoint_of_ne hne
  have h_meas : ∀ (q : DyadicCubes.DyadicCube n), MeasurableSet q.toSet := by
    intro q
    have hproj0 : Measurable (fun x : Plane => x 0) := by fun_prop
    have hproj1 : Measurable (fun x : Plane => x 1) := by fun_prop
    have h1 : MeasurableSet {x : Plane | x 0 ∈ Set.Ico (q.i * q.side) ((q.i + 1) * q.side)} :=
      measurableSet_Ico.preimage hproj0
    have h2 : MeasurableSet {x : Plane | x 1 ∈ Set.Ico (q.j * q.side) ((q.j + 1) * q.side)} :=
      measurableSet_Ico.preimage hproj1
    have h3 : q.toSet = {x : Plane | x 0 ∈ Set.Ico (q.i * q.side) ((q.i + 1) * q.side)} ∩
        {x : Plane | x 1 ∈ Set.Ico (q.j * q.side) ((q.j + 1) * q.side)} := by
      ext x
      simp [DyadicCubes.DyadicCube.toSet, Set.mem_inter_iff]
      <;> tauto
    rw [h3]
    exact MeasurableSet.inter h1 h2
  have h_cover_P : P ⊆ ⋃ q ∈ Q, q.toSet := by
    intro p hp
    have h_univ : (⋃ (i : ℤ) (j : ℤ),
        (⟨i, j⟩ : DyadicCubes.DyadicCube n).toSet) = Set.univ :=
      DyadicCubes.DyadicCube.cover n
    have h_p_in : p ∈ (⋃ (i : ℤ) (j : ℤ),
        (⟨i, j⟩ : DyadicCubes.DyadicCube n).toSet) := by
      rw [h_univ] <;> trivial
    rcases Set.mem_iUnion₂.mp h_p_in with ⟨i, j, hq⟩
    let q : DyadicCubes.DyadicCube n := ⟨i, j⟩
    have hqQ : q ∈ Q := by
      rw [DyadicCubes.D_nFinset_mem]
      exact ⟨p, hq, hp⟩
    exact Set.mem_iUnion₂.mpr ⟨q, hqQ, hq⟩
  have h2 : μ P + μ Pᶜ = μ Set.univ := by
    rw [← measure_union disjoint_compl_right hP_meas.compl] <;> simp
  have hμP : μ P = 1 := by
    rw [hμ_support, hμ_univ] at h2 <;> simpa using h2
  have h4 : μ P ≤ μ (⋃ q ∈ Q, q.toSet) := measure_mono h_cover_P
  have h5 : μ (⋃ q ∈ Q, q.toSet) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  have h6 : μ (⋃ q ∈ Q, q.toSet) = 1 := by
    have h7 : 1 ≤ μ (⋃ q ∈ Q, q.toSet) := by
      calc (1 : ENNReal) = μ P := hμP.symm
        _ ≤ μ (⋃ q ∈ Q, q.toSet) := h4
    have h8 : μ (⋃ q ∈ Q, q.toSet) ≤ 1 := by
      calc μ (⋃ q ∈ Q, q.toSet) ≤ μ Set.univ := h5
        _ = 1 := hμ_univ
    exact le_antisymm h8 h7
  have h1 : μ (⋃ q ∈ Q, q.toSet) = ∑ q ∈ Q, μ q.toSet := by
    exact MeasureTheory.measure_biUnion_finset
      (fun q1 _ q2 _ hne => h_disj q1 q2 hne)
      (fun q _ => h_meas q)
  have h_total : ∑ q ∈ Q, μ q.toSet = 1 := by
    rw [← h1, h6]
  have h_growth : ∀ (x : Plane) (r : ℝ), δ ≤ r →
      ∑ q ∈ Q.filter (fun q => q.center ∈ closedBall x r), μ q.toSet
      ≤ ENNReal.ofReal (C * (r + δ) ^ s) := by
    intro x r hr
    let Q' := Q.filter (fun q => q.center ∈ closedBall x r)
    have h1 : ∀ q ∈ Q', q.toSet ⊆ closedBall x (r + δ) := by
      intro q hq
      have hqc : q.center ∈ closedBall x r := (Finset.mem_filter.mp hq).2
      intro y hy
      have h2 : dist y q.center ≤ δ := DyadicCubes.DyadicCube.dist_center_le hy
      have h3 : dist q.center x ≤ r := Metric.mem_closedBall.mp hqc
      have h4 : dist y x ≤ r + δ := by
        calc dist y x ≤ dist y q.center + dist q.center x := dist_triangle y q.center x
          _ ≤ δ + r := by linarith
          _ = r + δ := by ring
      exact Metric.mem_closedBall.mpr h4
    have h_union : (⋃ q ∈ Q', q.toSet) ⊆ closedBall x (r + δ) := by
      intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨q, hq, hyq⟩
      exact h1 q hq hyq
    have h_sum : μ (⋃ q ∈ Q', q.toSet) = ∑ q ∈ Q', μ q.toSet := by
      exact MeasureTheory.measure_biUnion_finset
        (fun q1 _ q2 _ hne => h_disj q1 q2 hne)
        (fun q _ => h_meas q)
    have h5 : 0 < r + δ := by
      have h6 : 0 ≤ r := le_trans hδ_pos.le hr
      linarith
    calc
      ∑ q ∈ Q', μ q.toSet
        = μ (⋃ q ∈ Q', q.toSet) := h_sum.symm
      _ ≤ μ (closedBall x (r + δ)) := measure_mono h_union
      _ ≤ ENNReal.ofReal (C * (r + δ) ^ s) := h_ball x (r + δ) h5
  exact ⟨Q, h_total, h_growth⟩

/-! ### Energy to content (energy-capacity inequality) -/

/-- For a non-atomic measure, the Riesz energy contribution from within a set T
    is at least `μ(T)^2 / (ediam T)^s`. -/
lemma energy_within_set {μ : Measure Plane} [MeasureTheory.NoAtoms μ] {s : ℝ} (hs_pos : 0 < s)
    {T : Set Plane} (hT_meas : MeasurableSet T) :
    ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict T)) ∂(μ.restrict T)
    ≥ ((ediam T)^s)⁻¹ * (μ T)^2 := by
  let d : ENNReal := (ediam T)^s
  have h_restrict_univ : (μ.restrict T) Set.univ = μ T := by
    have h : (μ.restrict T) Set.univ = μ (Set.univ ∩ T) :=
      Measure.restrict_apply MeasurableSet.univ
    rw [h, Set.univ_inter]
  have h1 : ∀ (x : Plane), x ∈ T →
      ∫⁻ y, rieszKernel s x y ∂(μ.restrict T) ≥ d⁻¹ * μ T := by
    intro x hx
    have h_singleton : μ {x} = 0 := by exact measure_singleton x
    have h_restrict_singleton : (μ.restrict T) {x} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton x)]
      have h7 : ({x} ∩ T) ⊆ ({x} : Set Plane) := by simp
      have h8 : μ ({x} ∩ T) ≤ μ {x} := measure_mono h7
      have h9 : μ {x} = 0 := h_singleton
      have h10 : μ ({x} ∩ T) ≤ 0 := by
        rw [h9] at h8
        exact h8
      have h11 : μ ({x} ∩ T) = 0 := by
        exact le_zero_iff.mp h10
      exact h11
    have h_ne_x : ∀ᵐ (y : Plane) ∂(μ.restrict T), y ≠ x := by
      have h9 : ∀ᵐ (y : Plane) ∂(μ.restrict T), y ∉ ({x} : Set Plane) := by exact Measure.ae_ne (μ.restrict T) x
      filter_upwards [h9] with y hy
      simpa using hy
    have h2 : ∀ (y : Plane), y ∈ T → y ≠ x → rieszKernel s x y ≥ d⁻¹ := by
      intro y hy hyne
      have hne' : x ≠ y := hyne.symm
      have h_kernel : rieszKernel s x y = ((edist x y)^s)⁻¹ := by
        rw [rieszKernel, if_neg hne']
      rw [h_kernel]
      have h4 : edist x y ≤ ediam T := Metric.edist_le_ediam_of_mem hx hy
      have h5 : (edist x y)^s ≤ (ediam T)^s := by gcongr <;> linarith
      have h6 : d⁻¹ ≤ ((edist x y)^s)⁻¹ := by exact ENNReal.inv_le_inv.mpr h5
      exact h6
    have h3 : ∀ᵐ (y : Plane) ∂(μ.restrict T), rieszKernel s x y ≥ d⁻¹ := by
      filter_upwards [ae_restrict_mem hT_meas, h_ne_x] with y hy hyx
      exact h2 y hy hyx
    have h4 : ∫⁻ y, rieszKernel s x y ∂(μ.restrict T) ≥ ∫⁻ y, d⁻¹ ∂(μ.restrict T) :=
      lintegral_mono_ae h3
    have h5 : ∫⁻ y, d⁻¹ ∂(μ.restrict T) = d⁻¹ * μ T := by
      rw [lintegral_const, h_restrict_univ]
    have h6 : ∫⁻ y, rieszKernel s x y ∂(μ.restrict T) ≥ d⁻¹ * μ T := by
      calc
        ∫⁻ y, rieszKernel s x y ∂(μ.restrict T)
          ≥ ∫⁻ y, d⁻¹ ∂(μ.restrict T) := h4
        _ = d⁻¹ * μ T := h5
    exact h6
  have h_main_ae : ∀ᵐ (x : Plane) ∂(μ.restrict T),
      (∫⁻ y, rieszKernel s x y ∂(μ.restrict T)) ≥ d⁻¹ * μ T := by
    filter_upwards [ae_restrict_mem hT_meas] with x hx
    exact h1 x hx
  have h_main : ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict T)) ∂(μ.restrict T)
      ≥ ∫⁻ x, d⁻¹ * μ T ∂(μ.restrict T) :=
    lintegral_mono_ae h_main_ae
  have h5 : ∫⁻ x, d⁻¹ * μ T ∂(μ.restrict T) = d⁻¹ * (μ T)^2 := by
    rw [lintegral_const, h_restrict_univ] <;> ring
  have h6 : ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict T)) ∂(μ.restrict T)
      ≥ d⁻¹ * (μ T)^2 := by
    calc
      ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict T)) ∂(μ.restrict T)
        ≥ ∫⁻ x, d⁻¹ * μ T ∂(μ.restrict T) := h_main
      _ = d⁻¹ * (μ T)^2 := h5
  exact h6

/-- Titu's lemma (Cauchy-Schwarz) for ENNReal sums over a finset:
    `∑ a_i^2 / b_i ≥ (∑ a_i)^2 / ∑ b_i`. -/
lemma titu_ennreal {α : Type*} {s : Finset α} {a b : α → ENNReal}
    (hb_pos : ∀ i ∈ s, 0 < b i) (hb_top : (∑ i ∈ s, b i) ≠ ⊤) :
    (∑ i ∈ s, a i * a i * (b i)⁻¹) ≥ (∑ i ∈ s, a i)^2 * (∑ i ∈ s, b i)⁻¹ := by
  by_cases hs_empty : s = ∅
  · rw [hs_empty] <;> simp
  · have hs_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
    rcases hs_nonempty with ⟨i0, hi0⟩
    by_cases ha_top : (∑ i ∈ s, a i) = ⊤
    · have h_exists : ∃ i ∈ s, a i = ⊤ := ENNReal.sum_eq_top.mp ha_top
      rcases h_exists with ⟨i, hi, hxi⟩
      have hbi_ne_top : b i ≠ ⊤ := by
        have h_le : ∀ j ∈ s, (0 : ENNReal) ≤ b j := by intro j _; positivity
        have h : b i ≤ ∑ j ∈ s, b j := Finset.single_le_sum h_le hi
        exact ne_top_of_le_ne_top hb_top h
      have h2 : a i * a i * (b i)⁻¹ = ⊤ := by
        rw [hxi]
        have h3 : (b i)⁻¹ ≠ 0 := by
          intro h4
          have h5 : b i = ⊤ := by simpa [ENNReal.inv_eq_zero] using h4
          exact hbi_ne_top h5
        simp [h3, ENNReal.mul_eq_top]
      have h_le : a i * a i * (b i)⁻¹ ≤ ∑ j ∈ s, a j * a j * (b j)⁻¹ :=
        Finset.single_le_sum (fun j _ => show 0 ≤ a j * a j * (b j)⁻¹ from by positivity) hi
      have h3 : (∑ j ∈ s, a j * a j * (b j)⁻¹) = ⊤ := by
        rw [h2] at h_le; exact top_le_iff.mp h_le
      rw [h3] <;> simp
    · have ha_top' : (∑ i ∈ s, a i) ≠ ⊤ := ha_top
      have all_a_finite : ∀ i ∈ s, a i ≠ ⊤ := by
        intro i hi
        have h_le : ∀ j ∈ s, (0 : ENNReal) ≤ a j := by intro j _; positivity
        have h : a i ≤ ∑ j ∈ s, a j := Finset.single_le_sum h_le hi
        exact ne_top_of_le_ne_top ha_top' h
      have all_b_finite : ∀ i ∈ s, b i ≠ ⊤ := by
        intro i hi
        have h_le : ∀ j ∈ s, (0 : ENNReal) ≤ b j := by intro j _; positivity
        have h : b i ≤ ∑ j ∈ s, b j := Finset.single_le_sum h_le hi
        exact ne_top_of_le_ne_top hb_top h
      let A : ℝ := (∑ i ∈ s, a i).toReal
      let B : ℝ := (∑ i ∈ s, b i).toReal
      have h_sum_b_pos : 0 < ∑ i ∈ s, b i := by
        have h_le : ∀ j ∈ s, (0 : ENNReal) ≤ b j := by intro j _; positivity
        have h : b i0 ≤ ∑ j ∈ s, b j := Finset.single_le_sum h_le hi0
        exact lt_of_lt_of_le (hb_pos i0 hi0) h
      have hB_pos : 0 < B := ENNReal.toReal_pos (ne_of_gt h_sum_b_pos) hb_top
      have hb_real_pos : ∀ i ∈ s, 0 < (b i).toReal := by
        intro i hi
        have hne : b i ≠ 0 := ne_of_gt (hb_pos i hi)
        exact ENNReal.toReal_pos hne (all_b_finite i hi)
      let f : α → ℝ := fun i => (a i).toReal / Real.sqrt ((b i).toReal)
      let g : α → ℝ := fun i => Real.sqrt ((b i).toReal)
      have hfg : ∀ i ∈ s, f i * g i = (a i).toReal := by
        intro i hi
        have hbi : 0 < (b i).toReal := hb_real_pos i hi
        simp [f, g, Real.sqrt_pos.mpr hbi] <;> field_simp <;> ring
      have hf2 : ∀ i ∈ s, (f i)^2 = ((a i).toReal)^2 / (b i).toReal := by
        intro i hi
        have hbi : 0 ≤ (b i).toReal := by linarith [hb_real_pos i hi]
        calc
          (f i)^2
            = (((a i).toReal) / Real.sqrt ((b i).toReal))^2 := by rfl
          _ = ((a i).toReal)^2 / (Real.sqrt ((b i).toReal))^2 := by rw [div_pow]
          _ = ((a i).toReal)^2 / (b i).toReal := by rw [Real.sq_sqrt hbi]
      have hg2 : ∀ i ∈ s, (g i)^2 = (b i).toReal := by
        intro i hi
        have hbi : 0 ≤ (b i).toReal := by linarith [hb_real_pos i hi]
        simp [g, Real.sq_sqrt hbi]
      have hcs : (∑ i ∈ s, f i * g i)^2 ≤ (∑ i ∈ s, (f i)^2) * (∑ i ∈ s, (g i)^2) :=
        Finset.sum_mul_sq_le_sq_mul_sq s f g
      have hsum_fg : ∑ i ∈ s, f i * g i = ∑ i ∈ s, (a i).toReal := by
        apply Finset.sum_congr rfl; intro i hi; exact hfg i hi
      have hsum_f2 : ∑ i ∈ s, (f i)^2 = ∑ i ∈ s, ((a i).toReal)^2 / (b i).toReal := by
        apply Finset.sum_congr rfl; intro i hi; exact hf2 i hi
      have hsum_g2 : ∑ i ∈ s, (g i)^2 = ∑ i ∈ s, (b i).toReal := by
        apply Finset.sum_congr rfl; intro i hi; exact hg2 i hi
      rw [hsum_fg, hsum_f2, hsum_g2] at hcs
      have hB_pos' : 0 < ∑ i ∈ s, (b i).toReal := by
        have h_le : ∀ j ∈ s, (0 : ℝ) ≤ (b j).toReal := by intro j _; positivity
        have h : (b i0).toReal ≤ ∑ j ∈ s, (b j).toReal := Finset.single_le_sum h_le hi0
        exact lt_of_lt_of_le (hb_real_pos i0 hi0) h
      have hA : A = ∑ i ∈ s, (a i).toReal := by
        dsimp only [A]; exact ENNReal.toReal_sum all_a_finite
      have hB : B = ∑ i ∈ s, (b i).toReal := by
        dsimp only [B]; exact ENNReal.toReal_sum all_b_finite
      have h_main_real : ∑ i ∈ s, ((a i).toReal)^2 / (b i).toReal ≥ A^2 / B := by
        rw [hA, hB]
        have h_pos2 : 0 < ∑ i ∈ s, (b i).toReal := hB_pos'
        have h : (∑ i ∈ s, (a i).toReal)^2 ≤ (∑ i ∈ s, ((a i).toReal)^2 / (b i).toReal) * (∑ i ∈ s, (b i).toReal) := hcs
        set X := ∑ i ∈ s, ((a i).toReal)^2 / (b i).toReal with hX
        set Y := ∑ i ∈ s, (b i).toReal with hY
        have h' : X ≥ (∑ i ∈ s, (a i).toReal)^2 / Y := by
          have h_eq : X = (X * Y) / Y := by
            field_simp [h_pos2.ne'] <;> ring
          rw [h_eq]
          gcongr
        exact h'
      have all_prod_finite : ∀ i ∈ s, (a i * a i * (b i)⁻¹) ≠ ⊤ := by
        intro i hi
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (all_a_finite i hi) (all_a_finite i hi))
          (ENNReal.inv_ne_top.mpr (ne_of_gt (hb_pos i hi)))
      have hLHS_real : (∑ i ∈ s, a i * a i * (b i)⁻¹).toReal = ∑ i ∈ s, ((a i).toReal)^2 / (b i).toReal := by
        rw [ENNReal.toReal_sum all_prod_finite]
        apply Finset.sum_congr rfl; intro i hi
        have h6 : (a i * a i * (b i)⁻¹).toReal = (a i).toReal^2 / (b i).toReal := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_inv, all_a_finite i hi, all_b_finite i hi] <;> ring
        exact h6
      have hR1 : (∑ i ∈ s, a i)^2 ≠ ⊤ := ENNReal.pow_ne_top ha_top'
      have h_sum_b_ne_zero : (∑ i ∈ s, b i) ≠ 0 := ne_of_gt h_sum_b_pos
      have hR2 : (∑ i ∈ s, b i)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h_sum_b_ne_zero
      have hRHS_finite : ((∑ i ∈ s, a i)^2 * (∑ i ∈ s, b i)⁻¹) ≠ ⊤ := ENNReal.mul_ne_top hR1 hR2
      have hLHS_finite : (∑ i ∈ s, a i * a i * (b i)⁻¹) ≠ ⊤ := ENNReal.sum_ne_top.mpr all_prod_finite
      have h_pow2 : ((∑ i ∈ s, a i)^2).toReal = A^2 := by
        have h : (∑ i ∈ s, a i)^2 = (∑ i ∈ s, a i) * (∑ i ∈ s, a i) := by ring
        rw [h]
        rw [ENNReal.toReal_mul]
        <;> simp [A, ENNReal.toReal_sum, all_a_finite] <;> ring
      have h_inv : ((∑ i ∈ s, b i)⁻¹).toReal = B⁻¹ := by
        rw [ENNReal.toReal_inv] <;> simp [B]
      have h8 : (((∑ i ∈ s, a i)^2 * (∑ i ∈ s, b i)⁻¹).toReal) = A^2 / B := by
        rw [ENNReal.toReal_mul, h_pow2, h_inv] <;> ring
      have h4 : (∑ i ∈ s, a i * a i * (b i)⁻¹).toReal ≥ (((∑ i ∈ s, a i)^2 * (∑ i ∈ s, b i)⁻¹).toReal) := by
        rw [hLHS_real, h8]; exact h_main_real
      exact (ENNReal.toReal_le_toReal hRHS_finite hLHS_finite).mp h4

/-- Energy-capacity inequality: bounded s-energy implies positive Hausdorff content.

    For a non-atomic probability measure μ supported on A with `I_s(μ) ≤ M`,
    any finite disjoint measurable cover of A has total `ediam^s` cost at least `1/M`.
    This is the core of `energy_to_content`. -/
theorem energy_to_content_finite {μ : Measure Plane} [MeasureTheory.NoAtoms μ]
    {s M : ℝ} (hs_pos : 0 < s) (hM_pos : 0 < M)
    (hμ_univ : μ Set.univ = 1)
    (h_energy : rieszEnergy μ s ≤ ENNReal.ofReal M)
    {A : Set Plane} (hA_meas : MeasurableSet A) (hμA : μ A = 1)
    {α : Type*} [Fintype α] {T : α → Set Plane}
    (hT_meas : ∀ i, MeasurableSet (T i))
    (h_disj : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (h_cover : A ⊆ ⋃ i, T i) :
    (∑ i : α, (ediam (T i))^s) ≥ (ENNReal.ofReal M)⁻¹ := by
  have h1_top : ∀ i, μ (T i) ≠ ⊤ := by
    intro i
    have h2 : μ (T i) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [hμ_univ] at h2
    exact ne_top_of_le_ne_top (by simp) h2
  let s_univ : Finset α := Finset.univ
  have hd_univ : (↑s_univ : Set α).PairwiseDisjoint T := by
    intro i _ j _ hne; exact h_disj i j hne
  have h_univ_eq : (⋃ i ∈ s_univ, T i) = (⋃ i : α, T i) := by
    ext x; simp [s_univ]
  have h_sum1 : ∑ i : α, μ (T i) ≥ 1 := by
    have h2 : μ (⋃ i ∈ s_univ, T i) = ∑ i ∈ s_univ, μ (T i) :=
      MeasureTheory.measure_biUnion_finset hd_univ (fun i _ => hT_meas i)
    have h3 : μ A ≤ μ (⋃ i ∈ s_univ, T i) := by
      rw [h_univ_eq]
      exact measure_mono h_cover
    rw [hμA] at h3
    rw [h2] at h3
    simpa [s_univ] using h3
  let U := ⋃ i : α, T i
  have hU_meas : MeasurableSet U := MeasurableSet.iUnion hT_meas
  have h_restrict_sum : μ.restrict U = ∑ i : α, μ.restrict (T i) := by
    apply Measure.ext
    intro S hS
    simp only [Measure.restrict_apply hS, Finset.sum_apply]
    have hd2 : (↑s_univ : Set α).PairwiseDisjoint (fun i => S ∩ T i) := by
      intro i _ j _ hne
      have h1 : S ∩ T i ⊆ T i := by intro x hx; exact hx.2
      have h2 : S ∩ T j ⊆ T j := by intro x hx; exact hx.2
      exact (h_disj i j hne).mono h1 h2
    have h_eq : S ∩ U = ⋃ i ∈ s_univ, S ∩ T i := by
      ext x
      have h1 : x ∈ S ∩ U ↔ ∃ (i : α), x ∈ S ∧ x ∈ T i := by
        simp [U, Set.mem_inter_iff] <;> tauto
      have h2 : x ∈ (⋃ i ∈ s_univ, S ∩ T i) ↔ ∃ (i : α), x ∈ S ∧ x ∈ T i := by
        simp [s_univ, Set.mem_inter_iff] <;> tauto
      rw [h1, h2]
    have h_meas : μ (⋃ i ∈ s_univ, S ∩ T i) = ∑ i ∈ s_univ, μ (S ∩ T i) :=
      MeasureTheory.measure_biUnion_finset hd2 (fun i _ => hS.inter (hT_meas i))
    have h_goal : μ (S ∩ U) = ∑ i ∈ s_univ, μ (S ∩ T i) := by
      rw [h_eq]
      exact h_meas
    have h_sum : (∑ i : α, μ.restrict (T i)) S = ∑ i ∈ s_univ, μ (S ∩ T i) := by
      simp [Finset.sum_apply, Measure.restrict_apply hS]
      <;> rfl
    rw [h_goal, h_sum]
  let F : Plane → ENNReal := fun x => ∫⁻ y, rieszKernel s x y ∂μ
  have h1 : ∫⁻ x, F x ∂(μ.restrict U) ≤ rieszEnergy μ s := by
    have hle : μ.restrict U ≤ μ := Measure.restrict_le_self
    exact lintegral_mono' hle (le_refl F)
  have h_sum_meas : Measure.sum (fun i : α => μ.restrict (T i)) = ∑ i : α, μ.restrict (T i) := by
    simp [Measure.sum_fintype]
  have h2 : ∫⁻ x, F x ∂(μ.restrict U) = ∑ i : α, ∫⁻ x, F x ∂(μ.restrict (T i)) := by
    rw [h_restrict_sum, ← h_sum_meas]
    have h := MeasureTheory.lintegral_sum_measure F (fun i : α => μ.restrict (T i))
    simpa [tsum_fintype] using h
  have h3 : ∀ i : α, ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict (T i))) ∂(μ.restrict (T i))
      ≤ ∫⁻ x, F x ∂(μ.restrict (T i)) := by
    intro i
    have h31 : ∀ (x : Plane), ∫⁻ y, rieszKernel s x y ∂(μ.restrict (T i)) ≤ F x := by
      intro x
      have hle : μ.restrict (T i) ≤ μ := Measure.restrict_le_self
      exact lintegral_mono' hle (le_refl _)
    exact lintegral_mono h31
  have h_energy_decomp : rieszEnergy μ s ≥
      ∑ i : α, ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict (T i))) ∂(μ.restrict (T i)) := by
    calc
      ∑ i : α, ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict (T i))) ∂(μ.restrict (T i))
        ≤ ∑ i : α, ∫⁻ x, F x ∂(μ.restrict (T i)) := by
          apply Finset.sum_le_sum
          intro i _
          exact h3 i
      _ = ∫⁻ x, F x ∂(μ.restrict U) := h2.symm
      _ ≤ rieszEnergy μ s := h1
  have h4 : ∀ i, ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict (T i))) ∂(μ.restrict (T i))
      ≥ ((ediam (T i))^s)⁻¹ * (μ (T i))^2 :=
    fun i => energy_within_set hs_pos (hT_meas i)
  have h5 : rieszEnergy μ s ≥ ∑ i : α, ((ediam (T i))^s)⁻¹ * (μ (T i))^2 := by
    calc
      rieszEnergy μ s
        ≥ ∑ i : α, ∫⁻ x, (∫⁻ y, rieszKernel s x y ∂(μ.restrict (T i))) ∂(μ.restrict (T i)) := h_energy_decomp
      _ ≥ ∑ i : α, ((ediam (T i))^s)⁻¹ * (μ (T i))^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact h4 i
  by_cases h_top : (∑ i : α, (ediam (T i))^s) = ⊤
  · rw [h_top] <;> simp
  · have h6 : (∑ i : α, (ediam (T i))^s) ≠ ⊤ := h_top
    let S : Finset α := Finset.univ.filter (fun i => 0 < ediam (T i))
    have hS_pos : ∀ i ∈ S, 0 < ediam (T i) := by
      intro i hi; exact (Finset.mem_filter.mp hi).2
    have h_ediam_zero_imp_μ_zero : ∀ (i : α), ediam (T i) = 0 → μ (T i) = 0 := by
      intro i hEdiam
      have h_sub : Set.Subsingleton (T i) := by
        intro x hx y hy
        have h_dist : edist x y ≤ ediam (T i) := Metric.edist_le_ediam_of_mem hx hy
        rw [hEdiam] at h_dist
        have h_eq : edist x y = 0 := by simpa using h_dist
        exact edist_eq_zero.mp h_eq
      by_cases h_empty : (T i).Nonempty
      · rcases h_empty with ⟨x, hx⟩
        have h_eq_set : T i = {x} := by
          apply Set.Subset.antisymm
          · intro y hy; exact h_sub hy hx
          · simp [hx]
        rw [h_eq_set]
        have h_atom : μ {x} = 0 := by exact measure_singleton x
        exact h_atom
      · have hTi : T i = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h_empty
        rw [hTi, measure_empty]
    have h_sum_μ : ∑ i ∈ S, μ (T i) = ∑ i : α, μ (T i) := by
      rw [Finset.sum_subset (Finset.filter_subset _ _)]
      intro i _ hni
      have h_not_pos : ¬(0 < ediam (T i)) := by simpa [S, Finset.mem_filter] using hni
      have h_ediam_zero : ediam (T i) = 0 := by simpa using h_not_pos
      exact h_ediam_zero_imp_μ_zero i h_ediam_zero
    have h_sum_ediam : ∑ i ∈ S, (ediam (T i))^s = ∑ i : α, (ediam (T i))^s := by
      rw [Finset.sum_subset (Finset.filter_subset _ _)]
      intro i _ hni
      have h_not_pos : ¬(0 < ediam (T i)) := by simpa [S, Finset.mem_filter] using hni
      have h_ediam_zero : ediam (T i) = 0 := by simpa using h_not_pos
      rw [h_ediam_zero]; simp [hs_pos]
    have h_sum_energy : ∑ i ∈ S, ((ediam (T i))^s)⁻¹ * (μ (T i))^2 = ∑ i : α, ((ediam (T i))^s)⁻¹ * (μ (T i))^2 := by
      rw [Finset.sum_subset (Finset.filter_subset _ _)]
      intro i _ hni
      have h_not_pos : ¬(0 < ediam (T i)) := by simpa [S, Finset.mem_filter] using hni
      have h_ediam_zero : ediam (T i) = 0 := by simpa using h_not_pos
      have h_μ_zero : μ (T i) = 0 := h_ediam_zero_imp_μ_zero i h_ediam_zero
      rw [h_ediam_zero, h_μ_zero] <;> simp
    have h_pos : ∀ i ∈ S, 0 < (ediam (T i))^s := by
      intro i hi
      have h7 : 0 < ediam (T i) := hS_pos i hi
      positivity
    have h6_S : (∑ i ∈ S, (ediam (T i))^s) ≠ ⊤ := by
      rw [h_sum_ediam]; exact h6
    have h_titu := titu_ennreal (s := S) (a := fun i => μ (T i)) (b := fun i => (ediam (T i))^s) h_pos h6_S
    have h7 : (∑ i ∈ S, (μ (T i))^2 * ((ediam (T i))^s)⁻¹) ≥
        (∑ i ∈ S, μ (T i))^2 * (∑ i ∈ S, (ediam (T i))^s)⁻¹ := by
      have h_eq : ∑ i ∈ S, μ (T i) * μ (T i) * ((ediam (T i))^s)⁻¹ =
          ∑ i ∈ S, (μ (T i))^2 * ((ediam (T i))^s)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [← h_eq]
      exact h_titu
    have h8 : (∑ i ∈ S, (μ (T i))^2 * ((ediam (T i))^s)⁻¹) =
        ∑ i ∈ S, ((ediam (T i))^s)⁻¹ * (μ (T i))^2 := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [h8] at h7
    have h9 : (∑ i : α, μ (T i))^2 * (∑ i : α, (ediam (T i))^s)⁻¹ ≤ ENNReal.ofReal M := by
      calc
        (∑ i : α, μ (T i))^2 * (∑ i : α, (ediam (T i))^s)⁻¹
          = (∑ i ∈ S, μ (T i))^2 * (∑ i ∈ S, (ediam (T i))^s)⁻¹ := by
            rw [h_sum_μ, h_sum_ediam]
        _ ≤ ∑ i ∈ S, ((ediam (T i))^s)⁻¹ * (μ (T i))^2 := h7
        _ = ∑ i : α, ((ediam (T i))^s)⁻¹ * (μ (T i))^2 := h_sum_energy
        _ ≤ rieszEnergy μ s := h5
        _ ≤ ENNReal.ofReal M := h_energy
    have h10 : (∑ i : α, μ (T i)) ≥ 1 := h_sum1
    have h11 : (∑ i : α, μ (T i))^2 ≥ 1 := by
      have h12 : (1 : ENNReal)^2 ≤ (∑ i : α, μ (T i))^2 := by gcongr
      simpa using h12
    have h14 : (∑ i : α, (ediam (T i))^s)⁻¹ ≤ ENNReal.ofReal M := by
      calc
        (∑ i : α, (ediam (T i))^s)⁻¹
          = (1 : ENNReal) * (∑ i : α, (ediam (T i))^s)⁻¹ := by simp
        _ ≤ (∑ i : α, μ (T i))^2 * (∑ i : α, (ediam (T i))^s)⁻¹ := by gcongr
        _ ≤ ENNReal.ofReal M := h9
    have hM_ne_zero : (ENNReal.ofReal M) ≠ 0 := by positivity
    have hM_ne_top : (ENNReal.ofReal M) ≠ ⊤ := by simp
    have h_inv_inv : ((ENNReal.ofReal M)⁻¹)⁻¹ = ENNReal.ofReal M := by
      have h1 : (ENNReal.ofReal M) ≠ 0 := by positivity
      have h2 : (ENNReal.ofReal M) ≠ ⊤ := by simp
      simp [h1, h2, ENNReal.inv_eq_zero, ENNReal.inv_eq_top]
      <;> norm_cast
    have h16 : (∑ i : α, (ediam (T i))^s)⁻¹ ≤ ((ENNReal.ofReal M)⁻¹)⁻¹ := by
      rw [h_inv_inv] <;> exact h14
    exact (ENNReal.inv_le_inv).mp h16

/-- Disjointize a finite family of sets: `D i = T i \ ⋃_{j < i} T j`.
    The `D i` are pairwise disjoint, have the same union as `T i`, and `D i ⊆ T i`. -/
lemma disjointize_fin {n : ℕ} {T : Fin n → Set Plane}
    (hT_meas : ∀ i, MeasurableSet (T i)) :
    ∃ (D : Fin n → Set Plane), (∀ i, MeasurableSet (D i)) ∧
    (∀ i j, i ≠ j → Disjoint (D i) (D j)) ∧
    (⋃ i, D i) = (⋃ i, T i) ∧ (∀ i, D i ⊆ T i) := by
  let U_i : Fin n → Set Plane := fun i => Set.iUnion (fun j => if j < i then T j else ∅)
  let D : Fin n → Set Plane := fun i => T i \ U_i i
  have h_union_meas : ∀ i, MeasurableSet (U_i i) := by
    intro i
    apply MeasurableSet.iUnion
    intro j
    by_cases h : j < i
    · rw [if_pos h]; exact hT_meas j
    · rw [if_neg h]; exact MeasurableSet.empty
  have hD_meas : ∀ i, MeasurableSet (D i) := by
    intro i
    exact (hT_meas i).diff (h_union_meas i)
  have hD_sub : ∀ i, D i ⊆ T i := by
    intro i; simp [D]
  have hD_disj : ∀ i j, i ≠ j → Disjoint (D i) (D j) := by
    intro i j hne
    wlog h : i < j generalizing i j
    · exact (this j i hne.symm (hne.lt_or_gt.resolve_left h)).symm
    · have h1 : D j ⊆ (T j) \ T i := by
        intro x hx
        have h2 : x ∈ T j := hx.1
        have h3 : x ∉ U_i j := hx.2
        have h4 : x ∉ T i := by
          intro h5
          have h6 : x ∈ U_i j := by
            exact Set.mem_iUnion.mpr ⟨i, by rw [if_pos h]; exact h5⟩
          exact h3 h6
        exact ⟨h2, h4⟩
      have h_disj : Disjoint (D i) (D j) := by
        have h5 : Disjoint (T i) ((T j) \ T i) := by
          exact disjoint_sdiff_right
        exact h5.mono (hD_sub i) h1
      exact h_disj
  have hD_union : (⋃ i, D i) = (⋃ i, T i) := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.mpr ⟨i, (hD_sub i) hxi⟩
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      let S : Finset (Fin n) := Finset.univ.filter (fun k => x ∈ T k)
      have h_i_in_S : i ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hxi
      have hS_nonempty : S.Nonempty := ⟨i, h_i_in_S⟩
      let k := S.min' hS_nonempty
      have hk_in_S : k ∈ S := S.min'_mem hS_nonempty
      have hxk : x ∈ T k := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk_in_S
        exact hk_in_S
      have hk_min : ∀ j ∈ Finset.Iio k, x ∉ T j := by
        intro j hj
        have h_j_lt_k : j < k := Finset.mem_Iio.mp hj
        by_contra h_xin_Tj
        have h_j_in_S : j ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_xin_Tj
        have h_k_le_j : k ≤ j := Finset.min'_le S j h_j_in_S
        exact not_le.mpr h_j_lt_k h_k_le_j
      have h_notin_union : x ∉ U_i k := by
        intro h
        rcases Set.mem_iUnion.mp h with ⟨j, hj⟩
        by_cases h_j_lt_k : j < k
        · rw [if_pos h_j_lt_k] at hj
          exact hk_min j (Finset.mem_Iio.mpr h_j_lt_k) hj
        · rw [if_neg h_j_lt_k] at hj
          simpa using hj
      have h_xin_Dk : x ∈ D k := ⟨hxk, h_notin_union⟩
      exact Set.mem_iUnion.mpr ⟨k, h_xin_Dk⟩
  exact ⟨D, hD_meas, hD_disj, hD_union, hD_sub⟩

/-- Energy-capacity inequality for arbitrary finite measurable covers.

    By disjointizing the cover without increasing diameters, reduces to
    `energy_to_content_finite`. -/
theorem energy_to_content {μ : Measure Plane} [MeasureTheory.NoAtoms μ]
    {s M : ℝ} (hs_pos : 0 < s) (hM_pos : 0 < M)
    (hμ_univ : μ Set.univ = 1)
    (h_energy : rieszEnergy μ s ≤ ENNReal.ofReal M)
    {A : Set Plane} (hA_meas : MeasurableSet A) (hμA : μ A = 1)
    {n : ℕ} {T : Fin n → Set Plane}
    (hT_meas : ∀ i, MeasurableSet (T i))
    (h_cover : A ⊆ ⋃ i, T i) :
    (∑ i : Fin n, (ediam (T i))^s) ≥ (ENNReal.ofReal M)⁻¹ := by
  rcases disjointize_fin hT_meas with ⟨D, hD_meas, hD_disj, hD_union, hD_sub⟩
  have hD_cover : A ⊆ ⋃ i, D i := by
    rw [hD_union]
    exact h_cover
  have h_main := energy_to_content_finite hs_pos hM_pos hμ_univ h_energy hA_meas hμA
    (hT_meas := hD_meas) (h_disj := hD_disj) (h_cover := hD_cover)
  have h_ediam_mono : ∀ i, (ediam (D i))^s ≤ (ediam (T i))^s := by
    intro i
    have h1 : D i ⊆ T i := hD_sub i
    have h2 : ediam (D i) ≤ ediam (T i) := ediam_mono h1
    gcongr
  have h_sum_mono : (∑ i : Fin n, (ediam (D i))^s) ≤ (∑ i : Fin n, (ediam (T i))^s) := by
    apply Finset.sum_le_sum
    intro i _
    exact h_ediam_mono i
  exact le_trans h_main h_sum_mono

end DiscretisedFurstenbergEstimate.PotentialTheory

import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Angular sum bound for WZ1 Lemma 40

Given a base point `b₁`, a unit direction `v`, and a finite set `D` of points
satisfying a discrete thin-tubes (line non-concentration) condition, proves
`∑_{b₂ ∈ D} max(|θ(b₂)·v|, δ)^(-γ) ≤ angularSumConst(γ) · K · |G₂|`
via dyadic shell decomposition and a geometric series.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

open Finset Metric

/-! ### Coordinate helpers for Point2 -/

lemma point2_inner_eq' (a b : Point2) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  have h1 : inner ℝ a b = ∑ i : Fin 2, inner ℝ (a i) (b i) := PiLp.inner_apply a b
  rw [h1]
  have h2 : ∑ i : Fin 2, inner ℝ (a i) (b i) = a 0 * b 0 + a 1 * b 1 := by
    rw [Fin.sum_univ_two] <;> simp <;> ring
  exact h2

lemma point2_orthonormal_decomp (x v : Point2) (hv : ‖v‖ = 1) :
    x = (inner ℝ x v) • v + (inner ℝ x (wz1Perp2 v)) • (wz1Perp2 v) := by
  let w := wz1Perp2 v
  have h_w0 : w 0 = -v 1 := by simp [w, wz1Perp2] <;> ring
  have h_w1 : w 1 = v 0 := by simp [w, wz1Perp2] <;> ring
  have h_v_norm_sq : (v 0)^2 + (v 1)^2 = 1 := by
    have h3 : ‖v‖^2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
    have h4 : inner ℝ v v = (v 0)^2 + (v 1)^2 := by
      rw [point2_inner_eq' v v] <;> ring
    have h5 : ‖v‖^2 = 1 := by rw [hv] <;> norm_num
    linarith
  have h_inner_v : inner ℝ x v = x 0 * v 0 + x 1 * v 1 := point2_inner_eq' x v
  have h_inner_w : inner ℝ x w = -x 0 * v 1 + x 1 * v 0 := by
    rw [point2_inner_eq' x w, h_w0, h_w1] <;> ring
  have h_coordinate0 : ((inner ℝ x v) • v + (inner ℝ x w) • w) 0 = x 0 := by
    have h : ((inner ℝ x v) • v + (inner ℝ x w) • w) 0 =
        (inner ℝ x v) * v 0 + (inner ℝ x w) * w 0 := by
      simp [Pi.add_apply] <;> ring
    rw [h, h_inner_v, h_inner_w, h_w0]
    have h_goal : (x 0 * v 0 + x 1 * v 1) * v 0 + (-x 0 * v 1 + x 1 * v 0) * (-v 1) = x 0 := by
      have h9 : (x 0 * v 0 + x 1 * v 1) * v 0 + (-x 0 * v 1 + x 1 * v 0) * (-v 1) =
          x 0 * ((v 0)^2 + (v 1)^2) := by ring
      rw [h9, h_v_norm_sq] <;> ring
    exact h_goal
  have h_coordinate1 : ((inner ℝ x v) • v + (inner ℝ x w) • w) 1 = x 1 := by
    have h : ((inner ℝ x v) • v + (inner ℝ x w) • w) 1 =
        (inner ℝ x v) * v 1 + (inner ℝ x w) * w 1 := by
      simp [Pi.add_apply] <;> ring
    rw [h, h_inner_v, h_inner_w, h_w1]
    have h_goal : (x 0 * v 0 + x 1 * v 1) * v 1 + (-x 0 * v 1 + x 1 * v 0) * v 0 = x 1 := by
      have h9 : (x 0 * v 0 + x 1 * v 1) * v 1 + (-x 0 * v 1 + x 1 * v 0) * v 0 =
          x 1 * ((v 0)^2 + (v 1)^2) := by ring
      rw [h9, h_v_norm_sq] <;> ring
    exact h_goal
  have h_sum_eq : (inner ℝ x v) • v + (inner ℝ x w) • w = x := by
    apply PiLp.ext
    intro i
    fin_cases i
    · exact h_coordinate0
    · exact h_coordinate1
  exact h_sum_eq.symm

/-! ### Distance to line helper -/

lemma strip_membership_from_angular (b₁ b₂ v : Point2) (hv : ‖v‖ = 1)
    (h_sep : 1 / 2 ≤ dist b₁ b₂) (h_bound : dist b₁ b₂ ≤ 2) (r : ℝ)
    (h : |inner ℝ ((‖b₂ - b₁‖⁻¹) • (b₂ - b₁)) v| < r / 2) :
    b₂ ∈ Metric.thickening r
      (AffineSubspace.mk' b₁ (ℝ ∙ wz1Perp2 v) : Set Point2) := by
  let w := wz1Perp2 v
  let ℓ : AffineSubspace ℝ Point2 := AffineSubspace.mk' b₁ (ℝ ∙ w)
  let d := ‖b₂ - b₁‖
  let θ := d⁻¹ • (b₂ - b₁)
  have hd_pos : 0 < d := by
    dsimp only [d]
    have h_eq : dist b₁ b₂ = ‖b₂ - b₁‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    rw [h_eq] at h_sep
    exact lt_of_lt_of_le (by norm_num) h_sep
  set a_v : ℝ := inner ℝ (b₂ - b₁) v with ha_v_def
  set a_w : ℝ := inner ℝ (b₂ - b₁) w with ha_w_def
  have h_decomp : b₂ - b₁ = a_v • v + a_w • w := by
    simpa [ha_v_def, ha_w_def] using point2_orthonormal_decomp (b₂ - b₁) v hv
  let p : Point2 := b₁ + a_w • w
  have h3 : a_w • w ∈ (ℝ ∙ w : Submodule ℝ Point2) :=
    Submodule.mem_span_singleton.mpr ⟨a_w, by simp⟩
  have hp_in_ℓ : p ∈ (ℓ : Set Point2) := by
    have h5 : p - b₁ = a_w • w := by
      dsimp only [p] <;> abel
    have h6 : p -ᵥ b₁ = p - b₁ := by rfl
    have h7 : p -ᵥ b₁ ∈ (ℝ ∙ w : Submodule ℝ Point2) := by
      rw [h6, h5]
      exact h3
    simpa [ℓ, AffineSubspace.mem_mk'] using h7
  have h_diff : b₂ - p = a_v • v := by
    have h_eq1 : b₂ - p = (b₂ - b₁) - a_w • w := by
      dsimp only [p] <;> abel
    rw [h_eq1, h_decomp]
    <;> abel
  have h_norm_diff : ‖b₂ - p‖ = |a_v| := by
    rw [h_diff, norm_smul, Real.norm_eq_abs, hv] <;> ring
  have h_inner_scaled : a_v = d * inner ℝ θ v := by
    dsimp only [θ]
    have h_eq : inner ℝ (d⁻¹ • (b₂ - b₁)) v = d⁻¹ * inner ℝ (b₂ - b₁) v := by
      rw [inner_smul_left]
      <;> simp [starRingEnd_apply]
      <;> ring
    have h_goal : d * inner ℝ (d⁻¹ • (b₂ - b₁)) v = inner ℝ (b₂ - b₁) v := by
      rw [h_eq]
      field_simp [hd_pos.ne'] <;> ring
    exact h_goal.symm
  have h_abs : |a_v| = d * |inner ℝ θ v| := by
    rw [h_inner_scaled]
    have h3 : |d * inner ℝ θ v| = d * |inner ℝ θ v| := by
      rw [abs_mul, abs_of_nonneg (by positivity)] <;> ring
    exact h3
  have h_d_le_two : d ≤ 2 := by
    dsimp only [d]
    have h_sym : ‖b₂ - b₁‖ = ‖b₁ - b₂‖ := by rw [norm_sub_rev]
    have h_eq : dist b₁ b₂ = ‖b₁ - b₂‖ := by rfl
    linarith [h_bound, h_eq, h_sym]
  have h_main : ‖b₂ - p‖ < r := by
    calc ‖b₂ - p‖
      = |a_v| := h_norm_diff
      _ = d * |inner ℝ θ v| := h_abs
      _ ≤ 2 * |inner ℝ θ v| := by gcongr <;> linarith
      _ < r := by linarith
  exact Metric.mem_thickening_iff.mpr ⟨p, hp_in_ℓ, h_main⟩

/-! ### Angular sum constant -/

noncomputable def angularSumConst (γ : ℝ) : ℝ :=
  2 + (2 : ℝ)^(1 + γ) / (1 - (2 : ℝ)^(γ - 1))

/-! ### Angular sum bound from thin tubes -/

lemma angular_sum_from_thin_tubes
    {G₂ : DiscreteSet 2} {δ K γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hK : 1 ≤ K) (hγ : 0 < γ) (hγ_lt_one : γ < 1)
    (b₁ : Point2) (v : Point2) (hv : ‖v‖ = 1)
    (D : Finset Point2) (hD_sub : D ⊆ G₂)
    (h_sep : ∀ b₂ ∈ D, 1 / 2 ≤ dist b₁ b₂)
    (h_bound : ∀ b₂ ∈ D, dist b₁ b₂ ≤ 2)
    (h_thin : ∀ (r : ℝ), δ ≤ r →
      ((D.filter (fun b₂ => b₂ ∈ Metric.thickening r
        (AffineSubspace.mk' b₁ (ℝ ∙ wz1Perp2 v) : Set Point2))).card : ℝ) ≤
      K * r * (G₂.card : ℝ)) :
    ∑ b₂ ∈ D, (max (|inner ℝ ((‖b₂ - b₁‖⁻¹) • (b₂ - b₁)) v|) δ)^(-γ) ≤
    angularSumConst γ * K * (G₂.card : ℝ) := by
  let w := wz1Perp2 v
  let ℓ : AffineSubspace ℝ Point2 := AffineSubspace.mk' b₁ (ℝ ∙ w)
  let θ (b₂ : Point2) : Point2 := ‖b₂ - b₁‖⁻¹ • (b₂ - b₁)
  let lineSet : Set Point2 := (ℓ : Set Point2)
  by_cases hD_empty : D = ∅
  · rw [hD_empty]; simp
    have h_pos : 0 ≤ angularSumConst γ * K * (G₂.card : ℝ) := by
      have h1 : 0 < (2 : ℝ)^(1 + γ) := by positivity
      have h2 : (2 : ℝ)^(γ - 1) < 1 := by
        have h3 : γ - 1 < 0 := by linarith
        have h4 : (2 : ℝ)^(γ - 1) < (2 : ℝ)^(0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < (2 : ℝ) from by norm_num) h3
        simpa using h4
      have h3 : 0 < 1 - (2 : ℝ)^(γ - 1) := by linarith
      have h4 : 0 < (2 : ℝ)^(1 + γ) / (1 - (2 : ℝ)^(γ - 1)) := div_pos h1 h3
      have h5 : 0 < angularSumConst γ := by
        dsimp only [angularSumConst]
        linarith
      have h6 : 0 ≤ K := by linarith
      have h7 : 0 ≤ (G₂.card : ℝ) := by positivity
      exact mul_nonneg (mul_nonneg h5.le h6) h7
    exact h_pos
  have hD_nonempty : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD_empty
  have hG2_nonempty : G₂.Nonempty := hD_nonempty.mono hD_sub
  have hG2_pos : 0 < (G₂.card : ℝ) := by exact_mod_cast hG2_nonempty.card_pos
  have hK_pos : 0 < K := by linarith
  have h_count_strict : ∀ (r : ℝ), δ / 2 ≤ r →
      ((D.filter (fun b₂ => |inner ℝ (θ b₂) v| < r)).card : ℝ) ≤
      K * (2 * r) * (G₂.card : ℝ) := by
    intro r hr
    have h8 : δ ≤ 2 * r := by linarith
    have h_in : ∀ b₂ ∈ D.filter (fun b₂ => |inner ℝ (θ b₂) v| < r),
        b₂ ∈ Metric.thickening (2 * r) lineSet := by
      intro b₂ hb₂
      have hb₂_in_D : b₂ ∈ D := (Finset.mem_filter.mp hb₂).1
      have hlt : |inner ℝ (θ b₂) v| < r := (Finset.mem_filter.mp hb₂).2
      exact strip_membership_from_angular b₁ b₂ v hv (h_sep b₂ hb₂_in_D) (h_bound b₂ hb₂_in_D) (2 * r) (by linarith)
    have h7 : D.filter (fun b₂ => |inner ℝ (θ b₂) v| < r) ⊆
        D.filter (fun b₂ => b₂ ∈ Metric.thickening (2 * r) lineSet) := by
      intro b₂ hb₂
      simp only [Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hb₂).1, h_in b₂ hb₂⟩
    have h9 := h_thin (2 * r) h8
    exact le_trans (by exact_mod_cast Finset.card_le_card h7) h9
  have h_count_le : ∀ (r : ℝ), δ / 2 ≤ r →
      ((D.filter (fun b₂ => |inner ℝ (θ b₂) v| ≤ r)).card : ℝ) ≤
      K * (2 * r) * (G₂.card : ℝ) := by
    intro r hr
    let B := D.filter (fun b₂ => |inner ℝ (θ b₂) v| ≤ r)
    have h_limit : ∀ (ε : ℝ), 0 < ε → (B.card : ℝ) ≤ K * (2 * (r + ε)) * (G₂.card : ℝ) := by
      intro ε hε
      have h_in : B ⊆ D.filter (fun b₂ => |inner ℝ (θ b₂) v| < r + ε) := by
        intro b₂ hb₂
        have hle : |inner ℝ (θ b₂) v| ≤ r := (Finset.mem_filter.mp hb₂).2
        simp only [Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hb₂).1, by linarith⟩
      have h10 := h_count_strict (r + ε) (by linarith)
      exact le_trans (by exact_mod_cast Finset.card_le_card h_in) h10
    by_contra h
    have h' : (B.card : ℝ) > K * (2 * r) * (G₂.card : ℝ) := by linarith
    set ε : ℝ := ((B.card : ℝ) - K * (2 * r) * (G₂.card : ℝ)) / (4 * K * (G₂.card : ℝ)) with hε_def
    have hε_pos : 0 < ε := by positivity
    have h_contra := h_limit ε hε_pos
    have h11 : K * (2 * (r + ε)) * (G₂.card : ℝ) =
        K * (2 * r) * (G₂.card : ℝ) + 2 * ε * K * (G₂.card : ℝ) := by ring
    rw [h11] at h_contra
    have h12 : 2 * ε * K * (G₂.card : ℝ) =
        ((B.card : ℝ) - K * (2 * r) * (G₂.card : ℝ)) / 2 := by
      rw [hε_def]
      field_simp [hK_pos.ne', hG2_pos.ne'] <;> ring
    rw [h12] at h_contra
    linarith
  let S : Finset Point2 := D.filter (fun b₂ => |inner ℝ (θ b₂) v| ≤ δ)
  have hS_count : (S.card : ℝ) ≤ 2 * K * δ * (G₂.card : ℝ) := by
    have h := h_count_le δ (by linarith)
    linarith
  have hS_contrib : ∑ b₂ ∈ S, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) ≤
      2 * K * (G₂.card : ℝ) := by
    have h1 : ∀ b₂ ∈ S, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) = δ^(-γ) := by
      intro b₂ hb₂
      have h2 : |inner ℝ (θ b₂) v| ≤ δ := (Finset.mem_filter.mp hb₂).2
      have h3 : max (|inner ℝ (θ b₂) v|) δ = δ := by
        rw [max_eq_right] <;> linarith
      rw [h3]
    have h4 : ∑ b₂ ∈ S, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) = (S.card : ℝ) * δ^(-γ) := by
      rw [Finset.sum_congr rfl h1, Finset.sum_const] <;> ring
    rw [h4]
    have h5 : δ^(1 - γ) ≤ 1 := by
      have h6 : 0 < 1 - γ := by linarith
      exact Real.rpow_le_one (by linarith) hδ_le_one (by linarith)
    have h7 : (S.card : ℝ) * δ^(-γ) ≤ (2 * K * δ * (G₂.card : ℝ)) * δ^(-γ) := by
      gcongr <;> exact hS_count
    have h9 : δ^(1 - γ) = δ * δ^(-γ) := by
      have h10 : (1 - γ : ℝ) = 1 + (-γ) := by ring
      rw [h10]
      rw [Real.rpow_add hδ]
      have h11 : δ ^ (1 : ℝ) = δ := by simp
      rw [h11] <;> ring
    have h8 : (2 * K * δ * (G₂.card : ℝ)) * δ^(-γ) =
        2 * K * (G₂.card : ℝ) * δ^(1 - γ) := by
      calc
        (2 * K * δ * (G₂.card : ℝ)) * δ^(-γ)
          = 2 * K * (G₂.card : ℝ) * (δ * δ^(-γ)) := by ring
        _ = 2 * K * (G₂.card : ℝ) * δ^(1 - γ) := by rw [←h9]
    rw [h8] at h7
    have h10 : 0 ≤ 2 * K * (G₂.card : ℝ) := by positivity
    nlinarith
  obtain ⟨K_nat, hK_gt⟩ := exists_nat_gt (1 / δ)
  have h_nat_le : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ)^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have h4 : (1 : ℝ) ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
      calc (n.succ : ℝ) = (n : ℝ) + 1 := by simp
        _ ≤ (2 : ℝ)^n + 1 := by linarith
        _ ≤ (2 : ℝ)^n + (2 : ℝ)^n := by linarith [h4]
        _ = (2 : ℝ)^(n + 1) := by rw [pow_succ] <;> ring
  have hK2 : (2 : ℝ)^(K_nat : ℝ) > 1 / δ := by
    have h7 : (K_nat : ℝ) ≤ (2 : ℝ)^K_nat := h_nat_le K_nat
    have h9 : (K_nat : ℝ) > 1 / δ := hK_gt
    have h10 : (2 : ℝ)^K_nat = (2 : ℝ)^(K_nat : ℝ) := by norm_cast
    linarith
  have hK3 : (2 : ℝ)^(-(K_nat : ℝ)) < δ := by
    have h4 : (2 : ℝ)^(-(K_nat : ℝ)) = 1 / (2 : ℝ)^(K_nat : ℝ) := by
      rw [Real.rpow_neg (by norm_num)] <;> field_simp
    rw [h4]
    have h5 : 0 < (2 : ℝ)^(K_nat : ℝ) := by positivity
    have h6 : 1 < δ * (2 : ℝ)^(K_nat : ℝ) := by
      have h7 : 0 < δ := hδ
      calc 1 = δ * (1 / δ) := by field_simp [h7.ne'] <;> ring
        _ < δ * (2 : ℝ)^(K_nat : ℝ) := by exact mul_lt_mul_of_pos_left hK2 h7
    have h8 : 1 / (2 : ℝ)^(K_nat : ℝ) < δ := by
      calc 1 / (2 : ℝ)^(K_nat : ℝ)
          < (δ * (2 : ℝ)^(K_nat : ℝ)) / (2 : ℝ)^(K_nat : ℝ) := by gcongr
      _ = δ := by field_simp [h5.ne'] <;> ring
    exact h8
  have hK_pos : 0 < K_nat := by
    by_contra h
    have h' : K_nat = 0 := by omega
    rw [h'] at hK2
    have h10 : (1 : ℝ) > 1 / δ := by simpa using hK2
    have h11 : 1 / δ < 1 := by linarith
    have h12 : 0 < δ := hδ
    have h13 : 1 < δ := by
      calc 1 = δ * (1 / δ) := by field_simp [h12.ne'] <;> ring
        _ < δ * 1 := by exact mul_lt_mul_of_pos_left h11 h12
        _ = δ := by ring
    have h14 : δ ≤ 1 := hδ_le_one
    linarith
  let shell (k : ℕ) : Finset Point2 :=
    D.filter (fun b₂ => (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < |inner ℝ (θ b₂) v| ∧
      |inner ℝ (θ b₂) v| ≤ (2 : ℝ)^(-(k : ℝ)))
  let shell' (k : ℕ) : Finset Point2 := shell k \ S
  have h_exists_shell : ∀ (t : ℝ), (2 : ℝ)^(-(K_nat : ℝ)) < t → t ≤ 1 →
      ∃ k ∈ Finset.range K_nat, (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < t ∧ t ≤ (2 : ℝ)^(-(k : ℝ)) := by
    intro t ht_lower ht_upper
    let P : ℕ → Prop := fun n => (2 : ℝ)^(-(n + 1 : ℕ) : ℝ) < t
    have hP_K1 : P (K_nat - 1) := by
      have h_cast : (((K_nat - 1 : ℕ) : ℝ) + 1) = (K_nat : ℝ) := by
        simp [Nat.cast_add, hK_pos] <;> omega
      have h_goal : (2 : ℝ)^(-(( (K_nat - 1 : ℕ) : ℝ) + 1)) < t := by
        rw [h_cast]; exact ht_lower
      simpa [P] using h_goal
    have hP_nonempty : ∃ n, P n := ⟨K_nat - 1, hP_K1⟩
    let k := Nat.find hP_nonempty
    have hk1 : P k := Nat.find_spec hP_nonempty
    have hk2 : ∀ n < k, ¬P n := fun n hn => Nat.find_min hP_nonempty hn
    have hk_lt_K : k < K_nat := by
      have h5 : k ≤ K_nat - 1 := Nat.find_min' hP_nonempty hP_K1
      omega
    have hk_upper : t ≤ (2 : ℝ)^(-(k : ℝ)) := by
      by_cases h_k0 : k = 0
      · rw [h_k0]; simpa using ht_upper
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero h_k0
        have h4 : ¬P (k - 1) := hk2 (k - 1) (by omega)
        have h5 : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
          simp [Nat.cast_add, hk_pos] <;> omega
        have h6 : ¬((2 : ℝ)^(-(( (k - 1 : ℕ) : ℝ) + 1)) < t) := by simpa [P] using h4
        rw [h5] at h6
        exact le_of_not_gt h6
    exact ⟨k, Finset.mem_range.mpr hk_lt_K, hk1, hk_upper⟩
  have h_shell_disj : ∀ k1 ∈ Finset.range K_nat, ∀ k2 ∈ Finset.range K_nat, k1 ≠ k2 →
      Disjoint (shell k1) (shell k2) := by
    intro k1 _ k2 _ hne
    rw [Finset.disjoint_left]
    intro p h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    by_cases h : k1 < k2
    · have h5 : (2 : ℝ)^(-(k2 : ℝ)) ≤ (2 : ℝ)^(-(k1 + 1 : ℕ) : ℝ) := by
        have h6 : (k1 + 1 : ℕ) ≤ k2 := by omega
        have h7 : -((k1 + 1 : ℕ) : ℝ) ≥ -(k2 : ℝ) := by exact_mod_cast (by omega)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h7
      have h8 : (2 : ℝ)^(-(k2 : ℝ)) < |inner ℝ (θ p) v| := by
        calc (2 : ℝ)^(-(k2 : ℝ)) ≤ (2 : ℝ)^(-(k1 + 1 : ℕ) : ℝ) := h5
          _ < |inner ℝ (θ p) v| := h1'.1
      have h9 : |inner ℝ (θ p) v| ≤ (2 : ℝ)^(-(k2 : ℝ)) := h2'.2
      linarith
    · have h6 : k2 < k1 := by omega
      have h7 : (2 : ℝ)^(-(k1 : ℝ)) ≤ (2 : ℝ)^(-(k2 + 1 : ℕ) : ℝ) := by
        have h8 : (k2 + 1 : ℕ) ≤ k1 := by omega
        have h9 : -((k2 + 1 : ℕ) : ℝ) ≥ -(k1 : ℝ) := by exact_mod_cast (by omega)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h9
      have h10 : (2 : ℝ)^(-(k1 : ℝ)) < |inner ℝ (θ p) v| := by
        calc (2 : ℝ)^(-(k1 : ℝ)) ≤ (2 : ℝ)^(-(k2 + 1 : ℕ) : ℝ) := h7
          _ < |inner ℝ (θ p) v| := h2'.1
      have h11 : |inner ℝ (θ p) v| ≤ (2 : ℝ)^(-(k1 : ℝ)) := h1'.2
      linarith
  have h_shell'_disj : ∀ k1 ∈ Finset.range K_nat, ∀ k2 ∈ Finset.range K_nat, k1 ≠ k2 →
      Disjoint (shell' k1) (shell' k2) := by
    intro k1 hk1 k2 hk2 hne
    have h1 : shell' k1 ⊆ shell k1 := Finset.sdiff_subset
    have h2 : shell' k2 ⊆ shell k2 := Finset.sdiff_subset
    exact (h_shell_disj k1 hk1 k2 hk2 hne).mono h1 h2
  have h_partition : D \ S = Finset.biUnion (Finset.range K_nat) shell' := by
    ext θ₂
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨hθD, hnotinS⟩
      have h_t_gt : δ < |inner ℝ (θ θ₂) v| := by
        by_contra h
        have h' : |inner ℝ (θ θ₂) v| ≤ δ := by linarith
        have h_inS : θ₂ ∈ S := Finset.mem_filter.mpr ⟨hθD, by linarith⟩
        exact hnotinS h_inS
      have h_t_le_one : |inner ℝ (θ θ₂) v| ≤ 1 := by
        have h_sep2 : 1 / 2 ≤ dist b₁ θ₂ := h_sep θ₂ hθD
        have h_d_pos : 0 < ‖θ₂ - b₁‖ := by
          have h_eq : dist b₁ θ₂ = ‖θ₂ - b₁‖ := by
            rw [dist_eq_norm, norm_sub_rev]
          rw [h_eq] at h_sep2
          exact lt_of_lt_of_le (by norm_num) h_sep2
        have h_norm_θ : ‖θ θ₂‖ = 1 := by
          dsimp only [θ]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h_d_pos)]
          <;> field_simp [h_d_pos.ne'] <;> ring
        calc |inner ℝ (θ θ₂) v| ≤ ‖θ θ₂‖ * ‖v‖ := abs_real_inner_le_norm (θ θ₂) v
          _ = 1 := by rw [h_norm_θ, hv] <;> ring
      have h_t_gt_K : (2 : ℝ)^(-(K_nat : ℝ)) < |inner ℝ (θ θ₂) v| := by linarith
      obtain ⟨k, hkK, hk1, hk2⟩ := h_exists_shell (|inner ℝ (θ θ₂) v|) h_t_gt_K h_t_le_one
      have hθin_shell : θ₂ ∈ shell k := Finset.mem_filter.mpr ⟨hθD, ⟨hk1, hk2⟩⟩
      exact ⟨k, Finset.mem_range.mp hkK, Finset.mem_sdiff.mpr ⟨hθin_shell, hnotinS⟩⟩
    · rintro ⟨k, _, hθin⟩
      have h1 : θ₂ ∈ shell k := (Finset.mem_sdiff.mp hθin).1
      have h2 : θ₂ ∉ S := (Finset.mem_sdiff.mp hθin).2
      have h3 : θ₂ ∈ D := (Finset.mem_filter.mp h1).1
      exact ⟨h3, h2⟩
  have h_shell'_contrib : ∀ k ∈ Finset.range K_nat,
      ∑ b₂ ∈ shell' k, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) ≤
      (2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) * (2 : ℝ)^((k : ℝ) * (γ - 1)) := by
    intro k hk
    by_cases h_empty : shell' k = ∅
    · rw [h_empty]; simp; positivity
    · have h_nonempty : (shell' k).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
      obtain ⟨b₂, hb₂⟩ := h_nonempty
      have h2 : b₂ ∈ shell k := (Finset.mem_sdiff.mp hb₂).1
      have h3 : b₂ ∉ S := (Finset.mem_sdiff.mp hb₂).2
      have h4 : δ ≤ |inner ℝ (θ b₂) v| := by
        by_contra h
        have h5 : |inner ℝ (θ b₂) v| ≤ δ := by linarith
        have h_inS : b₂ ∈ S := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h2).1, h5⟩
        exact h3 h_inS
      have h5 : δ ≤ (2 : ℝ)^(-(k : ℝ)) := by
        have h6 : |inner ℝ (θ b₂) v| ≤ (2 : ℝ)^(-(k : ℝ)) := (Finset.mem_filter.mp h2).2.2
        linarith
      have h_count : (shell k).card ≤ 2 * K * (2 : ℝ)^(-(k : ℝ)) * (G₂.card : ℝ) := by
        have h7 : shell k ⊆ D.filter (fun b₂ => |inner ℝ (θ b₂) v| ≤ (2 : ℝ)^(-(k : ℝ))) := by
          intro p hp
          have h8 := (Finset.mem_filter.mp hp).2
          simp only [Finset.mem_filter]
          exact ⟨(Finset.mem_filter.mp hp).1, h8.2⟩
        have h9 := h_count_le ((2 : ℝ)^(-(k : ℝ))) (by linarith)
        have h9' : ((D.filter (fun b₂ => |inner ℝ (θ b₂) v| ≤ (2 : ℝ)^(-(k : ℝ)))).card : ℝ) ≤ 2 * K * (2 : ℝ)^(-(k : ℝ)) * (G₂.card : ℝ) := by linarith
        have h10 : ((shell k).card : ℝ) ≤ ((D.filter (fun b₂ => |inner ℝ (θ b₂) v| ≤ (2 : ℝ)^(-(k : ℝ)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card h7
        exact le_trans h10 h9'
      let bval : ℝ := (2 : ℝ)^(((k + 1 : ℕ) : ℝ) * γ)
      have h1 : ∀ (φ : Point2), φ ∈ shell' k → (max (|inner ℝ (θ φ) v|) δ)^(-γ) ≤ bval := by
        intro φ hφ
        have h2 : φ ∈ shell k := (Finset.mem_sdiff.mp hφ).1
        have h2cond := (Finset.mem_filter.mp h2).2
        have h4 : (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < |inner ℝ (θ φ) v| := h2cond.1
        have h5 : δ < |inner ℝ (θ φ) v| := by
          have h3 : φ ∉ S := (Finset.mem_sdiff.mp hφ).2
          have hφD : φ ∈ D := (Finset.mem_filter.mp h2).1
          by_contra h
          have hle : |inner ℝ (θ φ) v| ≤ δ := by linarith
          have h_inS : φ ∈ S := Finset.mem_filter.mpr ⟨hφD, hle⟩
          exact h3 h_inS
        have h7 : 0 < |inner ℝ (θ φ) v| := by linarith
        have h8 : (max (|inner ℝ (θ φ) v|) δ)^(-γ) ≤ ((2 : ℝ)^(-(k + 1 : ℕ) : ℝ))^(-γ) := by
          have h9 : max (|inner ℝ (θ φ) v|) δ = |inner ℝ (θ φ) v| := by
            rw [max_eq_left] <;> linarith
          rw [h9]
          have h10 : 0 < (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) := by positivity
          have h11 : (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < |inner ℝ (θ φ) v| := h4
          have h11' : (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) ≤ |inner ℝ (θ φ) v| := le_of_lt h11
          have h12 : (|inner ℝ (θ φ) v|)^(-γ) ≤ ((2 : ℝ)^(-(k + 1 : ℕ) : ℝ))^(-γ) := by
            have h13 : (|inner ℝ (θ φ) v|)^γ ≥ ((2 : ℝ)^(-(k + 1 : ℕ) : ℝ))^γ :=
              Real.rpow_le_rpow (by positivity) h11' (by linarith)
            have h14 : (|inner ℝ (θ φ) v|)^(-γ) = 1 / (|inner ℝ (θ φ) v|)^γ := by
              rw [Real.rpow_neg (by linarith)] <;> field_simp
            have h15 : ((2 : ℝ)^(-(k + 1 : ℕ) : ℝ))^(-γ) = 1 / ((2 : ℝ)^(-(k + 1 : ℕ) : ℝ))^γ := by
              rw [Real.rpow_neg (by positivity)] <;> field_simp
            rw [h14, h15]
            exact one_div_le_one_div_of_le (by positivity) h13
          exact h12
        have h_exp_eq : (-(k + 1 : ℕ) : ℝ) * (-γ) = ((k + 1 : ℕ) : ℝ) * γ := by
          have h1 : (-(k + 1 : ℕ) : ℝ) = -((k + 1 : ℕ) : ℝ) := by simp
          rw [h1] <;> ring
        have h16 : ((2 : ℝ)^(-(k + 1 : ℕ) : ℝ))^(-γ) = bval := by
          simp only [bval]
          rw [←Real.rpow_mul (by norm_num), h_exp_eq]
        rw [h16] at h8
        exact h8
      have h21 : ∑ b₂ ∈ shell' k, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) ≤
          (shell' k).card * bval := by
        calc
          _ ≤ ∑ b₂ ∈ shell' k, bval := Finset.sum_le_sum (fun b₂ hb₂ => h1 b₂ hb₂)
          _ = (shell' k).card * bval := by rw [Finset.sum_const] <;> ring
      have h3 : (shell' k).card ≤ (shell k).card := Finset.card_le_card Finset.sdiff_subset
      calc
        _ ≤ (shell' k).card * bval := h21
        _ ≤ (shell k).card * bval := by gcongr
        _ ≤ (2 * K * (2 : ℝ)^(-(k : ℝ)) * (G₂.card : ℝ)) * bval := by gcongr <;> exact h_count
        _ = (2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) * (2 : ℝ)^((k : ℝ) * (γ - 1)) := by
          simp only [bval]
          have h_expand : ((k + 1 : ℕ) : ℝ) * γ = γ + (k : ℝ) * γ := by
            simp [Nat.cast_add] <;> ring
          rw [h_expand]
          have h_factor : (2 : ℝ) * (2 : ℝ)^(-(k : ℝ)) * (2 : ℝ)^(γ + (k : ℝ) * γ) =
              (2 : ℝ)^(1 + γ) * (2 : ℝ)^((k : ℝ) * (γ - 1)) := by
            have h_a : (2 : ℝ) * (2 : ℝ)^(-(k : ℝ)) = (2 : ℝ)^(1 + (-(k : ℝ))) := by
              have h : (2 : ℝ)^(1 + (-(k : ℝ))) = (2 : ℝ) * (2 : ℝ)^(-(k : ℝ)) := by
                have h3 : (1 + (-(k : ℝ)) : ℝ) = (1 : ℝ) + (-(k : ℝ)) := by norm_num
                rw [h3, Real.rpow_add (by norm_num)] <;> simp
              exact h.symm
            have h_b : (2 : ℝ)^(1 + (-(k : ℝ))) * (2 : ℝ)^(γ + (k : ℝ) * γ) =
                (2 : ℝ)^((1 + (-(k : ℝ))) + (γ + (k : ℝ) * γ)) := by
              rw [←Real.rpow_add (by norm_num)] <;> ring
            have h_c : (1 + (-(k : ℝ))) + (γ + (k : ℝ) * γ) =
                (1 + γ) + (k : ℝ) * (γ - 1) := by ring
            have h_d : (2 : ℝ)^((1 + γ) + (k : ℝ) * (γ - 1)) =
                (2 : ℝ)^(1 + γ) * (2 : ℝ)^((k : ℝ) * (γ - 1)) := by
              rw [←Real.rpow_add (by norm_num)] <;> ring
            calc
              (2 : ℝ) * (2 : ℝ)^(-(k : ℝ)) * (2 : ℝ)^(γ + (k : ℝ) * γ)
                = ((2 : ℝ) * (2 : ℝ)^(-(k : ℝ))) * (2 : ℝ)^(γ + (k : ℝ) * γ) := by ring
              _ = (2 : ℝ)^(1 + (-(k : ℝ))) * (2 : ℝ)^(γ + (k : ℝ) * γ) := by rw [h_a]
              _ = (2 : ℝ)^((1 + (-(k : ℝ))) + (γ + (k : ℝ) * γ)) := h_b
              _ = (2 : ℝ)^((1 + γ) + (k : ℝ) * (γ - 1)) := by rw [h_c]
              _ = (2 : ℝ)^(1 + γ) * (2 : ℝ)^((k : ℝ) * (γ - 1)) := h_d
          have h_goal : (2 * K * (2 : ℝ)^(-(k : ℝ)) * (G₂.card : ℝ)) * (2 : ℝ)^(γ + (k : ℝ) * γ) =
              K * (G₂.card : ℝ) * ((2 : ℝ) * (2 : ℝ)^(-(k : ℝ)) * (2 : ℝ)^(γ + (k : ℝ) * γ)) := by ring
          rw [h_goal, h_factor] <;> ring
  let q : ℝ := (2 : ℝ)^(γ - 1)
  have hq_pos : 0 < q := by positivity
  have hq_lt_one : q < 1 := by
    have h1 : γ - 1 < 0 := by linarith
    have h2 : (2 : ℝ)^(γ - 1) < (2 : ℝ)^(0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
    simpa using h2
  have h_denom_pos : 0 < 1 - q := by linarith
  have h_rpow_eq : ∀ k : ℕ, (2 : ℝ)^((k : ℝ) * (γ - 1)) = q^k := by
    intro k
    induction k with
    | zero => simp [q]
    | succ k ih =>
      have h1 : ((k + 1 : ℕ) : ℝ) * (γ - 1) = (k : ℝ) * (γ - 1) + (γ - 1) := by
        simp [Nat.cast_add] <;> ring
      rw [h1, Real.rpow_add (by norm_num), ih] <;> simp [q] <;> ring
  have h_geom_sum : ∑ k ∈ Finset.range K_nat, q^k ≤ 1 / (1 - q) := by
    have h_formula : ∀ N : ℕ, ∑ k ∈ Finset.range N, q^k = (1 - q^N) / (1 - q) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp [h_denom_pos.ne'] <;> ring
    rw [h_formula K_nat]
    have h : (1 - q^K_nat) / (1 - q) ≤ 1 / (1 - q) := by
      apply div_le_div_of_nonneg_right
      · have h5 : 0 ≤ q^K_nat := by positivity
        linarith
      · linarith
    exact h
  have h_main : ∑ b₂ ∈ D, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) =
      (∑ b₂ ∈ S, (max (|inner ℝ (θ b₂) v|) δ)^(-γ)) +
      ∑ k ∈ Finset.range K_nat, ∑ b₂ ∈ shell' k, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) := by
    have h1 : S ∪ (D \ S) = D := by
      have h2 : (D \ S) ∪ S = D := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
      rw [Finset.union_comm] at h2
      exact h2
    have h1' : D = S ∪ (D \ S) := h1.symm
    have h_disj' : Disjoint S (D \ S) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 hx1
    rw [h1', Finset.sum_union h_disj']
    rw [h_partition, Finset.sum_biUnion h_shell'_disj]
  have h_step2 : (∑ b₂ ∈ S, (max (|inner ℝ (θ b₂) v|) δ)^(-γ)) +
      ∑ k ∈ Finset.range K_nat, ∑ b₂ ∈ shell' k, (max (|inner ℝ (θ b₂) v|) δ)^(-γ) ≤
      2 * K * (G₂.card : ℝ) +
      ∑ k ∈ Finset.range K_nat, ((2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) * (2 : ℝ)^((k : ℝ) * (γ - 1))) := by
    apply add_le_add
    · exact hS_contrib
    · apply Finset.sum_le_sum
      intro k hk
      exact h_shell'_contrib k hk
  have h_sum_rpow : ∑ k ∈ Finset.range K_nat, (2 : ℝ)^((k : ℝ) * (γ - 1)) ≤ 1 / (1 - q) := by
    have h_eq : ∑ k ∈ Finset.range K_nat, (2 : ℝ)^((k : ℝ) * (γ - 1)) = ∑ k ∈ Finset.range K_nat, q^k := by
      apply Finset.sum_congr rfl
      intro k _
      exact h_rpow_eq k
    rw [h_eq]
    exact h_geom_sum
  calc
    ∑ b₂ ∈ D, (max (|inner ℝ (θ b₂) v|) δ)^(-γ)
      = (∑ b₂ ∈ S, _) + ∑ k ∈ Finset.range K_nat, ∑ b₂ ∈ shell' k, _ := h_main
    _ ≤ _ := h_step2
    _ = 2 * K * (G₂.card : ℝ) +
        (2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) * ∑ k ∈ Finset.range K_nat, (2 : ℝ)^((k : ℝ) * (γ - 1)) := by
      have h_eq_sum : ∑ k ∈ Finset.range K_nat, ((2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) * (2 : ℝ)^((k : ℝ) * (γ - 1))) =
          (2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) * ∑ k ∈ Finset.range K_nat, (2 : ℝ)^((k : ℝ) * (γ - 1)) := by
        rw [Finset.mul_sum] <;> rfl
      rw [h_eq_sum] <;> ring
    _ ≤ 2 * K * (G₂.card : ℝ) +
        (2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) * (1 / (1 - q)) := by
      have h_pos : 0 ≤ (2 : ℝ)^(1 + γ) * K * (G₂.card : ℝ) := by positivity
      nlinarith [h_sum_rpow]
    _ = angularSumConst γ * K * (G₂.card : ℝ) := by
      have h1 : 1 / (1 - q) = 1 / (1 - (2 : ℝ)^(γ - 1)) := by
        simp [q]
      rw [h1]
      simp [angularSumConst] <;> ring

end Kakeya.Assouad

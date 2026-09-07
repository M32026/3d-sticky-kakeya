import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

noncomputable section

namespace Kakeya.Assouad

open Finset Metric

attribute [local instance] Classical.propDecidable

/-- Convert unnormalized inner product bound to strip membership. -/
lemma inner_to_thickening {b₁ v : Point2} (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 < r)
    {p : Point2} (h : |inner ℝ (p - b₁) v| < r) :
    p ∈ Metric.thickening r (AffineSubspace.mk' b₁ (ℝ ∙ wz1Perp2 v) : Set Point2) := by
  let d := wz1Perp2 v
  let ℓ : AffineSubspace ℝ Point2 := AffineSubspace.mk' b₁ (ℝ ∙ d)
  have hd0 : d 0 = -v 1 := by
    simp [d, wz1Perp2] <;> ring
  have hd1 : d 1 = v 0 := by
    simp [d, wz1Perp2] <;> ring
  have hd_norm2 : ‖d‖^2 = 1 := by
    have h1 : ‖d‖^2 = (d 0)^2 + (d 1)^2 := by
      have h2 : inner ℝ d d = ‖d‖^2 := real_inner_self_eq_norm_sq d
      have h3 : inner ℝ d d = (d 0)^2 + (d 1)^2 := by
        rw [point2_inner_eq d d] <;> ring
      linarith
    have h4 : ‖v‖^2 = (v 0)^2 + (v 1)^2 := by
      have h5 : inner ℝ v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
      have h6 : inner ℝ v v = (v 0)^2 + (v 1)^2 := by
        rw [point2_inner_eq v v] <;> ring
      linarith
    have h5 : ‖d‖^2 = (v 1)^2 + (v 0)^2 := by
      rw [h1, hd0, hd1] <;> ring
    have h6 : ‖v‖^2 = 1 := by rw [hv] <;> norm_num
    linarith
  have hd_norm : ‖d‖ = 1 := by
    have h7 : 0 ≤ ‖d‖ := norm_nonneg d
    nlinarith
  let w := p - b₁
  let t : ℝ := inner ℝ w d
  let q : Point2 := b₁ + t • d
  have hq_diff : q - b₁ = t • d := by simp [q] <;> abel
  have hq_in_ℓ : q ∈ (ℓ : Set Point2) := by
    have h : q - b₁ ∈ (ℝ ∙ d : Submodule ℝ Point2) := by
      rw [hq_diff]
      exact Submodule.mem_span_singleton.mpr ⟨t, rfl⟩
    simpa [ℓ, AffineSubspace.mem_mk'] using h
  have h_pyth : (inner ℝ w d)^2 + (inner ℝ w v)^2 = ‖w‖^2 := by
    have h := pythagorean_perp2 (hv := hv) (θ := w)
    have h_eq : inner ℝ w (wz1Perp2 v) = inner ℝ w d := by rfl
    rw [h_eq] at h
    linarith
  have h_norm2 : ‖w - t • d‖^2 = (inner ℝ w v)^2 := by
    have h3 : ‖w - t • d‖^2 = inner ℝ (w - t • d) (w - t • d) := by
      rw [←real_inner_self_eq_norm_sq] <;> rfl
    rw [h3]
    have h4 : inner ℝ (w - t • d) (w - t • d) =
        inner ℝ w w - 2 * t * inner ℝ w d + t^2 * inner ℝ d d := by
      have h51 : inner ℝ (w - t • d) (w - t • d) =
          inner ℝ w (w - t • d) - inner ℝ (t • d) (w - t • d) := by
        rw [inner_sub_left]
      rw [h51]
      have h52 : inner ℝ w (w - t • d) = inner ℝ w w - t * inner ℝ w d := by
        rw [inner_sub_right, inner_smul_right] <;> ring
      have h53 : inner ℝ (t • d) (w - t • d) =
          t * inner ℝ d w - t^2 * inner ℝ d d := by
        have h531 : inner ℝ (t • d) (w - t • d) = t * inner ℝ d (w - t • d) := by
          exact real_inner_smul_left d (w - t • d) t
        rw [h531]
        have h532 : inner ℝ d (w - t • d) = inner ℝ d w - inner ℝ d (t • d) := by
          rw [inner_sub_right]
        rw [h532]
        have h533 : inner ℝ d (t • d) = t * inner ℝ d d := by
          rw [inner_smul_right] <;> ring
        rw [h533] <;> ring
      rw [h52, h53]
      have h54 : inner ℝ d w = inner ℝ w d := by
        simpa [real_inner_comm] using rfl
      rw [h54] <;> ring
    rw [h4]
    have h5 : inner ℝ d d = 1 := by
      rw [real_inner_self_eq_norm_sq, hd_norm] <;> norm_num
    have h6 : inner ℝ w w = ‖w‖^2 := by rw [real_inner_self_eq_norm_sq]
    rw [h5, h6]
    have h7 : t = inner ℝ w d := by rfl
    rw [h7]
    linarith [h_pyth]
  have h1 : p - q = w - t • d := by simp [w, q] <;> abel
  have h_dist : dist p q = |inner ℝ w v| := by
    rw [dist_eq_norm, h1]
    have h8 : ‖w - t • d‖^2 = (inner ℝ w v)^2 := h_norm2
    have h9 : 0 ≤ ‖w - t • d‖ := norm_nonneg _
    nlinarith [abs_nonneg (inner ℝ w v), sq_abs (inner ℝ w v)]
  have h_lt : dist p q < r := by rw [h_dist] <;> exact h
  have h10 : p ∈ Metric.thickening r (ℓ : Set Point2) := by
    rw [Metric.mem_thickening_iff]
    exact ⟨q, hq_in_ℓ, h_lt⟩
  exact h10

/-- Unnormalized angular sum bound from thin tubes. -/
lemma thin_tubes_angular_sum_unnormalized
    {G₁ G₂ : DiscreteSet 2} {δ K γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hK : 1 ≤ K)
    (hγ : 0 < γ) (hγ_lt_one : γ < 1)
    (b₁ : Point2) (v : Point2) (hv : ‖v‖ = 1)
    (E : Finset (Point2 × Point2)) (hE_sub : E ⊆ G₁ ×ˢ G₂)
    (h_thin : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ((G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal) ≤
        ENNReal.ofReal (K * r) * (G₂.card : ENNReal))
    (hG1_ball : G₁.IsInUnitBall) (hG2_ball : G₂.IsInUnitBall)
    (hb₁ : b₁ ∈ G₁) :
    ∑ b₂ ∈ (G₂.filter (fun b₂ => (b₁, b₂) ∈ E)),
        (max (|inner ℝ (b₂ - b₁) v|) δ)^(-γ) ≤
    (2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * K * (G₂.card : ℝ) := by
  let d := wz1Perp2 v
  let ℓ : AffineSubspace ℝ Point2 := AffineSubspace.mk' b₁ (ℝ ∙ d)
  have hd_ne_zero : d ≠ 0 := by
    intro h
    have h1 : d 0 = 0 := by rw [h] <;> simp
    have h2 : v 1 = 0 := by simpa [d, wz1Perp2] using h1
    have h3 : d 1 = 0 := by rw [h] <;> simp
    have h4 : v 0 = 0 := by simpa [d, wz1Perp2] using h3
    have h6 : ‖v‖^2 = (v 0)^2 + (v 1)^2 := by
      have h7 : inner ℝ v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
      have h8 : inner ℝ v v = (v 0)^2 + (v 1)^2 := by
        rw [point2_inner_eq v v] <;> ring
      linarith
    have h5 : ‖v‖^2 = 0 := by rw [h6, h4, h2] <;> norm_num
    have h5' : ‖v‖ = 0 := by
      have h_nonneg : 0 ≤ ‖v‖ := norm_nonneg v
      nlinarith
    rw [h5'] at hv <;> norm_num at hv
  have hb₁_in_ℓ : b₁ ∈ (ℓ : Set Point2) := by
    simp [ℓ] <;> exact Submodule.zero_mem _
  have hfinrank : Module.finrank ℝ ℓ.direction = 1 := by
    have h_dir : ℓ.direction = (ℝ ∙ d) := by simp [ℓ]
    rw [h_dir]
    exact finrank_span_singleton hd_ne_zero

  let E_b1 := G₂.filter (fun b₂ => (b₁, b₂) ∈ E)
  let f (b₂ : Point2) : ℝ := |inner ℝ (b₂ - b₁) v|

  have h_strip : ∀ (b₂ : Point2), b₂ ∈ E_b1 → ∀ (t : ℝ), 0 < t → f b₂ < t →
      b₂ ∈ Metric.thickening t (ℓ : Set Point2) := by
    intro b₂ hb₂ t ht hft
    exact inner_to_thickening hv ht hft

  have h_f_le_two : ∀ b₂ ∈ E_b1, f b₂ ≤ 2 := by
    intro b₂ hb₂
    have hb₂_in_G2 : b₂ ∈ G₂ := (Finset.mem_filter.mp hb₂).1
    have h1 : ‖b₂ - b₁‖ ≤ 2 := by
      have h2 : dist b₁ 0 ≤ 1 := hG1_ball b₁ hb₁
      have h3 : dist b₂ 0 ≤ 1 := hG2_ball b₂ hb₂_in_G2
      have h4 : dist b₁ b₂ ≤ 2 := by
        calc dist b₁ b₂ ≤ dist b₁ 0 + dist 0 b₂ := dist_triangle _ _ _
          _ = dist b₁ 0 + dist b₂ 0 := by rw [dist_comm b₂ 0]
          _ ≤ 2 := by linarith
      have h5 : ‖b₂ - b₁‖ = dist b₁ b₂ := by
        rw [dist_eq_norm, norm_sub_rev]
      rw [h5]; exact h4
    have h4 : f b₂ ≤ ‖b₂ - b₁‖ := by
      dsimp only [f]
      have h_cauchy : abs (inner ℝ (b₂ - b₁) v) ≤ ‖b₂ - b₁‖ * ‖v‖ :=
        abs_real_inner_le_norm (b₂ - b₁) v
      rw [hv] at h_cauchy <;> linarith
    linarith [dist_eq_norm b₁ b₂]

  -- Bridge h_thin to all r ≥ δ
  have h_thin_bound : ∀ (r : ℝ), δ ≤ r →
      ((E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2))).card : ENNReal) ≤
      ENNReal.ofReal (K * r) * (G₂.card : ENNReal) := by
    intro r hr
    by_cases h_r_le_one : r ≤ 1
    · -- r ≤ 1: use h_thin directly
      have h_eq : E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)) =
          G₂.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E) := by
        ext b₂
        simp only [E_b1, Finset.mem_filter] <;> tauto
      rw [h_eq]
      exact h_thin b₁ hb₁ ℓ hb₁_in_ℓ hfinrank r hr h_r_le_one
    · -- r > 1: bound trivially
      have h_r_gt_one : 1 < r := by linarith
      have h1 : (E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2))).card ≤ G₂.card := by
        have h_sub : E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)) ⊆ G₂ := by
          intro x hx
          have h2 : x ∈ E_b1 := (Finset.mem_filter.mp hx).1
          exact (Finset.mem_filter.mp h2).1
        exact Finset.card_le_card h_sub
      have h2 : (G₂.card : ENNReal) ≤ ENNReal.ofReal (K * r) * (G₂.card : ENNReal) := by
        have hK_pos : 0 ≤ K := by linarith
        have h3 : 1 ≤ K * r := by
          calc 1 = 1 * 1 := by ring
            _ ≤ K * r := by gcongr <;> linarith
        have h4 : ENNReal.ofReal (K * r) ≥ 1 := by
          exact ENNReal.one_le_ofReal.mpr h3
        simpa [mul_assoc] using mul_le_mul_right' h4 (G₂.card : ENNReal)
      exact le_trans (by exact_mod_cast h1) h2

  -- Choose K0 minimal with 2^K0 * δ > 2
  have h_exists : ∃ (n : ℕ), (2 : ℝ)^n * δ > 2 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ)
    have h1 : (2 / δ : ℝ) < (n : ℝ) := hn
    have h2 : (n : ℝ) ≤ (2 : ℝ)^n := nat_le_pow_two n
    have h3 : (2 : ℝ)^n * δ > 2 := by
      have h4 : (2 / δ : ℝ) < (2 : ℝ)^n := lt_of_lt_of_le h1 h2
      have h5 : (2 : ℝ)^n * δ > (2 / δ) * δ := mul_lt_mul_of_pos_right h4 hδ
      rw [show (2 / δ) * δ = 2 by field_simp [hδ.ne'] <;> ring] at h5
      exact h5
    exact ⟨n, h3⟩
  let K0 := Nat.find h_exists
  have hK0_gt : (2 : ℝ)^K0 * δ > 2 := Nat.find_spec h_exists
  have hK0_min : ∀ k < K0, (2 : ℝ)^k * δ ≤ 2 := fun k hk =>
    have h : ¬((2 : ℝ)^k * δ > 2) := Nat.find_min h_exists hk
    by linarith
  have hK0_pos : 0 < K0 := by
    by_contra h; have h' : K0 = 0 := by omega
    rw [h'] at hK0_gt; simp at hK0_gt <;> linarith
  have h2pow_K0 : (2 : ℝ)^K0 ≤ 4 / δ := by
    have h : (2 : ℝ)^(K0 - 1) * δ ≤ 2 := hK0_min (K0 - 1) (by omega)
    have h2 : (2 : ℝ)^K0 = 2 * (2 : ℝ)^(K0 - 1) := by
      have h_pos : 0 < K0 := hK0_pos
      have h_eq : K0 = Nat.succ (K0 - 1) := by omega
      rw [h_eq]
      simp [pow_succ] <;> ring
    rw [h2]
    have h3 : 2 * (2 : ℝ)^(K0 - 1) ≤ 4 / δ := by
      have h4 : 2 * ((2 : ℝ)^(K0 - 1) * δ) ≤ 4 := by linarith
      calc 2 * (2 : ℝ)^(K0 - 1)
        = (2 * ((2 : ℝ)^(K0 - 1) * δ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ 4 / δ := by gcongr
    exact h3

  let shell (k : ℕ) := E_b1.filter (fun b₂ => (2 : ℝ)^k * δ ≤ f b₂ ∧ f b₂ < (2 : ℝ)^(k+1) * δ)
  let inner_shell := E_b1.filter (fun b₂ => f b₂ < δ)

  have h_disj_shells : ∀ k1 ∈ Finset.range K0, ∀ k2 ∈ Finset.range K0, k1 ≠ k2 → Disjoint (shell k1) (shell k2) := by
    intro k1 _ k2 _ hne
    simp only [shell, Finset.disjoint_left, Finset.mem_filter]
    intro b₂ h1 h2
    have h5 : (2 : ℝ)^k1 * δ ≤ f b₂ := h1.2.1
    have h6 : f b₂ < (2 : ℝ)^(k1+1) * δ := h1.2.2
    have h7 : (2 : ℝ)^k2 * δ ≤ f b₂ := h2.2.1
    have h8 : f b₂ < (2 : ℝ)^(k2+1) * δ := h2.2.2
    by_cases h : k1 < k2
    · have h9 : k1 + 1 ≤ k2 := by omega
      have h10 : (2 : ℝ)^(k1+1) ≤ (2 : ℝ)^k2 := pow_le_pow_right₀ (by norm_num) h9
      have h11 : (2 : ℝ)^(k1+1) * δ ≤ (2 : ℝ)^k2 * δ := by gcongr
      have h12 : f b₂ < (2 : ℝ)^k2 * δ := by linarith
      linarith [h7]
    · have h9 : k2 < k1 := by omega
      have h10 : k2 + 1 ≤ k1 := by omega
      have h11 : (2 : ℝ)^(k2+1) ≤ (2 : ℝ)^k1 := pow_le_pow_right₀ (by norm_num) h10
      have h12 : (2 : ℝ)^(k2+1) * δ ≤ (2 : ℝ)^k1 * δ := by gcongr
      have h13 : f b₂ < (2 : ℝ)^k1 * δ := by linarith
      linarith [h5]

  have h_disj_inner : ∀ k ∈ Finset.range K0, Disjoint inner_shell (shell k) := by
    intro k _
    simp only [inner_shell, shell, Finset.disjoint_left, Finset.mem_filter]
    intro b₂ h1 h2
    have h5 : f b₂ < δ := h1.2
    have h6 : (2 : ℝ)^k * δ ≤ f b₂ := h2.2.1
    have h7 : (1 : ℝ) ≤ (2 : ℝ)^k := by exact one_le_pow₀ (by norm_num)
    have h8 : δ ≤ (2 : ℝ)^k * δ := by
      calc δ = 1 * δ := by ring
        _ ≤ (2 : ℝ)^k * δ := by gcongr
    linarith

  have h_cover : E_b1 ⊆ inner_shell ∪ Finset.biUnion (Finset.range K0) shell := by
    intro b₂ hb₂
    by_cases h : f b₂ < δ
    · exact Finset.mem_union.mpr (Or.inl (by simp only [inner_shell, Finset.mem_filter] <;> exact ⟨hb₂, h⟩))
    · have h' : δ ≤ f b₂ := by linarith
      have h_exists_k : ∃ (k : ℕ), f b₂ < (2 : ℝ)^(k+1) * δ := by
        refine ⟨K0, ?_⟩
        have h5 : (2 : ℝ)^(K0+1) * δ > 2 := by
          have h6 : (2 : ℝ)^(K0+1) > (2 : ℝ)^K0 := by gcongr <;> norm_num
          nlinarith
        linarith [h_f_le_two b₂ hb₂]
      let k := Nat.find h_exists_k
      have hk_lt : f b₂ < (2 : ℝ)^(k+1) * δ := Nat.find_spec h_exists_k
      have hk_ge : (2 : ℝ)^k * δ ≤ f b₂ := by
        by_cases h_k0 : k = 0
        · rw [h_k0] <;> simpa using h'
        · have h_pos : 0 < k := by omega
          have h_prev : ¬(f b₂ < (2 : ℝ)^((k - 1) + 1) * δ) := Nat.find_min h_exists_k (by omega)
          have h9 : (k - 1) + 1 = k := by omega
          rw [h9] at h_prev
          by_contra h10
          have h11 : f b₂ < (2 : ℝ)^k * δ := by linarith
          exact h_prev h11
      have hk_lt_K0 : k < K0 := by
        by_contra h10
        have h11 : k ≥ K0 := by omega
        have h12 : (2 : ℝ)^k ≥ (2 : ℝ)^K0 := pow_le_pow_right₀ (by norm_num) h11
        have h13 : (2 : ℝ)^k * δ ≥ (2 : ℝ)^K0 * δ := by gcongr
        linarith [hk_ge, h_f_le_two b₂ hb₂, hK0_gt]
      have h_in_shell : b₂ ∈ shell k := by
        simp only [shell, Finset.mem_filter] <;> exact ⟨hb₂, ⟨hk_ge, hk_lt⟩⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk_lt_K0, h_in_shell⟩))

  -- Inner shell bound
  have h_inner_sub : inner_shell ⊆ E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening δ (ℓ : Set Point2)) := by
    intro b₂ hb₂
    have hb₂' : b₂ ∈ E_b1 := (Finset.mem_filter.mp hb₂).1
    have h_x : f b₂ < δ := (Finset.mem_filter.mp hb₂).2
    have h6 : b₂ ∈ Metric.thickening δ (ℓ : Set Point2) := h_strip b₂ hb₂' δ hδ h_x
    simp only [Finset.mem_filter] <;> exact ⟨hb₂', h6⟩
  have h_inner_count : (inner_shell.card : ℝ) ≤ K * δ * (G₂.card : ℝ) := by
    let S := E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening δ (ℓ : Set Point2))
    have h1 : inner_shell.card ≤ S.card := Finset.card_le_card h_inner_sub
    have h2_enn : (S.card : ENNReal) ≤ ENNReal.ofReal (K * δ) * (G₂.card : ENNReal) := h_thin_bound δ (by linarith)
    have hKδ : 0 ≤ K * δ := by positivity
    have h_eq : ENNReal.ofReal (K * δ) * (G₂.card : ENNReal) = ENNReal.ofReal ((K * δ) * (G₂.card : ℝ)) := by
      have hG2_coe : (G₂.card : ENNReal) = ENNReal.ofReal ((G₂.card : ℝ)) := by simp
      rw [hG2_coe]
      have h : ENNReal.ofReal (K * δ) * ENNReal.ofReal ((G₂.card : ℝ)) = ENNReal.ofReal ((K * δ) * (G₂.card : ℝ)) := by
        rw [← ENNReal.ofReal_mul hKδ] <;> ring
      exact h
    rw [h_eq] at h2_enn
    have h3 : (S.card : ℝ) ≤ (K * δ) * (G₂.card : ℝ) := by
      have h4 : (S.card : ENNReal) = ENNReal.ofReal ((S.card : ℝ)) := by simp
      rw [h4] at h2_enn
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2_enn
    have h5 : (inner_shell.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h1
    exact le_trans h5 h3

  have h_inner_contrib : ∑ b₂ ∈ inner_shell, (max (f b₂) δ)^(-γ) ≤ K * (G₂.card : ℝ) * δ^(1-γ) := by
    have h1 : ∀ b₂ ∈ inner_shell, (max (f b₂) δ)^(-γ) ≤ δ^(-γ) := by
      intro b₂ hb₂
      have h_x : f b₂ < δ := (Finset.mem_filter.mp hb₂).2
      have h2 : max (f b₂) δ = δ := by rw [max_eq_right] <;> linarith
      rw [h2]
    calc
      ∑ b₂ ∈ inner_shell, (max (f b₂) δ)^(-γ)
        ≤ ∑ b₂ ∈ inner_shell, δ^(-γ) := Finset.sum_le_sum h1
      _ = (inner_shell.card : ℝ) * δ^(-γ) := by rw [Finset.sum_const] <;> ring
      _ ≤ (K * δ * (G₂.card : ℝ)) * δ^(-γ) := by gcongr
      _ = K * (G₂.card : ℝ) * δ^(1-γ) := by
        have h3 : δ * δ^(-γ) = δ^(1-γ) := by
          have h5 : (1-γ) = (1 : ℝ) + (-γ) := by ring
          have h6 : δ^(1-γ) = δ^(1 : ℝ) * δ^(-γ) := by
            rw [h5]
            exact Real.rpow_add hδ (1 : ℝ) (-γ)
          have h7 : δ^(1 : ℝ) = δ := by simp
          rw [h7] at h6
          exact h6.symm
        rw [show (K * δ * (G₂.card : ℝ)) * δ^(-γ) = K * (G₂.card : ℝ) * (δ * δ^(-γ)) by ring]
        rw [h3] <;> ring

  -- Shell k bound
  have h_shell_contrib : ∀ k ∈ Finset.range K0,
      ∑ b₂ ∈ shell k, (max (f b₂) δ)^(-γ) ≤
      2 * K * (G₂.card : ℝ) * δ^(1-γ) * (2 : ℝ)^(k * (1-γ)) := by
    intro k hk
    have h_sub : shell k ⊆ E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening ((2 : ℝ)^(k+1) * δ) (ℓ : Set Point2)) := by
      intro b₂ hb₂
      have hb₂' : b₂ ∈ E_b1 := (Finset.mem_filter.mp hb₂).1
      have h_x : f b₂ < (2 : ℝ)^(k+1) * δ := (Finset.mem_filter.mp hb₂).2.2
      have h_pos : 0 < (2 : ℝ)^(k+1) * δ := by positivity
      have h6 : b₂ ∈ Metric.thickening ((2 : ℝ)^(k+1) * δ) (ℓ : Set Point2) :=
        h_strip b₂ hb₂' ((2 : ℝ)^(k+1) * δ) h_pos h_x
      simp only [Finset.mem_filter] <;> exact ⟨hb₂', h6⟩
    have h_count : (shell k).card ≤ K * (2 : ℝ)^(k+1) * δ * (G₂.card : ℝ) := by
      let S := E_b1.filter (fun b₂ => b₂ ∈ Metric.thickening ((2 : ℝ)^(k+1) * δ) (ℓ : Set Point2))
      have h1 : (shell k).card ≤ S.card := Finset.card_le_card h_sub
      have h_rge : δ ≤ (2 : ℝ)^(k+1) * δ := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ)^(k+1) := one_le_pow₀ (by norm_num)
        calc δ = 1 * δ := by ring
          _ ≤ (2 : ℝ)^(k+1) * δ := by gcongr
      have h2_enn : (S.card : ENNReal) ≤ ENNReal.ofReal (K * ((2 : ℝ)^(k+1) * δ)) * (G₂.card : ENNReal) :=
        h_thin_bound ((2 : ℝ)^(k+1) * δ) h_rge
      have h_pos : 0 ≤ K * ((2 : ℝ)^(k+1) * δ) := by positivity
      have h_eq : ENNReal.ofReal (K * ((2 : ℝ)^(k+1) * δ)) * (G₂.card : ENNReal) =
          ENNReal.ofReal ((K * ((2 : ℝ)^(k+1) * δ)) * (G₂.card : ℝ)) := by
        have hG2_coe : (G₂.card : ENNReal) = ENNReal.ofReal ((G₂.card : ℝ)) := by simp
        rw [hG2_coe]
        have h : ENNReal.ofReal (K * ((2 : ℝ)^(k+1) * δ)) * ENNReal.ofReal ((G₂.card : ℝ)) =
            ENNReal.ofReal ((K * ((2 : ℝ)^(k+1) * δ)) * (G₂.card : ℝ)) := by
          rw [← ENNReal.ofReal_mul h_pos] <;> ring
        exact h
      rw [h_eq] at h2_enn
      have h3 : (S.card : ℝ) ≤ (K * ((2 : ℝ)^(k+1) * δ)) * (G₂.card : ℝ) := by
        have h4 : (S.card : ENNReal) = ENNReal.ofReal ((S.card : ℝ)) := by simp
        rw [h4] at h2_enn
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2_enn
      have h5 : ((shell k).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h1
      have h6 : ((shell k).card : ℝ) ≤ (K * ((2 : ℝ)^(k+1) * δ)) * (G₂.card : ℝ) := le_trans h5 h3
      have h7 : (K * ((2 : ℝ)^(k+1) * δ)) * (G₂.card : ℝ) = K * (2 : ℝ)^(k+1) * δ * (G₂.card : ℝ) := by ring
      rw [h7] at h6
      exact h6
    have h1 : ∀ b₂ ∈ shell k, (max (f b₂) δ)^(-γ) ≤ ((2 : ℝ)^k * δ)^(-γ) := by
      intro b₂ hb₂
      have h_x : (2 : ℝ)^k * δ ≤ f b₂ := (Finset.mem_filter.mp hb₂).2.1
      have h_pos : 0 < (2 : ℝ)^k * δ := by positivity
      have h_pos2 : 0 < max (f b₂) δ := by positivity
      have h4 : ((2 : ℝ)^k * δ)^γ ≤ (max (f b₂) δ)^γ := by
        have h51 : (2 : ℝ)^k * δ ≤ f b₂ := h_x
        have h52 : f b₂ ≤ max (f b₂) δ := Std.left_le_max
        have h5 : (2 : ℝ)^k * δ ≤ max (f b₂) δ := le_trans h51 h52
        exact Real.rpow_le_rpow (by positivity) h5 (by linarith)
      have h_pos3 : 0 < ((2 : ℝ)^k * δ)^γ := by positivity
      have h_pos4 : 0 < (max (f b₂) δ)^γ := by positivity
      have h7 : ((max (f b₂) δ)^γ)⁻¹ ≤ (((2 : ℝ)^k * δ)^γ)⁻¹ := by gcongr
      have h6 : (max (f b₂) δ)^(-γ) = ((max (f b₂) δ)^γ)⁻¹ := by
        rw [Real.rpow_neg] <;> positivity
      have h8 : ((2 : ℝ)^k * δ)^(-γ) = (((2 : ℝ)^k * δ)^γ)⁻¹ := by
        rw [Real.rpow_neg] <;> positivity
      rw [h6, h8]
      exact h7
    calc
      ∑ b₂ ∈ shell k, (max (f b₂) δ)^(-γ)
        ≤ ∑ b₂ ∈ shell k, ((2 : ℝ)^k * δ)^(-γ) := Finset.sum_le_sum h1
      _ = (shell k).card * ((2 : ℝ)^k * δ)^(-γ) := by rw [Finset.sum_const] <;> ring
      _ ≤ (K * (2 : ℝ)^(k+1) * δ * (G₂.card : ℝ)) * ((2 : ℝ)^k * δ)^(-γ) := by gcongr
      _ = 2 * K * (G₂.card : ℝ) * δ^(1-γ) * (2 : ℝ)^(k * (1-γ)) := by
        have h91 : ((2 : ℝ)^k * δ)^(-γ) = ((2 : ℝ)^k)^(-γ) * δ^(-γ) := by
          rw [Real.mul_rpow (by positivity) (by linarith)]
        have h92 : ((2 : ℝ)^k)^(-γ) = (2 : ℝ)^(-(k : ℝ) * γ) := by
          have h93 : ((2 : ℝ)^k : ℝ) = (2 : ℝ)^(k : ℝ) := by simp
          rw [h93]
          have h94 : ((2 : ℝ)^(k : ℝ))^(-γ) = (2 : ℝ)^((k : ℝ) * (-γ)) := by
            rw [Real.rpow_mul (by norm_num)]
          rw [h94]
          have h95 : (k : ℝ) * (-γ) = -(k : ℝ) * γ := by ring
          rw [h95]
        have h9 : ((2 : ℝ)^k * δ)^(-γ) = (2 : ℝ)^(-(k : ℝ) * γ) * δ^(-γ) := by
          rw [h91, h92]
        have h10 : (2 : ℝ)^(k+1) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
        have h11 : δ * δ^(-γ) = δ^(1-γ) := by
          have h5 : (1-γ) = (1 : ℝ) + (-γ) := by ring
          have h6 : δ^(1-γ) = δ^(1 : ℝ) * δ^(-γ) := by
            rw [h5]
            exact Real.rpow_add hδ (1 : ℝ) (-γ)
          have h7 : δ^(1 : ℝ) = δ := by simp
          rw [h7] at h6
          exact h6.symm
        have h12 : (2 : ℝ)^k * (2 : ℝ)^(-(k : ℝ) * γ) = (2 : ℝ)^((k : ℝ) * (1-γ)) := by
          have h121 : (2 : ℝ)^k = (2 : ℝ)^(k : ℝ) := by simp
          rw [h121]
          have h_exp : (k : ℝ) + (-(k : ℝ) * γ) = (k : ℝ) * (1-γ) := by ring
          have h : (2 : ℝ)^(k : ℝ) * (2 : ℝ)^(-(k : ℝ) * γ) = (2 : ℝ)^((k : ℝ) + (-(k : ℝ) * γ)) := by
            exact (Real.rpow_add (by norm_num) (k : ℝ) (-(k : ℝ) * γ)).symm
          rw [h, h_exp]
        have h13 : (2 : ℝ)^((k : ℝ) * (1-γ)) = (2 : ℝ)^(k * (1-γ)) := by norm_cast
        calc
          (K * (2 : ℝ)^(k+1) * δ * (G₂.card : ℝ)) * ((2 : ℝ)^k * δ)^(-γ)
            = (K * (2 * (2 : ℝ)^k) * δ * (G₂.card : ℝ)) * ((2 : ℝ)^(-(k : ℝ) * γ) * δ^(-γ)) := by rw [h9, h10]
          _ = 2 * K * (G₂.card : ℝ) * (δ * δ^(-γ)) * ((2 : ℝ)^k * (2 : ℝ)^(-(k : ℝ) * γ)) := by ring
          _ = 2 * K * (G₂.card : ℝ) * δ^(1-γ) * ((2 : ℝ)^k * (2 : ℝ)^(-(k : ℝ) * γ)) := by rw [h11]
          _ = 2 * K * (G₂.card : ℝ) * δ^(1-γ) * (2 : ℝ)^((k : ℝ) * (1-γ)) := by rw [h12]
          _ = 2 * K * (G₂.card : ℝ) * δ^(1-γ) * (2 : ℝ)^(k * (1-γ)) := by rw [h13]

  -- Geometric series
  let r_geo := (2 : ℝ)^(1-γ)
  have hr_gt_one : 1 < r_geo := by
    have h1 : 0 < 1 - γ := by linarith
    exact Real.one_lt_rpow (by norm_num) h1
  have h_geom_sum : ∑ k ∈ Finset.range K0, r_geo^k ≤ r_geo^K0 / (r_geo - 1) := by
    have h1 : ∑ k ∈ Finset.range K0, r_geo^k = (r_geo^K0 - 1) / (r_geo - 1) := by
      induction K0 with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp [show (r_geo - 1 : ℝ) ≠ 0 by linarith] <;> ring
    rw [h1]
    have h2 : 0 ≤ r_geo^K0 - 1 := by have h3 : 1 ≤ r_geo^K0 := one_le_pow₀ (by linarith); linarith
    have h4 : 0 < r_geo - 1 := by linarith
    have h5 : (r_geo^K0 - 1) / (r_geo - 1) ≤ r_geo^K0 / (r_geo - 1) := by
      apply div_le_div_of_nonneg_right
      · linarith
      · linarith
    exact h5
  have h_rK0_bound : r_geo^K0 ≤ (4 / δ)^(1-γ) := by
    have h1 : r_geo^K0 = (2 : ℝ)^((K0 : ℝ) * (1-γ)) := by
      have h11 : r_geo^K0 = (r_geo)^(K0 : ℝ) := by norm_cast
      rw [h11]
      have h12 : (r_geo)^(K0 : ℝ) = (2 : ℝ)^((K0 : ℝ) * (1-γ)) := by
        simp only [r_geo]
        have h : ((2 : ℝ)^(1-γ))^(K0 : ℝ) = (2 : ℝ)^((K0 : ℝ) * (1-γ)) := by
          have h2 : (2 : ℝ)^((1-γ) * (K0 : ℝ)) = ((2 : ℝ)^(1-γ))^(K0 : ℝ) := Real.rpow_mul (by norm_num) (1-γ) (K0 : ℝ)
          have h3 : (1-γ) * (K0 : ℝ) = (K0 : ℝ) * (1-γ) := by ring
          rw [h3] at h2
          exact h2.symm
        exact h
      exact h12
    rw [h1]
    have h2 : (2 : ℝ)^((K0 : ℝ) * (1-γ)) = ((2 : ℝ)^(K0 : ℝ))^(1-γ) := by
      exact Real.rpow_mul (by norm_num) (K0 : ℝ) (1-γ)
    rw [h2]
    have h3 : (2 : ℝ)^(K0 : ℝ) = (2 : ℝ)^K0 := by norm_cast
    rw [h3]
    exact Real.rpow_le_rpow (by positivity) h2pow_K0 (by linarith)

  have h_shell_total : ∑ k ∈ Finset.range K0, ∑ b₂ ∈ shell k, (max (f b₂) δ)^(-γ) ≤
      2 * K * (G₂.card : ℝ) * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range K0, (2 * K * (G₂.card : ℝ) * δ^(1-γ) * r_geo^k) := by
        apply Finset.sum_le_sum
        intro k hk
        have h_eq : (2 : ℝ)^(k * (1-γ)) = r_geo^k := by
          have h1 : ((2 : ℝ)^(1-γ))^(k : ℝ) = (2 : ℝ)^((k : ℝ) * (1-γ)) := by
            have h2 : (2 : ℝ)^((1-γ) * (k : ℝ)) = ((2 : ℝ)^(1-γ))^(k : ℝ) := Real.rpow_mul (by norm_num) (1-γ) (k : ℝ)
            have h3 : (1-γ) * (k : ℝ) = (k : ℝ) * (1-γ) := by ring
            rw [h3] at h2
            exact h2.symm
          have h2 : ((2 : ℝ)^(1-γ))^k = ((2 : ℝ)^(1-γ))^(k : ℝ) := by norm_cast
          have h3 : (2 : ℝ)^((k : ℝ) * (1-γ)) = ((2 : ℝ)^(1-γ))^k := by
            exact h1.symm.trans h2.symm
          simpa [r_geo] using h3
        rw [←h_eq]
        exact h_shell_contrib k hk
      _ = 2 * K * (G₂.card : ℝ) * δ^(1-γ) * ∑ k ∈ Finset.range K0, r_geo^k := by
        rw [Finset.mul_sum] <;> ring
      _ ≤ 2 * K * (G₂.card : ℝ) * δ^(1-γ) * (r_geo^K0 / (r_geo - 1)) := by gcongr
      _ ≤ 2 * K * (G₂.card : ℝ) * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) := by
        have h5 : δ^(1-γ) * r_geo^K0 ≤ (4 : ℝ)^(1-γ) := by
          calc δ^(1-γ) * r_geo^K0
            ≤ δ^(1-γ) * (4 / δ)^(1-γ) := by gcongr <;> exact h_rK0_bound
          _ = (4 : ℝ)^(1-γ) := by
            have h6 : δ^(1-γ) * (4 / δ)^(1-γ) = (δ * (4 / δ))^(1-γ) := by
              rw [←Real.mul_rpow (by linarith) (by positivity)]
            rw [h6]
            have h7 : δ * (4 / δ) = 4 := by field_simp [hδ.ne'] <;> ring
            rw [h7] <;> ring
        have h8 : 0 < r_geo - 1 := by linarith
        have h9 : r_geo - 1 = (2 : ℝ)^(1-γ) - 1 := by simp [r_geo]
        have h10 : 2 * K * (G₂.card : ℝ) * δ^(1-γ) * (r_geo^K0 / (r_geo - 1)) =
            2 * K * (G₂.card : ℝ) * (δ^(1-γ) * r_geo^K0) / (r_geo - 1) := by ring
        rw [h10]
        have h11 : 0 ≤ 2 * K * (G₂.card : ℝ) := by positivity
        have h12 : 2 * K * (G₂.card : ℝ) * (δ^(1-γ) * r_geo^K0) / (r_geo - 1) ≤
            2 * K * (G₂.card : ℝ) * (4 : ℝ)^(1-γ) / (r_geo - 1) := by
          gcongr <;> linarith
        rw [h9] at h12
        exact h12

  have h_nonneg : ∀ b₂ ∈ E_b1, 0 ≤ (max (f b₂) δ)^(-γ) := by intro b₂ _; positivity

  have h_union_sub_Eb1 : (inner_shell ∪ Finset.biUnion (Finset.range K0) shell) ⊆ E_b1 := by
    intro b₂ hb₂
    simp only [Finset.mem_union, Finset.mem_biUnion] at hb₂
    rcases hb₂ with (h | ⟨k, _, h⟩)
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have h_union_sum : ∑ b₂ ∈ (inner_shell ∪ Finset.biUnion (Finset.range K0) shell), (max (f b₂) δ)^(-γ) =
      ∑ b₂ ∈ inner_shell, (max (f b₂) δ)^(-γ) + ∑ k ∈ Finset.range K0, ∑ b₂ ∈ shell k, (max (f b₂) δ)^(-γ) := by
    have h_disj : Disjoint inner_shell (Finset.biUnion (Finset.range K0) shell) := by
      simp only [Finset.disjoint_left, Finset.mem_biUnion]
      intro b₂ h1 ⟨k, hk, h2⟩
      have h_disj_k : Disjoint inner_shell (shell k) := h_disj_inner k hk
      have h_disj_fun : ∀ (x : Point2), x ∈ inner_shell → x ∈ shell k → False := by
        simpa [Finset.disjoint_left] using h_disj_k
      exact h_disj_fun b₂ h1 h2
    rw [Finset.sum_union h_disj, Finset.sum_biUnion h_disj_shells]

  calc
    ∑ b₂ ∈ E_b1, (max (f b₂) δ)^(-γ)
      ≤ ∑ b₂ ∈ (inner_shell ∪ Finset.biUnion (Finset.range K0) shell), (max (f b₂) δ)^(-γ) :=
        Finset.sum_le_sum_of_subset_of_nonneg h_cover (fun b₂ hb₂ _ => h_nonneg b₂ (h_union_sub_Eb1 hb₂))
    _ = _ := h_union_sum
    _ ≤ K * (G₂.card : ℝ) * δ^(1-γ) + 2 * K * (G₂.card : ℝ) * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) := by
      gcongr <;> exact h_shell_total
    _ ≤ (2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * K * (G₂.card : ℝ) := by
      have h10 : δ^(1-γ) ≤ 1 := by
        have h11 : 0 ≤ 1 - γ := by linarith
        have h12 : δ^(1-γ) ≤ (1 : ℝ)^(1-γ) := Real.rpow_le_rpow hδ.le hδ_le_one h11
        have h13 : (1 : ℝ)^(1-γ) = 1 := by simp
        rw [h13] at h12
        exact h12
      have h12 : K * (G₂.card : ℝ) * δ^(1-γ) ≤ K * (G₂.card : ℝ) := by
        have h13 : 0 ≤ K * (G₂.card : ℝ) := by positivity
        have h14 : K * (G₂.card : ℝ) * δ^(1-γ) ≤ K * (G₂.card : ℝ) * (1 : ℝ) := mul_le_mul_of_nonneg_left h10 h13
        have h15 : K * (G₂.card : ℝ) * (1 : ℝ) = K * (G₂.card : ℝ) := by ring
        rw [h15] at h14
        exact h14
      have h14 : 0 < (2 : ℝ)^(1-γ) - 1 := by
        have h15 : 1 < (2 : ℝ)^(1-γ) := hr_gt_one
        linarith
      have h13 : 2 * K * (G₂.card : ℝ) * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) ≤
          8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) * K * (G₂.card : ℝ) := by
        have h15 : 0 ≤ (4 : ℝ)^(1-γ) := by positivity
        have h16 : 0 ≤ K * (G₂.card : ℝ) := by positivity
        calc
          2 * K * (G₂.card : ℝ) * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)
            = 2 * ((4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * (K * (G₂.card : ℝ)) := by ring
          _ ≤ 8 * ((4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * (K * (G₂.card : ℝ)) := by gcongr <;> norm_num
          _ = 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) * K * (G₂.card : ℝ) := by ring
      have h12' : K * (G₂.card : ℝ) * δ^(1-γ) ≤ 2 * K * (G₂.card : ℝ) := by
        have h_pos : 0 ≤ K * (G₂.card : ℝ) := by positivity
        linarith [h12]
      have h17 : K * (G₂.card : ℝ) * δ^(1-γ) + 2 * K * (G₂.card : ℝ) * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) ≤
          (2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * K * (G₂.card : ℝ) := by
        have h18 : (2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * K * (G₂.card : ℝ) =
            2 * K * (G₂.card : ℝ) + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1) * K * (G₂.card : ℝ) := by ring
        rw [h18]
        exact add_le_add h12' h13
      exact h17

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanEnergy
import MyLeanRepo.Kakeya.Assouad.WZ1.AngularIntegral
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanFactor


/-!
# Total energy bound for Kaufman projection theorem
-/

namespace Kakeya.Assouad

/-- Angular integral constant for Kaufman theorem. -/
noncomputable def kaufman_K_ang (β γ : ℝ) : ℝ :=
  2 * (Real.sqrt 2)^β + 2 * (Real.sqrt 2)^β * (2 : ℝ)^γ / (1 - (2 : ℝ)^(-(β-γ)))

/-- Frostman energy constant for Kaufman theorem. -/
noncomputable def kaufman_K_frost0 (α γ : ℝ) : ℝ :=
  (2 : ℝ)^α / ((2 : ℝ)^(α-γ) - 1) + 3 * (2 : ℝ)^γ

/-- Total constant in the Kaufman energy bound. -/
noncomputable def kaufman_total_const (C α β γ : ℝ) : ℝ :=
  let K_ang := kaufman_K_ang β γ
  let K_frost0 := kaufman_K_frost0 α γ
  (C + K_ang * K_frost0 * (1 + C) + K_ang) * C

/-- From Frostman at scale δ: `δ^(-γ) ≤ C * |F|`. -/
lemma frostman_delta_bound {F : DiscreteSet 2} {δ C α γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hα : 0 < α) (hγ : 0 < γ) (hγ_le_alpha : γ ≤ α)
    (hC : 0 ≤ C) (hne : F.Nonempty)
    (hFrost : F.IsFrostman δ α (ENNReal.ofReal C)) :
    δ^(-γ) ≤ C * (F.card : ℝ) := by
  obtain ⟨x, hx⟩ := hne
  have h1 : δ^(-γ) ≤ δ^(-α) := by
    have h2 : -γ ≥ -α := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ_le_one h2
  have h4 : ((F.filter (fun y => dist y x ≤ δ)).card : ℝ) ≤ C * δ^α * (F.card : ℝ) :=
    frostman_real_bound hδ hC hFrost (by linarith) hδ_le_one
  have h5 : x ∈ F.filter (fun y => dist y x ≤ δ) := by
    simp only [Finset.mem_filter]
    exact ⟨hx, by simp [hδ.le]⟩
  have h6 : 0 < (F.filter (fun y => dist y x ≤ δ)).card := Finset.card_pos.mpr ⟨x, h5⟩
  have h7 : (1 : ℝ) ≤ ((F.filter (fun y => dist y x ≤ δ)).card : ℝ) := by exact_mod_cast h6
  have h8 : (1 : ℝ) ≤ C * δ^α * (F.card : ℝ) := by
    calc (1 : ℝ)
      ≤ ((F.filter (fun y => dist y x ≤ δ)).card : ℝ) := h7
    _ ≤ C * δ^α * (F.card : ℝ) := h4
  have h10 : 0 < δ^α := by positivity
  have h11 : δ^(-α) ≤ C * (F.card : ℝ) := by
    have h12 : δ^(-α) = 1 / δ^α := by
      rw [Real.rpow_neg hδ.le] <;> field_simp
    rw [h12]
    have h13 : 1 / δ^α ≤ C * (F.card : ℝ) := by
      calc 1 / δ^α
        = (1 : ℝ) / δ^α := by rfl
      _ ≤ (C * δ^α * (F.card : ℝ)) / δ^α := by gcongr
      _ = C * (F.card : ℝ) := by field_simp [h10.ne']
    exact h13
  linarith

/-- For d > 1, `max(d*a, δ)^(-γ) ≤ max(a, δ)^(-γ)`. -/
lemma angular_factorization_far {δ γ d a : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    (hd : 1 < d) (ha : 0 ≤ a) :
    (max (d * a) δ)^(-γ) ≤ (max a δ)^(-γ) := by
  have h1 : max a δ ≤ max (d * a) δ := by
    have h2 : a ≤ d * a := by nlinarith
    exact max_le_max h2 (by linarith)
  have h_pos1 : 0 < max a δ := by positivity
  have h_pos2 : 0 < max (d * a) δ := by positivity
  have h3 : (max (d * a) δ)^γ ≥ (max a δ)^γ := Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h4 : (max (d * a) δ)^(-γ) = 1 / (max (d * a) δ)^γ := by
    rw [Real.rpow_neg (by positivity)] <;> field_simp
  have h5 : (max a δ)^(-γ) = 1 / (max a δ)^γ := by
    rw [Real.rpow_neg (by positivity)] <;> field_simp
  rw [h4, h5]
  exact one_div_le_one_div_of_le (by positivity) h3

/-- Total energy bound for Kaufman's projection theorem. -/
lemma kaufman_total_energy_bound
    {F Λ : DiscreteSet 2} {δ C α β γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ_lt_alpha : γ < α) (hγ_lt_beta : γ < β)
    (hC : 0 ≤ C) (hC_ge_one : 1 ≤ C)
    (hFrostF : F.IsFrostman δ α (ENNReal.ofReal C))
    (hFrostΛ : Λ.IsFrostman δ β (ENNReal.ofReal C))
    (hsepF : F.IsDeltaSeparated δ)
    (hballF : F.IsInUnitBall)
    (hunitΛ : ∀ θ ∈ Λ, ‖θ‖ = 1)
    (hneF : F.Nonempty) (hneΛ : Λ.Nonempty) :
    ∑ θ ∈ Λ, ∑ x ∈ F, ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) ≤
    kaufman_total_const C α β γ * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
  classical
  set K_ang : ℝ := kaufman_K_ang β γ with hK_ang
  set K_frost0 : ℝ := kaufman_K_frost0 α γ with hK_frost0
  set K_frost : ℝ := K_frost0 * (1 + C) with hK_frost

  have hKang_pos : 0 ≤ K_ang := by
    have h_pos : 0 < kaufman_K_ang β γ := by
      dsimp only [kaufman_K_ang]
      have h1 : 0 < (Real.sqrt 2)^β := by positivity
      have h2 : 0 < (2 : ℝ)^γ := by positivity
      have h3 : 0 < 1 - (2 : ℝ)^(-(β-γ)) := by
        have h4 : 0 < β - γ := by linarith
        have h5 : (2 : ℝ)^(-(β-γ)) < 1 := by
          have h6 : (2 : ℝ)^(-(β-γ)) < (2 : ℝ)^(0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
          simpa using h6
        linarith
      positivity
    rw [hK_ang]
    exact h_pos.le

  have hδ_bound : δ^(-γ) ≤ C * (F.card : ℝ) :=
    frostman_delta_bound hδ hδ_le_one hα hγ (by linarith) hC hneF hFrostF

  have h_energy : ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) ≤ K_frost * (F.card : ℝ)^2 := by
    have h := frostman_energy_bound hδ hδ_le_one hα hγ hγ_lt_alpha hC hFrostF hsepF hballF
    have h_eq : ((2 : ℝ)^α / ((2 : ℝ)^(α-γ) - 1) + 3 * (2 : ℝ)^γ) * (1 + C) * (F.card : ℝ)^2 = K_frost * (F.card : ℝ)^2 := by
      congr 1
      <;> simp [K_frost, K_frost0, hK_frost0] <;> ring
    rw [h_eq] at h
    exact h

  have h_ang : ∀ (v : Point2), ‖v‖ = 1 → ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) ≤ K_ang * C * (Λ.card : ℝ) := by
    intro v hv
    have h := angular_integral_bound hδ hδ_le_one hβ hγ hγ_lt_beta hC hFrostΛ hunitΛ v hv
    have h_eq : (2 * (Real.sqrt 2)^β + 2 * (Real.sqrt 2)^β * (2 : ℝ)^γ / (1 - (2 : ℝ)^(-(β-γ)))) * C * (Λ.card : ℝ) = K_ang * C * (Λ.card : ℝ) := by
      congr 1
      <;> simp [K_ang, hK_ang] <;> ring
    rw [h_eq] at h
    exact h

  have h_rewrite : ∑ θ ∈ Λ, ∑ x ∈ F, ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) =
      ∑ p ∈ (F ×ˢ F), ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) := by
    have h1 : ∀ θ ∈ Λ, ∑ x ∈ F, ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) =
        ∑ p ∈ (F ×ˢ F), (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) := by
      intro θ _
      rw [Finset.sum_product]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]

  let S_diag : Finset (Point2 × Point2) := (F ×ˢ F).filter (fun p => p.1 = p.2)
  let S_off : Finset (Point2 × Point2) := (F ×ˢ F).filter (fun p => p.1 ≠ p.2)

  have h_part : (F ×ˢ F) = S_diag ∪ S_off := by
    ext ⟨x, y⟩
    simp only [S_diag, S_off, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    <;> by_cases h : x = y <;> simp [h] <;> tauto
  have h_disj : Disjoint S_diag S_off := by
    simp only [S_diag, S_off, Finset.disjoint_left, Finset.mem_filter] <;> tauto

  let KAC : ℝ := K_ang * C * (Λ.card : ℝ)
  have hKAC_nonneg : 0 ≤ KAC := by
    dsimp only [KAC]
    have h1 : 0 ≤ (Λ.card : ℝ) := by exact_mod_cast Nat.cast_nonneg _
    exact mul_nonneg (mul_nonneg hKang_pos hC) h1

  -- Pointwise off-diagonal bound
  have h_off_point : ∀ p ∈ S_off, ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
      (1 + ‖p.1 - p.2‖^(-γ)) * KAC := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    set d : ℝ := ‖p.1 - p.2‖ with hd_def
    have hd_pos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    set v : Point2 := d⁻¹ • (p.1 - p.2) with hv_def
    have hv_unit : ‖v‖ = 1 := by
      have h1 : ‖v‖ = ‖(d⁻¹ : ℝ)‖ * ‖p.1 - p.2‖ := by
        rw [hv_def] <;> exact norm_smul (d⁻¹ : ℝ) (p.1 - p.2)
      have h2 : ‖(d⁻¹ : ℝ)‖ = d⁻¹ := by
        have hpos : 0 < d⁻¹ := by positivity
        have h3 : ‖(d⁻¹ : ℝ)‖ = |d⁻¹| := Real.norm_eq_abs (d⁻¹)
        rw [h3, abs_of_pos hpos]
      rw [h1, h2]
      have h4 : ‖p.1 - p.2‖ = d := hd_def.symm
      rw [h4]
      field_simp [hd_pos.ne'] <;> ring
    have h_inner : ∀ θ : Point2, |inner ℝ θ (p.1 - p.2)| = d * |inner ℝ θ v| := by
      intro θ
      have h1 : inner ℝ θ v = d⁻¹ * inner ℝ θ (p.1 - p.2) := by
        rw [hv_def, inner_smul_right] <;> ring
      have hpos : 0 < d⁻¹ := by positivity
      have h_abs2 : |d⁻¹ * inner ℝ θ (p.1 - p.2)| = d⁻¹ * |inner ℝ θ (p.1 - p.2)| := by
        rw [abs_mul, abs_of_pos hpos]
      calc |inner ℝ θ (p.1 - p.2)|
        = d * (d⁻¹ * |inner ℝ θ (p.1 - p.2)|) := by field_simp [hd_pos.ne'] <;> ring
      _ = d * |d⁻¹ * inner ℝ θ (p.1 - p.2)| := by rw [←h_abs2]
      _ = d * |inner ℝ θ v| := by rw [h1]
    by_cases hnear : d ≤ 1
    · -- Near case
      have h1 : ∀ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
          d^(-γ) * (max (|inner ℝ θ v|) δ)^(-γ) := by
        intro θ hθ
        exact angular_factorization hδ hγ (hunitΛ θ hθ) hne hnear
      have h2 : ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
          d^(-γ) * ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) := by
        calc ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ)
          ≤ ∑ θ ∈ Λ, d^(-γ) * (max (|inner ℝ θ v|) δ)^(-γ) := Finset.sum_le_sum (fun θ hθ => h1 θ hθ)
        _ = d^(-γ) * ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) := by rw [Finset.mul_sum]
      have h3 : ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) ≤ KAC := h_ang v hv_unit
      have h5 : 0 ≤ d^(-γ) := by positivity
      have h6 : ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤ d^(-γ) * KAC := by
        calc ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ)
          ≤ d^(-γ) * ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) := h2
        _ ≤ d^(-γ) * KAC := by exact mul_le_mul_of_nonneg_left h3 h5
      have h7 : d^(-γ) * KAC ≤ (1 + d^(-γ)) * KAC := by
        have h8 : d^(-γ) ≤ 1 + d^(-γ) := by linarith
        exact mul_le_mul_of_nonneg_right h8 hKAC_nonneg
      exact h6.trans h7
    · -- Far case
      have hfar : 1 < d := by linarith
      have h1 : ∀ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
          (max (|inner ℝ θ v|) δ)^(-γ) := by
        intro θ hθ
        have h_abs : |inner ℝ θ (p.1 - p.2)| = d * |inner ℝ θ v| := h_inner θ
        rw [h_abs]
        exact angular_factorization_far hδ hγ hfar (by positivity)
      have h2 : ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
          ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) := Finset.sum_le_sum (fun θ hθ => h1 θ hθ)
      have h3 : ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) ≤ KAC := h_ang v hv_unit
      have h6 : ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤ KAC := h2.trans h3
      have h7 : KAC ≤ (1 + d^(-γ)) * KAC := by
        have hpos2 : 0 ≤ d^(-γ) := by positivity
        have h8 : (1 : ℝ) ≤ 1 + d^(-γ) := by linarith
        have h9 : (1 : ℝ) * KAC ≤ (1 + d^(-γ)) * KAC := by
          exact mul_le_mul_of_nonneg_right h8 hKAC_nonneg
        simpa using h9
      exact h6.trans h7

  -- Diagonal bound
  have h_diag : ∑ p ∈ S_diag, ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
      C^2 * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
    have h1 : S_diag = F.image (fun x => (x, x)) := by
      ext p
      simp only [S_diag, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
      constructor
      · rintro ⟨h, h_eq⟩
        have hpe : p = (p.1, p.1) := by
          ext <;> simp [h_eq] <;> tauto
        rw [hpe]
        exact ⟨p.1, h.1, by simp⟩
      · rintro ⟨x, hx, hpe⟩
        have h1 : p.1 = x := by
          have h : (x, x).1 = p.1 := by rw [hpe]
          simpa using h.symm
        have h2 : p.2 = x := by
          have h : (x, x).2 = p.2 := by rw [hpe]
          simpa using h.symm
        have h3 : p.1 = p.2 := by rw [h1, h2]
        exact ⟨⟨by rw [h1] <;> exact hx, by rw [h2] <;> exact hx⟩, h3⟩
    rw [h1]
    have h_inj : Set.InjOn (fun x : Point2 => (x, x)) (F : Set Point2) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image h_inj]
    have h4 : ∀ (x : Point2), ∀ θ ∈ Λ, (max (|inner ℝ θ (x - x)|) δ)^(-γ) = δ^(-γ) := by
      intro x θ _
      have h5 : inner ℝ θ (x - x) = 0 := by simp
      have h6 : |inner ℝ θ (x - x)| = 0 := by rw [h5] <;> simp
      rw [h6]
      have h7 : max (0 : ℝ) δ = δ := by rw [max_eq_right] <;> linarith
      rw [h7]
    have h_sum1 : ∀ x ∈ F, ∑ θ ∈ Λ, (max (|inner ℝ θ (x - x)|) δ)^(-γ) = (Λ.card : ℝ) * δ^(-γ) := by
      intro x hx
      have h : ∑ θ ∈ Λ, (max (|inner ℝ θ (x - x)|) δ)^(-γ) = ∑ θ ∈ Λ, δ^(-γ) :=
        Finset.sum_congr rfl (fun θ hθ => h4 x θ hθ)
      rw [h]
      simp only [Finset.sum_const]
      <;> ring
    have h2 : ∑ x ∈ F, ∑ θ ∈ Λ, (max (|inner ℝ θ (x - x)|) δ)^(-γ) =
        (F.card : ℝ) * (Λ.card : ℝ) * δ^(-γ) := by
      rw [Finset.sum_congr rfl h_sum1]
      simp only [Finset.sum_const]
      <;> ring
    rw [h2]
    have h5 : δ^(-γ) ≤ C * (F.card : ℝ) := hδ_bound
    have h6 : (F.card : ℝ) * (Λ.card : ℝ) * δ^(-γ) ≤ C^2 * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
      have h7 : 0 ≤ (F.card : ℝ) := by exact_mod_cast Nat.cast_nonneg _
      have h8 : 0 ≤ (Λ.card : ℝ) := by exact_mod_cast Nat.cast_nonneg _
      have h9 : C ≤ C^2 := by nlinarith
      have h10 : 0 ≤ (F.card : ℝ) * (Λ.card : ℝ) := mul_nonneg h7 h8
      have h11 : (F.card : ℝ) * (Λ.card : ℝ) * δ^(-γ) ≤ (F.card : ℝ) * (Λ.card : ℝ) * (C * (F.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hδ_bound h10
      have h12 : 0 ≤ (F.card : ℝ)^2 * (Λ.card : ℝ) := mul_nonneg (sq_nonneg _) h8
      calc (F.card : ℝ) * (Λ.card : ℝ) * δ^(-γ)
        ≤ (F.card : ℝ) * (Λ.card : ℝ) * (C * (F.card : ℝ)) := h11
      _ = C * (F.card : ℝ)^2 * (Λ.card : ℝ) := by ring
      _ ≤ C^2 * (F.card : ℝ)^2 * (Λ.card : ℝ) := by nlinarith
    exact h6

  -- Off-diagonal sum bound
  have h_off_sum : ∑ p ∈ S_off, ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
      K_ang * C * (1 + K_frost) * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
    let g : Point2 × Point2 → ℝ := fun p => (1 + ‖p.1 - p.2‖^(-γ)) * KAC
    have h1 : ∑ p ∈ S_off, ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤ ∑ p ∈ S_off, g p :=
      Finset.sum_le_sum h_off_point
    have h21 : ∀ p ∈ S_off, g p = KAC * (1 + ‖p.1 - p.2‖^(-γ)) := by
      intro p _; dsimp only [g, KAC]; ring
    have h2 : ∑ p ∈ S_off, g p = KAC * ∑ p ∈ S_off, (1 + ‖p.1 - p.2‖^(-γ)) := by
      rw [Finset.sum_congr rfl h21, Finset.mul_sum]
      <;> ring
    rw [h2] at h1
    have h3 : ∑ p ∈ S_off, (1 + ‖p.1 - p.2‖^(-γ)) =
        (S_off.card : ℝ) + ∑ p ∈ S_off, ‖p.1 - p.2‖^(-γ) := by
      rw [Finset.sum_add_distrib]
      <;> simp
    have h4 : (S_off.card : ℝ) ≤ (F.card : ℝ)^2 := by
      have h5 : S_off ⊆ F ×ˢ F := Finset.filter_subset _ _
      have h6 : S_off.card ≤ (F ×ˢ F).card := Finset.card_le_card h5
      have h7 : (F ×ˢ F).card = (F.card)^2 := by rw [Finset.card_product] <;> ring
      rw [h7] at h6
      exact_mod_cast h6
    have h5 : ∑ p ∈ S_off, ‖p.1 - p.2‖^(-γ) ≤ ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) := by
      have h51 : ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) = ∑ p ∈ F ×ˢ F, (dist p.1 p.2)^(-γ) := by
        rw [Finset.sum_product] <;> rfl
      rw [h51]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p _ _
      have h52 : ‖p.1 - p.2‖ = dist p.1 p.2 := by
        rw [dist_eq_norm]
      rw [h52] <;> positivity
    have h6 : ∑ p ∈ S_off, (1 + ‖p.1 - p.2‖^(-γ)) ≤
        (F.card : ℝ)^2 + K_frost * (F.card : ℝ)^2 := by
      rw [h3]
      have h7 : (S_off.card : ℝ) + ∑ p ∈ S_off, ‖p.1 - p.2‖^(-γ) ≤
          (F.card : ℝ)^2 + ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) := by
        exact add_le_add h4 h5
      calc (S_off.card : ℝ) + ∑ p ∈ S_off, ‖p.1 - p.2‖^(-γ)
        ≤ (F.card : ℝ)^2 + ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) := h7
      _ ≤ (F.card : ℝ)^2 + K_frost * (F.card : ℝ)^2 := by
        exact add_le_add_right h_energy ((F.card : ℝ)^2)
    have h7 : (F.card : ℝ)^2 + K_frost * (F.card : ℝ)^2 = (1 + K_frost) * (F.card : ℝ)^2 := by ring
    rw [h7] at h6
    have h_final : KAC * ∑ p ∈ S_off, (1 + ‖p.1 - p.2‖^(-γ)) ≤ KAC * ((1 + K_frost) * (F.card : ℝ)^2) :=
      mul_le_mul_of_nonneg_left h6 hKAC_nonneg
    have h9 : KAC * ((1 + K_frost) * (F.card : ℝ)^2) = K_ang * C * (1 + K_frost) * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
      dsimp only [KAC] <;> ring
    rw [h9] at h_final
    exact h1.trans h_final

  -- Total
  have h_const : kaufman_total_const C α β γ = C^2 + K_ang * C * (1 + K_frost) := by
    unfold kaufman_total_const
    have hK : K_frost = K_frost0 * (1 + C) := by simp [K_frost, hK_frost0]
    simp only [hK_ang, hK_frost0]
    rw [hK] <;> ring
  have h_sum : ∑ p ∈ (F ×ˢ F), ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) ≤
      kaufman_total_const C α β γ * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
    rw [h_part, Finset.sum_union h_disj]
    have h : C^2 * (F.card : ℝ)^2 * (Λ.card : ℝ) + K_ang * C * (1 + K_frost) * (F.card : ℝ)^2 * (Λ.card : ℝ) =
        kaufman_total_const C α β γ * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
      rw [h_const] <;> ring
    calc
      ∑ p ∈ S_diag, ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ) +
          ∑ p ∈ S_off, ∑ θ ∈ Λ, (max (|inner ℝ θ (p.1 - p.2)|) δ)^(-γ)
        ≤ C^2 * (F.card : ℝ)^2 * (Λ.card : ℝ) +
            K_ang * C * (1 + K_frost) * (F.card : ℝ)^2 * (Λ.card : ℝ) :=
          add_le_add h_diag h_off_sum
      _ = kaufman_total_const C α β γ * (F.card : ℝ)^2 * (Λ.card : ℝ) := h

  rw [h_rewrite]
  exact h_sum

end Kakeya.Assouad

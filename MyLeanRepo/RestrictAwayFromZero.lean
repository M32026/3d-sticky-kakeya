module

/-
# Restrict Measure Away From Zero
-/

public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set

namespace WeakTwoEndsSumProduct

lemma restrict_away_from_zero
    {κ C_mu : ℝ} {μ : Measure ℝ}
    (hμ : IsAllScaleFrostman κ C_mu μ)
    (h_supp : μ.support ⊆ Set.Icc 0 1) :
    ∃ (a : ℝ) (μ' : Measure ℝ),
      0 < a ∧
      a = (2 * C_mu)^(-1/κ) ∧
      μ'.support ⊆ Set.Icc a 1 ∧
      μ'.support ⊆ μ.support ∧
      IsAllScaleFrostman κ (2 * C_mu) μ' := by
  have hκ_pos : 0 < κ := hμ.2.1
  have hC_pos : 0 < C_mu := hμ.2.2.1
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have h_frost := hμ.2.2.2

  set a : ℝ := (2 * C_mu)^(-1/κ) with ha_def
  have h2C_pos : 0 < 2 * C_mu := by positivity
  have ha_pos : 0 < a := Real.rpow_pos_of_pos h2C_pos _

  have h_a_pow : a ^ κ = 1 / (2 * C_mu) := by
    have h_pos_base : 0 ≤ (2 * C_mu) := by positivity
    have h_exp : (-1/κ : ℝ) * κ = -1 := by field_simp [hκ_pos.ne'] <;> ring
    have h1 : a ^ κ = ((2 * C_mu)^(-1/κ)) ^ κ := by rw [ha_def]
    rw [h1]
    have h2 : ((2 * C_mu)^(-1/κ)) ^ κ = (2 * C_mu)^((-1/κ) * κ) := by
      rw [← Real.rpow_mul h_pos_base]
    rw [h2, h_exp]
    have h4 : (2 * C_mu)^(-1 : ℝ) = ((2 * C_mu)^(1 : ℝ))⁻¹ := by
      rw [Real.rpow_neg h_pos_base]
    rw [h4]
    have h5 : (2 * C_mu)^(1 : ℝ) = (2 * C_mu) := Real.rpow_one _
    rw [h5]
    field_simp [hC_pos.ne']

  have h_cover : Set.Icc (0 : ℝ) a ⊆ Set.Icc (a - a) (a + a) := by
    intro x hx
    have h1 : a - a ≤ x := by simpa using hx.1
    have h2 : x ≤ a + a := by linarith [ha_pos, hx.2]
    exact ⟨h1, h2⟩

  have h_frost_a : μ (Set.Icc (a - a) (a + a)) ≤ ENNReal.ofReal (C_mu * a ^ κ) :=
    h_frost a a ha_pos

  have h_mu_low : μ (Set.Icc (0 : ℝ) a) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h2 : C_mu * a ^ κ = (1 / 2 : ℝ) := by
      rw [h_a_pow] <;> field_simp [hC_pos.ne'] <;> ring
    calc μ (Set.Icc (0 : ℝ) a)
      ≤ μ (Set.Icc (a - a) (a + a)) := measure_mono h_cover
    _ ≤ ENNReal.ofReal (C_mu * a ^ κ) := h_frost_a
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by rw [h2]

  have h_compl_null : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    have h1 : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ μ.supportᶜ := by
      intro x hx hxs
      have h2 : x ∈ Set.Icc (0 : ℝ) 1 := h_supp hxs
      exact hx h2
    exact measure_mono_null h1 Measure.measure_compl_support

  have h_mu01 : μ (Set.Icc (0 : ℝ) 1) = 1 := by
    have h_univ : Set.univ = (Set.Icc (0 : ℝ) 1) ∪ ((Set.Icc (0 : ℝ) 1)ᶜ) := by
      ext x; simp
    have h_meas2 : MeasurableSet ((Set.Icc (0 : ℝ) 1)ᶜ) := measurableSet_Icc.compl
    have h_disj : Disjoint (Set.Icc (0 : ℝ) 1) ((Set.Icc (0 : ℝ) 1)ᶜ) := by
      exact HasSubset.Subset.disjoint_compl_right fun ⦃a⦄ a_1 => a_1
    have h_eq : μ Set.univ = μ (Set.Icc (0 : ℝ) 1) + μ ((Set.Icc (0 : ℝ) 1)ᶜ) := by
      rw [h_univ]
      exact measure_union h_disj h_meas2
    rw [h_eq, h_compl_null, add_zero] at hμ_univ
    exact hμ_univ

  have h_union_ab : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) a ∪ Set.Icc a 1 := by
    intro x hx
    by_cases h : x ≤ a
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨by linarith, hx.2⟩

  have h_subadd : μ (Set.Icc (0 : ℝ) 1) ≤ μ (Set.Icc (0 : ℝ) a) + μ (Set.Icc a 1) := by
    calc μ (Set.Icc (0 : ℝ) 1)
      ≤ μ (Set.Icc (0 : ℝ) a ∪ Set.Icc a 1) := measure_mono h_union_ab
    _ ≤ μ (Set.Icc (0 : ℝ) a) + μ (Set.Icc a 1) := measure_union_le _ _

  have h_mu_high : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ (Set.Icc a 1) := by
    by_contra h
    have h' : μ (Set.Icc a 1) < ENNReal.ofReal (1 / 2 : ℝ) := lt_of_not_ge h
    have h_step1 : μ (Set.Icc (0 : ℝ) a) + μ (Set.Icc a 1) ≤
        ENNReal.ofReal (1 / 2 : ℝ) + μ (Set.Icc a 1) := by
      exact add_le_add_left h_mu_low (μ (Set.Icc a 1))
    have h_pos2 : ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_step2 : ENNReal.ofReal (1 / 2 : ℝ) + μ (Set.Icc a 1) <
        ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) :=
      ENNReal.add_lt_add_left h_pos2 h'
    have h_step3 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = (1 : ENNReal) := by
      have h_add : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_add] <;> norm_num
      rw [h_add]
      have h2 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = (1 : ℝ) := by norm_num
      rw [h2]
      simp
    have h_sum : μ (Set.Icc (0 : ℝ) a) + μ (Set.Icc a 1) < (1 : ENNReal) := by
      calc _ ≤ ENNReal.ofReal (1 / 2 : ℝ) + μ (Set.Icc a 1) := h_step1
           _ < ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) := h_step2
           _ = (1 : ENNReal) := h_step3
    rw [h_mu01] at h_subadd
    exact not_le.mpr h_sum h_subadd

  set μ_restrict : Measure ℝ := μ.restrict (Set.Icc a 1) with hμ_restrict_def
  set μ' : Measure ℝ := (μ (Set.Icc a 1))⁻¹ • μ_restrict with hμ'_def

  have h_mu_a1_ne_zero : μ (Set.Icc a 1) ≠ 0 := by
    have h_pos : (0 : ENNReal) < ENNReal.ofReal (1 / 2 : ℝ) := by positivity
    exact ne_of_gt (h_pos.trans_le h_mu_high)

  have h_mu_a1_ne_top : μ (Set.Icc a 1) ≠ ⊤ := by
    have h_le : μ (Set.Icc a 1) ≤ μ Set.univ := measure_mono (by simp)
    have h9 : μ Set.univ = 1 := hμ_univ
    rw [h9] at h_le
    exact h_le.trans_lt ENNReal.one_lt_top |>.ne

  have hμ'_univ : μ' Set.univ = 1 := by
    have h1 : μ_restrict Set.univ = μ (Set.Icc a 1) := by
      rw [hμ_restrict_def, Measure.restrict_apply MeasurableSet.univ] <;> simp
    have h2 : μ' Set.univ = (μ (Set.Icc a 1))⁻¹ * μ_restrict Set.univ := by
      simp [hμ'_def, Measure.smul_apply] <;> rfl
    rw [h2, h1]
    rw [ENNReal.inv_mul_cancel h_mu_a1_ne_zero h_mu_a1_ne_top]

  have h_restrict_support : μ_restrict.support ⊆ Set.Icc a 1 := by
    have h1 : μ_restrict.support ⊆ closure (Set.Icc a 1) ∩ μ.support :=
      Measure.support_restrict_subset
    have h2 : μ_restrict.support ⊆ closure (Set.Icc a 1) := h1.trans (by simp)
    have h3 : closure (Set.Icc a 1) = Set.Icc a 1 := IsClosed.closure_eq isClosed_Icc
    rw [h3] at h2; exact h2

  have hc_ne_zero : (μ (Set.Icc a 1))⁻¹ ≠ 0 := by
    intro h
    have h' : μ (Set.Icc a 1) = ⊤ := ENNReal.inv_eq_zero.mp h
    exact h_mu_a1_ne_top h'

  have hμ'_support_eq : μ'.support = μ_restrict.support := by
    ext x
    constructor
    · intro hx
      by_contra h9
      let U := μ_restrict.supportᶜ
      have hU_open : IsOpen U := Measure.isOpen_compl_support
      have hxU : x ∈ U := h9
      have hμU : μ_restrict U = 0 := Measure.measure_compl_support
      have hνU : μ' U = 0 := by
        have h_eq : μ' U = (μ (Set.Icc a 1))⁻¹ * μ_restrict U := by
          simp [hμ'_def, Measure.smul_apply] <;> rfl
        rw [h_eq, hμU] <;> ring
      have h10 : U ⊆ μ'.supportᶜ := by
        rw [Measure.compl_support_eq_sUnion]
        intro y hy
        exact ⟨U, ⟨hU_open, hνU⟩, hy⟩
      exact h10 hxU hx
    · intro hx
      by_contra h9
      let U := μ'.supportᶜ
      have hU_open : IsOpen U := Measure.isOpen_compl_support
      have hxU : x ∈ U := h9
      have hνU : μ' U = 0 := Measure.measure_compl_support
      have h11 : (μ (Set.Icc a 1))⁻¹ * μ_restrict U = 0 := by
        have h_eq : μ' U = (μ (Set.Icc a 1))⁻¹ * μ_restrict U := by
          simp [hμ'_def, Measure.smul_apply] <;> rfl
        rw [h_eq] at hνU
        exact hνU
      have h12 : μ_restrict U = 0 :=
        (mul_eq_zero.mp h11).resolve_left hc_ne_zero
      have h13 : U ⊆ μ_restrict.supportᶜ := by
        rw [Measure.compl_support_eq_sUnion]
        intro y hy
        exact ⟨U, ⟨hU_open, h12⟩, hy⟩
      exact h13 hxU hx

  have hμ'_supp : μ'.support ⊆ Set.Icc a 1 := by
    rw [hμ'_support_eq]
    exact h_restrict_support

  have hμ'_supp_orig : μ'.support ⊆ μ.support := by
    rw [hμ'_support_eq]
    have h1 : μ_restrict.support ⊆ μ.support :=
      (Measure.support_restrict_subset).trans (by simp)
    exact h1

  have hμ'_frost : ∀ (x r : ℝ), 0 < r →
      μ' (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal ((2 * C_mu) * r ^ κ) := by
    intro x r hr
    have h1 : μ' (Set.Icc (x - r) (x + r)) =
        (μ (Set.Icc a 1))⁻¹ * μ_restrict (Set.Icc (x - r) (x + r)) := by
      simp [hμ'_def, Measure.smul_apply] <;> rfl
    rw [h1]
    have h2 : μ_restrict (Set.Icc (x - r) (x + r)) ≤ μ (Set.Icc (x - r) (x + r)) := by
      rw [hμ_restrict_def, Measure.restrict_apply measurableSet_Icc]
      have h3 : (Set.Icc (x - r) (x + r)) ∩ (Set.Icc a 1) ⊆ Set.Icc (x - r) (x + r) := by
        intro z hz; exact hz.1
      exact measure_mono h3
    have h3 : (μ (Set.Icc a 1))⁻¹ ≤ (2 : ENNReal) := by
      have h4 : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ (Set.Icc a 1) := h_mu_high
      have h5 : (μ (Set.Icc a 1))⁻¹ ≤ (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ :=
        ENNReal.inv_le_inv.mpr h4
      have h6 : (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ = (2 : ENNReal) := by simp
      rw [h6] at h5; exact h5
    have h4 : (μ (Set.Icc a 1))⁻¹ * μ_restrict (Set.Icc (x - r) (x + r)) ≤
        (2 : ENNReal) * μ (Set.Icc (x - r) (x + r)) := by
      calc (μ (Set.Icc a 1))⁻¹ * μ_restrict (Set.Icc (x - r) (x + r))
        ≤ (μ (Set.Icc a 1))⁻¹ * μ (Set.Icc (x - r) (x + r)) := by gcongr
      _ ≤ (2 : ENNReal) * μ (Set.Icc (x - r) (x + r)) := by gcongr <;> exact h3
    have h5 : (2 : ENNReal) * μ (Set.Icc (x - r) (x + r)) ≤
        (2 : ENNReal) * ENNReal.ofReal (C_mu * r ^ κ) := by
      gcongr <;> exact h_frost x r hr
    have h6 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_cast
    have h7 : (2 : ENNReal) * ENNReal.ofReal (C_mu * r ^ κ) =
        ENNReal.ofReal ((2 * C_mu) * r ^ κ) := by
      rw [h6]
      rw [← ENNReal.ofReal_mul (by positivity)]
      <;> ring_nf
    calc (μ (Set.Icc a 1))⁻¹ * μ_restrict (Set.Icc (x - r) (x + r))
      ≤ (2 : ENNReal) * μ (Set.Icc (x - r) (x + r)) := h4
    _ ≤ (2 : ENNReal) * ENNReal.ofReal (C_mu * r ^ κ) := h5
    _ = ENNReal.ofReal ((2 * C_mu) * r ^ κ) := h7

  have h2C_pos' : 0 < 2 * C_mu := by positivity
  exact ⟨a, μ', ha_pos, rfl, hμ'_supp, hμ'_supp_orig,
    ⟨hμ'_univ, hκ_pos, h2C_pos', hμ'_frost⟩⟩

end WeakTwoEndsSumProduct

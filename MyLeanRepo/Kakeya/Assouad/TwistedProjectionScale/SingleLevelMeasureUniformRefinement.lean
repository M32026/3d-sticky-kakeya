import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Single-level measure uniform refinement

Given a measurable set `Y` of finite positive measure and a finite disjoint
measurable cover `C` with at most `N` cells, produce a subfamily `S ⊆ C`
such that the occupied cells have pairwise comparable masses (within factor 2)
and at least a `1 / (2 * (Nat.log 2 (2*N) + 1))` fraction of the mass is retained.

Proof: discard light cells (below half the average positive mass), then
pigeonhole the heavy cells into dyadic mass classes with fixed base `R / (2*N)`.
-/

open MeasureTheory

namespace Kakeya.Assouad

lemma single_level_measure_uniform_refinement
    {α : Type} [MeasurableSpace α] (μ : Measure α)
    (Y : Set α) (hYmeas : MeasurableSet Y)
    (hYpos : μ Y ≠ 0) (hYfin : μ Y ≠ ⊤)
    (N : ℕ) (hNpos : 0 < N)
    (C : Finset (Set α))
    (hmeas : ∀ c ∈ C, MeasurableSet c)
    (hdisj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → Disjoint c₁ c₂)
    (hcov : Y ⊆ ⋃ c ∈ C, c)
    (hcard : C.card ≤ N) :
    ∃ (S : Finset (Set α)), S ⊆ C ∧
      let Y' := Y ∩ ⋃ c ∈ S, c
      MeasurableSet Y' ∧
      μ Y' ≠ 0 ∧
      μ Y ≤ (2 * (Nat.log 2 (2 * N) + 1) : ENNReal) * μ Y' ∧
      ∀ c₁ ∈ C, ∀ c₂ ∈ C,
        μ (Y' ∩ c₁) ≠ 0 → μ (Y' ∩ c₂) ≠ 0 →
        μ (Y' ∩ c₁) ≤ 2 * μ (Y' ∩ c₂) := by
  have hY_pos_real : 0 < (μ Y).toReal := ENNReal.toReal_pos hYpos hYfin
  set R : ℝ := (μ Y).toReal with hR

  have hfin : ∀ c ∈ C, μ (Y ∩ c) ≠ ⊤ := by
    intro c _
    have h : (Y ∩ c) ⊆ Y := by simp
    exact ne_top_of_le_ne_top hYfin (measure_mono h)

  have hYdisj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → Disjoint (Y ∩ c₁) (Y ∩ c₂) := by
    intro c₁ hc₁ c₂ hc₂ hne
    exact (hdisj c₁ hc₁ c₂ hc₂ hne).mono (by simp) (by simp)

  have hmeas_inter : ∀ c ∈ C, MeasurableSet (Y ∩ c) := by
    intro c hc
    exact hYmeas.inter (hmeas c hc)

  have h1_distrib : Y ∩ (⋃ c ∈ C, c) = ⋃ c ∈ C, (Y ∩ c) := by
    ext z
    aesop
  have h2_sub : Y = Y ∩ (⋃ c ∈ C, c) := by
    exact (Set.inter_eq_left.mpr hcov).symm
  have hYeq : Y = ⋃ c ∈ C, (Y ∩ c) := by
    exact h2_sub.trans h1_distrib

  have hsum_ennreal : μ Y = ∑ c ∈ C, μ (Y ∩ c) := by
    set U : Set α := ⋃ c ∈ C, (Y ∩ c) with hU
    have h1 : μ U = ∑ c ∈ C, μ (Y ∩ c) := by
      simpa [hU] using MeasureTheory.measure_biUnion_finset hYdisj hmeas_inter
    have h2 : μ Y = μ U := by rw [hYeq]
    exact h2.trans h1

  have hsum_real : R = ∑ c ∈ C, (μ (Y ∩ c)).toReal := by
    have h : (μ Y).toReal = (∑ c ∈ C, μ (Y ∩ c)).toReal := by rw [hsum_ennreal]
    have h2 : (∑ c ∈ C, μ (Y ∩ c)).toReal = ∑ c ∈ C, (μ (Y ∩ c)).toReal := by
      rw [ENNReal.toReal_sum hfin]
    exact hR.trans (h.trans h2)

  let r : Set α → ℝ := fun c => (μ (Y ∩ c)).toReal
  have hr_nonneg : ∀ c ∈ C, 0 ≤ r c := by
    intro c _
    positivity

  let pos : Finset (Set α) := C.filter (fun c => 0 < r c)
  have hpos_sub : pos ⊆ C := Finset.filter_subset _ _

  have hKpos : 0 < pos.card := by
    by_contra h
    have h' : pos = ∅ := by simpa using h
    have h_all_zero : ∀ c ∈ C, r c ≤ 0 := by
      intro c hc
      by_contra h2
      have h3 : 0 < r c := by linarith
      have h4 : c ∈ pos := by
        apply Finset.mem_filter.mpr
        exact ⟨hc, h3⟩
      rw [h'] at h4 <;> simp at h4
    have h5 : ∑ c ∈ C, r c ≤ 0 := by
      have h6 : ∑ c ∈ C, r c ≤ ∑ c ∈ C, (0 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _; exact h_all_zero i ‹_›
      simpa using h6
    have h_eq : ∑ c ∈ C, r c = R := hsum_real.symm
    rw [h_eq] at h5
    linarith [hY_pos_real]

  let K : ℕ := pos.card
  let avg : ℝ := R / (2 * K)
  let light : Finset (Set α) := pos.filter (fun c => r c < avg)
  let heavy : Finset (Set α) := pos \ light

  have hheavy_sub : heavy ⊆ C := by
    intro x hx
    exact hpos_sub ((Finset.mem_sdiff.mp hx).1)
  have hlight_sub : light ⊆ C := (Finset.filter_subset _ _).trans hpos_sub

  have hlight_sum : ∑ c ∈ light, r c < R / 2 := by
    by_cases hl : light = ∅
    · rw [hl]
      simp [hY_pos_real] <;> linarith
    · have hlight_ne : light.Nonempty := Finset.nonempty_iff_ne_empty.mpr hl
      have h1 : ∀ c ∈ light, r c < avg := fun c hc => (Finset.mem_filter.mp hc).2
      have h2 : ∑ c ∈ light, r c < ∑ c ∈ light, avg :=
        Finset.sum_lt_sum_of_nonempty hlight_ne h1
      have h3 : ∑ c ∈ light, avg = (light.card : ℝ) * avg := by
        rw [Finset.sum_const]
        <;> ring
      rw [h3] at h2
      have h4 : (light.card : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have h52 : 0 ≤ avg := by
        dsimp only [avg]
        have hR_nonneg : 0 ≤ R := hY_pos_real.le
        have h2K_pos : 0 < (2 * (K : ℝ)) := by exact_mod_cast (show 0 < 2 * K from by omega)
        exact div_nonneg hR_nonneg h2K_pos.le
      have h5 : (light.card : ℝ) * avg ≤ (K : ℝ) * avg :=
        mul_le_mul_of_nonneg_right h4 h52
      have h6 : (K : ℝ) * avg = R / 2 := by
        have hKpos' : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
        have h2 : (2 * (K : ℝ)) ≠ 0 := by
          have h2K_pos : 0 < (2 * (K : ℝ)) := by exact_mod_cast (show 0 < 2 * K from by omega)
          exact h2K_pos.ne'
        have h3 : (K : ℝ) * (R / (2 * (K : ℝ))) = R / 2 := by
          calc
            (K : ℝ) * (R / (2 * (K : ℝ)))
              = R * ((K : ℝ) / (2 * (K : ℝ))) := by ring
            _ = R * (1 / 2 : ℝ) := by
              have h4 : (K : ℝ) / (2 * (K : ℝ)) = (1 / 2 : ℝ) := by
                rw [div_eq_iff h2] <;> ring
              rw [h4]
            _ = R / 2 := by ring
        exact h3
      rw [h6] at h5
      linarith

  have hsum_pos : ∑ c ∈ pos, r c = R := by
    have h_disj : Disjoint pos (C \ pos) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 hx1
    have h_union : pos ∪ (C \ pos) = C := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      <;> tauto
    have h3 : ∑ c ∈ C, r c = ∑ c ∈ pos, r c + ∑ c ∈ (C \ pos), r c := by
      rw [← Finset.sum_union h_disj, h_union]
    have h4 : ∀ c ∈ (C \ pos), r c = 0 := by
      intro c hc
      have h5 : c ∈ C := (Finset.mem_sdiff.mp hc).1
      have h6 : c ∉ pos := (Finset.mem_sdiff.mp hc).2
      by_contra h7
      have h8 : 0 ≤ r c := hr_nonneg c h5
      have h9 : 0 < r c := lt_of_le_of_ne h8 (Ne.symm h7)
      have h10 : c ∈ pos := by
        rw [Finset.mem_filter]
        exact ⟨h5, h9⟩
      exact h6 h10
    have h10 : ∑ c ∈ (C \ pos), r c = 0 := by
      apply Finset.sum_eq_zero
      intro c hc; exact h4 c hc
    have h11 : ∑ c ∈ C, r c = R := hsum_real.symm
    linarith [h3, h10, h11]

  have hheavy_sum : ∑ c ∈ heavy, r c > R / 2 := by
    have h_disj_lh : Disjoint light heavy := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 hx1
    have h_union_lh : light ∪ heavy = pos := by
      have h_light_sub_pos : light ⊆ pos := Finset.filter_subset _ _
      have h : light ∪ (pos \ light) = pos := Finset.union_sdiff_of_subset h_light_sub_pos
      simpa [heavy] using h
    have h1 : ∑ c ∈ pos, r c = ∑ c ∈ light, r c + ∑ c ∈ heavy, r c := by
      rw [← Finset.sum_union h_disj_lh, h_union_lh]
    rw [hsum_pos] at h1
    linarith [hlight_sum]

  have hheavy_nonempty : heavy.Nonempty := by
    by_contra h
    have h' : heavy = ∅ := by simpa using h
    rw [h'] at hheavy_sum
    simp at hheavy_sum <;> linarith [hY_pos_real]

  -- Fixed base for dyadic classes
  let base : ℝ := R / (2 * N)
  let L : ℕ := Nat.log 2 (2 * N) + 1

  have hLpos : 0 < L := by
    dsimp only [L]
    have h1 : 0 ≤ Nat.log 2 (2 * N) := by positivity
    omega

  have h2N_lt_2L : (2 * N : ℕ) < 2 ^ L := by
    dsimp only [L]
    exact Nat.lt_pow_succ_log_self (by norm_num) (2 * N)

  have hbase_pos : 0 < base := by
    dsimp only [base]
    have hNpos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    positivity

  have hbase2L_gt_R : base * (2 : ℝ)^L > R := by
    dsimp only [base]
    have h1 : (2 : ℝ)^L > (2 * (N : ℝ)) := by exact_mod_cast h2N_lt_2L
    have h2 : 0 < R := hY_pos_real
    have h3 : 0 < (2 * (N : ℝ)) := by positivity
    calc
      R / (2 * (N : ℝ)) * (2 : ℝ)^L
        > R / (2 * (N : ℝ)) * (2 * (N : ℝ)) := by gcongr
      _ = R := by field_simp [h3.ne'] <;> ring

  have hK_le_N : K ≤ N := (Finset.card_le_card hpos_sub).trans hcard

  have hheavy_ge_base : ∀ c ∈ heavy, base ≤ r c := by
    intro c hc
    have h_c_in_pos : c ∈ pos := (Finset.mem_sdiff.mp hc).1
    have h_c_not_light : c ∉ light := (Finset.mem_sdiff.mp hc).2
    have h_r_ge_avg : avg ≤ r c := by
      by_contra h2
      have h3 : r c < avg := by linarith
      have h4 : c ∈ light := by
        apply Finset.mem_filter.mpr
        exact ⟨h_c_in_pos, h3⟩
      exact h_c_not_light h4
    have h_avg_ge_base : base ≤ avg := by
      dsimp only [base, avg]
      have hKpos' : (K : ℝ) > 0 := by exact_mod_cast hKpos
      have hNpos' : (N : ℝ) > 0 := by exact_mod_cast hNpos
      have h : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK_le_N
      have h4 : R / (2 * (K : ℝ)) ≥ R / (2 * (N : ℝ)) := by
        apply div_le_div_of_nonneg_left hY_pos_real.le
        · have h2K_pos : 0 < (2 * (K : ℝ)) := by exact_mod_cast (show 0 < 2 * K from by omega)
          exact h2K_pos
        · have h2K_le_2N : (2 * (K : ℝ)) ≤ (2 * (N : ℝ)) := by exact_mod_cast (show 2 * K ≤ 2 * N from by omega)
          exact h2K_le_2N
      exact h4
    linarith

  have hheavy_le_R : ∀ c ∈ heavy, r c ≤ R := by
    intro c hc
    have h_in_C : c ∈ C := hheavy_sub hc
    have h_sum_nonneg : ∀ i ∈ C, 0 ≤ r i := hr_nonneg
    have h : r c ≤ ∑ d ∈ C, r d := Finset.single_le_sum h_sum_nonneg h_in_C
    have h_eq : ∑ d ∈ C, r d = R := hsum_real.symm
    rw [h_eq] at h
    exact h

  have hheavy_lt_base2L : ∀ c ∈ heavy, r c < base * (2 : ℝ)^L := by
    intro c hc
    have h1 : r c ≤ R := hheavy_le_R c hc
    have h2 : R < base * (2 : ℝ)^L := hbase2L_gt_R
    linarith

  -- Dyadic classes
  let class_j : ℕ → Finset (Set α) := fun k =>
    heavy.filter (fun c => base * (2 : ℝ)^k ≤ r c ∧ r c < base * (2 : ℝ)^(k + 1))

  have h_class_cover : heavy = Finset.biUnion (Finset.range L) class_j := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro hc
      have h_ge : base ≤ r c := hheavy_ge_base c hc
      have h_lt : r c < base * (2 : ℝ)^L := hheavy_lt_base2L c hc
      let Q : ℕ → Prop := fun j => r c < base * (2 : ℝ)^(j + 1)
      have hQ : ∃ j, Q j := by
        refine ⟨L - 1, ?_⟩
        dsimp only [Q]
        have h11 : (L - 1) + 1 = L := by omega
        rw [h11]
        exact h_lt
      let k := Nat.find hQ
      have hPk : Q k := Nat.find_spec hQ
      have h_k_ge : base * (2 : ℝ)^k ≤ r c := by
        by_cases h_k : k = 0
        · rw [h_k]
          simpa using h_ge
        · have h_k1 : k - 1 < k := by omega
          have h_not : ¬ Q (k - 1) := Nat.find_min hQ h_k1
          have h10 : (k - 1) + 1 = k := by omega
          have h11 : ¬(r c < base * (2 : ℝ)^((k - 1) + 1)) := h_not
          have h12 : base * (2 : ℝ)^((k - 1) + 1) ≤ r c := by linarith
          rw [h10] at h12
          exact h12
      have h_kL : k < L := by
        have h12 : (L - 1) + 1 = L := by omega
        have h_goal : r c < base * (2 : ℝ)^((L - 1) + 1) := by
          rw [h12]
          exact h_lt
        have hQ_L1 : Q (L - 1) := h_goal
        by_contra h7
        have h8 : L ≤ k := by omega
        have h9 : L - 1 < k := by omega
        have h10 : ¬ Q (L - 1) := Nat.find_min hQ h9
        exact h10 hQ_L1
      have h_in_class : c ∈ class_j k := by
        dsimp only [class_j]
        apply Finset.mem_filter.mpr
        exact ⟨hc, ⟨h_k_ge, hPk⟩⟩
      exact ⟨k, h_kL, h_in_class⟩
    · rintro ⟨k, _, hck⟩
      dsimp only [class_j] at hck
      exact (Finset.mem_filter.mp hck).1

  have h_disj_classes : ∀ k₁ ∈ Finset.range L, ∀ k₂ ∈ Finset.range L, k₁ ≠ k₂ → Disjoint (class_j k₁) (class_j k₂) := by
    intro k₁ _ k₂ _ hne
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    have h1 : base * (2 : ℝ)^k₁ ≤ r c := (Finset.mem_filter.mp hc1).2.1
    have h2 : r c < base * (2 : ℝ)^(k₁ + 1) := (Finset.mem_filter.mp hc1).2.2
    have h3 : base * (2 : ℝ)^k₂ ≤ r c := (Finset.mem_filter.mp hc2).2.1
    have h4 : r c < base * (2 : ℝ)^(k₂ + 1) := (Finset.mem_filter.mp hc2).2.2
    by_cases h6 : k₁ < k₂
    · have h7 : k₁ + 1 ≤ k₂ := by omega
      have h8 : base * (2 : ℝ)^(k₁ + 1) ≤ base * (2 : ℝ)^k₂ := by
        have h9 : 0 < base := hbase_pos
        gcongr <;> norm_num
      linarith
    · have h7 : k₂ < k₁ := by omega
      have h8 : k₂ + 1 ≤ k₁ := by omega
      have h9 : base * (2 : ℝ)^(k₂ + 1) ≤ base * (2 : ℝ)^k₁ := by
        have h10 : 0 < base := hbase_pos
        gcongr <;> norm_num
      linarith

  have h_sum_classes : ∑ c ∈ heavy, r c = ∑ k ∈ Finset.range L, ∑ c ∈ class_j k, r c := by
    rw [h_class_cover]
    rw [Finset.sum_biUnion h_disj_classes] <;> rfl

  have h_pigeonhole : ∃ k ∈ Finset.range L, (∑ c ∈ class_j k, r c) ≥ (∑ c ∈ heavy, r c) / (L : ℝ) := by
    by_contra h
    push Not at h
    have h1 : ∑ k ∈ Finset.range L, (∑ c ∈ class_j k, r c) < ∑ k ∈ Finset.range L, ((∑ c ∈ heavy, r c) / (L : ℝ)) := by
      have hL_nonempty : (Finset.range L).Nonempty := Finset.nonempty_range_iff.mpr hLpos.ne'
      exact Finset.sum_lt_sum_of_nonempty hL_nonempty (fun k hk => h k hk)
    have h2 : ∑ k ∈ Finset.range L, ((∑ c ∈ heavy, r c) / (L : ℝ)) = (∑ c ∈ heavy, r c) := by
      have hLpos' : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
      have h_card : (Finset.range L).card = L := by simp
      have h_sum : ∑ k ∈ Finset.range L, ((∑ c ∈ heavy, r c) / (L : ℝ)) = (Finset.range L).card * ((∑ c ∈ heavy, r c) / (L : ℝ)) := by
        rw [Finset.sum_const]
        <;> simp
      rw [h_sum, h_card]
      have h_goal : (L : ℝ) * ((∑ c ∈ heavy, r c) / (L : ℝ)) = (∑ c ∈ heavy, r c) := by
        have h6 : (L : ℝ) * ((∑ c ∈ heavy, r c) / (L : ℝ)) = (L : ℝ) / (L : ℝ) * (∑ c ∈ heavy, r c) := by ring
        rw [h6]
        have h7 : (L : ℝ) / (L : ℝ) = 1 := by
          rw [div_self hLpos']
        rw [h7] <;> ring
      exact h_goal
    rw [h2] at h1
    rw [h_sum_classes] at h1
    <;> linarith

  rcases h_pigeonhole with ⟨k0, hk0_range, hS_sum⟩
  let S : Finset (Set α) := class_j k0

  have hS_sub_C : S ⊆ C := by
    dsimp only [S, class_j]
    exact (Finset.filter_subset _ _).trans hheavy_sub

  have hS_nonempty : S.Nonempty := by
    by_contra h
    have h' : S = ∅ := by simpa using h
    have hS_sum' : ∑ c ∈ S, r c ≥ (∑ c ∈ heavy, r c) / (L : ℝ) := by
      dsimp only [S]
      exact hS_sum
    rw [h'] at hS_sum'
    have h_zero : ∑ c ∈ (∅ : Finset (Set α)), r c = 0 := by simp
    rw [h_zero] at hS_sum'
    have h_pos : 0 < ∑ c ∈ heavy, r c := by linarith [hheavy_sum, hY_pos_real]
    have h_pos2 : 0 < (∑ c ∈ heavy, r c) / (L : ℝ) := by positivity
    linarith

  let Y' : Set α := Y ∩ ⋃ c ∈ S, c

  have hY'meas : MeasurableSet Y' := by
    apply hYmeas.inter
    apply MeasurableSet.biUnion (Finset.finite_toSet S).countable
    intro c hc
    exact hmeas c (hS_sub_C hc)

  have h_inter_eq : ∀ c ∈ S, Y' ∩ c = Y ∩ c := by
    intro c hc
    apply Set.Subset.antisymm
    · rintro x ⟨h1, h2⟩
      rcases h1 with ⟨hY, _⟩
      exact ⟨hY, h2⟩
    · rintro x ⟨hY, h2⟩
      have h3 : x ∈ (⋃ d ∈ S, d) := by
        simpa using ⟨c, hc, h2⟩
      exact ⟨⟨hY, h3⟩, h2⟩

  have hY'_ennreal : μ Y' = ∑ c ∈ S, μ (Y ∩ c) := by
    have h1 : Y' = ⋃ c ∈ S, (Y ∩ c) := by
      dsimp only [Y']
      ext z
      simp
      <;> tauto
    rw [h1]
    have h_disj : (S : Set (Set α)).PairwiseDisjoint (fun c => Y ∩ c) := by
      intro c₁ hc₁ c₂ hc₂ hne
      exact hYdisj c₁ (hS_sub_C hc₁) c₂ (hS_sub_C hc₂) hne
    have hmeas_S : ∀ c ∈ S, MeasurableSet (Y ∩ c) := by
      intro c hc
      exact hmeas_inter c (hS_sub_C hc)
    exact MeasureTheory.measure_biUnion_finset h_disj hmeas_S

  have hY'_real : (μ Y').toReal = ∑ c ∈ S, r c := by
    have h_eq1 : (μ Y').toReal = (∑ c ∈ S, μ (Y ∩ c)).toReal := by
      rw [hY'_ennreal]
    have h_eq2 : (∑ c ∈ S, μ (Y ∩ c)).toReal = ∑ c ∈ S, (μ (Y ∩ c)).toReal :=
      ENNReal.toReal_sum (fun c hc => hfin c (hS_sub_C hc))
    rw [h_eq1, h_eq2]
    <;> rfl

  have hY'pos : μ Y' ≠ 0 := by
    have h1 : 0 < (μ Y').toReal := by
      rw [hY'_real]
      have h2 : 0 < ∑ c ∈ heavy, r c := by linarith [hheavy_sum, hY_pos_real]
      have hLpos' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
      have h3 : 0 < (∑ c ∈ heavy, r c) / (L : ℝ) := by
        exact div_pos h2 hLpos'
      have h4 : (∑ c ∈ S, r c) ≥ (∑ c ∈ heavy, r c) / (L : ℝ) := hS_sum
      linarith
    have h5 : 0 < μ Y' := (ENNReal.toReal_pos_iff.mp h1).1
    exact h5.ne'

  have h_retention_real : R < (2 * (L : ℝ)) * (μ Y').toReal := by
    have h1 : (∑ c ∈ heavy, r c) > R / 2 := hheavy_sum
    have h2 : (μ Y').toReal = ∑ c ∈ S, r c := hY'_real
    rw [h2]
    have hLpos' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    calc R
      _ = 2 * (R / 2) := by ring
      _ < 2 * (∑ c ∈ heavy, r c) := by gcongr
      _ = 2 * (L : ℝ) * ((∑ c ∈ heavy, r c) / (L : ℝ)) := by
        have hLpos' : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
        field_simp [hLpos'] <;> ring
      _ ≤ 2 * (L : ℝ) * (∑ c ∈ S, r c) := by gcongr

  have h_retention_ennreal : μ Y ≤ (2 * L : ENNReal) * μ Y' := by
    have hY'_fin : μ Y' ≠ ⊤ := ne_top_of_le_ne_top hYfin (measure_mono (show Y' ⊆ Y from by simp [Y']))
    have h_top1 : μ Y ≠ ⊤ := hYfin
    have h_top2 : ((2 * L : ENNReal) * μ Y') ≠ ⊤ := by
      have h1 : (2 * L : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      exact ENNReal.mul_ne_top h1 hY'_fin
    have h1 : ((2 * L : ENNReal) * μ Y').toReal = (2 * (L : ℝ)) * (μ Y').toReal := by
      rw [ENNReal.toReal_mul]
      <;> norm_cast
    have h2 : (μ Y).toReal < ((2 * L : ENNReal) * μ Y').toReal := by
      rw [h1]
      exact h_retention_real
    have h3 : μ Y < (2 * L : ENNReal) * μ Y' := ENNReal.toReal_lt_toReal h_top1 h_top2 |>.mp h2
    exact h3.le

  have h_comparison : ∀ c₁ ∈ S, ∀ c₂ ∈ S,
      μ (Y' ∩ c₁) ≠ 0 → μ (Y' ∩ c₂) ≠ 0 →
      μ (Y' ∩ c₁) ≤ 2 * μ (Y' ∩ c₂) := by
    intro c₁ hc₁ c₂ hc₂ _ _
    have hc1_heavy : c₁ ∈ heavy := (Finset.mem_filter.mp hc₁).1
    have hc2_heavy : c₂ ∈ heavy := (Finset.mem_filter.mp hc₂).1
    have h1 : base * (2 : ℝ)^k0 ≤ r c₁ := (Finset.mem_filter.mp hc₁).2.1
    have h2 : r c₁ < base * (2 : ℝ)^(k0 + 1) := (Finset.mem_filter.mp hc₁).2.2
    have h3 : base * (2 : ℝ)^k0 ≤ r c₂ := (Finset.mem_filter.mp hc₂).2.1
    have h4 : r c₂ < base * (2 : ℝ)^(k0 + 1) := (Finset.mem_filter.mp hc₂).2.2
    have h5 : r c₁ < 2 * r c₂ := by
      have h6 : r c₁ < base * (2 : ℝ)^(k0 + 1) := h2
      have h7 : base * (2 : ℝ)^(k0 + 1) = 2 * (base * (2 : ℝ)^k0) := by
        ring
      rw [h7] at h6
      have h8 : 2 * (base * (2 : ℝ)^k0) ≤ 2 * r c₂ := by gcongr
      linarith
    have h91 : μ (Y' ∩ c₁) ≠ ⊤ := by
      rw [h_inter_eq c₁ hc₁]
      exact hfin c₁ (hS_sub_C hc₁)
    have h92 : (2 * μ (Y' ∩ c₂)) ≠ ⊤ := by
      have h921 : μ (Y' ∩ c₂) ≠ ⊤ := by
        rw [h_inter_eq c₂ hc₂]
        exact hfin c₂ (hS_sub_C hc₂)
      exact ENNReal.mul_ne_top (by norm_cast) h921
    have h93 : (2 * μ (Y' ∩ c₂)).toReal = 2 * (μ (Y' ∩ c₂)).toReal := by
      have h94 : (2 * μ (Y' ∩ c₂)).toReal = (2 : ENNReal).toReal * (μ (Y' ∩ c₂)).toReal := ENNReal.toReal_mul
      rw [h94] <;> norm_cast
    have h94 : (μ (Y' ∩ c₁)).toReal < (2 * μ (Y' ∩ c₂)).toReal := by
      rw [h93]
      have h10 : μ (Y' ∩ c₁) = μ (Y ∩ c₁) := by rw [h_inter_eq c₁ hc₁]
      have h11 : μ (Y' ∩ c₂) = μ (Y ∩ c₂) := by rw [h_inter_eq c₂ hc₂]
      rw [h10, h11]
      exact h5
    have h10 : μ (Y' ∩ c₁) < 2 * μ (Y' ∩ c₂) :=
      ENNReal.toReal_lt_toReal h91 h92 |>.mp h94
    exact h10.le

  have h_empty_outside : ∀ c ∈ C, c ∉ S → Y' ∩ c = ∅ := by
    intro c hc hns
    have h : Y' ∩ c ⊆ (∅ : Set α) := by
      rintro x ⟨hY', h2⟩
      have h3 : x ∈ (⋃ d ∈ S, d) := hY'.2
      have h4 : ∃ (d : Set α), d ∈ S ∧ x ∈ d := by
        simpa [Set.mem_biUnion] using h3
      rcases h4 with ⟨d, hd, hxd⟩
      have h5 : c ≠ d := by
        intro heq
        have hcs : c ∈ S := heq ▸ hd
        exact hns hcs
      have h6 : Disjoint c d := hdisj c hc d (hS_sub_C hd) h5
      exact (Set.disjoint_left.mp h6) h2 hxd
    exact Set.subset_empty_iff.mp h

  have h_comparison_all : ∀ c₁ ∈ C, ∀ c₂ ∈ C,
      μ (Y' ∩ c₁) ≠ 0 → μ (Y' ∩ c₂) ≠ 0 →
      μ (Y' ∩ c₁) ≤ 2 * μ (Y' ∩ c₂) := by
    intro c₁ hc₁ c₂ hc₂ hnz₁ hnz₂
    have h1 : c₁ ∈ S := by
      by_contra h
      have h_empty : Y' ∩ c₁ = ∅ := h_empty_outside c₁ hc₁ h
      rw [h_empty] at hnz₁
      simp at hnz₁
    have h2 : c₂ ∈ S := by
      by_contra h
      have h_empty : Y' ∩ c₂ = ∅ := h_empty_outside c₂ hc₂ h
      rw [h_empty] at hnz₂
      simp at hnz₂
    exact h_comparison c₁ h1 c₂ h2 hnz₁ hnz₂

  dsimp only
  have h_final : μ Y ≤ (2 * (Nat.log 2 (2 * N) + 1) : ENNReal) * μ Y' := by
    have hL_def : L = Nat.log 2 (2 * N) + 1 := by rfl
    have h_cast : (2 * L : ENNReal) = (2 * (Nat.log 2 (2 * N) + 1) : ENNReal) := by
      rw [hL_def] <;> norm_cast
    rw [h_cast] at h_retention_ennreal
    exact h_retention_ennreal
  exact ⟨S, hS_sub_C, hY'meas, hY'pos, h_final, h_comparison_all⟩

end Kakeya.Assouad

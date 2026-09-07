import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Tactic

/-!
# Upper Density Bound Implies Absolute Continuity

If a locally finite measure `μ` satisfies an upper density bound
`μ(closedBall x r) ≤ C · r^d` for all `x ∈ A` and sufficiently small `r`,
and `μH[d](A) = 0`, then `μ(A) = 0`.

This is the converse direction to `hausdorff_absolutely_continuous`
(lower density bound implies Hausdorff measure controlled by μ).

## Main results

- `measure_null_of_upper_density_uniform`: uniform upper density + H^d-null + bounded → μ-null
- `measure_null_of_upper_density`: pointwise upper density + H^d-null → μ-null
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {n d : ℕ}

/-- Helper: if `iInf f = 0` in `ENNReal`, then for any `ε > 0`, `∃ a, f a < ε`. -/
private lemma exists_lt_of_iInf_eq_zero {α : Type*} {f : α → ENNReal}
    (h : iInf f = 0) {ε : ENNReal} (hε : 0 < ε) :
    ∃ (a : α), f a < ε := by
  by_contra h2
  push Not at h2
  have h3 : ε ≤ iInf f := le_iInf h2
  rw [h] at h3
  exact False.elim (not_le.mpr hε h3)

/-- Helper: `iInf` over a false proposition is `⊤`. -/
private lemma iInf_false_eq_top {P : Prop} {f : P → ENNReal} (hnp : ¬P) :
    iInf f = ⊤ := by
  exact iInf_neg hnp

/-- Helper: `iInf` over a true proposition equals the value. -/
private lemma iInf_true {P : Prop} {f : P → ENNReal} (h : P) :
    iInf f = f h := by
  apply le_antisymm
  · exact iInf_le _ h
  · apply le_iInf
    intro h'
    rw [Subsingleton.elim h' h]

/-- If upper density bound holds at `x`, then `μ({x}) = 0`. -/
lemma upper_density_singleton_null
    {x : E n} {μ : Measure (E n)} [IsLocallyFiniteMeasure μ]
    (hd_pos : 0 < d) (C : ℝ) (hC_pos : 0 < C) (r0 : ℝ) (hr0_pos : 0 < r0)
    (h : ∀ (r : ℝ), 0 < r → r < r0 → μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ d)) :
    μ {x} = 0 := by
  have h_finite : μ {x} < ⊤ := measure_singleton_lt_top
  by_cases hpos : μ {x} = 0
  · exact hpos
  · have h_pos' : 0 < μ {x} := by
      simpa [pos_iff_ne_zero] using hpos
    let a : ℝ := (μ {x}).toReal
    have ha_pos : 0 < a := ENNReal.toReal_pos_iff.mpr ⟨h_pos', h_finite⟩
    have h_ofReal_a : ENNReal.ofReal a = μ {x} := by
      rw [ENNReal.ofReal_toReal h_finite.ne]
    have h_exists : ∃ (r : ℝ), 0 < r ∧ r < r0 ∧ C * r ^ d < a := by
      have h1 : Continuous (fun r : ℝ => C * r ^ d) := by fun_prop
      have h2 : (C * (0 : ℝ) ^ d) = 0 := by
        cases d with
        | zero => contradiction
        | succ _ => simp
      have h3 : ∃ δ > 0, ∀ (r : ℝ), |r| < δ → C * r ^ d < a := by
        have h_contAt : ContinuousAt (fun r : ℝ => C * r ^ d) 0 := h1.continuousAt
        have h4 := Metric.continuousAt_iff.mp h_contAt
        have h5 := h4 a ha_pos
        rcases h5 with ⟨δ, hδ_pos, h4⟩
        refine ⟨δ, hδ_pos, fun r hr => ?_⟩
        have hr' : dist r 0 < δ := by simpa [dist_eq_norm] using hr
        have h6 : dist (C * r ^ d) (C * (0 : ℝ) ^ d) < a := @h4 r hr'
        rw [h2] at h6
        have h7 : |C * r ^ d| < a := by simpa [dist_eq_norm] using h6
        have h8 : C * r ^ d ≤ |C * r ^ d| := le_abs_self (C * r ^ d)
        exact h8.trans_lt h7
      rcases h3 with ⟨δ, hδ_pos, h4⟩
      let r : ℝ := min δ (r0 / 2) / 2
      have hr_pos : 0 < r := by positivity
      have hr_lt_r0 : r < r0 := by
        have h5 : r ≤ r0 / 4 := by
          calc r = min δ (r0 / 2) / 2 := by rfl
            _ ≤ (r0 / 2) / 2 := by gcongr <;> exact min_le_right _ _
            _ = r0 / 4 := by ring
        linarith
      have h6 : |r| < δ := by
        have h7 : r ≤ δ / 2 := by
          calc r = min δ (r0 / 2) / 2 := by rfl
            _ ≤ δ / 2 := by gcongr <;> exact min_le_left _ _
        have h8 : |r| = r := abs_of_pos hr_pos
        rw [h8]
        linarith
      have h9 : C * r ^ d < a := h4 r h6
      exact ⟨r, hr_pos, hr_lt_r0, h9⟩
    rcases h_exists with ⟨r, hr_pos, hr_lt_r0, hlt⟩
    have h2 : {x} ⊆ closedBall x r := by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      simp [mem_closedBall, hr_pos.le]
    have h1 : μ {x} ≤ ENNReal.ofReal (C * r ^ d) :=
      measure_mono h2 |>.trans (h r hr_pos hr_lt_r0)
    have h3 : ENNReal.ofReal (C * r ^ d) < ENNReal.ofReal a :=
      (ofReal_lt_ofReal_iff ha_pos).mpr hlt
    rw [h_ofReal_a] at h3
    exact False.elim (not_le.mpr h3 h1)

/-- Extract a small cover from `μH[d] A = 0`. -/
private lemma hausdorff_null_extract_cover
    {A : Set (E n)} (hH_null : μH[(d : ℝ)] A = 0)
    {r : ENNReal} (hr_pos : 0 < r) {ε : ENNReal} (hε : 0 < ε) :
    ∃ (t : ℕ → Set (E n)), (A ⊆ ⋃ i, t i) ∧
      (∀ i, ediam (t i) ≤ r) ∧
      (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) < ε := by
  have h_formula := Measure.hausdorffMeasure_apply (d : ℝ) A
  rw [h_formula] at hH_null
  let F : ENNReal → ENNReal := fun r' =>
    ⨅ (t : ℕ → Set (E n)) (_ : A ⊆ ⋃ i, t i) (_ : ∀ i, ediam (t i) ≤ r'),
      ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)
  have h_iSup_zero : (⨆ (r' : ENNReal) (_ : 0 < r'), F r') = 0 := hH_null
  have hF_r_zero : F r = 0 := by
    have h : F r ≤ (⨆ (r' : ENNReal) (_ : 0 < r'), F r') := by
      apply le_iSup_of_le r
      apply le_iSup_of_le hr_pos
      exact le_refl _
    rw [h_iSup_zero] at h
    simpa using h
  have h_exists_t : ∃ (t : ℕ → Set (E n)),
      (⨅ (_ : A ⊆ ⋃ i, t i) (_ : ∀ i, ediam (t i) ≤ r),
        ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) < ε :=
    exists_lt_of_iInf_eq_zero hF_r_zero hε
  rcases h_exists_t with ⟨t, hlt⟩
  by_cases hcov : A ⊆ ⋃ i, t i
  · by_cases hediam : ∀ i, ediam (t i) ≤ r
    · have hsum : (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) < ε := by
        have h9 : (⨅ (h : A ⊆ ⋃ i, t i), ⨅ (h2 : ∀ i, ediam (t i) ≤ r),
            ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) =
            (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) := by
          rw [iInf_true hcov, iInf_true hediam]
        rw [h9] at hlt
        exact hlt
      exact ⟨t, hcov, hediam, hsum⟩
    · exfalso
      have h_top : (⨅ (h2 : ∀ i, ediam (t i) ≤ r),
          ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) = ⊤ :=
        iInf_false_eq_top hediam
      have h10 : (⨅ (h : A ⊆ ⋃ i, t i), ⨅ (h2 : ∀ i, ediam (t i) ≤ r),
          ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) = ⊤ := by
        rw [iInf_true hcov, h_top]
      rw [h10] at hlt
      simp at hlt
  · exfalso
    have h_top : (⨅ (h : A ⊆ ⋃ i, t i), ⨅ (h2 : ∀ i, ediam (t i) ≤ r),
        ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) = ⊤ :=
      iInf_false_eq_top hcov
    rw [h_top] at hlt
    simp at hlt

/-- **Uniform upper density implies absolute continuity** (bounded `A`). -/
lemma measure_null_of_upper_density_uniform
    {A : Set (E n)} {μ : Measure (E n)} [IsLocallyFiniteMeasure μ]
    (hA_bdd : Bornology.IsBounded A)
    (hd_pos : 0 < d)
    (C : ℝ) (hC_pos : 0 < C) (r0 : ℝ) (hr0_pos : 0 < r0)
    (h_density : ∀ x ∈ A, ∀ (r : ℝ), 0 < r → r < r0 →
      μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ d))
    (hH_null : μH[(d : ℝ)] A = 0) :
    μ A = 0 := by
  let r_ENNReal : ENNReal := ENNReal.ofReal (r0 / 2)
  have hr_pos : 0 < r_ENNReal := by positivity
  let C' : ENNReal := ENNReal.ofReal C
  have hC'_ne_zero : C' ≠ 0 := by
    simp [C', ENNReal.ofReal_eq_zero, hC_pos]
  have hC'_ne_top : C' ≠ ⊤ := ENNReal.ofReal_ne_top

  have h_main : ∀ (ε : ENNReal), 0 < ε → μ A ≤ C' * ε := by
    intro ε hε
    rcases hausdorff_null_extract_cover hH_null hr_pos hε with ⟨t, hcov, hediam, hsum⟩
    classical
    let P : ℕ → Prop := fun i => (t i ∩ A).Nonempty
    let g : ℕ → ENNReal := fun i => if P i then μ (t i) else 0
    let s : ℕ → Set (E n) := fun i => if P i then t i else ∅
    have hcov' : A ⊆ ⋃ (i : ℕ), s i := by
      intro x hx
      have h_in_union : x ∈ ⋃ (i : ℕ), t i := hcov hx
      rcases mem_iUnion.mp h_in_union with ⟨i, hi⟩
      have hPi : P i := ⟨x, hi, hx⟩
      have h_si : s i = t i := by simp [s, hPi]
      refine mem_iUnion.mpr ⟨i, ?_⟩
      rw [h_si] <;> exact hi
    have hμA : μ A ≤ ∑' i, g i := by
      calc μ A ≤ μ (⋃ (i : ℕ), s i) := measure_mono hcov'
           _ ≤ ∑' i, μ (s i) := measure_iUnion_le _
           _ = ∑' i, g i := by
             congr with i
             by_cases hPi : P i <;> simp [g, s, hPi]
    have h_each : ∀ i, g i ≤ C' * (⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) := by
      intro i
      by_cases hPi : P i
      · rcases hPi with ⟨x_i, hxi_t, hxi_A⟩
        have hPi' : P i := ⟨x_i, hxi_t, hxi_A⟩
        have h_nonempty : (t i).Nonempty := ⟨x_i, hxi_t⟩
        have h_gi : g i = μ (t i) := by
          simp [g, hPi']
        rw [h_gi]
        have h_ediam_lt : ediam (t i) < ⊤ := by
          have h1 : ediam (t i) ≤ r_ENNReal := hediam i
          have h2 : r_ENNReal ≠ ⊤ := ENNReal.ofReal_ne_top
          exact h1.trans_lt h2.lt_top
        have h_ediam_ne_top : ediam (t i) ≠ ⊤ := h_ediam_lt.ne
        let δ_i : ℝ := (ediam (t i)).toReal
        have h_ediam_eq : ediam (t i) = ENNReal.ofReal δ_i :=
          (ENNReal.ofReal_toReal h_ediam_ne_top).symm
        have h_diam_nonneg : 0 ≤ δ_i := by exact ENNReal.toReal_nonneg
        have h_diam_le : δ_i ≤ r0 / 2 := by
          have h1 : ediam (t i) ≤ r_ENNReal := hediam i
          rw [h_ediam_eq] at h1
          exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h1
        have h_diam_lt_r0 : δ_i < r0 := by linarith
        have h_t_sub : t i ⊆ closedBall x_i δ_i := by
          intro y hy
          have h1 : edist y x_i ≤ ediam (t i) := Metric.edist_le_ediam_of_mem hy hxi_t
          have h_edist_ne_top : edist y x_i ≠ ⊤ := ne_top_of_le_ne_top h_ediam_ne_top h1
          have h2 : (edist y x_i).toReal = dist y x_i := Eq.symm (dist_edist y x_i)
          have h3 : (edist y x_i).toReal ≤ δ_i :=
            (ENNReal.toReal_le_toReal h_edist_ne_top h_ediam_ne_top).mpr h1
          have h4 : dist y x_i ≤ δ_i := by rw [←h2] <;> exact h3
          simpa [mem_closedBall] using h4
        by_cases h_diam_pos : 0 < δ_i
        · have h4 : μ (t i) ≤ μ (closedBall x_i δ_i) := measure_mono h_t_sub
          have h5 : μ (closedBall x_i δ_i) ≤ ENNReal.ofReal (C * δ_i ^ d) :=
            h_density x_i hxi_A δ_i h_diam_pos h_diam_lt_r0
          have h6 : ENNReal.ofReal (C * δ_i ^ d) = C' * ediam (t i) ^ (d : ℝ) := by
            rw [h_ediam_eq]
            have h7 : ENNReal.ofReal (C * δ_i ^ d) = C' * ENNReal.ofReal (δ_i ^ d) := by
              rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
            rw [h7]
            have h8 : ENNReal.ofReal (δ_i ^ d) = (ENNReal.ofReal δ_i) ^ d :=
              ofReal_pow h_diam_nonneg d
            rw [h8]
            have h9 : (ENNReal.ofReal δ_i) ^ d = (ENNReal.ofReal δ_i) ^ (d : ℝ) := by norm_cast
            rw [h9] <;> rfl
          have h_iSup_eq : (⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) = ediam (t i) ^ (d : ℝ) := by
            letI : Nonempty (t i).Nonempty := ⟨h_nonempty⟩
            exact iSup_const
          have h5' : μ (closedBall x_i δ_i) ≤ C' * ediam (t i) ^ (d : ℝ) := by
            rw [←h6]
            exact h5
          calc μ (t i) ≤ μ (closedBall x_i δ_i) := h4
               _ ≤ C' * ediam (t i) ^ (d : ℝ) := h5'
               _ = C' * (⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) := by rw [h_iSup_eq]
        · have h_diam_zero : δ_i = 0 := by
            have h_not_pos : ¬(0 < δ_i) := h_diam_pos
            have h_le : δ_i ≤ 0 := not_lt.mp h_not_pos
            exact le_antisymm h_le h_diam_nonneg
          have h_singleton : t i ⊆ {x_i} := by
            intro y hy
            have h1 : edist y x_i ≤ ediam (t i) := Metric.edist_le_ediam_of_mem hy hxi_t
            have h7 : ediam (t i) = 0 := by
              rw [h_ediam_eq, h_diam_zero] <;> simp
            rw [h7] at h1
            have h3 : edist y x_i = 0 := by simpa using h1
            have h4 : y = x_i := by simpa [edist_eq_zero] using h3
            simp [h4]
          have hμ_x_i_zero : μ {x_i} = 0 :=
            upper_density_singleton_null hd_pos C hC_pos r0 hr0_pos
              (fun r hr_pos hr_lt => h_density x_i hxi_A r hr_pos hr_lt)
          have hμ_ti_zero : μ (t i) = 0 := by
            have h : μ (t i) ≤ μ {x_i} := measure_mono h_singleton
            rw [hμ_x_i_zero] at h
            exact nonpos_iff_eq_zero.mp h
          rw [hμ_ti_zero] <;> positivity
      · have h_gi : g i = 0 := by simp [g, hPi]
        rw [h_gi] <;> positivity
    have h_sum : ∑' i, g i ≤ C' * ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ) := by
      calc ∑' i, g i
        ≤ ∑' i, C' * (⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)) := ENNReal.tsum_le_tsum h_each
      _ = C' * ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ) := by
        rw [ENNReal.tsum_mul_left]
    have h_final : μ A ≤ C' * ε := hμA.trans (h_sum.trans (by gcongr))
    exact h_final

  have h_finite : μ A < ⊤ := Bornology.IsBounded.measure_lt_top hA_bdd
  have h_forall_delta : ∀ (δ : ENNReal), 0 < δ → μ A ≤ δ := by
    intro δ hδ
    let ε : ENNReal := δ * C'⁻¹
    have hC'_pos : 0 < C' := by
      simp [C', hC_pos] <;> positivity
    have h_inv_ne_zero : C'⁻¹ ≠ 0 := by
      intro h
      have h2 : C' = ⊤ := ENNReal.inv_eq_zero.mp h
      exact hC'_ne_top h2
    have h_inv_pos : 0 < C'⁻¹ := by
      simpa [pos_iff_ne_zero] using h_inv_ne_zero
    have hδ' : δ ≠ 0 := hδ.ne'
    have hε_pos : 0 < ε := by
      dsimp only [ε]
      exact ENNReal.mul_pos hδ' h_inv_ne_zero
    have h1 : μ A ≤ C' * ε := h_main ε hε_pos
    have h5 : C' * C'⁻¹ = 1 := ENNReal.mul_inv_cancel hC'_ne_zero hC'_ne_top
    have h2 : C' * ε = δ := by
      simp only [ε]
      calc C' * (δ * C'⁻¹)
        = C' * δ * C'⁻¹ := by rw [mul_assoc]
      _ = δ * C' * C'⁻¹ := by rw [mul_comm C' δ]
      _ = δ * (C' * C'⁻¹) := by rw [mul_assoc]
      _ = δ * 1 := by rw [h5]
      _ = δ := by rw [mul_one]
    rw [h2] at h1
    exact h1
  have h_eq_zero : μ A = 0 := by
    by_contra hpos
    have h_pos' : 0 < μ A := by
      simpa [pos_iff_ne_zero] using hpos
    have h4 := h_forall_delta (μ A / 2) (ENNReal.half_pos h_pos'.ne')
    have h5 : μ A / 2 < μ A := ENNReal.half_lt_self hpos h_finite.ne
    exact not_le.mpr h5 h4
  exact h_eq_zero

/-- **Pointwise upper density implies absolute continuity**. -/
lemma measure_null_of_upper_density
    {A : Set (E n)} {μ : Measure (E n)} [IsLocallyFiniteMeasure μ]
    (hd_pos : 0 < d)
    (h_density : ∀ x ∈ A, ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
      ∀ (r : ℝ), 0 < r → r < r0 → μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ d))
    (hH_null : μH[(d : ℝ)] A = 0) :
    μ A = 0 := by
  let A_kjl (k j l : ℕ) : Set (E n) :=
    {x ∈ A ∩ closedBall (0 : E n) l | ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ C ≤ (k : ℝ) + 1 ∧
      (1 : ℝ) / ((j : ℝ) + 1) ≤ r0 ∧
      ∀ (r : ℝ), 0 < r → r < r0 → μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ d)}
  have hcover : A ⊆ ⋃ (k : ℕ), ⋃ (j : ℕ), ⋃ (l : ℕ), A_kjl k j l := by
    intro x hx
    rcases h_density x hx with ⟨C_x, r0_x, hC_pos, hr0_pos, hbound⟩
    have h_k : ∃ (k : ℕ), C_x ≤ (k : ℝ) + 1 := by
      obtain ⟨k, hk⟩ := exists_nat_ge (C_x - 1)
      refine ⟨k, by linarith⟩
    have h_j : ∃ (j : ℕ), (1 : ℝ) / ((j : ℝ) + 1) ≤ r0_x := by
      by_cases h : r0_x ≥ 1
      · exact ⟨0, by norm_num <;> linarith⟩
      · have h' : r0_x < 1 := by linarith
        have h'' : 0 < r0_x := hr0_pos
        let j : ℕ := Nat.ceil (1 / r0_x - 1)
        have h_ge : (j : ℝ) ≥ 1 / r0_x - 1 := Nat.le_ceil _
        have h_main : (1 : ℝ) / ((j : ℝ) + 1) ≤ r0_x := by
          have h1 : (j : ℝ) + 1 ≥ 1 / r0_x := by linarith
          have h2 : 0 < r0_x := h''
          have h3 : 0 < (j : ℝ) + 1 := by positivity
          calc (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / (1 / r0_x) := by gcongr
            _ = r0_x := by field_simp [h2.ne'] <;> ring
        exact ⟨j, h_main⟩
    have h_l : ∃ (l : ℕ), dist x (0 : E n) ≤ (l : ℝ) := by
      obtain ⟨l, hl⟩ := exists_nat_ge (dist x 0)
      exact ⟨l, hl⟩
    rcases h_k with ⟨k, hk⟩
    rcases h_j with ⟨j, hj⟩
    rcases h_l with ⟨l, hl⟩
    have h_x_in : x ∈ A_kjl k j l := by
      simp only [A_kjl, Set.mem_setOf_eq]
      exact ⟨⟨hx, hl⟩, C_x, r0_x, hC_pos, hk, hj, hbound⟩
    simp only [Set.mem_iUnion]
    exact ⟨k, j, l, h_x_in⟩
  have h_null : ∀ (k j l : ℕ), μ (A_kjl k j l) = 0 := by
    intro k j l
    have hH_sub : μH[(d : ℝ)] (A_kjl k j l) = 0 := by
      have h1 : A_kjl k j l ⊆ A := by
        intro x hx
        exact hx.1.1
      exact measure_mono_null h1 hH_null
    have h_bdd : Bornology.IsBounded (A_kjl k j l) := by
      have h1 : A_kjl k j l ⊆ closedBall (0 : E n) l := by
        intro x hx
        exact hx.1.2
      exact Metric.isBounded_closedBall.subset h1
    let C_uniform : ℝ := (k : ℝ) + 1
    let r0_uniform : ℝ := (1 : ℝ) / ((j : ℝ) + 1)
    have hC_pos : 0 < C_uniform := by positivity
    have hr0_pos : 0 < r0_uniform := by positivity
    have h_uniform : ∀ x ∈ A_kjl k j l, ∀ (r : ℝ), 0 < r → r < r0_uniform →
        μ (closedBall x r) ≤ ENNReal.ofReal (C_uniform * r ^ d) := by
      intro x hx r hr_pos hr_lt
      rcases hx with ⟨_, C_x, r0_x, hCx_pos, hC_le, hr0_ge, hbound⟩
      have h_r_lt : r < r0_x := by
        have h1 : r < (1 : ℝ) / ((j : ℝ) + 1) := hr_lt
        linarith
      have h1 : μ (closedBall x r) ≤ ENNReal.ofReal (C_x * r ^ d) := hbound r hr_pos h_r_lt
      have h2 : C_x * r ^ d ≤ C_uniform * r ^ d := by gcongr <;> linarith
      have h3 : ENNReal.ofReal (C_x * r ^ d) ≤ ENNReal.ofReal (C_uniform * r ^ d) :=
        ENNReal.ofReal_le_ofReal h2
      exact h1.trans h3
    exact measure_null_of_upper_density_uniform h_bdd hd_pos C_uniform hC_pos
      r0_uniform hr0_pos h_uniform hH_sub
  let S : Set (E n) := ⋃ (k : ℕ), ⋃ (j : ℕ), ⋃ (l : ℕ), A_kjl k j l
  have hS_eq : S = ⋃ (p : ℕ × ℕ × ℕ), A_kjl p.1 p.2.1 p.2.2 := by
    ext x
    simp [S] <;> tauto
  have h3 : μ S ≤ ∑' p : ℕ × ℕ × ℕ, μ (A_kjl p.1 p.2.1 p.2.2) := by
    rw [hS_eq]
    exact measure_iUnion_le _
  have h4 : ∑' p : ℕ × ℕ × ℕ, μ (A_kjl p.1 p.2.1 p.2.2) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro p
    exact h_null p.1 p.2.1 p.2.2
  have hS_null : μ S = 0 := by
    have h5 : μ S ≤ 0 := h3.trans (by rw [h4] <;> simp)
    simpa using h5
  have h1 : μ A ≤ μ S := measure_mono hcover
  rw [hS_null] at h1
  simpa using h1

/-- Convert a ball-based upper density bound to a closedBall-based one,
at the cost of a factor `2^d` and shrinking the radius by 1/3. -/
lemma closedBall_bound_from_ball_bound
    {x : E n} {μ : Measure (E n)} [IsLocallyFiniteMeasure μ]
    (hd_pos : 0 < d) {C : ℝ} (hC_pos : 0 < C) {r0 : ℝ} (hr0_pos : 0 < r0)
    (h : ∀ (r : ℝ), 0 < r → r < r0 → μ (ball x r) ≤ ENNReal.ofReal (C * r ^ d)) :
    ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
      ∀ (r : ℝ), 0 < r → r < r0' → μ (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ d) := by
  let C' : ℝ := C * 2 ^ d
  let r0' : ℝ := r0 / 3
  have hC'_pos : 0 < C' := by positivity
  have hr0'_pos : 0 < r0' := by positivity
  refine ⟨C', r0', hC'_pos, hr0'_pos, fun r hr_pos hr_lt => ?_⟩
  have h1 : μ (closedBall x r) ≤ μ (ball x (2 * r)) := by
    apply measure_mono
    intro y hy
    have h2 : dist y x ≤ r := mem_closedBall.mp hy
    have h3 : dist y x < 2 * r := by linarith
    exact mem_ball.mpr h3
  have h4 : 0 < 2 * r := by positivity
  have h5 : 2 * r < r0 := by
    have h51 : r < r0 / 3 := by simpa [r0'] using hr_lt
    linarith
  have h6 : μ (ball x (2 * r)) ≤ ENNReal.ofReal (C * (2 * r) ^ d) := h (2 * r) h4 h5
  have h7 : C * (2 * r) ^ d = C' * r ^ d := by
    simp [C'] <;> ring
  rw [h7] at h6
  exact h1.trans h6

end Geometry

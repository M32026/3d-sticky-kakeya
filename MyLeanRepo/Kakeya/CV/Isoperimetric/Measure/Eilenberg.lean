import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Tactic

/-!
# Eilenberg Inequality

For a Lipschitz function `f : X → ℝ` and a set `A ⊆ X`,

  `∫⁻ t, μH[d](A ∩ f ⁻¹' {t}) ≤ Lip(f) * μH[d+1](A)`

Requires `d > 0`.

Proof: direct covering argument. For each scale r_n → 0, choose a cover
{E_i} of A with ∑ ediam(E_i)^(d+1) ≈ μH[d+1](A). For each t, the subfamily
of sets meeting f⁻¹{t} covers the level set, giving an upper bound on
μH[d](A ∩ f⁻¹{t}). Integrate over t using Fatou's lemma and the Lipschitz
bound volume(f '' E_i) ≤ L * ediam(E_i).
-/

open MeasureTheory Metric Set ENNReal Filter Classical
open scoped MeasureTheory

namespace Geometry
namespace EilenbergInequality

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Helper: for `d > 0`, the iSup over `s.Nonempty` of `ediam s ^ d`
equals `ediam s ^ d` (empty sets contribute 0). -/
lemma iSup_nonempty_ediam_rpow {s : Set X} {d : ℝ} (hd : 0 < d) :
    (⨆ _ : s.Nonempty, ediam s ^ d) = ediam s ^ d := by
  by_cases h : s.Nonempty
  · simpa [h] using rfl
  · have h_empty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h_empty]
    have h1 : ediam (∅ : Set X) = 0 := ediam_empty
    rw [h1]
    have h2 : (0 : ENNReal) ^ d = 0 := by
      simp [hd.ne'] <;> positivity
    simp [h2]

/-- For a Lipschitz `f : X → ℝ` and `E : Set X`, there exists a measurable
`I ⊇ f '' E` with `volume I ≤ L * ediam E`. -/
lemma exists_measurable_superset_image {f : X → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (E : Set X) :
    ∃ (I : Set ℝ), MeasurableSet I ∧ f '' E ⊆ I ∧
      volume I ≤ (L : ENNReal) * ediam E := by
  let S := f '' E
  by_cases hS : S = ∅
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · exact hS.subset
    · simp
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    by_cases hSb : Bornology.IsBounded S
    · let a := sInf S
      let b := sSup S
      let I := Icc a b
      refine ⟨I, isClosed_Icc.measurableSet, ?_, ?_⟩
      · intro y hy
        have hBddBelow : BddBelow S := hSb.bddBelow
        have hBddAbove : BddAbove S := hSb.bddAbove
        exact ⟨csInf_le hBddBelow hy, le_csSup hBddAbove hy⟩
      · have h_ediam : ediam S = ENNReal.ofReal (b - a) := Real.ediam_eq hSb
        have h_vol : volume I = ENNReal.ofReal (b - a) := by
          simp [I, Real.volume_Icc] <;> ring_nf
        rw [h_vol]
        have h_le1 : ediam S ≤ (L : ENNReal) * ediam E := hf.ediam_image_le E
        rw [h_ediam] at h_le1
        exact h_le1
    · refine ⟨Set.univ, MeasurableSet.univ, Set.subset_univ _, ?_⟩
      have h_ediam_top : ediam S = ⊤ := by
        exact Metric.ediam_of_unbounded hSb
      have h_le : ediam S ≤ (L : ENNReal) * ediam E := hf.ediam_image_le E
      rw [h_ediam_top] at h_le
      simpa using h_le

/-- **Eilenberg inequality** for Hausdorff measure.

For a Lipschitz map `f : X → ℝ`, a set `A ⊆ X`, and `d > 0`:
`∫⁻ t, μH[d](A ∩ f ⁻¹' {t}) ≤ Lip(f) * μH[d+1](A)`. -/
theorem eilenberg_inequality
    {f : X → ℝ} {A : Set X} {d : ℝ} (hd : 0 < d)
    {L : NNReal} (hf : LipschitzWith L f) :
    ∫⁻ (t : ℝ), μH[d] (A ∩ f ⁻¹' {t}) ≤ (L : ENNReal) * μH[d + 1] A := by
  -- Case L = 0: f is constant, level sets empty a.e.
  by_cases hL : L = 0
  · have h_f_const : ∀ (x y : X), f x = f y := by
      intro x y
      have h : edist (f x) (f y) ≤ (L : ENNReal) * edist x y := hf x y
      rw [hL] at h
      have h0 : edist (f x) (f y) ≤ 0 := by simpa using h
      have h1 : edist (f x) (f y) = 0 := le_zero_iff.mp h0
      exact edist_eq_zero.mp h1
    by_cases hA_empty : A = ∅
    · have h : ∀ t, A ∩ f ⁻¹' {t} = ∅ := by
        intro t; rw [hA_empty]; simp
      have h_main : ∫⁻ t, μH[d] (A ∩ f ⁻¹' {t}) = 0 := by
        have h2 : ∀ t, μH[d] (A ∩ f ⁻¹' {t}) = 0 := by
          intro t; rw [h t]; simp
        rw [lintegral_congr h2]; simp
      rw [h_main]; simp [hL]
    · have hA_ne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
      rcases hA_ne with ⟨x0, hx0⟩
      let c := f x0
      have hfc : ∀ x, f x = c := fun x => h_f_const x x0
      have h_g : ∀ (t : ℝ), t ≠ c → μH[d] (A ∩ f ⁻¹' {t}) = 0 := by
        intro t ht
        have h1 : f ⁻¹' {t} = ∅ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          intro hfx
          have h4 : f x = c := hfc x
          rw [h4] at hfx
          exact ht hfx.symm
        rw [h1]; simp
      have h_singleton : volume ({c} : Set ℝ) = 0 := by simp
      have h_ae : ∀ᵐ (t : ℝ), μH[d] (A ∩ f ⁻¹' {t}) = 0 := by
        filter_upwards [compl_mem_ae_iff.mpr h_singleton] with t ht
        exact h_g t ht
      have h_main : ∫⁻ (t : ℝ), μH[d] (A ∩ f ⁻¹' {t}) = 0 := by
        rw [lintegral_congr_ae h_ae]; simp
      rw [h_main]; simp [hL]
  · -- Case L > 0
    have hL_nnreal_pos : 0 < L := by
      exact lt_of_le_of_ne (by positivity) (Ne.symm hL)
    have hL_pos : (0 : ENNReal) < (L : ENNReal) := by exact_mod_cast hL_nnreal_pos
    by_cases h_top : μH[d + 1] A = ⊤
    · have h : (L : ENNReal) * μH[d + 1] A = ⊤ := by
        rw [h_top]
        exact ENNReal.mul_top hL_pos.ne'
      rw [h]; exact le_top
    · -- Main proof
      let M : ENNReal := μH[d + 1] A
      have hM_ne_top : M ≠ ⊤ := h_top

      let H_approx : ℝ≥0∞ → Set X → ENNReal := fun r s =>
        ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (d + 1)

      have hH_eq : μH[d + 1] A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), H_approx r A :=
        MeasureTheory.Measure.hausdorffMeasure_apply (d + 1) A

      have hd' : 0 < d + 1 := by linarith

      let r_n : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
      have hr_pos : ∀ n, 0 < r_n n := by
        intro n; simp [r_n] <;> positivity

      have h1_real : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h_cont : Continuous ENNReal.ofReal := ENNReal.continuous_ofReal
      have hr_tendsto : Tendsto r_n Filter.atTop (nhds (0 : ℝ≥0∞)) := by
        have h_cont_at : ContinuousAt ENNReal.ofReal (0 : ℝ) := h_cont.continuousAt
        have h_ofReal_tendsto : Tendsto ENNReal.ofReal (nhds (0 : ℝ)) (nhds (ENNReal.ofReal 0)) :=
          h_cont_at.tendsto
        have h : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) Filter.atTop (nhds (ENNReal.ofReal 0)) :=
          h_ofReal_tendsto.comp h1_real
        simpa [r_n] using h

      have hH_le : ∀ n, H_approx (r_n n) A ≤ M := by
        intro n
        have h1 : H_approx (r_n n) A ≤ ⨆ (r : ℝ≥0∞) (_ : 0 < r), H_approx r A :=
          le_iSup_of_le (r_n n) (le_iSup_of_le (hr_pos n) le_rfl)
        have h2 : (⨆ (r : ℝ≥0∞) (_ : 0 < r), H_approx r A) = M := hH_eq.symm
        rw [h2] at h1
        exact h1

      have hH_lt_top : ∀ n, H_approx (r_n n) A ≠ ⊤ := by
        intro n
        exact ne_top_of_le_ne_top hM_ne_top (hH_le n)

      have h_iSup_eq : ∀ (s : Set X),
          (⨆ _ : s.Nonempty, ediam s ^ (d + 1)) = ediam s ^ (d + 1) :=
        fun s => iSup_nonempty_ediam_rpow hd'

      -- Choose covers with sum ≤ H_approx + r_n
      have h_cover_exists : ∀ n : ℕ, ∃ (E : ℕ → Set X),
          (A ⊆ ⋃ i, E i) ∧ (∀ i, ediam (E i) ≤ r_n n) ∧
          (∑' i, ediam (E i) ^ (d + 1) ≤ H_approx (r_n n) A + r_n n) := by
        intro n
        let y := H_approx (r_n n) A + r_n n
        have hlt : H_approx (r_n n) A < y :=
          ENNReal.lt_add_right (hH_lt_top n) (hr_pos n).ne'
        have h_main : ∃ (t : ℕ → Set X), (A ⊆ ⋃ i, t i) ∧ (∀ i, ediam (t i) ≤ r_n n) ∧
            (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d + 1) < y) := by
          by_contra h
          push Not at h
          have hlb : y ≤ H_approx (r_n n) A := by
            exact le_iInf (fun t => le_iInf (fun hc => le_iInf (fun hd => h t hc hd)))
          exact False.elim (not_le.mpr hlt hlb)
        rcases h_main with ⟨E, hcover, hdiam, hsum⟩
        have h_sum_eq : ∑' i, ⨆ _ : (E i).Nonempty, ediam (E i) ^ (d + 1) =
            ∑' i, ediam (E i) ^ (d + 1) := by
          apply tsum_congr; intro i; exact h_iSup_eq (E i)
        refine ⟨E, hcover, hdiam, ?_⟩
        rw [←h_sum_eq]; exact le_of_lt hsum

      choose E hE_cover hE_diam hE_sum using h_cover_exists

      -- Choose measurable interval supersets
      have hI_exists : ∀ n i, ∃ (I : Set ℝ), MeasurableSet I ∧ f '' (E n i) ⊆ I ∧
          volume I ≤ (L : ENNReal) * ediam (E n i) := by
        intro n i
        exact exists_measurable_superset_image hf (E n i)

      choose I hI_meas hI_sub hI_vol using hI_exists

      let h : ℕ → (ℝ → ENNReal) := fun n t =>
        ∑' i : ℕ, ediam (E n i) ^ d * (if t ∈ I n i then (1 : ENNReal) else 0)

      have h_meas : ∀ n, Measurable (h n) := by
        intro n
        have h1 : ∀ i, Measurable (fun t : ℝ =>
            ediam (E n i) ^ d * (if t ∈ I n i then (1 : ENNReal) else 0)) := by
          intro i
          have h2 : Measurable (fun t : ℝ => (if t ∈ I n i then (1 : ENNReal) else 0)) :=
            measurable_const.indicator (hI_meas n i)
          exact h2.const_mul (ediam (E n i) ^ d)
        exact Measurable.tsum h1

      let cover_t : ℝ → ℕ → ℕ → Set X := fun t n i =>
        if t ∈ f '' (E n i) then E n i else (∅ : Set X)

      have h1 : ∀ t n, A ∩ f ⁻¹' {t} ⊆ ⋃ i, cover_t t n i := by
        intro t n x hx
        have hxA : x ∈ A := hx.1
        have hft : f x = t := hx.2
        rcases mem_iUnion.mp (hE_cover n hxA) with ⟨i, hi⟩
        have h_t_in : t ∈ f '' (E n i) := ⟨x, hi, hft⟩
        have h5 : cover_t t n i = E n i := by
          unfold cover_t; rw [if_pos h_t_in]
        have h6 : x ∈ cover_t t n i := by rw [h5]; exact hi
        exact mem_iUnion.mpr ⟨i, h6⟩

      have h2 : ∀ t n i, ediam (cover_t t n i) ≤ r_n n := by
        intro t n i
        by_cases h : t ∈ f '' (E n i)
        · have h5 : cover_t t n i = E n i := by
            unfold cover_t; rw [if_pos h]
          rw [h5]; exact hE_diam n i
        · have h5 : cover_t t n i = (∅ : Set X) := by
            unfold cover_t; rw [if_neg h]
          rw [h5, ediam_empty]
          exact le_of_lt (hr_pos n)

      have h3 : ∀ t n, ∑' i, ediam (cover_t t n i) ^ d ≤ h n t := by
        intro t n
        have h4 : ∀ i, ediam (cover_t t n i) ^ d ≤
            ediam (E n i) ^ d * (if t ∈ I n i then (1 : ENNReal) else 0) := by
          intro i
          by_cases h : t ∈ f '' (E n i)
          · have h_in_I : t ∈ I n i := hI_sub n i h
            have h_eq : ediam (cover_t t n i) ^ d = ediam (E n i) ^ d := by
              have h5 : cover_t t n i = E n i := by
                unfold cover_t; rw [if_pos h]
              rw [h5]
            rw [h_eq]
            have h_ind : (if t ∈ I n i then (1 : ENNReal) else 0) = 1 := by
              rw [if_pos h_in_I]
            rw [h_ind] <;> simp
          · have h_empty : cover_t t n i = (∅ : Set X) := by
              unfold cover_t; rw [if_neg h]
            rw [h_empty]
            have h_ediam_empty : ediam (∅ : Set X) ^ d = 0 := by
              rw [ediam_empty]
              have hz : (0 : ENNReal) ^ d = 0 := by
                exact ENNReal.zero_rpow_of_pos hd
              exact hz
            rw [h_ediam_empty]
            exact bot_le
        exact ENNReal.tsum_le_tsum h4

      have h_pointwise : ∀ (t : ℝ),
          μH[d] (A ∩ f ⁻¹' {t}) ≤ liminf (fun n => h n t) Filter.atTop := by
        intro t
        have h_main : μH[d] (A ∩ f ⁻¹' {t}) ≤
            liminf (fun n => ∑' i, ediam (cover_t t n i) ^ d) Filter.atTop :=
          MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum d (A ∩ f ⁻¹' {t})
            r_n hr_tendsto (cover_t t)
            (by filter_upwards with n; exact h2 t n)
            (by filter_upwards with n; exact h1 t n)
        have h_liminf_le : liminf (fun n => ∑' i, ediam (cover_t t n i) ^ d) Filter.atTop ≤
            liminf (fun n => h n t) Filter.atTop :=
          Filter.liminf_le_liminf (by filter_upwards with n; exact h3 t n)
        exact h_main.trans h_liminf_le

      -- Fatou's lemma
      have h_fatou : ∫⁻ (t : ℝ), liminf (fun n => h n t) Filter.atTop ≤
          liminf (fun n => ∫⁻ (t : ℝ), h n t) Filter.atTop :=
        lintegral_liminf_le h_meas

      have h_integral : ∀ n, ∫⁻ (t : ℝ), h n t =
          ∑' i : ℕ, ediam (E n i) ^ d * volume (I n i) := by
        intro n
        have h_meas_i : ∀ i, Measurable (fun t : ℝ =>
            ediam (E n i) ^ d * (if t ∈ I n i then (1 : ENNReal) else 0)) := by
          intro i
          have h2 : Measurable (fun t : ℝ => (if t ∈ I n i then (1 : ENNReal) else 0)) :=
            measurable_const.indicator (hI_meas n i)
          exact h2.const_mul (ediam (E n i) ^ d)
        rw [MeasureTheory.lintegral_tsum (fun i => (h_meas_i i).aemeasurable)]
        apply tsum_congr
        intro i
        let g : ℝ → ENNReal := fun t => if t ∈ I n i then (1 : ENNReal) else 0
        have hg : Measurable g := measurable_const.indicator (hI_meas n i)
        have h3 : ∫⁻ (t : ℝ), ediam (E n i) ^ d * g t =
            ediam (E n i) ^ d * volume (I n i) := by
          have h4 : ∫⁻ (t : ℝ), ediam (E n i) ^ d * g t =
              ediam (E n i) ^ d * ∫⁻ (t : ℝ), g t := by
            rw [lintegral_const_mul _ hg]
          rw [h4]
          have h5 : ∫⁻ (t : ℝ), g t = volume (I n i) := by
            have h6 : g = Set.indicator (I n i) (fun (_ : ℝ) => (1 : ENNReal)) := by
              funext t
              simp [g, Set.indicator_apply]
              <;> split_ifs <;> tauto
            rw [h6]
            rw [MeasureTheory.lintegral_indicator (hI_meas n i)]
            <;> simp
          rw [h5]
        exact h3

      have h_bound : ∀ n, ∫⁻ (t : ℝ), h n t ≤
          (L : ENNReal) * ∑' i : ℕ, ediam (E n i) ^ (d + 1) := by
        intro n
        rw [h_integral n]
        have h4 : ∑' i, ediam (E n i) ^ d * volume (I n i) ≤
            ∑' i, ediam (E n i) ^ d * ((L : ENNReal) * ediam (E n i)) := by
          exact ENNReal.tsum_le_tsum (fun i => mul_le_mul_left' (hI_vol n i) _)
        have h5 : ∑' i, ediam (E n i) ^ d * ((L : ENNReal) * ediam (E n i)) =
            (L : ENNReal) * ∑' i, ediam (E n i) ^ (d + 1) := by
          have h6 : ∀ i, ediam (E n i) ^ d * ((L : ENNReal) * ediam (E n i)) =
              (L : ENNReal) * ediam (E n i) ^ (d + 1) := by
            intro i
            set a := ediam (E n i) with ha
            have h7 : a ^ d * ((L : ENNReal) * a) = (L : ENNReal) * (a ^ d * a) := by
              rw [mul_left_comm (a ^ d) (L : ENNReal) a]
            rw [h7]
            have h8 : a ^ d * a = a ^ (d + 1) := by
              by_cases h0 : a = 0
              · rw [h0]
                have h1 : (0 : ENNReal) ^ d = 0 := by exact ENNReal.zero_rpow_of_pos hd
                have h2 : (0 : ENNReal) ^ (d + 1) = 0 := by exact ENNReal.zero_rpow_of_pos (by linarith)
                rw [h1, h2] <;> simp
              · by_cases htop : a = ⊤
                · rw [htop]
                  have h1 : (⊤ : ENNReal) ^ d = ⊤ := by exact ENNReal.top_rpow_of_pos hd
                  have h2 : (⊤ : ENNReal) ^ (d + 1) = ⊤ := by exact ENNReal.top_rpow_of_pos (by linarith)
                  rw [h1, h2] <;> simp
                · have h91 : a ^ d * a = a ^ d * a ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
                  rw [h91]
                  have h : a ^ (d + 1) = a ^ d * a ^ (1 : ℝ) := ENNReal.rpow_add d 1 h0 htop
                  exact h.symm
            rw [h8]
          have h10 : ∑' i, ediam (E n i) ^ d * ((L : ENNReal) * ediam (E n i)) =
              ∑' i, (L : ENNReal) * ediam (E n i) ^ (d + 1) := by
            apply tsum_congr; intro i; exact h6 i
          rw [h10]
          exact ENNReal.tsum_mul_left
        exact le_trans h4 (le_of_eq h5)

      have h_tendsto : Tendsto (fun n : ℕ => M + r_n n) Filter.atTop (nhds M) := by
        have h : Tendsto (fun n : ℕ => M + r_n n) Filter.atTop (nhds (M + 0)) :=
          tendsto_const_nhds.add hr_tendsto
        simpa using h

      have h_final : liminf (fun n : ℕ => H_approx (r_n n) A + r_n n) Filter.atTop ≤ M := by
        have h_le : ∀ n, H_approx (r_n n) A + r_n n ≤ M + r_n n := by
          intro n
          exact add_le_add_left (hH_le n) (r_n n)
        have h_liminf_eq : liminf (fun n : ℕ => M + r_n n) Filter.atTop = M :=
          h_tendsto.liminf_eq
        have h_liminf_le : liminf (fun n : ℕ => H_approx (r_n n) A + r_n n) Filter.atTop ≤
            liminf (fun n : ℕ => M + r_n n) Filter.atTop :=
          Filter.liminf_le_liminf (by filter_upwards with n; exact h_le n)
        rw [h_liminf_eq] at h_liminf_le
        exact h_liminf_le

      have hL_ne_top : (L : ENNReal) ≠ ⊤ := by
        exact ENNReal.coe_ne_top
      have h_cont_mul : Continuous (fun x : ENNReal => (L : ENNReal) * x) :=
        ENNReal.continuous_const_mul hL_ne_top
      have h_tendsto2 : Tendsto (fun n : ℕ => (L : ENNReal) * (M + r_n n)) Filter.atTop (nhds ((L : ENNReal) * M)) :=
        (h_cont_mul.tendsto (M : ENNReal)).comp h_tendsto
      have h_eq2 : liminf (fun n : ℕ => (L : ENNReal) * (M + r_n n)) Filter.atTop = (L : ENNReal) * M :=
        h_tendsto2.liminf_eq
      have h9 : ∀ n, (L : ENNReal) * ∑' i : ℕ, ediam (E n i) ^ (d + 1) ≤
          (L : ENNReal) * (H_approx (r_n n) A + r_n n) := by
        intro n
        exact mul_le_mul_left' (hE_sum n) _
      have h10 : ∀ n, (L : ENNReal) * (H_approx (r_n n) A + r_n n) ≤ (L : ENNReal) * (M + r_n n) := by
        intro n
        exact mul_le_mul_left' (add_le_add_left (hH_le n) (r_n n)) _
      have h11 : liminf (fun n : ℕ => (L : ENNReal) * (H_approx (r_n n) A + r_n n)) Filter.atTop ≤ (L : ENNReal) * M := by
        have h_liminf_le2 : liminf (fun n : ℕ => (L : ENNReal) * (H_approx (r_n n) A + r_n n)) Filter.atTop ≤
            liminf (fun n : ℕ => (L : ENNReal) * (M + r_n n)) Filter.atTop :=
          Filter.liminf_le_liminf (by filter_upwards with n; exact h10 n)
        rw [h_eq2] at h_liminf_le2
        exact h_liminf_le2

      calc
        ∫⁻ (t : ℝ), μH[d] (A ∩ f ⁻¹' {t})
          ≤ ∫⁻ (t : ℝ), liminf (fun n => h n t) Filter.atTop := lintegral_mono h_pointwise
        _ ≤ liminf (fun n => ∫⁻ (t : ℝ), h n t) Filter.atTop := h_fatou
        _ ≤ liminf (fun n => (L : ENNReal) * ∑' i : ℕ, ediam (E n i) ^ (d + 1)) Filter.atTop :=
          Filter.liminf_le_liminf (by filter_upwards with n; exact h_bound n)
        _ ≤ liminf (fun n : ℕ => (L : ENNReal) * (H_approx (r_n n) A + r_n n)) Filter.atTop :=
          Filter.liminf_le_liminf (by filter_upwards with n; exact h9 n)
        _ ≤ (L : ENNReal) * M := h11

end EilenbergInequality

section Euclidean

variable {n : ℕ} [Nonempty (Fin n)]

/-- Eilenberg inequality for Euclidean Hausdorff measure:
`∫⁻ s, μHE[n-1](A ∩ f⁻¹{s}) ≤ C * volume A` for some finite `C` independent of `A`. -/
lemma eilenberg_μHE (hn : 2 ≤ n)
    {f : E n → ℝ} {L : NNReal} (hf : LipschitzWith L f) (hL : L ≠ 0) :
    ∃ (C : ENNReal), C ≠ ⊤ ∧ C ≠ 0 ∧ ∀ (A : Set (E n)),
      ∫⁻ (s : ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s}) ≤ C * volume A := by
  let d : ℕ := n - 1
  have hd_pos : 0 < (d : ℝ) := by
    have h : 0 < n - 1 := by omega
    exact_mod_cast h
  have h_d1 : (d : ℝ) + 1 = (n : ℝ) := by
    have h : d + 1 = n := by omega
    exact_mod_cast h
  let c_d : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E d)) (μH[d] : Measure (E d))
  let c_n : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E n)) (μH[n] : Measure (E n))
  have hμHE_d : (μHE[d] : Measure (E n)) = (c_d : ENNReal) • μH[d] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := d)
  have hμHE_n : (μHE[n] : Measure (E n)) = (c_n : ENNReal) • μH[n] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := n)
  have hμHE_n_eq_vol : (μHE[n] : Measure (E n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  have hc_d_pos : (c_d : ENNReal) ≠ 0 := by
    simpa [c_d] using MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have hc_n_pos : (c_n : ENNReal) ≠ 0 := by
    simpa [c_n] using MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
  have hc_n_ne_top : (c_n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  let C_eil : ENNReal := (c_d : ENNReal) * (L : ENNReal) / (c_n : ENNReal)
  have hC_eil_ne_top : C_eil ≠ ⊤ := by
    apply ENNReal.mul_ne_top <;> simp [hc_n_pos] <;> exact ENNReal.coe_ne_top
  have h_main : ∀ (A : Set (E n)),
      ∫⁻ (s : ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s}) ≤ C_eil * volume A := by
    intro A
    have h1 : ∫⁻ (s : ℝ), μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) ≤ (L : ENNReal) * μH[(n : ℝ)] A := by
      have h_eil := EilenbergInequality.eilenberg_inequality (A := A) (hd := hd_pos) (hf := hf)
      rw [h_d1] at h_eil
      exact h_eil
    have h2 : ∫⁻ (s : ℝ), μHE[d] (A ∩ f ⁻¹' {s}) =
        (c_d : ENNReal) * ∫⁻ (s : ℝ), μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) := by
      have h3 : ∀ s, μHE[d] (A ∩ f ⁻¹' {s}) =
          (c_d : ENNReal) * μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) := by
        intro s; rw [hμHE_d]; simp [smul_apply] <;> rfl
      rw [lintegral_congr h3, lintegral_const_mul'] <;> simp
    have h4 : (c_n : ENNReal) * μH[n] A = volume A := by
      have h5 : (c_n : ENNReal) * μH[n] A = ((c_n : ENNReal) • μH[n]) A := by rfl
      have h6 : ((c_n : ENNReal) • μH[n]) A = (μHE[n] : Measure (E n)) A := by
        rw [hμHE_n.symm] <;> rfl
      have h7 : (μHE[n] : Measure (E n)) A = volume A := by
        rw [hμHE_n_eq_vol] <;> rfl
      rw [h5, h6, h7]
    have h_alg : (c_d : ENNReal) * ((L : ENNReal) * μH[n] A) = C_eil * volume A := by
      have h8 : μH[(n : ℝ)] A = μH[n] A := by rfl
      have h9 : C_eil * ((c_n : ENNReal) * μH[n] A) =
          (c_d : ENNReal) * (L : ENNReal) * μH[n] A := by
        have h10 : C_eil * (c_n : ENNReal) = (c_d : ENNReal) * (L : ENNReal) := by
          have h11 : C_eil * (c_n : ENNReal) = ((c_d : ENNReal) * (L : ENNReal) / (c_n : ENNReal)) * (c_n : ENNReal) := by rfl
          rw [h11]
          exact ENNReal.div_mul_cancel hc_n_pos hc_n_ne_top
        calc
          C_eil * ((c_n : ENNReal) * μH[n] A)
            = (C_eil * (c_n : ENNReal)) * μH[n] A := by ring
          _ = (c_d : ENNReal) * (L : ENNReal) * μH[n] A := by rw [h10]
      have h11 : C_eil * volume A = C_eil * ((c_n : ENNReal) * μH[n] A) := by rw [h4]
      rw [h11, h9] <;> ring
    rw [h2]
    have h6 : (c_d : ENNReal) * ∫⁻ (s : ℝ), μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) ≤
        (c_d : ENNReal) * ((L : ENNReal) * μH[(n : ℝ)] A) := by
      gcongr
    have h7 : μH[(n : ℝ)] A = μH[n] A := by rfl
    rw [h7] at h6
    rw [h_alg] at h6
    exact h6
  have hC_eil_pos : C_eil ≠ 0 := by
    have h_num : (c_d : ENNReal) * (L : ENNReal) ≠ 0 := by
      simp [mul_eq_zero, hc_d_pos, hL] <;> tauto
    have h : C_eil = 0 → False := by
      intro hz
      have h9 : C_eil * (c_n : ENNReal) = 0 := by rw [hz] <;> simp
      have h10 : C_eil * (c_n : ENNReal) = (c_d : ENNReal) * (L : ENNReal) := by
        have h11 : C_eil * (c_n : ENNReal) = ((c_d : ENNReal) * (L : ENNReal) / (c_n : ENNReal)) * (c_n : ENNReal) := by rfl
        rw [h11]
        exact ENNReal.div_mul_cancel hc_n_pos hc_n_ne_top
      rw [h10] at h9
      exact h_num h9
    exact h
  exact ⟨C_eil, hC_eil_ne_top, hC_eil_pos, h_main⟩

end Euclidean

end Geometry

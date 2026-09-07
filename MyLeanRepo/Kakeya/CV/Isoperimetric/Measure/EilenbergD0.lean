import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import Mathlib.Tactic

/-!
# Eilenberg Inequality — d = 0 Case (Banach Indicatrix Theorem)

For a Lipschitz map `f : X → ℝ` and `A : Set X`:

  `∫⁻ t, μH[0] (A ∩ f ⁻¹' {t}) ≤ Lip(f) * μH[1] A`

This is the boundary case of the Eilenberg inequality when the fiber
Hausdorff dimension is 0. Also known as the Banach indicatrix theorem.

## Proof

Covering argument: choose covers `{E_i}` of `A` with
`Σ diam(E_i) ≤ H¹(A) + ε`. For each `t`, any finite subset of
`A ∩ f⁻¹{t}` has at most one point in each `E_i` (once the cover
diameter is smaller than the minimum pairwise distance), so its
cardinality is bounded by the number of `E_i` whose image contains `t`.
Integrate this bound and use Fatou's lemma as the cover scale goes to 0.

## Dependencies

Uses `iSup_nonempty_ediam_rpow` and `exists_measurable_superset_image`
from `MyLeanRepo.Isoperimetric.Measure.Eilenberg`.
-/


open MeasureTheory Metric Set ENNReal Filter Classical
open scoped MeasureTheory

namespace Geometry
namespace EilenbergInequality

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Helper lemmas for Hausdorff 0-measure -/

/-- H^0 of a finite set equals its cardinality. -/
lemma hausdorff0_finset [DecidableEq X] (F : Finset X) :
    μH[0] (F : Set X) = (F.card : ENNReal) := by
  induction F using Finset.induction with
  | empty =>
    simp
  | @insert a F ha ih =>
    have h_ms_a : MeasurableSet ({a} : Set X) := isClosed_singleton.measurableSet
    have h_ms_F : MeasurableSet (F : Set X) := F.finite_toSet.measurableSet
    have h_disj : Disjoint ({a} : Set X) (F : Set X) := by
      simpa [Set.disjoint_left] using ha
    have h_coe : (↑(insert a F) : Set X) = ({a} : Set X) ∪ (F : Set X) := by
      simp [Finset.coe_insert]
    have h_union : μH[0] (↑(insert a F) : Set X) =
        μH[0] ({a} : Set X) + μH[0] (F : Set X) := by
      rw [h_coe]
      exact measure_union h_disj h_ms_F
    rw [h_union, Measure.hausdorffMeasure_zero_singleton a, ih]
    <;> simp [Finset.card_insert_of_notMem ha] <;> norm_cast <;> ring

/-- H^0(S) is bounded by the supremum of cardinalities of finite subsets of S. -/
lemma hausdorff0_le_iSup_finset [DecidableEq X] (S : Set X) :
    μH[0] S ≤ ⨆ (F : Finset X) (_ : (F : Set X) ⊆ S), (F.card : ENNReal) := by
  by_cases hS : S.Finite
  · let F := hS.toFinset
    have hF : (F : Set X) = S := hS.coe_toFinset
    have h1 : μH[0] S = (F.card : ENNReal) := by
      rw [←hF]
      exact hausdorff0_finset F
    rw [h1]
    exact le_iSup_of_le F (le_iSup_of_le (by simp [hF]) le_rfl)
  · have h_inf : S.Infinite := hS
    have h_forall : ∀ (n : ℕ), ∃ (F : Finset X), (F : Set X) ⊆ S ∧ F.card = n := by
      intro n
      induction n with
      | zero => exact ⟨∅, by simp, by simp⟩
      | succ n ih =>
        rcases ih with ⟨F, hF_sub, hF_card⟩
        have h_diff : (S \ (F : Set X)).Nonempty := by
          by_contra h
          have h_empty : S \ (F : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
          have h' : S ⊆ (F : Set X) := Set.diff_eq_empty.mp h_empty
          have h_fin : S.Finite := Set.Finite.subset (F.finite_toSet) h'
          exact hS h_fin
        rcases h_diff with ⟨x, hx⟩
        refine ⟨insert x F, ?_, ?_⟩
        · simp only [Finset.coe_insert]
          intro y hy
          rcases hy with (rfl | hy)
          · exact hx.1
          · exact hF_sub hy
        · rw [Finset.card_insert_of_notMem hx.2, hF_card] <;> simp
    set iSup : ENNReal := ⨆ (F : Finset X) (_ : (F : Set X) ⊆ S), (F.card : ENNReal) with hiSup
    have h_all_nat : ∀ (n : ℕ), (n : ENNReal) ≤ iSup := by
      intro n
      rcases h_forall n with ⟨F, hF_sub, hF_card⟩
      have h : (n : ENNReal) ≤ (F.card : ENNReal) := by rw [hF_card]
      exact le_trans h (le_iSup_of_le F (le_iSup_of_le hF_sub le_rfl))
    have h_top : iSup = ⊤ := by
      by_contra h_finite
      have h_lt : iSup < ⊤ := by
        simpa [lt_top_iff_ne_top] using h_finite
      let r : ℝ := iSup.toReal
      have hR : iSup = ENNReal.ofReal r := (ENNReal.ofReal_toReal h_finite).symm
      have h_arch : ∃ (n : ℕ), r < (n : ℝ) := exists_nat_gt r
      rcases h_arch with ⟨n, hn⟩
      have h6 : iSup < (n : ENNReal) := by
        rw [hR]
        have h_r_nonneg : 0 ≤ r := by positivity
        have h7 : ENNReal.ofReal r < ENNReal.ofReal (n : ℝ) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_r_nonneg).mpr hn
        have h8 : (ENNReal.ofReal (n : ℝ)) = (n : ENNReal) := by simp
        rw [h8] at h7
        exact h7
      have h9 : (n : ENNReal) ≤ iSup := h_all_nat n
      exact not_le.mpr h6 h9
    have h_goal : μH[0] S ≤ iSup := by
      rw [h_top] <;> exact le_top
    exact h_goal

/-! ### d=0 Eilenberg inequality (Banach indicatrix theorem) -/

/-- **d=0 Eilenberg inequality** (Banach indicatrix).

For a Lipschitz map `f : X → ℝ` and `A : Set X`:
`∫⁻ t, μH[0] (A ∩ f ⁻¹' {t}) ≤ Lip(f) * μH[1] A`.

Proof: cover A by E_i with Σ diam(E_i) ≤ H¹(A)+ε.
For each finite F ⊆ A ∩ f⁻¹{t}, small covers force each E_i to contain
at most one point of F, so |F| ≤ #{i : t ∈ f(E_i)}. Integrate and use
Fatou's lemma. -/
theorem eilenberg_inequality_d0 [DecidableEq X]
    {f : X → ℝ} {A : Set X} {L : NNReal} (hf : LipschitzWith L f) :
    ∫⁻ (t : ℝ), μH[0] (A ∩ f ⁻¹' {t}) ≤ (L : ENNReal) * μH[1] A := by
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
      have h_main : ∫⁻ t, μH[0] (A ∩ f ⁻¹' {t}) = 0 := by
        have h2 : ∀ t, μH[0] (A ∩ f ⁻¹' {t}) = 0 := by
          intro t; rw [h t]; simp
        rw [lintegral_congr h2]; simp
      rw [h_main]; simp [hL]
    · have hA_ne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
      rcases hA_ne with ⟨x0, hx0⟩
      let c := f x0
      have hfc : ∀ x, f x = c := fun x => h_f_const x x0
      have h_g : ∀ (t : ℝ), t ≠ c → μH[0] (A ∩ f ⁻¹' {t}) = 0 := by
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
      have h_ae : ∀ᵐ (t : ℝ), μH[0] (A ∩ f ⁻¹' {t}) = 0 := by
        filter_upwards [compl_mem_ae_iff.mpr h_singleton] with t ht
        exact h_g t ht
      have h_main : ∫⁻ (t : ℝ), μH[0] (A ∩ f ⁻¹' {t}) = 0 := by
        rw [lintegral_congr_ae h_ae]; simp
      rw [h_main]; simp [hL]
  · -- Case L > 0
    have hL_nnreal_pos : 0 < L := bot_lt_iff_ne_bot.mpr hL

    have hL_pos : (0 : ENNReal) < (L : ENNReal) := by exact_mod_cast hL_nnreal_pos
    by_cases h_top : μH[1] A = ⊤
    · have h : (L : ENNReal) * μH[1] A = ⊤ := by
        rw [h_top]
        exact ENNReal.mul_top hL_pos.ne'
      rw [h]; exact le_top
    · -- Main proof
      let M : ENNReal := μH[1] A
      have hM_ne_top : M ≠ ⊤ := h_top

      let H_approx : ℝ≥0∞ → Set X → ENNReal := fun r s =>
        ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (1 : ℝ)

      have hH_eq : μH[1] A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), H_approx r A :=
        MeasureTheory.Measure.hausdorffMeasure_apply (1 : ℝ) A

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
          (⨆ _ : s.Nonempty, ediam s ^ (1 : ℝ)) = ediam s ^ (1 : ℝ) :=
        fun s => iSup_nonempty_ediam_rpow (by norm_num)

      -- Choose covers with sum ≤ H_approx + r_n
      have h_cover_exists : ∀ n : ℕ, ∃ (E : ℕ → Set X),
          (A ⊆ ⋃ i, E i) ∧ (∀ i, ediam (E i) ≤ r_n n) ∧
          (∑' i, ediam (E i) ^ (1 : ℝ) ≤ H_approx (r_n n) A + r_n n) := by
        intro n
        let y := H_approx (r_n n) A + r_n n
        have hlt : H_approx (r_n n) A < y :=
          ENNReal.lt_add_right (hH_lt_top n) (hr_pos n).ne'
        have h_main : ∃ (t : ℕ → Set X), (A ⊆ ⋃ i, t i) ∧ (∀ i, ediam (t i) ≤ r_n n) ∧
            (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (1 : ℝ) < y) := by
          by_contra h
          push Not at h
          have hlb : y ≤ H_approx (r_n n) A := by
            exact le_iInf (fun t => le_iInf (fun hc => le_iInf (fun hd => h t hc hd)))
          exact False.elim (not_le.mpr hlt hlb)
        rcases h_main with ⟨E, hcover, hdiam, hsum⟩
        have h_sum_eq : ∑' i, ⨆ _ : (E i).Nonempty, ediam (E i) ^ (1 : ℝ) =
            ∑' i, ediam (E i) ^ (1 : ℝ) := by
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
        ∑' i : ℕ, ediam (E n i) ^ (0 : ℝ) * (if t ∈ I n i then (1 : ENNReal) else 0)

      have h_meas : ∀ n, Measurable (h n) := by
        intro n
        have h1 : ∀ i, Measurable (fun t : ℝ =>
            ediam (E n i) ^ (0 : ℝ) * (if t ∈ I n i then (1 : ENNReal) else 0)) := by
          intro i
          have h2 : Measurable (fun t : ℝ => (if t ∈ I n i then (1 : ENNReal) else 0)) :=
            measurable_const.indicator (hI_meas n i)
          exact h2.const_mul (ediam (E n i) ^ (0 : ℝ))
        exact Measurable.tsum h1

      -- Pointwise bound: H^0(A ∩ f⁻¹{t}) ≤ liminf h n t
      have h_pointwise : ∀ (t : ℝ),
          μH[0] (A ∩ f ⁻¹' {t}) ≤ liminf (fun n => h n t) Filter.atTop := by
        intro t
        let S := A ∩ f ⁻¹' {t}
        have hS1 : S ⊆ A := Set.inter_subset_left
        have hS2 : ∀ x ∈ S, f x = t := fun x hx => hx.2
        have h_le : μH[0] S ≤ ⨆ (F : Finset X) (_ : (F : Set X) ⊆ S), (F.card : ENNReal) :=
          hausdorff0_le_iSup_finset S
        apply le_trans h_le
        apply iSup₂_le
        intro F hF
        -- F is a finite subset of S
        -- For each pair of distinct points in F, eventually cover diameter < distance
        let P : Finset (X × X) := (F ×ˢ F).filter (fun p => p.1 ≠ p.2)
        have hP_pos : ∀ p ∈ P, 0 < edist p.1 p.2 := by
          intro p hp
          have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
          exact edist_pos.mpr hne
        have h_ev : ∀ p ∈ P, ∀ᶠ n in Filter.atTop, r_n n < edist p.1 p.2 := by
          intro p hp
          have hpos : 0 < edist p.1 p.2 := hP_pos p hp
          exact hr_tendsto.eventually (gt_mem_nhds hpos)
        have h_all : ∀ᶠ n in Filter.atTop, ∀ p ∈ P, r_n n < edist p.1 p.2 := by
          exact (Filter.eventually_all_finite (Finset.finite_toSet P)).mpr h_ev
        have h_main : ∀ᶠ n in Filter.atTop, (F.card : ENNReal) ≤ h n t := by
          filter_upwards [h_all] with n hn
          -- Each E n i contains at most one point of F
          have h_at_most_one : ∀ i, (E n i ∩ (F : Set X)).Subsingleton := by
            intro i x hx y hy
            by_contra hxy
            have h_xinE : x ∈ E n i := hx.1
            have h_yinE : y ∈ E n i := hy.1
            have h_xinF : x ∈ (F : Set X) := hx.2
            have h_yinF : y ∈ (F : Set X) := hy.2
            have h_pair : (x, y) ∈ P := by
              simp only [P, Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨h_xinF, h_yinF⟩, hxy⟩
            have h_lt : r_n n < edist x y := hn (x, y) h_pair
            have h_le1 : edist x y ≤ ediam (E n i) := Metric.edist_le_ediam_of_mem h_xinE h_yinE
            have h_le2 : ediam (E n i) ≤ r_n n := hE_diam n i
            have h_contra : r_n n < r_n n := lt_of_lt_of_le h_lt (le_trans h_le1 h_le2)
            exact lt_irrefl (r_n n) h_contra
          -- Choose an index i_x for each x ∈ F
          have hxA : ∀ x ∈ F, x ∈ A := fun x hx => (hF hx).1
          let idx : X → ℕ := fun x =>
            if h : x ∈ F then
              Classical.choose (mem_iUnion.mp (hE_cover n (hxA x h)))
            else 0
          have h_idx_mem : ∀ x ∈ F, x ∈ E n (idx x) := by
            intro x hx
            have h_def : idx x = Classical.choose (mem_iUnion.mp (hE_cover n (hxA x hx))) := by
              simp [idx, hx]
            rw [h_def]
            exact Classical.choose_spec (mem_iUnion.mp (hE_cover n (hxA x hx)))
          have h_inj : Set.InjOn idx (F : Set X) := by
            intro x hx y hy h_eq
            have h1 : x ∈ E n (idx x) := h_idx_mem x hx
            have h2 : y ∈ E n (idx y) := h_idx_mem y hy
            have h2' : y ∈ E n (idx x) := by
              have h_eq' : idx y = idx x := h_eq.symm
              rw [h_eq'] at h2
              exact h2
            have h3 : x ∈ E n (idx x) ∩ (F : Set X) := ⟨h1, hx⟩
            have h4 : y ∈ E n (idx x) ∩ (F : Set X) := ⟨h2', hy⟩
            exact h_at_most_one (idx x) h3 h4
          let I_F : Finset ℕ := F.image idx
          have hIF_card : I_F.card = F.card := by
            rw [Finset.card_image_of_injOn h_inj]
          have h_t_in_I : ∀ i ∈ I_F, t ∈ I n i := by
            intro i hi
            rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
            have h5 : x ∈ E n (idx x) := h_idx_mem x hx
            have h6 : f x = t := hS2 x (hF hx)
            have h7 : t ∈ f '' (E n (idx x)) := ⟨x, h5, h6⟩
            exact hI_sub n (idx x) h7
          -- h n t ≥ sum over I_F
          have h_rpow0 : ∀ (s : Set X), ediam s ^ (0 : ℝ) = 1 := by
            intro s; exact ENNReal.rpow_zero
          calc
            (F.card : ENNReal)
              = (I_F.card : ENNReal) := by rw [hIF_card]
            _ = ∑ i ∈ I_F, (1 : ENNReal) := by simp
            _ = ∑ i ∈ I_F, ediam (E n i) ^ (0 : ℝ) * (if t ∈ I n i then (1 : ENNReal) else 0) := by
                apply Finset.sum_congr rfl
                intro i hi
                have h9 : t ∈ I n i := h_t_in_I i hi
                simp [h_rpow0, h9]
            _ ≤ ∑' i : ℕ, ediam (E n i) ^ (0 : ℝ) * (if t ∈ I n i then (1 : ENNReal) else 0) :=
                ENNReal.sum_le_tsum I_F
            _ = h n t := by rfl
        have h_const : liminf (fun (_ : ℕ) => (F.card : ENNReal)) Filter.atTop = (F.card : ENNReal) :=
          liminf_const (F.card : ENNReal)
        rw [←h_const]
        exact Filter.liminf_le_liminf h_main

      -- Fatou's lemma
      have h_fatou : ∫⁻ (t : ℝ), liminf (fun n => h n t) Filter.atTop ≤
          liminf (fun n => ∫⁻ (t : ℝ), h n t) Filter.atTop :=
        lintegral_liminf_le h_meas

      have h_integral : ∀ n, ∫⁻ (t : ℝ), h n t =
          ∑' i : ℕ, ediam (E n i) ^ (0 : ℝ) * volume (I n i) := by
        intro n
        have h_meas_i : ∀ i, Measurable (fun t : ℝ =>
            ediam (E n i) ^ (0 : ℝ) * (if t ∈ I n i then (1 : ENNReal) else 0)) := by
          intro i
          have h2 : Measurable (fun t : ℝ => (if t ∈ I n i then (1 : ENNReal) else 0)) :=
            measurable_const.indicator (hI_meas n i)
          exact h2.const_mul (ediam (E n i) ^ (0 : ℝ))
        rw [MeasureTheory.lintegral_tsum (fun i => (h_meas_i i).aemeasurable)]
        apply tsum_congr
        intro i
        let g : ℝ → ENNReal := fun t => if t ∈ I n i then (1 : ENNReal) else 0
        have hg : Measurable g := measurable_const.indicator (hI_meas n i)
        have h3 : ∫⁻ (t : ℝ), ediam (E n i) ^ (0 : ℝ) * g t =
            ediam (E n i) ^ (0 : ℝ) * volume (I n i) := by
          have h4 : ∫⁻ (t : ℝ), ediam (E n i) ^ (0 : ℝ) * g t =
              ediam (E n i) ^ (0 : ℝ) * ∫⁻ (t : ℝ), g t := by
            rw [lintegral_const_mul _ hg]
          rw [h4]
          have h5 : ∫⁻ (t : ℝ), g t = volume (I n i) := by
            have h6 : g = Set.indicator (I n i) (fun (_ : ℝ) => (1 : ENNReal)) := by
              funext t
              simp [g, Set.indicator_apply] <;> split_ifs <;> tauto
            rw [h6]
            rw [MeasureTheory.lintegral_indicator (hI_meas n i)]
            <;> simp
          rw [h5]
        exact h3

      have h_bound : ∀ n, ∫⁻ (t : ℝ), h n t ≤
          (L : ENNReal) * ∑' i : ℕ, ediam (E n i) ^ (1 : ℝ) := by
        intro n
        rw [h_integral n]
        have h4 : ∑' i, ediam (E n i) ^ (0 : ℝ) * volume (I n i) ≤
            ∑' i, ediam (E n i) ^ (0 : ℝ) * ((L : ENNReal) * ediam (E n i)) := by
          exact ENNReal.tsum_le_tsum (fun i => mul_le_mul_left' (hI_vol n i) _)
        have h5 : ∑' i, ediam (E n i) ^ (0 : ℝ) * ((L : ENNReal) * ediam (E n i)) =
            (L : ENNReal) * ∑' i, ediam (E n i) ^ (1 : ℝ) := by
          have h6 : ∀ i, ediam (E n i) ^ (0 : ℝ) * ((L : ENNReal) * ediam (E n i)) =
              (L : ENNReal) * ediam (E n i) ^ (1 : ℝ) := by
            intro i
            simp [ENNReal.rpow_zero, ENNReal.rpow_one] <;> ring
          have h10 : ∑' i, ediam (E n i) ^ (0 : ℝ) * ((L : ENNReal) * ediam (E n i)) =
              ∑' i, (L : ENNReal) * ediam (E n i) ^ (1 : ℝ) := by
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
      have h9 : ∀ n, (L : ENNReal) * ∑' i : ℕ, ediam (E n i) ^ (1 : ℝ) ≤
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
        ∫⁻ (t : ℝ), μH[0] (A ∩ f ⁻¹' {t})
          ≤ ∫⁻ (t : ℝ), liminf (fun n => h n t) Filter.atTop := lintegral_mono h_pointwise
        _ ≤ liminf (fun n => ∫⁻ (t : ℝ), h n t) Filter.atTop := h_fatou
        _ ≤ liminf (fun n => (L : ENNReal) * ∑' i : ℕ, ediam (E n i) ^ (1 : ℝ)) Filter.atTop :=
          Filter.liminf_le_liminf (by filter_upwards with n; exact h_bound n)
        _ ≤ liminf (fun n : ℕ => (L : ENNReal) * (H_approx (r_n n) A + r_n n)) Filter.atTop :=
          Filter.liminf_le_liminf (by filter_upwards with n; exact h9 n)
        _ ≤ (L : ENNReal) * M := h11

end EilenbergInequality
end Geometry

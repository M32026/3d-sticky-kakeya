import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaRegularSet
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaCriticalSet
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaDirBounded
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaLocalPatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaPermutedDirection
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-!
# Final Coarea Assembly

Combines regular set equality and critical set bound to prove
the global coarea inequality for smooth functions.

## Key lemmas (to be proved)

1. `regular_set_coarea_equality`: exact coarea on {‖∇u‖ ≥ δ}
2. `critical_set_bound_scaling`: critical set bound with uniform constant C
-/

-- ============================================================================
-- Hard sub-lemmas (to be proved)
-- ============================================================================

/-- **Critical set bound with uniform constant.**

For a C¹ function u with compact support, there exists a finite constant C
such that for any δ > 0 and any bounded measurable A ⊆ {‖∇u‖ < δ},
`∫ μHE(A ∩ {u=s}) ≤ C * δ * volume A`. -/
lemma critical_set_bound_scaling
    (u : E n → ℝ) (hu : ContDiff ℝ 1 u)
    (h_support : HasCompactSupport u) (hn : 2 ≤ n) :
    ∃ (C : ENNReal), C ≠ ⊤ ∧
      ∀ (δ : ℝ), 0 < δ → ∀ (A : Set (E n)),
        MeasurableSet A → Bornology.IsBounded A →
        A ⊆ {x | ‖fderiv ℝ u x‖ < δ} →
        ∫⁻ (s : ℝ), μHE[n - 1] (A ∩ {x | u x = s}) ≤
          C * ENNReal.ofReal δ * volume A := by
  refine ⟨criticalSetConstant n, criticalSetConstant_ne_top n (by linarith), ?_⟩
  intro δ hδ A hA hA_bdd hA_sub
  exact critical_set_bound_explicit u hu δ hδ hn A hA hA_bdd hA_sub

-- ============================================================================
-- Hausdorff form
-- ============================================================================

/-- **Global coarea inequality — Hausdorff form.** -/
theorem coarea_hausdorff_smooth_upper
    (u : E n → ℝ) (hu : ContDiff ℝ 1 u)
    (h_support : HasCompactSupport u)
    (h0 : ∀ x, 0 ≤ u x) (h1 : ∀ x, u x ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hn : 2 ≤ n) :
    ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        μHE[n - 1] {x | u x = s}
      ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u x‖ := by
  · have hn' : 2 ≤ n := hn
    let G : ENNReal := ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u x‖
    let K : Set (E n) := tsupport u
    have hK_compact : IsCompact K := by exact HasCompactSupport.isCompact h_support
    have hK_meas : MeasurableSet K := hK_compact.measurableSet
    have hK_vol : volume K ≠ ⊤ := hK_compact.measure_lt_top.ne
    have hK_bdd : Bornology.IsBounded K := hK_compact.isBounded

    -- Helper: outside topological support, fderiv is zero
    have h_outside : ∀ x ∉ K, fderiv ℝ u x = 0 := by
      intro x hx
      have h3 : IsClosed K := hK_compact.isClosed
      have h4 : IsOpen Kᶜ := h3.isOpen_compl
      have h5 : x ∈ Kᶜ := by simpa using hx
      have h6 : Kᶜ ∈ nhds x := h4.mem_nhds h5
      have h7 : u =ᶠ[nhds x] 0 := by
        filter_upwards [h6] with y hy
        have h9 : y ∉ tsupport u := hy
        have h10 : u y = 0 := by
          exact image_eq_zero_of_notMem_tsupport hy
        exact h10
      have h8 : fderiv ℝ u x = fderiv ℝ (fun _ : E n => (0 : ℝ)) x := h7.fderiv_eq
      simpa using h8

    have hIoc_meas : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc

    by_cases hG0 : G = 0
    · -- G = 0 case: gradient zero a.e., hence u = 0 everywhere
      have h_ae_norm : ∀ᵐ x ∂volume, ‖fderiv ℝ u x‖ = 0 := by
        have h : (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u x‖) = 0 := hG0
        have h' : ∀ᵐ x ∂volume, ENNReal.ofReal ‖fderiv ℝ u x‖ = 0 :=
          (lintegral_eq_zero_iff (by fun_prop)).mp h
        filter_upwards [h'] with x hx
        have h9 : ENNReal.ofReal ‖fderiv ℝ u x‖ = 0 := hx
        have h10 : ‖fderiv ℝ u x‖ ≤ 0 := (ENNReal.ofReal_eq_zero).mp h9
        have h11 : 0 ≤ ‖fderiv ℝ u x‖ := by positivity
        have h12 : ‖fderiv ℝ u x‖ = 0 := by linarith
        exact h12
      have h_cont : Continuous (fun x => ‖fderiv ℝ u x‖) :=
        (hu.continuous_fderiv (by norm_num)).norm
      have h_grad_zero_all : ∀ x, ‖fderiv ℝ u x‖ = 0 := by
        intro x
        by_contra h
        have h_pos : 0 < ‖fderiv ℝ u x‖ := by
          have h' : ‖fderiv ℝ u x‖ ≠ 0 := h
          exact lt_of_le_of_ne (by positivity) h'.symm
        let S := {y : E n | 0 < ‖fderiv ℝ u y‖}
        have hS_open : IsOpen S := h_cont.isOpen_preimage (Set.Ioi 0) isOpen_Ioi
        have hxS : x ∈ S := h_pos
        have hS_nonempty : S.Nonempty := ⟨x, hxS⟩
        have hS_pos : 0 < volume S := hS_open.measure_pos volume hS_nonempty
        have hS_null : volume S = 0 := by
          have h1 : S ⊆ {y | ‖fderiv ℝ u y‖ ≠ 0} := by
            intro y hy; simpa [S] using hy
          have h2 : volume {y | ‖fderiv ℝ u y‖ ≠ 0} = 0 := h_ae_norm
          exact measure_mono_null h1 h2
        exact hS_pos.ne' hS_null
      have h_fderiv_zero : ∀ x, fderiv ℝ u x = 0 := by
        intro x
        have h11 : ‖fderiv ℝ u x‖ = 0 := h_grad_zero_all x
        simpa [norm_eq_zero] using h11
      -- u is constant since fderiv = 0 everywhere
      have h_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
      have h_const : ∀ (y z : E n), u y = u z := by
        intro y z
        have h_diff_at : ∀ (x : E n), DifferentiableAt ℝ u x := by
          intro x
          exact (hu.differentiable (by norm_num)).differentiableAt
        have h_bound : ∀ (x : E n), x ∈ (Set.univ : Set (E n)) → ‖fderiv ℝ u x‖ ≤ (0 : ℝ) := by
          intro x _
          have h14 : fderiv ℝ u x = 0 := h_fderiv_zero x
          rw [h14] <;> norm_num
        have h_mvt : ‖u z - u y‖ ≤ (0 : ℝ) * ‖z - y‖ :=
          Convex.norm_image_sub_le_of_norm_fderiv_le
            (fun x _ => h_diff_at x)
            h_bound
            convex_univ (by simp) (by simp)
        have h2 : ‖u z - u y‖ = 0 := by
          have h3 : ‖u z - u y‖ ≤ 0 := by simpa using h_mvt
          have h4 : 0 ≤ ‖u z - u y‖ := by positivity
          linarith
        have h3 : u z - u y = 0 := by simpa [norm_eq_zero] using h2
        have h4 : u z = u y := eq_of_sub_eq_zero h3
        exact h4.symm
      have h_u0 : u 0 = 0 := by
        by_cases h : u 0 = 0
        · exact h
        · -- u = nonzero constant, so tsupport = univ, contradicting compact support
          have hc : ∀ x, u x = u 0 := fun x => h_const x 0
          have h1 : Function.support u = Set.univ := by
            ext x
            simp only [Function.mem_support, Set.mem_univ, iff_true]
            have h2 : u x = u 0 := hc x
            rw [h2]
            exact h
          have h3 : tsupport u = Set.univ := by
            rw [tsupport, h1] <;> simp
          have h4 : K = Set.univ := by simpa [K] using h3
          rw [h4] at hK_compact
          have h5 : Bornology.IsBounded (Set.univ : Set (E n)) := hK_compact.isBounded
          have h6 : ∃ (r : ℝ), ∀ (x : E n), ‖x‖ ≤ r := by
            have h7 : ∃ (r : ℝ), (Set.univ : Set (E n)) ⊆ Metric.closedBall (0 : E n) r :=
              (Metric.isBounded_iff_subset_closedBall (0 : E n)).mp h5
            rcases h7 with ⟨r, hr⟩
            refine ⟨r, fun x => ?_⟩
            have h8 : x ∈ (Set.univ : Set (E n)) := by simp
            have h9 : x ∈ Metric.closedBall (0 : E n) r := hr h8
            simpa [Metric.mem_closedBall, dist_zero_right] using h9
          rcases h6 with ⟨r, hr⟩
          have hr_nonneg : 0 ≤ r := by
            have h7 : ‖(0 : E n)‖ ≤ r := hr 0
            simpa using h7
          let i : Fin n := ⟨0, by linarith⟩
          let v : E n := EuclideanSpace.single i 1
          have h8 : ‖v‖ = 1 := by simp [v]
          have h9 : ‖(r + 1) • v‖ ≤ r := hr ((r + 1) • v)
          have h10 : ‖(r + 1) • v‖ = (r + 1) := by
            have h11 : ‖(r + 1) • v‖ = |r + 1| * ‖v‖ := norm_smul (r + 1) v
            rw [h11, h8]
            have h12 : 0 ≤ r + 1 := by linarith
            rw [abs_of_nonneg h12] <;> ring
          rw [h10] at h9
          linarith
      have h_u_zero : ∀ x, u x = 0 := by
        intro x
        exact h_const x 0 ▸ h_u0
      have h9 : ∀ s ∈ Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s} = 0 := by
        intro s hs
        have h10 : 0 < s := hs.1
        have h11 : {x | u x = s} = ∅ := by
          ext x
          simp only [Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          intro h12
          have h13 : u x = s := h12
          have h14 : u x = 0 := h_u_zero x
          rw [h14] at h13
          linarith
        rw [h11] <;> simp
      have h10 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s} = 0 := by
        have h11 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s} ≤
            ∫⁻ s in Set.Ioc (0 : ℝ) 1, (0 : ENNReal) := by
          apply setLIntegral_mono' hIoc_meas
          intro s hs
          have h12 : μHE[n - 1] {x | u x = s} = 0 := h9 s hs
          rw [h12] <;> simp
        have h13 : 0 ≤ ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s} := by positivity
        have h14 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, (0 : ENNReal) = 0 := by simp
        rw [h14] at h11
        exact le_antisymm h11 h13
      rw [h10] <;> simp

    · -- G > 0 case
      have hG_pos : 0 < G := pos_iff_ne_zero.mpr hG0
      have hG_ne_top : G ≠ ⊤ := by
        have h_cont : Continuous (fun x => ‖fderiv ℝ u x‖) :=
          (hu.continuous_fderiv (by norm_num)).norm
        rcases hK_compact.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
        have hK_nonempty : K.Nonempty := by
          by_contra h
          have hK_empty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
          have h_grad_zero : ∀ x, fderiv ℝ u x = 0 := by
            intro x
            have h3 : x ∉ K := by rw [hK_empty]; simp
            exact h_outside x h3
          have hG_eq0 : G = 0 := by
            simp [G, h_grad_zero]
          exact hG0 hG_eq0
        obtain ⟨x0, hx0⟩ := hK_nonempty
        have hM_nonneg : 0 ≤ M := by
          have h : ‖fderiv ℝ u x0‖ ≤ M := hM ⟨x0, hx0, rfl⟩
          have h0' : 0 ≤ ‖fderiv ℝ u x0‖ := by positivity
          linarith
        have hM_all : ∀ x, ‖fderiv ℝ u x‖ ≤ M := by
          intro x
          by_cases hx : x ∈ K
          · exact hM ⟨x, hx, rfl⟩
          · rw [h_outside x hx]; simp <;> exact hM_nonneg
        have h4 : ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u x‖ =
            ∫⁻ x in K, ENNReal.ofReal ‖fderiv ℝ u x‖ := by
          have h5 : ∀ x ∉ K, ENNReal.ofReal ‖fderiv ℝ u x‖ = 0 := by
            intro x hx
            rw [h_outside x hx]; simp
          have h6 : ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u x‖ =
              ∫⁻ x, Set.indicator K (fun x => ENNReal.ofReal ‖fderiv ℝ u x‖) x := by
            apply lintegral_congr_ae
            filter_upwards with x
            by_cases hx : x ∈ K
            · simp [hx, Set.indicator_apply]
            · simp [hx, h5 x hx, Set.indicator_apply]
          have h7 : ∫⁻ x, Set.indicator K (fun x => ENNReal.ofReal ‖fderiv ℝ u x‖) x =
              ∫⁻ x in K, ENNReal.ofReal ‖fderiv ℝ u x‖ := by
            have h8 : ∫⁻ x in (Set.univ : Set (E n)), Set.indicator K (fun x => ENNReal.ofReal ‖fderiv ℝ u x‖) x =
                ∫⁻ x in K ∩ (Set.univ : Set (E n)), ENNReal.ofReal ‖fderiv ℝ u x‖ :=
              setLIntegral_indicator hK_meas (fun x => ENNReal.ofReal ‖fderiv ℝ u x‖)
            simpa using h8
          rw [h6, h7]
        have h1 : G ≤ ENNReal.ofReal M * volume K := by
          have hG_eq : G = ∫⁻ x in K, ENNReal.ofReal ‖fderiv ℝ u x‖ := by
            simpa [G] using h4
          rw [hG_eq]
          have h2 : ∫⁻ x in K, ENNReal.ofReal ‖fderiv ℝ u x‖ ≤
              ∫⁻ x in K, ENNReal.ofReal M := by
            exact setLIntegral_mono' hK_meas (fun x _ =>
              ENNReal.ofReal_le_ofReal (hM_all x))
          have h3 : ∫⁻ x in K, ENNReal.ofReal M = ENNReal.ofReal M * volume K := by simp
          exact h2.trans (le_of_eq h3)
        exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK_vol) h1

      -- Get uniform critical set constant
      rcases critical_set_bound_scaling u hu h_support hn' with ⟨C, hC_ne_top, hC_bound⟩

      -- Choose δ > 0 such that C * δ * volume(K) ≤ ε * G
      let V : ENNReal := volume K
      have hV_ne_top : V ≠ ⊤ := hK_vol
      have h_main : ∃ (δ : ℝ), 0 < δ ∧
          C * ENNReal.ofReal δ * V ≤ ENNReal.ofReal ε * G := by
        by_cases hC0 : C = 0
        · refine ⟨1, by norm_num, ?_⟩
          rw [hC0]; simp
        · by_cases hV0 : V = 0
          · refine ⟨1, by norm_num, ?_⟩
            rw [hV0]; simp
          · -- C > 0, V > 0, G > 0, all finite
            have hC_pos : 0 < C := pos_iff_ne_zero.mpr hC0
            have hV_pos : 0 < V := pos_iff_ne_zero.mpr hV0
            have hC_lt : C < ⊤ := WithTop.lt_top_iff_ne_top.mpr hC_ne_top
            have hV_lt : V < ⊤ := WithTop.lt_top_iff_ne_top.mpr hV_ne_top
            have hG_lt : G < ⊤ := WithTop.lt_top_iff_ne_top.mpr hG_ne_top
            let c : ℝ := C.toReal
            let v : ℝ := V.toReal
            let g : ℝ := G.toReal
            have hc_pos : 0 < c := ENNReal.toReal_pos_iff.mpr ⟨hC_pos, hC_lt⟩
            have hv_pos : 0 < v := ENNReal.toReal_pos_iff.mpr ⟨hV_pos, hV_lt⟩
            have hg_pos : 0 < g := ENNReal.toReal_pos_iff.mpr ⟨hG_pos, hG_lt⟩
            let δ : ℝ := (ε * g) / (2 * c * v)
            have hδ_pos : 0 < δ := by
              dsimp only [δ]; positivity
            refine ⟨δ, hδ_pos, ?_⟩
            have hC_eq : C = ENNReal.ofReal c := by rw [ENNReal.ofReal_toReal hC_ne_top]
            have hV_eq : V = ENNReal.ofReal v := by rw [ENNReal.ofReal_toReal hV_ne_top]
            have hG_eq : G = ENNReal.ofReal g := by rw [ENNReal.ofReal_toReal hG_ne_top]
            rw [hC_eq, hV_eq, hG_eq]
            have h4 : c * δ * v = ε * g / 2 := by
              dsimp only [δ]
              field_simp [hc_pos.ne', hv_pos.ne'] <;> ring
            have h5 : ENNReal.ofReal c * ENNReal.ofReal δ * ENNReal.ofReal v =
                ENNReal.ofReal (c * δ * v) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              <;> ring
            rw [h5]
            have h6 : ENNReal.ofReal (c * δ * v) = ENNReal.ofReal (ε * g / 2) := by rw [h4]
            rw [h6]
            have h7 : 0 ≤ ε * g := by positivity
            have h8 : ε * g / 2 ≤ ε * g := by linarith
            have h9 : ENNReal.ofReal (ε * g / 2) ≤ ENNReal.ofReal (ε * g) :=
              ENNReal.ofReal_le_ofReal h8
            have hε' : 0 ≤ ε := by linarith
            have h10 : ENNReal.ofReal (ε * g) = ENNReal.ofReal ε * ENNReal.ofReal g :=
              ENNReal.ofReal_mul hε'
            have h_goal : ENNReal.ofReal (ε * g / 2) ≤ ENNReal.ofReal ε * ENNReal.ofReal g := by
              convert h9 using 1
              <;> rw [h10]
            exact h_goal
      rcases h_main with ⟨δ, hδ_pos, hδ_choice⟩

      let Rδ : Set (E n) := {x | ‖fderiv ℝ u x‖ ≥ δ}
      let Cδ : Set (E n) := K \ Rδ

      have hCδ_meas : MeasurableSet Cδ := by
        have h1 : MeasurableSet Rδ := by
          have h_cont : Continuous (fun x => ‖fderiv ℝ u x‖) :=
            (hu.continuous_fderiv (by norm_num)).norm
          exact isClosed_Ici.measurableSet.preimage h_cont.measurable
        exact hK_meas.diff h1
      have hCδ_bdd : Bornology.IsBounded Cδ := hK_compact.isBounded.subset (diff_subset)
      have hCδ_sub : Cδ ⊆ {x | ‖fderiv ℝ u x‖ < δ} := by
        intro x hx
        simpa [Cδ, Rδ] using hx.2

      have h_vol_Cδ_le_V : volume Cδ ≤ V := by
        exact measure_mono (diff_subset)

      have h_crit_bound : ∫⁻ (s : ℝ), μHE[n - 1] (Cδ ∩ {x | u x = s}) ≤
          C * ENNReal.ofReal δ * V := by
        have h := hC_bound δ hδ_pos Cδ hCδ_meas hCδ_bdd hCδ_sub
        have h' : C * ENNReal.ofReal δ * volume Cδ ≤ C * ENNReal.ofReal δ * V := by
          gcongr <;> exact h_vol_Cδ_le_V
        exact h.trans h'

      -- For s > 0, {u=s} ⊆ K, and splits as Rδ ∪ Cδ parts
      have h_split_pos : ∀ (s : ℝ), 0 < s → μHE[n - 1] {x | u x = s} ≤
          μHE[n - 1] (Rδ ∩ {x | u x = s}) + μHE[n - 1] (Cδ ∩ {x | u x = s}) := by
        intro s hs_pos
        have h1 : {x | u x = s} ⊆ K := by
          intro x hx
          have h2 : u x ≠ 0 := by rw [hx]; linarith
          exact subset_closure (Function.mem_support.mpr h2)
        have h3 : {x | u x = s} = (Rδ ∩ {x | u x = s}) ∪ (Cδ ∩ {x | u x = s}) := by
          ext x
          simp only [Rδ, Cδ, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
          constructor
          · intro h4
            have h5 : x ∈ K := h1 h4
            by_cases h6 : ‖fderiv ℝ u x‖ ≥ δ
            · exact Or.inl ⟨h6, h4⟩
            · exact Or.inr ⟨⟨h5, h6⟩, h4⟩
          · rintro (⟨_, h4⟩ | ⟨_, h4⟩) <;> exact h4
        have h4 : μHE[n - 1] {x | u x = s} =
            μHE[n - 1] ((Rδ ∩ {x | u x = s}) ∪ (Cδ ∩ {x | u x = s})) := by
          congr 1
          <;> exact h3
        rw [h4]
        exact measure_union_le _ _

      have h_main_ineq :
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s} ≤
          (∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Rδ ∩ {x | u x = s})) +
          (∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Cδ ∩ {x | u x = s})) := by
        have h4 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s} ≤
            ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              (μHE[n - 1] (Rδ ∩ {x | u x = s}) + μHE[n - 1] (Cδ ∩ {x | u x = s})) :=
          setLIntegral_mono' hIoc_meas (fun s hs => h_split_pos s hs.1)
        have h5 : ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              (μHE[n - 1] (Rδ ∩ {x | u x = s}) + μHE[n - 1] (Cδ ∩ {x | u x = s})) ≤
            (∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Rδ ∩ {x | u x = s})) +
            (∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Cδ ∩ {x | u x = s})) := by
          let f : ℝ → ENNReal := fun s => μHE[n - 1] (Rδ ∩ {x | u x = s})
          let g : ℝ → ENNReal := fun s => μHE[n - 1] (Cδ ∩ {x | u x = s})
          rcases hu.lipschitzWith_of_hasCompactSupport h_support (by norm_num) with ⟨L, hL⟩
          have hRδ_meas : MeasurableSet Rδ := by
            have h_cont : Continuous (fun x => ‖fderiv ℝ u x‖) :=
              (hu.continuous_fderiv (by norm_num)).norm
            exact isClosed_Ici.measurableSet.preimage h_cont.measurable
          have hRδ_bdd : Bornology.IsBounded Rδ := hK_compact.isBounded.subset (by
            intro x hx
            simp only [Rδ, Set.mem_setOf_eq] at hx
            by_contra h
            have h9 : fderiv ℝ u x = 0 := h_outside x h
            rw [h9] at hx
            have h10 : (0 : ℝ) ≥ δ := by simpa using hx
            linarith)
          have hf_ae : AEMeasurable f volume :=
            levelSet_aemeasurable_lipschitz hn' hL hRδ_meas hRδ_bdd
          let S := Set.Ioc (0 : ℝ) 1
          let f' := Set.indicator S f
          let g' := Set.indicator S g
          have hf'_ae : AEMeasurable f' volume := hf_ae.indicator hIoc_meas
          have h_ind : f' + g' = Set.indicator S (f + g) := by
            funext s
            simp [f', g', Set.indicator_apply]
            <;> split_ifs <;> simp
          have h_add : ∫⁻ s, f' s + g' s = (∫⁻ s, f' s) + (∫⁻ s, g' s) := by
            have h : ∀ (g : ℝ → ENNReal), AEMeasurable f' volume →
                ∫⁻ (s : ℝ), f' s + g s = (∫⁻ (s : ℝ), f' s) + (∫⁻ (s : ℝ), g s) := by
              intro g hg
              exact lintegral_add_left' hf'_ae g
            exact h g' hf'_ae
          have h_eq1 : ∫⁻ s in S, (f s + g s) = ∫⁻ s, Set.indicator S (f + g) s := by exact Eq.symm (lintegral_indicator hIoc_meas (f + g))
          have h_eq2 : ∫⁻ s in S, f s = ∫⁻ s, f' s := by exact Eq.symm (lintegral_indicator hIoc_meas f)
          have h_eq3 : ∫⁻ s in S, g s = ∫⁻ s, g' s := by exact Eq.symm (lintegral_indicator hIoc_meas g)
          rw [h_eq1, h_eq2, h_eq3]
          have h_goal : ∫⁻ s, Set.indicator S (f + g) s = (∫⁻ s, f' s) + (∫⁻ s, g' s) := by
            have h1 : ∫⁻ s, Set.indicator S (f + g) s = ∫⁻ s, (f' + g') s := by rw [h_ind]
            rw [h1]
            have h2 : ∫⁻ s, (f' + g') s = ∫⁻ s, f' s + g' s := by
              congr with s <;> rfl
            rw [h2]
            exact h_add
          exact le_of_eq h_goal
        exact h4.trans h5

      have h_reg_le_G : ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          μHE[n - 1] (Rδ ∩ {x | u x = s}) ≤ G := by
        have h5 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Rδ ∩ {x | u x = s}) ≤
            ∫⁻ (s : ℝ), μHE[n - 1] (Rδ ∩ {x | u x = s}) :=
          setLIntegral_le_lintegral (Set.Ioc (0 : ℝ) 1) _
        have h6 := regular_set_coarea_equality u hu h_support δ hδ_pos hn'
        have h7 : ∫⁻ (x : E n) in Rδ, ENNReal.ofReal ‖fderiv ℝ u x‖ ≤ G :=
          setLIntegral_le_lintegral Rδ _
        exact h5.trans (h6.trans_le h7)

      have h_crit_le : ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          μHE[n - 1] (Cδ ∩ {x | u x = s}) ≤ C * ENNReal.ofReal δ * V := by
        have h5 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Cδ ∩ {x | u x = s}) ≤
            ∫⁻ (s : ℝ), μHE[n - 1] (Cδ ∩ {x | u x = s}) :=
          setLIntegral_le_lintegral (Set.Ioc (0 : ℝ) 1) _
        exact h5.trans h_crit_bound

      calc
        ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s}
          ≤ (∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Rδ ∩ {x | u x = s})) +
             (∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Cδ ∩ {x | u x = s})) := h_main_ineq
        _ ≤ G + C * ENNReal.ofReal δ * V := by gcongr <;> tauto
        _ ≤ G + ENNReal.ofReal ε * G := by gcongr <;> exact hδ_choice
        _ = ENNReal.ofReal (1 + ε) * G := by
          have h8 : G + ENNReal.ofReal ε * G = (1 + ENNReal.ofReal ε) * G := by
            rw [add_mul, one_mul]
          rw [h8]
          have h9 : (1 + ENNReal.ofReal ε) = ENNReal.ofReal (1 + ε) := by
            rw [ENNReal.ofReal_add (by norm_num) (show 0 ≤ ε from by linarith)] <;> norm_num
          rw [h9] <;> rfl

end Geometry

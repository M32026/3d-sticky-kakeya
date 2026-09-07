import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.Mollification
import Mathlib.Tactic


/-!
# Helper lemmas for gradient bounds

Provides 5 self-contained helper lemmas used by `SharpGradientBound`.
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory Convolution ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

/-- Smooth cutoff: exists η ∈ C_c^∞(Ω) with η=1 on K, 0≤η≤1. -/
lemma exists_smooth_cutoff
    {K : Set (E n)} (hK : IsCompact K)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (hKsub : K ⊆ Ω) :
    ∃ (η : E n → ℝ), ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      (∀ x ∈ K, η x = 1) ∧ (tsupport η ⊆ Ω) ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) := by
  let C := Ωᶜ
  have hC_closed : IsClosed C := hΩ_open.isClosed_compl
  have h_disj : Disjoint K C := by
    rw [Set.disjoint_left]
    intro x hx
    have h_x_in_Omega : x ∈ Ω := hKsub hx
    simpa [C] using h_x_in_Omega
  have h_main : ∃ (δ : ℝ), 0 < δ ∧ Disjoint (Metric.thickening δ K) (Metric.thickening δ C) :=
    h_disj.exists_thickenings hK hC_closed
  rcases h_main with ⟨δ, hδ_pos, hδ_disj⟩
  let U := Metric.thickening (δ / 2) K
  have hU_open : IsOpen U := Metric.isOpen_thickening
  have hK_U : K ⊆ U := Metric.self_subset_thickening (by linarith) K
  have hU_bounded : Bornology.IsBounded U := hK.isBounded.thickening
  have h_closure_U : closure U ⊆ Ω := by
    have h1 : closure U = Metric.cthickening (δ / 2) K := closure_thickening (by linarith) K
    rw [h1]
    have h2 : Metric.cthickening (δ / 2) K ⊆ Metric.thickening δ K :=
      Metric.cthickening_subset_thickening' (by linarith) (by linarith) K
    have h3 : Disjoint (Metric.thickening δ K) C :=
      hδ_disj.mono_right (Metric.self_subset_thickening hδ_pos C)
    have h4 : Metric.thickening δ K ⊆ Cᶜ := Set.disjoint_left.mp h3
    have h5 : Cᶜ = Ω := by ext x; simp [C]
    rw [h5] at h4
    exact h2.trans h4
  have hK_closed : IsClosed K := hK.isClosed
  let KC := Kᶜ
  have hKC_open : IsOpen KC := hK_closed.isOpen_compl
  rcases hU_open.exists_contDiff_support_eq (n := ⊤) with ⟨f, hf_support, hf_smooth, hf_range⟩
  rcases hKC_open.exists_contDiff_support_eq (n := ⊤) with ⟨g, hg_support, hg_smooth, hg_range⟩
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x => (hf_range ⟨x, rfl⟩).1
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => (hg_range ⟨x, rfl⟩).1
  have hf_pos_on_U : ∀ x ∈ U, 0 < f x := by
    intro x hx
    have h6 : x ∈ Function.support f := by rw [hf_support]; exact hx
    have h7 : f x ≠ 0 := h6
    have h8 : 0 ≤ f x := hf_nonneg x
    exact lt_of_le_of_ne h8 h7.symm
  have hg_pos_on_KC : ∀ x ∈ KC, 0 < g x := by
    intro x hx
    have h6 : x ∈ Function.support g := by rw [hg_support]; exact hx
    have h7 : g x ≠ 0 := h6
    have h8 : 0 ≤ g x := hg_nonneg x
    exact lt_of_le_of_ne h8 h7.symm
  have h_sum_pos : ∀ x, 0 < f x + g x := by
    intro x
    by_cases h : x ∈ U
    · exact add_pos_of_pos_of_nonneg (hf_pos_on_U x h) (hg_nonneg x)
    · have h9 : x ∉ K := fun hK => h (hK_U hK)
      have h10 : x ∈ KC := by exact h9
      exact add_pos_of_nonneg_of_pos (hf_nonneg x) (hg_pos_on_KC x h10)
  let η : E n → ℝ := fun x => f x / (f x + g x)
  have hη_smooth : ContDiff ℝ ∞ η :=
    hf_smooth.div (hf_smooth.add hg_smooth) (fun x => (h_sum_pos x).ne')
  have hη_one : ∀ x ∈ K, η x = 1 := by
    intro x hx
    have h10 : x ∈ U := hK_U hx
    have h11 : g x = 0 := by
      have h12 : x ∉ KC := by simpa [KC] using hx
      have h13 : x ∉ Function.support g := by rw [hg_support]; exact h12
      simpa [Function.mem_support] using h13
    have h14 : f x ≠ 0 := by
      have h15 : x ∈ Function.support f := by rw [hf_support]; exact h10
      exact h15
    simp [η, h11, h14]
  have hη_support : Function.support η ⊆ U := by
    intro x hx
    by_contra h9
    have h10 : f x = 0 := by
      have h11 : x ∉ Function.support f := by rw [hf_support]; exact h9
      simpa [Function.mem_support] using h11
    have h12 : η x = 0 := by simp [η, h10]
    have h13 : x ∉ Function.support η := by simpa [Function.mem_support] using h12
    exact h13 hx
  have hη_compact : HasCompactSupport η := by
    have h7 : tsupport η ⊆ closure U := closure_mono hη_support
    have h8 : IsCompact (closure U) := hU_bounded.isCompact_closure
    exact h8.of_isClosed_subset isClosed_closure h7
  have hη_bounds : ∀ x, 0 ≤ η x ∧ η x ≤ 1 := by
    intro x
    have h9 : 0 ≤ f x := hf_nonneg x
    have h10 : 0 ≤ g x := hg_nonneg x
    have h11 : 0 < f x + g x := h_sum_pos x
    constructor
    · exact div_nonneg h9 (by linarith)
    · have h12 : f x ≤ f x + g x := by linarith
      exact (div_le_one (by linarith)).mpr h12
  have h_tsupport_sub : tsupport η ⊆ Ω := by
    have h7 : tsupport η ⊆ closure U := closure_mono hη_support
    exact h7.trans h_closure_U
  exact ⟨η, hη_smooth, hη_compact, hη_one, h_tsupport_sub, hη_bounds⟩

/-- The standard mollifier is even: ρ(-x) = ρ(x). -/
lemma mollifier_even (ε : ℝ) (hε : 0 < ε) :
    ∀ (x : E n), Mollification.rho ε hε (-x) = Mollification.rho ε hε x := by
  let b : ContDiffBump (0 : E n) := Mollification.mollifier ε hε
  intro x
  have h1 : (b : E n → ℝ) (-x) = (b : E n → ℝ) x := by
    have h := b.sub x
    simpa using h
  have h2 : b.normed volume (-x) = b.normed volume x := by
    dsimp only [ContDiffBump.normed]
    rw [h1]
  exact h2

/-- Convolution adjoint: ∫ (ρ⋆f)(x)·h(x) dx = ∫ f(y)·(ρ⋆h)(y) dy
when ρ is even and compactly supported, f measurable bounded, h compactly supported. -/
lemma convolution_adjoint_symm
    {ρ : E n → ℝ} (hρ_cont : Continuous ρ) (hρ_support : HasCompactSupport ρ)
    (hρ_even : ∀ x, ρ (-x) = ρ x)
    {f : E n → ℝ} (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    {h : E n → ℝ} (hh_cont : Continuous h) (hh_support : HasCompactSupport h) :
    ∫ x, (convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * h x =
    ∫ y, f y * (convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume y) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  -- G1(t,x) = ρ(t) * f(x-t) * h(x), dominated by D1(t,x) = |ρ(t)| * |h(x)|
  let G1 : E n × E n → ℝ := fun p => ρ p.1 * f (p.2 - p.1) * h p.2
  have hG1_meas : Measurable G1 := by fun_prop
  let D1 : E n × E n → ℝ := fun p => |ρ p.1| * |h p.2|
  have hD1_cont : Continuous D1 :=
    (hρ_cont.norm.comp continuous_fst).mul (hh_cont.norm.comp continuous_snd)
  have hD1_support : Function.support D1 ⊆ (tsupport ρ) ×ˢ (tsupport h) := by
    rintro ⟨t, x⟩ hD1_ne
    have h1 : D1 (t, x) ≠ 0 := hD1_ne
    have h2 : |ρ t| ≠ 0 := (mul_ne_zero_iff.mp h1).1
    have h3 : |h x| ≠ 0 := (mul_ne_zero_iff.mp h1).2
    have h4 : ρ t ≠ 0 := by simpa [abs_ne_zero] using h2
    have h5 : h x ≠ 0 := by simpa [abs_ne_zero] using h3
    exact ⟨subset_tsupport ρ h4, subset_tsupport h h5⟩
  have hD1_cpct : HasCompactSupport D1 := by
    have h1 : tsupport D1 ⊆ closure (Function.support D1) := by simp [tsupport]
    have h2 : closure (Function.support D1) ⊆ (tsupport ρ) ×ˢ (tsupport h) :=
      closure_minimal hD1_support (hρ_support.prod hh_support).isClosed
    have h3 : IsCompact ((tsupport ρ) ×ˢ (tsupport h)) := hρ_support.prod hh_support
    exact h3.of_isClosed_subset isClosed_closure (h1.trans h2)
  have hD1_int : Integrable D1 (volume.prod volume) :=
    hD1_cont.integrable_of_hasCompactSupport hD1_cpct
  have hD1_nonneg : ∀ p, 0 ≤ D1 p := by intro p; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hG1_bound : ∀ p, |G1 p| ≤ |D1 p| := by
    intro p
    have h : |G1 p| ≤ D1 p := by
      rcases p with ⟨t, x⟩
      calc |G1 (t, x)| ≤ |ρ t| * |f (x - t)| * |h x| := by simp [G1, abs_mul] <;> ring_nf <;> exact le_refl _
        _ ≤ |ρ t| * 1 * |h x| := by gcongr; exact hf_bdd (x - t)
        _ = |ρ t| * |h x| := by ring
    rw [abs_of_nonneg (hD1_nonneg p)]
    exact h
  have hG1_int : Integrable G1 (volume.prod volume) := by
    have h_le : ∀ᵐ p, ‖G1 p‖ ≤ ‖D1 p‖ := by
      filter_upwards with p
      simpa [Real.norm_eq_abs] using hG1_bound p
    exact hD1_int.mono hG1_meas.aestronglyMeasurable h_le
  let g1 : E n → E n → ℝ := fun t x => ρ t * f (x - t) * h x
  have h_swap1 : ∫ t, ∫ x, g1 t x = ∫ x, ∫ t, g1 t x :=
    MeasureTheory.integral_integral_swap (f := g1) hG1_int
  have h_conv1 : ∀ (x : E n), convolution ρ f L volume x = ∫ t, ρ t * f (x - t) := by
    intro x
    simp [convolution_def, L, ContinuousLinearMap.lsmul_apply] <;> rfl
  have h_mul1 : ∀ (x : E n), (∫ t, ρ t * f (x - t)) * h x = ∫ t, g1 t x := by
    intro x
    have h_eq : ∀ t, g1 t x = (ρ t * f (x - t)) * h x := by
      intro t; simp [g1] <;> ring
    have h_int : ∫ t, g1 t x = ∫ t, (ρ t * f (x - t)) * h x := by
      apply integral_congr_ae; filter_upwards with t; exact h_eq t
    rw [h_int]
    have h2 : ∫ t, (ρ t * f (x - t)) * h x = (∫ t, ρ t * f (x - t)) * h x := by
      rw [MeasureTheory.integral_mul_const]
    rw [h2] <;> ring
  have h_eq1 : ∫ x, (convolution ρ f L volume x) * h x = ∫ t, ∫ x, g1 t x := by
    have h_step1 : ∫ x, (convolution ρ f L volume x) * h x =
        ∫ x, (∫ t, ρ t * f (x - t)) * h x := by
      apply integral_congr_ae; filter_upwards with x
      rw [h_conv1 x]
    rw [h_step1]
    have h_step2 : ∫ x, (∫ t, ρ t * f (x - t)) * h x = ∫ x, ∫ t, g1 t x := by
      apply integral_congr_ae; filter_upwards with x
      exact h_mul1 x
    rw [h_step2, h_swap1]
  rw [h_eq1]
  -- Translation: ∫ x, f(x-t)*h(x) = ∫ y, f(y)*h(y+t)
  have h_change : ∀ (t : E n), ∫ x : E n, f (x - t) * h x = ∫ y : E n, f y * h (y + t) := by
    intro t
    let g : E n → ℝ := fun x => f (x - t) * h x
    let e : E n ≃ᵐ E n :=
      { toFun := fun y : E n => y + t
        invFun := fun y : E n => y - t
        left_inv := by intro y; simp [add_sub_cancel]
        right_inv := by intro y; simp [sub_add_cancel]
        measurable_toFun := measurable_id.add measurable_const
        measurable_invFun := measurable_id.sub measurable_const }
    have hmp : MeasurePreserving e volume volume := measurePreserving_add_right volume t
    have h_trans : ∫ y : E n, g (e y) = ∫ x : E n, g x := hmp.integral_comp' g
    have h_eq2 : ∀ y, g (y + t) = f y * h (y + t) := by
      intro y
      have h9 : (y + t) - t = y := by abel
      simp [g, h9]
    have h_ey : ∀ y, g (e y) = g (y + t) := by intro y; rfl
    have h_trans2 : ∫ y, g (e y) = ∫ y, g (y + t) := by
      apply integral_congr_ae; filter_upwards with y; exact h_ey y
    have h_int2 : ∫ y, g (y + t) = ∫ y, f y * h (y + t) := by
      apply integral_congr_ae; filter_upwards with y; exact h_eq2 y
    calc
      ∫ x, g x = ∫ y, g (e y) := h_trans.symm
      _ = ∫ y, g (y + t) := h_trans2
      _ = ∫ y, f y * h (y + t) := h_int2
  have h4 : ∫ t, ∫ x, g1 t x = ∫ t, ρ t * (∫ y, f y * h (y + t)) := by
    have h_step : ∀ t, ∫ x, g1 t x = ρ t * (∫ y, f y * h (y + t)) := by
      intro t
      have h_a : ∫ x, g1 t x = ρ t * ∫ x, f (x - t) * h x := by
        have h_eq : ∀ x, g1 t x = ρ t * (f (x - t) * h x) := by intro x; simp [g1] <;> ring
        have h_int : ∫ x, g1 t x = ∫ x, ρ t * (f (x - t) * h x) := by
          apply integral_congr_ae; filter_upwards with x; exact h_eq x
        rw [h_int, integral_const_mul]
      rw [h_a, h_change t] <;> ring
    apply integral_congr_ae; filter_upwards with t; exact h_step t
  rw [h4]
  -- G2(t,y) = ρ(t) * f(y) * h(y+t), dominated by D2(t,y) = |ρ(t)| * |h(y+t)|
  let G2 : E n × E n → ℝ := fun p => ρ p.1 * f p.2 * h (p.2 + p.1)
  have hG2_meas : Measurable G2 := by fun_prop
  let D2 : E n × E n → ℝ := fun p => |ρ p.1| * |h (p.2 + p.1)|
  have hD2_cont : Continuous D2 :=
    (hρ_cont.norm.comp continuous_fst).mul (hh_cont.norm.comp (continuous_snd.add continuous_fst))
  let K1 := tsupport ρ
  let K2 := tsupport h
  have hK1 : IsCompact K1 := hρ_support
  have hK2 : IsCompact K2 := hh_support
  let Ksum := (fun p : E n × E n => p.1 - p.2) '' (K2 ×ˢ K1)
  have hKsum : IsCompact Ksum := (hK2.prod hK1).image (continuous_fst.sub continuous_snd)
  have hD2_support : Function.support D2 ⊆ K1 ×ˢ Ksum := by
    rintro ⟨t, y⟩ hD2_ne
    have h1 : D2 (t, y) ≠ 0 := hD2_ne
    have h2 : |ρ t| ≠ 0 := (mul_ne_zero_iff.mp h1).1
    have h3 : |h (y + t)| ≠ 0 := (mul_ne_zero_iff.mp h1).2
    have h4 : ρ t ≠ 0 := by simpa [abs_ne_zero] using h2
    have h5 : h (y + t) ≠ 0 := by simpa [abs_ne_zero] using h3
    have h6 : t ∈ K1 := subset_tsupport ρ h4
    have h7 : y + t ∈ K2 := subset_tsupport h h5
    have h8 : y ∈ Ksum := by
      use (y + t, t)
      constructor
      · exact ⟨h7, h6⟩
      · simp
    exact ⟨h6, h8⟩
  have hD2_cpct : HasCompactSupport D2 := by
    have h1 : tsupport D2 ⊆ closure (Function.support D2) := by
      simp [tsupport]
    have h2 : closure (Function.support D2) ⊆ K1 ×ˢ Ksum :=
      closure_minimal hD2_support (hK1.prod hKsum).isClosed
    have h3 : IsCompact (K1 ×ˢ Ksum) := hK1.prod hKsum
    exact h3.of_isClosed_subset isClosed_closure (h1.trans h2)
  have hD2_int : Integrable D2 (volume.prod volume) :=
    hD2_cont.integrable_of_hasCompactSupport hD2_cpct
  have hD2_nonneg : ∀ p, 0 ≤ D2 p := by intro p; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hG2_bound : ∀ p, |G2 p| ≤ |D2 p| := by
    intro p
    have h : |G2 p| ≤ D2 p := by
      rcases p with ⟨t, y⟩
      calc |G2 (t, y)| ≤ |ρ t| * |f y| * |h (y + t)| := by simp [G2, abs_mul] <;> ring_nf <;> exact le_refl _
        _ ≤ |ρ t| * 1 * |h (y + t)| := by gcongr; exact hf_bdd y
        _ = |ρ t| * |h (y + t)| := by ring
    rw [abs_of_nonneg (hD2_nonneg p)]
    exact h
  have hG2_int : Integrable G2 (volume.prod volume) := by
    have h_le : ∀ᵐ p, ‖G2 p‖ ≤ ‖D2 p‖ := by
      filter_upwards with p
      simpa [Real.norm_eq_abs] using hG2_bound p
    exact hD2_int.mono hG2_meas.aestronglyMeasurable h_le
  let g2 : E n → E n → ℝ := fun t y => ρ t * f y * h (y + t)
  have h_swap2 : ∫ t, ∫ y, g2 t y = ∫ y, ∫ t, g2 t y :=
    MeasureTheory.integral_integral_swap (f := g2) hG2_int
  have h_mul2 : ∀ y, ∫ t, g2 t y = f y * (∫ t, ρ t * h (y + t)) := by
    intro y
    have h_eq : ∀ t, g2 t y = ρ t * h (y + t) * f y := by
      intro t; simp [g2] <;> ring
    have h_int : ∫ t, g2 t y = ∫ t, ρ t * h (y + t) * f y := by
      apply integral_congr_ae; filter_upwards with t; exact h_eq t
    rw [h_int]
    have h2 : ∫ t, ρ t * h (y + t) * f y = (∫ t, ρ t * h (y + t)) * f y :=
      integral_mul_const (f y) (fun a => ρ a * h (y + a))
    rw [h2] <;> ring
  have h5 : ∫ t, ρ t * (∫ y, f y * h (y + t)) = ∫ y, f y * (∫ t, ρ t * h (y + t)) := by
    have h_step1 : ∫ t, ρ t * (∫ y, f y * h (y + t)) = ∫ t, ∫ y, g2 t y := by
      apply integral_congr_ae; filter_upwards with t
      have h6 : ρ t * ∫ y, f y * h (y + t) = ∫ y, g2 t y := by
        have h7 : ∫ y, g2 t y = ρ t * ∫ y, f y * h (y + t) := by
          have h_eq : ∀ y, g2 t y = ρ t * (f y * h (y + t)) := by
            intro y; simp [g2] <;> ring
          have h_int : ∫ y, g2 t y = ∫ y, ρ t * (f y * h (y + t)) := by
            apply integral_congr_ae; filter_upwards with y; exact h_eq y
          rw [h_int, integral_const_mul] <;> ring
        exact h7.symm
      exact h6
    rw [h_step1, h_swap2]
    apply integral_congr_ae; filter_upwards with y
    exact h_mul2 y
  rw [h5]
  -- Evenness: ∫ t, ρ(t)*h(y+t) = ∫ s, ρ(s)*h(y-s) = (ρ⋆h)(y)
  apply integral_congr_ae; filter_upwards with y
  have h6 : ∫ t : E n, ρ t * h (y + t) = ∫ s : E n, ρ s * h (y - s) := by
    let g_neg : E n → ℝ := fun s => ρ (-s) * h (y - s)
    let e_neg : E n ≃ₗᵢ[ℝ] E n :=
      { toFun := fun x : E n => -x
        invFun := fun x : E n => -x
        left_inv := by intro x; simp
        right_inv := by intro x; simp
        map_add' := by intro x y; exact neg_add x y
        map_smul' := by intro c x; exact (smul_neg c x).symm
        norm_map' := by intro x; exact norm_neg x }
    have h_neg_invar : ∀ (g : E n → ℝ), ∫ t, g (e_neg t) = ∫ s, g s := by
      intro g
      have hmp : MeasurePreserving (⇑e_neg) volume volume := LinearIsometryEquiv.measurePreserving e_neg
      have hme : MeasurableEmbedding (⇑e_neg) := by
        refine' ⟨e_neg.injective, e_neg.continuous.measurable, _⟩
        intro s hs
        have h_image : e_neg '' s = (fun x : E n => -x) ⁻¹' s := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            have h : e_neg x = -x := by rfl
            rw [h] at *; simpa using hx
          · intro hy
            refine ⟨-y, hy, ?_⟩
            have h : e_neg (-y) = y := by simp [e_neg]
            exact h
        rw [h_image]
        exact continuous_neg.measurable hs
      exact hmp.integral_comp hme g
    have h_neg : ∫ t : E n, g_neg (-t) = ∫ s : E n, g_neg s := by
      have h := h_neg_invar g_neg
      have h_eq : ∀ t, g_neg (e_neg t) = g_neg (-t) := by intro t; rfl
      have h' : ∫ t, g_neg (e_neg t) = ∫ t, g_neg (-t) := by
        apply integral_congr_ae; filter_upwards with t; exact h_eq t
      rw [h'] at h
      exact h
    have h_goal : ∫ t : E n, ρ t * h (y + t) = ∫ s : E n, ρ (-s) * h (y - s) := by
      have h_eq : ∀ t, g_neg (-t) = ρ t * h (y + t) := by
        intro t; simp [g_neg] <;> abel
      have h_int : ∫ t, g_neg (-t) = ∫ t, ρ t * h (y + t) := by
        apply integral_congr_ae; filter_upwards with t; exact h_eq t
      have h_final : ∫ s, g_neg s = ∫ s, ρ (-s) * h (y - s) := by
        apply integral_congr_ae; filter_upwards with s; rfl
      rw [h_int] at h_neg
      rw [h_final] at h_neg
      exact h_neg
    rw [h_goal]
    apply integral_congr_ae; filter_upwards with s; rw [hρ_even s]
  have h7 : ∫ s : E n, ρ s * h (y - s) = convolution ρ h L volume y := by
    simp [convolution_def, L, ContinuousLinearMap.lsmul_apply] <;> rfl
  rw [h6, h7] <;> rfl

/-- ∂_i(ρ ⋆ h) = ρ ⋆ ∂_i h when ρ is smooth compactly supported and h is smooth compactly supported. -/
lemma convolution_deriv_commute
    {ρ : E n → ℝ} (hρ_smooth : ContDiff ℝ ∞ ρ) (hρ_support : HasCompactSupport ρ)
    {h : E n → ℝ} (hh_smooth : ContDiff ℝ 1 h) (hh_support : HasCompactSupport h) (i : Fin n) :
    ∀ (x : E n), fderiv ℝ (convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
        (EuclideanSpace.single i 1) =
      convolution ρ (fun y => fderiv ℝ h y (EuclideanSpace.single i 1))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  intro x
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let L' := ContinuousLinearMap.precompR (Eₗ := E n) L
  have h1 : HasFDerivAt (convolution ρ h L volume)
      ((convolution ρ (fderiv ℝ h) L' volume) x) x :=
    hh_support.hasFDerivAt_convolution_right L
      hρ_smooth.continuous.locallyIntegrable hh_smooth x
  have h_fderiv : fderiv ℝ (convolution ρ h L volume) x =
      (convolution ρ (fderiv ℝ h) L' volume) x := h1.fderiv
  rw [h_fderiv]
  have h_fderiv_cont : Continuous (fderiv ℝ h) := hh_smooth.continuous_fderiv (by norm_num)
  have h_fderiv_support : HasCompactSupport (fderiv ℝ h) := hh_support.fderiv ℝ
  exact convolution_precompR_apply L
    hρ_smooth.continuous.locallyIntegrable h_fderiv_support h_fderiv_cont x
    (EuclideanSpace.single i 1)

/-- support(ρ ⋆ h) ⊆ support(ρ) + support(h) (Minkowski sum). -/
lemma support_convolution_bound
    {ρ h : E n → ℝ} (hρ_support : HasCompactSupport ρ) (hh_support : HasCompactSupport h) :
    Function.support (convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
      Set.image2 (· + ·) (Function.support ρ) (Function.support h) :=
  MeasureTheory.support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)

end Geometry.Perimeter

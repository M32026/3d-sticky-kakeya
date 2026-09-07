import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TrivialCovering
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic

/-!
# Small-diameter AD bound

Proves the paper-literal AD condition for a set `E` whose diameter is at most `2 * √rho`.
For `outputLoss = sigma / 2`, this holds for all `rho ≥ delta'` when `delta'` is small enough.

Uses interval covering (`length / r + 2`) and concavity of `x^(1-σ)`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set ENNReal

attribute [local instance] Classical.propDecidable

/-- A set of diameter at most `D` is contained in a closed interval of length `D`. -/
lemma set_of_diam_subset_interval
    {S : Set ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hS_diam : ∀ (x y : ℝ), x ∈ S → y ∈ S → |x - y| ≤ D) :
    ∃ (a : ℝ), S ⊆ Set.Icc a (a + D) := by
  by_cases hS : S.Nonempty
  · have h_bdd_above : BddAbove S := by
      rcases hS with ⟨x, hx⟩
      refine ⟨x + D, fun y hy => ?_⟩
      have h : |y - x| ≤ D := hS_diam y x hy hx
      have h' : y - x ≤ D := by
        have h_abs : y - x ≤ |y - x| := le_abs_self (y - x)
        linarith
      linarith
    have h_bdd_below : BddBelow S := by
      rcases hS with ⟨x, hx⟩
      refine ⟨x - D, fun y hy => ?_⟩
      have h : |y - x| ≤ D := hS_diam y x hy hx
      have h' : x - y ≤ D := by
        have h_abs : x - y ≤ |x - y| := le_abs_self (x - y)
        have h_symm : |x - y| = |y - x| := by
          have h2 : x - y = -(y - x) := by ring
          rw [h2, abs_neg]
        rw [h_symm] at h_abs
        linarith
      linarith
    let a : ℝ := sInf S
    let b : ℝ := sSup S
    have h_glb : IsGLB S a := Real.isGLB_sInf hS h_bdd_below
    have h_lub : IsLUB S b := Real.isLUB_sSup hS h_bdd_above
    have ha_lb : ∀ y ∈ S, a ≤ y := h_glb.1
    have hb_ub : ∀ y ∈ S, y ≤ b := h_lub.1
    have h3 : b - a ≤ D := by
      by_contra h4
      have h5 : D < b - a := by linarith
      set ε : ℝ := (b - a - D) / 3 with hε_def
      have hε_pos : 0 < ε := by linarith
      have h6 : ∃ x ∈ S, b - ε < x := by
        by_contra h
        push Not at h
        have h7 : b - ε ∈ upperBounds S := h
        have h8 : b ≤ b - ε := h_lub.2 h7
        linarith
      have h9 : ∃ y ∈ S, y < a + ε := by
        by_contra h
        push Not at h
        have h10 : a + ε ∈ lowerBounds S := h
        have h11 : a + ε ≤ a := h_glb.2 h10
        linarith
      rcases h6 with ⟨x, hx, hx_gt⟩
      rcases h9 with ⟨y, hy, hy_lt⟩
      have h12 : D < x - y := by linarith
      have h13 : |x - y| ≤ D := hS_diam x y hx hy
      have h14 : x - y ≤ |x - y| := le_abs_self (x - y)
      linarith
    exact ⟨a, fun y hy => ⟨ha_lb y hy, by linarith [hb_ub y hy, h3]⟩⟩
  · refine ⟨0, ?_⟩
    have h_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [h_empty]; simp

/-- Key inequality via concavity: if `C ≥ 3` and `C * (2t)^α ≥ 2t + 2`,
then `C * x^α ≥ x + 2` for all `x ∈ [1, 2t]`. -/
lemma key_ineq_concave2
    {α C t : ℝ} (hα1 : 0 < α) (hα2 : α < 1)
    (hC_pos : 0 < C) (ht_one : 1 ≤ t)
    (h1 : C ≥ 3)
    (ht : C * (2 * t)^α ≥ 2 * t + 2) :
    ∀ (x : ℝ), 1 ≤ x → x ≤ 2 * t → C * x^α ≥ x + 2 := by
  intro x hx1 hxt
  by_cases h_eq1 : x = 1
  · subst h_eq1
    have h_goal : C * (1 : ℝ)^α ≥ (1 : ℝ) + 2 := by
      have h : (1 : ℝ)^α = 1 := by simp
      rw [h]
      linarith
    exact h_goal
  · by_cases h_eqt : x = 2 * t
    · rw [h_eqt]; exact ht
    · have hx1' : 1 < x := by
        by_contra h3
        have h4 : x ≤ 1 := by linarith
        have h5 : x = 1 := by linarith
        exact h_eq1 h5
      have hxt' : x < 2 * t := by
        by_contra h3
        have h4 : x ≥ 2 * t := by linarith
        have h5 : x = 2 * t := by linarith
        exact h_eqt h5
      set w : ℝ := (2 * t - x) / (2 * t - 1) with hw_def
      have h_denom_pos : 0 < 2 * t - 1 := by linarith
      have hw0 : 0 ≤ w := by
        dsimp only [w]
        apply div_nonneg <;> linarith
      have hw1 : w ≤ 1 := by
        dsimp only [w]
        have h_num : 2 * t - x ≤ 2 * t - 1 := by linarith
        have h : (2 * t - x) / (2 * t - 1) ≤ 1 := by
          calc (2 * t - x) / (2 * t - 1)
            ≤ (2 * t - 1) / (2 * t - 1) := by gcongr
          _ = 1 := by field_simp [h_denom_pos.ne'] <;> ring
        exact h
      have hx_eq : x = w * (1 : ℝ) + (1 - w) * (2 * t) := by
        dsimp only [w]
        field_simp [h_denom_pos.ne'] <;> ring
      have h_concave : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ α) :=
        Real.concaveOn_rpow (by linarith) (by linarith)
      have h1' : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := by norm_num
      have ht' : (2 * t) ∈ Set.Ici (0 : ℝ) := by
        simp only [Set.mem_Ici] <;> linarith
      have h_1mw : 0 ≤ 1 - w := by
        have h : w ≤ 1 := hw1
        linarith
      have h_sum : w + (1 - w) = 1 := by ring
      have h_main : x ^ α ≥ w * (1 : ℝ)^α + (1 - w) * (2 * t)^α := by
        rw [hx_eq]
        have h_co := h_concave.2
        exact h_co h1' ht' hw0 h_1mw h_sum
      calc
        C * x^α
          ≥ C * (w * (1 : ℝ)^α + (1 - w) * (2 * t)^α) := by gcongr
        _ = w * C + (1 - w) * (C * (2 * t)^α) := by
          simp [one_rpow] <;> ring
        _ ≥ w * 3 + (1 - w) * (2 * t + 2) := by
          have h1w : 0 ≤ w := hw0
          have h2w : 0 ≤ 1 - w := by linarith
          nlinarith
        _ = x + 2 := by
          dsimp only [w]
          field_simp [h_denom_pos.ne'] <;> ring

/-- Small-diameter AD bound for `diam(E) ≤ 2√rho`.

For `outputLoss = sigma/2` and small `delta'`, the endpoint conditions hold for all
`rho ≥ delta'`, so this proves the full local AD bound. -/
lemma small_diameter_ad
    {delta' rho outputLoss sigma : ℝ}
    {E : Set ℝ}
    (hdelta'_pos : 0 < delta')
    (hdelta'_le_one : delta' ≤ 1)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hE_diam : ∀ (x y : ℝ), x ∈ E → y ∈ E → |x - y| ≤ 2 * Real.sqrt rho)
    (C : ENNReal)
    (hC_eq : C = Kakeya.realRpowENN delta' (-outputLoss))
    (hC_ge : (3 : ENNReal) ≤ C)
    (h_endpoint :
      ENNReal.ofReal (2 / Real.sqrt rho + 2) ≤
        C * Kakeya.realRpowENN (2 / Real.sqrt rho) (1 - sigma))
    (h_bridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2PaperADSet1 E rho (1 - sigma) C := by
  set c_real : ℝ := Real.rpow delta' (-outputLoss) with hc_real_def
  have hc_pos : 0 < c_real := Real.rpow_pos_of_pos hdelta'_pos _
  have hC_real : C = ENNReal.ofReal c_real := by
    rw [hC_eq]
    have h2 : c_real = Real.rpow delta' (-outputLoss) := hc_real_def.symm
    rw [h2]
    <;> rfl
  have hC_ge3 : 3 ≤ c_real := by
    have h : (3 : ENNReal) ≤ C := hC_ge
    rw [hC_real] at h
    have h' : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by norm_cast
    rw [h'] at h
    have h_iff : ENNReal.ofReal (3 : ℝ) ≤ ENNReal.ofReal c_real ↔ (3 : ℝ) ≤ c_real :=
      ENNReal.ofReal_le_ofReal_iff (by positivity)
    exact h_iff.mp h
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  set t : ℝ := 1 / Real.sqrt rho with ht_def
  have ht_one : 1 ≤ t := by
    dsimp only [t]
    have h : Real.sqrt rho ≤ 1 := by rw [Real.sqrt_le_one] <;> linarith
    have h2 : 0 < Real.sqrt rho := hsqrt_pos
    calc 1 = Real.sqrt rho / Real.sqrt rho := by field_simp [h2.ne'] <;> ring
      _ ≤ 1 / Real.sqrt rho := by gcongr
  have hα1 : 0 < 1 - sigma := by linarith
  have hα2 : 1 - sigma < 1 := by linarith
  have ht_real : c_real * (2 * t)^(1 - sigma) ≥ 2 * t + 2 := by
    have h_eq1 : (2 / Real.sqrt rho + 2 : ℝ) = 2 * t + 2 := by
      simp [ht_def] <;> ring
    have h_eq2 : (2 / Real.sqrt rho : ℝ) = 2 * t := by
      simp [ht_def] <;> ring
    have h3 : ENNReal.ofReal (2 * t + 2) ≤ C * Kakeya.realRpowENN (2 * t) (1 - sigma) := by
      have h4 : ENNReal.ofReal (2 / Real.sqrt rho + 2) ≤ C * Kakeya.realRpowENN (2 / Real.sqrt rho) (1 - sigma) := h_endpoint
      simpa [h_eq1, h_eq2] using h4
    have h_mul : C * Kakeya.realRpowENN (2 * t) (1 - sigma) = ENNReal.ofReal (c_real * (2 * t)^(1 - sigma)) := by
      rw [hC_real]
      have h5 : Kakeya.realRpowENN (2 * t) (1 - sigma) = ENNReal.ofReal ((2 * t)^(1 - sigma)) := by rfl
      rw [h5]
      rw [← ENNReal.ofReal_mul (by positivity)]
      <;> rfl
    rw [h_mul] at h3
    have h_iff : ENNReal.ofReal (2 * t + 2) ≤ ENNReal.ofReal (c_real * (2 * t)^(1 - sigma)) ↔
        2 * t + 2 ≤ c_real * (2 * t)^(1 - sigma) :=
      ENNReal.ofReal_le_ofReal_iff (by positivity)
    exact h_iff.mp h3
  have h_key : ∀ (x : ℝ), 1 ≤ x → x ≤ 2 * t → c_real * x^(1 - sigma) ≥ x + 2 :=
    key_ineq_concave2 hα1 hα2 hc_pos ht_one hC_ge3 ht_real
  refine' ⟨by linarith, by linarith, by linarith, _ , _ , _⟩
  · exact le_trans (by norm_num) hC_ge
  · have h : C ≠ ⊤ := by
      rw [hC_real]
      exact ENNReal.ofReal_ne_top
    exact h
  · intro r hr hdelta_le_r left length hlength_ge_r
    let T : Set ℝ := E ∩ Set.Icc left (left + length)
    have hr_pos : 0 < r := by linarith
    have hT_diam_E : ∀ (x y : ℝ), x ∈ T → y ∈ T → |x - y| ≤ 2 * Real.sqrt rho := by
      intro x y hx hy; exact hE_diam x y hx.1 hy.1
    have hT_diam_len : ∀ (x y : ℝ), x ∈ T → y ∈ T → |x - y| ≤ length := by
      intro x y hx hy
      have hx1 : left ≤ x := hx.2.1
      have hx2 : x ≤ left + length := hx.2.2
      have hy1 : left ≤ y := hy.2.1
      have hy2 : y ≤ left + length := hy.2.2
      have h : |x - y| ≤ length := by rw [abs_le] <;> constructor <;> linarith
      exact h
    set D : ℝ := min (2 * Real.sqrt rho) length with hD_def
    have hD_nonneg : 0 ≤ D := by
      dsimp only [D]
      have h1 : 0 ≤ 2 * Real.sqrt rho := by positivity
      have h2 : 0 ≤ length := by linarith [hlength_ge_r, hr_pos]
      exact le_min h1 h2
    have hT_diam : ∀ (x y : ℝ), x ∈ T → y ∈ T → |x - y| ≤ D := by
      intro x y hx hy
      have h1 : |x - y| ≤ 2 * Real.sqrt rho := hT_diam_E x y hx hy
      have h2 : |x - y| ≤ length := hT_diam_len x y hx hy
      exact le_min h1 h2
    rcases set_of_diam_subset_interval hD_nonneg hT_diam with ⟨a, hT_sub⟩
    have hcov : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
        ENNReal.ofReal (D / r) + 2 :=
      externalCoveringNumber_subset_interval hr_pos (by positivity) hT_sub
    by_cases h_len : length ≤ 2 * Real.sqrt rho
    · -- Case 1: length ≤ 2√rho
      have hD_eq : D = length := by
        simp [hD_def, h_len] <;> linarith
      rw [hD_eq] at hcov
      set x : ℝ := length / r with hx_def
      have hx1 : 1 ≤ x := by
        dsimp only [x]; calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
          _ ≤ length / r := by gcongr
      have hx_le : x ≤ 2 * t := by
        dsimp only [x, t]
        have h : length ≤ 2 * Real.sqrt rho := h_len
        have h5 : 0 < Real.sqrt rho := hsqrt_pos
        have h6 : 0 ≤ 2 * Real.sqrt rho := by positivity
        have h7 : (2 * Real.sqrt rho) / r ≤ (2 * Real.sqrt rho) / rho := by
          gcongr
          <;> linarith
        have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (by linarith)
        calc length / r
          ≤ (2 * Real.sqrt rho) / r := by gcongr
          _ ≤ (2 * Real.sqrt rho) / rho := h7
          _ = 2 / Real.sqrt rho := by
            have h8 : (2 * Real.sqrt rho) / rho = 2 / Real.sqrt rho := by
              have h_mult : (2 / Real.sqrt rho) * rho = 2 * Real.sqrt rho := by
                calc (2 / Real.sqrt rho) * rho
                  = (2 / Real.sqrt rho) * (Real.sqrt rho) ^ 2 := by rw [hsq]
                _ = 2 * Real.sqrt rho := by field_simp [h5.ne'] <;> ring
              exact (div_eq_iff (by positivity)).mpr h_mult.symm
            exact h8
          _ = 2 * t := by simp [ht_def] <;> ring
      have h_real : x + 2 ≤ c_real * x^(1 - sigma) := h_key x hx1 hx_le
      have h_ennreal : ENNReal.ofReal (x + 2) ≤
          C * Kakeya.realRpowENN x (1 - sigma) := by
        have h6 : C * Kakeya.realRpowENN x (1 - sigma) =
            ENNReal.ofReal (c_real * x^(1 - sigma)) := by
          rw [hC_real]
          have h7 : Kakeya.realRpowENN x (1 - sigma) = ENNReal.ofReal (x^(1 - sigma)) := by rfl
          rw [h7]
          rw [← ENNReal.ofReal_mul (by positivity)]
          <;> rfl
        rw [h6]
        exact ENNReal.ofReal_le_ofReal h_real
      have hcov' : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
          ENNReal.ofReal (x + 2) := by
        have h9 : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤ ENNReal.ofReal x + 2 := hcov
        have h10 : ENNReal.ofReal x + (2 : ENNReal) = ENNReal.ofReal (x + 2) := by
          have hx_nonneg : 0 ≤ x := by positivity
          have h2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
          have h11 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_cast
          rw [h11]
          exact (ENNReal.ofReal_add hx_nonneg h2_nonneg).symm
        rw [h10] at h9
        exact h9
      exact hcov'.trans h_ennreal
    · -- Case 2: length > 2√rho
      have hD_eq : D = 2 * Real.sqrt rho := by
        simp [hD_def] <;> linarith
      set y : ℝ := 2 * Real.sqrt rho / r with hy_def
      have h_y_nonneg : 0 ≤ y := by positivity
      have hy_le : y ≤ 2 * t := by
        dsimp only [y, t]
        have h : r ≥ rho := hdelta_le_r
        have h5 : 0 < Real.sqrt rho := hsqrt_pos
        have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (by linarith)
        calc (2 * Real.sqrt rho) / r
          ≤ (2 * Real.sqrt rho) / rho := by gcongr
          _ = 2 / Real.sqrt rho := by
            have h6 : (2 * Real.sqrt rho) / rho = 2 / Real.sqrt rho := by
              have h_mult : (2 / Real.sqrt rho) * rho = 2 * Real.sqrt rho := by
                calc (2 / Real.sqrt rho) * rho
                  = (2 / Real.sqrt rho) * (Real.sqrt rho) ^ 2 := by rw [hsq]
                _ = 2 * Real.sqrt rho := by field_simp [h5.ne'] <;> ring
              exact (div_eq_iff (by positivity)).mpr h_mult.symm
            exact h6
          _ = 2 * t := by simp [ht_def] <;> ring
      have h_y_lt_len : y < length / r := by
        dsimp only [y]
        have h : 2 * Real.sqrt rho < length := by linarith
        gcongr
      by_cases h_y1 : 1 ≤ y
      · -- Subcase 2a: y ≥ 1, use concavity
        have h_real : y + 2 ≤ c_real * y^(1 - sigma) := h_key y h_y1 hy_le
        have h_ennreal : ENNReal.ofReal (y + 2) ≤
            C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
          have h_pos1 : 0 ≤ y := by positivity
          have h3 : y^(1 - sigma) ≤ (length / r)^(1 - sigma) :=
            Real.rpow_le_rpow h_pos1 h_y_lt_len.le (by linarith)
          have h4 : c_real * y^(1 - sigma) ≤ c_real * (length / r)^(1 - sigma) := by gcongr
          have h5 : y + 2 ≤ c_real * (length / r)^(1 - sigma) := h_real.trans h4
          have h6 : C * Kakeya.realRpowENN (length / r) (1 - sigma) =
              ENNReal.ofReal (c_real * (length / r)^(1 - sigma)) := by
            rw [hC_real]
            have h7 : Kakeya.realRpowENN (length / r) (1 - sigma) = ENNReal.ofReal ((length / r)^(1 - sigma)) := by rfl
            rw [h7]
            rw [← ENNReal.ofReal_mul (by positivity)]
            <;> rfl
          rw [h6]
          exact ENNReal.ofReal_le_ofReal h5
        have hD_div_r_eq_y : D / r = y := by
          simp [hD_eq, hy_def] <;> ring
        have hcov_y : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤ ENNReal.ofReal y + 2 := by
          rw [hD_div_r_eq_y] at hcov
          exact hcov
        have hcov' : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
            ENNReal.ofReal (y + 2) := by
          have h10 : ENNReal.ofReal y + (2 : ENNReal) = ENNReal.ofReal (y + 2) := by
            have hy_nonneg : 0 ≤ y := by positivity
            have h2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
            have h11 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_cast
            rw [h11]
            exact (ENNReal.ofReal_add hy_nonneg h2_nonneg).symm
          rw [h10] at hcov_y
          exact hcov_y
        exact hcov'.trans h_ennreal
      · -- Subcase 2b: y < 1, i.e. r > 2√rho. Single ball suffices.
        have h_y_lt1 : y < 1 := by linarith
        have h_diam_lt_r : D < r := by
          dsimp only [y] at h_y_lt1
          have h : 2 * Real.sqrt rho / r < 1 := h_y_lt1
          have h2 : 0 < r := hr_pos
          have h3 : 2 * Real.sqrt rho < r := by
            calc 2 * Real.sqrt rho
              = (2 * Real.sqrt rho / r) * r := by field_simp [h2.ne'] <;> ring
            _ < 1 * r := by gcongr
            _ = r := by ring
          simpa [hD_eq] using h3
        have h_single : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤ 1 := by
          rcases set_of_diam_subset_interval (by linarith) hT_diam with ⟨a, hT_sub2⟩
          have h_center : T ⊆ Metric.closedBall a r := by
            intro z hz
            have hz1 : a ≤ z := (hT_sub2 hz).1
            have hz2 : z ≤ a + D := (hT_sub2 hz).2
            have h : dist z a ≤ r := by
              simp only [Real.dist_eq, abs_le]
              constructor <;> linarith [h_diam_lt_r]
            simpa [Metric.mem_closedBall] using h
          let ε : NNReal := ⟨r, hr⟩
          have h_iscover : Metric.IsCover ε T ({a} : Set ℝ) := by
            intro z hz
            have h_dist : dist z a ≤ r := h_center hz
            have h_edist : edist z a ≤ (ε : ENNReal) := by
              rw [edist_dist]
              have h_coe : (↑ε : ENNReal) = ENNReal.ofReal (↑ε : ℝ) := by simp
              rw [h_coe]
              have h_eps : (↑ε : ℝ) = r := Subtype.coe_mk r hr
              rw [h_eps]
              exact ENNReal.ofReal_le_ofReal h_dist
            exact ⟨a, by simp, h_edist⟩
          calc (Metric.externalCoveringNumber ε T : ENNReal)
            ≤ ({a} : Set ℝ).encard := by exact_mod_cast h_iscover.externalCoveringNumber_le_encard
          _ = 1 := by simp
        have h_len_r_ge1 : 1 ≤ length / r := by
          calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
            _ ≤ length / r := by gcongr
        have h_rpow_ge1 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / r) (1 - sigma) := by
          simp only [Kakeya.realRpowENN]
          have h15 : 0 ≤ 1 - sigma := by linarith
          have h16 : 1 ≤ Real.rpow (length / r) (1 - sigma) :=
            Real.one_le_rpow h_len_r_ge1 h15
          exact ENNReal.one_le_ofReal.mpr h16
        have h_final : (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
          have h1 : (1 : ENNReal) ≤ C := le_trans (by norm_num) hC_ge
          have h2 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / r) (1 - sigma) := h_rpow_ge1
          have h3 : (1 : ENNReal) * (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
            gcongr
          simpa using h3
        exact h_single.trans h_final

end Kakeya.Assouad

end

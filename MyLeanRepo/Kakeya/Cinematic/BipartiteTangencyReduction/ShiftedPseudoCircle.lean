import MyLeanRepo.Kakeya.Cinematic.Geometry
import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerturbationPreservation
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ReparametrizeBridge
import MyLeanRepo.Kakeya.Cinematic.PreliminaryDichotomy
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pseudo-circle property for pre-shifted bipartite families

This module proves that a bipartite family with a fixed polynomial-size vertical
shift on one color, followed by a small perturbation, forms a graph pseudo-circle
family on a short interval.

The key insight: for any pair of shifted curves, their difference is `h + c`
where `h` is the difference of the original (unshifted) functions and `c` is a
constant. Using the preliminary dichotomy on the original family:

- **Same-color pairs** (W-W or B-B): `|c| < d/(6K)` by the pairwise shift bound,
  since vertical translation by the same constant preserves `c2Distance`.
- **Cross-color pairs** (W-B): `|c| ≤ epsilon + 2*delta'`, and the quantitative
  bound `tangency^50 * delta ≤ t/(1000K²)` ensures `epsilon + 2*delta' < t/(3K)
  ≤ d/(6K)` since `d ≥ 2t`.

Thus `two_zeros_level_via_dichotomy` applies to every pair, giving at most two
intersections. Transversality follows from `HasNoExactTangenciesOn`.
-/

namespace Kakeya.Cinematic

open Set

noncomputable section

local instance instDecidableEqC2FunctionShiftedPseudoCircle :
    DecidableEq C2Function := Classical.decEq _

/--
Arithmetic bound: `epsilon + 2*delta' < t/(3K)` under the smallness condition.

This ensures the total relative shift for cross-color pairs is below the
dichotomy threshold `d/(6K)` (since `d ≥ 2t` implies `d/(6K) ≥ t/(3K)`).
-/
lemma shift_sum_lt_dist_sixth
    {K tangency delta t delta' : ℝ}
    (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (hdelta : 0 < delta) (ht : 0 < t)
    (h_small : tangency^50 * delta ≤ t / (1000 * K^2))
    (epsilon : ℝ) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_bound : epsilon ≤ 25 * tangency^10 * delta)
    (hdelta'_nonneg : 0 ≤ delta') (hdelta'_le : delta' ≤ delta) :
    epsilon + 2 * delta' < t / (3 * K) := by
  have hK_pos : 0 < K := by linarith
  have h_tang_pos : 0 < tangency := by linarith
  have h_tang50_pos : 0 < tangency^50 := by positivity
  have h_denom_pos : 0 < 1000 * K^2 * tangency^50 := by positivity

  -- Key arithmetic: 25*T^10 + 2 < (1000/3) * K * T^50 for K≥1, T≥5
  have h_key : 25 * tangency^10 + 2 < (1000 / 3 : ℝ) * K * tangency^50 := by
    have h1 : 25 * tangency^10 + 2 ≤ 27 * tangency^10 := by
      have h2 : 1 ≤ tangency^10 := by
        have h3 : 1 ≤ tangency := by linarith
        have h4 : (1 : ℝ)^10 ≤ tangency^10 := by gcongr
        simpa using h4
      nlinarith
    have h5 : 1 < tangency := by linarith
    have h_tang40_gt_one : 1 < tangency^40 := by
      have h6 : 5 ≤ tangency := htang
      have h7 : (5 : ℝ)^40 ≤ tangency^40 := by gcongr
      have h8 : (1 : ℝ) < (5 : ℝ)^40 := by norm_num
      linarith
    have h6 : tangency^10 < tangency^50 := by
      have h7 : tangency^50 = tangency^10 * tangency^40 := by ring
      rw [h7]
      have h9 : 0 < tangency^10 := by positivity
      nlinarith
    have h10 : (1000 / 3 : ℝ) * K > 27 := by nlinarith
    nlinarith [pow_pos h_tang_pos 10]

  -- delta ≤ t / (1000 * K^2 * tangency^50)
  have h_delta_bound : delta ≤ t / (1000 * K^2 * tangency^50) := by
    have h_eq : delta = (tangency^50 * delta) / tangency^50 := by
      field_simp [h_tang50_pos.ne'] <;> ring
    rw [h_eq]
    have h_div : (tangency^50 * delta) / tangency^50 ≤ (t / (1000 * K^2)) / tangency^50 := by
      apply div_le_div_of_nonneg_right h_small
      positivity
    have h_final : (t / (1000 * K^2)) / tangency^50 = t / (1000 * K^2 * tangency^50) := by
      field_simp [hK_pos.ne', h_tang50_pos.ne'] <;> ring
    rw [h_final] at h_div
    exact h_div

  -- (25*T^10+2) / (1000*K^2*T^50) < 1/(3*K)
  have h_frac : (25 * tangency^10 + 2) / (1000 * K^2 * tangency^50) < 1 / (3 * K) := by
    have h9 : 25 * tangency^10 + 2 < (1000 * K^2 * tangency^50) / (3 * K) := by
      have h10 : (1000 * K^2 * tangency^50) / (3 * K) = (1000 / 3 : ℝ) * K * tangency^50 := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h10]
      exact h_key
    have h11 : 0 < 3 * K := by positivity
    calc
      (25 * tangency^10 + 2) / (1000 * K^2 * tangency^50)
        < ((1000 * K^2 * tangency^50) / (3 * K)) / (1000 * K^2 * tangency^50) := by
          gcongr
      _ = 1 / (3 * K) := by
        field_simp [h_denom_pos.ne', h11.ne'] <;> ring

  have h1 : epsilon + 2 * delta' ≤ (25 * tangency^10 + 2) * delta := by
    calc
      epsilon + 2 * delta' ≤ 25 * tangency^10 * delta + 2 * delta := by gcongr
      _ = (25 * tangency^10 + 2) * delta := by ring

  calc
    epsilon + 2 * delta'
      ≤ (25 * tangency^10 + 2) * delta := h1
    _ ≤ (25 * tangency^10 + 2) * (t / (1000 * K^2 * tangency^50)) := by gcongr
    _ = ((25 * tangency^10 + 2) / (1000 * K^2 * tangency^50)) * t := by
      field_simp [h_denom_pos.ne'] <;> ring
    _ < (1 / (3 * K)) * t := by gcongr
    _ = t / (3 * K) := by field_simp [hK_pos.ne'] <;> ring

/--
Pseudo-circle property for a bipartite family with a fixed pre-shift on W.

Given `W, B ⊆ family`, a fixed shift `epsilon` applied to W, and a perturbation
`shift` with small amplitude, the resulting reparametrized curves form a graph
pseudo-circle family on `I`.
-/
lemma shifted_bipartite_pseudo_circle
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function} (hfam : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI_short : I.IsShort K) (hI_pos : 0 < I.length)
    {W B : Set C2Function} (hW : W ⊆ family) (hB : B ⊆ family)
    {delta t tangency epsilon : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t) (htang : 5 ≤ tangency)
    (h_small : tangency^50 * delta ≤ t / (1000 * K^2))
    (h_sep : ∀ w ∈ W, ∀ b ∈ B, 2 * t ≤ c2Distance w b)
    (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_bound : epsilon ≤ 25 * tangency^10 * delta)
    (F_up : FiniteFunctionFamily)
    (hF_up_W : ∀ f ∈ F_up.carrier, (∃ w ∈ W, f = w.verticalTranslate epsilon) ∨ f ∈ B)
    (hF_up_B : ∀ b ∈ B, b ∈ F_up.carrier)
    (hF_up_W' : ∀ w ∈ W, w.verticalTranslate epsilon ∈ F_up.carrier)
    {shift : C2Function → ℝ}
    (h_shift_amp : ∀ f ∈ F_up.carrier, |shift f| ≤ delta)
    (h_shift_bound : ∀ f ∈ F_up.carrier, ∀ g ∈ F_up.carrier, f ≠ g →
      |shift f - shift g| < c2Distance f g / (6 * K))
    (h_no_tang : F_up.HasNoExactTangenciesOn I shift) :
    IsGraphPseudoCircleFamily
      (F_up.toFinset.image (fun f => (f.verticalTranslate (shift f)).reparam I)) := by
  let F_shifted : Finset C2Function :=
    F_up.toFinset.image (fun f => f.verticalTranslate (shift f))

  -- Helper: vertical translation by same constant preserves c2Distance
  have h_vt_same_dist : ∀ (w1 w2 : C2Function),
      c2Distance (w1.verticalTranslate epsilon) (w2.verticalTranslate epsilon) =
      c2Distance w1 w2 := by
    intro w1 w2
    exact c2Distance_verticalTranslate_same w1 w2 epsilon

  -- At most two intersections for any pair in F_shifted
  have h_at_most_two : ∀ (F' : C2Function), F' ∈ F_shifted →
      ∀ (G' : C2Function), G' ∈ F_shifted → F' ≠ G' →
        ∀ (y₁ y₂ y₃ : UnitPoint), y₁ ∈ I.carrier → y₂ ∈ I.carrier → y₃ ∈ I.carrier →
          (y₁ : ℝ) < (y₂ : ℝ) → (y₂ : ℝ) < (y₃ : ℝ) →
          F' y₁ = G' y₁ → F' y₂ = G' y₂ → F' y₃ = G' y₃ → False := by
    intro F' hF' G' hG' hne
    rcases Finset.mem_image.mp hF' with ⟨f, hf_F, rfl⟩
    rcases Finset.mem_image.mp hG' with ⟨g, hg_F, rfl⟩
    have hf : f ∈ F_up.carrier := by simpa [FiniteFunctionFamily.toFinset] using hf_F
    have hg : g ∈ F_up.carrier := by simpa [FiniteFunctionFamily.toFinset] using hg_F
    have hfg : f ≠ g := by
      intro h; rw [h] at hne; exact hne rfl

    intro y₁ y₂ y₃ hy₁ hy₂ hy₃ h12 h23 eq1 eq2 eq3

    -- Extract original functions and constant c
    rcases hF_up_W f hf with (h_f_W | h_f_B) <;>
      rcases hF_up_W g hg with (h_g_W | h_g_B)

    · -- Both f, g from W_up
      rcases h_f_W with ⟨w1, hw1, rfl⟩
      rcases h_g_W with ⟨w2, hw2, rfl⟩
      have hfw1 : w1 ∈ family := hW hw1
      have hfw2 : w2 ∈ family := hW hw2
      have h_w1_ne_w2 : w1 ≠ w2 := by
        intro h; apply hfg; rw [h]
      set c : ℝ := shift (w2.verticalTranslate epsilon) - shift (w1.verticalTranslate epsilon) with hc_def
      have hc : |c| < c2Distance w1 w2 / (6 * K) := by
        have h_dist_eq : c2Distance (w1.verticalTranslate epsilon) (w2.verticalTranslate epsilon) =
            c2Distance w1 w2 := h_vt_same_dist w1 w2
        have h := h_shift_bound (w1.verticalTranslate epsilon) (hF_up_W' w1 hw1)
          (w2.verticalTranslate epsilon) (hF_up_W' w2 hw2) hfg
        rw [h_dist_eq] at h
        have h' : |c| < c2Distance w1 w2 / (6 * K) := by
          have h_abs : |shift (w2.verticalTranslate epsilon) - shift (w1.verticalTranslate epsilon)| =
              |shift (w1.verticalTranslate epsilon) - shift (w2.verticalTranslate epsilon)| := by
            rw [show shift (w2.verticalTranslate epsilon) - shift (w1.verticalTranslate epsilon) =
                -(shift (w1.verticalTranslate epsilon) - shift (w2.verticalTranslate epsilon)) by ring]
            rw [abs_neg]
          rw [h_abs]
          simpa [hc_def] using h
        exact h'
      have h_eq1 : w1 y₁ - w2 y₁ = c := by
        simp [verticalTranslate_apply] at eq1
        linarith [hc_def]
      have h_eq2 : w1 y₂ - w2 y₂ = c := by
        simp [verticalTranslate_apply] at eq2
        linarith [hc_def]
      have h_eq3 : w1 y₃ - w2 y₃ = c := by
        simp [verticalTranslate_apply] at eq3
        linarith [hc_def]
      exact two_zeros_level_via_dichotomy hK hD hfam hI_short hfw1 hfw2 h_w1_ne_w2 hc
        hy₁ hy₂ hy₃ h12 h23 h_eq1 h_eq2 h_eq3

    · -- f from W_up, g from B
      rcases h_f_W with ⟨w, hw, rfl⟩
      have hb : g ∈ B := h_g_B
      have hfw : w ∈ family := hW hw
      have hfg_fam : g ∈ family := hB hb
      have h_w_ne_g : w ≠ g := by
        have h_pos : 0 < c2Distance w g := by
          have h_sep' : 2 * t ≤ c2Distance w g := h_sep w hw g hb
          linarith
        intro h
        rw [h] at h_pos
        simp [c2Distance_eq_dist, dist_self] at h_pos <;> exact h_pos
      set c : ℝ := shift g - shift (w.verticalTranslate epsilon) - epsilon with hc_def
      have h_abs : |c| ≤ |shift g| + |shift (w.verticalTranslate epsilon)| + |epsilon| := by
        rw [hc_def]
        have h_tri : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
          intro a b
          have h : dist a b ≤ dist a (0 : ℝ) + dist (0 : ℝ) b := dist_triangle a 0 b
          simpa [Real.dist_eq] using h
        have h1 := h_tri (shift g - shift (w.verticalTranslate epsilon)) epsilon
        have h2 := h_tri (shift g) (shift (w.verticalTranslate epsilon))
        linarith
      have h_bound : |shift g| + |shift (w.verticalTranslate epsilon)| + |epsilon| ≤ delta + delta + epsilon := by
        have h3 : |shift g| ≤ delta := h_shift_amp g hg
        have h4 : |shift (w.verticalTranslate epsilon)| ≤ delta :=
          h_shift_amp (w.verticalTranslate epsilon) (hF_up_W' w hw)
        have h5 : |epsilon| = epsilon := abs_of_nonneg hepsilon_nonneg
        linarith
      have h_c_le : |c| ≤ epsilon + 2 * delta := by
        calc
          |c| ≤ |shift g| + |shift (w.verticalTranslate epsilon)| + |epsilon| := h_abs
          _ ≤ delta + delta + epsilon := h_bound
          _ = epsilon + 2 * delta := by ring
      have h_lt : epsilon + 2 * delta < t / (3 * K) :=
        shift_sum_lt_dist_sixth hK htang hdelta ht h_small epsilon
          hepsilon_nonneg hepsilon_bound (by linarith) (by linarith)
      have h6 : 2 * t ≤ c2Distance w g := h_sep w hw g hb
      have h7 : t / (3 * K) ≤ c2Distance w g / (6 * K) := by
        have hK_pos : 0 < K := by linarith
        have h_pos6 : 0 < 6 * K := by positivity
        have h : (2 * t) / (6 * K) ≤ c2Distance w g / (6 * K) := by
          apply div_le_div_of_nonneg_right h6
          positivity
        have h2 : t / (3 * K) = (2 * t) / (6 * K) := by
          field_simp [hK_pos.ne'] <;> ring
        rw [h2]
        exact h
      have hc : |c| < c2Distance w g / (6 * K) := by
        calc
          |c| ≤ epsilon + 2 * delta := h_c_le
          _ < t / (3 * K) := h_lt
          _ ≤ c2Distance w g / (6 * K) := h7
      have h_eq1 : w y₁ - g y₁ = c := by
        simp [verticalTranslate_apply] at eq1
        linarith [hc_def]
      have h_eq2 : w y₂ - g y₂ = c := by
        simp [verticalTranslate_apply] at eq2
        linarith [hc_def]
      have h_eq3 : w y₃ - g y₃ = c := by
        simp [verticalTranslate_apply] at eq3
        linarith [hc_def]
      exact two_zeros_level_via_dichotomy hK hD hfam hI_short hfw hfg_fam h_w_ne_g hc
        hy₁ hy₂ hy₃ h12 h23 h_eq1 h_eq2 h_eq3

    · -- f from B, g from W_up
      have hfb : f ∈ B := h_f_B
      rcases h_g_W with ⟨w, hw, rfl⟩
      have hff : f ∈ family := hB hfb
      have hfw : w ∈ family := hW hw
      have h_f_ne_w : f ≠ w := by
        have h_pos : 0 < c2Distance f w := by
          have h_sep' : 2 * t ≤ c2Distance w f := h_sep w hw f hfb
          have h_comm : c2Distance w f = c2Distance f w := by
            simp [c2Distance_eq_dist, dist_comm]
          linarith
        intro h
        rw [h] at h_pos
        simpa [c2Distance_eq_dist, dist_self] using h_pos
      set c : ℝ := shift (w.verticalTranslate epsilon) - shift f + epsilon with hc_def
      have h_abs : |c| ≤ |shift (w.verticalTranslate epsilon)| + |shift f| + |epsilon| := by
        rw [hc_def]
        have h_tri : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
          intro a b
          have h : dist a b ≤ dist a (0 : ℝ) + dist (0 : ℝ) b := dist_triangle a 0 b
          simpa [Real.dist_eq] using h
        have h1 : |shift (w.verticalTranslate epsilon) - shift f + epsilon| ≤
            |shift (w.verticalTranslate epsilon) - shift f| + |epsilon| := by
          have h := h_tri (shift (w.verticalTranslate epsilon) - shift f) (-epsilon)
          have h_eq : (shift (w.verticalTranslate epsilon) - shift f) - (-epsilon) =
              shift (w.verticalTranslate epsilon) - shift f + epsilon := by ring
          rw [h_eq] at h
          have h2 : |-epsilon| = |epsilon| := by rw [abs_neg]
          rw [h2] at h
          exact h
        have h2 := h_tri (shift (w.verticalTranslate epsilon)) (shift f)
        linarith
      have h_bound : |shift (w.verticalTranslate epsilon)| + |shift f| + |epsilon| ≤ delta + delta + epsilon := by
        have h3 : |shift (w.verticalTranslate epsilon)| ≤ delta :=
          h_shift_amp (w.verticalTranslate epsilon) (hF_up_W' w hw)
        have h4 : |shift f| ≤ delta := h_shift_amp f hf
        have h5 : |epsilon| = epsilon := abs_of_nonneg hepsilon_nonneg
        linarith
      have h_c_le : |c| ≤ epsilon + 2 * delta := by
        calc
          |c| ≤ |shift (w.verticalTranslate epsilon)| + |shift f| + |epsilon| := h_abs
          _ ≤ delta + delta + epsilon := h_bound
          _ = epsilon + 2 * delta := by ring
      have h_lt : epsilon + 2 * delta < t / (3 * K) :=
        shift_sum_lt_dist_sixth hK htang hdelta ht h_small epsilon
          hepsilon_nonneg hepsilon_bound (by linarith) (by linarith)
      have h6 : 2 * t ≤ c2Distance f w := by
        have h_sep' : 2 * t ≤ c2Distance w f := h_sep w hw f hfb
        have h_comm : c2Distance w f = c2Distance f w := by
          simp [c2Distance_eq_dist, dist_comm]
        linarith
      have h7 : t / (3 * K) ≤ c2Distance f w / (6 * K) := by
        have hK_pos : 0 < K := by linarith
        have h_pos6 : 0 < 6 * K := by positivity
        have h : (2 * t) / (6 * K) ≤ c2Distance f w / (6 * K) := by
          apply div_le_div_of_nonneg_right h6
          positivity
        have h2 : t / (3 * K) = (2 * t) / (6 * K) := by
          field_simp [hK_pos.ne'] <;> ring
        rw [h2]
        exact h
      have hc : |c| < c2Distance f w / (6 * K) := by
        calc
          |c| ≤ epsilon + 2 * delta := h_c_le
          _ < t / (3 * K) := h_lt
          _ ≤ c2Distance f w / (6 * K) := h7
      have h_eq1 : f y₁ - w y₁ = c := by
        simp [verticalTranslate_apply] at eq1
        linarith [hc_def]
      have h_eq2 : f y₂ - w y₂ = c := by
        simp [verticalTranslate_apply] at eq2
        linarith [hc_def]
      have h_eq3 : f y₃ - w y₃ = c := by
        simp [verticalTranslate_apply] at eq3
        linarith [hc_def]
      exact two_zeros_level_via_dichotomy hK hD hfam hI_short hff hfw h_f_ne_w hc
        hy₁ hy₂ hy₃ h12 h23 h_eq1 h_eq2 h_eq3

    · -- Both f, g from B
      have hfb1 : f ∈ B := h_f_B
      have hfb2 : g ∈ B := h_g_B
      have hff : f ∈ family := hB hfb1
      have hfg_fam : g ∈ family := hB hfb2
      set c : ℝ := shift g - shift f with hc_def
      have hc : |c| < c2Distance f g / (6 * K) := by
        have h := h_shift_bound f hf g hg hfg
        have h_abs : |c| = |shift f - shift g| := by
          rw [hc_def]
          have h3 : shift g - shift f = -(shift f - shift g) := by ring
          rw [h3, abs_neg]
        rw [h_abs]
        exact h
      have h_eq1 : f y₁ - g y₁ = c := by
        simp [verticalTranslate_apply] at eq1
        linarith [hc_def]
      have h_eq2 : f y₂ - g y₂ = c := by
        simp [verticalTranslate_apply] at eq2
        linarith [hc_def]
      have h_eq3 : f y₃ - g y₃ = c := by
        simp [verticalTranslate_apply] at eq3
        linarith [hc_def]
      exact two_zeros_level_via_dichotomy hK hD hfam hI_short hff hfg_fam hfg hc
        hy₁ hy₂ hy₃ h12 h23 h_eq1 h_eq2 h_eq3

  -- Transversality
  have h_transverse : ∀ (F' : C2Function), F' ∈ F_shifted →
      ∀ (G' : C2Function), G' ∈ F_shifted → F' ≠ G' →
        ∀ (y : UnitPoint), y ∈ I.carrier → F' y = G' y →
          F'.firstDeriv y ≠ G'.firstDeriv y := by
    intro F' hF' G' hG' hne y hy h_eq
    rcases Finset.mem_image.mp hF' with ⟨f, hf_F, rfl⟩
    rcases Finset.mem_image.mp hG' with ⟨g, hg_F, rfl⟩
    have hf : f ∈ F_up.carrier := by simpa [FiniteFunctionFamily.toFinset] using hf_F
    have hg : g ∈ F_up.carrier := by simpa [FiniteFunctionFamily.toFinset] using hg_F
    have hfg : f ≠ g := by
      intro h; rw [h] at hne; exact hne rfl
    exact perturbed_intersections_transverse h_no_tang hf hg hfg hy h_eq

  have h_image_eq : Finset.image (fun f : C2Function => f.reparam I) F_shifted =
      F_up.toFinset.image (fun f => (f.verticalTranslate (shift f)).reparam I) := by
    rw [Finset.image_image]
    <;> rfl
  rw [←h_image_eq]
  exact reparametrized_is_pseudo_circle hI_pos h_at_most_two h_transverse

end

end Kakeya.Cinematic

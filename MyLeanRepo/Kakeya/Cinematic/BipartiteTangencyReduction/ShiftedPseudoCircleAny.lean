import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ShiftedPseudoCircle

/-!
# Pseudo-circle property for arbitrary-sign pre-shift

This generalizes `shifted_bipartite_pseudo_circle` to allow a negative
pre-shift on the first color, as required by the downward lens direction.
Only the absolute value of the pre-shift enters the quantitative bound.
-/

namespace Kakeya.Cinematic

open Set C2Function

noncomputable section

local instance instDecidableEqC2FunctionShiftedPseudoCircleAny :
    DecidableEq C2Function := Classical.decEq _

lemma shifted_bipartite_pseudo_circle_any
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function} (hfam : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI_short : I.IsShort K)
    (hI_pos : 0 < I.length)
    {W B : Set C2Function} (hW : W ⊆ family) (hB : B ⊆ family)
    {delta t tangency epsilon_dir : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t) (htang : 5 ≤ tangency)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 2))
    (h_sep : ∀ w ∈ W, ∀ b ∈ B, 2 * t ≤ c2Distance w b)
    (hepsilon_abs : |epsilon_dir| ≤ 25 * tangency ^ 10 * delta)
    (F_up : FiniteFunctionFamily)
    (hF_up_W :
      ∀ f ∈ F_up.carrier,
        (∃ w ∈ W, f = w.verticalTranslate epsilon_dir) ∨ f ∈ B)
    (hF_up_W' :
      ∀ w ∈ W, w.verticalTranslate epsilon_dir ∈ F_up.carrier)
    {shift : C2Function → ℝ}
    (h_shift_amp : ∀ f ∈ F_up.carrier, |shift f| ≤ delta)
    (h_shift_bound :
      ∀ f ∈ F_up.carrier, ∀ g ∈ F_up.carrier, f ≠ g →
        |shift f - shift g| < c2Distance f g / (6 * K))
    (h_no_tang : F_up.HasNoExactTangenciesOn I shift) :
    IsGraphPseudoCircleFamily
      (F_up.toFinset.image
        (fun f => (f.verticalTranslate (shift f)).reparam I)) := by
  let epsilon_abs : ℝ := |epsilon_dir|
  have hepsilon_abs_nonneg : 0 ≤ epsilon_abs := abs_nonneg _
  have h_abs_sum : epsilon_abs + 2 * delta < t / (3 * K) :=
    shift_sum_lt_dist_sixth hK htang hdelta ht h_small epsilon_abs
      hepsilon_abs_nonneg hepsilon_abs (by linarith) (by linarith)
  let F_shifted : Finset C2Function :=
    F_up.toFinset.image (fun f => f.verticalTranslate (shift f))
  have h_vt_same_dist : ∀ (w1 w2 : C2Function),
      c2Distance
          (w1.verticalTranslate epsilon_dir)
          (w2.verticalTranslate epsilon_dir) =
        c2Distance w1 w2 := by
    intro w1 w2
    exact c2Distance_verticalTranslate_same w1 w2 epsilon_dir
  have h_at_most_two :
      ∀ (F' : C2Function), F' ∈ F_shifted →
        ∀ (G' : C2Function), G' ∈ F_shifted → F' ≠ G' →
          ∀ (y₁ y₂ y₃ : UnitPoint),
            y₁ ∈ I.carrier → y₂ ∈ I.carrier → y₃ ∈ I.carrier →
            (y₁ : ℝ) < (y₂ : ℝ) → (y₂ : ℝ) < (y₃ : ℝ) →
            F' y₁ = G' y₁ → F' y₂ = G' y₂ →
            F' y₃ = G' y₃ → False := by
    intro F' hF' G' hG' hne
    rcases Finset.mem_image.mp hF' with ⟨f, hf_F, rfl⟩
    rcases Finset.mem_image.mp hG' with ⟨g, hg_F, rfl⟩
    have hf : f ∈ F_up.carrier := by
      simpa [FiniteFunctionFamily.toFinset] using hf_F
    have hg : g ∈ F_up.carrier := by
      simpa [FiniteFunctionFamily.toFinset] using hg_F
    have hfg : f ≠ g := by
      intro h
      rw [h] at hne
      exact hne rfl
    intro y₁ y₂ y₃ hy₁ hy₂ hy₃ h12 h23 eq1 eq2 eq3
    rcases hF_up_W f hf with (h_f_W | h_f_B) <;>
      rcases hF_up_W g hg with (h_g_W | h_g_B)
    · rcases h_f_W with ⟨w1, hw1, rfl⟩
      rcases h_g_W with ⟨w2, hw2, rfl⟩
      have hfw1 : w1 ∈ family := hW hw1
      have hfw2 : w2 ∈ family := hW hw2
      have h_w1_ne_w2 : w1 ≠ w2 := by
        intro h
        apply hfg
        rw [h]
      set c : ℝ :=
        shift (w2.verticalTranslate epsilon_dir) -
          shift (w1.verticalTranslate epsilon_dir) with hc_def
      have hc : |c| < c2Distance w1 w2 / (6 * K) := by
        have h_dist_eq :
            c2Distance
                (w1.verticalTranslate epsilon_dir)
                (w2.verticalTranslate epsilon_dir) =
              c2Distance w1 w2 :=
          h_vt_same_dist w1 w2
        have h :=
          h_shift_bound
            (w1.verticalTranslate epsilon_dir) (hF_up_W' w1 hw1)
            (w2.verticalTranslate epsilon_dir) (hF_up_W' w2 hw2) hfg
        rw [h_dist_eq] at h
        have h_abs :
            |shift (w2.verticalTranslate epsilon_dir) -
                shift (w1.verticalTranslate epsilon_dir)| =
              |shift (w1.verticalTranslate epsilon_dir) -
                shift (w2.verticalTranslate epsilon_dir)| := by
          rw [show
            shift (w2.verticalTranslate epsilon_dir) -
                shift (w1.verticalTranslate epsilon_dir) =
              -(shift (w1.verticalTranslate epsilon_dir) -
                shift (w2.verticalTranslate epsilon_dir)) by ring]
          rw [abs_neg]
        rw [h_abs]
        simpa [hc_def] using h
      have h_eq1 : w1 y₁ - w2 y₁ = c := by
        simp [verticalTranslate_apply] at eq1
        linarith [hc_def]
      have h_eq2 : w1 y₂ - w2 y₂ = c := by
        simp [verticalTranslate_apply] at eq2
        linarith [hc_def]
      have h_eq3 : w1 y₃ - w2 y₃ = c := by
        simp [verticalTranslate_apply] at eq3
        linarith [hc_def]
      exact
        two_zeros_level_via_dichotomy hK hD hfam hI_short
          hfw1 hfw2 h_w1_ne_w2 hc hy₁ hy₂ hy₃ h12 h23
          h_eq1 h_eq2 h_eq3
    · rcases h_f_W with ⟨w, hw, rfl⟩
      have hb : g ∈ B := h_g_B
      have hfw : w ∈ family := hW hw
      have hfg_fam : g ∈ family := hB hb
      have h_w_ne_g : w ≠ g := by
        have h_pos : 0 < c2Distance w g := by
          linarith [h_sep w hw g hb]
        intro h
        rw [h] at h_pos
        simp [c2Distance_eq_dist] at h_pos
      set c : ℝ :=
        shift g - shift (w.verticalTranslate epsilon_dir) -
          epsilon_dir with hc_def
      have h_abs :
          |c| ≤
            |shift g| + |shift (w.verticalTranslate epsilon_dir)| +
              epsilon_abs := by
        rw [hc_def]
        have h_tri : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
          intro a b
          have h :
              dist a b ≤ dist a (0 : ℝ) + dist (0 : ℝ) b :=
            dist_triangle a 0 b
          simpa [Real.dist_eq] using h
        have h1 :=
          h_tri
            (shift g - shift (w.verticalTranslate epsilon_dir))
            epsilon_dir
        have h2 :=
          h_tri (shift g) (shift (w.verticalTranslate epsilon_dir))
        have h3 : |epsilon_dir| = epsilon_abs := rfl
        linarith
      have h_bound :
          |shift g| + |shift (w.verticalTranslate epsilon_dir)| +
              epsilon_abs ≤
            delta + delta + epsilon_abs := by
        have h3 : |shift g| ≤ delta := h_shift_amp g hg
        have h4 : |shift (w.verticalTranslate epsilon_dir)| ≤ delta :=
          h_shift_amp
            (w.verticalTranslate epsilon_dir) (hF_up_W' w hw)
        linarith
      have h_c_le : |c| ≤ epsilon_abs + 2 * delta := by
        calc
          |c| ≤
              |shift g| + |shift (w.verticalTranslate epsilon_dir)| +
                epsilon_abs := h_abs
          _ ≤ delta + delta + epsilon_abs := h_bound
          _ = epsilon_abs + 2 * delta := by ring
      have h6 : 2 * t ≤ c2Distance w g := h_sep w hw g hb
      have h7 : t / (3 * K) ≤ c2Distance w g / (6 * K) := by
        have hK_pos : 0 < K := by linarith
        have h :
            (2 * t) / (6 * K) ≤ c2Distance w g / (6 * K) :=
          div_le_div_of_nonneg_right h6 (by positivity)
        have h2 : t / (3 * K) = (2 * t) / (6 * K) := by
          field_simp [hK_pos.ne']
          ring
        rw [h2]
        exact h
      have hc : |c| < c2Distance w g / (6 * K) := by
        calc
          |c| ≤ epsilon_abs + 2 * delta := h_c_le
          _ < t / (3 * K) := h_abs_sum
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
      exact
        two_zeros_level_via_dichotomy hK hD hfam hI_short
          hfw hfg_fam h_w_ne_g hc hy₁ hy₂ hy₃ h12 h23
          h_eq1 h_eq2 h_eq3
    · have hfb : f ∈ B := h_f_B
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
        simp [c2Distance_eq_dist] at h_pos
      set c : ℝ :=
        shift (w.verticalTranslate epsilon_dir) - shift f +
          epsilon_dir with hc_def
      have h_abs :
          |c| ≤
            |shift (w.verticalTranslate epsilon_dir)| + |shift f| +
              epsilon_abs := by
        rw [hc_def]
        have h_tri : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
          intro a b
          have h :
              dist a b ≤ dist a (0 : ℝ) + dist (0 : ℝ) b :=
            dist_triangle a 0 b
          simpa [Real.dist_eq] using h
        have h1 :
            |shift (w.verticalTranslate epsilon_dir) - shift f +
                epsilon_dir| ≤
              |shift (w.verticalTranslate epsilon_dir) - shift f| +
                |epsilon_dir| := by
          have h :=
            h_tri
              (shift (w.verticalTranslate epsilon_dir) - shift f)
              (-epsilon_dir)
          have h_eq :
              (shift (w.verticalTranslate epsilon_dir) - shift f) -
                  (-epsilon_dir) =
                shift (w.verticalTranslate epsilon_dir) - shift f +
                  epsilon_dir := by
            ring
          rw [h_eq] at h
          rw [abs_neg] at h
          exact h
        have h2 :=
          h_tri (shift (w.verticalTranslate epsilon_dir)) (shift f)
        have h3 : |epsilon_dir| = epsilon_abs := rfl
        linarith
      have h_bound :
          |shift (w.verticalTranslate epsilon_dir)| + |shift f| +
              epsilon_abs ≤
            delta + delta + epsilon_abs := by
        have h3 : |shift (w.verticalTranslate epsilon_dir)| ≤ delta :=
          h_shift_amp
            (w.verticalTranslate epsilon_dir) (hF_up_W' w hw)
        have h4 : |shift f| ≤ delta := h_shift_amp f hf
        linarith
      have h_c_le : |c| ≤ epsilon_abs + 2 * delta := by
        calc
          |c| ≤
              |shift (w.verticalTranslate epsilon_dir)| + |shift f| +
                epsilon_abs := h_abs
          _ ≤ delta + delta + epsilon_abs := h_bound
          _ = epsilon_abs + 2 * delta := by ring
      have h6 : 2 * t ≤ c2Distance f w := by
        have h_sep' : 2 * t ≤ c2Distance w f := h_sep w hw f hfb
        simpa [c2Distance_eq_dist, dist_comm] using h_sep'
      have h7 : t / (3 * K) ≤ c2Distance f w / (6 * K) := by
        have hK_pos : 0 < K := by linarith
        have h :
            (2 * t) / (6 * K) ≤ c2Distance f w / (6 * K) :=
          div_le_div_of_nonneg_right h6 (by positivity)
        have h2 : t / (3 * K) = (2 * t) / (6 * K) := by
          field_simp [hK_pos.ne']
          ring
        rw [h2]
        exact h
      have hc : |c| < c2Distance f w / (6 * K) := by
        calc
          |c| ≤ epsilon_abs + 2 * delta := h_c_le
          _ < t / (3 * K) := h_abs_sum
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
      exact
        two_zeros_level_via_dichotomy hK hD hfam hI_short
          hff hfw h_f_ne_w hc hy₁ hy₂ hy₃ h12 h23
          h_eq1 h_eq2 h_eq3
    · have hfb1 : f ∈ B := h_f_B
      have hfb2 : g ∈ B := h_g_B
      have hff : f ∈ family := hB hfb1
      have hfg_fam : g ∈ family := hB hfb2
      set c : ℝ := shift g - shift f with hc_def
      have hc : |c| < c2Distance f g / (6 * K) := by
        have h := h_shift_bound f hf g hg hfg
        have h_abs : |c| = |shift f - shift g| := by
          rw [hc_def]
          have h3 : shift g - shift f = -(shift f - shift g) := by
            ring
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
      exact
        two_zeros_level_via_dichotomy hK hD hfam hI_short
          hff hfg_fam hfg hc hy₁ hy₂ hy₃ h12 h23
          h_eq1 h_eq2 h_eq3
  have h_transverse :
      ∀ (F' : C2Function), F' ∈ F_shifted →
        ∀ (G' : C2Function), G' ∈ F_shifted → F' ≠ G' →
          ∀ (y : UnitPoint), y ∈ I.carrier → F' y = G' y →
            F'.firstDeriv y ≠ G'.firstDeriv y := by
    intro F' hF' G' hG' hne y hy h_eq
    rcases Finset.mem_image.mp hF' with ⟨f, hf_F, rfl⟩
    rcases Finset.mem_image.mp hG' with ⟨g, hg_F, rfl⟩
    have hf : f ∈ F_up.carrier := by
      simpa [FiniteFunctionFamily.toFinset] using hf_F
    have hg : g ∈ F_up.carrier := by
      simpa [FiniteFunctionFamily.toFinset] using hg_F
    have hfg : f ≠ g := by
      intro h
      rw [h] at hne
      exact hne rfl
    exact
      perturbed_intersections_transverse
        h_no_tang hf hg hfg hy h_eq
  have h_image_eq :
      Finset.image (fun f : C2Function => f.reparam I) F_shifted =
        F_up.toFinset.image
          (fun f => (f.verticalTranslate (shift f)).reparam I) := by
    rw [Finset.image_image]
    rfl
  rw [← h_image_eq]
  exact
    reparametrized_is_pseudo_circle
      hI_pos h_at_most_two h_transverse

end

end Kakeya.Cinematic

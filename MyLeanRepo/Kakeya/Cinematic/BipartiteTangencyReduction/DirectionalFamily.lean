import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerturbationPreservation
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.NoTangencyTransfer
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ShiftBound
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ShiftedPseudoCircle

/-!
# Directional shifted family construction

Construct a directional shifted family F_dir from W and B,
define the perturbation shift on it, and transfer no-tangency and shift-bound
certificates from the original union family F.

The direction is encoded by a signed `epsilon_dir`. For upward, `epsilon_dir > 0`;
for downward, `epsilon_dir < 0`. Only `|epsilon_dir|` enters the quantitative bounds.
-/

noncomputable section

namespace Kakeya.Cinematic

open Set

/--
Construct the directional shifted family and transfer certificates.

Given W, B, shift0, signed epsilon_dir with no-tangencies on F = W ∪ B under
the directional shift, produce F_dir = {w.verticalTranslate epsilon_dir | w ∈ W} ∪ B
and shift_dir' with no-tangencies and shift bounds.
-/
lemma directional_family
    {K : ℝ} (hK : 1 ≤ K)
    {I : ParameterInterval}
    (W B F : FiniteFunctionFamily)
    (hF_eq : F.carrier = W.carrier ∪ B.carrier)
    (shift0 : C2Function → ℝ)
    {epsilon_dir delta t tangency : ℝ}
    [DecidableEq C2Function]
    (hdelta : 0 < delta) (ht : 0 < t) (htang : 5 ≤ tangency)
    (h_small : tangency^50 * delta ≤ t / (1000 * K^2))
    (h_sep : W.AreSeparated B (2 * t))
    (hepsilon_abs : |epsilon_dir| ≤ 25 * tangency^10 * delta)
    (h_amp : ∀ f ∈ F.carrier, |shift0 f| ≤ delta)
    (h_pairwise : ∀ f ∈ F.carrier, ∀ g ∈ F.carrier, f ≠ g →
      |shift0 f - shift0 g| < c2Distance f g / (6 * K))
    (h_no_tang_dir : F.HasNoExactTangenciesOn I
      (fun f => if f ∈ W.toFinset then epsilon_dir + shift0 f else shift0 f)) :
    ∃ (F_dir : FiniteFunctionFamily) (shift_dir' : C2Function → ℝ),
      (∀ f ∈ F_dir.carrier,
        (∃ w ∈ W.carrier, f = w.verticalTranslate epsilon_dir) ∨ f ∈ B.carrier) ∧
      (∀ w ∈ W.carrier, w.verticalTranslate epsilon_dir ∈ F_dir.carrier) ∧
      (∀ b ∈ B.carrier, b ∈ F_dir.carrier) ∧
      (∀ f ∈ F_dir.carrier, |shift_dir' f| ≤ delta) ∧
      (∀ f ∈ F_dir.carrier, ∀ g ∈ F_dir.carrier, f ≠ g →
        |shift_dir' f - shift_dir' g| < c2Distance f g / (6 * K)) ∧
      (∀ w ∈ W.carrier, shift_dir' (w.verticalTranslate epsilon_dir) = shift0 w) ∧
      (∀ b ∈ B.carrier, shift_dir' b = shift0 b) ∧
      F_dir.HasNoExactTangenciesOn I shift_dir' := by
  let eps_abs : ℝ := |epsilon_dir|
  have heps_abs_nonneg : 0 ≤ eps_abs := abs_nonneg _
  have h_eps_bound : eps_abs ≤ 25 * tangency^10 * delta := hepsilon_abs

  have h_sum : eps_abs + 2 * delta < t / (3 * K) :=
    shift_sum_lt_dist_sixth hK htang hdelta ht h_small eps_abs
      heps_abs_nonneg h_eps_bound (by linarith) (by linarith)
  have h_eps_lt_t : eps_abs < t := by
    have h2 : eps_abs < t / (3 * K) := by linarith
    have h3 : t / (3 * K) < t := by
      have hK_pos : 0 < K := by linarith
      have h4 : 1 < 3 * K := by linarith
      exact (div_lt_self ht h4)
    linarith

  let W_dir : Set C2Function := W.carrier.image (fun w => w.verticalTranslate epsilon_dir)
  have hW_dir_finite : W_dir.Finite := W.finite.image _
  let F_dir : FiniteFunctionFamily :=
    { carrier := W_dir ∪ B.carrier
      finite := hW_dir_finite.union B.finite }

  have h_W_B_disjoint : ∀ w ∈ W.carrier, w ∉ B.carrier := by
    intro w hw hb
    have h : 2 * t ≤ c2Distance w w := h_sep hw hb
    have h0 : c2Distance w w = 0 := by
      rw [c2Distance_eq_dist, dist_self]
    rw [h0] at h
    linarith

  have h_disjoint : ∀ w ∈ W.carrier, w.verticalTranslate epsilon_dir ∉ B.carrier := by
    intro w hw hb
    have h_sep' : 2 * t ≤ c2Distance w (w.verticalTranslate epsilon_dir) := h_sep hw hb
    have h_dist : c2Distance w (w.verticalTranslate epsilon_dir) = eps_abs :=
      c2Distance_verticalTranslate_self w epsilon_dir
    rw [h_dist] at h_sep'
    linarith

  let orig : C2Function → C2Function := fun f =>
    if f ∈ B.toFinset then f else f.verticalTranslate (-epsilon_dir)
  let shift_dir' : C2Function → ℝ := fun f => shift0 (orig f)

  have hB_mem : ∀ b ∈ B.carrier, b ∈ B.toFinset := by
    intro b hb
    exact B.finite.mem_toFinset.mpr hb
  have hshift_not_B : ∀ w ∈ W.carrier, w.verticalTranslate epsilon_dir ∉ B.toFinset := by
    intro w hw hmem
    exact h_disjoint w hw (B.finite.mem_toFinset.mp hmem)
  have vt_zero : ∀ (f : C2Function), f.verticalTranslate (0 : ℝ) = f := by
    intro f
    apply C2Function.toJet_injective
    dsimp only [C2Function.toJet]
    apply Prod.ext
    · ext x
      change (f.verticalTranslate (0 : ℝ)) x = f x
      simp [verticalTranslate_apply]
    · apply Prod.ext <;> rfl
  have horigW : ∀ w ∈ W.carrier, orig (w.verticalTranslate epsilon_dir) = w := by
    intro w hw
    have h_notin : w.verticalTranslate epsilon_dir ∉ B.toFinset := hshift_not_B w hw
    have h1 : orig (w.verticalTranslate epsilon_dir) =
        (w.verticalTranslate epsilon_dir).verticalTranslate (-epsilon_dir) := by
      dsimp only [orig]
      rw [if_neg h_notin]
    rw [h1]
    have h2 : (w.verticalTranslate epsilon_dir).verticalTranslate (-epsilon_dir) = w := by
      rw [verticalTranslate_compose]
      have h3 : epsilon_dir + (-epsilon_dir) = (0 : ℝ) := by ring
      rw [h3]
      exact vt_zero w
    exact h2
  have horigB : ∀ b ∈ B.carrier, orig b = b := by
    intro b hb
    simp [orig, hB_mem b hb]

  have hF_dir_W : ∀ f ∈ F_dir.carrier,
      (∃ w ∈ W.carrier, f = w.verticalTranslate epsilon_dir) ∨ f ∈ B.carrier := by
    intro f hf
    have h : f ∈ W_dir ∪ B.carrier := hf
    rcases h with (h | h)
    · left
      have h' : ∃ w ∈ W.carrier, w.verticalTranslate epsilon_dir = f := by
        simpa [W_dir, Set.mem_image] using h
      rcases h' with ⟨w, hw, h_eq⟩
      exact ⟨w, hw, h_eq.symm⟩
    · right; exact h
  have hF_dir_W' : ∀ w ∈ W.carrier, w.verticalTranslate epsilon_dir ∈ F_dir.carrier := by
    intro w hw
    have h : w.verticalTranslate epsilon_dir ∈ W_dir := by
      refine ⟨w, hw, rfl⟩
    exact Or.inl h
  have hF_dir_B : ∀ b ∈ B.carrier, b ∈ F_dir.carrier := by
    intro b hb
    exact Or.inr hb

  have horig_mem : ∀ f ∈ F_dir.carrier, orig f ∈ F.carrier := by
    intro f hf
    rcases hF_dir_W f hf with ⟨w, hw, rfl⟩ | hb
    · rw [horigW w hw, hF_eq]; exact Or.inl hw
    · rw [horigB f hb, hF_eq]; exact Or.inr hb

  have h_amp' : ∀ f ∈ F_dir.carrier, |shift_dir' f| ≤ delta := by
    intro f hf
    exact h_amp (orig f) (horig_mem f hf)

  have h_pairwise' : ∀ f ∈ F_dir.carrier, ∀ g ∈ F_dir.carrier, f ≠ g →
      |shift_dir' f - shift_dir' g| < c2Distance f g / (6 * K) := by
    intro f hf g hg hfg
    rcases hF_dir_W f hf with ⟨w, hw, rfl⟩ | hfB
    · rcases hF_dir_W g hg with ⟨w', hw', rfl⟩ | hgB
      · have hww' : w ≠ w' := by
          intro h; rw [h] at hfg; exact hfg rfl
        have h_dist : c2Distance (w.verticalTranslate epsilon_dir) (w'.verticalTranslate epsilon_dir) =
            c2Distance w w' := c2Distance_verticalTranslate_same w w' epsilon_dir
        have h1 : shift_dir' (w.verticalTranslate epsilon_dir) = shift0 w := by
          simp [shift_dir', horigW w hw]
        have h2 : shift_dir' (w'.verticalTranslate epsilon_dir) = shift0 w' := by
          simp [shift_dir', horigW w' hw']
        rw [h1, h2, h_dist]
        exact h_pairwise w (by rw [hF_eq]; exact Or.inl hw)
          w' (by rw [hF_eq]; exact Or.inl hw') hww'
      · have h_cross1 : |shift_dir' (w.verticalTranslate epsilon_dir) - shift_dir' g| ≤ 2 * delta := by
          have h1 : shift_dir' (w.verticalTranslate epsilon_dir) = shift0 w := by
            simp [shift_dir', horigW w hw]
          have h2 : shift_dir' g = shift0 g := by
            simp [shift_dir', horigB g hgB]
          rw [h1, h2]
          calc
            |shift0 w - shift0 g| ≤ |shift0 w| + |shift0 g| := by exact abs_sub _ _
            _ ≤ delta + delta := by gcongr <;> exact h_amp _ (by rw [hF_eq] <;> tauto)
            _ = 2 * delta := by ring
        have h_g0 : g.verticalTranslate (0 : ℝ) = g := vt_zero g
        have h_lower : c2Distance (w.verticalTranslate epsilon_dir) g ≥
            c2Distance w g - eps_abs := by
          have h := c2Distance_verticalTranslate_lower w g epsilon_dir (0 : ℝ)
          have h4 : |epsilon_dir - (0 : ℝ)| = eps_abs := by simp [eps_abs]
          rw [h_g0, h4] at h
          linarith
        have h_sep2 : 2 * t ≤ c2Distance w g := h_sep hw hgB
        have h_main : 2 * delta < c2Distance (w.verticalTranslate epsilon_dir) g / (6 * K) := by
          have h1 : c2Distance (w.verticalTranslate epsilon_dir) g ≥ 2 * t - eps_abs := by
            linarith
          have h2 : 2 * delta < t / (3 * K) - eps_abs := by linarith
          have h3 : t / (3 * K) - eps_abs ≤ (2 * t - eps_abs) / (6 * K) := by
            have hK_pos : 0 < K := by linarith
            field_simp [hK_pos.ne'] <;> ring_nf <;> nlinarith
          calc
            2 * delta < t / (3 * K) - eps_abs := h2
            _ ≤ (2 * t - eps_abs) / (6 * K) := h3
            _ ≤ c2Distance (w.verticalTranslate epsilon_dir) g / (6 * K) := by gcongr
        exact lt_of_le_of_lt h_cross1 h_main
    · rcases hF_dir_W g hg with ⟨w, hw, rfl⟩ | hgB
      · have h_cross2 : |shift_dir' f - shift_dir' (w.verticalTranslate epsilon_dir)| ≤ 2 * delta := by
          have h1 : shift_dir' f = shift0 f := by
            simp [shift_dir', horigB f hfB]
          have h2 : shift_dir' (w.verticalTranslate epsilon_dir) = shift0 w := by
            simp [shift_dir', horigW w hw]
          rw [h1, h2]
          calc
            |shift0 f - shift0 w| ≤ |shift0 f| + |shift0 w| := by exact abs_sub _ _
            _ ≤ delta + delta := by gcongr <;> exact h_amp _ (by rw [hF_eq] <;> tauto)
            _ = 2 * delta := by ring
        have h_f0 : f.verticalTranslate (0 : ℝ) = f := vt_zero f
        have h_lower : c2Distance f (w.verticalTranslate epsilon_dir) ≥
            c2Distance f w - eps_abs := by
          have h := c2Distance_verticalTranslate_lower f w (0 : ℝ) epsilon_dir
          have h4 : |(0 : ℝ) - epsilon_dir| = eps_abs := by simp [eps_abs]
          rw [h_f0, h4] at h
          linarith
        have h_sep2 : 2 * t ≤ c2Distance w f := h_sep hw hfB
        have h_sym : c2Distance f w = c2Distance w f := by
          rw [c2Distance_eq_dist, c2Distance_eq_dist, dist_comm]
        have h_main : 2 * delta < c2Distance f (w.verticalTranslate epsilon_dir) / (6 * K) := by
          have h4 : c2Distance f w ≥ 2 * t := by
            rw [h_sym]
            exact h_sep2
          have h1 : c2Distance f (w.verticalTranslate epsilon_dir) ≥ 2 * t - eps_abs := by
            linarith [h_lower, h4]
          have h2 : 2 * delta < t / (3 * K) - eps_abs := by linarith
          have h3 : t / (3 * K) - eps_abs ≤ (2 * t - eps_abs) / (6 * K) := by
            have hK_pos : 0 < K := by linarith
            field_simp [hK_pos.ne'] <;> ring_nf <;> nlinarith
          calc
            2 * delta < t / (3 * K) - eps_abs := h2
            _ ≤ (2 * t - eps_abs) / (6 * K) := h3
            _ ≤ c2Distance f (w.verticalTranslate epsilon_dir) / (6 * K) := by gcongr
        exact lt_of_le_of_lt h_cross2 h_main
      · have hbb' : f ≠ g := hfg
        have h1 : shift_dir' f = shift0 f := by
          simp [shift_dir', horigB f hfB]
        have h2 : shift_dir' g = shift0 g := by
          simp [shift_dir', horigB g hgB]
        rw [h1, h2]
        exact h_pairwise f (by rw [hF_eq]; exact Or.inr hfB)
          g (by rw [hF_eq]; exact Or.inr hgB) hbb'

  let shiftDir : C2Function → ℝ := fun f =>
    if f ∈ W.toFinset then epsilon_dir + shift0 f else shift0 f
  have h_shiftDir_W : ∀ w ∈ W.carrier, shiftDir w = epsilon_dir + shift0 w := by
    intro w hw
    have h : w ∈ W.toFinset := W.finite.mem_toFinset.mpr hw
    simp [shiftDir, h]
  have h_shiftDir_B : ∀ b ∈ B.carrier, shiftDir b = shift0 b := by
    intro b hb
    have h : b ∉ W.toFinset := by
      intro hmem
      exact h_W_B_disjoint b (W.finite.mem_toFinset.mp hmem) hb
    simp [shiftDir, h]
  have h_shift'_W : ∀ w ∈ W.carrier,
      shift_dir' (w.verticalTranslate epsilon_dir) = shift0 w := by
    intro w hw
    simp [shift_dir', horigW w hw]
  have h_shift'_B : ∀ b ∈ B.carrier, shift_dir' b = shift0 b := by
    intro b hb
    simp [shift_dir', horigB b hb]

  have h_no_tang' : F_dir.HasNoExactTangenciesOn I shift_dir' :=
    no_tangencies_transfer
      (hF_union := hF_eq)
      (h_W_B_disjoint := h_W_B_disjoint)
      (h_disjoint := h_disjoint)
      (hF_W := hF_dir_W)
      (h_shift'_W := h_shift'_W)
      (h_shift'_B := h_shift'_B)
      (h_shift_W := h_shiftDir_W)
      (h_shift_B := h_shiftDir_B)
      (h_no_tang := h_no_tang_dir)

  exact ⟨F_dir, shift_dir', hF_dir_W, hF_dir_W', hF_dir_B, h_amp', h_pairwise', h_shift'_W, h_shift'_B, h_no_tang'⟩

end Kakeya.Cinematic

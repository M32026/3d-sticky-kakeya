import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory CompactlySupported ZeroAtInfty

namespace Geometry.Perimeter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]

/-- Inclusion from `C_c(X, ℝ)` to `C₀(X, ℝ)`. -/
def Cc.toC₀ (f : C_c(X, ℝ)) : C₀(X, ℝ) :=
  { toFun := f
    continuous_toFun := f.continuous
    zero_at_infty' := f.hasCompactSupport.is_zero_at_infty }

section Helpers

lemma real_sSup_image2_add {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hbA : BddAbove A) (hbB : BddAbove B) :
    sSup (image2 (· + ·) A B) = sSup A + sSup B := by
  have h1 : ∀ x ∈ image2 (· + ·) A B, x ≤ sSup A + sSup B := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    have ha' : a ≤ sSup A := le_csSup hbA ha
    have hb' : b ≤ sSup B := le_csSup hbB hb
    exact add_le_add ha' hb'
  have h2 : sSup (image2 (· + ·) A B) ≤ sSup A + sSup B :=
    csSup_le (hA.image2 hB) h1
  have h3 : sSup A + sSup B ≤ sSup (image2 (· + ·) A B) := by
    by_contra h
    have h4 : sSup (image2 (· + ·) A B) < sSup A + sSup B := by linarith
    set ε : ℝ := (sSup A + sSup B - sSup (image2 (· + ·) A B)) / 2 with hε
    have hε_pos : 0 < ε := by linarith
    have h5 : ∃ a, a ∈ A ∧ sSup A - ε < a := by
      by_contra h7; push Not at h7
      have h8 : sSup A ≤ sSup A - ε := csSup_le hA h7; linarith
    have h6 : ∃ b, b ∈ B ∧ sSup B - ε < b := by
      by_contra h8; push Not at h8
      have h9 : sSup B ≤ sSup B - ε := csSup_le hB h8; linarith
    rcases h5 with ⟨a, ha, ha'⟩
    rcases h6 with ⟨b, hb, hb'⟩
    have h10 : a + b ∈ image2 (· + ·) A B := ⟨a, ha, b, hb, rfl⟩
    have hBdd : BddAbove (image2 (· + ·) A B) := ⟨sSup A + sSup B, h1⟩
    have h11 : a + b ≤ sSup (image2 (· + ·) A B) := le_csSup hBdd h10
    have h12 : sSup A + sSup B - sSup (image2 (· + ·) A B) = 2 * ε := by
      linarith [hε]
    linarith
  exact le_antisymm h2 h3

lemma real_sSup_const_mul {A : Set ℝ} (hA : A.Nonempty) (hbA : BddAbove A) {c : ℝ} (hc : 0 ≤ c) :
    sSup ((fun x => c * x) '' A) = c * sSup A := by
  by_cases hc0 : c = 0
  · simp [hc0, hA]
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have h1 : ∀ y ∈ (fun x => c * x) '' A, y ≤ c * sSup A := by
      rintro y ⟨x, hx, rfl⟩
      exact mul_le_mul_of_nonneg_left (le_csSup hbA hx) hc
    have h2 : sSup ((fun x => c * x) '' A) ≤ c * sSup A :=
      csSup_le (hA.image _) h1
    have h3 : c * sSup A ≤ sSup ((fun x => c * x) '' A) := by
      by_contra h
      have h4 : sSup ((fun x => c * x) '' A) < c * sSup A := by linarith
      set ε : ℝ := (c * sSup A - sSup ((fun x => c * x) '' A)) / 2 with hε
      have hε_pos : 0 < ε := by linarith
      have h5 : ∃ a, a ∈ A ∧ sSup A - ε / c < a := by
        by_contra h6; push Not at h6
        have h7 : sSup A ≤ sSup A - ε / c := csSup_le hA h6
        have h8 : 0 < ε / c := div_pos hε_pos hc_pos
        linarith
      rcases h5 with ⟨a, ha, ha'⟩
      have h8 : c * a ∈ (fun x => c * x) '' A := ⟨a, ha, rfl⟩
      have hBdd : BddAbove ((fun x => c * x) '' A) := ⟨c * sSup A, h1⟩
      have h9 : c * a ≤ sSup ((fun x => c * x) '' A) := le_csSup hBdd h8
      have h10 : c * (sSup A - ε / c) < c * a := mul_lt_mul_of_pos_left ha' hc_pos
      have h11 : c * (sSup A - ε / c) = c * sSup A - ε := by
        field_simp [hc_pos.ne'] <;> ring
      linarith
    exact le_antisymm h2 h3

end Helpers

section PreJordan

def admissibleSet (f : C_c(X, ℝ)) : Set (C_c(X, ℝ)) := {g | 0 ≤ g ∧ g ≤ f}

lemma norm_mono_aux {f g : C_c(X, ℝ)} (hf : 0 ≤ f) (h1 : 0 ≤ g) (h2 : g ≤ f) :
    ‖Cc.toC₀ g‖ ≤ ‖Cc.toC₀ f‖ := by
  have h : ∀ (x : X), |g x| ≤ ‖Cc.toC₀ f‖ := by
    intro x
    have h3 : 0 ≤ g x := h1 x
    have h4 : g x ≤ f x := h2 x
    have h5 : |g x| ≤ |f x| := by
      rw [abs_of_nonneg h3, abs_of_nonneg (hf x)] <;> exact h4
    have h6 : |(Cc.toC₀ f) x| ≤ ‖Cc.toC₀ f‖ := by
      simpa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
        BoundedContinuousFunction.norm_coe_le_norm (Cc.toC₀ f).toBCF x
    have h7 : |f x| = |(Cc.toC₀ f) x| := by rfl
    exact h5.trans (h7 ▸ h6)
  have h7 : ‖(Cc.toC₀ g).toBCF‖ ≤ ‖Cc.toC₀ f‖ := by
    rw [BoundedContinuousFunction.norm_le (show 0 ≤ ‖Cc.toC₀ f‖ from by positivity)]
    exact h
  simpa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using h7

end PreJordan

section JordanDecomposition

lemma bddAbove_admissible
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)
    (f : C_c(X, ℝ)) (hf : 0 ≤ f) :
    BddAbove (L '' admissibleSet f) := by
  refine ⟨C * ‖Cc.toC₀ f‖, ?_⟩
  rintro y ⟨g, hg, rfl⟩
  have h_norm : ‖Cc.toC₀ g‖ ≤ ‖Cc.toC₀ f‖ := norm_mono_aux hf hg.1 hg.2
  have h4 : |L g| ≤ C * ‖Cc.toC₀ g‖ := hL g
  have h5 : L g ≤ |L g| := le_abs_self (L g)
  calc L g ≤ |L g| := h5
    _ ≤ C * ‖Cc.toC₀ g‖ := h4
    _ ≤ C * ‖Cc.toC₀ f‖ := by
      exact mul_le_mul_of_nonneg_left h_norm hC

lemma nonempty_admissible
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ)) (hf : 0 ≤ f) :
    (L '' admissibleSet f).Nonempty := by
  have h0 : (0 : C_c(X, ℝ)) ∈ admissibleSet f := by
    simp [admissibleSet, hf]
  exact ⟨L 0, 0, h0, rfl⟩

/-- The positive part of L evaluated on a nonnegative function. -/
noncomputable def posPartRaw
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ)) : ℝ :=
  sSup (L '' admissibleSet f)

lemma posPartRaw_nonneg
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ posPartRaw L f := by
  have hL0 : L (0 : C_c(X, ℝ)) = 0 := by simp
  have h1 : (0 : ℝ) ∈ L '' admissibleSet f := by
    rw [← hL0]
    have h : (0 : C_c(X, ℝ)) ∈ admissibleSet f := by simp [admissibleSet, hf]
    exact ⟨0, h, rfl⟩
  exact le_csSup (bddAbove_admissible L C hC hL f hf) h1

lemma posPartRaw_bdd
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    posPartRaw L f ≤ C * ‖Cc.toC₀ f‖ := by
  have h : ∀ (y : ℝ), y ∈ L '' admissibleSet f → y ≤ C * ‖Cc.toC₀ f‖ := by
    rintro y ⟨g, hg, rfl⟩
    have h_norm : ‖Cc.toC₀ g‖ ≤ ‖Cc.toC₀ f‖ := norm_mono_aux hf hg.1 hg.2
    have h4 : |L g| ≤ C * ‖Cc.toC₀ g‖ := hL g
    have h5 : L g ≤ |L g| := le_abs_self (L g)
    calc L g ≤ |L g| := h5
      _ ≤ C * ‖Cc.toC₀ g‖ := h4
      _ ≤ C * ‖Cc.toC₀ f‖ := by exact mul_le_mul_of_nonneg_left h_norm hC
  exact csSup_le (nonempty_admissible L f hf) h

lemma L_le_posPartRaw
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) : L f ≤ posPartRaw L f := by
  have hf' : f ∈ admissibleSet f := by
    simp [admissibleSet, hf]
  have h : L f ∈ L '' admissibleSet f := ⟨f, hf', rfl⟩
  exact le_csSup (bddAbove_admissible L C hC hL f hf) h

lemma posPartRaw_smul
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) {c : ℝ} (hc : 0 ≤ c) :
    posPartRaw L (c • f) = c * posPartRaw L f := by
  by_cases hc0 : c = 0
  · have h_eq : c • f = (0 : C_c(X, ℝ)) := by
      ext x; simp [hc0]
    rw [h_eq]
    have h_set : admissibleSet (0 : C_c(X, ℝ)) = {(0 : C_c(X, ℝ))} := by
      apply Set.ext
      intro g
      simp only [admissibleSet, Set.mem_singleton_iff]
      constructor
      · intro h
        have h1 : 0 ≤ g := h.1
        have h2 : g ≤ 0 := h.2
        have h3 : g = 0 := by
          ext x; linarith [h1 x, h2 x]
        exact h3
      · intro h
        rw [h]
        <;> simp
    have h_image : L '' {(0 : C_c(X, ℝ))} = {(0 : ℝ)} := by
      simp
    have h_main : posPartRaw L (0 : C_c(X, ℝ)) = 0 := by
      rw [posPartRaw, h_set, h_image]
      simp
    rw [h_main, hc0]
    <;> ring
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have h1 : 0 ≤ c • f := by
      intro x; exact mul_nonneg hc (hf x)
    have h_set_eq : (L '' admissibleSet (c • f)) =
        (fun x : ℝ => c * x) '' (L '' admissibleSet f) := by
      ext y
      simp only [Set.mem_image, admissibleSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
        let h : C_c(X, ℝ) := c⁻¹ • g
        have h_h1 : 0 ≤ h := by
          intro x; exact mul_nonneg (by positivity) (hg1 x)
        have h_h2 : h ≤ f := by
          intro x
          have h5 : g x ≤ c * f x := hg2 x
          have h10 : h x = g x / c := by
            simp [h] <;> field_simp [hc_pos.ne'] <;> ring
          rw [h10]
          have h8 : g x / c ≤ (c * f x) / c :=
            div_le_div_of_nonneg_right h5 (by linarith)
          have h9 : (c * f x) / c = f x := by
            field_simp [hc_pos.ne'] <;> ring
          rw [h9] at h8
          exact h8
        refine ⟨L h, ⟨h, ⟨h_h1, h_h2⟩, rfl⟩, ?_⟩
        simp [h, L.map_smul] <;> field_simp [hc_pos.ne'] <;> ring
      · rintro ⟨z, ⟨h, ⟨hh1, hh2⟩, rfl⟩, rfl⟩
        let g : C_c(X, ℝ) := c • h
        have hg1 : 0 ≤ g := by
          intro x; exact mul_nonneg hc (hh1 x)
        have hg2 : g ≤ c • f := by
          intro x; exact mul_le_mul_of_nonneg_left (hh2 x) hc
        exact ⟨g, ⟨hg1, hg2⟩, by simp [g, L.map_smul]⟩
    rw [posPartRaw, h_set_eq]
    exact real_sSup_const_mul (nonempty_admissible L f hf)
      (bddAbove_admissible L C hC hL f hf) hc

lemma posPartRaw_add
    (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)
    {f₁ f₂ : C_c(X, ℝ)} (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) :
    posPartRaw L (f₁ + f₂) = posPartRaw L f₁ + posPartRaw L f₂ := by
  let S₁ := L '' admissibleSet f₁
  let S₂ := L '' admissibleSet f₂
  let S := L '' admissibleSet (f₁ + f₂)
  have hS1_nonempty : S₁.Nonempty := nonempty_admissible L f₁ hf₁
  have hS2_nonempty : S₂.Nonempty := nonempty_admissible L f₂ hf₂
  have hb1 : BddAbove S₁ := bddAbove_admissible L C hC hL f₁ hf₁
  have hb2 : BddAbove S₂ := bddAbove_admissible L C hC hL f₂ hf₂
  have h_main1 : S ⊆ image2 (· + ·) S₁ S₂ := by
    rintro y ⟨g, ⟨hg1, hg2⟩, rfl⟩
    let g₁ : C_c(X, ℝ) := g ⊓ f₁
    let g₂ : C_c(X, ℝ) := g - g₁
    have hg1_nonneg : 0 ≤ g₁ := by
      intro x; exact le_inf (hg1 x) (hf₁ x)
    have hg1_le : g₁ ≤ f₁ := by
      intro x; exact inf_le_right
    have hg2_nonneg : 0 ≤ g₂ := by
      intro x
      have h : g₁ x ≤ g x := inf_le_left
      simpa [g₂, sub_nonneg] using h
    have hg2_le : g₂ ≤ f₂ := by
      intro x
      have h5 : g x ≤ f₁ x + f₂ x := hg2 x
      have h6 : g₁ x = min (g x) (f₁ x) := rfl
      have h_goal : g x - g₁ x ≤ f₂ x := by
        rw [h6]
        by_cases h7 : g x ≤ f₁ x
        · rw [min_eq_left h7]
          have h_nonneg : 0 ≤ f₂ x := hf₂ x
          linarith
        · rw [min_eq_right (by linarith)] <;> linarith
      have h_g2_def : g₂ x = g x - g₁ x := by
        simp [g₂] <;> ring
      rw [h_g2_def]
      exact h_goal
    have h_sum : g₁ + g₂ = g := by
      ext x
      simp [g₂] <;> ring
    have hL_sum : L g = L g₁ + L g₂ := by
      rw [← h_sum, L.map_add]
    exact ⟨L g₁, ⟨g₁, ⟨hg1_nonneg, hg1_le⟩, rfl⟩, L g₂, ⟨g₂, ⟨hg2_nonneg, hg2_le⟩, rfl⟩, hL_sum.symm⟩
  have h_main2 : image2 (· + ·) S₁ S₂ ⊆ S := by
    rintro y ⟨z1, ⟨g1, hg1, rfl⟩, z2, ⟨g2, hg2, rfl⟩, rfl⟩
    let g : C_c(X, ℝ) := g1 + g2
    have hg_nonneg : 0 ≤ g := by
      intro x; exact add_nonneg (hg1.1 x) (hg2.1 x)
    have hg_le : g ≤ f₁ + f₂ := by
      intro x; exact add_le_add (hg1.2 x) (hg2.2 x)
    have h : L g ∈ S := ⟨g, ⟨hg_nonneg, hg_le⟩, rfl⟩
    have hLg : L g = L g1 + L g2 := by rw [L.map_add]
    rw [hLg] at h
    exact h
  have h_eq : S = image2 (· + ·) S₁ S₂ := Set.Subset.antisymm h_main1 h_main2
  have h1 : posPartRaw L (f₁ + f₂) = sSup S := by rfl
  have h2 : posPartRaw L f₁ = sSup S₁ := by rfl
  have h3 : posPartRaw L f₂ = sSup S₂ := by rfl
  rw [h1, h2, h3, h_eq]
  exact real_sSup_image2_add hS1_nonempty hS2_nonempty hb1 hb2

end JordanDecomposition

section Extension

/-- Pointwise identity for positive/negative parts. -/
lemma real_pos_neg_add_identity (a b : ℝ) :
    max (a + b) 0 + max (-a) 0 + max (-b) 0 =
    max (-(a + b)) 0 + max a 0 + max b 0 := by
  simp [max_def] <;> split_ifs <;> linarith

/-- Positive part of f: f⁺ = f ⊔ 0. -/
def posPart (f : C_c(X, ℝ)) : C_c(X, ℝ) := f ⊔ 0

/-- Negative part of f: f⁻ = (-f) ⊔ 0. -/
def negPart (f : C_c(X, ℝ)) : C_c(X, ℝ) := (-f) ⊔ 0

lemma posPart_nonneg (f : C_c(X, ℝ)) : 0 ≤ posPart f := by
  intro x; exact le_max_right _ _

lemma negPart_nonneg (f : C_c(X, ℝ)) : 0 ≤ negPart f := by
  intro x; exact le_max_right _ _

lemma posPart_negPart_identity (f : C_c(X, ℝ)) : f = posPart f - negPart f := by
  ext x
  simp [posPart, negPart, max_def] <;> split_ifs <;> linarith

lemma posPart_smul_nonneg (f : C_c(X, ℝ)) {c : ℝ} (hc : 0 ≤ c) :
    posPart (c • f) = c • posPart f := by
  ext x
  have h : max (c * f x) 0 = c * max (f x) 0 := by
    by_cases h2 : 0 ≤ f x
    · rw [max_eq_left h2, max_eq_left (mul_nonneg hc h2)]
    · have h3 : f x < 0 := by linarith
      have h4 : c * f x ≤ 0 := by nlinarith
      rw [max_eq_right h4, max_eq_right (by linarith)] <;> ring
  simpa [posPart] using h

lemma negPart_smul_nonneg (f : C_c(X, ℝ)) {c : ℝ} (hc : 0 ≤ c) :
    negPart (c • f) = c • negPart f := by
  ext x
  have h : max (-(c * f x)) 0 = c * max (-(f x)) 0 := by
    by_cases h2 : 0 ≤ f x
    · have h3 : -(c * f x) ≤ 0 := by nlinarith
      have h4 : -(f x) ≤ 0 := by linarith
      rw [max_eq_right h3, max_eq_right h4] <;> nlinarith
    · have h3 : f x < 0 := by linarith
      have h4 : 0 ≤ -(c * f x) := by nlinarith
      have h5 : 0 ≤ -(f x) := by linarith
      rw [max_eq_left h4, max_eq_left h5] <;> nlinarith
  simpa [negPart] using h

lemma posPart_smul_neg (f : C_c(X, ℝ)) {c : ℝ} (hc : c < 0) :
    posPart (c • f) = (-c) • negPart f := by
  ext x
  have h : max (c * f x) 0 = (-c) * max (-(f x)) 0 := by
    by_cases h2 : 0 ≤ f x
    · have h3 : c * f x ≤ 0 := by nlinarith
      have h4 : -(f x) ≤ 0 := by linarith
      rw [max_eq_right h3, max_eq_right h4] <;> nlinarith
    · have h3 : f x < 0 := by linarith
      have h4 : 0 ≤ c * f x := by nlinarith
      have h5 : 0 ≤ -(f x) := by linarith
      rw [max_eq_left h4, max_eq_left h5] <;> nlinarith
  simpa [posPart, negPart] using h

lemma negPart_smul_neg (f : C_c(X, ℝ)) {c : ℝ} (hc : c < 0) :
    negPart (c • f) = (-c) • posPart f := by
  ext x
  have h : max (-(c * f x)) 0 = (-c) * max (f x) 0 := by
    by_cases h2 : 0 ≤ f x
    · have h3 : 0 ≤ -(c * f x) := by nlinarith
      rw [max_eq_left h3, max_eq_left h2] <;> nlinarith
    · have h3 : f x < 0 := by linarith
      have h4 : -(c * f x) ≤ 0 := by nlinarith
      rw [max_eq_right h4, max_eq_right (by linarith)] <;> nlinarith
  simpa [posPart, negPart] using h

lemma add_identity (f g : C_c(X, ℝ)) :
    posPart (f + g) + negPart f + negPart g =
    negPart (f + g) + posPart f + posPart g := by
  ext x
  exact real_pos_neg_add_identity (f x) (g x)

variable (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
  (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)

include L C hC hL

/-- The extended positive linear functional. -/
noncomputable def Lpos (f : C_c(X, ℝ)) : ℝ :=
  posPartRaw L (posPart f) - posPartRaw L (negPart f)

lemma Lpos_add (f g : C_c(X, ℝ)) : Lpos L (f + g) = Lpos L f + Lpos L g := by
  have h_eq := add_identity f g
  have h1 : 0 ≤ posPart (f + g) := posPart_nonneg (f + g)
  have h2 : 0 ≤ negPart f := negPart_nonneg f
  have h3 : 0 ≤ negPart g := negPart_nonneg g
  have h4 : 0 ≤ negPart (f + g) := negPart_nonneg (f + g)
  have h5 : 0 ≤ posPart f := posPart_nonneg f
  have h6 : 0 ≤ posPart g := posPart_nonneg g
  have h_raw := posPartRaw_add L C hC hL h1 (show 0 ≤ negPart f + negPart g from by
    intro x; exact add_nonneg (h2 x) (h3 x))
  have h_raw2 := posPartRaw_add L C hC hL h4 (show 0 ≤ posPart f + posPart g from by
    intro x; exact add_nonneg (h5 x) (h6 x))
  have h7 : posPartRaw L (posPart (f + g) + negPart f + negPart g) =
      posPartRaw L (posPart (f + g)) + posPartRaw L (negPart f) + posPartRaw L (negPart g) := by
    have h8 := posPartRaw_add L C hC hL h1 (show 0 ≤ negPart f + negPart g from by
      intro x; exact add_nonneg (h2 x) (h3 x))
    have h9 := posPartRaw_add L C hC hL h2 h3
    have h_assoc : posPart (f + g) + negPart f + negPart g = posPart (f + g) + (negPart f + negPart g) := by abel
    rw [h_assoc, h8, h9] <;> ring
  have h10 : posPartRaw L (negPart (f + g) + posPart f + posPart g) =
      posPartRaw L (negPart (f + g)) + posPartRaw L (posPart f) + posPartRaw L (posPart g) := by
    have h11 := posPartRaw_add L C hC hL h4 (show 0 ≤ posPart f + posPart g from by
      intro x; exact add_nonneg (h5 x) (h6 x))
    have h12 := posPartRaw_add L C hC hL h5 h6
    have h_assoc : negPart (f + g) + posPart f + posPart g = negPart (f + g) + (posPart f + posPart g) := by abel
    rw [h_assoc, h11, h12] <;> ring
  have h13 : posPart (f + g) + negPart f + negPart g = negPart (f + g) + posPart f + posPart g := h_eq
  have h14 : posPartRaw L (posPart (f + g) + negPart f + negPart g) =
      posPartRaw L (negPart (f + g) + posPart f + posPart g) := by
    rw [h13]
  rw [h7, h10] at h14
  have h_goal : posPartRaw L (posPart (f + g)) - posPartRaw L (negPart (f + g)) =
      (posPartRaw L (posPart f) - posPartRaw L (negPart f)) +
      (posPartRaw L (posPart g) - posPartRaw L (negPart g)) := by
    linarith
  simpa [Lpos] using h_goal

lemma posPartRaw_zero : posPartRaw L (0 : C_c(X, ℝ)) = 0 := by
  have h_set : admissibleSet (0 : C_c(X, ℝ)) = {(0 : C_c(X, ℝ))} := by
    ext g
    simp only [admissibleSet, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      have h1 : 0 ≤ g := h.1
      have h2 : g ≤ 0 := h.2
      ext x; linarith [h1 x, h2 x]
    · intro h
      rw [h]
      <;> simp
  rw [posPartRaw, h_set]
  have h_image : L '' {(0 : C_c(X, ℝ))} = {(0 : ℝ)} := by simp
  rw [h_image]
  simp

lemma Lpos_smul (c : ℝ) (f : C_c(X, ℝ)) : Lpos L (c • f) = c * Lpos L f := by
  by_cases hc : 0 ≤ c
  · -- c ≥ 0
    rw [Lpos, posPart_smul_nonneg f hc, negPart_smul_nonneg f hc]
    rw [posPartRaw_smul L C hC hL (posPart_nonneg f) hc]
    rw [posPartRaw_smul L C hC hL (negPart_nonneg f) hc]
    have h_def : Lpos L f = posPartRaw L (posPart f) - posPartRaw L (negPart f) := by rfl
    rw [h_def] <;> ring
  · -- c < 0
    have hc' : c < 0 := by linarith
    rw [Lpos, posPart_smul_neg f hc', negPart_smul_neg f hc']
    rw [posPartRaw_smul L C hC hL (negPart_nonneg f) (by linarith)]
    rw [posPartRaw_smul L C hC hL (posPart_nonneg f) (by linarith)]
    have h_def : Lpos L f = posPartRaw L (posPart f) - posPartRaw L (negPart f) := by rfl
    rw [h_def] <;> ring

lemma Lpos_positive {f : C_c(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ Lpos L f := by
  have h1 : posPart f = f := by
    ext x
    have h2 : 0 ≤ f x := hf x
    simp [posPart, max_eq_left h2]
  have h3 : negPart f = 0 := by
    ext x
    have h4 : 0 ≤ f x := hf x
    have h5 : -f x ≤ 0 := by linarith
    have h6 : max (-f x) 0 = 0 := max_eq_right h5
    simpa [negPart] using h6
  rw [Lpos, h1, h3]
  rw [posPartRaw_zero L C hC hL]
  have h : 0 ≤ posPartRaw L f := posPartRaw_nonneg L C hC hL hf
  simpa using h

noncomputable def Lpos_linear : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun := Lpos L
  map_add' := Lpos_add L C hC hL
  map_smul' := Lpos_smul L C hC hL

noncomputable def Lpos_positiveLinearMap : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { Lpos_linear L C hC hL with
    monotone' := fun {f g} h => by
      have h' : 0 ≤ g - f := by
        intro x; exact sub_nonneg.mpr (h x)
      have h'' : 0 ≤ Lpos L (g - f) := Lpos_positive L C hC hL h'
      have h3 : Lpos L (g - f) = Lpos L g - Lpos L f :=
        (Lpos_linear L C hC hL).map_sub g f
      rw [h3] at h''
      simpa [Lpos_linear] using h'' }

/-- The negative part functional. -/
noncomputable def Lneg (f : C_c(X, ℝ)) : ℝ := Lpos L f - L f

lemma Lneg_positive {f : C_c(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ Lneg L f := by
  rw [Lneg]
  have h1 : L f ≤ posPartRaw L f := L_le_posPartRaw L C hC hL hf
  have h2 : posPart f = f := by
    ext x; have h3 : 0 ≤ f x := hf x; simp [posPart, max_eq_left h3]
  have h4 : negPart f = 0 := by
    ext x
    have h5 : 0 ≤ f x := hf x
    have h6 : -f x ≤ 0 := by linarith
    have h7 : max (-f x) 0 = 0 := max_eq_right h6
    simpa [negPart] using h7
  have h5 : Lpos L f = posPartRaw L f := by
    rw [Lpos, h2, h4, posPartRaw_zero L C hC hL] <;> ring
  rw [h5]
  linarith

noncomputable def Lneg_linear : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
  { toFun := Lneg L
    map_add' := by
      intro f g
      have h : Lneg L (f + g) = Lneg L f + Lneg L g := by
        simp only [Lneg]
        rw [Lpos_add L C hC hL, L.map_add] <;> ring
      exact h
    map_smul' := by
      intro c f
      have h : Lneg L (c • f) = c * Lneg L f := by
        simp only [Lneg]
        rw [Lpos_smul L C hC hL, L.map_smul] <;> ring
      exact h }

noncomputable def Lneg_positiveLinearMap : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { Lneg_linear L C hC hL with
    monotone' := fun {f g} h => by
      have h' : 0 ≤ g - f := by
        intro x; exact sub_nonneg.mpr (h x)
      have h'' : 0 ≤ Lneg L (g - f) := Lneg_positive L C hC hL h'
      have h3 : Lneg L (g - f) = Lneg L g - Lneg L f :=
        (Lneg_linear L C hC hL).map_sub g f
      rw [h3] at h''
      simpa [Lneg_linear] using h'' }

end Extension

section MainTheorem

variable (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
  (hL : ∀ (f : C_c(X, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖)

include L C hC hL

/-- Bound: for 0 ≤ f with f x ≤ 1 for all x, Lpos(f) + Lneg(f) ≤ C. -/
lemma pos_neg_sum_bound {f : C_c(X, ℝ)} (hf1 : 0 ≤ f) (hf2 : ∀ x, f x ≤ 1) :
    Lpos L f + Lneg L f ≤ C := by
  have h_pos : Lpos L f = posPartRaw L f := by
    have h1 : posPart f = f := by
      ext x; have h2 : 0 ≤ f x := hf1 x; simp [posPart, max_eq_left h2]
    have h3 : negPart f = 0 := by
      ext x
      have h4 : 0 ≤ f x := hf1 x
      have h5 : -f x ≤ 0 := by linarith
      have h6 : max (-f x) 0 = 0 := max_eq_right h5
      simpa [negPart] using h6
    rw [Lpos, h1, h3, posPartRaw_zero L C hC hL] <;> ring
  have h_neg : Lneg L f = posPartRaw L f - L f := by
    rw [Lneg, h_pos] <;> ring
  rw [h_pos, h_neg]
  -- Key idea: for any admissible g, ‖2g - f‖ ≤ 1, so 2L(g) - L(f) = L(2g-f) ≤ C.
  have h7 : ∀ (g : C_c(X, ℝ)), g ∈ admissibleSet f → 2 * L g ≤ L f + C := by
    intro g hg
    have hg1 : 0 ≤ g := hg.1
    have hg2 : g ≤ f := hg.2
    let h : C_c(X, ℝ) := (2 : ℝ) • g - f
    have h_eq : L h = 2 * L g - L f := by
      simp [h, L.map_sub, L.map_smul] <;> ring
    have h_norm : ‖Cc.toC₀ h‖ ≤ 1 := by
      have h_bound : ∀ (x : X), |(Cc.toC₀ h) x| ≤ (1 : ℝ) := by
        intro x
        have h1 : 0 ≤ g x := hg1 x
        have h2 : g x ≤ f x := hg2 x
        have h3 : f x ≤ 1 := hf2 x
        have h4 : (Cc.toC₀ h) x = 2 * g x - f x := by
          have h5 : (Cc.toC₀ h) x = h x := by rfl
          rw [h5]
          have h6 : h x = (2 : ℝ) * g x - f x := by
            exact rfl
          exact h6
        rw [h4]
        have h5 : |2 * g x - f x| ≤ f x := by
          rw [abs_le] <;> constructor <;> linarith
        linarith
      have h8 : ‖(Cc.toC₀ h).toBCF‖ ≤ (1 : ℝ) := by
        rw [BoundedContinuousFunction.norm_le (show (0 : ℝ) ≤ (1 : ℝ) from by norm_num)]
        exact h_bound
      simpa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using h8
    have h9 : L h ≤ C := by
      calc L h ≤ |L h| := le_abs_self (L h)
        _ ≤ C * ‖Cc.toC₀ h‖ := hL h
        _ ≤ C * 1 := by gcongr
        _ = C := by ring
    rw [h_eq] at h9
    linarith
  have h10 : BddAbove (L '' admissibleSet f) := bddAbove_admissible L C hC hL f hf1
  have h11 : (L '' admissibleSet f).Nonempty := nonempty_admissible L f hf1
  have h12 : posPartRaw L f ≤ (L f + C) / 2 := by
    dsimp only [posPartRaw]
    have h13 : ∀ y ∈ L '' admissibleSet f, y ≤ (L f + C) / 2 := by
      intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      have h14 : 2 * L g ≤ L f + C := h7 g hg
      linarith
    have h_iff : sSup (L '' admissibleSet f) ≤ (L f + C) / 2 ↔
        ∀ y ∈ L '' admissibleSet f, y ≤ (L f + C) / 2 :=
      csSup_le_iff h10 h11
    exact h_iff.mpr h13
  linarith

/-- The signed Riesz representation theorem. -/
theorem signed_riesz_representation :
    ∃ (μ : SignedMeasure X),
      (∀ (f : C_c(X, ℝ)),
        L f = (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
                (∫ x, f x ∂μ.toJordanDecomposition.negPart)) ∧
      (μ.totalVariation Set.univ ≤ ENNReal.ofReal C) := by
  let Lpos' : C_c(X, ℝ) →ₚ[ℝ] ℝ := Lpos_positiveLinearMap L C hC hL
  let Lneg' : C_c(X, ℝ) →ₚ[ℝ] ℝ := Lneg_positiveLinearMap L C hC hL
  let μpos : Measure X := RealRMK.rieszMeasure Lpos'
  let μneg : Measure X := RealRMK.rieszMeasure Lneg'
  have h_reg_pos : μpos.Regular := by infer_instance
  have h_reg_neg : μneg.Regular := by infer_instance
  have h_int_pos : ∀ (f : C_c(X, ℝ)), ∫ x, f x ∂μpos = Lpos' f :=
    RealRMK.integral_rieszMeasure Lpos'
  have h_int_neg : ∀ (f : C_c(X, ℝ)), ∫ x, f x ∂μneg = Lneg' f :=
    RealRMK.integral_rieszMeasure Lneg'
  have hLpos_eq : ∀ (f : C_c(X, ℝ)), Lpos' f = Lpos L f := by intro f; rfl
  have hLneg_eq : ∀ (f : C_c(X, ℝ)), Lneg' f = Lneg L f := by intro f; rfl
  -- Urysohn: for any compact K, exists f : C_c(X, ℝ), 0 ≤ f ≤ 1, f = 1 on K
  have h_urysohn : ∀ (K : Set X), IsCompact K →
      ∃ (f : C_c(X, ℝ)), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ ∀ x ∈ K, f x = 1 := by
    intro K hK
    have h_main : ∃ (g : C(X, ℝ)), Set.EqOn g 1 K ∧ IsCompact (tsupport g) ∧
        tsupport g ⊆ (Set.univ : Set X) ∧ ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (Set.subset_univ K)
    rcases h_main with ⟨g, hg1, hg2, _, hg4⟩
    have hsupport : HasCompactSupport g := by
      simpa [HasCompactSupport] using hg2
    let f : C_c(X, ℝ) := ⟨g, hsupport⟩
    refine ⟨f, ?_, ?_⟩
    · intro x; have h4 : f x ∈ Set.Icc (0 : ℝ) 1 := hg4 x; exact ⟨h4.1, h4.2⟩
    · intro x hx; exact hg1 hx
  -- Bound μpos K ≤ ofReal C for all compact K
  have h_pos_bound : ∀ (K : Set X), IsCompact K → μpos K ≤ ENNReal.ofReal C := by
    intro K hK
    rcases h_urysohn K hK with ⟨f, hf1, hfK⟩
    have hf1' : 0 ≤ f := by intro x; exact (hf1 x).1
    have hf2' : ∀ x, f x ≤ 1 := by intro x; exact (hf1 x).2
    have h_bound : Lpos' f ≤ C := by
      rw [hLpos_eq]
      have h : Lpos L f + Lneg L f ≤ C := pos_neg_sum_bound L C hC hL hf1' hf2'
      have h_nonneg : 0 ≤ Lneg L f := Lneg_positive L C hC hL hf1'
      linarith
    have h9 : μpos K ≤ ENNReal.ofReal (Lpos' f) :=
      RealRMK.rieszMeasure_le_of_eq_one Lpos' (fun x => (hf1 x).1) hK hfK
    exact h9.trans (ENNReal.ofReal_le_ofReal h_bound)
  -- Bound μneg K ≤ ofReal C for all compact K
  have h_neg_bound : ∀ (K : Set X), IsCompact K → μneg K ≤ ENNReal.ofReal C := by
    intro K hK
    rcases h_urysohn K hK with ⟨f, hf1, hfK⟩
    have hf1' : 0 ≤ f := by intro x; exact (hf1 x).1
    have hf2' : ∀ x, f x ≤ 1 := by intro x; exact (hf1 x).2
    have h_bound : Lneg' f ≤ C := by
      rw [hLneg_eq]
      have h : Lpos L f + Lneg L f ≤ C := pos_neg_sum_bound L C hC hL hf1' hf2'
      have h_nonneg : 0 ≤ Lpos L f := Lpos_positive L C hC hL hf1'
      linarith
    have h9 : μneg K ≤ ENNReal.ofReal (Lneg' f) :=
      RealRMK.rieszMeasure_le_of_eq_one Lneg' (fun x => (hf1 x).1) hK hfK
    exact h9.trans (ENNReal.ofReal_le_ofReal h_bound)
  -- Finiteness of μpos via inner regularity
  have h_pos_univ : μpos Set.univ ≤ ENNReal.ofReal C := by
    by_contra h
    have h' : ENNReal.ofReal C < μpos Set.univ := lt_of_not_ge h
    have h_inner := h_reg_pos.innerRegular isOpen_univ (ENNReal.ofReal C) h'
    rcases h_inner with ⟨K, _, hK, hK2⟩
    have hK3 := h_pos_bound K hK
    exact not_le.mpr hK2 hK3
  letI h_finite_pos : IsFiniteMeasure μpos := by
    refine' ⟨h_pos_univ.trans_lt ENNReal.ofReal_lt_top⟩
  -- Finiteness of μneg via inner regularity
  have h_neg_univ : μneg Set.univ ≤ ENNReal.ofReal C := by
    by_contra h
    have h' : ENNReal.ofReal C < μneg Set.univ := lt_of_not_ge h
    have h_inner := h_reg_neg.innerRegular isOpen_univ (ENNReal.ofReal C) h'
    rcases h_inner with ⟨K, _, hK, hK2⟩
    have hK3 := h_neg_bound K hK
    exact not_le.mpr hK2 hK3
  letI h_finite_neg : IsFiniteMeasure μneg := by
    refine' ⟨h_neg_univ.trans_lt ENNReal.ofReal_lt_top⟩
  let s : SignedMeasure X := μpos.toSignedMeasure - μneg.toSignedMeasure
  let j : JordanDecomposition X := s.toJordanDecomposition
  -- Identify j via the subtraction theorem
  have h_j : j = Measure.jordanDecompositionOfToSignedMeasureSub μpos μneg :=
    Measure.toJordanDecomposition_toSignedMeasure_sub (μ := μpos) (ν := μneg)
  have h_jpos : j.posPart = μpos - μneg := by
    rw [h_j]; exact Measure.jordanDecompositionOfToSignedMeasureSub_posPart
  have h_jneg : j.negPart = μneg - μpos := by
    rw [h_j]; exact Measure.jordanDecompositionOfToSignedMeasureSub_negPart
  -- Measure equality: j.posPart + μneg = j.negPart + μpos
  have h_j_eq : j.posPart + μneg = j.negPart + μpos := by
    have h1 : j.posPart.toSignedMeasure - j.negPart.toSignedMeasure =
        μpos.toSignedMeasure - μneg.toSignedMeasure :=
      SignedMeasure.toSignedMeasure_toJordanDecomposition s
    ext1 E hE
    have h2 : (j.posPart.toSignedMeasure - j.negPart.toSignedMeasure) E =
        (μpos.toSignedMeasure - μneg.toSignedMeasure) E := by rw [h1]
    have h3 : j.posPart.real E - j.negPart.real E = μpos.real E - μneg.real E := by
      simpa [Measure.toSignedMeasure_sub_apply hE] using h2
    have h4 : j.posPart.real E + μneg.real E = j.negPart.real E + μpos.real E := by linarith
    have hfin1 : j.posPart E < ⊤ := by
      rw [h_jpos]
      have h_sub : (μpos - μneg) ≤ μpos := Measure.sub_le
      exact lt_of_le_of_lt (h_sub E) (measure_lt_top μpos E)
    have hfin2 : j.negPart E < ⊤ := by
      rw [h_jneg]
      have h_sub : (μneg - μpos) ≤ μneg := Measure.sub_le
      exact lt_of_le_of_lt (h_sub E) (measure_lt_top μneg E)
    have hfin3 : μpos E < ⊤ := measure_lt_top μpos E
    have hfin4 : μneg E < ⊤ := measure_lt_top μneg E
    have h_real1 : j.posPart.real E = (j.posPart E).toReal := by rfl
    have h_real2 : μneg.real E = (μneg E).toReal := by rfl
    have h_real3 : j.negPart.real E = (j.negPart E).toReal := by rfl
    have h_real4 : μpos.real E = (μpos E).toReal := by rfl
    rw [h_real1, h_real2, h_real3, h_real4] at h4
    have h5 : (j.posPart E + μneg E).toReal = (j.negPart E + μpos E).toReal := by
      rw [ENNReal.toReal_add hfin1.ne hfin4.ne, ENNReal.toReal_add hfin2.ne hfin3.ne]
      exact h4
    have hfin_sum1 : (j.posPart E + μneg E) ≠ ⊤ := (add_lt_top.mpr ⟨hfin1, hfin4⟩).ne
    have hfin_sum2 : (j.negPart E + μpos E) ≠ ⊤ := (add_lt_top.mpr ⟨hfin2, hfin3⟩).ne
    have h_add1 : (j.posPart + μneg) E = j.posPart E + μneg E := by simp
    have h_add2 : (j.negPart + μpos) E = j.negPart E + μpos E := by simp
    rw [h_add1, h_add2]
    rw [← ENNReal.ofReal_toReal hfin_sum1, ← ENNReal.ofReal_toReal hfin_sum2, h5]
  -- Integral formula
  have h_integral_formula : ∀ (f : C_c(X, ℝ)),
      L f = (∫ x, f x ∂j.posPart) - (∫ x, f x ∂j.negPart) := by
    intro f
    have h_int1 : Integrable f μpos := CompactlySupportedContinuousMap.integrable f
    have h_int2 : Integrable f μneg := CompactlySupportedContinuousMap.integrable f
    have h_int3 : Integrable f j.posPart := by
      rw [h_jpos]
      exact Integrable.mono_measure h_int1 Measure.sub_le
    have h_int4 : Integrable f j.negPart := by
      rw [h_jneg]
      exact Integrable.mono_measure h_int2 Measure.sub_le
    have h_eq1 : ∫ x, f x ∂j.posPart + ∫ x, f x ∂μneg =
        ∫ x, f x ∂j.negPart + ∫ x, f x ∂μpos := by
      rw [← integral_add_measure h_int3 h_int2, ← integral_add_measure h_int4 h_int1, h_j_eq]
    have h_rmk_pos : ∫ x, f x ∂μpos = Lpos' f := h_int_pos f
    have h_rmk_neg : ∫ x, f x ∂μneg = Lneg' f := h_int_neg f
    have h_L : L f = Lpos' f - Lneg' f := by
      have h6 : Lneg' f = Lpos' f - L f := by
        rw [hLneg_eq, hLpos_eq, Lneg] <;> ring
      linarith
    linarith
  -- Variation bound
  have h_variation_bound : s.totalVariation Set.univ ≤ ENNReal.ofReal C := by
    have h1 : s.totalVariation = j.posPart + j.negPart := by rfl
    rw [h1]
    have h2 : j.posPart ≤ μpos := by
      rw [h_jpos]; exact Measure.sub_le
    have h3 : j.negPart ≤ μneg := by
      rw [h_jneg]; exact Measure.sub_le
    have h4 : j.posPart + j.negPart ≤ μpos + μneg := add_le_add h2 h3
    have h5 : (μpos + μneg) Set.univ ≤ ENNReal.ofReal C := by
      let ν : Measure X := μpos + μneg
      have h_regν : ν.Regular := by infer_instance
      have h_main : ∀ (K : Set X), IsCompact K → ν K ≤ ENNReal.ofReal C := by
        intro K hK
        rcases h_urysohn K hK with ⟨f, hf1, hfK⟩
        have hf1' : 0 ≤ f := by intro x; exact (hf1 x).1
        have hf2' : ∀ x, f x ≤ 1 := by intro x; exact (hf1 x).2
        have h_bound : Lpos' f + Lneg' f ≤ C := by
          rw [hLpos_eq, hLneg_eq]
          exact pos_neg_sum_bound L C hC hL hf1' hf2'
        have h_pos_nonneg : 0 ≤ Lpos' f := by
          rw [hLpos_eq]; exact Lpos_positive L C hC hL hf1'
        have h_neg_nonneg : 0 ≤ Lneg' f := by
          rw [hLneg_eq]; exact Lneg_positive L C hC hL hf1'
        have h10 : μpos K ≤ ENNReal.ofReal (Lpos' f) :=
          RealRMK.rieszMeasure_le_of_eq_one Lpos' (fun x => (hf1 x).1) hK hfK
        have h11 : μneg K ≤ ENNReal.ofReal (Lneg' f) :=
          RealRMK.rieszMeasure_le_of_eq_one Lneg' (fun x => (hf1 x).1) hK hfK
        have h12 : ν K = μpos K + μneg K := by simp [ν]
        have h13 : ENNReal.ofReal (Lpos' f) + ENNReal.ofReal (Lneg' f) = ENNReal.ofReal (Lpos' f + Lneg' f) := by
          rw [ENNReal.ofReal_add h_pos_nonneg h_neg_nonneg]
        have h14 : μpos K + μneg K ≤ ENNReal.ofReal (Lpos' f + Lneg' f) := by
          calc μpos K + μneg K
            ≤ ENNReal.ofReal (Lpos' f) + ENNReal.ofReal (Lneg' f) := add_le_add h10 h11
            _ = ENNReal.ofReal (Lpos' f + Lneg' f) := h13
        rw [h12]
        exact h14.trans (ENNReal.ofReal_le_ofReal h_bound)
      have h_inner : ν Set.univ ≤ ENNReal.ofReal C := by
        by_contra h
        have h' : ENNReal.ofReal C < ν Set.univ := lt_of_not_ge h
        have h_inner2 := h_regν.innerRegular isOpen_univ (ENNReal.ofReal C) h'
        rcases h_inner2 with ⟨K, _, hK, hK2⟩
        have hK3 := h_main K hK
        exact not_le.mpr hK2 hK3
      exact h_inner
    have h4' : (j.posPart + j.negPart) Set.univ ≤ (μpos + μneg) Set.univ := h4 Set.univ
    exact h4'.trans h5
  exact ⟨s, h_integral_formula, h_variation_bound⟩

end MainTheorem

import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.BaseSliceValuesAD
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ActualTripartitePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalizedTripartitePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23UnitBallGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.ArbitraryPositiveAffineAD
import Mathlib.Tactic

/-!
# Dot-difference AD at the graph scale

Helper lemmas for transferring global slab AD to the unit-ball dot-difference set.
-/

namespace Kakeya.Assouad

open Metric Set

/-- Translation preserves IsADSet1 if the translated set stays within [-4,4]. -/
lemma IsADSet1.translate
    {E : Set ℝ} {δ α : ℝ} {C : ENNReal} {c : ℝ}
    (hE : IsADSet1 E δ α C)
    (hE'_bounded : ((fun x : ℝ => x + c) '' E) ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 ((fun x : ℝ => x + c) '' E) δ α C := by
  rcases hE with ⟨hδ, hα, hα_one, hC, _hE_bounded, hcover⟩
  let f : ℝ → ℝ := fun x => x + c
  have hf_isom : Isometry f := isometry_add_right c
  have hf_surj : Function.Surjective f := by intro y; exact ⟨y - c, by ring⟩
  refine ⟨hδ, hα, hα_one, hC, hE'_bounded, ?_⟩
  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  have h_image_inter :
      f '' (E ∩ Metric.closedBall (x - c) r) =
      (f '' E) ∩ Metric.closedBall x r := by
    rw [Set.image_inter hf_isom.injective]
    have h_ball : f '' Metric.closedBall (x - c) r = Metric.closedBall x r := by
      ext z
      simp only [Set.mem_image, Metric.mem_closedBall, f]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h : dist (y + c) x = dist y (x - c) := by
          simp [dist_eq_norm, Real.norm_eq_abs] <;> ring_nf
        rw [h]; exact hy
      · intro hz
        refine ⟨z - c, ?_, by abel⟩
        have hdist : dist (z - c) (x - c) = dist z x := by
          simp [dist_eq_norm, Real.norm_eq_abs] <;> ring_nf
        rw [hdist]; exact hz
    rw [h_ball]
  have h_cover :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩
        ((f '' E) ∩ Metric.closedBall x r) : ENNReal) =
      (Metric.externalCoveringNumber ⟨rho, hrho⟩
        (E ∩ Metric.closedBall (x - c) r) : ENNReal) := by
    have h : Metric.externalCoveringNumber ⟨rho, hrho⟩ (f '' (E ∩ Metric.closedBall (x - c) r)) =
        Metric.externalCoveringNumber ⟨rho, hrho⟩ (E ∩ Metric.closedBall (x - c) r) :=
      Isometry.externalCoveringNumber_image hf_isom hf_surj
        (A := E ∩ Metric.closedBall (x - c) r) (ε := ⟨rho, hrho⟩)
    rw [←h_image_inter]
    exact_mod_cast h
  rw [h_cover]
  exact hcover rho hrho hdelta_rho hrho_one (x - c) r hrho_r hr_one

/-- If `a < ENNReal.ofReal (b + δ)` for all `δ > 0`, then `a ≤ ENNReal.ofReal b`. -/
private lemma forall_pos_imp_le {a : ENNReal} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ (δ : ℝ), 0 < δ → a < ENNReal.ofReal (b + δ)) : a ≤ ENNReal.ofReal b := by
  by_contra h2
  have h3 : ENNReal.ofReal b < a := by simpa [not_le] using h2
  rcases ENNReal.lt_iff_exists_real_btwn.mp h3 with ⟨r, _, hr1, hr2⟩
  have h_iff : ENNReal.ofReal b < ENNReal.ofReal r ↔ b < r :=
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hp := hb)
  have h4 : b < r := h_iff.mp hr1
  set δ : ℝ := (r - b) / 2 with hδ_def
  have hδ_pos : 0 < δ := by linarith
  have h5 : b + δ ≤ r := by
    dsimp only [δ]
    linarith
  have h6 : ENNReal.ofReal (b + δ) ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal h5
  have h7 : a < ENNReal.ofReal (b + δ) := h δ hδ_pos
  have h8 : a < ENNReal.ofReal r := h7.trans_le h6
  exact lt_asymm h8 hr2

/-- Scaling a cthickening by a positive real constant `c` on ℝ. -/
lemma cthickening_scaling
    {A B : Set ℝ} {ε : ℝ} {c : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (h : A ⊆ Metric.cthickening ε B) :
    (fun x : ℝ => c * x) '' A ⊆ Metric.cthickening (c * ε) ((fun x : ℝ => c * x) '' B) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have h1 : infEDist x B ≤ ENNReal.ofReal ε := h hx
  have h_main : ∀ (δ : ℝ), 0 < δ →
      infEDist (c * x) ((fun x : ℝ => c * x) '' B) < ENNReal.ofReal (c * ε + δ) := by
    intro δ hδ
    have h_pos2 : 0 < ε + δ / c := by positivity
    have h_lt : ε < ε + δ / c := by
      apply lt_add_of_pos_right
      positivity
    have h_strict : ENNReal.ofReal ε < ENNReal.ofReal (ε + δ / c) := by
      rw [ENNReal.ofReal_lt_ofReal_iff h_pos2]; exact h_lt
    have h2 : infEDist x B < ENNReal.ofReal (ε + δ / c) := h1.trans_lt h_strict
    rcases Metric.infEDist_lt_iff.mp h2 with ⟨b, hb, h3⟩
    have h4 : dist x b < ε + δ / c := by
      have h_iff : edist x b < ENNReal.ofReal (ε + δ / c) ↔ dist x b < ε + δ / c := by
        simp [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hp := dist_nonneg)]
      exact h_iff.mp h3
    have h5 : dist (c * x) (c * b) = c * dist x b := by
      have h_eq1 : dist (c * x) (c * b) = |c * x - c * b| := by rfl
      rw [h_eq1]
      have h_eq2 : |c * x - c * b| = |c| * |x - b| := by
        have h : c * x - c * b = c * (x - b) := by ring
        rw [h, abs_mul]
      rw [h_eq2]
      have h_abs : |c| = c := abs_of_pos hc
      rw [h_abs] <;> rfl
    have h61 : c * dist x b < c * (ε + δ / c) := by gcongr
    have h62 : c * (ε + δ / c) = c * ε + δ := by
      field_simp [hc.ne'] <;> ring
    have h6 : dist (c * x) (c * b) < c * ε + δ := by
      rw [h5]; rw [h62] at h61; exact h61
    have h7 : (c * b) ∈ (fun x : ℝ => c * x) '' B := ⟨b, hb, by ring⟩
    have h8 : infEDist (c * x) ((fun x : ℝ => c * x) '' B) ≤ edist (c * x) (c * b) :=
      Metric.infEDist_le_edist_of_mem h7
    have h9 : edist (c * x) (c * b) = ENNReal.ofReal (dist (c * x) (c * b)) := by simp [edist_dist]
    rw [h9] at h8
    have h_iff2 : ENNReal.ofReal (dist (c * x) (c * b)) < ENNReal.ofReal (c * ε + δ) ↔
        dist (c * x) (c * b) < c * ε + δ :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hp := dist_nonneg)
    have h10 : ENNReal.ofReal (dist (c * x) (c * b)) < ENNReal.ofReal (c * ε + δ) := h_iff2.mpr h6
    exact h8.trans_lt h10
  exact forall_pos_imp_le (by positivity) h_main

/-- If `A ⊆ [-2,2]`, `ε < 2`, and `A ⊆ cthickening ε B`, then
`A ⊆ cthickening ε (B ∩ [-4,4])`. -/
lemma cthickening_restrict_bounded
    {A B : Set ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hε_lt_two : ε < 2)
    (hA_bounded : A ⊆ Set.Icc (-2 : ℝ) 2)
    (h : A ⊆ Metric.cthickening ε B) :
    A ⊆ Metric.cthickening ε (B ∩ Set.Icc (-4 : ℝ) 4) := by
  intro x hx
  have h1 : infEDist x B ≤ ENNReal.ofReal ε := h hx
  have hx2 : x ∈ Set.Icc (-2 : ℝ) 2 := hA_bounded hx
  have h_absx : |x| ≤ 2 := abs_le.mpr ⟨hx2.1, hx2.2⟩
  have h_help : ∀ (δ' : ℝ), 0 < δ' → δ' < 2 - ε →
      infEDist x (B ∩ Set.Icc (-4 : ℝ) 4) < ENNReal.ofReal (ε + δ') := by
    intro δ' hδ' hsmall
    have h2 : infEDist x B < ENNReal.ofReal (ε + δ') :=
      h1.trans_lt (by
        rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)] <;> linarith)
    rcases Metric.infEDist_lt_iff.mp h2 with ⟨b, hb, h3⟩
    have h4 : dist x b < ε + δ' := by
      simpa [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hp := dist_nonneg)] using h3
    have h5 : |b| ≤ dist x b + |x| := by
      have h_tri : dist b 0 ≤ dist b x + dist x 0 := dist_triangle b x 0
      have h6 : dist b 0 = |b| := by simp [Real.dist_eq]
      have h7 : dist b x = dist x b := dist_comm b x
      have h8 : dist x 0 = |x| := by simp [Real.dist_eq]
      rw [h6, h7, h8] at h_tri
      exact h_tri
    have h5' : |b| ≤ |x| + dist x b := by linarith
    have h9 : |b| < 4 := by
      calc |b| ≤ |x| + dist x b := h5'
        _ ≤ 2 + dist x b := by gcongr
        _ < 2 + (ε + δ') := by gcongr
        _ < 4 := by linarith
    have h10 : b ∈ Set.Icc (-4 : ℝ) 4 := by
      exact abs_le.mp (by linarith)
    have h11 : b ∈ B ∩ Set.Icc (-4 : ℝ) 4 := ⟨hb, h10⟩
    have h12 : infEDist x (B ∩ Set.Icc (-4 : ℝ) 4) ≤ edist x b :=
      Metric.infEDist_le_edist_of_mem h11
    exact h12.trans_lt h3
  have h_main : ∀ (δ : ℝ), 0 < δ →
      infEDist x (B ∩ Set.Icc (-4 : ℝ) 4) < ENNReal.ofReal (ε + δ) := by
    intro δ hδ
    by_cases hsmall : δ < 2 - ε
    · exact h_help δ hδ hsmall
    · let δ' := (2 - ε) / 2
      have h_pos : 0 < 2 - ε := by linarith
      have hδ'_pos : 0 < δ' := by
        dsimp only [δ']; exact half_pos h_pos
      have hδ'_lt : δ' < 2 - ε := by
        dsimp only [δ']; exact half_lt_self h_pos
      have h1 := h_help δ' hδ'_pos hδ'_lt
      have h2 : ε + δ' ≤ ε + δ := by linarith
      exact h1.trans_le (ENNReal.ofReal_le_ofReal h2)
  exact forall_pos_imp_le hε h_main

/-- Transfer AD from source set E to the unit-ball dot-difference set. -/
lemma dot_difference_AD_transfer
    {E baseValues normalizedValues normalizedDotDiff unitBallDotDiff : Set ℝ}
    {rho : ℝ} {C : ENNReal} {sigma : ℝ}
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma)
    (hsigma_one : sigma < 1)
    (hC_top : C ≠ ⊤)
    (hAD_E : IsADSet1 E rho (1 - sigma) C)
    (hbaseValues_contain : baseValues ⊆ Metric.cthickening (4 * rho) E)
    (hnormalizedValues_eq : normalizedValues = (fun x : ℝ => x / Real.sqrt rho) '' baseValues)
    (hnormalizedDotDiff_contain : normalizedDotDiff ⊆ Metric.cthickening (4 * Real.sqrt rho) normalizedValues)
    (hunitBallDotDiff_eq : unitBallDotDiff = (fun x : ℝ => x / 25) '' normalizedDotDiff)
    (hunitBallDotDiff_bounded : unitBallDotDiff ⊆ Set.Icc (-2 : ℝ) 2) :
    IsADSet1 unitBallDotDiff (Real.sqrt rho / (25 * Real.sqrt 3)) (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C) := by
  let a1 : ℝ := 1 / Real.sqrt rho
  let a2 : ℝ := 1 / 25
  let a : ℝ := a1 * a2
  let E_scaled : Set ℝ := (fun x : ℝ => a1 * x) '' E
  let E_affine : Set ℝ := (fun x : ℝ => a * x) '' E
  let delta_AD : ℝ := Real.sqrt rho / 25
  let dichScale : ℝ := Real.sqrt rho / (25 * Real.sqrt 3)
  have ha1_pos : 0 < a1 := by positivity
  have ha2_pos : 0 < a2 := by norm_num
  have ha_pos : 0 < a := by positivity
  have hdelta_AD_pos : 0 < delta_AD := by positivity
  have hdelta_AD_one : delta_AD ≤ 1 := by
    dsimp only [delta_AD]
    have h1 : Real.sqrt rho ≤ 1 := by
      rw [Real.sqrt_le_left (by positivity)] <;> linarith
    linarith
  have ha_rho : a * rho = delta_AD := by
    dsimp only [a, a1, a2, delta_AD]
    have h : (1 / Real.sqrt rho) * (1 / 25) * rho = Real.sqrt rho / 25 := by
      field_simp [hrho_pos.ne'] <;> nlinarith [Real.sq_sqrt (show 0 ≤ rho by linarith)]
    exact h
  rcases hAD_E with ⟨hδ, hα, hα_one, hC, hE_bounded, hcover⟩
  have hAD_E' : IsADSet1 E rho (1 - sigma) C :=
    ⟨hδ, hα, hα_one, hC, hE_bounded, hcover⟩
  have ha_rho_le_one : a * rho ≤ 1 := by
    rw [ha_rho]; exact hdelta_AD_one
  have hE_affine_eq : E_affine = (fun x : ℝ => a2 * x) '' E_scaled := by
    ext y
    simp only [E_affine, E_scaled, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨a1 * x, ⟨x, hx, rfl⟩, by ring⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by ring⟩
  -- Step 1: affine_small4
  have h_affine_set_eq : ((fun x : ℝ => a * x + 0) '' E) = E_affine := by
    ext y; simp [E_affine] <;> ring
  have hAD_affine0 : IsADSet1 (((fun x : ℝ => a * x + 0) '' E) ∩ Set.Icc (-4 : ℝ) 4) (a * rho) (1 - sigma) (5 * C) :=
    hAD_E'.affine_image_arbitrary_positive
      (a := a) (b := 0) ha_pos hE_bounded ha_rho_le_one
  have hAD_affine : IsADSet1 (E_affine ∩ Set.Icc (-4 : ℝ) 4) delta_AD (1 - sigma) (5 * C) := by
    have h_set_eq : ((fun x : ℝ => a * x + 0) '' E) ∩ Set.Icc (-4 : ℝ) 4 = E_affine ∩ Set.Icc (-4 : ℝ) 4 := by
      rw [h_affine_set_eq]
    rw [ha_rho] at hAD_affine0
    rw [h_set_eq] at hAD_affine0
    exact hAD_affine0
  -- Step 2: scale baseValues by a1
  have h4rho_pos : 0 ≤ 4 * rho := by positivity
  have h1_raw : (fun x : ℝ => a1 * x) '' baseValues ⊆
      Metric.cthickening (a1 * (4 * rho)) ((fun x : ℝ => a1 * x) '' E) :=
    cthickening_scaling ha1_pos h4rho_pos hbaseValues_contain
  have ha1_mul4rho : a1 * (4 * rho) = 4 * Real.sqrt rho := by
    dsimp only [a1]
    field_simp [hrho_pos.ne'] <;> nlinarith [Real.sq_sqrt (show 0 ≤ rho by linarith)]
  have h_eq1 : (fun x : ℝ => x / Real.sqrt rho) = (fun x : ℝ => a1 * x) := by
    funext x; dsimp only [a1]; ring
  have h1 : normalizedValues ⊆ Metric.cthickening (4 * Real.sqrt rho) E_scaled := by
    rw [hnormalizedValues_eq, h_eq1]
    rw [ha1_mul4rho] at h1_raw
    exact h1_raw
  -- Step 3: chain containments
  have h3 : Metric.cthickening (4 * Real.sqrt rho) normalizedValues ⊆
      Metric.cthickening (4 * Real.sqrt rho) (Metric.cthickening (4 * Real.sqrt rho) E_scaled) :=
    Metric.cthickening_subset_of_subset (4 * Real.sqrt rho) h1
  have h4 : normalizedDotDiff ⊆
      Metric.cthickening (4 * Real.sqrt rho) (Metric.cthickening (4 * Real.sqrt rho) E_scaled) :=
    hnormalizedDotDiff_contain.trans h3
  have h_pos4 : 0 ≤ 4 * Real.sqrt rho := by positivity
  have h_sum4 : 4 * Real.sqrt rho + 4 * Real.sqrt rho = 8 * Real.sqrt rho := by ring
  have h5 : normalizedDotDiff ⊆ Metric.cthickening (8 * Real.sqrt rho) E_scaled := by
    have h_chain := Metric.cthickening_cthickening_subset h_pos4 h_pos4 E_scaled
    rw [h_sum4] at h_chain
    exact h4.trans h_chain
  -- Step 4: scale by a2
  have h8sqrt_pos : 0 ≤ 8 * Real.sqrt rho := by positivity
  have h6_raw : (fun x : ℝ => a2 * x) '' normalizedDotDiff ⊆
      Metric.cthickening (a2 * (8 * Real.sqrt rho)) ((fun x : ℝ => a2 * x) '' E_scaled) :=
    cthickening_scaling ha2_pos h8sqrt_pos h5
  have ha2_mul8sqrt : a2 * (8 * Real.sqrt rho) = 8 * delta_AD := by
    dsimp only [a2, delta_AD] <;> ring
  have h_eq2 : (fun x : ℝ => x / 25) = (fun x : ℝ => a2 * x) := by
    funext x; dsimp only [a2]; ring
  have h6 : unitBallDotDiff ⊆ Metric.cthickening (8 * delta_AD) E_affine := by
    rw [hunitBallDotDiff_eq, h_eq2]
    rw [ha2_mul8sqrt] at h6_raw
    rw [hE_affine_eq] at *
    <;> exact h6_raw
  -- Step 5: restrict to [-4,4]
  have h8delta_AD_lt_two : 8 * delta_AD < 2 := by
    dsimp only [delta_AD]
    have h1 : Real.sqrt rho ≤ 1 := by
      rw [Real.sqrt_le_left (by positivity)] <;> linarith
    linarith
  have h9 : unitBallDotDiff ⊆ Metric.cthickening (8 * delta_AD) (E_affine ∩ Set.Icc (-4 : ℝ) 4) :=
    cthickening_restrict_bounded (by positivity) h8delta_AD_lt_two hunitBallDotDiff_bounded h6
  -- Step 6: generalized_thickening
  have hunitBall4 : unitBallDotDiff ⊆ Set.Icc (-4 : ℝ) 4 :=
    hunitBallDotDiff_bounded.trans (by intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have h_const1 : (2 * (Nat.ceil ((8 * delta_AD) / delta_AD) + 1) : ENNReal) ^ 2 * (5 * C) =
      (1620 : ENNReal) * C := by
    have hdiv : (8 * delta_AD) / delta_AD = 8 := by
      field_simp [hdelta_AD_pos.ne'] <;> ring
    rw [hdiv]
    have hceil : Nat.ceil (8 : ℝ) = 8 := by
      rw [Nat.ceil_eq_iff] <;> norm_num
    rw [hceil] <;> norm_num <;> ring
  have hAD_dotDiff : IsADSet1 unitBallDotDiff delta_AD (1 - sigma) ((1620 : ENNReal) * C) := by
    rw [← h_const1]
    exact hAD_affine.generalized_thickening h9 hunitBall4 hdelta_AD_pos (by positivity)
  -- Step 7: weaken scale
  have hdichScale_pos : 0 < dichScale := by positivity
  have hsqrt3_ge_one : (1 : ℝ) ≤ Real.sqrt 3 := by
    have hsq : (1 : ℝ) ^ 2 ≤ (3 : ℝ) := by norm_num
    have h : (1 : ℝ) ≤ Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    exact h
  have hdichScale_le_deltaAD : dichScale ≤ delta_AD := by
    dsimp only [dichScale, delta_AD]
    have h : Real.sqrt rho / (25 * Real.sqrt 3) ≤ Real.sqrt rho / 25 := by
      gcongr
      <;> linarith [hsqrt3_ge_one]
    exact h
  have hratio : delta_AD / dichScale = Real.sqrt 3 := by
    dsimp only [delta_AD, dichScale]
    field_simp [hrho_pos.ne'] <;> ring
  have hfactor : ENNReal.ofReal ((10 * delta_AD) / dichScale) =
      (10 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) := by
    have h_algebra : (10 * delta_AD) / dichScale = 10 * Real.sqrt 3 := by
      have h1 : (10 * delta_AD) / dichScale = 10 * (delta_AD / dichScale) := by
        field_simp [hdichScale_pos.ne'] <;> ring
      rw [h1, hratio] <;> ring
    rw [h_algebra]
    have h_mul : ENNReal.ofReal (10 * Real.sqrt 3) =
        ENNReal.ofReal (10 : ℝ) * ENNReal.ofReal (Real.sqrt 3) := by
      exact ENNReal.ofReal_mul (by norm_num)
    rw [h_mul]
    <;> norm_cast
  have hAD_final0 : IsADSet1 unitBallDotDiff dichScale (1 - sigma)
      (((1620 : ENNReal) * C) * ENNReal.ofReal ((10 * delta_AD) / dichScale)) :=
    hAD_dotDiff.weaken_scale hdichScale_pos hdichScale_le_deltaAD hdelta_AD_one
  have h_final_const : ((1620 : ENNReal) * C) * ENNReal.ofReal ((10 * delta_AD) / dichScale) =
      (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C := by
    rw [hfactor] <;> ring
  have hAD_final : IsADSet1 unitBallDotDiff dichScale (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C) := by
    rw [h_final_const] at hAD_final0
    exact hAD_final0
  exact hAD_final

/--
Shifted variant of `dot_difference_AD_transfer`.

The source values may be translated by a constant `c` (e.g. subtracting
`baseGlobalBin * rho`).  We apply `affine_small4` to the original AD set `E`
with the affine map `x ↦ a*x - a*c`, so the boundedness of `E` is preserved
and we never need to construct `IsADSet1 (E - c)`.
-/
lemma dot_difference_AD_transfer_shifted
    {E baseValues normalizedValues normalizedDotDiff unitBallDotDiff : Set ℝ}
    {rho : ℝ} {C : ENNReal} {sigma : ℝ} {c : ℝ}
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma)
    (hsigma_one : sigma < 1)
    (hC_top : C ≠ ⊤)
    (hAD_E : IsADSet1 E rho (1 - sigma) C)
    (hbaseValues_contain : baseValues ⊆ Metric.cthickening (4 * rho) ((fun x : ℝ => x - c) '' E))
    (hnormalizedValues_eq : normalizedValues = (fun x : ℝ => x / Real.sqrt rho) '' baseValues)
    (hnormalizedDotDiff_contain : normalizedDotDiff ⊆ Metric.cthickening (4 * Real.sqrt rho) normalizedValues)
    (hunitBallDotDiff_eq : unitBallDotDiff = (fun x : ℝ => x / 25) '' normalizedDotDiff)
    (hunitBallDotDiff_bounded : unitBallDotDiff ⊆ Set.Icc (-2 : ℝ) 2) :
    IsADSet1 unitBallDotDiff (Real.sqrt rho / (25 * Real.sqrt 3)) (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C) := by
  let a1 : ℝ := 1 / Real.sqrt rho
  let a2 : ℝ := 1 / 25
  let a : ℝ := a1 * a2
  let E' : Set ℝ := (fun x : ℝ => x - c) '' E
  let E'_scaled : Set ℝ := (fun x : ℝ => a1 * x) '' E'
  let E'_affine : Set ℝ := (fun x : ℝ => a * x) '' E'
  let delta_AD : ℝ := Real.sqrt rho / 25
  let dichScale : ℝ := Real.sqrt rho / (25 * Real.sqrt 3)
  have ha1_pos : 0 < a1 := by positivity
  have ha2_pos : 0 < a2 := by norm_num
  have ha_pos : 0 < a := by positivity
  have hdelta_AD_pos : 0 < delta_AD := by positivity
  have hdelta_AD_one : delta_AD ≤ 1 := by
    dsimp only [delta_AD]
    have h1 : Real.sqrt rho ≤ 1 := by
      rw [Real.sqrt_le_left (by positivity)] <;> linarith
    linarith
  have ha_rho : a * rho = delta_AD := by
    dsimp only [a, a1, a2, delta_AD]
    have h : (1 / Real.sqrt rho) * (1 / 25) * rho = Real.sqrt rho / 25 := by
      field_simp [hrho_pos.ne'] <;> nlinarith [Real.sq_sqrt (show 0 ≤ rho by linarith)]
    exact h
  have hE'_affine_eq : E'_affine = (fun x : ℝ => a * x - a * c) '' E := by
    ext y
    simp only [E'_affine, E', Set.mem_image]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, by ring⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x - c, ⟨x, hx, by ring⟩, by ring⟩
  -- Step 1: affine_small4 with shift
  have ha_rho_le_one : a * rho ≤ 1 := by
    rw [ha_rho]; exact hdelta_AD_one
  rcases hAD_E with ⟨hδ, hα, hα_one, hC, hE_bounded, hcover⟩
  have hAD_E' : IsADSet1 E rho (1 - sigma) C :=
    ⟨hδ, hα, hα_one, hC, hE_bounded, hcover⟩
  have hE_small : E ⊆ Set.Icc (-4 : ℝ) 4 := hE_bounded
  have hAD_affine0 : IsADSet1 (((fun x : ℝ => a * x + (-a * c)) '' E) ∩ Set.Icc (-4 : ℝ) 4) (a * rho) (1 - sigma) (5 * C) :=
    hAD_E'.affine_image_arbitrary_positive
      (a := a) (b := -a * c) ha_pos hE_small ha_rho_le_one
  have h_set_eq : ((fun x : ℝ => a * x + (-a * c)) '' E) ∩ Set.Icc (-4 : ℝ) 4 = E'_affine ∩ Set.Icc (-4 : ℝ) 4 := by
    have h1 : (fun x : ℝ => a * x + (-a * c)) = (fun x : ℝ => a * x - a * c) := by funext x; ring
    rw [h1, hE'_affine_eq]
  rw [h_set_eq] at hAD_affine0
  have hAD_affine : IsADSet1 (E'_affine ∩ Set.Icc (-4 : ℝ) 4) delta_AD (1 - sigma) (5 * C) := by
    rw [ha_rho] at hAD_affine0; exact hAD_affine0
  -- Step 2: scale baseValues by a1
  have h4rho_pos : 0 ≤ 4 * rho := by positivity
  have h1_raw : (fun x : ℝ => a1 * x) '' baseValues ⊆
      Metric.cthickening (a1 * (4 * rho)) E'_scaled :=
    cthickening_scaling ha1_pos h4rho_pos hbaseValues_contain
  have ha1_mul4rho : a1 * (4 * rho) = 4 * Real.sqrt rho := by
    dsimp only [a1]
    field_simp [hrho_pos.ne'] <;> nlinarith [Real.sq_sqrt (show 0 ≤ rho by linarith)]
  have h_eq1 : (fun x : ℝ => x / Real.sqrt rho) = (fun x : ℝ => a1 * x) := by
    funext x; dsimp only [a1]; ring
  have h1 : normalizedValues ⊆ Metric.cthickening (4 * Real.sqrt rho) E'_scaled := by
    rw [hnormalizedValues_eq, h_eq1]
    rw [ha1_mul4rho] at h1_raw
    exact h1_raw
  -- Step 3: chain containments
  have h3 : Metric.cthickening (4 * Real.sqrt rho) normalizedValues ⊆
      Metric.cthickening (4 * Real.sqrt rho) (Metric.cthickening (4 * Real.sqrt rho) E'_scaled) :=
    Metric.cthickening_subset_of_subset (4 * Real.sqrt rho) h1
  have h4 : normalizedDotDiff ⊆
      Metric.cthickening (4 * Real.sqrt rho) (Metric.cthickening (4 * Real.sqrt rho) E'_scaled) :=
    hnormalizedDotDiff_contain.trans h3
  have h_pos4 : 0 ≤ 4 * Real.sqrt rho := by positivity
  have h_sum4 : 4 * Real.sqrt rho + 4 * Real.sqrt rho = 8 * Real.sqrt rho := by ring
  have h5 : normalizedDotDiff ⊆ Metric.cthickening (8 * Real.sqrt rho) E'_scaled := by
    have h_chain := Metric.cthickening_cthickening_subset h_pos4 h_pos4 E'_scaled
    rw [h_sum4] at h_chain
    exact h4.trans h_chain
  -- Step 4: scale by a2
  have h8sqrt_pos : 0 ≤ 8 * Real.sqrt rho := by positivity
  have h6_raw : (fun x : ℝ => a2 * x) '' normalizedDotDiff ⊆
      Metric.cthickening (a2 * (8 * Real.sqrt rho)) ((fun x : ℝ => a2 * x) '' E'_scaled) :=
    cthickening_scaling ha2_pos h8sqrt_pos h5
  have ha2_mul8sqrt : a2 * (8 * Real.sqrt rho) = 8 * delta_AD := by
    dsimp only [a2, delta_AD] <;> ring
  have h_eq2 : (fun x : ℝ => x / 25) = (fun x : ℝ => a2 * x) := by
    funext x; dsimp only [a2]; ring
  have hE'_affine_eq2 : (fun x : ℝ => a2 * x) '' E'_scaled = E'_affine := by
    ext y
    simp only [E'_affine, E'_scaled, Set.mem_image]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, by ring⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨a1 * x, ⟨x, hx, rfl⟩, by ring⟩
  have h6 : unitBallDotDiff ⊆ Metric.cthickening (8 * delta_AD) E'_affine := by
    rw [hunitBallDotDiff_eq, h_eq2]
    have h6_raw' : (fun x : ℝ => a2 * x) '' normalizedDotDiff ⊆
        Metric.cthickening (8 * delta_AD) E'_affine := by
      rw [ha2_mul8sqrt] at h6_raw
      rw [hE'_affine_eq2] at h6_raw
      exact h6_raw
    exact h6_raw'
  -- Step 5: restrict to [-4,4]
  have h8delta_AD_lt_two : 8 * delta_AD < 2 := by
    dsimp only [delta_AD]
    have h1 : Real.sqrt rho ≤ 1 := by
      rw [Real.sqrt_le_left (by positivity)] <;> linarith
    linarith
  have h9 : unitBallDotDiff ⊆ Metric.cthickening (8 * delta_AD) (E'_affine ∩ Set.Icc (-4 : ℝ) 4) :=
    cthickening_restrict_bounded (by positivity) h8delta_AD_lt_two hunitBallDotDiff_bounded h6
  -- Step 6: generalized_thickening
  have hunitBall4 : unitBallDotDiff ⊆ Set.Icc (-4 : ℝ) 4 :=
    hunitBallDotDiff_bounded.trans (by intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have h_const1 : (2 * (Nat.ceil ((8 * delta_AD) / delta_AD) + 1) : ENNReal) ^ 2 * (5 * C) =
      (1620 : ENNReal) * C := by
    have hdiv : (8 * delta_AD) / delta_AD = 8 := by
      field_simp [hdelta_AD_pos.ne'] <;> ring
    rw [hdiv]
    have hceil : Nat.ceil (8 : ℝ) = 8 := by
      rw [Nat.ceil_eq_iff] <;> norm_num
    rw [hceil] <;> norm_num <;> ring
  have hAD_dotDiff : IsADSet1 unitBallDotDiff delta_AD (1 - sigma) ((1620 : ENNReal) * C) := by
    rw [← h_const1]
    exact hAD_affine.generalized_thickening h9 hunitBall4 hdelta_AD_pos (by positivity)
  -- Step 7: weaken scale
  have hdichScale_pos : 0 < dichScale := by positivity
  have hsqrt3_ge_one : (1 : ℝ) ≤ Real.sqrt 3 := by
    have hsq : (1 : ℝ) ^ 2 ≤ (3 : ℝ) := by norm_num
    have h : (1 : ℝ) ≤ Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    exact h
  have hdichScale_le_deltaAD : dichScale ≤ delta_AD := by
    dsimp only [dichScale, delta_AD]
    have h : Real.sqrt rho / (25 * Real.sqrt 3) ≤ Real.sqrt rho / 25 := by
      gcongr <;> linarith [hsqrt3_ge_one]
    exact h
  have hratio : delta_AD / dichScale = Real.sqrt 3 := by
    dsimp only [delta_AD, dichScale]
    field_simp [hrho_pos.ne'] <;> ring
  have hfactor : ENNReal.ofReal ((10 * delta_AD) / dichScale) =
      (10 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) := by
    have h_algebra : (10 * delta_AD) / dichScale = 10 * Real.sqrt 3 := by
      have h1 : (10 * delta_AD) / dichScale = 10 * (delta_AD / dichScale) := by
        field_simp [hdichScale_pos.ne'] <;> ring
      rw [h1, hratio] <;> ring
    rw [h_algebra]
    have h_mul : ENNReal.ofReal (10 * Real.sqrt 3) =
        ENNReal.ofReal (10 : ℝ) * ENNReal.ofReal (Real.sqrt 3) := by
      exact ENNReal.ofReal_mul (by norm_num)
    rw [h_mul] <;> norm_cast
  have hAD_final0 : IsADSet1 unitBallDotDiff dichScale (1 - sigma)
      (((1620 : ENNReal) * C) * ENNReal.ofReal ((10 * delta_AD) / dichScale)) :=
    hAD_dotDiff.weaken_scale hdichScale_pos hdichScale_le_deltaAD hdelta_AD_one
  have h_final_const : ((1620 : ENNReal) * C) * ENNReal.ofReal ((10 * delta_AD) / dichScale) =
      (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C := by
    rw [hfactor] <;> ring
  have hAD_final : IsADSet1 unitBallDotDiff dichScale (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C) := by
    rw [h_final_const] at hAD_final0
    exact hAD_final0
  exact hAD_final

end Kakeya.Assouad

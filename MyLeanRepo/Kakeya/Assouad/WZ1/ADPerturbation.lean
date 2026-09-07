import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# AD perturbation under bounded Hausdorff shift

If two subsets of `ℝ` are `δ`-close (one-sided: every point of `E'` is within
`δ` of `E`) and `E` satisfies `IsADSet1 E δ α C`, then `E'` satisfies
`IsADSet1 E' δ α (8 * C)`.

The key geometric fact is that in one dimension, the `δ`-neighborhood of a
`rho`-ball (with `δ ≤ rho`) can be covered by two `rho`-balls.
-/

namespace Kakeya.Assouad

open Metric Set

/-- In `ℝ`, if every point of `B` is within `δ` of some point in `A`, and
`0 ≤ δ ≤ rho`, then the `rho`-external covering number of `B` is at most
twice that of `A`. -/
lemma externalCoveringNumber_thickening_two_mul_real
    {A B : Set ℝ} {rho delta : ℝ} (hrho : 0 < rho) (hdelta : 0 ≤ delta)
    (hdelta_rho : delta ≤ rho)
    (h : ∀ x ∈ B, ∃ y ∈ A, |x - y| ≤ delta) :
    Metric.externalCoveringNumber ⟨rho, hrho.le⟩ B ≤
      2 * Metric.externalCoveringNumber ⟨rho, hrho.le⟩ A := by
  let ε : NNReal := ⟨rho, hrho.le⟩
  by_cases h_top : Metric.externalCoveringNumber ε A = ⊤
  · rw [h_top]; simp
  · let S : Type _ := {C : Set ℝ // Metric.IsCover ε A C}
    haveI : Nonempty S := by
      refine ⟨⟨Set.univ, fun x hx => ⟨x, Set.mem_univ x, ?_⟩⟩⟩
      simp
    let f : S → ℕ∞ := fun C => C.val.encard
    have h_ext : iInf f = Metric.externalCoveringNumber ε A := by
      apply le_antisymm
      · apply le_iInf₂
        intro C hC
        exact iInf_le (α := ℕ∞) (f := f) ⟨C, hC⟩
      · apply le_iInf
        intro C
        have h1 : Metric.externalCoveringNumber ε A ≤
            iInf (fun h : Metric.IsCover ε A C.val => C.val.encard) :=
          iInf_le (α := ℕ∞) (f := fun D : Set ℝ =>
            iInf (fun h : Metric.IsCover ε A D => D.encard)) C.val
        have h2 : iInf (fun h : Metric.IsCover ε A C.val => C.val.encard) ≤ C.val.encard :=
          iInf_le (α := ℕ∞) (f := fun h : Metric.IsCover ε A C.val => C.val.encard) C.property
        exact h1.trans h2
    rcases ENat.exists_eq_iInf f with ⟨C, h_eq⟩
    let C' : Set ℝ := (fun c : ℝ => c - rho) '' C.val ∪ (fun c : ℝ => c + rho) '' C.val
    have hC'_cover : Metric.IsCover ε B C' := by
      intro x hx
      rcases h x hx with ⟨y, hyA, hxy⟩
      rcases C.property hyA with ⟨c, hc, hcy⟩
      have h_edist : edist y c ≤ (ε : ENNReal) := hcy
      have h_nndist : nndist y c ≤ ε := edist_le_coe.mp h_edist
      have h_dist_y_c : dist y c ≤ rho := by
        have h : dist y c ≤ (ε : ℝ) := dist_le_coe.mp h_nndist
        have h_rho : (ε : ℝ) = rho := by
          exact NNReal.coe_mk rho hrho.le
        rw [h_rho] at h
        exact h
      have h_abs_y_c : |y - c| ≤ rho := by
        simpa [Real.dist_eq] using h_dist_y_c
      have h_dist_x_c : |x - c| ≤ 2 * rho := by
        calc |x - c|
          = |(x - y) + (y - c)| := by ring_nf
        _ ≤ |x - y| + |y - c| := by
          have h_eq : (x - y) + (y - c) = x - c := by ring
          rw [h_eq]
          exact dist_triangle x y c
        _ ≤ delta + rho := by linarith
        _ ≤ 2 * rho := by linarith
      have h_x_bounds : c - 2 * rho ≤ x ∧ x ≤ c + 2 * rho := by
        have h1 : |x - c| ≤ 2 * rho := h_dist_x_c
        exact ⟨by linarith [abs_le.mp h1], by linarith [abs_le.mp h1]⟩
      by_cases h2 : x ≤ c
      · -- x ≤ c: use ball centered at c - rho
        have h3 : |x - (c - rho)| ≤ rho := by
          rw [abs_le]
          constructor <;> linarith
        refine ⟨c - rho, Or.inl ⟨c, hc, by ring⟩, ?_⟩
        have h11 : dist x (c - rho) ≤ (ε : ℝ) := by
          have h_rho : (ε : ℝ) = rho := by
            dsimp only [ε] <;> rfl
          rw [h_rho]
          have h_dist : dist x (c - rho) = |x - (c - rho)| := Real.dist_eq x (c - rho)
          rw [h_dist]
          exact h3
        have h12 : nndist x (c - rho) ≤ ε := dist_le_coe.mpr h11
        exact edist_le_coe.mpr h12
      · -- x > c: use ball centered at c + rho
        have h2' : c < x := by linarith
        have h3 : |x - (c + rho)| ≤ rho := by
          rw [abs_le]
          constructor <;> linarith
        refine ⟨c + rho, Or.inr ⟨c, hc, by ring⟩, ?_⟩
        have h11 : dist x (c + rho) ≤ (ε : ℝ) := by
          have h_rho : (ε : ℝ) = rho := by
            dsimp only [ε] <;> rfl
          rw [h_rho]
          have h_dist : dist x (c + rho) = |x - (c + rho)| := Real.dist_eq x (c + rho)
          rw [h_dist]
          exact h3
        have h12 : nndist x (c + rho) ≤ ε := dist_le_coe.mpr h11
        exact edist_le_coe.mpr h12
    have h_card : C'.encard ≤ 2 * C.val.encard := by
      have h1 : C'.encard ≤ ((fun c : ℝ => c - rho) '' C.val).encard + ((fun c : ℝ => c + rho) '' C.val).encard :=
        Set.encard_union_le _ _
      have h2 : ((fun c : ℝ => c - rho) '' C.val).encard ≤ C.val.encard := Set.encard_image_le _ _
      have h3 : ((fun c : ℝ => c + rho) '' C.val).encard ≤ C.val.encard := Set.encard_image_le _ _
      calc
        C'.encard ≤ _ + _ := h1
        _ ≤ C.val.encard + C.val.encard := by gcongr
        _ = 2 * C.val.encard := by ring
    have h_main : Metric.externalCoveringNumber ε B ≤ C'.encard :=
      hC'_cover.externalCoveringNumber_le_encard
    have h_final : C'.encard ≤ 2 * Metric.externalCoveringNumber ε A := by
      calc
        C'.encard ≤ 2 * C.val.encard := h_card
        _ = 2 * f C := by rfl
        _ = 2 * Metric.externalCoveringNumber ε A := by rw [h_eq, h_ext]
    exact h_main.trans h_final

/-- Perturbation lemma for `IsADSet1`: if every point of `E'` is within `δ`
of `E`, then `E'` inherits the AD bound with constant `8 * C`. -/
lemma IsADSet1.perturb_by_delta
    {E E' : Set ℝ} {δ α : ℝ} {C : ENNReal}
    (hE : IsADSet1 E δ α C)
    (h_close : ∀ x ∈ E', ∃ y ∈ E, |x - y| ≤ δ)
    (hE'_bounded : E' ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 E' δ α (8 * C) := by
  rcases hE with ⟨hδ_pos, hα_pos, hα_one, hC_one, hE_bounded, hcover⟩
  have hC8_one : (1 : ENNReal) ≤ 8 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : C ≤ 8 * C := le_mul_of_one_le_left' (by norm_num)
    exact h1.trans h2
  refine ⟨hδ_pos, hα_pos, hα_one, hC8_one, hE'_bounded, ?_⟩
  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  let ε : NNReal := ⟨rho, hrho⟩
  have hrho_pos : 0 < rho := by linarith
  set A : Set ℝ := E ∩ closedBall x (r + δ) with hA_def
  set B : Set ℝ := E' ∩ closedBall x r with hB_def
  have h_close' : ∀ z ∈ B, ∃ y ∈ A, |z - y| ≤ δ := by
    intro z hz
    have hz1 : z ∈ E' := hz.1
    have hz2 : z ∈ closedBall x r := hz.2
    rcases h_close z hz1 with ⟨y, hyE, hyz⟩
    have hyr : y ∈ closedBall x (r + δ) := by
      simp only [mem_closedBall, Real.dist_eq] at hz2 ⊢
      have h1 : |y - x| ≤ |y - z| + |z - x| := by
        have h2 : |y - x| = |(y - z) + (z - x)| := by ring_nf
        rw [h2]
        have h_eq : (y - z) + (z - x) = y - x := by ring
        rw [h_eq]
        exact dist_triangle y z x
      have h_yz : |y - z| ≤ δ := by
        have h_eq : |y - z| = |z - y| := by
          have h : y - z = -(z - y) := by ring
          rw [h, abs_neg]
        rw [h_eq]
        exact hyz
      have h_final : |y - x| ≤ r + δ := by
        calc |y - x| ≤ |y - z| + |z - x| := h1
             _ ≤ δ + r := by linarith
             _ = r + δ := by ring
      exact h_final
    exact ⟨y, ⟨hyE, hyr⟩, hyz⟩
  have h_thick : (Metric.externalCoveringNumber ε B : ENNReal) ≤
      2 * (Metric.externalCoveringNumber ε A : ENNReal) := by
    have h := externalCoveringNumber_thickening_two_mul_real
      (hrho := hrho_pos) (hdelta := hδ_pos.le) (hdelta_rho := hdelta_rho) h_close'
    exact_mod_cast h
  by_cases h_case : r + δ ≤ 1
  · -- Case 1: r + δ ≤ 1
    have h_rho_le_rpd : rho ≤ r + δ := by linarith
    have h_cover_A : (Metric.externalCoveringNumber ε A : ENNReal) ≤
        C * Kakeya.realRpowENN ((r + δ) / rho) α :=
      hcover rho hrho hdelta_rho hrho_one x (r + δ) h_rho_le_rpd h_case
    have h_ratio1 : (r + δ) / rho ≤ 2 * (r / rho) := by
      have h1 : r + δ ≤ 2 * r := by linarith
      have h2 : 0 ≤ rho := hrho_pos.le
      have h3 : (r + δ) / rho ≤ (2 * r) / rho := div_le_div_of_nonneg_right h1 h2
      have h4 : (2 * r) / rho = 2 * (r / rho) := by ring
      rw [h4] at h3
      exact h3
    have h_rpow1 : Kakeya.realRpowENN ((r + δ) / rho) α ≤
        Kakeya.realRpowENN (2 * (r / rho)) α := by
      apply ENNReal.ofReal_le_ofReal
      have hpos1 : 0 ≤ (r + δ) / rho := by
        have h1 : 0 < r + δ := by linarith
        have h2 : 0 < rho := hrho_pos
        exact div_nonneg h1.le h2.le
      have hpos2 : 0 ≤ 2 * (r / rho) := by
        have h1 : 0 ≤ r / rho := by
          have h1r : 0 ≤ r := by linarith
          exact div_nonneg h1r hrho_pos.le
        linarith
      exact Real.rpow_le_rpow hpos1 h_ratio1 hα_pos.le
    have h_rpow2 : Kakeya.realRpowENN (2 * (r / rho)) α =
        Kakeya.realRpowENN 2 α * Kakeya.realRpowENN (r / rho) α := by
      simp only [Kakeya.realRpowENN]
      have hpos1 : 0 ≤ (2 : ℝ) := by norm_num
      have hpos2 : 0 ≤ r / rho := by
        have h1 : 0 ≤ r := by linarith
        have h2 : 0 < rho := hrho_pos
        exact div_nonneg h1 h2.le
      have h_eq : Real.rpow (2 * (r / rho)) α = Real.rpow 2 α * Real.rpow (r / rho) α := by
        have h : (2 * (r / rho)) ^ α = (2 : ℝ) ^ α * (r / rho) ^ α := Real.mul_rpow hpos1 hpos2
        simpa using h
      rw [h_eq]
      have h_nonneg1 : 0 ≤ Real.rpow 2 α := Real.rpow_nonneg (by norm_num) α
      have h_nonneg2 : 0 ≤ Real.rpow (r / rho) α := Real.rpow_nonneg hpos2 α
      rw [ENNReal.ofReal_mul (hp := h_nonneg1)]
    have h_rpow3 : Kakeya.realRpowENN 2 α ≤ (2 : ENNReal) := by
      simp only [Kakeya.realRpowENN]
      have h : Real.rpow 2 α ≤ 2 := by
        have h9 : Real.rpow 2 α ≤ Real.rpow 2 (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_one
        simpa using h9
      have h10 : ENNReal.ofReal (Real.rpow 2 α) ≤ ENNReal.ofReal (2 : ℝ) := ENNReal.ofReal_le_ofReal h
      have h11 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by simp
      rw [h11] at h10
      exact h10
    calc
      (Metric.externalCoveringNumber ε B : ENNReal)
        ≤ 2 * (Metric.externalCoveringNumber ε A : ENNReal) := h_thick
      _ ≤ 2 * (C * Kakeya.realRpowENN ((r + δ) / rho) α) := by gcongr
      _ ≤ 2 * (C * Kakeya.realRpowENN (2 * (r / rho)) α) := by gcongr
      _ = 2 * (C * (Kakeya.realRpowENN 2 α * Kakeya.realRpowENN (r / rho) α)) := by
        rw [h_rpow2]
      _ = 2 * Kakeya.realRpowENN 2 α * (C * Kakeya.realRpowENN (r / rho) α) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ 2 * (2 : ENNReal) * (C * Kakeya.realRpowENN (r / rho) α) := by gcongr
      _ = 4 * C * Kakeya.realRpowENN (r / rho) α := by
        have h2 : (2 : ENNReal) * (2 : ENNReal) = (4 : ENNReal) := by norm_num
        rw [h2, mul_assoc]
      _ ≤ 8 * C * Kakeya.realRpowENN (r / rho) α := by
        have h4 : (4 : ENNReal) * C ≤ 8 * C := by
          have h5 : (4 : ENNReal) ≤ 8 := by norm_num
          have h6 : C * (4 : ENNReal) ≤ C * 8 := mul_le_mul_left' h5 C
          have h7 : (4 : ENNReal) * C = C * (4 : ENNReal) := by apply mul_comm
          have h8 : (8 : ENNReal) * C = C * (8 : ENNReal) := by apply mul_comm
          rw [h7, h8]
          exact h6
        gcongr
      _ = (8 * C) * Kakeya.realRpowENN (r / rho) α := by
        rw [mul_assoc]
  · -- Case 2: r + δ > 1
    have h_r_gt_half : 1 / 2 < r := by linarith
    let y1 : ℝ := x - (r + δ) + 1
    let y2 : ℝ := x + (r + δ) - 1
    have h_cover_interval : closedBall x (r + δ) ⊆ closedBall y1 1 ∪ closedBall y2 1 := by
      intro z hz
      simp only [mem_closedBall, Real.dist_eq] at hz
      have h1 : |z - x| ≤ r + δ := hz
      have h2 : x - (r + δ) ≤ z ∧ z ≤ x + (r + δ) := by
        exact ⟨by linarith [abs_le.mp h1], by linarith [abs_le.mp h1]⟩
      by_cases h3 : z ≤ x
      · left
        have h4 : |z - y1| ≤ 1 := by
          simp only [y1]
          rw [abs_le] <;> constructor <;> linarith [abs_le.mp h1]
        simpa [mem_closedBall, Real.dist_eq] using h4
      · right
        have h4 : |z - y2| ≤ 1 := by
          simp only [y2]
          rw [abs_le] <;> constructor <;> linarith [abs_le.mp h1]
        simpa [mem_closedBall, Real.dist_eq] using h4
    have hA_subset : A ⊆ (E ∩ closedBall y1 1) ∪ (E ∩ closedBall y2 1) := by
      intro z hz
      have hz1 : z ∈ E := hz.1
      have hz2 : z ∈ closedBall x (r + δ) := hz.2
      have hz3 : z ∈ closedBall y1 1 ∪ closedBall y2 1 := h_cover_interval hz2
      cases hz3 with
      | inl h => exact Or.inl ⟨hz1, h⟩
      | inr h => exact Or.inr ⟨hz1, h⟩
    have h_cover1 : (Metric.externalCoveringNumber ε (E ∩ closedBall y1 1) : ENNReal) ≤
        C * Kakeya.realRpowENN (1 / rho) α :=
      hcover rho hrho hdelta_rho hrho_one y1 1 (by linarith) (by norm_num)
    have h_cover2 : (Metric.externalCoveringNumber ε (E ∩ closedBall y2 1) : ENNReal) ≤
        C * Kakeya.realRpowENN (1 / rho) α :=
      hcover rho hrho hdelta_rho hrho_one y2 1 (by linarith) (by norm_num)
    have h_union : (Metric.externalCoveringNumber ε A : ENNReal) ≤
        (Metric.externalCoveringNumber ε (E ∩ closedBall y1 1) : ENNReal) +
        (Metric.externalCoveringNumber ε (E ∩ closedBall y2 1) : ENNReal) := by
      have h := externalCoveringNumber_union_le (ε := ε) (A := E ∩ closedBall y1 1) (B := E ∩ closedBall y2 1)
      have h' : Metric.externalCoveringNumber ε A ≤
          Metric.externalCoveringNumber ε ((E ∩ closedBall y1 1) ∪ (E ∩ closedBall y2 1)) :=
        Metric.externalCoveringNumber_mono_set hA_subset
      exact_mod_cast h'.trans h
    have h_ratio2 : Kakeya.realRpowENN (1 / rho) α ≤
        2 * Kakeya.realRpowENN (r / rho) α := by
      have hpos_r : 0 < r := by linarith
      have hpos_rho : 0 < rho := hrho_pos
      have h1 : 1 / rho = (r / rho) * (1 / r) := by
        field_simp [hpos_r.ne', hpos_rho.ne'] <;> ring
      rw [h1]
      have h2 : Kakeya.realRpowENN ((r / rho) * (1 / r)) α =
          Kakeya.realRpowENN (r / rho) α * Kakeya.realRpowENN (1 / r) α := by
        simp only [Kakeya.realRpowENN]
        have hpos1 : 0 ≤ r / rho := by positivity
        have hpos2 : 0 ≤ 1 / r := by positivity
        have h_eq : Real.rpow ((r / rho) * (1 / r)) α = Real.rpow (r / rho) α * Real.rpow (1 / r) α := by
          have h : ((r / rho) * (1 / r)) ^ α = (r / rho) ^ α * (1 / r) ^ α := Real.mul_rpow hpos1 hpos2
          simpa using h
        rw [h_eq]
        have h_nonneg1 : 0 ≤ Real.rpow (r / rho) α := Real.rpow_nonneg hpos1 α
        rw [ENNReal.ofReal_mul (hp := h_nonneg1)]
      rw [h2]
      have h3 : Kakeya.realRpowENN (1 / r) α ≤ (2 : ENNReal) := by
        simp only [Kakeya.realRpowENN]
        have h4 : 1 / r < 2 := by
          have h5 : 1 / 2 < r := h_r_gt_half
          have h6 : 0 < r := by linarith
          calc 1 / r < 1 / (1 / 2 : ℝ) := by gcongr
               _ = 2 := by norm_num
        have h7 : Real.rpow (1 / r) α ≤ 2 := by
          have h8 : 0 ≤ 1 / r := by positivity
          have h9 : Real.rpow (1 / r) α ≤ Real.rpow 2 α :=
            Real.rpow_le_rpow h8 (by linarith) hα_pos.le
          have h10 : Real.rpow 2 α ≤ 2 := by
            have h11 : Real.rpow 2 α ≤ Real.rpow 2 (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_one
            simpa using h11
          exact h9.trans h10
        exact ENNReal.ofReal_le_ofReal h7 |>.trans (by simp)
      calc
        Kakeya.realRpowENN (r / rho) α * Kakeya.realRpowENN (1 / r) α
          ≤ Kakeya.realRpowENN (r / rho) α * (2 : ENNReal) := by gcongr
        _ = 2 * Kakeya.realRpowENN (r / rho) α := by ring
    calc
      (Metric.externalCoveringNumber ε B : ENNReal)
        ≤ 2 * (Metric.externalCoveringNumber ε A : ENNReal) := h_thick
      _ ≤ 2 * ((Metric.externalCoveringNumber ε (E ∩ closedBall y1 1) : ENNReal) +
                 (Metric.externalCoveringNumber ε (E ∩ closedBall y2 1) : ENNReal)) := by
        gcongr
      _ ≤ 2 * (C * Kakeya.realRpowENN (1 / rho) α + C * Kakeya.realRpowENN (1 / rho) α) := by
        gcongr <;> linarith
      _ = 2 * (2 * (C * Kakeya.realRpowENN (1 / rho) α)) := by ring
      _ = 4 * (C * Kakeya.realRpowENN (1 / rho) α) := by ring
      _ ≤ 4 * (C * (2 * Kakeya.realRpowENN (r / rho) α)) := by gcongr
      _ = 8 * C * Kakeya.realRpowENN (r / rho) α := by ring
      _ = (8 * C) * Kakeya.realRpowENN (r / rho) α := by ring

end Kakeya.Assouad

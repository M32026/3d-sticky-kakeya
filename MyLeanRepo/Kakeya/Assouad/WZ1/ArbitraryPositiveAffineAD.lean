import MyLeanRepo.Kakeya.Assouad.WZ1.ADAffineThickeningTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers

/-!
# Arbitrary positive affine transport for bounded one-dimensional AD sets

This is the similarity-scale transport used by the Lemma-23 dot-difference
normalization.  The affine factor may be larger than four; intersecting the
image with the fixed paper window costs only the explicit factor five.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

private lemma arbitraryAffine_externalCoveringNumber_union_le
    {X : Type*} [PseudoMetricSpace X]
    {A B : Set X} {epsilon : NNReal} :
    (Metric.externalCoveringNumber epsilon (A ∪ B) : ENNReal) ≤
      (Metric.externalCoveringNumber epsilon A : ENNReal) +
        (Metric.externalCoveringNumber epsilon B : ENNReal) := by
  exact_mod_cast externalCoveringNumber_union_le

/-- Variant of `affine_small` for `E ⊆ [-4,4]` with constant `5*C`.

Covers `E` by 4 unit balls (when `rho ≤ 1`) or 5 balls of radius `rho`
(when `rho > 1`), summing the AD bounds using union subadditivity. -/
lemma IsADSet1.affine_image_arbitrary_positive
    {E : Set ℝ} {δ α : ℝ} {C : ENNReal} {a b : ℝ}
    (ha_pos : 0 < a)
    (hE : IsADSet1 E δ α C)
    (hE_small : E ⊆ Set.Icc (-4 : ℝ) 4)
    (_hδ_a : a * δ ≤ 1) :
    IsADSet1 (((fun x : ℝ => a * x + b) '' E) ∩ Set.Icc (-4 : ℝ) 4) (a * δ) α (5 * C) := by
  rcases hE with ⟨hδ, hα, hα_one, hC, _hE_bounded, hcover⟩
  let E' := ((fun x : ℝ => a * x + b) '' E) ∩ Set.Icc (-4 : ℝ) 4
  have hE'_bounded : E' ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro x hx; exact hx.2
  refine ⟨by positivity, hα, hα_one, ?_, hE'_bounded, ?_⟩
  · have h : (1 : ENNReal) ≤ C := hC
    have h' : (1 : ENNReal) ≤ 5 := by norm_num
    calc (1 : ENNReal)
      ≤ 5 := h'
      _ = 5 * 1 := by simp
      _ ≤ 5 * C := by gcongr
  intro rho' hrho' hdelta'_rho hrho'_one x' r' hrho'_r hr'_one
  let rho : ℝ := rho' / a
  let x : ℝ := (x' - b) / a
  let r : ℝ := r' / a
  have hδ_rho : δ ≤ rho := by
    have h : a * δ ≤ rho' := hdelta'_rho
    calc δ = (a * δ) / a := by field_simp [ha_pos.ne']
      _ ≤ rho' / a := by gcongr
  have hrho_r : rho ≤ r := by dsimp only [rho, r]; gcongr
  have h_rho'_eq : a * rho = rho' := by
    dsimp only [rho]; field_simp [ha_pos.ne']
  have hrho_nonneg : 0 ≤ rho := by positivity
  let eps_nn : NNReal := ⟨rho, hrho_nonneg⟩
  let rho'_nn : NNReal := ⟨rho', hrho'⟩
  let T : ℝ → ℝ := fun v => v + b
  let D : ℝ → ℝ := fun u => a * u
  let f : ℝ → ℝ := fun u => a * u + b
  have hT_isom : Isometry T := isometry_add_right b
  have hT_surj : Function.Surjective T := by
    intro y; exact ⟨y - b, by ring⟩
  have h_f_image : f '' E = T '' (D '' E) := by
    ext z; simp only [Set.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨D u, ⟨u, hu, rfl⟩, by simp [f, T, D]⟩
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, by simp [f, T, D]⟩
  have h_ball_T : T '' Metric.closedBall (x' - b) r' = Metric.closedBall x' r' := by
    ext z; simp only [T, Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa [Real.dist_eq] using hy
    · intro hz; refine ⟨z - b, ?_, by ring⟩; simpa [Real.dist_eq] using hz
  have h_T_inter :
      T '' (D '' E ∩ Metric.closedBall (x' - b) r') =
        T '' (D '' E) ∩ Metric.closedBall x' r' := by
    rw [Set.image_inter hT_isom.injective, h_ball_T]
  have h_image_inter :
      f '' E ∩ Metric.closedBall x' r' =
        T '' (D '' E ∩ Metric.closedBall (x' - b) r') := by
    rw [h_f_image]; exact h_T_inter.symm
  have h_scale_x : a * x = x' - b := by
    dsimp only [x]; field_simp [ha_pos.ne']
  have h_scale_r : a * r = r' := by
    dsimp only [r]; field_simp [ha_pos.ne']
  have h_dilation_inter :
      D '' E ∩ Metric.closedBall (x' - b) r' = D '' (E ∩ Metric.closedBall x r) := by
    have h := dilation_inter_closedBall (a := a) (ha := ha_pos) (S := E) (x := x) (r := r)
    rw [h_scale_x, h_scale_r] at h
    exact h.symm
  let a_eps_nn : NNReal := ⟨a * (eps_nn : ℝ), by positivity⟩
  have h6 : rho'_nn = a_eps_nn := by
    apply NNReal.coe_injective
    have h_coe : (a_eps_nn : ℝ) = a * (eps_nn : ℝ) := by rfl
    rw [h_coe]
    have h_eps : (eps_nn : ℝ) = rho := by rfl
    rw [h_eps, h_rho'_eq] <;> rfl
  have h_dilation_cover :
      Metric.externalCoveringNumber a_eps_nn (D '' (E ∩ Metric.closedBall x r)) =
        Metric.externalCoveringNumber eps_nn (E ∩ Metric.closedBall x r) :=
    externalCoveringNumber_dilation_eq (a := a) (ha := ha_pos) (ε := eps_nn)
  have h_dil :
      Metric.externalCoveringNumber rho'_nn (D '' (E ∩ Metric.closedBall x r)) =
        Metric.externalCoveringNumber eps_nn (E ∩ Metric.closedBall x r) := by
    rw [h6]; exact h_dilation_cover
  have h_isometry_cover :
      Metric.externalCoveringNumber rho'_nn (T '' (D '' E ∩ Metric.closedBall (x' - b) r')) =
        Metric.externalCoveringNumber rho'_nn (D '' E ∩ Metric.closedBall (x' - b) r') :=
    Isometry.externalCoveringNumber_image hT_isom hT_surj
      (A := D '' E ∩ Metric.closedBall (x' - b) r') (ε := rho'_nn)
  have h_main_cover :
      Metric.externalCoveringNumber rho'_nn (f '' E ∩ Metric.closedBall x' r') =
        Metric.externalCoveringNumber eps_nn (E ∩ Metric.closedBall x r) := by
    rw [h_image_inter, h_isometry_cover, h_dilation_inter, h_dil]
  have h_sub : E' ∩ Metric.closedBall x' r' ⊆ f '' E ∩ Metric.closedBall x' r' := by
    intro y hy; exact ⟨hy.1.1, hy.2⟩
  have h_mono : (Metric.externalCoveringNumber rho'_nn (E' ∩ Metric.closedBall x' r') : ENNReal) ≤
      (Metric.externalCoveringNumber rho'_nn (f '' E ∩ Metric.closedBall x' r') : ENNReal) := by
    simpa using Metric.externalCoveringNumber_mono_set h_sub
  rw [h_main_cover] at h_mono
  have h_eps_eq : eps_nn = (⟨rho, by positivity⟩ : NNReal) := by
    apply NNReal.coe_injective; rfl
  have h_ratio : r / rho = r' / rho' := by
    dsimp only [r, rho]; field_simp [ha_pos.ne']
  let C' : ENNReal := 5 * C
  have h_goal : (Metric.externalCoveringNumber eps_nn (E ∩ Metric.closedBall x r) : ENNReal) ≤
      C' * Kakeya.realRpowENN (r' / rho') α := by
    by_cases hr_one : r ≤ 1
    · -- Case 1: r ≤ 1, use AD directly
      have hrho_one : rho ≤ 1 := by
        calc rho ≤ r := hrho_r
          _ ≤ 1 := hr_one
      have h1 := hcover rho hrho_nonneg hδ_rho hrho_one x r hrho_r hr_one
      rw [←h_eps_eq] at h1
      rw [h_ratio] at h1
      have h_final : C * Kakeya.realRpowENN (r' / rho') α ≤ C' * Kakeya.realRpowENN (r' / rho') α := by
        dsimp only [C']
        have h4 : C ≤ 5 * C := by
          calc C = 1 * C := by simp
            _ ≤ 5 * C := by gcongr <;> norm_num
        exact mul_le_mul_right' h4 (Kakeya.realRpowENN (r' / rho') α)
      exact h1.trans h_final
    · -- Case 2: r > 1
      have hr_gt_one : 1 < r := by linarith
      have h9 : (Metric.externalCoveringNumber eps_nn (E ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber eps_nn E : ENNReal) := by
        simpa using Metric.externalCoveringNumber_mono_set (Set.inter_subset_left)
      by_cases hrho_one : rho ≤ 1
      · -- Subcase 2a: rho ≤ 1, cover E by 4 unit balls and sum AD bounds
        let A1 := E ∩ Metric.closedBall (-3 : ℝ) 1
        let A2 := E ∩ Metric.closedBall (-1 : ℝ) 1
        let A3 := E ∩ Metric.closedBall (1 : ℝ) 1
        let A4 := E ∩ Metric.closedBall (3 : ℝ) 1
        let U34 := A3 ∪ A4
        let U234 := A2 ∪ U34
        have hcover4 : E ⊆ A1 ∪ U234 := by
          intro y hy
          have h1 : -4 ≤ y := (hE_small hy).1
          have h2 : y ≤ 4 := (hE_small hy).2
          have h_main : y ∈ A1 ∨ y ∈ A2 ∨ y ∈ A3 ∨ y ∈ A4 := by
            by_cases h3 : y ≤ -2
            · have h4 : dist y (-3 : ℝ) ≤ 1 := by
                rw [Real.dist_eq]; apply abs_le.mpr; constructor <;> linarith
              exact Or.inl ⟨hy, h4⟩
            · by_cases h4 : y ≤ 0
              · have h5 : dist y (-1 : ℝ) ≤ 1 := by
                  rw [Real.dist_eq]; apply abs_le.mpr; constructor <;> linarith
                exact Or.inr (Or.inl ⟨hy, h5⟩)
              · by_cases h5 : y ≤ 2
                · have h6 : dist y (1 : ℝ) ≤ 1 := by
                    rw [Real.dist_eq]; apply abs_le.mpr; constructor <;> linarith
                  exact Or.inr (Or.inr (Or.inl ⟨hy, h6⟩))
                · have h7 : dist y (3 : ℝ) ≤ 1 := by
                    rw [Real.dist_eq]; apply abs_le.mpr; constructor <;> linarith
                  exact Or.inr (Or.inr (Or.inr ⟨hy, h7⟩))
          rcases h_main with (h | h | h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        have hB1 : (Metric.externalCoveringNumber eps_nn A1 : ENNReal) ≤ C * Kakeya.realRpowENN (1 / rho) α := by
          have h := hcover rho hrho_nonneg hδ_rho hrho_one (-3) 1 (by linarith) (by norm_num)
          rw [←h_eps_eq] at h; exact h
        have hB2 : (Metric.externalCoveringNumber eps_nn A2 : ENNReal) ≤ C * Kakeya.realRpowENN (1 / rho) α := by
          have h := hcover rho hrho_nonneg hδ_rho hrho_one (-1) 1 (by linarith) (by norm_num)
          rw [←h_eps_eq] at h; exact h
        have hB3 : (Metric.externalCoveringNumber eps_nn A3 : ENNReal) ≤ C * Kakeya.realRpowENN (1 / rho) α := by
          have h := hcover rho hrho_nonneg hδ_rho hrho_one 1 1 (by linarith) (by norm_num)
          rw [←h_eps_eq] at h; exact h
        have hB4 : (Metric.externalCoveringNumber eps_nn A4 : ENNReal) ≤ C * Kakeya.realRpowENN (1 / rho) α := by
          have h := hcover rho hrho_nonneg hδ_rho hrho_one 3 1 (by linarith) (by norm_num)
          rw [←h_eps_eq] at h; exact h
        have hU34 : (Metric.externalCoveringNumber eps_nn U34 : ENNReal) ≤
            (Metric.externalCoveringNumber eps_nn A3 : ENNReal) + (Metric.externalCoveringNumber eps_nn A4 : ENNReal) :=
          arbitraryAffine_externalCoveringNumber_union_le (A := A3) (B := A4)
        have hU234 : (Metric.externalCoveringNumber eps_nn U234 : ENNReal) ≤
            (Metric.externalCoveringNumber eps_nn A2 : ENNReal) + (Metric.externalCoveringNumber eps_nn U34 : ENNReal) :=
          arbitraryAffine_externalCoveringNumber_union_le (A := A2) (B := U34)
        have hU1234 : (Metric.externalCoveringNumber eps_nn (A1 ∪ U234) : ENNReal) ≤
            (Metric.externalCoveringNumber eps_nn A1 : ENNReal) + (Metric.externalCoveringNumber eps_nn U234 : ENNReal) :=
          arbitraryAffine_externalCoveringNumber_union_le (A := A1) (B := U234)
        have h_sum4 : (Metric.externalCoveringNumber eps_nn E : ENNReal) ≤
            4 * C * Kakeya.realRpowENN (1 / rho) α := by
          calc
            (Metric.externalCoveringNumber eps_nn E : ENNReal)
              ≤ (Metric.externalCoveringNumber eps_nn (A1 ∪ U234) : ENNReal) := by
                simpa using Metric.externalCoveringNumber_mono_set hcover4
            _ ≤ (Metric.externalCoveringNumber eps_nn A1 : ENNReal) +
                   (Metric.externalCoveringNumber eps_nn U234 : ENNReal) := hU1234
            _ ≤ (Metric.externalCoveringNumber eps_nn A1 : ENNReal) +
                   (Metric.externalCoveringNumber eps_nn A2 : ENNReal) +
                   (Metric.externalCoveringNumber eps_nn U34 : ENNReal) := by
              have h' : (Metric.externalCoveringNumber eps_nn U234 : ENNReal) ≤
                  (Metric.externalCoveringNumber eps_nn A2 : ENNReal) +
                  (Metric.externalCoveringNumber eps_nn U34 : ENNReal) := hU234
              calc (Metric.externalCoveringNumber eps_nn A1 : ENNReal) + (Metric.externalCoveringNumber eps_nn U234 : ENNReal)
                  ≤ (Metric.externalCoveringNumber eps_nn A1 : ENNReal) + ((Metric.externalCoveringNumber eps_nn A2 : ENNReal) + (Metric.externalCoveringNumber eps_nn U34 : ENNReal)) := by gcongr
                _ = (Metric.externalCoveringNumber eps_nn A1 : ENNReal) + (Metric.externalCoveringNumber eps_nn A2 : ENNReal) + (Metric.externalCoveringNumber eps_nn U34 : ENNReal) := by abel
            _ ≤ (Metric.externalCoveringNumber eps_nn A1 : ENNReal) +
                   (Metric.externalCoveringNumber eps_nn A2 : ENNReal) +
                   (Metric.externalCoveringNumber eps_nn A3 : ENNReal) +
                   (Metric.externalCoveringNumber eps_nn A4 : ENNReal) := by
              have h' : (Metric.externalCoveringNumber eps_nn U34 : ENNReal) ≤
                  (Metric.externalCoveringNumber eps_nn A3 : ENNReal) +
                  (Metric.externalCoveringNumber eps_nn A4 : ENNReal) := hU34
              calc (Metric.externalCoveringNumber eps_nn A1 : ENNReal) + (Metric.externalCoveringNumber eps_nn A2 : ENNReal) + (Metric.externalCoveringNumber eps_nn U34 : ENNReal)
                  ≤ (Metric.externalCoveringNumber eps_nn A1 : ENNReal) + (Metric.externalCoveringNumber eps_nn A2 : ENNReal) + ((Metric.externalCoveringNumber eps_nn A3 : ENNReal) + (Metric.externalCoveringNumber eps_nn A4 : ENNReal)) := by gcongr
                _ = (Metric.externalCoveringNumber eps_nn A1 : ENNReal) + (Metric.externalCoveringNumber eps_nn A2 : ENNReal) + (Metric.externalCoveringNumber eps_nn A3 : ENNReal) + (Metric.externalCoveringNumber eps_nn A4 : ENNReal) := by abel
            _ ≤ 4 * (C * Kakeya.realRpowENN (1 / rho) α) := by
              have h_all : (Metric.externalCoveringNumber eps_nn A1 : ENNReal) +
                  (Metric.externalCoveringNumber eps_nn A2 : ENNReal) +
                  (Metric.externalCoveringNumber eps_nn A3 : ENNReal) +
                  (Metric.externalCoveringNumber eps_nn A4 : ENNReal) ≤
                  4 * (C * Kakeya.realRpowENN (1 / rho) α) := by
                calc
                  _ = (Metric.externalCoveringNumber eps_nn A1 : ENNReal) +
                        (Metric.externalCoveringNumber eps_nn A2 : ENNReal) +
                        (Metric.externalCoveringNumber eps_nn A3 : ENNReal) +
                        (Metric.externalCoveringNumber eps_nn A4 : ENNReal) := by rfl
                  _ ≤ (C * Kakeya.realRpowENN (1 / rho) α) +
                        (C * Kakeya.realRpowENN (1 / rho) α) +
                        (C * Kakeya.realRpowENN (1 / rho) α) +
                        (C * Kakeya.realRpowENN (1 / rho) α) := by gcongr
                  _ = 4 * (C * Kakeya.realRpowENN (1 / rho) α) := by ring
              exact h_all
            _ = 4 * C * Kakeya.realRpowENN (1 / rho) α := by ring
        have h14 : a ≤ r' := by
          have h16 : 1 < r' / a := by dsimp only [r] at hr_gt_one; exact hr_gt_one
          have h17 : a < r' := by
            calc a = a * 1 := by ring
              _ < a * (r' / a) := mul_lt_mul_of_pos_left h16 ha_pos
              _ = r' := by field_simp [ha_pos.ne']
          exact h17.le
        have h15 : Kakeya.realRpowENN (a / rho') α ≤ Kakeya.realRpowENN (r' / rho') α := by
          apply ENNReal.ofReal_le_ofReal
          exact Real.rpow_le_rpow (by positivity) (by gcongr) hα.le
        have h13 : (1 : ℝ) / rho = a / rho' := by
          dsimp only [rho]; field_simp [ha_pos.ne']
        rw [h13] at h_sum4
        have h10 : 4 * C ≤ 5 * C := by
          have h11 : (4 : ENNReal) ≤ 5 := by norm_num
          exact mul_le_mul_right' h11 C
        calc
          (Metric.externalCoveringNumber eps_nn (E ∩ Metric.closedBall x r) : ENNReal)
            ≤ (Metric.externalCoveringNumber eps_nn E : ENNReal) := h9
          _ ≤ 4 * C * Kakeya.realRpowENN (a / rho') α := h_sum4
          _ ≤ 5 * C * Kakeya.realRpowENN (r' / rho') α := by
            have h16 : (4 * C) * Kakeya.realRpowENN (a / rho') α ≤
                (4 * C) * Kakeya.realRpowENN (r' / rho') α := by gcongr
            have h17 : (4 * C) * Kakeya.realRpowENN (r' / rho') α ≤
                (5 * C) * Kakeya.realRpowENN (r' / rho') α := by gcongr
            exact le_trans h16 h17
      · -- Subcase 2b: rho > 1, cover E by 5 balls of radius rho
        have hrho_gt_one : 1 < rho := by linarith
        let centers5 : Set ℝ := {-4, -2, 0, 2, 4}
        have hcover5 : E ⊆ ⋃ c ∈ centers5, Metric.closedBall c rho := by
          intro y hy
          have h1 : -4 ≤ y := (hE_small hy).1
          have h2 : y ≤ 4 := (hE_small hy).2
          have h3 : ∃ (c : ℝ), c ∈ centers5 ∧ dist y c ≤ rho := by
            by_cases h4 : y ≤ -3
            · have h_nonneg : 0 ≤ y - (-4 : ℝ) := by linarith
              refine ⟨-4, by simp [centers5], ?_⟩
              rw [Real.dist_eq, abs_of_nonneg h_nonneg] <;> linarith
            · by_cases h5 : y ≤ -1
              · refine ⟨-2, by simp [centers5], ?_⟩
                rw [Real.dist_eq, abs_le] <;> constructor <;> linarith
              · by_cases h6 : y ≤ 1
                · refine ⟨0, by simp [centers5], ?_⟩
                  rw [Real.dist_eq, abs_le] <;> constructor <;> linarith
                · by_cases h7 : y ≤ 3
                  · refine ⟨2, by simp [centers5], ?_⟩
                    rw [Real.dist_eq, abs_le] <;> constructor <;> linarith
                  · have h_nonpos : y - (4 : ℝ) ≤ 0 := by linarith
                    refine ⟨4, by simp [centers5], ?_⟩
                    rw [Real.dist_eq, abs_of_nonpos h_nonpos] <;> linarith
          rcases h3 with ⟨c, hc, hdist⟩
          exact Set.mem_iUnion₂.mpr ⟨c, hc, hdist⟩
        have h_rad : (eps_nn : ℝ) = rho := rfl
        have hcover5' : E ⊆ ⋃ c ∈ centers5, Metric.closedBall c eps_nn := by
          have h_eq : (⋃ c ∈ centers5, Metric.closedBall c eps_nn) = ⋃ c ∈ centers5, Metric.closedBall c rho := by
            ext z; simp only [Set.mem_iUnion₂, Metric.mem_closedBall]
            <;> congr! <;> exact h_rad
          rw [h_eq]; exact hcover5
        have h_iscover : Metric.IsCover eps_nn E centers5 := by
          rw [Metric.isCover_iff_subset_iUnion_closedBall]; exact hcover5'
        have h_encard : centers5.encard ≤ 5 := by
          have h_eq : centers5 = (↑({-4, -2, 0, 2, 4} : Finset ℝ) : Set ℝ) := by
            ext z; simp [centers5] <;> tauto
          rw [h_eq]
          rw [Set.encard_coe_eq_coe_finsetCard]
          have hcard : ({-4, -2, 0, 2, 4} : Finset ℝ).card ≤ 5 := by
            have h_eq2 : ({-4, -2, 0, 2, 4} : Finset ℝ) =
                (Finset.range 5).image (fun n : ℕ => (n : ℝ) * 2 - 4) := by
              ext z
              simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range, Finset.mem_image]
              constructor
              · rintro (rfl | rfl | rfl | rfl | rfl)
                · exact ⟨0, by norm_num, by norm_num⟩
                · exact ⟨1, by norm_num, by norm_num⟩
                · exact ⟨2, by norm_num, by norm_num⟩
                · exact ⟨3, by norm_num, by norm_num⟩
                · exact ⟨4, by norm_num, by norm_num⟩
              · rintro ⟨n, hn, rfl⟩
                interval_cases n <;> norm_num
            rw [h_eq2]
            exact Finset.card_image_le.trans (by simp [Finset.card_range])
          exact_mod_cast hcard
        have h5 : (Metric.externalCoveringNumber eps_nn E : ENNReal) ≤ 5 := by
          have h1 : Metric.externalCoveringNumber eps_nn E ≤ centers5.encard :=
            h_iscover.externalCoveringNumber_le_encard
          have h2 : (Metric.externalCoveringNumber eps_nn E : ENNReal) ≤ (centers5.encard : ENNReal) := by
            exact_mod_cast h1
          have h3 : (centers5.encard : ENNReal) ≤ (5 : ENNReal) := by
            have h4 : centers5.encard ≤ (5 : ℕ∞) := h_encard
            exact_mod_cast h4
          exact le_trans h2 h3
        have hrho'_pos : 0 < rho' := by
          have h_pos : 0 < a * δ := mul_pos ha_pos hδ
          linarith
        have h21 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r' / rho') α := by
          have h20 : 1 ≤ r' / rho' := (one_le_div hrho'_pos).mpr hrho'_r
          have h : Real.rpow 1 α ≤ Real.rpow (r' / rho') α :=
            Real.rpow_le_rpow (by norm_num) h20 hα.le
          have h2 : Real.rpow 1 α = 1 := by simp
          have h3 : (1 : ℝ) ≤ Real.rpow (r' / rho') α := by linarith
          have h4 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow (r' / rho') α) :=
            ENNReal.ofReal_le_ofReal h3
          have h5 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
          rw [h5]; exact h4
        have hC5 : (5 : ENNReal) ≤ C' := by
          dsimp only [C']
          have h6 : (1 : ENNReal) ≤ C := hC
          calc (5 : ENNReal) = 5 * 1 := by simp
            _ ≤ 5 * C := by gcongr
        have h19 : (5 : ENNReal) ≤ C' * Kakeya.realRpowENN (r' / rho') α := by
          calc (5 : ENNReal)
              ≤ C' := hC5
            _ = C' * 1 := by simp
            _ ≤ C' * Kakeya.realRpowENN (r' / rho') α := by gcongr
        calc
          (Metric.externalCoveringNumber eps_nn (E ∩ Metric.closedBall x r) : ENNReal)
            ≤ (Metric.externalCoveringNumber eps_nn E : ENNReal) := h9
          _ ≤ 5 := h5
          _ ≤ C' * Kakeya.realRpowENN (r' / rho') α := h19
  exact h_mono.trans h_goal

end Kakeya.Assouad

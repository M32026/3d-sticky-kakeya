import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.NonConcentrationToThinTubes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# WZ1 Lemma 44: direct thin-tubes bound for large ζ

When `ζ ≥ 1/4` (or the heavy threshold falls below `δ`), the line
non-concentration bound and the trivial `|G₂|` bound together cover every
radius `r ≥ δ` with no deletion needed.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open scoped ENNReal

/-- Algebraic core: for `ζ ≥ 1/4` and `r < δ^{12α/ζ+4λ}`,
the non-concentration bound is at most the final thin-tubes bound. -/
lemma quarter_nc_bound
    {delta lambda zeta alpha : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (hzeta_ge : zeta ≥ 1 / 4)
    (r : ℝ) (hr_pos : 0 < r)
    (h_r_lt_T : r < Real.rpow delta (12 * alpha / zeta + 4 * lambda)) :
    Real.rpow (Real.rpow delta (-lambda) * r) zeta ≤
    Real.rpow delta (-3 * alpha / zeta - lambda) * Real.rpow r (1 / 4 : ℝ) := by
  by_cases h_eq : zeta = 1 / 4
  · -- Case ζ = 1/4
    have hz : zeta = 1 / 4 := h_eq
    have h1 : 0 ≤ Real.rpow delta (-lambda) := le_of_lt (Real.rpow_pos_of_pos hdelta _)
    have h2 : 0 ≤ r := by positivity
    have h3 : Real.rpow (Real.rpow delta (-lambda) * r) zeta =
        Real.rpow (Real.rpow delta (-lambda)) zeta * Real.rpow r zeta :=
      Real.mul_rpow h1 h2
    rw [h3, hz]
    have h41 : Real.rpow (Real.rpow delta (-lambda)) (1 / 4 : ℝ) =
        Real.rpow delta ((-lambda) * (1 / 4 : ℝ)) :=
      (Real.rpow_mul (show 0 ≤ delta by linarith) (-lambda) (1 / 4 : ℝ)).symm
    have h42 : (-lambda) * (1 / 4 : ℝ) = -lambda / 4 := by ring
    rw [h41, h42]
    have h5 : Real.rpow delta (-lambda / 4) ≤ Real.rpow delta (-12 * alpha - lambda) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1.le (by linarith)
    have h6 : 0 ≤ Real.rpow r (1 / 4 : ℝ) := Real.rpow_nonneg hr_pos.le (1 / 4 : ℝ)
    have h7 : (-12 * alpha - lambda : ℝ) = -3 * alpha / (1 / 4 : ℝ) - lambda := by ring
    rw [h7] at h5
    exact mul_le_mul_of_nonneg_right h5 h6
  · -- Case ζ > 1/4
    have hzeta_gt : 1 / 4 < zeta := by
      exact lt_of_le_of_ne hzeta_ge (Ne.symm h_eq)
    set S : ℝ := 12 * alpha / zeta + 4 * lambda with hS
    set E : ℝ := lambda * (zeta - 1) - 3 * alpha / zeta with hE
    have h_exp_pos : 0 < zeta - 1 / 4 := by linarith
    have h_pos : 0 < 12 * alpha + 3 * lambda * zeta := by positivity
    have hS_gt_E : S * (zeta - 1 / 4) > E := by
      have h : S * (zeta - 1 / 4) - E = 12 * alpha + 3 * lambda * zeta := by
        dsimp only [S, E]
        field_simp [hzeta.ne']
        ring
      linarith [h_pos, h]
    have h1 : Real.rpow r (zeta - 1 / 4) < Real.rpow delta E := by
      have h2 : Real.rpow r (zeta - 1 / 4) <
          Real.rpow (Real.rpow delta S) (zeta - 1 / 4) :=
        Real.rpow_lt_rpow (by linarith) h_r_lt_T h_exp_pos
      have h3 : Real.rpow (Real.rpow delta S) (zeta - 1 / 4) =
          Real.rpow delta (S * (zeta - 1 / 4)) :=
        (Real.rpow_mul (show 0 ≤ delta by linarith) S (zeta - 1 / 4)).symm
      rw [h3] at h2
      have h4 : Real.rpow delta (S * (zeta - 1 / 4)) < Real.rpow delta E :=
        Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 hS_gt_E
      exact lt_trans h2 h4
    have h_nonneg1 : 0 ≤ Real.rpow delta (-lambda) := le_of_lt (Real.rpow_pos_of_pos hdelta _)
    have h_nonneg2 : 0 ≤ r := by positivity
    have h5 : Real.rpow (Real.rpow delta (-lambda) * r) zeta =
        Real.rpow (Real.rpow delta (-lambda)) zeta * Real.rpow r zeta :=
      Real.mul_rpow h_nonneg1 h_nonneg2
    have h5b : Real.rpow (Real.rpow delta (-lambda)) zeta =
        Real.rpow delta (-lambda * zeta) :=
      (Real.rpow_mul (show 0 ≤ delta by linarith) (-lambda) zeta).symm
    rw [h5, h5b]
    have h6 : Real.rpow r zeta =
        Real.rpow r (1 / 4 : ℝ) * Real.rpow r (zeta - 1 / 4) := by
      have h61 : Real.rpow r ((1 / 4 : ℝ) + (zeta - 1 / 4)) =
          Real.rpow r (1 / 4 : ℝ) * Real.rpow r (zeta - 1 / 4) :=
        Real.rpow_add hr_pos (1 / 4 : ℝ) (zeta - 1 / 4)
      have h62 : (1 / 4 : ℝ) + (zeta - 1 / 4) = zeta := by ring
      rw [h62] at h61
      exact h61
    rw [h6]
    have h7 : Real.rpow delta (-lambda * zeta) * Real.rpow r (zeta - 1 / 4) ≤
        Real.rpow delta (-3 * alpha / zeta - lambda) := by
      have h_pos2 : 0 < Real.rpow delta (-lambda * zeta) := Real.rpow_pos_of_pos hdelta _
      have h8 : Real.rpow delta (-lambda * zeta) * Real.rpow r (zeta - 1 / 4) <
          Real.rpow delta (-lambda * zeta) * Real.rpow delta E :=
        mul_lt_mul_of_pos_left h1 h_pos2
      have h9 : Real.rpow delta (-lambda * zeta) * Real.rpow delta E =
          Real.rpow delta (-lambda * zeta + E) :=
        (Real.rpow_add hdelta (-lambda * zeta) E).symm
      rw [h9] at h8
      have h10 : -lambda * zeta + E = -3 * alpha / zeta - lambda := by
        simp [hE]
        ring
      rw [h10] at h8
      exact le_of_lt h8
    calc
      Real.rpow delta (-lambda * zeta) *
          (Real.rpow r (1 / 4 : ℝ) * Real.rpow r (zeta - 1 / 4))
        = Real.rpow r (1 / 4 : ℝ) *
          (Real.rpow delta (-lambda * zeta) * Real.rpow r (zeta - 1 / 4)) := by ring
      _ ≤ Real.rpow r (1 / 4 : ℝ) * Real.rpow delta (-3 * alpha / zeta - lambda) := by
        exact mul_le_mul_of_nonneg_left h7 (Real.rpow_nonneg hr_pos.le _)
      _ = Real.rpow delta (-3 * alpha / zeta - lambda) * Real.rpow r (1 / 4 : ℝ) := by ring

/-- Direct thin-tubes construction when `ζ ≥ 1/4` or the heavy threshold
is at or below `δ`.  Uses `E = G₁ ×ˢ G₂` (zero deletion). -/
lemma wz1_quarter_direct_bound
    {delta lambda zeta alpha : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    {G₁ G₂ : DiscreteSet 2}
    (_hG1ne : G₁.Nonempty) (_hG2ne : G₂.Nonempty)
    (hNonConc : WZ1LineNonConcentration delta lambda zeta G₂)
    (h_main : zeta ≥ 1 / 4 ∨ 12 * alpha / zeta + 4 * lambda ≥ 1) :
    HasDiscreteThinTubes delta (1 / 4)
      (Real.rpow delta (-3 * alpha / zeta - lambda))
      (Real.rpow delta alpha) G₁ G₂ := by
  set K_final : ℝ := Real.rpow delta (-3 * alpha / zeta - lambda) with hK_def
  set c : ℝ := Real.rpow delta alpha with hc_def
  set E_rel : Finset (Point2 × Point2) := G₁ ×ˢ G₂ with hE_def

  have hK : 1 ≤ K_final := by
    rw [hK_def]
    have h_pos : 0 < 3 * alpha / zeta + lambda := by positivity
    have h_exp_neg : -3 * alpha / zeta - lambda < 0 := by
      have h_eq : -3 * alpha / zeta - lambda = -(3 * alpha / zeta + lambda) := by ring
      rw [h_eq]
      have h_neg : -(3 * alpha / zeta + lambda) < 0 := neg_neg_of_pos h_pos
      exact h_neg
    have h : Real.rpow delta (-3 * alpha / zeta - lambda) > Real.rpow delta 0 :=
      Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 h_exp_neg
    have h2 : Real.rpow delta 0 = 1 := by simp
    rw [h2] at h
    exact h.le

  have hc_pos : 0 < c := by
    rw [hc_def]
    exact Real.rpow_pos_of_pos hdelta alpha

  have hc_lt_one : c < 1 := by
    rw [hc_def]
    have h : Real.rpow delta alpha < Real.rpow delta 0 :=
      Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 (by linarith)
    have h2 : Real.rpow delta 0 = 1 := by simp
    rw [h2] at h
    exact h

  have hc : c ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩

  have hE_sub : E_rel ⊆ G₁ ×ˢ G₂ := by simp [hE_def]

  have hE_card : (E_rel.card : ENNReal) = (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
    simp [hE_def, Finset.card_product]

  have h_mass : (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)
      ≤ (E_rel.card : ENNReal) := by
    rw [hE_card]
    have h1 : (1 - ENNReal.ofReal c) ≤ 1 := by simp
    have h4 : (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) ≤ (G₁.card : ENNReal) := by
      calc
        (1 - ENNReal.ofReal c) * (G₁.card : ENNReal)
          ≤ (1 : ENNReal) * (G₁.card : ENNReal) := by gcongr <;> exact h1
        _ = (G₁.card : ENNReal) := by simp
    have h5 : (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) * (G₂.card : ENNReal) ≤
        (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
      calc
        (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)
          = ((1 - ENNReal.ofReal c) * (G₁.card : ENNReal)) * (G₂.card : ENNReal) := by ring
        _ ≤ (G₁.card : ENNReal) * (G₂.card : ENNReal) := by gcongr
    exact h5


  let T : ℝ := Real.rpow delta (12 * alpha / zeta + 4 * lambda)

  have hK_final_mul : ∀ (r : ℝ), T ≤ r →
      1 ≤ K_final * Real.rpow r (1 / 4 : ℝ) := by
    intro r hr
    have hT_pos : 0 < T := Real.rpow_pos_of_pos hdelta _
    have h1 : Real.rpow r (1 / 4 : ℝ) ≥ Real.rpow T (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hT_pos.le hr (by norm_num)
    have h2 : Real.rpow T (1 / 4 : ℝ) =
        Real.rpow delta ((12 * alpha / zeta + 4 * lambda) * (1 / 4 : ℝ)) := by
      have h_rpow : Real.rpow (Real.rpow delta (12 * alpha / zeta + 4 * lambda)) (1 / 4 : ℝ) =
          Real.rpow delta ((12 * alpha / zeta + 4 * lambda) * (1 / 4 : ℝ)) :=
        (Real.rpow_mul hdelta.le (12 * alpha / zeta + 4 * lambda) (1 / 4 : ℝ)).symm
      exact h_rpow
    rw [h2] at h1
    have h3 : (12 * alpha / zeta + 4 * lambda) * (1 / 4 : ℝ) =
        3 * alpha / zeta + lambda := by ring
    rw [h3] at h1
    have h4 : K_final * Real.rpow r (1 / 4 : ℝ) ≥
        K_final * Real.rpow delta (3 * alpha / zeta + lambda) := by gcongr
    have h5 : K_final * Real.rpow delta (3 * alpha / zeta + lambda) = 1 := by
      rw [hK_def]
      have h6 : Real.rpow delta (-3 * alpha / zeta - lambda) *
          Real.rpow delta (3 * alpha / zeta + lambda) =
          Real.rpow delta ((-3 * alpha / zeta - lambda) + (3 * alpha / zeta + lambda)) := by
        exact (Real.rpow_add hdelta (-3 * alpha / zeta - lambda) (3 * alpha / zeta + lambda)).symm
      rw [h6]
      have h7 : (-3 * alpha / zeta - lambda) + (3 * alpha / zeta + lambda) = 0 := by ring
      rw [h7]
      simp
    rw [h5] at h4
    exact h4

  have h_trivial_bound : ∀ (ℓ : AffineSubspace ℝ Point2) (hfin : Module.finrank ℝ ℓ.direction = 1)
      (r : ℝ), T ≤ r →
      ((G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card : ENNReal) ≤
      ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * (G₂.card : ENNReal) := by
    intro ℓ hfin r hr
    have hKge1 : 1 ≤ K_final * Real.rpow r (1 / 4 : ℝ) := hK_final_mul r hr
    have h_count_le : ((G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card : ENNReal) ≤
        (G₂.card : ENNReal) := by
      have h : (G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card ≤ G₂.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      exact Nat.cast_le.mpr h
    have h9 : (1 : ENNReal) ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) := by
      have h10 : 0 ≤ K_final * Real.rpow r (1 / 4 : ℝ) := by positivity
      have h11 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hKge1
      have h12 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
      rw [h12] at h11
      exact h11
    calc
      ((G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card : ENNReal)
        ≤ (G₂.card : ENNReal) := h_count_le
      _ = (1 : ENNReal) * (G₂.card : ENNReal) := by simp
      _ ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * (G₂.card : ENNReal) := by gcongr

  have h_main_bound : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, delta ≤ r →
        ((G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E_rel).card : ENNReal) ≤
        ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * (G₂.card : ENNReal) := by
    intro b₁ hb₁ ℓ hb₁_line hfin r hr
    have hr_pos : 0 < r := hdelta.trans_le hr
    have h_in_E : ∀ b₂ ∈ G₂, (b₁, b₂) ∈ E_rel := by
      intro b₂ hb₂
      simp only [hE_def, Finset.mem_product]
      exact ⟨hb₁, hb₂⟩
    have h_filter_simp : (G₂.filter fun b₂ =>
        b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E_rel) =
        G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2) := by
      ext b₂
      simp only [Finset.mem_filter]
      constructor
      · intro h; exact ⟨h.1, h.2.1⟩
      · intro h; exact ⟨h.1, h.2, h_in_E b₂ h.1⟩
    rw [h_filter_simp]

    rcases h_main with (hzeta_ge | h_exp_ge1)

    · -- Case 1: ζ ≥ 1/4
      by_cases hT : T ≤ r
      · exact h_trivial_bound ℓ hfin r hT
      · -- NC bound
        have h_r_lt_T : r < T := by linarith
        have h_T_lt_one : T < 1 := by
          have h_exp_pos : 0 < 12 * alpha / zeta + 4 * lambda := by positivity
          have h : Real.rpow delta (12 * alpha / zeta + 4 * lambda) < Real.rpow delta 0 :=
            Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 (by positivity)
          have h2 : Real.rpow delta 0 = 1 := by simp
          rw [h2] at h
          exact h
        have h_r_le_one : r ≤ 1 := by linarith
        have h_nc_le : Real.rpow (Real.rpow delta (-lambda) * r) zeta ≤
            K_final * Real.rpow r (1 / 4 : ℝ) :=
          quarter_nc_bound hdelta hdelta1 hlambda hzeta halpha hzeta_ge r hr_pos h_r_lt_T
        obtain ⟨n, hn, hn_orth⟩ := exists_unit_normal_of_finrank_one hfin
        let t : ℝ := inner ℝ b₁ n
        have h_strip_sub : Metric.thickening r (ℓ : Set Point2) ⊆
            {y : Point2 | |inner ℝ y n - t| ≤ r} :=
          thickening_subset_strip hfin n hn hn_orth b₁ hb₁_line r hr_pos
        have h_filter_sub : (G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)) ⊆
            G₂.filter fun y => |inner ℝ y n - t| ≤ r := by
          intro b₂ hb₂
          have h_in_G₂ : b₂ ∈ G₂ := (Finset.mem_filter.mp hb₂).1
          have h_in_thick : b₂ ∈ Metric.thickening r (ℓ : Set Point2) :=
            (Finset.mem_filter.mp hb₂).2
          have h_in_strip : b₂ ∈ {y : Point2 | |inner ℝ y n - t| ≤ r} := h_strip_sub h_in_thick
          exact Finset.mem_filter.mpr ⟨h_in_G₂, h_in_strip⟩
        have h_card_le : ((G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card : ENNReal) ≤
            ((G₂.filter fun y => |inner ℝ y n - t| ≤ r).card : ENNReal) := by
          have h : (G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card ≤
              (G₂.filter fun y => |inner ℝ y n - t| ≤ r).card := Finset.card_le_card h_filter_sub
          exact Nat.cast_le.mpr h
        have h_bound := hNonConc n hn t r hr h_r_le_one
        have h_enn_le : Kakeya.realRpowENN (Real.rpow delta (-lambda) * r) zeta ≤
            ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) := by
          simp only [Kakeya.realRpowENN]
          exact ENNReal.ofReal_le_ofReal h_nc_le
        calc
          ((G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card : ENNReal)
            ≤ ((G₂.filter fun y => |inner ℝ y n - t| ≤ r).card : ENNReal) := h_card_le
          _ ≤ Kakeya.realRpowENN (Real.rpow delta (-lambda) * r) zeta * (G₂.card : ENNReal) := h_bound
          _ ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * (G₂.card : ENNReal) := by
              gcongr

    · -- Case 2: 12α/ζ + 4λ ≥ 1, so T ≤ δ ≤ r
      have hT_le_delta : T ≤ delta := by
        have h1 : Real.rpow delta (12 * alpha / zeta + 4 * lambda) ≤ Real.rpow delta 1 :=
          Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1.le h_exp_ge1
        have h2 : Real.rpow delta 1 = delta := by simp
        rw [h2] at h1
        exact h1
      have hT_le_r : T ≤ r := by linarith
      exact h_trivial_bound ℓ hfin r hT_le_r

  exact ⟨by norm_num, hK, hc, E_rel, hE_sub, h_mass, h_main_bound⟩

end Kakeya.Assouad

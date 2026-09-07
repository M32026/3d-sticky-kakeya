import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements

/-!
# Assembly helper lemmas for Wolff hairbrush preprocessing

Pure ENNReal/real-analysis helpers used by the final assembly:
- `card_retention_transfer`: chain cardinality bounds through pruning + angle separation
- `frostman_transfer`: Frostman slab bound from F to subfamily F2
- `hairbrush_delta₀_exists`: choose inputEta and delta₀ satisfying all four inequalities
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/-- Multiply two `realRpowENN` terms: `δ^a * δ^b = δ^(a+b)`. -/
private lemma realRpowENN_mul {δ a b : ℝ} (hδ : 0 < δ) :
    Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ b = Kakeya.realRpowENN δ (a + b) := by
  have hδ' : 0 ≤ δ := by linarith
  have hpos1 : 0 ≤ Real.rpow δ a := Real.rpow_nonneg hδ' a
  have h_eq : Real.rpow δ a * Real.rpow δ b = Real.rpow δ (a + b) :=
    (Real.rpow_add hδ a b).symm
  have h1 : ENNReal.ofReal (Real.rpow δ a) * ENNReal.ofReal (Real.rpow δ b) =
      ENNReal.ofReal (Real.rpow δ a * Real.rpow δ b) := by
    rw [← ENNReal.ofReal_mul hpos1]
  have h_main : ENNReal.ofReal (Real.rpow δ a) * ENNReal.ofReal (Real.rpow δ b) =
      ENNReal.ofReal (Real.rpow δ (a + b)) := by
    rw [h1, h_eq]
  simpa [Kakeya.realRpowENN] using h_main

/-- `realRpowENN δ 0 = 1`. -/
private lemma realRpowENN_zero {δ : ℝ} :
    Kakeya.realRpowENN δ 0 = 1 := by
  simp [Kakeya.realRpowENN, Real.rpow_zero]

/-- Monotonicity of `containedCount` in the tube family. -/
private lemma containedCount_mono {δ : ℝ} {F F2 : Kakeya.TubeFamily δ} {W : Set Point3}
    (h : F2 ⊆ F) : F2.containedCount W ≤ F.containedCount W := by
  dsimp only [Kakeya.TubeFamily.containedCount]
  classical
  exact_mod_cast Finset.card_le_card (show
      (F2.filter fun T : Kakeya.DeltaTube δ => T.carrier ⊆ W) ⊆
      (F.filter fun T : Kakeya.DeltaTube δ => T.carrier ⊆ W) from by
    intro T hT
    have hT1 : T ∈ F2 := (Finset.mem_filter.mp hT).1
    have hT2 : T.carrier ⊆ W := (Finset.mem_filter.mp hT).2
    exact Finset.mem_filter.mpr ⟨h hT1, hT2⟩)

lemma card_retention_transfer
    {δ inputEta outputEta : ℝ}
    {F F1 F2 : Kakeya.TubeFamily δ}
    (hδ : 0 < δ)
    (hF1_card : Kakeya.realRpowENN δ (3 * inputEta / 2) * F.enncard ≤ F1.enncard)
    (h_card_bound2 : F1.enncard ≤
      (128 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) * F2.enncard)
    (h_ineq : (1 / 128 : ENNReal) * Kakeya.realRpowENN δ (5 * inputEta / 2) ≥
      Kakeya.realRpowENN δ outputEta) :
    Kakeya.realRpowENN δ outputEta * F.enncard ≤ F2.enncard := by
  set a := Kakeya.realRpowENN δ (3 * inputEta / 2)
  set b := Kakeya.realRpowENN δ inputEta
  set b' := Kakeya.realRpowENN δ (-inputEta)
  set d := Kakeya.realRpowENN δ (5 * inputEta / 2)
  set e := Kakeya.realRpowENN δ outputEta
  set c := (1 / 128 : ENNReal)
  have h_ab : b * a = d := by
    have h : b * a = Kakeya.realRpowENN δ (inputEta + (3 * inputEta / 2)) := realRpowENN_mul hδ
    have h2 : inputEta + (3 * inputEta / 2) = (5 * inputEta / 2 : ℝ) := by ring
    rw [h, h2] <;> rfl
  have h_bb' : b * b' = 1 := by
    have h : b * b' = Kakeya.realRpowENN δ (inputEta + (-inputEta)) := realRpowENN_mul hδ
    have h2 : inputEta + (-inputEta) = (0 : ℝ) := by ring
    rw [h, h2, realRpowENN_zero]
  have h1 : a * F.enncard ≤ (128 : ENNReal) * b' * F2.enncard :=
    le_trans hF1_card h_card_bound2
  have h2 : b * (a * F.enncard) ≤ b * ((128 : ENNReal) * b' * F2.enncard) := by gcongr
  have hLHS : b * (a * F.enncard) = d * F.enncard := by
    have h3 : b * (a * F.enncard) = (b * a) * F.enncard := by rw [mul_assoc]
    rw [h3, h_ab]
  have h_b128 : b * ((128 : ENNReal) * b') = (128 : ENNReal) := by
    calc
      b * ((128 : ENNReal) * b')
        = (b * (128 : ENNReal)) * b' := by rw [mul_assoc]
      _ = ((128 : ENNReal) * b) * b' := by rw [mul_comm b (128 : ENNReal)]
      _ = (128 : ENNReal) * (b * b') := by rw [mul_assoc]
      _ = (128 : ENNReal) * 1 := by rw [h_bb']
      _ = (128 : ENNReal) := by rw [mul_one]
  have hRHS : b * (((128 : ENNReal) * b') * F2.enncard) = (128 : ENNReal) * F2.enncard := by
    have h3 : b * (((128 : ENNReal) * b') * F2.enncard) =
        (b * ((128 : ENNReal) * b')) * F2.enncard := by
      exact (mul_assoc b ((128 : ENNReal) * b') F2.enncard).symm
    rw [h3, h_b128]
  have h2' : d * F.enncard ≤ (128 : ENNReal) * F2.enncard := by
    rw [hLHS, hRHS] at h2
    exact h2
  have h3 : c * (d * F.enncard) ≤ c * ((128 : ENNReal) * F2.enncard) := by gcongr
  have h_c128 : c * (128 : ENNReal) = 1 := by
    have h_c_def : c = (128 : ENNReal)⁻¹ := by simp [c] <;> rfl
    rw [h_c_def]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have h4 : c * ((128 : ENNReal) * F2.enncard) = F2.enncard := by
    have h5 : c * ((128 : ENNReal) * F2.enncard) = (c * (128 : ENNReal)) * F2.enncard := by
      rw [mul_assoc]
    rw [h5, h_c128, one_mul]
  rw [h4] at h3
  have h7 : c * d * F.enncard ≤ F2.enncard := by
    have h8 : c * (d * F.enncard) = c * d * F.enncard := by rw [mul_assoc]
    rw [h8] at h3
    exact h3
  have h9 : e * F.enncard ≤ c * d * F.enncard := by
    have h10 : e ≤ c * d := h_ineq
    gcongr
    <;> exact h10
  exact le_trans h9 h7

lemma frostman_transfer
    {δ inputEta outputEta : ℝ}
    {F F2 : Kakeya.TubeFamily δ}
    (hδ : 0 < δ)
    (hF2_sub_F : F2 ⊆ F)
    (hFrostman : Kakeya.FrostmanSlabWolffBound F (Real.rpow δ (-inputEta)))
    (h_card : Kakeya.realRpowENN δ (outputEta - inputEta) * F.enncard ≤ F2.enncard) :
    Kakeya.FrostmanSlabWolffBound F2 (Real.rpow δ (-outputEta)) := by
  set a := Kakeya.realRpowENN δ (outputEta - inputEta)
  set a_inv := Kakeya.realRpowENN δ (inputEta - outputEta)
  have ha_mul : a_inv * a = 1 := by
    have h : a_inv * a = Kakeya.realRpowENN δ ((inputEta - outputEta) + (outputEta - inputEta)) :=
      realRpowENN_mul hδ
    have h2 : (inputEta - outputEta) + (outputEta - inputEta) = (0 : ℝ) := by ring
    rw [h, h2, realRpowENN_zero]
  have hF_card : F.enncard ≤ a_inv * F2.enncard := by
    have h : a_inv * (a * F.enncard) ≤ a_inv * F2.enncard := by gcongr
    have h2 : a_inv * (a * F.enncard) = (a_inv * a) * F.enncard := by rw [mul_assoc]
    rw [h2] at h
    rw [ha_mul] at h
    simpa using h
  have h_rpow_mul : Real.rpow δ (-inputEta) * Real.rpow δ (inputEta - outputEta) =
      Real.rpow δ (-outputEta) := by
    have h : Real.rpow δ ((-inputEta) + (inputEta - outputEta)) =
        Real.rpow δ (-inputEta) * Real.rpow δ (inputEta - outputEta) :=
      Real.rpow_add hδ (-inputEta) (inputEta - outputEta)
    have h_sum : (-inputEta) + (inputEta - outputEta) = -outputEta := by ring
    rw [h_sum] at h
    exact h.symm
  have hpos : 0 ≤ Real.rpow δ (-inputEta) := Real.rpow_nonneg (by linarith) (-inputEta)
  set r := ENNReal.ofReal (Real.rpow δ (-inputEta))
  have h_mul_enn : r * a_inv = ENNReal.ofReal (Real.rpow δ (-outputEta)) := by
    simp only [r, a_inv, Kakeya.realRpowENN]
    have h : ENNReal.ofReal (Real.rpow δ (-inputEta)) * ENNReal.ofReal (Real.rpow δ (inputEta - outputEta)) =
        ENNReal.ofReal (Real.rpow δ (-inputEta) * Real.rpow δ (inputEta - outputEta)) := by
      rw [← ENNReal.ofReal_mul hpos]
    rw [h, h_rpow_mul]
  intro S
  have h1 : F2.containedCount S.carrier ≤ F.containedCount S.carrier :=
    containedCount_mono hF2_sub_F
  have h2 : F.containedCount S.carrier ≤ r * MeasureTheory.volume S.carrier * F.enncard :=
    hFrostman S
  have h3 : r * F.enncard ≤ ENNReal.ofReal (Real.rpow δ (-outputEta)) * F2.enncard := by
    calc
      r * F.enncard
        ≤ r * (a_inv * F2.enncard) := by gcongr
      _ = (r * a_inv) * F2.enncard := by rw [mul_assoc]
      _ = ENNReal.ofReal (Real.rpow δ (-outputEta)) * F2.enncard := by rw [h_mul_enn]
  calc
    F2.containedCount S.carrier
      ≤ F.containedCount S.carrier := h1
    _ ≤ r * MeasureTheory.volume S.carrier * F.enncard := h2
    _ = r * F.enncard * MeasureTheory.volume S.carrier := by
      rw [mul_assoc, mul_comm (MeasureTheory.volume S.carrier)] <;> rw [mul_assoc]
    _ ≤ ENNReal.ofReal (Real.rpow δ (-outputEta)) * F2.enncard * MeasureTheory.volume S.carrier := by
      gcongr <;> exact h3
    _ = ENNReal.ofReal (Real.rpow δ (-outputEta)) * MeasureTheory.volume S.carrier * F2.enncard := by
      rw [mul_assoc, mul_comm F2.enncard (MeasureTheory.volume S.carrier), ←mul_assoc]

lemma hairbrush_delta₀_exists
    (outputEta : ℝ) (h_outputEta_pos : 0 < outputEta) :
    ∃ (inputEta delta₀ : ℝ), 0 < inputEta ∧ inputEta = outputEta / 4 ∧
      0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧ delta₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
        (Kakeya.realRpowENN δ (3 * inputEta / 2) ≤
          (1 / 2 : ENNReal) * Kakeya.realRpowENN δ inputEta) ∧
        ((125 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) + 1 ≤
          (128 : ENNReal) * Kakeya.realRpowENN δ (-inputEta)) ∧
        ((1 / 128 : ENNReal) * Kakeya.realRpowENN δ (5 * inputEta / 2) ≥
          Kakeya.realRpowENN δ outputEta) ∧
        ((1 / 128 : ENNReal) * Kakeya.realRpowENN δ (5 * inputEta / 2) ≥
          Kakeya.realRpowENN δ (outputEta - inputEta)) := by
  let inputEta : ℝ := outputEta / 4
  let D : ℝ := (1 / 128 : ℝ) ^ (8 / outputEta)
  let delta₀ : ℝ := min D (1 / 2)
  have h_inputEta_pos : 0 < inputEta := by
    dsimp only [inputEta] <;> linarith
  have h_inputEta_eq : inputEta = outputEta / 4 := by rfl
  have h_exp_pos : 0 < 8 / outputEta := by positivity
  have hD_pos : 0 < D := by dsimp only [D] <;> positivity
  have h_delta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min hD_pos (by norm_num)
  have h_delta₀_half : delta₀ ≤ 1 / 2 := min_le_right _ _
  have h_delta₀_le_one : delta₀ ≤ 1 := by
    have h : delta₀ ≤ 1 / 2 := h_delta₀_half
    linarith
  have hD_delta₀ : delta₀ ≤ D := min_le_left _ _
  refine' ⟨inputEta, delta₀, h_inputEta_pos, h_inputEta_eq, h_delta₀_pos, h_delta₀_half, h_delta₀_le_one, _⟩
  intro δ hδ hδ_le
  have hδ_le_one : δ ≤ 1 := by linarith
  have hδ' : 0 ≤ δ := by linarith
  have h_rpow_mono : ∀ (p : ℝ), 0 < p → Real.rpow δ p ≤ Real.rpow delta₀ p := by
    intro p hp
    exact Real.rpow_le_rpow (by linarith) hδ_le hp.le
  have h_delta₀_rpow : ∀ (p : ℝ), 0 < p →
      Real.rpow delta₀ p ≤ (1 / 128 : ℝ) ^ (p * (8 / outputEta)) := by
    intro p hp
    have h1 : Real.rpow delta₀ p ≤ Real.rpow D p :=
      Real.rpow_le_rpow (by positivity) hD_delta₀ hp.le
    have h_base_pos : (0 : ℝ) ≤ (1 / 128 : ℝ) := by norm_num
    have h2 : Real.rpow D p = (1 / 128 : ℝ) ^ ((8 / outputEta) * p) := by
      dsimp only [D]
      exact (Real.rpow_mul h_base_pos (8 / outputEta) p).symm
    rw [h2] at h1
    have h3 : (8 / outputEta) * p = p * (8 / outputEta) := by ring
    rw [h3] at h1
    exact h1
  -- Condition 1: δ^(3η/2) ≤ (1/2) * δ^η  ⟺  δ^(η/2) ≤ 1/2
  have h_p1 : 0 < inputEta / 2 := by positivity
  have h_cond1_real : Real.rpow δ (inputEta / 2) ≤ 1 / 2 := by
    have h : Real.rpow δ (inputEta / 2) ≤ Real.rpow delta₀ (inputEta / 2) := h_rpow_mono (inputEta / 2) h_p1
    have h4 : Real.rpow delta₀ (inputEta / 2) ≤ (1 / 128 : ℝ) ^ ((inputEta / 2) * (8 / outputEta)) :=
      h_delta₀_rpow (inputEta / 2) h_p1
    have h5 : (inputEta / 2) * (8 / outputEta) = 1 := by
      dsimp only [inputEta]
      field_simp [h_outputEta_pos.ne'] <;> ring
    rw [h5] at h4
    have h6 : (1 / 128 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
    exact le_trans h (le_trans h4 h6)
  have h_add1 : Real.rpow δ (3 * inputEta / 2) =
      Real.rpow δ inputEta * Real.rpow δ (inputEta / 2) := by
    have h_add : Real.rpow δ (inputEta + (inputEta / 2)) =
        Real.rpow δ inputEta * Real.rpow δ (inputEta / 2) :=
      Real.rpow_add hδ inputEta (inputEta / 2)
    have h_sum : inputEta + (inputEta / 2) = 3 * inputEta / 2 := by ring
    rw [h_sum] at h_add
    exact h_add
  have h7 : 0 ≤ Real.rpow δ inputEta := Real.rpow_nonneg hδ' inputEta
  have h_real1 : Real.rpow δ (3 * inputEta / 2) ≤ (1 / 2 : ℝ) * Real.rpow δ inputEta := by
    rw [h_add1]
    nlinarith
  have h_ofReal1 : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow δ inputEta) =
      (1 / 2 : ENNReal) * ENNReal.ofReal (Real.rpow δ inputEta) := by
    have h : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow δ inputEta) =
        ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (Real.rpow δ inputEta) :=
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [h] <;> simp
  have h_cond1 : Kakeya.realRpowENN δ (3 * inputEta / 2) ≤
      (1 / 2 : ENNReal) * Kakeya.realRpowENN δ inputEta := by
    have h_enn : ENNReal.ofReal (Real.rpow δ (3 * inputEta / 2)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow δ inputEta) :=
      ENNReal.ofReal_le_ofReal h_real1
    rw [h_ofReal1] at h_enn
    simpa [Kakeya.realRpowENN] using h_enn
  -- Condition 2: 125 * δ^(-η) + 1 ≤ 128 * δ^(-η)  ⟺  1 ≤ 3 * δ^(-η)  ⟺  δ^η ≤ 3
  have h_cond2_real : Real.rpow δ inputEta ≤ 3 := by
    have h9 : Real.rpow δ inputEta ≤ Real.rpow 1 inputEta :=
      Real.rpow_le_rpow (by linarith) hδ_le_one h_inputEta_pos.le
    have h10 : Real.rpow 1 inputEta = 1 := by simp
    rw [h10] at h9
    linarith
  have h_rpow_prod_one : Real.rpow δ inputEta * Real.rpow δ (-inputEta) = 1 := by
    have h : Real.rpow δ (inputEta + (-inputEta)) =
        Real.rpow δ inputEta * Real.rpow δ (-inputEta) := Real.rpow_add hδ inputEta (-inputEta)
    have h_sum : inputEta + (-inputEta) = (0 : ℝ) := by ring
    rw [h_sum] at h
    have h_zero : Real.rpow δ 0 = (1 : ℝ) := Real.rpow_zero δ
    rw [h_zero] at h
    exact h.symm
  have h_pos_neg : 0 ≤ Real.rpow δ (-inputEta) := Real.rpow_nonneg hδ' (-inputEta)
  have h12 : (1 : ℝ) ≤ (3 : ℝ) * Real.rpow δ (-inputEta) := by
    calc (1 : ℝ)
      = Real.rpow δ inputEta * Real.rpow δ (-inputEta) := h_rpow_prod_one.symm
    _ ≤ (3 : ℝ) * Real.rpow δ (-inputEta) := by
      exact mul_le_mul_of_nonneg_right h_cond2_real h_pos_neg
  have h_ofReal2 : ENNReal.ofReal ((3 : ℝ) * Real.rpow δ (-inputEta)) =
      (3 : ENNReal) * ENNReal.ofReal (Real.rpow δ (-inputEta)) := by
    have h : ENNReal.ofReal ((3 : ℝ) * Real.rpow δ (-inputEta)) =
        ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal (Real.rpow δ (-inputEta)) :=
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)
    rw [h] <;> simp
  have h11 : (1 : ENNReal) ≤ (3 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) := by
    have h : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal ((3 : ℝ) * Real.rpow δ (-inputEta)) :=
      ENNReal.ofReal_le_ofReal h12
    rw [h_ofReal2] at h
    simpa [Kakeya.realRpowENN] using h
  have h_cond2 : (125 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) + 1 ≤
      (128 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) := by
    have h16 : (125 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) + 1 ≤
        (125 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) +
        (3 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) := by gcongr
    have h17 : (125 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) +
        (3 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) =
        (128 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) := by
      rw [← add_mul] <;> norm_num
    rw [h17] at h16
    exact h16
  -- Condition 3: (1/128) * δ^(5η/2) ≥ δ^outputEta
  have h_p3 : 0 < outputEta - 5 * inputEta / 2 := by
    dsimp only [inputEta] <;> linarith
  have h_cond3_real : Real.rpow δ (outputEta - 5 * inputEta / 2) ≤ 1 / 128 := by
    have h : Real.rpow δ (outputEta - 5 * inputEta / 2) ≤
        Real.rpow delta₀ (outputEta - 5 * inputEta / 2) := h_rpow_mono _ h_p3
    have h4 : Real.rpow delta₀ (outputEta - 5 * inputEta / 2) ≤
        (1 / 128 : ℝ) ^ ((outputEta - 5 * inputEta / 2) * (8 / outputEta)) :=
      h_delta₀_rpow (outputEta - 5 * inputEta / 2) h_p3
    have h5 : (outputEta - 5 * inputEta / 2) * (8 / outputEta) = 3 := by
      dsimp only [inputEta]
      field_simp [h_outputEta_pos.ne'] <;> ring
    rw [h5] at h4
    have h6 : (1 / 128 : ℝ) ^ (3 : ℝ) ≤ (1 / 128 : ℝ) := by norm_num
    exact le_trans h (le_trans h4 h6)
  have h_exp_sum3 : (5 * inputEta / 2) + (outputEta - 5 * inputEta / 2) = outputEta := by ring
  have h_add3 : Real.rpow δ outputEta =
      Real.rpow δ (5 * inputEta / 2) * Real.rpow δ (outputEta - 5 * inputEta / 2) := by
    have h_add : Real.rpow δ ((5 * inputEta / 2) + (outputEta - 5 * inputEta / 2)) =
        Real.rpow δ (5 * inputEta / 2) * Real.rpow δ (outputEta - 5 * inputEta / 2) :=
      Real.rpow_add hδ (5 * inputEta / 2) (outputEta - 5 * inputEta / 2)
    rw [h_exp_sum3] at h_add
    exact h_add
  have h73 : 0 ≤ Real.rpow δ (5 * inputEta / 2) := Real.rpow_nonneg hδ' (5 * inputEta / 2)
  have h_real3 : Real.rpow δ outputEta ≤ (1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2) := by
    rw [h_add3]
    nlinarith
  have h_ofReal3 : ENNReal.ofReal ((1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2)) =
      (1 / 128 : ENNReal) * ENNReal.ofReal (Real.rpow δ (5 * inputEta / 2)) := by
    have h : ENNReal.ofReal ((1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2)) =
        ENNReal.ofReal (1 / 128 : ℝ) * ENNReal.ofReal (Real.rpow δ (5 * inputEta / 2)) :=
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 128)
    rw [h] <;> simp
  have h_cond3 : (1 / 128 : ENNReal) * Kakeya.realRpowENN δ (5 * inputEta / 2) ≥
      Kakeya.realRpowENN δ outputEta := by
    have h_enn : ENNReal.ofReal (Real.rpow δ outputEta) ≤
        ENNReal.ofReal ((1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2)) :=
      ENNReal.ofReal_le_ofReal h_real3
    rw [h_ofReal3] at h_enn
    simpa [Kakeya.realRpowENN] using h_enn
  -- Condition 4: (1/128) * δ^(5η/2) ≥ δ^(outputEta - inputEta)
  have h_p4 : 0 < outputEta - inputEta - 5 * inputEta / 2 := by
    dsimp only [inputEta] <;> linarith
  have h_cond4_real : Real.rpow δ (outputEta - inputEta - 5 * inputEta / 2) ≤ 1 / 128 := by
    have h : Real.rpow δ (outputEta - inputEta - 5 * inputEta / 2) ≤
        Real.rpow delta₀ (outputEta - inputEta - 5 * inputEta / 2) := h_rpow_mono _ h_p4
    have h4 : Real.rpow delta₀ (outputEta - inputEta - 5 * inputEta / 2) ≤
        (1 / 128 : ℝ) ^ ((outputEta - inputEta - 5 * inputEta / 2) * (8 / outputEta)) :=
      h_delta₀_rpow (outputEta - inputEta - 5 * inputEta / 2) h_p4
    have h5 : (outputEta - inputEta - 5 * inputEta / 2) * (8 / outputEta) = 1 := by
      dsimp only [inputEta]
      field_simp [h_outputEta_pos.ne'] <;> ring
    rw [h5] at h4
    simpa using le_trans h h4
  have h_exp_sum4 : (5 * inputEta / 2) + (outputEta - inputEta - 5 * inputEta / 2) = outputEta - inputEta := by ring
  have h_add4 : Real.rpow δ (outputEta - inputEta) =
      Real.rpow δ (5 * inputEta / 2) * Real.rpow δ (outputEta - inputEta - 5 * inputEta / 2) := by
    have h_add : Real.rpow δ ((5 * inputEta / 2) + (outputEta - inputEta - 5 * inputEta / 2)) =
        Real.rpow δ (5 * inputEta / 2) * Real.rpow δ (outputEta - inputEta - 5 * inputEta / 2) :=
      Real.rpow_add hδ (5 * inputEta / 2) (outputEta - inputEta - 5 * inputEta / 2)
    rw [h_exp_sum4] at h_add
    exact h_add
  have h74 : 0 ≤ Real.rpow δ (5 * inputEta / 2) := Real.rpow_nonneg hδ' (5 * inputEta / 2)
  have h_real4 : Real.rpow δ (outputEta - inputEta) ≤ (1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2) := by
    rw [h_add4]
    nlinarith
  have h_ofReal4 : ENNReal.ofReal ((1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2)) =
      (1 / 128 : ENNReal) * ENNReal.ofReal (Real.rpow δ (5 * inputEta / 2)) := by
    have h : ENNReal.ofReal ((1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2)) =
        ENNReal.ofReal (1 / 128 : ℝ) * ENNReal.ofReal (Real.rpow δ (5 * inputEta / 2)) :=
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 128)
    rw [h] <;> simp
  have h_cond4 : (1 / 128 : ENNReal) * Kakeya.realRpowENN δ (5 * inputEta / 2) ≥
      Kakeya.realRpowENN δ (outputEta - inputEta) := by
    have h_enn : ENNReal.ofReal (Real.rpow δ (outputEta - inputEta)) ≤
        ENNReal.ofReal ((1 / 128 : ℝ) * Real.rpow δ (5 * inputEta / 2)) :=
      ENNReal.ofReal_le_ofReal h_real4
    rw [h_ofReal4] at h_enn
    simpa [Kakeya.realRpowENN] using h_enn
  exact ⟨h_cond1, h_cond2, h_cond3, h_cond4⟩

end Kakeya.Assouad

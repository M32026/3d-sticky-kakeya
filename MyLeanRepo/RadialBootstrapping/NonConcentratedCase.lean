module

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.FurstenbergLowerBound
public import MyLeanRepo.RadialBootstrapping.FurstenbergCaller
public import MyLeanRepo.RadialBootstrapping.TxDeltaSet
public import MyLeanRepo.RadialBootstrapping.DiscreteFrostmanIsDeltaSet
public import MyLeanRepo.RadialBootstrapping.TwoSeparatedSubsets
public import MyLeanRepo.RadialBootstrapping.BoundedOverlap
public import MyLeanRepo.RadialBootstrapping.MeasureHelpers
public import MyLeanRepo.RadialBootstrapping.StepA_Extract

@[expose] public section

/-!
# Non-Concentrated Case — Contradiction Lemma (v3)

Given the data for the non-concentrated case (two separated subsets per tube,
T^r reference family with bounded overlap K_overlap, Furstenberg lower bound),
derive a contradiction.

## v3 changes (OSW-correct strategy)
- T^r reference family with full-metric cr-separation, O(r^{-κ}) overlap
- K_overlap : ℝ (e.g. C·r^{-κ}), not constant 13
- Contradiction exponent: εF > 8η + κ (was εF > 8η)
- Step B delta-set constant is existential (∃ C_B), not hardcoded 2·r^{-5η}
- Added hr_width2 hypothesis for two-separated-subsets at 2r scale

## Proof steps

1. Double counting upper bound: `∑ ≤ K_overlap`
2. Lower bound from mass: `∑ ≥ |T'| · r^{2σ+8η}`
3. Furstenberg (2r scale): `|T'| ≥ (2r)^{-(2σ+εF)} = factor · r^{-(2σ+εF)}`
4. Combine: `factor · r^{8η-εF} ≤ K_overlap`
5. Contradiction: `factor · r^{8η-εF} > factor · r^{-(εF-8η-κ)} > K_overlap`
   where `factor = 2^{-(2σ+εF)}`

Whiteprint node: non-concentrated-case
-/

open MeasureTheory Metric Set Finset
open SeedMathlib.MeasureTheory.FractalGeometry.FrostmanLemma
open scoped Classical

noncomputable section

namespace RadialBootstrapping

/-! ==========================================================================
   Double counting with constant overlap
   ========================================================================== -/

/-- If for every pair `(y1,y2)`, at most `K` tubes `T` have `y1 ∈ Y1 T` and
`y2 ∈ Y2 T`, then the sum of product measures is at most `K`. -/
lemma double_counting_upper_bound_const
    {ν : Measure Point} [IsProbabilityMeasure ν]
    {T'fin : Finset Line2}
    {Y1 Y2 : Line2 → Set Point}
    (hY1_meas : ∀ T ∈ T'fin, MeasurableSet (Y1 T))
    (hY2_meas : ∀ T ∈ T'fin, MeasurableSet (Y2 T))
    {K : ℝ} (hK_nonneg : 0 ≤ K)
    (h_overlap : ∀ (y1 y2 : Point),
        (T'fin.filter (fun T => y1 ∈ Y1 T ∧ y2 ∈ Y2 T)).card ≤ K) :
    ∑ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) ≤ ENNReal.ofReal K := by
  classical
  let f (p : Point × Point) : ENNReal := ∑ T ∈ T'fin,
    (Y1 T ×ˢ Y2 T).indicator (1 : Point × Point → ENNReal) p
  have h1 : ∑ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) = ∫⁻ p, f p ∂(ν.prod ν) := by
    have h_term : ∀ (T : Line2), T ∈ T'fin →
        ∫⁻ p, (Y1 T ×ˢ Y2 T).indicator (1 : Point × Point → ENNReal) p ∂(ν.prod ν) =
        (ν.prod ν) (Y1 T ×ˢ Y2 T) := by
      intro T hT
      have hmeas : MeasurableSet (Y1 T ×ˢ Y2 T) :=
        (hY1_meas T hT).prod (hY2_meas T hT)
      exact MeasureTheory.lintegral_indicator_one hmeas
    have h_sum : ∑ T ∈ T'fin, ∫⁻ p, (Y1 T ×ˢ Y2 T).indicator (1 : Point × Point → ENNReal) p ∂(ν.prod ν) =
        ∑ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) :=
      Finset.sum_congr rfl (fun T hT => h_term T hT)
    have h_meas : ∀ (T : Line2), T ∈ T'fin →
        Measurable ((Y1 T ×ˢ Y2 T).indicator (1 : Point × Point → ENNReal)) := by
      intro T hT
      have hmeas : MeasurableSet (Y1 T ×ˢ Y2 T) :=
        (hY1_meas T hT).prod (hY2_meas T hT)
      exact Measurable.indicator (measurable_const) hmeas
    have h2 : ∫⁻ p, f p ∂(ν.prod ν) =
        ∑ T ∈ T'fin, ∫⁻ p, (Y1 T ×ˢ Y2 T).indicator (1 : Point × Point → ENNReal) p ∂(ν.prod ν) := by
      dsimp only [f]
      exact MeasureTheory.lintegral_finsetSum T'fin h_meas
    rw [h2, h_sum]
  rw [h1]
  have h2 : ∀ (p : Point × Point), f p ≤ ENNReal.ofReal K := by
    intro p
    have h3 : f p = ((T'fin.filter (fun T => p.1 ∈ Y1 T ∧ p.2 ∈ Y2 T)).card : ENNReal) := by
      dsimp only [f]
      have h4 : ∑ T ∈ T'fin, (Y1 T ×ˢ Y2 T).indicator (1 : Point × Point → ENNReal) p =
          ∑ T ∈ T'fin, if p.1 ∈ Y1 T ∧ p.2 ∈ Y2 T then (1 : ENNReal) else 0 := by
        apply Finset.sum_congr rfl
        intro T _
        simp [Set.indicator_apply]
        <;> split_ifs <;> tauto
      rw [h4]
      rw [Finset.sum_ite]
      <;> simp
    rw [h3]
    have h6 : ((T'fin.filter (fun T => p.1 ∈ Y1 T ∧ p.2 ∈ Y2 T)).card : ℝ) ≤ K := h_overlap p.1 p.2
    have h_card_nonneg : 0 ≤ ((T'fin.filter (fun T => p.1 ∈ Y1 T ∧ p.2 ∈ Y2 T)).card : ℝ) := by positivity
    have h7 : ((T'fin.filter (fun T => p.1 ∈ Y1 T ∧ p.2 ∈ Y2 T)).card : ENNReal) ≤ ENNReal.ofReal K := by
      have h_eq : ((T'fin.filter (fun T => p.1 ∈ Y1 T ∧ p.2 ∈ Y2 T)).card : ENNReal) = ENNReal.ofReal ((T'fin.filter (fun T => p.1 ∈ Y1 T ∧ p.2 ∈ Y2 T)).card : ℝ) := by
        simp
      rw [h_eq]
      exact (ENNReal.ofReal_le_ofReal_iff hK_nonneg).mpr h6
    exact h7
  have h4 : ∫⁻ p, f p ∂(ν.prod ν) ≤ ∫⁻ (_ : Point × Point), ENNReal.ofReal K ∂(ν.prod ν) :=
    lintegral_mono h2
  rw [lintegral_const] at h4
  simpa [MeasureTheory.measure_univ] using h4

/-! ==========================================================================
   Core contradiction lemma (constant overlap version)
   ========================================================================== -/

/-- The non-concentrated case leads to a contradiction.

Takes all constructed data as explicit hypotheses. Uses bounded overlap
`K_overlap` (which may depend on r, e.g. K_overlap = C·r^{-κ}). -/
theorem non_concentrated_contradiction
    {μ ν : Measure Point} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r σ η εF K_overlap : ℝ}
    (hr : 0 < r)
    (hr1 : r < 1)
    (hσ : 0 < σ)
    (hσ1 : σ < 1)
    (hη : 0 < η)
    (hεF : 0 < εF)
    (hK_pos : 0 < K_overlap)
    (h_contradiction : 8 * η + 2 * (14 * η / (1 - σ)) < εF)
    (hr_small : Real.rpow 2 (-(2 * σ + εF)) * Real.rpow r (-(εF - 8 * η - 2 * (14 * η / (1 - σ)))) > K_overlap)
    {P : Set Point}
    (hP_nonempty : P.Nonempty)
    (hP_finite : P.Finite)
    (T'_x : Point → Set Line2)
    (Y1 Y2 : Line2 → Set Point)
    (T' : Set Line2)
    (hT'_eq : T' = ⋃ x ∈ P, T'_x x)
    (hT'_finite : Set.Finite T')
    (hY1_meas : ∀ T ∈ T', MeasurableSet (Y1 T))
    (hY2_meas : ∀ T ∈ T', MeasurableSet (Y2 T))
    (hY1_sub : ∀ T ∈ T', Y1 T ⊆ tube (2 * r) T)
    (hY2_sub : ∀ T ∈ T', Y2 T ⊆ tube (2 * r) T)
    (h_sep : ∀ T ∈ T', ∀ y1 ∈ Y1 T, ∀ y2 ∈ Y2 T,
        Real.rpow r (14 * η / (1 - σ)) / 4 ≤ dist y1 y2)
    (hY1_mass : ∀ T ∈ T', ν (Y1 T) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)))
    (hY2_mass : ∀ T ∈ T', ν (Y2 T) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)))
    (h_bounded_overlap : ∀ (y1 y2 : Point),
        Real.rpow r (14 * η / (1 - σ)) / 4 ≤ dist y1 y2 →
          (hT'_finite.toFinset.filter (fun L =>
             y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)).card ≤ (K_overlap : ℝ))
    (h_furstenberg_lower : (T'.ncard : ENNReal) ≥
        ENNReal.ofReal (Real.rpow (2 * r) (-(2 * σ + εF))))
    : False := by
  classical
  let κ : ℝ := 14 * η / (1 - σ)
  have hκ_pos : 0 < κ := by
    have h1 : 0 < 1 - σ := by linarith
    positivity
  let sep : ℝ := Real.rpow r κ / 4
  have hsep_pos : 0 < sep := by
    have h1 : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ
    positivity
  let T'fin : Finset Line2 := hT'_finite.toFinset
  have hT'fin_coe : (T'fin : Set Line2) = T' := hT'_finite.coe_toFinset

  --------------------------------------------------------------------------
  -- Step 1: Double counting upper bound
  --------------------------------------------------------------------------
  have h_overlap_Y : ∀ (y1 y2 : Point),
      (T'fin.filter (fun T => y1 ∈ Y1 T ∧ y2 ∈ Y2 T)).card ≤ K_overlap := by
    intro y1 y2
    let A := T'fin.filter (fun T => y1 ∈ Y1 T ∧ y2 ∈ Y2 T)
    let B := T'fin.filter (fun L => y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)
    by_cases h_empty : A.Nonempty
    · rcases h_empty with ⟨T, hT⟩
      have h2 : y1 ∈ Y1 T ∧ y2 ∈ Y2 T := (Finset.mem_filter.mp hT).2
      have hT_in : T ∈ T' := by
        have h : T ∈ T'fin := (Finset.mem_filter.mp hT).1
        exact hT'fin_coe ▸ h
      have h_sep' : sep ≤ dist y1 y2 := h_sep T hT_in y1 h2.1 y2 h2.2
      have h_sub : A ⊆ B := by
        intro L hL
        have h1 : L ∈ T'fin := (Finset.mem_filter.mp hL).1
        have h2 : y1 ∈ Y1 L ∧ y2 ∈ Y2 L := (Finset.mem_filter.mp hL).2
        have hL_in : L ∈ T' := hT'fin_coe ▸ h1
        exact Finset.mem_filter.mpr ⟨h1, hY1_sub L hL_in h2.1, hY2_sub L hL_in h2.2⟩
      have h3 : (B.card : ℝ) ≤ K_overlap := h_bounded_overlap y1 y2 h_sep'
      have h4 : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
      exact h4.trans h3
    · have h_empty' : A = ∅ := by simpa [A] using h_empty
      have h_goal : (A.card : ℝ) ≤ K_overlap := by
        rw [h_empty']
        simpa using hK_pos.le
      exact h_goal

  have hY1_meas' : ∀ T ∈ T'fin, MeasurableSet (Y1 T) := by
    intro T hT
    have h : T ∈ T' := hT'fin_coe ▸ hT
    exact hY1_meas T h
  have hY2_meas' : ∀ T ∈ T'fin, MeasurableSet (Y2 T) := by
    intro T hT
    have h : T ∈ T' := hT'fin_coe ▸ hT
    exact hY2_meas T h

  have h_double_count :
      ∑ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) ≤ ENNReal.ofReal K_overlap :=
    double_counting_upper_bound_const
      (hY1_meas := hY1_meas')
      (hY2_meas := hY2_meas')
      (hK_nonneg := hK_pos.le)
      (h_overlap := h_overlap_Y)

  --------------------------------------------------------------------------
  -- Step 2: Lower bound on the sum
  --------------------------------------------------------------------------
  have h_prod_eq : ∀ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) = ν (Y1 T) * ν (Y2 T) := by
    intro T _
    exact Measure.prod_prod (Y1 T) (Y2 T)

  have h_mass_prod : ∀ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) ≥
      ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := by
    intro T hT
    have hT_in : T ∈ T' := hT'fin_coe ▸ hT
    rw [h_prod_eq T hT]
    have h4 : ν (Y1 T) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) := hY1_mass T hT_in
    have h5 : ν (Y2 T) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) := hY2_mass T hT_in
    have h6 : ENNReal.ofReal (Real.rpow r (σ + 4 * η)) *
                ENNReal.ofReal (Real.rpow r (σ + 4 * η)) =
              ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := by
      have h7 : 0 ≤ Real.rpow r (σ + 4 * η) := Real.rpow_nonneg hr.le _
      have h8 : ENNReal.ofReal (Real.rpow r (σ + 4 * η)) *
                   ENNReal.ofReal (Real.rpow r (σ + 4 * η)) =
                 ENNReal.ofReal (Real.rpow r (σ + 4 * η) * Real.rpow r (σ + 4 * η)) := by
        rw [← ENNReal.ofReal_mul h7]
      rw [h8]
      have h9 : Real.rpow r (σ + 4 * η) * Real.rpow r (σ + 4 * η) =
          Real.rpow r (2 * σ + 8 * η) := by
        have h10 : Real.rpow r ((σ + 4 * η) + (σ + 4 * η)) =
            Real.rpow r (σ + 4 * η) * Real.rpow r (σ + 4 * η) :=
          Real.rpow_add hr (σ + 4 * η) (σ + 4 * η)
        have h11 : (σ + 4 * η) + (σ + 4 * η) = 2 * σ + 8 * η := by ring
        rw [h11] at h10
        exact h10.symm
      rw [h9]
    calc ν (Y1 T) * ν (Y2 T)
        ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) * ν (Y2 T) := by gcongr
      _ ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) *
            ENNReal.ofReal (Real.rpow r (σ + 4 * η)) := by gcongr
      _ = ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := h6

  have h_sum_lower :
      ∑ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) ≥
        (T'fin.card : ENNReal) * ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := by
    have h_sum : ∑ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) ≥
        ∑ T ∈ T'fin, ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) :=
      Finset.sum_le_sum h_mass_prod
    have h_sum_const : ∑ T ∈ T'fin, ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) =
        (T'fin.card : ENNReal) * ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := by
      rw [Finset.sum_const]
      <;> simp [mul_comm]
      <;> rfl
    rw [h_sum_const] at h_sum
    exact h_sum

  --------------------------------------------------------------------------
  -- Step 3: Contradiction
  --------------------------------------------------------------------------
  have h_card_eq : (T'fin.card : ENNReal) = (T'.ncard : ENNReal) := by
    have h1 : (T'fin : Set Line2) = T' := hT'_finite.coe_toFinset
    have h2 : T'.ncard = T'fin.card := by
      have h3 : T'.ncard = (T'fin : Set Line2).ncard := by rw [h1]
      rw [h3]; simp
    exact_mod_cast h2.symm

  let factor : ℝ := Real.rpow 2 (-(2 * σ + εF))
  have hfactor_pos : 0 < factor := Real.rpow_pos_of_pos (by norm_num) _
  have hfactor_nonneg : 0 ≤ factor := by positivity
  have h_rpow_split : Real.rpow (2 * r) (-(2 * σ + εF)) =
      factor * Real.rpow r (-(2 * σ + εF)) := by
    have h : Real.rpow (2 * r) (-(2 * σ + εF)) =
        Real.rpow 2 (-(2 * σ + εF)) * Real.rpow r (-(2 * σ + εF)) :=
      Real.mul_rpow (hx := by norm_num) (hy := hr.le)
    exact h

  have h11 : (T'fin.card : ENNReal) * ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) ≥
      ENNReal.ofReal (Real.rpow (2 * r) (-(2 * σ + εF))) *
      ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := by
    rw [h_card_eq]
    exact mul_le_mul_of_nonneg_right h_furstenberg_lower (by positivity)

  have h_pos1 : 0 ≤ Real.rpow r (-(2 * σ + εF)) := Real.rpow_nonneg hr.le _
  have h_pos2 : 0 ≤ factor * Real.rpow r (-(2 * σ + εF)) := by positivity
  have h12 : ENNReal.ofReal (Real.rpow (2 * r) (-(2 * σ + εF))) *
      ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) =
      ENNReal.ofReal (factor * Real.rpow r (8 * η - εF)) := by
    rw [h_rpow_split]
    rw [← ENNReal.ofReal_mul h_pos2]
    have h13 : factor * Real.rpow r (-(2 * σ + εF)) * Real.rpow r (2 * σ + 8 * η) =
        factor * Real.rpow r ((-(2 * σ + εF)) + (2 * σ + 8 * η)) := by
      have h14 : Real.rpow r (-(2 * σ + εF)) * Real.rpow r (2 * σ + 8 * η) =
          Real.rpow r ((-(2 * σ + εF)) + (2 * σ + 8 * η)) :=
        (Real.rpow_add hr _ _).symm
      have h_assoc : factor * Real.rpow r (-(2 * σ + εF)) * Real.rpow r (2 * σ + 8 * η) =
          factor * (Real.rpow r (-(2 * σ + εF)) * Real.rpow r (2 * σ + 8 * η)) := by ring
      rw [h_assoc, h14] <;> ring
    rw [h13]
    have h15 : (-(2 * σ + εF)) + (2 * σ + 8 * η) = 8 * η - εF := by ring
    rw [h15]

  have h15 : ENNReal.ofReal (factor * Real.rpow r (8 * η - εF)) ≤ ENNReal.ofReal K_overlap := by
    calc ENNReal.ofReal (factor * Real.rpow r (8 * η - εF))
      = ENNReal.ofReal (Real.rpow (2 * r) (-(2 * σ + εF))) *
          ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := h12.symm
    _ ≤ (T'fin.card : ENNReal) * ENNReal.ofReal (Real.rpow r (2 * σ + 8 * η)) := h11
    _ ≤ ∑ T ∈ T'fin, (ν.prod ν) (Y1 T ×ˢ Y2 T) := h_sum_lower
    _ ≤ ENNReal.ofReal K_overlap := h_double_count

  have h16 : 0 < εF - 8 * η - 2 * κ := by
    have hκ_eq2 : κ = 14 * η / (1 - σ) := by rfl
    rw [hκ_eq2]
    linarith
  have h17 : factor * Real.rpow r (8 * η - εF) >
      factor * Real.rpow r (-(εF - 8 * η - 2 * κ)) := by
    have h18 : (8 * η - εF) < (-(εF - 8 * η - 2 * κ)) := by linarith [hκ_pos]
    have h19 : Real.rpow r (8 * η - εF) > Real.rpow r (-(εF - 8 * η - 2 * κ)) :=
      Real.rpow_lt_rpow_of_exponent_gt hr hr1 h18
    exact mul_lt_mul_of_pos_left h19 hfactor_pos
  have h20 : factor * Real.rpow r (8 * η - εF) ≤ K_overlap := by
    have h21 : 0 ≤ factor * Real.rpow r (8 * η - εF) :=
      mul_nonneg hfactor_nonneg (Real.rpow_nonneg hr.le _)
    have h22 : 0 ≤ K_overlap := hK_pos.le
    have h23 : ENNReal.ofReal (factor * Real.rpow r (8 * η - εF)) ≤ ENNReal.ofReal K_overlap := h15
    exact (ENNReal.ofReal_le_ofReal_iff h22).mp h23
  have h21 : factor * Real.rpow r (-(εF - 8 * η - 2 * κ)) > K_overlap := hr_small
  have h22 : factor * Real.rpow r (8 * η - εF) > K_overlap := by
    calc factor * Real.rpow r (8 * η - εF)
      > factor * Real.rpow r (-(εF - 8 * η - 2 * κ)) := h17
    _ > K_overlap := h21
  exact lt_irrefl _ (lt_of_le_of_lt h20 h22)

/-! ==========================================================================
   Direct bridge: accepts pre-extracted P (bounded delta-set)
   ========================================================================== -/

/-- Direct bridge from pre-extracted P to core contradiction.

    Skips Step A (Frostman extraction); caller provides P directly.
    Uses `furstenberg_caller_lower_bound` for the Furstenberg step.
    Requires P ⊆ B(0,1) and explicit delta-set constant bounds.
    Doubling constants are obtained internally from Point_exists_doubling
    and Line2_exists_doubling.
-/
theorem non_concentrated_bridge_direct
    {ν₁ ν₂ : Measure Point} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {r σ τ κ εF K_overlap : ℝ}
    (hσ : 0 < σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ) (hr : 0 < r) (hr_small : r < 1)
    (hr2_small : 2 * r < 1)
    (hκ : κ = 14 * τ / (1 - σ)) (hκ_lt_one : κ < 1)
    (hεF_pos : 0 < εF)
    (hεF_large : 8 * τ + 2 * κ < εF)
    (hK_overlap_pos : 0 < K_overlap)
    (hr_small3 : Real.rpow 2 (-(2 * σ + εF)) * Real.rpow r (-(εF - 8 * τ - 2 * κ)) > K_overlap)
    (hr_mass : Real.rpow r τ ≤ 1 / 6)
    (hr_width2 : 2 * r ≤ (Real.sqrt 3 / 2) * Real.rpow r κ)
    -- Pre-extracted P (must be in B(0,1) for Furstenberg)
    {P : Set Point}
    (hP_finite : P.Finite)
    (hP_nonempty : P.Nonempty)
    (hP_ball : P ⊆ closedBall 0 1)
    (C_X : ℝ) (hC_X_nonneg : 0 ≤ C_X)
    (hP_delta : IsDeltaSet r 1 C_X hr (by norm_num) hC_X_nonneg P)
    -- Tube family and overlap
    (T_r : Finset Line2)
    (hT_r_overlap : ∀ (y1 y2 : Point),
        Real.rpow r κ / 4 ≤ dist y1 y2 →
          (T_r.filter (fun L => y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)).card ≤ K_overlap)
    -- Step B construction (includes C_T bound for Furstenberg)
    (h_step_B : ∃ (T'_x : Point → Set Line2) (A : Line2 → Set Point) (D_T : ℕ),
          (0 < D_T) ∧
          (∀ (L : Line2) (ε : ℝ), 0 < ε →
            ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D_T) ∧
          (∀ x ∈ P, Set.Finite (T'_x x)) ∧
          (∀ x ∈ P, (T'_x x).Nonempty) ∧
          (∀ x ∈ P, ∃ (C_B : ℝ) (hC_B : 0 ≤ C_B),
            IsDeltaSet r σ C_B hr hσ.le hC_B (T'_x x) ∧
            C_B * (D_T : ℝ) ≤ Real.rpow (2 * r) (-εF)) ∧
          (∀ x ∈ P, ∀ L ∈ T'_x x, x ∈ tube (2 * r) L) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), L ∈ (T_r : Set Line2)) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), MeasurableSet (A L)) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), A L ⊆ tube (2 * r) L) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x),
            ν₂ (A L) ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ))) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), ∀ (x : Point),
            ν₂ (A L ∩ Metric.ball x (Real.rpow r κ)) ≤ ν₂ (A L) / 3))
    -- Furstenberg axiom parameters
    (ε_F δ₀ : ℝ) (hε_F_pos : 0 < ε_F) (hδ₀_pos : 0 < δ₀)
    (hF : ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
      ∀ (X : Set Point) (T : Point → Set Line2),
        X.Nonempty → X ⊆ closedBall 0 1 →
        IsDeltaSet δ 1 (Real.rpow δ (-ε_F)) hδ (by norm_num) (Real.rpow_nonneg hδ.le _) X →
        (∀ x ∈ X, (T x).Nonempty ∧
          IsDeltaSet δ σ (Real.rpow δ (-ε_F)) hδ hσ.le (Real.rpow_nonneg hδ.le _) (T x) ∧
          ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
        Set.Finite (⋃ x ∈ X, T x) →
        (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * σ - ε_F)))
    (hεF_le : εF ≤ ε_F)
    (hδ_le : 2 * r ≤ δ₀)
    -- Point doubling constant (provided by caller since it appears in hC_X_bound)
    (D_X : ℕ) (hD_X_pos : 0 < D_X)
    (h_double_X : ∀ (x : Point) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Point), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D_X)
    (hC_X_bound : C_X * (D_X : ℝ) ≤ Real.rpow (2 * r) (-εF))
    : False := by
  classical
  let η : ℝ := τ
  have hη : 0 < η := hτ
  have h1m_pos : 0 < 1 - σ := by linarith
  have hκ_pos : 0 < κ := by
    rw [hκ]; positivity
  have hκ_eq : κ = 14 * η / (1 - σ) := by
    simpa [η] using hκ
  let sep : ℝ := Real.rpow r κ / 4
  have hsep_pos : 0 < sep := by
    have h1 : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ
    positivity

  -- Step B: Apply caller-provided construction
  rcases h_step_B with ⟨T'_x, A, D_T, hD_T_pos, h_double_T,
      hT'_x_finite, hT'_x_nonempty, hT'_x_delta, hT'_x_tube,
      hT'_subset_Tr, hA_meas, hA_sub, hA_mass, hA_nonconc⟩

  let T' : Set Line2 := ⋃ x ∈ P, T'_x x
  have hT'_finite : Set.Finite T' := by
    apply Set.Finite.biUnion hP_finite
    intro x hx
    exact hT'_x_finite x hx
  let T'fin : Finset Line2 := hT'_finite.toFinset
  have hT'fin_coe : (T'fin : Set Line2) = T' := hT'_finite.coe_toFinset

  -- Step C: Two separated subsets for each tube in T'
  have hρ_pos : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ
  have hm_pos : 0 < Real.rpow r (σ + 3 * η) := Real.rpow_pos_of_pos hr (σ + 3 * η)

  have h_mass6_real : Real.rpow r (σ + 3 * η) / 6 ≥ Real.rpow r (σ + 4 * η) := by
    have h1 : Real.rpow r η ≤ 1 / 6 := by simpa [η] using hr_mass
    have h2 : Real.rpow r (σ + 4 * η) = Real.rpow r (σ + 3 * η) * Real.rpow r η := by
      have h3 : Real.rpow r ((σ + 3 * η) + η) =
          Real.rpow r (σ + 3 * η) * Real.rpow r η := Real.rpow_add hr (σ + 3 * η) η
      have h4 : (σ + 3 * η) + η = σ + 4 * η := by ring
      rw [h4] at h3
      exact h3
    have h5 : 0 ≤ Real.rpow r (σ + 3 * η) := Real.rpow_nonneg hr.le _
    have h6 : Real.rpow r (σ + 3 * η) / 6 = Real.rpow r (σ + 3 * η) * (1 / 6 : ℝ) := by ring
    rw [h6, h2]
    have h_goal : Real.rpow r (σ + 3 * η) * (1 / 6 : ℝ) ≥
        Real.rpow r (σ + 3 * η) * Real.rpow r η := by
      exact mul_le_mul_of_nonneg_left h1 h5
    exact h_goal
  have h_mass6 : ENNReal.ofReal (Real.rpow r (σ + 3 * η) / 6) ≥
      ENNReal.ofReal (Real.rpow r (σ + 4 * η)) := by
    have h8 : 0 ≤ Real.rpow r (σ + 3 * η) / 6 := by positivity
    exact ENNReal.ofReal_le_ofReal_iff h8 |>.mpr h_mass6_real

  have h_two_data : ∀ (L : Line2), L ∈ T' → ∃ (Y1 Y2 : Set Point),
      MeasurableSet Y1 ∧ MeasurableSet Y2 ∧
      Y1 ⊆ tube (2 * r) L ∧ Y2 ⊆ tube (2 * r) L ∧
      ν₂ Y1 ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) ∧
      ν₂ Y2 ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) ∧
      ∀ y1 ∈ Y1, ∀ y2 ∈ Y2, sep ≤ dist y1 y2 := by
    intro L hL
    have hA_measL : MeasurableSet (A L) := hA_meas L hL
    have hA_subL : A L ⊆ tube (2 * r) L := hA_sub L hL
    have hA_massL : ν₂ (A L) ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * η)) := hA_mass L hL
    have hA_nonconcL : ∀ (x : Point),
        ν₂ (A L ∩ Metric.ball x (Real.rpow r κ)) ≤ ν₂ (A L) / 3 := hA_nonconc L hL

    rcases two_separated_subsets_in_tube_affine
        L.toAffine L.2 (2 * r) (Real.rpow r κ) (Real.rpow r (σ + 3 * η))
        (by positivity) hρ_pos hm_pos hr_width2 ν₂ (A L) hA_measL hA_subL hA_massL hA_nonconcL
      with ⟨Y1, Y2, hY1_meas, hY2_meas, hY1_sub, hY2_sub, hY1_mass, hY2_mass, h_sep_dist⟩

    have hY1_sub' : Y1 ⊆ tube (2 * r) L := by
      calc Y1 ⊆ A L := hY1_sub
         _ ⊆ tube (2 * r) L := hA_subL
    have hY2_sub' : Y2 ⊆ tube (2 * r) L := by
      calc Y2 ⊆ A L := hY2_sub
         _ ⊆ tube (2 * r) L := hA_subL
    have hY1_mass' : ν₂ Y1 ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) :=
      le_trans h_mass6 hY1_mass
    have hY2_mass' : ν₂ Y2 ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) :=
      le_trans h_mass6 hY2_mass
    have h_sep' : ∀ y1 ∈ Y1, ∀ y2 ∈ Y2, sep ≤ dist y1 y2 := by
      intro y1 hy1 y2 hy2
      have h : dist y1 y2 ≥ Real.rpow r κ := h_sep_dist y1 hy1 y2 hy2
      have h9 : sep ≤ Real.rpow r κ := by
        dsimp only [sep]
        have h10 : 0 ≤ Real.rpow r κ := by positivity
        exact div_le_self h10 (by norm_num)
      exact le_trans h9 h
    exact ⟨Y1, Y2, hY1_meas, hY2_meas, hY1_sub', hY2_sub', hY1_mass', hY2_mass', h_sep'⟩

  choose Y1_raw Y2_raw hY1_meas_raw hY2_meas_raw hY1_sub_raw hY2_sub_raw
    hY1_mass_raw hY2_mass_raw h_sep_raw using h_two_data

  let Y1 (L : Line2) : Set Point := if h : L ∈ T' then Y1_raw L h else ∅
  let Y2 (L : Line2) : Set Point := if h : L ∈ T' then Y2_raw L h else ∅

  have hY1_meas : ∀ T ∈ T', MeasurableSet (Y1 T) := by
    intro T hT
    simp [Y1, hT] <;> exact hY1_meas_raw T hT
  have hY2_meas : ∀ T ∈ T', MeasurableSet (Y2 T) := by
    intro T hT
    simp [Y2, hT] <;> exact hY2_meas_raw T hT
  have hY1_sub : ∀ T ∈ T', Y1 T ⊆ tube (2 * r) T := by
    intro T hT
    simp [Y1, hT] <;> exact hY1_sub_raw T hT
  have hY2_sub : ∀ T ∈ T', Y2 T ⊆ tube (2 * r) T := by
    intro T hT
    simp [Y2, hT] <;> exact hY2_sub_raw T hT
  have hY1_mass : ∀ T ∈ T', ν₂ (Y1 T) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) := by
    intro T hT
    simp [Y1, hT] <;> exact hY1_mass_raw T hT
  have hY2_mass : ∀ T ∈ T', ν₂ (Y2 T) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * η)) := by
    intro T hT
    simp [Y2, hT] <;> exact hY2_mass_raw T hT
  have h_sep : ∀ T ∈ T', ∀ y1 ∈ Y1 T, ∀ y2 ∈ Y2 T, sep ≤ dist y1 y2 := by
    intro T hT y1 hy1 y2 hy2
    simp [Y1, Y2, hT] at hy1 hy2
    exact h_sep_raw T hT y1 hy1 y2 hy2

  -- Step D: Bounded overlap via T^r reference family
  have hT'_subset_Tr' : ∀ L ∈ T'fin, L ∈ (T_r : Set Line2) := by
    intro L hL
    have hL' : L ∈ T' := hT'fin_coe ▸ hL
    exact hT'_subset_Tr L hL'

  have h_bounded_overlap : ∀ (y1 y2 : Point), sep ≤ dist y1 y2 →
      (T'fin.filter (fun L => y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)).card ≤ K_overlap := by
    intro y1 y2 hdist
    let A := T'fin.filter (fun L => y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)
    let B := T_r.filter (fun L => y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)
    have h_sub : A ⊆ B := by
      intro L hL
      have h1 : L ∈ T'fin := (Finset.mem_filter.mp hL).1
      have h2 : L ∈ (T_r : Set Line2) := hT'_subset_Tr' L h1
      have h3 : y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L := (Finset.mem_filter.mp hL).2
      exact Finset.mem_filter.mpr ⟨by exact_mod_cast h2, h3⟩
    have h4 : (B.card : ℝ) ≤ K_overlap := hT_r_overlap y1 y2 hdist
    have h5 : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
    exact h5.trans h4

  -- Step E: Furstenberg lower bound via furstenberg_caller_lower_bound
  have hT_data : ∀ x ∈ P, (T'_x x).Nonempty ∧
      (∃ (C_T : ℝ) (hC_T : 0 ≤ C_T),
        IsDeltaSet r σ C_T hr hσ.le hC_T (T'_x x) ∧
        C_T * (D_T : ℝ) ≤ Real.rpow (2 * r) (-εF)) ∧
      ∀ ℓ ∈ T'_x x, x ∈ tube (2 * r) ℓ := by
    intro x hx
    have h_nonempty : (T'_x x).Nonempty := hT'_x_nonempty x hx
    have h_delta_bound : ∃ (C_B : ℝ) (hC_B : 0 ≤ C_B),
        IsDeltaSet r σ C_B hr hσ.le hC_B (T'_x x) ∧
        C_B * (D_T : ℝ) ≤ Real.rpow (2 * r) (-εF) := hT'_x_delta x hx
    have h_tube : ∀ ℓ ∈ T'_x x, x ∈ tube (2 * r) ℓ := hT'_x_tube x hx
    exact ⟨h_nonempty, h_delta_bound, h_tube⟩

  have h_furstenberg_lower' : (T'.ncard : ENNReal) ≥
      ENNReal.ofReal (Real.rpow (2 * r) (-(2 * σ + εF))) :=
    furstenberg_caller_lower_bound
      σ hσ hσ_lt_one r εF hr hr_small hr2_small hεF_pos
      D_X D_T hD_X_pos hD_T_pos h_double_X h_double_T
      ε_F δ₀ hε_F_pos hδ₀_pos hF hεF_le hδ_le
      P T'_x hP_nonempty hP_ball C_X hC_X_nonneg hP_delta hC_X_bound
      hT_data hT'_finite

  have h_contradiction' : 8 * η + 2 * (14 * η / (1 - σ)) < εF := by
    have h2 : 8 * η + 2 * κ < εF := by simpa [η] using hεF_large
    rw [hκ_eq] at h2
    exact h2
  have hr_small' : Real.rpow 2 (-(2 * σ + εF)) * Real.rpow r (-(εF - 8 * η - 2 * (14 * η / (1 - σ)))) > K_overlap := by
    have h_eq : εF - 8 * η - 2 * (14 * η / (1 - σ)) = εF - 8 * τ - 2 * κ := by
      simp [η, hκ_eq] <;> ring
    rw [h_eq]
    exact hr_small3

  exact non_concentrated_contradiction
    (μ := ν₁) (ν := ν₂)
    (hr := hr) (hr1 := hr_small)
    (hσ := hσ) (hσ1 := hσ_lt_one)
    (hη := hη) (hεF := hεF_pos)
    (hK_pos := hK_overlap_pos)
    (h_contradiction := h_contradiction')
    (hr_small := hr_small')
    (P := P) (hP_nonempty := hP_nonempty) (hP_finite := hP_finite)
    (T'_x := T'_x) (Y1 := Y1) (Y2 := Y2) (T' := T')
    (hT'_eq := by rfl) (hT'_finite := hT'_finite)
    (hY1_meas := hY1_meas) (hY2_meas := hY2_meas)
    (hY1_sub := hY1_sub) (hY2_sub := hY2_sub)
    (h_sep := fun T hT y1 hy1 y2 hy2 => by
      have h_eq : Real.rpow r (14 * η / (1 - σ)) / 4 = sep := by
        have h9 : 14 * η / (1 - σ) = κ := hκ_eq.symm
        congr <;> exact h9
      rw [h_eq]
      exact h_sep T hT y1 hy1 y2 hy2)
    (hY1_mass := hY1_mass) (hY2_mass := hY2_mass)
    (h_bounded_overlap := fun y1 y2 hdist =>
      have h_eq : Real.rpow r (14 * η / (1 - σ)) / 4 = sep := by
        have h9 : 14 * η / (1 - σ) = κ := hκ_eq.symm
        congr <;> exact h9
      h_bounded_overlap y1 y2 (by rw [←h_eq]; exact hdist))
    (h_furstenberg_lower := h_furstenberg_lower')

end RadialBootstrapping

module

/-
# Direction Transport on Projective Line (Bridge)

Proves `direction_transport_projective_line` by adapting the technique from
`DirectionTransportProof.charted_direction_measure_with_coefficient_identity`.

Key improvement: uses the midpoint trick to avoid the extra `2^τ` factor.
For a set S with diameter ≤ 2·L·r, the midpoint c = (Inf S + Sup S)/2
satisfies S ⊆ [c - L·r, c + L·r], giving Frostman constant with L^τ
(not (2L)^τ).

## Proof steps

1. **Pigeonhole**: Split Θ_bad' into left/right of pole y1.
   Pole neighborhood has mass ≤ δ^ε/2, so remaining mass ≥ δ^ε/2.
   One side has ≥ δ^ε/4.

2. **Define transport measure**: normalized pushforward through f_dir.

3. **Probability measure**: standard normalization argument.

4. **Support ⊆ [0,1]**: f_dir maps Θ_bad' into [0,1].

5. **Frostman with midpoint trick**:
   - Preimage of interval I has diameter ≤ 2·L_chart·r by co-Lipschitz
   - Midpoint gives containment in interval of radius L_chart·r
   - Normalization factor ≤ 4·δ^{-ε}
   - Total: C_ν · 4·δ^{-ε} · L_chart^τ · r^τ
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical

namespace ProductLikeIncidence.ProductReduction

lemma direction_transport_projective_line
    {δ ε κ0 q_pole q_pole_loss τ C_ν L_chart : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hε_pos : 0 < ε) (hkappa_pos : 0 < κ0)
    (hq_pole_pos : 0 < q_pole) (hq_pole_loss_pos : 0 < q_pole_loss)
    (hτ_pos : 0 < τ) (hC_ν_pos : 0 < C_ν)
    (hL_chart_pos : 0 < L_chart)
    (hL_chart_ge_one : 1 ≤ L_chart)
    {Ybar : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    {y1 y2 y3 : ℝ}
    (h_boundary_null : ν {y1 - δ ^ q_pole} = 0 ∧ ν {y1 + δ ^ q_pole} = 0)
    (hy1_in_unit : y1 ∈ Set.Icc 0 1)
    (hy2_in_unit : y2 ∈ Set.Icc 0 1)
    (hy3_in_unit : y3 ∈ Set.Icc 0 1)
    (h_sep12 : |y1 - y2| ≥ δ ^ (10 * ε / κ0))
    (h_sep13 : |y1 - y3| ≥ δ ^ (10 * ε / κ0))
    {Θ_bad' : Set ℝ}
    (hΘ_bad'_sub : Θ_bad' ⊆ Ybar)
    (hΘ_bad'_mass : ν Θ_bad' ≥ ENNReal.ofReal (δ ^ ε))
    (h_pole_mass_small :
      ν (Metric.ball y1 (δ ^ q_pole)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε))
    (h_r_pole : δ ^ q_pole ≤ δ ^ (10 * ε / κ0) / 2)
    (f_dir : ℝ → ℝ)
    (ν' : Measure ℝ)
    (hν'_link : ν' = Measure.map f_dir ν)
    (h_f_dir_lip : ∀ y z, y ≠ y1 → z ≠ y1 →
      |f_dir y - f_dir z| ≤ δ ^ (-q_pole_loss) * |y - z|)
    (h_f_dir_range : ∀ y ∈ Θ_bad', f_dir y ∈ Set.Icc 0 1)
    (h_f_dir_colip : ∀ y ∈ Θ_bad', ∀ z ∈ Θ_bad', y ≠ y1 → z ≠ y1 →
      |y - z| ≤ L_chart * |f_dir y - f_dir z|)
    (h_chart_absorb : (4 : ℝ) * δ ^ (-ε) * L_chart ^ τ ≤ δ ^ (-q_pole_loss)) :
    ∃ (Θ_transport : Set ℝ)
      (ν_transport : Measure ℝ),
      (Θ_transport ⊆ Θ_bad' ∩ Set.Ioi (y1 + δ ^ q_pole) ∨
       Θ_transport ⊆ Θ_bad' ∩ Set.Iio (y1 - δ ^ q_pole)) ∧
      ν Θ_transport ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) ∧
      ν Θ_transport > 0 ∧ ν Θ_transport ≠ ⊤ ∧
      ν_transport = (ν Θ_transport)⁻¹ • Measure.map f_dir (ν.restrict Θ_transport) ∧
      IsProbabilityMeasure ν_transport ∧
      IsDirectionFrostman δ τ (C_ν * ((4 : ℝ) * δ ^ (-ε) * L_chart ^ τ)) ν_transport ∧
      (∀ y ∈ Θ_transport, y ≠ y1) := by
  let r_pole : ℝ := δ ^ q_pole
  have hr_pole_pos : 0 < r_pole := Real.rpow_pos_of_pos hδ_pos q_pole
  have hδε_pos : 0 < δ ^ ε := Real.rpow_pos_of_pos hδ_pos ε
  have hδε_half_pos : 0 < (1 / 2 : ℝ) * δ ^ ε := by positivity
  have hδε_quarter_pos : 0 < (1 / 4 : ℝ) * δ ^ ε := by positivity

  -- Extract Frostman components
  have hν_univ : ν Set.univ = 1 := hν_frost.1
  have hν_supp : ν.support ⊆ Set.Icc (0 : ℝ) 1 := hν_frost.2.1
  have hν_reg : ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
      ν (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C_ν * r ^ τ) := hν_frost.2.2

  -- C_ν ≥ 1 (needed for large-radius case)
  have hC_ν_ge1 : 1 ≤ C_ν := by
    have h4 : ν (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) ≤
        ENNReal.ofReal (C_ν * (1 : ℝ) ^ τ) :=
      hν_reg (1 / 2 : ℝ) 1 (by linarith) (by norm_num)
    have h5 : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1) := by
      intro x hx; have hxl : 0 ≤ x := hx.1; have hxr : x ≤ 1 := hx.2
      constructor <;> norm_num <;> linarith
    have h_supp_compl_null : ν (ν.supportᶜ) = 0 :=
      MeasureTheory.Measure.measure_compl_support (μ := ν)
    have h_Icc_compl_null : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
      measure_mono_null (compl_subset_compl.mpr hν_supp) h_supp_compl_null
    have h_Icc_eq_univ : ν (Set.Icc (0 : ℝ) 1) = ν Set.univ := by
      have h1 : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := h_Icc_compl_null
      have h2 : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = ν Set.univ - ν (Set.Icc (0 : ℝ) 1) :=
        MeasureTheory.measure_compl isClosed_Icc.measurableSet (by simp)
      have h3 : ν Set.univ - ν (Set.Icc (0 : ℝ) 1) = 0 := by rw [← h2, h1]
      have h4 : ν Set.univ ≤ ν (Set.Icc (0 : ℝ) 1) := tsub_eq_zero_iff_le.mp h3
      have h5 : ν (Set.Icc (0 : ℝ) 1) ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      exact le_antisymm h5 h4
    have h6 : ν (Set.Icc (0 : ℝ) 1) = 1 := by rw [h_Icc_eq_univ, hν_univ]
    have h9 : ν (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) ≥ 1 := by
      calc _ ≥ ν (Set.Icc (0 : ℝ) 1) := measure_mono h5
           _ = 1 := h6
    have h10 : (1 : ENNReal) ≤ ENNReal.ofReal (C_ν * (1 : ℝ) ^ τ) := le_trans h9 h4
    simpa using h10

  -- Measurability of f_dir: Lipschitz on ℝ \ {y1}, hence continuous there,
  -- hence Borel measurable (single exceptional point is measurable).
  let C_lip : ℝ := δ ^ (-q_pole_loss)
  have hC_lip_pos : 0 < C_lip := Real.rpow_pos_of_pos hδ_pos (-q_pole_loss)
  have hf_dir_cont_on : ContinuousOn f_dir ({y1}ᶜ : Set ℝ) := by
    intro x hx
    have h_x_ne : x ≠ y1 := hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    let δ' := min (dist x y1 / 2) (ε / (C_lip + 1))
    have h1_pos : 0 < dist x y1 / 2 := by
      have h : 0 < dist x y1 := dist_pos.mpr h_x_ne
      linarith
    have h2_pos : 0 < ε / (C_lip + 1) := by positivity
    have hδ'_pos : 0 < δ' := lt_min h1_pos h2_pos
    refine' ⟨δ', hδ'_pos, _⟩
    intro z hz_in hz_lt
    have h_z_ne : z ≠ y1 := hz_in
    have h4 : |f_dir z - f_dir x| ≤ C_lip * |z - x| := h_f_dir_lip z x h_z_ne h_x_ne
    have h5 : |z - x| < ε / (C_lip + 1) := lt_of_lt_of_le hz_lt (min_le_right _ _)
    simpa [Real.dist_eq] using calc
      |f_dir z - f_dir x| ≤ C_lip * |z - x| := h4
      _ ≤ (C_lip + 1) * |z - x| := by gcongr <;> linarith
      _ < (C_lip + 1) * (ε / (C_lip + 1)) := by gcongr
      _ = ε := by field_simp [hC_lip_pos.ne'] <;> ring
  have hf_dir_meas : Measurable f_dir := by
    have h_main : ∀ (U : Set ℝ), IsOpen U → MeasurableSet (f_dir ⁻¹' U) := by
      intro U hU
      have h1 : IsOpen (({y1}ᶜ : Set ℝ) ∩ f_dir ⁻¹' U) :=
        hf_dir_cont_on.isOpen_inter_preimage (isOpen_compl_singleton) hU
      have h1' : IsOpen (f_dir ⁻¹' U ∩ ({y1}ᶜ : Set ℝ)) := by
        have h_eq : ({y1}ᶜ : Set ℝ) ∩ f_dir ⁻¹' U = f_dir ⁻¹' U ∩ ({y1}ᶜ : Set ℝ) := by
          ext z; simp [and_comm]
        rw [h_eq] at h1; exact h1
      have h2 : f_dir ⁻¹' U = (f_dir ⁻¹' U ∩ ({y1}ᶜ : Set ℝ)) ∪ (f_dir ⁻¹' U ∩ {y1}) := by
        ext x; by_cases h : x = y1 <;> simp [h] <;> tauto
      rw [h2]
      have h3 : MeasurableSet (f_dir ⁻¹' U ∩ {y1}) := by
        have h4 : Set.Subsingleton (f_dir ⁻¹' U ∩ {y1}) := by
          intro z hz w hw
          have hz' : z = y1 := by simpa [Set.mem_singleton_iff] using hz.2
          have hw' : w = y1 := by simpa [Set.mem_singleton_iff] using hw.2
          exact hz'.trans hw'.symm
        exact h4.measurableSet
      exact h1'.measurableSet.union h3
    exact measurable_of_isOpen h_main

  -- Step 1: Pigeonhole selection
  let U_left := Θ_bad' ∩ Set.Iio (y1 - r_pole)
  let U_right := Θ_bad' ∩ Set.Ioi (y1 + r_pole)

  -- Closed ball around pole
  let B_closed := Set.Icc (y1 - r_pole) (y1 + r_pole)
  let B_open := Metric.ball y1 r_pole
  let B_union := (B_open ∪ {y1 - r_pole}) ∪ {y1 + r_pole}

  have h_B_sub : B_closed ⊆ B_union := by
    intro x hx
    have h1 : y1 - r_pole ≤ x := hx.1
    have h2 : x ≤ y1 + r_pole := hx.2
    by_cases h3 : x = y1 - r_pole
    · have h_goal : x ∈ B_union := by
        have h9 : {y1 - r_pole} ⊆ B_union := by
          intro z hz
          have h10 : z ∈ (B_open ∪ {y1 - r_pole}) ∪ {y1 + r_pole} := Or.inl (Or.inr hz)
          exact h10
        exact h9 (by simp [h3])
      exact h_goal
    · by_cases h4 : x = y1 + r_pole
      · have h_goal : x ∈ B_union := by
          have h9 : {y1 + r_pole} ⊆ B_union := by
            intro z hz
            have h10 : z ∈ (B_open ∪ {y1 - r_pole}) ∪ {y1 + r_pole} := Or.inr hz
            exact h10
          exact h9 (by simp [h4])
        exact h_goal
      · have h5 : y1 - r_pole < x := lt_of_le_of_ne h1 (Ne.symm h3)
        have h6 : x < y1 + r_pole := lt_of_le_of_ne h2 h4
        have h7 : |x - y1| < r_pole := by
          rw [abs_lt] <;> constructor <;> linarith
        have h8 : x ∈ B_open := h7
        have h9 : B_open ⊆ B_union := by
          intro z hz
          have h10 : z ∈ (B_open ∪ {y1 - r_pole}) ∪ {y1 + r_pole} := Or.inl (Or.inl hz)
          exact h10
        exact h9 h8

  have h_ν_B_closed : ν B_closed ≤ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) := by
    have h : ν B_closed ≤ ν B_union := measure_mono h_B_sub
    have h2 : ν B_union ≤ ν B_open + ν {y1 - r_pole} + ν {y1 + r_pole} := by
      dsimp only [B_union]
      calc ν ((B_open ∪ {y1 - r_pole}) ∪ {y1 + r_pole})
        ≤ ν (B_open ∪ {y1 - r_pole}) + ν {y1 + r_pole} := measure_union_le _ _
      _ ≤ ν B_open + ν {y1 - r_pole} + ν {y1 + r_pole} := by
        gcongr <;> exact measure_union_le _ _
    have h3 : ν B_closed ≤ ν B_open + ν {y1 - r_pole} + ν {y1 + r_pole} := le_trans h h2
    have h4 : ν {y1 - r_pole} = 0 := h_boundary_null.1
    have h5 : ν {y1 + r_pole} = 0 := h_boundary_null.2
    have h6 : ν B_closed ≤ ν B_open := by
      calc ν B_closed
        ≤ ν B_open + ν {y1 - r_pole} + ν {y1 + r_pole} := h3
      _ = ν B_open + 0 + 0 := by rw [h4, h5]
      _ = ν B_open := by simp
    exact le_trans h6 h_pole_mass_small

  -- Complement of U_left ∪ U_right within Θ_bad' is contained in B_closed
  have h_compl_sub : Θ_bad' \ (U_left ∪ U_right) ⊆ B_closed := by
    intro y hy
    have h_y_in : y ∈ Θ_bad' := hy.1
    have h_not_in : y ∉ U_left ∪ U_right := hy.2
    have h1 : ¬(y < y1 - r_pole) := by intro h2; exact h_not_in (Or.inl ⟨h_y_in, h2⟩)
    have h2 : ¬(y > y1 + r_pole) := by intro h3; exact h_not_in (Or.inr ⟨h_y_in, h3⟩)
    have h3 : y1 - r_pole ≤ y := by linarith
    have h4 : y ≤ y1 + r_pole := by linarith
    exact ⟨h3, h4⟩

  have h_disj : Disjoint U_left U_right := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    have h5 : y < y1 - r_pole := hy1.2
    have h6 : y > y1 + r_pole := hy2.2
    linarith

  -- Mass of union ≥ δ^ε / 2
  have h_mass_union : ν (U_left ∪ U_right) ≥ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) := by
    by_contra h
    have h' : ν (U_left ∪ U_right) < ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) := by
      exact lt_of_not_ge h
    have h4 : ν (Θ_bad' \ (U_left ∪ U_right)) ≤ ν B_closed := measure_mono h_compl_sub
    have h5 : ν (Θ_bad' \ (U_left ∪ U_right)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) :=
      le_trans h4 h_ν_B_closed
    have h6 : ν Θ_bad' ≤ ν (U_left ∪ U_right) + ν (Θ_bad' \ (U_left ∪ U_right)) := by
      have h7 : Θ_bad' ⊆ (U_left ∪ U_right) ∪ (Θ_bad' \ (U_left ∪ U_right)) := by
        intro y hy; by_cases h : y ∈ U_left ∪ U_right <;> simp [h, hy] <;> tauto
      calc ν Θ_bad' ≤ ν ((U_left ∪ U_right) ∪ (Θ_bad' \ (U_left ∪ U_right))) := measure_mono h7
           _ ≤ ν (U_left ∪ U_right) + ν (Θ_bad' \ (U_left ∪ U_right)) := measure_union_le _ _
    have h7 : ν (U_left ∪ U_right) + ν (Θ_bad' \ (U_left ∪ U_right)) <
        ENNReal.ofReal (δ ^ ε) := by
      have h81 : (1 / 2 : ℝ) * δ ^ ε + (1 / 2 : ℝ) * δ ^ ε = δ ^ ε := by linarith
      have h8 : ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) + ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) =
          ENNReal.ofReal (δ ^ ε) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), h81]
      have hc_ne_top : ν (Θ_bad' \ (U_left ∪ U_right)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top h5
      have h9 : ν (U_left ∪ U_right) + ν (Θ_bad' \ (U_left ∪ U_right)) <
          ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) + ν (Θ_bad' \ (U_left ∪ U_right)) :=
        ENNReal.add_lt_add_right hc_ne_top h'
      have h10 : ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) + ν (Θ_bad' \ (U_left ∪ U_right)) ≤
          ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) + ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) := by
        gcongr
      have h11 : ν (U_left ∪ U_right) + ν (Θ_bad' \ (U_left ∪ U_right)) <
          ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) + ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) :=
        lt_of_lt_of_le h9 h10
      rw [h8] at h11
      exact h11
    have h9 : ν Θ_bad' < ENNReal.ofReal (δ ^ ε) := lt_of_le_of_lt h6 h7
    exact not_le.mpr h9 hΘ_bad'_mass

  -- Pigeonhole: one side has mass ≥ δ^ε / 4
  have h_pigeonhole : ν U_left ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) ∨
      ν U_right ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) := by
    by_cases h : ν U_left ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε)
    · exact Or.inl h
    · have h' : ν U_left < ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) := lt_of_not_ge h
      by_cases h2 : ν U_right ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε)
      · exact Or.inr h2
      · have h3 : ν U_right < ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) := lt_of_not_ge h2
        have h4 : ν U_left + ν U_right < ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) := by
          have h51 : (1 / 4 : ℝ) * δ ^ ε + (1 / 4 : ℝ) * δ ^ ε = (1 / 2 : ℝ) * δ ^ ε := by linarith
          have h5 : ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) + ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) =
              ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), h51]
          have h6 : ν U_left + ν U_right <
              ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) + ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) :=
            ENNReal.add_lt_add h' h3
          rw [h5] at h6
          exact h6
        have h5 : ν (U_left ∪ U_right) ≤ ν U_left + ν U_right := measure_union_le _ _
        have h6 : ν (U_left ∪ U_right) < ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε) :=
          lt_of_le_of_lt h5 h4
        exact False.elim (lt_irrefl (ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε)) (lt_of_le_of_lt h_mass_union h6))

  -- Choose Θ_transport
  let Θ_transport : Set ℝ :=
    if ν U_left ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) then U_left else U_right

  have hΘ_mass : ν Θ_transport ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) := by
    dsimp only [Θ_transport]
    split_ifs <;> tauto

  have hΘ_pos : 0 < ν Θ_transport := by
    have h : 0 < ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) :=
      ENNReal.ofReal_pos.mpr hδε_quarter_pos
    exact h.trans_le hΘ_mass

  have hΘ_ne_top : ν Θ_transport ≠ ⊤ := by
    have h : ν Θ_transport ≤ ν Set.univ := measure_mono (Set.subset_univ _)
    rw [hν_univ] at h
    exact ne_top_of_le_ne_top (by simp) h

  have hΘ_side : Θ_transport ⊆ Θ_bad' ∩ Set.Ioi (y1 + r_pole) ∨
      Θ_transport ⊆ Θ_bad' ∩ Set.Iio (y1 - r_pole) := by
    dsimp only [Θ_transport]
    split_ifs with h
    · exact Or.inr (show U_left ⊆ Θ_bad' ∩ Set.Iio (y1 - r_pole) from Subset.refl U_left)
    · exact Or.inl (show U_right ⊆ Θ_bad' ∩ Set.Ioi (y1 + r_pole) from Subset.refl U_right)

  have hΘ_sub_bad : Θ_transport ⊆ Θ_bad' := by
    rcases hΘ_side with (h | h)
    · intro y hy; exact (h hy).1
    · intro y hy; exact (h hy).1

  have h_pole_avoid : ∀ y ∈ Θ_transport, y ≠ y1 := by
    rcases hΘ_side with (h | h)
    · intro y hy
      have h5 : y ∈ Set.Ioi (y1 + r_pole) := (h hy).2
      have h6 : y > y1 + r_pole := h5
      linarith
    · intro y hy
      have h5 : y ∈ Set.Iio (y1 - r_pole) := (h hy).2
      have h6 : y < y1 - r_pole := h5
      linarith

  -- Step 2: Define transport measure
  let ν_transport : Measure ℝ :=
    (ν Θ_transport)⁻¹ • Measure.map f_dir (ν.restrict Θ_transport)

  -- Step 3: Probability measure
  have h_prob : IsProbabilityMeasure ν_transport := by
    have h_map_univ : (Measure.map f_dir (ν.restrict Θ_transport)) Set.univ = ν Θ_transport := by
      rw [Measure.map_apply hf_dir_meas (MeasurableSet.univ)] <;> simp
    refine' ⟨_⟩
    have h : ν_transport Set.univ = (ν Θ_transport)⁻¹ * (Measure.map f_dir (ν.restrict Θ_transport)) Set.univ := by
      simp [ν_transport] <;> rfl
    rw [h, h_map_univ]
    exact ENNReal.inv_mul_cancel hΘ_pos.ne' hΘ_ne_top

  -- Step 4: Support ⊆ [0,1]
  have h_range_transport : ∀ y ∈ Θ_transport, f_dir y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    exact h_f_dir_range y (hΘ_sub_bad hy)

  have h_compl_null : ν_transport ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    have h1 : (Measure.map f_dir (ν.restrict Θ_transport)) ((Set.Icc (0 : ℝ) 1)ᶜ) =
        (ν.restrict Θ_transport) (f_dir ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ)) := by
      rw [Measure.map_apply hf_dir_meas (isClosed_Icc.isOpen_compl.measurableSet)]
    have h_meas_set : MeasurableSet (f_dir ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ)) :=
      isClosed_Icc.isOpen_compl.measurableSet.preimage hf_dir_meas
    have h2 : (ν.restrict Θ_transport) (f_dir ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ)) =
        ν (f_dir ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ) ∩ Θ_transport) := by
      rw [Measure.restrict_apply h_meas_set] <;> rfl
    have h3 : f_dir ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ) ∩ Θ_transport = ∅ := by
      have h_nonempty : ¬ Set.Nonempty (f_dir ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ) ∩ Θ_transport) := by
        rintro ⟨z, hz⟩
        have hz1 : f_dir z ∉ Set.Icc (0 : ℝ) 1 := hz.1
        have hz2 : z ∈ Θ_transport := hz.2
        have h4 : f_dir z ∈ Set.Icc (0 : ℝ) 1 := h_range_transport z hz2
        exact hz1 h4
      simpa [Set.not_nonempty_iff_eq_empty] using h_nonempty
    have h4 : ν_transport ((Set.Icc (0 : ℝ) 1)ᶜ) =
        (ν Θ_transport)⁻¹ * (Measure.map f_dir (ν.restrict Θ_transport)) ((Set.Icc (0 : ℝ) 1)ᶜ) := by
      simp [ν_transport] <;> rfl
    rw [h4, h1, h2, h3] <;> simp

  have h_supp : ν_transport.support ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    by_contra h
    have h5 : x ∈ (Set.Icc (0 : ℝ) 1)ᶜ := h
    have h6 : IsOpen ((Set.Icc (0 : ℝ) 1)ᶜ) := isClosed_Icc.isOpen_compl
    have h7 : 0 < ν_transport ((Set.Icc (0 : ℝ) 1)ᶜ) := by
      rw [Measure.mem_support_iff_forall] at hx
      exact hx ((Set.Icc (0 : ℝ) 1)ᶜ) (h6.mem_nhds h5)
    rw [h_compl_null] at h7
    exact False.elim (lt_irrefl 0 h7)

  -- Step 5: Frostman property with midpoint trick
  have h_norm_factor : (ν Θ_transport)⁻¹ ≤ ENNReal.ofReal ((4 : ℝ) * δ ^ (-ε)) := by
    have h1 : ν Θ_transport ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε) := hΘ_mass
    have h2 : (ν Θ_transport)⁻¹ ≤ (ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε))⁻¹ := by gcongr
    have h31 : ((1 / 4 : ℝ) * δ ^ ε)⁻¹ = (4 : ℝ) * δ ^ (-ε) := by
      have h_pos1 : 0 < (1 / 4 : ℝ) * δ ^ ε := hδε_quarter_pos
      field_simp [h_pos1.ne']
      have h_eq : δ ^ ε * δ ^ (-ε) = 1 := by
        rw [← Real.rpow_add hδ_pos] <;> ring_nf <;> norm_num
      linarith
    have h32 : (ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε))⁻¹ =
        ENNReal.ofReal (((1 / 4 : ℝ) * δ ^ ε)⁻¹) := by
      exact (ENNReal.ofReal_inv_of_pos (x := (1 / 4 : ℝ) * δ ^ ε) hδε_quarter_pos).symm
    rw [h32, h31] at h2
    exact h2

  set C_frost : ℝ := C_ν * ((4 : ℝ) * δ ^ (-ε) * L_chart ^ τ) with hC_frost_def

  have h_frost : ∀ (x : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
      ν_transport (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C_frost * r ^ τ) := by
    intro x r hrδ hr1
    let I := Set.Icc (x - r) (x + r)
    let S := Θ_transport ∩ f_dir ⁻¹' I
    have hr_pos : 0 < r := by linarith
    have h_measI : MeasurableSet I := measurableSet_Icc
    have h_eq1 : (Measure.map f_dir (ν.restrict Θ_transport)) I =
        (ν.restrict Θ_transport) (f_dir ⁻¹' I) := by
      rw [Measure.map_apply hf_dir_meas h_measI]
    have h_eq2 : (ν.restrict Θ_transport) (f_dir ⁻¹' I) = ν S := by
      have h_set : f_dir ⁻¹' I ∩ Θ_transport = S := by
        ext z; simp [S, and_comm]
      rw [Measure.restrict_apply (h_measI.preimage hf_dir_meas), h_set]
    have h_eq : ν_transport I = (ν Θ_transport)⁻¹ * ν S := by
      have h : ν_transport I = (ν Θ_transport)⁻¹ * (Measure.map f_dir (ν.restrict Θ_transport)) I := by
        simp [ν_transport] <;> rfl
      rw [h, h_eq1, h_eq2]
    rw [h_eq]
    by_cases hS : S = ∅
    · rw [hS]; simp
    · -- S nonempty
      rcases Set.nonempty_iff_ne_empty.mpr hS with ⟨y0, hy0⟩
      have h_y0_in : y0 ∈ Θ_transport := hy0.1
      have h_y0_ne : y0 ≠ y1 := h_pole_avoid y0 h_y0_in

      -- Diameter bound: |y - z| ≤ 2 * L_chart * r for all y, z ∈ S
      have h_diam : ∀ y ∈ S, ∀ z ∈ S, |y - z| ≤ 2 * L_chart * r := by
        intro y hy z hz
        have h_y_in : y ∈ Θ_transport := hy.1
        have h_z_in : z ∈ Θ_transport := hz.1
        have h_y_ne : y ≠ y1 := h_pole_avoid y h_y_in
        have h_z_ne : z ≠ y1 := h_pole_avoid z h_z_in
        have h1 : f_dir y ∈ I := hy.2
        have h2 : f_dir z ∈ I := hz.2
        have h3 : |f_dir y - f_dir z| ≤ 2 * r := by
          rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        have h4 := h_f_dir_colip y (hΘ_sub_bad h_y_in) z (hΘ_sub_bad h_z_in) h_y_ne h_z_ne
        calc |y - z| ≤ L_chart * |f_dir y - f_dir z| := h4
          _ ≤ L_chart * (2 * r) := by gcongr
          _ = 2 * L_chart * r := by ring

      -- S is bounded (diameter finite)
      have h_bounded : BddAbove S ∧ BddBelow S := by
        have h1 : ∀ y ∈ S, |y - y0| ≤ 2 * L_chart * r := fun y hy => h_diam y hy y0 hy0
        constructor
        · use y0 + 2 * L_chart * r
          intro y hy
          have h2 : |y - y0| ≤ 2 * L_chart * r := h1 y hy
          linarith [abs_le.mp h2]
        · use y0 - 2 * L_chart * r
          intro y hy
          have h2 : |y - y0| ≤ 2 * L_chart * r := h1 y hy
          linarith [abs_le.mp h2]

      have hS' : Set.Nonempty S := Set.nonempty_iff_ne_empty.mpr hS
      let a : ℝ := sInf S
      let b : ℝ := sSup S

      have ha_le : ∀ y ∈ S, a ≤ y := fun y hy => csInf_le h_bounded.2 hy
      have h_le_b : ∀ y ∈ S, y ≤ b := fun y hy => le_csSup h_bounded.1 hy

      -- b - a ≤ 2 * L_chart * r
      have h_span : b - a ≤ 2 * L_chart * r := by
        have h1 : ∀ z ∈ S, b ≤ z + 2 * L_chart * r := by
          intro z hz
          have h2 : ∀ y ∈ S, y ≤ z + 2 * L_chart * r := by
            intro y hy
            have h3 : |y - z| ≤ 2 * L_chart * r := h_diam y hy z hz
            have h4 : y - z ≤ 2 * L_chart * r := by linarith [abs_le.mp h3]
            linarith
          exact csSup_le hS' h2
        have h3 : ∀ z ∈ S, b - 2 * L_chart * r ≤ z := by
          intro z hz
          linarith [h1 z hz]
        have h4 : b - 2 * L_chart * r ≤ a := le_csInf hS' h3
        linarith

      let c : ℝ := (a + b) / 2
      let R : ℝ := L_chart * r

      -- S ⊆ [c - R, c + R]
      have h_S_sub : S ⊆ Set.Icc (c - R) (c + R) := by
        intro y hy
        have h6 : a ≤ y := ha_le y hy
        have h7 : y ≤ b := h_le_b y hy
        have h8 : y - c ≤ (b - a) / 2 := by
          dsimp only [c]
          have h : 2 * y - a - b ≤ b - a := by linarith
          linarith
        have h9 : c - y ≤ (b - a) / 2 := by
          dsimp only [c]
          have h : a + b - 2 * y ≤ b - a := by linarith
          linarith
        have h10 : (b - a) / 2 ≤ R := by
          dsimp only [R]
          linarith [h_span]
        constructor
        · linarith
        · linarith

      have hR_pos : 0 < R := by positivity
      have hR_ge_delta : δ ≤ R := by
        have h1 : δ ≤ r := hrδ
        have h2 : 1 ≤ L_chart := hL_chart_ge_one
        nlinarith

      by_cases h_large : R > 1
      · -- Large radius: use probability bound
        have h5 : ν S ≤ 1 := by
          have h6 : ν S ≤ ν Set.univ := measure_mono (Set.subset_univ _)
          rw [hν_univ] at h6; exact h6
        have h6 : 1 ≤ C_ν * R ^ τ := by
          have h7 : 1 < R := h_large
          have h8 : 1 < R ^ τ := Real.one_lt_rpow h7 hτ_pos
          have h9 : 1 ≤ C_ν := hC_ν_ge1
          have h10 : 0 ≤ C_ν := by linarith
          nlinarith
        have h11 : C_ν * R ^ τ = C_ν * L_chart ^ τ * r ^ τ := by
          have h12 : R = L_chart * r := rfl
          rw [h12]
          have h13 : (L_chart * r) ^ τ = L_chart ^ τ * r ^ τ :=
            Real.mul_rpow (by linarith) (by linarith)
          rw [h13] <;> ring
        have h14 : 1 ≤ C_ν * L_chart ^ τ * r ^ τ := by
          rw [← h11]; exact h6
        have h15 : C_frost * r ^ τ = (4 : ℝ) * δ ^ (-ε) * (C_ν * L_chart ^ τ * r ^ τ) := by
          rw [hC_frost_def] <;> ring
        calc (ν Θ_transport)⁻¹ * ν S
        ≤ ENNReal.ofReal ((4 : ℝ) * δ ^ (-ε)) * 1 := by gcongr
        _ = ENNReal.ofReal ((4 : ℝ) * δ ^ (-ε)) := by simp
        _ ≤ ENNReal.ofReal (C_frost * r ^ τ) := by
          rw [h15]
          have h16 : 0 ≤ (4 : ℝ) * δ ^ (-ε) := by positivity
          have h17 : (4 : ℝ) * δ ^ (-ε) ≤ (4 : ℝ) * δ ^ (-ε) * (C_ν * L_chart ^ τ * r ^ τ) :=
            le_mul_of_one_le_right h16 h14
          exact ENNReal.ofReal_le_ofReal h17
      · -- Small radius: R ≤ 1, apply Frostman
        have h_small : R ≤ 1 := by linarith
        have h_frost_S : ν S ≤ ENNReal.ofReal (C_ν * R ^ τ) :=
          calc ν S ≤ ν (Set.Icc (c - R) (c + R)) := measure_mono h_S_sub
               _ ≤ ENNReal.ofReal (C_ν * R ^ τ) := hν_reg c R hR_ge_delta h_small
        have h_R_pow : R ^ τ = L_chart ^ τ * r ^ τ := by
          have h1 : R = L_chart * r := rfl
          rw [h1]
          exact Real.mul_rpow (by linarith) (by linarith)
        have h_final : (4 : ℝ) * δ ^ (-ε) * (C_ν * R ^ τ) ≤ C_frost * r ^ τ := by
          have h_eq : (4 : ℝ) * δ ^ (-ε) * (C_ν * R ^ τ) = C_frost * r ^ τ := by
            have h2 : R ^ τ = L_chart ^ τ * r ^ τ := h_R_pow
            simp only [hC_frost_def, h2]
            <;> ring
          exact le_of_eq h_eq
        calc (ν Θ_transport)⁻¹ * ν S
        ≤ ENNReal.ofReal ((4 : ℝ) * δ ^ (-ε)) * ENNReal.ofReal (C_ν * R ^ τ) := by gcongr
        _ = ENNReal.ofReal ((4 : ℝ) * δ ^ (-ε) * (C_ν * R ^ τ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (C_frost * r ^ τ) := by
          exact ENNReal.ofReal_le_ofReal h_final

  -- Assemble IsDirectionFrostman
  have h_main_frost : IsDirectionFrostman δ τ C_frost ν_transport := by
    exact ⟨h_prob.1, h_supp, h_frost⟩

  exact ⟨Θ_transport, ν_transport, hΘ_side, hΘ_mass, hΘ_pos, hΘ_ne_top,
    rfl, h_prob, h_main_frost, h_pole_avoid⟩

/-- Helper: a map that is Lipschitz away from a pole is continuous on the
complement and Borel measurable. -/
lemma projective_chart_continuous_measurable
    {δ q_pole_loss y1 : ℝ} (hδ_pos : 0 < δ) (hq_pole_loss_pos : 0 < q_pole_loss)
    (f_dir : ℝ → ℝ)
    (h_f_dir_lip : ∀ y z, y ≠ y1 → z ≠ y1 →
      |f_dir y - f_dir z| ≤ δ ^ (-q_pole_loss) * |y - z|) :
    ContinuousOn f_dir ({y1}ᶜ : Set ℝ) ∧ Measurable f_dir := by
  let C_lip := δ ^ (-q_pole_loss)
  have hC_lip_pos : 0 < C_lip := Real.rpow_pos_of_pos hδ_pos (-q_pole_loss)
  have h_cont : ContinuousOn f_dir ({y1}ᶜ : Set ℝ) := by
    intro x hx
    have h_x_ne : x ≠ y1 := hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    let δ' := min (dist x y1 / 2) (ε / (C_lip + 1))
    have hδ'_pos : 0 < δ' := by
      have h1 : 0 < dist x y1 := dist_pos.mpr h_x_ne
      positivity
    refine' ⟨δ', hδ'_pos, _⟩
    intro z hz_in hz_lt
    have h_z_ne : z ≠ y1 := hz_in
    have h4 : |f_dir z - f_dir x| ≤ C_lip * |z - x| := h_f_dir_lip z x h_z_ne h_x_ne
    have h5 : |z - x| < ε / (C_lip + 1) := lt_of_lt_of_le hz_lt (min_le_right _ _)
    have h6 : |f_dir z - f_dir x| < ε := by
      calc |f_dir z - f_dir x|
        ≤ C_lip * |z - x| := h4
      _ ≤ (C_lip + 1) * |z - x| := by
        have h7 : C_lip ≤ C_lip + 1 := by linarith
        exact mul_le_mul_of_nonneg_right h7 (abs_nonneg _)
      _ < (C_lip + 1) * (ε / (C_lip + 1)) := by
        exact mul_lt_mul_of_pos_left h5 (by linarith)
      _ = ε := by field_simp [hC_lip_pos.ne'] <;> ring
    simpa [Real.dist_eq] using h6
  have h_meas : Measurable f_dir := by
    have h_main : ∀ (U : Set ℝ), IsOpen U → MeasurableSet (f_dir ⁻¹' U) := by
      intro U hU
      have h1 : IsOpen (({y1}ᶜ : Set ℝ) ∩ f_dir ⁻¹' U) :=
        h_cont.isOpen_inter_preimage (isOpen_compl_singleton) hU
      have h1' : IsOpen (f_dir ⁻¹' U ∩ ({y1}ᶜ : Set ℝ)) := by
        have h_eq : ({y1}ᶜ : Set ℝ) ∩ f_dir ⁻¹' U = f_dir ⁻¹' U ∩ ({y1}ᶜ : Set ℝ) := by
          ext z; simp [and_comm]
        rw [h_eq] at h1; exact h1
      have h2 : f_dir ⁻¹' U = (f_dir ⁻¹' U ∩ ({y1}ᶜ : Set ℝ)) ∪ (f_dir ⁻¹' U ∩ {y1}) := by
        ext x; by_cases h : x = y1 <;> simp [h] <;> tauto
      rw [h2]
      have h3 : MeasurableSet (f_dir ⁻¹' U ∩ {y1}) := by
        have h4 : Set.Subsingleton (f_dir ⁻¹' U ∩ {y1}) := by
          intro z hz w hw
          have hz' : z = y1 := by simpa [Set.mem_singleton_iff] using hz.2
          have hw' : w = y1 := by simpa [Set.mem_singleton_iff] using hw.2
          exact hz'.trans hw'.symm
        exact h4.measurableSet
      exact h1'.measurableSet.union h3
    exact measurable_of_isOpen h_main
  exact ⟨h_cont, h_meas⟩

/-- Support correspondence for the projective line direction transport.

Given `t ∈ support(ν_transport)`, recovers an original direction `y_t ∈ ν.support`
such that `f_dir y_t = t` and `y_t` avoids the pole `y1`. -/
lemma direction_transport_projective_line_support_corr
    {δ ε κ0 q_pole q_pole_loss τ C_ν L_chart : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hε_pos : 0 < ε) (hkappa_pos : 0 < κ0)
    (hq_pole_pos : 0 < q_pole) (hq_pole_loss_pos : 0 < q_pole_loss)
    (hτ_pos : 0 < τ) (hC_ν_pos : 0 < C_ν)
    (hL_chart_pos : 0 < L_chart)
    (hL_chart_ge_one : 1 ≤ L_chart)
    {Ybar : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    {y1 y2 y3 : ℝ}
    (h_boundary_null : ν {y1 - δ ^ q_pole} = 0 ∧ ν {y1 + δ ^ q_pole} = 0)
    (hy1_in_unit : y1 ∈ Set.Icc 0 1)
    (hy2_in_unit : y2 ∈ Set.Icc 0 1)
    (hy3_in_unit : y3 ∈ Set.Icc 0 1)
    (h_sep12 : |y1 - y2| ≥ δ ^ (10 * ε / κ0))
    (h_sep13 : |y1 - y3| ≥ δ ^ (10 * ε / κ0))
    {Θ_bad' : Set ℝ}
    (hΘ_bad'_sub : Θ_bad' ⊆ Ybar)
    (hΘ_bad'_mass : ν Θ_bad' ≥ ENNReal.ofReal (δ ^ ε))
    (h_pole_mass_small :
      ν (Metric.ball y1 (δ ^ q_pole)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ ε))
    (h_r_pole : δ ^ q_pole ≤ δ ^ (10 * ε / κ0) / 2)
    (f_dir : ℝ → ℝ)
    (ν' : Measure ℝ)
    (hν'_link : ν' = Measure.map f_dir ν)
    (h_f_dir_lip : ∀ y z, y ≠ y1 → z ≠ y1 →
      |f_dir y - f_dir z| ≤ δ ^ (-q_pole_loss) * |y - z|)
    (h_f_dir_range : ∀ y ∈ Θ_bad', f_dir y ∈ Set.Icc 0 1)
    (h_f_dir_colip : ∀ y ∈ Θ_bad', ∀ z ∈ Θ_bad', y ≠ y1 → z ≠ y1 →
      |y - z| ≤ L_chart * |f_dir y - f_dir z|)
    (h_chart_absorb : (4 : ℝ) * δ ^ (-ε) * L_chart ^ τ ≤ δ ^ (-q_pole_loss))
    {Θ_transport : Set ℝ} {ν_transport : Measure ℝ}
    (hΘ_side : Θ_transport ⊆ Θ_bad' ∩ Set.Ioi (y1 + δ ^ q_pole) ∨
      Θ_transport ⊆ Θ_bad' ∩ Set.Iio (y1 - δ ^ q_pole))
    (hΘ_mass : ν Θ_transport ≥ ENNReal.ofReal ((1 / 4 : ℝ) * δ ^ ε))
    (hΘ_pos : 0 < ν Θ_transport)
    (hΘ_ne_top : ν Θ_transport ≠ ⊤)
    (hν_transport_def : ν_transport = (ν Θ_transport)⁻¹ • Measure.map f_dir (ν.restrict Θ_transport))
    (h_prob : IsProbabilityMeasure ν_transport)
    (h_main_frost : IsDirectionFrostman δ τ (C_ν * ((4 : ℝ) * δ ^ (-ε) * L_chart ^ τ)) ν_transport)
    (h_pole_avoid : ∀ y ∈ Θ_transport, y ≠ y1) :
    ∀ (t : ℝ), t ∈ ν_transport.support →
      ∃ (y_t : ℝ), y_t ∈ ν.support ∧ f_dir y_t = t ∧ y_t ≠ y1 := by
  have h_cont_meas := projective_chart_continuous_measurable hδ_pos hq_pole_loss_pos f_dir h_f_dir_lip
  have hf_dir_cont_on : ContinuousOn f_dir ({y1}ᶜ : Set ℝ) := h_cont_meas.1
  have hf_dir_meas : Measurable f_dir := h_cont_meas.2

  let A := Θ_transport ∩ ν.support
  let K := closure A

  have hν_supp_unit : ν.support ⊆ Set.Icc (0 : ℝ) 1 := hν_frost.2.1
  have hν_supp_closed : IsClosed ν.support := Measure.isClosed_support
  have hν_supp_compact : IsCompact ν.support :=
    IsCompact.of_isClosed_subset isCompact_Icc hν_supp_closed hν_supp_unit

  have hK_sub_supp : K ⊆ ν.support := by
    have h1 : A ⊆ ν.support := by
      dsimp only [A]
      exact Set.inter_subset_right
    have h2 : closure A ⊆ closure ν.support := closure_mono h1
    have h3 : closure ν.support ⊆ ν.support := IsClosed.closure_subset hν_supp_closed
    exact h2.trans h3
  have hK_compact : IsCompact K :=
    hν_supp_compact.of_isClosed_subset isClosed_closure hK_sub_supp

  have hK_avoid_pole : ∀ y ∈ K, y ≠ y1 := by
    rcases hΘ_side with (h | h)
    · have h1 : Θ_transport ⊆ Set.Ioi (y1 + δ ^ q_pole) := fun y hy => (h hy).2
      have h21 : A ⊆ Θ_transport := by dsimp only [A]; exact Set.inter_subset_left
      have h2 : A ⊆ Set.Ioi (y1 + δ ^ q_pole) := h21.trans h1
      have h2' : A ⊆ Set.Ici (y1 + δ ^ q_pole) := by
        intro x hx
        have h : y1 + δ ^ q_pole < x := by simpa [Set.mem_Ioi] using h2 hx
        simpa [Set.mem_Ici] using le_of_lt h
      have h4 : closure A ⊆ closure (Set.Ici (y1 + δ ^ q_pole)) := by
        exact closure_mono h2'
      have h5 : closure (Set.Ici (y1 + δ ^ q_pole)) = Set.Ici (y1 + δ ^ q_pole) := by
        exact closure_Ici (y1 + δ ^ q_pole)
      have h3 : K ⊆ Set.Ici (y1 + δ ^ q_pole) := by
        rw [h5] at h4
        exact h4
      intro y hy
      have h4 : y ≥ y1 + δ ^ q_pole := h3 hy
      have h5 : 0 < δ ^ q_pole := Real.rpow_pos_of_pos hδ_pos q_pole
      linarith
    · have h1 : Θ_transport ⊆ Set.Iio (y1 - δ ^ q_pole) := fun y hy => (h hy).2
      have h21 : A ⊆ Θ_transport := by dsimp only [A]; exact Set.inter_subset_left
      have h2 : A ⊆ Set.Iio (y1 - δ ^ q_pole) := h21.trans h1
      have h2' : A ⊆ Set.Iic (y1 - δ ^ q_pole) := by
        intro x hx
        have h : x < y1 - δ ^ q_pole := by simpa [Set.mem_Iio] using h2 hx
        simpa [Set.mem_Iic] using le_of_lt h
      have h4 : closure A ⊆ closure (Set.Iic (y1 - δ ^ q_pole)) := by
        exact closure_mono h2'
      have h5 : closure (Set.Iic (y1 - δ ^ q_pole)) = Set.Iic (y1 - δ ^ q_pole) := by
        exact closure_Iic (y1 - δ ^ q_pole)
      have h3 : K ⊆ Set.Iic (y1 - δ ^ q_pole) := by
        rw [h5] at h4
        exact h4
      intro y hy
      have h4 : y ≤ y1 - δ ^ q_pole := h3 hy
      have h5 : 0 < δ ^ q_pole := Real.rpow_pos_of_pos hδ_pos q_pole
      linarith

  have hK_sub_compl : K ⊆ ({y1}ᶜ : Set ℝ) := fun y hy => hK_avoid_pole y hy
  have h_cont_on_K : ContinuousOn f_dir K := hf_dir_cont_on.mono hK_sub_compl

  have h_image_compact : IsCompact (f_dir '' K) := hK_compact.image_of_continuousOn h_cont_on_K
  have h_image_closed : IsClosed (f_dir '' K) := IsCompact.isClosed h_image_compact

  have h_compl_supp_null : ν (ν.supportᶜ) = 0 := Measure.measure_compl_support (μ := ν)
  have h_diff_sub : Θ_transport \ ν.support ⊆ ν.supportᶜ := by
    intro x hx
    exact hx.2
  have h_diff_null : ν (Θ_transport \ ν.support) = 0 :=
    measure_mono_null h_diff_sub h_compl_supp_null

  have hA_sub_Θ : A ⊆ Θ_transport := by dsimp only [A]; exact Set.inter_subset_left

  have h_restrict_eq : ν.restrict Θ_transport = ν.restrict A := by
    ext s hs
    have h1 : s ∩ Θ_transport ⊆ (s ∩ A) ∪ (Θ_transport \ ν.support) := by
      intro x hx
      by_cases h : x ∈ ν.support
      · exact Or.inl ⟨hx.1, ⟨hx.2, h⟩⟩
      · exact Or.inr ⟨hx.2, h⟩
    have h2 : ν (s ∩ Θ_transport) ≤ ν (s ∩ A) := by
      calc ν (s ∩ Θ_transport)
        ≤ ν ((s ∩ A) ∪ (Θ_transport \ ν.support)) := measure_mono h1
      _ ≤ ν (s ∩ A) + ν (Θ_transport \ ν.support) := measure_union_le _ _
      _ = ν (s ∩ A) := by rw [h_diff_null]; simp
    have h3 : ν (s ∩ A) ≤ ν (s ∩ Θ_transport) := by
      have h31 : s ∩ A ⊆ s ∩ Θ_transport := by
        intro x hx
        exact ⟨hx.1, hA_sub_Θ hx.2⟩
      exact measure_mono h31
    have h4 : ν (s ∩ Θ_transport) = ν (s ∩ A) := le_antisymm h2 h3
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact h4

  have h_compl_image_null : (Measure.map f_dir (ν.restrict Θ_transport)) (f_dir '' K)ᶜ = 0 := by
    rw [h_restrict_eq]
    rw [Measure.map_apply hf_dir_meas (h_image_closed.isOpen_compl.measurableSet)]
    have h1 : (ν.restrict A) (f_dir ⁻¹' ((f_dir '' K)ᶜ)) = ν (f_dir ⁻¹' ((f_dir '' K)ᶜ) ∩ A) := by
      rw [Measure.restrict_apply ((h_image_closed.isOpen_compl.measurableSet).preimage hf_dir_meas)] <;> rfl
    rw [h1]
    have hA_sub_K : A ⊆ K := subset_closure
    have h2 : f_dir ⁻¹' ((f_dir '' K)ᶜ) ∩ A = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      intro hz
      have h3 : z ∈ K := hA_sub_K hz.2
      have h4 : f_dir z ∈ f_dir '' K := ⟨z, h3, rfl⟩
      exact hz.1 h4
    rw [h2] <;> simp

  let c := (ν Θ_transport)⁻¹
  have hc_pos : 0 < c := ENNReal.inv_pos.mpr hΘ_ne_top
  have hc_ne_top : c ≠ ⊤ := ENNReal.inv_ne_top.mpr hΘ_pos.ne'
  have h_smul_support : (c • Measure.map f_dir (ν.restrict Θ_transport)).support =
      (Measure.map f_dir (ν.restrict Θ_transport)).support := by
    ext x
    simp only [Measure.mem_support_iff_forall, Measure.coe_smul, Pi.smul_apply]
    constructor
    · intro h U hU
      have h5 : 0 < c * (Measure.map f_dir (ν.restrict Θ_transport)) U := h U hU
      exact (ENNReal.mul_pos_iff).mp h5 |>.2
    · intro h U hU
      have h6 : 0 < (Measure.map f_dir (ν.restrict Θ_transport)) U := h U hU
      exact ENNReal.mul_pos hc_pos.ne' h6.ne'

  have h_support_eq : ν_transport.support = (Measure.map f_dir (ν.restrict Θ_transport)).support := by
    rw [hν_transport_def, h_smul_support]

  have h_supp_sub : ν_transport.support ⊆ f_dir '' K := by
    rw [h_support_eq]
    intro x hx
    by_cases h_in : x ∈ f_dir '' K
    · exact h_in
    · let U := (f_dir '' K)ᶜ
      have hU_open : IsOpen U := h_image_closed.isOpen_compl
      have hxU : x ∈ U := h_in
      have h_zero : (Measure.map f_dir (ν.restrict Θ_transport)) U = 0 := h_compl_image_null
      have h_contra : x ∉ (Measure.map f_dir (ν.restrict Θ_transport)).support := by
        rw [Measure.mem_support_iff_forall x]
        intro h
        have h_pos : 0 < (Measure.map f_dir (ν.restrict Θ_transport)) U := h U (hU_open.mem_nhds hxU)
        rw [h_zero] at h_pos
        exact False.elim (lt_irrefl 0 h_pos)
      exact False.elim (h_contra hx)

  intro t ht
  have h_in_image : t ∈ f_dir '' K := h_supp_sub ht
  rcases h_in_image with ⟨y_t, hy_t_K, rfl⟩
  have hy_t_supp : y_t ∈ ν.support := hK_sub_supp hy_t_K
  have hy_t_ne : y_t ≠ y1 := hK_avoid_pole y_t hy_t_K
  exact ⟨y_t, hy_t_supp, rfl, hy_t_ne⟩

/-- Compose reverse support correspondence with a per-direction graph family.

Given that `DirectionTransportProof` provides `∀ t ∈ ν_dir.support, ∃ y ∈ Θ_sec, F_chart y = t`,
and a family of graphs `G_family y` satisfying density/projection bounds at direction `F_chart y`,
this produces the `h_graph_witness` hypothesis expected by `sector_ring_lemma51_wrapper`.

This is the Phase 7 fixed-sector composition: the sector is fixed BEFORE Ring,
so all graphs use the same sector coordinate chart.

IMPORTANT: In the Phase 7 pipeline, `G_family y` must come from the
counter-assumption failure on `F = E' ∩ (B1 × B2)`, NOT from a BSG graph.
The BSG/Ruzsa machinery establishes the density of F, but the graph points
themselves are subsets of F. -/
lemma fixed_sector_graph_witness
    {δ c_proj K_BSG εgain : ℝ}
    {B1 B2 : Set ℝ}
    {ν_dir : Measure ℝ}
    {Θ_sec : Set ℝ}
    {F_chart : ℝ → ℝ}
    (G_family : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
    (hG_family : ∀ y ∈ Θ_sec,
      IsBounded (G_family y) ∧
      (∀ p ∈ G_family y, p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
      (∀ p ∈ G_family y, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
      ENat.toENNReal (dyadicCoveringNumber δ (G_family y)) ≥
        ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 ∧
      ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (F_chart y) (G_family y))) <
        (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2)
    (h_reverse_support : ∀ t ∈ ν_dir.support, ∃ y ∈ Θ_sec, F_chart y = t) :
    ∀ (t : ℝ), t ∈ ν_dir.support →
      ∃ (G_t : Set (EuclideanSpace ℝ (Fin 2))),
        IsBounded G_t ∧
        (∀ p ∈ G_t, p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
        (∀ p ∈ G_t, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
        ENat.toENNReal (dyadicCoveringNumber δ G_t) ≥
          ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 ∧
        ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_t)) <
          (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
            ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 := by
  intro t ht
  rcases h_reverse_support t ht with ⟨y, hyΘ, rfl⟩
  have h_main := hG_family y hyΘ
  refine ⟨G_family y, h_main.1, h_main.2.1, h_main.2.2.1, h_main.2.2.2.1, ?_⟩
  simpa using h_main.2.2.2.2

end ProductLikeIncidence.ProductReduction

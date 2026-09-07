import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Targets.AntipodalSignSeparation.MeasureContinuity

/-!
# Uniform finite-family stability of polynomial bisections

Turns exact bisections by a nonzero center polynomial into simultaneous 40/40
cuts throughout a sufficiently small coefficient neighborhood.
-/

noncomputable section

open MeasureTheory MvPolynomial Set Filter
open scoped ENNReal

namespace Kakeya.CV

lemma continuous_parameterPolynomial_eval {k : ℕ}
    (P : PolynomialParameterization k) (z : Point 3) :
    Continuous (fun y : CoefficientSpace P.dim =>
      polynomialValue (parameterPolynomial P y) z) := by
  let f : (CoefficientSpace P.dim) →ₗ[ℝ] ℝ :=
    { toFun := fun y => polynomialValue (parameterPolynomial P y) z
      map_add' := by
        intro y1 y2
        have h1 : parameterPolynomial P (y1 + y2) =
            parameterPolynomial P y1 + parameterPolynomial P y2 := by
          simp [parameterPolynomial, map_add]
        rw [h1]
        simp [polynomialValue, MvPolynomial.eval_add]
      map_smul' := by
        intro c y
        have h1 : parameterPolynomial P (c • y) = c • parameterPolynomial P y := by
          simp [parameterPolynomial, map_smul]
        rw [h1]
        have h2 : polynomialValue (c • parameterPolynomial P y) z =
            c * polynomialValue (parameterPolynomial P y) z := by
          simp [polynomialValue]
        exact h2 }
  exact f.continuous_of_finiteDimensional

lemma vpos_seq_continuous {k : ℕ} (P : PolynomialParameterization k)
    (R : Set (Point 3)) (hRmeas : MeasurableSet R) (hRfin : volume R < ⊤)
    (x : CoefficientSpace P.dim) (hp : parameterPolynomial P x ≠ 0) :
    ∀ (xseq : ℕ → CoefficientSpace P.dim),
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      Filter.Tendsto
        (fun m => volume
          (R ∩ {z : Point 3 | 0 < polynomialValue (parameterPolynomial P (xseq m)) z}))
        Filter.atTop
        (nhds (volume
          (R ∩ {z : Point 3 | 0 < polynomialValue (parameterPolynomial P x) z}))) := by
  intro xseq hxseq
  let pseq := fun m => parameterPolynomial P (xseq m)
  let p := parameterPolynomial P x
  have hconv : ∀ (z : Point 3), Filter.Tendsto (fun m => polynomialValue (pseq m) z)
      Filter.atTop (nhds (polynomialValue p z)) := by
    intro z
    have hcont : Continuous
        (fun y : CoefficientSpace P.dim => polynomialValue (parameterPolynomial P y) z) :=
      continuous_parameterPolynomial_eval P z
    exact hcont.tendsto x |>.comp hxseq
  exact sign_volume_pos_continuity R hRmeas hRfin pseq p hp hconv

lemma vneg_seq_continuous {k : ℕ} (P : PolynomialParameterization k)
    (R : Set (Point 3)) (hRmeas : MeasurableSet R) (hRfin : volume R < ⊤)
    (x : CoefficientSpace P.dim) (hp : parameterPolynomial P x ≠ 0) :
    ∀ (xseq : ℕ → CoefficientSpace P.dim),
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      Filter.Tendsto
        (fun m => volume
          (R ∩ {z : Point 3 | polynomialValue (parameterPolynomial P (xseq m)) z < 0}))
        Filter.atTop
        (nhds (volume
          (R ∩ {z : Point 3 | polynomialValue (parameterPolynomial P x) z < 0}))) := by
  intro xseq hxseq
  let pseq := fun m => parameterPolynomial P (xseq m)
  let p := parameterPolynomial P x
  have hconv : ∀ (z : Point 3), Filter.Tendsto (fun m => polynomialValue (pseq m) z)
      Filter.atTop (nhds (polynomialValue p z)) := by
    intro z
    have hcont : Continuous
        (fun y : CoefficientSpace P.dim => polynomialValue (parameterPolynomial P y) z) :=
      continuous_parameterPolynomial_eval P z
    exact hcont.tendsto x |>.comp hxseq
  exact sign_volume_neg_continuity R hRmeas hRfin pseq p hp hconv

lemma seq_continuous_gt_nhds {α : Type*} [PseudoMetricSpace α]
    {f : α → ℝ≥0∞} {x : α} {c : ℝ≥0∞}
    (hcont : ∀ (xseq : ℕ → α),
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      Filter.Tendsto (f ∘ xseq) Filter.atTop (nhds (f x)))
    (h : c < f x) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ, c < f y := by
  by_contra h'
  push Not at h'
  have hseq : ∀ n : ℕ, ∃ y : α, y ∈ Metric.ball x (1 / (n + 1 : ℝ)) ∧ f y ≤ c := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    exact h' (1 / (n + 1 : ℝ)) hpos
  choose y hy1 hy2 using hseq
  have hytend : Filter.Tendsto y Filter.atTop (nhds x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨Nat.ceil (1 / ε), fun n hn => ?_⟩
    have h4 : dist (y n) x < 1 / (n + 1 : ℝ) := hy1 n
    have h7 : (1 / ε : ℝ) < (n + 1 : ℝ) := by
      have h8 : (Nat.ceil (1 / ε) : ℝ) ≥ 1 / ε := Nat.le_ceil _
      have h9 : (n : ℝ) ≥ (Nat.ceil (1 / ε) : ℝ) := by exact_mod_cast hn
      linarith
    have h10 : 1 / (n + 1 : ℝ) < ε := by
      have h11 : 0 < (1 / ε : ℝ) := by positivity
      have h12 : 1 / (n + 1 : ℝ) < 1 / (1 / ε) := one_div_lt_one_div_of_lt h11 h7
      have h13 : 1 / (1 / ε) = ε := by
        field_simp [hε.ne']
      rw [h13] at h12
      exact h12
    linarith
  have hftend : Filter.Tendsto (f ∘ y) Filter.atTop (nhds (f x)) := hcont y hytend
  have hle : ∀ n, f (y n) ≤ c := hy2
  have hIic_closed : IsClosed (Set.Iic c) := isClosed_Iic
  have h_eventually : ∀ᶠ n in Filter.atTop, f (y n) ∈ Set.Iic c := by
    filter_upwards with n
    exact hle n
  have h_main : f x ∈ Set.Iic c :=
    hIic_closed.mem_of_tendsto hftend h_eventually
  exact not_le.mpr h h_main

lemma two_fifths_lt_half {v : ℝ≥0∞} (hvpos : 0 < v) (hvfin : v < ⊤) :
    (2 / 5 : ℝ≥0∞) * v < v / 2 := by
  let v' : NNReal := v.toNNReal
  have hv_eq : (↑v' : ℝ≥0∞) = v := ENNReal.coe_toNNReal (ne_of_lt hvfin)
  have hv'pos : 0 < v' := by
    by_contra h
    have h' : v' = 0 := by simpa using h
    rw [h'] at hv_eq
    have h0 : (0 : ℝ≥0∞) = v := by simpa using hv_eq
    exact hvpos.ne' h0.symm
  have h11 : (2 / 5 : ℝ≥0∞) = ↑((2 / 5 : NNReal)) := by
    have h : ((↑((2 / 5 : NNReal)) : ℝ≥0∞)) =
        (↑2 : ℝ≥0∞) / (↑5 : ℝ≥0∞) := by
      simp [div_eq_mul_inv]
    exact h.symm
  have h1 : (2 / 5 : ℝ≥0∞) * v = ↑((2 / 5 : NNReal) * v') := by
    rw [h11, ← hv_eq]
    simp
  have h2 : v / 2 = ↑(v' / 2) := by
    have hdiv : ((↑v' : ℝ≥0∞) / 2) = ↑(v' / 2) := by
      simp [div_eq_mul_inv]
    have h : v / 2 = (↑v' : ℝ≥0∞) / 2 := by rw [← hv_eq]
    rw [h, hdiv]
  rw [h1, h2]
  apply ENNReal.coe_lt_coe.mpr
  have h4 : (2 / 5 : NNReal) < (1 / 2 : NNReal) := by norm_num
  have h5 : (2 / 5 : NNReal) * v' < (1 / 2 : NNReal) * v' :=
    mul_lt_mul_of_pos_right h4 hv'pos
  have h6 : (1 / 2 : NNReal) * v' = v' / 2 := by
    field_simp
  rw [h6] at h5
  exact h5

lemma bisection_half_volume {p : MvPolynomial (Fin 3) ℝ} (hp : p ≠ 0)
    {R : Set (Point 3)} (hRmeas : MeasurableSet R) (_hRfin : volume R < ⊤)
    (hbisect : PolynomialBisects p R) :
    volume (R ∩ {y | 0 < polynomialValue p y}) = volume R / 2 ∧
    volume (R ∩ {y | polynomialValue p y < 0}) = volume R / 2 := by
  let pos := R ∩ {y | 0 < polynomialValue p y}
  let neg := R ∩ {y | polynomialValue p y < 0}
  let zer := R ∩ polynomialZeroSet p
  have h_pos_meas : MeasurableSet pos := hRmeas.inter (posSignRegion_measurable p)
  have h_neg_meas : MeasurableSet neg := hRmeas.inter (negSignRegion_measurable p)
  have h_zer_meas : MeasurableSet zer := by
    have h : MeasurableSet (polynomialZeroSet p) :=
      isClosed_eq (continuous_polynomialValue3 p) continuous_const |>.measurableSet
    exact hRmeas.inter h
  have h_disj1 : Disjoint pos neg := by
    rw [Set.disjoint_left]
    intro y h1 h2
    have hpos : 0 < polynomialValue p y := h1.2
    have hneg : polynomialValue p y < 0 := h2.2
    linarith
  have h_disj2 : Disjoint pos zer := by
    rw [Set.disjoint_left]
    intro y h1 h2
    have hpos : 0 < polynomialValue p y := h1.2
    have hzero : polynomialValue p y = 0 := h2.2
    linarith
  have h_disj3 : Disjoint neg zer := by
    rw [Set.disjoint_left]
    intro y h1 h2
    have hneg : polynomialValue p y < 0 := h1.2
    have hzero : polynomialValue p y = 0 := h2.2
    linarith
  have h_disj4 : Disjoint (pos ∪ neg) zer :=
    Set.disjoint_union_left.mpr ⟨h_disj2, h_disj3⟩
  have h_union : R = (pos ∪ neg) ∪ zer := by
    ext y
    simp only [pos, neg, zer, Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro hy
      by_cases hpos : 0 < polynomialValue p y
      · exact Or.inl (Or.inl ⟨hy, hpos⟩)
      · by_cases hneg : polynomialValue p y < 0
        · exact Or.inl (Or.inr ⟨hy, hneg⟩)
        · have hzero : polynomialValue p y = 0 := by linarith
          exact Or.inr ⟨hy, hzero⟩
    · rintro ((h | h) | h) <;> exact h.1
  have h_vol0 : volume zer = 0 :=
    measure_mono_null inter_subset_right (polynomialZeroSet3_null p hp)
  have h_vol1 : volume (pos ∪ neg) = volume pos + volume neg :=
    MeasureTheory.measure_union' h_disj1 h_pos_meas
  have h_vol2 : volume ((pos ∪ neg) ∪ zer) = volume (pos ∪ neg) + volume zer :=
    MeasureTheory.measure_union' h_disj4 (h_pos_meas.union h_neg_meas)
  have h_volR : volume R = volume pos + volume neg := by
    calc
      volume R = volume ((pos ∪ neg) ∪ zer) := by rw [h_union]
      _ = volume (pos ∪ neg) + volume zer := h_vol2
      _ = volume pos + volume neg + volume zer := by rw [h_vol1]
      _ = volume pos + volume neg := by rw [h_vol0, add_zero]
  have h_bisect : volume neg = volume pos := hbisect
  have h_double : volume pos + volume pos = volume R := by
    calc
      volume pos + volume pos = volume pos + volume neg := by rw [h_bisect]
      _ = volume R := h_volR.symm
  have h2_pos : (2 : ℝ≥0∞) * volume pos = volume R := by
    have h : (2 : ℝ≥0∞) * volume pos = volume pos + volume pos := by
      simp [two_mul]
    rw [h]
    exact h_double
  have h_pos_eq : volume pos = volume R / 2 := by
    have h12 : (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞) = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    have h_left : (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) * volume pos) = volume pos := by
      have h_assoc : (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) * volume pos) =
          ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)) * volume pos := by
        rw [← mul_assoc]
      rw [h_assoc, h12, one_mul]
    have h_right : (2 : ℝ≥0∞)⁻¹ * volume R = volume R / 2 := by
      have hdiv : volume R / 2 = volume R * (2 : ℝ≥0∞)⁻¹ := by
        rw [div_eq_mul_inv]
      have hcomm : (2 : ℝ≥0∞)⁻¹ * volume R =
          volume R * (2 : ℝ≥0∞)⁻¹ := by rw [mul_comm]
      rw [hcomm, hdiv]
    have h : (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) * volume pos) =
        (2 : ℝ≥0∞)⁻¹ * volume R := by
      rw [h2_pos]
    rw [h_left] at h
    rw [h_right] at h
    exact h
  have h_neg_eq : volume neg = volume R / 2 := by
    rw [h_bisect, h_pos_eq]
  exact ⟨h_pos_eq, h_neg_eq⟩

theorem finite_bisections_stable_under_coefficient_perturbation
    (k : ℕ) (P : PolynomialParameterization k)
    (ι : Type*) [Fintype ι] (regions : ι → Set (Point 3))
    (x : CoefficientSpace P.dim)
    (hp : parameterPolynomial P x ≠ 0)
    (hmeas : ∀ i, MeasurableSet (regions i))
    (hfin : ∀ i, volume (regions i) < ⊤)
    (hbisect : ∀ i, PolynomialBisects (parameterPolynomial P x) (regions i)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Metric.ball x δ, ∀ i,
        PolynomialCutsAtLeast (parameterPolynomial P y) (regions i)
          (2 / 5 : ℝ≥0∞) := by
  let p := parameterPolynomial P x
  let V_pos : ι → CoefficientSpace P.dim → ℝ≥0∞ := fun i y =>
    volume (regions i ∩ {z : Point 3 | 0 < polynomialValue (parameterPolynomial P y) z})
  let V_neg : ι → CoefficientSpace P.dim → ℝ≥0∞ := fun i y =>
    volume (regions i ∩ {z : Point 3 | polynomialValue (parameterPolynomial P y) z < 0})
  have h_halves : ∀ i,
      V_pos i x = volume (regions i) / 2 ∧
      V_neg i x = volume (regions i) / 2 := by
    intro i
    have h := bisection_half_volume hp (hmeas i) (hfin i) (hbisect i)
    exact ⟨h.1, h.2⟩
  have hcont_pos : ∀ i, ∀ (xseq : ℕ → CoefficientSpace P.dim),
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      Filter.Tendsto (V_pos i ∘ xseq) Filter.atTop (nhds (V_pos i x)) := by
    intro i
    exact vpos_seq_continuous P (regions i) (hmeas i) (hfin i) x hp
  have hcont_neg : ∀ i, ∀ (xseq : ℕ → CoefficientSpace P.dim),
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      Filter.Tendsto (V_neg i ∘ xseq) Filter.atTop (nhds (V_neg i x)) := by
    intro i
    exact vneg_seq_continuous P (regions i) (hmeas i) (hfin i) x hp
  have h_main : ∀ i : ι, ∃ δ : ℝ, 0 < δ ∧
      (volume (regions i) = 0 ∨
        (∀ y ∈ Metric.ball x δ,
          (2 / 5 : ℝ≥0∞) * volume (regions i) < V_pos i y ∧
          (2 / 5 : ℝ≥0∞) * volume (regions i) < V_neg i y)) := by
    intro i
    by_cases hvol : volume (regions i) = 0
    · exact ⟨1, by norm_num, Or.inl hvol⟩
    · have hvol_pos : 0 < volume (regions i) := by
        simpa [pos_iff_ne_zero] using hvol
      have h_half_pos : V_pos i x = volume (regions i) / 2 := (h_halves i).1
      have h_half_neg : V_neg i x = volume (regions i) / 2 := (h_halves i).2
      have hfin_i : volume (regions i) < ⊤ := hfin i
      have h_lt_pos : (2 / 5 : ℝ≥0∞) * volume (regions i) < V_pos i x := by
        rw [h_half_pos]
        exact two_fifths_lt_half hvol_pos hfin_i
      have h_lt_neg : (2 / 5 : ℝ≥0∞) * volume (regions i) < V_neg i x := by
        rw [h_half_neg]
        exact two_fifths_lt_half hvol_pos hfin_i
      rcases seq_continuous_gt_nhds (hcont_pos i) h_lt_pos with
        ⟨δ1, hδ1_pos, hδ1⟩
      rcases seq_continuous_gt_nhds (hcont_neg i) h_lt_neg with
        ⟨δ2, hδ2_pos, hδ2⟩
      let δ := min δ1 δ2
      have hδ_pos : 0 < δ := lt_min hδ1_pos hδ2_pos
      have hball1 : Metric.ball x δ ⊆ Metric.ball x δ1 :=
        Metric.ball_subset_ball (min_le_left δ1 δ2)
      have hball2 : Metric.ball x δ ⊆ Metric.ball x δ2 :=
        Metric.ball_subset_ball (min_le_right δ1 δ2)
      refine ⟨δ, hδ_pos, Or.inr (fun y hy => ?_)⟩
      exact ⟨hδ1 y (hball1 hy), hδ2 y (hball2 hy)⟩
  choose δ hδ_pos hδ_cond using h_main
  by_cases h_univ_nonempty : (Finset.univ : Finset ι).Nonempty
  · have h_exists : ∃ i : ι, ∀ j : ι, δ i ≤ δ j := by
      have h := Finset.exists_min_image (Finset.univ : Finset ι) δ h_univ_nonempty
      rcases h with ⟨i, _, hmin⟩
      exact ⟨i, fun j => hmin j (Finset.mem_univ j)⟩
    rcases h_exists with ⟨i0, hmin⟩
    let δ0 := δ i0
    have hδ0_pos : 0 < δ0 := hδ_pos i0
    have hδ0_le : ∀ j, δ0 ≤ δ j := fun j => hmin j
    refine ⟨δ0, hδ0_pos, fun y hy i => ?_⟩
    have h_y_in : y ∈ Metric.ball x (δ i) :=
      Metric.ball_subset_ball (hδ0_le i) hy
    cases hδ_cond i with
    | inl hvol0 =>
      have h_zero : (2 / 5 : ℝ≥0∞) * volume (regions i) = 0 := by
        simp [hvol0]
      simp only [PolynomialCutsAtLeast, h_zero]
      exact ⟨by positivity, by positivity⟩
    | inr hstrict =>
      have h := hstrict y h_y_in
      simp only [PolynomialCutsAtLeast]
      exact ⟨h.2.le, h.1.le⟩
  · refine ⟨1, by norm_num, fun _ _ i => ?_⟩
    have h_contra : (Finset.univ : Finset ι).Nonempty :=
      ⟨i, Finset.mem_univ i⟩
    exact False.elim (h_univ_nonempty h_contra)

end Kakeya.CV

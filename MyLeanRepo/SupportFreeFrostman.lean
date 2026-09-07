module

/-
# Support-Free Finite-Scale Frostman Interface

Factorization for the product-measure bridge: separates the interval bound
from support location. The energy argument only needs probability +
finite-scale interval bound, not any support constraint.

## Main definitions

- `FiniteScaleIntervalBound δ κ C μ`: μ(univ)=1 AND
  ∀ a r, δ≤r≤1 → μ(Icc(a-r,a+r)) ≤ C*r^κ

## Main lemmas

- `product_ball_bound_support_free`: product measure ball bound from
  probability + interval bound only (no support hypothesis).
- `frostman_energy_inner_bound_finite_scale`: layer-cake energy bound
  using finite-scale interval bound + bounded diameter.
-/

public import MyLeanRepo.ProductMeasureEnergy
public import MyLeanRepo.FrostmanEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

/-! ## Support-free finite-scale interval bound -/

/-- A probability measure on ℝ with a finite-scale Frostman-type interval bound.
    No support location is assumed. -/
structure FiniteScaleIntervalBound (δ κ C : ℝ) (μ : Measure ℝ) : Prop where
  prob : μ Set.univ = 1
  bound : ∀ (a : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
    μ (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C * r ^ κ)

/-! ## Support-free product ball bound -/

/-- Product measure ball bound using only probability + interval bound.
    Generalizes `IsAllScaleFrostman.product_ball_bound` without any
    support hypothesis. Requires r ≥ δ and r ≤ 1. -/
lemma product_ball_bound_support_free
    {δ κ C : ℝ} {μ : Measure ℝ}
    (hδ_pos : 0 < δ)
    (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    (h : FiniteScaleIntervalBound δ κ C μ)
    {m : ℕ} {x : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hr_ge_delta : δ ≤ r) (hr_le_one : r ≤ 1) :
    ProductMeasureEnergy.productMeasure μ (Metric.ball x r) ≤
      ENNReal.ofReal (C ^ m * r ^ ((m : ℝ) * κ)) := by
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hr_pos : 0 < r := by linarith [hδ_pos, hr_ge_delta]
  have h_prob : μ Set.univ = 1 := h.prob
  let I : Fin m → Set ℝ := fun i => Set.Icc (x i - r) (x i + r)
  let box : Set (Fin m → ℝ) := Set.pi Set.univ I
  have hI_meas : ∀ i, MeasurableSet (I i) := fun _ => measurableSet_Icc
  have h_ball_meas : MeasurableSet (Metric.ball x r) :=
    Metric.isOpen_ball.measurableSet
  letI : IsFiniteMeasure μ := ⟨by rw [h_prob] <;> norm_num⟩
  let e : EuclideanSpace ℝ (Fin m) ≃ (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  have h1 : e '' (Metric.ball x r) ⊆ box := by
    intro f hf
    rcases hf with ⟨y, hy, rfl⟩
    have h_dist : dist y x < r := by simpa [Metric.mem_ball] using hy
    intro i _
    have h3 : |y i - x i| ≤ dist y x := ProductMeasureEnergy.coord_le_dist i
    have h4 : |y i - x i| < r := by linarith
    have h5 : y i ∈ Set.Icc (x i - r) (x i + r) := by
      rw [Set.mem_Icc]; rw [abs_lt] at h4; exact ⟨by linarith, by linarith⟩
    exact h5
  have h_preimage : e.symm ⁻¹' (Metric.ball x r) = e '' (Metric.ball x r) := by
    ext f; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hf; exact ⟨e.symm f, hf, e.apply_symm_apply f⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  have h_main : ProductMeasureEnergy.productMeasure μ (Metric.ball x r) =
      MeasureTheory.Measure.pi (fun (_ : Fin m) => μ) (e '' (Metric.ball x r)) := by
    have h_eq1 : ProductMeasureEnergy.productMeasure μ (Metric.ball x r) =
        Measure.map e.symm (MeasureTheory.Measure.pi (fun (_ : Fin m) => μ)) (Metric.ball x r) := by
      rfl
    rw [h_eq1]
    have h_apply : Measure.map e.symm (MeasureTheory.Measure.pi (fun (_ : Fin m) => μ)) (Metric.ball x r) =
        MeasureTheory.Measure.pi (fun (_ : Fin m) => μ) (e.symm ⁻¹' (Metric.ball x r)) := by
      rw [Measure.map_apply (by exact measurable_comap_iff.mpr fun ⦃t⦄ a => a) h_ball_meas]
    rw [h_apply]
    exact congr_arg (fun S : Set (Fin m → ℝ) => MeasureTheory.Measure.pi (fun (_ : Fin m) => μ) S) h_preimage
  have h3 : MeasureTheory.Measure.pi (fun (_ : Fin m) => μ) box =
      ∏ i : Fin m, μ (I i) := by exact Measure.pi_pi_aux (fun x => μ) I hI_meas
  have h4 : ∀ i : Fin m, μ (I i) ≤ ENNReal.ofReal (C * r ^ κ) := by
    intro i
    exact h.bound (x i) r hr_ge_delta hr_le_one
  have h5 : ∏ i : Fin m, μ (I i) ≤
      ∏ i : Fin m, ENNReal.ofReal (C * r ^ κ) := by
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _; exact h4 i
  have h6 : ∏ i : Fin m, ENNReal.ofReal (C * r ^ κ) =
      ENNReal.ofReal (C ^ m * r ^ ((m : ℝ) * κ)) := by
    have h7 : ∏ i : Fin m, ENNReal.ofReal (C * r ^ κ) =
        ENNReal.ofReal ((C * r ^ κ) ^ m) := by
      have h71 : ∏ i : Fin m, ENNReal.ofReal (C * r ^ κ) =
          (ENNReal.ofReal (C * r ^ κ)) ^ m := by
        simp [Finset.prod_const]
      rw [h71]
      have h72 : 0 ≤ C * r ^ κ := by
        have h73 : 0 ≤ r ^ κ := Real.rpow_nonneg hr_pos.le κ
        exact mul_nonneg hC_nonneg h73
      rw [← ENNReal.ofReal_pow h72]
    rw [h7]
    have h8 : (C * r ^ κ) ^ m = C ^ m * r ^ ((m : ℝ) * κ) := by
      have h9 : (C * r ^ κ) ^ m = C ^ m * (r ^ κ) ^ m := by
        rw [mul_pow]
      rw [h9]
      have h101 : (r ^ κ) ^ m = (r ^ κ) ^ (m : ℝ) := by
        exact Eq.symm (Real.rpow_natCast (r ^ κ) m)
      rw [h101]
      have h102 : (r ^ κ) ^ (m : ℝ) = r ^ (κ * (m : ℝ)) := by
        rw [Real.rpow_mul (by linarith)]
      rw [h102]
      have h103 : κ * (m : ℝ) = (m : ℝ) * κ := by ring
      rw [h103]
    rw [h8]
  calc ProductMeasureEnergy.productMeasure μ (Metric.ball x r)
    = MeasureTheory.Measure.pi (fun (_ : Fin m) => μ) (e '' (Metric.ball x r)) := h_main
  _ ≤ MeasureTheory.Measure.pi (fun (_ : Fin m) => μ) box :=
      measure_mono h1
  _ = ∏ i : Fin m, μ (I i) := h3
  _ ≤ ∏ i : Fin m, ENNReal.ofReal (C * r ^ κ) := h5
  _ = ENNReal.ofReal (C ^ m * r ^ ((m : ℝ) * κ)) := h6

/-! ## Finite-scale Riesz energy bound -/

/-- Integral of t^{-s} from 1 to b: (1 - b^{1-s})/(s-1). -/
private lemma integral_t_neg_s_finite {s b : ℝ} (hs : 1 < s) (hb : 1 ≤ b) :
    ∫ t in (1 : ℝ)..b, t ^ (-s) = (1 - b ^ (1 - s)) / (s - 1) := by
  have h1 : (-s : ℝ) ≠ -1 := by linarith
  have h2 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) b := by
    rw [Set.uIcc_of_le hb]
    intro h3; linarith [h3.1]
  have h3 := integral_rpow (h := Or.inr ⟨h1, h2⟩)
  have h4 : (-s : ℝ) + 1 = 1 - s := by ring
  have h_main : (b ^ ((-s : ℝ) + 1) - (1 : ℝ) ^ ((-s : ℝ) + 1)) / ((-s : ℝ) + 1) =
      (1 - b ^ (1 - s)) / (s - 1) := by
    rw [h4]
    have h7 : (1 : ℝ) ^ (1 - s) = 1 := by simp
    have h8 : 1 - s ≠ 0 := by linarith
    have h9 : s - 1 ≠ 0 := by linarith
    rw [h7]
    field_simp [h8, h9] <;> ring
  rw [h3]
  exact h_main

/-- **Finite-scale Riesz energy inner bound**.

    For `f(y) = max(dist(x,y), δ)^{-1}`, uses the truncated layer-cake:
    - `t ≥ δ^{-1}`: no contribution since `f ≤ δ^{-1}`
    - `0 < t < 1`: `ν{f>t} ≤ ν(univ) = 1`
    - `1 ≤ t < δ^{-1}`: `{f>t} = ball(x,1/t)` with `δ < 1/t ≤ 1`,
      so use the finite-scale Frostman bound.

    Result: `∫ f dν ≤ 1 + C'/(s-1)` for `s > 1`.

    This does NOT require any Frostman estimate for `r < δ`. -/
lemma frostman_energy_finite_scale
    {X : Type*} [MeasurableSpace X] [MetricSpace X] [OpensMeasurableSpace X]
    {ν : Measure X} (hν_prob : ν Set.univ = 1)
    {s C' : ℝ} (hs : 1 < s) (hC'_pos : 0 < C')
    {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hFrost : ∀ (x : X) (r : ℝ), δ ≤ r → r ≤ 1 →
      ν (Metric.ball x r) ≤ ENNReal.ofReal (C' * r ^ s))
    (x : X) :
    ∫⁻ (y : X), ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ≤
      ENNReal.ofReal (1 + C' / (s - 1)) := by
  let f : X → ℝ := fun y => (max (dist x y) δ) ^ (-1 : ℝ)
  have hf_nonneg : ∀ y, 0 ≤ f y := by intro y; positivity
  have hf_meas : Measurable f := by fun_prop
  have hsm1_pos : 0 < s - 1 := by linarith
  have hC'_div_pos : 0 < C' / (s - 1) := by positivity
  have h1 : ∫⁻ (y : X), ENNReal.ofReal (f y) ∂ν =
      ∫⁻ (t : ℝ) in Set.Ioi (0 : ℝ), ν {y | t < f y} :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt ν
      (by filter_upwards with y; exact hf_nonneg y) hf_meas.aemeasurable
  rw [h1]
  let g : ℝ → ENNReal := fun t => ν {y | t < f y}
  have hg_eq : ∀ (t : ℝ), 0 < t → t < δ⁻¹ → g t = ν (Metric.ball x (1 / t)) := by
    intro t ht htl
    have hδ_lt : δ < 1 / t := by
      have h_t_pos : 0 < t := ht
      have hδ_pos : 0 < δ := hδ
      have h : t < 1 / δ := by
        have h9 : t < δ⁻¹ := htl
        have h10 : (δ⁻¹ : ℝ) = 1 / δ := by exact inv_eq_one_div δ
        rw [h10] at h9; exact h9
      have h2 : t * δ < 1 := by
        calc t * δ < (1 / δ) * δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne'] <;> ring
      calc δ
        = (t * δ) / t := by field_simp [h_t_pos.ne'] <;> ring
      _ < 1 / t := by gcongr
    have h4 : ∀ (y : X), t < f y ↔ dist x y < 1 / t := by
      intro y
      let M := max (dist x y) δ
      have hM_pos : 0 < M := by positivity
      have h_fy : f y = M⁻¹ := by
        simp only [f]
        have h10 : M ^ (-1 : ℝ) = M⁻¹ := by
          rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hM_pos.le] <;> simp
        exact h10
      have h_iff : t < f y ↔ M < 1 / t := by
        rw [h_fy]
        constructor
        · intro h
          have h9 : t * M < 1 := by
            calc t * M < M⁻¹ * M := by gcongr
            _ = 1 := by field_simp [hM_pos.ne'] <;> ring
          calc M = (t * M) / t := by field_simp [ht.ne'] <;> ring
            _ < 1 / t := by gcongr
        · intro h
          have h9 : t * M < 1 := by
            calc t * M < t * (1 / t) := by gcongr
            _ = 1 := by field_simp [ht.ne'] <;> ring
          calc t = (t * M) / M := by field_simp [hM_pos.ne'] <;> ring
            _ < M⁻¹ := by
              have h10 : (t * M) / M < 1 / M := by gcongr
              have h11 : (1 / M : ℝ) = M⁻¹ := by exact one_div M
              rw [h11] at h10; exact h10
      have h7 : M < 1 / t ↔ dist x y < 1 / t := by
        constructor
        · intro h; exact (le_max_left _ _).trans_lt h
        · intro h; exact max_lt h hδ_lt
      rw [h_iff, h7]
    have h_set : {y : X | t < f y} = Metric.ball x (1 / t) := by
      ext y
      have h10 : y ∈ {y : X | t < f y} ↔ t < f y := by simp
      have h11 : y ∈ Metric.ball x (1 / t) ↔ dist y x < 1 / t := by
        simp [Metric.mem_ball]
      have h12 : dist y x = dist x y := dist_comm y x
      rw [h10, h11, h12]
      exact h4 y
    simpa [g] using congr_arg ν h_set
  have hg_zero : ∀ (t : ℝ), δ⁻¹ ≤ t → g t = 0 := by
    intro t hle
    have h5 : ∀ (y : X), ¬(t < f y) := by
      intro y
      have h6 : f y ≤ δ⁻¹ := by
        simp only [f]
        let M := max (dist x y) δ
        have hM_pos : 0 < M := by positivity
        have h_eq : M ^ (-1 : ℝ) = M⁻¹ := by
          rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hM_pos.le] <;> simp
        rw [h_eq]
        have h7 : δ ≤ M := le_max_right _ _
        have h8 : M⁻¹ ≤ δ⁻¹ := by gcongr <;> positivity
        exact h8
      have h7 : f y ≤ t := le_trans h6 hle
      exact not_lt.mpr h7
    have h9 : {y : X | t < f y} = ∅ := by
      ext y
      simpa using h5 y
    simpa [g] using congr_arg ν h9
  have h_disj : Disjoint (Set.Ioo (0 : ℝ) δ⁻¹) (Set.Ici δ⁻¹) := by
    simp [Set.disjoint_left] <;> linarith
  have h_union : Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) δ⁻¹ ∪ Set.Ici δ⁻¹ := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro h
      by_cases h2 : t < δ⁻¹
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact h.1
      · have hpos : 0 < δ⁻¹ := by positivity
        linarith
  have h_meas1 : MeasurableSet (Set.Ioo (0 : ℝ) δ⁻¹) := measurableSet_Ioo
  have h_meas2 : MeasurableSet (Set.Ici δ⁻¹) := measurableSet_Ici
  have h_int2 : ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, g t = 0 := by
    have h_le : ∀ t ∈ Set.Ici δ⁻¹, g t ≤ (0 : ENNReal) := by
      intro t ht
      have h' : g t = 0 := hg_zero t ht
      rw [h'] <;> simp
    have h' : ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, g t ≤ ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, (0 : ENNReal) :=
      MeasureTheory.setLIntegral_mono' h_meas2 h_le
    have h0 : ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, (0 : ENNReal) = 0 := by simp
    rw [h0] at h'
    exact le_zero_iff.mp h'
  have h_reduce : ∫⁻ (t : ℝ) in Set.Ioi (0 : ℝ), g t =
      ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) δ⁻¹, g t := by
    rw [h_union]
    rw [MeasureTheory.lintegral_union h_meas2 h_disj]
    rw [h_int2, add_zero]
  rw [h_reduce]
  by_cases hδge : δ ≥ 1
  · have hδinv_le_one : δ⁻¹ ≤ 1 := by
      have h : δ⁻¹ ≤ 1⁻¹ := by gcongr <;> linarith
      simpa using h
    have h_ball_le_one : ∀ t ∈ Set.Ioo (0 : ℝ) δ⁻¹, g t ≤ 1 := by
      intro t ht
      have h_t_pos : 0 < t := ht.1
      have h_t_lt : t < δ⁻¹ := ht.2
      rw [hg_eq t h_t_pos h_t_lt]
      have h : ν (Metric.ball x (1 / t)) ≤ ν Set.univ := measure_mono (subset_univ _)
      rw [hν_prob] at h
      exact h
    calc ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) δ⁻¹, g t
      ≤ ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) δ⁻¹, (1 : ENNReal) := MeasureTheory.setLIntegral_mono' h_meas1 h_ball_le_one
    _ = ENNReal.ofReal δ⁻¹ := by
      rw [MeasureTheory.setLIntegral_one, Real.volume_Ioo] <;> simp [hδ.ne'] <;> norm_cast <;> linarith
    _ ≤ ENNReal.ofReal (1 + C' / (s - 1)) := by
      have h9 : δ⁻¹ ≤ 1 + C' / (s - 1) := by
        have h10 : δ⁻¹ ≤ 1 := hδinv_le_one
        have h11 : 0 < C' / (s - 1) := hC'_div_pos
        linarith
      exact ENNReal.ofReal_le_ofReal h9
  · have hδ_lt_one : δ < 1 := by linarith
    have hδinv_gt_one : 1 < δ⁻¹ := by
      have h2 : 0 < δ := hδ
      have h3 : δ < 1 := hδ_lt_one
      have h4 : (1 : ℝ) / δ > 1 := by
        calc (1 : ℝ) / δ > 1 / 1 := by gcongr
        _ = 1 := by norm_num
      have h5 : (1 : ℝ) / δ = δ⁻¹ := by exact one_div δ
      rw [h5] at h4
      exact h4
    have h_disj2 : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ico (1 : ℝ) δ⁻¹) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h1 : x < 1 := hx1.2
      have h2 : 1 ≤ x := hx2.1
      linarith
    have h_union2 : Set.Ioo (0 : ℝ) δ⁻¹ = Set.Ioo (0 : ℝ) 1 ∪ Set.Ico (1 : ℝ) δ⁻¹ := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ico]
      constructor
      · intro h
        have h_pos : 0 < t := h.1
        have h_lt : t < δ⁻¹ := h.2
        by_cases h2 : t < 1
        · exact Or.inl ⟨h_pos, h2⟩
        · have h3 : 1 ≤ t := by
            by_contra h4
            exact h2 (by linarith)
          exact Or.inr ⟨h3, h_lt⟩
      · rintro (h | h)
        · exact ⟨h.1, by linarith⟩
        · have h_pos2 : 0 < t := by linarith
          exact ⟨h_pos2, h.2⟩
    have h_meas3 : MeasurableSet (Set.Ioo (0 : ℝ) 1) := measurableSet_Ioo
    have h_meas4 : MeasurableSet (Set.Ico (1 : ℝ) δ⁻¹) := measurableSet_Ico
    rw [h_union2]
    rw [MeasureTheory.lintegral_union h_meas4 h_disj2]
    have h_first : ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, g t ≤ 1 := by
      have h_ball_le_one : ∀ t ∈ Set.Ioo (0 : ℝ) 1, g t ≤ 1 := by
        intro t ht
        have h_t_pos : 0 < t := ht.1
        have h_t_lt : t < 1 := ht.2
        have h_t_lt2 : t < δ⁻¹ := by linarith
        rw [hg_eq t h_t_pos h_t_lt2]
        have h : ν (Metric.ball x (1 / t)) ≤ ν Set.univ := measure_mono (subset_univ _)
        rw [hν_prob] at h; exact h
      calc ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, g t
        ≤ ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, (1 : ENNReal) := MeasureTheory.setLIntegral_mono' h_meas3 h_ball_le_one
      _ = 1 := by
        rw [MeasureTheory.setLIntegral_one, Real.volume_Ioo] <;> simp
    have h_second : ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, g t ≤
        ENNReal.ofReal (C' / (s - 1)) := by
      have h_ball_le : ∀ t ∈ Set.Ico (1 : ℝ) δ⁻¹, g t ≤ ENNReal.ofReal (C' * t ^ (-s)) := by
        intro t ht
        have h_t_pos : 0 < t := zero_lt_one.trans_le ht.1
        have h_t_ge_one : 1 ≤ t := ht.1
        have h_t_lt : t < δ⁻¹ := ht.2
        rw [hg_eq t h_t_pos h_t_lt]
        have h1 : 0 < 1 / t := by positivity
        have h2 : δ ≤ 1 / t := by
          have hδ_lt2 : δ < 1 / t := by
            have h_t_pos2 : 0 < t := h_t_pos
            have hδ_pos2 : 0 < δ := hδ
            have h : t < 1 / δ := by
              have h9 : t < δ⁻¹ := h_t_lt
              have h10 : (δ⁻¹ : ℝ) = 1 / δ := by exact inv_eq_one_div δ
              rw [h10] at h9; exact h9
            have h2 : t * δ < 1 := by
              calc t * δ < (1 / δ) * δ := by gcongr
              _ = 1 := by field_simp [hδ_pos2.ne'] <;> ring
            calc δ
              = (t * δ) / t := by field_simp [h_t_pos2.ne'] <;> ring
            _ < 1 / t := by gcongr
          exact hδ_lt2.le
        have h3 : 1 / t ≤ 1 := by
          apply (div_le_one (by linarith)).mpr; linarith
        have h4 : ν (Metric.ball x (1 / t)) ≤ ENNReal.ofReal (C' * (1 / t) ^ s) :=
          hFrost x (1 / t) h2 h3
        have h5 : C' * (1 / t) ^ s = C' * t ^ (-s) := by
          have h6 : (1 / t) ^ s = (t ^ s)⁻¹ := by
            have h7 : (1 / t) = t⁻¹ := by field_simp [h_t_pos.ne']
            rw [h7]
            exact Real.inv_rpow h_t_pos.le s
          have h7 : t ^ (-s) = (t ^ s)⁻¹ := Real.rpow_neg h_t_pos.le s
          rw [h6, h7]
        rw [h5] at h4; exact h4
      calc ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, g t
        ≤ ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, ENNReal.ofReal (C' * t ^ (-s)) :=
          MeasureTheory.setLIntegral_mono' h_meas4 h_ball_le
      _ = ENNReal.ofReal (∫ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, C' * t ^ (-s)) := by
        have h_cont : ContinuousOn (fun t : ℝ => C' * t ^ (-s)) (Set.Icc (1 : ℝ) δ⁻¹) := by
          apply ContinuousOn.const_mul
          have h : ContinuousOn (fun t : ℝ => t ^ (-s)) (Set.Icc (1 : ℝ) δ⁻¹) := by
            intro t ht
            have h_t_pos : 0 < t := zero_lt_one.trans_le ht.1
            exact (Real.continuousAt_rpow_const t (-s) (Or.inl h_t_pos.ne')).continuousWithinAt
          exact h
        have h_le_one' : 1 ≤ δ⁻¹ := by linarith
        have h_iOn_Icc : IntegrableOn (fun t : ℝ => C' * t ^ (-s)) (Set.Icc (1 : ℝ) δ⁻¹) volume :=
          h_cont.integrableOn_Icc
        have h_iOn : IntegrableOn (fun t : ℝ => C' * t ^ (-s)) (Set.Ico (1 : ℝ) δ⁻¹) volume :=
          h_iOn_Icc.mono_set (show Set.Ico (1 : ℝ) δ⁻¹ ⊆ Set.Icc (1 : ℝ) δ⁻¹ from by
            intro x hx; exact ⟨hx.1, le_of_lt hx.2⟩)
        have h_nn : 0 ≤ᵐ[volume.restrict (Set.Ico (1 : ℝ) δ⁻¹)] (fun t : ℝ => C' * t ^ (-s)) := by
          have h_mem : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ico (1 : ℝ) δ⁻¹), t ∈ Set.Ico (1 : ℝ) δ⁻¹ :=
            ae_restrict_mem h_meas4
          filter_upwards [h_mem] with t ht
          have h_t_pos : 0 < t := zero_lt_one.trans_le ht.1
          exact mul_nonneg hC'_pos.le (Real.rpow_nonneg h_t_pos.le _)
        have h_main_eq : ENNReal.ofReal (∫ (t : ℝ), C' * t ^ (-s) ∂(volume.restrict (Set.Ico (1 : ℝ) δ⁻¹))) =
            ∫⁻ (t : ℝ), ENNReal.ofReal (C' * t ^ (-s)) ∂(volume.restrict (Set.Ico (1 : ℝ) δ⁻¹)) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_iOn h_nn
        simpa using h_main_eq.symm
      _ ≤ ENNReal.ofReal (C' / (s - 1)) := by
        have h_le_one : 1 ≤ δ⁻¹ := by linarith
        have h_eq1 : ∫ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, C' * t ^ (-s) =
            ∫ (t : ℝ) in Set.Ioc (1 : ℝ) δ⁻¹, C' * t ^ (-s) := by exact integral_Ico_eq_integral_Ioc
        have h_int_Ioc : ∫ (t : ℝ) in Set.Ioc (1 : ℝ) δ⁻¹, C' * t ^ (-s) =
            ∫ t in (1 : ℝ)..δ⁻¹, C' * t ^ (-s) := by
          exact (intervalIntegral.integral_of_le h_le_one).symm
        have h_bound : ∫ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, C' * t ^ (-s) ≤ C' / (s - 1) := by
          rw [h_eq1, h_int_Ioc]
          have h_mul : ∫ t in (1 : ℝ)..δ⁻¹, C' * t ^ (-s) =
              C' * ∫ t in (1 : ℝ)..δ⁻¹, t ^ (-s) := by
            rw [intervalIntegral.integral_const_mul]
          rw [h_mul, integral_t_neg_s_finite hs h_le_one]
          have h10 : C' * ((1 - (δ⁻¹) ^ (1 - s)) / (s - 1)) ≤ C' / (s - 1) := by
            have h11 : C' * ((1 - (δ⁻¹) ^ (1 - s)) / (s - 1)) =
                (C' * (1 - (δ⁻¹) ^ (1 - s))) / (s - 1) := by
              rw [mul_div_assoc]
            rw [h11]
            have h12 : 0 ≤ (δ⁻¹) ^ (1 - s) := Real.rpow_nonneg (by positivity) _
            have h13 : 1 - (δ⁻¹) ^ (1 - s) ≤ 1 := by linarith
            have h14 : C' * (1 - (δ⁻¹) ^ (1 - s)) ≤ C' := mul_le_of_le_one_right hC'_pos.le h13
            exact div_le_div_of_nonneg_right h14 (by linarith)
          exact h10
        exact ofReal_le_ofReal h_bound
    calc (∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, g t) + ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, g t
      ≤ (1 : ENNReal) + ENNReal.ofReal (C' / (s - 1)) := by gcongr
    _ = ENNReal.ofReal (1 + C' / (s - 1)) := by
      have h_one : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h_one]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      <;> norm_cast

end WeakTwoEndsSumProduct

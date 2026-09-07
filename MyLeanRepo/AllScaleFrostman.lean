module

/-
# All-Scale Frostman Measures

Definition and basic properties of all-scale Frostman measures, as used in the
Expansion Theorem (Theorem 1) and Strong Ring Theorem.

Unlike `IsDirectionFrostman δ κ C μ`, which only controls radii `δ ≤ r ≤ 1`,
the all-scale version controls **every** radius `r > 0`.

## Main results

- `IsAllScaleFrostman.diam_lower`: diameter of support ≥ C^{-1/κ}
- `IsAllScaleFrostman.product_ball_bound`: product measure μ^×n Frostman bound
- `IsAllScaleFrostman.restrict_renormalize`: restriction preserves Frostman

## References

- Corso-Shmerkin-Wang, arXiv:2511.21656, Section 3
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductMeasureEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Measure Set Metric Classical
open scoped Topology

namespace WeakTwoEndsSumProduct

/-- An all-scale `(κ, C)`-Frostman probability measure on ℝ.

    `μ(Icc(x-r, x+r)) ≤ C · r^κ` for all `x ∈ ℝ` and `r > 0`. -/
def IsAllScaleFrostman (κ C : ℝ) (μ : Measure ℝ) : Prop :=
  μ Set.univ = 1 ∧
  0 < κ ∧
  0 < C ∧
  ∀ (x r : ℝ), 0 < r →
    μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ κ)

namespace IsAllScaleFrostman

/-- Monotonicity in the constant: a `(κ, C)`-Frostman measure is also
    `(κ, C')`-Frostman for any `C' ≥ C`. -/
lemma mono {κ C C' : ℝ} {μ : Measure ℝ}
    (h : IsAllScaleFrostman κ C μ) (hC : C ≤ C') :
    IsAllScaleFrostman κ C' μ := by
  have hκ_pos : 0 < κ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hC'_pos : 0 < C' := by linarith
  have h_frost := h.2.2.2
  exact ⟨h.1, hκ_pos, hC'_pos, fun x r hr => by
    have h1 : C * r ^ κ ≤ C' * r ^ κ := by
      have h2 : 0 ≤ r ^ κ := by positivity
      exact mul_le_mul_of_nonneg_right hC h2
    exact (h_frost x r hr).trans (ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h1)⟩

/-- If the support is contained in Icc(x-r, x+r), then r ≥ C^{-1/κ}. -/
lemma diam_lower {κ C : ℝ} {μ : Measure ℝ}
    (h : IsAllScaleFrostman κ C μ)
    {x r : ℝ} (hr : 0 < r)
    (hsup : μ.support ⊆ Set.Icc (x - r) (x + r)) :
    C ^ (-1 / κ) ≤ r := by
  have hκ_pos : 0 < κ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have h_frost := h.2.2.2
  -- The interval has full measure because it contains the support
  have h1 : μ (Set.Icc (x - r) (x + r)) = 1 := by
    have h_compl : μ (μ.supportᶜ) = 0 := Measure.measure_compl_support
    have h2 : (Set.Icc (x - r) (x + r))ᶜ ⊆ μ.supportᶜ := by
      intro z hz
      simp only [Set.mem_compl_iff] at hz ⊢
      exact fun h => hz (hsup h)
    have h3 : μ (Set.Icc (x - r) (x + r))ᶜ = 0 :=
      nonpos_iff_eq_zero.mp (le_trans (measure_mono h2) h_compl.le)
    have hS_meas : MeasurableSet (Set.Icc (x - r) (x + r)) := measurableSet_Icc
    have hS_compl_meas : MeasurableSet (Set.Icc (x - r) (x + r))ᶜ := hS_meas.compl
    have h_disj : Disjoint (Set.Icc (x - r) (x + r)) (Set.Icc (x - r) (x + r))ᶜ := disjoint_compl_right
    have h_union : (Set.Icc (x - r) (x + r)) ∪ (Set.Icc (x - r) (x + r))ᶜ = Set.univ := by simp
    have h41 : μ (Set.Icc (x - r) (x + r)) + μ (Set.Icc (x - r) (x + r))ᶜ = μ Set.univ := by
      rw [← measure_union h_disj hS_compl_meas, h_union, h.1]
    rw [h3] at h41
    have h42 : μ (Set.Icc (x - r) (x + r)) = μ Set.univ := by simpa using h41
    rw [h.1] at h42
    exact h42
  have h4 : μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ κ) :=
    h_frost x r hr
  rw [h1] at h4
  have h5 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C * r ^ κ) := by
    simpa using h4
  have h6 : 1 ≤ C * r ^ κ := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h5
  have h7 : 0 < r ^ κ := by positivity
  have h8 : 1 / C ≤ r ^ κ := by
    have h9 : 0 < C := hC_pos
    calc 1 / C
      = (1 : ℝ) / C := by ring
    _ ≤ (C * r ^ κ) / C := by gcongr
    _ = r ^ κ := by field_simp [h9.ne'] <;> ring
  have h10 : (1 / C) ^ (1 / κ) ≤ (r ^ κ) ^ (1 / κ) :=
    Real.rpow_le_rpow (by positivity) h8 (by positivity)
  have h11 : (1 / C) ^ (1 / κ) = C ^ (-1 / κ) := by
    have h11a : 1 / C = C ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      <;> ring
    rw [h11a]
    have h11b : (C ^ (-1 : ℝ)) ^ (1 / κ) = C ^ ((-1 : ℝ) * (1 / κ)) := by
      rw [← Real.rpow_mul (by positivity)]
    rw [h11b]
    have h11c : (-1 : ℝ) * (1 / κ) = -1 / κ := by ring
    rw [h11c]
  have h12 : (r ^ κ) ^ (1 / κ) = r := by
    have h12a : κ * (1 / κ) = 1 := by field_simp [hκ_pos.ne'] <;> ring
    rw [← Real.rpow_mul (by positivity), h12a, Real.rpow_one]
  rw [h11, h12] at h10
  exact h10

/-- Product measure μ^×n on EuclideanSpace ℝ (Fin n) satisfies an
    `(nκ, C^n)` Frostman ball bound. -/
lemma product_ball_bound {κ C : ℝ} {μ : Measure ℝ}
    (h : IsAllScaleFrostman κ C μ)
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 < r) :
    ProductMeasureEnergy.productMeasure μ (Metric.ball x r) ≤
      ENNReal.ofReal (C ^ n * r ^ ((n : ℝ) * κ)) := by
  have hκ_pos : 0 < κ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have h_frost := h.2.2.2
  have h_prob : μ Set.univ = 1 := h.1
  let I : Fin n → Set ℝ := fun i => Set.Icc (x i - r) (x i + r)
  let box : Set (Fin n → ℝ) := Set.pi Set.univ I
  have hI_meas : ∀ i, MeasurableSet (I i) := fun _ => measurableSet_Icc
  have h_ball_meas : MeasurableSet (Metric.ball x r) :=
    Metric.isOpen_ball.measurableSet
  letI : IsFiniteMeasure μ := ⟨by rw [h_prob] <;> norm_num⟩
  let e : EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  have h1 : e '' (Metric.ball x r) ⊆ box := by
    intro f hf
    rcases hf with ⟨y, hy, rfl⟩
    have h_dist : dist y x < r := by simpa [Metric.mem_ball] using hy
    intro i _
    have h3 : |y i - x i| ≤ dist y x := ProductMeasureEnergy.coord_le_dist i
    have h4 : |y i - x i| < r := by linarith
    have h5 : y i ∈ Set.Icc (x i - r) (x i + r) := by
      rw [Set.mem_Icc]
      rw [abs_lt] at h4
      exact ⟨by linarith, by linarith⟩
    exact h5
  have h_preimage : e.symm ⁻¹' (Metric.ball x r) = e '' (Metric.ball x r) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hf
      exact ⟨e.symm f, hf, e.apply_symm_apply f⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  have h_main : ProductMeasureEnergy.productMeasure μ (Metric.ball x r) =
      MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (e '' (Metric.ball x r)) := by
    have h_eq1 : ProductMeasureEnergy.productMeasure μ (Metric.ball x r) =
        Measure.map e.symm (MeasureTheory.Measure.pi (fun (_ : Fin n) => μ)) (Metric.ball x r) := by
      rfl
    rw [h_eq1]
    have h_apply : Measure.map e.symm (MeasureTheory.Measure.pi (fun (_ : Fin n) => μ)) (Metric.ball x r) =
        MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (e.symm ⁻¹' (Metric.ball x r)) := by
      rw [Measure.map_apply (by exact measurable_comap_iff.mpr fun ⦃t⦄ a => a) h_ball_meas]
    rw [h_apply]
    exact congr_arg (fun S : Set (Fin n → ℝ) => MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) S) h_preimage
  have h3 : MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) box =
      ∏ i : Fin n, μ (I i) := by exact pi_pi_aux (fun x => μ) I hI_meas
  have h4 : ∀ i : Fin n, μ (I i) ≤ ENNReal.ofReal (C * r ^ κ) := by
    intro i
    exact h_frost (x i) r hr
  have h5 : ∏ i : Fin n, μ (I i) ≤
      ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) := by
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _; exact h4 i
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have h_rpow_nonneg : 0 ≤ r ^ κ := by positivity
  have h6 : ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) =
      ENNReal.ofReal (C ^ n * r ^ ((n : ℝ) * κ)) := by
    have h : ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) =
        ∏ i : Fin n, (ENNReal.ofReal C * ENNReal.ofReal (r ^ κ)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul hC_nonneg]
    rw [h]
    have h_prod : ∏ i : Fin n, (ENNReal.ofReal C * ENNReal.ofReal (r ^ κ)) =
        (ENNReal.ofReal C * ENNReal.ofReal (r ^ κ)) ^ n := by
      simp [Finset.prod_const]
      <;> rfl
    rw [h_prod]
    have h_mul_pow : (ENNReal.ofReal C * ENNReal.ofReal (r ^ κ)) ^ n =
        (ENNReal.ofReal C) ^ n * (ENNReal.ofReal (r ^ κ)) ^ n := by
      rw [mul_pow]
    rw [h_mul_pow]
    have hC_pow : (ENNReal.ofReal C) ^ n = ENNReal.ofReal (C ^ n) := by
      rw [← ENNReal.ofReal_pow hC_nonneg] <;> rfl
    have hr_pow : (ENNReal.ofReal (r ^ κ)) ^ n = ENNReal.ofReal ((r ^ κ) ^ n) := by
      rw [← ENNReal.ofReal_pow h_rpow_nonneg] <;> rfl
    rw [hC_pow, hr_pow]
    have h_rpow_mul : (r ^ κ) ^ n = r ^ ((n : ℝ) * κ) := by
      have h1 : (r ^ κ) ^ n = (r ^ κ) ^ (n : ℝ) := by norm_cast
      rw [h1]
      have h2 : (r ^ κ) ^ (n : ℝ) = r ^ (κ * (n : ℝ)) := by
        rw [Real.rpow_mul (by linarith)]
      rw [h2]
      have h3 : κ * (n : ℝ) = (n : ℝ) * κ := by ring
      rw [h3]
    rw [h_rpow_mul]
    rw [← ENNReal.ofReal_mul (by positivity)]
  calc ProductMeasureEnergy.productMeasure μ (Metric.ball x r)
    = MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (e '' (Metric.ball x r)) := h_main
  _ ≤ MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) box := measure_mono h1
  _ = ∏ i : Fin n, μ (I i) := h3
  _ ≤ ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) := h5
  _ = ENNReal.ofReal (C ^ n * r ^ ((n : ℝ) * κ)) := h6

/-- Restrict to a positive-measure set and renormalize.
    The result is `(κ, C / μ(S))`-Frostman. -/
lemma restrict_renormalize {κ C : ℝ} {μ : Measure ℝ}
    (h : IsAllScaleFrostman κ C μ)
    {S : Set ℝ} (hS_meas : MeasurableSet S)
    (hS_pos : 0 < μ S) (hS_lt_top : μ S < ⊤) :
    ∃ (ν : Measure ℝ), IsAllScaleFrostman κ (C / (μ S).toReal) ν ∧
      ν.support ⊆ closure S ∩ μ.support := by
  have hκ_pos : 0 < κ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have h_frost := h.2.2.2
  have h_prob : μ Set.univ = 1 := h.1
  have hS_real_pos : 0 < (μ S).toReal := by
    by_contra h
    have h_nonneg : 0 ≤ (μ S).toReal := by positivity
    have h' : (μ S).toReal = 0 := by linarith
    have h'' : μ S = 0 ∨ μ S = ⊤ := by
      rw [ENNReal.toReal_eq_zero_iff] at h'
      exact h'
    rcases h'' with (h0 | htop)
    · exact False.elim (hS_pos.ne' h0)
    · exact False.elim (hS_lt_top.ne htop)
  let c_enn : ENNReal := ENNReal.ofReal ((μ S).toReal⁻¹)
  have hc_ne_zero : (μ S).toReal ≠ 0 := hS_real_pos.ne'
  have h_mul : c_enn * μ S = 1 := by
    have h_eq1 : μ S = ENNReal.ofReal (μ S).toReal := by
      rw [ENNReal.ofReal_toReal hS_lt_top.ne]
    rw [h_eq1]
    have h_mul2 : c_enn * ENNReal.ofReal (μ S).toReal =
        ENNReal.ofReal (((μ S).toReal⁻¹) * (μ S).toReal) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_mul2]
    have h3 : (μ S).toReal⁻¹ * (μ S).toReal = 1 := by
      field_simp [hc_ne_zero] <;> ring
    rw [h3] <;> simp
  let ν : Measure ℝ := c_enn • μ.restrict S
  have hν_prob : ν Set.univ = 1 := by
    simp [ν, Measure.restrict_apply hS_meas, h_mul] <;> rfl
  have hν_frost : ∀ (x r : ℝ), 0 < r →
      ν (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal ((C / (μ S).toReal) * r ^ κ) := by
    intro x r hr
    have h1 : ν (Set.Icc (x - r) (x + r)) =
        c_enn * μ (Set.Icc (x - r) (x + r) ∩ S) := by
      simp [ν, Measure.restrict_apply hS_meas] <;> rfl
    rw [h1]
    have h21 : (Set.Icc (x - r) (x + r) ∩ S) ⊆ (Set.Icc (x - r) (x + r)) := Set.inter_subset_left
    have h2 : μ (Set.Icc (x - r) (x + r) ∩ S) ≤ μ (Set.Icc (x - r) (x + r)) :=
      measure_mono h21
    have h3 : μ (Set.Icc (x - r) (x + r) ∩ S) ≤ ENNReal.ofReal (C * r ^ κ) :=
      le_trans h2 (h_frost x r hr)
    have h4 : c_enn * μ (Set.Icc (x - r) (x + r) ∩ S) ≤
        c_enn * ENNReal.ofReal (C * r ^ κ) := by gcongr
    calc c_enn * μ (Set.Icc (x - r) (x + r) ∩ S)
      ≤ c_enn * ENNReal.ofReal (C * r ^ κ) := h4
    _ = ENNReal.ofReal (((μ S).toReal⁻¹) * (C * r ^ κ)) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    _ = ENNReal.ofReal ((C / (μ S).toReal) * r ^ κ) := by
      have h_eq : ((μ S).toReal⁻¹) * (C * r ^ κ) = (C / (μ S).toReal) * r ^ κ := by ring
      rw [h_eq]
  have h_main : IsAllScaleFrostman κ (C / (μ S).toReal) ν :=
    ⟨hν_prob, hκ_pos, by positivity, hν_frost⟩
  have hν_support_eq : ν.support = (μ.restrict S).support := by
    ext z
    simp only [mem_support_iff_forall]
    constructor
    · intro h U hU
      have h2 : 0 < ν U := h U hU
      have h3 : ν U = c_enn * (μ.restrict S) U := by exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp rfl
      rw [h3] at h2
      by_contra h5
      have h6 : (μ.restrict S) U = 0 := by simpa [not_lt] using h5
      rw [h6] at h2; simp at h2
    · intro h U hU
      have h2 : 0 < (μ.restrict S) U := h U hU
      have h3 : ν U = c_enn * (μ.restrict S) U := by exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp rfl
      rw [h3]
      have hc : c_enn ≠ 0 := by simp [c_enn] <;> positivity
      exact ENNReal.mul_pos hc h2.ne'
  have h_support : ν.support ⊆ closure S ∩ μ.support := by
    rw [hν_support_eq]
    exact support_restrict_subset (μ := μ) (s := S)
  exact ⟨ν, h_main, h_support⟩

end IsAllScaleFrostman

end WeakTwoEndsSumProduct

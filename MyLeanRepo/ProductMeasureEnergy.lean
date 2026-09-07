module

/-
# Product Measure Energy

If μ is a Frostman measure of exponent κ on ℝ, then the product measure μ^n
on EuclideanSpace ℝ (Fin n) has Frostman exponent nκ:
  μ^n(B(x, r)) ≤ C^n · r^{nκ}

## Proof route

1. A Euclidean ball in ℝ^n is contained in a product of intervals ∏ [x_i - r, x_i + r].
2. Product measure of a box is the product of measures.
3. Each interval has measure ≤ C · r^κ by the Frostman property.
4. Therefore μ^n(ball) ≤ C^n · r^{nκ}.

## Whiteprint node
Helper for product measure energy in Bourgain projection theorem.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical BigOperators

namespace ProductMeasureEnergy

/-! ## Product measure construction -/

/-- The n-fold product measure on EuclideanSpace ℝ (Fin n). -/
def productMeasure {n : ℕ} (μ : Measure ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (EuclideanSpace.equiv (Fin n) ℝ).symm
    (MeasureTheory.Measure.pi (fun (_ : Fin n) => μ))

/-! ## Coordinate bound -/

lemma coord_le_dist {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)} (i : Fin n) :
    |y i - x i| ≤ dist y x := by
  have h1 : ‖y - x‖ = Real.sqrt (∑ j : Fin n, |(y - x) j| ^ 2) :=
    PiLp.norm_eq_of_L2 (y - x)
  have h2 : |(y - x) i| ^ 2 ≤ ∑ j : Fin n, |(y - x) j| ^ 2 := by
    apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
  have h3 : |(y - x) i| ≤ Real.sqrt (∑ j : Fin n, |(y - x) j| ^ 2) := by
    have h4 : 0 ≤ |(y - x) i| := by positivity
    have h5 : 0 ≤ ∑ j : Fin n, |(y - x) j| ^ 2 := by positivity
    rw [Real.le_sqrt (by positivity)] <;> nlinarith
  have h4 : |(y - x) i| ≤ ‖y - x‖ := by
    rw [h1] at * <;> exact h3
  simpa [dist_eq_norm] using h4

/-! ## Product Frostman ball bound -/

theorem product_frostman_ball_bound {n : ℕ} {δ κ C : ℝ}
    {μ : Measure ℝ} (hμ : IsDirectionFrostman δ κ C μ)
    (hC_pos : 0 < C) (hκ_nonneg : 0 ≤ κ)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hδ : 0 < δ) (hrδ : δ ≤ r) (hr1 : r ≤ 1) :
    productMeasure μ (Metric.ball x r) ≤
      ENNReal.ofReal (C ^ n * r ^ ((n : ℝ) * κ)) := by
  let I : Fin n → Set ℝ := fun i => Set.Icc (x i - r) (x i + r)
  let box : Set (Fin n → ℝ) := Set.pi Set.univ I
  have hI_meas : ∀ i, MeasurableSet (I i) := fun _ => measurableSet_Icc
  have h_ball_meas : MeasurableSet (Metric.ball x r) :=
    Metric.isOpen_ball.measurableSet
  have hμ_fin : μ Set.univ < ⊤ := by rw [hμ.1] <;> norm_num
  letI : IsFiniteMeasure μ := ⟨by rw [hμ.1] <;> norm_num⟩
  let e : EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  have h1 : e '' (Metric.ball x r) ⊆ box := by
    intro f hf
    rcases hf with ⟨y, hy, rfl⟩
    have h_dist : dist y x < r := by simpa [Metric.mem_ball] using hy
    intro i _
    have h3 : |y i - x i| ≤ dist y x := coord_le_dist i
    have h4 : |y i - x i| < r := by linarith
    have h5 : y i ∈ Set.Icc (x i - r) (x i + r) := by
      rw [Set.mem_Icc]
      rw [abs_lt] at h4
      exact ⟨by linarith, by linarith⟩
    exact h5
  have h_preimage : (EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹' (Metric.ball x r) =
      e '' (Metric.ball x r) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hf
      exact ⟨e.symm f, hf, e.apply_symm_apply f⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  have h_main : productMeasure μ (Metric.ball x r) =
      MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (e '' (Metric.ball x r)) := by
    simp only [productMeasure]
    rw [Measure.map_apply (by exact measurable_comap_iff.mpr fun ⦃t⦄ a => a) h_ball_meas]
    rw [h_preimage]
  have h3 : MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) box =
      ∏ i : Fin n, μ (I i) := by
    have h : MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (Set.pi Set.univ I) =
        ∏ i : Fin n, μ (I i) := by
      exact Measure.pi_pi_aux (fun x => μ) I hI_meas
    exact h
  have h4 : ∀ i : Fin n, μ (I i) ≤ ENNReal.ofReal (C * r ^ κ) := by
    intro i
    exact hμ.2.2 (x i) r hrδ hr1
  have h5 : ∏ i : Fin n, μ (I i) ≤
      ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) := by
    apply Finset.prod_le_prod
    · intro i _
      positivity
    · intro i _
      exact h4 i
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hr_pos : 0 < r := by linarith
  have h_rpow_nonneg : 0 ≤ r ^ κ := by positivity
  have h61 : ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) =
      (ENNReal.ofReal C) ^ n * (ENNReal.ofReal (r ^ κ)) ^ n := by
    have h : ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) =
        ∏ i : Fin n, (ENNReal.ofReal C * ENNReal.ofReal (r ^ κ)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul hC_nonneg]
    rw [h]
    simp [Finset.prod_const] <;> ring
  have hC1 : (ENNReal.ofReal C) ^ n = ENNReal.ofReal (C ^ n) := by
    rw [← ENNReal.ofReal_pow hC_nonneg] <;> rfl
  have hr1 : (ENNReal.ofReal (r ^ κ)) ^ n = ENNReal.ofReal ((r ^ κ) ^ n) := by
    rw [← ENNReal.ofReal_pow h_rpow_nonneg] <;> rfl
  have hpow : (r ^ κ) ^ n = r ^ ((n : ℝ) * κ) := by
    have h1 : (r ^ κ) ^ n = (r ^ κ) ^ (n : ℝ) :=
      (Real.rpow_natCast (r ^ κ) n).symm
    rw [h1]
    have h2 : (r ^ κ) ^ (n : ℝ) = r ^ (κ * (n : ℝ)) := by
      rw [Real.rpow_mul (by linarith)]
    rw [h2]
    have h3 : κ * (n : ℝ) = (n : ℝ) * κ := by ring
    exact congr_arg (fun x : ℝ => r ^ x) h3
  have h62 : (ENNReal.ofReal C) ^ n * (ENNReal.ofReal (r ^ κ)) ^ n =
      ENNReal.ofReal (C ^ n * r ^ ((n : ℝ) * κ)) := by
    rw [hC1, hr1, hpow]
    rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
  have h6 : ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) =
      ENNReal.ofReal (C ^ n * r ^ ((n : ℝ) * κ)) := by
    rw [h61, h62]
  calc productMeasure μ (Metric.ball x r)
    = MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (e '' (Metric.ball x r)) := h_main
  _ ≤ MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) box := measure_mono h1
  _ = ∏ i : Fin n, μ (I i) := h3
  _ ≤ ∏ i : Fin n, ENNReal.ofReal (C * r ^ κ) := h5
  _ = ENNReal.ofReal (C ^ n * r ^ ((n : ℝ) * κ)) := h6

/-- The product measure is a probability measure. -/
lemma product_measure_univ {n : ℕ} {μ : Measure ℝ} (hμ : μ Set.univ = 1) :
    productMeasure μ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) = 1 := by
  letI : IsFiniteMeasure μ := ⟨by rw [hμ] <;> norm_num⟩
  let e : EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  have h_preimage : (EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹' (Set.univ : Set (EuclideanSpace ℝ (Fin n))) =
      (Set.univ : Set (Fin n → ℝ)) := by
    ext f; simp
  have h_main : productMeasure μ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) =
      MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (Set.univ : Set (Fin n → ℝ)) := by
    simp only [productMeasure]
    rw [Measure.map_apply (by exact measurable_comap_iff.mpr fun ⦃t⦄ a => a) MeasurableSet.univ, h_preimage]
  rw [h_main]
  have h_eq : (Set.univ : Set (Fin n → ℝ)) = Set.pi Set.univ (fun (_ : Fin n) => Set.univ) := by
    ext x; simp
  rw [h_eq]
  have h : MeasureTheory.Measure.pi (fun (_ : Fin n) => μ) (Set.pi Set.univ (fun (_ : Fin n) => Set.univ)) =
      ∏ i : Fin n, μ (Set.univ) := by exact Measure.pi_pi (fun x => μ) fun x => univ
  rw [h]
  simp [hμ, Finset.prod_const] <;> norm_cast

end ProductMeasureEnergy

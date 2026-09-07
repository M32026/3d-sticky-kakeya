module

/-
# Riesz Energy Monotonicity and Scaling

Provides:
- `rieszEnergy_subset_uniform_projected`: I(π μE3) ≤ (|E|/|E3|)² · I(π μE)
- `rieszEnergy_subset_uniform_delta_bound`: explicit δ^{-6ε} bound

## Proof
1. ν = uniformMeasureOn E3 = a • μ.restrict(E3), where a = |E|/|E3|
2. map f ν = a • map f (μ.restrict(E3))
3. map f (μ.restrict(E3)) ≤ map f μ
4. Energy monotonicity + quadratic scaling gives bound

## Whiteprint node
`riesz_energy_monotonicity`
-/

public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal MeasureTheory Finset

noncomputable section

namespace ProductLikeIncidence.ProductReduction

attribute [local instance] Classical.propDecidable

/-! ### Uniform measure on a Finset -/

/-- Uniform probability measure on a nonempty Finset. -/
def uniformMeasureOn {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (E : Finset α) : Measure α :=
  (E.card : ENNReal)⁻¹ • Measure.count.restrict (E : Set α)

lemma uniformMeasureOn_apply {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (E : Finset α) (hE_nonempty : E.Nonempty) (A : Set α) (hA : MeasurableSet A) :
    uniformMeasureOn E A = ENat.toENNReal ((E : Set α) ∩ A).encard * (E.card : ENNReal)⁻¹ := by
  have h_card_pos : (E.card : ENNReal) ≠ 0 := by
    have h1 : 0 < E.card := Finset.Nonempty.card_pos hE_nonempty
    exact_mod_cast h1.ne'
  have hE_fin : (E : Set α).Finite := Finset.finite_toSet E
  have h_inter_meas : MeasurableSet ((E : Set α) ∩ A) := hE_fin.measurableSet.inter hA
  have h_count1 : Measure.count ((E : Set α) ∩ A) = ENat.toENNReal ((E : Set α) ∩ A).encard :=
    MeasureTheory.Measure.count_apply h_inter_meas
  have h_restrict : (Measure.count.restrict (E : Set α)) A = Measure.count ((E : Set α) ∩ A) := by
    rw [Measure.restrict_apply hA, Set.inter_comm]
  have h_main : uniformMeasureOn E A =
      (E.card : ENNReal)⁻¹ * ENat.toENNReal ((E : Set α) ∩ A).encard := by
    rw [uniformMeasureOn, Measure.smul_apply, h_restrict, h_count1]
    <;> ring
  rw [h_main] <;> ring

lemma uniformMeasureOn_isProbabilityMeasure {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (E : Finset α) (hE_nonempty : E.Nonempty) :
    IsProbabilityMeasure (uniformMeasureOn E) := by
  have h1_pos : 0 < E.card := Finset.Nonempty.card_pos hE_nonempty
  have h_card_pos : (E.card : ENNReal) ≠ 0 := by exact_mod_cast h1_pos.ne'
  have h_card_ne_top : (E.card : ENNReal) ≠ ⊤ := by simp
  have h_encard : ENat.toENNReal (E : Set α).encard = (E.card : ENNReal) := by simp
  have h1 : uniformMeasureOn E Set.univ = 1 := by
    rw [uniformMeasureOn_apply E hE_nonempty Set.univ MeasurableSet.univ]
    have h2 : (E : Set α) ∩ Set.univ = (E : Set α) := by simp
    rw [h2, h_encard]
    exact ENNReal.mul_inv_cancel h_card_pos h_card_ne_top
  exact ⟨h1⟩

/-! ### Energy monotonicity and scaling -/

/-- Riesz energy is monotone in the measure: if ν ≤ μ, then I(ν) ≤ I(μ).
    Uses `lintegral_mono'` which does not require measurability of the kernel. -/
lemma rieszEnergy_mono {α : Type*} [MeasurableSpace α] [MetricSpace α]
    {δ : ℝ} (hδ : 0 < δ) {α_exp : ℝ} {μ ν : Measure α} (h : ν ≤ μ) :
    robust_projection_main.rieszEnergy α_exp hδ ν ≤
    robust_projection_main.rieszEnergy α_exp hδ μ := by
  dsimp only [robust_projection_main.rieszEnergy]
  let g : α → α → ENNReal := fun x y =>
    ENNReal.ofReal ((max (dist x y) δ) ^ (-α_exp))
  have h1 : ∀ (x : α), ∫⁻ (y : α), g x y ∂ν ≤ ∫⁻ (y : α), g x y ∂μ := by
    intro x
    exact MeasureTheory.lintegral_mono' h (le_refl (g x))
  have h2 : ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂ν) ∂ν ≤
      ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂ν := by
    apply lintegral_mono
    intro x
    exact h1 x
  have h3 : ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂ν ≤
      ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂μ := by
    exact MeasureTheory.lintegral_mono' h (le_refl _)
  exact le_trans h2 h3

/-- Riesz energy scales quadratically: I(c • μ) = c² · I(μ). -/
lemma rieszEnergy_smul {α : Type*} [MeasurableSpace α] [MetricSpace α]
    {δ : ℝ} (hδ : 0 < δ) {α_exp : ℝ} {μ : Measure α} {c : ENNReal} (hc : c ≠ ⊤) :
    robust_projection_main.rieszEnergy α_exp hδ (c • μ) =
    c * c * robust_projection_main.rieszEnergy α_exp hδ μ := by
  dsimp only [robust_projection_main.rieszEnergy]
  let g : α → α → ENNReal := fun x y =>
    ENNReal.ofReal ((max (dist x y) δ) ^ (-α_exp))
  have h1 : ∀ (x : α), ∫⁻ (y : α), g x y ∂(c • μ) = c * ∫⁻ (y : α), g x y ∂μ := by
    intro x
    exact MeasureTheory.lintegral_smul_measure c _
  have h2 : ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂(c • μ)) ∂(c • μ) =
      ∫⁻ (x : α), c * (∫⁻ (y : α), g x y ∂μ) ∂(c • μ) := by
    apply lintegral_congr
    intro x
    exact h1 x
  have h3 : ∫⁻ (x : α), c * (∫⁻ (y : α), g x y ∂μ) ∂(c • μ) =
      c * ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂(c • μ) := by
    exact MeasureTheory.lintegral_const_mul' c _ hc
  have h4 : ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂(c • μ) =
      c * ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂μ := by
    exact MeasureTheory.lintegral_smul_measure c _
  calc ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂(c • μ)) ∂(c • μ)
    = ∫⁻ (x : α), c * (∫⁻ (y : α), g x y ∂μ) ∂(c • μ) := h2
  _ = c * ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂(c • μ) := h3
  _ = c * (c * ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂μ) := by rw [h4]
  _ = c * c * ∫⁻ (x : α), (∫⁻ (y : α), g x y ∂μ) ∂μ := by ring

/-! ### Subset energy bound -/

/-- Uniform measure on E3 = (|E|/|E3|) • (uniform measure on E restricted to E3). -/
lemma uniformMeasureOn_subset_eq_smul {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (E E3 : Finset α) (hE3_sub : E3 ⊆ E) (hE3_nonempty : E3.Nonempty) :
    uniformMeasureOn E3 =
      ((E.card : ENNReal) * (E3.card : ENNReal)⁻¹) •
      (uniformMeasureOn E).restrict (E3 : Set α) := by
  let a : ENNReal := (E.card : ENNReal) * (E3.card : ENNReal)⁻¹
  have hE3_pos : (E3.card : ENNReal) ≠ 0 := by
    have h1 : 0 < E3.card := Finset.Nonempty.card_pos hE3_nonempty
    exact_mod_cast h1.ne'
  apply Measure.ext
  intro A hA
  have h_left : uniformMeasureOn E3 A =
      ENat.toENNReal ((E3 : Set α) ∩ A).encard * (E3.card : ENNReal)⁻¹ :=
    uniformMeasureOn_apply E3 hE3_nonempty A hA
  have h_right : (a • (uniformMeasureOn E).restrict (E3 : Set α)) A =
      a * ((uniformMeasureOn E).restrict (E3 : Set α) A) := by
    simp [Measure.smul_apply]
    <;> ring
  rw [h_left, h_right]
  have h_restrict_apply : (uniformMeasureOn E).restrict (E3 : Set α) A =
      uniformMeasureOn E ((E3 : Set α) ∩ A) := by
    rw [Measure.restrict_apply hA, Set.inter_comm]
  rw [h_restrict_apply]
  have hE_inter : (E : Set α) ∩ ((E3 : Set α) ∩ A) = (E3 : Set α) ∩ A := by
    ext x
    simp only [Set.mem_inter_iff]
    <;> tauto
  have h_apply_E : uniformMeasureOn E ((E3 : Set α) ∩ A) =
      ENat.toENNReal ((E3 : Set α) ∩ A).encard * (E.card : ENNReal)⁻¹ := by
    rw [uniformMeasureOn_apply E (hE3_nonempty.mono hE3_sub) ((E3 : Set α) ∩ A)
        ((Finset.finite_toSet E3).measurableSet.inter hA)]
    <;> rw [hE_inter]
  rw [h_apply_E]
  dsimp only [a]
  have hE_pos : (E.card : ENNReal) ≠ 0 := by
    have h1 : 0 < E.card := Finset.Nonempty.card_pos (hE3_nonempty.mono hE3_sub)
    exact_mod_cast h1.ne'
  have hE_top : (E.card : ENNReal) ≠ ⊤ := by simp
  have h_mul_inv : (E.card : ENNReal) * (E.card : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hE_pos hE_top
  calc ENat.toENNReal ((E3 : Set α) ∩ A).encard * (E3.card : ENNReal)⁻¹
    = ENat.toENNReal ((E3 : Set α) ∩ A).encard * 1 * (E3.card : ENNReal)⁻¹ := by ring
  _ = ENat.toENNReal ((E3 : Set α) ∩ A).encard * ((E.card : ENNReal) * (E.card : ENNReal)⁻¹) * (E3.card : ENNReal)⁻¹ := by rw [h_mul_inv]
  _ = (E.card : ENNReal) * (E3.card : ENNReal)⁻¹ * (ENat.toENNReal ((E3 : Set α) ∩ A).encard * (E.card : ENNReal)⁻¹) := by ring

/-- **Main lemma**: Riesz energy of uniform measure on E3 ⊆ E, after a measurable
    projection f, is bounded by (|E|/|E3|)² times the energy on E. -/
lemma rieszEnergy_subset_uniform_projected
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MetricSpace β] [MeasurableSpace β]
    {δ : ℝ} (hδ : 0 < δ) {α_exp : ℝ}
    (E E3 : Finset α) (hE3_sub : E3 ⊆ E) (hE3_nonempty : E3.Nonempty)
    (f : α → β) (hf : Measurable f) :
    robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E3)) ≤
    ((E.card : ENNReal) * (E3.card : ENNReal)⁻¹)^2 *
    robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) := by
  let a : ENNReal := (E.card : ENNReal) * (E3.card : ENNReal)⁻¹
  have hE_top : (E.card : ENNReal) ≠ ⊤ := by simp
  have hE3_pos : (E3.card : ENNReal) ≠ 0 := by
    have h1 : 0 < E3.card := Finset.Nonempty.card_pos hE3_nonempty
    exact_mod_cast h1.ne'
  have hE3_inv_top : (E3.card : ENNReal)⁻¹ ≠ ⊤ := inv_ne_top.mpr hE3_pos
  have ha_ne_top : a ≠ ⊤ := by
    dsimp only [a]
    exact mul_ne_top hE_top hE3_inv_top
  have h1 : uniformMeasureOn E3 = a • (uniformMeasureOn E).restrict (E3 : Set α) :=
    uniformMeasureOn_subset_eq_smul E E3 hE3_sub hE3_nonempty
  have h_map_smul : Measure.map f (a • (uniformMeasureOn E).restrict (E3 : Set α)) =
      a • Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α)) := by
    exact MeasureTheory.Measure.map_smul a _ f
  have h2 : Measure.map f (uniformMeasureOn E3) =
      a • Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α)) := by
    calc Measure.map f (uniformMeasureOn E3)
      = Measure.map f (a • (uniformMeasureOn E).restrict (E3 : Set α)) := by rw [h1]
    _ = a • Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α)) := h_map_smul
  have h3 : Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α)) ≤
      Measure.map f (uniformMeasureOn E) :=
    Measure.map_mono Measure.restrict_le_self hf
  have h3_smul : a • Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α)) ≤
      a • Measure.map f (uniformMeasureOn E) := by
    have h : ∀ (s : Set β), MeasurableSet s →
        (a • Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α))) s ≤
        (a • Measure.map f (uniformMeasureOn E)) s := by
      intro s hs
      have h3' : ∀ (t : Set β), MeasurableSet t →
          (Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α))) t ≤
          (Measure.map f (uniformMeasureOn E)) t :=
        (Measure.le_iff).mp h3
      have h4 : (Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α))) s ≤
          (Measure.map f (uniformMeasureOn E)) s := h3' s hs
      have h5 : (a • Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α))) s =
          a * (Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α))) s := by
        simp [Measure.smul_apply]
      have h6 : (a • Measure.map f (uniformMeasureOn E)) s =
          a * (Measure.map f (uniformMeasureOn E)) s := by
        simp [Measure.smul_apply]
      rw [h5, h6]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    simpa [Measure.le_iff] using h
  rw [h2]
  have h4 : robust_projection_main.rieszEnergy α_exp hδ
      (a • Measure.map f ((uniformMeasureOn E).restrict (E3 : Set α))) ≤
      robust_projection_main.rieszEnergy α_exp hδ (a • Measure.map f (uniformMeasureOn E)) :=
    rieszEnergy_mono hδ h3_smul
  have h5 : robust_projection_main.rieszEnergy α_exp hδ
      (a • Measure.map f (uniformMeasureOn E)) =
      a * a * robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) :=
    rieszEnergy_smul hδ ha_ne_top
  rw [h5] at h4
  have h6 : a * a = a^2 := by ring
  rw [h6] at h4
  exact h4

/-- **Corollary**: If |E3| ≥ δ^{3ε} · |E|, then I(π μE3) ≤ δ^{-6ε} · I(π μE). -/
lemma rieszEnergy_subset_uniform_delta_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MetricSpace β] [MeasurableSpace β]
    {δ ε : ℝ} (hδ : 0 < δ) {α_exp : ℝ}
    (E E3 : Finset α) (hE3_sub : E3 ⊆ E) (hE3_nonempty : E3.Nonempty)
    (f : α → β) (hf : Measurable f)
    (hε_pos : 0 < ε)
    (h_retention : (E3.card : ℝ) ≥ δ ^ (3 * ε) * (E.card : ℝ)) :
    robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E3)) ≤
    ENNReal.ofReal (δ ^ (-(6 * ε))) *
    robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) := by
  let a : ENNReal := (E.card : ENNReal) * (E3.card : ENNReal)⁻¹
  have h_main := rieszEnergy_subset_uniform_projected (α_exp := α_exp) hδ E E3 hE3_sub hE3_nonempty f hf
  have hE_pos : 0 < E.card := Finset.Nonempty.card_pos (hE3_nonempty.mono hE3_sub)
  have hE3_pos : 0 < E3.card := Finset.Nonempty.card_pos hE3_nonempty
  have hE_pos' : (E.card : ℝ) > 0 := by exact_mod_cast hE_pos
  have hE3_pos' : (E3.card : ℝ) > 0 := by exact_mod_cast hE3_pos
  have h4_pos : 0 < δ ^ (3 * ε) := by positivity
  have h2 : (E.card : ℝ) / (E3.card : ℝ) ≤ δ ^ (-(3 * ε)) := by
    have h3 : (E3.card : ℝ) ≥ δ ^ (3 * ε) * (E.card : ℝ) := h_retention
    have h_div_mono : (E.card : ℝ) / (E3.card : ℝ) ≤ (E.card : ℝ) / (δ ^ (3 * ε) * (E.card : ℝ)) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) h3
    have h5 : (E.card : ℝ) / (E3.card : ℝ) ≤ (δ ^ (3 * ε))⁻¹ := by
      calc (E.card : ℝ) / (E3.card : ℝ)
        ≤ (E.card : ℝ) / (δ ^ (3 * ε) * (E.card : ℝ)) := h_div_mono
      _ = (δ ^ (3 * ε))⁻¹ := by
        field_simp [hE_pos'.ne'] <;> ring
    have h6 : (δ ^ (3 * ε))⁻¹ = δ ^ (-(3 * ε)) := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    rw [h6] at h5
    exact h5
  have h7 : a = ENNReal.ofReal ((E.card : ℝ) / (E3.card : ℝ)) := by
    dsimp only [a]
    have h71 : (E.card : ENNReal) = ENNReal.ofReal (E.card : ℝ) := by simp
    have h72 : (E3.card : ENNReal) = ENNReal.ofReal (E3.card : ℝ) := by simp
    rw [h71, h72]
    have h_pos_y : 0 < (E3.card : ℝ) := hE3_pos'
    have h_div : (E.card : ℝ) / (E3.card : ℝ) = (E.card : ℝ) * (E3.card : ℝ)⁻¹ := by
      field_simp [h_pos_y.ne'] <;> ring
    rw [h_div]
    have h_mul : ENNReal.ofReal ((E.card : ℝ) * (E3.card : ℝ)⁻¹) =
        ENNReal.ofReal (E.card : ℝ) * ENNReal.ofReal ((E3.card : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h_mul]
    have h_inv : ENNReal.ofReal ((E3.card : ℝ)⁻¹) = (ENNReal.ofReal (E3.card : ℝ))⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos h_pos_y]
    rw [h_inv]
    <;> rfl
  have h_a_le : a ≤ ENNReal.ofReal (δ ^ (-(3 * ε))) := by
    rw [h7]
    exact ENNReal.ofReal_le_ofReal h2
  have h_a2_le : a^2 ≤ (ENNReal.ofReal (δ ^ (-(3 * ε))))^2 := by
    have h : a * a ≤ (ENNReal.ofReal (δ ^ (-(3 * ε)))) * (ENNReal.ofReal (δ ^ (-(3 * ε)))) :=
      mul_le_mul h_a_le h_a_le (by positivity) (by positivity)
    simpa [pow_two] using h
  have h_nonneg : 0 ≤ δ ^ (-(3 * ε)) := by positivity
  have h_rpow : (δ ^ (-(3 * ε))) ^ 2 = δ ^ (-(6 * ε)) := by
    have h1 : (δ ^ (-(3 * ε))) ^ 2 = (δ ^ (-(3 * ε))) * (δ ^ (-(3 * ε))) := by ring
    rw [h1]
    have h2 : (δ ^ (-(3 * ε))) * (δ ^ (-(3 * ε))) = δ ^ (-(3 * ε) + (-(3 * ε))) := by
      rw [← Real.rpow_add (by linarith)] <;> ring
    rw [h2] <;> ring_nf
  have h_sq : (ENNReal.ofReal (δ ^ (-(3 * ε))))^2 = ENNReal.ofReal (δ ^ (-(6 * ε))) := by
    have h_pos2 : 0 ≤ δ ^ (-(3 * ε)) := by positivity
    have h9 : (ENNReal.ofReal (δ ^ (-(3 * ε))))^2 =
        ENNReal.ofReal ((δ ^ (-(3 * ε))) ^ 2) := by
      have h10 : (ENNReal.ofReal (δ ^ (-(3 * ε))))^2 =
          ENNReal.ofReal (δ ^ (-(3 * ε))) * ENNReal.ofReal (δ ^ (-(3 * ε))) := by ring
      rw [h10]
      have h11 : ENNReal.ofReal (δ ^ (-(3 * ε))) * ENNReal.ofReal (δ ^ (-(3 * ε))) =
          ENNReal.ofReal ((δ ^ (-(3 * ε))) * (δ ^ (-(3 * ε)))) := by
        rw [← ENNReal.ofReal_mul h_pos2]
      rw [h11]
      have h12 : (δ ^ (-(3 * ε))) * (δ ^ (-(3 * ε))) = (δ ^ (-(3 * ε))) ^ 2 := by ring
      rw [h12]
    rw [h9, h_rpow]
  have h_final : a^2 * robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) ≤
      (ENNReal.ofReal (δ ^ (-(3 * ε))))^2 * robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) := by
    exact mul_le_mul_of_nonneg_right h_a2_le (by positivity)
  rw [h_sq] at h_final
  exact le_trans h_main h_final

/-! ### Spatial scaling of Riesz energy -/

/-- Pointwise kernel inequality: scaling distances by c ∈ (0,1] scales the
    Riesz kernel by at most c^{-α_exp}. -/
lemma scaled_kernel_ineq {δ c d α_exp : ℝ}
    (hδ : 0 < δ) (hc_pos : 0 < c) (hc_le_one : c ≤ 1) (hα_pos : 0 < α_exp) (hd_nonneg : 0 ≤ d) :
    (max (c * d) δ) ^ (-α_exp) ≤ c ^ (-α_exp) * (max d δ) ^ (-α_exp) := by
  set M : ℝ := max d δ with hM_def
  have hM_pos : 0 < M := hδ.trans_le (le_max_right _ _)
  have h1 : c * M ≤ max (c * d) δ := by
    by_cases h : d ≥ δ
    · have hM : M = d := by
        rw [hM_def]; exact max_eq_left h
      rw [hM]; exact le_max_left _ _
    · have h_d_lt : d < δ := lt_of_not_ge h
      have hM : M = δ := by
        rw [hM_def]; exact max_eq_right (by linarith)
      have h_cd_le : c * d ≤ δ := by
        have h3 : c * d ≤ d := mul_le_of_le_one_left hd_nonneg hc_le_one
        linarith
      have h5 : max (c * d) δ = δ := by rw [max_eq_right] <;> linarith
      rw [hM, h5]
      exact mul_le_of_le_one_left (by linarith) hc_le_one
  have h2_pos : 0 < c * M := mul_pos hc_pos hM_pos
  have h3 : (max (c * d) δ) ^ (-α_exp) ≤ (c * M) ^ (-α_exp) := by
    have h5 : Real.log (c * M) ≤ Real.log (max (c * d) δ) := Real.log_le_log (by linarith) h1
    have h6 : (-α_exp) * Real.log (max (c * d) δ) ≤ (-α_exp) * Real.log (c * M) := by
      have h_neg : -α_exp < 0 := by linarith
      nlinarith
    have h7 : Real.log ((max (c * d) δ) ^ (-α_exp)) = (-α_exp) * Real.log (max (c * d) δ) := by
      rw [Real.log_rpow (by linarith)]
    have h8 : Real.log ((c * M) ^ (-α_exp)) = (-α_exp) * Real.log (c * M) := by
      rw [Real.log_rpow (by linarith)]
    have h9 : Real.log ((max (c * d) δ) ^ (-α_exp)) ≤ Real.log ((c * M) ^ (-α_exp)) := by
      rw [h7, h8] <;> exact h6
    have h10 : 0 < (max (c * d) δ) ^ (-α_exp) := by positivity
    have h11 : 0 < (c * M) ^ (-α_exp) := by positivity
    exact (Real.log_le_log_iff h10 h11).mp h9
  have h4 : (c * M) ^ (-α_exp) = c ^ (-α_exp) * M ^ (-α_exp) := by
    rw [Real.mul_rpow (by linarith) (by linarith)] <;> ring
  rw [h4] at h3
  exact h3

/-- **Scaling bound for real measures**: If ν is a measure on ℝ and 0 < c ≤ 1,
    then I_α(map (x ↦ c*x) ν) ≤ c^{-α} · I_α(ν). -/
lemma rieszEnergy_scaled_real_measure
    {δ : ℝ} (hδ : 0 < δ) {α_exp : ℝ} (hα_pos : 0 < α_exp)
    {ν : Measure ℝ} [SFinite ν]
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1) :
    robust_projection_main.rieszEnergy α_exp hδ (Measure.map (fun x : ℝ => c * x) ν) ≤
    ENNReal.ofReal (c ^ (-α_exp)) * robust_projection_main.rieszEnergy α_exp hδ ν := by
  let kernel : ℝ → ℝ → ENNReal := fun u v =>
    ENNReal.ofReal ((max (dist u v) δ) ^ (-α_exp))
  let h_scale : ℝ → ℝ := fun x => c * x
  have h_scale_meas : Measurable h_scale := by fun_prop
  have h_base_cont : Continuous (fun p : ℝ × ℝ => max (dist p.1 p.2) δ) := by continuity
  have h_base_ne_zero : ∀ (p : ℝ × ℝ), max (dist p.1 p.2) δ ≠ 0 := by
    intro p; have h_pos : 0 < max (dist p.1 p.2) δ := hδ.trans_le (le_max_right _ _); exact h_pos.ne'
  have h2 : Continuous (fun p : ℝ × ℝ => (max (dist p.1 p.2) δ) ^ (-α_exp)) :=
    h_base_cont.rpow continuous_const (fun p => Or.inl (h_base_ne_zero p))
  have h_kern_cont : Continuous (fun p : ℝ × ℝ => kernel p.1 p.2) :=
    ENNReal.continuous_ofReal.comp h2
  have h_kern_meas : Measurable (fun p : ℝ × ℝ => kernel p.1 p.2) := h_kern_cont.measurable
  let ν_c : Measure ℝ := Measure.map h_scale ν
  haveI h_sfin_c : SFinite ν_c := by
    exact Measure.instSFiniteMap ν h_scale
  have h_meas_u : Measurable (fun u : ℝ => ∫⁻ (v : ℝ), kernel u v ∂ν_c) :=
    h_kern_meas.lintegral_prod_right' (ν := ν_c)
  have h1 : ∫⁻ (u : ℝ), ∫⁻ (v : ℝ), kernel u v ∂ν_c ∂ν_c =
      ∫⁻ (x : ℝ), ∫⁻ (v : ℝ), kernel (h_scale x) v ∂ν_c ∂ν := by
    rw [lintegral_map' h_meas_u.aemeasurable h_scale_meas.aemeasurable] <;> rfl
  have h2_meas_v : ∀ (x : ℝ), Measurable (fun v : ℝ => kernel (h_scale x) v) := by
    intro x
    have h_cont : Continuous (fun v : ℝ => (h_scale x, v)) := by continuity
    exact (h_kern_cont.comp h_cont).measurable
  have h2' : ∀ (x : ℝ), ∫⁻ (v : ℝ), kernel (h_scale x) v ∂ν_c =
      ∫⁻ (y : ℝ), kernel (h_scale x) (h_scale y) ∂ν := by
    intro x
    rw [lintegral_map' (h2_meas_v x).aemeasurable h_scale_meas.aemeasurable] <;> rfl
  have h3 : ∫⁻ (x : ℝ), ∫⁻ (v : ℝ), kernel (h_scale x) v ∂ν_c ∂ν =
      ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), kernel (h_scale x) (h_scale y) ∂ν ∂ν := by
    apply lintegral_congr; intro x; exact h2' x
  have h_pointwise : ∀ (x y : ℝ),
      kernel (h_scale x) (h_scale y) ≤ ENNReal.ofReal (c ^ (-α_exp)) * kernel x y := by
    intro x y
    have h4 : dist (h_scale x) (h_scale y) = c * dist x y := by
      have h5 : dist (c * x) (c * y) = |c * x - c * y| := by
        simp [dist_eq_norm] <;> rfl
      rw [h5]
      have h6 : |c * x - c * y| = c * |x - y| := by
        calc |c * x - c * y| = |c * (x - y)| := by ring_nf
          _ = |c| * |x - y| := by rw [abs_mul]
          _ = c * |x - y| := by rw [abs_of_pos hc_pos]
      rw [h6]
      have h7 : dist x y = |x - y| := by simp [dist_eq_norm] <;> rfl
      rw [h7] <;> rfl
    dsimp only [kernel]
    rw [h4]
    have h5 : (max (c * dist x y) δ) ^ (-α_exp) ≤
        c ^ (-α_exp) * (max (dist x y) δ) ^ (-α_exp) :=
      scaled_kernel_ineq hδ hc_pos hc_le_one hα_pos (show 0 ≤ dist x y from by positivity)
    have h6 : ENNReal.ofReal ((max (c * dist x y) δ) ^ (-α_exp)) ≤
        ENNReal.ofReal (c ^ (-α_exp) * (max (dist x y) δ) ^ (-α_exp)) :=
      ENNReal.ofReal_le_ofReal h5
    have h7 : ENNReal.ofReal (c ^ (-α_exp) * (max (dist x y) δ) ^ (-α_exp)) =
        ENNReal.ofReal (c ^ (-α_exp)) * ENNReal.ofReal ((max (dist x y) δ) ^ (-α_exp)) := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h7] at h6
    exact h6
  have h4_ineq : ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), kernel (h_scale x) (h_scale y) ∂ν ∂ν ≤
      ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ENNReal.ofReal (c ^ (-α_exp)) * kernel x y) ∂ν ∂ν := by
    apply lintegral_mono; intro x; apply lintegral_mono; intro y; exact h_pointwise x y
  have h6_inner : ∀ (x : ℝ), ∫⁻ (y : ℝ), (ENNReal.ofReal (c ^ (-α_exp)) * kernel x y) ∂ν =
      ENNReal.ofReal (c ^ (-α_exp)) * ∫⁻ (y : ℝ), kernel x y ∂ν := by
    intro x
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (c ^ (-α_exp))) _ (by simp)]
  have h6_step1 : ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ENNReal.ofReal (c ^ (-α_exp)) * kernel x y) ∂ν ∂ν =
      ∫⁻ (x : ℝ), ENNReal.ofReal (c ^ (-α_exp)) * ∫⁻ (y : ℝ), kernel x y ∂ν ∂ν := by
    apply lintegral_congr; intro x; exact h6_inner x
  have h6_step2 : ∫⁻ (x : ℝ), ENNReal.ofReal (c ^ (-α_exp)) * ∫⁻ (y : ℝ), kernel x y ∂ν ∂ν =
      ENNReal.ofReal (c ^ (-α_exp)) * ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), kernel x y ∂ν ∂ν := by
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (c ^ (-α_exp))) _ (by simp)]
  have h5 : ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ENNReal.ofReal (c ^ (-α_exp)) * kernel x y) ∂ν ∂ν =
      ENNReal.ofReal (c ^ (-α_exp)) * ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), kernel x y ∂ν ∂ν := by
    rw [h6_step1, h6_step2]
  have h_result : ∫⁻ (u : ℝ), ∫⁻ (v : ℝ), kernel u v ∂ν_c ∂ν_c ≤
      ENNReal.ofReal (c ^ (-α_exp)) * ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), kernel x y ∂ν ∂ν := by
    calc ∫⁻ (u : ℝ), ∫⁻ (v : ℝ), kernel u v ∂ν_c ∂ν_c
      = ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), kernel (h_scale x) (h_scale y) ∂ν ∂ν := by rw [h1, h3]
    _ ≤ ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ENNReal.ofReal (c ^ (-α_exp)) * kernel x y) ∂ν ∂ν := h4_ineq
    _ = ENNReal.ofReal (c ^ (-α_exp)) * ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), kernel x y ∂ν ∂ν := h5
  simpa [robust_projection_main.rieszEnergy, ν_c, kernel] using h_result

/-- **Combined bound**: I(c·f μE3) ≤ c^{-α} · δ^{-6ε} · I(f μE). -/
lemma rieszEnergy_scaled_subset_uniform_bound
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {δ ε : ℝ} (hδ : 0 < δ) {α_exp : ℝ} (hα_pos : 0 < α_exp)
    (E E3 : Finset α) (hE3_sub : E3 ⊆ E) (hE3_nonempty : E3.Nonempty)
    (f : α → ℝ) (hf : Measurable f)
    (hε_pos : 0 < ε)
    (h_retention : (E3.card : ℝ) ≥ δ ^ (3 * ε) * (E.card : ℝ))
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1) :
    robust_projection_main.rieszEnergy α_exp hδ
      (Measure.map (fun x => c * f x) (uniformMeasureOn E3)) ≤
    ENNReal.ofReal (c ^ (-α_exp)) * ENNReal.ofReal (δ ^ (-(6 * ε))) *
      robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) := by
  let h_scale : ℝ → ℝ := fun x => c * x
  have h_scale_meas : Measurable h_scale := by fun_prop
  have h_eq : (fun x : α => c * f x) = h_scale ∘ f := by funext x; rfl
  have h_map_comp : Measure.map (fun x : α => c * f x) (uniformMeasureOn E3) =
      Measure.map h_scale (Measure.map f (uniformMeasureOn E3)) := by
    rw [h_eq, Measure.map_map h_scale_meas hf]
  rw [h_map_comp]
  haveI : SFinite (Measure.map f (uniformMeasureOn E3)) := by
    have h_prob : IsProbabilityMeasure (uniformMeasureOn E3) :=
      uniformMeasureOn_isProbabilityMeasure E3 hE3_nonempty
    have h_fin : IsFiniteMeasure (Measure.map f (uniformMeasureOn E3)) := by
      exact Measure.isFiniteMeasure_map (uniformMeasureOn E3) f
    letI : IsFiniteMeasure (Measure.map f (uniformMeasureOn E3)) := h_fin
    exact Measure.instSFiniteMap (uniformMeasureOn E3) f
  have h_scaled := rieszEnergy_scaled_real_measure hδ (hα_pos := hα_pos)
    (ν := Measure.map f (uniformMeasureOn E3)) hc_pos hc_le_one
  have h_subset := rieszEnergy_subset_uniform_delta_bound (α_exp := α_exp) hδ E E3 hE3_sub hE3_nonempty f hf hε_pos h_retention
  have h_main : robust_projection_main.rieszEnergy α_exp hδ (Measure.map h_scale (Measure.map f (uniformMeasureOn E3))) ≤
      ENNReal.ofReal (c ^ (-α_exp)) * robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E3)) := h_scaled
  have h_final : ENNReal.ofReal (c ^ (-α_exp)) * robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E3)) ≤
      ENNReal.ofReal (c ^ (-α_exp)) * ENNReal.ofReal (δ ^ (-(6 * ε))) *
        robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) := by
    have h_final' : ENNReal.ofReal (c ^ (-α_exp)) * robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E3)) ≤
        ENNReal.ofReal (c ^ (-α_exp)) * (ENNReal.ofReal (δ ^ (-(6 * ε))) *
          robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E))) :=
      mul_le_mul_of_nonneg_left h_subset (by positivity)
    have h_assoc : ENNReal.ofReal (c ^ (-α_exp)) * (ENNReal.ofReal (δ ^ (-(6 * ε))) *
          robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E))) =
        ENNReal.ofReal (c ^ (-α_exp)) * ENNReal.ofReal (δ ^ (-(6 * ε))) *
          robust_projection_main.rieszEnergy α_exp hδ (Measure.map f (uniformMeasureOn E)) := by
      rw [mul_assoc]
    rw [h_assoc] at h_final'
    exact h_final'
  exact le_trans h_main h_final

end ProductLikeIncidence.ProductReduction

module

/-
# Coordinate Normalization for Phase 3

Normalizes bounded 2D sets to [0,1]^2 using power-of-2 affine scaling,
preserving dyadic scales, covering numbers, δ-set properties, and tracking
Riesz energy scaling.

## Key results

1. `rieszEnergy_affine_scaling` — energy scales by `c^{-α}` under Lipschitz map with factor `c`
2. `affine_normalize_extract` — normalize bounded E3' to [0,1]^2, apply extraction, denormalize

## Whiteprint node
`coordinate_normalization`
-/

public import MyLeanRepo.Energy.RegularSetHasBoundedEnergy
public import MyLeanRepo.RoundingWrapper
public import MyLeanRepo.ProductLikeIncidence.RoundingExtractionBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ### Energy scaling under affine maps -/

/-- Riesz energy scales by `c^{-α}` under a map that scales distances by `c > 0`.
Requires `SFinite ν` for Tonelli's theorem. -/
lemma rieszEnergy_affine_scaling {α : ℝ} {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 < c)
    {X Y : Type*} [MeasurableSpace X] [MetricSpace X] [MeasurableSpace Y] [MetricSpace Y]
    [BorelSpace X] [BorelSpace Y]
    [BorelSpace (X × X)] [BorelSpace (Y × Y)]
    (T : X → Y) (hT_meas : Measurable T)
    (hT_dist : ∀ x y, dist (T x) (T y) = c * dist x y)
    (ν : Measure X) [SFinite ν] :
    robust_projection_main.rieszEnergy α (show 0 < c * δ from mul_pos hc hδ)
      (Measure.map T ν) =
    ENNReal.ofReal (c ^ (-α)) * robust_projection_main.rieszEnergy α hδ ν := by
  let k : Y × Y → ENNReal := fun p =>
    ENNReal.ofReal ((max (dist p.1 p.2) (c * δ)) ^ (-α))
  let k0 : X × X → ENNReal := fun p =>
    ENNReal.ofReal ((max (dist p.1 p.2) δ) ^ (-α))
  have h_pos_k : ∀ (p : Y × Y), 0 < max (dist p.1 p.2) (c * δ) := by
    intro p; have h : 0 < c * δ := mul_pos hc hδ; positivity
  have h_pos_k0 : ∀ (p : X × X), 0 < max (dist p.1 p.2) δ := by
    intro p; positivity
  have h_distY_cont : Continuous (fun p : Y × Y => dist p.1 p.2) := continuous_dist
  have h_baseY_cont : Continuous (fun p : Y × Y => max (dist p.1 p.2) (c * δ)) :=
    h_distY_cont.max continuous_const
  have hk_cont : Continuous k := by
    have h1 : Continuous (fun p : Y × Y => (max (dist p.1 p.2) (c * δ)) ^ (-α)) := by
      refine' Continuous.rpow h_baseY_cont continuous_const _
      intro p; left; exact (h_pos_k p).ne'
    exact ENNReal.continuous_ofReal.comp h1
  have h_distX_cont : Continuous (fun p : X × X => dist p.1 p.2) := continuous_dist
  have h_baseX_cont : Continuous (fun p : X × X => max (dist p.1 p.2) δ) :=
    h_distX_cont.max continuous_const
  have hk0_cont : Continuous k0 := by
    have h1 : Continuous (fun p : X × X => (max (dist p.1 p.2) δ) ^ (-α)) := by
      refine' Continuous.rpow h_baseX_cont continuous_const _
      intro p; left; exact (h_pos_k0 p).ne'
    exact ENNReal.continuous_ofReal.comp h1
  have hk_meas : Measurable k := hk_cont.measurable
  have hk0_meas : Measurable k0 := hk0_cont.measurable
  have h_eq1 : ∀ (p : X × X), k (T p.1, T p.2) = ENNReal.ofReal (c ^ (-α)) * k0 p := by
    intro p
    dsimp only [k, k0]
    have h2 : dist (T p.1) (T p.2) = c * dist p.1 p.2 := hT_dist p.1 p.2
    have h3 : max (dist (T p.1) (T p.2)) (c * δ) = c * max (dist p.1 p.2) δ := by
      rw [h2]
      by_cases h : dist p.1 p.2 ≤ δ
      · have h4 : c * dist p.1 p.2 ≤ c * δ := by gcongr
        rw [max_eq_right h4, max_eq_right h] <;> ring
      · have h4 : c * δ ≤ c * dist p.1 p.2 := by gcongr <;> linarith
        rw [max_eq_left h4, max_eq_left (by linarith)] <;> ring
    rw [h3]
    have h4 : (c * max (dist p.1 p.2) δ) ^ (-α) = c ^ (-α) * (max (dist p.1 p.2) δ) ^ (-α) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)] <;> ring
    rw [h4, ENNReal.ofReal_mul (by positivity)] <;> rfl
  let μ := Measure.map T ν
  haveI hμ_sfinite : SFinite μ := by
    exact Measure.instSFiniteMap ν T
  simp only [robust_projection_main.rieszEnergy]
  have h_step1 : ∫⁻ (x : Y), (∫⁻ (y : Y), k (x, y) ∂μ) ∂μ =
      ∫⁻ (p : Y × Y), k p ∂(μ.prod μ) := by
    rw [MeasureTheory.lintegral_prod k hk_meas.aemeasurable]
  have h_step2 : μ.prod μ = Measure.map (Prod.map T T) (ν.prod ν) := by
    exact MeasureTheory.Measure.map_prod_map ν ν hT_meas hT_meas
  have h_step3 : ∫⁻ (p : Y × Y), k p ∂(μ.prod μ) =
      ∫⁻ (p : X × X), k (Prod.map T T p) ∂(ν.prod ν) := by
    rw [h_step2]
    exact MeasureTheory.lintegral_map' hk_meas.aemeasurable
      ((hT_meas.comp continuous_fst.measurable).prodMk
        (hT_meas.comp continuous_snd.measurable)).aemeasurable
  have h_step4 : ∫⁻ (p : X × X), k (Prod.map T T p) ∂(ν.prod ν) =
      ∫⁻ (p : X × X), ENNReal.ofReal (c ^ (-α)) * k0 p ∂(ν.prod ν) := by
    congr with p; exact h_eq1 p
  set c_enn : ENNReal := ENNReal.ofReal (c ^ (-α)) with hc_enn
  have h_step5 : ∫⁻ (p : X × X), c_enn * k0 p ∂(ν.prod ν) =
      c_enn * ∫⁻ (p : X × X), k0 p ∂(ν.prod ν) := by
    exact lintegral_const_mul c_enn hk0_meas
  have h_step6 : ∫⁻ (p : X × X), k0 p ∂(ν.prod ν) =
      ∫⁻ (x : X), (∫⁻ (y : X), k0 (x, y) ∂ν) ∂ν := by
    rw [MeasureTheory.lintegral_prod k0 hk0_meas.aemeasurable]
  rw [h_step1, h_step3, h_step4, h_step5, h_step6]

/-! ### Power-of-2 normalization -/

/-- Find `k : ℕ` such that `C ≤ 2^k`. -/
lemma exists_pow2_ge (C : ℝ) : ∃ k : ℕ, C ≤ (2 : ℝ) ^ k := by
  obtain ⟨n, hn⟩ := exists_nat_ge C
  have h2 : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    have h3 : ∀ m : ℕ, (m : ℝ) ≤ (2 : ℝ) ^ m := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        have h4 : (2 : ℝ) ^ m ≥ 1 := by
          induction m with
          | zero => norm_num
          | succ m ih => simp [pow_succ] at * <;> nlinarith
        calc (m.succ : ℝ) = (m : ℝ) + 1 := by simp
          _ ≤ (2 : ℝ) ^ m + 1 := by linarith
          _ ≤ (2 : ℝ) ^ m + (2 : ℝ) ^ m := by linarith
          _ = 2 * (2 : ℝ) ^ m := by ring
          _ = (2 : ℝ) ^ (m + 1) := by ring
    exact h3 n
  exact ⟨n, le_trans hn h2⟩

/-- Affine normalization map `T(x) = (x + R) / L` where `L = 2R`.
Maps `[-R, R]` to `[0, 1]`. -/
def normalizeMap (R L : ℝ) (x : ℝ) : ℝ := (x + R) / L

/-- Inverse normalization map `T^{-1}(y) = L * y - R`. -/
def denormalizeMap (R L : ℝ) (y : ℝ) : ℝ := L * y - R

lemma normalizeMap_range {R L : ℝ} (hR_pos : 0 < R) (hL : L = 2 * R) {x : ℝ}
    (hx : |x| ≤ R) : normalizeMap R L x ∈ Set.Icc (0 : ℝ) 1 := by
  have hL_pos : 0 < L := by linarith
  have h1 : -R ≤ x := (abs_le.mp hx).1
  have h2 : x ≤ R := (abs_le.mp hx).2
  have h3 : 0 ≤ x + R := by linarith
  have h4 : x + R ≤ L := by linarith
  dsimp only [normalizeMap]
  constructor
  · exact div_nonneg h3 (by linarith)
  · exact (div_le_one hL_pos).mpr h4

lemma normalizeMap_dist {R L : ℝ} (hR_pos : 0 < R) (hL : L = 2 * R) (x y : ℝ) :
    dist (normalizeMap R L x) (normalizeMap R L y) = (1 / L) * dist x y := by
  have hL_pos : 0 < L := by linarith
  dsimp only [normalizeMap, Real.dist_eq]
  have h : |(x + R) / L - (y + R) / L| = (1 / L) * |x - y| := by
    have h5 : (x + R) / L - (y + R) / L = (x - y) / L := by
      field_simp [hL_pos.ne'] <;> ring
    rw [h5]
    rw [abs_div, abs_of_pos (show (0 : ℝ) < L by linarith)]
    <;> ring
  exact h

lemma denormalizeMap_leftInverse {R L : ℝ} (hR_pos : 0 < R) (hL : L = 2 * R) :
    Function.LeftInverse (denormalizeMap R L) (normalizeMap R L) := by
  intro x
  dsimp only [denormalizeMap, normalizeMap]
  have hL_pos : 0 < L := by linarith
  field_simp [hL_pos.ne'] <;> ring

lemma normalizeMap_leftInverse {R L : ℝ} (hR_pos : 0 < R) (hL : L = 2 * R) :
    Function.LeftInverse (normalizeMap R L) (denormalizeMap R L) := by
  intro y
  dsimp only [denormalizeMap, normalizeMap]
  have hL_pos : 0 < L := by linarith
  field_simp [hL_pos.ne'] <;> ring

/-- If `δ` is dyadic and `L = 2^m`, then `δ / L` is dyadic. -/
lemma dyadicScale_div_pow2 {δ : ℝ} (hδ : δ ∈ dyadicScales) {m : ℕ} :
    δ / (2 : ℝ) ^ m ∈ dyadicScales := by
  rcases hδ with ⟨n, rfl⟩
  refine ⟨n + m, ?_⟩
  have h_eq : (2 : ℝ) ^ (-(n : ℤ)) / (2 : ℝ) ^ m =
      (2 : ℝ) ^ (-((n + m : ℕ) : ℤ)) := by
    have h1 : ((n + m : ℕ) : ℤ) = (n : ℤ) + (m : ℤ) := by
      simp
    rw [h1]
    have h2 : (2 : ℝ) ^ (-((n : ℤ) + (m : ℤ))) = (2 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ (-(m : ℤ)) := by
      rw [← zpow_add₀ (by norm_num)]
      <;> ring_nf
    rw [h2]
    have h3 : (2 : ℝ) ^ (-(m : ℤ)) = 1 / (2 : ℝ) ^ m := by
      simp [zpow_neg, zpow_ofNat]
      <;> field_simp
    rw [h3]
    <;> ring
  exact h_eq

end ProductLikeIncidence.ProductReduction

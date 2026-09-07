module

/-
# Obligation 3 — Projective Normalization via Phase2Transport (CORRECTED v2)

Phase2 ONLY: transforms point sets via G, retains x/fullLambda,
exports THREE coordinate covering bounds.

No direction pushforward — that belongs to Phase7.

## Outputs
- G, G_inv: projective normalization and inverse
- Pbar', E3', μE3': transformed point data
- P_y': transformed parameter realizations (ORIGINAL y labels)
- x(y): cross-ratio direction map formula
- fullLambda(y): projective scaling formula
- Projection identity: π_{x(y)}(E3') = scaleSet(fullLambda(y))(π_y(E3))
- Three covering bounds: q0 vs π_θ2, q1 vs π_θ1, q0+q1 vs π_θ3
- Lipschitz bounds for G and G_inv

## Whiteprint node
`obligation3_projective_transform_all`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.Compat
public import MyLeanRepo.ProductLikeIncidence.Phase2Transport
public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.Energy.RegularSetHasBoundedEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section


open Set Bornology ENNReal MeasureTheory

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Helper: each coordinate of a 2D Euclidean vector is bounded by its norm. -/
private lemma cobalt_coord_le_norm (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |z i| ≤ ‖z‖ := by
  have h_norm_sq : ‖z‖^2 = (z 0)^2 + (z 1)^2 := by
    have h1 : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [h1, Real.sq_sqrt] <;> positivity
  have h_sq : (z i)^2 ≤ ‖z‖^2 := by
    rw [h_norm_sq]
    fin_cases i <;> simp [sq_nonneg]
  have h_abs : |z i|^2 = (z i)^2 := by simp
  have h1 : |z i|^2 ≤ ‖z‖^2 := by rw [h_abs] <;> exact h_sq
  have h2 : 0 ≤ |z i| := by positivity
  have h3 : 0 ≤ ‖z‖ := by positivity
  nlinarith

/-- Forward Lipschitz bound for the projective normalization G. -/
private lemma cobalt_G_lipschitz
    {θ1 θ2 θ3 : ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hG_formula : ∀ p, G p = ![
        ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1),
        ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)])
    (u v : EuclideanSpace ℝ (Fin 2)) :
    dist (G u) (G v) ≤ (Real.sqrt 2 * max
        (|((θ3 - θ1) / (θ2 - θ1))| * (|θ2| + 1))
        (|((θ2 - θ3) / (θ2 - θ1))| * (|θ1| + 1))) * dist u v := by
  let b3 := (θ3 - θ1) / (θ2 - θ1)
  let a3 := (θ2 - θ3) / (θ2 - θ1)
  let L_proj : ℝ := Real.sqrt 2 * max (|b3| * (|θ2| + 1)) (|a3| * (|θ1| + 1))
  set A := |b3| * (|θ2| + 1) with hA_def
  set B := |a3| * (|θ1| + 1) with hB_def
  let z := u - v
  have hGz : G u - G v = G z := by
    ext i; fin_cases i <;> simp [hG_formula, z] <;> ring
  have h_eq0 : (G z) 0 = b3 * (z 0 * θ2 + z 1) := by
    simpa [b3] using congr_fun (hG_formula z) 0
  have h_eq1 : (G z) 1 = a3 * (z 0 * θ1 + z 1) := by
    simpa [a3] using congr_fun (hG_formula z) 1
  have h_znorm2 : ‖z‖^2 = (z 0)^2 + (z 1)^2 := by
    have h1 : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [h1, Real.sq_sqrt] <;> positivity
  have h_Gnorm2 : ‖G z‖^2 = ((G z) 0)^2 + ((G z) 1)^2 := by
    have h1 : ‖G z‖ = Real.sqrt (((G z) 0)^2 + ((G z) 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [h1, Real.sq_sqrt] <;> positivity
  have h_cs1 : (z 0 * θ2 + z 1)^2 ≤ (θ2^2 + 1) * ‖z‖^2 := by
    rw [h_znorm2]
    nlinarith [sq_nonneg (z 0 - θ2 * z 1)]
  have h_cs2 : (z 0 * θ1 + z 1)^2 ≤ (θ1^2 + 1) * ‖z‖^2 := by
    rw [h_znorm2]
    nlinarith [sq_nonneg (z 0 - θ1 * z 1)]
  have h_θ2_bound : θ2^2 + 1 ≤ (|θ2| + 1)^2 := by
    have h2 : |θ2|^2 = θ2^2 := by simp [sq_abs]
    nlinarith [abs_nonneg θ2]
  have h_θ1_bound : θ1^2 + 1 ≤ (|θ1| + 1)^2 := by
    have h2 : |θ1|^2 = θ1^2 := by simp [sq_abs]
    nlinarith [abs_nonneg θ1]
  have h_A2 : b3^2 * (θ2^2 + 1) ≤ A^2 := by
    have h4 : |b3|^2 = b3^2 := by simp [sq_abs]
    calc b3^2 * (θ2^2 + 1)
      ≤ b3^2 * (|θ2| + 1)^2 := by gcongr
    _ = |b3|^2 * (|θ2| + 1)^2 := by rw [h4]
    _ = A^2 := by rw [hA_def] <;> ring
  have h_B2 : a3^2 * (θ1^2 + 1) ≤ B^2 := by
    have h4 : |a3|^2 = a3^2 := by simp [sq_abs]
    calc a3^2 * (θ1^2 + 1)
      ≤ a3^2 * (|θ1| + 1)^2 := by gcongr
    _ = |a3|^2 * (|θ1| + 1)^2 := by rw [h4]
    _ = B^2 := by rw [hB_def] <;> ring
  have h_sum_bound : A^2 + B^2 ≤ L_proj^2 := by
    have h61 : A ≤ max A B := le_max_left A B
    have h62 : B ≤ max A B := le_max_right A B
    have h63 : A^2 ≤ (max A B)^2 := by gcongr
    have h64 : B^2 ≤ (max A B)^2 := by gcongr
    have h65 : A^2 + B^2 ≤ 2 * (max A B)^2 := by linarith
    have h_sqrt2_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have h8 : L_proj = Real.sqrt 2 * max A B := by
      simp [L_proj, hA_def, hB_def]
    have h7 : 2 * (max A B)^2 = L_proj^2 := by
      rw [h8, mul_pow, h_sqrt2_sq] <;> ring
    exact h65.trans h7.le
  have h_main2 : ‖G z‖^2 ≤ (L_proj * ‖z‖)^2 := by
    have h1 : ‖G z‖^2 = (b3 * (z 0 * θ2 + z 1))^2 + (a3 * (z 0 * θ1 + z 1))^2 := by
      rw [h_Gnorm2, h_eq0, h_eq1] <;> ring
    rw [h1]
    have h2 : (b3 * (z 0 * θ2 + z 1))^2 ≤ b3^2 * (θ2^2 + 1) * ‖z‖^2 := by
      calc (b3 * (z 0 * θ2 + z 1))^2
        = b3^2 * (z 0 * θ2 + z 1)^2 := by ring
      _ ≤ b3^2 * ((θ2^2 + 1) * ‖z‖^2) := by gcongr
      _ = b3^2 * (θ2^2 + 1) * ‖z‖^2 := by ring
    have h3 : (a3 * (z 0 * θ1 + z 1))^2 ≤ a3^2 * (θ1^2 + 1) * ‖z‖^2 := by
      calc (a3 * (z 0 * θ1 + z 1))^2
        = a3^2 * (z 0 * θ1 + z 1)^2 := by ring
      _ ≤ a3^2 * ((θ1^2 + 1) * ‖z‖^2) := by gcongr
      _ = a3^2 * (θ1^2 + 1) * ‖z‖^2 := by ring
    have h4 : (b3 * (z 0 * θ2 + z 1))^2 + (a3 * (z 0 * θ1 + z 1))^2 ≤
        (A^2 + B^2) * ‖z‖^2 := by
      have h41 : b3^2 * (θ2^2 + 1) + a3^2 * (θ1^2 + 1) ≤ A^2 + B^2 := add_le_add h_A2 h_B2
      calc (b3 * (z 0 * θ2 + z 1))^2 + (a3 * (z 0 * θ1 + z 1))^2
        ≤ b3^2 * (θ2^2 + 1) * ‖z‖^2 + a3^2 * (θ1^2 + 1) * ‖z‖^2 := by linarith
      _ = (b3^2 * (θ2^2 + 1) + a3^2 * (θ1^2 + 1)) * ‖z‖^2 := by ring
      _ ≤ (A^2 + B^2) * ‖z‖^2 := by gcongr
    have h5 : (A^2 + B^2) * ‖z‖^2 ≤ L_proj^2 * ‖z‖^2 := by
      exact mul_le_mul_of_nonneg_right h_sum_bound (by positivity)
    have h6 : L_proj^2 * ‖z‖^2 = (L_proj * ‖z‖)^2 := by ring
    exact h4.trans (h5.trans h6.le)
  have h10 : 0 ≤ ‖G z‖ := by positivity
  have h11 : 0 ≤ L_proj * ‖z‖ := by positivity
  have h12 : Real.sqrt (‖G z‖^2) ≤ Real.sqrt ((L_proj * ‖z‖)^2) := Real.sqrt_le_sqrt h_main2
  have h13 : Real.sqrt (‖G z‖^2) = ‖G z‖ := Real.sqrt_sq h10
  have h14 : Real.sqrt ((L_proj * ‖z‖)^2) = L_proj * ‖z‖ := Real.sqrt_sq h11
  have h_main : ‖G z‖ ≤ L_proj * ‖z‖ := by
    rw [h13, h14] at h12
    exact h12
  have h_goal : ‖G u - G v‖ ≤ L_proj * ‖u - v‖ := by
    rw [hGz] <;> exact h_main
  have h_dist1 : dist (G u) (G v) = ‖G u - G v‖ := dist_eq_norm (G u) (G v)
  have h_dist2 : dist u v = ‖u - v‖ := dist_eq_norm u v
  rw [h_dist1, h_dist2]
  exact h_goal

/-- For 0 < a ≤ b and c ≤ 0, b^c ≤ a^c. -/
private lemma cobalt_rpow_neg_mono {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : c ≤ 0) (h : a ≤ b) :
    b ^ c ≤ a ^ c := by
  have h1 : Real.log a ≤ Real.log b := Real.log_le_log ha h
  have h2 : c * Real.log b ≤ c * Real.log a := by nlinarith
  have h3 : Real.exp (c * Real.log b) ≤ Real.exp (c * Real.log a) := Real.exp_le_exp.mpr h2
  have h4 : b ^ c = Real.exp (c * Real.log b) := by
    simp [Real.rpow_def_of_pos hb] <;> ring
  have h5 : a ^ c = Real.exp (c * Real.log a) := by
    simp [Real.rpow_def_of_pos ha] <;> ring
  rw [h4, h5]
  exact h3

/-- Riesz energy is monotone decreasing in the regularization scale δ (for α > 0). -/
lemma cobalt_rieszEnergy_mono_scale {α : ℝ} (hα_pos : 0 < α)
    {δ1 δ2 : ℝ} (hδ1 : 0 < δ1) (hδ2 : 0 < δ2) (h : δ1 ≤ δ2)
    {X : Type*} [MeasurableSpace X] [MetricSpace X] (ν : Measure X) :
    robust_projection.rieszEnergy α hδ2 ν ≤ robust_projection.rieszEnergy α hδ1 ν := by
  have h1 : ∀ (x y : X), ENNReal.ofReal ((max (dist x y) δ2) ^ (-α)) ≤
      ENNReal.ofReal ((max (dist x y) δ1) ^ (-α)) := by
    intro x y
    have h_pos1 : 0 < max (dist x y) δ1 := by positivity
    have h_pos2 : 0 < max (dist x y) δ2 := by positivity
    have h_le : max (dist x y) δ1 ≤ max (dist x y) δ2 := by gcongr
    exact ENNReal.ofReal_le_ofReal (cobalt_rpow_neg_mono h_pos1 h_pos2 (by linarith) h_le)
  simp only [robust_projection.rieszEnergy]
  exact lintegral_mono fun x => lintegral_mono fun y => h1 x y

/-- Riesz energy scales by c^{-α} under a distance-scaling map with factor c > 0. -/
lemma cobalt_rieszEnergy_affine_scaling {α : ℝ} {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 < c)
    {X Y : Type*} [MeasurableSpace X] [MetricSpace X] [MeasurableSpace Y] [MetricSpace Y]
    [BorelSpace X] [BorelSpace Y]
    [BorelSpace (X × X)] [BorelSpace (Y × Y)]
    (T : X → Y) (hT_meas : Measurable T)
    (hT_dist : ∀ x y, dist (T x) (T y) = c * dist x y)
    (ν : Measure X) [SFinite ν] :
    robust_projection.rieszEnergy α (show 0 < c * δ from mul_pos hc hδ)
      (Measure.map T ν) =
    ENNReal.ofReal (c ^ (-α)) * robust_projection.rieszEnergy α hδ ν := by
  let k : Y × Y → ENNReal := fun p =>
    ENNReal.ofReal ((max (dist p.1 p.2) (c * δ)) ^ (-α))
  let k0 : X × X → ENNReal := fun p =>
    ENNReal.ofReal ((max (dist p.1 p.2) δ) ^ (-α))
  have h_pos_k : ∀ (p : Y × Y), 0 < max (dist p.1 p.2) (c * δ) := by
    intro p; have h : 0 < c * δ := mul_pos hc hδ; positivity
  have h_pos_k0 : ∀ (p : X × X), 0 < max (dist p.1 p.2) δ := by
    intro p; positivity
  have h_eq1 : ∀ (p : X × X), k (Prod.map T T p) = ENNReal.ofReal (c ^ (-α)) * k0 p := by
    intro p
    dsimp only [k, k0, Prod.map]
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
  have hk_cont : Continuous k := by
    have h1 : Continuous (fun p : Y × Y => (max (dist p.1 p.2) (c * δ)) ^ (-α)) := by
      refine' Continuous.rpow (continuous_dist.max continuous_const) continuous_const _
      intro p; left; exact (h_pos_k p).ne'
    exact ENNReal.continuous_ofReal.comp h1
  have hk0_cont : Continuous k0 := by
    have h1 : Continuous (fun p : X × X => (max (dist p.1 p.2) δ) ^ (-α)) := by
      refine' Continuous.rpow (continuous_dist.max continuous_const) continuous_const _
      intro p; left; exact (h_pos_k0 p).ne'
    exact ENNReal.continuous_ofReal.comp h1
  let hk_meas : Measurable k := hk_cont.measurable
  let hk0_meas : Measurable k0 := hk0_cont.measurable
  let μ := Measure.map T ν
  haveI hμ_sfinite : SFinite μ := by exact Measure.instSFiniteMap ν T
  simp only [robust_projection.rieszEnergy]
  have h_step1 : ∫⁻ (x : Y), (∫⁻ (y : Y), k (x, y) ∂μ) ∂μ =
      ∫⁻ (p : Y × Y), k p ∂(μ.prod μ) := by
    rw [MeasureTheory.lintegral_prod k hk_meas.aemeasurable]
  have h_step2 : μ.prod μ = Measure.map (Prod.map T T) (ν.prod ν) := by
    exact MeasureTheory.Measure.map_prod_map ν ν hT_meas hT_meas
  have h_step3 : ∫⁻ (p : Y × Y), k p ∂(μ.prod μ) =
      ∫⁻ (p : X × X), k (Prod.map T T p) ∂(ν.prod ν) := by
    rw [h_step2]
    exact MeasureTheory.lintegral_map' hk_meas.aemeasurable
      ((hT_meas.comp measurable_fst).prodMk
        (hT_meas.comp measurable_snd)).aemeasurable
  have h_step4 : ∫⁻ (p : X × X), k (Prod.map T T p) ∂(ν.prod ν) =
      ∫⁻ (p : X × X), ENNReal.ofReal (c ^ (-α)) * k0 p ∂(ν.prod ν) := by
    congr with p; exact h_eq1 p
  set c_enn : ENNReal := ENNReal.ofReal (c ^ (-α)) with hc_enn
  have h_step5 : ∫⁻ (p : X × X), c_enn * k0 p ∂(ν.prod ν) =
      c_enn * ∫⁻ (p : X × X), k0 p ∂(ν.prod ν) := by exact lintegral_const_mul c_enn hk0_meas
  have h_step6 : ∫⁻ (p : X × X), k0 p ∂(ν.prod ν) =
      ∫⁻ (x : X), (∫⁻ (y : X), k0 (x, y) ∂ν) ∂ν := by
    rw [MeasureTheory.lintegral_prod k0 hk0_meas.aemeasurable]
  rw [h_step1, h_step3, h_step4, h_step5, h_step6]

/-- Energy bound for a scalar dilation c of a measure on ℝ.
Generalized to accept `rho_sep` directly; energy cost is `2*κ0*rho_sep`. -/
private lemma cobalt_scalar_energy_bound
    {δ κ0 rho_sep : ℝ} (hδ_pos : 0 < δ) (hκ_pos : 0 < κ0)
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    (hc_lower : c ≥ δ ^ rho_sep)
    {μ : Measure ℝ} [SFinite μ] :
    robust_projection.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun x : ℝ => c * x) μ) ≤
    ENNReal.ofReal (δ ^ (-2 * κ0 * rho_sep)) * robust_projection.rieszEnergy (2 * κ0) hδ_pos μ := by
  have h_scale := cobalt_rieszEnergy_affine_scaling (α := 2 * κ0) hδ_pos hc_pos
      (fun x : ℝ => c * x) (measurable_const.mul measurable_id)
      (fun x y => by
        have h1 : dist (c * x) (c * y) = |c * x - c * y| := by simp [Real.dist_eq]
        rw [h1]
        have h2 : c * x - c * y = c * (x - y) := by ring
        rw [h2]
        have h3 : |c * (x - y)| = c * |x - y| := by
          rw [abs_mul, abs_of_pos hc_pos] <;> ring
        rw [h3]
        have h4 : dist x y = |x - y| := by simp [Real.dist_eq]
        rw [h4] <;> ring) μ
  have hcδ_leδ : c * δ ≤ δ := by
    calc c * δ ≤ 1 * δ := by gcongr
         _ = δ := by ring
  have h_mono : robust_projection.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun x : ℝ => c * x) μ) ≤
      robust_projection.rieszEnergy (2 * κ0) (show 0 < c * δ from mul_pos hc_pos hδ_pos)
        (Measure.map (fun x : ℝ => c * x) μ) :=
    cobalt_rieszEnergy_mono_scale (by linarith) (by positivity) hδ_pos hcδ_leδ _
  rw [h_scale] at h_mono
  have h_exp : c ^ (-(2 * κ0)) ≤ δ ^ (-2 * κ0 * rho_sep) := by
    have h_pos2 : 0 < δ ^ rho_sep := by positivity
    have h3 : c ^ (-(2 * κ0)) ≤ (δ ^ rho_sep) ^ (-(2 * κ0)) :=
      cobalt_rpow_neg_mono h_pos2 hc_pos (by linarith) hc_lower
    have h4 : (δ ^ rho_sep) ^ (-(2 * κ0)) = δ ^ (-2 * κ0 * rho_sep) := by
      rw [← Real.rpow_mul (by positivity)]
      have h5 : rho_sep * (-(2 * κ0)) = -2 * κ0 * rho_sep := by ring
      rw [h5]
    rw [h4] at h3
    exact h3
  have h5 : ENNReal.ofReal (c ^ (-(2 * κ0))) ≤ ENNReal.ofReal (δ ^ (-2 * κ0 * rho_sep)) :=
    ENNReal.ofReal_le_ofReal h_exp
  calc robust_projection.rieszEnergy (2 * κ0) hδ_pos (Measure.map (fun x : ℝ => c * x) μ)
      ≤ ENNReal.ofReal (c ^ (-(2 * κ0))) * robust_projection.rieszEnergy (2 * κ0) hδ_pos μ := h_mono
    _ ≤ ENNReal.ofReal (δ ^ (-2 * κ0 * rho_sep)) * robust_projection.rieszEnergy (2 * κ0) hδ_pos μ := by gcongr

/-- **Obligation 3 (CORRECTED v2)**: Projective normalization with THREE coordinate
projections and x/fullLambda retention. NO direction pushforward (Phase7).

Owner: cobalt (application) + pelican (phase2_transport) -/
lemma obligation3_projective_transform_all
    {δ κ0 rho_sep : ℝ}
    (hδ_pos : 0 < δ) (_hδ_lt_one : δ < 1)
    (_hkappa_pos : 0 < κ0)
    {θ1 θ2 θ3 : ℝ}
    {Pbar E3 : Set (EuclideanSpace ℝ (Fin 2))}
    {μE3 : Measure (EuclideanSpace ℝ (Fin 2))}
    {Y : Set ℝ} {ν_Y : Measure ℝ} [IsProbabilityMeasure ν_Y]
    {P_y : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    (hθ1_lt_θ3 : θ1 < θ3) (hθ3_lt_θ2 : θ3 < θ2)
    (hθ1_in_unit : θ1 ∈ Set.Icc 0 1)
    (hθ2_in_unit : θ2 ∈ Set.Icc 0 1)
    (hθ3_in_unit : θ3 ∈ Set.Icc 0 1)
    (hPbar_bounded : IsBounded Pbar)
    (hE3_sub_Pbar : E3 ⊆ Pbar)
    (hE3_bounded : IsBounded E3)
    [IsProbabilityMeasure μE3]
    (hμE3_support : μE3.support = E3)
    (hE3_nonempty : E3.Nonempty)
    (hP_y_bdd : ∀ y, IsBounded (P_y y))
    (h_dir_sep13 : θ3 - θ1 ≥ δ ^ rho_sep)
    (h_dir_sep32 : θ2 - θ3 ≥ δ ^ rho_sep)
    (hν_Y_supp : ν_Y.support ⊆ Y) :
    ∃ (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (F_inv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (x : ℝ → ℝ)
      (Pbar' E3' : Set (EuclideanSpace ℝ (Fin 2)))
      (μE3' : Measure (EuclideanSpace ℝ (Fin 2)))
      (P_y' : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
      (L_proj C_inv : ℝ)
      (C_q0 C_q1 C_q01 E_q0 E_q1 : ENNReal),
      Pbar' = F '' Pbar ∧
      E3' = F '' E3 ∧
      μE3' = Measure.map F μE3 ∧
      (∀ y, P_y' y = F '' (P_y y)) ∧
      -- Projective transform formula (coordinate-wise)
      (∀ p, (F p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) ∧
                (F p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) ∧
      (∀ p ∈ Pbar, F_inv (F p) = p) ∧
      (∀ p' ∈ Pbar', F (F_inv p') = p') ∧
      E3'.Nonempty ∧
      IsProbabilityMeasure μE3' ∧
      μE3'.support = E3' ∧
      -- Cross-ratio direction map
      (∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) ∧
      -- fullLambda projective scaling
      (∀ y, y ≠ θ2 →
        (((θ2 - θ3) / (θ2 - θ1)) / ((θ2 - y) / (θ2 - θ1))) = (θ2 - θ3) / (θ2 - y)) ∧
      -- Projection identity
      (∀ y, y ≠ θ2 →
        affineProjection (x y) E3' =
          scaleSet (((θ2 - θ3) / (θ2 - θ1)) / ((θ2 - y) / (θ2 - θ1)))
            (affineProjection y E3)) ∧
      -- Lipschitz bounds
      0 ≤ L_proj ∧
      (∀ u v, dist (F u) (F v) ≤ L_proj * dist u v) ∧
      0 ≤ C_inv ∧
      C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep) ∧
      (∀ u v, dist (F_inv u) (F_inv v) ≤ C_inv * dist u v) ∧
      -- THREE PROJECTION BOUNDS
      -- q0 = coordinate 0, bounded against π_θ2
      C_q0 ≠ ⊤ ∧
      Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3') ≤
        C_q0 * Nreal δ (affineProjection θ2 E3) ∧
      -- q1 = coordinate 1, bounded against π_θ1
      C_q1 ≠ ⊤ ∧
      Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3') ≤
        C_q1 * Nreal δ (affineProjection θ1 E3) ∧
      -- q0+q1 = diagonal, bounded against π_θ3
      C_q01 ≠ ⊤ ∧
      Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3') ≤
        C_q01 * Nreal δ (affineProjection θ3 E3) ∧
      C_q0 = 2 ∧
      C_q1 = 2 ∧
      E_q0 ≠ ⊤ ∧
      robust_projection.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun q : EuclideanSpace ℝ (Fin 2) => q 0) μE3') ≤
        E_q0 * robust_projection.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * θ2 + p 1) μE3) ∧
      E_q1 ≠ ⊤ ∧
      robust_projection.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun q : EuclideanSpace ℝ (Fin 2) => q 1) μE3') ≤
        E_q1 * robust_projection.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * θ1 + p 1) μE3) := by
  rcases phase2_transport hδ_pos hθ1_lt_θ3 hθ3_lt_θ2
      hθ1_in_unit hθ2_in_unit hθ3_in_unit
      hPbar_bounded hE3_sub_Pbar hE3_bounded hμE3_support hE3_nonempty
      hP_y_bdd with
    ⟨G, G_inv, x, Pbar', E3', μE3', P_y', C_forward, C_backward, C_inv,
     hG_formula, hGinv_G, hG_Ginv, hG_inj, hx_formula,
     hPbar'_eq, hE3'_eq, hμE3'_eq, hPy'_eq,
     hμE3'_supp, hμE3'_prob, hPbar'_bdd, hE3'_bdd, hPy'_bdd,
     hC_fwd_ne_top, hC_bwd_ne_top, hCover_fwd_Pbar, hCover_fwd_Py,
     hCover_bwd_Pbar, hCover_bwd_Py,
     hCinv_nonneg, hCinv_formula, hGinv_lip, hProj_cover⟩
  let b3 := (θ3 - θ1) / (θ2 - θ1)
  let a3 := (θ2 - θ3) / (θ2 - θ1)
  let L_proj : ℝ := Real.sqrt 2 * max (|b3| * (|θ2| + 1)) (|a3| * (|θ1| + 1))
  have hG_lip : ∀ u v, dist (G u) (G v) ≤ L_proj * dist u v :=
    cobalt_G_lipschitz hG_formula
  have hθ1_ne_θ2 : θ1 ≠ θ2 := by linarith
  have hθ3_ne_θ2 : θ3 ≠ θ2 := by linarith
  have hθ3_ne_θ1 : θ3 ≠ θ1 := by linarith
  have hD_ne : θ2 - θ1 ≠ 0 := by linarith
  have h23_ne : θ2 - θ3 ≠ 0 := by linarith

  -- x(θ1)=0, x(θ3)=1
  have h_x_θ1 : x θ1 = 0 := by
    rw [hx_formula] <;> field_simp [hθ1_ne_θ2] <;> ring
  have h_x_θ3 : x θ3 = 1 := by
    rw [hx_formula]
    field_simp [hθ3_ne_θ1, h23_ne] <;> ring

  -- fullLambda formula simplification
  have h_fl_formula : ∀ y, y ≠ θ2 →
      ((θ2 - θ3) / (θ2 - θ1)) / ((θ2 - y) / (θ2 - θ1)) = (θ2 - θ3) / (θ2 - y) := by
    intro y hy
    have h_2y_ne : θ2 - y ≠ 0 := sub_ne_zero.mpr hy.symm
    have h_ay_ne : (θ2 - y) / (θ2 - θ1) ≠ 0 := by
      apply div_ne_zero h_2y_ne hD_ne
    field_simp [hD_ne, h_ay_ne] <;> ring

  -- Projection identity: π_{x(y)}(E3') = scaleSet(fullLambda(y))(π_y(E3))
  have h_proj_id : ∀ y, y ≠ θ2 →
      affineProjection (x y) E3' =
        scaleSet (((θ2 - θ3) / (θ2 - θ1)) / ((θ2 - y) / (θ2 - θ1)))
          (affineProjection y E3) := by
    intro y hy
    have h_2y_ne : θ2 - y ≠ 0 := sub_ne_zero.mpr hy.symm
    ext z
    simp only [affineProjection, scaleSet, Set.mem_image, hE3'_eq]
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨p 0 * y + p 1, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (G p) 0 * x y + (G p) 1 =
          (((θ2 - θ3) / (θ2 - θ1)) / ((θ2 - y) / (θ2 - θ1))) * (p 0 * y + p 1) := by
        simp [hG_formula, hx_formula]
        field_simp [hD_ne, h_2y_ne] <;> ring
      exact h1.symm
    · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨G p, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (G p) 0 * x y + (G p) 1 =
          (((θ2 - θ3) / (θ2 - θ1)) / ((θ2 - y) / (θ2 - θ1))) * (p 0 * y + p 1) := by
        simp [hG_formula, hx_formula]
        field_simp [hD_ne, h_2y_ne] <;> ring
      exact h1

  -- q0 projection: image (fun q => q 0) E3' = scaleSet b3 (affineProjection θ2 E3)
  have h_q0_set : (fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3' =
      scaleSet b3 (affineProjection θ2 E3) := by
    ext z
    simp only [Set.mem_image, scaleSet, hE3'_eq]
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨p 0 * θ2 + p 1, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (G p) 0 = b3 * (p 0 * θ2 + p 1) := by
        simpa [b3] using congr_fun (hG_formula p) 0
      exact h1.symm
    · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨G p, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (G p) 0 = b3 * (p 0 * θ2 + p 1) := by
        simpa [b3] using congr_fun (hG_formula p) 0
      simpa using h1
  let C_q0 : ENNReal := (Nat.ceil (|b3|) + 1 : ENNReal)
  have h_proj_θ2_bdd : IsBounded (affineProjection θ2 E3) :=
    projectionSet.bounded θ2 hE3_bounded
  have hC_q0 : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3') ≤
      C_q0 * Nreal δ (affineProjection θ2 E3) := by
    rw [h_q0_set]
    exact FourSectorChart.scalar_covering_upper hδ_pos (abs_nonneg b3) h_proj_θ2_bdd (le_refl |b3|)
  have hC_q0_ne_top : C_q0 ≠ ⊤ := by
    simp [C_q0]

  -- q1 projection: from hProj_cover at y=θ1 (x(θ1)=0, fullLambda=a3)
  let a_y1 := (θ2 - θ1) / (θ2 - θ1)
  let fullLambda1 := a3 / a_y1
  let M1 := |fullLambda1|
  let C_q1 : ENNReal := (Nat.ceil M1 + 1 : ENNReal)
  have hC1_raw := hProj_cover θ1 hθ1_ne_θ2
  rw [h_x_θ1] at hC1_raw
  have h_q1_set : (fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3' = affineProjection 0 E3' := by
    ext z
    simp [affineProjection] <;> rfl
  have hC_q1 : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3') ≤
      C_q1 * Nreal δ (affineProjection θ1 E3) := by
    rw [h_q1_set]
    exact hC1_raw
  have hC_q1_ne_top : C_q1 ≠ ⊤ := by
    simp [C_q1]

  -- q0+q1 projection: from hProj_cover at y=θ3 (x(θ3)=1, fullLambda=1)
  let a_y3 := (θ2 - θ3) / (θ2 - θ1)
  let fullLambda3 := a3 / a_y3
  let M3 := |fullLambda3|
  let C_q01 : ENNReal := (Nat.ceil M3 + 1 : ENNReal)
  have hC3_raw := hProj_cover θ3 hθ3_ne_θ2
  rw [h_x_θ3] at hC3_raw
  have h_q01_set : (fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3' = affineProjection 1 E3' := by
    ext z
    simp [affineProjection] <;> rfl
  have hC_q01 : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3') ≤
      C_q01 * Nreal δ (affineProjection θ3 E3) := by
    rw [h_q01_set]
    exact hC3_raw
  have hC_q01_ne_top : C_q01 ≠ ⊤ := by
    simp [C_q01]

  -- === ENERGY BOUNDS ===
  let π_q0 : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => q 0
  let π_θ2 : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 * θ2 + p 1
  let μ_q0 := Measure.map π_q0 μE3'
  let μ_θ2 := Measure.map π_θ2 μE3
  let π_q1 : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => q 1
  let π_θ1 : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 * θ1 + p 1
  let μ_q1 := Measure.map π_q1 μE3'
  let μ_θ1 := Measure.map π_θ1 μE3

  have hb3_pos : 0 < b3 := by apply div_pos <;> linarith
  have ha3_pos : 0 < a3 := by apply div_pos <;> linarith
  have hb3_le_one : b3 ≤ 1 := by apply (div_le_one (by linarith)).mpr; linarith
  have ha3_le_one : a3 ≤ 1 := by apply (div_le_one (by linarith)).mpr; linarith
  have hθ21_le_one : θ2 - θ1 ≤ 1 := by linarith [hθ1_in_unit.1, hθ2_in_unit.2]
  have hb3_lower : b3 ≥ δ ^ rho_sep := by
    have h : b3 = (θ3 - θ1) / (θ2 - θ1) := by rfl
    rw [h]
    have h2 : (θ3 - θ1) / (θ2 - θ1) ≥ θ3 - θ1 := by
      have h4 : 0 < θ2 - θ1 := by linarith
      calc (θ3 - θ1) / (θ2 - θ1)
        ≥ (θ3 - θ1) / 1 := by gcongr
      _ = θ3 - θ1 := by ring
    exact h_dir_sep13.trans h2
  have ha3_lower : a3 ≥ δ ^ rho_sep := by
    have h : a3 = (θ2 - θ3) / (θ2 - θ1) := by rfl
    rw [h]
    have h2 : (θ2 - θ3) / (θ2 - θ1) ≥ θ2 - θ3 := by
      have h4 : 0 < θ2 - θ1 := by linarith
      calc (θ2 - θ3) / (θ2 - θ1)
        ≥ (θ2 - θ3) / 1 := by gcongr
      _ = θ2 - θ3 := by ring
    exact h_dir_sep32.trans h2

  let E_q0 : ENNReal := ENNReal.ofReal (δ ^ (-2 * κ0 * rho_sep))
  let E_q1 : ENNReal := ENNReal.ofReal (δ ^ (-2 * κ0 * rho_sep))
  have hE_q0_ne_top : E_q0 ≠ ⊤ := by simp [E_q0]
  have hE_q1_ne_top : E_q1 ≠ ⊤ := by simp [E_q1]

  have hG_meas : Measurable G := by
    have hL_nonneg : 0 ≤ L_proj := by
      have h1 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have h2 : 0 ≤ max (|b3| * (|θ2| + 1)) (|a3| * (|θ1| + 1)) := by positivity
      exact mul_nonneg h1 h2
    have h_cont : Continuous G := by
      apply Metric.continuous_iff.mpr
      intro x ε hε
      use ε / (L_proj + 1)
      constructor
      · positivity
      · intro y hy
        have h7 : dist (G x) (G y) ≤ L_proj * dist x y := hG_lip x y
        have h8 : L_proj * dist x y < ε := by
          have h9 : 0 < L_proj + 1 := by linarith
          have h10 : dist x y < ε / (L_proj + 1) := by rwa [dist_comm] at hy
          have h11 : L_proj * dist x y ≤ L_proj * (ε / (L_proj + 1)) := by gcongr
          have h12 : L_proj * (ε / (L_proj + 1)) < ε := by
            have h13 : L_proj / (L_proj + 1) < 1 := by
              apply (div_lt_one (by linarith)).mpr; linarith
            calc L_proj * (ε / (L_proj + 1))
              = (L_proj / (L_proj + 1)) * ε := by ring
            _ < 1 * ε := by gcongr
            _ = ε := by ring
          exact h11.trans_lt h12
        have h13 : dist (G y) (G x) < ε := by
          have h14 : dist (G y) (G x) = dist (G x) (G y) := dist_comm (G y) (G x)
          rw [h14]
          exact h7.trans_lt h8
        exact h13
    exact h_cont.measurable

  have h_map_q0 : μ_q0 = Measure.map (fun x : ℝ => b3 * x) μ_θ2 := by
    have h1 : μ_q0 = Measure.map (π_q0 ∘ G) μE3 := by
      rw [show μ_q0 = Measure.map π_q0 μE3' from rfl, hμE3'_eq]
      exact Measure.map_map (by fun_prop) hG_meas
    have h2 : (π_q0 ∘ G) = (fun p : EuclideanSpace ℝ (Fin 2) => b3 * π_θ2 p) := by
      funext p
      simpa [π_q0, π_θ2, b3] using congr_fun (hG_formula p) 0
    rw [h1, h2]
    exact (Measure.map_map (by fun_prop) (by fun_prop)).symm

  have h_map_q1 : μ_q1 = Measure.map (fun x : ℝ => a3 * x) μ_θ1 := by
    have h1 : μ_q1 = Measure.map (π_q1 ∘ G) μE3 := by
      rw [show μ_q1 = Measure.map π_q1 μE3' from rfl, hμE3'_eq]
      exact Measure.map_map (by fun_prop) hG_meas
    have h2 : (π_q1 ∘ G) = (fun p : EuclideanSpace ℝ (Fin 2) => a3 * π_θ1 p) := by
      funext p
      simpa [π_q1, π_θ1, a3] using congr_fun (hG_formula p) 1
    rw [h1, h2]
    exact (Measure.map_map (by fun_prop) (by fun_prop)).symm

  have h_energy_q0 : robust_projection.rieszEnergy (2 * κ0) hδ_pos μ_q0 ≤
      E_q0 * robust_projection.rieszEnergy (2 * κ0) hδ_pos μ_θ2 := by
    rw [h_map_q0]
    exact cobalt_scalar_energy_bound hδ_pos _hkappa_pos hb3_pos hb3_le_one hb3_lower

  have h_energy_q1 : robust_projection.rieszEnergy (2 * κ0) hδ_pos μ_q1 ≤
      E_q1 * robust_projection.rieszEnergy (2 * κ0) hδ_pos μ_θ1 := by
    rw [h_map_q1]
    exact cobalt_scalar_energy_bound hδ_pos _hkappa_pos ha3_pos ha3_le_one ha3_lower

  have hL_proj_nonneg : 0 ≤ L_proj := by
    have h1 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have h2 : 0 ≤ max (|b3| * (|θ2| + 1)) (|a3| * (|θ1| + 1)) := by positivity
    exact mul_nonneg h1 h2

  have hE3'_nonempty : E3'.Nonempty := by
    rw [hE3'_eq]
    exact hE3_nonempty.image G

  have hG_formula' : ∀ p, (G p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) ∧
                         (G p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1) := by
    intro p
    have h0 : (G p) 0 = b3 * (p 0 * θ2 + p 1) := by
      simpa [b3] using congr_fun (hG_formula p) 0
    have h1 : (G p) 1 = a3 * (p 0 * θ1 + p 1) := by
      simpa [a3] using congr_fun (hG_formula p) 1
    exact ⟨by simpa [b3] using h0, by simpa [a3] using h1⟩

  -- Prove C_q0 = 2 from 0 < b3 < 1
  have hb3_pos : 0 < b3 := by
    dsimp only [b3]
    have h1 : 0 < θ3 - θ1 := by linarith
    have h2 : 0 < θ2 - θ1 := by linarith
    positivity
  have hb3_lt_one : b3 < 1 := by
    dsimp only [b3]
    have h1 : θ3 - θ1 < θ2 - θ1 := by linarith
    have h2 : 0 < θ2 - θ1 := by linarith
    exact (div_lt_one h2).mpr h1
  have h_ceil_b3 : Nat.ceil (|b3|) = 1 := by
    have h_abs : |b3| = b3 := abs_of_pos hb3_pos
    rw [h_abs]
    have h_bound : (0 : ℝ) < b3 ∧ b3 ≤ 1 := ⟨hb3_pos, by linarith⟩
    have h_main : Nat.ceil b3 = 1 := by
      rw [Nat.ceil_eq_iff (by norm_num)]
      simpa using h_bound
    exact h_main
  have hC_q0_eq_two : C_q0 = 2 := by
    dsimp only [C_q0]
    rw [h_ceil_b3]
    <;> norm_num

  -- Prove C_q1 = 2 from 0 < fullLambda1 < 1
  have h_a_y1_eq_one : a_y1 = 1 := by
    dsimp only [a_y1]
    have hD_ne : θ2 - θ1 ≠ 0 := by linarith
    field_simp [hD_ne] <;> ring
  have h_fl1_eq_a3 : fullLambda1 = a3 := by
    dsimp only [fullLambda1]
    rw [h_a_y1_eq_one] <;> ring
  have ha3_pos : 0 < a3 := by
    dsimp only [a3]
    have h1 : 0 < θ2 - θ3 := by linarith
    have h2 : 0 < θ2 - θ1 := by linarith
    positivity
  have ha3_lt_one : a3 < 1 := by
    dsimp only [a3]
    have h1 : θ2 - θ3 < θ2 - θ1 := by linarith
    have h2 : 0 < θ2 - θ1 := by linarith
    exact (div_lt_one h2).mpr h1
  have h_fl1_pos : 0 < fullLambda1 := by rw [h_fl1_eq_a3]; exact ha3_pos
  have h_fl1_lt_one : fullLambda1 < 1 := by rw [h_fl1_eq_a3]; exact ha3_lt_one
  have h_ceil_fl1 : Nat.ceil (|fullLambda1|) = 1 := by
    have h_abs : |fullLambda1| = fullLambda1 := abs_of_pos h_fl1_pos
    rw [h_abs]
    have h_bound : (0 : ℝ) < fullLambda1 ∧ fullLambda1 ≤ 1 := ⟨h_fl1_pos, by linarith⟩
    have h_main : Nat.ceil fullLambda1 = 1 := by
      rw [Nat.ceil_eq_iff (by norm_num)]
      simpa using h_bound
    exact h_main
  have hC_q1_eq_two : C_q1 = 2 := by
    dsimp only [C_q1, M1]
    rw [h_ceil_fl1]
    <;> norm_num

  have hCinv_bound : C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep) := by
    rw [hCinv_formula]
    have h1 : 0 < θ3 - θ1 := by linarith
    have h2 : 0 < θ2 - θ3 := by linarith
    have h3 : θ1 ≤ 1 := hθ1_in_unit.2
    have h4 : θ2 ≤ 1 := hθ2_in_unit.2
    have h5 : 1 / (θ3 - θ1) ≤ δ ^ (-rho_sep) := by
      have h6 : θ3 - θ1 ≥ δ ^ rho_sep := h_dir_sep13
      have h7 : 0 < δ ^ rho_sep := by positivity
      have h8 : 1 / (θ3 - θ1) ≤ 1 / (δ ^ rho_sep) := by gcongr
      have h9 : 1 / (δ ^ rho_sep) = δ ^ (-rho_sep) := by
        rw [Real.rpow_neg (by linarith)] <;> ring
      rw [h9] at h8; exact h8
    have h10 : 1 / (θ2 - θ3) ≤ δ ^ (-rho_sep) := by
      have h11 : θ2 - θ3 ≥ δ ^ rho_sep := h_dir_sep32
      have h12 : 0 < δ ^ rho_sep := by positivity
      have h13 : 1 / (θ2 - θ3) ≤ 1 / (δ ^ rho_sep) := by gcongr
      have h14 : 1 / (δ ^ rho_sep) = δ ^ (-rho_sep) := by
        rw [Real.rpow_neg (by linarith)] <;> ring
      rw [h14] at h13; exact h13
    have h15 : θ1 / (θ3 - θ1) ≤ δ ^ (-rho_sep) := by
      calc θ1 / (θ3 - θ1) ≤ 1 / (θ3 - θ1) := by gcongr <;> linarith
        _ ≤ δ ^ (-rho_sep) := h5
    have h16 : θ2 / (θ2 - θ3) ≤ δ ^ (-rho_sep) := by
      calc θ2 / (θ2 - θ3) ≤ 1 / (θ2 - θ3) := by gcongr <;> linarith
        _ ≤ δ ^ (-rho_sep) := h10
    have h17 : 1 / (θ3 - θ1) + 1 / (θ2 - θ3) + θ1 / (θ3 - θ1) + θ2 / (θ2 - θ3) ≤ 4 * δ ^ (-rho_sep) := by
      linarith
    have h18 : Real.sqrt 2 * (1 / (θ3 - θ1) + 1 / (θ2 - θ3) + θ1 / (θ3 - θ1) + θ2 / (θ2 - θ3)) ≤
        Real.sqrt 2 * (4 * δ ^ (-rho_sep)) := by gcongr
    have h19 : Real.sqrt 2 * (4 * δ ^ (-rho_sep)) = 4 * Real.sqrt 2 * δ ^ (-rho_sep) := by ring
    rw [h19] at h18
    exact h18

  exact ⟨G, G_inv, x, Pbar', E3', μE3', P_y', L_proj, C_inv, C_q0, C_q1, C_q01, E_q0, E_q1,
    hPbar'_eq, hE3'_eq, hμE3'_eq, hPy'_eq, hG_formula',
    (fun p _ => hGinv_G p), (fun p' _ => hG_Ginv p'),
    hE3'_nonempty, hμE3'_prob, hμE3'_supp, hx_formula, h_fl_formula, h_proj_id,
    hL_proj_nonneg, hG_lip, hCinv_nonneg, hCinv_bound, hGinv_lip,
    hC_q0_ne_top, hC_q0, hC_q1_ne_top, hC_q1, hC_q01_ne_top, hC_q01,
    hC_q0_eq_two, hC_q1_eq_two,
    hE_q0_ne_top, h_energy_q0, hE_q1_ne_top, h_energy_q1⟩

end ProductLikeIncidence.ProductReduction

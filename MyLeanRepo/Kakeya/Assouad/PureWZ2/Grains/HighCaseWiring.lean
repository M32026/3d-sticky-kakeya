import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SlabExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaToHighData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
import Mathlib.Tactic

/-!
# High-case local AD wiring helpers

Provides the missing pieces for the HIGH case local AD in the target theorem:

1. `cover_condition_from_nonempty`: cover condition follows from P nonempty
   (pick any p0 ∈ propertyThree near q; distance ≤ 5τ < 40L).

2. `sqrt_rho_le_4tau`: containment condition from rho ≤ 48L².

3. `cordoba_high_to_ad`: full wiring Córdoba slab bound → HighData → slab_to_ad →
   PureWZ2PaperADSet1, with mono down to the target set.

4. `trivial_ad_for_large_rho`: for rho ≥ 10 * δ^outputLoss, the trivial bound
   `10/rho ≤ δ^(-outputLoss)` gives AD directly.

## Cover condition proof

For any x ∈ S = coarseShading.union ∩ ball(q, 4τ) and any
p0 ∈ propertyThree.union ∩ ball(q, τ):
  |inner x n - inner p0 n| ≤ ‖x - p0‖ ≤ ‖x - q‖ + ‖q - p0‖ ≤ 4τ + τ = 5τ
Since τ = L√3, 5τ = 5√3 L ≈ 8.66L < 40L = W0.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Cover condition: if P = scalarProjection n (propertyThree.union ∩ ball(q, τ))
is nonempty, then every t in scalarProjection n S is within W0 = 40L of some t' ∈ P.

Uses the triangle inequality: for any x ∈ S and p0 ∈ propertyThree.union ∩ ball(q, τ),
|inner x n - inner p0 n| ≤ ‖x - p0‖ ≤ 4τ + τ = 5τ < 40L. -/
lemma cover_condition_from_nonempty
    {L : ℝ} (hL_pos : 0 < L)
    {tau : ℝ} (htau_eq : tau = L * Real.sqrt 3)
    {n : Point3} (hn_unit : ‖n‖ = 1)
    {q : Point3}
    {S : Set Point3}
    (hS_sub : S ⊆ Metric.closedBall q (4 * tau))
    {propertyThree_union : Set Point3}
    {P : Set ℝ}
    (hP_def : P = scalarProjection n (propertyThree_union ∩ Metric.closedBall q tau))
    (hP_nonempty : (propertyThree_union ∩ Metric.closedBall q tau).Nonempty) :
    ∀ (t : ℝ), t ∈ scalarProjection n S → ∃ (t' : ℝ), t' ∈ P ∧ |t - t'| ≤ 40 * L := by
  rcases hP_nonempty with ⟨p0, hp0_prop, hp0_ball⟩
  let t' : ℝ := inner ℝ p0 n
  have ht'_in_P : t' ∈ P := by
    rw [hP_def]
    exact ⟨p0, ⟨hp0_prop, hp0_ball⟩, rfl⟩
  intro t ht
  rcases ht with ⟨x, hxS, rfl⟩
  have hx_ball : dist x q ≤ 4 * tau := hS_sub hxS
  have h1 : ‖x - q‖ ≤ 4 * tau := by simpa [dist_eq_norm] using hx_ball
  have h2 : ‖p0 - q‖ ≤ tau := by simpa [dist_eq_norm] using hp0_ball
  have h3 : ‖x - p0‖ ≤ 5 * tau := by
    calc ‖x - p0‖
      = ‖(x - q) - (p0 - q)‖ := by abel
    _ ≤ ‖x - q‖ + ‖p0 - q‖ := norm_sub_le _ _
    _ ≤ 4 * tau + tau := by linarith
    _ = 5 * tau := by ring
  have h4 : |inner ℝ x n - inner ℝ p0 n| ≤ ‖x - p0‖ := by
    have h5 : inner ℝ x n - inner ℝ p0 n = inner ℝ (x - p0) n := by
      simp [inner_sub_left]
    rw [h5]
    have h6 : |inner ℝ (x - p0) n| ≤ ‖x - p0‖ * ‖n‖ := abs_real_inner_le_norm _ _
    rw [hn_unit] at h6
    simpa using h6
  have h6 : |inner ℝ x n - t'| ≤ 5 * tau := by
    calc |inner ℝ x n - t'|
      ≤ ‖x - p0‖ := h4
    _ ≤ 5 * tau := h3
  have h7 : 5 * tau ≤ 40 * L := by
    rw [htau_eq]
    have h8 : 5 * Real.sqrt 3 ≤ 40 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    nlinarith
  exact ⟨t', ht'_in_P, by linarith⟩

/-- Containment: if rho ≤ 48 * L², then √rho ≤ 4τ where τ = L√3. -/
lemma sqrt_rho_le_4tau
    {L rho tau : ℝ} (hL_pos : 0 < L) (hrho_nonneg : 0 ≤ rho)
    (htau_eq : tau = L * Real.sqrt 3)
    (hrho_bound : rho ≤ 48 * L^2) :
    Real.sqrt rho ≤ 4 * tau := by
  have h1 : Real.sqrt rho ≤ Real.sqrt (48 * L^2) := Real.sqrt_le_sqrt hrho_bound
  have h2 : Real.sqrt (48 * L^2) = 4 * (L * Real.sqrt 3) := by
    have h3 : 0 ≤ L := by linarith
    have h4 : Real.sqrt (48 * L^2) = Real.sqrt 48 * L := by
      calc Real.sqrt (48 * L^2)
        = Real.sqrt (48) * Real.sqrt (L^2) := by rw [Real.sqrt_mul] <;> positivity
      _ = Real.sqrt 48 * L := by
        have h5 : Real.sqrt (L^2) = L := by
          rw [Real.sqrt_sq] <;> linarith
        rw [h5] <;> ring
    rw [h4]
    have h6 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
      have h7 : Real.sqrt 48 = Real.sqrt (16 * 3) := by norm_num
      rw [h7]
      have h8 : Real.sqrt (16 * 3) = Real.sqrt 16 * Real.sqrt 3 := by
        rw [Real.sqrt_mul] <;> positivity
      rw [h8]
      have h9 : Real.sqrt 16 = 4 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h9] <;> ring
    rw [h6] <;> ring
  rw [h2] at h1
  rw [htau_eq]
  exact h1

/-- Full wiring: Córdoba slab bound + cover + containment + arithmetic → AD.

Takes the Córdoba slab bound on P, produces HighData via cordoba_to_high_data,
applies slab_to_ad, and monos down to the target set
`shading.union ∩ ball(q, √rho)`. -/
lemma cordoba_high_to_ad
    {delta' rho L : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading coarseShading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (C : ENNReal)
    (q : Point3)
    (hq : q ∈ shading.union)
    (v : Point3)
    (hv_unit : ‖v‖ = 1)
    (tau : ℝ)
    (htau_pos : 0 < tau)
    (W0 : ℝ)
    (hW0_pos : 0 < W0)
    (V_min : ℝ)
    (hVmin_pos : 0 < V_min)
    (V_total : ℝ)
    (hV_total_pos : 0 < V_total)
    (S : Set Point3)
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (P : Set ℝ)
    (h_slab_P : ∀ t ∈ P,
        volume (S ∩ {x | |inner ℝ x v - t| ≤ W0}) ≥ ENNReal.ofReal V_min)
    (h_cover : ∀ t ∈ scalarProjection v S, ∃ t' ∈ P, |t - t'| ≤ W0)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (h_arithmetic :
        ENNReal.ofReal ((V_total / V_min) * (2 * (2 * W0) / rho + 2)) ≤ C)
    (h_dir : v = planeMap ⟨q, hq⟩)
    (h_contain : shading.union ∩ Metric.closedBall q (Real.sqrt rho) ⊆ S)
    (hrho_pos : 0 < rho)
    (sigma : ℝ)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤) :
    PureWZ2PaperADSet1
      (scalarProjection v (shading.union ∩ Metric.closedBall q (Real.sqrt rho)))
      rho (1 - sigma) C := by
  let W : ℝ := 2 * W0
  have hW_pos : 0 < W := by positivity
  have h_slab_full : ∀ t ∈ scalarProjection v S,
      volume (S ∩ {x | |inner ℝ x v - t| ≤ W}) ≥ ENNReal.ofReal V_min :=
    PureWZ2.extend_slab_bounds hS_meas hW0_pos hVmin_pos h_slab_P h_cover
  have h_ad_S : PureWZ2PaperADSet1 (scalarProjection v S) rho (1 - sigma) C :=
    slab_to_ad hv_unit hS_meas W V_min V_total hW_pos hVmin_pos hV_total_pos
      hV_total h_slab_full hrho_pos hsigma_pos hsigma_lt_one hC_one hC_top h_arithmetic
  have h_target_sub :
      scalarProjection v (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ⊆
      scalarProjection v S := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, h_contain hx, rfl⟩
  exact PureWZ2PaperADSet1.mono_set h_ad_S h_target_sub

/-- Trivial AD for large rho: if rho ≥ 10 * delta'^outputLoss, then
`10/rho ≤ delta'^(-outputLoss)`, so the trivial bound gives AD with constant C. -/
lemma trivial_ad_for_large_rho
    {delta' rho outputLoss sigma : ℝ}
    {E : Set ℝ}
    (hdelta'_pos : 0 < delta')
    (hdelta'_le_one : delta' ≤ 1)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hE_bdd : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hrho_large : rho ≥ 100 * Real.rpow delta' outputLoss)
    (C : ENNReal)
    (hC_eq : C = Kakeya.realRpowENN delta' (-outputLoss))
    (h_bridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2PaperADSet1 E rho (1 - sigma) C := by
  have h2_pos : 0 < Real.rpow delta' outputLoss := Real.rpow_pos_of_pos hdelta'_pos outputLoss
  have h1 : (10 : ℝ) / rho ≤ Real.rpow delta' (-outputLoss) / 10 := by
    have h31 : 0 < (100 * Real.rpow delta' outputLoss) := by positivity
    have h3 : (10 : ℝ) / rho ≤ (10 : ℝ) / (100 * Real.rpow delta' outputLoss) := by
      gcongr
      <;> linarith
    have h4 : (10 : ℝ) / (100 * Real.rpow delta' outputLoss) =
        Real.rpow delta' (-outputLoss) / 10 := by
      have h5 : Real.rpow delta' (-outputLoss) = (Real.rpow delta' outputLoss)⁻¹ :=
        Real.rpow_neg hdelta'_pos.le outputLoss
      rw [h5]
      field_simp [h2_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3
  have h_trivial : IsADSet1 E rho (1 - sigma) (ENNReal.ofReal ((10 : ℝ) / rho)) :=
    IsADSet1.trivial_bound (α := (1 - sigma)) hE_bdd (by linarith) hrho_le_one
      (by linarith) (by linarith)
  have h_rpow_nonneg : 0 ≤ Real.rpow delta' (-outputLoss) := Real.rpow_nonneg hdelta'_pos.le _
  let C' : ENNReal := ENNReal.ofReal (Real.rpow delta' (-outputLoss) / 10)
  have h6 : ENNReal.ofReal ((10 : ℝ) / rho) ≤ C' :=
    ENNReal.ofReal_le_ofReal h1
  have h_trivial' : IsADSet1 E rho (1 - sigma) C' := h_trivial.mono_constant h6
  have hC'_ne_top : C' ≠ ⊤ := by
    simp [C'] <;> exact ENNReal.ofReal_ne_top
  have h_bridge2 : ∀ (set : Set ℝ) (δ α : ℝ) (C'' : ENNReal),
      0 < δ → δ ≤ 1 → C'' ≠ ⊤ → IsADSet1 set δ α C'' → PureWZ2PaperADSet1 set δ α (10 * C'') :=
    h_bridge.2
  have h_final : PureWZ2PaperADSet1 E rho (1 - sigma) (10 * C') :=
    h_bridge2 E rho (1 - sigma) C' hrho_pos hrho_le_one hC'_ne_top h_trivial'
  have h10C' : 10 * C' = C := by
    have h_pos : 0 ≤ Real.rpow delta' (-outputLoss) := h_rpow_nonneg
    have h_eq1 : (10 : ENNReal) * C' = ENNReal.ofReal ((10 : ℝ) * (Real.rpow delta' (-outputLoss) / 10)) := by
      simp only [C']
      have h_cast : (10 : ENNReal) = ENNReal.ofReal (10 : ℝ) := by norm_cast
      rw [h_cast]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      <;> rfl
    rw [h_eq1]
    have h_eq2 : (10 : ℝ) * (Real.rpow delta' (-outputLoss) / 10) = Real.rpow delta' (-outputLoss) := by ring
    rw [h_eq2]
    exact hC_eq.symm
  rw [h10C'] at h_final
  exact h_final

/-- Given slab bounds on `S = coarseShading.union ∩ ball(q, 4τ)`, produce AD
for the projection of any target set contained in `coarseShading.union ∩ ball(q, √rho)`.

Thin wrapper around `cordoba_high_to_ad` that handles the family mismatch by using
`coarseShading` for both shading parameters and then mono-ing down to the target. -/
lemma cordoba_slab_to_ad_for_subset
    {L rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (C : ENNReal)
    (q : Point3)
    (hq_coarse : q ∈ coarseShading.union)
    (v : Point3)
    (hv_unit : ‖v‖ = 1)
    (tau W0 : ℝ)
    (htau_pos : 0 < tau)
    (hW0_pos : 0 < W0)
    (V_min V_total : ℝ)
    (hVmin_pos : 0 < V_min)
    (hV_total_pos : 0 < V_total)
    (S : Set Point3)
    (hS_eq : S = coarseShading.union ∩ Metric.closedBall q (4 * tau))
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (P : Set ℝ)
    (h_slab_P : ∀ t ∈ P,
        volume (S ∩ {x | |inner ℝ x v - t| ≤ W0}) ≥ ENNReal.ofReal V_min)
    (h_cover : ∀ t ∈ scalarProjection v S, ∃ t' ∈ P, |t - t'| ≤ W0)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (h_arithmetic : ENNReal.ofReal ((V_total / V_min) * (2 * (2 * W0) / rho + 2)) ≤ C)
    (target : Set Point3)
    (h_target_sub : target ⊆ coarseShading.union ∩ Metric.closedBall q (Real.sqrt rho))
    (hsqrt_rho_le_4tau : Real.sqrt rho ≤ 4 * tau)
    (hrho_pos : 0 < rho)
    (sigma : ℝ)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤) :
    PureWZ2PaperADSet1 (scalarProjection v target) rho (1 - sigma) C := by
  let planeMap' : {point : Point3 // point ∈ coarseShading.union} → Point3 := fun _ => v
  have hplaneMap'_unit : ∀ p, ‖planeMap' p‖ = 1 := by intro _; exact hv_unit
  have h_dir : v = planeMap' ⟨q, hq_coarse⟩ := by simp [planeMap']
  have h_contain : coarseShading.union ∩ Metric.closedBall q (Real.sqrt rho) ⊆ S := by
    rw [hS_eq]
    intro x hx
    have h1 : x ∈ coarseShading.union := hx.1
    have h2 : dist x q ≤ Real.sqrt rho := hx.2
    have h3 : dist x q ≤ 4 * tau := by linarith [hsqrt_rho_le_4tau]
    exact ⟨h1, h3⟩
  have h_ad_S : PureWZ2PaperADSet1
      (scalarProjection v (coarseShading.union ∩ Metric.closedBall q (Real.sqrt rho)))
      rho (1 - sigma) C :=
    cordoba_high_to_ad (delta' := L) (rho := rho) (L := L)
      (family := coarse) (shading := coarseShading) (coarseShading := coarseShading)
      planeMap' C q hq_coarse v hv_unit tau htau_pos W0 hW0_pos V_min hVmin_pos V_total hV_total_pos
      S hS_meas hS_sub_ball P h_slab_P h_cover hV_total h_arithmetic h_dir h_contain
      hrho_pos sigma hsigma_pos hsigma_lt_one hC_one hC_top
  have h_proj_sub : scalarProjection v target ⊆
      scalarProjection v (coarseShading.union ∩ Metric.closedBall q (Real.sqrt rho)) := by
    rintro y ⟨x, hx, rfl⟩
    have h4 : x ∈ coarseShading.union ∩ Metric.closedBall q (Real.sqrt rho) := h_target_sub hx
    exact ⟨x, h4, rfl⟩
  exact PureWZ2PaperADSet1.mono_set h_ad_S h_proj_sub

end Kakeya.Assouad

end

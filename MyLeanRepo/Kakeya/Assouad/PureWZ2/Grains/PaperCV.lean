import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.CV.MultilinearKakeya.Complete
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# CV broad-set estimate for WZ1 paper tube shadings

Adapts the completed multilinear Kakeya theorem from standard unit-segment
`TubeShading` to `WZ1PaperTubeShading` (6δ-thick full lines cropped to a box).

Approach: scale space by (6δ)⁻¹, map paper carriers to unit-line tubes,
apply the unit-scale theorem, scale back by (6δ)³.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.Assouad

/-- Trilinear multiplicity for a paper tube shading. -/
def paperShadingTrilinearMultiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F) (x : Point3) : ENNReal :=
  ∑ i : Fin F.card, ∑ j : Fin F.card, ∑ k : Fin F.card,
    Kakeya.CV.setIndicator (Y.carrier i) x *
    Kakeya.CV.setIndicator (Y.carrier j) x *
    Kakeya.CV.setIndicator (Y.carrier k) x *
    ENNReal.ofReal
      (Kakeya.CV.tripleVolume
        ![ (F.tube i).direction, (F.tube j).direction, (F.tube k).direction])

/-- The completed unit-scale multilinear Kakeya theorem. -/
private theorem unit_scale_multilinear_kakeya :
    Kakeya.CV.UnitScaleMultilinearKakeyaStatement :=
  Kakeya.CV.polynomial_visibility_to_unitScale_multilinear_kakeya_of_factorization
    Kakeya.CV.polynomial_visibility_to_lattice_factorization_closed
    Kakeya.CV.polynomial_visibility_complete
    (Kakeya.CV.concrete_mollified_surface
      Kakeya.CV.generic_polynomial_regularity
      Kakeya.CV.polynomial_cylinder_estimate
      Kakeya.CV.squarefree_singularSet_null
      Kakeya.CV.coefficientSurfaceFunctional_aeMeasurable
      Kakeya.CV.mollified_surface_continuity)
    (Kakeya.CV.concrete_mollified_visibility
      (Kakeya.CV.concrete_mollified_surface
        Kakeya.CV.generic_polynomial_regularity
        Kakeya.CV.polynomial_cylinder_estimate
        Kakeya.CV.squarefree_singularSet_null
        Kakeya.CV.coefficientSurfaceFunctional_aeMeasurable
        Kakeya.CV.mollified_surface_continuity))
    Kakeya.CV.polynomial_cylinder_estimate
    Kakeya.CV.visibility_directional_surface_bound
    (Kakeya.CV.visibility_degree_bound
      Kakeya.CV.polynomial_cylinder_estimate
      Kakeya.CV.visibility_directional_surface_bound)
    Kakeya.CV.multilinear_kakeya_preliminary_reduction

/-- The unit-line family obtained by scaling paper tube axes by (6δ)⁻¹. -/
private def paperUnitLineFamily
    {delta : ℝ} (_hdelta : 0 < delta)
    (F : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.CV.UnitLineFamily :=
  { card := F.card
    base := fun i => (6 * delta)⁻¹ • (F.tube i).base
    direction := fun i => (F.tube i).direction
    direction_unit := fun i => (F.tube i).direction_unit }

/-- The tube axis line is closed. -/
private lemma tubeAxisLine_isClosed {delta : ℝ} (T : Kakeya.DeltaTube delta) :
    IsClosed (tubeAxisLine T) := by
  let dir : Submodule ℝ Point3 := Submodule.span ℝ {T.direction}
  have h_dir_closed : IsClosed (dir : Set Point3) := by
    exact Submodule.closed_of_finiteDimensional dir
  let trans : Point3 ≃ₜ Point3 :=
    { toFun := fun x => T.base + x
      invFun := fun x => x - T.base
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      continuous_toFun := continuous_const.add continuous_id
      continuous_invFun := continuous_id.sub continuous_const }
  have h_line_closed : IsClosed (trans '' (dir : Set Point3)) :=
    trans.isClosed_image.mpr h_dir_closed
  have h1 : trans '' (dir : Set Point3) = tubeAxisLine T := by
    ext z
    simp only [trans, Set.mem_image, tubeAxisLine, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h_v1 : ∃ (a : ℝ), a • T.direction = v := by
        simpa [dir, Submodule.mem_span_singleton] using hv
      rcases h_v1 with ⟨t, ht⟩
      exact ⟨t, by simp [ht]⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t • T.direction, ?_, by simp⟩
      simp [dir, Submodule.mem_span_singleton]
  rw [← h1]
  exact h_line_closed

/-- For nonempty closed sets, infEDist = ofReal ∘ infDist. -/
private lemma infEDist_eq_ofReal_infDist
    {x : Point3} {s : Set Point3} (hs : s.Nonempty) (hclosed : IsClosed s) :
    Metric.infEDist x s = ENNReal.ofReal (Metric.infDist x s) := by
  obtain ⟨z, hz, hdist_eq⟩ := hclosed.exists_infDist_eq_dist hs x
  have h1 : edist x z = ENNReal.ofReal (Metric.infDist x s) := by
    rw [edist_dist x z, hdist_eq]
  have h2 : Metric.infEDist x s ≤ edist x z :=
    Metric.infEDist_le_edist_of_mem hz
  have h3 : Metric.infEDist x s ≤ ENNReal.ofReal (Metric.infDist x s) := by
    rw [h1] at h2
    exact h2
  have h4 : ENNReal.ofReal (Metric.infDist x s) ≤ Metric.infEDist x s := by
    have h_all : ∀ y ∈ s, ENNReal.ofReal (Metric.infDist x s) ≤ edist x y := by
      intro y hy
      have h5 : Metric.infDist x s ≤ dist x y := Metric.infDist_le_dist_of_mem hy
      have h6 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
      rw [h6]
      exact ENNReal.ofReal_le_ofReal h5
    exact Metric.le_infEDist.mpr h_all
  exact le_antisymm h3 h4

/-- Scaling lemma: paper carrier at (6δ)•y implies unit-tube membership. -/
private lemma paper_scaled_mem_unitTube
    {delta : ℝ} (hdelta : 0 < delta)
    (T : Kakeya.DeltaTube delta) (y : Point3)
    (hy : (6 * delta) • y ∈ wz1PaperTubeCarrier T) :
    y ∈ Kakeya.CV.unitTube ((6 * delta)⁻¹ • T.base) T.direction := by
  set c : ℝ := 6 * delta with hc
  have hc_pos : 0 < c := by positivity
  set x : Point3 := c • y with hx
  have h1 : x ∈ Metric.cthickening c (tubeAxisLine T) := hy.1
  have h_infEDist : Metric.infEDist x (tubeAxisLine T) ≤ ENNReal.ofReal c := by
    simpa [Metric.cthickening_eq_preimage_infEDist] using h1
  have h_nonempty : (tubeAxisLine T).Nonempty := by
    refine ⟨T.base, ?_⟩
    simp [tubeAxisLine] <;> exact ⟨0, by simp⟩
  have h_closed : IsClosed (tubeAxisLine T) := tubeAxisLine_isClosed T
  have h_eq_inf : Metric.infEDist x (tubeAxisLine T) =
      ENNReal.ofReal (Metric.infDist x (tubeAxisLine T)) :=
    infEDist_eq_ofReal_infDist h_nonempty h_closed
  have h_infDist : Metric.infDist x (tubeAxisLine T) ≤ c := by
    rw [h_eq_inf] at h_infEDist
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h_infEDist
  obtain ⟨z, hz, hdist_eq⟩ := h_closed.exists_infDist_eq_dist h_nonempty x
  have hdist : dist x z ≤ c := by
    have h : dist x z = Metric.infDist x (tubeAxisLine T) := hdist_eq.symm
    rw [h]
    exact h_infDist
  rcases hz with ⟨t, rfl⟩
  let z' : Point3 := c⁻¹ • (T.base + t • T.direction)
  have hz' : z' ∈ Kakeya.CV.affineLine (c⁻¹ • T.base) T.direction := by
    refine ⟨c⁻¹ * t, ?_⟩
    dsimp only [z']
    simp [smul_add, smul_smul] <;> ring
  have hscale : c • z' = T.base + t • T.direction := by
    dsimp only [z']
    rw [smul_smul, mul_inv_cancel₀ hc_pos.ne', one_smul]
  have hdist' : dist y z' ≤ 1 := by
    have hscaled : c * dist y z' ≤ c := by
      calc
        c * dist y z'
          = dist (c • y) (c • z') := by
            rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc_pos]
        _ = dist x (T.base + t • T.direction) := by rw [hscale]
        _ ≤ c := hdist
    nlinarith
  exact (Metric.infDist_le_dist_of_mem hz').trans hdist'

/-- Indicator scaling: paper indicator at (6δ)•y ≤ unit-tube indicator at y. -/
private lemma paper_indicator_scaled_le
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (i : Fin F.card) (y : Point3) :
    Kakeya.CV.setIndicator (Y.carrier i) ((6 * delta) • y) ≤
    Kakeya.CV.setIndicator
      (Kakeya.CV.unitTube ((6 * delta)⁻¹ • (F.tube i).base) (F.tube i).direction) y := by
  by_cases hy : (6 * delta) • y ∈ Y.carrier i
  · have hbody : (6 * delta) • y ∈ wz1PaperTubeCarrier (F.tube i) :=
      Y.subset_body i hy
    have hy' : y ∈ Kakeya.CV.unitTube ((6 * delta)⁻¹ • (F.tube i).base) (F.tube i).direction :=
      paper_scaled_mem_unitTube hdelta (F.tube i) y hbody
    have h_lhs : Kakeya.CV.setIndicator (Y.carrier i) ((6 * delta) • y) = 1 := by
      rw [Kakeya.CV.setIndicator, Set.indicator_of_mem hy] <;> simp
    have h_rhs : Kakeya.CV.setIndicator (Kakeya.CV.unitTube ((6 * delta)⁻¹ • (F.tube i).base) (F.tube i).direction) y = 1 := by
      rw [Kakeya.CV.setIndicator, Set.indicator_of_mem hy'] <;> simp
    rw [h_lhs, h_rhs]
  · have h_lhs : Kakeya.CV.setIndicator (Y.carrier i) ((6 * delta) • y) = 0 := by
      rw [Kakeya.CV.setIndicator]
      simp [Set.indicator, hy]
    rw [h_lhs] <;> positivity

/-- Paper multiplicity at (6δ)•y is bounded by unit-scale multiplicity at y. -/
private lemma paper_multiplicity_scaled_le
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F) (y : Point3) :
    paperShadingTrilinearMultiplicity Y ((6 * delta) • y) ≤
    Kakeya.CV.unitScaleTrilinearMultiplicity
      (paperUnitLineFamily hdelta F)
      (paperUnitLineFamily hdelta F)
      (paperUnitLineFamily hdelta F) y := by
  dsimp only [paperShadingTrilinearMultiplicity,
    Kakeya.CV.unitScaleTrilinearMultiplicity,
    Kakeya.CV.UnitLineFamily.tube]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  have hi := paper_indicator_scaled_le hdelta Y i y
  have hj := paper_indicator_scaled_le hdelta Y j y
  have hk := paper_indicator_scaled_le hdelta Y k y
  have h_ij := mul_le_mul' hi hj
  have h_ijk := mul_le_mul' h_ij hk
  have h_tv : ENNReal.ofReal (Kakeya.CV.tripleVolume
          ![ (F.tube i).direction, (F.tube j).direction, (F.tube k).direction]) =
        ENNReal.ofReal (Kakeya.CV.tripleVolume
          ![ (paperUnitLineFamily hdelta F).direction i,
             (paperUnitLineFamily hdelta F).direction j,
             (paperUnitLineFamily hdelta F).direction k]) := by
    congr <;> rfl
  rw [h_tv]
  exact mul_le_mul' h_ijk (le_refl _)

/-- Lintegral scaling by (6δ)³. -/
private lemma lintegral_scaling
    (f : Point3 → ENNReal) {delta : ℝ} (hdelta : 0 < delta) :
    (∫⁻ x : Point3, f x ∂volume) =
      ENNReal.ofReal ((6 * delta) ^ 3) *
        ∫⁻ y : Point3, f ((6 * delta) • y) ∂volume := by
  let c : ℝ := 6 * delta
  have hc_pos : 0 < c := by positivity
  let e : Point3 ≃ᵐ Point3 :=
    (Homeomorph.smul
      (isUnit_iff_ne_zero.2 (inv_ne_zero hc_pos.ne')).unit).toMeasurableEquiv
  have he_apply : ∀ x : Point3, e x = c⁻¹ • x := by
    intro x
    rfl
  have hmap : Measure.map e volume = ENNReal.ofReal (c ^ 3) • volume := by
    change Measure.map (c⁻¹ • ·) volume = _
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hc_pos.ne')]
    have hfinrank : Module.finrank ℝ Point3 = 3 := finrank_euclideanSpace_fin
    rw [hfinrank, inv_pow, inv_inv, abs_of_pos (pow_pos hc_pos 3)]
  calc
    (∫⁻ x : Point3, f x ∂volume) =
        ∫⁻ x : Point3, f (c • e x) ∂volume := by
      apply lintegral_congr
      intro x
      rw [he_apply]
      simp [hc_pos.ne']
    _ = ∫⁻ y : Point3, f (c • y) ∂Measure.map e volume := by
      exact (MeasureTheory.lintegral_map_equiv (fun y : Point3 => f (c • y)) e).symm
    _ = ∫⁻ y : Point3, f (c • y) ∂(ENNReal.ofReal (c ^ 3) • volume) := by
      rw [hmap]
    _ = ENNReal.ofReal (c ^ 3) * ∫⁻ y : Point3, f (c • y) ∂volume := by
      rw [lintegral_smul_measure] <;> rfl

/-- Scaling identity for the RHS: (6δ)³ * C * N^(3/2) = C * (δ² * N)^(3/2) * 6³. -/
private lemma paper_scaling_rhs_identity (C N : ENNReal)
    {delta : ℝ} (hdelta : 0 < delta) :
    ENNReal.ofReal ((6 * delta) ^ 3) *
        (C * (N * N * N) ^ (1 / 2 : ℝ)) =
      (ENNReal.ofReal ((6 : ℝ) ^ 3) * C) *
        (ENNReal.ofReal (delta ^ 2) * N) ^ (3 / 2 : ℝ) := by
  have hδ0 : 0 ≤ delta := hdelta.le
  have h6pos : 0 ≤ (6 : ℝ) := by norm_num
  have h_ofReal6δ3 : ENNReal.ofReal ((6 * delta) ^ 3) =
      ENNReal.ofReal ((6 : ℝ) ^ 3) * ENNReal.ofReal (delta ^ 3) := by
    rw [show (6 * delta) ^ 3 = (6 : ℝ) ^ 3 * delta ^ 3 by ring]
    rw [ENNReal.ofReal_mul] <;> positivity
  have h_ofRealδ2 : ENNReal.ofReal (delta ^ 2) = (ENNReal.ofReal delta) ^ 2 := by
    rw [ENNReal.ofReal_pow hδ0 2]
  have h_ofRealδ3 : ENNReal.ofReal (delta ^ 3) = (ENNReal.ofReal delta) ^ 3 := by
    rw [ENNReal.ofReal_pow hδ0 3]
  have hN : (N * N * N) ^ (1 / 2 : ℝ) = N ^ (3 / 2 : ℝ) := by
    have hN3 : N * N * N = N ^ 3 := by simp [pow_succ] <;> ring
    rw [hN3, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] <;> norm_num
  have hD : ((ENNReal.ofReal delta) ^ 2) ^ (3 / 2 : ℝ) = (ENNReal.ofReal delta) ^ 3 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] <;> norm_num
  rw [h_ofReal6δ3, h_ofRealδ2, h_ofRealδ3, hN]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [hD]
  <;> ring

/--
CV broad-set estimate for paper tube shadings.

Given a measurable set E on which the sqrt-trilinear multiplicity is at least L,
the volume of E is bounded by C * (δ² * |F|)^(3/2).
-/
theorem paper_cv_broad_set_estimate :
    ∃ (C : ENNReal), C ≠ ⊤ ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (F : Kakeya.Streamlined.TubeFamily delta),
          ∀ (Y : WZ1PaperTubeShading F),
            ∀ (E : Set Point3) (L : ENNReal),
              MeasurableSet E →
                (∀ x ∈ E, L ≤
                  (paperShadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ)) →
                L * volume E ≤
                  C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) := by
  rcases unit_scale_multilinear_kakeya with ⟨C0, hC0, hUnit⟩
  let C : ENNReal := ENNReal.ofReal ((6 : ℝ) ^ 3) * C0
  have hC_ne_top : C ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC0
  refine ⟨C, hC_ne_top, ?_⟩
  intro delta hdelta hdelta_one F Y E L hE hLower
  let UF := paperUnitLineFamily hdelta F
  have hpoint : ∀ (y : Point3),
      (paperShadingTrilinearMultiplicity Y ((6 * delta) • y)) ^ (1 / 2 : ℝ) ≤
      (Kakeya.CV.unitScaleTrilinearMultiplicity UF UF UF y) ^ (1 / 2 : ℝ) := by
    intro y
    apply ENNReal.rpow_le_rpow
    · exact paper_multiplicity_scaled_le hdelta Y y
    · norm_num
  have h_integral_bound :
      (∫⁻ x : Point3,
        (paperShadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ)) ≤
      C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) := by
    calc
      (∫⁻ x : Point3,
          (paperShadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ))
        = ENNReal.ofReal ((6 * delta) ^ 3) *
            ∫⁻ y : Point3,
              (paperShadingTrilinearMultiplicity Y ((6 * delta) • y)) ^
                (1 / 2 : ℝ) :=
          lintegral_scaling (fun x =>
            (paperShadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ)) hdelta
      _ ≤ ENNReal.ofReal ((6 * delta) ^ 3) *
            ∫⁻ y : Point3,
              (Kakeya.CV.unitScaleTrilinearMultiplicity UF UF UF y) ^
                (1 / 2 : ℝ) := by
          have h_int : ∫⁻ y : Point3,
              (paperShadingTrilinearMultiplicity Y ((6 * delta) • y)) ^ (1 / 2 : ℝ) ≤
            ∫⁻ y : Point3,
              (Kakeya.CV.unitScaleTrilinearMultiplicity UF UF UF y) ^ (1 / 2 : ℝ) :=
            lintegral_mono hpoint
          exact mul_le_mul_right h_int _
      _ ≤ ENNReal.ofReal ((6 * delta) ^ 3) *
            (C0 * ((F.enncard * F.enncard * F.enncard) ^ (1 / 2 : ℝ))) := by
          apply mul_le_mul_right
          have h_card : UF.card = F.card := by rfl
          have h_main : ∀ (G : Kakeya.CV.UnitLineFamily), G.card = F.card →
              (∫⁻ y : Point3, (Kakeya.CV.unitScaleTrilinearMultiplicity G G G y) ^ (1 / 2 : ℝ)) ≤
              C0 * ((F.enncard * F.enncard * F.enncard) ^ (1 / 2 : ℝ)) := by
            intro G hG
            have h := hUnit G G G
            have h2 : (G.card : ENNReal) * (G.card : ENNReal) * (G.card : ENNReal) =
                F.enncard * F.enncard * F.enncard := by
              simp [hG, Kakeya.Streamlined.TubeFamily.enncard]
            have h_rhs : C0 * (((G.card : ENNReal) * (G.card : ENNReal) * (G.card : ENNReal)) ^ (1 / 2 : ℝ)) =
                C0 * ((F.enncard * F.enncard * F.enncard) ^ (1 / 2 : ℝ)) := by
              rw [h2]
            rw [h_rhs] at h
            exact h
          exact h_main UF h_card
      _ = C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) :=
          paper_scaling_rhs_identity C0 F.enncard hdelta
  have h_final : L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) := by
    have h_step1 : L * volume E = ∫⁻ _x : Point3 in E, L ∂volume := by
      rw [setLIntegral_const] <;> rfl
    have h_step2 : (∫⁻ _x : Point3 in E, L ∂volume) ≤
        ∫⁻ x : Point3 in E, (paperShadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ) := by
      exact setLIntegral_mono' hE hLower
    have h_step3 : (∫⁻ x : Point3 in E, (paperShadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ)) ≤
        ∫⁻ x : Point3, (paperShadingTrilinearMultiplicity Y x) ^ (1 / 2 : ℝ) := by
      exact setLIntegral_le_lintegral E fun x =>
        paperShadingTrilinearMultiplicity Y x ^ (1 / 2 : ℝ)
    rw [h_step1]
    exact le_trans h_step2 (le_trans h_step3 h_integral_bound)
  exact h_final

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers

/-!
# The visibility body is a convex body

Proves that `visibilityBody p S` is a compact convex set with nonempty interior,
using the polynomial cylinder estimate.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Kakeya.CV

/-- The visibility body is a convex body. -/
lemma visibilityBody_convexBody
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ≠ 0)
    (hSing : HasNegligibleSingularSet p)
    (k : ℕ) (hk : 1 ≤ k)
    (C_cyl : NNReal) (hC_cyl_pos : 0 < C_cyl)
    (hCylinder : ∀ (a e : Point 3), ‖e‖ = 1 →
      directionalSurfaceArea e p (polynomialZeroSet p ∩ unitTube a e) ≤
        (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞))
    (Q : Set (Point 3)) (c : Point 3) (hQ : Q ⊆ Metric.closedBall c 1)
    (e : Point 3) (he : ‖e‖ = 1)
    (h_area : directionalSurfaceArea e p (polynomialZeroSet p ∩ Q) ≤ 1) :
    JohnEllipsoid.IsConvexBody (visibilityBody p (polynomialZeroSet p ∩ Q)) := by
  let S : Set (Point 3) := polynomialZeroSet p ∩ Q
  let K : Set (Point 3) := visibilityBody p S

  -- --------------------------------------------------------------------------
  -- 1. Convexity
  -- --------------------------------------------------------------------------
  have h_conv : Convex ℝ K := by
    intro u hu v hv a b ha hb hab
    have hu_ball : u ∈ unitBall 3 := hu.1
    have hv_ball : v ∈ unitBall 3 := hv.1
    have hu_area : directionalSurfaceArea u p S ≤ 1 := hu.2
    have hv_area : directionalSurfaceArea v p S ≤ 1 := hv.2
    let w := a • u + b • v
    have hw_ball : w ∈ unitBall 3 := by
      have h : Convex ℝ (unitBall 3) := convex_closedBall 0 1
      exact h hu_ball hv_ball ha hb hab
    have hw_area : directionalSurfaceArea w p S ≤ 1 := by
      calc
        directionalSurfaceArea w p S
          ≤ directionalSurfaceArea (a • u) p S +
              directionalSurfaceArea (b • v) p S :=
          directionalSurfaceArea_subadditivity (a • u) (b • v) p S
        _ = ENNReal.ofReal a * directionalSurfaceArea u p S +
              ENNReal.ofReal b * directionalSurfaceArea v p S := by
          rw [directionalSurfaceArea_homogeneity a ha u p S,
              directionalSurfaceArea_homogeneity b hb v p S]
        _ ≤ ENNReal.ofReal a * 1 + ENNReal.ofReal b * 1 := by
          gcongr <;> assumption
        _ = 1 := by
          have h : ENNReal.ofReal a + ENNReal.ofReal b = 1 := by
            rw [← ENNReal.ofReal_add ha hb, hab] <;> norm_num
          simpa using h
    exact ⟨hw_ball, hw_area⟩

  -- --------------------------------------------------------------------------
  -- 2. Compactness (closed + bounded)
  -- --------------------------------------------------------------------------
  have h_bounded : Bornology.IsBounded K := by
    have h : K ⊆ unitBall 3 := fun x hx => hx.1
    exact Metric.isBounded_closedBall.subset h

  have h_closed : IsClosed K := by
    have h1 : IsClosed (unitBall 3) := Metric.isClosed_closedBall
    have hseq : IsSeqClosed {u : Point 3 | directionalSurfaceArea u p S ≤ 1} := by
      intro u u₀ hu_in hlim
      let f : ℕ → Point 3 → ENNReal := fun n x =>
        ENNReal.ofReal ‖inner ℝ (u n) (polynomialUnitNormal p x)‖
      let f₀ : Point 3 → ENNReal := fun x =>
        ENNReal.ofReal ‖inner ℝ u₀ (polynomialUnitNormal p x)‖
      have hf_meas : ∀ n, Measurable (f n) := by
        intro n
        exact directionalSurfaceArea_integrand_measurable (u n) p
      have h_pointwise : ∀ x, Filter.liminf (fun n => f n x) Filter.atTop = f₀ x := by
        intro x
        have h_cont : Continuous (fun y : Point 3 =>
            ‖inner ℝ y (polynomialUnitNormal p x)‖) := by fun_prop
        have h_lim : Filter.Tendsto (fun n => ‖inner ℝ (u n) (polynomialUnitNormal p x)‖)
            Filter.atTop (nhds ‖inner ℝ u₀ (polynomialUnitNormal p x)‖) :=
          h_cont.tendsto u₀ |>.comp hlim
        have h_ofReal_tendsto : Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (f₀ x)) := by
          have h : Continuous (fun r : ℝ => ENNReal.ofReal r) :=
            ENNReal.continuous_ofReal
          exact h.tendsto _ |>.comp h_lim
        exact h_ofReal_tendsto.liminf_eq
      have h_fatou : ∫⁻ (x : Point 3) in S, f₀ x
            ∂(MeasureTheory.Measure.hausdorffMeasure 2) ≤
          Filter.liminf (fun n => ∫⁻ (x : Point 3) in S, f n x
            ∂(MeasureTheory.Measure.hausdorffMeasure 2)) Filter.atTop := by
        let μ' := (MeasureTheory.Measure.hausdorffMeasure 2).restrict S
        have h : ∫⁻ (x : Point 3), Filter.liminf (fun n => f n x) Filter.atTop ∂μ' ≤
            Filter.liminf (fun n => ∫⁻ (x : Point 3), f n x ∂μ') Filter.atTop := by
          exact lintegral_liminf_le hf_meas
        simpa [h_pointwise] using h
      have h_le1 : ∀ n, directionalSurfaceArea (u n) p S ≤ 1 := hu_in
      have h_liminf_le1 : Filter.liminf (fun n => directionalSurfaceArea (u n) p S) Filter.atTop ≤ 1 := by
        have h_freq : ∃ᶠ (n : ℕ) in Filter.atTop, directionalSurfaceArea (u n) p S ≤ 1 :=
          Filter.Frequently.of_forall h_le1
        exact Filter.liminf_le_of_frequently_le h_freq
      have h_main : directionalSurfaceArea u₀ p S ≤ 1 := by
        simpa [directionalSurfaceArea, f₀] using h_fatou.trans h_liminf_le1
      exact h_main
    have h2 : IsClosed {u : Point 3 | directionalSurfaceArea u p S ≤ 1} :=
      IsSeqClosed.isClosed hseq
    exact h1.inter h2

  have h_compact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded h_closed h_bounded

  -- --------------------------------------------------------------------------
  -- 3. Nonempty interior
  -- --------------------------------------------------------------------------
  let M : ℝ := max 1 (C_cyl : ℝ)
  have hM_pos : 0 < M := by positivity
  have hC_le_M : (C_cyl : ℝ) ≤ M := le_max_right _ _
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  let r : ℝ := 1 / (M * (k : ℝ))
  have hr_pos : 0 < r := by positivity
  have h_ball_subset : Metric.ball 0 r ⊆ K := by
    intro u hu
    have h_norm_lt : ‖u‖ < r := by
      simpa [Metric.mem_ball] using hu
    have h_norm_le1 : ‖u‖ ≤ 1 := by
      have h : 1 ≤ M * (k : ℝ) := by
        have h1 : 1 ≤ M := le_max_left _ _
        have h2 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
        nlinarith
      have h' : r * (M * (k : ℝ)) = 1 := by
        simp [r] <;> field_simp [hM_pos.ne', hk_pos.ne'] <;> ring
      have h'' : r ≤ 1 := by
        calc r
          = r * 1 := by ring
        _ ≤ r * (M * (k : ℝ)) := by gcongr <;> linarith
        _ = 1 := h'
      linarith
    have h_ball : u ∈ unitBall 3 := by
      simpa [unitBall, Metric.mem_closedBall] using h_norm_le1
    by_cases hz : u = 0
    · subst hz
      have h0_ball : (0 : Point 3) ∈ unitBall 3 := by
        simp [unitBall, Metric.mem_closedBall] <;> norm_num
      have h0 : directionalSurfaceArea (0 : Point 3) p S = 0 := by
        have h := directionalSurfaceArea_homogeneity 0 (by norm_num) e p S
        simpa using h
      have h0_area : directionalSurfaceArea (0 : Point 3) p S ≤ 1 := by
        rw [h0] <;> simp
      exact ⟨h0_ball, h0_area⟩
    · have hnorm_pos : 0 < ‖u‖ := by
        rw [norm_pos_iff] <;> exact hz
      let u' : Point 3 := ‖u‖⁻¹ • u
      have hu'_norm : ‖u'‖ = 1 := by
        simp [u', norm_smul, hnorm_pos.ne'] <;> field_simp [hnorm_pos.ne'] <;> norm_num
      have hQ_tube : Q ⊆ unitTube c u' := by
        calc Q
          ⊆ Metric.closedBall c 1 := hQ
        _ ⊆ unitTube c u' := unitBall_subset_unitTube c u' hu'_norm
      have hS_subset : S ⊆ polynomialZeroSet p ∩ unitTube c u' := by
        exact Set.inter_subset_inter_right _ hQ_tube
      have h_cyl : directionalSurfaceArea u' p (polynomialZeroSet p ∩ unitTube c u') ≤
          (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) :=
        hCylinder c u' hu'_norm
      have h_area_u' : directionalSurfaceArea u' p S ≤
          (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) := by
        calc directionalSurfaceArea u' p S
          ≤ directionalSurfaceArea u' p (polynomialZeroSet p ∩ unitTube c u') :=
            directionalSurfaceArea_mono u' p hS_subset
        _ ≤ (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) := h_cyl
      have h_u_eq : u = ‖u‖ • u' := by
        simp [u', smul_smul] <;> field_simp [hnorm_pos.ne'] <;> simp
      have h_area_u : directionalSurfaceArea u p S ≤ 1 := by
        rw [h_u_eq]
        have h_hom : directionalSurfaceArea (‖u‖ • u') p S =
            ENNReal.ofReal ‖u‖ * directionalSurfaceArea u' p S :=
          directionalSurfaceArea_homogeneity ‖u‖ (by positivity) u' p S
        rw [h_hom]
        have h1 : ENNReal.ofReal ‖u‖ * directionalSurfaceArea u' p S ≤
            ENNReal.ofReal ‖u‖ * ((C_cyl : ℝ≥0∞) * (k : ℝ≥0∞)) := by
          exact mul_le_mul_right h_area_u' _
        have h2 : ENNReal.ofReal ‖u‖ * ((C_cyl : ℝ≥0∞) * (k : ℝ≥0∞)) ≤
            ENNReal.ofReal r * (ENNReal.ofReal M * (k : ℝ≥0∞)) := by
          have h21 : ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal r :=
            ENNReal.ofReal_le_ofReal h_norm_lt.le
          have h22 : (C_cyl : ℝ≥0∞) ≤ ENNReal.ofReal M := by
            have h221 : (C_cyl : ℝ≥0∞) = ENNReal.ofReal (C_cyl : ℝ) := by simp
            rw [h221]
            exact ENNReal.ofReal_le_ofReal hC_le_M
          gcongr
        have h3 : ENNReal.ofReal r * (ENNReal.ofReal M * (k : ℝ≥0∞)) =
            ENNReal.ofReal (r * M * (k : ℝ)) := by
          have hk_coe : (k : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) := by simp
          rw [hk_coe]
          have h31 : ENNReal.ofReal r * (ENNReal.ofReal M * ENNReal.ofReal (k : ℝ)) =
              ENNReal.ofReal (r * M * (k : ℝ)) := by
            have h : ENNReal.ofReal r * (ENNReal.ofReal M * ENNReal.ofReal (k : ℝ)) =
                ENNReal.ofReal r * ENNReal.ofReal M * ENNReal.ofReal (k : ℝ) := by ring
            rw [h]
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            <;> rfl
          exact h31
        have h4 : ENNReal.ofReal (r * M * (k : ℝ)) = 1 := by
          have h5 : r * M * (k : ℝ) = 1 := by
            simp [r] <;> field_simp [hM_pos.ne', hk_pos.ne'] <;> ring
          rw [h5] <;> simp
        have h5 : ENNReal.ofReal ‖u‖ * directionalSurfaceArea u' p S ≤ 1 := by
          calc ENNReal.ofReal ‖u‖ * directionalSurfaceArea u' p S
            ≤ ENNReal.ofReal ‖u‖ * ((C_cyl : ℝ≥0∞) * (k : ℝ≥0∞)) := h1
            _ ≤ ENNReal.ofReal r * (ENNReal.ofReal M * (k : ℝ≥0∞)) := h2
            _ = ENNReal.ofReal (r * M * (k : ℝ)) := h3
            _ = 1 := h4
        exact h5
      exact ⟨h_ball, h_area_u⟩
  have h_interior : (interior K).Nonempty := by
    have h_open : IsOpen (Metric.ball (0 : Point 3) r) := Metric.isOpen_ball
    have h : Metric.ball (0 : Point 3) r ⊆ interior K :=
      (h_open.subset_interior_iff).mpr h_ball_subset
    exact ⟨0, h (Metric.mem_ball_self hr_pos)⟩

  -- --------------------------------------------------------------------------
  -- 4. Combine
  -- --------------------------------------------------------------------------
  exact ⟨h_conv, h_compact, h_interior⟩

end Kakeya.CV

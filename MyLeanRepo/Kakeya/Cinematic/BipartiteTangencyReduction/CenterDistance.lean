import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleRefinement.DoublingLemma

/-!
# Center distance bound for polynomial refinement

If a curvilinear rectangle `R` is `5`-tangent to a family member `w`, then the
`C²` distance between `R.function` and `w` is bounded by a constant multiple of
`t`.  This lets us use any fixed `w₀ ∈ W` as the center required by
`PolynomialRectangleRefinementStatement`.

## Proof

Apply `CommonTangentRectangleRobustStatement` with `tangency = 5` to the pair
`(R.function, w)` using `R` itself as the common rectangle.  Since
`tangencyParameterOn I f g ≥ 0`, the factor `(tangencyParameter + δ)` is at
least `δ`, so dividing by `δ` yields the bound.
-/

noncomputable section

namespace Kakeya.Cinematic

/-- The tangency parameter is always non-negative. -/
lemma tangencyParameterOn_nonneg {I : ParameterInterval} {f g : C2Function} :
    0 ≤ tangencyParameterOn I f g := by
  apply Real.sInf_nonneg
  intro r hr
  simp only [tangencyParameterOn, Set.mem_setOf_eq] at hr
  rcases hr with ⟨x, _, rfl⟩
  positivity

/--
If `R` is `5`-tangent to `w`, then `c2Distance R.function w` is `O(t)`.

The constant depends only on `K` (through the common-tangent-rectangle
constant and the doubling constant derived from cinematic curvature).
-/
lemma rectangle_center_distance_bound
    {K : ℝ} (hK : 1 ≤ K)
    {family : Set C2Function} (hcurv : HasCinematicCurvature family K)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t : ℝ} (hdelta : 0 < delta) (hdt : delta ≤ t) (ht1 : t ≤ 1)
    {R : CurvilinearRectangle delta t}
    (hRfam : R.function ∈ family) (hRquarter : R.IsOverCentralQuarterOf I)
    {w : C2Function} (hw : w ∈ family)
    (hRt : R.IsLambdaTangent w 5)
    (hCommonTangent : CommonTangentRectangleRobustStatement) :
    ∃ C_center : ℝ, 0 < C_center ∧
      c2Distance R.function w ≤ C_center * t := by
  by_cases h_eq : R.function = w
  · have h : c2Distance R.function w = 0 := by
      rw [h_eq]
      exact dist_self _
    refine ⟨1, by positivity, ?_⟩
    rw [h]
    have ht_pos : 0 ≤ t := by linarith [hdelta]
    exact mul_nonneg (by norm_num) ht_pos
  · obtain ⟨D, hD1, hfamily⟩ :=
      hasCinematicCurvature_implies_isCinematicFamily hK hcurv
    obtain ⟨C_ct, hC_ct1, hCT⟩ := hCommonTangent K D hK hD1
    have hRt_self : R.IsLambdaTangent R.function 5 := by
      intro p hp
      have h : |p.2 - R.function p.1| ≤ delta := hp.2
      exact h.trans (by linarith [hdelta])
    have hbound :
        (tangencyParameterOn I R.function w + delta) *
          c2Distance R.function w ≤
        C_ct * Real.rpow 5 C_ct * delta * t :=
      hCT 5 (by norm_num) family hfamily I hI delta t hdelta hdt ht1
        R hRfam hRquarter R.function hRfam w hw h_eq hRt_self hRt
    have htp_nonneg : 0 ≤ tangencyParameterOn I R.function w :=
      tangencyParameterOn_nonneg
    have hnonneg : 0 ≤ c2Distance R.function w := dist_nonneg
    have h_rpow_pos : 0 < C_ct * Real.rpow 5 C_ct := by
      apply mul_pos
      · linarith
      · exact Real.rpow_pos_of_pos (by norm_num) _
    have h_main : c2Distance R.function w ≤ C_ct * Real.rpow 5 C_ct * t := by
      have h1 : delta * c2Distance R.function w ≤
          (tangencyParameterOn I R.function w + delta) *
            c2Distance R.function w := by
        gcongr
        <;> linarith
      have h2 : delta * c2Distance R.function w ≤
          C_ct * Real.rpow 5 C_ct * delta * t :=
        h1.trans hbound
      calc
        c2Distance R.function w
          = (delta * c2Distance R.function w) / delta := by
            field_simp [hdelta.ne'] <;> ring
        _ ≤ (C_ct * Real.rpow 5 C_ct * delta * t) / delta := by gcongr
        _ = C_ct * Real.rpow 5 C_ct * t := by
            field_simp [hdelta.ne'] <;> ring
    exact ⟨C_ct * Real.rpow 5 C_ct, h_rpow_pos, h_main⟩

/--
All rectangle functions are within a constant multiple of `t` of any fixed
member `w₀` of `W`, provided every rectangle is `5`-tangent to some member of
`W` and all members of `W` have pairwise distance at most `6 * t`.
-/
lemma family_center_distance_bound
    {K : ℝ} (hK : 1 ≤ K)
    {family : Set C2Function} (hcurv : HasCinematicCurvature family K)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t : ℝ} (hdelta : 0 < delta) (hdt : delta ≤ t) (ht1 : t ≤ 1)
    {W : FiniteFunctionFamily} (hW : W.carrier ⊆ family)
    {R : RectangleFamily delta t}
    (hRfam : R.CentersIn family)
    (hRquarter : R.IsOverCentralQuarterOf I)
    (w₀ : C2Function) (hw₀ : w₀ ∈ W.carrier)
    (hcounts : ∀ i, 0 < RectangleFamily.tangentCount (R.rectangle i) W 5)
    (hdiam : ∀ ⦃f⦄, f ∈ W.carrier → ∀ ⦃g⦄, g ∈ W.carrier → dist f g ≤ 6 * t)
    (hCommonTangent : CommonTangentRectangleRobustStatement) :
    ∃ C_center : ℝ, 0 < C_center ∧
      ∀ i, c2Distance (R.rectangle i).function w₀ ≤ C_center * t := by
  classical
  obtain ⟨D, hD1, hfamily⟩ :=
    hasCinematicCurvature_implies_isCinematicFamily hK hcurv
  obtain ⟨C_ct, hC_ct1, hCT⟩ := hCommonTangent K D hK hD1
  set C_center : ℝ := C_ct * Real.rpow 5 C_ct + 6 with hC_center_def
  have hC_center_pos : 0 < C_center := by
    rw [hC_center_def]
    have h : 0 < C_ct * Real.rpow 5 C_ct := by
      apply mul_pos
      · linarith
      · exact Real.rpow_pos_of_pos (by norm_num) _
    linarith
  refine ⟨C_center, hC_center_pos, ?_⟩
  intro i
  have h_pos : 0 < RectangleFamily.tangentCount (R.rectangle i) W 5 := hcounts i
  have h_nonempty : (W.toFinset.filter fun w =>
      (R.rectangle i).IsLambdaTangent w 5).Nonempty :=
    Finset.card_pos.mp h_pos
  rcases h_nonempty with ⟨w_i, hwi⟩
  have hwiW : w_i ∈ W.carrier :=
    W.finite.mem_toFinset.mp (Finset.mem_filter.mp hwi).1
  have hwi_tan : (R.rectangle i).IsLambdaTangent w_i 5 :=
    (Finset.mem_filter.mp hwi).2
  by_cases h_eq : (R.rectangle i).function = w_i
  · have hdist_wi : dist w_i w₀ ≤ 6 * t := hdiam hwiW hw₀
    have h_c2dist : c2Distance w_i w₀ ≤ 6 * t := by
      have h : c2Distance w_i w₀ = dist w_i w₀ := by rfl
      rw [h]
      exact hdist_wi
    have h_rpow_pos : 0 < C_ct * Real.rpow 5 C_ct := by
      apply mul_pos
      · linarith
      · exact Real.rpow_pos_of_pos (by norm_num) _
    have h6 : 6 * t ≤ C_center * t := by
      have hC6 : 6 ≤ C_center := by
        rw [hC_center_def]
        linarith [h_rpow_pos]
      have ht_pos : 0 < t := lt_of_lt_of_le hdelta hdt
      exact mul_le_mul_of_nonneg_right hC6 ht_pos.le
    have h_final : c2Distance (R.rectangle i).function w₀ ≤ C_center * t := by
      rw [h_eq]
      exact h_c2dist.trans h6
    exact h_final
  · have hRt_self : (R.rectangle i).IsLambdaTangent (R.rectangle i).function 5 := by
      intro p hp
      have h : |p.2 - (R.rectangle i).function p.1| ≤ delta := hp.2
      exact h.trans (by linarith [hdelta])
    have hbound :
        (tangencyParameterOn I (R.rectangle i).function w_i + delta) *
          c2Distance (R.rectangle i).function w_i ≤
        C_ct * Real.rpow 5 C_ct * delta * t :=
      hCT 5 (by norm_num) family hfamily I hI delta t hdelta hdt ht1
        (R.rectangle i) (hRfam i) (hRquarter i)
        (R.rectangle i).function (hRfam i) w_i (hW hwiW) h_eq
        hRt_self hwi_tan
    have htp_nonneg : 0 ≤ tangencyParameterOn I (R.rectangle i).function w_i :=
      tangencyParameterOn_nonneg
    have hnonneg : 0 ≤ c2Distance (R.rectangle i).function w_i := dist_nonneg
    have h1 : c2Distance (R.rectangle i).function w_i ≤
        C_ct * Real.rpow 5 C_ct * t := by
      have h2 : delta * c2Distance (R.rectangle i).function w_i ≤
          (tangencyParameterOn I (R.rectangle i).function w_i + delta) *
            c2Distance (R.rectangle i).function w_i := by
        gcongr <;> linarith
      have h3 : delta * c2Distance (R.rectangle i).function w_i ≤
          C_ct * Real.rpow 5 C_ct * delta * t :=
        h2.trans hbound
      calc
        c2Distance (R.rectangle i).function w_i
          = (delta * c2Distance (R.rectangle i).function w_i) / delta := by
            field_simp [hdelta.ne'] <;> ring
        _ ≤ (C_ct * Real.rpow 5 C_ct * delta * t) / delta := by gcongr
        _ = C_ct * Real.rpow 5 C_ct * t := by
            field_simp [hdelta.ne'] <;> ring
    have hdist_wi : dist w_i w₀ ≤ 6 * t := hdiam hwiW hw₀
    have h_c2dist : c2Distance w_i w₀ ≤ 6 * t := by
      have h : c2Distance w_i w₀ = dist w_i w₀ := by rfl
      rw [h]; exact hdist_wi
    calc
      c2Distance (R.rectangle i).function w₀ ≤
          c2Distance (R.rectangle i).function w_i + c2Distance w_i w₀ :=
        dist_triangle _ _ _
      _ ≤ C_ct * Real.rpow 5 C_ct * t + 6 * t := by gcongr
      _ = C_center * t := by
        rw [hC_center_def] <;> ring

end Kakeya.Cinematic

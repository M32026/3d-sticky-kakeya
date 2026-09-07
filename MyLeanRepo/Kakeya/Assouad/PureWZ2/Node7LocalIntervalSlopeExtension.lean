import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeJetExtension

/-!
# A local-to-global representation adapter for Node 7 slopes

The mathematical hypotheses and conclusions remain interval-local.  This
file only supplies the globally `C²` representative required by the legacy
`SlopeFunction` bundle, while preserving the complete two-jet on the chosen
compact interval.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set
open scoped Interval

structure PureWZ2Node7LocalIntervalSlopeExtensionData
    (source : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) where
  slope : SlopeFunction
  eq_on : ∀ x ∈ Set.Icc a b, slope x = source x
  deriv_eq_on : ∀ x ∈ Set.Icc a b, deriv slope x = deriv source x
  second_deriv_eq_on : ∀ x ∈ Set.Icc a b,
    deriv (deriv slope) x = deriv (deriv source) x
  second_deriv_eq_proj : ∀ x : ℝ,
    deriv (deriv slope) x =
      deriv (deriv source) (Set.projIcc a b hab x)
  deriv_sub_proj_eq_integral : ∀ x : ℝ,
    deriv slope x - deriv source (Set.projIcc a b hab x) =
      ∫ u in (Set.projIcc a b hab x : ℝ)..x,
        deriv (deriv source) (Set.projIcc a b hab u)

/-- Extend a locally `C²` real function from a compact interval.  No claim is
made about the extension outside the interval beyond the global regularity
stored by `SlopeFunction`. -/
theorem pureWZ2_node7_localIntervalSlopeExtension
    (source : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hsmooth : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 source x) :
    Nonempty (PureWZ2Node7LocalIntervalSlopeExtensionData source a b hab) := by
  let interval : Set ℝ := Set.Icc a b
  have hsourceOn : ContDiffOn ℝ 2 source interval :=
    fun x hx => (hsmooth x hx).contDiffWithinAt
  have hsourceDerivOn : ContDiffOn ℝ 1 (deriv source) interval := by
    intro x hx
    exact ((hsmooth x hx).derivWithin (m := 1) (by norm_num)).contDiffWithinAt
  let curvatureCore : Set.Icc a b → ℝ :=
    fun x => deriv (deriv source) x.1
  have hcurvatureCore : Continuous curvatureCore := by
    have hsecondOn : ContinuousOn (deriv (deriv source)) interval := by
      intro x hx
      exact ((hsmooth x hx).derivWithin (m := 1) (by norm_num))
        |>.derivWithin (m := 0) (by norm_num) |>.continuousAt
        |>.continuousWithinAt
    exact continuousOn_iff_continuous_restrict.mp hsecondOn
  let curvature : ℝ → ℝ := Set.IccExtend hab curvatureCore
  have hcurvature : Continuous curvature := hcurvatureCore.Icc_extend'
  let first : ℝ → ℝ := fun x =>
    deriv source a + ∫ u in a..x, curvature u
  have hfirstHasDeriv : ∀ x, HasDerivAt first (curvature x) x := by
    intro x
    exact (hcurvature.integral_hasStrictDerivAt a x).hasDerivAt.const_add _
  have hfirstDifferentiable : Differentiable ℝ first :=
    fun x => (hfirstHasDeriv x).differentiableAt
  have hfirstDeriv : deriv first = curvature := by
    funext x
    exact (hfirstHasDeriv x).deriv
  have hfirstContDiff : ContDiff ℝ 1 first := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hfirstDifferentiable, hfirstDeriv ▸ hcurvature⟩
  let extended : ℝ → ℝ := fun x =>
    source a + ∫ u in a..x, first u
  have hextendedHasDeriv : ∀ x, HasDerivAt extended (first x) x := by
    intro x
    exact (hfirstContDiff.continuous.integral_hasStrictDerivAt a x)
      |>.hasDerivAt.const_add _
  have hextendedDifferentiable : Differentiable ℝ extended :=
    fun x => (hextendedHasDeriv x).differentiableAt
  have hextendedDeriv : deriv extended = first := by
    funext x
    exact (hextendedHasDeriv x).deriv
  have hextendedContDiff : ContDiff ℝ 2 extended := by
    apply (contDiff_succ_iff_deriv (n := 1)).2
    refine ⟨hextendedDifferentiable, by simp, ?_⟩
    simpa only [hextendedDeriv] using hfirstContDiff
  let slope : SlopeFunction := ⟨extended, hextendedContDiff⟩
  have hcurvatureEq : ∀ x ∈ Set.Icc a b,
      curvature x = deriv (deriv source) x := by
    intro x hx
    simpa [curvature, curvatureCore] using
      Set.IccExtend_of_mem hab curvatureCore hx
  have hfirstEq : ∀ x ∈ Set.Icc a b, first x = deriv source x := by
    intro x hx
    have hsegment : Set.uIcc a x ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ hx
    have hintegralCongr :
        (∫ u in a..x, curvature u) =
          ∫ u in a..x, deriv (deriv source) u := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hcurvatureEq u (hsegment hu)
    have hFTC : (∫ u in a..x, deriv (deriv source) u) =
        deriv source x - deriv source a := by
      apply intervalIntegral.integral_deriv_of_contDiffOn_Icc
      · exact hsourceDerivOn.mono (Set.Icc_subset_Icc le_rfl hx.2)
      · exact hx.1
    dsimp only [first]
    rw [hintegralCongr, hFTC]
    ring
  have hextendedEq : ∀ x ∈ Set.Icc a b, extended x = source x := by
    intro x hx
    have hsegment : Set.uIcc a x ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ hx
    have hintegralCongr :
        (∫ u in a..x, first u) = ∫ u in a..x, deriv source u := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hfirstEq u (hsegment hu)
    have hFTC : (∫ u in a..x, deriv source u) =
        source x - source a := by
      apply intervalIntegral.integral_deriv_of_contDiffOn_Icc
      · exact (hsourceOn.of_le (by norm_num)).mono
          (Set.Icc_subset_Icc le_rfl hx.2)
      · exact hx.1
    dsimp only [extended]
    rw [hintegralCongr, hFTC]
    ring
  have hsecondProj : ∀ x : ℝ,
      deriv (deriv extended) x =
        deriv (deriv source) (Set.projIcc a b hab x) := by
    intro x
    rw [hextendedDeriv, hfirstDeriv]
    rfl
  have hderivIntegral : ∀ x : ℝ,
      deriv extended x - deriv source (Set.projIcc a b hab x) =
        ∫ u in (Set.projIcc a b hab x : ℝ)..x,
          deriv (deriv source) (Set.projIcc a b hab u) := by
    intro x
    let projected : ℝ := Set.projIcc a b hab x
    have hprojected : projected ∈ Set.Icc a b :=
      (Set.projIcc a b hab x).property
    change deriv extended x - deriv source projected = _
    rw [hextendedDeriv]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hcurvature.intervalIntegrable a projected)
      (hcurvature.intervalIntegrable projected x)
    change first x - deriv source projected =
      ∫ u in projected..x, curvature u
    rw [← hfirstEq projected hprojected]
    dsimp only [first]
    linarith
  exact ⟨{
    slope := slope
    eq_on := fun x hx => hextendedEq x hx
    deriv_eq_on := fun x hx => by
      change deriv extended x = deriv source x
      rw [hextendedDeriv]
      exact hfirstEq x hx
    second_deriv_eq_on := fun x hx => by
      change deriv (deriv extended) x = deriv (deriv source) x
      rw [hextendedDeriv, hfirstDeriv]
      exact hcurvatureEq x hx
    second_deriv_eq_proj := hsecondProj
    deriv_sub_proj_eq_integral := hderivIntegral
  }⟩

namespace PureWZ2Node7LocalIntervalSlopeExtensionData

theorem second_deriv_abs_le
    {source : ℝ → ℝ} {a b K : ℝ} {hab : a ≤ b}
    (data : PureWZ2Node7LocalIntervalSlopeExtensionData source a b hab)
    (hcurvature : ∀ x ∈ Set.Icc a b,
      |deriv (deriv source) x| ≤ K) (x : ℝ) :
    |deriv (deriv data.slope) x| ≤ K := by
  rw [data.second_deriv_eq_proj]
  exact hcurvature _ (Set.projIcc a b hab x).property

theorem deriv_sub_proj_abs_le
    {source : ℝ → ℝ} {a b K : ℝ} {hab : a ≤ b}
    (data : PureWZ2Node7LocalIntervalSlopeExtensionData source a b hab)
    (hcurvature : ∀ x ∈ Set.Icc a b,
      |deriv (deriv source) x| ≤ K) (x : ℝ) :
    |deriv data.slope x -
        deriv source (Set.projIcc a b hab x)| ≤
      K * |x - Set.projIcc a b hab x| := by
  rw [data.deriv_sub_proj_eq_integral]
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (Set.projIcc a b hab x : ℝ)) (b := x) (C := K)
    (f := fun u : ℝ => deriv (deriv source) (Set.projIcc a b hab u))
    (fun u _hu => by
      simpa only [Real.norm_eq_abs] using
        hcurvature (Set.projIcc a b hab u)
          (Set.projIcc a b hab u).property)
  simpa only [Real.norm_eq_abs, abs_sub_comm] using hintegral

end PureWZ2Node7LocalIntervalSlopeExtensionData

end Kakeya.Assouad

end

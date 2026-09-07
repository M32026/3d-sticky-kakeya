import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Exact C2 extension from a compact interval

The bump extension in `IntervalSlopeExtension` is useful when only local
agreement matters, but multiplication by a cutoff does not preserve a lower
bound for the first derivative.  Here we extend the second derivative
constantly beyond a compact interval and integrate twice.  The resulting
global `SlopeFunction` has exactly the same value, first derivative, and
second derivative on the original interval.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set
open scoped Interval

/-- Projection to a real interval is no farther from a point than any point
already lying in that interval. -/
theorem abs_sub_projIcc_le_of_mem
    {a b x y : ℝ} (hab : a ≤ b) (hy : y ∈ Set.Icc a b) :
    |x - (Set.projIcc a b hab x : ℝ)| ≤ |x - y| := by
  by_cases hleft : x ≤ a
  · rw [Set.projIcc_of_le_left hab hleft]
    rw [abs_of_nonpos (sub_nonpos.mpr hleft),
      abs_of_nonpos (sub_nonpos.mpr (hleft.trans hy.1))]
    linarith [hy.1]
  by_cases hright : b ≤ x
  · rw [Set.projIcc_of_right_le hab hright]
    rw [abs_of_nonneg (sub_nonneg.mpr hright),
      abs_of_nonneg (sub_nonneg.mpr (hy.2.trans hright))]
    linarith [hy.2]
  · have hx : x ∈ Set.Icc a b :=
      ⟨le_of_not_ge hleft, le_of_not_ge hright⟩
    rw [Set.projIcc_of_mem hab hx]
    simp

/-- The integral jet extension together with its global curvature formula. -/
structure PureWZ2IntervalSlopeJetExtensionData
    (source : SlopeFunction) (a b : ℝ) (hab : a ≤ b)
    extends PureWZ2IntervalSlopeExtensionData source (Set.Icc a b) where
  second_deriv_eq_proj : ∀ x : ℝ,
    deriv (deriv slope) x =
      deriv (deriv source) (Set.projIcc a b hab x)
  deriv_sub_proj_eq_integral : ∀ x : ℝ,
    deriv slope x - deriv source (Set.projIcc a b hab x) =
      ∫ u in (Set.projIcc a b hab x : ℝ)..x,
        deriv (deriv source) (Set.projIcc a b hab u)

/-- Extend the second derivative of a global C2 source constantly beyond
`[a,b]`, then integrate twice from `a`.  This is a quantitative-friendly
extension: outside the core its second derivative is one of the two endpoint
values rather than a cutoff error. -/
theorem pureWZ2_intervalSlopeJetExtension
    (source : SlopeFunction) {a b : ℝ} (hab : a ≤ b) :
    Nonempty (PureWZ2IntervalSlopeJetExtensionData source a b hab) := by
  let curvatureCore : Set.Icc a b → ℝ :=
    fun x => deriv (deriv source) x.1
  have hsourceDeriv : ContDiff ℝ 1 (deriv source) := by
    exact ((contDiff_succ_iff_deriv (n := 1)).mp source.contDiff).2.2
  have hcurvatureCore : Continuous curvatureCore := by
    exact hsourceDeriv.continuous_deriv_one.comp continuous_subtype_val
  let curvature : ℝ → ℝ := Set.IccExtend hab curvatureCore
  have hcurvature : Continuous curvature := by
    exact hcurvatureCore.Icc_extend'
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
    exact (hfirstContDiff.continuous.integral_hasStrictDerivAt a x).hasDerivAt.const_add _
  have hextendedDifferentiable : Differentiable ℝ extended :=
    fun x => (hextendedHasDeriv x).differentiableAt
  have hextendedDeriv : deriv extended = first := by
    funext x
    exact (hextendedHasDeriv x).deriv
  have hextendedContDiff : ContDiff ℝ 2 extended := by
    apply (contDiff_succ_iff_deriv (n := 1)).2
    refine ⟨hextendedDifferentiable, by simp, ?_⟩
    simpa only [hextendedDeriv] using hfirstContDiff
  let slope : SlopeFunction :=
    { toFun := extended
      contDiff := hextendedContDiff }
  have hcurvatureEq : ∀ x ∈ Set.Icc a b,
      curvature x = deriv (deriv source) x := by
    intro x hx
    simpa [curvature, curvatureCore] using
      Set.IccExtend_of_mem hab curvatureCore hx
  have hfirstEq : ∀ x ∈ Set.Icc a b, first x = deriv source x := by
    intro x hx
    have hinterval : Set.uIcc a x ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ hx
    have hintegralCongr :
        (∫ u in a..x, curvature u) =
          ∫ u in a..x, deriv (deriv source) u := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hcurvatureEq u (hinterval hu)
    have hFTC : (∫ u in a..x, deriv (deriv source) u) =
        deriv source x - deriv source a := by
      apply intervalIntegral.integral_deriv_of_contDiffOn_Icc
      · exact hsourceDeriv.contDiffOn.mono (Set.Icc_subset_Icc le_rfl hx.2)
      · exact hx.1
    dsimp only [first]
    rw [hintegralCongr, hFTC]
    ring
  have hextendedEq : ∀ x ∈ Set.Icc a b, extended x = source x := by
    intro x hx
    have hinterval : Set.uIcc a x ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ hx
    have hintegralCongr :
        (∫ u in a..x, first u) = ∫ u in a..x, deriv source u := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hfirstEq u (hinterval hu)
    have hFTC : (∫ u in a..x, deriv source u) = source x - source a := by
      apply intervalIntegral.integral_deriv_of_contDiffOn_Icc
      · exact (source.contDiff.of_le (by norm_num)).contDiffOn.mono
          (Set.Icc_subset_Icc le_rfl hx.2)
      · exact hx.1
    dsimp only [extended]
    rw [hintegralCongr, hFTC]
    ring
  refine ⟨{
    slope := slope
    eq_on := ?_
    deriv_eq_on := ?_
    second_deriv_eq_on := ?_
    second_deriv_eq_proj := ?_
    deriv_sub_proj_eq_integral := ?_
  }⟩
  · intro x hx
    exact hextendedEq x hx
  · intro x hx
    change deriv extended x = deriv source x
    rw [hextendedDeriv]
    exact hfirstEq x hx
  · intro x hx
    change deriv (deriv extended) x = deriv (deriv source) x
    rw [hextendedDeriv, hfirstDeriv]
    exact hcurvatureEq x hx
  · intro x
    change deriv (deriv extended) x = _
    rw [hextendedDeriv, hfirstDeriv]
    change curvature x = _
    rfl
  · intro x
    let projected : ℝ := Set.projIcc a b hab x
    have hprojected : projected ∈ Set.Icc a b :=
      (Set.projIcc a b hab x).property
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hcurvature.intervalIntegrable a projected)
      (hcurvature.intervalIntegrable projected x)
    change deriv extended x - _ = _
    rw [hextendedDeriv]
    change first x - deriv source projected =
      ∫ u in projected..x, curvature u
    rw [← hfirstEq projected hprojected]
    dsimp only [first]
    linarith

namespace PureWZ2IntervalSlopeJetExtensionData

/-- The first derivative of the jet extension differs from the derivative at
the clamped core point by at most curvature times distance. -/
theorem deriv_sub_proj_abs_le
    {source : SlopeFunction} {a b K : ℝ} {hab : a ≤ b}
    (data : PureWZ2IntervalSlopeJetExtensionData source a b hab)
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

/-- The extension has the same curvature bound everywhere as the source has
on the compact core. -/
theorem second_deriv_abs_le
    {source : SlopeFunction} {a b K : ℝ} {hab : a ≤ b}
    (data : PureWZ2IntervalSlopeJetExtensionData source a b hab)
    (hcurvature : ∀ x ∈ Set.Icc a b,
      |deriv (deriv source) x| ≤ K) (x : ℝ) :
    |deriv (deriv data.slope) x| ≤ K := by
  rw [data.second_deriv_eq_proj]
  exact hcurvature _ (Set.projIcc a b hab x).property

end PureWZ2IntervalSlopeJetExtensionData

end Kakeya.Assouad

end

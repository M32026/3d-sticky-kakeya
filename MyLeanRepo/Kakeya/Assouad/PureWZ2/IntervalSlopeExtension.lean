import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# A global internal representative of an interval-local C2 slope

Node 5 exposes only a function on `[-1,1]` together with an ambient function
which is C2 on that interval.  Downstream affine geometry uses the bundled
`SlopeFunction` type for convenience.  This file bridges the two without
strengthening the public Node-5 interface: a smooth cutoff makes the ambient
representative globally C2 and is identically one on the smaller interval
actually used by the construction.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A globally C2 internal witness which agrees, together with its first two
derivatives, with an interval-local representative on one compact core. -/
structure PureWZ2IntervalSlopeExtensionData
    (source : ℝ → ℝ) (core : Set ℝ) where
  slope : SlopeFunction
  eq_on : ∀ x ∈ core, slope x = source x
  deriv_eq_on : ∀ x ∈ core, deriv slope x = deriv source x
  second_deriv_eq_on :
    ∀ x ∈ core, deriv (deriv slope) x = deriv (deriv source) x

/-- A genuine globally smooth representative of a paper slope.  Only the
values on the paper interval are identified with the originally chosen
ambient representative.  At the endpoints, the derivatives of the new
representative are the one-sided derivatives determined by `ContDiffOn`;
they need not equal Lean's ordinary derivative of the original ambient
function. -/
structure PureWZ2GlobalizedPaperSlopeData (source : ℝ → ℝ) where
  slope : SlopeFunction
  eq_on : ∀ x ∈ Set.Icc (-1 : ℝ) 1, slope x = source x
  normalized : slope.IsNormalized

/-- Multiply an interval-local C2 representative by a smooth bump which is
one near the working core and supported in the public interval. -/
theorem pureWZ2_intervalSlopeExtension
    (source : ℝ → ℝ) (core : Set ℝ)
    (center innerRadius outerRadius : ℝ)
    (hinner : 0 < innerRadius)
    (houter : innerRadius < outerRadius)
    (hcore : core ⊆ Metric.ball center innerRadius)
    (hsupport : Metric.closedBall center outerRadius ⊆
      Set.Ioo (-1 : ℝ) 1)
    (hsmooth : ContDiffOn ℝ 2 source (Set.Icc (-1 : ℝ) 1)) :
    Nonempty (PureWZ2IntervalSlopeExtensionData source core) := by
  let bump : ContDiffBump center :=
    { rIn := innerRadius
      rOut := outerRadius
      rIn_pos := hinner
      rIn_lt_rOut := houter }
  let extended : ℝ → ℝ := fun x => bump x * source x
  have hextended : ContDiff ℝ 2 extended := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall center outerRadius
    · have hxInterval := hsupport hx
      have hsourceAt : ContDiffAt ℝ 2 source x :=
        hsmooth.contDiffAt (Icc_mem_nhds hxInterval.1 hxInterval.2)
      exact bump.contDiffAt.mul hsourceAt
    · have hxSupport : x ∉ tsupport (bump : ℝ → ℝ) := by
        rw [bump.tsupport_eq]
        exact hx
      have hbumpZero : (bump : ℝ → ℝ) =ᶠ[nhds x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hxSupport
      have hextendedZero : extended =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [hbumpZero] with y hy
        simp [extended, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hextendedZero
  let slope : SlopeFunction :=
    { toFun := extended
      contDiff := hextended }
  have heqNear : ∀ x ∈ core, slope =ᶠ[nhds x] source := by
    intro x hx
    have hxBall : x ∈ Metric.ball center innerRadius := hcore hx
    have hbumpOne : (bump : ℝ → ℝ) =ᶠ[nhds x] 1 :=
      bump.eventuallyEq_one_of_mem_ball hxBall
    filter_upwards [hbumpOne] with y hy
    simp [slope, extended, hy]
  exact ⟨{
    slope := slope
    eq_on := fun x hx => (heqNear x hx).self_of_nhds
    deriv_eq_on := fun x hx => (heqNear x hx).deriv_eq
    second_deriv_eq_on := fun x hx =>
      ((heqNear x hx).deriv).deriv_eq
  }⟩

/-- The interval-local C2 witness carried by a paper-facing C2 grain
configuration can be globalized on any compact core strictly inside the
paper height interval.  Only equality of the two-jet on that core is claimed.
-/
theorem PureWZ2C2GlobalGrainData.intervalSlopeExtension
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C)
    (core : Set ℝ) (center innerRadius outerRadius : ℝ)
    (hinner : 0 < innerRadius)
    (houter : innerRadius < outerRadius)
    (hcore : core ⊆ Metric.ball center innerRadius)
    (hsupport : Metric.closedBall center outerRadius ⊆
      Set.Ioo (-1 : ℝ) 1) :
    Nonempty (PureWZ2IntervalSlopeExtensionData data.slope core) :=
  pureWZ2_intervalSlopeExtension data.slope core center innerRadius outerRadius
    hinner houter hcore hsupport data.slope_contDiffOn

/-- Globalize an interval-local normalized `C²` representative by extending
its relative second derivative constantly beyond `[-1,1]` and integrating
twice.  This is the Node-6 bridge from the literal paper interface to the
globally bundled calculus used by the affine backend. -/
theorem pureWZ2_globalizePaperSlope
    (source : ℝ → ℝ)
    (hsmooth : ContDiffOn ℝ 2 source (Set.Icc (-1 : ℝ) 1))
    (hnormalized : PureWZ2AmbientSlopeIsNormalized source) :
    Nonempty (PureWZ2GlobalizedPaperSlopeData source) := by
  let interval : Set ℝ := Set.Icc (-1 : ℝ) 1
  let first : ℝ → ℝ := derivWithin source interval
  have hintervalUnique : UniqueDiffOn ℝ interval := by
    simpa [interval] using uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)
  have hfirstContDiff : ContDiffOn ℝ 1 first interval := by
    dsimp only [first]
    exact hsmooth.derivWithin hintervalUnique (by norm_num)
  have hfirstContinuous : ContinuousOn first interval :=
    hfirstContDiff.continuousOn
  let secondCore : Set.Icc (-1 : ℝ) 1 → ℝ := fun x =>
    derivWithin first interval x.1
  have hsecondCoreContinuous : Continuous secondCore := by
    exact continuousOn_iff_continuous_restrict.mp
      (hfirstContDiff.continuousOn_derivWithin hintervalUnique
        (by norm_num))
  let curvature : ℝ → ℝ :=
    Set.IccExtend (by norm_num : (-1 : ℝ) ≤ 1) secondCore
  have hcurvatureContinuous : Continuous curvature := by
    exact hsecondCoreContinuous.Icc_extend'
  let globalFirst : ℝ → ℝ := fun x =>
    first (-1) + ∫ u in (-1 : ℝ)..x, curvature u
  have hglobalFirstHasDeriv : ∀ x, HasDerivAt globalFirst (curvature x) x := by
    intro x
    exact (hcurvatureContinuous.integral_hasStrictDerivAt (-1) x).hasDerivAt.const_add _
  have hglobalFirstDifferentiable : Differentiable ℝ globalFirst :=
    fun x => (hglobalFirstHasDeriv x).differentiableAt
  have hglobalFirstDeriv : deriv globalFirst = curvature := by
    funext x
    exact (hglobalFirstHasDeriv x).deriv
  have hglobalFirstContDiff : ContDiff ℝ 1 globalFirst := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hglobalFirstDifferentiable, hglobalFirstDeriv ▸ hcurvatureContinuous⟩
  let extended : ℝ → ℝ := fun x =>
    source (-1) + ∫ u in (-1 : ℝ)..x, globalFirst u
  have hextendedHasDeriv : ∀ x, HasDerivAt extended (globalFirst x) x := by
    intro x
    exact (hglobalFirstContDiff.continuous.integral_hasStrictDerivAt (-1) x).hasDerivAt.const_add _
  have hextendedDifferentiable : Differentiable ℝ extended :=
    fun x => (hextendedHasDeriv x).differentiableAt
  have hextendedDeriv : deriv extended = globalFirst := by
    funext x
    exact (hextendedHasDeriv x).deriv
  have hextendedContDiff : ContDiff ℝ 2 extended := by
    apply (contDiff_succ_iff_deriv (n := 1)).2
    refine ⟨hextendedDifferentiable, by simp, ?_⟩
    simpa only [hextendedDeriv] using hglobalFirstContDiff
  have hcurvatureEq : ∀ x ∈ interval, curvature x = derivWithin first interval x := by
    intro x hx
    simpa [curvature, secondCore, interval] using
      Set.IccExtend_of_mem (by norm_num : (-1 : ℝ) ≤ 1) secondCore hx
  have hglobalFirstEq : ∀ x ∈ interval, globalFirst x = first x := by
    intro x hx
    rcases hx.1.eq_or_lt with hleft | hleft
    · subst x
      simp [globalFirst]
    let segment : Set ℝ := Set.Icc (-1 : ℝ) x
    have hsegment : segment ⊆ interval := by
      intro u hu
      exact ⟨hu.1, hu.2.trans hx.2⟩
    have hsegmentUnique : UniqueDiffOn ℝ segment := by
      simpa [segment] using uniqueDiffOn_Icc hleft
    have hintegral : (∫ u in (-1 : ℝ)..x, curvature u) =
        ∫ u in (-1 : ℝ)..x, derivWithin first segment u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ segment := by
        simpa [segment, Set.uIcc_of_le hleft.le] using hu
      rw [hcurvatureEq u (hsegment hu')]
      exact (derivWithin_subset hsegment
        (hsegmentUnique u hu')
        ((hfirstContDiff u (hsegment hu')).differentiableWithinAt
          (by norm_num))).symm
    have hFTC : (∫ u in (-1 : ℝ)..x, derivWithin first segment u) =
        first x - first (-1) := by
      exact intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
        (hfirstContDiff.mono hsegment)
        hleft.le
    dsimp only [globalFirst]
    rw [hintegral, hFTC]
    ring
  have hextendedEq : ∀ x ∈ interval, extended x = source x := by
    intro x hx
    rcases hx.1.eq_or_lt with hleft | hleft
    · subst x
      simp [extended]
    let segment : Set ℝ := Set.Icc (-1 : ℝ) x
    have hsegment : segment ⊆ interval := by
      intro u hu
      exact ⟨hu.1, hu.2.trans hx.2⟩
    have hsegmentUnique : UniqueDiffOn ℝ segment := by
      simpa [segment] using uniqueDiffOn_Icc hleft
    have hintegral : (∫ u in (-1 : ℝ)..x, globalFirst u) =
        ∫ u in (-1 : ℝ)..x, derivWithin source segment u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ segment := by
        simpa [segment, Set.uIcc_of_le hleft.le] using hu
      rw [hglobalFirstEq u (hsegment hu')]
      exact (derivWithin_subset hsegment
        (hsegmentUnique u hu')
        ((hsmooth u (hsegment hu')).differentiableWithinAt
          (by norm_num))).symm
    have hFTC : (∫ u in (-1 : ℝ)..x, derivWithin source segment u) =
        source x - source (-1) := by
      exact intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
        ((hsmooth.of_le (by norm_num)).mono hsegment) hleft.le
    dsimp only [extended]
    rw [hintegral, hFTC]
    ring
  have hfirstInterior : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, |first x| ≤ 1 := by
    intro x hx
    have hnhds : interval ∈ nhds x := by
      exact Icc_mem_nhds hx.1 hx.2
    rw [show first x = deriv source x by
      dsimp only [first]
      exact derivWithin_of_mem_nhds hnhds]
    exact (hnormalized x ⟨hx.1.le, hx.2.le⟩).2.1
  have hfirstBound : ∀ x ∈ interval, |first x| ≤ 1 := by
    intro x hx
    apply le_on_closure hfirstInterior
    · simpa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), interval] using
        hfirstContinuous.abs
    · exact continuousOn_const
    · simpa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), interval] using hx
  have hsecondContinuous : ContinuousOn (fun x => derivWithin first interval x) interval :=
    hfirstContDiff.continuousOn_derivWithin hintervalUnique (by norm_num)
  have hsecondInterior : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      |derivWithin first interval x| ≤ 1 := by
    intro x hx
    have hnhds : interval ∈ nhds x := Icc_mem_nhds hx.1 hx.2
    have heventually : first =ᶠ[nhds x] deriv source := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      dsimp only [first]
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
    rw [derivWithin_of_mem_nhds hnhds, heventually.deriv_eq]
    exact (hnormalized x ⟨hx.1.le, hx.2.le⟩).2.2
  have hsecondBound : ∀ x ∈ interval, |derivWithin first interval x| ≤ 1 := by
    intro x hx
    apply le_on_closure hsecondInterior
    · simpa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), interval] using
        hsecondContinuous.abs
    · exact continuousOn_const
    · simpa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), interval] using hx
  let slope : SlopeFunction :=
    { toFun := extended
      contDiff := hextendedContDiff }
  refine ⟨{
    slope := slope
    eq_on := fun x hx => hextendedEq x hx
    normalized := ?_
  }⟩
  intro x hx
  have hvalue : |slope x| ≤ 1 := by
    rw [show slope x = source x by exact hextendedEq x hx]
    exact (hnormalized x hx).1
  have hfirstEqAt : deriv slope x = first x := by
    calc
      deriv slope x = globalFirst x := by
        change deriv extended x = globalFirst x
        exact congrFun hextendedDeriv x
      _ = first x := hglobalFirstEq x hx
  have hsecondEq : deriv (deriv slope) x = derivWithin first interval x := by
    change deriv (deriv extended) x = derivWithin first interval x
    rw [hextendedDeriv, hglobalFirstDeriv]
    exact hcurvatureEq x hx
  exact ⟨hvalue, by rw [hfirstEqAt]; exact hfirstBound x hx, by
    rw [hsecondEq]
    exact hsecondBound x hx⟩

/-- Canonical Node-6 global representative of the public C2 grain slope. -/
theorem PureWZ2C2GlobalGrainData.globalizedSlope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C) :
    Nonempty (PureWZ2GlobalizedPaperSlopeData data.slope) :=
  pureWZ2_globalizePaperSlope data.slope data.slope_contDiffOn
    data.slope_normalized

end Kakeya.Assouad

end

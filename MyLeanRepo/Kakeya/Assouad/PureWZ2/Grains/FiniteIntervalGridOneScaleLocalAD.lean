import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleLocalGrain
import MyLeanRepo.Kakeya.Assouad.WZ1.MultiScaleAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer

/-!
# Finite interval grid to one-scale local AD

This is the structure-only part of the paper's Lemma 4.11.  At one fixed
outer query scale, a finite family of interval-local covering estimates
between that scale and its square root is assembled into `IsADSet1`.  The
argument is independent of any uniform-tube structure: all geometric
refinements and their mass losses belong in the producer of `hinterval`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- A point-centered projection covering estimate at one resolution and one
spatial radius.  This is the direct output of the dependent Córdoba estimate
before the good-line interval assembly. -/
def PureWZ2PointCenteredCoveringAt
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (resolutionScale : NNReal)
    (spatialRadius : ℝ)
    (constant : ENNReal) : Prop :=
  ∀ point : {point : Point3 // point ∈ shading.union},
    (Metric.externalCoveringNumber resolutionScale
      (scalarProjection (planeMap point)
        (shading.union ∩ Metric.closedBall (point : Point3) spatialRadius)) :
      ENNReal) ≤ constant

/-- Point-centered covering estimates pass to subshadings. -/
lemma pureWZ2PointCenteredCoveringAt_mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source next : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {resolutionScale : NNReal} {spatialRadius : ℝ} {constant : ENNReal}
    (hsub : PaperIsSubshading next source)
    (hcover : PureWZ2PointCenteredCoveringAt source planeMap
      resolutionScale spatialRadius constant) :
    PureWZ2PointCenteredCoveringAt next planeMap
      resolutionScale spatialRadius constant := by
  intro point
  have hpointSource : (point : Point3) ∈ source.union := by
    rcases point.property with ⟨index, hindex⟩
    exact ⟨index, hsub index hindex⟩
  have hset :
      scalarProjection (planeMap point)
          (next.union ∩ Metric.closedBall (point : Point3) spatialRadius) ⊆
        scalarProjection (planeMap point)
          (source.union ∩ Metric.closedBall (point : Point3) spatialRadius) := by
    exact Set.image_mono <| Set.inter_subset_inter_left _ <| by
      rintro other ⟨index, hindex⟩
      exact ⟨index, hsub index hindex⟩
  have hmono :
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
          (next.union ∩ Metric.closedBall (point : Point3) spatialRadius)) :
        ENNReal) ≤
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
          (source.union ∩ Metric.closedBall (point : Point3) spatialRadius)) :
        ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hset
  exact hmono.trans (hcover ⟨point, hpointSource⟩)

/-- Reindex a point-centered covering estimate along a genuine tube
subfamily.  Only the shaded union shrinks; the spatial center, projection
direction, resolution, and radius are unchanged. -/
lemma pureWZ2PointCenteredCoveringAt_restrictSubfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {planeMap : Point3 → Point3}
    {resolutionScale : NNReal} {spatialRadius : ℝ} {constant : ENNReal}
    (hcover : PureWZ2PointCenteredCoveringAt source planeMap
      resolutionScale spatialRadius constant) :
    PureWZ2PointCenteredCoveringAt
      (restrictPaperShading selected source) planeMap
      resolutionScale spatialRadius constant := by
  intro point
  have hpointSource : (point : Point3) ∈ source.union := by
    rcases point.property with ⟨index, hindex⟩
    exact ⟨selected.embedding index, hindex⟩
  have hset :
      scalarProjection (planeMap point)
          ((restrictPaperShading selected source).union ∩
            Metric.closedBall (point : Point3) spatialRadius) ⊆
        scalarProjection (planeMap point)
          (source.union ∩
            Metric.closedBall (point : Point3) spatialRadius) := by
    exact Set.image_mono <| Set.inter_subset_inter_left _ <| by
      rintro other ⟨index, hindex⟩
      exact ⟨selected.embedding index, hindex⟩
  have hmono :
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
          ((restrictPaperShading selected source).union ∩
            Metric.closedBall (point : Point3) spatialRadius)) : ENNReal) ≤
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
          (source.union ∩
            Metric.closedBall (point : Point3) spatialRadius)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hset
  exact hmono.trans (hcover ⟨point, hpointSource⟩)

/-- The interval-localized covering estimate accumulated in the inner
Lemma 4.11 iteration. -/
def PureWZ2IntervalCoveringAt
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (queryScale : ℝ)
    (resolutionScale windowScale : NNReal)
    (constant : ENNReal) : Prop :=
  ∀ point : {point : Point3 // point ∈ shading.union},
    ∀ center : ℝ,
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)) ∩
          Metric.closedBall center (windowScale : ℝ)) : ENNReal) ≤
        constant

/-- Interval covering bounds pass to a subshading without changing any of
the three scale parameters. -/
lemma pureWZ2IntervalCoveringAt_mono
    {delta queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source next : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {resolutionScale windowScale : NNReal}
    {constant : ENNReal}
    (hsub : PaperIsSubshading next source)
    (hcover : PureWZ2IntervalCoveringAt source planeMap queryScale
      resolutionScale windowScale constant) :
    PureWZ2IntervalCoveringAt next planeMap queryScale
      resolutionScale windowScale constant := by
  intro point center
  have hpointSource : (point : Point3) ∈ source.union := by
    rcases point.property with ⟨index, hindex⟩
    exact ⟨index, hsub index hindex⟩
  have hset :
      scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)) ∩
          Metric.closedBall center (windowScale : ℝ) ⊆
        scalarProjection (planeMap point)
            (source.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)) ∩
          Metric.closedBall center (windowScale : ℝ) := by
    rintro value ⟨⟨other, hother, rfl⟩, hvalue⟩
    refine ⟨⟨other, ⟨?_, hother.2⟩, rfl⟩, hvalue⟩
    rcases hother.1 with ⟨index, hindex⟩
    exact ⟨index, hsub index hindex⟩
  have hmono :
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)) ∩
          Metric.closedBall center (windowScale : ℝ)) : ENNReal) ≤
        (Metric.externalCoveringNumber resolutionScale
          (scalarProjection (planeMap point)
              (source.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center (windowScale : ℝ)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hset
  exact hmono.trans (hcover ⟨point, hpointSource⟩ center)

/-- Enlarge the numerical constant in an interval covering estimate. -/
lemma pureWZ2IntervalCoveringAt_mono_constant
    {delta queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {resolutionScale windowScale : NNReal}
    {sourceConstant targetConstant : ENNReal}
    (hconstant : sourceConstant ≤ targetConstant)
    (hcover : PureWZ2IntervalCoveringAt shading planeMap queryScale
      resolutionScale windowScale sourceConstant) :
    PureWZ2IntervalCoveringAt shading planeMap queryScale
      resolutionScale windowScale targetConstant := by
  intro point center
  exact (hcover point center).trans hconstant

/-- Shrinking the spatial localization scale preserves an interval covering
estimate.  This is the bridge from a pair output localized to
`sqrt (scale k)` to the fixed final query ball. -/
lemma pureWZ2IntervalCoveringAt_mono_queryScale
    {delta smallQuery largeQuery : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {resolutionScale windowScale : NNReal}
    {constant : ENNReal}
    (hquery : smallQuery ≤ largeQuery)
    (hcover : PureWZ2IntervalCoveringAt shading planeMap largeQuery
      resolutionScale windowScale constant) :
    PureWZ2IntervalCoveringAt shading planeMap smallQuery
      resolutionScale windowScale constant := by
  intro point center
  have hball : Metric.closedBall (point : Point3)
      (Real.sqrt smallQuery) ⊆
      Metric.closedBall (point : Point3) (Real.sqrt largeQuery) :=
    Metric.closedBall_subset_closedBall (Real.sqrt_le_sqrt hquery)
  have hset :
      scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt smallQuery)) ∩
          Metric.closedBall center (windowScale : ℝ) ⊆
        scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt largeQuery)) ∩
          Metric.closedBall center (windowScale : ℝ) := by
    exact Set.inter_subset_inter
      (Set.image_mono (Set.inter_subset_inter_right _ hball))
      Set.Subset.rfl
  have hmono :
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt smallQuery)) ∩
          Metric.closedBall center (windowScale : ℝ)) : ENNReal) ≤
        (Metric.externalCoveringNumber resolutionScale
          (scalarProjection (planeMap point)
              (shading.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt largeQuery)) ∩
            Metric.closedBall center (windowScale : ℝ)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hset
  exact hmono.trans (hcover point center)

/-- The geometric covering part of one paper-faithful interval output.
`queryScale`, the covering resolution, and the scalar interval radius are
kept independent.  In particular, this interface does not identify the
Lemma 4.11 interval scale with the final `sqrt queryScale` spatial window. -/
structure PureWZ2IntervalCoveringData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (queryScale : ℝ)
    (resolutionScale windowScale : NNReal)
    (constant : ENNReal) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading source
  interval_covering : PureWZ2IntervalCoveringAt shading planeMap queryScale
    resolutionScale windowScale constant

namespace PureWZ2IntervalCoveringData

variable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {queryScale : ℝ}
    {resolutionScale windowScale : NNReal}
    {constant : ENNReal}

/-- An interval covering output survives any later subshading by set
monotonicity, independently of the loss used to restore extremality there. -/
noncomputable def restrict
    (data : PureWZ2IntervalCoveringData (source := source)
      planeMap queryScale resolutionScale windowScale constant)
    (next : WZ1PaperTubeShading family)
    (hnext : PaperIsSubshading next data.shading) :
    PureWZ2IntervalCoveringData (source := source)
      planeMap queryScale resolutionScale windowScale constant where
  shading := next
  subshading := fun index _point hpoint =>
    data.subshading index (hnext index hpoint)
  interval_covering :=
    pureWZ2IntervalCoveringAt_mono hnext data.interval_covering

end PureWZ2IntervalCoveringData

/-- One complete PureWZ2 interval output, consisting of the geometric
covering fact and the freshly restored extremality/CWA state on its shading.
This is the `UniformTubeStructure`-free analogue of
`WZ1LocalGrainIntervalData`. -/
structure PureWZ2IntervalLocalGrainData
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (queryScale : ℝ)
    (resolutionScale windowScale : NNReal)
    (constant : ENNReal)
    extends PureWZ2IntervalCoveringData
      (source := source) planeMap queryScale resolutionScale windowScale
        constant where
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss family shading
  cwa : WZ2PaperConvexWolffBound family
    (Kakeya.realRpowENN delta (-outputLoss))

namespace PureWZ2IntervalLocalGrainData

variable
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {queryScale : ℝ}
    {resolutionScale windowScale : NNReal}
    {constant : ENNReal}

/-- Forget the analytic state and retain the interval bound on a later
subshading. -/
noncomputable def restrictCovering
    (data : PureWZ2IntervalLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss) (source := source)
      planeMap queryScale resolutionScale windowScale constant)
    (next : WZ1PaperTubeShading family)
    (hnext : PaperIsSubshading next data.shading) :
    PureWZ2IntervalCoveringData (source := source)
      planeMap queryScale resolutionScale windowScale constant :=
  data.toPureWZ2IntervalCoveringData.restrict next hnext

end PureWZ2IntervalLocalGrainData

/-- Immediately restore extremality and CWA after a mass-retaining interval
candidate has been selected.  This is the generic final operation required
by every inner Lemma 4.11 pair step. -/
theorem intervalLocalGrain_of_mass_ledger
    {delta sigma inputLoss outputLoss queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source candidate : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    {resolutionScale windowScale : NNReal} {constant : ENNReal}
    (hsourceExtremal :
      WZ2PaperCroppedIsExtremal sigma inputLoss family source)
    (hsourceCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-inputLoss)))
    (hsub : PaperIsSubshading candidate source)
    (hcubical : WZ1PaperIsCubicalShading candidate)
    (hcover : PureWZ2IntervalCoveringAt candidate planeMap queryScale
      resolutionScale windowScale constant)
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossTop : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * source.mass ≤ candidate.mass)
    (hinputOutput : inputLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : massLoss *
      Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta inputLoss) :
    ∃ data : PureWZ2IntervalLocalGrainData
        (sigma := sigma) (outputLoss := outputLoss) (source := source)
        planeMap queryScale resolutionScale windowScale constant,
      data.shading = candidate := by
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss family candidate := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop hsourceExtremal hsub hmass hcubical
      hinputOutput
    · exact hrestore
    · exact hsourceExtremal.delta_pos
    · exact hsourceExtremal.delta_le_one
    · exact houtputLoss
  have hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := source) (_shading2 := candidate)
      hsourceCWA hinputOutput
      hsourceExtremal.delta_pos hsourceExtremal.delta_le_one
  exact ⟨{
    shading := candidate
    subshading := hsub
    interval_covering := hcover
    extremal := hextremal
    cwa := hcwa
  }, rfl⟩

private lemma exists_last_finite_interval_grid_index
    {N k : ℕ} (scale : ℕ → NNReal) {radius : ℝ}
    (hkN : k < N)
    (hscale : (scale k : ℝ) ≤ radius)
    (hradius : radius < (scale N : ℝ)) :
    ∃ j : ℕ,
      k ≤ j ∧ j < N ∧
      (scale j : ℝ) ≤ radius ∧
      radius < (scale (j + 1) : ℝ) := by
  let candidates : Finset ℕ :=
    Finset.filter (fun index => (scale index : ℝ) ≤ radius)
      (Finset.Icc k N)
  have hcandidates : candidates.Nonempty := by
    exact ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, hkN.le⟩, hscale⟩⟩
  let j : ℕ := candidates.max' hcandidates
  have hjmem : j ∈ candidates := Finset.max'_mem candidates hcandidates
  have hjrange : k ≤ j ∧ j ≤ N :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hjmem).1
  have hjscale : (scale j : ℝ) ≤ radius :=
    (Finset.mem_filter.mp hjmem).2
  have hjN : j < N := by
    by_contra hnot
    have hj : j = N := Nat.le_antisymm hjrange.2 (Nat.le_of_not_gt hnot)
    rw [hj] at hjscale
    linarith
  have hradiusNext : radius < (scale (j + 1) : ℝ) := by
    by_contra hnot
    have hnextScale : (scale (j + 1) : ℝ) ≤ radius := le_of_not_gt hnot
    have hnextMem : j + 1 ∈ candidates := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr
          ⟨hjrange.1.trans (Nat.le_succ j), Nat.succ_le_iff.mpr hjN⟩,
          hnextScale⟩
    exact (Nat.not_succ_le_self j)
      (Finset.le_max' candidates (j + 1) hnextMem)
  exact ⟨j, hjrange.1, hjN, hjscale, hradiusNext⟩

/-- Discrete interval estimates for every grid pair imply the continuous
interval estimate consumed by `multiscale_to_ad_set`.  The sole interpolation
cost is one adjacent grid ratio. -/
lemma finite_interval_grid_bounds_to_continuous
    {delta discreteLoss continuousLoss ratio alpha queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (N : ℕ) (scale : ℕ → NNReal)
    (hdelta : 0 < delta)
    (halpha : 0 < alpha)
    (hratio : 1 ≤ ratio)
    (hscaleTop : (scale N : ℝ) = Real.sqrt queryScale)
    (hscalePos : ∀ index, index ≤ N → 0 < (scale index : ℝ))
    (hscaleRatio : ∀ index, index < N →
      (scale (index + 1) : ℝ) ≤ ratio * (scale index : ℝ))
    (habsorb : Real.rpow delta (-discreteLoss) * ratio ^ alpha ≤
      Real.rpow delta (-continuousLoss))
    (hdiscrete : ∀ k j, k < j → j ≤ N →
      PureWZ2IntervalCoveringAt shading planeMap queryScale
        (scale k) (scale j)
        (ENNReal.ofReal
          (Real.rpow delta (-discreteLoss) *
            Real.rpow ((scale j : ℝ) / (scale k : ℝ)) alpha))) :
    ∀ point : {point : Point3 // point ∈ shading.union},
      ∀ k, k < N → ∀ radius : ℝ,
        (scale k : ℝ) ≤ radius →
        radius ≤ Real.sqrt queryScale → ∀ center : ℝ,
        (Metric.externalCoveringNumber (scale k)
          (scalarProjection (planeMap point)
              (shading.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center radius) : ENNReal) ≤
          ENNReal.ofReal
            (Real.rpow delta (-continuousLoss) *
              Real.rpow (radius / (scale k : ℝ)) alpha) := by
  intro point k hk radius hscaleRadius hradiusTop center
  have hscaleKPos : 0 < (scale k : ℝ) := hscalePos k hk.le
  have hradiusNonnegative : 0 ≤ radius :=
    hscaleKPos.le.trans hscaleRadius
  by_cases hradiusEq : radius = Real.sqrt queryScale
  · have hpair := hdiscrete k N hk le_rfl point center
    have hset : Metric.closedBall center radius =
        Metric.closedBall center (scale N : ℝ) := by
      rw [hradiusEq, hscaleTop]
    rw [hset]
    have hloss : Real.rpow delta (-discreteLoss) ≤
        Real.rpow delta (-continuousLoss) := by
      have hratioPower : 1 ≤ ratio ^ alpha :=
        Real.one_le_rpow hratio halpha.le
      calc
        Real.rpow delta (-discreteLoss) =
            Real.rpow delta (-discreteLoss) * 1 := by ring
        _ ≤ Real.rpow delta (-discreteLoss) * ratio ^ alpha := by
          exact mul_le_mul_of_nonneg_left hratioPower
            (Real.rpow_nonneg hdelta.le _)
        _ ≤ Real.rpow delta (-continuousLoss) := habsorb
    have hratioEq :
        (scale N : ℝ) / (scale k : ℝ) =
          radius / (scale k : ℝ) := by
      rw [hscaleTop, hradiusEq]
    exact hpair.trans (ENNReal.ofReal_le_ofReal <| by
      rw [hratioEq]
      exact mul_le_mul_of_nonneg_right hloss
        (Real.rpow_nonneg
          (div_nonneg hradiusNonnegative hscaleKPos.le) _))
  · have hradiusLt : radius < (scale N : ℝ) := by
      rw [hscaleTop]
      exact lt_of_le_of_ne hradiusTop hradiusEq
    rcases exists_last_finite_interval_grid_index scale hk hscaleRadius
        hradiusLt with
      ⟨j, hkj, hjN, hscaleJRadius, hradiusNext⟩
    have hkjNext : k < j + 1 := Nat.lt_succ_of_le hkj
    have hjNextN : j + 1 ≤ N := Nat.succ_le_iff.mpr hjN
    have hpair := hdiscrete k (j + 1) hkjNext hjNextN point center
    have hset :
        scalarProjection (planeMap point)
              (shading.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center radius ⊆
          scalarProjection (planeMap point)
              (shading.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center (scale (j + 1) : ℝ) := by
      exact Set.inter_subset_inter_right _
        (Metric.closedBall_subset_closedBall hradiusNext.le)
    have hcover :
        (Metric.externalCoveringNumber (scale k)
          (scalarProjection (planeMap point)
              (shading.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center radius) : ENNReal) ≤
          (Metric.externalCoveringNumber (scale k)
            (scalarProjection (planeMap point)
                (shading.union ∩ Metric.closedBall (point : Point3)
                  (Real.sqrt queryScale)) ∩
              Metric.closedBall center (scale (j + 1) : ℝ)) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hset
    have hnext : (scale (j + 1) : ℝ) ≤ ratio * radius := by
      exact (hscaleRatio j hjN).trans
        (mul_le_mul_of_nonneg_left hscaleJRadius
          (le_trans (by norm_num) hratio))
    have hratioNonnegative : 0 ≤ ratio := le_trans (by norm_num) hratio
    have hquotient :
        (scale (j + 1) : ℝ) / (scale k : ℝ) ≤
          ratio * (radius / (scale k : ℝ)) := by
      calc
        (scale (j + 1) : ℝ) / (scale k : ℝ) ≤
            (ratio * radius) / (scale k : ℝ) := by gcongr
        _ = ratio * (radius / (scale k : ℝ)) := by ring
    have hpower :
        Real.rpow ((scale (j + 1) : ℝ) / (scale k : ℝ)) alpha ≤
          ratio ^ alpha *
            Real.rpow (radius / (scale k : ℝ)) alpha := by
      calc
        Real.rpow ((scale (j + 1) : ℝ) / (scale k : ℝ)) alpha ≤
            Real.rpow (ratio * (radius / (scale k : ℝ))) alpha :=
          Real.rpow_le_rpow (by positivity) hquotient halpha.le
        _ = ratio ^ alpha *
              Real.rpow (radius / (scale k : ℝ)) alpha :=
          Real.mul_rpow hratioNonnegative
            (div_nonneg hradiusNonnegative hscaleKPos.le)
    have hreal :
        Real.rpow delta (-discreteLoss) *
            Real.rpow ((scale (j + 1) : ℝ) / (scale k : ℝ)) alpha ≤
          Real.rpow delta (-continuousLoss) *
            Real.rpow (radius / (scale k : ℝ)) alpha := by
      calc
        Real.rpow delta (-discreteLoss) *
              Real.rpow ((scale (j + 1) : ℝ) / (scale k : ℝ)) alpha ≤
            Real.rpow delta (-discreteLoss) *
              (ratio ^ alpha *
                Real.rpow (radius / (scale k : ℝ)) alpha) := by
          exact mul_le_mul_of_nonneg_left hpower
            (Real.rpow_nonneg hdelta.le _)
        _ = (Real.rpow delta (-discreteLoss) * ratio ^ alpha) *
              Real.rpow (radius / (scale k : ℝ)) alpha := by ring
        _ ≤ Real.rpow delta (-continuousLoss) *
              Real.rpow (radius / (scale k : ℝ)) alpha := by
          exact mul_le_mul_of_nonneg_right habsorb
            (Real.rpow_nonneg
              (div_nonneg hradiusNonnegative hscaleKPos.le) _)
    exact hcover.trans <| hpair.trans <| ENNReal.ofReal_le_ofReal hreal

/-- Package a fixed-shading finite interval grid as the one-query output used
by the outer Lemma 4.12 iteration.  This theorem changes neither the shading
nor the plane map; it only invokes the metric finite-grid assembly. -/
noncomputable def one_scale_local_grain_of_finite_interval_grid
    {delta sigma intervalLoss outputLoss queryScale ratio : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source final : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (hsub : PaperIsSubshading final source)
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss family final)
    (hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss)))
    (hunit : ∀ point ∈ source.union, ‖planeMap point‖ = 1)
    (N : ℕ) (scale : ℕ → NNReal)
    (hquery : 0 < queryScale) (hqueryOne : queryScale ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hintervalLoss : 0 < intervalLoss) (houtputLoss : 0 < outputLoss)
    (hratio : 1 ≤ ratio)
    (hscaleZero : (scale 0 : ℝ) = queryScale)
    (hscaleTop : (scale N : ℝ) = Real.sqrt queryScale)
    (hscalePos : ∀ index, index ≤ N → 0 < (scale index : ℝ))
    (hscaleMono : ∀ index, index < N →
      (scale index : ℝ) ≤ (scale (index + 1) : ℝ))
    (hscaleRatio : ∀ index, index < N →
      (scale (index + 1) : ℝ) ≤ ratio * (scale index : ℝ))
    (hscaleCovers : ∀ radius : ℝ, queryScale ≤ radius →
      radius ≤ Real.sqrt queryScale →
      ∃ index, index < N ∧ (scale index : ℝ) ≤ radius ∧
        radius ≤ (scale (index + 1) : ℝ))
    (hinterval : ∀ point : {point : Point3 // point ∈ final.union},
      ∀ index, index < N → ∀ radius : ℝ,
        (scale index : ℝ) ≤ radius →
        radius ≤ Real.sqrt queryScale → ∀ center : ℝ,
        (Metric.externalCoveringNumber (scale index)
          (scalarProjection
              (planeMap point)
              (final.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center radius) : ENNReal) ≤
          ENNReal.ofReal
            (Real.rpow delta (-intervalLoss) *
              Real.rpow (radius / (scale index : ℝ)) (1 - sigma)))
    (habsorb : (3 : ℝ) * Real.rpow delta (-intervalLoss) *
      ratio ^ (1 - sigma) ≤ Real.rpow delta (-outputLoss)) :
    PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point) where
  shading := final
  subshading := hsub
  extremal := hextremal
  cwa := hcwa
  local_ad := by
    intro point hpoint
    have hpointSource : (point : Point3) ∈ source.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hsub index hindex⟩
    let E : Set ℝ := scalarProjection (planeMap point)
      (final.union ∩ Metric.closedBall point (Real.sqrt queryScale))
    have hdiameter : ∀ first second, first ∈ E → second ∈ E →
        dist first second ≤ 2 * Real.sqrt queryScale := by
      apply projection_diameter_bound hquery (hunit point hpointSource)
      intro other hother
      exact hother.2
    have hbounded : E ⊆ Set.Icc (-4 : ℝ) 4 := by
      apply scalarProjection_bounded (hunit point hpointSource) E
      rintro value ⟨other, hother, rfl⟩
      have hotherSource : other ∈ source.union := by
        rcases hother.1 with ⟨index, hindex⟩
        exact ⟨index, hsub index hindex⟩
      exact ⟨other, hotherSource, rfl⟩
    exact Kakeya.Assouad.multiscale_to_ad_set E queryScale (1 - sigma)
      delta intervalLoss outputLoss ratio N scale hquery hqueryOne hdelta
      hdeltaOne (by linarith) (by linarith) hintervalLoss houtputLoss
      hratio hscaleZero hscaleTop hscalePos hscaleMono hscaleRatio
      hscaleCovers (hinterval ⟨point, hpoint⟩) hdiameter hbounded habsorb

/-- Close the structure-only part of Lemma 4.11 directly from covering
estimates at every ordered pair of grid scales.  The first absorption pays
for interpolation from `scale (j + 1)` down to an arbitrary interval radius;
the second is the fixed factor in `multiscale_to_ad_set`. -/
noncomputable def one_scale_local_grain_of_discrete_interval_pairs
    {delta sigma discreteLoss intervalLoss outputLoss queryScale ratio : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source final : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (hsub : PaperIsSubshading final source)
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss family final)
    (hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss)))
    (hunit : ∀ point ∈ source.union, ‖planeMap point‖ = 1)
    (N : ℕ) (scale : ℕ → NNReal)
    (hquery : 0 < queryScale) (hqueryOne : queryScale ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hintervalLoss : 0 < intervalLoss) (houtputLoss : 0 < outputLoss)
    (hratio : 1 ≤ ratio)
    (hscaleZero : (scale 0 : ℝ) = queryScale)
    (hscaleTop : (scale N : ℝ) = Real.sqrt queryScale)
    (hscalePos : ∀ index, index ≤ N → 0 < (scale index : ℝ))
    (hscaleMono : ∀ index, index < N →
      (scale index : ℝ) ≤ (scale (index + 1) : ℝ))
    (hscaleRatio : ∀ index, index < N →
      (scale (index + 1) : ℝ) ≤ ratio * (scale index : ℝ))
    (hscaleCovers : ∀ radius : ℝ, queryScale ≤ radius →
      radius ≤ Real.sqrt queryScale →
      ∃ index, index < N ∧ (scale index : ℝ) ≤ radius ∧
        radius ≤ (scale (index + 1) : ℝ))
    (hdiscrete : ∀ k j, k < j → j ≤ N →
      PureWZ2IntervalCoveringAt final planeMap queryScale
        (scale k) (scale j)
        (ENNReal.ofReal
          (Real.rpow delta (-discreteLoss) *
            Real.rpow ((scale j : ℝ) / (scale k : ℝ)) (1 - sigma))))
    (hinterpolate : Real.rpow delta (-discreteLoss) *
      ratio ^ (1 - sigma) ≤ Real.rpow delta (-intervalLoss))
    (habsorb : (3 : ℝ) * Real.rpow delta (-intervalLoss) *
      ratio ^ (1 - sigma) ≤ Real.rpow delta (-outputLoss)) :
    PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point) := by
  apply one_scale_local_grain_of_finite_interval_grid planeMap hsub
    hextremal hcwa hunit N scale hquery hqueryOne hdelta hdeltaOne
    hsigma hsigmaOne hintervalLoss houtputLoss hratio hscaleZero
    hscaleTop hscalePos hscaleMono hscaleRatio hscaleCovers
  · exact finite_interval_grid_bounds_to_continuous planeMap N scale hdelta
      (by linarith) hratio hscaleTop hscalePos hscaleRatio hinterpolate
      hdiscrete
  · exact habsorb

end Kakeya.Assouad.PureWZ2

end

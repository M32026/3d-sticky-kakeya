import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-!
# Pure WZ2 grain statements

These are the paper-facing outputs of `prop: grain` and `prop: C2`.  They use
the same family and shading for the global and local grain conclusions and do
not store the internal re-entry or refinement history.
-/

noncomputable section

namespace Kakeya.Assouad

open Classical

/-- Pointwise containment of cropped paper shadings on one fixed family. -/
def PureWZ2PaperIsSubshading
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (refined source : WZ1PaperTubeShading family) : Prop :=
  ∀ index, refined.carrier index ⊆ source.carrier index

/--
Definition 7 from WZ, specialized to subsets of `ℝ` without the historical
bounded-window truncation.

This is the paper's literal upper AD condition: all covering scales
`rho ≥ delta` and all localization radii `r ≥ rho` are allowed.
-/
def PureWZ2PaperADSet1
    (set : Set ℝ) (delta alpha : ℝ) (C : ENNReal) : Prop :=
  0 < delta ∧
    0 < alpha ∧ alpha ≤ 1 ∧
    1 ≤ C ∧ C ≠ ⊤ ∧
    ∀ rho : ℝ, ∀ hrho : 0 ≤ rho, delta ≤ rho →
      ∀ left length : ℝ, rho ≤ length →
        (↑(Metric.externalCoveringNumber
          ⟨rho, hrho⟩
          (set ∩ Set.Icc left (left + length))) : ENNReal) ≤
            C * Kakeya.realRpowENN (length / rho) alpha

/-- Close-direction count for paper tube shadings.

Number of tubes `j` containing `p` whose direction is within `kappa`
of tube `i` in cross-product norm. -/
def paperCloseDirectionCount {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F) (p : Point3) (i : Fin F.card) (kappa : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun j =>
    p ∈ Y.carrier j ∧
      ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa).card

/-- Subshading relation for paper tube shadings. -/
def PaperIsSubshading {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z Y : WZ1PaperTubeShading F) : Prop :=
  ∀ i, Z.carrier i ⊆ Y.carrier i

/--
The exact plane-map and local-grain conclusion used in WZ2 Section 6.

The plane map is defined on `E_T`, as in the paper's definition.  Later uses
whose geometric window is centered at an ambient square center must choose a
genuine occupied anchor; they may not evaluate this map outside its subtype
domain.
-/
structure PureWZ2LocalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) where
  planeMap : {point : Point3 // point ∈ shading.union} → Point3
  planeMap_lipschitz :
    LipschitzWith 1 planeMap
  planeMap_unit :
    ∀ point,
      ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        |inner ℝ (family.tube index).direction
            (planeMap
              ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta
  local_ad :
    ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩
              Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) C

/--
The conversion boundary between the paper-literal AD predicate and the
bounded internal predicate used by the existing WZ1 proof infrastructure.
-/
def PureWZ2PaperADBridgeStatement : Prop :=
  (∀ set : Set ℝ, ∀ delta alpha : ℝ, ∀ C : ENNReal,
      set ⊆ Set.Icc (-4 : ℝ) 4 →
      PureWZ2PaperADSet1 set delta alpha C →
        IsADSet1 set delta alpha (10 * C)) ∧
  (∀ set : Set ℝ, ∀ delta alpha : ℝ, ∀ C : ENNReal,
      0 < delta → delta ≤ 1 →
      C ≠ ⊤ →
      IsADSet1 set delta alpha C →
        PureWZ2PaperADSet1 set delta alpha (10 * C))

/-- The literal interval domain used by the slope functions in WZ
Propositions 6.3 and 6.5. -/
abbrev PureWZ2UnitInterval :=
  {z : ℝ // z ∈ Set.Icc (-1 : ℝ) 1}

/-- A real-valued function on the literal paper interval. -/
abbrev PureWZ2IntervalFunction :=
  PureWZ2UnitInterval → ℝ

/-- Compatibility name used by the Proposition 6.5 implementation. -/
abbrev PureWZ2SlopeFunction :=
  PureWZ2IntervalFunction

/-- The global-grain conclusion of `prop: grain`. -/
structure PureWZ2LipschitzGlobalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) where
  f : PureWZ2IntervalFunction
  lipschitz :
    LipschitzWith 1 f
  paper_ad :
    ∀ z : PureWZ2UnitInterval,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (f z))
          (horizontalSlice shading.union z.1))
        delta (1 - sigma) C

namespace PureWZ2LipschitzGlobalGrainData

variable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}

/-- Clamp an ambient height to the literal paper interval. -/
def clampHeight (z : ℝ) : PureWZ2UnitInterval :=
  ⟨max (-1) (min 1 z), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)⟩

@[simp] theorem clampHeight_coe_of_mem
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    (clampHeight z : ℝ) = z := by
  simp [clampHeight, min_eq_right hz.2, max_eq_right hz.1]

theorem clampHeight_lipschitz :
    LipschitzWith 1 clampHeight := by
  convert (LipschitzWith.projIcc (by norm_num : (-1 : ℝ) ≤ 1)) using 1
  funext z
  apply Subtype.ext
  rfl

/-- Compatibility extension used by the existing ambient construction.  The
public witness remains the interval function `f`. -/
def slope (data : PureWZ2LipschitzGlobalGrainData shading sigma C) : ℝ → ℝ :=
  fun z => data.f (clampHeight z)

/-- The ambient compatibility function is globally one-Lipschitz.  This is
the strong `ℝ → ℝ` object consumed by legacy Lipschitz lemmas; it is not the
paper-facing witness and it is not asserted to be `C²`. -/
theorem slope_global_lipschitz
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C) :
    LipschitzWith 1 data.slope := by
  change LipschitzWith 1 (data.f ∘ clampHeight)
  simpa only [one_mul] using data.lipschitz.comp clampHeight_lipschitz

theorem slope_lipschitz
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C) :
    LipschitzOnWith 1 data.slope (Set.Icc (-1 : ℝ) 1) :=
  data.slope_global_lipschitz.lipschitzOnWith

theorem slope_eq_f
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    data.slope z = data.f ⟨z, hz⟩ := by
  change data.f (clampHeight z) = data.f ⟨z, hz⟩
  congr 1
  apply Subtype.ext
  exact clampHeight_coe_of_mem hz

/-- Compatibility form for existing ambient projection lemmas. -/
theorem global_ad
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (data.slope z))
        (horizontalSlice shading.union z))
      delta (1 - sigma) C := by
  rw [data.slope_eq_f z hz]
  exact data.paper_ad ⟨z, hz⟩

/-- Package an internally convenient ambient slope by restricting it to the
literal interval required by Proposition 6.3. -/
def ofRealFunction
    (slope : ℝ → ℝ)
    (slopeLipschitz :
      LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1))
    (globalAD :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        PureWZ2PaperADSet1
          (scalarProjection (globalGrainDirection (slope z))
            (horizontalSlice shading.union z))
          delta (1 - sigma) C) :
    PureWZ2LipschitzGlobalGrainData shading sigma C where
  f := fun z => slope z.1
  lipschitz := slopeLipschitz.to_restrict
  paper_ad := fun z => globalAD z.1 z.2

end PureWZ2LipschitzGlobalGrainData

/-- One same-configuration paper output of WZ2 `prop: grain`. -/
structure PureWZ2GrainConfiguration
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  shading :
    WZ1PaperTubeShading family
  line_class :
    WZ1PaperIsLineClass family
  cubical :
    WZ1PaperIsCubicalShading shading
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma loss family shading
  top_level_cwa :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-loss))
  globalGrains :
    PureWZ2LipschitzGlobalGrainData
      shading sigma
      (Kakeya.realRpowENN delta (-loss))
  localGrains :
    PureWZ2LocalGrainData
      shading sigma
      (Kakeya.realRpowENN delta (-loss))

/--
Same-family output of `prop: grain` on a supplied cropped extremizer.

This is the dependent form needed by Lemma 24: the refinement, global
grains, local grains, extremality, and CWA all live on the caller's family.
-/
structure PureWZ2GrainRefinementData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading family)
    (sigma outputLoss : ℝ) where
  shading : WZ1PaperTubeShading family
  subshading : PureWZ2PaperIsSubshading shading sourceShading
  line_class : WZ1PaperIsLineClass family
  cubical : WZ1PaperIsCubicalShading shading
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss family shading
  top_level_cwa :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss))
  volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      MeasureTheory.volume shading.union
  globalGrains :
    PureWZ2LipschitzGlobalGrainData
      shading sigma
      (Kakeya.realRpowENN delta (-outputLoss))
  localGrains :
    PureWZ2LocalGrainData
      shading sigma
      (Kakeya.realRpowENN delta (-outputLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2

/-- Forget the supplied-source provenance after a grain-facing refinement. -/
noncomputable def PureWZ2GrainRefinementData.toGrainConfiguration
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    (data :
      PureWZ2GrainRefinementData
        sourceShading sigma outputLoss) :
    PureWZ2GrainConfiguration sigma outputLoss delta where
  family := family
  shading := data.shading
  line_class := data.line_class
  cubical := data.cubical
  extremal := data.extremal
  top_level_cwa := data.top_level_cwa
  globalGrains := data.globalGrains
  localGrains := data.localGrains

/-- The paper conclusion of `prop: grain` for one pure critical package. -/
def PureWZ2GrainsFromCriticalStatement : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss delta₀ : ℝ,
        0 < outputLoss → 0 < delta₀ →
          ∃ delta : ℝ,
            0 < delta ∧ delta ≤ delta₀ ∧
            Nonempty
              (PureWZ2GrainConfiguration
                sigma outputLoss delta)

/-!
Grain-facing form of `prop: grain`.  Lemma 24 must apply the proposition to
the particular coarse extremizer produced by the first sticky decomposition,
not to a new unrelated member of the critical sequence.
-/
def PureWZ2GrainsAtExtremizerStatement : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss : ℝ, 0 < outputLoss →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ family : Kakeya.Streamlined.TubeFamily delta,
              ∀ shading : WZ1PaperTubeShading family,
                WZ1PaperIsLineClass family →
                WZ2PaperCroppedIsExtremal
                    sigma inputLoss family shading →
                  Nonempty
                    (PureWZ2GrainRefinementData
                      shading sigma outputLoss)

/-- Node 4's frozen paper-facing statement in the serial heavy-task chain.
The same-extremizer restoration above is a Node-5-private interface and is not
added as a third public conjunct. -/
def PureWZ2GrainsStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    PureWZ2CriticalExtractionStatement →
      PureWZ2PropStickyStatement →
        PureWZ2PaperADBridgeStatement ∧
          PureWZ2GrainsFromCriticalStatement

/-- The paper's function `f : [-1,1] → ℝ`. -/
abbrev PureWZ2C2SlopeFunction :=
  PureWZ2IntervalFunction

/--
The bounded `C²` conclusion on the literal interval domain.

The ambient representative is only a certificate for expressing the
derivatives in Lean; it is required to be `C²` on `[-1,1]`, not globally.
-/
def PureWZ2C2SlopeIsNormalized
    (f : PureWZ2C2SlopeFunction) : Prop :=
  ∃ extension : ℝ → ℝ,
    ContDiffOn ℝ 2 extension (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z : PureWZ2UnitInterval, extension z.1 = f z) ∧
      ∀ z : PureWZ2UnitInterval,
        |f z| ≤ 1 ∧
          |deriv extension z.1| ≤ 1 ∧
          |deriv (deriv extension) z.1| ≤ 1

/-- The interval-local normalized bounds for one chosen ambient
representative. -/
def PureWZ2AmbientSlopeIsNormalized (extension : ℝ → ℝ) : Prop :=
  ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    |extension z| ≤ 1 ∧
      |deriv extension z| ≤ 1 ∧
      |deriv (deriv extension) z| ≤ 1

/--
Reuse a normalized ambient slope only as an extension witness for its literal
restriction to `[-1,1]`.  This is the one-way compatibility bridge: the
paper-facing object remains a function on the interval.
-/
theorem SlopeFunction.isNormalized_restrict_unitInterval
    (extension : SlopeFunction)
    (hnormalized : extension.IsNormalized) :
    PureWZ2C2SlopeIsNormalized (fun z => extension z.1) := by
  exact
    ⟨extension, extension.contDiff.contDiffOn, fun _ => rfl,
      fun z => hnormalized z.1 z.2⟩

/-- The global `C²` grain conclusion of WZ2 `prop: C2`. -/
structure PureWZ2C2GlobalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) where
  f : PureWZ2C2SlopeFunction
  normalized : PureWZ2C2SlopeIsNormalized f
  global_ad :
    ∀ z : PureWZ2UnitInterval,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (f z))
          (horizontalSlice shading.union z.1))
        delta (1 - sigma) C

namespace PureWZ2C2GlobalGrainData

/-- Choose the ambient representative carried by the interval-local
normalization certificate.  No global smoothness is claimed. -/
noncomputable def slope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C) : ℝ → ℝ :=
  Classical.choose data.normalized

theorem slope_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    data.slope z = data.f ⟨z, hz⟩ :=
  (Classical.choose_spec data.normalized).2.1 ⟨z, hz⟩

theorem slope_contDiffOn
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C) :
    ContDiffOn ℝ 2 data.slope (Set.Icc (-1 : ℝ) 1) :=
  (Classical.choose_spec data.normalized).1

theorem slope_normalized
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C) :
    PureWZ2AmbientSlopeIsNormalized data.slope := by
  intro z hz
  have hbounds := (Classical.choose_spec data.normalized).2.2 ⟨z, hz⟩
  rw [data.slope_eq z hz]
  exact hbounds

/-- The chosen ambient representative is one-Lipschitz on the paper height
interval. -/
theorem slope_lipschitzOn
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C) :
    LipschitzOnWith 1 data.slope (Set.Icc (-1 : ℝ) 1) := by
  have hcontinuous : ContinuousOn data.slope (Set.Icc (-1 : ℝ) 1) :=
    data.slope_contDiffOn.continuousOn
  have hdifferentiable : DifferentiableOn ℝ data.slope
      (interior (Set.Icc (-1 : ℝ) 1)) :=
    (data.slope_contDiffOn.differentiableOn (by norm_num)).mono
      interior_subset
  apply LipschitzOnWith.of_dist_le_mul
  intro first hfirst second hsecond
  have hreal : |data.slope first - data.slope second| ≤
      |first - second| := by
    by_cases horder : first ≤ second
    · have hupper := (convex_Icc (-1 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
        hcontinuous hdifferentiable
        (fun height hheight =>
          (abs_le.mp (data.slope_normalized height
            (interior_subset hheight)).2.1).2)
        first hfirst second hsecond horder
      have hlower := (convex_Icc (-1 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
        hcontinuous hdifferentiable
        (fun height hheight =>
          (abs_le.mp (data.slope_normalized height
            (interior_subset hheight)).2.1).1)
        first hfirst second hsecond horder
      rw [abs_of_nonpos (sub_nonpos.mpr horder), abs_le]
      constructor <;> linarith
    · have horder' : second ≤ first := le_of_not_ge horder
      have hupper := (convex_Icc (-1 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
        hcontinuous hdifferentiable
        (fun height hheight =>
          (abs_le.mp (data.slope_normalized height
            (interior_subset hheight)).2.1).2)
        second hsecond first hfirst horder'
      have hlower := (convex_Icc (-1 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
        hcontinuous hdifferentiable
        (fun height hheight =>
          (abs_le.mp (data.slope_normalized height
            (interior_subset hheight)).2.1).1)
        second hsecond first hfirst horder'
      rw [abs_of_nonneg (sub_nonneg.mpr horder'), abs_le]
      constructor <;> linarith
  simpa [Real.dist_eq] using hreal

theorem global_ad_slope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (data.slope z))
        (horizontalSlice shading.union z))
      delta (1 - sigma) C := by
  rw [data.slope_eq z hz]
  exact data.global_ad ⟨z, hz⟩

end PureWZ2C2GlobalGrainData

/-- One same-configuration paper output of WZ2 `prop: C2`. -/
structure PureWZ2C2GrainConfiguration
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  shading :
    WZ1PaperTubeShading family
  line_class :
    WZ1PaperIsLineClass family
  /-- The ordinary representatives stay in the normalization window used by
  the Proposition 6.2 re-entry consumed by Node 6. -/
  bounded_base : HasBoundedBase family 4
  cubical :
    WZ1PaperIsCubicalShading shading
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma loss family shading
  top_level_cwa :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-loss))
  globalGrains :
    PureWZ2C2GlobalGrainData
      shading sigma
      (Kakeya.realRpowENN delta (-loss))
  localGrains :
    PureWZ2LocalGrainData
      shading sigma
      (Kakeya.realRpowENN delta (-loss))

/-- Internal provenance coupling the global grain direction to the local
plane field.  This is consumed by the Node 6 construction and is not added to
the paper-facing grain conclusion. -/
structure PureWZ2LocalGlobalCompatibility
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta) : Prop where
  tube_base_local : ∀ index, ‖(cfg.family.tube index).base‖ ≤ 5
  normal_first : ∀ point,
    1 / 4 ≤ |cfg.localGrains.planeMap point 0|
  normal_tilt : ∀ point,
    |cfg.localGrains.planeMap point 1 -
        cfg.globalGrains.slope (point.1 2) *
          cfg.localGrains.planeMap point 0| ≤ 1 / 10

/-- The paper conclusion of `prop: C2` for one pure critical package. -/
def PureWZ2C2GrainsFromCriticalStatement : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss delta₀ : ℝ,
        0 < outputLoss → 0 < delta₀ →
          ∃ delta : ℝ,
            0 < delta ∧ delta ≤ delta₀ ∧
            Nonempty
              (PureWZ2C2GrainConfiguration
                sigma outputLoss delta)

/-- Node 5's paper-facing statement in the serial heavy-task chain. -/
def PureWZ2C2GrainsStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    PureWZ2CriticalExtractionStatement →
      PureWZ2PropStickyStatement →
        PureWZ2GrainsStatement →
          PureWZ2C2GrainsFromCriticalStatement

end Kakeya.Assouad

end

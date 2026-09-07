import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingRediscretizationStatements

/-!
# WZ1 Proposition 9: final mild rescaling

The first global-planiness construction produces the correct global and local
grain certificates with small power losses in their Lipschitz constants.
WZ1 Proposition 9 then restricts to a mass-popular axis-parallel box and
applies Lemma 8 to normalize both maps to be `1`-Lipschitz.

This module freezes that missing scale-changing boundary.  The output records
the actual box, the retained refinement inside it, the diagonal affine map,
source-parent relation, carrier and axis provenance, and the transformed slope
and plane map.
-/

noncomputable section

namespace Kakeya.Assouad

/-- An axis-parallel box centered at `center` with positive half-widths. -/
def wz1AxisBox (center halfWidth : Point3) : Set Point3 :=
  {p | ∀ i, |p i - center i| ≤ halfWidth i}

/-- The fixed coordinate window used after the mild rescaling. -/
def wz1CoordinateWindow : Set Point3 :=
  {p | ∀ i, |p i| ≤ 1 / 4}

/-- The diagonal affine map used in WZ Lemma 8. -/
def wz1MildRescalingMap
    (center scale : Point3) (p : Point3) : Point3 :=
  point3
    (scale 0 * (p 0 - center 0))
    (scale 1 * (p 1 - center 1))
    (scale 2 * (p 2 - center 2))

/-- Inverse-transpose transport for plane normals under the diagonal map. -/
def wz1MildRescalingNormal
    (scale normal : Point3) : Point3 :=
  point3
    (normal 0 / scale 0)
    (normal 1 / scale 1)
    (normal 2 / scale 2)

/-- Normalize a nonzero transported normal. -/
def wz1NormalizeNormal (normal : Point3) : Point3 :=
  (‖normal‖)⁻¹ • normal

/-- Clamp a height to the source slope window `[-1,1]`. -/
def wz1ClampHeight (z : ℝ) : ℝ :=
  max (-1) (min 1 z)

/--
The global slope after the diagonal coordinate change.

This is the unique slope for which the transformed horizontal grain direction
is proportional to the source direction at the corresponding source height.
Clamping affects only inactive target heights and makes the definition valid
even when the selected source box meets the boundary of `[-1,1]`.
-/
def wz1MildRescaledSlope
    (center scale : Point3) (slope : ℝ → ℝ) (z : ℝ) : ℝ :=
  (scale 0 / scale 1) *
    slope (wz1ClampHeight (center 2 + z / scale 2))

/--
Paper-faithful output of the final mild rescaling in WZ1 Proposition 9.
-/
structure WZ1Proposition9MildRescalingData
    {sigma inputLoss sourceDelta outputLoss : ℝ}
    (source :
      WZ1PreNormalizedPlaninessGraininessData
        sigma inputLoss sourceDelta) where
  targetDelta : ℝ
  center : Point3
  halfWidth : Point3
  halfWidth_pos : ∀ i, 0 < halfWidth i
  scale : Point3
  scale_pos : ∀ i, 0 < scale i
  one_le_scale : ∀ i, 1 ≤ scale i
  scale_isotropic :
    scale 0 = scale 1 ∧ scale 1 = scale 2
  scale_lower :
    ∀ i, Real.rpow sourceDelta inputLoss ≤ scale i
  scale_upper :
    ∀ i, scale i ≤ Real.rpow sourceDelta (-inputLoss)
  slope_lipschitz_le_scale :
    (source.global_grains.lipschitzConstant : ℝ) ≤ scale 0
  planeMap_lipschitz_le_scale :
    (source.local_grains.lipschitzConstant : ℝ) ≤ scale 0
  targetDelta_pos : 0 < targetDelta
  targetDelta_eq :
    targetDelta = sourceDelta * scale 0
  sourceDelta_le_targetDelta : sourceDelta ≤ targetDelta
  targetDelta_le_quarter : targetDelta ≤ 1 / 4
  targetDelta_le_source_power :
    targetDelta ≤ Real.rpow sourceDelta (1 - inputLoss)
  target :
    WZ1PlaninessGraininessPackage sigma outputLoss targetDelta
  selected :
    Kakeya.Streamlined.TubeShading source.family
  selected_subshading : IsSubshading selected source.shading
  /--
  The retained source shading may be a genuine refinement inside the chosen
  box.  Lemma 8 must discard conflicting image tubes before producing an
  essentially-distinct target family.
  -/
  selected_carrier_subset :
    ∀ i,
      selected.carrier i ⊆
        source.shading.carrier i ∩ wz1AxisBox center halfWidth
  /--
  Conservative loss for the three-dimensional box pigeonhole and the
  six-parameter essentially-distinct cleanup.  The outer statement reserves
  the larger budget `100 * inputLoss < outputLoss`.
  -/
  selected_mass :
    Kakeya.realRpowENN sourceDelta (10 * inputLoss) *
        source.shading.mass ≤
      selected.mass
  box_maps_to_window :
    wz1MildRescalingMap center scale ''
        wz1AxisBox center halfWidth ⊆
      wz1CoordinateWindow
  sourceParent :
    Fin target.family.card → Fin source.family.card
  sourceFiberCap : ℕ
  sourceFiberCap_pos : 0 < sourceFiberCap
  sourceFiberCap_bound :
    ∀ i,
      (Finset.univ.filter fun j => sourceParent j = i).card ≤
        sourceFiberCap
  /--
  Faithful unit-child rediscretization has `ceil scale` children over one
  source tube.  Since `1 ≤ scale`, this is bounded by `2 * scale`, not by
  `scale` itself.  The fixed factor two is absorbed separately in the
  cardinality-loss budget.
  -/
  sourceFiberCap_power :
    (sourceFiberCap : ENNReal) ≤
      2 * Kakeya.realRpowENN sourceDelta (-inputLoss)
  axis_provenance :
    ∀ j,
      tubeAxisLine (target.family.tube j) =
        wz1MildRescalingMap center scale ''
          tubeAxisLine (source.family.tube (sourceParent j))
  carrier_provenance :
    ∀ j,
      target.shading.carrier j ⊆
        Metric.cthickening targetDelta
          (wz1MildRescalingMap center scale ''
            selected.carrier (sourceParent j))
  image_covered :
    wz1MildRescalingMap center scale '' selected.union ⊆
      target.shading.union
  source_image_covered :
    ∀ i,
      wz1MildRescalingMap center scale '' selected.carrier i ⊆
        ⋃ j ∈
            Finset.univ.filter (fun j => sourceParent j = i),
          target.shading.carrier j
  slope_provenance :
    target.global_grains.slope =
      wz1MildRescaledSlope center scale source.global_grains.slope
  slope_on_image :
    ∀ p ∈ selected.union,
      target.global_grains.slope
          ((wz1MildRescalingMap center scale p) 2) =
        (scale 0 / scale 1) * source.global_grains.slope (p 2)
  planeMap_provenance :
    ∀ p ∈ selected.union,
      target.local_grains.planeMap
          (wz1MildRescalingMap center scale p) =
        wz1NormalizeNormal
          (wz1MildRescalingNormal scale
            (source.local_grains.planeMap p))

/--
WZ1 Proposition 9 final mild-rescaling lemma.

The source threshold is chosen after the requested target threshold, so the
new tube radius remains below the caller's bound despite the power-sized
coordinate dilation.
-/
def WZ1Proposition9MildRescalingStatement : Prop :=
  ∀ sigma outputLoss targetDelta₀ : ℝ,
    0 < sigma → sigma < 1 →
    0 < outputLoss → 0 < targetDelta₀ →
      ∃ inputLoss sourceDelta₀ : ℝ,
        0 < inputLoss ∧
        100 * inputLoss < outputLoss ∧
        inputLoss < 1 / 4 ∧
        0 < sourceDelta₀ ∧ sourceDelta₀ ≤ 1 ∧
        ∀ sourceDelta : ℝ,
          0 < sourceDelta → sourceDelta ≤ sourceDelta₀ →
            ∀ source :
                WZ1PreNormalizedPlaninessGraininessData
                  sigma inputLoss sourceDelta,
              ∃ data :
                  WZ1Proposition9MildRescalingData
                    (outputLoss := outputLoss) source,
                data.targetDelta ≤ targetDelta₀

/--
Assemble the final Proposition 9 mild rescaling from the raw multi-child
isotropic rediscretization.

The predecessor only covers the long homothetic image by unit target tubes.
This theorem must still perform the essentially-distinct cleanup, transport
the uniform/Frostman structure and both grain certificates, and absorb all
finite losses into `outputLoss`.
-/
def WZ1Proposition9MildRescalingFromRediscretizationStatement : Prop :=
  WZ1IsotropicTubeRediscretizationStatement →
    WZ1Proposition9MildRescalingStatement

end Kakeya.Assouad

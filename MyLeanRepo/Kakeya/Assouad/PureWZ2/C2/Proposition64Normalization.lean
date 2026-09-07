import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ShortSlab
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Refinement
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingADProof

/-!
# Analytic normalization in Proposition 6.4

This is the exact-image part of the final normalization in `wz2_64.tex`.
It applies

`(x,y,z) -> ((x + g(z_*) y) / C_*, y, (z-c)/halfHeight)`

to the mass-heavy short slab, transports the slope by subtracting `g(z_*)`,
and records the exact scalar-projection identity.  The later Lemma 3.5 step
replaces this affine image by ordinary tubes and a cubical shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

@[simp] theorem deriv_pureWZ2Proposition64Slope
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization t : ℝ) :
    deriv (pureWZ2Proposition64Slope g slabCenter anchorHeight
      halfHeight normalization) t =
      halfHeight * deriv g (slabCenter + halfHeight * t) / normalization := by
  have hbase :=
    deriv_rescaled_slope g slabCenter halfHeight normalization t
  have hfun :
      (pureWZ2Proposition64Slope
        g slabCenter anchorHeight halfHeight normalization : ℝ → ℝ) =
      fun s : ℝ =>
        g (slabCenter + halfHeight * s) / normalization -
          g anchorHeight / normalization := by
    funext s
    simp [pureWZ2Proposition64Slope]
    ring
  rw [hfun, deriv_sub_const]
  exact hbase

@[simp] theorem second_deriv_pureWZ2Proposition64Slope
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization t : ℝ) :
    deriv (deriv (pureWZ2Proposition64Slope
      g slabCenter anchorHeight halfHeight normalization)) t =
      halfHeight ^ 2 * deriv (deriv g)
        (slabCenter + halfHeight * t) / normalization := by
  have hfun : deriv (pureWZ2Proposition64Slope
      g slabCenter anchorHeight halfHeight normalization) =
      deriv (fun s : ℝ =>
        g (slabCenter + halfHeight * s) / normalization) := by
    funext s
    rw [deriv_pureWZ2Proposition64Slope,
      deriv_rescaled_slope]
  rw [hfun]
  exact second_deriv_rescaled_slope
    g slabCenter halfHeight normalization t

/-- The Proposition 6.4 slope becomes normalized after restricting to the
short slab and dividing by a sufficiently large fixed normalization. -/
theorem pureWZ2Proposition64Slope_normalized
    {delta rawLoss extensionConstant slabCenter anchorHeight
      halfHeight normalization : ℝ}
    (g : SlopeFunction)
    (_hdelta : 0 < delta)
    (hhalf : 0 < halfHeight) (hhalfOne : halfHeight ≤ 1)
    (hnormalizationPos : 0 < normalization)
    (hwindow : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      slabCenter + halfHeight * t ∈ Set.Icc (-1 : ℝ) 1)
    (hanchor : anchorHeight ∈
      Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight))
    (hfirst : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv g z| ≤ extensionConstant * Real.rpow delta (-rawLoss))
    (hsecond : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (deriv g) z| ≤
        extensionConstant * Real.rpow delta (-rawLoss))
    (hnormalization :
      2 * halfHeight * extensionConstant *
        Real.rpow delta (-rawLoss) ≤ normalization) :
    (pureWZ2Proposition64Slope
      g slabCenter anchorHeight halfHeight normalization).IsNormalized := by
  intro t ht
  have hz := hwindow t ht
  have hzSlab : slabCenter + halfHeight * t ∈
      Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight) := by
    constructor <;> nlinarith [ht.1, ht.2, hhalf]
  have hleftWindow := hwindow (-1) (by norm_num)
  have hrightWindow := hwindow 1 (by norm_num)
  have hanchorWindow : anchorHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [hanchor.1, hanchor.2,
      hleftWindow.1, hrightWindow.2]
  have hdistance :
      |(slabCenter + halfHeight * t) - anchorHeight| ≤
        2 * halfHeight := by
    rw [abs_le]
    constructor <;> linarith [hzSlab.1, hzSlab.2, hanchor.1, hanchor.2]
  have hdiff : Differentiable ℝ g :=
    g.contDiff.differentiable (by norm_num)
  have hderivNorm : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ‖deriv g z‖ ≤ extensionConstant * Real.rpow delta (-rawLoss) := by
    intro z hz'
    simpa [Real.norm_eq_abs] using hfirst z hz'
  have hslopeDiff :
      |g (slabCenter + halfHeight * t) - g anchorHeight| ≤
        2 * halfHeight *
          (extensionConstant * Real.rpow delta (-rawLoss)) := by
    have hmvt :
        ‖g anchorHeight - g (slabCenter + halfHeight * t)‖ ≤
          (extensionConstant * Real.rpow delta (-rawLoss)) *
            ‖anchorHeight - (slabCenter + halfHeight * t)‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun point _ => hdiff.differentiableAt) hderivNorm
        (convex_Icc _ _) (hwindow t ht) hanchorWindow
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm] at hmvt
    have hboundNonneg :
        0 ≤ extensionConstant * Real.rpow delta (-rawLoss) :=
      (abs_nonneg (deriv g (slabCenter + halfHeight * t))).trans
        (hfirst _ hz)
    calc
      |g (slabCenter + halfHeight * t) - g anchorHeight|
          ≤ (extensionConstant * Real.rpow delta (-rawLoss)) *
              |(slabCenter + halfHeight * t) - anchorHeight| := by
            simpa [abs_sub_comm] using hmvt
      _ ≤ (extensionConstant * Real.rpow delta (-rawLoss)) *
            (2 * halfHeight) := by gcongr
      _ = 2 * halfHeight *
          (extensionConstant * Real.rpow delta (-rawLoss)) := by ring
  have hvalueNew :
      |pureWZ2Proposition64Slope
          g slabCenter anchorHeight halfHeight normalization t| ≤ 1 := by
    rw [pureWZ2Proposition64Slope_apply, abs_div,
      abs_of_pos hnormalizationPos]
    apply (div_le_one hnormalizationPos).2
    exact hslopeDiff.trans (by simpa [mul_assoc] using hnormalization)
  have hfirstNew :
      |deriv (pureWZ2Proposition64Slope
          g slabCenter anchorHeight halfHeight normalization) t| ≤ 1 := by
    rw [deriv_pureWZ2Proposition64Slope, abs_div, abs_mul,
      abs_of_pos hnormalizationPos, abs_of_pos hhalf]
    have hboundNonneg :
        0 ≤ extensionConstant * Real.rpow delta (-rawLoss) :=
      (abs_nonneg (deriv g (slabCenter + halfHeight * t))).trans
        (hfirst _ hz)
    calc
      halfHeight * |deriv g (slabCenter + halfHeight * t)| / normalization
          ≤ halfHeight *
              (extensionConstant * Real.rpow delta (-rawLoss)) /
                normalization := by
            gcongr
            exact hfirst _ hz
      _ ≤ 1 := by
        apply (div_le_one hnormalizationPos).2
        nlinarith [hboundNonneg]
  have hsecondNew :
      |deriv (deriv (pureWZ2Proposition64Slope
          g slabCenter anchorHeight halfHeight normalization)) t| ≤ 1 := by
    rw [second_deriv_pureWZ2Proposition64Slope, abs_div, abs_mul, abs_pow,
      abs_of_pos hnormalizationPos, abs_of_pos hhalf]
    have hhalfSq : halfHeight ^ 2 ≤ 1 := by nlinarith
    have hboundNonneg :
        0 ≤ extensionConstant * Real.rpow delta (-rawLoss) :=
      (abs_nonneg (deriv (deriv g)
        (slabCenter + halfHeight * t))).trans (hsecond _ hz)
    calc
      halfHeight ^ 2 *
          |deriv (deriv g) (slabCenter + halfHeight * t)| / normalization
          ≤ halfHeight ^ 2 *
              (extensionConstant * Real.rpow delta (-rawLoss)) /
                normalization := by
            gcongr
            exact hsecond _ hz
      _ ≤ 1 := by
        apply (div_le_one hnormalizationPos).2
        nlinarith [sq_nonneg halfHeight, hboundNonneg]
  exact ⟨hvalueNew, hfirstNew, hsecondNew⟩

/-- The exact-image analytic data after the Proposition 6.4 affine map. -/
structure PureWZ2Proposition64NormalizedData
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma C rawLoss extensionConstant)
    (slabCenter anchorHeight halfHeight normalization : ℝ) where
  halfHeight_pos : 0 < halfHeight
  normalization_pos : 0 < normalization
  anchor_mem : anchorHeight ∈
    Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight)
  anchor_value_bound : |raw.slope anchorHeight| ≤ 8
  source_window : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
    slabCenter + halfHeight * t ∈ Set.Icc (-1 : ℝ) 1
  slope : SlopeFunction :=
    pureWZ2Proposition64Slope raw.slope slabCenter anchorHeight
      halfHeight normalization
  slope_eq : slope =
    pureWZ2Proposition64Slope raw.slope slabCenter anchorHeight
      halfHeight normalization
  normalized : slope.IsNormalized
  projection_identity :
    ∀ sourceSet : Set Point3, ∀ t : ℝ,
      scalarProjection (globalGrainDirection (slope t))
          (horizontalSlice
            (pureWZ2Proposition64Map raw.slope slabCenter anchorHeight
              halfHeight normalization '' sourceSet) t) =
        (fun value : ℝ => value / normalization) ''
          scalarProjection
            (globalGrainDirection
              (raw.slope (slabCenter + halfHeight * t)))
            (horizontalSlice sourceSet (slabCenter + halfHeight * t))
  global_ad :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope t))
          (horizontalSlice
            (pureWZ2Proposition64Map raw.slope slabCenter anchorHeight
              halfHeight normalization '' sourceShading.union) t))
        (delta / normalization) (1 - sigma) (6 * C)

private theorem pureWZ2Proposition64_slice_image
    (g : ℝ → ℝ) {slabCenter halfHeight normalization : ℝ}
    (anchorHeight : ℝ)
    (hhalf : halfHeight ≠ 0) (sourceSet : Set Point3) (t : ℝ) :
    pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization ''
        horizontalSlice sourceSet (slabCenter + halfHeight * t) =
      horizontalSlice
        (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
          normalization ''
          sourceSet) t := by
  ext point
  constructor
  · rintro ⟨sourcePoint, ⟨hsource, hsourceHeight⟩, rfl⟩
    refine ⟨⟨sourcePoint, hsource, rfl⟩, ?_⟩
    rw [pureWZ2Proposition64Map_apply_two, hsourceHeight]
    field_simp [hhalf]
    ring
  · rintro ⟨⟨sourcePoint, hsource, hpoint⟩, hheight⟩
    subst point
    refine ⟨sourcePoint, ⟨hsource, ?_⟩, rfl⟩
    rw [pureWZ2Proposition64Map_apply_two] at hheight
    apply (sub_eq_iff_eq_add).mp
    apply (div_eq_iff hhalf).mp at hheight
    linarith

private theorem pureWZ2Proposition64_projection_set
    (g : SlopeFunction)
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    (hhalf : halfHeight ≠ 0) (sourceSet : Set Point3) (t : ℝ) :
    scalarProjection
        (globalGrainDirection
          (pureWZ2Proposition64Slope
            g slabCenter anchorHeight halfHeight normalization t))
        (horizontalSlice
          (pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
            normalization ''
            sourceSet) t) =
      (fun value : ℝ => value / normalization) ''
        scalarProjection
          (globalGrainDirection (g (slabCenter + halfHeight * t)))
          (horizontalSlice sourceSet (slabCenter + halfHeight * t)) := by
  rw [← pureWZ2Proposition64_slice_image g anchorHeight hhalf sourceSet t]
  ext value
  constructor
  · rintro ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨inner ℝ sourcePoint
        (globalGrainDirection (g (slabCenter + halfHeight * t))),
      ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    have hheight : sourcePoint 2 = slabCenter + halfHeight * t :=
      hsourcePoint.2
    have hmapHeight :
        pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight normalization
            sourcePoint 2 = t := by
      rw [pureWZ2Proposition64Map_apply_two, hheight]
      field_simp [hhalf]
      ring
    rw [show pureWZ2Proposition64Slope
        g slabCenter anchorHeight halfHeight normalization t =
          pureWZ2Proposition64Slope
            g slabCenter anchorHeight halfHeight normalization
              (pureWZ2Proposition64Map g slabCenter anchorHeight
                halfHeight normalization sourcePoint 2) by rw [hmapHeight]]
    simpa [hheight, hmapHeight] using
      (pureWZ2Proposition64Map_projection_identity
        g slabCenter anchorHeight halfHeight normalization hhalf
          sourcePoint).symm
  · rintro ⟨sourceValue, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization
        sourcePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    have hheight : sourcePoint 2 = slabCenter + halfHeight * t :=
      hsourcePoint.2
    have hmapHeight :
        pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight normalization
            sourcePoint 2 = t := by
      rw [pureWZ2Proposition64Map_apply_two, hheight]
      field_simp [hhalf]
      ring
    rw [show pureWZ2Proposition64Slope
        g slabCenter anchorHeight halfHeight normalization t =
          pureWZ2Proposition64Slope
            g slabCenter anchorHeight halfHeight normalization
              (pureWZ2Proposition64Map g slabCenter anchorHeight
                halfHeight normalization sourcePoint 2) by rw [hmapHeight]]
    simpa [hheight, hmapHeight] using
      pureWZ2Proposition64Map_projection_identity
        g slabCenter anchorHeight halfHeight normalization hhalf sourcePoint

/-- Package the exact analytic image of the Proposition 6.4 short slab. -/
theorem PureWZ2RawC2GlobalGrainData.proposition64Normalize
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma C rawLoss extensionConstant)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (hdelta : 0 < delta)
    (hhalf : 0 < halfHeight) (hhalfOne : halfHeight ≤ 1)
    (hanchor : anchorHeight ∈
      Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight))
    (hanchorActive : horizontalSlice sourceShading.union anchorHeight ≠ ∅)
    (hnormalization :
      2 * halfHeight * extensionConstant *
        Real.rpow delta (-rawLoss) ≤ normalization)
    (hwindow : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      slabCenter + halfHeight * t ∈ Set.Icc (-1 : ℝ) 1) :
    Nonempty (PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization) := by
  have hnormalizationPos : 0 < normalization := by
    have hApos : 0 < extensionConstant := by
      linarith [raw.extensionConstant_one]
    have hpowPos : 0 < Real.rpow delta (-rawLoss) :=
      Real.rpow_pos_of_pos hdelta _
    nlinarith [mul_pos hApos hpowPos]
  have hnormalized := pureWZ2Proposition64Slope_normalized
    raw.slope hdelta hhalf hhalfOne hnormalizationPos hwindow hanchor
      raw.first_derivative_bound raw.second_derivative_bound hnormalization
  have hanchorWindow : anchorHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    have hleft := hwindow (-1) (by norm_num)
    have hright := hwindow 1 (by norm_num)
    constructor <;> linarith [hanchor.1, hanchor.2,
      hleft.1, hright.2]
  have hprojection := pureWZ2Proposition64_projection_set
    raw.slope (slabCenter := slabCenter) (anchorHeight := anchorHeight)
      (halfHeight := halfHeight)
      (normalization := normalization) hhalf.ne'
  have hglobal : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2Proposition64Slope raw.slope slabCenter anchorHeight
              halfHeight normalization t))
          (horizontalSlice
            (pureWZ2Proposition64Map raw.slope slabCenter anchorHeight
              halfHeight normalization '' sourceShading.union) t))
        (delta / normalization) (1 - sigma) (6 * C) := by
    intro t ht
    rw [hprojection sourceShading.union t]
    have himage :=
      (raw.global_ad (slabCenter + halfHeight * t) (hwindow t ht)).image_mul
        (show 0 < 1 / normalization by positivity)
    have hset : (fun value : ℝ => value / normalization) =
        fun value : ℝ => (1 / normalization) * value := by
      funext value
      ring
    rw [hset]
    convert himage using 1 <;> ring
  exact ⟨{
    halfHeight_pos := hhalf
    normalization_pos := hnormalizationPos
    anchor_mem := hanchor
    anchor_value_bound :=
      raw.active_value_bound anchorHeight hanchorWindow hanchorActive
    source_window := hwindow
    slope := pureWZ2Proposition64Slope raw.slope slabCenter anchorHeight
      halfHeight normalization
    slope_eq := rfl
    normalized := hnormalized
    projection_identity := hprojection
    global_ad := hglobal }⟩

end Kakeya.Assouad

end

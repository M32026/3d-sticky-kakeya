import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedStep4Witness
import MyLeanRepo.Kakeya.Assouad.LargeSlope.PrismMassPigeonhole
import MyLeanRepo.Kakeya.Assouad.LargeSlope.PigeonholeActiveCount
import MyLeanRepo.Kakeya.Assouad.PaperTubeSegmentADDirectionBound
import MyLeanRepo.Kakeya.Assouad.LargeSlope.NegativeExponentAbsorption
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ConvexOverloadHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SlabExpansion
import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.EMetricSpace.Diam

/-!
# Cropped convex overload for pure WZ2 large-slope (Option B)

Adapts `LargeSlope.ConvexOverload` to paper carriers:
- Uses `orientedBoxSlab` (axisBox ∩ strip) instead of `orientedUnitSlab`
- Paper tube carrier containment with width `2√3 · τ + 12δ`
- Volume bound `24 · width` (box has radius √3 vs unit ball radius 1)
- No `deltaTubeVolume 1` factor; conclusion directly contradicts paper CWA

Constants:
- Volume bound: `volume W ≤ 24 * width`
- Width bound: `width ≤ 11 * τ` (since `2√3 + 7 < 11`)
- Total: `volume W ≤ 264 * τ`
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- A slab bounded by the axis box instead of the Euclidean unit ball. -/
def orientedBoxSlab (center normal : Point3) (width : ℝ) : Set Point3 :=
  Kakeya.Streamlined.axisBox 2 2 2 ∩
    {x | |inner ℝ (x - center) normal| ≤ width}

/-- `orientedBoxSlab` is convex. -/
lemma orientedBoxSlab_convex (center normal : Point3) (width : ℝ) :
    Convex ℝ (orientedBoxSlab center normal width) := by
  have hcoord_convex : ∀ (i : Fin 3), Convex ℝ {x : Point3 | |x i| ≤ 1} := by
    intro i
    let f : Point3 → ℝ := fun x => x i
    have hf : IsLinearMap ℝ f := by
      refine { map_add := ?_, map_smul := ?_ }
      · intro x y; rfl
      · intro c x; rfl
    have h1 : Convex ℝ {x : Point3 | f x ≤ 1} := convex_halfSpace_le hf 1
    have h2 : Convex ℝ {x : Point3 | -1 ≤ f x} := convex_halfSpace_ge hf (-1)
    have h3 : {x : Point3 | |f x| ≤ 1} = {x : Point3 | f x ≤ 1} ∩ {x : Point3 | -1 ≤ f x} := by
      ext x; simp [abs_le] <;> constructor <;> intro h <;> constructor <;> linarith
    rw [h3]
    exact h1.inter h2
  have hbox : Convex ℝ (Kakeya.Streamlined.axisBox 2 2 2) := by
    have h_eq1 : Kakeya.Streamlined.axisBox 2 2 2 =
        ({x : Point3 | |x 0| ≤ 1} ∩ {x : Point3 | |x 1| ≤ 1}) ∩ {x : Point3 | |x 2| ≤ 1} := by
      ext x
      simp [Kakeya.Streamlined.axisBox]
      <;> constructor <;> intro h <;> norm_num at * <;> tauto
    rw [h_eq1]
    exact ((hcoord_convex 0).inter (hcoord_convex 1)).inter (hcoord_convex 2)
  let f : Point3 → ℝ := fun x => inner ℝ x normal
  have hf : IsLinearMap ℝ f := by
    refine { map_add := ?_, map_smul := ?_ }
    · intro x y; simp [f, inner_add_left]
    · intro c x; simp [f, inner_smul_left]
  have hstrip1 : Convex ℝ {x : Point3 | f x ≤ width + f center} :=
    convex_halfSpace_le hf (width + f center)
  have hstrip2 : Convex ℝ {x : Point3 | f x ≥ -width + f center} :=
    convex_halfSpace_ge hf (-width + f center)
  have hstrip : Convex ℝ {x : Point3 | |inner ℝ (x - center) normal| ≤ width} := by
    have h_eq : {x : Point3 | |inner ℝ (x - center) normal| ≤ width} =
        {x : Point3 | f x ≤ width + f center} ∩
          {x : Point3 | f x ≥ -width + f center} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      have h9 : inner ℝ (x - center) normal = f x - f center := by
        simp [f, inner_sub_left]
      rw [h9, abs_le] <;> constructor <;> intro h <;> constructor <;> linarith
    rw [h_eq]
    exact hstrip1.inter hstrip2
  exact hbox.inter hstrip

/-- Shift the center of an oriented box slab. -/
lemma orientedBoxSlab_shift_center
    {q c normal : Point3} {w d : ℝ} (x : Point3)
    (hx : x ∈ orientedBoxSlab q normal w)
    (hshift : |inner ℝ (q - c) normal| ≤ d) :
    x ∈ orientedBoxSlab c normal (w + d) := by
  have h1 : x ∈ Kakeya.Streamlined.axisBox 2 2 2 := hx.1
  have h2 : |inner ℝ (x - q) normal| ≤ w := hx.2
  have h3 : inner ℝ (x - c) normal =
      inner ℝ (x - q) normal + inner ℝ (q - c) normal := by
    have h : x - c = (x - q) + (q - c) := by abel
    rw [h, inner_add_left]
  have h4 : |inner ℝ (x - c) normal| ≤ w + d := by
    rw [h3]
    calc |inner ℝ (x - q) normal + inner ℝ (q - c) normal|
      ≤ |inner ℝ (x - q) normal| + |inner ℝ (q - c) normal| := abs_add_le _ _
    _ ≤ w + d := by linarith
  exact ⟨h1, h4⟩

/-- Volume bound for oriented box slab: `≤ 24 * width`. -/
theorem oriented_box_slab_volume
    (center normal : Point3) (width : ℝ)
    (hnorm : ‖normal‖ = 1) (hwidth : 0 ≤ width) :
    MeasureTheory.volume (orientedBoxSlab center normal width) ≤
      ENNReal.ofReal (24 * width) := by
  let e3 : Point3 := EuclideanSpace.single 2 (1 : ℝ)
  let v : Point3 := normal - e3
  let K : Submodule ℝ Point3 := (Submodule.span ℝ {v})ᗮ
  let A : Point3 ≃ₗᵢ[ℝ] Point3 := K.reflection
  let c : ℝ := inner ℝ center normal

  have he3_norm : ‖e3‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  have hA_normal : A normal = e3 :=
    Submodule.reflection_sub (hnorm.trans he3_norm.symm)
  have hA_inner : ∀ (x y : Point3), inner ℝ (A x) (A y) = inner ℝ x y :=
    A.inner_map_map
  have hA_norm : ∀ (x : Point3), ‖A x‖ = ‖x‖ := A.norm_map

  let s := orientedBoxSlab center normal width
  let s' := A '' s

  have hs_meas : MeasurableSet s := by
    have h1 : MeasurableSet (Kakeya.Streamlined.axisBox 2 2 2) := by
      simp [Kakeya.Streamlined.axisBox] <;> fun_prop
    have h_cont : Continuous (fun x : Point3 => |inner ℝ (x - center) normal|) := by fun_prop
    have h2 : MeasurableSet {x : Point3 | |inner ℝ (x - center) normal| ≤ width} :=
      (isClosed_Iic.preimage h_cont).measurableSet
    exact h1.inter h2

  let A_meas : Point3 ≃ᵐ Point3 := A.toMeasurableEquiv
  have h_preimg : A ⁻¹' s' = s := Set.preimage_image_eq s A.injective
  have hvol : MeasureTheory.volume s = MeasureTheory.volume s' := by
    have h : MeasureTheory.volume (A ⁻¹' s') = MeasureTheory.volume s' :=
      A.measurePreserving.measure_preimage_emb A_meas.measurableEmbedding s'
    rw [h_preimg] at h
    exact h

  let eLp : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := WithLp.ofLp
      invFun := WithLp.toLp 2
      left_inv := by intro x; exact WithLp.toLp_ofLp (2 : ENNReal) x
      right_inv := by intro x; exact WithLp.ofLp_toLp (2 : ENNReal) x
      measurable_toFun := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable }
  let s'' : Set (Fin 3 → ℝ) := eLp '' s'

  have h_ofLp_vol : MeasureTheory.MeasurePreserving eLp MeasureTheory.volume MeasureTheory.volume :=
    by simpa [eLp] using PiLp.volume_preserving_ofLp (ι := Fin 3)

  have hs'_meas : MeasurableSet s' := A_meas.measurableSet_image.mpr hs_meas
  have h_preimg2 : eLp ⁻¹' s'' = s' := by
    rw [← Set.preimage_image_eq s' eLp.injective]
  have hvol2 : MeasureTheory.volume s' = MeasureTheory.volume s'' := by
    have h : MeasureTheory.volume (eLp ⁻¹' s'') = MeasureTheory.volume s'' :=
      h_ofLp_vol.measure_preimage_emb eLp.measurableEmbedding s''
    rw [h_preimg2] at h
    exact h

  have h_box_norm : ∀ (x : Point3), x ∈ Kakeya.Streamlined.axisBox 2 2 2 → ‖x‖ ≤ Real.sqrt 3 := by
    intro x hx
    have h1 : |x 0| ≤ 1 := by
      have h := hx.1
      norm_num at h ⊢ <;> exact h
    have h2 : |x 1| ≤ 1 := by
      have h := hx.2.1
      norm_num at h ⊢ <;> exact h
    have h3 : |x 2| ≤ 1 := by
      have h := hx.2.2
      norm_num at h ⊢ <;> exact h
    have h4 : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
      have h5 : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
        <;> ring
      rw [h5]
      rw [Real.sq_sqrt (by positivity)]
    have h5 : ‖x‖ ^ 2 ≤ 3 := by
      rw [h4]
      have h6 : (x 0)^2 ≤ 1 := by nlinarith [abs_le.mp h1]
      have h7 : (x 1)^2 ≤ 1 := by nlinarith [abs_le.mp h2]
      have h8 : (x 2)^2 ≤ 1 := by nlinarith [abs_le.mp h3]
      nlinarith
    have h6 : 0 ≤ ‖x‖ := by positivity
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  have h_coord : ∀ (y : Point3), y ∈ s' →
      |(y : Fin 3 → ℝ) 0| ≤ Real.sqrt 3 ∧
      |(y : Fin 3 → ℝ) 1| ≤ Real.sqrt 3 ∧
      |(y : Fin 3 → ℝ) 2 - c| ≤ width := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxbox : x ∈ Kakeya.Streamlined.axisBox 2 2 2 := hx.1
    have hxslab : |inner ℝ (x - center) normal| ≤ width := hx.2
    have hAx_norm : ‖A x‖ ≤ Real.sqrt 3 := by
      rw [hA_norm] <;> exact h_box_norm x hxbox
    have hinner : |inner ℝ (A x - A center) e3| ≤ width := by
      have h5 : inner ℝ (A x - A center) e3 = inner ℝ (x - center) normal := by
        calc inner ℝ (A x - A center) e3
          = inner ℝ (A (x - center)) (A normal) := by rw [← hA_normal, map_sub] <;> rfl
        _ = inner ℝ (x - center) normal := hA_inner (x - center) normal
      rw [h5] <;> exact hxslab
    have h_y2_eval : inner ℝ (A x) e3 = (A x : Fin 3 → ℝ) 2 := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have hAc : inner ℝ (A center) e3 = c := by
      calc inner ℝ (A center) e3
        = inner ℝ (A center) (A normal) := by rw [hA_normal]
      _ = inner ℝ center normal := hA_inner center normal
      _ = c := rfl
    have h_abs_coord : ∀ (i : Fin 3), |(A x : Fin 3 → ℝ) i| ≤ ‖A x‖ := by
      intro i
      have h_cs : |inner ℝ (A x) (EuclideanSpace.single i (1 : ℝ))| ≤
          ‖A x‖ * ‖(EuclideanSpace.single i (1 : ℝ))‖ :=
        abs_real_inner_le_norm (A x) (EuclideanSpace.single i (1 : ℝ))
      have h2 : inner ℝ (A x) (EuclideanSpace.single i (1 : ℝ)) =
          (A x : Fin 3 → ℝ) i := by
        rw [EuclideanSpace.inner_single_right] <;> simp
      have h3 : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
        rw [PiLp.norm_single] <;> norm_num
      rw [h2, h3] at h_cs <;> linarith
    have h_y0 : |(A x : Fin 3 → ℝ) 0| ≤ Real.sqrt 3 := by
      have h := h_abs_coord 0
      linarith [hAx_norm]
    have h_y1 : |(A x : Fin 3 → ℝ) 1| ≤ Real.sqrt 3 := by
      have h := h_abs_coord 1
      linarith [hAx_norm]
    have h_y2' : |(A x : Fin 3 → ℝ) 2 - c| ≤ width := by
      have h6 : inner ℝ (A x - A center) e3 = (A x : Fin 3 → ℝ) 2 - c := by
        rw [inner_sub_left, h_y2_eval, hAc] <;> rfl
      rw [h6] at hinner
      exact hinner
    exact ⟨h_y0, h_y1, h_y2'⟩

  have h_coord2 : ∀ (z : Fin 3 → ℝ), z ∈ s'' →
      |z 0| ≤ Real.sqrt 3 ∧ |z 1| ≤ Real.sqrt 3 ∧ |z 2 - c| ≤ width := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact h_coord y hy

  have h0 : Function.eval 0 '' s'' ⊆ Set.Icc (-(Real.sqrt 3)) (Real.sqrt 3) := by
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    have h := (h_coord2 z hz).1
    have h' : -Real.sqrt 3 ≤ z 0 ∧ z 0 ≤ Real.sqrt 3 := abs_le.mp h
    exact ⟨h'.1, h'.2⟩
  have h1 : Function.eval 1 '' s'' ⊆ Set.Icc (-(Real.sqrt 3)) (Real.sqrt 3) := by
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    have h := (h_coord2 z hz).2.1
    have h' : -Real.sqrt 3 ≤ z 1 ∧ z 1 ≤ Real.sqrt 3 := abs_le.mp h
    exact ⟨h'.1, h'.2⟩
  have h2 : Function.eval 2 '' s'' ⊆ Set.Icc (c - width) (c + width) := by
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    have h := (h_coord2 z hz).2.2
    have h_abs : -width ≤ z 2 - c ∧ z 2 - c ≤ width := abs_le.mp h
    exact ⟨by linarith, by linarith⟩

  have hdiam0 : Metric.ediam (Function.eval 0 '' s'') ≤ ENNReal.ofReal (2 * Real.sqrt 3) := by
    calc Metric.ediam (Function.eval 0 '' s'')
      ≤ Metric.ediam (Set.Icc (-(Real.sqrt 3)) (Real.sqrt 3)) := Metric.ediam_mono h0
    _ = ENNReal.ofReal (2 * Real.sqrt 3) := by
      rw [Real.ediam_Icc] <;> ring_nf
  have hdiam1 : Metric.ediam (Function.eval 1 '' s'') ≤ ENNReal.ofReal (2 * Real.sqrt 3) := by
    calc Metric.ediam (Function.eval 1 '' s'')
      ≤ Metric.ediam (Set.Icc (-(Real.sqrt 3)) (Real.sqrt 3)) := Metric.ediam_mono h1
    _ = ENNReal.ofReal (2 * Real.sqrt 3) := by
      rw [Real.ediam_Icc] <;> ring_nf
  have hdiam2 : Metric.ediam (Function.eval 2 '' s'') ≤ ENNReal.ofReal (2 * width) := by
    calc Metric.ediam (Function.eval 2 '' s'')
      ≤ Metric.ediam (Set.Icc (c - width) (c + width)) := Metric.ediam_mono h2
    _ = ENNReal.ofReal (2 * width) := by
      rw [Real.ediam_Icc] <;> ring_nf

  have h_prod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' s'')) =
      Metric.ediam (Function.eval 0 '' s'') *
      Metric.ediam (Function.eval 1 '' s'') *
      Metric.ediam (Function.eval 2 '' s'') := by
    simp [Fin.prod_univ_succ] <;> ring
  have hmain : MeasureTheory.volume s'' ≤
      ENNReal.ofReal (2 * Real.sqrt 3) * ENNReal.ofReal (2 * Real.sqrt 3) *
        ENNReal.ofReal (2 * width) := by
    have h := Real.volume_pi_le_prod_diam s''
    rw [h_prod] at h
    exact h.trans (by gcongr <;> assumption)

  have h_arith : ENNReal.ofReal (2 * Real.sqrt 3) * ENNReal.ofReal (2 * Real.sqrt 3) *
      ENNReal.ofReal (2 * width) = ENNReal.ofReal (24 * width) := by
    have h_pos1 : 0 ≤ (2 * Real.sqrt 3 : ℝ) := by positivity
    have h_pos2 : 0 ≤ (2 * width : ℝ) := by positivity
    have h_mul1 : ENNReal.ofReal (2 * Real.sqrt 3) * ENNReal.ofReal (2 * Real.sqrt 3) =
        ENNReal.ofReal ((2 * Real.sqrt 3) ^ 2) := by
      rw [← ENNReal.ofReal_mul h_pos1] <;> ring
    have h_sq : (2 * Real.sqrt 3) ^ 2 = 12 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [h_mul1, h_sq]
    have h_mul2 : ENNReal.ofReal (12 : ℝ) * ENNReal.ofReal (2 * width) =
        ENNReal.ofReal (24 * width) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> norm_num <;> ring
    exact h_mul2

  calc
    MeasureTheory.volume s
      = MeasureTheory.volume s' := hvol
    _ = MeasureTheory.volume s'' := hvol2
    _ ≤ _ := hmain
    _ = ENNReal.ofReal (24 * width) := h_arith

/--
Orthogonal projection onto a tube axis line minimizes distance.
-/
lemma orthogonal_projection_minimizes
    {delta : ℝ} {T : Kakeya.DeltaTube delta} (x : Point3) :
    ∀ (y : Point3), y ∈ tubeAxisLine T →
    ‖x - (T.base + inner ℝ (x - T.base) T.direction • T.direction)‖ ≤ ‖x - y‖ := by
  let s := inner ℝ (x - T.base) T.direction
  let p := T.base + s • T.direction
  have horth : inner ℝ (x - p) T.direction = 0 := by
    have h_expand : x - p = (x - T.base) - s • T.direction := by
      simp [p] <;> abel
    rw [h_expand]
    have h1 : inner ℝ ((x - T.base) - s • T.direction) T.direction =
        inner ℝ (x - T.base) T.direction - inner ℝ (s • T.direction) T.direction := by
      rw [inner_sub_left]
    rw [h1]
    have h2 : inner ℝ (s • T.direction) T.direction = s * inner ℝ T.direction T.direction := by
      simpa [inner_smul_left] using rfl
    rw [h2]
    have h3 : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
      exact real_inner_self_eq_norm_sq T.direction
    rw [h3, T.direction_unit]
    <;> simp [s] <;> ring
  intro y hy
  have h1 : ∃ (t : ℝ), y = T.base + t • T.direction := by
    simpa [tubeAxisLine, Set.mem_setOf_eq] using hy
  rcases h1 with ⟨t, ht⟩
  set y_t : Point3 := T.base + t • T.direction with hy_t_def
  have h_y_eq : y = y_t := ht
  have h_parallel : inner ℝ (x - p) (p - y_t) = 0 := by
    have h : p - y_t = (s - t) • T.direction := by
      simp [p, hy_t_def, sub_smul] <;> abel
    rw [h]
    have h4 : inner ℝ (x - p) ((s - t) • T.direction) = (s - t) * inner ℝ (x - p) T.direction := by
      rw [inner_smul_right]
    rw [h4, horth] <;> ring
  have hpy : ‖x - y_t‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - y_t‖ ^ 2 := by
    have h_sum : x - y_t = (x - p) + (p - y_t) := by abel
    rw [h_sum]
    have h9 := norm_add_sq_real (x - p) (p - y_t)
    rw [h9, h_parallel] <;> ring
  have h_nonneg : 0 ≤ ‖p - y_t‖ ^ 2 := by positivity
  have h12 : ‖x - y_t‖ ^ 2 ≥ ‖x - p‖ ^ 2 := by linarith
  have h13 : 0 ≤ ‖x - p‖ := by positivity
  have h14 : 0 ≤ ‖x - y_t‖ := by positivity
  have h15 : ‖x - p‖ ≤ ‖x - y_t‖ := by nlinarith
  rw [h_y_eq]
  exact h15

/--
Distance from a point to its orthogonal projection on the tube axis line
is bounded by the cthickening radius.
-/
lemma projection_dist_bound
    {delta : ℝ} (hdelta : 0 < delta)
    {T : Kakeya.DeltaTube delta} {x : Point3}
    (hx : x ∈ Metric.cthickening (6 * delta) (tubeAxisLine T)) :
    ‖x - (T.base + inner ℝ (x - T.base) T.direction • T.direction)‖ ≤ 6 * delta := by
  let s := inner ℝ (x - T.base) T.direction
  let p := T.base + s • T.direction
  have hp_line : p ∈ tubeAxisLine T := by
    simp [tubeAxisLine, p] <;> exact ⟨s, rfl⟩
  have hmin : ∀ y ∈ tubeAxisLine T, ‖x - p‖ ≤ ‖x - y‖ :=
    orthogonal_projection_minimizes x

  -- infEDist equals ENNReal.ofReal ‖x - p‖ since p achieves the minimum
  have h_inf_edist : Metric.infEDist x (tubeAxisLine T) = ENNReal.ofReal ‖x - p‖ := by
    have h1 : Metric.infEDist x (tubeAxisLine T) ≤ ENNReal.ofReal ‖x - p‖ := by
      have h11 : Metric.infEDist x (tubeAxisLine T) ≤ edist x p :=
        Metric.infEDist_le_edist_of_mem hp_line
      have h12 : edist x p = ENNReal.ofReal ‖x - p‖ := by
        simp [edist_dist, dist_eq_norm]
      rw [h12] at h11
      exact h11
    have h2 : ENNReal.ofReal ‖x - p‖ ≤ Metric.infEDist x (tubeAxisLine T) := by
      have h21 : ∀ y ∈ tubeAxisLine T, ENNReal.ofReal ‖x - p‖ ≤ edist x y := by
        intro y hy
        have h3 : ‖x - p‖ ≤ ‖x - y‖ := hmin y hy
        have h4 : edist x y = ENNReal.ofReal ‖x - y‖ := by
          simp [edist_dist, dist_eq_norm]
        rw [h4]
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h3
      exact (Metric.le_infEDist).mpr h21
    exact le_antisymm h1 h2

  have h_edist : Metric.infEDist x (tubeAxisLine T) ≤ ENNReal.ofReal (6 * delta) := by
    simpa [Metric.cthickening] using hx
  rw [h_inf_edist] at h_edist
  have h_pos : 0 ≤ ‖x - p‖ := by positivity
  have h6 : 0 ≤ 6 * delta := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff h6).mp h_edist

/--
Paper tube carrier containment in a box slab.

For a paper carrier (6δ-thickening of axis line ∩ axisBox), the strip width
needed is `2√3 · τ + 12δ`:
- Two perpendicular offsets of 6δ each
- Axial separation bounded by `2√3 · τ` (box diameter times direction bound)
-/
lemma paper_tube_contained_in_box_slab
    {delta tau : ℝ} (hdelta : 0 < delta) (htau : 0 ≤ tau)
    {T : Kakeya.DeltaTube delta}
    (normal q : Point3) (hnormal : ‖normal‖ = 1)
    (hq : q ∈ wz1PaperTubeCarrier T)
    (hinner : |inner ℝ T.direction normal| ≤ tau) :
    wz1PaperTubeCarrier T ⊆
      orientedBoxSlab q normal (2 * Real.sqrt 3 * tau + 12 * delta) := by
  intro x hx
  have hx_box : x ∈ Kakeya.Streamlined.axisBox 2 2 2 := hx.2
  have hq_box : q ∈ Kakeya.Streamlined.axisBox 2 2 2 := hq.2
  have hx_thick : x ∈ Metric.cthickening (6 * delta) (tubeAxisLine T) := hx.1
  have hq_thick : q ∈ Metric.cthickening (6 * delta) (tubeAxisLine T) := hq.1

  let s := inner ℝ (x - T.base) T.direction
  let p := T.base + s • T.direction
  let t := inner ℝ (q - T.base) T.direction
  let pq := T.base + t • T.direction

  have hdist_x : ‖x - p‖ ≤ 6 * delta :=
    projection_dist_bound hdelta hx_thick
  have hdist_q : ‖q - pq‖ ≤ 6 * delta :=
    projection_dist_bound hdelta hq_thick

  have hx_box' : |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hx_box
  have hq_box' : |q 0| ≤ 1 ∧ |q 1| ≤ 1 ∧ |q 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hq_box

  have hst : |s - t| ≤ 2 * Real.sqrt 3 := by
    have h_eq : s - t = inner ℝ (x - q) T.direction := by
      simp [s, t, inner_sub_left] <;> ring
    rw [h_eq]
    have h2 : |inner ℝ (x - q) T.direction| ≤ ‖x - q‖ * ‖T.direction‖ :=
      abs_real_inner_le_norm (x - q) T.direction
    have h3 : ‖T.direction‖ = 1 := T.direction_unit
    rw [h3] at h2
    have h4 : ‖x - q‖ ≤ 2 * Real.sqrt 3 := by
      have hx1 : |x 0| ≤ 1 := hx_box'.1
      have hx2 : |x 1| ≤ 1 := hx_box'.2.1
      have hx3 : |x 2| ≤ 1 := hx_box'.2.2
      have hq1 : |q 0| ≤ 1 := hq_box'.1
      have hq2 : |q 1| ≤ 1 := hq_box'.2.1
      have hq3 : |q 2| ≤ 1 := hq_box'.2.2
      have h5 : ‖x - q‖ ^ 2 = (x 0 - q 0)^2 + (x 1 - q 1)^2 + (x 2 - q 2)^2 := by
        have h : ‖x - q‖ = Real.sqrt ((x 0 - q 0)^2 + (x 1 - q 1)^2 + (x 2 - q 2)^2) := by
          simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;> ring
        rw [h]
        rw [Real.sq_sqrt (by positivity)]
      have h6 : |x 0 - q 0| ≤ 2 := by
        calc |x 0 - q 0| ≤ |x 0| + |q 0| := by exact abs_sub (x 0) (q 0)
          _ ≤ 1 + 1 := by gcongr <;> linarith [abs_le.mp hx1, abs_le.mp hq1]
          _ = 2 := by norm_num
      have h7 : |x 1 - q 1| ≤ 2 := by
        calc |x 1 - q 1| ≤ |x 1| + |q 1| := by exact abs_sub (x 1) (q 1)
          _ ≤ 1 + 1 := by gcongr <;> linarith [abs_le.mp hx2, abs_le.mp hq2]
          _ = 2 := by norm_num
      have h8 : |x 2 - q 2| ≤ 2 := by
        calc |x 2 - q 2| ≤ |x 2| + |q 2| := by exact abs_sub (x 2) (q 2)
          _ ≤ 1 + 1 := by gcongr <;> linarith [abs_le.mp hx3, abs_le.mp hq3]
          _ = 2 := by norm_num
      have h9 : ‖x - q‖ ^ 2 ≤ 12 := by
        rw [h5]
        have h10 : (x 0 - q 0)^2 ≤ 4 := by nlinarith [abs_le.mp h6]
        have h11 : (x 1 - q 1)^2 ≤ 4 := by nlinarith [abs_le.mp h7]
        have h12 : (x 2 - q 2)^2 ≤ 4 := by nlinarith [abs_le.mp h8]
        nlinarith
      have h10 : 0 ≤ ‖x - q‖ := by positivity
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    linarith

  set vx := x - p with hvx_def
  set vq := pq - q with hvq_def

  have hnorm_vx : ‖vx‖ ≤ 6 * delta := by
    simpa [hvx_def] using hdist_x
  have hnorm_vq : ‖vq‖ ≤ 6 * delta := by
    have h : ‖q - pq‖ ≤ 6 * delta := hdist_q
    simpa [hvq_def, norm_sub_rev] using h

  have hdecomp :
      inner ℝ (x - q) normal =
        inner ℝ vx normal + inner ℝ (p - pq) normal + inner ℝ vq normal := by
    have h : x - q = vx + (p - pq) + vq := by
      simp [vx, vq] <;> abel
    rw [h]
    simp [inner_add_left]
  have h3 : |inner ℝ vx normal| ≤ 6 * delta := by
    calc |inner ℝ vx normal| ≤ ‖vx‖ * ‖normal‖ := abs_real_inner_le_norm vx normal
      _ = ‖vx‖ := by rw [hnormal] <;> ring
      _ ≤ 6 * delta := hnorm_vx
  have h4 : |inner ℝ vq normal| ≤ 6 * delta := by
    calc |inner ℝ vq normal| ≤ ‖vq‖ * ‖normal‖ := abs_real_inner_le_norm vq normal
      _ = ‖vq‖ := by rw [hnormal] <;> ring
      _ ≤ 6 * delta := hnorm_vq
  have h5 : p - pq = (s - t) • T.direction := by
    simp [p, pq, sub_smul]
  have h6 : |inner ℝ (p - pq) normal| ≤ 2 * Real.sqrt 3 * tau := by
    rw [h5]
    have h7 : inner ℝ ((s - t) • T.direction) normal =
        (s - t) * inner ℝ T.direction normal := by
      simp [inner_smul_left]
    rw [h7, abs_mul]
    calc |s - t| * |inner ℝ T.direction normal|
      ≤ (2 * Real.sqrt 3) * |inner ℝ T.direction normal| := by gcongr
    _ ≤ (2 * Real.sqrt 3) * tau := by gcongr
    _ = 2 * Real.sqrt 3 * tau := by ring
  have h2 : |inner ℝ (x - q) normal| ≤ 2 * Real.sqrt 3 * tau + 12 * delta := by
    rw [hdecomp]
    have h_tri1 : |inner ℝ vx normal + inner ℝ (p - pq) normal + inner ℝ vq normal| ≤
        |inner ℝ vx normal + inner ℝ (p - pq) normal| + |inner ℝ vq normal| :=
      abs_add_le _ _
    have h_tri2 : |inner ℝ vx normal + inner ℝ (p - pq) normal| ≤
        |inner ℝ vx normal| + |inner ℝ (p - pq) normal| := abs_add_le _ _
    linarith
  exact ⟨hx_box, h2⟩

/--
Cropped slab width bound:
`2√3 · τ + 12δ + √ρ ≤ 11 · τ`
when `2δ ≤ τ` and `√ρ ≤ τ`.
-/
lemma cropped_slab_width_bound
    {delta rho tau : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho)
    (h2delta : 2 * delta ≤ tau) (hsqrt_rho : Real.sqrt rho ≤ tau) :
    2 * Real.sqrt 3 * tau + 12 * delta + Real.sqrt rho ≤ 11 * tau := by
  have htau_pos : 0 < tau := by linarith
  have h1 : 12 * delta ≤ 6 * tau := by linarith
  have h2 : Real.sqrt rho ≤ tau := hsqrt_rho
  have h3 : Real.sqrt 3 < 2 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h4 : 2 * Real.sqrt 3 * tau ≤ 4 * tau := by
    have h5 : 2 * Real.sqrt 3 < 4 := by linarith
    exact (mul_lt_mul_of_pos_right h5 htau_pos).le
  linarith

/--
Key ratio inequality without V1:
Given `K < δ^a · ρ^(-σ/2)`, prove
`K · √ρ · δ^(eR-a) < δ^eR · ρ^((1-σ)/2)`.
-/
lemma key_ratio_ineq_noV1
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hsigma : 0 < sigma)
    (K a eR : ℝ) (hK_pos : 0 < K)
    (h_ratio : K < Real.rpow delta a * Real.rpow rho (-sigma / 2)) :
    K * Real.sqrt rho * Real.rpow delta (eR - a) <
      Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := by
  set X : ℝ := Real.rpow delta a with hX
  set Y : ℝ := Real.rpow rho (-sigma / 2) with hY
  have hX_pos : 0 < X := Real.rpow_pos_of_pos hdelta a
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hrho _
  have h_eR_pos : 0 < Real.rpow delta eR := Real.rpow_pos_of_pos hdelta eR
  have h_rho1_pos : 0 < Real.rpow rho ((1 - sigma) / 2) := Real.rpow_pos_of_pos hrho _
  have h_sqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho

  have h_main2 : K * X⁻¹ * Y⁻¹ < 1 := by
    have h_pos5 : 0 < X * Y := mul_pos hX_pos hY_pos
    have h : K < X * Y := h_ratio
    have h2 : K * X⁻¹ * Y⁻¹ = K / (X * Y) := by
      field_simp [hX_pos.ne', hY_pos.ne'] <;> ring
    rw [h2]
    have h3 : K / (X * Y) < (X * Y) / (X * Y) := by gcongr
    have h4 : (X * Y) / (X * Y) = 1 := by
      field_simp [h_pos5.ne']
    linarith

  have h_rpow_delta_neg_a : Real.rpow delta (-a) = X⁻¹ := by
    have h : Real.rpow delta (-a) = (Real.rpow delta a)⁻¹ := Real.rpow_neg (by linarith) a
    simpa [hX] using h
  have h_rpow_rho_sigma2 : Real.rpow rho (sigma / 2) = Y⁻¹ := by
    have h_neg : Real.rpow rho (-(sigma / 2)) = (Real.rpow rho (sigma / 2))⁻¹ :=
      Real.rpow_neg (by linarith) (sigma / 2)
    have hY_eq : Y = Real.rpow rho (-(sigma / 2)) := by
      have h_eq : (-sigma / 2 : ℝ) = -(sigma / 2) := by ring
      simp [hY, h_eq]
    have h9 : Y = (Real.rpow rho (sigma / 2))⁻¹ := by
      rw [hY_eq, h_neg]
    have h10 : 0 < Real.rpow rho (sigma / 2) := Real.rpow_pos_of_pos hrho _
    have h11 : Y⁻¹ = Real.rpow rho (sigma / 2) := by
      rw [h9]; field_simp [h10.ne']
    exact h11.symm

  have h_rpow_delta : Real.rpow delta (eR - a) = Real.rpow delta eR * Real.rpow delta (-a) := by
    have h : eR - a = eR + (-a) := by ring
    rw [h]
    exact Real.rpow_add hdelta eR (-a)
  have h_rpow_rho : Real.sqrt rho = Real.rpow rho ((1 - sigma) / 2) * Real.rpow rho (sigma / 2) := by
    have h_sqrt_eq : Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) := Real.sqrt_eq_rpow rho
    rw [h_sqrt_eq]
    have h2 : (1 / 2 : ℝ) = ((1 - sigma) / 2) + (sigma / 2) := by ring
    rw [h2]
    exact Real.rpow_add hrho ((1 - sigma) / 2) (sigma / 2)

  calc
    K * Real.sqrt rho * Real.rpow delta (eR - a)
      = K * (Real.rpow rho ((1 - sigma) / 2) * Real.rpow rho (sigma / 2)) *
          (Real.rpow delta eR * Real.rpow delta (-a)) := by
        rw [h_rpow_delta, h_rpow_rho]
    _ = Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) *
          (K * Real.rpow delta (-a) * Real.rpow rho (sigma / 2)) := by ring
    _ = Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) * (K * X⁻¹ * Y⁻¹) := by
      rw [h_rpow_delta_neg_a, h_rpow_rho_sigma2] <;> ring
    _ < Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) * 1 := by
      have h_pos6 : 0 < Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) :=
        mul_pos h_eR_pos h_rho1_pos
      exact mul_lt_mul_of_pos_left h_main2 h_pos6
    _ = Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := by ring

/--
Convert absorption `K · 64^(σ/2) < δ^E` and `ρ ≤ 64 · δ^(2ε)`
to `K < δ^a · ρ^(-σ/2)` where `E = a - εσ`.
-/
lemma absorption_to_ratio_noV1
    {delta rho epsilon sigma : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    (K : ℝ) (hK_pos : 0 < K)
    (hrho_bound : rho ≤ 64 * Real.rpow delta (2 * epsilon))
    (a E : ℝ) (hE : E = a - epsilon * sigma)
    (h_absorb : K * Real.rpow 64 (sigma / 2) < Real.rpow delta E) :
    K < Real.rpow delta a * Real.rpow rho (-sigma / 2) := by
  have h64_pos : (0 : ℝ) < 64 := by norm_num
  have h64_nonneg : (0 : ℝ) ≤ 64 := by norm_num
  have hdelta_le : 0 ≤ delta := by linarith
  have h_rpow2eps_pos : 0 < Real.rpow delta (2 * epsilon) :=
    Real.rpow_pos_of_pos hdelta (2 * epsilon)
  set B : ℝ := 64 * Real.rpow delta (2 * epsilon) with hB_def
  have hB_pos : 0 < B := mul_pos h64_pos h_rpow2eps_pos
  let z : ℝ := -sigma / 2
  let z' : ℝ := sigma / 2
  have hz'_pos : 0 < z' := by dsimp only [z']; linarith
  have hz_eq : z = -z' := by simp [z, z'] <;> ring

  have h_rpow_split : Real.rpow delta E = Real.rpow delta a * Real.rpow delta (-epsilon * sigma) := by
    rw [hE]
    have h : a - epsilon * sigma = a + (-epsilon * sigma) := by ring
    rw [h]
    exact Real.rpow_add hdelta a (-epsilon * sigma)

  have h_absorb' : K * Real.rpow 64 z' <
      Real.rpow delta a * Real.rpow delta (-epsilon * sigma) := by
    have h1 : Real.rpow 64 z' = Real.rpow 64 (sigma / 2) := by simp [z'] <;> ring
    rw [h1]
    rw [h_rpow_split] at h_absorb
    exact h_absorb

  have h_rpow_B : Real.rpow B z = Real.rpow 64 z * Real.rpow delta (-epsilon * sigma) := by
    have h_mul1 : Real.rpow B z = Real.rpow 64 z * Real.rpow (Real.rpow delta (2 * epsilon)) z := by
      have h := Real.mul_rpow (x := (64 : ℝ)) (y := Real.rpow delta (2 * epsilon)) (z := z)
        h64_nonneg (by positivity)
      have hB : B = 64 * Real.rpow delta (2 * epsilon) := by simp [B, hB_def]
      rw [hB]; exact h
    rw [h_mul1]
    have h_tower : Real.rpow (Real.rpow delta (2 * epsilon)) z =
        Real.rpow delta ((2 * epsilon) * z) := by
      have h : Real.rpow delta ((2 * epsilon) * z) =
          Real.rpow (Real.rpow delta (2 * epsilon)) z :=
        Real.rpow_mul hdelta_le (2 * epsilon) z
      exact h.symm
    rw [h_tower]
    have h4 : (2 * epsilon) * z = -epsilon * sigma := by simp [z] <;> ring
    rw [h4]

  have h_neg_mon : ∀ (x y : ℝ), 0 < x → x ≤ y →
      Real.rpow x z ≥ Real.rpow y z := by
    intro x y hx hxy
    have hx_nonneg : 0 ≤ x := by linarith
    have hy_nonneg : 0 ≤ y := by linarith
    have h1 : Real.rpow x z' ≤ Real.rpow y z' :=
      Real.rpow_le_rpow hx_nonneg hxy hz'_pos.le
    have h2 : 0 < Real.rpow x z' := Real.rpow_pos_of_pos hx z'
    have h3 : 0 < Real.rpow y z' := Real.rpow_pos_of_pos (by linarith) z'
    have h4 : (Real.rpow x z')⁻¹ ≥ (Real.rpow y z')⁻¹ := by gcongr
    have h51 : Real.rpow x z = Real.rpow x (-z') := by rw [hz_eq]
    have h52 : Real.rpow x (-z') = (Real.rpow x z')⁻¹ := Real.rpow_neg hx_nonneg z'
    have h61 : Real.rpow y z = Real.rpow y (-z') := by rw [hz_eq]
    have h62 : Real.rpow y (-z') = (Real.rpow y z')⁻¹ := Real.rpow_neg hy_nonneg z'
    calc Real.rpow x z = Real.rpow x (-z') := h51
      _ = (Real.rpow x z')⁻¹ := h52
      _ ≥ (Real.rpow y z')⁻¹ := h4
      _ = Real.rpow y (-z') := h62.symm
      _ = Real.rpow y z := by rw [hz_eq]

  have h_rho_lower : Real.rpow rho z ≥ Real.rpow 64 z * Real.rpow delta (-epsilon * sigma) := by
    have h1 : Real.rpow rho z ≥ Real.rpow B z := h_neg_mon rho B hrho hrho_bound
    rw [h_rpow_B] at h1
    exact h1

  have h_rpow64_inv : Real.rpow 64 z' * Real.rpow 64 z = 1 := by
    have h : Real.rpow 64 (z' + z) = Real.rpow 64 z' * Real.rpow 64 z :=
      Real.rpow_add h64_pos z' z
    have h2 : z' + z = 0 := by simp [z, z'] <;> ring
    have h3 : Real.rpow 64 (0 : ℝ) = 1 := by simp
    have h4 : Real.rpow 64 (z' + z) = 1 := by rw [h2, h3]
    rw [h4] at h
    exact h.symm

  have h64_z_pos : 0 < Real.rpow 64 z := Real.rpow_pos_of_pos h64_pos z
  have h_pos_a : 0 < Real.rpow delta a := Real.rpow_pos_of_pos hdelta a

  set P : ℝ := Real.rpow delta a * Real.rpow delta (-epsilon * sigma) with hP_def
  have h : K * Real.rpow 64 z' < P := h_absorb'
  have h_mul : (K * Real.rpow 64 z') * Real.rpow 64 z < P * Real.rpow 64 z :=
    mul_lt_mul_of_pos_right h h64_z_pos
  have h_left : (K * Real.rpow 64 z') * Real.rpow 64 z = K := by
    calc (K * Real.rpow 64 z') * Real.rpow 64 z
      = K * (Real.rpow 64 z' * Real.rpow 64 z) := by ring
    _ = K * 1 := by rw [h_rpow64_inv]
    _ = K := by ring
  have h_right : P * Real.rpow 64 z =
      Real.rpow delta a * (Real.rpow delta (-epsilon * sigma) * Real.rpow 64 z) := by
    simp [hP_def] <;> ring
  rw [h_left, h_right] at h_mul

  have h9 : Real.rpow delta (-epsilon * sigma) * Real.rpow 64 z ≤ Real.rpow rho z := by
    have h10 : Real.rpow delta (-epsilon * sigma) * Real.rpow 64 z =
        Real.rpow 64 z * Real.rpow delta (-epsilon * sigma) := by ring
    rw [h10]
    exact h_rho_lower
  have h11 : 0 < Real.rpow delta a := h_pos_a
  have h_final : Real.rpow delta a * (Real.rpow delta (-epsilon * sigma) * Real.rpow 64 z) ≤
      Real.rpow delta a * Real.rpow rho z :=
    mul_le_mul_of_nonneg_left h9 h11.le

  have h_goal : K < Real.rpow delta a * Real.rpow rho z := h_mul.trans_le h_final
  simpa [z] using h_goal

/--
Full cropped real inequality: `δ^(-η) · vol · card < count` (no V1).
-/
lemma cropped_convex_overload_final_ineq_real
    {delta rho epsilon sigma eta vol card count : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hvol_nonneg : 0 ≤ vol) (hcard_nonneg : 0 ≤ card) (hcount_nonneg : 0 ≤ count)
    (K : ℝ) (hK_pos : 0 < K)
    (C_count : ℝ) (hC_count : 1 ≤ C_count)
    (hvol : vol ≤ K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)))
    (hcard : card ≤ Real.rpow delta (-2 - eta / 1000))
    (hactive : (C_count)⁻¹ * Real.rpow delta (24 * eta - 2) * Real.rpow rho ((1 - sigma) / 2) ≤ count)
    (hrho_bound : rho ≤ 64 * Real.rpow delta (2 * epsilon))
    (h_absorb : C_count * K * Real.rpow 64 (sigma / 2) <
        Real.rpow delta (25 * eta + 36 * eta / sigma + eta / 1000 - epsilon * sigma)) :
    Real.rpow delta (-eta) * vol * card < count := by
  set a : ℝ := 25 * eta + 36 * eta / sigma + eta / 1000 with ha_def
  set eR : ℝ := 24 * eta - 2 with heR_def
  set eL : ℝ := -eta - 36 * eta / sigma - 2 - eta / 1000 with heL_def
  set K' : ℝ := C_count * K with hK'_def
  have hK'_pos : 0 < K' := by positivity
  have hC_count_pos : 0 < C_count := by linarith
  have h_exp_rel : eL = eR - a := by
    simp [heL_def, heR_def, ha_def] <;> ring

  have h_ratio : K' < Real.rpow delta a * Real.rpow rho (-sigma / 2) :=
    absorption_to_ratio_noV1 hdelta hrho hsigma hepsilon K' hK'_pos hrho_bound a
      (a - epsilon * sigma) (by ring) h_absorb

  have h_key : K' * Real.sqrt rho * Real.rpow delta eL <
      Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := by
    rw [h_exp_rel]
    exact key_ratio_ineq_noV1 hdelta hrho hsigma K' a eR hK'_pos h_ratio

  have h_key_scaled : K * Real.sqrt rho * Real.rpow delta eL <
      (C_count)⁻¹ * Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := by
    have h1 : K' * Real.sqrt rho * Real.rpow delta eL =
        C_count * (K * Real.sqrt rho * Real.rpow delta eL) := by
      simp [hK'_def] <;> ring
    have h2 : C_count * (K * Real.sqrt rho * Real.rpow delta eL) <
        Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := by
      rw [←h1]; exact h_key
    have h3 : 0 < C_count := hC_count_pos
    have h4 : K * Real.sqrt rho * Real.rpow delta eL <
        (C_count)⁻¹ * Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := by
      calc
        K * Real.sqrt rho * Real.rpow delta eL
          = (C_count)⁻¹ * (C_count * (K * Real.sqrt rho * Real.rpow delta eL)) := by
            field_simp [h3.ne'] <;> ring
        _ < (C_count)⁻¹ * (Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2)) := by
          gcongr
        _ = (C_count)⁻¹ * Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := by ring
    exact h4

  have hLHS : Real.rpow delta (-eta) * vol * card ≤
      K * Real.sqrt rho * Real.rpow delta eL := by
    have h1 : Real.rpow delta (-eta) * Real.rpow delta (-(36 * eta / sigma)) =
        Real.rpow delta (-eta - 36 * eta / sigma) := by
      have h := Real.rpow_add hdelta (-eta) (-(36 * eta / sigma))
      have h_sum : (-eta) + (-(36 * eta / sigma)) = -eta - 36 * eta / sigma := by ring
      rw [h_sum] at h; exact h.symm
    have h2 : Real.rpow delta (-eta - 36 * eta / sigma) * Real.rpow delta (-2 - eta / 1000) =
        Real.rpow delta eL := by
      have h3 : (-eta - 36 * eta / sigma) + (-2 - eta / 1000) = eL := by
        simp [heL_def] <;> ring
      have h4 := Real.rpow_add hdelta (-eta - 36 * eta / sigma) (-2 - eta / 1000)
      rw [h3] at h4; exact h4.symm
    have h3 : 0 ≤ Real.rpow delta (-eta) := Real.rpow_nonneg hdelta.le (-eta)
    have h44 : 0 ≤ K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)) := by
      have hK : 0 ≤ K := by linarith
      have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
      have hrpow : 0 ≤ Real.rpow delta (-(36 * eta / sigma)) := Real.rpow_nonneg hdelta.le _
      exact mul_nonneg (mul_nonneg hK hsqrt) hrpow
    calc
      Real.rpow delta (-eta) * vol * card
        = (Real.rpow delta (-eta) * vol) * card := by ring
      _ ≤ (Real.rpow delta (-eta) * (K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)))) * card := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol h3) hcard_nonneg
      _ ≤ (Real.rpow delta (-eta) * (K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)))) *
            Real.rpow delta (-2 - eta / 1000) := by
        exact mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = K * Real.sqrt rho * (Real.rpow delta (-eta) * Real.rpow delta (-(36 * eta / sigma)) *
            Real.rpow delta (-2 - eta / 1000)) := by ring
      _ = K * Real.sqrt rho * Real.rpow delta eL := by rw [h1, h2] <;> ring

  have hRHS : (C_count)⁻¹ * Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) ≤ count := by
    simpa [heR_def] using hactive

  calc
    Real.rpow delta (-eta) * vol * card
      ≤ K * Real.sqrt rho * Real.rpow delta eL := hLHS
    _ < (C_count)⁻¹ * Real.rpow delta eR * Real.rpow rho ((1 - sigma) / 2) := h_key_scaled
    _ ≤ count := hRHS

/--
Card-cancellation version of the final real inequality for cropped convex overload.

The family cardinality `card` appears on both sides and cancels.
Key absorption: `4608 * K * 64^(sigma/2) / pi < delta^(loss + 13*eta + 36*eta/sigma - epsilon*sigma)`.
-/
lemma cropped_convex_overload_final_ineq_card
    {delta rho epsilon sigma eta loss vol card count ba : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hcard_pos : 0 < card) (hba_pos : 0 < ba)
    (K : ℝ) (hK_pos : 0 < K)
    (hrho_eq : rho = 64 * ba ^ 2)
    (hvol : vol ≤ K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)))
    (hactive : (Real.pi / (576 * Real.rpow 64 (sigma / 2))) *
        Real.rpow delta (loss + 12 * eta) * card * Real.rpow ba (1 - sigma) ≤ count)
    (hba_eps : ba ≤ Real.rpow delta epsilon)
    (h_absorb : (4608 * K * Real.rpow 64 (sigma / 2) / Real.pi) <
        Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma)) :
    Real.rpow delta (-eta) * vol * card < count := by
  have hsqrt_rho : Real.sqrt rho = 8 * ba := by
    rw [hrho_eq]
    have h1 : 0 ≤ ba := by linarith
    have h2 : Real.sqrt (64 * ba ^ 2) = 8 * ba := by
      rw [Real.sqrt_mul (by positivity)]
      have h3 : Real.sqrt (ba ^ 2) = ba := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h1]
      rw [h3]
      have h4 : Real.sqrt 64 = 8 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h4] <;> ring
    exact h2
  set C_active : ℝ := Real.pi / (576 * Real.rpow 64 (sigma / 2)) with hC_active_def
  have h64_pos : 0 < Real.rpow 64 (sigma / 2) := Real.rpow_pos_of_pos (by norm_num) (sigma / 2)
  have hC_active_pos : 0 < C_active := by
    dsimp only [C_active]
    exact div_pos Real.pi_pos (mul_pos (by norm_num) h64_pos)
  have h8K_div_C : 8 * K / C_active = 4608 * K * Real.rpow 64 (sigma / 2) / Real.pi := by
    simp [hC_active_def] <;> field_simp <;> ring

  -- ba^{-σ} ≥ δ^{-εσ} since ba ≤ δ^ε and -σ < 0
  have h_ba_neg_sigma : Real.rpow ba (-sigma) ≥ Real.rpow delta (-epsilon * sigma) := by
    have h1 : 0 ≤ ba := by linarith
    have h2 : ba ≤ Real.rpow delta epsilon := hba_eps
    have h3 : Real.rpow (Real.rpow delta epsilon) (-sigma) ≤ Real.rpow ba (-sigma) :=
      Real.rpow_le_rpow_of_nonpos hba_pos h2 (by linarith)
    have h4 : Real.rpow (Real.rpow delta epsilon) (-sigma) = Real.rpow delta (-epsilon * sigma) := by
      have h5 : Real.rpow delta (epsilon * (-sigma)) = Real.rpow (Real.rpow delta epsilon) (-sigma) :=
        Real.rpow_mul hdelta.le epsilon (-sigma)
      have h6 : epsilon * (-sigma) = -epsilon * sigma := by ring
      rw [h6] at h5
      exact h5.symm
    rw [h4] at h3
    exact h3

  -- 8K * δ^{-η-36η/σ} < C_active * δ^{loss+12η-εσ}
  have h_key1 : 8 * K * Real.rpow delta (-eta - 36 * eta / sigma) <
      C_active * Real.rpow delta (loss + 12 * eta - epsilon * sigma) := by
    have h_pos_rpow : 0 < Real.rpow delta (-eta - 36 * eta / sigma) := Real.rpow_pos_of_pos hdelta _
    have h_absorb' : 8 * K / C_active <
        Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) := by
      rw [h8K_div_C]; exact h_absorb
    have h_mul : (8 * K / C_active) * (C_active * Real.rpow delta (-eta - 36 * eta / sigma)) <
        Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) *
          (C_active * Real.rpow delta (-eta - 36 * eta / sigma)) :=
      mul_lt_mul_of_pos_right h_absorb' (mul_pos hC_active_pos h_pos_rpow)
    have h_lhs : (8 * K / C_active) * (C_active * Real.rpow delta (-eta - 36 * eta / sigma)) =
        8 * K * Real.rpow delta (-eta - 36 * eta / sigma) := by
      field_simp [hC_active_pos.ne'] <;> ring
    have h_rhs : Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) *
          (C_active * Real.rpow delta (-eta - 36 * eta / sigma)) =
        C_active * Real.rpow delta (loss + 12 * eta - epsilon * sigma) := by
      have h_comm : Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) *
          (C_active * Real.rpow delta (-eta - 36 * eta / sigma)) =
          C_active * (Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) *
            Real.rpow delta (-eta - 36 * eta / sigma)) := by ring
      rw [h_comm]
      have h_sum : (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) + (-eta - 36 * eta / sigma) =
          loss + 12 * eta - epsilon * sigma := by ring
      have h_add : Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) *
          Real.rpow delta (-eta - 36 * eta / sigma) =
          Real.rpow delta (loss + 12 * eta - epsilon * sigma) := by
        have h_raw : Real.rpow delta ((loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) + (-eta - 36 * eta / sigma)) =
            Real.rpow delta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) *
            Real.rpow delta (-eta - 36 * eta / sigma) :=
          Real.rpow_add hdelta (loss + 13 * eta + 36 * eta / sigma - epsilon * sigma) (-eta - 36 * eta / sigma)
        rw [h_sum] at h_raw
        exact h_raw.symm
      rw [h_add] <;> ring
    rw [h_lhs, h_rhs] at h_mul
    exact h_mul

  -- 8K * ba * δ^{-η-36η/σ} < C_active * δ^{loss+12η} * ba^{1-σ}
  have h_key2 : 8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) <
      C_active * Real.rpow delta (loss + 12 * eta) * Real.rpow ba (1 - sigma) := by
    have h1_raw : (8 * K * Real.rpow delta (-eta - 36 * eta / sigma)) * ba <
        (C_active * Real.rpow delta (loss + 12 * eta - epsilon * sigma)) * ba :=
      mul_lt_mul_of_pos_right h_key1 hba_pos
    have h1 : 8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) <
        C_active * ba * Real.rpow delta (loss + 12 * eta - epsilon * sigma) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h1_raw
    have h_ba_exp : Real.rpow ba (1 - sigma) = ba * Real.rpow ba (-sigma) := by
      have h5 : Real.rpow ba (1 - sigma) = Real.rpow ba 1 * Real.rpow ba (-sigma) := by
        have h6 : Real.rpow ba (1 + (-sigma)) = Real.rpow ba 1 * Real.rpow ba (-sigma) :=
          Real.rpow_add hba_pos 1 (-sigma)
        have h7 : 1 + (-sigma) = 1 - sigma := by ring
        rw [h7] at h6
        exact h6
      rw [h5]
      have h6 : Real.rpow ba 1 = ba := by simp
      rw [h6] <;> ring
    have h2 : C_active * ba * Real.rpow delta (loss + 12 * eta - epsilon * sigma) ≤
        C_active * Real.rpow delta (loss + 12 * eta) * Real.rpow ba (1 - sigma) := by
      have h3 : Real.rpow delta (loss + 12 * eta - epsilon * sigma) =
          Real.rpow delta (loss + 12 * eta) * Real.rpow delta (-epsilon * sigma) := by
        have h4 : Real.rpow delta ((loss + 12 * eta) + (-epsilon * sigma)) =
            Real.rpow delta (loss + 12 * eta) * Real.rpow delta (-epsilon * sigma) :=
          Real.rpow_add hdelta (loss + 12 * eta) (-epsilon * sigma)
        have h5 : (loss + 12 * eta) + (-epsilon * sigma) = loss + 12 * eta - epsilon * sigma := by ring
        rw [h5] at h4
        exact h4
      rw [h3, h_ba_exp]
      have h4 : C_active * ba * (Real.rpow delta (loss + 12 * eta) * Real.rpow delta (-epsilon * sigma)) ≤
          C_active * Real.rpow delta (loss + 12 * eta) * (ba * Real.rpow ba (-sigma)) := by
        have h5 : Real.rpow delta (-epsilon * sigma) ≤ Real.rpow ba (-sigma) := h_ba_neg_sigma
        have hX_pos : 0 < C_active * Real.rpow delta (loss + 12 * eta) * ba :=
          mul_pos (mul_pos hC_active_pos (Real.rpow_pos_of_pos hdelta _)) hba_pos
        have h6 : (C_active * Real.rpow delta (loss + 12 * eta) * ba) * Real.rpow delta (-epsilon * sigma) ≤
            (C_active * Real.rpow delta (loss + 12 * eta) * ba) * Real.rpow ba (-sigma) :=
          mul_le_mul_of_nonneg_left h5 hX_pos.le
        simpa [mul_assoc, mul_comm, mul_left_comm] using h6
      simpa [mul_assoc] using h4
    exact lt_of_lt_of_le h1 h2

  -- LHS ≤ 8K * ba * δ^{-η-36η/σ} * card
  have hLHS : Real.rpow delta (-eta) * vol * card ≤
      8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) * card := by
    have h1 : Real.rpow delta (-eta) * vol ≤
        Real.rpow delta (-eta) * (K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma))) :=
      mul_le_mul_of_nonneg_left hvol (Real.rpow_nonneg hdelta.le _)
    have h2 : Real.rpow delta (-eta) * (K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma))) =
        8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) := by
      rw [hsqrt_rho]
      have h3 : Real.rpow delta (-eta) * Real.rpow delta (-(36 * eta / sigma)) =
          Real.rpow delta (-eta - 36 * eta / sigma) := by
        have h_sum : (-eta) + (-(36 * eta / sigma)) = -eta - 36 * eta / sigma := by ring
        have h_raw : Real.rpow delta ((-eta) + (-(36 * eta / sigma))) =
            Real.rpow delta (-eta) * Real.rpow delta (-(36 * eta / sigma)) :=
          Real.rpow_add hdelta (-eta) (-(36 * eta / sigma))
        rw [h_sum] at h_raw
        exact h_raw.symm
      have h_goal : Real.rpow delta (-eta) * (K * (8 * ba) * Real.rpow delta (-(36 * eta / sigma))) =
          (Real.rpow delta (-eta) * Real.rpow delta (-(36 * eta / sigma))) * (8 * K * ba) := by ring
      rw [h_goal, h3] <;> ring
    calc
      Real.rpow delta (-eta) * vol * card
        = (Real.rpow delta (-eta) * vol) * card := by ring
      _ ≤ (Real.rpow delta (-eta) * (K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)))) * card := by gcongr
      _ = 8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) * card := by rw [h2] <;> ring

  have h_main : 8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) * card <
      C_active * Real.rpow delta (loss + 12 * eta) * card * Real.rpow ba (1 - sigma) := by
    have h : 8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) <
        C_active * Real.rpow delta (loss + 12 * eta) * Real.rpow ba (1 - sigma) := h_key2
    have h' : (8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma)) * card <
        (C_active * Real.rpow delta (loss + 12 * eta) * Real.rpow ba (1 - sigma)) * card :=
      mul_lt_mul_of_pos_right h hcard_pos
    simpa [mul_assoc, mul_comm, mul_left_comm] using h'

  have h_final : C_active * Real.rpow delta (loss + 12 * eta) * card * Real.rpow ba (1 - sigma) ≤ count := by
    have hactive_eq : C_active * Real.rpow delta (loss + 12 * eta) * card * Real.rpow ba (1 - sigma) =
        (Real.pi / (576 * Real.rpow 64 (sigma / 2))) *
          Real.rpow delta (loss + 12 * eta) * card * Real.rpow ba (1 - sigma) := by
      simp [hC_active_def] <;> ring
    rw [hactive_eq]
    exact hactive
  calc
    Real.rpow delta (-eta) * vol * card
      ≤ 8 * K * ba * Real.rpow delta (-eta - 36 * eta / sigma) * card := hLHS
    _ < C_active * Real.rpow delta (loss + 12 * eta) * card * Real.rpow ba (1 - sigma) := h_main
    _ ≤ count := h_final

/-- Convert the real pigeonhole inequality into the card-proportional active
count bound used by the cropped final inequality.  Keeping this algebra in a
separate declaration lets the main geometric theorem elaborate under the
default heartbeat budget. -/
lemma cropped_active_count_from_pigeonhole
    {delta rho sigma eta loss card count ba : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hba : 0 < ba)
    (hpi : (Real.pi / 16) * Real.rpow delta (loss + 2) * card * ba ≤
      (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
        Real.rpow 64 (sigma / 2) * Real.rpow ba sigma * count) :
    (Real.pi / (576 * Real.rpow 64 (sigma / 2))) *
        Real.rpow delta (loss + 12 * eta) * card *
          Real.rpow ba (1 - sigma) ≤ count := by
  have h64 : 0 < Real.rpow 64 (sigma / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hba_sigma : 0 < Real.rpow ba sigma :=
    Real.rpow_pos_of_pos hba _
  have hdelta_power : 0 < Real.rpow delta (-(12 * eta) + 2) :=
    Real.rpow_pos_of_pos hdelta _
  have hdenom :
      0 < (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
        Real.rpow 64 (sigma / 2) * Real.rpow ba sigma := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hdelta_power) h64) hba_sigma
  have hpi' :
      (Real.pi / 16) * Real.rpow delta (loss + 2) * card * ba ≤
        count * ((36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
          Real.rpow 64 (sigma / 2) * Real.rpow ba sigma) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpi
  have hdiv := div_le_iff₀ hdenom |>.mpr hpi'
  have hconst :
      Real.pi / (576 * Real.rpow 64 (sigma / 2)) =
        (Real.pi / 16) / (36 * Real.rpow 64 (sigma / 2)) := by
    field_simp [h64.ne']
    ring
  have hdelta_ratio :
      Real.rpow delta (loss + 12 * eta) =
        Real.rpow delta (loss + 2) /
          Real.rpow delta (-(12 * eta) + 2) := by
    calc
      Real.rpow delta (loss + 12 * eta) =
          Real.rpow delta ((loss + 2) - (-(12 * eta) + 2)) := by
            congr 1
            ring
      _ = Real.rpow delta (loss + 2) /
          Real.rpow delta (-(12 * eta) + 2) :=
            Real.rpow_sub hdelta (loss + 2) (-(12 * eta) + 2)
  have hba_ratio :
      Real.rpow ba (1 - sigma) = ba / Real.rpow ba sigma := by
    have h := Real.rpow_sub hba 1 sigma
    simpa using h
  have heq :
      (Real.pi / (576 * Real.rpow 64 (sigma / 2))) *
          Real.rpow delta (loss + 12 * eta) * card *
            Real.rpow ba (1 - sigma) =
        ((Real.pi / 16) * Real.rpow delta (loss + 2) * card * ba) /
          ((36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
            Real.rpow 64 (sigma / 2) * Real.rpow ba sigma) := by
    rw [hconst, hdelta_ratio, hba_ratio]
    field_simp [hdelta_power.ne', h64.ne', hba_sigma.ne']
  rw [heq]
  exact hdiv

/-- Cropped convex overload statement (Option B, paper-carrier form). -/
def LargeSlopeCroppedConvexOverloadStatement : Prop :=
  ∀ epsilon sigma eta loss : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < sigma → sigma < 1 →
    0 < eta → eta ≤ epsilon →
    loss ≤ eta →
    1000 * eta ≤ epsilon * sigma ^ 2 →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
          (C : ENNReal) (a b : ℝ)
          (refined : LargeSlopeCroppedRefinementData cfg eta C a b),
          b - a ≤ Real.rpow delta epsilon →
          ∀ step4 : LargeSlopeCroppedStep4Witness refined.shading sigma eta a b,
            ∃ W : Set Point3,
              Convex ℝ W ∧
              Kakeya.realRpowENN delta (-eta) *
                MeasureTheory.volume W * cfg.family.enncard <
                (wz1PaperBodyFamily cfg.family).containedCount W

/--
Cropped large-slope convex overload (paper-carrier form).

Produces a convex set W whose paper-body containedCount exceeds
`δ^(-η) · volume(W) · |F|`, directly contradicting the paper CWA.
-/
theorem large_slope_cropped_convex_overload :
    LargeSlopeCroppedConvexOverloadStatement := by
  intro epsilon sigma eta loss hepsilon hepsilon_half hsigma hsigma1 heta heta_epsilon hloss_le_eta hgap

  set eta' : ℝ := 12 * eta with heta'_def
  have heta'_pos : 0 < eta' := by positivity

  -- 1. Direction bound threshold
  rcases paper_tube_segment_ad_direction_bound
      tube_segment_projection_covering_lower_bound
      tube_segment_projection_localization
      ad_covering_comparison_with_constant
      sigma eta' hsigma hsigma1 heta'_pos with
    ⟨delta₁, hdelta₁_pos, hdelta₁_one, hdir_bound⟩

  -- 2. Slab width threshold (2*delta ≤ tau)
  set e_width : ℝ := 36 * eta / sigma with he_width_def
  have he_width_pos : 0 < e_width := by positivity
  rcases exists_delta_slab_width he_width_pos with
    ⟨delta₂, hdelta₂_pos, hdelta₂_one, hwidth_threshold⟩

  -- 3. Absorption threshold for final inequality
  set exp : ℝ := loss + 13 * eta + 36 * eta / sigma - epsilon * sigma with hexp_def
  have hexp_neg : exp < 0 := large_slope_exponent_negative_card hsigma hsigma1 heta hloss_le_eta hgap

  set K : ℝ := 1024 with hK_def
  have hK_pos : 0 < K := by norm_num [hK_def]
  set C_real : ℝ := 4608 * K * Real.rpow 64 (sigma / 2) / Real.pi with hC_real_def
  have h64pow_pos : 0 < Real.rpow 64 (sigma / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hC_real_pos : 0 < C_real := by
    rw [hC_real_def]; positivity
  set C_enn : ENNReal := ENNReal.ofReal C_real with hC_enn_def
  have hC_enn_ne_top : C_enn ≠ ⊤ := ENNReal.ofReal_ne_top

  rcases exists_delta_absorb_constant_ennreal hC_enn_ne_top exp hexp_neg with
    ⟨delta₃, hdelta₃_pos, hdelta₃_one, h_absorb_enn⟩

  -- Global threshold
  let delta₀ : ℝ := min (min delta₁ delta₂) delta₃
  have hdelta₀_pos : 0 < delta₀ := by
    exact lt_min (lt_min hdelta₁_pos hdelta₂_pos) hdelta₃_pos
  have hdelta₀_one : delta₀ ≤ 1 := by
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hdelta₁_one)

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le cfg C a b refined hba step4

  have hdelta₁' : delta ≤ delta₁ := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ min delta₁ delta₂ := min_le_left _ _
         _ ≤ delta₁ := min_le_left _ _
  have hdelta₂' : delta ≤ delta₂ := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ min delta₁ delta₂ := min_le_left _ _
         _ ≤ delta₂ := min_le_right _ _
  have hdelta₃' : delta ≤ delta₃ := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ delta₃ := min_le_right _ _

  set rho : ℝ := step4.rho with hrho_def
  have hrho_pos : 0 < rho := step4.rho_pos
  have hdelta_rho : delta ≤ rho := step4.delta_le_rho
  have hrho_le_quarter : rho ≤ 1 / 4 := step4.rho_le_quarter

  -- rho ≤ 64 * delta^(2*epsilon)
  have hrho_upper : rho ≤ 64 * Real.rpow delta (2 * epsilon) := by
    have h_order : a < b := refined.ordered
    have hba_pos : 0 < b - a := by linarith
    have h1 : b - a ≤ Real.rpow delta epsilon := hba
    have h1' : 0 ≤ Real.rpow delta epsilon := Real.rpow_nonneg hdelta.le epsilon
    have h2 : (b - a) ^ 2 ≤ (Real.rpow delta epsilon) ^ 2 := by gcongr
    have h3 : (Real.rpow delta epsilon) ^ 2 = Real.rpow delta (2 * epsilon) := by
      have h31 : (Real.rpow delta epsilon) ^ 2 = Real.rpow delta epsilon * Real.rpow delta epsilon := by ring
      rw [h31]
      have h32 : Real.rpow delta epsilon * Real.rpow delta epsilon = Real.rpow delta (epsilon + epsilon) :=
        (Real.rpow_add hdelta epsilon epsilon).symm
      rw [h32]
      have h33 : epsilon + epsilon = 2 * epsilon := by ring
      rw [h33]
    have h4 : rho = 64 * (b - a) ^ 2 := step4.rho_eq
    rw [h4]
    rw [h3] at h2
    linarith

  -- tau = sqrt(rho) * delta^(-36*eta/sigma)
  set tau : ℝ := Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)) with htau_def
  have htau_nonneg : 0 ≤ tau := by
    have h1 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    have h2 : 0 ≤ Real.rpow delta (-(36 * eta / sigma)) := Real.rpow_nonneg hdelta.le _
    exact mul_nonneg h1 h2

  -- 2*delta ≤ tau (from width threshold)
  have h2delta_le_tau : 2 * delta ≤ tau :=
    hwidth_threshold delta rho hdelta hdelta₂' hdelta_rho

  -- sqrt(rho) ≤ tau
  have hsqrt_rho_le_tau : Real.sqrt rho ≤ tau := by
    rw [htau_def]
    have h1 : Real.rpow delta (-(36 * eta / sigma)) ≥ 1 :=
      rpow_neg_ge_one hdelta (le_trans hdelta₁' hdelta₁_one) he_width_pos
    have h4 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    calc Real.sqrt rho ≤ Real.sqrt rho * 1 := by linarith
      _ ≤ Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)) := by gcongr

  -- Pigeonhole: select heavy prism j₀ using card-proportional total mass
  let pieceMass : Fin cfg.family.card → Fin step4.prismCount → ENNReal :=
    fun i j => MeasureTheory.volume (step4.piece i j)
  let cap : ENNReal :=
    ENNReal.ofReal (36 * Real.sqrt rho * delta ^ 2)

  have h_ba_pos : 0 < b - a := by linarith [refined.ordered]

  -- Family nonempty from extremality
  have h_enncard_pos : 0 < cfg.family.enncard := by
    have h1 : 0 < cfg.family.card := cfg.extremal.nonempty
    have h2 : cfg.family.enncard = (cfg.family.card : ENNReal) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]
    rw [h2]
    exact_mod_cast h1

  -- Card-proportional total piece mass: (π/16) * δ^(loss+2) * |F| * (b-a)
  let total_card : ENNReal :=
    ENNReal.ofReal (Real.pi / 16) * Kakeya.realRpowENN delta (loss + 2) *
      cfg.family.enncard * ENNReal.ofReal (b - a)

  have h_pi16 : ENNReal.ofReal (Real.pi / 16) = (1 / 4 : ENNReal) * ENNReal.ofReal (Real.pi / 4) := by
    have h1 : (Real.pi / 16) = (1 / 4 : ℝ) * (Real.pi / 4) := by ring
    rw [h1]
    have h2 : ENNReal.ofReal ((1 / 4 : ℝ) * (Real.pi / 4)) =
        ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (Real.pi / 4) :=
      ENNReal.ofReal_mul (by norm_num)
    rw [h2]
    have h3 : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ENNReal) := by
      simp
    rw [h3] <;> rfl

  have htotal_card : total_card ≤ ∑ i : Fin cfg.family.card, ∑ j : Fin step4.prismCount, pieceMass i j := by
    have h_slab_card : ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (loss + 2) *
        cfg.family.enncard * ENNReal.ofReal (b - a) ≤
        paperShadedMassInSlab refined.shading a b := refined.slab_mass_card
    have h_total_card_slab : (1 / 4 : ENNReal) * paperShadedMassInSlab refined.shading a b ≤
        ∑ i : Fin cfg.family.card, ∑ j : Fin step4.prismCount, pieceMass i j :=
      step4.total_piece_mass_slab
    calc
      total_card
        = (1 / 4 : ENNReal) * (ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (loss + 2) *
            cfg.family.enncard * ENNReal.ofReal (b - a)) := by
          simp only [total_card]
          rw [h_pi16] <;> simp [mul_assoc]
      _ ≤ (1 / 4 : ENNReal) * paperShadedMassInSlab refined.shading a b := by gcongr
      _ ≤ ∑ i, ∑ j, pieceMass i j := h_total_card_slab

  have hcap : ∀ i ∈ (Finset.univ : Finset (Fin cfg.family.card)),
      ∀ j ∈ (Finset.univ : Finset (Fin step4.prismCount)), pieceMass i j ≤ cap :=
    fun i _ j _ => step4.piece_mass_upper i j
  have hprisms_nonempty : (Finset.univ : Finset (Fin step4.prismCount)).Nonempty := by
    have hne : Nonempty (Fin step4.prismCount) := Fin.pos_iff_nonempty.mp step4.prismCount_pos
    exact Finset.univ_nonempty_iff.mpr hne

  rcases prism_mass_pigeonhole (Finset.univ : Finset (Fin cfg.family.card))
      (Finset.univ : Finset (Fin step4.prismCount))
      hprisms_nonempty pieceMass total_card cap htotal_card hcap with
    ⟨j₀, hj₀, h_j₀⟩

  let active : Finset (Fin cfg.family.card) :=
    Finset.univ.filter fun i => pieceMass i j₀ ≠ 0

  have h_univ_card : (Finset.univ : Finset (Fin step4.prismCount)).card = step4.prismCount := by simp
  have h1_card : total_card ≤ (step4.prismCount : ENNReal) * cap * (active.card : ENNReal) := by
    simpa [h_univ_card, active] using h_j₀

  have hprism_pos : 0 < (step4.prismCount : ENNReal) := by
    exact_mod_cast step4.prismCount_pos
  have hprism_ne_top : (step4.prismCount : ENNReal) ≠ ⊤ := by
    simp <;> exact WithTop.coe_ne_top

  have h_active_pos : 0 < (active.card : ENNReal) := by
    have h1_pos : 0 < (ENNReal.ofReal (Real.pi / 16)) := by positivity
    have h2_pos : 0 < (Kakeya.realRpowENN delta (loss + 2)) := by
      simp [Kakeya.realRpowENN] <;> exact Real.rpow_pos_of_pos hdelta _
    have h3_pos : 0 < cfg.family.enncard := h_enncard_pos
    have h4_pos : 0 < ENNReal.ofReal (b - a) := ENNReal.ofReal_pos.mpr h_ba_pos
    have h_tot_pos : 0 < total_card := by
      simp only [total_card]
      positivity
    by_contra h
    have h' : (active.card : ENNReal) = 0 := by simpa using h
    have h_mul_zero : (step4.prismCount : ENNReal) * cap * (active.card : ENNReal) = 0 := by
      rw [h'] <;> simp
    have h1_card' : total_card ≤ 0 := by
      rw [h_mul_zero] at h1_card
      exact h1_card
    have h_eq : total_card = 0 := le_antisymm h1_card' (by simp)
    exact h_tot_pos.ne' h_eq

  -- Direction bound for each active tube
  have h_dir : ∀ i ∈ active,
      |inner ℝ (cfg.family.tube i).direction (step4.prismNormal j₀)| ≤ tau := by
    intro i hi
    have hvol_ne_zero : pieceMass i j₀ ≠ 0 := (Finset.mem_filter.mp hi).2
    have hpiece_lower36 : ENNReal.ofReal
        (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho) ≤
        pieceMass i j₀ := by
      have h := step4.piece_mass_lower i j₀ hvol_ne_zero
      simpa [pieceMass, hrho_def] using h
    have hpiece_ad : IsADSet1
        (scalarProjection (step4.prismNormal j₀) (step4.piece i j₀))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-(12 * eta))) :=
      step4.piece_local_ad i j₀ hvol_ne_zero
    have hpiece_sub : step4.piece i j₀ ⊆
        tubeSegmentCarrier (6 * delta) (cfg.family.tube i).base (cfg.family.tube i).direction
          (step4.segmentStart i j₀) rho :=
      step4.piece_sub_segment i j₀
    have hpiece_meas : MeasurableSet (step4.piece i j₀) :=
      step4.piece_measurable i j₀
    have hnormal_unit : ‖step4.prismNormal j₀‖ = 1 := step4.prismNormal_unit j₀
    have hdir_unit : ‖(cfg.family.tube i).direction‖ = 1 := (cfg.family.tube i).direction_unit
    have h_bound := hdir_bound delta rho (step4.segmentStart i j₀)
        hdelta hdelta₁' step4.six_delta_le_rho hrho_le_quarter
        (cfg.family.tube i).base (cfg.family.tube i).direction (step4.prismNormal j₀)
        hdir_unit hnormal_unit
        (step4.piece i j₀) hpiece_meas hpiece_sub hpiece_lower36 hpiece_ad
    have h9 : |inner ℝ (cfg.family.tube i).direction (step4.prismNormal j₀)| ≤ tau := by
      have h10 := direction_bound_to_real hdelta hrho_pos h_bound
      have h11 : 3 * eta' / sigma = 36 * eta / sigma := by
        simp [heta'_def] <;> ring
      rw [h11] at h10
      simpa [htau_def] using h10
    exact h9

  -- Use the occupied common-slice normal attached to the selected prism.
  let strip_width : ℝ :=
    Real.sqrt rho + 12 * delta +
      (12 * delta + 2 * Real.sqrt 3) * tau
  let W : Set Point3 :=
    orientedBoxSlab (step4.prismCenter j₀) (step4.prismNormal j₀) strip_width

  have hW_convex : Convex ℝ W :=
    orientedBoxSlab_convex (step4.prismCenter j₀) (step4.prismNormal j₀) strip_width

  have h_contain : ∀ i ∈ active,
      wz1PaperTubeCarrier (cfg.family.tube i) ⊆ W := by
    intro i hi
    have h_i_active : pieceMass i j₀ ≠ 0 := (Finset.mem_filter.mp hi).2
    have hpiece_nonempty : (step4.piece i j₀).Nonempty := by
      by_contra h
      have h' : step4.piece i j₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have h_vol : pieceMass i j₀ = 0 := by
        simp [pieceMass, h']
      exact h_i_active h_vol
    rcases hpiece_nonempty with ⟨q_i, hq_i⟩
    have hq_in_paper : q_i ∈ wz1PaperTubeCarrier (cfg.family.tube i) := by
      have h1 : q_i ∈ step4.piece i j₀ := hq_i
      have h2 : step4.piece i j₀ ⊆ step4.fine.carrier i := step4.piece_sub_fine i j₀
      have h3 : step4.fine.carrier i ⊆ wz1PaperTubeCarrier (cfg.family.tube i) :=
        step4.fine.subset_body i
      exact h3 (h2 h1)
    have htransverse :
        |inner ℝ (q_i - step4.prismCenter j₀) (step4.prismNormal j₀)| ≤
          Real.sqrt rho :=
      step4.prism_transverse j₀ (step4.piece_sub_prism i j₀ hq_i)
    have hdir_shared :
        |inner ℝ (cfg.family.tube i).direction (step4.prismNormal j₀)| ≤ tau :=
      h_dir i hi
    intro q hq
    refine ⟨hq.2, ?_⟩
    exact paper_carrier_in_expanded_slab hdelta
      (step4.prismNormal_unit j₀) (by positivity) hdir_shared
      hq_in_paper htransverse q hq

  -- containedCount(W) ≥ active.card
  have h_cc : (active.card : ENNReal) ≤
      (wz1PaperBodyFamily cfg.family).containedCount W := by
    classical
    let bf := wz1PaperBodyFamily cfg.family
    let filterSet : Finset (Fin cfg.family.card) :=
      Finset.univ.filter (fun i => (bf.body i).carrier ⊆ W)
    have h1 : active ⊆ filterSet := by
      intro i hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, h_contain i hi⟩
    have h2 : active.card ≤ filterSet.card := Finset.card_le_card h1
    have h3 : bf.containedCount W = (filterSet.card : ENNReal) := by
      simp [Kakeya.Streamlined.BodyFamily.containedCount, Kakeya.Streamlined.BodyFamily.containedIndices, filterSet]
      <;> rfl
    rw [h3]
    exact_mod_cast h2

  -- Width bound after changing from the per-piece normal to the shared normal.
  have hwidth_le_24tau : strip_width ≤ 24 * tau := by
    have hdelta_one : delta ≤ 1 := hdelta_le.trans hdelta₀_one
    have hsqrt3_le_two : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have h12delta : 12 * delta ≤ 6 * tau := by
      linarith [h2delta_le_tau]
    have hcoeff : 12 * delta + 2 * Real.sqrt 3 ≤ 16 := by
      nlinarith
    have hprod :
        (12 * delta + 2 * Real.sqrt 3) * tau ≤ 16 * tau := by
      have htau_nonneg' : 0 ≤ tau := by positivity
      exact mul_le_mul_of_nonneg_right hcoeff htau_nonneg'
    dsimp only [strip_width]
    linarith [hsqrt_rho_le_tau]

  -- Volume bound
  have hwidth_nonneg : 0 ≤ strip_width := by positivity
  have h_vol_raw : MeasureTheory.volume W ≤ ENNReal.ofReal (24 * strip_width) :=
    oriented_box_slab_volume (step4.prismCenter j₀) (step4.prismNormal j₀) strip_width
      (step4.prismNormal_unit j₀) hwidth_nonneg
  let K_enn : ENNReal := ENNReal.ofReal K
  have hK_nonneg : 0 ≤ K := by norm_num [hK_def]
  have h_vol : MeasureTheory.volume W ≤
      K_enn * ENNReal.ofReal tau := by
    calc MeasureTheory.volume W
      ≤ ENNReal.ofReal (24 * strip_width) := h_vol_raw
    _ ≤ ENNReal.ofReal (24 * (24 * tau)) := by gcongr <;> linarith
    _ ≤ ENNReal.ofReal (K * tau) := by
      have h_eq : 24 * (24 * tau) ≤ K * tau := by
        simp [hK_def] <;> linarith
      exact ENNReal.ofReal_le_ofReal h_eq
    _ = K_enn * ENNReal.ofReal tau := by
      have h_mul : ENNReal.ofReal (K * tau) =
          ENNReal.ofReal K * ENNReal.ofReal tau :=
        ENNReal.ofReal_mul hK_nonneg
      rw [h_mul] <;> rfl

  -- Convert absorption to real form
  have h_absorb_strict : C_enn < Kakeya.realRpowENN delta exp :=
    h_absorb_enn delta hdelta hdelta₃'
  have h_absorb_real : C_real < Real.rpow delta exp := by
    simpa [Kakeya.realRpowENN, hC_enn_def] using
      (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hdelta exp)).mp h_absorb_strict

  -- Convert ENNReal bounds to Real
  have hK_enn_ne_top : K_enn ≠ ⊤ := by
    simp [K_enn, ENNReal.ofReal_ne_top]
  have h_rhs_vol_ne_top : K_enn * ENNReal.ofReal tau ≠ ⊤ := by
    apply ENNReal.mul_ne_top hK_enn_ne_top
    simp [ENNReal.ofReal_ne_top]
  have h_vol_ne_top : MeasureTheory.volume W ≠ ⊤ :=
    ne_top_of_le_ne_top h_rhs_vol_ne_top h_vol
  have h_enncard_ne_top : cfg.family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard] <;> exact WithTop.coe_ne_top
  have h_count_ne_top : (wz1PaperBodyFamily cfg.family).containedCount W ≠ ⊤ := by
    simp [Kakeya.Streamlined.BodyFamily.containedCount]
    <;> exact WithTop.coe_ne_top

  set vol_real : ℝ := (MeasureTheory.volume W).toReal with hvol_real_def
  set card_real : ℝ := cfg.family.enncard.toReal with hcard_real_def
  set count_real : ℝ := ((wz1PaperBodyFamily cfg.family).containedCount W).toReal with hcount_real_def
  set ba_real : ℝ := b - a with hba_real_def

  have hvol_real_nonneg : 0 ≤ vol_real := by positivity
  have hcard_real_pos : 0 < card_real := by
    have h_eq : cfg.family.enncard = ENNReal.ofReal card_real :=
      (ENNReal.ofReal_toReal h_enncard_ne_top).symm
    rw [h_eq] at h_enncard_pos
    exact ENNReal.ofReal_pos.mp h_enncard_pos
  have hcount_real_nonneg : 0 ≤ count_real := by positivity
  have hba_real_pos : 0 < ba_real := h_ba_pos

  have h_vol2 : MeasureTheory.volume W ≤ ENNReal.ofReal (K * tau) := by
    have h_mul : ENNReal.ofReal (K * tau) = K_enn * ENNReal.ofReal tau :=
      ENNReal.ofReal_mul hK_nonneg
    have h_eq : K_enn * ENNReal.ofReal tau = ENNReal.ofReal (K * tau) := h_mul.symm
    rw [h_eq] at h_vol
    exact h_vol

  have hvol_real : vol_real ≤ K * tau := by
    have h9 : MeasureTheory.volume W = ENNReal.ofReal vol_real :=
      (ENNReal.ofReal_toReal h_vol_ne_top).symm
    rw [h9] at h_vol2
    have h_Ktau_nonneg : 0 ≤ K * tau := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h_Ktau_nonneg).mp h_vol2

  have hvol_real' : vol_real ≤ K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)) := by
    have h : K * tau = K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)) := by
      rw [htau_def] <;> ring
    rw [h] at hvol_real
    exact hvol_real

  -- rho^(sigma/2) = 64^(sigma/2) * ba^sigma
  have h_rho_sigma : Real.rpow rho (sigma / 2) =
      Real.rpow 64 (sigma / 2) * ba_real ^ sigma := by
    have h1 : rho = 64 * ba_real ^ 2 := step4.rho_eq
    rw [h1]
    have h21 : 0 ≤ (64 : ℝ) := by norm_num
    have h22 : 0 ≤ ba_real ^ 2 := by positivity
    have hba_nonneg : 0 ≤ ba_real := by linarith
    have h_mul : Real.rpow (64 * ba_real ^ 2) (sigma / 2) =
        Real.rpow 64 (sigma / 2) * Real.rpow (ba_real ^ 2) (sigma / 2) :=
      Real.mul_rpow (x := (64 : ℝ)) (y := (ba_real ^ 2)) (z := (sigma / 2)) h21 h22
    rw [h_mul]
    have h4 : Real.rpow (ba_real ^ 2) (sigma / 2) = ba_real ^ sigma := by
      have h5 : Real.rpow (ba_real ^ 2) (sigma / 2) = Real.rpow ba_real (2 * (sigma / 2)) :=
        (Real.rpow_natCast_mul hba_nonneg 2 (sigma / 2)).symm
      rw [h5]
      have h6 : 2 * (sigma / 2) = sigma := by ring
      rw [h6]
      <;> simp
    rw [h4] <;> ring

  -- prismCount * cap ≤ 36 * δ^(-12η+2) * 64^(σ/2) * ba^σ
  have h_prism_cap_real : (step4.prismCount : ENNReal) * cap ≤
      ENNReal.ofReal ((36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
        Real.rpow 64 (sigma / 2) * ba_real ^ sigma) := by
    have h1 : (step4.prismCount : ENNReal) * cap ≤
        (Kakeya.realRpowENN delta (-(12 * eta)) *
          Kakeya.realRpowENN rho ((-1 + sigma) / 2)) * cap := by
      have h_upper : (step4.prismCount : ENNReal) ≤
          Kakeya.realRpowENN delta (-(12 * eta)) *
            Kakeya.realRpowENN rho ((-1 + sigma) / 2) :=
        step4.prism_card_upper
      gcongr
      <;> exact h_upper
    set expr1 : ℝ := (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) * Real.rpow rho (sigma / 2) with hexpr1_def
    set expr2 : ℝ := (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
        Real.rpow 64 (sigma / 2) * ba_real ^ sigma with hexpr2_def
    have h_expr_eq : expr1 = expr2 := by
      simp only [hexpr1_def, hexpr2_def]
      rw [h_rho_sigma] <;> ring
    have h2 : (Kakeya.realRpowENN delta (-(12 * eta)) *
          Kakeya.realRpowENN rho ((-1 + sigma) / 2)) * cap =
        ENNReal.ofReal expr1 := by
      simp only [cap, Kakeya.realRpowENN, hexpr1_def]
      have hsqrt : Real.sqrt rho = Real.rpow rho (1 / 2) :=
        Real.sqrt_eq_rpow rho
      have h_a_nonneg : 0 ≤ Real.rpow delta (-(12 * eta)) := Real.rpow_nonneg hdelta.le _
      have h_b_nonneg : 0 ≤ Real.rpow rho ((-1 + sigma) / 2) := Real.rpow_nonneg hrho_pos.le _
      have h_c_nonneg : 0 ≤ (36 : ℝ) * Real.sqrt rho * delta ^ 2 := by positivity
      have h_ab_nonneg : 0 ≤ Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2) :=
        mul_nonneg h_a_nonneg h_b_nonneg
      have h_nonneg : 0 ≤ (36 : ℝ) * Real.rpow delta (-(12 * eta)) *
          Real.rpow rho ((-1 + sigma) / 2) * Real.sqrt rho * delta ^ 2 := by
        have h1 : 0 ≤ (36 : ℝ) := by norm_num
        have h2 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
        have h3 : 0 ≤ delta ^ 2 := by positivity
        positivity
      have h_eq : (36 : ℝ) * Real.rpow delta (-(12 * eta)) *
          Real.rpow rho ((-1 + sigma) / 2) * Real.sqrt rho * delta ^ 2 = expr1 := by
        simp only [hexpr1_def]
        rw [hsqrt]
        have h9 : Real.rpow delta (-(12 * eta)) * delta ^ 2 =
            Real.rpow delta (-(12 * eta) + 2) := by
          have h10 : delta ^ 2 = Real.rpow delta 2 := by simp
          rw [h10]
          exact (Real.rpow_add hdelta (-(12 * eta)) 2).symm
        have h11 : Real.rpow rho ((-1 + sigma) / 2) * Real.rpow rho (1 / 2) =
            Real.rpow rho (sigma / 2) := by
          have h12 : Real.rpow rho (((-1 + sigma) / 2) + (1 / 2)) =
              Real.rpow rho ((-1 + sigma) / 2) * Real.rpow rho (1 / 2) :=
            Real.rpow_add hrho_pos ((-1 + sigma) / 2) (1 / 2)
          have h13 : ((-1 + sigma) / 2) + (1 / 2) = sigma / 2 := by ring
          rw [h13] at h12
          exact h12.symm
        calc
          (36 : ℝ) * Real.rpow delta (-(12 * eta)) *
              Real.rpow rho ((-1 + sigma) / 2) * Real.rpow rho (1 / 2) * delta ^ 2
            = 36 * (Real.rpow delta (-(12 * eta)) * delta ^ 2) *
                (Real.rpow rho ((-1 + sigma) / 2) * Real.rpow rho (1 / 2)) := by ring
          _ = 36 * Real.rpow delta (-(12 * eta) + 2) *
                (Real.rpow rho ((-1 + sigma) / 2) * Real.rpow rho (1 / 2)) := by rw [h9]
          _ = 36 * Real.rpow delta (-(12 * eta) + 2) * Real.rpow rho (sigma / 2) := by rw [h11]
      have h_combine1 : ENNReal.ofReal (Real.rpow delta (-(12 * eta))) * ENNReal.ofReal (Real.rpow rho ((-1 + sigma) / 2)) =
          ENNReal.ofReal (Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2)) :=
        (ENNReal.ofReal_mul h_a_nonneg).symm
      have h_combine2 : ENNReal.ofReal (Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2)) *
          ENNReal.ofReal ((36 : ℝ) * Real.sqrt rho * delta ^ 2) =
        ENNReal.ofReal ((Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2)) *
          ((36 : ℝ) * Real.sqrt rho * delta ^ 2)) :=
        (ENNReal.ofReal_mul h_ab_nonneg).symm
      rw [h_combine1, h_combine2]
      congr 1
      have h_ring : (Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2) * ((36 : ℝ) * Real.sqrt rho * delta ^ 2)) =
          (36 : ℝ) * Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2) * Real.sqrt rho * delta ^ 2 := by ring
      rw [h_ring]
      exact h_eq
    rw [h2] at h1
    rw [h_expr_eq] at h1
    exact h1

  -- total_card = ofReal((π/16) * δ^(loss+2) * card_real * ba_real)
  have h_total_card_real : total_card =
      ENNReal.ofReal ((Real.pi / 16) * Real.rpow delta (loss + 2) * card_real * ba_real) := by
    have h_enncard_eq : cfg.family.enncard = ENNReal.ofReal card_real :=
      (ENNReal.ofReal_toReal h_enncard_ne_top).symm
    simp only [total_card, Kakeya.realRpowENN, hba_real_def]
    rw [h_enncard_eq]
    have h_pos1 : 0 ≤ (Real.pi / 16) := by positivity
    have h_pos2 : 0 ≤ Real.rpow delta (loss + 2) := Real.rpow_nonneg hdelta.le _
    have h_pos3 : 0 ≤ card_real := by positivity
    have h_pos4 : 0 ≤ ba_real := by linarith
    rw [← ENNReal.ofReal_mul h_pos1, ← ENNReal.ofReal_mul (mul_nonneg h_pos1 h_pos2)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h_pos1 h_pos2) h_pos3)]
    <;> rfl

  -- Convert pigeonhole inequality to real: total_card ≤ prismCount * cap * count
  have h1_real : (Real.pi / 16) * Real.rpow delta (loss + 2) * card_real * ba_real ≤
      (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
        Real.rpow 64 (sigma / 2) * ba_real ^ sigma * count_real := by
    have h9 : total_card ≤ (step4.prismCount : ENNReal) * cap * (wz1PaperBodyFamily cfg.family).containedCount W := by
      calc total_card
        ≤ (step4.prismCount : ENNReal) * cap * (active.card : ENNReal) := h1_card
        _ ≤ (step4.prismCount : ENNReal) * cap * (wz1PaperBodyFamily cfg.family).containedCount W := by
          gcongr <;> exact h_cc
    rw [h_total_card_real] at h9
    have h10 : (step4.prismCount : ENNReal) * cap * (wz1PaperBodyFamily cfg.family).containedCount W ≤
        ENNReal.ofReal ((36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
          Real.rpow 64 (sigma / 2) * ba_real ^ sigma) * (wz1PaperBodyFamily cfg.family).containedCount W := by
      gcongr <;> exact h_prism_cap_real
    have h_pos_coeff : 0 ≤ (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
        Real.rpow 64 (sigma / 2) * ba_real ^ sigma := by
      have h1 : 0 ≤ Real.rpow delta (-(12 * eta) + 2) := Real.rpow_nonneg hdelta.le _
      have h2 : 0 ≤ Real.rpow 64 (sigma / 2) := Real.rpow_nonneg (by norm_num) _
      have h3 : 0 ≤ ba_real ^ sigma := Real.rpow_nonneg hba_real_pos.le _
      positivity
    have h11 : ENNReal.ofReal ((36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
          Real.rpow 64 (sigma / 2) * ba_real ^ sigma) * (wz1PaperBodyFamily cfg.family).containedCount W =
        ENNReal.ofReal ((36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
          Real.rpow 64 (sigma / 2) * ba_real ^ sigma * count_real) := by
      rw [ENNReal.ofReal_mul h_pos_coeff]
      have h_count9 : (wz1PaperBodyFamily cfg.family).containedCount W = ENNReal.ofReal count_real :=
        (ENNReal.ofReal_toReal h_count_ne_top).symm
      rw [h_count9] <;> rfl
    rw [h11] at h10
    have h12 := h9.trans h10
    have h_pos_lhs : 0 ≤ (Real.pi / 16) * Real.rpow delta (loss + 2) * card_real * ba_real := by
      have h1 : 0 ≤ Real.rpow delta (loss + 2) := Real.rpow_nonneg hdelta.le _
      have h2 : 0 ≤ card_real := hcard_real_pos.le
      have h3 : 0 ≤ ba_real := hba_real_pos.le
      positivity
    have h_pos_rhs : 0 ≤ (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
        Real.rpow 64 (sigma / 2) * ba_real ^ sigma * count_real := by
      have h1 : 0 ≤ Real.rpow delta (-(12 * eta) + 2) := Real.rpow_nonneg hdelta.le _
      have h2 : 0 ≤ Real.rpow 64 (sigma / 2) := Real.rpow_nonneg (by norm_num) _
      have h3 : 0 ≤ ba_real ^ sigma := Real.rpow_nonneg hba_real_pos.le _
      have h4 : 0 ≤ count_real := hcount_real_nonneg
      positivity
    have h_iff : ENNReal.ofReal ((Real.pi / 16) * Real.rpow delta (loss + 2) * card_real * ba_real) ≤
        ENNReal.ofReal ((36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
          Real.rpow 64 (sigma / 2) * ba_real ^ sigma * count_real) ↔
        (Real.pi / 16) * Real.rpow delta (loss + 2) * card_real * ba_real ≤
        (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
          Real.rpow 64 (sigma / 2) * ba_real ^ sigma * count_real :=
      ENNReal.ofReal_le_ofReal_iff h_pos_rhs
    exact h_iff.mp h12

  have h_coeff_pos : 0 < (36 : ℝ) * Real.rpow delta (-(12 * eta) + 2) *
      Real.rpow 64 (sigma / 2) * ba_real ^ sigma := by
    have h1 : 0 < Real.rpow delta (-(12 * eta) + 2) := Real.rpow_pos_of_pos hdelta _
    have h2 : 0 < Real.rpow 64 (sigma / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < ba_real ^ sigma := Real.rpow_pos_of_pos hba_real_pos _
    positivity

  -- Card-proportional count lower bound
  have h_active_card_real :
      (Real.pi / (576 * Real.rpow 64 (sigma / 2))) *
        Real.rpow delta (loss + 12 * eta) * card_real * ba_real ^ (1 - sigma) ≤ count_real := by
    exact cropped_active_count_from_pigeonhole hdelta hrho_pos hba_real_pos h1_real

  -- Final inequality: δ^{-η} * vol * card < count
  have hrho_eq : rho = 64 * ba_real ^ 2 := by
    have h1 : rho = 64 * (b - a) ^ 2 := step4.rho_eq
    rw [h1, hba_real_def] <;> ring
  have h_final : Real.rpow delta (-eta) * vol_real * card_real < count_real :=
    cropped_convex_overload_final_ineq_card
      hdelta hsigma heta hepsilon
      hcard_real_pos hba_real_pos
      K hK_pos hrho_eq
      hvol_real' h_active_card_real hba h_absorb_real

  -- Convert back to ENNReal
  have h_vol9 : MeasureTheory.volume W = ENNReal.ofReal vol_real :=
    (ENNReal.ofReal_toReal h_vol_ne_top).symm
  have h_card9 : cfg.family.enncard = ENNReal.ofReal card_real :=
    (ENNReal.ofReal_toReal h_enncard_ne_top).symm
  have h_count9 : (wz1PaperBodyFamily cfg.family).containedCount W = ENNReal.ofReal count_real :=
    (ENNReal.ofReal_toReal h_count_ne_top).symm

  have h_lhs_enn : Kakeya.realRpowENN delta (-eta) * MeasureTheory.volume W * cfg.family.enncard =
      ENNReal.ofReal (Real.rpow delta (-eta) * vol_real * card_real) := by
    have h1 : Kakeya.realRpowENN delta (-eta) = ENNReal.ofReal (Real.rpow delta (-eta)) := by
      simp [Kakeya.realRpowENN]
    rw [h1, h_vol9, h_card9]
    have h_pos1 : 0 ≤ Real.rpow delta (-eta) := Real.rpow_nonneg hdelta.le _
    have h_pos12 : 0 ≤ Real.rpow delta (-eta) * vol_real := mul_nonneg h_pos1 hvol_real_nonneg
    have h_mul1 : ENNReal.ofReal (Real.rpow delta (-eta)) * ENNReal.ofReal vol_real =
        ENNReal.ofReal (Real.rpow delta (-eta) * vol_real) :=
      (ENNReal.ofReal_mul h_pos1).symm
    rw [h_mul1]
    have h_mul2 : ENNReal.ofReal (Real.rpow delta (-eta) * vol_real) * ENNReal.ofReal card_real =
        ENNReal.ofReal ((Real.rpow delta (-eta) * vol_real) * card_real) :=
      (ENNReal.ofReal_mul h_pos12).symm
    rw [h_mul2]

  have h_strict_enn : ENNReal.ofReal (Real.rpow delta (-eta) * vol_real * card_real) <
      ENNReal.ofReal count_real := by
    have h_pos_lhs : 0 ≤ Real.rpow delta (-eta) * vol_real * card_real :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hdelta.le _) hvol_real_nonneg) hcard_real_pos.le
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_pos_lhs).mpr h_final

  have h_goal : Kakeya.realRpowENN delta (-eta) * MeasureTheory.volume W * cfg.family.enncard <
      (wz1PaperBodyFamily cfg.family).containedCount W := by
    calc Kakeya.realRpowENN delta (-eta) * MeasureTheory.volume W * cfg.family.enncard
      = ENNReal.ofReal (Real.rpow delta (-eta) * vol_real * card_real) := h_lhs_enn
    _ < ENNReal.ofReal count_real := h_strict_enn
    _ = (wz1PaperBodyFamily cfg.family).containedCount W := h_count9.symm
  exact ⟨W, hW_convex, h_goal⟩

end Kakeya.Assouad

end

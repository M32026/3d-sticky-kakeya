import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! WZ2 Section 6, Step 4: volume of a bounded oriented slab.

Proof route: reflect normal to z-axis, convert via ofLp, then use
Real.volume_pi_le_prod_diam. Coordinate diameters: 2, 2, 2*width.
-/

namespace Kakeya.Assouad

theorem oriented_unit_slab_volume :
    OrientedUnitSlabVolumeStatement := by
  intro center normal width hnorm hwidth
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

  have hAc : inner ℝ (A center) e3 = c := by
    calc
      inner ℝ (A center) e3
        = inner ℝ (A center) (A normal) := by rw [hA_normal]
      _ = inner ℝ center normal := hA_inner center normal
      _ = c := rfl

  let s := orientedUnitSlab center normal width
  let s' := A '' s

  have hs_meas : MeasurableSet s := by
    have h1 : MeasurableSet (Kakeya.DeltaTube.unitBall : Set Point3) :=
      Metric.isClosed_closedBall.measurableSet
    have h_cont : Continuous (fun x : Point3 => |inner ℝ (x - center) normal|) := by
      fun_prop
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
      left_inv := by
        intro x
        exact WithLp.toLp_ofLp (2 : ENNReal) x
      right_inv := by
        intro x
        exact WithLp.ofLp_toLp (2 : ENNReal) x
      measurable_toFun := by
        exact
          (PiLp.continuous_ofLp (p := 2)
            (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := by
        exact
          (PiLp.continuous_toLp (p := 2)
            (β := fun _ : Fin 3 => ℝ)).measurable }
  let s'' : Set (Fin 3 → ℝ) := eLp '' s'

  have h_ofLp_vol : MeasureTheory.MeasurePreserving eLp MeasureTheory.volume MeasureTheory.volume :=
    by simpa [eLp] using PiLp.volume_preserving_ofLp (ι := Fin 3)

  have hs'_meas : MeasurableSet s' :=
    A_meas.measurableSet_image.mpr hs_meas

  have h_preimg2 : eLp ⁻¹' s'' = s' := by
    rw [← Set.preimage_image_eq s' eLp.injective]
  have hvol2 : MeasureTheory.volume s' = MeasureTheory.volume s'' := by
    have h : MeasureTheory.volume (eLp ⁻¹' s'') = MeasureTheory.volume s'' :=
      h_ofLp_vol.measure_preimage_emb eLp.measurableEmbedding s''
    rw [h_preimg2] at h
    exact h

  have h_coord : ∀ (y : Point3), y ∈ s' →
      |(y : Fin 3 → ℝ) 0| ≤ 1 ∧ |(y : Fin 3 → ℝ) 1| ≤ 1 ∧
        |(y : Fin 3 → ℝ) 2 - c| ≤ width := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxball' : ‖x‖ ≤ 1 := by
      simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using hx.1
    have hxslab : |inner ℝ (x - center) normal| ≤ width := hx.2
    have hAyball : ‖A x‖ ≤ 1 := by
      rw [hA_norm] <;> exact hxball'
    have hinner : |inner ℝ (A x - A center) e3| ≤ width := by
      have h5 : inner ℝ (A x - A center) e3 = inner ℝ (x - center) normal := by
        calc
          inner ℝ (A x - A center) e3
            = inner ℝ (A (x - center)) (A normal) := by
              rw [← hA_normal, map_sub] <;> rfl
          _ = inner ℝ (x - center) normal := hA_inner (x - center) normal
      rw [h5] <;> exact hxslab
    have h_y2_eval : inner ℝ (A x) e3 = (A x : Fin 3 → ℝ) 2 := by
      rw [EuclideanSpace.inner_single_right] <;> simp
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
    have h_y0 : |(A x : Fin 3 → ℝ) 0| ≤ 1 := by
      have h := h_abs_coord 0
      linarith [hAyball]
    have h_y1 : |(A x : Fin 3 → ℝ) 1| ≤ 1 := by
      have h := h_abs_coord 1
      linarith [hAyball]
    have h_y2' : |(A x : Fin 3 → ℝ) 2 - c| ≤ width := by
      have h6 : inner ℝ (A x - A center) e3 = (A x : Fin 3 → ℝ) 2 - c := by
        rw [inner_sub_left, h_y2_eval, hAc] <;> rfl
      rw [h6] at hinner
      exact hinner
    exact ⟨h_y0, h_y1, h_y2'⟩

  have h_coord2 : ∀ (z : Fin 3 → ℝ), z ∈ s'' →
      |z 0| ≤ 1 ∧ |z 1| ≤ 1 ∧ |z 2 - c| ≤ width := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact h_coord y hy

  have h0 : Function.eval 0 '' s'' ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    have h := (h_coord2 z hz).1
    have h' : -1 ≤ z 0 ∧ z 0 ≤ 1 := abs_le.mp h
    exact ⟨h'.1, h'.2⟩
  have h1 : Function.eval 1 '' s'' ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    have h := (h_coord2 z hz).2.1
    have h' : -1 ≤ z 1 ∧ z 1 ≤ 1 := abs_le.mp h
    exact ⟨h'.1, h'.2⟩
  have h2 : Function.eval 2 '' s'' ⊆ Set.Icc (c - width) (c + width) := by
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    have h := (h_coord2 z hz).2.2
    have h_abs : -width ≤ z 2 - c ∧ z 2 - c ≤ width := abs_le.mp h
    exact ⟨by linarith, by linarith⟩

  have hdiam0 : Metric.ediam (Function.eval 0 '' s'') ≤ ENNReal.ofReal 2 := by
    calc
      Metric.ediam (Function.eval 0 '' s'')
        ≤ Metric.ediam (Set.Icc (-1 : ℝ) 1) := Metric.ediam_mono h0
      _ = ENNReal.ofReal 2 := by
        rw [Real.ediam_Icc] <;> norm_num
  have hdiam1 : Metric.ediam (Function.eval 1 '' s'') ≤ ENNReal.ofReal 2 := by
    calc
      Metric.ediam (Function.eval 1 '' s'')
        ≤ Metric.ediam (Set.Icc (-1 : ℝ) 1) := Metric.ediam_mono h1
      _ = ENNReal.ofReal 2 := by
        rw [Real.ediam_Icc] <;> norm_num
  have hdiam2 : Metric.ediam (Function.eval 2 '' s'') ≤ ENNReal.ofReal (2 * width) := by
    calc
      Metric.ediam (Function.eval 2 '' s'')
        ≤ Metric.ediam (Set.Icc (c - width) (c + width)) := Metric.ediam_mono h2
      _ = ENNReal.ofReal (2 * width) := by
        rw [Real.ediam_Icc] <;> ring_nf

  have h_prod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' s'')) =
      Metric.ediam (Function.eval 0 '' s'') *
      Metric.ediam (Function.eval 1 '' s'') *
      Metric.ediam (Function.eval 2 '' s'') := by
    simp [Fin.prod_univ_succ]
    <;> ring
  have hmain : MeasureTheory.volume s'' ≤
      ENNReal.ofReal 2 * ENNReal.ofReal 2 * ENNReal.ofReal (2 * width) := by
    have h := Real.volume_pi_le_prod_diam s''
    rw [h_prod] at h
    exact h.trans (by gcongr <;> assumption)

  have h_arith1 : ENNReal.ofReal 2 * ENNReal.ofReal 2 = ENNReal.ofReal 4 := by
    have h : ENNReal.ofReal ((2 : ℝ) * (2 : ℝ)) =
        ENNReal.ofReal 2 * ENNReal.ofReal 2 :=
      ENNReal.ofReal_mul (by norm_num)
    have h' : ENNReal.ofReal ((2 : ℝ) * (2 : ℝ)) = ENNReal.ofReal 4 := by norm_num
    rw [← h, h']
  have h_arith2 : ENNReal.ofReal 4 * ENNReal.ofReal (2 * width) =
      ENNReal.ofReal (8 * width) := by
    have h : ENNReal.ofReal ((4 : ℝ) * (2 * width)) =
        ENNReal.ofReal 4 * ENNReal.ofReal (2 * width) :=
      ENNReal.ofReal_mul (by norm_num)
    have h' : ENNReal.ofReal ((4 : ℝ) * (2 * width)) =
        ENNReal.ofReal (8 * width) := by
      congr 1
      ring
    rw [← h, h']

  calc
    MeasureTheory.volume s
      = MeasureTheory.volume s' := hvol
    _ = MeasureTheory.volume s'' := hvol2
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal 2 * ENNReal.ofReal (2 * width) := hmain
    _ = (ENNReal.ofReal 2 * ENNReal.ofReal 2) * ENNReal.ofReal (2 * width) := by ring
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (2 * width) := by rw [h_arith1]
    _ = ENNReal.ofReal (8 * width) := h_arith2

end Kakeya.Assouad

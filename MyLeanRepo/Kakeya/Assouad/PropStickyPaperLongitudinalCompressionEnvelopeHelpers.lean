import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCWATransferStatements
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Helper lemmas for the longitudinal compression envelope

This file develops properties of `wz2PaperLongitudinalCompression`, the map
`(x, y, z) ↦ (x, y, z / 100)`, that are needed for the envelope theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- Diagonal entries for the compression matrix. -/
def compressionDiagonal : Fin 3 → ℝ := ![1, 1, (1 / 100 : ℝ)]

/-- The longitudinal compression as a continuous linear map. -/
def wz2PaperLongitudinalCompressionCLM : Point3 →L[ℝ] Point3 := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)) (Matrix.diagonal compressionDiagonal)

/-- The underlying linear map. -/
def wz2PaperLongitudinalCompressionLin : Point3 →ₗ[ℝ] Point3 :=
  wz2PaperLongitudinalCompressionCLM

lemma wz2PaperLongitudinalCompressionLin_apply (p : Point3) :
    wz2PaperLongitudinalCompressionLin p = wz2PaperLongitudinalCompression p := by
  ext i
  have h : WithLp.ofLp (wz2PaperLongitudinalCompressionLin p) =
      (Matrix.diagonal compressionDiagonal).mulVec (WithLp.ofLp p) := by
    dsimp only [wz2PaperLongitudinalCompressionLin, wz2PaperLongitudinalCompressionCLM]
    exact Matrix.ofLp_toEuclideanCLM (Matrix.diagonal compressionDiagonal) p
  have h2 : WithLp.ofLp (wz2PaperLongitudinalCompressionLin p) i =
      ((Matrix.diagonal compressionDiagonal).mulVec (WithLp.ofLp p)) i := by
    rw [h]
  rw [h2]
  have h3 : ((Matrix.diagonal compressionDiagonal).mulVec (WithLp.ofLp p)) i =
      compressionDiagonal i * (WithLp.ofLp p) i :=
    Matrix.mulVec_diagonal compressionDiagonal (WithLp.ofLp p) i
  rw [h3]
  fin_cases i <;> simp [compressionDiagonal, wz2PaperLongitudinalCompression]

lemma wz2PaperLongitudinalCompressionLin_eq :
    ⇑wz2PaperLongitudinalCompressionLin = wz2PaperLongitudinalCompression :=
  funext wz2PaperLongitudinalCompressionLin_apply

/-- Determinant of the compression linear map is `1 / 100`. -/
lemma wz2PaperLongitudinalCompression_det :
    LinearMap.det wz2PaperLongitudinalCompressionLin = (1 / 100 : ℝ) := by
  have h_eq : (wz2PaperLongitudinalCompressionCLM : Point3 →ₗ[ℝ] Point3) =
      Matrix.toLpLin 2 2 (Matrix.diagonal compressionDiagonal) := by
    dsimp only [wz2PaperLongitudinalCompressionCLM]
    exact Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (Matrix.diagonal compressionDiagonal)
  rw [show LinearMap.det wz2PaperLongitudinalCompressionLin =
      LinearMap.det (Matrix.toLpLin 2 2 (Matrix.diagonal compressionDiagonal)) from by
    congr 1]
  rw [LinearMap.det_toLpLin 2 (Matrix.diagonal compressionDiagonal)]
  rw [Matrix.det_diagonal]
  simp [compressionDiagonal, Fin.prod_univ_succ]

/-- The compression map decreases norms: `‖f v‖ ≤ ‖v‖`. -/
lemma wz2PaperLongitudinalCompression_norm_le (v : Point3) :
    ‖wz2PaperLongitudinalCompression v‖ ≤ ‖v‖ := by
  have h2 : ‖wz2PaperLongitudinalCompression v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have h3 : ((wz2PaperLongitudinalCompression v) i) ^ 2 ≤ (v i) ^ 2 := by
      fin_cases i <;> simp [wz2PaperLongitudinalCompression] <;> nlinarith [sq_nonneg (v 2)]
    exact h3
  have h4 : 0 ≤ ‖wz2PaperLongitudinalCompression v‖ := norm_nonneg _
  have h5 : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith

/-- The compression map is 1-Lipschitz. -/
lemma wz2PaperLongitudinalCompression_lipschitz :
    LipschitzWith 1 wz2PaperLongitudinalCompression := by
  have h : ∀ (x y : Point3), dist (wz2PaperLongitudinalCompression x)
        (wz2PaperLongitudinalCompression y) ≤ (1 : ℝ) * dist x y := by
    intro x y
    rw [one_mul]
    rw [← wz2PaperLongitudinalCompressionLin_eq]
    have h_lin : wz2PaperLongitudinalCompressionLin (x - y) =
        wz2PaperLongitudinalCompressionLin x - wz2PaperLongitudinalCompressionLin y :=
      wz2PaperLongitudinalCompressionLin.map_sub x y
    have h_dist : dist (wz2PaperLongitudinalCompressionLin x)
        (wz2PaperLongitudinalCompressionLin y) =
        ‖wz2PaperLongitudinalCompressionLin x -
          wz2PaperLongitudinalCompressionLin y‖ :=
      dist_eq_norm _ _
    rw [h_dist, ← h_lin]
    have h6 : ‖wz2PaperLongitudinalCompressionLin (x - y)‖ ≤ ‖x - y‖ := by
      rw [wz2PaperLongitudinalCompressionLin_eq]
      exact wz2PaperLongitudinalCompression_norm_le (x - y)
    have h7 : ‖x - y‖ = dist x y := by rw [dist_eq_norm]
    rw [h7] at h6
    exact h6
  have h' : LipschitzWith (Real.toNNReal 1) wz2PaperLongitudinalCompression :=
    LipschitzWith.of_dist_le' (K := (1 : ℝ)) h
  simpa using h'

/-- Compression preserves the box `axisBox 2 2 2`. -/
lemma wz2PaperLongitudinalCompression_axisBox {p : Point3}
    (h : p ∈ Kakeya.Streamlined.axisBox 2 2 2) :
    wz2PaperLongitudinalCompression p ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
  simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at h ⊢
  have h0 : |(wz2PaperLongitudinalCompression p) 0| ≤ (2 : ℝ) / 2 := by
    have h01 : |(wz2PaperLongitudinalCompression p) 0| = |p 0| := by
      simp [wz2PaperLongitudinalCompression]
    rw [h01]
    exact h.1
  have h1 : |(wz2PaperLongitudinalCompression p) 1| ≤ (2 : ℝ) / 2 := by
    have h11 : |(wz2PaperLongitudinalCompression p) 1| = |p 1| := by
      simp [wz2PaperLongitudinalCompression]
    rw [h11]
    exact h.2.1
  have h2 : |(wz2PaperLongitudinalCompression p) 2| ≤ (2 : ℝ) / 2 := by
    have h21 : |(wz2PaperLongitudinalCompression p) 2| = (1 / 100 : ℝ) * |p 2| := by
      simp [wz2PaperLongitudinalCompression, abs_mul]
    rw [h21]
    have h22 : |p 2| ≤ (2 : ℝ) / 2 := h.2.2
    nlinarith
  exact ⟨h0, h1, h2⟩

/-- A 1-Lipschitz map sends the closed thickening of a set into the closed thickening of its image. -/
lemma image_cthickening_subset_cthickening_image_one
    {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {f : α → β} (hf : LipschitzWith 1 f) {r : ℝ} (hr : 0 ≤ r) {s : Set α} :
    f '' Metric.cthickening r s ⊆ Metric.cthickening r (f '' s) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  by_cases hs : s.Nonempty
  · have h_inf_edist : infEDist y s ≤ ENNReal.ofReal r :=
      (Metric.mem_cthickening_iff).mp hy
    have h_ne_top : infEDist y s ≠ ⊤ := infEDist_ne_top hs
    have h_inf : infDist y s ≤ r := by
      have h_eq : infDist y s = (infEDist y s).toReal := by rfl
      rw [h_eq]
      have h : (infEDist y s).toReal ≤ (ENNReal.ofReal r).toReal :=
        (ENNReal.toReal_le_toReal h_ne_top ENNReal.ofReal_ne_top).mpr h_inf_edist
      simpa [hr] using h
    have h_main : ∀ (ε : ℝ), 0 < ε → infDist (f y) (f '' s) < r + ε := by
      intro ε hε
      have h1 : infDist y s < r + ε := by linarith
      have h2 : ∃ z ∈ s, dist y z < r + ε := (infDist_lt_iff hs).mp h1
      rcases h2 with ⟨z, hz, hdist⟩
      have h3 : dist (f y) (f z) ≤ (1 : ℝ) * dist y z := hf.dist_le_mul y z
      have h3' : dist (f y) (f z) ≤ dist y z := by simpa using h3
      have h4 : dist (f y) (f z) < r + ε := by linarith
      have h5 : f z ∈ f '' s := Set.mem_image_of_mem f hz
      have h6 : infDist (f y) (f '' s) ≤ dist (f y) (f z) :=
        infDist_le_dist_of_mem h5
      linarith
    have h7 : infDist (f y) (f '' s) ≤ r := by
      by_contra h8
      have h9 : r < infDist (f y) (f '' s) := by linarith
      set ε : ℝ := (infDist (f y) (f '' s) - r) / 2 with hε_def
      have hε_pos : 0 < ε := by linarith
      have h10 := h_main ε hε_pos
      linarith
    have hfs : (f '' s).Nonempty := hs.image f
    have h8 : infEDist (f y) (f '' s) ≠ ⊤ := infEDist_ne_top hfs
    have h9 : infEDist (f y) (f '' s) ≤ ENNReal.ofReal r := by
      have h10 : infEDist (f y) (f '' s) =
          ENNReal.ofReal (infDist (f y) (f '' s)) := by
        rw [← ENNReal.ofReal_toReal h8]
        <;> rfl
      rw [h10]
      have h11 : 0 ≤ infDist (f y) (f '' s) := Metric.infDist_nonneg
      exact ENNReal.ofReal_le_ofReal h7
    rw [Metric.mem_cthickening_iff]
    exact h9
  · have hse : s = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hs
    rw [hse, Metric.cthickening_empty] at hy
    simp at hy

/-- Compression sends the thickening of a set into the thickening of its image. -/
lemma wz2PaperLongitudinalCompression_image_cthickening {r : ℝ} (hr : 0 ≤ r)
    {s : Set Point3} :
    wz2PaperLongitudinalCompression '' Metric.cthickening r s ⊆
      Metric.cthickening r (wz2PaperLongitudinalCompression '' s) :=
  image_cthickening_subset_cthickening_image_one
    wz2PaperLongitudinalCompression_lipschitz hr

/--
If the literal tube axis is the image of the historical tube axis under compression,
then the image of the historical paper tube carrier is contained in the literal paper tube carrier.
-/
lemma wz2PaperLongitudinalCompression_image_tubeCarrier
    {scale : ℝ} (hscale : 0 < scale)
    {historicalTube literalTube : Kakeya.DeltaTube scale}
    (h_axis : tubeAxisLine literalTube =
        wz2PaperLongitudinalCompression '' tubeAxisLine historicalTube) :
    wz2PaperLongitudinalCompression '' wz1PaperTubeCarrier historicalTube ⊆
      wz1PaperTubeCarrier literalTube := by
  have hr : 0 ≤ 6 * scale := by positivity
  have h1 : wz2PaperLongitudinalCompression ''
        (Metric.cthickening (6 * scale) (tubeAxisLine historicalTube) ∩
          Kakeya.Streamlined.axisBox 2 2 2) ⊆
      (wz2PaperLongitudinalCompression ''
          Metric.cthickening (6 * scale) (tubeAxisLine historicalTube)) ∩
        (wz2PaperLongitudinalCompression ''
          Kakeya.Streamlined.axisBox 2 2 2) := by
    apply Set.image_inter_subset
  have h2 : wz2PaperLongitudinalCompression ''
        Metric.cthickening (6 * scale) (tubeAxisLine historicalTube) ⊆
      Metric.cthickening (6 * scale)
        (wz2PaperLongitudinalCompression '' tubeAxisLine historicalTube) :=
    wz2PaperLongitudinalCompression_image_cthickening hr
  have h3 : wz2PaperLongitudinalCompression ''
        Kakeya.Streamlined.axisBox 2 2 2 ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact wz2PaperLongitudinalCompression_axisBox hp
  calc
    wz2PaperLongitudinalCompression '' wz1PaperTubeCarrier historicalTube
      = wz2PaperLongitudinalCompression ''
          (Metric.cthickening (6 * scale) (tubeAxisLine historicalTube) ∩
            Kakeya.Streamlined.axisBox 2 2 2) := by rfl
    _ ⊆ (wz2PaperLongitudinalCompression ''
            Metric.cthickening (6 * scale) (tubeAxisLine historicalTube)) ∩
          (wz2PaperLongitudinalCompression ''
            Kakeya.Streamlined.axisBox 2 2 2) := h1
    _ ⊆ Metric.cthickening (6 * scale)
            (wz2PaperLongitudinalCompression '' tubeAxisLine historicalTube) ∩
          Kakeya.Streamlined.axisBox 2 2 2 := by
        gcongr
        <;> tauto
    _ = Metric.cthickening (6 * scale) (tubeAxisLine literalTube) ∩
          Kakeya.Streamlined.axisBox 2 2 2 := by rw [h_axis]
    _ = wz1PaperTubeCarrier literalTube := by rfl

/-- The preimage of a convex set under compression is convex. -/
lemma wz2PaperLongitudinalCompression_preimage_convex {S : Set Point3}
    (hS : Convex ℝ S) :
    Convex ℝ (wz2PaperLongitudinalCompression ⁻¹' S) := by
  rw [← wz2PaperLongitudinalCompressionLin_eq]
  exact hS.linear_preimage wz2PaperLongitudinalCompressionLin

/-- Volume of the preimage under compression is exactly `100 * volume S`. -/
lemma wz2PaperLongitudinalCompression_preimage_volume {S : Set Point3} :
    volume (wz2PaperLongitudinalCompression ⁻¹' S) =
      (100 : ENNReal) * volume S := by
  have hdet : LinearMap.det wz2PaperLongitudinalCompressionLin ≠ 0 := by
    rw [wz2PaperLongitudinalCompression_det]
    <;> norm_num
  have h : volume (wz2PaperLongitudinalCompressionLin ⁻¹' S) =
      ENNReal.ofReal (|(LinearMap.det wz2PaperLongitudinalCompressionLin)⁻¹|) *
        volume S :=
    MeasureTheory.Measure.addHaar_preimage_linearMap volume hdet S
  rw [← wz2PaperLongitudinalCompressionLin_eq] at *
  rw [h]
  rw [wz2PaperLongitudinalCompression_det]
  have h2 : ENNReal.ofReal (|((1 / 100 : ℝ))⁻¹|) = (100 : ENNReal) := by
    norm_num
  rw [h2]
  <;> rfl

end Kakeya.Assouad

end

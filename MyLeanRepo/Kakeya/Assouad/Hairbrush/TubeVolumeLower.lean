import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Tube volume lower bound

Every `δ`-tube has volume at least `δ²/8`.

## Proof route

The canonical tube `Metric.cthickening δ (unitSegment 0 e0)` contains the
axis-aligned box with coordinates `x₀ ∈ [1/4, 3/4]`, `x₁, x₂ ∈ [-δ/4, δ/4]`.
For any point in this box, its distance to the point `x₀ • e0` on the segment
is at most `δ/2 < δ`. The box has volume `(1/2)·(δ/2)·(δ/2) = δ²/8`.

A rigid isometry maps any tube to the canonical tube while preserving Lebesgue
volume, so the same lower bound holds for every tube.

## Whiteprint node

`whiteprint/Kakeya/Assouad/HairbrushSpatialTwoEndsReduction/`
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Assouad

lemma tube_volume_lower {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (T : Kakeya.DeltaTube δ) :
    T.volume ≥ ENNReal.ofReal (δ^2 / 8) := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) 1
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 1 / 4
    | 1 => -δ / 4
    | 2 => -δ / 4
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 3 / 4
    | 1 => δ / 4
    | 2 => δ / 4
  let box : Set Point3 := (WithLp.toLp 2) '' Set.Icc lo hi
  let canonicalTube : Set Point3 :=
    Metric.cthickening δ (Kakeya.unitSegment 0 e0)

  -- Box ⊆ canonical tube
  have hbox_sub : box ⊆ canonicalTube := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hlo : ∀ i, lo i ≤ y i := (Set.mem_Icc.mp hy).1
    have hhi : ∀ i, y i ≤ hi i := (Set.mem_Icc.mp hy).2
    set t : ℝ := y 0 with ht_def
    have ht0 : 1 / 4 ≤ t := by
      dsimp only [t]
      have h := hlo 0
      dsimp only [lo] at h
      exact h
    have ht1 : t ≤ 3 / 4 := by
      dsimp only [t]
      have h := hhi 0
      dsimp only [hi] at h
      exact h
    have hy1 : |y 1| ≤ δ / 4 := by
      have h1 : -δ / 4 ≤ y 1 := by
        have h := hlo 1; dsimp only [lo] at h; exact h
      have h2 : y 1 ≤ δ / 4 := by
        have h := hhi 1; dsimp only [hi] at h; exact h
      exact abs_le.mpr ⟨by linarith, h2⟩
    have hy2 : |y 2| ≤ δ / 4 := by
      have h1 : -δ / 4 ≤ y 2 := by
        have h := hlo 2; dsimp only [lo] at h; exact h
      have h2 : y 2 ≤ δ / 4 := by
        have h := hhi 2; dsimp only [hi] at h; exact h
      exact abs_le.mpr ⟨by linarith, h2⟩
    let p : Point3 := t • e0
    have hp : p ∈ Kakeya.unitSegment 0 e0 :=
      ⟨t, ⟨by linarith, by linarith⟩, by simp [p]⟩
    let v : Point3 := (WithLp.toLp 2 y) - p
    have hv0 : v 0 = 0 := by
      have h1 : (WithLp.toLp 2 y) 0 = y 0 := by simp
      have h2 : p 0 = t := by simp [p, e0]
      have h3 : v 0 = (WithLp.toLp 2 y) 0 - p 0 := by rfl
      rw [h3, h1, h2, ht_def] <;> ring
    have hv1 : v 1 = y 1 := by
      have h1 : (WithLp.toLp 2 y) 1 = y 1 := by simp
      have h2 : p 1 = 0 := by simp [p, e0]
      have h3 : v 1 = (WithLp.toLp 2 y) 1 - p 1 := by rfl
      rw [h3, h1, h2] <;> ring
    have hv2 : v 2 = y 2 := by
      have h1 : (WithLp.toLp 2 y) 2 = y 2 := by simp
      have h2 : p 2 = 0 := by simp [p, e0]
      have h3 : v 2 = (WithLp.toLp 2 y) 2 - p 2 := by rfl
      rw [h3, h1, h2] <;> ring
    have hnorm_sq : ‖v‖ ^ 2 = (y 1)^2 + (y 2)^2 := by
      have h : ‖v‖ ^ 2 = ∑ i : Fin 3, v i ^ 2 :=
        EuclideanSpace.real_norm_sq_eq v
      have hsum : ∑ i : Fin 3, v i ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
        simp [Fin.sum_univ_succ]
        <;> ring
      rw [h, hsum, hv0, hv1, hv2] <;> ring
    have hsq : (y 1)^2 + (y 2)^2 ≤ δ^2 := by
      have h1 : (y 1)^2 ≤ (δ / 4)^2 := by
        have h11 : |y 1| ≤ δ / 4 := hy1
        calc
          (y 1)^2 ≤ |y 1| ^ 2 := by rw [sq_abs]
          _ ≤ (δ / 4)^2 := by gcongr <;> linarith
      have h2 : (y 2)^2 ≤ (δ / 4)^2 := by
        have h21 : |y 2| ≤ δ / 4 := hy2
        calc
          (y 2)^2 ≤ |y 2| ^ 2 := by rw [sq_abs]
          _ ≤ (δ / 4)^2 := by gcongr <;> linarith
      nlinarith
    have hnorm : ‖v‖ ≤ δ := by
      have hpos : 0 ≤ ‖v‖ := by positivity
      nlinarith [hnorm_sq, hsq]
    have hdist : dist (WithLp.toLp 2 y) p ≤ δ := by
      simpa [dist_eq_norm, v] using hnorm
    exact Metric.mem_cthickening_of_dist_le (WithLp.toLp 2 y) p δ _ hp hdist

  -- Volume of box
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i <;> dsimp [lo, hi] <;> linarith
  have hbox_vol : volume box = ENNReal.ofReal (δ^2 / 8) := by
    rw [volume_rectBox lo hi hlohi]
    have hprod : (hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2) = δ^2 / 8 := by
      simp [lo, hi] <;> ring
    rw [hprod]

  -- Rigid isometry mapping T's carrier to canonical tube
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm_dir : ‖T.direction‖ = ‖e0‖ := by
    rw [T.direction_unit, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
  have hA : A T.direction = e0 := Submodule.reflection_sub hnorm_dir
  let translate : Point3 ≃ᵢ Point3 :=
    { toFun := fun x => x - T.base
      invFun := fun y => y + T.base
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      isometry_toFun := by
        intro x y
        simp [edist_dist, dist_eq_norm] }
  let rigid : Point3 ≃ᵢ Point3 := translate.trans A
  have hrigid : ∀ x, rigid x = A (x - T.base) := by
    intro x; rfl

  have hsegment :
      rigid '' Kakeya.unitSegment T.base T.direction =
        Kakeya.unitSegment 0 e0 := by
    ext y
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp [hrigid, hA, A.map_smul]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
      simp [hrigid, hA, A.map_smul]

  have hcthickening : ∀ (s : Set Point3),
      rigid '' Metric.cthickening δ s =
        Metric.cthickening δ (rigid '' s) := by
    intro s
    ext z
    simp only [Set.mem_image, Metric.mem_cthickening_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Metric.infEDist_image rigid.isometry]
      exact hx
    · intro hy
      refine ⟨rigid.symm z, ?_, rigid.apply_symm_apply z⟩
      have hdist := Metric.infEDist_image rigid.symm.isometry
        (x := z) (t := rigid '' s)
      have himage : rigid.symm '' (rigid '' s) = s := by
        rw [← Set.image_comp]
        simp
      rw [himage] at hdist
      rw [hdist]
      exact hy

  have hcarrier : rigid '' T.carrier = canonicalTube := by
    rw [Kakeya.DeltaTube.carrier, hcthickening, hsegment]

  have hpreserving : MeasurePreserving rigid volume volume :=
    (A.measurePreserving).comp (measurePreserving_sub_right volume T.base)

  have hbox_meas : MeasurableSet box := by
    have hcont : Continuous (WithLp.toLp 2) :=
      PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
    have hcompact : IsCompact (Set.Icc lo hi) := isCompact_Icc
    exact (hcompact.image hcont).measurableSet

  have hpreimage_sub : rigid ⁻¹' box ⊆ T.carrier := by
    intro x hx
    have h10 : rigid x ∈ canonicalTube := hbox_sub hx
    rw [← hcarrier] at h10
    rcases h10 with ⟨z, hz, hrz⟩
    have h_inj : rigid z = rigid x := hrz
    have hzx : z = x := rigid.injective h_inj
    rw [hzx] at hz
    exact hz

  have hvol_preimage : volume (rigid ⁻¹' box) = volume box :=
    hpreserving.measure_preimage hbox_meas.nullMeasurableSet

  have hmain : volume box ≤ volume T.carrier := by
    calc
      volume box = volume (rigid ⁻¹' box) := hvol_preimage.symm
      _ ≤ volume T.carrier := measure_mono hpreimage_sub

  rw [hbox_vol] at hmain
  exact hmain

end Kakeya.Assouad

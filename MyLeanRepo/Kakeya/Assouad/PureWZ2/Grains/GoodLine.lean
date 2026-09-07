import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Fubini good-line selection lemma

Core measure-theoretic ingredient for WZ1 Lemma 18:
given a measurable set E with positive volume in a ball, find a vertical
line whose intersection with E has large 1D measure.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

-- ============================================================================
-- Coordinate equivalence Point3 ≃ᵐ (ℝ × ℝ) × ℝ, splitting off z as fiber
-- ============================================================================

private def point3ToFiber : Point3 ≃ᵐ (ℝ × ℝ) × ℝ :=
  let toLp3 : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := @WithLp.ofLp (2 : ENNReal) (Fin 3 → ℝ)
      invFun := @WithLp.toLp (2 : ENNReal) (Fin 3 → ℝ)
      left_inv := WithLp.toLp_ofLp (p := (2 : ENNReal))
      right_inv := WithLp.ofLp_toLp (p := (2 : ENNReal))
      measurable_toFun := (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable }
  let e1 : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun (_ : Fin 3) => ℝ) 2
  let e2 : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ :=
    MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ)
  let e3 : (ℝ × (Fin 2 → ℝ)) ≃ᵐ ℝ × (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr e2
  let e4 : (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × ℝ) × ℝ :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      measurable_toFun := measurable_snd.prodMk measurable_fst
      measurable_invFun := measurable_snd.prodMk measurable_fst }
  toLp3.trans e1 |>.trans e3 |>.trans e4

private lemma point3ToFiber_apply (p : Point3) :
    point3ToFiber p = ((p 0, p 1), p 2) := by
  ext <;> simp [point3ToFiber, MeasurableEquiv.piFinSuccAbove_apply] <;> aesop

private lemma point3ToFiber_symm_apply (xyz : (ℝ × ℝ) × ℝ) :
    point3ToFiber.symm xyz = point3 xyz.1.1 xyz.1.2 xyz.2 := by
  ext i; fin_cases i <;> simp [point3ToFiber, point3] <;> aesop

private lemma point3ToFiber_measurePreserving :
    MeasurePreserving point3ToFiber volume volume := by
  have h_toLp : MeasurePreserving (@WithLp.ofLp (2 : ENNReal) (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have h_e1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun (_ : Fin 3) => ℝ) 2) volume volume :=
    volume_preserving_piFinSuccAbove (fun (_ : Fin 3) => ℝ) 2
  have h_e2 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ)) volume volume :=
    volume_preserving_piFinTwo (fun (_ : Fin 2) => ℝ)
  have h_e3 : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ))) volume volume := by
    have hvol : (volume : Measure (ℝ × (Fin 2 → ℝ))) = volume.prod volume := Measure.volume_eq_prod _ _
    have h : MeasurePreserving (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ))) (volume.prod volume) (volume.prod volume) :=
      MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ)) h_e2
    rw [hvol] at *
    exact h
  have h_e4 : MeasurePreserving (Prod.swap : (ℝ × (ℝ × ℝ)) → (ℝ × ℝ) × ℝ) volume volume := by
    have hvol : (volume : Measure (ℝ × (ℝ × ℝ))) = volume.prod volume := Measure.volume_eq_prod _ _
    refine ⟨measurable_snd.prodMk measurable_fst, ?_⟩
    rw [hvol]
    exact Measure.measurePreserving_swap.map_eq
  exact h_e4.comp (h_e3.comp (h_e1.comp h_toLp))

-- ============================================================================
-- Coordinate helpers
-- ============================================================================

private lemma point3_coord0 (x y z : ℝ) : (point3 x y z) 0 = x := by
  simp [point3]
private lemma point3_coord1 (x y z : ℝ) : (point3 x y z) 1 = y := by
  simp [point3]
private lemma point3_coord2 (x y z : ℝ) : (point3 x y z) 2 = z := by
  simp [point3]

private lemma point3_coord_abs_le_norm (v : Point3) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  let e : Point3 := EuclideanSpace.single i (1 : ℝ)
  have h2 : inner ℝ v e = v i := by
    simp [e, EuclideanSpace.inner_single_right]
  have h3 : |inner ℝ v e| ≤ ‖v‖ * ‖e‖ := abs_real_inner_le_norm v e
  have h4 : ‖e‖ = 1 := by simp [e]
  have h5 : |inner ℝ v e| ≤ ‖v‖ := by
    rw [h4] at h3
    simpa using h3
  rw [h2] at h5
  exact h5

-- ============================================================================
-- Main theorem
-- ============================================================================

/--
Fubini vertical line selection.

Given E ⊆ closedBall(center, r) with volume ≥ V, there exists an
anchor point in E such that the vertical line through it has
1D intersection measure ≥ V / (4 * r^2).
-/
theorem fubini_vertical_line_selection
    {E : Set Point3} (hE : MeasurableSet E)
    (hE_finite : volume E ≠ ⊤)
    {r V : ℝ} (hr : 0 < r) (hV_pos : 0 < V)
    (center : Point3)
    (hE_sub : E ⊆ Metric.closedBall center r)
    (hV : ENNReal.ofReal V ≤ volume E) :
    ∃ (anchor : Point3),
      anchor ∈ E ∧
      ENNReal.ofReal (V / (4 * r^2)) ≤
        volume {t : ℝ | point3 (anchor 0) (anchor 1) t ∈ E} := by
  let E' : Set ((ℝ × ℝ) × ℝ) := point3ToFiber '' E
  have hE'_meas : MeasurableSet E' :=
    point3ToFiber.measurableSet_image.mpr hE
  have hvol' : volume E' = volume E := by
    have hmp : MeasurePreserving point3ToFiber volume volume :=
      point3ToFiber_measurePreserving
    have h_inj : Function.Injective point3ToFiber := point3ToFiber.injective
    have h1 : Measure.map point3ToFiber volume E' = volume (point3ToFiber ⁻¹' E') :=
      Measure.map_apply point3ToFiber.measurable hE'_meas
    have h2 : point3ToFiber ⁻¹' E' = E := by
      simpa [E', h_inj.preimage_image] using rfl
    have h3 : Measure.map point3ToFiber volume = volume := hmp.map_eq
    have h4 : volume E' = Measure.map point3ToFiber volume E' := by rw [h3]
    rw [h4, h1, h2]

  let f : (ℝ × ℝ) → ENNReal := fun q =>
    volume {t : ℝ | (q, t) ∈ E'}
  have hfubini : volume E' = ∫⁻ q, f q := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
    exact Measure.prod_apply hE'_meas

  let S : Set (ℝ × ℝ) :=
    Set.Icc (center 0 - r) (center 0 + r) ×ˢ Set.Icc (center 1 - r) (center 1 + r)

  have hS_meas : MeasurableSet S :=
    measurableSet_Icc.prod measurableSet_Icc

  have hS_area : volume S = ENNReal.ofReal (4 * r^2) := by
    have hvol_eq : (volume : Measure (ℝ × ℝ)) = volume.prod volume := Measure.volume_eq_prod _ _
    have hvol_prod : volume S = volume (Set.Icc (center 0 - r) (center 0 + r)) * volume (Set.Icc (center 1 - r) (center 1 + r)) := by
      rw [hvol_eq]
      exact Measure.prod_prod (s := Set.Icc (center 0 - r) (center 0 + r)) (t := Set.Icc (center 1 - r) (center 1 + r))
    rw [hvol_prod]
    have h1 : volume (Set.Icc (center 0 - r) (center 0 + r)) = ENNReal.ofReal (2 * r) := by
      rw [Real.volume_Icc] <;> ring
    have h2 : volume (Set.Icc (center 1 - r) (center 1 + r)) = ENNReal.ofReal (2 * r) := by
      rw [Real.volume_Icc] <;> ring
    rw [h1, h2]
    have hmul : ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * r) = ENNReal.ofReal (4 * r^2) := by
      have hpos : 0 ≤ 2 * r := by positivity
      rw [← ENNReal.ofReal_mul hpos]
      <;> norm_cast <;> ring
    exact hmul

  have hS_nonzero : volume S ≠ 0 := by
    rw [hS_area]
    positivity

  have hsupport : ∀ q ∉ S, f q = 0 := by
    rintro ⟨x, y⟩ hq
    have h_not : ¬(x ∈ Set.Icc (center 0 - r) (center 0 + r) ∧
                    y ∈ Set.Icc (center 1 - r) (center 1 + r)) := by
      intro h
      exact hq ⟨h.1, h.2⟩
    have h_empty : {t : ℝ | ((x, y), t) ∈ E'} = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ht
      rcases ht with ⟨p, hpE, hp_eq⟩
      have hp2 : point3ToFiber.symm ((x, y), t) = p := by
        apply point3ToFiber.injective
        exact hp_eq.symm
      have hball : point3ToFiber.symm ((x, y), t) ∈ Metric.closedBall center r :=
        hE_sub (by rw [hp2]; exact hpE)
      let v : Point3 := point3ToFiber.symm ((x, y), t)
      have hcoord0 : |v 0 - center 0| ≤ r := by
        have h4 : |(v - center) 0| ≤ ‖v - center‖ := point3_coord_abs_le_norm (v - center) 0
        have h5 : (v - center) 0 = v 0 - center 0 := by rfl
        rw [h5] at h4
        have h6 : ‖v - center‖ ≤ r := hball
        exact le_trans h4 h6
      have hcoord1 : |v 1 - center 1| ≤ r := by
        have h4 : |(v - center) 1| ≤ ‖v - center‖ := point3_coord_abs_le_norm (v - center) 1
        have h5 : (v - center) 1 = v 1 - center 1 := by rfl
        rw [h5] at h4
        have h6 : ‖v - center‖ ≤ r := hball
        exact le_trans h4 h6
      have hxin : x ∈ Set.Icc (center 0 - r) (center 0 + r) := by
        have h7 : v 0 = x := by
          have h8 : v = point3 x y t := point3ToFiber_symm_apply ((x, y), t)
          rw [h8, point3_coord0]
        rw [h7] at hcoord0
        have h9 : |x - center 0| ≤ r := hcoord0
        have h10 : -r ≤ x - center 0 ∧ x - center 0 ≤ r := abs_le.mp h9
        exact ⟨by linarith [h10.1], by linarith [h10.2]⟩
      have hyin : y ∈ Set.Icc (center 1 - r) (center 1 + r) := by
        have h7 : v 1 = y := by
          have h8 : v = point3 x y t := point3ToFiber_symm_apply ((x, y), t)
          rw [h8, point3_coord1]
        rw [h7] at hcoord1
        have h9 : |y - center 1| ≤ r := hcoord1
        have h10 : -r ≤ y - center 1 ∧ y - center 1 ≤ r := abs_le.mp h9
        exact ⟨by linarith [h10.1], by linarith [h10.2]⟩
      exact h_not ⟨hxin, hyin⟩
    have h_f : f (x, y) = volume {t : ℝ | ((x, y), t) ∈ E'} := by rfl
    rw [h_f, h_empty]
    simp

  have hintegral_on_S : ∫⁻ q, f q = ∫⁻ q in S, f q := by
    have h_eq : ∀ q, f q = Set.indicator S f q := by
      intro q
      by_cases h : q ∈ S
      · simp [h, Set.indicator_apply]
      · simp [h, Set.indicator_apply, hsupport q h]
    have h : ∫⁻ q, f q = ∫⁻ q, Set.indicator S f q := by
      congr with q
      exact h_eq q
    have hdef : (∫⁻ q in S, f q) = ∫⁻ q, Set.indicator S f q := by
      exact Eq.symm (lintegral_indicator hS_meas f)
    rw [hdef] at *
    exact h

  have htotal : ∫⁻ q in S, f q = volume E' := by
    rw [← hintegral_on_S, hfubini]

  have hfinite : (∫⁻ q in S, f q) ≠ ⊤ := by
    rw [htotal, hvol']
    exact hE_finite

  rcases exists_setLAverage_le hS_nonzero hS_meas.nullMeasurableSet hfinite with
    ⟨q, hq, havg⟩

  have havg' : (∫⁻ x in S, f x) / volume S ≤ f q := by
    simpa [setLAverage_eq] using havg

  have hdenom_ne_zero : ENNReal.ofReal (4 * r^2) ≠ 0 := by positivity
  have hdenom_ne_top : ENNReal.ofReal (4 * r^2) ≠ ⊤ := ENNReal.ofReal_ne_top

  -- Multiply average inequality by volume S to avoid division
  have hS_ne_top : volume S ≠ ⊤ := by
    rw [hS_area]
    exact ENNReal.ofReal_ne_top
  have hcancel : volume S * ((∫⁻ x in S, f x) / volume S) = ∫⁻ x in S, f x :=
    ENNReal.mul_div_cancel hS_nonzero hS_ne_top
  have hcancel2 : ((∫⁻ x in S, f x) / volume S) * volume S = ∫⁻ x in S, f x := by
    rw [mul_comm]
    exact hcancel
  have h1 : (∫⁻ x in S, f x) ≤ f q * volume S := by
    have hmul : ((∫⁻ x in S, f x) / volume S) * volume S ≤ f q * volume S := by
      exact mul_le_mul_of_nonneg_right havg' (by simp)
    rw [hcancel2] at hmul
    exact hmul

  have h2 : ENNReal.ofReal V ≤ f q * ENNReal.ofReal (4 * r^2) := by
    rw [htotal, hvol', hS_area] at h1
    exact le_trans hV h1

  have hpos2 : 0 ≤ V / (4 * r^2) := by
    apply div_nonneg
    · exact hV_pos.le
    · positivity
  have h_eq_real : (V / (4 * r^2)) * (4 * r^2) = V := by
    field_simp [show (4 * r^2) ≠ 0 by positivity] <;> ring
  have h3 : ENNReal.ofReal (V / (4 * r^2)) * ENNReal.ofReal (4 * r^2) = ENNReal.ofReal V := by
    rw [← ENNReal.ofReal_mul hpos2, h_eq_real]

  have h4 : ENNReal.ofReal (V / (4 * r^2)) * ENNReal.ofReal (4 * r^2) ≤ f q * ENNReal.ofReal (4 * r^2) := by
    rw [h3]
    exact h2

  have hfiber_large : ENNReal.ofReal (V / (4 * r^2)) ≤ f q := by
    exact (ENNReal.mul_le_mul_iff_left
      hdenom_ne_zero hdenom_ne_top).mp h4

  have hfiber_pos : 0 < f q := by
    have hpos : 0 < V / (4 * r^2) := by
      apply div_pos hV_pos
      positivity
    have hpos' : 0 < ENNReal.ofReal (V / (4 * r^2)) := ENNReal.ofReal_pos.mpr hpos
    have h : ENNReal.ofReal (V / (4 * r^2)) ≤ f q := hfiber_large
    exact lt_of_lt_of_le hpos' h

  have hmem : ∃ t : ℝ, (q, t) ∈ E' := by
    by_contra h
    have h' : ∀ t : ℝ, (q, t) ∉ E' := by simpa using h
    have h_empty : {t : ℝ | (q, t) ∈ E'} = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false, Set.mem_setOf_eq]
      exact h' t
    have h_fq : f q = 0 := by
      simp [f, h_empty]
    rw [h_fq] at hfiber_pos
    simp at hfiber_pos

  rcases hmem with ⟨t0, ht0⟩

  let anchor : Point3 := point3ToFiber.symm (q, t0)
  have hanchorE : anchor ∈ E := by
    rcases ht0 with ⟨p, hpE, hp_eq⟩
    have h : anchor = p := by
      apply point3ToFiber.injective
      have h4 : point3ToFiber anchor = point3ToFiber p := by
        simpa [anchor] using hp_eq.symm
      exact h4
    rw [h]
    exact hpE

  have hanchor0 : anchor 0 = q.1 := by
    have h4 : anchor = point3ToFiber.symm (q, t0) := rfl
    rw [h4, point3ToFiber_symm_apply, point3_coord0]
  have hanchor1 : anchor 1 = q.2 := by
    have h5 : anchor = point3ToFiber.symm (q, t0) := rfl
    rw [h5, point3ToFiber_symm_apply, point3_coord1]

  have hfiber_eq : f q = volume {t : ℝ | point3 (anchor 0) (anchor 1) t ∈ E} := by
    have h1 : ∀ t : ℝ, (q, t) ∈ E' ↔ point3 (anchor 0) (anchor 1) t ∈ E := by
      intro t
      have h2 : point3ToFiber.symm (q, t) = point3 (anchor 0) (anchor 1) t := by
        rw [point3ToFiber_symm_apply, hanchor0, hanchor1]
      have h3 : (q, t) ∈ E' ↔ point3ToFiber.symm (q, t) ∈ E := by
        constructor
        · rintro ⟨p, hpE, hp_eq⟩
          have h4 : point3ToFiber.symm (q, t) = p := by
            apply point3ToFiber.injective
            exact hp_eq.symm
          rw [h4]; exact hpE
        · intro h
          exact ⟨point3ToFiber.symm (q, t), h, by simp⟩
      rw [h3, h2]
    have h_set : {t : ℝ | (q, t) ∈ E'} = {t : ℝ | point3 (anchor 0) (anchor 1) t ∈ E} := by
      ext t; exact h1 t
    simpa [f] using congr_arg volume h_set

  exact ⟨anchor, hanchorE, by rw [←hfiber_eq]; exact hfiber_large⟩

/-- Directional form of `fubini_vertical_line_selection`.  An orthogonal
reflection sends the supplied unit direction to the vertical axis, without
changing volume or the enclosing-ball radius.  Translating the resulting
one-dimensional parameter makes the chosen base point lie in `E`. -/
theorem fubini_directional_line_selection
    {E : Set Point3} (hE : MeasurableSet E)
    (hE_finite : volume E ≠ ⊤)
    {r V : ℝ} (hr : 0 < r) (hV_pos : 0 < V)
    (center : Point3)
    (hE_sub : E ⊆ Metric.closedBall center r)
    (hV : ENNReal.ofReal V ≤ volume E)
    (direction : Point3) (hdirection : ‖direction‖ = 1) :
    ∃ anchor : Point3,
      anchor ∈ E ∧
      ENNReal.ofReal (V / (4 * r ^ 2)) ≤
        volume {t : ℝ | anchor + t • direction ∈ E} := by
  let vertical : Point3 := point3 0 0 1
  have hvertical : ‖vertical‖ = 1 := by
    simp [vertical, point3, EuclideanSpace.norm_eq]
  let orthogonal : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (direction - vertical))ᗮ
  have horthogonalDirection : orthogonal direction = vertical :=
    Submodule.reflection_sub (hdirection.trans hvertical.symm)
  let transformed : Set Point3 := orthogonal '' E
  have htransformedMeasurable : MeasurableSet transformed := by
    let measurableOrthogonal : Point3 ≃ᵐ Point3 :=
      { toFun := orthogonal
        invFun := orthogonal.symm
        left_inv := orthogonal.left_inv
        right_inv := orthogonal.right_inv
        measurable_toFun := orthogonal.continuous.measurable
        measurable_invFun := orthogonal.symm.continuous.measurable }
    exact measurableOrthogonal.measurableSet_image.mpr hE
  have htransformedVolume : volume transformed = volume E := by
    have hpreserving : MeasurePreserving orthogonal volume volume :=
      orthogonal.measurePreserving
    have hpreimage : orthogonal ⁻¹' transformed = E := by
      simpa [transformed] using
        Set.preimage_image_eq E orthogonal.injective
    calc
      volume transformed = Measure.map orthogonal volume transformed := by
        rw [hpreserving.map_eq]
      _ = volume (orthogonal ⁻¹' transformed) :=
        Measure.map_apply orthogonal.continuous.measurable
          htransformedMeasurable
      _ = volume E := by rw [hpreimage]
  have htransformedFinite : volume transformed ≠ ⊤ := by
    rw [htransformedVolume]
    exact hE_finite
  have htransformedSub : transformed ⊆
      Metric.closedBall (orthogonal center) r := by
    rintro point ⟨source, hsource, rfl⟩
    simpa [orthogonal.dist_map] using hE_sub hsource
  have htransformedLower : ENNReal.ofReal V ≤ volume transformed := by
    rw [htransformedVolume]
    exact hV
  rcases fubini_vertical_line_selection htransformedMeasurable
      htransformedFinite hr hV_pos (orthogonal center)
      htransformedSub htransformedLower with
    ⟨transformedAnchor, htransformedAnchor, hline⟩
  let anchor : Point3 := orthogonal.symm transformedAnchor
  have hanchorImage : orthogonal anchor = transformedAnchor := by
    simp [anchor]
  have hanchor : anchor ∈ E := by
    have hmember : orthogonal anchor ∈ transformed := by
      rw [hanchorImage]
      exact htransformedAnchor
    rcases hmember with ⟨source, hsource, heq⟩
    have : source = anchor := orthogonal.injective <| by
      rw [heq, hanchorImage]
    rwa [this] at hsource
  let sourceSlice : Set ℝ :=
    {height : ℝ |
      point3 (transformedAnchor 0) (transformedAnchor 1) height ∈
        transformed}
  have hsourceSliceMeasurable : MeasurableSet sourceSlice := by
    exact htransformedMeasurable.preimage
      (continuous_const.add (continuous_id.smul continuous_const)).measurable
  let height := transformedAnchor (2 : Fin 3)
  have hlineImage : ∀ t : ℝ,
      orthogonal (anchor + t • direction) =
        point3 (transformedAnchor 0) (transformedAnchor 1)
          (t + height) := by
    intro t
    rw [orthogonal.map_add, orthogonal.map_smul,
      hanchorImage, horthogonalDirection]
    ext coordinate
    fin_cases coordinate <;>
      simp [vertical, height, point3, smul_eq_mul] <;> ring
  have hparameterSet :
      {t : ℝ | anchor + t • direction ∈ E} =
        (fun t : ℝ => t + height) ⁻¹' sourceSlice := by
    ext t
    change anchor + t • direction ∈ E ↔
      point3 (transformedAnchor 0) (transformedAnchor 1)
        (t + height) ∈ transformed
    rw [← hlineImage]
    constructor
    · intro hmember
      exact ⟨anchor + t • direction, hmember, rfl⟩
    · rintro ⟨source, hsource, heq⟩
      have hsourceEq : source = anchor + t • direction :=
        orthogonal.injective heq
      simpa [← hsourceEq] using hsource
  have htranslation :
      MeasurePreserving (fun t : ℝ => t + height) volume volume :=
    ⟨by fun_prop, map_add_right_eq_self volume height⟩
  have hlineVolume :
      volume {t : ℝ | anchor + t • direction ∈ E} =
        volume sourceSlice := by
    rw [hparameterSet]
    calc
      volume ((fun t : ℝ => t + height) ⁻¹' sourceSlice) =
          Measure.map (fun t : ℝ => t + height) volume sourceSlice :=
        (Measure.map_apply htranslation.measurable
          hsourceSliceMeasurable).symm
      _ = volume sourceSlice := by rw [htranslation.map_eq]
  refine ⟨anchor, hanchor, ?_⟩
  rw [hlineVolume]
  simpa [sourceSlice] using hline

/-- Relative directional Fubini selection.  For a positive finite-volume set
inside a radius-`r` ball, one directional fiber captures at least the total
volume divided by the transverse area bound `4 * r ^ 2`. -/
theorem fubini_directional_line_selection_relative
    {E : Set Point3} (hE : MeasurableSet E)
    (hE_finite : volume E ≠ ⊤)
    (hE_pos : volume E ≠ 0)
    {r : ℝ} (hr : 0 < r)
    (center : Point3)
    (hE_sub : E ⊆ Metric.closedBall center r)
    (direction : Point3) (hdirection : ‖direction‖ = 1) :
    ∃ anchor : Point3,
      anchor ∈ E ∧
      volume E ≤ ENNReal.ofReal (4 * r ^ 2) *
        volume {t : ℝ | anchor + t • direction ∈ E} := by
  have hvolumeRealPos : 0 < (volume E).toReal :=
    ENNReal.toReal_pos hE_pos hE_finite
  have hvolumeLower : ENNReal.ofReal (volume E).toReal ≤ volume E := by
    rw [ENNReal.ofReal_toReal hE_finite]
  rcases fubini_directional_line_selection hE hE_finite hr
      hvolumeRealPos center hE_sub hvolumeLower direction hdirection with
    ⟨anchor, hanchor, hline⟩
  refine ⟨anchor, hanchor, ?_⟩
  have hareaPos : 0 < ENNReal.ofReal (4 * r ^ 2) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hline' :
      volume E / ENNReal.ofReal (4 * r ^ 2) ≤
        volume {t : ℝ | anchor + t • direction ∈ E} := by
    calc
      volume E / ENNReal.ofReal (4 * r ^ 2) =
          ENNReal.ofReal ((volume E).toReal / (4 * r ^ 2)) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity),
          ENNReal.ofReal_toReal hE_finite]
      _ ≤ volume {t : ℝ | anchor + t • direction ∈ E} := hline
  have := (ENNReal.div_le_iff hareaPos.ne' ENNReal.ofReal_ne_top).mp hline'
  simpa [mul_comm] using this

end Kakeya.Assouad

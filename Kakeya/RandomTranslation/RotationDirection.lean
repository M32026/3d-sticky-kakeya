/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RotationHaar

/-!
# The direction law of a Haar-random rotation

This file proves the rotational factor of GWZ Appendix A equation (106): for a Haar-random rotation
`u` and a fixed unit vector `d`, the direction `u d` lands in a projective cap of radius `r` with
probability `≲ r^(n-1)`.

## Method

Rather than identify the law of `u d` with the uniform sphere measure (which would need uniqueness
of invariant measures on a homogeneous space, absent from Mathlib), we use an averaging argument
that needs only Tonelli:

* **centre independence** — `Kakeya.rotHaar_dirBall_congr`. Transitivity of the rotation group
  on the sphere (`Kakeya.exists_mem_unitary_apply_eq`) with left invariance of `rotHaar`
  shows `P[‖u d - e‖ ≤ r]` does not depend on the unit vector `e`.
* **averaging** — integrating that constant over `e` against the uniform sphere measure and swapping
  the order of integration (Tonelli) turns it into
  `∫_u (sphere measure of the cap of radius r about u d) du`, which the geometric bound
  `Kakeya.toSphere_projectiveCap_le` controls by `≲ r^(n-1)` pointwise in `u`.

Dividing by the total sphere mass gives the result. No packing or separated-set construction is
needed.

The uniform sphere measure is used in its pushed-forward form `Kakeya.sphereMeasure`, a measure on
`E` concentrated on the unit sphere, so that every set in sight lives in `E`.

Directions stay projective (`min ‖x - d₀‖ ‖x + d₀‖`) throughout, since a tube axis is
unoriented; the projective cap splits into the two ordinary caps about `±d₀`, which costs a
factor `2`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Evaluation of a rotation at a fixed vector is continuous. -/
theorem continuous_unitaryApply (d : E) :
    Continuous (fun u : unitary (E →L[ℝ] E) => (u : E →L[ℝ] E) d) := by
  exact (continuous_eval_const d).comp continuous_subtype_val

/-- **The uniform measure on the unit sphere of `E`, pushed forward into `E`.**
This is Mathlib's `MeasureTheory.Measure.toSphere` transported along the inclusion of the sphere, so
that it can be paired with measures on `E` without subtype bookkeeping. Its total mass is
`n · volume (ball 0 1)`, not `1`. -/
def sphereMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  ((volume : Measure E).toSphere).map Subtype.val

instance instIsFiniteMeasureSphereMeasure : IsFiniteMeasure (sphereMeasure E) := by
  constructor
  have huniv : sphereMeasure E Set.univ = (Module.finrank ℝ E) * volume (ball (0 : E) 1) := by
    rw [sphereMeasure]
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    simp
  rw [huniv]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top (Module.finrank ℝ E))
    (MeasureTheory.measure_ball_lt_top (x := (0 : E)) (r := 1))

/-- The total mass of the sphere measure. -/
theorem sphereMeasure_univ :
    sphereMeasure E Set.univ = (Module.finrank ℝ E) * volume (ball (0 : E) 1) := by
  rw [sphereMeasure]
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp

theorem sphereMeasure_univ_ne_zero [Nontrivial E] :
    sphereMeasure E Set.univ ≠ 0 := by
  rw [sphereMeasure_univ]
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℝ) (M := E))))
    (ne_of_gt (Metric.measure_ball_pos volume (0 : E) one_pos))

/-- **Cap bound for the sphere measure**, transported from
`Kakeya.toSphere_projectiveCap_le`. -/
theorem sphereMeasure_closedBall_le [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    sphereMeasure E {x : E | ‖x - c‖ ≤ r}
      ≤ (Module.finrank ℝ E)
          * (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
  have hmeas : MeasurableSet {x : E | ‖x - c‖ ≤ r} := by
    rw [show {x : E | ‖x - c‖ ≤ r} = Metric.closedBall c r by
      ext x
      simp [Metric.mem_closedBall, dist_eq_norm]]
    exact measurableSet_closedBall
  rw [sphereMeasure, Measure.map_apply measurable_subtype_coe hmeas]
  refine toSphere_projectiveCap_le c hc hr hr1 (hmeas.preimage measurable_subtype_coe) ?_
  intro u hu
  exact le_trans (min_le_left _ _) hu

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Centre independence.** By transitivity of the rotation group on the unit sphere and left
invariance of Haar measure, the probability that the random direction `u d` lies within `r` of a
fixed unit vector does not depend on which unit vector. -/
theorem rotHaar_dirBall_congr {d : E} (_hd : ‖d‖ = 1)
    {e e' : E} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) (r : ℝ) :
    rotHaar (E := E) {u | ‖(u : E →L[ℝ] E) d - e‖ ≤ r}
      = rotHaar (E := E) {u | ‖(u : E →L[ℝ] E) d - e'‖ ≤ r} := by
  obtain ⟨Q, hQ⟩ := Kakeya.exists_mem_unitary_apply_eq he he'
  have hnorm : ∀ v : unitary (E →L[ℝ] E),
      ‖(((Q * v : unitary (E →L[ℝ] E)) : E →L[ℝ] E) d) - e'‖ =
        ‖((v : E →L[ℝ] E) d) - e‖ := by
    intro v
    rw [← hQ]
    rw [Submonoid.coe_mul]
    rw [ContinuousLinearMap.mul_apply]
    rw [← map_sub (↑Q : E →L[ℝ] E)]
    rw [Kakeya.norm_apply_of_mem_unitary Q.property]
  have hset : (fun v : unitary (E →L[ℝ] E) => Q * v) ⁻¹'
      {u : unitary (E →L[ℝ] E) | ‖((u : E →L[ℝ] E) d) - e'‖ ≤ r}
      = {u : unitary (E →L[ℝ] E) | ‖((u : E →L[ℝ] E) d) - e‖ ≤ r} := by
    ext v
    rw [Set.mem_preimage]
    simp only [Set.mem_setOf]
    rw [hnorm v]
  rw [← hset]
  rw [MeasureTheory.measure_preimage_mul]

/-- **The ordinary (oriented) direction-cap bound for a Haar-random rotation.** -/
theorem rotHaar_dirBall_le [Nontrivial E] :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ {d e : E}, ‖d‖ = 1 → ‖e‖ = 1 → ∀ {r : ℝ}, 0 < r → r ≤ 1 →
        rotHaar (E := E) {u | ‖(u : E →L[ℝ] E) d - e‖ ≤ r}
          ≤ C * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) := by
  let C0 : ENNReal := ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
  let Ctotal : ENNReal := (Module.finrank ℝ E) * (2 * C0)
  let C : ENNReal := Ctotal / sphereMeasure E Set.univ
  have hfn_ne : (Module.finrank ℝ E : ENNReal) ≠ ⊤ :=
    ne_of_lt (ENNReal.natCast_lt_top (Module.finrank ℝ E))
  have htwo_ne : (2 : ENNReal) ≠ ⊤ := by
    exact ENNReal.coe_ne_top (r := (2 : NNReal))
  have htube_ne : (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)) ≠ ⊤ := by
    exact ENNReal.coe_ne_top (r := (Tube.volume_le.C (Module.finrank ℝ E) : NNReal))
  have hCtot_ne : Ctotal ≠ ⊤ := by
    dsimp [Ctotal]
    exact ENNReal.mul_ne_top hfn_ne (ENNReal.mul_ne_top htwo_ne htube_ne)
  have hCne' : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.div_ne_top hCtot_ne Kakeya.sphereMeasure_univ_ne_zero
  refine ⟨C, hCne', ?_⟩
  intro d e hd he r hr hr1
  let μ : Measure (unitary (E →L[ℝ] E)) := rotHaar
  let σ : Measure E := sphereMeasure E
  let rpow : ENNReal := ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
  let p : ENNReal := μ {u : unitary (E →L[ℝ] E) | ‖((u : E →L[ℝ] E) d) - e‖ ≤ r}
  let K : ENNReal := (Module.finrank ℝ E)
    * (2 * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)) * rpow)
  let S : Set (E × unitary (E →L[ℝ] E)) :=
    {q | ‖(((q.2 : unitary (E →L[ℝ] E) ) : E →L[ℝ] E) d) - q.1‖ ≤ r}
  have hmeasS : MeasurableSet S := by
    have h1 : Continuous (fun q : E × unitary (E →L[ℝ] E) =>
        ((q.2 : unitary (E →L[ℝ] E)) : E →L[ℝ] E) d) :=
      Continuous.comp (continuous_unitaryApply d) continuous_snd
    have hf : Continuous (fun q : E × unitary (E →L[ℝ] E) => q.1) := continuous_fst
    have hsub : Continuous (fun q : E × unitary (E →L[ℝ] E) =>
        ((q.2 : unitary (E →L[ℝ] E)) : E →L[ℝ] E) d - q.1) := h1.sub hf
    have hnorm : Continuous (fun q : E × unitary (E →L[ℝ] E) =>
        ‖((q.2 : unitary (E →L[ℝ] E)) : E →L[ℝ] E) d - q.1‖) := hsub.norm
    have hclosed : IsClosed {q : E × unitary (E →L[ℝ] E) |
        ‖((q.2 : unitary (E →L[ℝ] E)) : E →L[ℝ] E) d - q.1‖ ≤ r} :=
      isClosed_le hnorm continuous_const
    simpa [S] using hclosed.measurableSet
  have hsplit : ∀ y : sphere (0 : E) 1, μ (Prod.mk (y : E) ⁻¹' S) = p := by
    intro y
    have hx : ‖(y : E)‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
    have hslice : Prod.mk (y : E) ⁻¹' S =
        {u : unitary (E →L[ℝ] E) | ‖((u : E →L[ℝ] E) d) - (y : E)‖ ≤ r} := by
      ext u
      simp [S]
    rw [hslice]
    exact (rotHaar_dirBall_congr (E := E) hd he hx r).symm
  have hmeas2 : Measurable (fun x : E => μ (Prod.mk x ⁻¹' S)) := by
    exact (measurable_measure_prodMk_left hmeasS)
  have hc : (σ.prod μ) S = p * σ Set.univ := by
    rw [Measure.prod_apply hmeasS]
    have hlin : (∫⁻ x : E, μ (Prod.mk x ⁻¹' S) ∂(σ)) =
        (∫⁻ y : sphere (0 : E) 1, μ (Prod.mk (y : E) ⁻¹' S) ∂(volume : Measure E).toSphere) := by
      change (∫⁻ x : E, μ (Prod.mk x ⁻¹' S) ∂(((volume : Measure E).toSphere).map Subtype.val)) = _
      rw [MeasureTheory.lintegral_map hmeas2 measurable_subtype_coe]
    rw [hlin]
    rw [MeasureTheory.lintegral_congr hsplit]
    rw [MeasureTheory.lintegral_const]
    congr 1
    dsimp [σ]
    rw [sphereMeasure]
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    simp
  have hspB : ∀ u : unitary (E →L[ℝ] E), σ ((fun x : E => (x, u)) ⁻¹' S) ≤ K := by
    intro u
    have hu : ‖(u : E →L[ℝ] E) d‖ = 1 := by
      rw [Kakeya.norm_apply_of_mem_unitary u.property d, hd]
    have hslice : (fun x : E => (x, u)) ⁻¹' S =
        {x : E | ‖x - ((u : E →L[ℝ] E) d)‖ ≤ r} := by
      ext x
      simp [S, norm_sub_rev]
    rw [hslice]
    exact Kakeya.sphereMeasure_closedBall_le (E := E) hu hr hr1
  have hprod_le : (σ.prod μ) S ≤ K := by
    rw [Measure.prod_apply_symm hmeasS]
    calc
      (∫⁻ u : unitary (E →L[ℝ] E), σ ((fun x : E => (x, u)) ⁻¹' S) ∂μ)
          ≤ ∫⁻ _u : unitary (E →L[ℝ] E), K ∂μ := by
            exact MeasureTheory.lintegral_mono hspB
      _ = K * μ Set.univ := by rw [MeasureTheory.lintegral_const]
      _ = K := by rw [measure_univ, mul_one]
  have hpσ : p * σ Set.univ ≤ K := by
    rw [← hc]
    exact hprod_le
  have htop : σ Set.univ ≠ ⊤ := MeasureTheory.measure_ne_top σ Set.univ
  have htop0 : σ Set.univ ≠ 0 := by
    dsimp [σ]
    exact Kakeya.sphereMeasure_univ_ne_zero
  have hp : p ≤ K / σ Set.univ :=
    (ENNReal.le_div_iff_mul_le (Or.inl htop0) (Or.inl htop)).mpr hpσ
  have hK : K = Ctotal * rpow := by
    dsimp [K, Ctotal, C0]
    ac_rfl
  have hKdiv : K / σ Set.univ = C * rpow := by
    rw [hK]
    rw [ENNReal.mul_div_right_comm]
  exact le_trans hp (le_of_eq hKdiv)

/-- **The projective direction-cap bound for a Haar-random rotation.**
This is the rotational factor of GWZ Appendix A equation (106): the axis of a randomly rotated tube
lands in a projective `r`-cap about a fixed axis with probability `≲ r^(n-1)`. -/
theorem rotHaar_projectiveCap_le [Nontrivial E] :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ {d d₀ : E}, ‖d‖ = 1 → ‖d₀‖ = 1 → ∀ {r : ℝ}, 0 < r → r ≤ 1 →
        rotHaar (E := E)
            {u : unitary (E →L[ℝ] E) |
              min ‖(u : E →L[ℝ] E) d - d₀‖ ‖(u : E →L[ℝ] E) d + d₀‖ ≤ r}
          ≤ C * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) := by
  obtain ⟨C₁, hC₁, h₀⟩ := rotHaar_dirBall_le (E := E)
  refine ⟨2 * C₁, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hC₁
  · intro d d₀ hd hd₀ r hr hr1
    have hsub :
        {u : unitary (E →L[ℝ] E) |
          min ‖(u : E →L[ℝ] E) d - d₀‖ ‖(u : E →L[ℝ] E) d + d₀‖ ≤ r}
          ⊆ {u | ‖(u : E →L[ℝ] E) d - d₀‖ ≤ r} ∪ {u | ‖(u : E →L[ℝ] E) d - (-d₀)‖ ≤ r} := by
      intro u hu
      simp only [Set.mem_setOf, min_le_iff, sub_neg_eq_add] at hu ⊢
      exact hu
    calc
      rotHaar (E := E)
          {u : unitary (E →L[ℝ] E) |
            min ‖(u : E →L[ℝ] E) d - d₀‖ ‖(u : E →L[ℝ] E) d + d₀‖ ≤ r}
          ≤ rotHaar (E := E)
            ({u | ‖(u : E →L[ℝ] E) d - d₀‖ ≤ r} ∪ {u | ‖(u : E →L[ℝ] E) d - (-d₀)‖ ≤ r}) :=
        measure_mono hsub
      _ ≤ rotHaar (E := E) {u | ‖(u : E →L[ℝ] E) d - d₀‖ ≤ r}
            + rotHaar (E := E) {u | ‖(u : E →L[ℝ] E) d - (-d₀)‖ ≤ r} :=
        measure_union_le _ _
      _ ≤ C₁ * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
            + C₁ * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) := by
        exact add_le_add (h₀ hd hd₀ hr hr1) (h₀ hd (by simpa using hd₀) hr hr1)
      _ = 2 * C₁ * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) := by
        ring

end

end Kakeya

end

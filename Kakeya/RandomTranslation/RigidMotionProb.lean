/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidMotion
public import Kakeya.Tube.EDPacking.AxialAngle

/-!
# GWZ Appendix A equation (106)

For a random rigid motion `R` and `δ`-tubes `T`, `T₀`, GWZ bound

`P[R(T) ⊆ 100 T₀] ≲ |T_δ|²`,

i.e. by `δ^(2(n-1))`. The square is essential: it is what makes the ED multiplicity of the
randomised family in GWZ Lemma 3.8 independent of the number of copies. One factor `δ^(n-1)` is
translational, the other rotational.

## The factored form

The main theorem, `Kakeya.prob_rigidMove_subset_le`, keeps the two factors visibly separate:

`P[R(T) ⊆ K] ≤ C · ρ^(n-1) · volume K`

for any convex target `K` such that containment in `K` forces the axis of `R(T)` to lie
within projective distance `ρ` of a fixed direction `d₀`. Nothing about `K` is used beyond
that hypothesis and its volume, so the rotational factor is not hidden in a volume estimate.

Specialising to `K = ` the `99δ`-thickening of a `δ`-tube `T₀` gives (106): the alignment hypothesis
is then `Kakeya.bad_axial_angle_le` (containment implies the axes are within `O(δ)`), which supplies
`ρ ≍ δ`, and `volume K ≲ δ^(n-1)`; multiplying gives `δ^(2(n-1))`.

## Proof

`Kakeya.rigidMeasure` is a product measure, so `MeasureTheory.Measure.prod_apply` writes the
probability as an integral over the rotation of the translational probability. For each rotation the
inner probability is bounded by `Kakeya.prob_tube_translate_subset_le` (the existing `δ^(n-1)`-sharp
translation estimate), and the integrand vanishes off the set of aligned rotations, whose Haar
measure is `≲ ρ^(n-1)` by `Kakeya.rotHaar_projectiveCap_le`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The event that a rigidly moved tube lands inside a closed target is closed, hence measurable:
it is an intersection over the points of the tube of closed conditions. -/
theorem isClosed_rigidMove_subset {δ : NNReal} (T : Tube δ E) (K : ConvexSpaceBody E) :
    IsClosed {ω : unitary (E →L[ℝ] E) × E |
      (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := by
  have hKclosed : IsClosed K.carrier := K.isCompact.isClosed
  have hset :
      {ω : unitary (E →L[ℝ] E) × E |
          (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} =
        ⋂ x ∈ T.carrier, {ω : unitary (E →L[ℝ] E) × E |
          (ω.1 : E →L[ℝ] E) x + ω.2 ∈ K.carrier} := by
    ext ω
    simp only [Tube.rigidMove_carrier, Set.image_subset_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Kakeya.rigidMap_apply]
    rfl
  rw [hset]
  refine isClosed_biInter (fun x _ => ?_)
  exact hKclosed.preimage (((continuous_unitaryApply x).comp continuous_fst).add continuous_snd)

/-- **The translational factor.** For a fixed rotation, the probability that the translated copy of
`T` lands inside `K` is at most a dimensional constant times `volume K`. This is the existing
`Kakeya.prob_tube_translate_subset_le` transported along `Tube.rigidMove`. -/
theorem prob_translate_rigidMove_le [Nontrivial E] :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ {δ : NNReal} (T : Tube δ E) (K : ConvexSpaceBody E) (u : unitary (E →L[ℝ] E)),
        uniformBallMeasure E {v : E | (T.rigidMove u v).carrier ⊆ K.carrier}
          ≤ C * volume K.carrier := by
  refine ⟨ENNReal.ofReal (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) *
      (volume (Metric.closedBall (0 : E) 1))⁻¹, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.2 (Metric.measure_closedBall_pos volume (0 : E) zero_lt_one).ne')
  · intro δ T K u
    have hcar : ∀ v : E,
        (T.rigidMove u v).carrier = ((T.rigidMove u 0).translate v).carrier := by
      intro v
      have r_im : (v + ·) '' (Kakeya.rigidMap u 0 '' T.carrier) =
          Kakeya.rigidMap u v '' T.carrier := by
        rw [← Set.image_comp]
        congr 1
        funext x
        simp [Kakeya.rigidMap, add_comm]
      calc
        (T.rigidMove u v).carrier = Kakeya.rigidMap u v '' T.carrier := Tube.rigidMove_carrier T u v
        _ = (v + ·) '' (Kakeya.rigidMap u 0 '' T.carrier) := r_im.symm
        _ = (v + ·) '' (T.rigidMove u 0).carrier := by rw [Tube.rigidMove_carrier]
        _ = ((T.rigidMove u 0).translate v).carrier := by
          simp [Tube.translate]
    have hset : {v : E | (T.rigidMove u v).carrier ⊆ K.carrier} =
        {v : E | ((T.rigidMove u 0).translate ((1 : ℝ) • v)).carrier ⊆ K.carrier} := by
      ext ω
      simp only [Set.mem_setOf_eq, one_smul]
      rw [hcar ω]
    rw [hset]
    simpa [one_pow, div_one] using
      prob_tube_translate_subset_le (E := E) (δ := δ) (T := T.rigidMove u 0)
        (K := K) (r := 1) (hr_pos := by norm_num)

/-- **GWZ Appendix A, equation (106), in factored form.**
If containment of the moved tube in `K` forces its axis into the projective `ρ`-cap about `d₀`, then

`P[R(T) ⊆ K] ≤ C · ρ^(n-1) · volume K`.

Both factors are explicit: `ρ^(n-1)` is the probability that the random rotation aligns the axis,
and `volume K` is the translational factor. -/
theorem prob_rigidMove_subset_le [Nontrivial E] :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ {δ : NNReal} (T : Tube δ E) (K : ConvexSpaceBody E) {d₀ : E}, ‖d₀‖ = 1 →
      ∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
        (∀ (u : unitary (E →L[ℝ] E)) (v : E),
            (T.rigidMove u v).carrier ⊆ K.carrier →
            min ‖(u : E →L[ℝ] E) T.direction - d₀‖
              ‖(u : E →L[ℝ] E) T.direction + d₀‖ ≤ ρ) →
        rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
            (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
          ≤ C * ((ρ.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
              * volume K.carrier := by
  obtain ⟨Ctr, hCtr, hTrans⟩ := prob_translate_rigidMove_le (E := E)
  obtain ⟨Crot, hCrot, hRot⟩ := rotHaar_projectiveCap_le (E := E)
  refine ⟨Ctr * Crot, ENNReal.mul_ne_top hCtr hCrot, ?_⟩
  intro δ T K d₀ hd₀ ρ hρ hρ1 halign
  set A : Set (unitary (E →L[ℝ] E)) := {u |
    min ‖(u : E →L[ℝ] E) T.direction - d₀‖
      ‖(u : E →L[ℝ] E) T.direction + d₀‖ ≤ ρ} with hA
  have hA_meas : MeasurableSet A := by
    rw [hA]
    have hf : Continuous (fun u : unitary (E →L[ℝ] E) =>
        ‖(u : E →L[ℝ] E) T.direction - d₀‖) :=
      ((continuous_unitaryApply T.direction).sub continuous_const).norm
    have hg : Continuous (fun u : unitary (E →L[ℝ] E) =>
        ‖(u : E →L[ℝ] E) T.direction + d₀‖) :=
      ((continuous_unitaryApply T.direction).add continuous_const).norm
    exact (isClosed_le (Continuous.min hf hg) continuous_const).measurableSet
  have hpt : ∀ u : unitary (E →L[ℝ] E),
      uniformBallMeasure E {v : E | (T.rigidMove u v).carrier ⊆ K.carrier}
        ≤ A.indicator (fun _ : unitary (E →L[ℝ] E) => Ctr * volume K.carrier) u := by
    intro u
    by_cases hu : u ∈ A
    · simpa [hu] using hTrans T K u
    · have h_empty : {v : E | (T.rigidMove u v).carrier ⊆ K.carrier} = (∅ : Set E) := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hv => hu (halign u v hv)
      rw [h_empty]
      simp [hu, measure_empty]
  calc
    rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
        (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
        = (rotHaar (E := E)).prod (uniformBallMeasure E)
            {ω : unitary (E →L[ℝ] E) × E |
              (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := by
          rw [rigidMeasure]
    _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E (Prod.mk u ⁻¹'
        {ω : unitary (E →L[ℝ] E) × E |
              (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}) ∂(rotHaar (E := E)) := by
          exact Measure.prod_apply (isClosed_rigidMove_subset T K).measurableSet
    _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E
            {v : E | (T.rigidMove u v).carrier ⊆ K.carrier} ∂(rotHaar (E := E)) := by
          rfl
    _ ≤ ∫⁻ u : unitary (E →L[ℝ] E),
            A.indicator (fun _ : unitary (E →L[ℝ] E) => Ctr * volume K.carrier) u
            ∂(rotHaar (E := E)) := by
          exact lintegral_mono (fun u => hpt u)
    _ = ∫⁻ u in A, Ctr * volume K.carrier ∂(rotHaar (E := E)) := by
          rw [lintegral_indicator hA_meas]
    _ = (Ctr * volume K.carrier) * (rotHaar (E := E) A) := by
          rw [setLIntegral_const]
    _ ≤ (Ctr * volume K.carrier) * (Crot *
        ((ρ.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
          have hrotA : rotHaar (E := E) A ≤ Crot *
              ((ρ.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) := by
            rw [hA]
            exact hRot (Tube.norm_direction T) hd₀ hρ hρ1
          exact mul_le_mul_of_nonneg_left hrotA (by positivity)
    _ = (Ctr * Crot) * ((ρ.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
            * volume K.carrier := by
          ring

/-- **GWZ Appendix A, equation (108), for rigid motions.**
`P[R(T) ⊆ K] ≤ C · volume K` for a random *rigid* motion, with no rotational gain. This is the
estimate the **Frostman** conjunct of GWZ Lemma 3.8 needs: there the rotation is along for the ride
and only the translational spreading matters. It is obtained from the fibrewise translation estimate
`Kakeya.prob_translate_rigidMove_le` by integrating over `rotHaar`, which is a probability measure.

Contrast `Kakeya.prob_rigidMove_bad_le` below, the *ED* conjunct, which does exploit the
rotation and gains the second factor of `δ^(n-1)`. -/
theorem prob_rigidMove_subset_volume_le [Nontrivial E] :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ {δ : NNReal} (T : Tube δ E) (K : ConvexSpaceBody E),
        rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
            (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
          ≤ C * volume K.carrier := by
  obtain ⟨Ctr, hCtr, hTrans⟩ := prob_translate_rigidMove_le (E := E)
  refine ⟨Ctr, hCtr, ?_⟩
  intro δ T K
  calc
    rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
        (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
        = (rotHaar (E := E)).prod (uniformBallMeasure E)
            {ω : unitary (E →L[ℝ] E) × E |
              (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := by
          rw [rigidMeasure]
    _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E (Prod.mk u ⁻¹'
        {ω : unitary (E →L[ℝ] E) × E |
            (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}) ∂(rotHaar (E := E)) := by
        exact Measure.prod_apply (isClosed_rigidMove_subset T K).measurableSet
    _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E
            {v : E | (T.rigidMove u v).carrier ⊆ K.carrier} ∂(rotHaar (E := E)) := by
        rfl
    _ ≤ ∫⁻ _u : unitary (E →L[ℝ] E), Ctr * volume K.carrier ∂(rotHaar (E := E)) := by
        exact lintegral_mono (fun u => hTrans T K u)
    _ = Ctr * volume K.carrier * rotHaar (E := E) Set.univ := by
        rw [lintegral_const]
    _ = Ctr * volume K.carrier := by
        rw [measure_univ, mul_one]

/-- **GWZ Appendix A, equation (106).**
For a random rigid motion `R` and `δ`-tubes `T`, `T₀`, the probability that `R(T)` lands inside the
`99δ`-thickening of `T₀` is at most `C · δ^(2(n-1))`. In dimension `3` the exponent is `4`.

The two factors are produced separately and multiplied:

* the **rotational** factor `δ^(n-1)`: containment in the thickening forces the axes to be
  projectively `O(δ)`-close (`Kakeya.bad_axial_angle_le`), and the Haar measure of that cap is
  `≲ δ^(n-1)` (`Kakeya.rotHaar_projectiveCap_le`, used inside
  `Kakeya.prob_rigidMove_subset_le`);
* the **translational** factor `δ^(n-1)`: the thickening is itself a `100δ`-tube
  (`Tube.toConvexBody_cthickening_eq`), so it has volume `≲ δ^(n-1)`
  (`Tube.volume_le`).

The smallness threshold `δ₀` only has to make `100δ ≤ 1` and the angular radius at most `1`; it
depends on the dimension alone. -/
theorem prob_rigidMove_bad_le [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (C : ENNReal) (δ₀ : NNReal), C ≠ ⊤ ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → ∀ (T T₀ : Tube δ E),
        rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
            (T.rigidMove ω.1 ω.2).carrier
              ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀.carrier}
          ≤ C * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
  obtain ⟨Cprob, hCprob, hProb⟩ := prob_rigidMove_subset_le (E := E)
  obtain ⟨Cax, hCax, hAx⟩ := bad_axial_angle_le (E := E) hn
  let CaxN : NNReal := ⟨Cax, hCax.le⟩
  have hCaxN_co : (CaxN : ℝ) = Cax := rfl
  let δ₀ : NNReal := min (1 / 100) (1 / (CaxN + 1))
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min (by norm_num) (by positivity)
  let C : ENNReal := Cprob * (CaxN : ENNReal) ^ (Module.finrank ℝ E - 1) *
      (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
      (100 : ENNReal) ^ (Module.finrank ℝ E - 1)
  refine ⟨C, δ₀, ?_, hδ₀_pos, ?_⟩
  · dsimp [C]
    have hN : (CaxN : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
      ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h100 : (100 : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
      ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hvC : (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) ≠ ⊤ :=
      ENNReal.coe_ne_top
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hCprob hN) hvC) h100
  · intro δ hδ hδ_le T T₀
    let K : ConvexSpaceBody E := T₀.toConvexSpaceBody.cthickening (99 * (δ : ℝ))
    let ρ : ℝ := Cax * (δ : ℝ)
    have hρ_pos : 0 < ρ := by
      dsimp [ρ]
      exact mul_pos hCax (NNReal.coe_pos.mpr hδ)
    have hδ₁₀₀ : δ ≤ 1 / 100 := le_trans hδ_le (min_le_left _ _)
    have hδ₁ : δ ≤ 1 := le_trans hδ₁₀₀ (by exact_mod_cast (by norm_num : (1 / 100 : ℝ) ≤ 1))
    have hδ_inv : δ ≤ 1 / (CaxN + 1) := le_trans hδ_le (min_le_right _ _)
    have h100δ : (100 * δ : NNReal) ≤ 1 := by
      calc
        100 * δ ≤ 100 * (1 / 100 : NNReal) :=
          mul_le_mul_of_nonneg_left hδ₁₀₀ (by norm_num)
        _ = 1 := by norm_num
    have hρ₁ : ρ ≤ 1 := by
      dsimp [ρ]
      have hδ_inv_r : (δ : ℝ) ≤ ((1 / (CaxN + 1) : NNReal) : ℝ) := by
        exact_mod_cast hδ_inv
      have hCe : Cax * (δ : ℝ) ≤ Cax * ((1 / (CaxN + 1) : NNReal) : ℝ) :=
        mul_le_mul_of_nonneg_left hδ_inv_r hCax.le
      have htop : Cax * ((1 / (CaxN + 1) : NNReal) : ℝ) ≤ 1 := by
        have hco : ((1 / (CaxN + 1) : NNReal) : ℝ) = 1 / ((CaxN : ℝ) + 1) := by
          rw [NNReal.coe_div]
          simp [hCaxN_co]
        rw [hco, hCaxN_co]
        have hden : 0 < (Cax : ℝ) + 1 := by linarith
        rw [one_div, ← div_eq_mul_inv]
        exact (div_le_one₀ hden).mpr (by linarith)
      exact le_trans hCe htop
    have halign : ∀ (u : unitary (E →L[ℝ] E)) (v : E),
        (T.rigidMove u v).carrier ⊆ K.carrier →
        min ‖(u : E →L[ℝ] E) T.direction - T₀.direction‖
          ‖(u : E →L[ℝ] E) T.direction + T₀.direction‖ ≤ ρ := by
      intro u v hsub
      dsimp [ρ]
      have hsub' : (T.rigidMove u v).carrier ⊆
          Metric.cthickening (99 * (δ : ℝ)) T₀.carrier := by
        exact hsub
      have hbad : ENNReal.ofReal (1 : ℝ) * volume (T.rigidMove u v).carrier ≤
          volume ((T.rigidMove u v).carrier ∩
            Metric.cthickening (99 * δ) T₀.carrier) := by
        rw [ENNReal.ofReal_one, one_mul]
        rw [Set.inter_eq_self_of_subset_left hsub']
      simpa [Tube.rigidMove_direction, div_one] using
        hAx hδ hδ₁ (T.rigidMove u v) T₀ (c := 1) one_pos le_rfl hbad
    let s : ℕ := Module.finrank ℝ E - 1
    have hmain : rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
        (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} ≤
        Cprob * ((ρ.toNNReal : NNReal) : ENNReal) ^ s * volume K.carrier := by
      simpa [s] using
        hProb T K (d₀ := T₀.direction) (Tube.norm_direction T₀) hρ_pos hρ₁ halign
    have hKres : K = (T₀.rescale (100 * δ : NNReal)).toConvexSpaceBody := by
      dsimp [K]
      rw [show (99 : ℝ) * (δ : ℝ) = ((99 * δ : NNReal) : ℝ) by
          push_cast; ring]
      rw [Tube.toConvexBody_cthickening_eq (T := T₀) (ρ := 99 * δ)]
      rw [show (δ + 99 * δ : NNReal) = (100 * δ : NNReal) by ring]
    have hvolK : volume K.carrier ≤
        (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
          ((100 * δ : NNReal) : ENNReal) ^ s := by
      rw [hKres]
      simpa [s, ENNReal.coe_pow, ENNReal.coe_mul] using
        Tube.volume_le h100δ (T₀.rescale (100 * δ : NNReal))
    have hρN : ρ.toNNReal = CaxN * δ := by
      dsimp [ρ]
      rw [Real.toNNReal_mul (p := Cax) (q := (δ : ℝ)) hCax.le]
      rw [← hCaxN_co]
      rw [Real.toNNReal_coe, Real.toNNReal_coe]
    have hρ_pow : ((ρ.toNNReal : NNReal) : ENNReal) ^ s =
        (CaxN : ENNReal) ^ s * (δ : ENNReal) ^ s := by
      rw [hρN, ENNReal.coe_mul, mul_pow]
    have hβ_pow : ((100 * δ : NNReal) : ENNReal) ^ s =
        (100 : ENNReal) ^ s * (δ : ENNReal) ^ s := by
      rw [ENNReal.coe_mul, mul_pow]
      simp
    calc
      rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
          (T.rigidMove ω.1 ω.2).carrier ⊆
            Metric.cthickening (99 * (δ : ℝ)) T₀.carrier}
          = rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
              (T.rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := by
            rfl
      _ ≤ Cprob * ((ρ.toNNReal : NNReal) : ENNReal) ^ s
            * volume K.carrier := hmain
      _ ≤ Cprob * ((ρ.toNNReal : NNReal) : ENNReal) ^ s *
            ((Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
              ((100 * δ : NNReal) : ENNReal) ^ s) := by
            exact mul_le_mul_of_nonneg_left hvolK (by positivity)
      _ = Cprob * (CaxN : ENNReal) ^ s * (δ : ENNReal) ^ s *
            (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
            (100 : ENNReal) ^ s * (δ : ENNReal) ^ s := by
            rw [hρ_pow, hβ_pow]
            ring
      _ = Cprob * (CaxN : ENNReal) ^ s *
            (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
            (100 : ENNReal) ^ s * (δ : ENNReal) ^ (2 * s) := by
            rw [two_mul, pow_add]
            ring
      _ = C * (δ : ENNReal) ^ (2 * s) := by
            dsimp [C, s]

end

end Kakeya

end

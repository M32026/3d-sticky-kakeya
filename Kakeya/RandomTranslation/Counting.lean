/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.Measure
public import Kakeya.Probability

/-!
# Tube-contained counts and their Chernoff tails

The random variable `X(ω) = #{i ∈ s | R(ω)(T i) ⊆ K}` of [GWZ, §9], its
product-space copies `X_j` on `Fin J → Ω`, and the Chernoff tail bounds for
`∑_j X_j` obtained from `Probability.lemma_A1_case_lt`.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory

namespace Kakeya

namespace HasUniformTranslation

/-! ### Tube-contained count (the GWZ §9 Frostman-conjunct random variable)

This section introduces the random variable used in [GWZ §9, Lemma `randCF`,
Frostman half]: for a finite family `T : ι → Tube δ E` and a measurable
target `K`, the count `X(ω) := #{i ∈ s | R(ω)(T i) ⊆ K}`.

The count sees the full tube containment event
`{ω | R(ω) · T_i ⊆ K}`, not merely the image of an anchor point. Its trivial
pointwise bound is still `≤ |s|`, but crucially it admits the ED-packing
pointwise bound
`X ≤ C_dim · Δ_max(𝕋) · vol(K) / vol(T_δ)`, which is what GWZ §9 uses to
absorb the `+|s|+1` correction that an anchor-based condition forces. -/

section TubeContainedCount

variable
  {Ω : Type*} [MeasurableSpace Ω]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [HasUniformTranslation Ω E]

variable {ι : Type*} {δ : NNReal}

/-- The set of sample points `ω` whose translation `R(ω)` sends the tube `T`
fully into the test set `K`. Used as the measurable event inside
`tubeContainedCount`. -/
def tubeContainedSet (T : Tube δ E) (K : Set E) : Set Ω :=
  {ω | Translation.actSet (HasUniformTranslation.shift (Ω := Ω) (E := E) ω) T.carrier ⊆ K}

/-- The number of tubes `T i` (for `i ∈ s`) that are sent into the target set
`K` by the translation `R y`, realized as an `ℝ`-valued sum of indicator
functions.

This is the GWZ §9 Frostman-conjunct random variable: it counts the cardinality
of `R(𝕋) ∩ K` (equivalently `|𝕋[R⁻¹(K)]|`). -/
noncomputable def tubeContainedCount (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E) (y : Ω) : ℝ :=
  ∑ i ∈ s, (tubeContainedSet (Ω := Ω) (T i) K).indicator (fun _ : Ω => (1 : ℝ)) y

lemma tubeContainedCount_nonneg (s : Finset ι) (T : ι → Tube δ E) (K : Set E)
    (y : Ω) : 0 ≤ tubeContainedCount (Ω := Ω) s T K y :=
  Finset.sum_nonneg fun _ _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma tubeContainedCount_le_card (s : Finset ι) (T : ι → Tube δ E) (K : Set E)
    (y : Ω) : tubeContainedCount (Ω := Ω) s T K y ≤ (s.card : ℝ) := by
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) (fun i _ => ?_)) ?_
  · by_cases hω : y ∈ (tubeContainedSet (Ω := Ω) (T i) K)
    · rw [Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω]; norm_num
  · simp [Finset.sum_const]

lemma tubeContainedCount_measurable (s : Finset ι) (T : ι → Tube δ E) (K : Set E)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K)) :
    Measurable (tubeContainedCount (Ω := Ω) s T K) := by
  refine Finset.measurable_sum s fun i hi => ?_
  exact measurable_const.indicator (hMeas i hi)

/-- Real-valued form of `Kakeya.sum_volume_eq_densityIn_mul_volume`. -/
private lemma sum_measureReal_eq_densityIn_mul
    (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) :
    ∑ i ∈ s with W i ≤ K, volume.real (W i).carrier =
      (densityIn s W K).toReal * volume.real K.carrier := by
  simp only [MeasureTheory.measureReal_def]
  rw [← ENNReal.toReal_sum fun i _ => (W i).isCompact'.measure_lt_top.ne,
    Kakeya.sum_volume_eq_densityIn_mul_volume, ENNReal.toReal_mul]

/-- Real-valued form of `Kakeya.sum_volume_eq_densityIn_mul_volume'`. -/
private lemma sum_measureReal_eq_densityIn_mul'
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    (h : ∀ i ∈ s, W i ≤ K) :
    ∑ i ∈ s, volume.real (W i).carrier =
      (densityIn s W K).toReal * volume.real K.carrier := by
  rw [← sum_measureReal_eq_densityIn_mul s W K, Finset.filter_true_of_mem h]

/-- **Deterministic Frostman packing count bound.**

If the bodies `W i` (`i ∈ s`) lie in the closed unit ball, have volumes between
`c_vol · δ ^ k` and `M_vol · δ ^ k`, and the family is Frostman-controlled with constant `CF`
in the unit ball, then for every sub-body `K` of the unit ball the number of `W i` contained
in `K` satisfies
`#{i ∈ s | W i ≤ K} · c_vol · vol(B(0,1)) ≤ CF · M_vol · |s| · vol(K)`. -/
private lemma card_filter_le_of_isFrostmanIn [Nontrivial E] {ι : Type*}
    {δ : NNReal} (hδ_pos : (0 : ℝ) < (δ : ℝ)) {k : ℕ}
    (s : Finset ι) (W : ι → ConvexSpaceBody E) {CF c_vol M_vol : ℝ} (hCF_nn : 0 ≤ CF)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s W ConvexSpaceBody.closedUnitBall
      (ENNReal.ofReal CF))
    (hW_in_B1 : ∀ i ∈ s, W i ≤ ConvexSpaceBody.closedUnitBall)
    (hW_vol_lb : ∀ i ∈ s, c_vol * (δ : ℝ) ^ k ≤ volume.real (W i).carrier)
    (hW_vol_ub : ∀ i ∈ s, volume.real (W i).carrier ≤ M_vol * (δ : ℝ) ^ k)
    (K : ConvexSpaceBody E) (hK : K ≤ ConvexSpaceBody.closedUnitBall) :
    ((s.filter (fun i => W i ≤ K)).card : ℝ) *
        (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) ≤
      CF * M_vol * (s.card : ℝ) *
        volume.real K.carrier := by
  have hvolB_pos : 0 < volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
    ENNReal.toReal_pos ConvexSpaceBody.closedUnitBall_volume_pos.ne'
      (ConvexSpaceBody.closedUnitBall (E := E)).isCompact'.measure_lt_top.ne
  have hvolK_nn : 0 ≤ volume.real K.carrier := MeasureTheory.measureReal_nonneg
  -- Step A+B: the count times the minimal volume is at most the density times `vol K`.
  have hStepAB : ((s.filter (fun i => W i ≤ K)).card : ℝ) * (c_vol * (δ : ℝ) ^ k) ≤
      (densityIn s W K).toReal * volume.real K.carrier := by
    rw [← sum_measureReal_eq_densityIn_mul s W K, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => hW_vol_lb i (Finset.mem_filter.mp hi).1
  -- Step C: Frostman comparison with the unit ball, transported to `ℝ`.
  have hStepC : (densityIn s W K).toReal ≤
      CF * (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal := by
    have h1 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (densityIn_ne_top s W _)) (hFrost K hK)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCF_nn] at h1
  -- Step D: the density in the unit ball is controlled by the maximal body volume.
  have hStepD : (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal *
      volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≤
        (s.card : ℝ) * (M_vol * (δ : ℝ) ^ k) := by
    rw [← sum_measureReal_eq_densityIn_mul' hW_in_B1, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hW_vol_ub
  refine le_of_mul_le_mul_right ?_ (pow_pos hδ_pos k)
  calc ((s.filter (fun i => W i ≤ K)).card : ℝ) *
          (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) * (δ : ℝ) ^ k
      = ((s.filter (fun i => W i ≤ K)).card : ℝ) * (c_vol * (δ : ℝ) ^ k)
          * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by ring
    _ ≤ ((densityIn s W K).toReal * volume.real K.carrier)
          * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
          mul_le_mul_of_nonneg_right hStepAB hvolB_pos.le
    _ ≤ (CF * (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal
            * volume.real K.carrier)
          * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hStepC hvolK_nn) hvolB_pos.le
    _ = (CF * volume.real K.carrier) *
          ((densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal *
            volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) := by ring
    _ ≤ (CF * volume.real K.carrier) * ((s.card : ℝ) * (M_vol * (δ : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left hStepD (mul_nonneg hCF_nn hvolK_nn)
    _ = CF * M_vol * (s.card : ℝ) * volume.real K.carrier * (δ : ℝ) ^ k := by ring

/-- **Deterministic Frostman packing count bound, for an arbitrary test body.**

Same as `card_filter_le_of_isFrostmanIn`, but with no containment hypothesis on `K`: replacing
`K` by `K ∩ B(0,1)` only shrinks the volume on the right and does not change the count, since
every `W i` already lies in `B(0,1)`. -/
private lemma card_filter_le_of_isFrostmanIn' [Nontrivial E] {ι : Type*}
    {δ : NNReal} (hδ_pos : (0 : ℝ) < (δ : ℝ)) {k : ℕ}
    (s : Finset ι) (W : ι → ConvexSpaceBody E) {CF c_vol M_vol : ℝ}
    (hCF_nn : 0 ≤ CF) (hM_vol_nn : 0 ≤ M_vol)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s W ConvexSpaceBody.closedUnitBall
      (ENNReal.ofReal CF))
    (hW_in_B1 : ∀ i ∈ s, W i ≤ ConvexSpaceBody.closedUnitBall)
    (hW_vol_lb : ∀ i ∈ s, c_vol * (δ : ℝ) ^ k ≤ volume.real (W i).carrier)
    (hW_vol_ub : ∀ i ∈ s, volume.real (W i).carrier ≤ M_vol * (δ : ℝ) ^ k)
    (K : ConvexSpaceBody E) :
    ((s.filter (fun i => W i ≤ K)).card : ℝ) *
        (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) ≤
      CF * M_vol * (s.card : ℝ) *
        volume.real K.carrier := by
  classical
  have hCFMs_nn : 0 ≤ CF * M_vol * (s.card : ℝ) :=
    mul_nonneg (mul_nonneg hCF_nn hM_vol_nn) (Nat.cast_nonneg _)
  by_cases hempty : ∀ i ∈ s, ¬ W i ≤ K
  · rw [Finset.filter_false_of_mem hempty]
    simpa using mul_nonneg hCFMs_nn MeasureTheory.measureReal_nonneg
  · push Not at hempty
    obtain ⟨i₀, hi₀_mem, hi₀_le⟩ := hempty
    set K_inter : ConvexSpaceBody E :=
      ConvexSpaceBody.inter K (ConvexSpaceBody.closedUnitBall (E := E))
        ((W i₀).nonempty'.mono fun x hx => ⟨hi₀_le hx, hW_in_B1 i₀ hi₀_mem hx⟩)
    rw [show s.filter (fun i => W i ≤ K) = s.filter (fun i => W i ≤ K_inter) from
      Finset.filter_congr fun i hi =>
        ⟨fun h x hx => ⟨h hx, hW_in_B1 i hi hx⟩, fun h x hx => (h hx).1⟩]
    refine (card_filter_le_of_isFrostmanIn hδ_pos s W hCF_nn hFrost hW_in_B1 hW_vol_lb
      hW_vol_ub K_inter fun _ hx => hx.2).trans (mul_le_mul_of_nonneg_left ?_ hCFMs_nn)
    exact MeasureTheory.measureReal_mono (fun _ hx => hx.1) K.isCompact'.measure_lt_top.ne

/-- **GWZ §9 ED-packing bound for `tubeContainedCount` (random-variable form).**

Given Frostman-controlled `δ`-shaded-tubes `T : ι → ShadedTube δ E` inside the
closed unit ball, uniform volume bounds `c_vol·δ^(n-1) ≤ vol(T_i) ≤ M_vol·δ^(n-1)`,
and a translation-shape hypothesis `hR_translate` matching the canonical
`Ω = E` instance, the GWZ §9 packing inequality

```
tubeContainedCount s (T·.toTube) K.carrier ω ≤ C_pack · |s| · vol(K)
```

with `C_pack := CF · M_vol / (c_vol · vol(B(0,1)))` holds for *every* `ω : Ω`
and *every* `K : ConvexSpaceBody E` (no constraint `K ⊆ B(0,2)`). This is the
random-variable version of the deterministic Frostman packing count bound,
obtained by translating the action `R(ω)·T_i ⊆ K` to `T_i ⊆ K - R(ω)(0)` and
applying the deterministic count bound to the translated body. -/
lemma tubeContainedCount_le_ED_packing
    [Nontrivial E]
    {δ : NNReal} (hδ_pos : (0 : ℝ) < (δ : ℝ))
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (CF : ℝ) (hCF_nn : 0 ≤ CF)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF))
    (hT_in_B1 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (c_vol M_vol : ℝ) (_hc_vol_pos : 0 < c_vol) (hM_vol_nn : 0 ≤ M_vol)
    (hT_vol_lb :
      ∀ i ∈ s, c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier)
    (hT_vol_ub :
      ∀ i ∈ s, volume.real (T i).carrier ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1))
    (hR_translate :
      ∀ (i : ι) (ω : Ω),
        ((HasUniformTranslation.shift (Ω := Ω) (E := E) ω).actShadedTube
          (T i)).carrier
            = ((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) ω 0)).carrier)
    (K : ConvexSpaceBody E) (ω : Ω) :
    tubeContainedCount (Ω := Ω) s (fun i => (T i).toTube) K.carrier ω *
        (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) ≤
      CF * M_vol * (s.card : ℝ) * volume.real K.carrier := by
  classical
  -- Let `w := R(ω) 0`, the translation vector applied by the translation at 0.
  set w : E := HasUniformTranslation.shift (Ω := Ω) (E := E) ω 0
  -- Translated target body `K_v := K - w`, whose carrier is `(-w + ·) '' K.carrier`.
  set K_v : ConvexSpaceBody E := ConvexSpaceBody.translate K (-w)
  -- Step 1: `R(ω)·T_i ⊆ K` is the same condition as `T_i ⊆ K_v`.
  have hfilter_eq :
      s.filter (fun i =>
        ω ∈ tubeContainedSet (Ω := Ω) ((T i).toTube) K.carrier) =
        s.filter (fun i => (T i).toConvexSpaceBody ≤ K_v) := by
    refine Finset.filter_congr fun i _ => ?_
    have hR_eq : HasUniformTranslation.shift (Ω := Ω) (E := E) ω '' (T i).toTube.carrier =
        (fun x : E => -w + x) ⁻¹' (T i).toTube.carrier := by
      rw [← Translation.actShadedTube_carrier, hR_translate i ω, Tube.translate_carrier]
    unfold tubeContainedSet
    simp only [Set.mem_setOf_eq, Translation.actSet_def, hR_eq]
    refine ⟨fun hsub a ha => ⟨w + a, hsub (by rwa [Set.mem_preimage, neg_add_cancel_left]),
      neg_add_cancel_left w a⟩, fun hsub x hx => ?_⟩
    obtain ⟨y, hy_K, hy_eq⟩ := hsub (show -w + x ∈ (T i).toConvexSpaceBody.carrier from hx)
    exact add_left_cancel hy_eq ▸ hy_K
  -- Step 2: the count equals the filtered cardinality (cast to ℝ).
  have hcount_eq :
      tubeContainedCount (Ω := Ω) s (fun i => (T i).toTube) K.carrier ω =
        ((s.filter (fun i => (T i).toConvexSpaceBody ≤ K_v)).card : ℝ) := by
    unfold tubeContainedCount
    simp only [Set.indicator_apply, Finset.sum_boole, hfilter_eq]
  -- Step 3: the deterministic packing count bound applied to the translated body `K_v`.
  rw [hcount_eq, ← Kakeya.volumeReal_translate K (-w)]
  exact card_filter_le_of_isFrostmanIn' hδ_pos s _ hCF_nn hM_vol_nn hFrost hT_in_B1
    hT_vol_lb hT_vol_ub K_v

/-- Expected tube-contained count: integral over `Ω` of `tubeContainedCount`
is bounded by `uniformConstant · |s| · vol(K)`, using
`prob_actSet_subset_le` term-by-term. -/
lemma integral_tubeContainedCount_le (s : Finset ι) (T : ι → Tube δ E)
    (xT : ι → E) (hxT : ∀ i ∈ s, xT i ∈ (T i).carrier)
    (hxBall : ∀ i ∈ s, xT i ∈ Metric.closedBall (0 : E) 1)
    {K : Set E} (hK : MeasurableSet K) (hKsub : K ⊆ Metric.closedBall (0 : E) 2)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K)) :
    ∫ y, tubeContainedCount (Ω := Ω) s T K y
        ∂(HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω) ≤
      HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K := by
  classical
  set μ : Measure Ω := HasUniformTranslation.measure (Ω := Ω) (E := E) with hμ
  -- Each indicator is bounded by 1, so it's integrable.
  have hint : ∀ i ∈ s, Integrable
      (fun y => (tubeContainedSet (Ω := Ω) (T i) K).indicator
        (fun _ : Ω => (1 : ℝ)) y) μ := by
    intro i hi
    refine Integrable.of_bound (measurable_const.indicator (hMeas i hi)).aestronglyMeasurable
      1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    by_cases hω : y ∈ (tubeContainedSet (Ω := Ω) (T i) K)
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  -- Linearity of integral over Finset.
  rw [show tubeContainedCount (Ω := Ω) s T K =
        fun y => ∑ i ∈ s, (tubeContainedSet (Ω := Ω) (T i) K).indicator
          (fun _ : Ω => (1 : ℝ)) y from rfl,
      MeasureTheory.integral_finsetSum s hint]
  -- For each i, integral of indicator equals (μ tubeContainedSet).toReal.
  have hpoint : ∀ i ∈ s,
      ∫ y, (tubeContainedSet (Ω := Ω) (T i) K).indicator
        (fun _ : Ω => (1 : ℝ)) y ∂μ =
        (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal := by
    intro i hi
    rw [MeasureTheory.integral_indicator (hMeas i hi),
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [Finset.sum_congr rfl hpoint]
  -- Bound each via prob_actSet_subset_le.
  have hbound : ∀ i ∈ s,
      (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal ≤
        HasUniformTranslation.uniformConstant Ω E * volume.real K := by
    intro i hi
    have hKtop : volume K ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono hKsub) measure_closedBall_lt_top)
    have h := prob_actSet_subset_le (Ω := Ω) (T i) (xT i) (hxT i hi)
      (hxBall i hi) hK hKsub
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop) h
    simpa [hμ, tubeContainedSet, Measure.real, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (HasUniformTranslation.uniformConstantPos (Ω := Ω) (E := E)).le] using hreal
  calc ∑ i ∈ s, (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal
      ≤ ∑ _ ∈ s, HasUniformTranslation.uniformConstant Ω E * volume.real K :=
        Finset.sum_le_sum hbound
    _ = HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **General-radius expected tube-contained count.**

Same as `integral_tubeContainedCount_le`, but without the `xT ∈ B(0,1)` /
`K ⊆ B(0,2)` constraints: only `volume K ≠ ⊤` is needed. -/
lemma integral_tubeContainedCount_le_general (s : Finset ι) (T : ι → Tube δ E)
    (xT : ι → E) (hxT : ∀ i ∈ s, xT i ∈ (T i).carrier)
    {K : Set E} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K)) :
    ∫ y, tubeContainedCount (Ω := Ω) s T K y
        ∂(HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω) ≤
      HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K := by
  classical
  set μ : Measure Ω := HasUniformTranslation.measure (Ω := Ω) (E := E) with hμ
  have hint : ∀ i ∈ s, Integrable
      (fun y => (tubeContainedSet (Ω := Ω) (T i) K).indicator
        (fun _ : Ω => (1 : ℝ)) y) μ := by
    intro i hi
    refine Integrable.of_bound (measurable_const.indicator (hMeas i hi)).aestronglyMeasurable
      1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    by_cases hω : y ∈ (tubeContainedSet (Ω := Ω) (T i) K)
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [show tubeContainedCount (Ω := Ω) s T K =
        fun y => ∑ i ∈ s, (tubeContainedSet (Ω := Ω) (T i) K).indicator
          (fun _ : Ω => (1 : ℝ)) y from rfl,
      MeasureTheory.integral_finsetSum s hint]
  have hpoint : ∀ i ∈ s,
      ∫ y, (tubeContainedSet (Ω := Ω) (T i) K).indicator
        (fun _ : Ω => (1 : ℝ)) y ∂μ =
        (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal := by
    intro i hi
    rw [MeasureTheory.integral_indicator (hMeas i hi),
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [Finset.sum_congr rfl hpoint]
  have hbound : ∀ i ∈ s,
      (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal ≤
        HasUniformTranslation.uniformConstant Ω E * volume.real K := by
    intro i hi
    have h := prob_actSet_subset_le_general (Ω := Ω) (T i) (xT i) (hxT i hi) hK hKtop
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop) h
    simpa [hμ, tubeContainedSet, Measure.real, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (HasUniformTranslation.uniformConstantPos (Ω := Ω) (E := E)).le] using hreal
  calc ∑ i ∈ s, (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal
      ≤ ∑ _ ∈ s, HasUniformTranslation.uniformConstant Ω E * volume.real K :=
        Finset.sum_le_sum hbound
    _ = HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Mean tube-contained count from an arbitrary per-tube probability bound.**

Generalizes `integral_tubeContainedCount_le_general`, which hard-codes the abstract
`uniformConstant · vol K` estimate.  Taking the per-tube probability bound `p` as a *hypothesis*
lets a caller substitute a sharper geometric estimate; for tubes translated by `r • ω` with `ω`
uniform on the unit ball, the sharp bound is `prob_tube_translate_subset_le`, which beats
`uniformConstant · vol K` by a factor `r`.

None of `xT`, `hxT`, `hK`, `hKtop` are needed any more: in the original proof they served only to
produce the per-tube bound. -/
lemma integral_tubeContainedCount_le_of_prob (s : Finset ι) (T : ι → Tube δ E)
    {K : Set E}
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    (p : ℝ)
    (hprob : ∀ i ∈ s,
      ((HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω)
        (tubeContainedSet (Ω := Ω) (T i) K)).toReal ≤ p) :
    ∫ y, tubeContainedCount (Ω := Ω) s T K y
        ∂(HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω) ≤ (s.card : ℝ) * p := by
  classical
  set μ : Measure Ω := HasUniformTranslation.measure (Ω := Ω) (E := E) with hμ
  have hint : ∀ i ∈ s, Integrable
      (fun y => (tubeContainedSet (Ω := Ω) (T i) K).indicator
        (fun _ : Ω => (1 : ℝ)) y) μ := by
    intro i hi
    refine Integrable.of_bound (measurable_const.indicator (hMeas i hi)).aestronglyMeasurable
      1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    by_cases hω : y ∈ (tubeContainedSet (Ω := Ω) (T i) K)
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [show tubeContainedCount (Ω := Ω) s T K =
        fun y => ∑ i ∈ s, (tubeContainedSet (Ω := Ω) (T i) K).indicator
          (fun _ : Ω => (1 : ℝ)) y from rfl,
      MeasureTheory.integral_finsetSum s hint]
  have hpoint : ∀ i ∈ s,
      ∫ y, (tubeContainedSet (Ω := Ω) (T i) K).indicator
        (fun _ : Ω => (1 : ℝ)) y ∂μ =
        (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal := by
    intro i hi
    rw [MeasureTheory.integral_indicator (hMeas i hi),
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [Finset.sum_congr rfl hpoint]
  calc ∑ i ∈ s, (μ (tubeContainedSet (Ω := Ω) (T i) K)).toReal
      ≤ ∑ _ ∈ s, p := Finset.sum_le_sum hprob
    _ = (s.card : ℝ) * p := by rw [Finset.sum_const, nsmul_eq_mul]

end TubeContainedCount

/-! ### Tube-contained count in the product space -/

section ProductTubeContainedCount

variable
  {Ω : Type*} [MeasurableSpace Ω]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [HasUniformTranslation Ω E]

variable {ι : Type*} {δ : NNReal}

/-- Product-space version of `tubeContainedCount`, evaluated at the `j`-th
fibre of `Ω^J`. -/
noncomputable def productTubeContainedCount (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E) (J : ℕ) (j : Fin J) (ω : Fin J → Ω) : ℝ :=
  tubeContainedCount (Ω := Ω) s T K (ω j)

lemma productTubeContainedCount_eq_tubeContainedCount_eval (s : Finset ι)
    (T : ι → Tube δ E) (K : Set E) (J : ℕ) (j : Fin J) :
    (fun ω : Fin J → Ω => productTubeContainedCount (Ω := Ω) s T K J j ω) =
      tubeContainedCount (Ω := Ω) s T K ∘ Function.eval j := rfl

lemma productTubeContainedCount_nonneg (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E) (J : ℕ) (j : Fin J) (ω : Fin J → Ω) :
    0 ≤ productTubeContainedCount (Ω := Ω) s T K J j ω :=
  tubeContainedCount_nonneg s T K _

lemma productTubeContainedCount_le_card (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E) (J : ℕ) (j : Fin J) (ω : Fin J → Ω) :
    productTubeContainedCount (Ω := Ω) s T K J j ω ≤ s.card :=
  tubeContainedCount_le_card s T K _

lemma productTubeContainedCount_measurable (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    (J : ℕ) (j : Fin J) :
    Measurable (productTubeContainedCount (Ω := Ω) s T K J j) :=
  (tubeContainedCount_measurable s T K hMeas).comp (measurable_pi_apply j)

/-- The product tube-contained counts are jointly independent. -/
lemma productTubeContainedCount_iIndepFun (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    (J : ℕ) :
    iIndepFun (fun j (ω : Fin J → Ω) =>
        productTubeContainedCount (Ω := Ω) s T K J j ω)
      (productMeasure Ω E J) := by
  unfold productMeasure productTubeContainedCount
  exact iIndepFun_pi
    (μ := fun _ : Fin J => HasUniformTranslation.measure (Ω := Ω) (E := E))
    (X := fun _ : Fin J => fun y : Ω => tubeContainedCount (Ω := Ω) s T K y)
    (fun _ => (tubeContainedCount_measurable s T K hMeas).aemeasurable)

/-- The product tube-contained counts are identically distributed. -/
lemma productTubeContainedCount_identDistrib (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    (J : ℕ) (j₁ j₂ : Fin J) :
    IdentDistrib
      (fun ω : Fin J → Ω => productTubeContainedCount (Ω := Ω) s T K J j₁ ω)
      (fun ω : Fin J → Ω => productTubeContainedCount (Ω := Ω) s T K J j₂ ω)
      (productMeasure Ω E J) (productMeasure Ω E J) := by
  have hmeas : Measurable (tubeContainedCount (Ω := Ω) s T K) :=
    tubeContainedCount_measurable s T K hMeas
  refine ⟨(productTubeContainedCount_measurable s T K hMeas J j₁).aemeasurable,
          (productTubeContainedCount_measurable s T K hMeas J j₂).aemeasurable, ?_⟩
  rw [productTubeContainedCount_eq_tubeContainedCount_eval s T K J j₁,
      productTubeContainedCount_eq_tubeContainedCount_eval s T K J j₂,
      ← Measure.map_map hmeas (measurable_pi_apply j₁),
      ← Measure.map_map hmeas (measurable_pi_apply j₂),
      productMeasure_map_eval, productMeasure_map_eval]

/-- **GWZ §9 density lower bound on Bdd event for the product family.**

For a tube family `T : ι → ShadedTube δ E` with tubes in `B(0,1)` and lower
volume bound `c_vol · δ^(n-1) ≤ vol(T_i)`, and `ω : Fin J → Ω` such that every
`R(ωj)(0) ∈ B(0,1)`, every body
`F^ω(i,j) := (R(ωj).actShadedTube (T i)).toConvexSpaceBody` has carrier inside
`cthickening 1 closedUnitBall = B(0,2)`. Consequently the density of the
product family on this thickening satisfies

```
densityIn (s ×ˢ univ) F^ω (cthickening 1 cUB) · vol(cthickening 1 cUB)
  ≥ |s| · J · c_vol · δ^(n-1).
```

This is the deterministic density lower bound used in the GWZ §9 Frostman half
to close the `BadFrostmanEvent K ⊆ {ω | ∑ X_j > S}` residual. -/
lemma productTubeContainedCount_density_lb_on_Bdd
    {ι : Type*} {δ : NNReal} (_hδ_pos : (0 : ℝ) < (δ : ℝ))
    (s : Finset ι) (T : ι → ShadedTube δ E)
    (c_vol : ℝ) (_hc_vol_pos : 0 < c_vol)
    (hT_in_B1 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (hT_vol_lb :
      ∀ i ∈ s, c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier)
    (hR_translate :
      ∀ (i : ι) (ω : Ω),
        ((HasUniformTranslation.shift (Ω := Ω) (E := E) ω).actShadedTube
          (T i)).carrier
            = ((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) ω 0)).carrier)
    (J : ℕ) (ω : Fin J → Ω)
    (hBdd : ∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
                  ∈ Metric.closedBall (0 : E) 1) :
    (densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J =>
          ((HasUniformTranslation.shift (Ω := Ω) (E := E)
              (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
        (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)))).toReal
      * volume.real
          (ConvexSpaceBody.cthickening 1
            (ConvexSpaceBody.closedUnitBall (E := E))).carrier
      ≥ (s.card : ℝ) * (J : ℝ) * (c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) := by
  set F : ι × Fin J → ConvexSpaceBody E :=
    fun p => ((HasUniformTranslation.shift (Ω := Ω) (E := E)
      (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody with hF_def
  set B2 : ConvexSpaceBody E :=
    ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) with hB2_def
  -- Step 1: every body F p lies inside B2.
  have hB2_carrier : B2.carrier = Metric.closedBall (0 : E) 2 := by
    rw [hB2_def, Kakeya.cthickening_closedUnitBall_carrier (E := E) 1 zero_le_one]; norm_num
  have hsub : ∀ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), F p ≤ B2 := by
    intro p hp
    have hpi := (Finset.mem_product.mp hp).1
    set v : E := HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2) 0
    have hv_norm : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp (hBdd p.2)
    intro x hx
    -- `-v + x` lies in `T p.1 ⊆ B(0,1)`, so `‖x‖ ≤ ‖v‖ + ‖-v + x‖ ≤ 2`.
    have hx_T : -v + x ∈ (T p.1).toConvexSpaceBody.carrier := by
      have hx_F : x ∈ ((HasUniformTranslation.shift (Ω := Ω) (E := E)
        (ω p.2)).actShadedTube (T p.1)).carrier := hx
      rwa [hR_translate p.1 (ω p.2), Tube.translate_carrier] at hx_F
    have hxv_norm : ‖-v + x‖ ≤ 1 := by
      rw [← mem_closedBall_zero_iff, ← ConvexSpaceBody.closedUnitBall_carrier]
      exact hT_in_B1 p.1 hpi hx_T
    have hx_norm : ‖x‖ ≤ 2 := by
      have hbnd : ‖v + (-v + x)‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
      rwa [add_neg_cancel_left] at hbnd
    change x ∈ B2.carrier
    rw [hB2_carrier, mem_closedBall_zero_iff]
    exact hx_norm
  -- Step 2: the real-valued density identity for the family `F` inside `B2`.
  have hsum_eq :
      ∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), volume.real (F p).carrier =
        (densityIn (s ×ˢ (Finset.univ : Finset (Fin J))) F B2).toReal *
          volume.real B2.carrier :=
    sum_measureReal_eq_densityIn_mul' hsub
  -- Step 3: lower bound the sum
  have hvol_F : ∀ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
      c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real (F p).carrier := by
    intro p hp
    have hvol_eq : volume.real (F p).carrier = volume.real (T p.1).carrier := by
      simp only [hF_def, Measure.real, Kakeya.Translation.volume_actShadedTube_carrier]
    exact hvol_eq ▸ hT_vol_lb p.1 (Finset.mem_product.mp hp).1
  -- Step 4: conclude
  rw [ge_iff_le, ← hsum_eq,
    show ((s.card : ℝ) * (J : ℝ)) = ((s ×ˢ (Finset.univ : Finset (Fin J))).card : ℝ) from by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]; push_cast; ring,
    ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum hvol_F

/-- The expectation of each `X_j` under the product measure is bounded by
`uniformConstant · |s| · vol(K)`. -/
lemma productTubeContainedCount_integral_le (s : Finset ι) (T : ι → Tube δ E)
    (xT : ι → E) (hxT : ∀ i ∈ s, xT i ∈ (T i).carrier)
    (hxBall : ∀ i ∈ s, xT i ∈ Metric.closedBall (0 : E) 1)
    {K : Set E} (hK : MeasurableSet K) (hKsub : K ⊆ Metric.closedBall (0 : E) 2)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    (J : ℕ) (j : Fin J) :
    ∫ ω, productTubeContainedCount (Ω := Ω) s T K J j ω ∂(productMeasure Ω E J) ≤
      HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K := by
  change ∫ ω, tubeContainedCount (Ω := Ω) s T K (Function.eval j ω)
        ∂(productMeasure Ω E J) ≤ _
  rw [← MeasureTheory.integral_map (measurable_pi_apply j).aemeasurable
        (tubeContainedCount_measurable s T K hMeas).aestronglyMeasurable,
      productMeasure_map_eval]
  exact integral_tubeContainedCount_le s T xT hxT hxBall hK hKsub hMeas

/-- **General-radius product-space expected tube-contained count.**

Same as `productTubeContainedCount_integral_le`, but without the ball
constraints on the centers `xT` or the target `K`: only `volume K ≠ ⊤`
is needed. -/
lemma productTubeContainedCount_integral_le_general (s : Finset ι) (T : ι → Tube δ E)
    (xT : ι → E) (hxT : ∀ i ∈ s, xT i ∈ (T i).carrier)
    {K : Set E} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    (J : ℕ) (j : Fin J) :
    ∫ ω, productTubeContainedCount (Ω := Ω) s T K J j ω ∂(productMeasure Ω E J) ≤
      HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K := by
  change ∫ ω, tubeContainedCount (Ω := Ω) s T K (Function.eval j ω)
        ∂(productMeasure Ω E J) ≤ _
  rw [← MeasureTheory.integral_map (measurable_pi_apply j).aemeasurable
        (tubeContainedCount_measurable s T K hMeas).aestronglyMeasurable,
      productMeasure_map_eval]
  exact integral_tubeContainedCount_le_general s T xT hxT hK hKtop hMeas

/-- Product-space form of `integral_tubeContainedCount_le_of_prob`. -/
lemma productTubeContainedCount_integral_le_of_prob (s : Finset ι) (T : ι → Tube δ E)
    {K : Set E}
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    (p : ℝ)
    (hprob : ∀ i ∈ s,
      ((HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω)
        (tubeContainedSet (Ω := Ω) (T i) K)).toReal ≤ p)
    (J : ℕ) (j : Fin J) :
    ∫ ω, productTubeContainedCount (Ω := Ω) s T K J j ω ∂(productMeasure Ω E J) ≤
      (s.card : ℝ) * p := by
  change ∫ ω, tubeContainedCount (Ω := Ω) s T K (Function.eval j ω)
        ∂(productMeasure Ω E J) ≤ (s.card : ℝ) * p
  rw [← MeasureTheory.integral_map (measurable_pi_apply j).aemeasurable
        (tubeContainedCount_measurable s T K hMeas).aestronglyMeasurable,
      productMeasure_map_eval]
  exact integral_tubeContainedCount_le_of_prob s T hMeas p hprob

end ProductTubeContainedCount

/-! ### Chernoff tail bound for the sum of hit counts -/

section ChernoffWrapper

variable
  {Ω : Type*} [MeasurableSpace Ω]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [HasUniformTranslation Ω E]

variable {ι : Type*}

/--
**Chernoff tail with parameterized cap `M`** for the product tube-contained
count.

GWZ §9 form: `X_j(ω) := #{i ∈ s | R_j(ω)(T i) ⊆ K}`. The caller supplies the
per-fibre cap `M`, the pointwise bound `X_j ω ≤ M`, and the Chernoff
precondition `J · uc · |s| · vol(K) < M`. Measurability of the per-tube
containment events `{ω | R(ω) · T_i ⊆ K}` is also passed in by the caller —
this is the analytic obstruction that does not follow from the abstract
`HasUniformTranslation` typeclass alone.

The bound is
```
P[∑ X_j > S] ≤ exp(10·e − S/M).
```
-/
lemma productTubeContainedCount_chernoff_tail_scaledM {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ E)
    (xT : ι → E) (hxT : ∀ i ∈ s, xT i ∈ (T i).carrier)
    (hxBall : ∀ i ∈ s, xT i ∈ Metric.closedBall (0 : E) 1)
    {K : Set E} (hK : MeasurableSet K) (hKsub : K ⊆ Metric.closedBall (0 : E) 2)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    {J : ℕ} [NeZero J]
    (M : ℝ) (hM_pos : 0 < M)
    (hXM : ∀ j ω, (productTubeContainedCount (Ω := Ω) s T K J j ω : ℝ) ≤ M)
    (hJmM : (J : ℝ) *
        (HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K) < M)
    (S : ℝ) :
    ((productMeasure Ω E J)
        {ω | ∑ j : Fin J, productTubeContainedCount (Ω := Ω) s T K J j ω > S}).toReal ≤
      Real.exp (10 * Real.exp 1 - S / M) := by
  set μ : Measure (Fin J → Ω) := productMeasure Ω E J with hμ
  set X : Fin J → (Fin J → Ω) → ℝ := fun j ω =>
    productTubeContainedCount (Ω := Ω) s T K J j ω with hX
  set m : ℝ := ∫ ω, X 0 ω ∂μ with hm_def
  have hmeas : ∀ j, Measurable (X j) := fun j =>
    productTubeContainedCount_measurable s T K hMeas J j
  have hbound : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ X j ω ∧ X j ω ≤ M := fun j =>
    Filter.Eventually.of_forall fun ω =>
      ⟨productTubeContainedCount_nonneg s T K J j ω, hXM j ω⟩
  have hm_nn : 0 ≤ m :=
    MeasureTheory.integral_nonneg fun ω => productTubeContainedCount_nonneg s T K J 0 ω
  have hm_le_bd : m ≤ HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) *
        volume.real K :=
    productTubeContainedCount_integral_le s T xT hxT hxBall hK hKsub hMeas J 0
  have hJ_pos : 0 < (J : ℝ) := by exact_mod_cast Nat.pos_of_neZero J
  have hJm : (J : ℝ) * m < M := by
    refine lt_of_le_of_lt ?_ hJmM
    exact mul_le_mul_of_nonneg_left hm_le_bd hJ_pos.le
  have hmM : m ≤ M := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne J)
    have : m ≤ (J : ℝ) * m := by
      have := mul_le_mul_of_nonneg_right h1 hm_nn
      simpa using this
    linarith [hJm]
  have hindep : iIndepFun X μ := productTubeContainedCount_iIndepFun s T K hMeas J
  have hident : ∀ j : Fin J, IdentDistrib (X j) (X 0) μ μ := fun j =>
    productTubeContainedCount_identDistrib s T K hMeas J j 0
  exact Probability.lemma_A1_case_lt J X hmeas M hM_pos m hm_nn hmM hbound rfl hindep hident S hJm

/-- **General-radius product-space Chernoff tail.**

Same conclusion as `productTubeContainedCount_chernoff_tail_scaledM`, but
without the `xT ∈ B(0,1)` / `K ⊆ B(0,2)` constraints: only `volume K ≠ ⊤`
is required. This is the variant invoked by the radius-2 enclosing-ball
version of `RandomTranslation.exists_refinement`. -/
lemma productTubeContainedCount_chernoff_tail_scaledM_general {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ E)
    (xT : ι → E) (hxT : ∀ i ∈ s, xT i ∈ (T i).carrier)
    {K : Set E} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    {J : ℕ} [NeZero J]
    (M : ℝ) (hM_pos : 0 < M)
    (hXM : ∀ j ω, (productTubeContainedCount (Ω := Ω) s T K J j ω : ℝ) ≤ M)
    (hJmM : (J : ℝ) *
        (HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) * volume.real K) < M)
    (S : ℝ) :
    ((productMeasure Ω E J)
        {ω | ∑ j : Fin J, productTubeContainedCount (Ω := Ω) s T K J j ω > S}).toReal ≤
      Real.exp (10 * Real.exp 1 - S / M) := by
  set μ : Measure (Fin J → Ω) := productMeasure Ω E J with hμ
  set X : Fin J → (Fin J → Ω) → ℝ := fun j ω =>
    productTubeContainedCount (Ω := Ω) s T K J j ω with hX
  set m : ℝ := ∫ ω, X 0 ω ∂μ with hm_def
  have hmeas : ∀ j, Measurable (X j) := fun j =>
    productTubeContainedCount_measurable s T K hMeas J j
  have hbound : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ X j ω ∧ X j ω ≤ M := fun j =>
    Filter.Eventually.of_forall fun ω =>
      ⟨productTubeContainedCount_nonneg s T K J j ω, hXM j ω⟩
  have hm_nn : 0 ≤ m :=
    MeasureTheory.integral_nonneg fun ω => productTubeContainedCount_nonneg s T K J 0 ω
  have hm_le_bd : m ≤ HasUniformTranslation.uniformConstant Ω E * (s.card : ℝ) *
        volume.real K :=
    productTubeContainedCount_integral_le_general s T xT hxT hK hKtop hMeas J 0
  have hJ_pos : 0 < (J : ℝ) := by exact_mod_cast Nat.pos_of_neZero J
  have hJm : (J : ℝ) * m < M := by
    refine lt_of_le_of_lt ?_ hJmM
    exact mul_le_mul_of_nonneg_left hm_le_bd hJ_pos.le
  have hmM : m ≤ M := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne J)
    have : m ≤ (J : ℝ) * m := by
      have := mul_le_mul_of_nonneg_right h1 hm_nn
      simpa using this
    linarith [hJm]
  have hindep : iIndepFun X μ := productTubeContainedCount_iIndepFun s T K hMeas J
  have hident : ∀ j : Fin J, IdentDistrib (X j) (X 0) μ μ := fun j =>
    productTubeContainedCount_identDistrib s T K hMeas J j 0
  exact Probability.lemma_A1_case_lt J X hmeas M hM_pos m hm_nn hmM hbound rfl hindep hident S hJm

/-- **Chernoff tail driven by a caller-supplied per-tube probability bound (Brick Z).**

Same conclusion as `productTubeContainedCount_chernoff_tail_scaledM_general`, but the mean is
controlled through an explicit per-tube probability bound `p` instead of the abstract
`uniformConstant · vol K`.  The Chernoff precondition becomes `J · (|s| · p) < M`.

This is what makes a *`J`-independent* density estimate possible.  With the abstract constant the
mean bound coincides with the pointwise cap `M`, so `J · mean < M` forces `J` to be bounded and
Chernoff buys nothing.  Feeding in the sharp `prob_tube_translate_subset_le` instead gains a factor
`r` (the translation radius), and the precondition turns into GWZ's calibration
`J · |s| · |T_δ| ≲ |T_ρ|` — a condition on the *total volume* of the translated
family, not on `J`. -/
lemma productTubeContainedCount_chernoff_tail_of_prob {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ E)
    {K : Set E}
    (hMeas : ∀ i ∈ s, MeasurableSet (tubeContainedSet (Ω := Ω) (T i) K))
    {J : ℕ} [NeZero J]
    (M : ℝ) (hM_pos : 0 < M)
    (hXM : ∀ j ω, (productTubeContainedCount (Ω := Ω) s T K J j ω : ℝ) ≤ M)
    (p : ℝ)
    (hprob : ∀ i ∈ s,
      ((HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω)
        (tubeContainedSet (Ω := Ω) (T i) K)).toReal ≤ p)
    (hJmM : (J : ℝ) * ((s.card : ℝ) * p) < M)
    (S : ℝ) :
    ((productMeasure Ω E J)
        {ω | ∑ j : Fin J, productTubeContainedCount (Ω := Ω) s T K J j ω > S}).toReal ≤
      Real.exp (10 * Real.exp 1 - S / M) := by
  set μ : Measure (Fin J → Ω) := productMeasure Ω E J with hμ
  set X : Fin J → (Fin J → Ω) → ℝ := fun j ω =>
    productTubeContainedCount (Ω := Ω) s T K J j ω with hX
  set m : ℝ := ∫ ω, X 0 ω ∂μ with hm_def
  have hmeas : ∀ j, Measurable (X j) := fun j =>
    productTubeContainedCount_measurable s T K hMeas J j
  have hbound : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ X j ω ∧ X j ω ≤ M := fun j =>
    Filter.Eventually.of_forall fun ω =>
      ⟨productTubeContainedCount_nonneg s T K J j ω, hXM j ω⟩
  have hm_nn : 0 ≤ m :=
    MeasureTheory.integral_nonneg fun ω => productTubeContainedCount_nonneg s T K J 0 ω
  have hm_le_bd : m ≤ (s.card : ℝ) * p :=
    productTubeContainedCount_integral_le_of_prob s T hMeas p hprob J 0
  have hJ_pos : 0 < (J : ℝ) := by exact_mod_cast Nat.pos_of_neZero J
  have hJm : (J : ℝ) * m < M := by
    refine lt_of_le_of_lt ?_ hJmM
    exact mul_le_mul_of_nonneg_left hm_le_bd hJ_pos.le
  have hmM : m ≤ M := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne J)
    have : m ≤ (J : ℝ) * m := by
      have := mul_le_mul_of_nonneg_right h1 hm_nn
      simpa using this
    linarith [hJm]
  have hindep : iIndepFun X μ := productTubeContainedCount_iIndepFun s T K hMeas J
  have hident : ∀ j : Fin J, IdentDistrib (X j) (X 0) μ μ := fun j =>
    productTubeContainedCount_identDistrib s T K hMeas J j 0
  exact Probability.lemma_A1_case_lt J X hmeas M hM_pos m hm_nn hmM hbound rfl hindep hident S hJm

/-- **Pointwise count bound from a `maxDensity` envelope.**

For ANY translation `R y`, the number of tubes of `s` whose `R y`-image lands inside `K` is at
most `M_dens · vol K / V_lb`: pulling `K` back by `R y⁻¹` preserves its volume, the pulled-back
count is controlled by `sum_volume_le_maxDensity_mul_volume`, and each tube has volume `≥ V_lb`.

Note this uses **no** ball-position hypotheses on the tubes or on `K` — that is what makes the
ball-constraint-free Chernoff tail below possible. -/
lemma tubeContainedCount_le_of_maxDensity {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ E) (K : ConvexSpaceBody E)
    (M_dens : ℝ)
    (hM_dens_bound :
      (maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal ≤ M_dens)
    (V_lb : ℝ) (hV_lb_pos : 0 < V_lb)
    (hV_lb : ∀ i ∈ s, V_lb ≤ volume.real (T i).carrier)
    (M : ℝ) (hM_cap : M_dens * volume.real K.carrier / V_lb ≤ M) :
    ∀ y : Ω, tubeContainedCount (Ω := Ω) s T K.carrier y ≤ M := by
  classical
  intro y
  -- Inverse translation.
  set R : Translation E :=
    HasUniformTranslation.shift (Ω := Ω) (E := E) y with hR_def
  let Rinv : Translation E := ⟨-R.translation⟩
  -- `K' := Rinv.actConvexBody K`.
  let K' : ConvexSpaceBody E := Rinv.actConvexBody K
  have hvolK' : volume.real K'.carrier = volume.real K.carrier := by
    change (volume (Rinv.actConvexBody K).carrier).toReal = (volume K.carrier).toReal
    exact congrArg ENNReal.toReal (Translation.volume_actConvexBody Rinv K)
  -- Equivalence `actSet R (T i).carrier ⊆ K.carrier ↔ (T i).toConvexSpaceBody ≤ K'`.
  have hIff : ∀ i,
      Translation.actSet R (T i).carrier ⊆ K.carrier ↔
        (T i).toConvexSpaceBody ≤ K' := by
    intro i
    change (T i).toConvexSpaceBody.translate R.translation ≤ K ↔
      (T i).toConvexSpaceBody ≤ K.translate (-R.translation)
    simpa using (ConvexSpaceBody.le_translate_iff
      (K := (T i).toConvexSpaceBody) (L := K) (-R.translation)).symm
  -- Rewrite the filter set.
  have hfilter_eq :
      s.filter (fun i => y ∈ tubeContainedSet (Ω := Ω) (T i) K.carrier) =
      s.filter (fun i => (T i).toConvexSpaceBody ≤ K') := by
    apply Finset.filter_congr
    intro i _
    unfold tubeContainedSet
    simp only [Set.mem_setOf_eq]
    exact hIff i
  -- `tubeContainedCount = filter cardinality (cast to ℝ)`.
  have hcount_eq :
      tubeContainedCount (Ω := Ω) s T K.carrier y =
        ((s.filter (fun i => (T i).toConvexSpaceBody ≤ K')).card : ℝ) := by
    unfold tubeContainedCount
    have hind : ∀ i ∈ s,
        (tubeContainedSet (Ω := Ω) (T i) K.carrier).indicator
          (fun _ : Ω => (1 : ℝ)) y =
        if y ∈ tubeContainedSet (Ω := Ω) (T i) K.carrier then (1 : ℝ) else 0 := by
      intro i _
      by_cases hω : y ∈ tubeContainedSet (Ω := Ω) (T i) K.carrier
      · rw [Set.indicator_of_mem hω, if_pos hω]
      · rw [Set.indicator_of_notMem hω, if_neg hω]
    rw [Finset.sum_congr rfl hind, Finset.sum_boole]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (congrArg Finset.card hfilter_eq)
  rw [hcount_eq]
  -- `V_lb · |F| ≤ Σ_{i ∈ F} vol(T i) ≤ maxDensity · vol(K') = maxDensity · vol(K)`.
  set F : Finset ι := s.filter (fun i => (T i).toConvexSpaceBody ≤ K') with hF_def
  have hF_subset : F ⊆ s := Finset.filter_subset _ _
  have hV_lb_card :
      V_lb * (F.card : ℝ) ≤ ∑ i ∈ F, volume.real (T i).carrier := by
    calc V_lb * (F.card : ℝ)
        = ∑ _ ∈ F, V_lb := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ F, volume.real (T i).carrier :=
          Finset.sum_le_sum (fun i hi => hV_lb i (hF_subset hi))
  have hSum_le :
      (∑ i ∈ F, volume.real (T i).carrier) ≤ M_dens * volume.real K.carrier := by
    have hSumE :
        (∑ i ∈ s with (T i).toConvexSpaceBody ≤ K', volume (T i).carrier) ≤
          maxDensity s (fun i => (T i).toConvexSpaceBody) * volume K'.carrier := by
      exact sum_volume_le_maxDensity_mul_volume s (fun i => (T i).toConvexSpaceBody) K'
    have hMaxFin : maxDensity s (fun i => (T i).toConvexSpaceBody) ≠ ⊤ :=
      maxDensity_ne_top s _
    have hVK'_fin : volume K'.carrier ≠ ⊤ :=
      K'.isCompact'.measure_lt_top.ne
    have hT_fin : ∀ i ∈ s, volume (T i).carrier ≠ ⊤ :=
      fun i _ => (T i).isCompact.measure_lt_top.ne
    have hSum_toReal :
        (∑ i ∈ F, volume.real (T i).carrier) =
          (∑ i ∈ s with (T i).toConvexSpaceBody ≤ K', volume (T i).carrier).toReal := by
      unfold MeasureTheory.Measure.real
      rw [ENNReal.toReal_sum]
      intro i hi
      exact hT_fin i (Finset.mem_filter.mp hi).1
    rw [hSum_toReal]
    have hStep1 :
        (∑ i ∈ s with (T i).toConvexSpaceBody ≤ K', volume (T i).carrier).toReal ≤
          (maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal *
            volume.real K'.carrier := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top hMaxFin hVK'_fin) hSumE
      rw [ENNReal.toReal_mul] at this
      exact this
    calc (∑ i ∈ s with (T i).toConvexSpaceBody ≤ K', volume (T i).carrier).toReal
        ≤ (maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal *
            volume.real K'.carrier := hStep1
      _ = (maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal *
            volume.real K.carrier := by rw [hvolK']
      _ ≤ M_dens * volume.real K.carrier := by
          apply mul_le_mul_of_nonneg_right hM_dens_bound
          exact MeasureTheory.measureReal_nonneg
  -- Combine into `(F.card : ℝ) ≤ M_dens · vol(K) / V_lb ≤ M`.
  have hCard_le : (F.card : ℝ) ≤ M_dens * volume.real K.carrier / V_lb := by
    rw [le_div_iff₀ hV_lb_pos]
    calc (F.card : ℝ) * V_lb
        = V_lb * (F.card : ℝ) := by ring
      _ ≤ ∑ i ∈ F, volume.real (T i).carrier := hV_lb_card
      _ ≤ M_dens * volume.real K.carrier := hSum_le
  exact le_trans hCard_le hM_cap

end ChernoffWrapper

end HasUniformTranslation

end Kakeya

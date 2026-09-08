/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidEDGood

/-!
# The Frostman-side rigid count

GWZ Lemma 3.8 needs two probabilistic events for the randomised family:

* **B**, the ED multiplicity event, which exploits the rotation and is handled by
  `Kakeya.edBadCount_chernoff_tail` and `Kakeya.exists_rigid_family_ed_good`;
* **A**, the Frostman concentration event, which controls, for every convex test body `K` in a net,
  how many members of the randomised family land inside `K`.

For **A** the rotation is along for the ride: only the translational spreading matters, so the
per-copy input is the rigid-motion form of GWZ (108),
`Kakeya.prob_rigidMove_subset_volume_le`, rather than the sharper (106).

## Why this is not a rewrite of the old argument

The existing translation-only Frostman proof is organised exactly this way: a per-copy count, its
independence and identical distribution under the product measure, a mean bound from the per-copy
probability estimate, and then `Kakeya.Probability.lemma_A1_case_lt` (GWZ Lemma A.1). Only the
*sample space* changes. A fibrewise reduction to the translation-only lemmas is **not** available,
because different copies carry different rotations and the existing
`Kakeya.productTubeContainedCount` machinery is hard-wired to one fixed family for all
copies. So the four structural lemmas are reproved here for `Kakeya.rigidPiMeasure`, verbatim
in shape with the ED versions in `Kakeya/RandomTranslation/RigidMotionChernoff.lean`, and GWZ
A.1 is reused unchanged.

`Kakeya.rigidCountIn` generalises `Kakeya.edBadCount` from a thickened test tube to an arbitrary
convex test body; `Kakeya.edBadCount_eq_rigidCountIn` records that the ED count is the special case,
so the two conjuncts share one set of structural lemmas.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The number of members of the family that the rigid motion `ω` pushes into the convex test body
`K`. This is the Frostman-side count; `Kakeya.edBadCount` is the special case where `K` is the
`99δ`-thickening of a test tube. -/
def rigidCountIn {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) (ω : unitary (E →L[ℝ] E) × E) : ℕ :=
  (@Finset.filter ι (fun i => ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier)
    (Classical.decPred _) s).card

omit [MeasurableSpace E] [BorelSpace E] in
/-- The ED bad count is the rigid count against the thickened test tube. -/
theorem edBadCount_eq_rigidCountIn {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) (ω : unitary (E →L[ℝ] E) × E) :
    edBadCount s T T₀ ω
      = rigidCountIn s T (T₀.toConvexSpaceBody.cthickening (99 * (δ : ℝ))) ω := rfl

/-- The rigid count is a measurable function of the rigid motion. -/
theorem measurable_rigidCountIn {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) :
    Measurable (fun ω : unitary (E →L[ℝ] E) × E => (rigidCountIn s T K ω : ℝ)) := by
  classical
  let P : (unitary (E →L[ℝ] E) × E) → ι → Prop := fun ω i =>
    ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier
  have hmeas : ∀ i ∈ s,
      Measurable (fun ω : unitary (E →L[ℝ] E) × E => if P ω i then (1 : ℝ) else 0) := by
    intro i hi
    have hPmeas : MeasurableSet {ω : (unitary (E →L[ℝ] E)) × E | P ω i} := by
      have hcl : IsClosed {ω : (unitary (E →L[ℝ] E)) × E | P ω i} := by
        simpa [P] using isClosed_rigidMove_subset (T i) K
      exact hcl.measurableSet
    exact Measurable.ite hPmeas measurable_const measurable_const
  have h_eq : (fun ω : (unitary (E →L[ℝ] E)) × E => (rigidCountIn s T K ω : ℝ))
      = fun ω => s.sum (fun i => if P ω i then (1 : ℝ) else 0) := by
    funext ω
    unfold rigidCountIn P
    exact (Finset.sum_boole (fun i => P ω i) s).symm
  rw [h_eq]
  exact Finset.measurable_fun_sum s hmeas

/-- The rigid count of the `j`-th of `J` independent rigid copies. -/
def rigidCountInAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) (J : ℕ) (j : Fin J)
    (ω : Fin J → (unitary (E →L[ℝ] E) × E)) : ℝ :=
  (rigidCountIn s T K (ω j) : ℝ)

theorem measurable_rigidCountInAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) (J : ℕ) (j : Fin J) :
    Measurable (rigidCountInAt s T K J j) :=
  (measurable_rigidCountIn s T K).comp (measurable_pi_apply j)

/-- The rigid counts of the `J` independent copies are jointly independent. -/
theorem iIndepFun_rigidCountInAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) (J : ℕ) :
    ProbabilityTheory.iIndepFun (fun j => rigidCountInAt s T K J j) (rigidPiMeasure E J) := by
  unfold rigidPiMeasure rigidCountInAt
  exact ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin J => rigidMeasure E)
    (X := fun _ : Fin J => fun y : unitary (E →L[ℝ] E) × E => (rigidCountIn s T K y : ℝ))
    (fun _ => (measurable_rigidCountIn s T K).aemeasurable)

/-- The rigid counts of the `J` independent copies are identically distributed. -/
theorem identDistrib_rigidCountInAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) (J : ℕ) (j₁ j₂ : Fin J) :
    ProbabilityTheory.IdentDistrib (rigidCountInAt s T K J j₁) (rigidCountInAt s T K J j₂)
      (rigidPiMeasure E J) (rigidPiMeasure E J) := by
  have hg : Measurable (fun y : unitary (E →L[ℝ] E) × E => (rigidCountIn s T K y : ℝ)) :=
    measurable_rigidCountIn s T K
  have hmap_eval : ∀ j : Fin J, (rigidPiMeasure E J).map (Function.eval j) = rigidMeasure E := by
    intro j
    rw [rigidPiMeasure]
    exact (measurePreserving_eval (μ := fun _ : Fin J => rigidMeasure E) j).map_eq
  refine ⟨(measurable_rigidCountInAt s T K J j₁).aemeasurable,
          (measurable_rigidCountInAt s T K J j₂).aemeasurable, ?_⟩
  rw [show rigidCountInAt s T K J j₁ =
        (fun y : unitary (E →L[ℝ] E) × E => (rigidCountIn s T K y : ℝ)) ∘ Function.eval j₁ by rfl]
  rw [show rigidCountInAt s T K J j₂ =
        (fun y : unitary (E →L[ℝ] E) × E => (rigidCountIn s T K y : ℝ)) ∘ Function.eval j₂ by rfl]
  rw [← Measure.map_map hg (measurable_pi_apply j₁)]
  rw [← Measure.map_map hg (measurable_pi_apply j₂)]
  rw [hmap_eval j₁, hmap_eval j₂]

/-- The mean of one coordinate is the mean over a single rigid motion. -/
theorem integral_rigidCountInAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) {J : ℕ} (j : Fin J) :
    ∫ ω, rigidCountInAt s T K J j ω ∂(rigidPiMeasure E J)
      = ∫ y, (rigidCountIn s T K y : ℝ) ∂(rigidMeasure E) := by
  have hg : Measurable (fun y : unitary (E →L[ℝ] E) × E => (rigidCountIn s T K y : ℝ)) :=
    measurable_rigidCountIn s T K
  have hmap_eval : (rigidPiMeasure E J).map (Function.eval j) = rigidMeasure E := by
    rw [rigidPiMeasure]
    exact (measurePreserving_eval (μ := fun _ : Fin J => rigidMeasure E) j).map_eq
  have hmap_int :
    ∫ y, (rigidCountIn s T K y : ℝ)
        ∂((rigidPiMeasure E J).map (Function.eval j))
      = ∫ ω, (rigidCountIn s T K (Function.eval j ω) : ℝ)
          ∂(rigidPiMeasure E J) := by
    exact MeasureTheory.integral_map (measurable_pi_apply j).aemeasurable
      hg.aestronglyMeasurable
  change ∫ ω, (rigidCountIn s T K (Function.eval j ω) : ℝ) ∂(rigidPiMeasure E J)
      = ∫ y, (rigidCountIn s T K y : ℝ) ∂(rigidMeasure E)
  rw [← hmap_int]
  rw [hmap_eval]

/-- **The Frostman-side mean bound**, by linearity of expectation from the rigid form of GWZ
(108). The mean is proportional to `|s| · volume K`, with no rotational gain — that is the
correct input for the Frostman conjunct. -/
theorem lintegral_rigidCountIn_le [Nontrivial E] :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (K : ConvexSpaceBody E),
        ∫⁻ ω, (rigidCountIn s T K ω : ENNReal) ∂(rigidMeasure E)
          ≤ C * (s.card : ENNReal) * volume K.carrier := by
  classical
  obtain ⟨C₁₀₈, hC₁₀₈, hC⟩ := prob_rigidMove_subset_volume_le (E := E)
  refine ⟨C₁₀₈, hC₁₀₈, ?_⟩
  intro δ ι s T K
  let P : ι → Set (unitary (E →L[ℝ] E) × E) := fun i =>
    {ω : unitary (E →L[ℝ] E) × E | ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
  have hP_meas : ∀ i : ι, MeasurableSet (P i) := by
    intro i
    dsimp [P]
    exact (isClosed_rigidMove_subset (T i) K).measurableSet
  have hmeas : ∀ i : ι,
      Measurable (fun ω : unitary (E →L[ℝ] E) × E =>
        if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0) := by
    intro i
    exact Measurable.ite (hP_meas i) measurable_const measurable_const
  have hcount : ∀ ω : unitary (E →L[ℝ] E) × E,
      (rigidCountIn s T K ω : ENNReal) =
        ∑ i ∈ s, if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0 := by
    intro ω
    dsimp [rigidCountIn]
    rw [Finset.natCast_card_filter]
  have hterm : ∀ i : ι, (∫⁻ ω : unitary (E →L[ℝ] E) × E,
      if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0
      ∂(rigidMeasure E)) = rigidMeasure E (P i) := by
    intro i
    rw [show (fun ω : unitary (E →L[ℝ] E) × E =>
      if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
        = (P i).indicator (fun _ : unitary (E →L[ℝ] E) × E => (1 : ENNReal)) by
        funext ω
        rfl]
    exact lintegral_indicator_one (μ := rigidMeasure E) (s := P i) (hP_meas i)
  have hbound : ∀ i : ι, rigidMeasure E (P i) ≤ C₁₀₈ * volume K.carrier := by
    intro i
    calc
      rigidMeasure E (P i)
          = rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
              ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := rfl
      _ ≤ C₁₀₈ * volume K.carrier := hC (T i) K
  calc
    ∫⁻ ω, (rigidCountIn s T K ω : ENNReal) ∂(rigidMeasure E)
        = ∫⁻ ω, ∑ i ∈ s,
        (if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
        ∂(rigidMeasure E) := by
          apply lintegral_congr
          intro ω
          exact hcount ω
    _ = ∑ i ∈ s, ∫⁻ ω,
            (if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
            ∂(rigidMeasure E) := by
          exact lintegral_finsetSum' (μ := rigidMeasure E) (s := s)
            (f := fun (i : ι) (ω : unitary (E →L[ℝ] E) × E) =>
              if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
            (hf := fun i hi => (hmeas i).aemeasurable)
    _ ≤ ∑ i ∈ s, C₁₀₈ * volume K.carrier := by
          exact Finset.sum_le_sum (fun i _ => (hterm i).trans_le (hbound i))
    _ = (s.card : ENNReal) * (C₁₀₈ * volume K.carrier) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = C₁₀₈ * (s.card : ENNReal) * volume K.carrier := by
          ring

/-- **Real-integral mean bound from an explicit per-tube probability bound.**
The Bochner-integral analogue of `Kakeya.lintegral_rigidCountIn_le`, phrased with an abstract
per-tube probability `p` so that the caller can calibrate it. This mirrors the translation-only
`Kakeya.integral_tubeContainedCount_le_of_prob`. -/
theorem integral_rigidCountIn_le_of_prob {δ : NNReal} {ι : Type*} (s : Finset ι)
    (T : ι → Tube δ E) (K : ConvexSpaceBody E) (p : ℝ)
    (hp : ∀ i ∈ s, (rigidMeasure E
        {ω : unitary (E →L[ℝ] E) × E |
          ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier}).toReal ≤ p) :
    ∫ y, (rigidCountIn s T K y : ℝ) ∂(rigidMeasure E) ≤ (s.card : ℝ) * p := by
  classical
  let P : ι → Set (unitary (E →L[ℝ] E) × E) := fun i =>
    {ω : unitary (E →L[ℝ] E) × E | ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
  have hP_meas : ∀ i ∈ s, MeasurableSet (P i) := by
    intro i hi
    dsimp [P]
    exact (isClosed_rigidMove_subset (T i) K).measurableSet
  have hint : ∀ i ∈ s, Integrable
      (fun y => (P i).indicator (fun _ : unitary (E →L[ℝ] E) × E => (1 : ℝ)) y)
      (rigidMeasure E) := by
    intro i hi
    refine Integrable.of_bound
      (measurable_const.indicator (hP_meas i hi)).aestronglyMeasurable 1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    by_cases hω : y ∈ P i
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hpoint : ∀ i ∈ s,
      ∫ y, (P i).indicator (fun _ : unitary (E →L[ℝ] E) × E => (1 : ℝ)) y ∂(rigidMeasure E) =
        (rigidMeasure E (P i)).toReal := by
    intro i hi
    rw [MeasureTheory.integral_indicator (hP_meas i hi),
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have hcount : ∀ y, (rigidCountIn s T K y : ℝ) =
      ∑ i ∈ s, (P i).indicator (fun _ : unitary (E →L[ℝ] E) × E => (1 : ℝ)) y := by
    intro y
    trans ∑ i ∈ s, if ((T i).rigidMove y.1 y.2).carrier ⊆ K.carrier then (1 : ℝ) else 0
    · dsimp [rigidCountIn]
      exact (Finset.sum_boole (fun i => ((T i).rigidMove y.1 y.2).carrier ⊆ K.carrier) s).symm
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Set.indicator_apply]
      rfl
  calc
    ∫ y, (rigidCountIn s T K y : ℝ) ∂(rigidMeasure E)
        = ∫ y, ∑ i ∈ s, (P i).indicator
          (fun _ : unitary (E →L[ℝ] E) × E => (1 : ℝ)) y
          ∂(rigidMeasure E) := by
          apply integral_congr_ae
          filter_upwards with y
          exact hcount y
    _ = ∑ i ∈ s, ∫ y,
          (P i).indicator (fun _ : unitary (E →L[ℝ] E) × E => (1 : ℝ)) y
          ∂(rigidMeasure E) := by
          exact MeasureTheory.integral_finsetSum s hint
    _ = ∑ i ∈ s, (rigidMeasure E (P i)).toReal := by
          exact Finset.sum_congr rfl hpoint
    _ ≤ ∑ i ∈ s, p := Finset.sum_le_sum (fun i hi => by simpa [P] using hp i hi)
    _ = (s.card : ℝ) * p := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- **Chernoff tail for the Frostman-side count of `J` independent rigid copies.**
GWZ Lemma A.1 applied to `Kakeya.rigidCountInAt`. The pointwise cap `M` and the per-tube probability
`p` are parameters, exactly as in the translation-only
`Kakeya.productTubeContainedCount_chernoff_tail_of_prob`, so that the caller can calibrate
`J · (|s| · p) < M` — which is where the `J`-cancellation enters for the Frostman conjunct. -/
theorem rigidCountIn_chernoff_tail [Nontrivial E] {δ : NNReal} {ι : Type*}
    (s : Finset ι) (T : ι → Tube δ E) (K : ConvexSpaceBody E)
    {J : ℕ} (hJ : 0 < J)
    (M : ℝ) (hM : 0 < M)
    (hXM : ∀ (j : Fin J) (ω : Fin J → (unitary (E →L[ℝ] E) × E)),
      rigidCountInAt s T K J j ω ≤ M)
    (p : ℝ)
    (hp : ∀ i ∈ s, (rigidMeasure E
        {ω : unitary (E →L[ℝ] E) × E |
          ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier}).toReal ≤ p)
    (hJmM : (J : ℝ) * ((s.card : ℝ) * p) < M)
    (S : ℝ) :
    ((rigidPiMeasure E J)
        {ω | ∑ j : Fin J, rigidCountInAt s T K J j ω > S}).toReal
      ≤ Real.exp (10 * Real.exp 1 - S / M) := by
  haveI : NeZero J := ⟨hJ.ne'⟩
  set X : Fin J → (Fin J → (unitary (E →L[ℝ] E) × E)) → ℝ :=
    fun j => rigidCountInAt s T K J j with hX
  set m : ℝ := ∫ y, (rigidCountIn s T K y : ℝ) ∂(rigidMeasure E) with hm_def
  have hmeas : ∀ j : Fin J, Measurable (X j) := fun j => by
    simpa [X] using measurable_rigidCountInAt s T K J j
  have hnn : ∀ (j : Fin J) ω, 0 ≤ X j ω := by
    intro j ω
    dsimp [X]
    exact Nat.cast_nonneg _
  have hbound : ∀ j : Fin J,
      ∀ᵐ ω ∂(rigidPiMeasure E J), 0 ≤ X j ω ∧ X j ω ≤ M := fun j =>
    Filter.Eventually.of_forall fun ω => ⟨hnn j ω, hXM j ω⟩
  have hm_nn : 0 ≤ m := by
    dsimp [m]
    exact MeasureTheory.integral_nonneg fun y => Nat.cast_nonneg _
  have hm_le_bd : m ≤ (s.card : ℝ) * p := by
    exact hm_def.trans_le (integral_rigidCountIn_le_of_prob s T K p hp)
  have hJ_pos : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hJm : (J : ℝ) * m < M := by
    refine lt_of_le_of_lt ?_ hJmM
    exact mul_le_mul_of_nonneg_left hm_le_bd hJ_pos.le
  have hmM : m ≤ M := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne J)
    have hm_le_Jm : m ≤ (J : ℝ) * m := by
      have := mul_le_mul_of_nonneg_right h1 hm_nn
      simpa using this
    linarith [hJm]
  have hindep : ProbabilityTheory.iIndepFun X (rigidPiMeasure E J) := by
    simpa [X] using iIndepFun_rigidCountInAt s T K J
  have hident : ∀ j : Fin J,
      ProbabilityTheory.IdentDistrib (X j) (X 0) (rigidPiMeasure E J) (rigidPiMeasure E J) := by
    intro j
    simpa [X] using identDistrib_rigidCountInAt s T K J j 0
  exact Probability.lemma_A1_case_lt J X hmeas M hM m hm_nn hmM hbound
    (integral_rigidCountInAt s T K (0 : Fin J)) hindep hident S hJm

end

end Kakeya

end

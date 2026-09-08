/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.Counting
public import Kakeya.RandomTranslation.TranslationProb

/-!
# Scaled-translation counts

The counts and Chernoff tail that `RandomTranslation.exists_refinement` consumes,
phrased directly in terms of the predicate `(T i).translate (r • t) ⊆ K` rather
than through `scaledUniformTranslationSelf`.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory

namespace Kakeya

/-! ### Scaled-translation counts: the interface consumed by `RandomTranslation.exists_refinement`

The random-translation lemmas translate tubes by `r • ω` with `ω` uniform on `B(0,1)`, so their bad
events must be phrased against that action, not the unscaled one.  Rather than expose
`scaledUniformTranslationSelf` to callers, we package the counts and the Chernoff tail here in terms
of the canonical `productMeasure E E J` (which is unchanged, since the scaled instance has the same
`measure` field) and the explicit predicate `(T i).translate (r • t) ⊆ K`. -/

section ScaledTranslationCount

open HasUniformTranslation

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

/-- The set of samples `t` whose `r`-scaled translation carries `T` into `K`. -/
def scaledTubeContainedSet (r : ℝ) (T : Tube δ E) (K : Set E) : Set E :=
  {t : E | ((T.translate (r • t)).carrier) ⊆ K}

/-- The number of tubes `T i`, `i ∈ s`, that the `r`-scaled translation by `t` carries into `K`. -/
noncomputable def scaledTubeContainedCount (r : ℝ) (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E) (t : E) : ℝ :=
  ∑ i ∈ s, (scaledTubeContainedSet r (T i) K).indicator (fun _ : E => (1 : ℝ)) t

/-- Product-space form of `scaledTubeContainedCount`, read off the `j`-th coordinate. -/
noncomputable def scaledProductTubeContainedCount (r : ℝ) (s : Finset ι) (T : ι → Tube δ E)
    (K : Set E) (J : ℕ) (j : Fin J) (ω : Fin J → E) : ℝ :=
  scaledTubeContainedCount r s T K (ω j)

/-- The scaled containment event is exactly the generic one for the `r`-scaled motion. -/
lemma tubeContainedSet_scaledUniformTranslationSelf {r : ℝ} (hr : 0 < r) (T : Tube δ E)
    (K : Set E) :
    @tubeContainedSet E _ E _ _ _ _ _ (scaledUniformTranslationSelf (E := E) hr) δ T K
      = scaledTubeContainedSet r T K :=
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- `scaledTubeContainedSet` is closed whenever the target is: it is the intersection over
`x ∈ T.carrier` of the closed preimages `{t | r • t + x ∈ K}`. -/
lemma isClosed_scaledTubeContainedSet (r : ℝ) (T : Tube δ E) {K : Set E}
    (hK_closed : IsClosed K) :
    IsClosed (scaledTubeContainedSet r T K) := by
  have hset_eq : scaledTubeContainedSet r T K = ⋂ x ∈ T.carrier, {t : E | r • t + x ∈ K} := by
    apply Set.Subset.antisymm
    · intro t ht
      -- ht : t ∈ scaledTubeContainedSet r T K  i.e. (T.translate (r • t)).carrier ⊆ K
      have hcarrier : (T.translate (r • t)).carrier = (fun z : E => r • t + z) '' T.carrier := rfl
      have hsub : (fun z : E => r • t + z) '' T.carrier ⊆ K := by
        rw [← hcarrier]; exact ht
      -- Goal: t ∈ ⋂ x ∈ T.carrier, {t : E | r • t + x ∈ K}
      -- i.e. ∀ x ∈ T.carrier, r • t + x ∈ K
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro x hx
      apply hsub
      exact Set.mem_image_of_mem (fun z : E => r • t + z) hx
    · intro t ht
      -- ht : t ∈ ⋂ x ∈ T.carrier, {t : E | r • t + x ∈ K}
      -- i.e. ∀ x ∈ T.carrier, r • t + x ∈ K
      have h_all : ∀ x ∈ T.carrier, r • t + x ∈ K := by
        simpa only [Set.mem_iInter, Set.mem_setOf_eq] using ht
      dsimp [scaledTubeContainedSet]
      have hcarrier : (T.translate (r • t)).carrier = (fun z : E => r • t + z) '' T.carrier := rfl
      rw [hcarrier]
      rintro y ⟨x, hx, rfl⟩
      exact h_all x hx
  rw [hset_eq]
  exact isClosed_biInter fun x _ =>
    hK_closed.preimage ((continuous_const_smul r).add continuous_const)

/-- Measurability of the scaled product count, needed to build the bad events. -/
lemma scaledProductTubeContainedCount_measurable {r : ℝ} (hr : 0 < r) (s : Finset ι)
    (T : ι → Tube δ E) (K : Set E)
    (hMeas : ∀ i ∈ s, MeasurableSet (scaledTubeContainedSet r (T i) K))
    (J : ℕ) (j : Fin J) :
    Measurable (scaledProductTubeContainedCount r s T K J j) := by
  have hMeas' : ∀ i ∈ s, MeasurableSet
      (@tubeContainedSet E _ E _ _ _ _ _ (scaledUniformTranslationSelf (E := E) hr) δ (T i) K) := by
    intro i hi
    rw [tubeContainedSet_scaledUniformTranslationSelf hr (T i) K]
    exact hMeas i hi
  have h := @productTubeContainedCount_measurable E _ E _ _ _ _ _
    (scaledUniformTranslationSelf (E := E) hr) ι δ s T K hMeas' J j
  -- h : Measurable (productTubeContainedCount (Ω := E) (inst := scaledUniformTranslationSelf hr)
  --   s T K J j)
  -- Goal: Measurable (scaledProductTubeContainedCount r s T K J j)
  -- The two functions are equal by definitional unfolding + the bridge lemma
  have h_eq : (fun ω : Fin J → E => @productTubeContainedCount E _ E _ _ _ _ _
      (scaledUniformTranslationSelf (E := E) hr) ι δ s T K J j ω) =
    scaledProductTubeContainedCount r s T K J j := by
    ext ω
    dsimp [productTubeContainedCount, tubeContainedCount,
    scaledProductTubeContainedCount, scaledTubeContainedCount]
    simp [tubeContainedSet_scaledUniformTranslationSelf hr]
  simpa [h_eq] using h

/-- **Pointwise cap for the scaled count from a maximal-density bound.**

If the family `T` has maximal density at most `M_dens` and every tube has volume at least `V_lb`,
then no translate of the family can put more than `M_dens · vol K / V_lb` tubes inside `K`.  This is
the cap `M` fed to `scaledProductTubeContainedCount_chernoff_tail`. -/
lemma scaledTubeContainedCount_le_of_maxDensity {r : ℝ} (hr : 0 < r) (s : Finset ι)
    (T : ι → Tube δ E) (K : ConvexSpaceBody E)
    (M_dens : ℝ)
    (hM_dens_bound : (Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal ≤ M_dens)
    (V_lb : ℝ) (hV_lb_pos : 0 < V_lb)
    (hV_lb : ∀ i ∈ s, V_lb ≤ volume.real (T i).carrier)
    (M : ℝ) (hM_cap : M_dens * volume.real K.carrier / V_lb ≤ M) :
    ∀ t : E, scaledTubeContainedCount r s T K.carrier t ≤ M := by
  intro t
  have h := @tubeContainedCount_le_of_maxDensity E _ E _ _ _ _ _
    (scaledUniformTranslationSelf (E := E) hr) ι δ s T K M_dens hM_dens_bound V_lb hV_lb_pos hV_lb
    M hM_cap t
  simpa [tubeContainedCount, scaledTubeContainedCount,
    tubeContainedSet_scaledUniformTranslationSelf hr] using h

/-- **Chernoff tail for the `r`-scaled translated family.**

The mean is controlled by the sharp per-tube probability `prob_tube_translate_subset_le_toReal`, so
the precondition `hJmM` reads
`J · |s| · (C_n · vol K / (r^(n-1) · vol B₁)) < M`.
With `M := M_dens · vol K / V_lb` the factors of `vol K` cancel and what remains is
`J · |s| · V_lb / r^(n-1) ≲ M_dens` — GWZ's calibration `J · |s| · |T_δ| ≲ |T_ρ|`,
a condition on the total volume of the translated family and **not** a bound on `J`. -/
lemma scaledProductTubeContainedCount_chernoff_tail [Nontrivial E] (s : Finset ι)
    (T : ι → Tube δ E) (K : ConvexSpaceBody E)
    {r : ℝ} (hr_pos : 0 < r)
    (hMeas : ∀ i ∈ s, MeasurableSet (scaledTubeContainedSet r (T i) K.carrier))
    {J : ℕ} [NeZero J]
    (M : ℝ) (hM_pos : 0 < M)
    (hXM : ∀ t : E, scaledTubeContainedCount r s T K.carrier t ≤ M)
    (hJmM : (J : ℝ) * ((s.card : ℝ) *
        ((translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) /
          r ^ (Module.finrank ℝ E - 1) *
          (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K.carrier)) < M)
    (S : ℝ) :
    ((productMeasure E E J)
        {ω : Fin J → E | ∑ j : Fin J,
            scaledProductTubeContainedCount r s T K.carrier J j ω > S}).toReal ≤
      Real.exp (10 * Real.exp 1 - S / M) := by
  set p := (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) /
    r ^ (Module.finrank ℝ E - 1) *
      (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K.carrier with hp
  have hXM' : ∀ (j : Fin J) (ω : Fin J → E),
    (@productTubeContainedCount E _ E _ _ _ _ _
    (scaledUniformTranslationSelf (E := E) hr_pos) ι δ s T K.carrier J j ω : ℝ) ≤ M := by
    intro j ω
    exact hXM (ω j)
  have hprob' : ∀ i ∈ s,
    ((@HasUniformTranslation.measure E _ E _ _ _ _ _
        (scaledUniformTranslationSelf (E := E) hr_pos) : Measure E)
      (@tubeContainedSet E _ E _ _ _ _ _
        (scaledUniformTranslationSelf (E := E) hr_pos) δ (T i) K.carrier)).toReal ≤ p := by
    intro i hi
    have h_temp := prob_tube_translate_subset_le_toReal (E := E) (T i) K hr_pos
    calc
      ((@HasUniformTranslation.measure E _ E _ _ _ _ _
          (scaledUniformTranslationSelf (E := E) hr_pos) : Measure E)
        (@tubeContainedSet E _ E _ _ _ _ _
          (scaledUniformTranslationSelf (E := E) hr_pos) δ (T i) K.carrier)).toReal
          = (uniformBallMeasure E (scaledTubeContainedSet r (T i) K.carrier)).toReal := rfl
      _ = (uniformBallMeasure E
          {ω : E | ((T i).translate (r • ω)).carrier ⊆ K.carrier}).toReal := rfl
      _ ≤ (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) / r ^ (Module.finrank ℝ E - 1)
          * (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K.carrier
          := h_temp
      _ = p := by rw [hp]
  refine @productTubeContainedCount_chernoff_tail_of_prob E _ E _ _ _ _ _
    (scaledUniformTranslationSelf (E := E) hr_pos) ι δ s T K.carrier hMeas
    J _ M hM_pos hXM' p hprob' ?_ S
  simpa [hp] using hJmM

end ScaledTranslationCount

end Kakeya

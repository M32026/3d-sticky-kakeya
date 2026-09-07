module

/-
  NegationHelpers.lean

  Lemmas for unfolding the negation of HasMeasureThinTubes.

  Main result:
  `not_hasMeasureThinTubes` — if a pair does NOT have thin tubes
  (under the standard parameter assumptions), then every measurable
  set of measure ≥ 1-c admits a violating tube.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.HasMeasureThinTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

/-- Full negation of HasMeasureThinTubes with support conditions. -/
lemma not_hasMeasureThinTubes_full
    {β K c : ℝ}
    {ν₁ ν₂ : ProbabilityMeasure Point}
    (hβ : 0 ≤ β)
    (hK : 1 ≤ K)
    (hc : c ∈ Set.Ico (0 : ℝ) 1)
    (h : ¬ HasMeasureThinTubes β K c ν₁ ν₂) :
    ∀ (E : Set (Point × Point)),
      MeasurableSet E →
      E ⊆ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support →
      (ν₁.prod ν₂) E ≥ 1 - ENNReal.ofReal c →
      ∃ (x : Point) (hx : x ∈ (ν₁ : Measure Point).support)
        (ℓ : AffineSubspace ℝ Point) (hxl : x ∈ (ℓ : Set Point))
        (hfin : Module.finrank ℝ ℓ.direction = 1)
        (r : ℝ) (hr : 0 < r),
        ν₂ {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ E} >
          Real.toNNReal (K * r ^ β) := by
  simp only [HasMeasureThinTubes, hβ, hK, hc, true_and] at h
  push Not at h
  intro E hE_meas hE_support hE_measure
  have h' := h E hE_meas hE_support (by simpa using hE_measure)
  rcases h' with ⟨x, hx, ℓ, hxl, hfin, r, hr, hviol⟩
  refine' ⟨x, hx, ℓ, hxl, hfin, r, hr, _⟩
  simpa using hviol

/-- Simplified negation of HasMeasureThinTubes without support restrictions. -/
lemma not_hasMeasureThinTubes
    {β K c : ℝ}
    {ν₁ ν₂ : ProbabilityMeasure Point}
    (hβ : 0 ≤ β)
    (hK : 1 ≤ K)
    (hc : c ∈ Set.Ico (0 : ℝ) 1)
    (h : ¬ HasMeasureThinTubes β K c ν₁ ν₂) :
    ∀ (E : Set (Point × Point)),
      MeasurableSet E →
      (ν₁.prod ν₂) E ≥ 1 - ENNReal.ofReal c →
      ∃ (x : Point) (ℓ : AffineSubspace ℝ Point) (r : ℝ),
        x ∈ (ℓ : Set Point) ∧
        Module.finrank ℝ ℓ.direction = 1 ∧
        0 < r ∧
        ν₂ {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ E} >
          Real.toNNReal (K * r ^ β) := by
  let S := (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support
  let μ : Measure (Point × Point) := (ν₁.prod ν₂ : Measure (Point × Point))
  -- Supports are closed, hence measurable
  have hS1_closed : IsClosed ((ν₁ : Measure Point).support) :=
    MeasureTheory.Measure.isClosed_support (μ := (ν₁ : Measure Point))
  have hS2_closed : IsClosed ((ν₂ : Measure Point).support) :=
    MeasureTheory.Measure.isClosed_support (μ := (ν₂ : Measure Point))
  have hS_meas : MeasurableSet S :=
    hS1_closed.measurableSet.prod hS2_closed.measurableSet
  -- Complements of supports have measure zero
  have h1c : (ν₁ : Measure Point) ((ν₁ : Measure Point).supportᶜ) = 0 :=
    MeasureTheory.Measure.measure_compl_support (μ := (ν₁ : Measure Point))
  have h2c : (ν₂ : Measure Point) ((ν₂ : Measure Point).supportᶜ) = 0 :=
    MeasureTheory.Measure.measure_compl_support (μ := (ν₂ : Measure Point))
  -- Therefore S has full product measure (its complement has measure zero)
  have hS_full : μ Sᶜ = 0 :=
    MeasureTheory.Measure.measure_prod_compl_eq_zero h1c h2c
  let h_full := not_hasMeasureThinTubes_full hβ hK hc h
  intro E hE_meas hE_measure
  let E' := E ∩ S
  have hE'_meas : MeasurableSet E' := hE_meas.inter hS_meas
  have hE'_support : E' ⊆ S := Set.inter_subset_right
  -- E \ S is a subset of Sᶜ, hence has measure zero
  have h_diff_sub : E \ S ⊆ Sᶜ := by
    intro z hz
    exact hz.2
  have h_diff_null : μ (E \ S) = 0 :=
    measure_mono_null h_diff_sub hS_full
  have hE_diff_meas : MeasurableSet (E \ S) := hE_meas.diff hS_meas
  -- E = E' ∪ (E \ S), and E' and E \ S are disjoint
  have h_union : E = E' ∪ (E \ S) := by
    ext z
    simp only [E', Set.mem_union, Set.mem_diff, Set.mem_inter_iff] <;> tauto
  have h_disj : Disjoint E' (E \ S) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz2.2 hz1.2
  have h_eq : μ E' = μ E := by
    have h_add : μ (E' ∪ (E \ S)) = μ E' + μ (E \ S) :=
      measure_union h_disj hE_diff_meas
    have h1 : μ E' + μ (E \ S) = μ E' := by
      rw [h_diff_null] <;> simp
    have h2 : μ (E' ∪ (E \ S)) = μ E :=
      congr_arg μ h_union.symm
    rw [←h2, h_add, h1]
  -- Convert NNReal measure hypothesis to ENNReal
  have h_coe_E : μ E = ↑((ν₁.prod ν₂) E) := by
    exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν₁.prod ν₂) E)
  have hE_measure' : μ E ≥ 1 - ENNReal.ofReal c := by
    rw [h_coe_E]
    exact hE_measure
  have hE'_measure' : μ E' ≥ 1 - ENNReal.ofReal c := by
    rw [h_eq]
    exact hE_measure'
  -- Convert back to NNReal for h_full
  have h_coe_E' : μ E' = ↑((ν₁.prod ν₂) E') := by
    exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν₁.prod ν₂) E')
  have hE'_measure_nnreal : (ν₁.prod ν₂) E' ≥ 1 - ENNReal.ofReal c := by
    have h : μ E' ≥ 1 - ENNReal.ofReal c := hE'_measure'
    rw [h_coe_E'] at h
    exact h
  rcases h_full E' hE'_meas hE'_support hE'_measure_nnreal with
    ⟨x, _hx_support, ℓ, hxl, hfin, r, hr, hviol⟩
  refine' ⟨x, ℓ, r, hxl, hfin, hr, _⟩
  let A' := {b₂ : Point | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ E'}
  let A := {b₂ : Point | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ E}
  have h_sub : A' ⊆ A := by
    intro b₂ hb
    exact ⟨hb.1, hb.2.1⟩
  have h_mono_ennreal : (ν₂ : Measure Point) A' ≤ (ν₂ : Measure Point) A :=
    measure_mono h_sub
  have h_mono_nnreal : ν₂ A' ≤ ν₂ A := by
    have h_enn : (↑(ν₂ A') : ENNReal) ≤ (↑(ν₂ A) : ENNReal) := by
      have h1 : (↑(ν₂ A') : ENNReal) = (ν₂ : Measure Point) A' :=
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ A'
      have h2 : (↑(ν₂ A) : ENNReal) = (ν₂ : Measure Point) A :=
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ A
      rw [h1, h2]
      exact h_mono_ennreal
    have h_main : ν₂ A' ≤ ν₂ A := by
      by_contra h
      have h_lt : ν₂ A < ν₂ A' := lt_of_not_ge h
      have h_contra : (↑(ν₂ A) : ENNReal) < (↑(ν₂ A') : ENNReal) := by
        exact_mod_cast h_lt
      exact not_le.mpr h_contra h_enn
    exact h_main
  exact hviol.trans_le h_mono_nnreal

end RadialBootstrapping

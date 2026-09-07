import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Generic constant-multiplicity mass-volume bounds

Generalizes `constant_multiplicity_mass_volume` from `TubeShading` to any
`Shading BF`.  The proof is identical because all dependencies
(`coe_pointMultiplicity_eq_sum_indicator`, `lintegral_pointMultiplicity`,
`measurableSet_shading_union`) already work for arbitrary `BodyFamily`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
From constant multiplicity `[m, 2m]` on any shading, derive mass-volume inequalities:
`m * volume(Y.union) ≤ Y.mass` and `Y.mass ≤ 2 * m * volume(Y.union)`.
-/
lemma constant_multiplicity_mass_volume_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Y : Kakeya.Streamlined.Shading BF}
    {m : ℕ}
    (hcm : Y.HasConstantMultiplicity m (2 * m)) :
    (m : ENNReal) * MeasureTheory.volume Y.union ≤ Y.mass ∧
    Y.mass ≤ (2 * m : ENNReal) * MeasureTheory.volume Y.union := by
  have h1 : ∀ p ∈ Y.union, (m : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) := by
    intro p hp
    exact_mod_cast (hcm p hp).1
  have h2 : ∀ p ∈ Y.union, (Y.pointMultiplicity p : ENNReal) ≤ (2 * m : ENNReal) := by
    intro p hp
    exact_mod_cast (hcm p hp).2
  have h_zero_outside : ∀ p, p ∉ Y.union → (Y.pointMultiplicity p : ENNReal) = 0 := by
    intro p hp
    have h_i : ∀ (i : Fin BF.card), p ∉ Y.carrier i := by
      intro i h_in
      have h_in_union : p ∈ Y.union := by
        simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
        exact ⟨i, h_in⟩
      exact hp h_in_union
    have h_sum : (∑ i : Fin BF.card, (Y.carrier i).indicator (fun _ : Point3 => (1 : ENNReal)) p) = 0 := by
      classical
      apply Finset.sum_eq_zero
      intro i _
      have h_ind : (Y.carrier i).indicator (fun _ : Point3 => (1 : ENNReal)) p = 0 := by
        simp [Set.indicator_apply, h_i i]
      exact h_ind
    have h_eq2 : (Y.pointMultiplicity p : ENNReal) =
        ∑ i : Fin BF.card, (Y.carrier i).indicator (fun _ : Point3 => (1 : ENNReal)) p :=
      coe_pointMultiplicity_eq_sum_indicator Y p
    rw [h_eq2, h_sum]
  have h_eq : (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) = Y.mass :=
    lintegral_pointMultiplicity Y
  have h_indicator : ∀ p : Point3, (Y.pointMultiplicity p : ENNReal) =
      (Y.union).indicator (fun p : Point3 => (Y.pointMultiplicity p : ENNReal)) p := by
    intro p
    by_cases h : p ∈ Y.union
    · simp [h, Set.indicator_apply]
    · have hz : (Y.pointMultiplicity p : ENNReal) = 0 := h_zero_outside p h
      simp [h, hz, Set.indicator_apply]
  have h_set_eq : (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) =
      ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) := by
    rw [lintegral_congr h_indicator]
    rw [lintegral_indicator (measurableSet_shading_union Y)]
  have h3 : (m : ENNReal) * volume Y.union ≤ ∫⁻ p, (Y.pointMultiplicity p : ENNReal) := by
    rw [h_set_eq]
    have h5 : ∫⁻ p in Y.union, (m : ENNReal) ≤ ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) :=
      setLIntegral_mono' (measurableSet_shading_union Y) h1
    have h6 : ∫⁻ p in Y.union, (m : ENNReal) = (m : ENNReal) * volume Y.union := by
      rw [setLIntegral_const]
    rw [h6] at h5
    exact h5
  have h7 : ∫⁻ p, (Y.pointMultiplicity p : ENNReal) ≤ (2 * m : ENNReal) * volume Y.union := by
    rw [h_set_eq]
    have h5 : ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) ≤ ∫⁻ p in Y.union, (2 * m : ENNReal) :=
      setLIntegral_mono' (measurableSet_shading_union Y) h2
    have h6 : ∫⁻ p in Y.union, (2 * m : ENNReal) = (2 * m : ENNReal) * volume Y.union := by
      rw [setLIntegral_const]
    rw [h6] at h5
    exact h5
  rw [h_eq] at h3 h7
  exact ⟨h3, h7⟩

/--
Convert a union-volume comparison into an indexed-mass comparison for two
shadings in the same factor-two multiplicity band.  The body families may be
different: only the common multiplicity scale is used.
-/
lemma constant_multiplicity_mass_le_of_union_volume_le
    {BF₁ BF₂ : Kakeya.Streamlined.BodyFamily}
    {S : Kakeya.Streamlined.Shading BF₁}
    {T : Kakeya.Streamlined.Shading BF₂}
    {m : ℕ}
    (hS : S.HasConstantMultiplicity m (2 * m))
    (hT : T.HasConstantMultiplicity m (2 * m))
    (K : ENNReal)
    (hvolume : MeasureTheory.volume S.union ≤
      K * MeasureTheory.volume T.union) :
    S.mass ≤ 2 * K * T.mass := by
  have hSmass := (constant_multiplicity_mass_volume_generic hS).2
  have hTmass := (constant_multiplicity_mass_volume_generic hT).1
  calc
    S.mass ≤ (2 * m : ENNReal) * MeasureTheory.volume S.union := hSmass
    _ ≤ (2 * m : ENNReal) *
        (K * MeasureTheory.volume T.union) := by gcongr
    _ = 2 * K * ((m : ENNReal) * MeasureTheory.volume T.union) := by
      push_cast
      ring
    _ ≤ 2 * K * T.mass := by gcongr

/-- A finite coloring retains at least the reciprocal number of colors of an
`ENNReal` weight.  This version is deliberately independent of any geometric
carrier, so a caller can use the exact per-cell incidence mass as `weight`
without replacing it by union volume. -/
lemma finset_ennreal_weighted_fiber_retention
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    [Nonempty β]
    (indices : Finset α) (weight : α → ENNReal) (color : α → β) :
    ∃ target : β,
      (∑ index ∈ indices, weight index) ≤
        (Fintype.card β : ENNReal) *
          ∑ index ∈ indices.filter (fun index => color index = target),
            weight index := by
  let fiberWeight : β → ENNReal := fun target =>
    ∑ index ∈ indices.filter (fun index => color index = target),
      weight index
  have htargets : (Finset.univ : Finset β).Nonempty :=
    Finset.univ_nonempty
  rcases Finset.exists_max_image Finset.univ fiberWeight htargets with
    ⟨target, _htarget, hmax⟩
  have htotal :
      (∑ other : β, fiberWeight other) =
        ∑ index ∈ indices, weight index := by
    simpa [fiberWeight] using Finset.sum_fiberwise indices color weight
  refine ⟨target, ?_⟩
  rw [← htotal]
  calc
    (∑ other : β, fiberWeight other) ≤
        ∑ _other : β, fiberWeight target := by
      exact Finset.sum_le_sum fun other _ =>
        hmax other (Finset.mem_univ other)
    _ = (Fintype.card β : ENNReal) * fiberWeight target := by
      simp [Finset.sum_const]
    _ = (Fintype.card β : ENNReal) *
        ∑ index ∈ indices.filter (fun index => color index = target),
          weight index := rfl

end Kakeya.Assouad

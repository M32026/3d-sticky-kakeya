import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax

/-!
# Submultiplicativity and density control lemmas

Key lemmas for bounding Δ_max across factorings and subfamilies.

## Main results

- `subfamily_deltaMax_le`: Δ_max of a subfamily ≤ Δ_max of the whole family
- `fiber_containedMass_le`: fiber contained mass bounded by whole-family deltaMax

The full multi-scale submultiplicativity (paper `lemmasubmultD`) requires
geometric nesting between consecutive coarse scales and is not yet
formalized here.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace BodyFamily

/-- The contained mass of a subfamily is at most that of the whole family. -/
lemma subfamily_containedMass_le {F G : BodyFamily}
    {embed : Fin G.card → Fin F.card}
    (h_inj : Function.Injective embed)
    (h_carrier : ∀ i, (G.body i).carrier = (F.body (embed i)).carrier)
    (K : Set Point3) :
    G.containedMass K ≤ F.containedMass K := by
  classical
  let SG := G.containedIndices K
  let SF := F.containedIndices K
  have h_sub : Finset.image embed SG ⊆ SF := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have h_in : (G.body i).carrier ⊆ K :=
      (Finset.mem_filter.mp hi).2
    have h_F : (F.body (embed i)).carrier ⊆ K := by
      rw [←h_carrier i] <;> exact h_in
    simp only [SF, BodyFamily.containedIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact h_F
  have h_vol : ∀ i ∈ SG, (G.body i).volume = (F.body (embed i)).volume := by
    intro i _
    have h : (G.body i).carrier = (F.body (embed i)).carrier := h_carrier i
    simpa [Body.volume] using congr_arg volume h
  have h_inj_on : Set.InjOn embed (SG : Set (Fin G.card)) :=
    fun x _ y _ h => h_inj h
  have h_sum_eq : ∑ i ∈ SG, (F.body (embed i)).volume =
      ∑ x ∈ Finset.image embed SG, (F.body x).volume := by
    rw [Finset.sum_image h_inj_on]
  calc
    G.containedMass K = ∑ i ∈ SG, (G.body i).volume := by rfl
    _ = ∑ i ∈ SG, (F.body (embed i)).volume := by
      apply Finset.sum_congr rfl; intro i hi; exact h_vol i hi
    _ = ∑ x ∈ Finset.image embed SG, (F.body x).volume := h_sum_eq
    _ ≤ ∑ x ∈ SF, (F.body x).volume := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
      intro _ _ _; positivity
    _ = F.containedMass K := by rfl

/-- Δ_max of a subfamily is at most Δ_max of the whole family. -/
lemma subfamily_deltaMax_le {F G : BodyFamily}
    {embed : Fin G.card → Fin F.card}
    (h_inj : Function.Injective embed)
    (h_carrier : ∀ i, (G.body i).carrier = (F.body (embed i)).carrier) :
    G.deltaMax ≤ F.deltaMax := by
  have h1 : ∀ (K : Set Point3), Convex ℝ K → G.density K ≤ F.density K := by
    intro K hK
    have h2 : G.containedMass K ≤ F.containedMass K :=
      subfamily_containedMass_le h_inj h_carrier K
    dsimp only [BodyFamily.density]
    gcongr
  let SG : Set ENNReal :=
    {d | ∃ (K : Set Point3), Convex ℝ K ∧ d = G.density K}
  by_cases h_empty : Set.Nonempty SG
  · have h3 : ∀ d ∈ SG, d ≤ F.deltaMax := by
      rintro d ⟨K, hK, rfl⟩
      have h4 : G.density K ≤ F.density K := h1 K hK
      have h5 : F.density K ≤ F.deltaMax :=
        density_le_of_deltaMax_le (le_refl F.deltaMax) hK
      exact h4.trans h5
    exact csSup_le h_empty h3
  · have hSG_empty : SG = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h_empty
    have h_set_empty : {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = G.density K} = ∅ := by
      exact_mod_cast hSG_empty
    have h_deltaMax_empty : G.deltaMax = 0 := by
      dsimp only [BodyFamily.deltaMax]
      rw [h_set_empty]
      <;> simp
    rw [h_deltaMax_empty]
    positivity

end BodyFamily

namespace Factoring

/-- The contained mass of a fiber in K is at most the contained mass
of the whole fine family in K. -/
lemma fiberContainedMass_le_containedMass {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (j : Fin coarse.card) (K : Set Point3) :
    P.fiberContainedMass j K ≤ fine.containedMass K := by
  classical
  dsimp only [Factoring.fiberContainedMass, BodyFamily.containedMass,
    BodyFamily.containedIndices]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have h2 : (fine.body i).carrier ⊆ K :=
      (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h2
  · intro _ _ _; positivity

/-- Every fiber has contained mass bounded by fine.deltaMax * volume K.

Requires `0 < C` to handle the `volume K = ⊤` edge case. In applications
C is always positive (e.g. δ^(-η₁)). -/
lemma fiber_containedMass_le_deltaMax {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (j : Fin coarse.card)
    (C : ENNReal) (hC_pos : 0 < C) (h : fine.deltaMax ≤ C)
    (K : Set Point3) (hK : Convex ℝ K) :
    P.fiberContainedMass j K ≤ C * volume K := by
  classical
  have h1 : P.fiberContainedMass j K ≤ fine.containedMass K :=
    fiberContainedMass_le_containedMass P j K
  have h2 : fine.density K ≤ C :=
    BodyFamily.density_le_of_deltaMax_le h hK
  have hC_ne_zero : C ≠ 0 := hC_pos.ne'
  by_cases h5 : volume K = 0
  · -- volume K = 0: every contained body has volume 0, so mass is 0
    have h_contained_zero : fine.containedMass K = 0 := by
      have h : ∀ i ∈ fine.containedIndices K, (fine.body i).volume = 0 := by
        intro i hi
        have h_sub : (fine.body i).carrier ⊆ K :=
          (Finset.mem_filter.mp hi).2
        have h_vol : (fine.body i).volume ≤ volume K := measure_mono h_sub
        rw [h5] at h_vol
        simpa using h_vol
      dsimp only [BodyFamily.containedMass]
      rw [Finset.sum_eq_zero]
      exact h
    have h_fiber_zero : P.fiberContainedMass j K = 0 := by
      have h9 : P.fiberContainedMass j K ≤ fine.containedMass K := h1
      rw [h_contained_zero] at h9
      simpa using h9
    rw [h_fiber_zero]
    <;> simp [h5]
  · by_cases h6 : volume K = ⊤
    · -- volume K = ⊤ and C > 0, so C * volume K = ⊤
      rw [h6]
      have h7 : C * (⊤ : ENNReal) = ⊤ := by
        exact ENNReal.mul_top hC_ne_zero
      rw [h7]
      <;> exact le_top
    · -- volume K ≠ 0, ≠ ⊤: use div_le_iff
      have h4 : fine.density K = fine.containedMass K / volume K := by rfl
      rw [h4] at h2
      have h7 : fine.containedMass K / volume K ≤ C := h2
      have h8 : fine.containedMass K ≤ C * volume K :=
        (ENNReal.div_le_iff h5 h6).mp h7
      exact h1.trans h8

end Factoring

namespace TubeCover

/-- Every fiber of a tube cover has contained mass bounded by
fine.deltaMax * volume K. -/
lemma fiber_containedMass_le {δ ρ : ℝ} {fine : TubeFamily δ}
    {coarse : TubeFamily ρ} (P : TubeCover fine coarse)
    (j : Fin coarse.card) (C : ENNReal) (hC_pos : 0 < C)
    (h : fine.toBodyFamily.deltaMax ≤ C)
    (K : Set Point3) (hK : Convex ℝ K) :
    P.toFactoring.fiberContainedMass j K ≤ C * volume K :=
  Factoring.fiber_containedMass_le_deltaMax P.toFactoring j C hC_pos h K hK

end TubeCover

end Kakeya.Streamlined

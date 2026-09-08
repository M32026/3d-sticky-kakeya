import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.KStrongConflictBasic
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateUniformStructure
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConvexThickeningGrowth
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# K-strong conflict degree bound from deltaMax

For a tube family with bounded deltaMax, the K-strong conflict degree of each
tube is bounded by `(1000*K)^3 * deltaMax`.

The proof translates a conflicting pair so one midpoint is zero.  Overlap
then bounds the other midpoint, allowing the closed K-strong dilated
containment theorem to be applied without any global support assumption.
-/

open scoped Classical

noncomputable section

open MeasureTheory Metric SimpleGraph Finset
open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.WithShading

/-- K-strong conflict degree bound from `deltaMax`, with no support bound. -/
lemma k_strong_degree_from_deltaMax
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {T : TubeFamily δ} {C : ENNReal} (hC_ne_top : C ≠ ⊤)
    (hC : T.toBodyFamily.deltaMax ≤ C)
    (K : ℝ) (hK : 2 ≤ K) :
    ∀ v : Fin T.card,
      (kStrongConflictGraph T
        (Kakeya.deltaTubeVolume δ) (ENNReal.ofReal K)).degree v ≤
        Nat.ceil ((ENNReal.ofReal ((1000 * K) ^ 3) * C).toReal) := by
  classical
  let V := Kakeya.deltaTubeVolume δ
  let A : ℝ := 1000 * K
  have hA_pos : 0 < A := by positivity
  have hV_pos : 0 < V := by
    have h_lower : V ≥
        ENNReal.ofReal
          (Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      capsule_volume_lower δ hδ
    have h_pos :
        0 < Real.pi * δ ^ 2 +
          (4 / 3 : ℝ) * Real.pi * δ ^ 3 := by
      positivity
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr h_pos) h_lower
  have hV_ne_top : V ≠ ⊤ := by
    have h_upper : V ≤
        ENNReal.ofReal
          (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_upper
  have h_vol_eq : ∀ i, (T.tube i).volume = V := by
    intro i
    exact tube_volume_eq
      (T.tube i) ⟨0, EuclideanSpace.single 0 1, by simp⟩
  let Bound : ENNReal := ENNReal.ofReal (A ^ 3) * C
  have hBound_ne_top : Bound ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC_ne_top
  intro v
  let K_set : Set Point3 := dilatedTubeCarrier A (T.tube v)
  have hK_convex : Convex ℝ K_set :=
    GeometricLemmas.dilatedTubeCarrier_convex (T.tube v)
  have hK_vol : volume K_set = ENNReal.ofReal (A ^ 3) * V := by
    have h :=
      Kakeya.Streamlined.volume_dilatedTubeCarrier
        (A := A) hA_pos.ne' (T.tube v)
    simpa [abs_of_pos hA_pos, V] using h
  have hK_vol_pos : 0 < volume K_set := by
    rw [hK_vol]
    positivity
  have hK_vol_ne_top : volume K_set ≠ ⊤ := by
    rw [hK_vol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV_ne_top
  have h_density_le : T.toBodyFamily.density K_set ≤ C :=
    BodyFamily.density_le_of_deltaMax_le hC hK_convex
  have h_mass_le :
      T.toBodyFamily.containedMass K_set ≤ C * volume K_set := by
    have h_density_eq :
        T.toBodyFamily.density K_set =
          T.toBodyFamily.containedMass K_set / volume K_set := by
      rfl
    rw [h_density_eq] at h_density_le
    exact
      (ENNReal.div_le_iff hK_vol_pos.ne' hK_vol_ne_top).mp
        h_density_le
  let neighbors : Finset (Fin T.card) :=
    Finset.univ.filter fun w =>
      w ≠ v ∧
        volume ((T.tube w).carrier ∩ (T.tube v).carrier) >
          V / ENNReal.ofReal K
  have h_containment : ∀ w ∈ neighbors,
      (T.tube w).carrier ⊆ K_set := by
    intro w hw
    have h_overlap :
        volume ((T.tube w).carrier ∩ (T.tube v).carrier) >
          V / ENNReal.ofReal K :=
      (Finset.mem_filter.mp hw).2.2
    have h_vol_w : (T.tube w).volume = V := h_vol_eq w
    have h_overlap' :
        volume ((T.tube w).carrier ∩ (T.tube v).carrier) >
          (T.tube w).volume / ENNReal.ofReal K := by
      rw [h_vol_w]
      exact h_overlap
    exact
      strong_containment_via_translation hδ hδ1 hK h_overlap'
  have h_neighbors_subset :
      neighbors ⊆ T.toBodyFamily.containedIndices K_set := by
    intro w hw
    exact BodyFamily.mem_containedIndices_iff.mpr
      (h_containment w hw)
  have h_sum_vol :
      ∑ w ∈ neighbors, (T.tube w).volume =
        (neighbors.card : ENNReal) * V := by
    calc
      ∑ w ∈ neighbors, (T.tube w).volume =
          ∑ _w ∈ neighbors, V := by
        apply Finset.sum_congr rfl
        intro w _
        exact h_vol_eq w
      _ = (neighbors.card : ENNReal) * V := by
        simp [Finset.sum_const]
  have h_mass_bound :
      (neighbors.card : ENNReal) * V ≤
        T.toBodyFamily.containedMass K_set := by
    calc
      (neighbors.card : ENNReal) * V =
          ∑ w ∈ neighbors, (T.tube w).volume := h_sum_vol.symm
      _ ≤ ∑ w ∈ T.toBodyFamily.containedIndices K_set,
          (T.tube w).volume := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h_neighbors_subset
        intro _ _ _
        positivity
      _ = T.toBodyFamily.containedMass K_set := by
        rfl
  have h_main :
      (neighbors.card : ENNReal) * V ≤ C * volume K_set :=
    h_mass_bound.trans h_mass_le
  rw [hK_vol] at h_main
  have h_final :
      (neighbors.card : ENNReal) ≤ ENNReal.ofReal (A ^ 3) * C := by
    by_contra h
    have h2 :
        ENNReal.ofReal (A ^ 3) * C <
          (neighbors.card : ENNReal) :=
      lt_of_not_ge h
    have h3 :
        (ENNReal.ofReal (A ^ 3) * C) * V <
          (neighbors.card : ENNReal) * V :=
      ENNReal.mul_lt_mul_left hV_pos.ne' hV_ne_top h2
    have h4 :
        (ENNReal.ofReal (A ^ 3) * C) * V =
          C * (ENNReal.ofReal (A ^ 3) * V) := by
      ring
    rw [h4] at h3
    exact (not_lt_of_ge h_main) h3
  have h_neighborFinset_eq :
      (kStrongConflictGraph T V
        (ENNReal.ofReal K)).neighborFinset v = neighbors := by
    rw [SimpleGraph.neighborFinset_eq_filter]
    apply Finset.ext
    intro w
    simp only [neighbors, kStrongConflictGraph,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hov⟩
      exact ⟨hne.symm, by simpa [Set.inter_comm] using hov⟩
    · rintro ⟨hne, hov⟩
      exact ⟨hne.symm, by simpa [Set.inter_comm] using hov⟩
  have h_degree_eq :
      (kStrongConflictGraph T V
        (ENNReal.ofReal K)).degree v = neighbors.card := by
    have h_card :
        (kStrongConflictGraph T V
          (ENNReal.ofReal K)).degree v =
          ((kStrongConflictGraph T V
            (ENNReal.ofReal K)).neighborFinset v).card := by
      unfold SimpleGraph.degree
      rw [SimpleGraph.neighborFinset_def]
      <;> simp
    rw [h_card, h_neighborFinset_eq]
  rw [h_degree_eq]
  have h6 : (neighbors.card : ENNReal) ≤ Bound := by
    simpa [Bound] using h_final
  have h7 : (neighbors.card : ℝ) ≤ Bound.toReal := by
    have h8 : ENNReal.ofReal (neighbors.card : ℝ) ≤ Bound := by
      simpa [ENNReal.ofReal_natCast] using h6
    exact (ENNReal.ofReal_le_iff_le_toReal hBound_ne_top).mp h8
  have h9 :
      (neighbors.card : ℝ) ≤ (Nat.ceil Bound.toReal : ℝ) := by
    exact h7.trans (Nat.le_ceil Bound.toReal)
  exact_mod_cast h9

end Kakeya.Streamlined.WithShading

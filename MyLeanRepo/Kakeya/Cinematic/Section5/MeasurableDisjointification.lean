import MyLeanRepo.Kakeya.Cinematic.Section5.MeasurableDisjointificationInputs
import Mathlib.Order.Disjointed

/-!
# Finite measurable cover disjointification

Given a finite measurable cover of a measurable set, produce pairwise-disjoint
measurable pieces that exactly cover the original set and preserve its measure
for any measure.

Uses Mathlib's `disjointed` construction for index-order disjointification.
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem finite_measurable_disjointification :
    FiniteMeasurableDisjointificationStatement := by
  intro α _ N E cover hE hcover hsub
  let f : Fin N → Set α := fun i ↦ E ∩ cover i
  let piece : Fin N → Set α := disjointed f
  have hf_mble : ∀ i, MeasurableSet (f i) := by
    intro i
    exact hE.inter (hcover i)
  have hpiece_mble : ∀ i, MeasurableSet (piece i) := by
    intro i
    exact disjointedRec (p := MeasurableSet)
      (fun {t i} ht ↦ ht.diff (hf_mble i)) (hf_mble i)
  have hpiece_sub : ∀ i, piece i ⊆ E ∩ cover i := by
    intro i
    exact disjointed_le f i
  have hdisj_pairwise : Pairwise (Function.onFun Disjoint piece) :=
    disjoint_disjointed f
  have hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin N)) piece := by
    intro i _ j _ hne
    exact hdisj_pairwise hne
  have hunion : (⋃ i, piece i) = ⋃ i, f i := iUnion_disjointed
  have hfi_union : (⋃ i : Fin N, f i) = E ∩ (⋃ i : Fin N, cover i) := by
    have h : (⋃ i : Fin N, E ∩ cover i) = E ∩ (⋃ i : Fin N, cover i) :=
      (Set.inter_iUnion E cover).symm
    exact h
  have hE_eq : E = ⋃ i, piece i := by
    rw [hunion, hfi_union]
    rw [Set.inter_eq_left.mpr hsub]
  have hmeasure : ∀ (μ : Measure α), μ E = ∑ i : Fin N, μ (piece i) := by
    intro μ
    letI : Fintype (Fin N) := by infer_instance
    have hdisj' : ((Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint piece := by
      simpa using hdisj
    have h1 : μ (⋃ i ∈ (Finset.univ : Finset (Fin N)), piece i) =
        ∑ i ∈ (Finset.univ : Finset (Fin N)), μ (piece i) :=
      MeasureTheory.measure_biUnion_finset hdisj' (fun i _ ↦ hpiece_mble i)
    have h2 : (⋃ i ∈ (Finset.univ : Finset (Fin N)), piece i) = (⋃ i : Fin N, piece i) := by
      simp
    have h3 : (∑ i ∈ (Finset.univ : Finset (Fin N)), μ (piece i)) = ∑ i : Fin N, μ (piece i) := by
      simp
    rw [hE_eq]
    rw [h2, h3] at h1
    exact h1
  refine' ⟨piece, hpiece_mble, hdisj, hpiece_sub, hE_eq, hmeasure⟩

end Kakeya.Cinematic

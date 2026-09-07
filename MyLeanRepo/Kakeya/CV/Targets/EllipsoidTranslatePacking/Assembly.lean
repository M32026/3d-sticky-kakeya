import MyLeanRepo.Kakeya.CV.Targets.ManyBisections.AffineTools
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.Basic
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.VolumeScaling
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.HalfBallVolume
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.MaximalPacking
import MyLeanRepo.Kakeya.CV.Statements

/-!
# Assembly of the ellipsoid translate packing theorem

Assembles the final proof of `ellipsoid_translate_packing` from the
auxiliary lemmas in Basic, VolumeScaling, HalfBallVolume, and MaximalPacking.

## Proof outline

1. Obtain a maximal packing `S` via `exists_maximal_packing_max`.
2. Derive the covering property from maximality: doubled ellipsoids cover
   `closedBall 0 (1/2)`.
3. Let `n := S.card` and enumerate `S` as `z : Fin n → Point 3`.
4. Each ellipsoid is in the unit ball.
5. The ellipsoids are pairwise disjoint.
6. **Upper bound**: `n` disjoint ellipsoids of volume `V` inside the unit ball
   give `n * V ≤ volume(unitBall)`, hence `n ≤ volume(unitBall) / V`.
7. **Lower bound**: doubled ellipsoids cover `closedBall 0 (1/2)`, whose volume
   is `volume(unitBall) / 8`. Each doubled ellipsoid has volume `8 * V`.
   Subadditivity gives `volume(unitBall) / 8 ≤ n * 8 * V`, hence
   `volume(unitBall) / V ≤ 64 * n`.
8. Thus `C = 64` satisfies both required inequalities.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal BigOperators

namespace Kakeya.CV

/-- Covering property: doubled ellipsoids of a maximal packing cover the
closed half-ball. -/
lemma assembly_covering (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (hη : 0 < η)
    (S : Finset (Point 3))
    (hS_maximal : ∀ (x : Point 3), ‖x‖ ≤ 1 / 2 →
      (∀ z ∈ S, Disjoint (scaledEllipsoid A η x) (scaledEllipsoid A η z)) → x ∈ S) :
    Metric.closedBall (0 : Point 3) (1 / 2) ⊆ ⋃ z ∈ S, scaledEllipsoid A (2 * η) z := by
  intro x hx
  by_contra h_not
  have h1 : x ∉ ⋃ z ∈ S, scaledEllipsoid A (2 * η) z := h_not
  have h2 : ∀ (z : Point 3), z ∈ S → x ∉ scaledEllipsoid A (2 * η) z := by
    intro z hz
    intro h
    have h_in : x ∈ (⋃ z ∈ S, scaledEllipsoid A (2 * η) z) := by
      simpa [Finset.mem_biUnion] using ⟨z, hz, h⟩
    exact h1 h_in
  have h3 : ∀ (z : Point 3), z ∈ S → Disjoint (scaledEllipsoid A η x) (scaledEllipsoid A η z) := by
    intro z hz
    exact (disjointness_criterion A η hη x z).mpr (h2 z hz)
  have h4 : x ∈ S := hS_maximal x (by simpa [Metric.mem_closedBall] using hx) h3
  have h5 : x ∈ scaledEllipsoid A (2 * η) x := ellipsoid_mem_self A η hη x
  exact h2 x h4 h5

/-- Main assembly lemma. -/
lemma ellipsoid_translate_packing_main (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ)
    (hη : 0 < η) (hcontain : scaledEllipsoid A (2 * η) 0 ⊆ unitBall 3) :
    ∃ (n : ℕ) (z : Fin n → Point 3),
      (∀ i, scaledEllipsoid A η (z i) ⊆ unitBall 3) ∧
      Pairwise (fun i j => Disjoint (scaledEllipsoid A η (z i)) (scaledEllipsoid A η (z j))) ∧
      volume (unitBall 3) / volume (scaledEllipsoid A η 0) ≤ (64 : ℝ≥0∞) * (n : ℝ≥0∞) ∧
      (n : ℝ≥0∞) ≤ (64 : ℝ≥0∞) * volume (unitBall 3) / volume (scaledEllipsoid A η 0) := by
  set V : ℝ≥0∞ := volume (scaledEllipsoid A η 0) with hV_def
  have hV_pos : 0 < V := volume_scaledEllipsoid_pos A η hη 0
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hV_lt_top : V < ⊤ := by
    have h1 : scaledEllipsoid A η 0 ⊆ unitBall 3 :=
      center_containment A η hη 0 hcontain (by norm_num)
    have h2 : V ≤ volume (unitBall 3) := measure_mono h1
    exact h2.trans_lt volume_unitBall_lt_top
  have hV_ne_top : V ≠ ⊤ := hV_lt_top.ne
  rcases exists_maximal_packing_max A η hη hcontain with
    ⟨S, hS_centers, hS_inball, hS_disjoint, hS_maximal⟩
  have h_cover : Metric.closedBall (0 : Point 3) (1 / 2) ⊆ ⋃ z ∈ S, scaledEllipsoid A (2 * η) z :=
    assembly_covering A η hη S hS_maximal
  let n : ℕ := S.card
  let e : {z // z ∈ S} ≃ Fin n := Finset.equivFin S
  let z : Fin n → Point 3 := fun i => (e.symm i : Point 3)
  have hz_mem : ∀ i, z i ∈ S := by
    intro i
    exact (e.symm i).property
  have h1_containment : ∀ i, scaledEllipsoid A η (z i) ⊆ unitBall 3 := by
    intro i
    exact hS_inball (z i) (hz_mem i)
  have h1_disjoint : Pairwise (fun i j : Fin n =>
      Disjoint (scaledEllipsoid A η (z i)) (scaledEllipsoid A η (z j))) := by
    intro i j hne
    have h_ne_center : z i ≠ z j := by
      intro h
      have h' : (e.symm i : Point 3) = (e.symm j : Point 3) := h
      have h'' : e.symm i = e.symm j := Subtype.ext h'
      have h3 : i = j := by
        simpa [e] using congr_arg e h''
      exact hne h3
    have h_disj' : ∀ (x : Point 3), x ∈ S → ∀ (y : Point 3), y ∈ S → x ≠ y →
        Disjoint (scaledEllipsoid A η x) (scaledEllipsoid A η y) := by
      exact hS_disjoint
    exact h_disj' (z i) (hz_mem i) (z j) (hz_mem j) h_ne_center
  let f : Fin n → Set (Point 3) := fun i => scaledEllipsoid A η (z i)
  have h_meas : ∀ i, MeasurableSet (f i) := fun i =>
    measurableSet_scaledEllipsoid A η (z i)
  have h_disj : Pairwise (fun x y : Fin n => Disjoint (f x) (f y)) := by
    intro x y hne
    exact h1_disjoint hne
  have h_union_sub : (⋃ i, f i) ⊆ unitBall 3 := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hi⟩
    exact h1_containment i hi
  have h_eq : volume (⋃ i, f i) = ∑ i : Fin n, volume (f i) := by
    rw [MeasureTheory.measure_iUnion h_disj h_meas, tsum_fintype]
  have h_upper1 : (n : ℝ≥0∞) * V ≤ volume (unitBall 3) := by
    have h_union_vol : volume (⋃ i, f i) ≤ volume (unitBall 3) := measure_mono h_union_sub
    rw [h_eq] at h_union_vol
    have h4 : ∀ i, volume (f i) = V := by
      intro i
      exact volume_scaledEllipsoid_translate A η (z i)
    have h_sum : ∑ i : Fin n, volume (f i) = (n : ℝ≥0∞) * V := by
      rw [Finset.sum_congr rfl (fun x _ => h4 x)]
      simp [Finset.sum_const, Finset.card_fin]
    rw [h_sum] at h_union_vol
    exact h_union_vol
  have h_upper2 : (n : ℝ≥0∞) ≤ volume (unitBall 3) / V :=
    packing_upper_bound_div hV_ne_zero hV_ne_top h_upper1
  set B : ℝ≥0∞ := volume (unitBall 3) with hB_def
  have h_lower1 : (1 / 8 : ℝ≥0∞) * B ≤ (n : ℝ≥0∞) * (8 * V) := by
    have h_vol_cover : volume (Metric.closedBall (0 : Point 3) (1 / 2)) ≤
        volume (⋃ z ∈ S, scaledEllipsoid A (2 * η) z) :=
      measure_mono h_cover
    rw [volume_halfBall] at h_vol_cover
    have h_sub : volume (⋃ z ∈ S, scaledEllipsoid A (2 * η) z) ≤
        ∑ z ∈ S, volume (scaledEllipsoid A (2 * η) z) :=
      MeasureTheory.measure_biUnion_finset_le S (fun z => scaledEllipsoid A (2 * η) z)
    have h3 : ∀ z ∈ S, volume (scaledEllipsoid A (2 * η) z) = 8 * V := by
      intro z _
      have h4 : volume (scaledEllipsoid A η z) = V := volume_scaledEllipsoid_translate A η z
      rw [volume_scaledEllipsoid_double A η hη z, h4, hV_def]
    have h_sum2 : ∑ z ∈ S, volume (scaledEllipsoid A (2 * η) z) =
        (n : ℝ≥0∞) * (8 * V) := by
      rw [Finset.sum_congr rfl h3]
      simp [Finset.sum_const, n]
    calc (1 / 8 : ℝ≥0∞) * B
      ≤ volume (⋃ z ∈ S, scaledEllipsoid A (2 * η) z) := h_vol_cover
    _ ≤ ∑ z ∈ S, volume (scaledEllipsoid A (2 * η) z) := h_sub
    _ = (n : ℝ≥0∞) * (8 * V) := h_sum2
  have h_lower2 : B / V ≤ (64 : ℝ≥0∞) * (n : ℝ≥0∞) :=
    packing_lower_bound_div hV_ne_zero hV_ne_top volume_unitBall_lt_top.ne h_lower1
  have h10 : B ≤ (64 : ℝ≥0∞) * B := by
    have h11 : (1 : ℝ≥0∞) ≤ (64 : ℝ≥0∞) := by norm_num
    have h12 : 0 ≤ B := by positivity
    have h13 : (1 : ℝ≥0∞) * B ≤ (64 : ℝ≥0∞) * B := mul_le_mul_of_nonneg_right h11 h12
    simpa using h13
  have h_final_upper : (n : ℝ≥0∞) ≤ (64 : ℝ≥0∞) * B / V := by
    calc (n : ℝ≥0∞)
      ≤ B / V := h_upper2
    _ ≤ ((64 : ℝ≥0∞) * B) / V := by
      apply ENNReal.div_le_div h10
      <;> simp [hV_ne_zero]
  simpa [hB_def, hV_def] using ⟨n, z, h1_containment, h1_disjoint, h_lower2, h_final_upper⟩

end Kakeya.CV

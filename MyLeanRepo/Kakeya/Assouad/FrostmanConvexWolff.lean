import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Every-scale Frostman control implies the Convex-Wolff count

This is the finite-fiber summation used in WZ2 Section 6.  It keeps the
unit-scale tube volume explicit, matching `ConvexWolffBound`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

theorem frostman_to_convex_wolff
    (hvolume : TubeVolumeScalingStatement)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (C : ENNReal)
    (hFrost : U.IsFrostmanAtEveryScale C) :
    ConvexWolffBound F C := by
  classical
  rcases hvolume with ⟨h_equal_volume, h_volume_finite, _⟩
  have hVdelta := h_volume_finite delta hdelta_pos hdelta_le_one
  let oneScale : Kakeya.Streamlined.AdmissibleScale delta :=
    ⟨1, hdelta_le_one, le_rfl⟩
  let coarse := U.coarse oneScale
  let cover := U.cover oneScale
  let factoring := cover.toFactoring
  have hFrostOne := hFrost oneScale
  intro W hW_convex
  let K : Fin coarse.card → Set Point3 := fun j =>
    W ∩ (coarse.tube j).carrier
  have hK_convex : ∀ j, Convex ℝ (K j) := by
    intro j
    exact hW_convex.inter (by
      change Convex ℝ (Metric.cthickening 1
        (Kakeya.unitSegment (coarse.tube j).base
          (coarse.tube j).direction))
      apply Convex.cthickening
      intro x hx y hy a b ha hb hab
      rcases hx with ⟨s, hs, rfl⟩
      rcases hy with ⟨t, ht, rfl⟩
      refine ⟨a * s + b * t,
        (convex_Icc (0 : ℝ) 1) hs ht ha hb hab, ?_⟩
      simp only [Kakeya.unitSegment, Set.mem_image] at *
      have hbase :
          a • (coarse.tube j).base + b • (coarse.tube j).base =
            (coarse.tube j).base := by
        rw [← add_smul, hab, one_smul]
      rw [smul_add, smul_add, smul_smul, smul_smul]
      rw [show
        a • (coarse.tube j).base +
            (a * s) • (coarse.tube j).direction +
            (b • (coarse.tube j).base +
              (b * t) • (coarse.tube j).direction) =
          (a • (coarse.tube j).base + b • (coarse.tube j).base) +
            ((a * s) • (coarse.tube j).direction +
              (b * t) • (coarse.tube j).direction) by abel]
      rw [hbase, ← add_smul])
  have hK_sub : ∀ j, K j ⊆ (coarse.tube j).carrier := by
    intro j x hx
    exact hx.2
  have hFiber :
      ∀ j,
        factoring.fiberContainedMass j (K j) *
            (coarse.tube j).volume ≤
          C * factoring.fiberMass j * volume (K j) := by
    intro j
    exact hFrostOne j (K j) (hK_convex j) (hK_sub j)
  have hsum :
      ∑ j, factoring.fiberContainedMass j (K j) *
          (coarse.tube j).volume ≤
        C * ∑ j, factoring.fiberMass j * volume (K j) := by
    calc
      ∑ j, factoring.fiberContainedMass j (K j) *
          (coarse.tube j).volume
          ≤ ∑ j, C * (factoring.fiberMass j * volume (K j)) := by
            apply Finset.sum_le_sum
            intro j _
            simpa [mul_assoc] using hFiber j
      _ = C * ∑ j, factoring.fiberMass j * volume (K j) := by
            rw [Finset.mul_sum]
  have hcoarse_volume : ∀ j, (coarse.tube j).volume =
      Kakeya.deltaTubeVolume 1 := by
    intro j
    exact h_equal_volume 1 (coarse.tube j)
  have hlhs :
      ∑ j, factoring.fiberContainedMass j (K j) *
          (coarse.tube j).volume =
        Kakeya.deltaTubeVolume 1 *
          ∑ j, factoring.fiberContainedMass j (K j) := by
    calc
      ∑ j, factoring.fiberContainedMass j (K j) *
          (coarse.tube j).volume
          = ∑ j, Kakeya.deltaTubeVolume 1 *
              factoring.fiberContainedMass j (K j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hcoarse_volume j]
            exact mul_comm _ _
      _ = Kakeya.deltaTubeVolume 1 *
          ∑ j, factoring.fiberContainedMass j (K j) := by
            rw [Finset.mul_sum]
  have hfiber_filter :
      ∀ j,
        (factoring.fiberIndices j).filter
            (fun i => (F.tube i).carrier ⊆ K j) =
          (factoring.fiberIndices j).filter
            (fun i => (F.tube i).carrier ⊆ W) := by
    intro j
    apply Finset.filter_congr
    intro i hi
    have hparent : factoring.parent i = j :=
      (Finset.mem_filter.mp hi).2
    have hnested : (F.tube i).carrier ⊆
        (coarse.tube j).carrier := by
      have h := factoring.contained i
      rw [hparent] at h
      exact h
    constructor
    · intro h
      exact h.trans Set.inter_subset_left
    · intro h
      exact Set.subset_inter h hnested
  have hfibers_disjoint :
      ∀ j ∈ (Finset.univ : Finset (Fin coarse.card)),
        ∀ k ∈ (Finset.univ : Finset (Fin coarse.card)), j ≠ k →
          Disjoint (factoring.fiberIndices j)
            (factoring.fiberIndices k) := by
    intro j _ k _ hjk
    rw [Finset.disjoint_left]
    intro i hij hik
    have hj : factoring.parent i = j :=
      (Finset.mem_filter.mp hij).2
    have hk : factoring.parent i = k :=
      (Finset.mem_filter.mp hik).2
    exact hjk (hj.symm.trans hk)
  have hfibers_filtered_disjoint :
      ∀ j ∈ (Finset.univ : Finset (Fin coarse.card)),
        ∀ k ∈ (Finset.univ : Finset (Fin coarse.card)), j ≠ k →
          Disjoint
            ((factoring.fiberIndices j).filter
              (fun i => (F.tube i).carrier ⊆ W))
            ((factoring.fiberIndices k).filter
              (fun i => (F.tube i).carrier ⊆ W)) := by
    intro j hj k hk hjk
    exact Disjoint.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (hfibers_disjoint j hj k hk hjk)
  have hfiltered_union :
      Finset.biUnion Finset.univ (fun j =>
        (factoring.fiberIndices j).filter
          (fun i => (F.tube i).carrier ⊆ W)) =
        F.toBodyFamily.containedIndices W := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_biUnion.mp hi with ⟨j, _, hij⟩
      have hsub := (Finset.mem_filter.mp hij).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩
    · intro hi
      have hsub := (Finset.mem_filter.mp hi).2
      apply Finset.mem_biUnion.mpr
      refine ⟨factoring.parent i, Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, rfl⟩, hsub⟩
  have hcontained_mass :
      ∑ j, factoring.fiberContainedMass j (K j) =
        F.toBodyFamily.containedMass W := by
    simp only [Kakeya.Streamlined.Factoring.fiberContainedMass,
      Kakeya.Streamlined.BodyFamily.containedMass]
    calc
      ∑ j, ∑ i ∈ (factoring.fiberIndices j).filter
          (fun i => (F.tube i).carrier ⊆ K j),
          (F.tube i).volume
          = ∑ j, ∑ i ∈ (factoring.fiberIndices j).filter
              (fun i => (F.tube i).carrier ⊆ W),
              (F.tube i).volume := by
                apply Finset.sum_congr rfl
                intro j _
                rw [hfiber_filter j]
      _ = ∑ i ∈ Finset.biUnion Finset.univ (fun j =>
            (factoring.fiberIndices j).filter
              (fun i => (F.tube i).carrier ⊆ W)),
            (F.tube i).volume :=
              (Finset.sum_biUnion hfibers_filtered_disjoint).symm
      _ = ∑ i ∈ F.toBodyFamily.containedIndices W,
            (F.tube i).volume := by
              rw [hfiltered_union]
              rfl
  have hK_volume : ∀ j, volume (K j) ≤ volume W := by
    intro j
    exact measure_mono Set.inter_subset_left
  have hrhs :
      ∑ j, factoring.fiberMass j * volume (K j) ≤
        volume W * ∑ j, factoring.fiberMass j := by
    calc
      ∑ j, factoring.fiberMass j * volume (K j)
          ≤ ∑ j, factoring.fiberMass j * volume W := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_left' (hK_volume j) _
      _ = volume W * ∑ j, factoring.fiberMass j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            exact mul_comm _ _
  have hfiber_union :
      Finset.biUnion Finset.univ factoring.fiberIndices =
        (Finset.univ : Finset (Fin F.card)) := by
    ext i
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      apply Finset.mem_biUnion.mpr
      refine ⟨factoring.parent i, Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, rfl⟩
  have hfiber_mass :
      ∑ j, factoring.fiberMass j = F.toBodyFamily.mass := by
    simp only [Kakeya.Streamlined.Factoring.fiberMass,
      Kakeya.Streamlined.BodyFamily.mass]
    calc
      ∑ j, ∑ i ∈ factoring.fiberIndices j, (F.tube i).volume
          = ∑ i ∈ Finset.biUnion Finset.univ factoring.fiberIndices,
              (F.tube i).volume :=
            (Finset.sum_biUnion hfibers_disjoint).symm
      _ = ∑ i, (F.tube i).volume := by
            rw [hfiber_union]
            rfl
  have hmass_eq :
      F.toBodyFamily.mass =
        F.enncard * Kakeya.deltaTubeVolume delta := by
    calc
      F.toBodyFamily.mass = ∑ i, (F.tube i).volume := rfl
      _ = ∑ i, Kakeya.deltaTubeVolume delta := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_equal_volume delta (F.tube i)
      _ = F.enncard * Kakeya.deltaTubeVolume delta := by
        simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hcontained_eq :
      F.toBodyFamily.containedMass W =
        F.toBodyFamily.containedCount W *
          Kakeya.deltaTubeVolume delta := by
    simp only [Kakeya.Streamlined.BodyFamily.containedMass,
      Kakeya.Streamlined.BodyFamily.containedCount]
    calc
      ∑ i ∈ F.toBodyFamily.containedIndices W,
          (F.tube i).volume
          = ∑ i ∈ F.toBodyFamily.containedIndices W,
              Kakeya.deltaTubeVolume delta := by
                apply Finset.sum_congr rfl
                intro i _
                exact h_equal_volume delta (F.tube i)
      _ = (F.toBodyFamily.containedIndices W).card *
            Kakeya.deltaTubeVolume delta := by simp
  rw [hlhs, hcontained_mass, hcontained_eq] at hsum
  have hmain :
      Kakeya.deltaTubeVolume 1 *
          (F.toBodyFamily.containedCount W *
            Kakeya.deltaTubeVolume delta) ≤
        C * (volume W *
          (F.enncard * Kakeya.deltaTubeVolume delta)) := by
    calc
      Kakeya.deltaTubeVolume 1 *
          (F.toBodyFamily.containedCount W *
            Kakeya.deltaTubeVolume delta)
          ≤ C * ∑ j, factoring.fiberMass j * volume (K j) := hsum
      _ ≤ C * (volume W * ∑ j, factoring.fiberMass j) := by
            gcongr
      _ = C * (volume W *
          (F.enncard * Kakeya.deltaTubeVolume delta)) := by
            rw [hfiber_mass, hmass_eq]
  have hbound_with_factor :
      (F.toBodyFamily.containedCount W *
          Kakeya.deltaTubeVolume 1) *
          Kakeya.deltaTubeVolume delta ≤
        (C * volume W * F.enncard) *
          Kakeya.deltaTubeVolume delta := by
    calc
      (F.toBodyFamily.containedCount W *
          Kakeya.deltaTubeVolume 1) *
          Kakeya.deltaTubeVolume delta
          = Kakeya.deltaTubeVolume 1 *
              (F.toBodyFamily.containedCount W *
                Kakeya.deltaTubeVolume delta) := by ring
      _ ≤ C * (volume W *
          (F.enncard * Kakeya.deltaTubeVolume delta)) := hmain
      _ = (C * volume W * F.enncard) *
          Kakeya.deltaTubeVolume delta := by ring
  have hcancel := mul_le_mul_right' hbound_with_factor
    (Kakeya.deltaTubeVolume delta)⁻¹
  simpa [mul_assoc,
    ENNReal.mul_inv_cancel hVdelta.1.ne' hVdelta.2] using hcancel

end Kakeya.Assouad

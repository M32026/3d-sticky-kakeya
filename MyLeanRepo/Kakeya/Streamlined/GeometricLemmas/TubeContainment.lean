import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Tube containment from nearby midpoint and direction

This module records the geometric containment criterion used when assigning a
fine tube to a nearby coarse parameter cell.
-/

noncomputable section

open Metric

namespace Kakeya.Streamlined.GeometricLemmas

/-- The midpoint of the unit segment defining a tube. -/
def tubeMidpoint {δ : ℝ} (T : Kakeya.DeltaTube δ) : Point3 :=
  T.base + (1 / 2 : ℝ) • T.direction

private lemma isCompact_unitSegment {base direction : Point3} :
    IsCompact (Kakeya.unitSegment base direction) := by
  apply IsCompact.image
  · exact isCompact_Icc
  · exact continuous_const.add (continuous_id.smul continuous_const)

private lemma nonempty_unitSegment {base direction : Point3} :
    (Kakeya.unitSegment base direction).Nonempty := by
  exact ⟨base, ⟨0, by norm_num, by simp⟩⟩

/--
If the midpoint error plus half the direction error and the fine radius fit
inside the coarse radius, then the fine tube is contained in the coarse tube.
-/
lemma tube_contained_of_midpoint_direction_close
    {δ ρ : ℝ} (hδ : 0 ≤ δ)
    (fine : Kakeya.DeltaTube δ) (coarse : Kakeya.DeltaTube ρ)
    (hclose :
      ‖tubeMidpoint fine - tubeMidpoint coarse‖ +
          ‖fine.direction - coarse.direction‖ / 2 + δ ≤ ρ) :
    fine.carrier ⊆ coarse.carrier := by
  intro x hx
  have h_inf :
      Metric.infEDist x (Kakeya.unitSegment fine.base fine.direction) ≤
        ENNReal.ofReal δ := hx
  rcases (isCompact_unitSegment (base := fine.base) (direction := fine.direction)).exists_infEDist_eq_edist
      nonempty_unitSegment x with ⟨y, hy_segment, h_inf_eq⟩
  have hxy_edist : edist x y ≤ ENNReal.ofReal δ := by
    rw [← h_inf_eq]
    exact h_inf
  have hxy : dist x y ≤ δ := by
    rw [edist_dist] at hxy_edist
    exact (ENNReal.ofReal_le_ofReal_iff hδ).mp hxy_edist
  rcases hy_segment with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  let z : Point3 := coarse.base + t • coarse.direction
  have hz_segment : z ∈ Kakeya.unitSegment coarse.base coarse.direction :=
    ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hyz :
      dist (fine.base + t • fine.direction) z ≤
        ‖tubeMidpoint fine - tubeMidpoint coarse‖ +
          ‖fine.direction - coarse.direction‖ / 2 := by
    have hdiff :
        fine.base + t • fine.direction - z =
          (tubeMidpoint fine - tubeMidpoint coarse) +
            (t - 1 / 2 : ℝ) • (fine.direction - coarse.direction) := by
      simp only [z, tubeMidpoint]
      ext i
      simp [sub_smul, smul_sub]
      ring
    rw [dist_eq_norm, hdiff]
    calc
      ‖(tubeMidpoint fine - tubeMidpoint coarse) +
          (t - 1 / 2 : ℝ) • (fine.direction - coarse.direction)‖
          ≤ ‖tubeMidpoint fine - tubeMidpoint coarse‖ +
              ‖(t - 1 / 2 : ℝ) • (fine.direction - coarse.direction)‖ :=
        norm_add_le _ _
      _ = ‖tubeMidpoint fine - tubeMidpoint coarse‖ +
            |t - 1 / 2| * ‖fine.direction - coarse.direction‖ := by
        rw [norm_smul]
        rfl
      _ ≤ ‖tubeMidpoint fine - tubeMidpoint coarse‖ +
            (1 / 2 : ℝ) * ‖fine.direction - coarse.direction‖ := by
        gcongr
        rw [abs_le]
        constructor <;> linarith
      _ = ‖tubeMidpoint fine - tubeMidpoint coarse‖ +
            ‖fine.direction - coarse.direction‖ / 2 := by ring
  have hxz : dist x z ≤ ρ := by
    calc
      dist x z ≤ dist x (fine.base + t • fine.direction) +
          dist (fine.base + t • fine.direction) z :=
        dist_triangle _ _ _
      _ ≤ δ + (‖tubeMidpoint fine - tubeMidpoint coarse‖ +
          ‖fine.direction - coarse.direction‖ / 2) := by gcongr
      _ ≤ ρ := by linarith [hclose]
  exact Metric.mem_cthickening_of_dist_le x z ρ
    (Kakeya.unitSegment coarse.base coarse.direction) hz_segment hxz

end Kakeya.Streamlined.GeometricLemmas

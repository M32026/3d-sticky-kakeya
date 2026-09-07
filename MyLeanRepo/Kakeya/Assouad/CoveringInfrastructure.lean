import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoveringNumberBridge
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Finite witnesses for external covering numbers

Mathlib defines the external covering number as an `ENat` infimum.  These
lemmas expose a finite minimizing cover and convert it to the `Finset` witness
used by `CanCoverByBalls`.
-/

noncomputable section

open Metric

namespace Kakeya.Assouad

/--
An external covering-number bound by a finite `ENNReal` constant produces the
finite set of closed-ball centers required by `CanCoverByBalls`.
-/
lemma canCoverByBalls_of_externalCoveringNumber_le
    (E : Set Point3) (radius : ℝ) (hradius : 0 ≤ radius)
    (N : ENNReal) (hN : N ≠ ⊤)
    (hcovering :
      (↑(Metric.externalCoveringNumber ⟨radius, hradius⟩ E) : ENNReal) ≤ N) :
    CanCoverByBalls E radius N := by
  classical
  have hfinite :
      Metric.externalCoveringNumber ⟨radius, hradius⟩ E ≠ ⊤ := by
    intro htop
    rw [htop] at hcovering
    exact hN (top_le_iff.mp hcovering)
  obtain ⟨centers, hcenters_finite, hcenters_cover, hcenters_card⟩ :=
    exists_set_encard_eq_externalCoveringNumber hfinite
  let centersFinset : Finset Point3 := hcenters_finite.toFinset
  refine ⟨centersFinset, ?_, ?_⟩
  · have hcard_enat :
        (↑centersFinset.card : ℕ∞) =
          Metric.externalCoveringNumber ⟨radius, hradius⟩ E := by
      calc
        (↑centersFinset.card : ℕ∞)
            = centers.encard := by
                simpa [centersFinset] using
                  hcenters_finite.encard_eq_coe_toFinset_card.symm
        _ = Metric.externalCoveringNumber
            ⟨radius, hradius⟩ E := hcenters_card
    have hcard :
        (centersFinset.card : ENNReal) =
          (↑(Metric.externalCoveringNumber
            ⟨radius, hradius⟩ E) : ENNReal) := by
      exact_mod_cast hcard_enat
    rw [hcard]
    exact hcovering
  · intro y hy
    have hy_cover := hcenters_cover.subset_iUnion_closedBall hy
    simp only [Set.mem_iUnion] at hy_cover
    obtain ⟨x, hx_centers, hy_ball⟩ := hy_cover
    refine ⟨x, ?_, ?_⟩
    · have hx_set : x ∈ (centersFinset : Set Point3) := by
        simpa [centersFinset, hcenters_finite.coe_toFinset] using hx_centers
      exact hx_set
    · have hy_dist : dist y x ≤ radius := by
        exact_mod_cast hy_ball
      simpa [Metric.mem_closedBall] using hy_dist

/--
A cover by at most `N` balls of radius `r` has volume at most
`N * 8 r^3`.  The constant eight is a convenient rational upper bound for
the exact three-dimensional ball-volume constant.
-/
lemma CanCoverByBalls.volume_le
    {E : Set Point3} {radius : ℝ} {N : ENNReal}
    (hradius : 0 ≤ radius)
    (hcover : CanCoverByBalls E radius N) :
    MeasureTheory.volume E ≤
      N * ENNReal.ofReal (8 * radius ^ 3) := by
  rcases hcover with ⟨centers, hcard, hcenters⟩
  have hsubset :
      E ⊆ ⋃ x ∈ centers, Metric.closedBall x radius := by
    intro y hy
    rcases hcenters y hy with ⟨x, hx, hyx⟩
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hyx⟩
  have hsum :
      MeasureTheory.volume E ≤
        ∑ x ∈ centers,
          MeasureTheory.volume (Metric.closedBall x radius) := by
    exact (MeasureTheory.measure_mono hsubset).trans
      (MeasureTheory.measure_biUnion_finset_le centers
        (fun x => Metric.closedBall x radius))
  have hball :
      ∀ x : Point3,
        MeasureTheory.volume (Metric.closedBall x radius) ≤
          ENNReal.ofReal (8 * radius ^ 3) := by
    intro x
    rw [EuclideanSpace.volume_closedBall_fin_three]
    rw [← ENNReal.ofReal_pow hradius 3]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ radius ^ 3)]
    apply ENNReal.ofReal_mono
    have hpi : Real.pi * 4 / 3 ≤ 8 := by
      linarith [Real.pi_lt_four]
    have hradius_cube : 0 ≤ radius ^ 3 := by positivity
    nlinarith
  calc
    MeasureTheory.volume E
        ≤ ∑ x ∈ centers,
          MeasureTheory.volume (Metric.closedBall x radius) := hsum
    _ ≤ ∑ _x ∈ centers, ENNReal.ofReal (8 * radius ^ 3) := by
          exact Finset.sum_le_sum fun x _ => hball x
    _ = (centers.card : ENNReal) *
        ENNReal.ofReal (8 * radius ^ 3) := by simp
    _ ≤ N * ENNReal.ofReal (8 * radius ^ 3) := by
          exact mul_le_mul_right' hcard _

end Kakeya.Assouad

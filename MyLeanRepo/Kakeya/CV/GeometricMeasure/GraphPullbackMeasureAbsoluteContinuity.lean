import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphPullbackMeasure
import MyLeanRepo.Kakeya.CV.GeometricMeasure.AffineGraphArea
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Absolute continuity of the graph pullback measure

For a globally C¹ function `g : R² → R`, the pullback of ambient Hausdorff
2-measure along the graph embedding is absolutely continuous with respect to
Lebesgue measure on R².

## Proof

Use a σ-compact exhaustion of R² by closed balls. On each compact ball, the
graph map is Lipschitz (since it is globally C¹, hence locally Lipschitz).
If `E` has Lebesgue measure zero, then on each compact `K_n`:

`μH[2](graphMap g '' (E ∩ K_n)) ≤ C_n² · μH[2](E ∩ K_n) = C_n² · planeConstant · volume(E ∩ K_n) = 0`

Summing over the countable exhaustion gives `graphPullbackMeasure g E = 0`.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- The graph pullback measure of a globally C¹ function is absolutely
continuous with respect to planar Lebesgue measure. -/
lemma graphPullbackMeasure_absolutelyContinuous
    (g : R2 → ℝ) (hg : ContDiff ℝ 1 g) :
    graphPullbackMeasure g ≪ volume := by
  have hgraph : ContDiff ℝ 1 (graphMap g) := graphMap_contDiff hg
  have hlocal : LocallyLipschitz (graphMap g) := hgraph.locallyLipschitz
  let K : ℕ → Set R2 := fun n => closedBall 0 ((n : ℝ) + 1)
  have hK_compact : ∀ n, IsCompact (K n) := by
    intro n
    dsimp only [K]
    exact isCompact_closedBall _ _
  have hK_cover : (⋃ n, K n) = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (dist y 0)
    have h5 : dist y 0 ≤ (n : ℝ) + 1 := by
      have h6 : dist y 0 ≤ (n : ℝ) := hn
      linarith
    exact ⟨n, h5⟩
  have h_lip_on_compact :
      ∀ n, ∃ C : NNReal, LipschitzOnWith C (graphMap g) (K n) := by
    intro n
    have h_ll : LocallyLipschitzOn (K n) (graphMap g) :=
      hlocal.locallyLipschitzOn
    exact h_ll.exists_lipschitzOnWith_of_compact (hK_compact n)
  choose C hC using h_lip_on_compact
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hvol
  have hE_cover : E ⊆ ⋃ n, E ∩ K n := by
    intro y hy
    have h_y_univ : y ∈ ⋃ n, K n := by
      rw [hK_cover]
      trivial
    rcases Set.mem_iUnion.mp h_y_univ with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨hy, hn⟩⟩
  have h1 :
      graphPullbackMeasure g E ≤
        ∑' n, graphPullbackMeasure g (E ∩ K n) := by
    calc
      graphPullbackMeasure g E
          ≤ graphPullbackMeasure g (⋃ n, E ∩ K n) :=
        measure_mono hE_cover
      _ ≤ ∑' n, graphPullbackMeasure g (E ∩ K n) :=
        measure_iUnion_le _
  have h4 : ∀ n, graphPullbackMeasure g (E ∩ K n) = 0 := by
    intro n
    have hK_meas : MeasurableSet (K n) := (hK_compact n).measurableSet
    have hLip : LipschitzOnWith (C n) (graphMap g) (K n) := hC n
    have h_sub : E ∩ K n ⊆ K n := Set.inter_subset_right
    have hLip' : LipschitzOnWith (C n) (graphMap g) (E ∩ K n) :=
      hLip.mono h_sub
    rw [graphPullbackMeasure_apply hg.continuous (hE.inter hK_meas)]
    have h5 :
        μH[2] (graphMap g '' (E ∩ K n)) ≤
          (C n : ENNReal) ^ (2 : ℝ) * μH[2] (E ∩ K n) :=
      hLip'.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
    have h6 : volume (E ∩ K n) = 0 :=
      measure_mono_null Set.inter_subset_left hvol
    have h7 : μH[2] (E ∩ K n) = 0 := by
      rw [μH2_eq (E ∩ K n), h6]
      ring
    rw [h7] at h5
    simpa using h5
  have h5 : ∑' n, graphPullbackMeasure g (E ∩ K n) = 0 := by
    rw [tsum_congr h4]
    simp
  have h6 : graphPullbackMeasure g E = 0 := by
    rw [h5] at h1
    simpa using h1
  exact h6

end Kakeya.CV

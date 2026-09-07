import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# AD-set thickening volume bound

Converts a finite ball cover of a set into a volume bound for its thickening.
-/

noncomputable section

namespace Kakeya.Assouad

open Set Metric MeasureTheory

/-- The ρ-thickening of a ρ-ball is contained in the 2ρ-ball. -/
lemma cthickening_closedBall_double {X : Type _} [PseudoMetricSpace X] {c : X} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    cthickening ρ (closedBall c ρ) ⊆ closedBall c (2 * ρ) := by
  have h_main : ∀ (ε : ℝ), 0 < ε → cthickening ρ (closedBall c ρ) ⊆ closedBall c (2 * ρ + ε) := by
    intro ε hε
    have hpos : 0 < ρ + ε := by linarith
    have hlt : ρ < ρ + ε := by linarith
    have h1 : cthickening ρ (closedBall c ρ) ⊆ ⋃ x ∈ closedBall c ρ, closedBall x (ρ + ε) :=
      cthickening_subset_iUnion_closedBall_of_lt (closedBall c ρ) (hδ₀ := hpos) (hδδ' := hlt)
    have h2 : (⋃ x ∈ closedBall c ρ, closedBall x (ρ + ε)) ⊆ closedBall c (2 * ρ + ε) := by
      intro y hy
      rcases mem_iUnion₂.mp hy with ⟨x, hx, hy2⟩
      have h3 : dist y x ≤ ρ + ε := by simpa [closedBall] using hy2
      have h4 : dist x c ≤ ρ := by simpa [closedBall] using hx
      have h5 : dist y c ≤ dist y x + dist x c := dist_triangle y x c
      have h6 : dist y c ≤ 2 * ρ + ε := by linarith
      simpa [closedBall] using h6
    exact h1.trans h2
  intro y hy
  have h_all : ∀ (ε : ℝ), 0 < ε → y ∈ closedBall c (2 * ρ + ε) := by
    intro ε hε
    exact h_main ε hε hy
  have h7 : dist y c ≤ 2 * ρ := by
    by_contra h
    have h8 : dist y c > 2 * ρ := by linarith
    set ε : ℝ := (dist y c - 2 * ρ) / 2 with hε_def
    have hε_pos : 0 < ε := by linarith
    have h9 : y ∈ closedBall c (2 * ρ + ε) := h_all ε hε_pos
    have h10 : dist y c ≤ 2 * ρ + ε := by simpa [closedBall] using h9
    linarith
  simpa [closedBall] using h7

/-- cthickening of a finite union of balls is contained in the union of double-radius balls. -/
lemma cthickening_finite_balls_double {X : Type _} [PseudoMetricSpace X] [DecidableEq X]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (centers : Finset X) :
    cthickening ρ (⋃ c ∈ centers, closedBall c ρ) ⊆
      ⋃ c ∈ centers, closedBall c (2 * ρ) := by
  induction centers using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    have h1 : (⋃ c ∈ (insert a s), closedBall c ρ) =
        closedBall a ρ ∪ (⋃ c ∈ s, closedBall c ρ) := by
      ext x; simp [ha, Finset.mem_insert]
    rw [h1]
    rw [cthickening_union ρ (closedBall a ρ) (⋃ c ∈ s, closedBall c ρ)]
    have h2 : cthickening ρ (closedBall a ρ) ⊆ closedBall a (2 * ρ) :=
      cthickening_closedBall_double hρ
    have h3 : cthickening ρ (⋃ c ∈ s, closedBall c ρ) ⊆ ⋃ c ∈ s, closedBall c (2 * ρ) := ih
    have h4 : cthickening ρ (closedBall a ρ) ∪ cthickening ρ (⋃ c ∈ s, closedBall c ρ) ⊆
        closedBall a (2 * ρ) ∪ (⋃ c ∈ s, closedBall c (2 * ρ)) := by
      exact union_subset_union h2 h3
    have h5 : closedBall a (2 * ρ) ∪ (⋃ c ∈ s, closedBall c (2 * ρ)) =
        ⋃ c ∈ (insert a s), closedBall c (2 * ρ) := by
      ext x; simp [ha, Finset.mem_insert]
    exact h4.trans h5.subset

/--
If a set E in ℝ² is covered by a finite family of ρ-balls, then the
ρ-thickening of E has volume at most the number of balls times the volume
of a 2ρ-ball.
-/
lemma volume_cthickening_le_finite_cover
    {E : Set Point2} {ρ : ℝ} {centers : Finset Point2}
    (hρ : 0 ≤ ρ) (hcover : E ⊆ ⋃ c ∈ centers, closedBall c ρ) :
    volume (cthickening ρ E) ≤
      (centers.card : ENNReal) * volume (closedBall (0 : Point2) (2 * ρ)) := by
  have h1 : cthickening ρ E ⊆ cthickening ρ (⋃ c ∈ centers, closedBall c ρ) :=
    cthickening_subset_of_subset ρ hcover
  have h2 : cthickening ρ (⋃ c ∈ centers, closedBall c ρ) ⊆
      ⋃ c ∈ centers, closedBall c (2 * ρ) :=
    cthickening_finite_balls_double hρ centers
  have h5 : cthickening ρ E ⊆ ⋃ c ∈ centers, closedBall c (2 * ρ) :=
    h1.trans h2
  have h6 : volume (cthickening ρ E) ≤ volume (⋃ c ∈ centers, closedBall c (2 * ρ)) :=
    measure_mono h5
  have h7 : volume (⋃ c ∈ centers, closedBall c (2 * ρ)) ≤
      ∑ c ∈ centers, volume (closedBall c (2 * ρ)) :=
    measure_biUnion_finset_le centers (fun c => closedBall c (2 * ρ))
  have h9 : ∀ c : Point2, volume (closedBall c (2 * ρ)) = volume (closedBall (0 : Point2) (2 * ρ)) := by
    intro c
    have h10 : volume (closedBall c (2 * ρ)) =
        ENNReal.ofReal (2 * ρ) ^ 2 * ENNReal.ofReal Real.pi :=
      EuclideanSpace.volume_closedBall_fin_two c (2 * ρ)
    have h11 : volume (closedBall (0 : Point2) (2 * ρ)) =
        ENNReal.ofReal (2 * ρ) ^ 2 * ENNReal.ofReal Real.pi :=
      EuclideanSpace.volume_closedBall_fin_two 0 (2 * ρ)
    rw [h10, h11]
  have h12 : ∑ c ∈ centers, volume (closedBall c (2 * ρ)) =
      (centers.card : ENNReal) * volume (closedBall (0 : Point2) (2 * ρ)) := by
    have h13 : ∑ c ∈ centers, volume (closedBall c (2 * ρ)) =
        ∑ c ∈ centers, volume (closedBall (0 : Point2) (2 * ρ)) := by
      apply Finset.sum_congr rfl
      intro c _
      exact h9 c
    rw [h13]
    simp [Finset.sum_const]
    <;> ring
  rw [h12] at h7
  exact le_trans h6 h7

end Kakeya.Assouad

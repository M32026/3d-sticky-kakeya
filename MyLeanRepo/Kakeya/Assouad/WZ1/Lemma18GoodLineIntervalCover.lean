import MyLeanRepo.Kakeya.Assouad.WZ1.NestedFullGrainGoodLineStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers

/-!
# Self-centered interval cover for the WZ1 Lemma 18 good line

The good-line argument must feed Lemma 17 at actual shaded line points.
Arbitrary grid centers are therefore insufficient.  This module first
replaces every occupied half-radius grid ball by one point of the supplied
set, and then specializes the result to parameters of the selected line.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
A subset of one real ball admits a cover by balls centered in the subset.

The half-radius grid has at most `ceil (4 * radius / targetRadius) + 1`
members. Replacing every occupied grid center by a point of the set doubles
the covering radius to `targetRadius`.
-/
lemma real_subset_self_centered_cover
    {source : Set ℝ} {center radius targetRadius : ℝ}
    (htarget : 0 < targetRadius)
    (hradius : 0 < radius)
    (hsource : source ⊆ closedBall center radius) :
    ∃ selected : Finset ℝ,
      (selected : Set ℝ) ⊆ source ∧
      (selected.card : ENNReal) ≤
        (Nat.ceil (4 * radius / targetRadius) + 1 : ENNReal) ∧
      source ⊆
        ⋃ selectedCenter ∈ selected,
          closedBall selectedCenter targetRadius := by
  let halfRadius := targetRadius / 2
  have hhalf : 0 < halfRadius := by
    dsimp only [halfRadius]
    positivity
  by_cases hsmall : radius < halfRadius
  · by_cases hsourceEmpty : source = ∅
    · refine ⟨∅, ?_, by simp, ?_⟩
      · simp [hsourceEmpty]
      · simp [hsourceEmpty]
    · rcases Set.nonempty_iff_ne_empty.mpr hsourceEmpty with
        ⟨selectedCenter, hselectedCenter⟩
      refine ⟨{selectedCenter}, by simpa, ?_, ?_⟩
      · have hboundNonneg :
            (0 : ℝ) ≤ 4 * radius / targetRadius := by
          positivity
        have hceilNonneg :
            0 ≤ Nat.ceil (4 * radius / targetRadius) :=
          Nat.zero_le _
        simp only [Finset.card_singleton, Nat.cast_one]
        norm_cast
        omega
      · intro point hpoint
        have hpointBall := hsource hpoint
        have hcenterBall := hsource hselectedCenter
        have hdistance :
            dist point selectedCenter < targetRadius := by
          have hpointDistance :
              dist point center ≤ radius :=
            hpointBall
          have hselectedDistance :
              dist center selectedCenter ≤ radius := by
            simpa [dist_comm] using hcenterBall
          calc
            dist point selectedCenter ≤
                dist point center + dist center selectedCenter :=
              dist_triangle _ _ _
            _ ≤ radius + radius :=
              add_le_add hpointDistance hselectedDistance
            _ < targetRadius := by
              dsimp only [halfRadius] at hsmall
              linarith
        exact Set.mem_iUnion₂.mpr
          ⟨selectedCenter, by simp,
            Metric.mem_closedBall.mpr hdistance.le⟩
  · have hhalfLe : halfRadius ≤ radius := le_of_not_gt hsmall
    rcases
        real_closedBall_finer_cover
          center hhalf hradius hhalfLe with
      ⟨grid, hgridCard, hgridCover⟩
    let occupied : Finset ℝ :=
      grid.filter fun gridCenter =>
        (source ∩ closedBall gridCenter halfRadius).Nonempty
    let representative : ℝ → ℝ := fun gridCenter =>
      if hoccupied : gridCenter ∈ occupied then
        Classical.choose
          ((Finset.mem_filter.mp hoccupied).2)
      else 0
    let selected : Finset ℝ :=
      occupied.image representative
    have hrepresentative :
        ∀ gridCenter, gridCenter ∈ occupied →
          representative gridCenter ∈
            source ∩ closedBall gridCenter halfRadius := by
      intro gridCenter hoccupied
      dsimp only [representative]
      rw [dif_pos hoccupied]
      exact
        Classical.choose_spec
          ((Finset.mem_filter.mp hoccupied).2)
    have hselectedSource :
        (selected : Set ℝ) ⊆ source := by
      intro point hpoint
      rcases Finset.mem_image.mp hpoint with
        ⟨gridCenter, hoccupied, rfl⟩
      exact (hrepresentative gridCenter hoccupied).1
    have hselectedCard :
        selected.card ≤ grid.card := by
      calc
        selected.card ≤ occupied.card :=
          Finset.card_image_le
        _ ≤ grid.card :=
          Finset.card_filter_le _ _
    have hgridCardReal :
        (grid.card : ENNReal) ≤
          (Nat.ceil (4 * radius / targetRadius) + 1 : ENNReal) := by
      have hratio :
          2 * radius / halfRadius =
            4 * radius / targetRadius := by
        dsimp only [halfRadius]
        field_simp [htarget.ne']
        ring
      simpa [hratio] using hgridCard
    have hselectedGridENN :
        (selected.card : ENNReal) ≤ (grid.card : ENNReal) := by
      exact_mod_cast hselectedCard
    have hselectedCardENN :
        (selected.card : ENNReal) ≤
          (Nat.ceil (4 * radius / targetRadius) + 1 : ENNReal) :=
      hselectedGridENN.trans hgridCardReal
    refine
      ⟨selected, hselectedSource, hselectedCardENN, ?_⟩
    intro point hpoint
    have hpointGrid :
        point ∈
          ⋃ gridCenter ∈ grid,
            closedBall gridCenter halfRadius :=
      hgridCover (hsource hpoint)
    rcases Set.mem_iUnion₂.mp hpointGrid with
      ⟨gridCenter, hgridCenter, hpointBall⟩
    have hoccupied :
        gridCenter ∈ occupied := by
      exact Finset.mem_filter.mpr
        ⟨hgridCenter, ⟨point, hpoint, hpointBall⟩⟩
    have hrepresentativeBall :=
      (hrepresentative gridCenter hoccupied).2
    have hpointDistance :
        dist point gridCenter ≤ halfRadius :=
      hpointBall
    have hrepresentativeDistance :
        dist gridCenter (representative gridCenter) ≤ halfRadius := by
      calc
        dist gridCenter (representative gridCenter) =
            dist (representative gridCenter) gridCenter :=
          dist_comm _ _
        _ ≤ halfRadius :=
          Metric.mem_closedBall.mp hrepresentativeBall
    have hdistance :
        dist point (representative gridCenter) ≤ targetRadius := by
      calc
        dist point (representative gridCenter) ≤
            dist point gridCenter +
              dist gridCenter (representative gridCenter) :=
          dist_triangle _ _ _
        _ ≤ halfRadius + halfRadius :=
          add_le_add hpointDistance hrepresentativeDistance
        _ = targetRadius := by
          dsimp only [halfRadius]
          ring
    have hrepresentativeSelected :
        representative gridCenter ∈ selected :=
      Finset.mem_image.mpr
        ⟨gridCenter, hoccupied, rfl⟩
    refine Set.mem_iUnion.mpr
      ⟨representative gridCenter, ?_⟩
    refine Set.mem_iUnion.mpr
      ⟨hrepresentativeSelected, ?_⟩
    exact Metric.mem_closedBall.mpr hdistance

/-- Projection along a unit-speed selected good line is affine in its parameter. -/
lemma wz1Lemma18LinePoint_projection
    (anchor normal : Point3) (parameter : ℝ)
    (hnormal : ‖normal‖ = 1) :
    inner ℝ
        (wz1Lemma18LinePoint anchor normal parameter)
        normal =
      inner ℝ anchor normal + parameter := by
  rw [wz1Lemma18LinePoint, inner_add_left, real_inner_smul_left]
  have hself :
      inner ℝ normal normal = 1 := by
    rw [real_inner_self_eq_norm_sq, hnormal]
    norm_num
  rw [hself]
  ring

/-- A unit-speed selected good line preserves distance between parameters. -/
lemma wz1Lemma18LinePoint_dist
    (anchor normal : Point3) (first second : ℝ)
    (hnormal : ‖normal‖ = 1) :
    dist
        (wz1Lemma18LinePoint anchor normal first)
        (wz1Lemma18LinePoint anchor normal second) =
      dist first second := by
  rw [dist_eq_norm, Real.dist_eq]
  have hdifference :
      wz1Lemma18LinePoint anchor normal first -
          wz1Lemma18LinePoint anchor normal second =
        (first - second) • normal := by
    simp only [wz1Lemma18LinePoint]
    module
  rw [hdifference, norm_smul, Real.norm_eq_abs, hnormal]
  ring

/--
The actual shaded parameters of one good line whose projections lie in a
radius-`2*tau` interval are covered by at most nine radius-`tau` spatial balls
centered at actual shaded points of the same line.
-/
lemma wz1_lemma18_good_line_interval_cover
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (source : Set Point3)
    (anchor normal : Fin cellCount → Point3)
    (activeCell : Fin cellCount)
    (tau intervalCenter : ℝ)
    (htau : 0 < tau)
    (hnormal : ‖normal activeCell‖ = 1) :
    ∃ selected : Finset ℝ,
      (selected : Set ℝ) ⊆
        wz1Lemma18LineParameters
          cell source anchor normal activeCell ∧
      selected.card ≤ 9 ∧
      ∀ parameter ∈
          wz1Lemma18LineParameters
            cell source anchor normal activeCell,
        inner ℝ
            (wz1Lemma18LinePoint
              (anchor activeCell) (normal activeCell) parameter)
            (normal activeCell) ∈
              closedBall intervalCenter (2 * tau) →
          ∃ selectedParameter ∈ selected,
            wz1Lemma18LinePoint
                (anchor activeCell) (normal activeCell) parameter ∈
              closedBall
                (wz1Lemma18LinePoint
                  (anchor activeCell) (normal activeCell)
                  selectedParameter)
                tau := by
  let offset :=
    inner ℝ (anchor activeCell) (normal activeCell)
  let intervalParameters : Set ℝ :=
    wz1Lemma18LineParameters
        cell source anchor normal activeCell ∩
      closedBall (intervalCenter - offset) (2 * tau)
  have hintervalSubset :
      intervalParameters ⊆
        closedBall (intervalCenter - offset) (2 * tau) :=
    Set.inter_subset_right
  rcases
      real_subset_self_centered_cover
        htau (by positivity) hintervalSubset with
    ⟨selected, hselectedParameters, hselectedCard, hcover⟩
  have hcardNine : selected.card ≤ 9 := by
    have hceil :
        Nat.ceil (4 * (2 * tau) / tau) = 8 := by
      have htauNe : tau ≠ 0 := htau.ne'
      have hratio : 4 * (2 * tau) / tau = (8 : ℝ) := by
        field_simp [htauNe] <;> ring
      rw [hratio]
      norm_num
    rw [hceil] at hselectedCard
    have hselectedCard' :
        (selected.card : ENNReal) ≤ (9 : ENNReal) := by
      norm_num at hselectedCard ⊢
      exact hselectedCard
    exact_mod_cast hselectedCard'
  refine
    ⟨selected,
      fun parameter hparameter =>
        (hselectedParameters hparameter).1,
      hcardNine, ?_⟩
  intro parameter hparameter hprojection
  have hparameterBall :
      parameter ∈
        closedBall (intervalCenter - offset) (2 * tau) := by
    rw [Metric.mem_closedBall, Real.dist_eq] at hprojection ⊢
    rw [wz1Lemma18LinePoint_projection
      (anchor activeCell) (normal activeCell) parameter hnormal]
      at hprojection
    dsimp only [offset]
    ring_nf at hprojection ⊢
    exact hprojection
  have hparameterInterval :
      parameter ∈ intervalParameters :=
    ⟨hparameter, hparameterBall⟩
  rcases Set.mem_iUnion₂.mp (hcover hparameterInterval) with
    ⟨selectedParameter, hselectedParameter, hdistance⟩
  refine
    ⟨selectedParameter, hselectedParameter, ?_⟩
  rw [Metric.mem_closedBall] at hdistance ⊢
  rw [wz1Lemma18LinePoint_dist
    (anchor activeCell) (normal activeCell)
    parameter selectedParameter hnormal]
  exact hdistance

end Kakeya.Assouad

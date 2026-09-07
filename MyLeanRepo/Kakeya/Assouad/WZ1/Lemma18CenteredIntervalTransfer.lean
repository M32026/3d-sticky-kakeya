import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeFineProjectionCoveringTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ExternalCoveringNumberIsometry

/-!
# Centered multi-normal interval transfer for WZ1 Lemma 18

Different square-root cells carry different representative normals.  Their
absolute scalar projections cannot be compared directly: changing the normal
also changes the scalar offset at the center of the ambient square-root ball.

This module translates each cell projection so that all projections agree at
the ambient center, pays only the centered normal error, and combines the
resulting interval estimates over a finite cell set.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

/-- Translate one cell-normal projection to agree with `targetNormal` at `center`. -/
def wz1Lemma18AlignedProjection
    (center targetNormal sourceNormal : Point3)
    (source : Set ℝ) : Set ℝ :=
  (fun value =>
    value + inner ℝ center targetNormal -
      inner ℝ center sourceNormal) '' source

/--
Finite-cell interval transfer after centering all projection directions at
one ambient point.

Each source cell has a `rho`-covering bound in every radius-`tau` interval.
The target set is decomposed among finitely many source cells.  If centered
target and source projections differ by at most `epsilon`, then the target
interval covering number is bounded by:

* `5`, for covering the expanded radius-`2*tau` source interval by
  radius-`tau` intervals;
* the number of source cells; and
* the explicit `epsilon`-thickening grid factor.
-/
theorem wz1_lemma18_centered_finite_cell_interval_transfer
    {index : Type*}
    (cells : Finset index)
    (piece : index → Set Point3)
    (normal : index → Point3)
    (targetSet : Set Point3)
    (center targetNormal : Point3)
    (rho tau epsilon : ℝ)
    (bound : ENNReal)
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (hepsilon : 0 < epsilon)
    (hepsilonTau : epsilon ≤ tau)
    (hdecompose :
      ∀ point ∈ targetSet,
        ∃ cellIndex ∈ cells, point ∈ piece cellIndex)
    (hcentered :
      ∀ cellIndex ∈ cells,
        ∀ point ∈ piece cellIndex,
          dist
              (inner ℝ (point - center) targetNormal)
              (inner ℝ (point - center)
                (normal cellIndex)) ≤
            epsilon)
    (hlocal :
      ∀ cellIndex ∈ cells,
        ∀ intervalCenter : ℝ,
          (↑(externalCoveringNumber
            (Real.toNNReal rho)
            (scalarProjection (normal cellIndex)
                (piece cellIndex) ∩
              closedBall intervalCenter tau)) : ENNReal) ≤
            bound) :
    ∀ intervalCenter : ℝ,
      (↑(externalCoveringNumber
        (Real.toNNReal rho)
        (scalarProjection targetNormal targetSet ∩
          closedBall intervalCenter tau)) : ENNReal) ≤
        (2 * Nat.ceil (epsilon / rho) + 2 : ENNReal) *
          ((cells.card : ENNReal) * (5 * bound)) := by
  intro intervalCenter
  let shiftedCenter : index → ℝ := fun cellIndex =>
    intervalCenter -
      inner ℝ center targetNormal +
      inner ℝ center (normal cellIndex)
  let localSource : index → Set ℝ := fun cellIndex =>
    scalarProjection (normal cellIndex) (piece cellIndex) ∩
      closedBall (shiftedCenter cellIndex) (2 * tau)
  let alignedSource : index → Set ℝ := fun cellIndex =>
    wz1Lemma18AlignedProjection center targetNormal
      (normal cellIndex) (localSource cellIndex)
  let allSources : Set ℝ :=
    ⋃ cellIndex ∈ cells, alignedSource cellIndex
  have htargetSubset :
      scalarProjection targetNormal targetSet ∩
          closedBall intervalCenter tau ⊆
        cthickening epsilon allSources := by
    intro value hvalue
    rcases hvalue.1 with ⟨point, hpoint, rfl⟩
    rcases hdecompose point hpoint with
      ⟨cellIndex, hcellIndex, hpointPiece⟩
    let sourceValue :=
      inner ℝ point (normal cellIndex)
    let alignedValue :=
      sourceValue +
        inner ℝ center targetNormal -
        inner ℝ center (normal cellIndex)
    have hsourceInterval :
        sourceValue ∈
          closedBall (shiftedCenter cellIndex)
            (2 * tau) := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      have htargetInterval :
          |inner ℝ point targetNormal -
              intervalCenter| ≤ tau := by
        simpa [Metric.mem_closedBall, Real.dist_eq]
          using hvalue.2
      have hcenteredAt :=
        hcentered cellIndex hcellIndex point hpointPiece
      rw [Real.dist_eq] at hcenteredAt
      have hcenteredIdentity :
          (inner ℝ point (normal cellIndex) -
              inner ℝ center (normal cellIndex)) -
            (intervalCenter -
              inner ℝ center targetNormal) =
          ((inner ℝ point (normal cellIndex) -
              inner ℝ center (normal cellIndex)) -
            (inner ℝ point targetNormal -
              inner ℝ center targetNormal)) +
            (inner ℝ point targetNormal -
              intervalCenter) := by
        ring
      dsimp only [sourceValue, shiftedCenter]
      have hleft :
          inner ℝ point (normal cellIndex) -
              (intervalCenter -
                inner ℝ center targetNormal +
                inner ℝ center (normal cellIndex)) =
            (inner ℝ point (normal cellIndex) -
                inner ℝ center (normal cellIndex)) -
              (intervalCenter -
                inner ℝ center targetNormal) := by
        ring
      rw [hleft]
      rw [hcenteredIdentity]
      calc
        |((inner ℝ point (normal cellIndex) -
              inner ℝ center (normal cellIndex)) -
            (inner ℝ point targetNormal -
              inner ℝ center targetNormal)) +
            (inner ℝ point targetNormal -
              intervalCenter)| ≤
            |(inner ℝ point (normal cellIndex) -
                inner ℝ center (normal cellIndex)) -
              (inner ℝ point targetNormal -
                inner ℝ center targetNormal)| +
              |inner ℝ point targetNormal -
                intervalCenter| :=
          abs_add_le _ _
        _ ≤ epsilon + tau := by
          have hcentered' :
              |(inner ℝ point (normal cellIndex) -
                  inner ℝ center (normal cellIndex)) -
                (inner ℝ point targetNormal -
                  inner ℝ center targetNormal)| ≤
                epsilon := by
            rw [abs_sub_comm]
            simpa [inner_sub_left] using hcenteredAt
          exact add_le_add hcentered' htargetInterval
        _ ≤ 2 * tau := by linarith
    have hsource :
        sourceValue ∈ localSource cellIndex :=
      ⟨⟨point, hpointPiece, rfl⟩, hsourceInterval⟩
    have haligned :
        alignedValue ∈ alignedSource cellIndex :=
      ⟨sourceValue, hsource, rfl⟩
    have hall :
        alignedValue ∈ allSources := by
      exact Set.mem_iUnion₂.mpr
        ⟨cellIndex, hcellIndex, haligned⟩
    have hdistance :
        dist (inner ℝ point targetNormal) alignedValue ≤
          epsilon := by
      rw [Real.dist_eq]
      have hcenteredAt :=
        hcentered cellIndex hcellIndex point hpointPiece
      rw [Real.dist_eq] at hcenteredAt
      have hidentity :
          inner ℝ point targetNormal - alignedValue =
            (inner ℝ point targetNormal -
              inner ℝ center targetNormal) -
            (inner ℝ point (normal cellIndex) -
              inner ℝ center (normal cellIndex)) := by
        dsimp only [alignedValue, sourceValue]
        ring
      rw [hidentity]
      simpa [inner_sub_left] using hcenteredAt
    exact
      mem_cthickening_of_dist_le
        (inner ℝ point targetNormal) alignedValue
        epsilon allSources hall hdistance
  have hlocalSource :
      ∀ cellIndex ∈ cells,
        (↑(externalCoveringNumber
          (Real.toNNReal rho)
          (localSource cellIndex)) : ENNReal) ≤
          5 * bound := by
    intro cellIndex hcellIndex
    rcases
        real_closedBall_finer_cover
          (shiftedCenter cellIndex) htau
          (show 0 < 2 * tau by positivity)
          (by linarith : tau ≤ 2 * tau) with
      ⟨intervalCenters, hintervalCentersCard,
        hintervalCentersCover⟩
    have hcardFive :
        (intervalCenters.card : ENNReal) ≤ 5 := by
      have hceil :
          Nat.ceil (2 * (2 * tau) / tau) = 4 := by
        have htauNe : tau ≠ 0 := htau.ne'
        have hratio :
            2 * (2 * tau) / tau = (4 : ℝ) := by
          field_simp [htauNe] <;> ring
        rw [hratio]
        norm_num
      rw [hceil] at hintervalCentersCard
      norm_num at hintervalCentersCard ⊢
      exact hintervalCentersCard
    have hsubset :
        localSource cellIndex ⊆
          ⋃ sourceCenter ∈ intervalCenters,
            scalarProjection (normal cellIndex)
                (piece cellIndex) ∩
              closedBall sourceCenter tau := by
      intro value hvalue
      rcases Set.mem_iUnion₂.mp
          (hintervalCentersCover hvalue.2) with
        ⟨sourceCenter, hsourceCenter, hvalueBall⟩
      exact Set.mem_iUnion₂.mpr
        ⟨sourceCenter, hsourceCenter,
          ⟨hvalue.1, hvalueBall⟩⟩
    have hmono :
        (↑(externalCoveringNumber
          (Real.toNNReal rho)
          (localSource cellIndex)) : ENNReal) ≤
          (↑(externalCoveringNumber
            (Real.toNNReal rho)
            (⋃ sourceCenter ∈ intervalCenters,
              scalarProjection (normal cellIndex)
                  (piece cellIndex) ∩
                closedBall sourceCenter tau)) : ENNReal) := by
      exact_mod_cast externalCoveringNumber_mono_set hsubset
    have hunion :=
      externalCoveringNumber_biUnion_le_card
        (ε := Real.toNNReal rho)
        (s := intervalCenters)
        (A := fun sourceCenter =>
          scalarProjection (normal cellIndex)
              (piece cellIndex) ∩
            closedBall sourceCenter tau)
        (fun sourceCenter hsourceCenter =>
          hlocal cellIndex hcellIndex sourceCenter)
    exact hmono.trans (hunion.trans (by gcongr))
  have halignedCover :
      ∀ cellIndex ∈ cells,
        (↑(externalCoveringNumber
          (Real.toNNReal rho)
          (alignedSource cellIndex)) : ENNReal) ≤
          5 * bound := by
    intro cellIndex hcellIndex
    let translation : ℝ :=
      inner ℝ center targetNormal -
        inner ℝ center (normal cellIndex)
    have hset :
        alignedSource cellIndex =
          (fun value : ℝ => value + translation) ''
            localSource cellIndex := by
      simp only [alignedSource,
        wz1Lemma18AlignedProjection, translation]
      congr 1
      funext value
      ring
    have htranslation' :
        externalCoveringNumber (Real.toNNReal rho)
            ((fun value : ℝ => value + translation) ''
              localSource cellIndex) =
          externalCoveringNumber (Real.toNNReal rho)
            (localSource cellIndex) := by
      let map : ℝ → ℝ := fun value => value + translation
      have hmap : Isometry map := isometry_add_right translation
      have hsurjective : Function.Surjective map := by
        intro value
        exact ⟨value - translation, by
          dsimp only [map]
          ring⟩
      exact
        Isometry.externalCoveringNumber_image
          hmap hsurjective
    rw [hset, htranslation']
    exact hlocalSource cellIndex hcellIndex
  have hallSources :
      (↑(externalCoveringNumber
        (Real.toNNReal rho) allSources) : ENNReal) ≤
        (cells.card : ENNReal) * (5 * bound) := by
    exact
      externalCoveringNumber_biUnion_le_card
        (ε := Real.toNNReal rho)
        (s := cells)
        (A := alignedSource)
        halignedCover
  exact
    externalCoveringNumber_of_subset_cthickening
      hrho hepsilon htargetSubset hallSources

end Kakeya.Assouad

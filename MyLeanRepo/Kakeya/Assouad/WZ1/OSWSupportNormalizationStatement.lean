import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic

/-!
# Common-similarity normalization for the OSW bootstrap

The finite-point model smooths each point before applying OSW.  A pair whose
original distance is exactly `1 / 2` would therefore lose the strict support
margin required by OSW.  This module freezes the common-similarity
normalization that creates that margin without applying different maps to the
two sets.
-/

namespace Kakeya.Assouad

open MeasureTheory

/-- Midpoint-centered homothety used to normalize a closest pair to distance one. -/
noncomputable def wz1OSWPairNormalize
    (center₁ center₂ : Point2) (x : Point2) : Point2 :=
  (dist center₁ center₂)⁻¹ •
    (x - (2 : ℝ)⁻¹ • (center₁ + center₂))

/--
Geometric output of the common-similarity normalization.

Both finite sets are transformed by the same homothety.  The scale lies
between `1 / 2` and `2`; the transformed discrete scale is at most `1 / 5`;
the transformed sets remain separated at that scale; and smoothing them at
one tenth of that scale produces probability measures supported in the unit
ball with mutual support distance at least `1 / 2`.
-/
structure WZ1OSWSupportNormalizationData
    (delta : ℝ) (G₁ G₂ : DiscreteSet 2) where
  center₁ : Point2
  center₂ : Point2
  center₁_mem : center₁ ∈ G₁
  center₂_mem : center₂ ∈ G₂
  closest :
    ∀ x ∈ G₁, ∀ y ∈ G₂,
      dist center₁ center₂ ≤ dist x y
  scale : ℝ
  scale_eq : scale = (dist center₁ center₂)⁻¹
  scale_lower : (1 : ℝ) / 2 ≤ scale
  scale_upper : scale ≤ 2
  normalizedDelta : ℝ
  normalizedDelta_eq : normalizedDelta = scale * delta
  normalizedDelta_pos : 0 < normalizedDelta
  normalizedDelta_upper : normalizedDelta ≤ (1 : ℝ) / 5
  normalized₁ : DiscreteSet 2
  normalized₂ : DiscreteSet 2
  normalized₁_eq :
    normalized₁ = G₁.image (wz1OSWPairNormalize center₁ center₂)
  normalized₂_eq :
    normalized₂ = G₂.image (wz1OSWPairNormalize center₁ center₂)
  normalized₁_nonempty : normalized₁.Nonempty
  normalized₂_nonempty : normalized₂.Nonempty
  normalized₁_separated :
    normalized₁.IsDeltaSeparated normalizedDelta
  normalized₂_separated :
    normalized₂.IsDeltaSeparated normalizedDelta
  normalized₁_in_inner_ball :
    (normalized₁ : Set Point2) ⊆
      Metric.closedBall 0 (7 / 10 : ℝ)
  normalized₂_in_inner_ball :
    (normalized₂ : Set Point2) ⊆
      Metric.closedBall 0 (7 / 10 : ℝ)
  normalized_mutual_distance :
    ∀ x ∈ normalized₁, ∀ y ∈ normalized₂,
      1 ≤ dist x y
  smooth₁_support :
    (smoothMeasure normalized₁ normalized₁_nonempty
        (normalizedDelta / 10) (by positivity) :
      Measure Point2).support ⊆ Metric.closedBall 0 1
  smooth₂_support :
    (smoothMeasure normalized₂ normalized₂_nonempty
        (normalizedDelta / 10) (by positivity) :
      Measure Point2).support ⊆ Metric.closedBall 0 1
  smooth_mutual_distance :
    (1 : ℝ) / 2 ≤
      sInf {d : ℝ |
        ∃ x ∈
            (smoothMeasure normalized₁ normalized₁_nonempty
              (normalizedDelta / 10) (by positivity) :
                Measure Point2).support,
          ∃ y ∈
              (smoothMeasure normalized₂ normalized₂_nonempty
                (normalizedDelta / 10) (by positivity) :
                  Measure Point2).support,
            dist x y = d}

/--
Normalize a pair of small, mutually separated planar sets by one common
similarity before smoothing.

The diameter hypotheses are the two `G`-parts of the paper's standard
separation conditions.  Unit-ball containment gives the upper bound on the
closest-pair distance, while mutual `1 / 2` separation gives the lower bound.
The common map is essential: independently translating the two sets would
not preserve thin-tube geometry.
-/
def WZ1OSWSupportNormalizationStatement : Prop :=
  ∀ {delta : ℝ} (G₁ G₂ : DiscreteSet 2),
    G₁.Nonempty →
    G₂.Nonempty →
    0 < delta →
    delta ≤ (1 : ℝ) / 10 →
    G₁.IsDeltaSeparated delta →
    G₂.IsDeltaSeparated delta →
    G₁.IsInUnitBall →
    G₂.IsInUnitBall →
    (∀ x ∈ G₁, ∀ y ∈ G₁, dist x y ≤ (1 : ℝ) / 10) →
    (∀ x ∈ G₂, ∀ y ∈ G₂, dist x y ≤ (1 : ℝ) / 10) →
    (∀ x ∈ G₁, ∀ y ∈ G₂, (1 : ℝ) / 2 ≤ dist x y) →
      Nonempty (WZ1OSWSupportNormalizationData delta G₁ G₂)

end Kakeya.Assouad

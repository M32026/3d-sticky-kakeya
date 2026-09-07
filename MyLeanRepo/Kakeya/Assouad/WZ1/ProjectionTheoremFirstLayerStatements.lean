import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# First-layer leaves for WZ1 Theorem 22

This module freezes the five independent inputs at the bottom of the paper's
Section 8 dependency graph: Lemmas 37, 40, 44, 47, and 48.  Proposition 41,
Proposition 45, Lemma 49, and the final removal of standard separation are
deliberately not hidden in these interfaces.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

/-- Edges agreeing with `edge` on the coordinate set `I`. -/
def wz1HypergraphFiber
    {k : ℕ} {α : Type*} [DecidableEq α]
    (H : Finset (Fin k → α)) (I : Finset (Fin k))
    (edge : Fin k → α) : Finset (Fin k → α) := by
  classical
  exact H.filter fun other => ∀ i ∈ I, other i = edge i

/-- Product of the sizes of the vertex classes indexed by `I`. -/
def wz1VertexCardProduct
    {k : ℕ} {α : Type*}
    (A : Fin k → Finset α) (I : Finset (Fin k)) : ENNReal :=
  ∏ i ∈ I, (A i).card

/--
The paper's uniform hypergraph density, including support in the prescribed
vertex classes.

The fiber condition is imposed for every edge and every coordinate subset,
including the empty and full subsets.
-/
def WZ1UniformHypergraphDensity
    {k : ℕ} {α : Type*} [DecidableEq α]
    (c : ENNReal) (A : Fin k → Finset α)
    (H : Finset (Fin k → α)) : Prop :=
  (∀ edge ∈ H, ∀ i, edge i ∈ A i) ∧
    ∀ edge ∈ H, ∀ I : Finset (Fin k),
      c * wz1VertexCardProduct A (Finset.univ \ I) ≤
        ((wz1HypergraphFiber H I edge).card : ENNReal)

/--
WZ1 Lemma 37, the general finite hypergraph refinement lemma.

The density in the conclusion is exactly
`2^{-k} * epsilon * #H / ∏ #Aᵢ`; the retained edge count is at least
`(1-epsilon) * #H`.
-/
def WZ1HypergraphRefinementStatement : Prop :=
  ∀ {k : ℕ} {α : Type*} [DecidableEq α],
    ∀ A : Fin k → Finset α,
      ∀ H : Finset (Fin k → α),
        (∀ edge ∈ H, ∀ i, edge i ∈ A i) →
        ∀ epsilon : ENNReal, 0 < epsilon → epsilon < 1 →
          ∃ H' : Finset (Fin k → α),
            H' ⊆ H ∧
            (1 - epsilon) * (H.card : ENNReal) ≤
              (H'.card : ENNReal) ∧
            WZ1UniformHypergraphDensity
              ((epsilon / (2 : ENNReal) ^ k) *
                ((H.card : ENNReal) /
                  wz1VertexCardProduct A Finset.univ))
              A H'

/-- Coordinate projection of a tripartite edge. -/
def wz1TripleCoordinate
    (edge : Point2 × Point2 × Point2) (i : Fin 3) : Point2 :=
  match i with
  | 0 => edge.1
  | 1 => edge.2.1
  | 2 => edge.2.2

/-- Vertex classes of a tripartite planar hypergraph. -/
def wz1TripleVertexClasses
    (F G₁ G₂ : DiscreteSet 2) (i : Fin 3) : DiscreteSet 2 :=
  match i with
  | 0 => F
  | 1 => G₁
  | 2 => G₂

/-- The function-valued encoding used by the general hypergraph predicate. -/
def wz1EncodeTriples
    (H : Finset (Point2 × Point2 × Point2)) :
    Finset (Fin 3 → Point2) :=
  H.image wz1TripleCoordinate

/-- Uniform density for the paper's tripartite graph. -/
def WZ1UniformTripleDensity
    (c : ENNReal) (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)) : Prop :=
  H.Nonempty ∧
    WZ1UniformHypergraphDensity c
      (wz1TripleVertexClasses F G₁ G₂)
      (wz1EncodeTriples H)

/-- Pairwise distance between two finite planar sets is at least `r`. -/
def WZ1MutuallySeparated
    (A B : DiscreteSet 2) (r : ℝ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, r ≤ dist a b

/--
The literal non-vacuous standard-separation conditions used in Lemma 40.
-/
def WZ1StandardSeparation
    (F G₁ G₂ : DiscreteSet 2) : Prop :=
  (∀ x ∈ F, ∀ y ∈ F, dist x y ≤ 1 / 10) ∧
  (∀ x ∈ G₁, ∀ y ∈ G₁, dist x y ≤ 1 / 10) ∧
  (∀ x ∈ G₂, ∀ y ∈ G₂, dist x y ≤ 1 / 10) ∧
  WZ1MutuallySeparated G₁ G₂ (1 / 2) ∧
  (∀ a ∈ F, 1 / 2 ≤ dist a 0)

/--
WZ1 Lemma 40: thin tubes and uniform tripartite density force a large
dot-difference projection.

`A` is the implicit constant in the paper's `gtrsim` for the fixed
projection-loss exponent `epsilon`.  The
finite sets are explicitly nonempty, separated, and bounded, and the graph
is explicitly supported and nonempty through `WZ1UniformTripleDensity`.
-/
def WZ1ThinTubesLargeDotProductStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ A : ℝ, 1 ≤ A ∧
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ c K : ℝ, 0 ≤ c → c < 1 → 1 ≤ K →
            ∀ F G₁ G₂ : DiscreteSet 2,
              F.Nonempty → G₁.Nonempty → G₂.Nonempty →
              F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
              F.IsDeltaSeparated delta →
              G₁.IsDeltaSeparated delta →
              G₂.IsDeltaSeparated delta →
              F.IsFrostman delta 1 (ENNReal.ofReal K) →
              G₁.IsFrostman delta 1 (ENNReal.ofReal K) →
              G₂.IsFrostman delta 1 (ENNReal.ofReal K) →
              WZ1StandardSeparation F G₁ G₂ →
              HasDiscreteThinTubes delta 1 K c G₁ G₂ →
              ∀ H : Finset (Point2 × Point2 × Point2),
                WZ1UniformTripleDensity
                  (ENNReal.ofReal (2 * c)) F G₁ G₂ H →
                  ENNReal.ofReal
                      ((c ^ 5 / (A * K ^ 2)) *
                        Real.rpow delta (epsilon - 1)) ≤
                    (↑(Metric.externalCoveringNumber
                      (Real.toNNReal delta)
                      (wz1DotDifferenceSet H)) : ENNReal)

/-- The line non-concentration hypothesis used in Lemma 44. -/
def WZ1LineNonConcentration
    (delta lambda zeta : ℝ) (G : DiscreteSet 2) : Prop :=
  ∀ normal : Point2, ‖normal‖ = 1 →
    ∀ t r : ℝ, delta ≤ r → r ≤ 1 →
      ((G.filter fun y =>
        |inner ℝ y normal - t| ≤ r).card : ENNReal) ≤
          Kakeya.realRpowENN
              (Real.rpow delta (-lambda) * r) zeta *
            G.enncard

/--
WZ1 Lemma 44: line non-concentration gives one-quarter thin tubes.

The exceptional fraction is exactly `delta^alpha`, while the thin-tube
constant is `delta^(-3 alpha / zeta - lambda)`.
-/
def WZ1QuarterThinTubesStatement : Prop :=
  ∀ lambda zeta alpha : ℝ,
    0 < lambda → 0 < zeta → 0 < alpha →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ G₁ G₂ : DiscreteSet 2,
            G₁.Nonempty → G₂.Nonempty →
            G₁.IsInUnitBall → G₂.IsInUnitBall →
            G₁.IsDeltaSeparated delta →
            G₂.IsDeltaSeparated delta →
            G₁.IsFrostman delta 1
              (Kakeya.realRpowENN delta (-lambda)) →
            G₂.IsFrostman delta 1
              (Kakeya.realRpowENN delta (-lambda)) →
            WZ1MutuallySeparated G₁ G₂ (1 / 2) →
            WZ1LineNonConcentration delta lambda zeta G₂ →
              HasDiscreteThinTubes delta (1 / 4)
                (Real.rpow delta (-3 * alpha / zeta - lambda))
                (Real.rpow delta alpha) G₁ G₂

/--
Discrete output of the anisotropic Frostman rescaling in Lemma 47.

The assignment records the `delta / w` cells meeting the affine image.
Every occupied cell has comparable source multiplicity, so the coarse
Frostman set and the retained source subset remain quantitatively linked.
-/
structure WZ1AnisotropicFrostmanRescalingData
    (E : DiscreteSet 2) (phi : Point2 ≃ᵃ[ℝ] Point2)
    (delta w epsilon : ℝ) (C : ENNReal) where
  selected : DiscreteSet 2
  selected_subset : selected ⊆ E
  selected_nonempty : selected.Nonempty
  retention :
    Kakeya.realRpowENN (delta / w) epsilon * E.enncard ≤
      selected.enncard
  coarse : DiscreteSet 2
  coarse_nonempty : coarse.Nonempty
  coarse_separated : coarse.IsDeltaSeparated (delta / w)
  coarse_frostman :
    coarse.IsFrostman (delta / w) 1
      (Kakeya.realRpowENN (w / delta) epsilon * C)
  assignment : Point2 → Point2
  assignment_mem :
    ∀ x ∈ selected, assignment x ∈ coarse
  assignment_close :
    ∀ x ∈ selected, dist (phi x) (assignment x) ≤ delta / w
  assignment_surjective :
    ∀ q ∈ coarse, ∃ x ∈ selected, assignment x = q
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_comparable :
    ∀ q ∈ coarse,
      fiberMultiplicity ≤
          (selected.filter fun x => assignment x = q).card ∧
        (selected.filter fun x => assignment x = q).card ≤
          2 * fiberMultiplicity

/--
WZ1 Lemma 47: anisotropic rescaling with a balanced cell refinement.

The geometric assumptions say that the inverse affine map does not enlarge
distances and that the source rectangle is sent into a fixed bounded window.
These are the exact properties of the paper's map from a `1 x w` rectangle
to the unit square that enter the Frostman proof.
-/
def WZ1AnisotropicFrostmanRescalingStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta w : ℝ,
        0 < delta → delta ≤ delta₀ →
        delta ≤ w → w ≤ 1 →
        Real.rpow delta (1 - epsilon) ≤ w →
          ∀ E : DiscreteSet 2, E.Nonempty →
            ∀ C : ENNReal, 1 ≤ C →
              E.IsDeltaSeparated delta →
              E.IsFrostman delta 1 C →
              ∀ phi : Point2 ≃ᵃ[ℝ] Point2,
                (∀ x y, dist (phi.symm x) (phi.symm y) ≤ dist x y) →
                (∀ x ∈ E, dist (phi x) 0 ≤ 2) →
                  Nonempty
                    (WZ1AnisotropicFrostmanRescalingData
                      E phi delta w epsilon C)

/-- Balanced occupied cells produced by the Frostman coarsening lemma. -/
structure WZ1FrostmanCoarseningData
    (E : DiscreteSet 2) (delta rho alpha : ℝ) (C : ENNReal) where
  selected : DiscreteSet 2
  selected_subset : selected ⊆ E
  selected_nonempty : selected.Nonempty
  logarithmicLoss : ℝ
  logarithmicLoss_pos : 0 < logarithmicLoss
  logarithmicLoss_bound :
    logarithmicLoss ≤ 20 * (1 + Real.log delta⁻¹)
  retention :
    E.enncard ≤
      ENNReal.ofReal logarithmicLoss * selected.enncard
  coarse : DiscreteSet 2
  coarse_nonempty : coarse.Nonempty
  coarse_separated : coarse.IsDeltaSeparated rho
  coarse_frostman :
    coarse.IsFrostman rho alpha
      (ENNReal.ofReal (100 * logarithmicLoss) * C)
  assignment : Point2 → Point2
  assignment_mem :
    ∀ x ∈ selected, assignment x ∈ coarse
  assignment_close :
    ∀ x ∈ selected, dist x (assignment x) ≤ rho
  assignment_surjective :
    ∀ q ∈ coarse, ∃ x ∈ selected, assignment x = q
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_comparable :
    ∀ q ∈ coarse,
      fiberMultiplicity ≤
          (selected.filter fun x => assignment x = q).card ∧
        (selected.filter fun x => assignment x = q).card ≤
          2 * fiberMultiplicity

/--
WZ1 Lemma 48: coarsen a finite Frostman set after a logarithmic
equal-occupancy refinement.
-/
def WZ1FrostmanCoarseningStatement : Prop :=
  ∀ delta rho alpha : ℝ,
    0 < delta → delta ≤ 1 / 2 →
    delta ≤ rho → rho ≤ 1 →
    0 < alpha → alpha ≤ 2 →
      ∀ E : DiscreteSet 2, E.Nonempty →
        E.IsInUnitBall →
        E.IsDeltaSeparated delta →
        ∀ C : ENNReal, 1 ≤ C →
          E.IsFrostman delta alpha C →
            Nonempty
              (WZ1FrostmanCoarseningData
                E delta rho alpha C)

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalTiltStatements

/-!
# Planar projection fullness in WZ1 Lemma 23 Step 1

An almost-full planar slice lies in one `sqrt rho` coarse square and one
width-`rho` local-projection strip.  Its image under the global-grain
projection lies in the tilt-controlled interval from
`Lemma23NormalTiltGeometry`.  The area lower bound forces that image to occupy
a definite fraction of the interval.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

/-- The slope-independent planar fullness core. -/
def WZ1Lemma23PlanarProjectionFullnessCoreStatement : Prop :=
  ∀ (rho eta : ℝ),
    0 < rho → rho ≤ 1 →
    0 < eta →
    32 * Real.rpow rho eta ≤ 1 →
    ∀ (slice : Set (Fin 2 → ℝ))
      (sliceCenter : Fin 2 → ℝ)
      (stripCenter : ℝ)
      (normal : Point3) (slope : ℝ),
      MeasurableSet slice →
      ‖normal‖ = 1 →
      |normal (2 : Fin 3)| ≤ 1 / 2 →
      (∀ point ∈ slice,
        |point 0 - sliceCenter 0| ≤ Real.sqrt rho ∧
          |point 1 - sliceCenter 1| ≤ Real.sqrt rho) →
      (∀ point ∈ slice,
        |normal 0 * point 0 + normal 1 * point 1 -
            stripCenter| ≤ rho) →
      let globalProjection : Set ℝ :=
        (fun point : Fin 2 → ℝ =>
          point 0 + slope * point 1) '' slice
      let projectionRadius : ℝ :=
        4 * rho +
          4 * Real.sqrt rho *
            |normal 1 - slope * normal 0|
      Kakeya.realRpowENN rho (3 / 2 + 2 * eta) ≤
          volume slice →
      |normal 1 - slope * normal 0| ≤ Real.sqrt rho ∨
        ∃ density : ENNReal,
          Kakeya.realRpowENN rho (3 * eta) ≤ density ∧
            density * ENNReal.ofReal (2 * projectionRadius) ≤
              volume globalProjection

/--
The pure planar fullness leaf used to construct
`WZ1Lemma23NormalTiltWitness`.

The `sliceArea` premise is the Fubini output from an almost-full local grain.
The conclusion is the exact `globalProjection_full` field of the faithful
normal-tilt witness.
-/
def WZ1Lemma23PlanarProjectionFullnessStatement : Prop :=
  ∀ (rho eta : ℝ),
    0 < rho → rho ≤ 1 →
    0 < eta →
    32 * Real.rpow rho eta ≤ 1 →
    ∀ (slice : Set (Fin 2 → ℝ))
      (sliceCenter : Fin 2 → ℝ)
      (stripCenter : ℝ)
      (normal : Point3) (slope : ℝ),
      MeasurableSet slice →
      ‖normal‖ = 1 →
      |normal (2 : Fin 3)| ≤ 1 / 2 →
      |slope| ≤ 1 / 10 →
      (∀ point ∈ slice,
        |point 0 - sliceCenter 0| ≤ Real.sqrt rho ∧
          |point 1 - sliceCenter 1| ≤ Real.sqrt rho) →
      (∀ point ∈ slice,
        |normal 0 * point 0 + normal 1 * point 1 -
            stripCenter| ≤ rho) →
      let globalProjection : Set ℝ :=
        (fun point : Fin 2 → ℝ =>
          point 0 + slope * point 1) '' slice
      let projectionRadius : ℝ :=
        4 * rho +
          4 * Real.sqrt rho *
            |normal 1 - slope * normal 0|
      Kakeya.realRpowENN rho (3 / 2 + 2 * eta) ≤
          volume slice →
      |normal 1 - slope * normal 0| ≤ Real.sqrt rho ∨
        ∃ density : ENNReal,
          Kakeya.realRpowENN rho (3 * eta) ≤ density ∧
            density * ENNReal.ofReal (2 * projectionRadius) ≤
              volume globalProjection

/--
The planar fullness statement with the source-package slope bound `3`.
The proof is slope-independent, but this hypothesis records the bound
available to the witness producer.
-/
def WZ1Lemma23PlanarProjectionFullnessStatementGeneralized : Prop :=
  ∀ (rho eta : ℝ),
    0 < rho → rho ≤ 1 →
    0 < eta →
    32 * Real.rpow rho eta ≤ 1 →
    ∀ (slice : Set (Fin 2 → ℝ))
      (sliceCenter : Fin 2 → ℝ)
      (stripCenter : ℝ)
      (normal : Point3) (slope : ℝ),
      MeasurableSet slice →
      ‖normal‖ = 1 →
      |normal (2 : Fin 3)| ≤ 1 / 2 →
      |slope| ≤ 3 →
      (∀ point ∈ slice,
        |point 0 - sliceCenter 0| ≤ Real.sqrt rho ∧
          |point 1 - sliceCenter 1| ≤ Real.sqrt rho) →
      (∀ point ∈ slice,
        |normal 0 * point 0 + normal 1 * point 1 -
            stripCenter| ≤ rho) →
      let globalProjection : Set ℝ :=
        (fun point : Fin 2 → ℝ =>
          point 0 + slope * point 1) '' slice
      let projectionRadius : ℝ :=
        4 * rho +
          4 * Real.sqrt rho *
            |normal 1 - slope * normal 0|
      Kakeya.realRpowENN rho (3 / 2 + 2 * eta) ≤
          volume slice →
      |normal 1 - slope * normal 0| ≤ Real.sqrt rho ∨
        ∃ density : ENNReal,
          Kakeya.realRpowENN rho (3 * eta) ≤ density ∧
            density * ENNReal.ofReal (2 * projectionRadius) ≤
              volume globalProjection
end

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalHorizontalComponent
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ProjectionFullnessAD

/-!
# Faithful Step 1 boundary for WZ1 Lemma 23

Before defining the local graph, the paper proves that the normal attached to
each retained `sqrt rho` spatial cube has large first horizontal component.
This does not follow from the final Proposition 9 package alone.  It uses:

1. an almost-full local-grain fiber in the coarse cube;
2. a horizontal slice of that fiber with large planar area;
3. exact-slice global AD control; and
4. the geometric relation between the slice rectangle and the two projection
   directions.

The structures below expose those genuine witnesses without assuming the
desired component bound itself.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

/--
One planar witness produced from an almost-full local grain in a selected
`sqrt rho` coarse cube.
-/
structure WZ1Lemma23NormalTiltWitness
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) (normal : Point3) where
  sliceHeight : ℝ
  slice : Set Point2
  sliceCenter : Point2
  stripCenter : ℝ
  projected : Set ℝ
  projectionCenter : ℝ
  projectionRadius : ℝ
  slice_measurable : MeasurableSet slice
  slice_in_square :
    ∀ point ∈ slice,
      |point 0 - sliceCenter 0| ≤ Real.sqrt rho ∧
        |point 1 - sliceCenter 1| ≤ Real.sqrt rho
  slice_in_local_strip :
    ∀ point ∈ slice,
      |normal 0 * point 0 + normal 1 * point 1 -
          stripCenter| ≤ rho
  normal_unit : ‖normal‖ = 1
  normal_vertical : |normal (2 : Fin 3)| ≤ 1 / 2
  slope_small : |slope sliceHeight| ≤ 1 / 10
  globalAD : IsADSet1 projected rho (1 - sigma) C
  tiltedProjection : Set ℝ
  tiltedProjection_eq :
    tiltedProjection =
      (fun point : Point2 =>
        point 0 * (-slope sliceHeight) + point 1) '' slice
  globalProjection : Set ℝ
  globalProjection_eq :
    globalProjection =
      (fun point : Point2 =>
        point 0 + slope sliceHeight * point 1) '' slice
  projectionCenter_eq :
    projectionCenter =
      ((normal 0 + slope sliceHeight * normal 1) *
            stripCenter -
          (normal 1 - slope sliceHeight * normal 0) *
            (normal 0 * sliceCenter 1 -
              normal 1 * sliceCenter 0)) /
        (normal 0 ^ 2 + normal 1 ^ 2)
  projectionRadius_eq :
    projectionRadius =
      4 * rho +
        4 * Real.sqrt rho *
          |normal 1 - slope sliceHeight * normal 0|
  globalProjection_sub_projected :
    globalProjection ⊆ projected
  projectionRadius_upper : projectionRadius ≤ 1
  density : ENNReal
  density_lower :
    Kakeya.realRpowENN rho (3 * eta) ≤ density
  globalProjection_full :
    density * ENNReal.ofReal (2 * projectionRadius) ≤
      volume globalProjection

/--
The generalized witness for the source-package slope bound `3`.  The lower
tilt bound records that this witness is produced only in the non-small-tilt
branch; it is what absorbs the larger local-coordinate error.
-/
structure WZ1Lemma23NormalTiltWitnessGeneralized
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) (normal : Point3) where
  sliceHeight : ℝ
  slice : Set Point2
  sliceCenter : Point2
  stripCenter : ℝ
  projected : Set ℝ
  projectionCenter : ℝ
  projectionRadius : ℝ
  slice_measurable : MeasurableSet slice
  slice_in_square :
    ∀ point ∈ slice,
      |point 0 - sliceCenter 0| ≤ Real.sqrt rho ∧
        |point 1 - sliceCenter 1| ≤ Real.sqrt rho
  slice_in_local_strip :
    ∀ point ∈ slice,
      |normal 0 * point 0 + normal 1 * point 1 -
          stripCenter| ≤ rho
  normal_unit : ‖normal‖ = 1
  normal_vertical : |normal (2 : Fin 3)| ≤ 1 / 2
  slope_small : |slope sliceHeight| ≤ 3
  tilt_lower :
    Real.sqrt rho ≤
      |normal 1 - slope sliceHeight * normal 0|
  globalAD : IsADSet1 projected rho (1 - sigma) C
  tiltedProjection : Set ℝ
  tiltedProjection_eq :
    tiltedProjection =
      (fun point : Point2 =>
        point 0 * (-slope sliceHeight) + point 1) '' slice
  globalProjection : Set ℝ
  globalProjection_eq :
    globalProjection =
      (fun point : Point2 =>
        point 0 + slope sliceHeight * point 1) '' slice
  projectionCenter_eq :
    projectionCenter =
      ((normal 0 + slope sliceHeight * normal 1) *
            stripCenter -
          (normal 1 - slope sliceHeight * normal 0) *
            (normal 0 * sliceCenter 1 -
              normal 1 * sliceCenter 0)) /
        (normal 0 ^ 2 + normal 1 ^ 2)
  projectionRadius_eq :
    projectionRadius =
      4 * rho +
        4 * Real.sqrt rho *
          |normal 1 - slope sliceHeight * normal 0|
  globalProjection_sub_projected :
    globalProjection ⊆ projected
  projectionRadius_upper : projectionRadius ≤ 1
  density : ENNReal
  density_lower :
    Kakeya.realRpowENN rho (3 * eta) ≤ density
  globalProjection_full :
    density * ENNReal.ofReal (2 * projectionRadius) ≤
      volume globalProjection

/--
The hard geometric Step 1 leaf.

The conclusion is the quantitative normal tilt used by
`wz1_lemma23_normal_first_component`; the premise retains the actual
full-grain slice and both scalar projections, so a diagonal or auxiliary-grid
substitute cannot satisfy the API.
-/
def WZ1Lemma23NormalTiltStatement : Prop :=
  ∀ (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) (normal : Point3),
    0 < rho → rho ≤ 1 →
    0 < sigma → sigma < 1 →
    0 < eta → 4 * eta < sigma →
    C ≠ ⊤ →
    C ≤ Kakeya.realRpowENN rho (-eta) →
    Real.rpow rho (1 - 4 * eta / sigma) ≤
      Real.sqrt rho / 10 →
    ∀ witness :
      WZ1Lemma23NormalTiltWitness
        rho sigma eta C slope normal,
      witness.projectionRadius ≤
          Real.rpow rho (1 - 4 * eta / sigma) ∧
        |normal (1 : Fin 3) -
            slope witness.sliceHeight *
              normal (0 : Fin 3)| ≤ 1 / 10

/-- The normal-tilt statement for generalized witnesses. -/
def WZ1Lemma23NormalTiltStatementGeneralized : Prop :=
  ∀ (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) (normal : Point3),
    0 < rho → rho ≤ 1 →
    0 < sigma → sigma < 1 →
    0 < eta → 4 * eta < sigma →
    C ≠ ⊤ →
    C ≤ Kakeya.realRpowENN rho (-eta) →
    Real.rpow rho (1 - 4 * eta / sigma) ≤
      Real.sqrt rho / 14 →
    ∀ witness :
      WZ1Lemma23NormalTiltWitnessGeneralized
        rho sigma eta C slope normal,
      witness.projectionRadius ≤
          Real.rpow rho (1 - 4 * eta / sigma) ∧
        |normal (1 : Fin 3) -
            slope witness.sliceHeight *
              normal (0 : Fin 3)| ≤ 1 / 14

/--
Once the faithful Step 1 geometric leaf is supplied, the normal's first
horizontal component has the lower bound needed by the local graph extension.
-/
theorem wz1_lemma23_normal_first_component_from_tilt
    (hTilt : WZ1Lemma23NormalTiltStatement)
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) (normal : Point3)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 10)
    (witness :
      WZ1Lemma23NormalTiltWitness
        rho sigma eta C slope normal) :
    1 / 4 ≤ |normal (0 : Fin 3)| := by
  exact wz1_lemma23_normal_first_component
    normal (slope witness.sliceHeight)
    witness.normal_unit witness.normal_vertical
    witness.slope_small
    (hTilt rho sigma eta C slope normal
      hrho hrho_one hsigma hsigma_one
      heta heta_sigma hC hCpower habsorb witness).2

/--
The first-component consequence of the generalized normal-tilt statement.
-/
theorem wz1_lemma23_normal_first_component_from_tilt_generalized
    (hTilt : WZ1Lemma23NormalTiltStatementGeneralized)
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) (normal : Point3)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (witness :
      WZ1Lemma23NormalTiltWitnessGeneralized
        rho sigma eta C slope normal) :
    1 / 4 ≤ |normal (0 : Fin 3)| := by
  exact wz1_lemma23_normal_first_component_generalized
    normal (slope witness.sliceHeight)
    witness.normal_unit witness.normal_vertical
    witness.slope_small
    (hTilt rho sigma eta C slope normal
      hrho hrho_one hsigma hsigma_one
      heta heta_sigma hC hCpower habsorb witness).2

end

end Kakeya.Assouad

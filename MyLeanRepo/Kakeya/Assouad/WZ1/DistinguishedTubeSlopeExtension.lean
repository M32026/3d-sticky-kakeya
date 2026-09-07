import MyLeanRepo.Kakeya.Assouad.TubeBaseAlignment
import MyLeanRepo.Kakeya.Assouad.WZ1.NormalRatioSlopeExtension
import Mathlib.Tactic

/-!
# Slope extension from separated samples on a distinguished tube

Property (P) supplies actual shaded samples on one distinguished tube.  The
height used after anchored rescaling is the scalar coordinate along that
tube's direction.  This module converts spatial Lipschitz control of the
plane normal on separated genuine samples into a global normal-ratio slope.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The source height which becomes the third coordinate under anchored unit
rescaling about `tube`. -/
def distinguishedTubeHeight
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (point : Point3) : ℝ :=
  inner ℝ
    (point - (tube.base + (1 / 2 : ℝ) • tube.direction))
    tube.direction

/-- Two points in the same tube carrier are close once their genuine anchored
heights are close.  The additive `4 * delta` is the two endpoint/thickness
errors from decomposing both points against the unit axis segment. -/
lemma same_tube_dist_le_height_add_four_delta
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (tube : Kakeya.DeltaTube delta)
    {first second : Point3}
    (hfirst : first ∈ tube.carrier)
    (hsecond : second ∈ tube.carrier) :
    dist first second ≤
      |distinguishedTubeHeight tube first -
        distinguishedTubeHeight tube second| + 4 * delta := by
  rcases tube_carrier_decomp hdelta tube first hfirst with
    ⟨firstParameter, hfirstParameter, firstError,
      hfirstError, hfirstEq⟩
  rcases tube_carrier_decomp hdelta tube second hsecond with
    ⟨secondParameter, hsecondParameter, secondError,
      hsecondError, hsecondEq⟩
  have hfirstHeight :
      distinguishedTubeHeight tube first =
        firstParameter - 1 / 2 +
          inner ℝ firstError tube.direction := by
    rw [hfirstEq]
    simp only [distinguishedTubeHeight]
    have hvector :
        tube.base + firstParameter • tube.direction + firstError -
            (tube.base + (1 / 2 : ℝ) • tube.direction) =
          (firstParameter - 1 / 2) • tube.direction + firstError := by
      module
    rw [hvector, inner_add_left, inner_smul_left,
      real_inner_self_eq_norm_sq, tube.direction_unit]
    norm_num
  have hsecondHeight :
      distinguishedTubeHeight tube second =
        secondParameter - 1 / 2 +
          inner ℝ secondError tube.direction := by
    rw [hsecondEq]
    simp only [distinguishedTubeHeight]
    have hvector :
        tube.base + secondParameter • tube.direction + secondError -
            (tube.base + (1 / 2 : ℝ) • tube.direction) =
          (secondParameter - 1 / 2) • tube.direction + secondError := by
      module
    rw [hvector, inner_add_left, inner_smul_left,
      real_inner_self_eq_norm_sq, tube.direction_unit]
    norm_num
  have hfirstInner :
      |inner ℝ firstError tube.direction| ≤ delta := by
    calc
      |inner ℝ firstError tube.direction|
          ≤ ‖firstError‖ * ‖tube.direction‖ :=
        abs_real_inner_le_norm firstError tube.direction
      _ = ‖firstError‖ := by rw [tube.direction_unit, mul_one]
      _ ≤ delta := hfirstError
  have hsecondInner :
      |inner ℝ secondError tube.direction| ≤ delta := by
    calc
      |inner ℝ secondError tube.direction|
          ≤ ‖secondError‖ * ‖tube.direction‖ :=
        abs_real_inner_le_norm secondError tube.direction
      _ = ‖secondError‖ := by rw [tube.direction_unit, mul_one]
      _ ≤ delta := hsecondError
  have hparameter :
      |firstParameter - secondParameter| ≤
        |distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube second| + 2 * delta := by
    have halgebra :
        firstParameter - secondParameter =
          (distinguishedTubeHeight tube first -
            distinguishedTubeHeight tube second) -
          inner ℝ firstError tube.direction +
          inner ℝ secondError tube.direction := by
      rw [hfirstHeight, hsecondHeight]
      ring
    rw [halgebra]
    calc
      |(distinguishedTubeHeight tube first -
            distinguishedTubeHeight tube second) -
          inner ℝ firstError tube.direction +
          inner ℝ secondError tube.direction|
          ≤ |distinguishedTubeHeight tube first -
                distinguishedTubeHeight tube second| +
              |inner ℝ firstError tube.direction| +
              |inner ℝ secondError tube.direction| := by
            calc
              |(distinguishedTubeHeight tube first -
                    distinguishedTubeHeight tube second) -
                  inner ℝ firstError tube.direction +
                  inner ℝ secondError tube.direction|
                  ≤ |(distinguishedTubeHeight tube first -
                        distinguishedTubeHeight tube second) -
                      inner ℝ firstError tube.direction| +
                    |inner ℝ secondError tube.direction| :=
                abs_add_le _ _
              _ ≤ (|distinguishedTubeHeight tube first -
                        distinguishedTubeHeight tube second| +
                      |inner ℝ firstError tube.direction|) +
                    |inner ℝ secondError tube.direction| := by
                gcongr
                exact abs_sub _ _
      _ ≤ |distinguishedTubeHeight tube first -
              distinguishedTubeHeight tube second| +
            delta + delta := by
          linarith
      _ = |distinguishedTubeHeight tube first -
              distinguishedTubeHeight tube second| + 2 * delta := by ring
  have hpointDifference :
      first - second =
        (firstParameter - secondParameter) • tube.direction +
          (firstError - secondError) := by
    rw [hfirstEq, hsecondEq]
    module
  rw [dist_eq_norm, hpointDifference]
  calc
    ‖(firstParameter - secondParameter) • tube.direction +
          (firstError - secondError)‖
        ≤ ‖(firstParameter - secondParameter) • tube.direction‖ +
            ‖firstError - secondError‖ := norm_add_le _ _
    _ = |firstParameter - secondParameter| +
          ‖firstError - secondError‖ := by
        rw [norm_smul, Real.norm_eq_abs, tube.direction_unit, mul_one]
    _ ≤ |firstParameter - secondParameter| +
          (‖firstError‖ + ‖secondError‖) := by
        gcongr
        exact norm_sub_le firstError secondError
    _ ≤ (|distinguishedTubeHeight tube first -
            distinguishedTubeHeight tube second| + 2 * delta) +
          (delta + delta) := by gcongr
    _ = |distinguishedTubeHeight tube first -
            distinguishedTubeHeight tube second| + 4 * delta := by ring

/--
Extend the genuine normal-ratio slope sampled on a distinguished tube.

The samples have their exact anchored heights and are separated at the tube
thickness scale.  Thus the additive carrier error is absorbed into the height
distance.  No value of the slope is chosen independently: on every retained
height the output is exactly the coordinate ratio of `planeNormal` at the
corresponding actual shaded sample.
-/
theorem distinguished_tube_normal_ratio_slope_extension
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (tube : Kakeya.DeltaTube delta)
    {heights : Set ℝ} (sample : ℝ → Point3)
    (hsample_carrier : ∀ z ∈ heights, sample z ∈ tube.carrier)
    (hsample_height :
      ∀ z ∈ heights, distinguishedTubeHeight tube (sample z) = z)
    (hheight_separated :
      ∀ first ∈ heights, ∀ second ∈ heights,
        first ≠ second → 4 * delta ≤ |first - second|)
    (planeNormal : Point3 → Point3) (K : NNReal)
    (hplane_lipschitz : LipschitzOnWith K planeNormal tube.carrier)
    (hplane_unit :
      ∀ z ∈ heights, ‖planeNormal (sample z)‖ = 1)
    (hplane_transverse :
      ∀ z ∈ heights,
        1 / 3 ≤ |planeNormal (sample z) (0 : Fin 3)|) :
    ∃ slope : ℝ → ℝ,
      LipschitzWith (24 * K) slope ∧
      (∀ z, |slope z| ≤ 3) ∧
      Set.EqOn
        (fun z =>
          planeNormal (sample z) (1 : Fin 3) /
            planeNormal (sample z) (0 : Fin 3))
        slope heights := by
  let sampledNormal : ℝ → Point3 := fun z => planeNormal (sample z)
  have hsampled_lipschitz :
      LipschitzOnWith (2 * K) sampledNormal heights := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    by_cases heq : first = second
    · subst second
      simp
    · have hdistance :=
        same_tube_dist_le_height_add_four_delta
          hdelta tube (hsample_carrier first hfirst)
            (hsample_carrier second hsecond)
      rw [hsample_height first hfirst,
        hsample_height second hsecond] at hdistance
      have hseparation :=
        hheight_separated first hfirst second hsecond heq
      have hsampleDistance :
          dist (sample first) (sample second) ≤
            2 * dist first second := by
        rw [Real.dist_eq]
        linarith
      have hnormalDistance :
          dist (planeNormal (sample first))
              (planeNormal (sample second)) ≤
            (K : ℝ) * dist (sample first) (sample second) :=
        hplane_lipschitz.dist_le_mul
          (sample first) (hsample_carrier first hfirst)
          (sample second) (hsample_carrier second hsecond)
      change dist (sampledNormal first) (sampledNormal second) ≤
        ((2 * K : NNReal) : ℝ) * dist first second
      calc
        dist (sampledNormal first) (sampledNormal second)
            ≤ (K : ℝ) * dist (sample first) (sample second) :=
          hnormalDistance
        _ ≤ (K : ℝ) * (2 * dist first second) := by gcongr
        _ = (2 * (K : ℝ)) * dist first second := by ring
  rcases normal_ratio_slope_extension
      (normal := sampledNormal)
      (hnormal_unit := hplane_unit)
      (hnormal_transverse := hplane_transverse)
      hsampled_lipschitz with
    ⟨slope, hslope, hslopeBound, hslopeEq⟩
  refine ⟨slope, ?_, hslopeBound, hslopeEq⟩
  have hconstant : (12 : NNReal) * (2 * K) = 24 * K := by
    ext
    push_cast
    ring
  rwa [hconstant] at hslope

/--
Approximate-height version used by the literal Property-(P) interface.  A
sample need not occur at the center of its labelled grid layer.  The error is
tracked explicitly and absorbed by separating retained layer labels by at
least `4 * delta + 2 * heightError`.
-/
theorem distinguished_tube_approximate_normal_ratio_slope_extension
    {delta heightError : ℝ} (hdelta : 0 ≤ delta)
    (hheightError : 0 ≤ heightError)
    (tube : Kakeya.DeltaTube delta)
    {heights : Set ℝ} (sample : ℝ → Point3)
    (hsample_carrier : ∀ z ∈ heights, sample z ∈ tube.carrier)
    (hsample_height :
      ∀ z ∈ heights,
        |distinguishedTubeHeight tube (sample z) - z| ≤ heightError)
    (hheight_separated :
      ∀ first ∈ heights, ∀ second ∈ heights,
        first ≠ second →
          4 * delta + 2 * heightError ≤ |first - second|)
    (planeNormal : Point3 → Point3) (K : NNReal)
    (hplane_lipschitz : LipschitzOnWith K planeNormal tube.carrier)
    (hplane_unit :
      ∀ z ∈ heights, ‖planeNormal (sample z)‖ = 1)
    (hplane_transverse :
      ∀ z ∈ heights,
        1 / 3 ≤ |planeNormal (sample z) (0 : Fin 3)|) :
    ∃ slope : ℝ → ℝ,
      LipschitzWith (24 * K) slope ∧
      (∀ z, |slope z| ≤ 3) ∧
      Set.EqOn
        (fun z =>
          planeNormal (sample z) (1 : Fin 3) /
            planeNormal (sample z) (0 : Fin 3))
        slope heights := by
  let sampledNormal : ℝ → Point3 := fun z => planeNormal (sample z)
  have hsampled_lipschitz :
      LipschitzOnWith (2 * K) sampledNormal heights := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    by_cases heq : first = second
    · subst second
      simp
    · have hdistance :=
        same_tube_dist_le_height_add_four_delta
          hdelta tube (hsample_carrier first hfirst)
            (hsample_carrier second hsecond)
      have hfirstError := hsample_height first hfirst
      have hsecondError := hsample_height second hsecond
      have hheightDifference :
          |distinguishedTubeHeight tube (sample first) -
              distinguishedTubeHeight tube (sample second)| ≤
            |first - second| + 2 * heightError := by
        calc
          |distinguishedTubeHeight tube (sample first) -
              distinguishedTubeHeight tube (sample second)|
              = |(distinguishedTubeHeight tube (sample first) - first) +
                  (first - second) +
                  (second -
                    distinguishedTubeHeight tube (sample second))| := by
                congr 1
                ring
          _ ≤ |distinguishedTubeHeight tube (sample first) - first| +
                |first - second| +
                |second -
                  distinguishedTubeHeight tube (sample second)| := by
              have houter := abs_add_le
                ((distinguishedTubeHeight tube (sample first) - first) +
                  (first - second))
                (second - distinguishedTubeHeight tube (sample second))
              have hinner := abs_add_le
                (distinguishedTubeHeight tube (sample first) - first)
                (first - second)
              linarith
          _ ≤ heightError + |first - second| + heightError := by
              have hsecondError' :
                  |second - distinguishedTubeHeight tube (sample second)| ≤
                    heightError := by
                rw [abs_sub_comm]
                exact hsecondError
              linarith
          _ = |first - second| + 2 * heightError := by ring
      have hseparation :=
        hheight_separated first hfirst second hsecond heq
      have hsampleDistance :
          dist (sample first) (sample second) ≤
            2 * dist first second := by
        rw [Real.dist_eq]
        calc
          dist (sample first) (sample second)
              ≤ |distinguishedTubeHeight tube (sample first) -
                    distinguishedTubeHeight tube (sample second)| +
                  4 * delta := hdistance
          _ ≤ (|first - second| + 2 * heightError) +
                4 * delta := by gcongr
          _ ≤ 2 * |first - second| := by linarith
      have hnormalDistance :
          dist (planeNormal (sample first))
              (planeNormal (sample second)) ≤
            (K : ℝ) * dist (sample first) (sample second) :=
        hplane_lipschitz.dist_le_mul
          (sample first) (hsample_carrier first hfirst)
          (sample second) (hsample_carrier second hsecond)
      change dist (sampledNormal first) (sampledNormal second) ≤
        ((2 * K : NNReal) : ℝ) * dist first second
      calc
        dist (sampledNormal first) (sampledNormal second)
            ≤ (K : ℝ) * dist (sample first) (sample second) :=
          hnormalDistance
        _ ≤ (K : ℝ) * (2 * dist first second) := by gcongr
        _ = (2 * (K : ℝ)) * dist first second := by ring
  rcases normal_ratio_slope_extension
      (normal := sampledNormal)
      (hnormal_unit := hplane_unit)
      (hnormal_transverse := hplane_transverse)
      hsampled_lipschitz with
    ⟨slope, hslope, hslopeBound, hslopeEq⟩
  refine ⟨slope, ?_, hslopeBound, hslopeEq⟩
  have hconstant : (12 : NNReal) * (2 * K) = 24 * K := by
    ext
    push_cast
    ring
  rwa [hconstant] at hslope

end Kakeya.Assouad

end

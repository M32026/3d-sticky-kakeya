import MyLeanRepo.Kakeya.CV.PolynomialCylinder.SinglePatchEquality
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphPatchIntegralMeasurability
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.FamilyMeasurability
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Measurability of a single graph-patch contribution

This module constructs a measurable extension of one regular graph patch and
uses `single_patch_equality` to identify its Hausdorff contribution with a
coefficient-wise measurable Lebesgue integral.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real Classical

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

lemma continuousOn_open_indicator_measurable
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {s : Set α} (hs : IsOpen s)
    {f : α → ℝ} (hf : ContinuousOn f s) :
    Measurable (s.indicator f) :=
  hf.measurable_piecewise continuousOn_const hs.measurableSet

lemma dirGraphMap_const_continuous (dir : Fin 3) :
    Continuous
      (fun q : ℝ × Point 2 =>
        dirGraphMap dir (fun _ => q.1) q.2) := by
  have hvec :
      Continuous (fun q : ℝ × Point 2 => ![q.2 0, q.2 1, q.1]) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
        continuous_snd
    · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
        continuous_snd
    · exact continuous_fst
  have hgraph :
      Continuous
        (fun q : ℝ × Point 2 =>
          graphMap (fun _ => q.1) q.2) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
      hvec
  fin_cases dir
  · exact (swapCoords 0 2).continuous.comp hgraph
  · exact (swapCoords 1 2).continuous.comp hgraph
  · exact hgraph

lemma dirGraphMap_congr_at
    (dir : Fin 3) {f f' : Point 2 → ℝ} {y : Point 2}
    (h : f y = f' y) :
    dirGraphMap dir f y = dirGraphMap dir f' y := by
  fin_cases dir <;>
    simp [dirGraphMap, xGraphMap, yGraphMap, graphMap, h]

def coverPatchDomain (patch : CoverPatch k P) :
    Set (CoefficientSpace P.dim × Point 2) :=
  patch.V ×ˢ patch.A

def coverPatchExtendedHeight (patch : CoverPatch k P) :
    CoefficientSpace P.dim × Point 2 → ℝ :=
  (coverPatchDomain patch).indicator (fun p => patch.g p.1 p.2)

def coverPatchGraphPoint
    (patch : CoverPatch k P)
    (x : CoefficientSpace P.dim) (y : Point 2) : Point 3 :=
  dirGraphMap patch.dir
    (fun _ => coverPatchExtendedHeight patch (x, y)) y

def coverPatchDirectionalFactor
    (patch : CoverPatch k P) (u : Point 3)
    (x : CoefficientSpace P.dim) (y : Point 2) : ℝ :=
  let grad :=
    polynomialGradient (parameterPolynomial P x)
      (coverPatchGraphPoint patch x y)
  ‖inner ℝ u grad‖ / |grad patch.dir|

def coverPatchBaseDomain
    (patch : CoverPatch k P)
    (D : Set (CoefficientSpace P.dim × Point 3)) :
    Set (CoefficientSpace P.dim × Point 2) :=
  {p | (p.1, coverPatchGraphPoint patch p.1 p.2) ∈ D}

lemma coverPatchExtendedHeight_measurable (patch : CoverPatch k P) :
    Measurable (coverPatchExtendedHeight patch) := by
  exact continuousOn_open_indicator_measurable
    (patch.hV_open.prod patch.hA_open)
    patch.hg_smooth.continuousOn

lemma coverPatchGraphPoint_measurable (patch : CoverPatch k P) :
    Measurable
      (fun p : CoefficientSpace P.dim × Point 2 =>
        coverPatchGraphPoint patch p.1 p.2) := by
  have hpair :
      Measurable
        (fun p : CoefficientSpace P.dim × Point 2 =>
          (coverPatchExtendedHeight patch p, p.2)) :=
    (coverPatchExtendedHeight_measurable patch).prodMk measurable_snd
  exact (dirGraphMap_const_continuous patch.dir).measurable.comp hpair

lemma coverPatchDirectionalFactor_measurable
    (patch : CoverPatch k P) (u : Point 3) :
    Measurable
      (fun p : CoefficientSpace P.dim × Point 2 =>
        coverPatchDirectionalFactor patch u p.1 p.2) := by
  let jointGraph :
      CoefficientSpace P.dim × Point 2 →
        CoefficientSpace P.dim × Point 3 :=
    fun p => (p.1, coverPatchGraphPoint patch p.1 p.2)
  have hjoint : Measurable jointGraph :=
    measurable_fst.prodMk (coverPatchGraphPoint_measurable patch)
  have hgrad :
      Measurable
        (fun p : CoefficientSpace P.dim × Point 2 =>
          polynomialGradient (parameterPolynomial P p.1)
            (coverPatchGraphPoint patch p.1 p.2)) := by
    change Measurable
      ((fun q : CoefficientSpace P.dim × Point 3 =>
        polynomialGradient (parameterPolynomial P q.1) q.2) ∘ jointGraph)
    exact family_polynomialGradient_continuous.measurable.comp hjoint
  exact (measurable_const.inner hgrad).norm.div
    (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) patch.dir).measurable.comp
      hgrad).norm)

lemma coverPatchBaseDomain_measurable
    (patch : CoverPatch k P)
    {D : Set (CoefficientSpace P.dim × Point 3)}
    (hD : MeasurableSet D) :
    MeasurableSet (coverPatchBaseDomain patch D) := by
  exact hD.preimage
    (measurable_fst.prodMk (coverPatchGraphPoint_measurable patch))

lemma coverPatchGraphPoint_eq
    (patch : CoverPatch k P)
    {x : CoefficientSpace P.dim} {y : Point 2}
    (hx : x ∈ patch.V) (hy : y ∈ patch.A) :
    coverPatchGraphPoint patch x y =
      dirGraphMap patch.dir (patch.g x) y := by
  apply dirGraphMap_congr_at
  simp [coverPatchExtendedHeight, coverPatchDomain, hx, hy]

/-- The Hausdorff contribution of a measurable subset of one graph patch is
measurable in the polynomial coefficients. -/
lemma single_patch_contribution_measurable
    (patch : CoverPatch k P)
    {U : Set (Point 3)} (hU : MeasurableSet U)
    (u : Point 3)
    (D : Set (CoefficientSpace P.dim × Point 3))
    (hD : MeasurableSet D)
    (hD_sub : D ⊆ coverPatchImage patch) :
    Measurable (fun x : CoefficientSpace P.dim =>
      ∫⁻ z : Point 3,
        {z : Point 3 | (x, z) ∈ D}.indicator
            (1 : Point 3 → ENNReal) z *
          U.indicator (1 : Point 3 → ENNReal) z *
          ENNReal.ofReal ‖inner ℝ u
            (polynomialUnitNormal (parameterPolynomial P x) z)‖
      ∂μH[2]) := by
  let F : CoefficientSpace P.dim × Point 3 → ENNReal := fun p =>
    ENNReal.ofReal ‖inner ℝ u
      (polynomialUnitNormal (parameterPolynomial P p.1) p.2)‖
  have hF_meas : Measurable F := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.inner family_polynomialUnitNormal_measurable).norm
  let graphPoint := coverPatchGraphPoint patch
  have hgraph :
      Measurable
        (fun p : CoefficientSpace P.dim × Point 2 =>
          graphPoint p.1 p.2) :=
    coverPatchGraphPoint_measurable patch
  let directionalFactor := coverPatchDirectionalFactor patch u
  have hfactor :
      Measurable
        (fun p : CoefficientSpace P.dim × Point 2 =>
          directionalFactor p.1 p.2) :=
    coverPatchDirectionalFactor_measurable patch u
  have hfactor_nonneg :
      ∀ x y, 0 ≤ directionalFactor x y := by
    intro x y
    exact div_nonneg (norm_nonneg _) (abs_nonneg _)
  have hfactor_eq :
      ∀ x ∈ patch.V, ∀ y ∈ patch.A,
        directionalFactor x y =
          ‖inner ℝ u (polynomialGradient (parameterPolynomial P x)
            (dirGraphMap patch.dir (patch.g x) y))‖ /
          |(polynomialGradient (parameterPolynomial P x)
            (dirGraphMap patch.dir (patch.g x) y)) patch.dir| := by
    intro x hx y hy
    simp only [directionalFactor, coverPatchDirectionalFactor]
    rw [coverPatchGraphPoint_eq patch hx hy]
  let B_set := coverPatchBaseDomain patch D
  have hB_set : MeasurableSet B_set :=
    coverPatchBaseDomain_measurable patch hD
  have hvol :
      Measurable (fun x : CoefficientSpace P.dim =>
        ∫⁻ y : Point 2,
          B_set.indicator (fun _ => (1 : ENNReal)) (x, y) *
            U.indicator (fun _ => (1 : ENNReal)) (graphPoint x y) *
            ENNReal.ofReal |directionalFactor x y| ∂volume) :=
    graph_patch_integral_measurable_general
      hB_set graphPoint hgraph directionalFactor hfactor hU
  have hgraph_form :
      ∀ x y, ∃ f : Point 2 → ℝ,
        graphPoint x y = dirGraphMap patch.dir f y := by
    intro x y
    exact ⟨fun _ => coverPatchExtendedHeight patch (x, y), rfl⟩
  have hagree :
      ∀ p ∈ patch.V ×ˢ patch.A,
        graphPoint p.1 p.2 =
          dirGraphMap patch.dir (patch.g p.1) p.2 := by
    intro p hp
    exact coverPatchGraphPoint_eq patch hp.1 hp.2
  have heq := single_patch_equality
    patch hU u D hD hD_sub F hF_meas
    (fun _ _ => rfl)
    graphPoint hgraph
    directionalFactor hfactor_nonneg hfactor_eq
    B_set rfl hgraph_form hagree
  have hfun :
      (fun x : CoefficientSpace P.dim =>
        ∫⁻ z : Point 3,
          {z : Point 3 | (x, z) ∈ D}.indicator
              (1 : Point 3 → ENNReal) z *
            U.indicator (1 : Point 3 → ENNReal) z *
            F (x, z) ∂μH[2]) =
      (fun x : CoefficientSpace P.dim =>
        planeConstant * (∫⁻ y : Point 2,
          B_set.indicator (fun _ => (1 : ENNReal)) (x, y) *
            U.indicator (fun _ => (1 : ENNReal)) (graphPoint x y) *
            ENNReal.ofReal |directionalFactor x y| ∂volume)) := by
    funext x
    exact heq x
  change Measurable (fun x : CoefficientSpace P.dim =>
    ∫⁻ z : Point 3,
      {z : Point 3 | (x, z) ∈ D}.indicator
          (1 : Point 3 → ENNReal) z *
        U.indicator (1 : Point 3 → ENNReal) z *
        F (x, z) ∂μH[2])
  rw [hfun]
  exact hvol.const_mul planeConstant

end Kakeya.CV

import MyLeanRepo.Kakeya.CV.PolynomialMollification
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Coefficient measurability of graph-patch integrals

Joint measurability of a graph parameterization, a directional factor, and
the patch domain implies measurability of the corresponding coefficient-wise
Lebesgue integral. The same argument applies after disjointifying a countable
family by finite prefixes.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

/-- A jointly measurable graph-patch integrand has a measurable
coefficient-wise integral. -/
lemma graph_patch_integral_measurable_general
    {D : Set (CoefficientSpace P.dim × Point 2)}
    (hD : MeasurableSet D)
    (graphPoint : CoefficientSpace P.dim → Point 2 → Point 3)
    (hgraph : Measurable
      (fun p : CoefficientSpace P.dim × Point 2 => graphPoint p.1 p.2))
    (directionalFactor : CoefficientSpace P.dim → Point 2 → ℝ)
    (hfactor : Measurable
      (fun p : CoefficientSpace P.dim × Point 2 =>
        directionalFactor p.1 p.2))
    {U : Set (Point 3)} (hU : MeasurableSet U) :
    Measurable (fun x : CoefficientSpace P.dim =>
      ∫⁻ y : Point 2,
        D.indicator
            (fun _ : CoefficientSpace P.dim × Point 2 => (1 : ENNReal))
            (x, y) *
          U.indicator (fun _ : Point 3 => (1 : ENNReal))
            (graphPoint x y) *
          ENNReal.ofReal |directionalFactor x y| ∂volume) := by
  let integrand : CoefficientSpace P.dim × Point 2 → ENNReal := fun p =>
    D.indicator
        (fun _ : CoefficientSpace P.dim × Point 2 => (1 : ENNReal)) p *
      U.indicator (fun _ : Point 3 => (1 : ENNReal))
        (graphPoint p.1 p.2) *
      ENNReal.ofReal |directionalFactor p.1 p.2|
  have hintegrand : Measurable integrand := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact measurable_const.indicator hD
      · exact measurable_const.indicator (hU.preimage hgraph)
    · exact ENNReal.measurable_ofReal.comp (hfactor.norm)
  have hsection : Measurable (fun x : CoefficientSpace P.dim =>
      ∫⁻ y : Point 2, integrand (x, y) ∂volume) :=
    hintegrand.lintegral_prod_right'
  simpa [integrand] using hsection

/-- The coefficient-wise contribution of the `n`-th patch remains measurable
after removing all earlier measurable patch images. -/
lemma disjointified_patch_integral_measurable
    (W : ℕ → Set (CoefficientSpace P.dim × Point 3))
    (hW : ∀ n, MeasurableSet (W n))
    (graphPoint : ℕ → CoefficientSpace P.dim → Point 2 → Point 3)
    (hgraph : ∀ n, Measurable
      (fun p : CoefficientSpace P.dim × Point 2 =>
        graphPoint n p.1 p.2))
    (directionalFactor : ℕ → CoefficientSpace P.dim → Point 2 → ℝ)
    (hfactor : ∀ n, Measurable
      (fun p : CoefficientSpace P.dim × Point 2 =>
        directionalFactor n p.1 p.2))
    {U : Set (Point 3)} (hU : MeasurableSet U)
    (n : ℕ) :
    Measurable (fun x : CoefficientSpace P.dim =>
      ∫⁻ y : Point 2,
        {p : CoefficientSpace P.dim × Point 2 |
            (p.1, graphPoint n p.1 p.2) ∈
              W n \ ⋃ m ∈ Finset.range n, W m}.indicator
            (fun _ : CoefficientSpace P.dim × Point 2 => (1 : ENNReal))
            (x, y) *
          U.indicator (fun _ : Point 3 => (1 : ENNReal))
            (graphPoint n x y) *
          ENNReal.ofReal |directionalFactor n x y| ∂volume) := by
  let previous : Set (CoefficientSpace P.dim × Point 3) :=
    ⋃ m ∈ Finset.range n, W m
  have hprevious : MeasurableSet previous := by
    apply MeasurableSet.biUnion
      (Finset.countable_toSet (Finset.range n))
    intro m _
    exact hW m
  let disjointPatch : Set (CoefficientSpace P.dim × Point 3) :=
    W n \ previous
  have hdisjointPatch : MeasurableSet disjointPatch :=
    (hW n).diff hprevious
  let jointGraph :
      CoefficientSpace P.dim × Point 2 →
        CoefficientSpace P.dim × Point 3 :=
    fun p => (p.1, graphPoint n p.1 p.2)
  have hjointGraph : Measurable jointGraph :=
    measurable_fst.prodMk (hgraph n)
  let domain : Set (CoefficientSpace P.dim × Point 2) :=
    jointGraph ⁻¹' disjointPatch
  have hdomain : MeasurableSet domain :=
    hdisjointPatch.preimage hjointGraph
  have hdomain_eq :
      domain =
        {p : CoefficientSpace P.dim × Point 2 |
          (p.1, graphPoint n p.1 p.2) ∈
            W n \ ⋃ m ∈ Finset.range n, W m} := by
    ext p
    simp [domain, jointGraph, disjointPatch, previous]
  rw [← hdomain_eq]
  exact graph_patch_integral_measurable_general hdomain
    (graphPoint n) (hgraph n)
    (directionalFactor n) (hfactor n) hU

/-- A countable sum of measurable `ENNReal`-valued patch contributions is
measurable. -/
lemma graph_patch_tsum_measurable
    {f : ℕ → CoefficientSpace P.dim → ENNReal}
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ∑' n, f n x) :=
  Measurable.tsum hf

end Kakeya.CV

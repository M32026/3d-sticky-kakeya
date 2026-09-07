import MyLeanRepo.Kakeya.CV.FiniteBisectionStability
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform stability on the normalized coefficient sphere

For each region, the exact-bisector locus on the normalized coefficient sphere
is compact.  Pointwise finite-bisection stability gives it an open
neighborhood of 40/40 cuts; compactness supplies a uniform thickening radius.
Taking the minimum over a finite region family gives one global radius.
-/

noncomputable section

open MeasureTheory Set Filter

namespace Kakeya.CV

lemma parameterPolynomial_ne_zero_of_normalized
    {k : ℕ} {P : PolynomialParameterization k}
    {x : CoefficientSpace P.dim}
    (hx : x ∈ normalizedPolynomialParameters P) :
    parameterPolynomial P x ≠ 0 := by
  intro hp
  have hsub : P.equiv x = 0 := by
    apply Subtype.ext
    exact hp
  have hx0 : x = 0 := P.equiv.injective (by simpa using hsub)
  have hnorm : ‖x‖ = 1 := by
    simpa [normalizedPolynomialParameters, Metric.mem_sphere] using hx
  rw [hx0] at hnorm
  norm_num at hnorm

theorem uniform_finite_bisections_stable :
    UniformFiniteBisectionStabilityStatement := by
  intro k P ι _ regions hmeas hfin
  let Bisect : ι → Set (CoefficientSpace P.dim) := fun i =>
    {x | x ∈ normalizedPolynomialParameters P ∧
      PolynomialBisects (parameterPolynomial P x) (regions i)}
  have hBisect_closed : ∀ i, IsClosed (Bisect i) := by
    intro i
    apply IsSeqClosed.isClosed
    intro xseq x hxseq hxlim
    have hsphere_closed :
        IsClosed (normalizedPolynomialParameters P) := by
      exact Metric.isClosed_sphere
    have hxnorm : x ∈ normalizedPolynomialParameters P :=
      hsphere_closed.mem_of_tendsto hxlim
        (Filter.Eventually.of_forall fun n => (hxseq n).1)
    have hp : parameterPolynomial P x ≠ 0 :=
      parameterPolynomial_ne_zero_of_normalized hxnorm
    have hpos := vpos_seq_continuous P (regions i) (hmeas i) (hfin i) x hp xseq hxlim
    have hneg := vneg_seq_continuous P (regions i) (hmeas i) (hfin i) x hp xseq hxlim
    have hneg_to_pos :
        Filter.Tendsto
          (fun m => volume
            (regions i ∩
              {z : Point 3 | polynomialValue (parameterPolynomial P (xseq m)) z < 0}))
          Filter.atTop
          (nhds (volume
            (regions i ∩
              {z : Point 3 | 0 < polynomialValue (parameterPolynomial P x) z}))) := by
      apply hpos.congr'
      filter_upwards with m
      exact (hxseq m).2.symm
    have hlimit :
        volume
            (regions i ∩
              {z : Point 3 | polynomialValue (parameterPolynomial P x) z < 0}) =
          volume
            (regions i ∩
              {z : Point 3 | 0 < polynomialValue (parameterPolynomial P x) z}) :=
      tendsto_nhds_unique hneg hneg_to_pos
    exact ⟨hxnorm, hlimit⟩
  have hBisect_compact : ∀ i, IsCompact (Bisect i) := by
    intro i
    exact (isCompact_sphere (0 : CoefficientSpace P.dim) 1).of_isClosed_subset
      (hBisect_closed i) (fun _ hx => hx.1)
  let τ : ENNReal := (2 : ENNReal) / 5
  have hlocal : ∀ i, ∀ x ∈ Bisect i,
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ Metric.ball x δ,
          PolynomialCutsAtLeast (parameterPolynomial P y) (regions i) τ := by
    intro i x hx
    have hp : parameterPolynomial P x ≠ 0 :=
      parameterPolynomial_ne_zero_of_normalized hx.1
    rcases finite_bisections_stable_under_coefficient_perturbation
      k P ι (fun _ => regions i) x hp
      (fun _ => hmeas i) (fun _ => hfin i) (fun _ => hx.2) with
      ⟨δ, hδ, hstable⟩
    exact ⟨δ, hδ, fun y hy => hstable y hy i⟩
  choose radius hradius_pos hstable using hlocal
  let Good : ι → Set (CoefficientSpace P.dim) := fun i =>
    ⋃ x : {x // x ∈ Bisect i}, Metric.ball x.1 (radius i x.1 x.2)
  have hGood_open : ∀ i, IsOpen (Good i) := by
    intro i
    exact isOpen_iUnion fun x => Metric.isOpen_ball
  have hBisect_subset_Good : ∀ i, Bisect i ⊆ Good i := by
    intro i x hx
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩, Metric.mem_ball_self (hradius_pos i x hx)⟩
  have huniform : ∀ i, ∃ δ : ℝ, 0 < δ ∧
      Metric.thickening δ (Bisect i) ⊆ Good i := by
    intro i
    exact (hBisect_compact i).exists_thickening_subset_open
      (hGood_open i) (hBisect_subset_Good i)
  choose δ hδ_pos hδ_subset using huniform
  by_cases h_univ_nonempty : (Finset.univ : Finset ι).Nonempty
  · obtain ⟨i0, _, hmin⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ι) δ h_univ_nonempty
    let δ0 := δ i0
    have hδ0_pos : 0 < δ0 := hδ_pos i0
    refine ⟨δ0, hδ0_pos, ?_⟩
    intro x hxnorm y hy i hbisect
    have hxB : x ∈ Bisect i := ⟨hxnorm, hbisect⟩
    have hδ0_le : δ0 ≤ δ i := hmin i (Finset.mem_univ i)
    have hy_thick : y ∈ Metric.thickening (δ i) (Bisect i) := by
      rw [Metric.mem_thickening_iff]
      exact ⟨x, hxB, hy.trans_le hδ0_le⟩
    have hy_good : y ∈ Good i := hδ_subset i hy_thick
    rcases Set.mem_iUnion.mp hy_good with ⟨z, hyz⟩
    simpa [τ] using hstable i z.1 z.2 y hyz
  · refine ⟨1, by norm_num, ?_⟩
    intro _ _ _ _ i
    exact False.elim (h_univ_nonempty ⟨i, Finset.mem_univ i⟩)

end Kakeya.CV

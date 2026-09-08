import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalRelationExactProfileIdentity
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ScaleChains

/-!
# Reference-density telescope reduced to coherent cardinality branching

For a represented conditional relation,

```text
referenceDensity
  = relationCardinality
      * tubeVolume(fine) / dilatedParentVolume(coarse).
```

Along an arbitrary grid subchain, the scale-only factors telescope without
loss: each intermediate tube volume cancels, while every edge contributes
one copy of the fixed parent-dilation volume.  Since that dilation factor is
at least one, the product of edge scale factors is bounded by the whole-chain
scale factor.

Consequently the remaining v5 producer obligation is purely combinatorial:
the product of the edge maximum relation cardinalities must be controlled by
the whole-chain minimum relation cardinality.  This module proves that such a
cardinality telescope is sufficient for the reference-density telescope.  It
does not assert that the existing independent conditional covers provide the
required coherent branching identity.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

private lemma adjacent_ratio_product_range
    (value : ℕ → ENNReal)
    (constant : ENNReal)
    (hvalueZero : ∀ k, value k ≠ 0)
    (hvalueTop : ∀ k, value k ≠ ⊤)
    (hconstantZero : constant ≠ 0)
    (hconstantTop : constant ≠ ⊤) :
    ∀ n : ℕ,
      (∏ k ∈ Finset.range n,
          value (k + 1) / (constant * value k)) =
        value n / (constant ^ n * value 0) := by
  intro n
  induction n with
  | zero =>
      simp [ENNReal.div_self (hvalueZero 0) (hvalueTop 0)]
  | succ n inductionHypothesis =>
      rw [Finset.prod_range_succ, inductionHypothesis]
      apply (ENNReal.toReal_eq_toReal_iff'
        (ENNReal.mul_ne_top
          (ENNReal.div_ne_top (hvalueTop n)
            (mul_ne_zero (pow_ne_zero _ hconstantZero) (hvalueZero 0)))
          (ENNReal.div_ne_top (hvalueTop (n + 1))
            (mul_ne_zero hconstantZero (hvalueZero n))))
        (ENNReal.div_ne_top (hvalueTop (n + 1))
          (mul_ne_zero
            (pow_ne_zero _ hconstantZero) (hvalueZero 0)))).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
        ENNReal.toReal_pow]
      have hvalueReal : ∀ k, (value k).toReal ≠ 0 :=
        fun k => ENNReal.toReal_ne_zero.mpr
          ⟨hvalueZero k, hvalueTop k⟩
      have hconstantReal : constant.toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr
          ⟨hconstantZero, hconstantTop⟩
      rw [pow_succ]
      field_simp [hvalueReal n, hvalueReal 0,
        hconstantReal]

private lemma adjacent_ratio_product
    (value : ℕ → ENNReal)
    (constant : ENNReal)
    (hvalueZero : ∀ k, value k ≠ 0)
    (hvalueTop : ∀ k, value k ≠ ⊤)
    (hconstantZero : constant ≠ 0)
    (hconstantTop : constant ≠ ⊤)
    (n : ℕ) :
    (∏ k : Fin n,
        value (k.val + 1) / (constant * value k.val)) =
      value n / (constant ^ n * value 0) := by
  rw [show
    (∏ k : Fin n,
        value (k.val + 1) / (constant * value k.val)) =
      ∏ k ∈ Finset.range n,
        value (k + 1) / (constant * value k) by
      simpa using Fin.prod_univ_eq_prod_range
        (fun k => value (k + 1) / (constant * value k)) n]
  exact adjacent_ratio_product_range
    value constant hvalueZero hvalueTop hconstantZero hconstantTop n

namespace FrostmanConditionalFactorScope

/--
The product of the edge scale factors is bounded by the whole-chain scale
factor.  The only inequality is that the fixed parent-dilation volume is at
least one; all intermediate tube-volume factors cancel exactly.
-/
lemma relationReferenceScaleFactor_product_le
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    {J : ℕ} (hJ : 1 ≤ J)
    (chain : GridIndexSubchain delta J)
    (hcoarse : chain.index 0 = P.coarse)
    (hfine : chain.index J = P.fine) :
    (∏ interval : Fin J,
        P.relationReferenceScaleFactor
          (chain.fineIndex interval)
          (chain.coarseIndex interval)) ≤
      P.relationReferenceScaleFactor P.fine P.coarse := by
  let value : ℕ → ENNReal :=
    fun k =>
      Kakeya.deltaTubeVolume
        (uniformScale delta hdelta_le_one (chain.index k)).1
  let constant : ENNReal :=
    ENNReal.ofReal (|independentCoverParentDilation A| ^ 3)
  have hscalePos :
      ∀ k, 0 <
        (uniformScale delta hdelta_le_one (chain.index k)).1 :=
    fun k => lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one (chain.index k)).property.1
  have hvalueZero : ∀ k, value k ≠ 0 :=
    fun k =>
      (RandomTranslation.deltaTubeVolume_pos (hscalePos k)).ne'
  have hvalueTop : ∀ k, value k ≠ ⊤ :=
    fun _ => RandomTranslation.deltaTubeVolume_ne_top
  have hDOne : 1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  have hconstantOne : 1 ≤ constant := by
    rw [ENNReal.one_le_ofReal]
    have hDnonneg : 0 ≤ independentCoverParentDilation A :=
      zero_le_one.trans hDOne
    rw [abs_of_nonneg hDnonneg]
    exact one_le_pow₀ hDOne
  have hconstantZero : constant ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hconstantOne)
  have hconstantTop : constant ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hproduct :
      (∏ interval : Fin J,
          P.relationReferenceScaleFactor
            (chain.fineIndex interval)
            (chain.coarseIndex interval)) =
        value J / (constant ^ J * value 0) := by
    calc
      (∏ interval : Fin J,
          P.relationReferenceScaleFactor
            (chain.fineIndex interval)
            (chain.coarseIndex interval))
          =
        ∏ interval : Fin J,
          value (interval.val + 1) /
            (constant * value interval.val) := by
              apply Finset.prod_congr rfl
              intro interval _
              rfl
      _ = value J / (constant ^ J * value 0) :=
        adjacent_ratio_product
          value constant hvalueZero hvalueTop
          hconstantZero hconstantTop J
  have hdenominator :
      constant * value 0 ≤ constant ^ J * value 0 := by
    gcongr
    simpa using pow_le_pow_right₀ hconstantOne hJ
  rw [hproduct]
  change value J / (constant ^ J * value 0) ≤
    Kakeya.deltaTubeVolume
        (uniformScale delta hdelta_le_one P.fine).1 /
      (constant *
        Kakeya.deltaTubeVolume
          (uniformScale delta hdelta_le_one P.coarse).1)
  rw [← hfine, ← hcoarse]
  exact ENNReal.div_le_div le_rfl hdenominator

/--
A coherent cardinality telescope implies the reference-density telescope.

This is the exact consumer boundary for the v5 hierarchy producer.  All
measure-theoretic and scale-volume factors have already been discharged; the
producer needs only the displayed relation-cardinality product inequality.
-/
theorem referenceDensity_telescope_of_cardinality_telescope
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (hF_ball : F.IsInUnitBall)
    {J : ℕ} (hJ : 1 ≤ J)
    (chain : GridIndexSubchain delta J)
    (hcoarse : chain.index 0 = P.coarse)
    (hfine : chain.index J = P.fine)
    (densityLoss : ENNReal)
    (hcardinality :
      (∏ interval : Fin J,
          P.relationCardMax hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval)) ≤
        densityLoss * P.relationCardMin hF P.fine P.coarse) :
    (∏ interval : Fin J,
        P.relationReferenceDensityMax hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval)) ≤
      densityLoss *
        P.relationReferenceDensityMin hF P.fine P.coarse := by
  have hedge :
      ∀ interval : Fin J,
        P.relationReferenceDensityMax hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval) ≤
          P.relationCardMax hF
              (chain.fineIndex interval)
              (chain.coarseIndex interval) *
            P.relationReferenceScaleFactor
              (chain.fineIndex interval)
              (chain.coarseIndex interval) := by
    intro interval
    exact
      P.relationReferenceDensityMax_le_cardMax_mul_scaleFactor
        hA hdelta hF hF_ball
        (chain.fineIndex interval)
        (chain.coarseIndex interval)
        (chain.fineScale_le_coarseScale
          hdelta hdelta_le_one interval)
  have hedgeProduct :
      (∏ interval : Fin J,
          P.relationReferenceDensityMax hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval)) ≤
        (∏ interval : Fin J,
          P.relationCardMax hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval)) *
        ∏ interval : Fin J,
          P.relationReferenceScaleFactor
            (chain.fineIndex interval)
            (chain.coarseIndex interval) := by
    calc
      (∏ interval : Fin J,
          P.relationReferenceDensityMax hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval))
          ≤
        ∏ interval : Fin J,
          (P.relationCardMax hF
              (chain.fineIndex interval)
              (chain.coarseIndex interval) *
            P.relationReferenceScaleFactor
              (chain.fineIndex interval)
              (chain.coarseIndex interval)) := by
                exact Finset.prod_le_prod
                  (fun _ _ => by positivity)
                  (fun interval _ => hedge interval)
      _ =
        (∏ interval : Fin J,
          P.relationCardMax hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval)) *
        ∏ interval : Fin J,
          P.relationReferenceScaleFactor
            (chain.fineIndex interval)
            (chain.coarseIndex interval) := by
              rw [Finset.prod_mul_distrib]
  have hscale :=
    P.relationReferenceScaleFactor_product_le
      hA hdelta hJ chain hcoarse hfine
  have hwhole :=
    P.cardMin_mul_scaleFactor_le_relationReferenceDensityMin
      hA hdelta hF hF_ball P.fine P.coarse
        P.fineScale_le_coarseScale
  calc
    (∏ interval : Fin J,
        P.relationReferenceDensityMax hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval))
        ≤
      (∏ interval : Fin J,
        P.relationCardMax hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval)) *
      ∏ interval : Fin J,
        P.relationReferenceScaleFactor
          (chain.fineIndex interval)
          (chain.coarseIndex interval) :=
      hedgeProduct
    _ ≤
      (densityLoss * P.relationCardMin hF P.fine P.coarse) *
        P.relationReferenceScaleFactor P.fine P.coarse := by
          gcongr
    _ =
      densityLoss *
        (P.relationCardMin hF P.fine P.coarse *
          P.relationReferenceScaleFactor P.fine P.coarse) := by
            ac_rfl
    _ ≤
      densityLoss *
        P.relationReferenceDensityMin hF P.fine P.coarse := by
          gcongr

end FrostmanConditionalFactorScope

end Kakeya.Streamlined

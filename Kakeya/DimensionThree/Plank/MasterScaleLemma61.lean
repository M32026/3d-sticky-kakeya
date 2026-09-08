module

public import Kakeya.DimensionThree.Plank.FlatPrismInnerEstimate

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

/-- **The master-scale Katz--Tao reading of GWZ Lemma 6.1 is a theorem, not a hypothesis.** -/
theorem KatzTaoEstimate.plankEstimateAtMasterScale {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β) :
    PlankEstimateAtMasterScale.{0} β := by
  intro ε hε
  obtain ⟨η, hη, b₀, hb₀, hbound⟩ :=
    KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity hβpos hβle hKKT (ε / 2) (by positivity)
  refine ⟨min η (ε / 2), lt_min hη (by positivity), b₀, hb₀, ?_⟩
  intro ι s δ a b hab hb1 V hδ hδa hbb₀ hwin hed hfull hKT γ hγ0 hγ1 hslab
  have hδ1 : δ ≤ 1 := hδa.trans (hab.trans hb1)
  have hηmin : min η (ε / 2) ≤ η := min_le_left _ _
  have hηε : min η (ε / 2) ≤ ε / 2 := min_le_right _ _
  -- fullness transfers
  have hfull' : (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hηmin) hfull
  -- slab transfers
  have hslab' : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
        ≤ δ ^ (-η) * φ ^ γ * (s.card : ℝ≥0) := by
    intro φ hφR hφ S
    refine (hslab φ hφR hφ S).trans ?_
    have hrp : (δ : ℝ≥0) ^ (-(min η (ε / 2))) ≤ (δ : ℝ≥0) ^ (-η) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηmin)
    exact mul_le_mul_left (mul_le_mul_left hrp _) _
  have hmain := hbound s hab hb1 V hδ hδa hbb₀ hwin hed hfull' γ hγ0 hγ1 hslab'
  refine hmain.trans ?_
  have hδ0' : ((δ : ENNReal)) ≠ 0 := by
    simpa using hδ.ne'
  have hδtop : ((δ : ENNReal)) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1' : ((δ : ENNReal)) ≤ 1 := by exact_mod_cast hδ1
  have hdens : maxDensity s (fun i => (V i).toConvexSpaceBody) ^ (1 - β)
      ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
    have h1 : maxDensity s (fun i => (V i).toConvexSpaceBody) ^ (1 - β)
        ≤ ((δ : ENNReal) ^ (-(min η (ε / 2)))) ^ (1 - β) :=
      ENNReal.rpow_le_rpow hKT (by linarith)
    refine h1.trans ?_
    rw [← ENNReal.rpow_mul]
    refine ENNReal.rpow_le_rpow_of_exponent_ge hδ1' ?_
    nlinarith [min_le_right η (ε / 2), lt_min hη (show (0:ℝ) < ε/2 by positivity)]
  calc
    (δ : ENNReal) ^ (-(ε / 2)) * maxDensity s (fun i => (V i).toConvexSpaceBody) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β
      ≤ (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2))
        * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
        gcongr
    _ = (δ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
        * (s.card : ENNReal) ^ β := by
        rw [← ENNReal.rpow_add _ _ hδ0' hδtop]
        ring_nf

/-- **GWZ Proposition 6.6(B) over the Part-(B) datum, with both readings of GWZ Lemma 6.1
discharged.**

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61` is proved, but it takes
the two master-scale readings of GWZ Lemma 6.1 as *hypotheses*
(`Kakeya.PlankEstimateAtMasterScale` and `Kakeya.PlankEstimateAtMasterScaleWithDensity`), so what it
establishes is an implication rather than the proposition.  Both hypotheses are now theorems of
`K_KT(β)`:

* the density (`γ = 1`) reading is `Kakeya.KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity`;
* the Katz--Tao (`γ = 0`) reading is `Kakeya.KatzTaoEstimate.plankEstimateAtMasterScale`, above.

So the conclusion below depends only on `K_KT(β)`, `K_F(β)` and the factorisation datum.  It is
still *not* the project statement `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`: it is stated
over `Kakeya.Section6PartBData` (a hypothesis-richer datum than
`Kakeya.GlobalPlankFactorization`), it assumes leaf-scale essential distinctness of the fine tubes
(since  also a hypothesis of the project statement, GWZ Definition 2.1(ii) at `ρ = δ`)
and of the outer representative planks, and it carries the inner-scale threshold `δ ≤ s₀ * a`
(derivable, `Kakeya.Prop66BScale.le_mul_of_plankScale_le`).  Bridging the datum gap and the
outer-representative gap is what remains of Proposition 6.6(B).

**Uniformity of `(𝕋, Y)` is not among them, and no longer appears here.**  Until steps  this
statement, and every statement of the chain below it, carried
`∃ C ≤ δ ^ (-η), Nonempty (ShadedTube.IsUniform q T (Set.Icc δ 1) C)` — the *per-scale* rendering of
GWZ Definition 2.2, which is not the rendering
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` supplies.  No step of the chain eliminated it:
`Kakeya.factoringAndMultPropGlobal_of_remark53` introduced it and never mentioned it again.  The
binder has been deleted from all six statements, which strengthens each of them, and both
hypothesis-carrying forms are recovered from the result in
`Kakeya/DimensionThree/Plank/Prop66BUniformityShapes.lean`.  What consumes uniformity in this
argument is the datum `Kakeya.Section6PartBData` together with
`Kakeya.Section6PartBData.Remark53Prop51`, so the grid clause of Proposition 6.6(B) is to be spent
where that datum is built, not here. -/
theorem tubeMultiplicityOfGlobalPlankFactorisation_of_partBData (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), ∃ s₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
          {κ : Type*} (r : Finset κ)
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
          C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
          δ ≤ ρ → ρ ≤ a → δ ≤ s₀ * a →
          ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
          D.Remark53Prop51 Cprop →
          (D.factor.cells : Set D.factor.Cell).Pairwise
            (fun x y => _root_.IsEssentiallyDistinct
              (D.factor.repr x).carrier (D.factor.repr y).carrier) →
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β :=
  tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61 Cprop hCprop hβpos hβle hKKT hKF
    (KatzTaoEstimate.plankEstimateAtMasterScale hβpos hβle hKKT)
    (KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity hβpos hβle hKKT)

end Kakeya

end

end

module

public import Kakeya.DimensionThree.MainLemma1.OneScaleProductOnly

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Two axiom-clean one-scale product factorizations, composed without any uniformity bundle. -/
theorem exists_twoScaleProductOnly (hdim : Module.finrank ℝ E = 3)
    {δ τ θ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    {ι κ : Type u} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ}
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hfine : IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ)
    (hmass : 0 < ∑ i ∈ s, volume (T i).shade)
    (hballτ : ∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1)
    (hcoarse : IsParentFamily tτ Tτ tθ Tθ pθ) :
    ∃ (tm : Finset κ) (Zτ : κ → ShadedTube τ E) (Zf : ι → ShadedTube δ E)
      (tc : Finset κ) (Zc : κ → ShadedTube θ E) (Zm : κ → ShadedTube τ E),
      tm.Nonempty ∧ tc.Nonempty ∧ tm ⊆ tτ ∧ tc ⊆ tθ ∧
      ∀ k ∈ tm, ∀ l ∈ tc,
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody) ≤
          (factorTwoScales.C s.card δ tm.card τ : ENNReal)
            * ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody)
            * ShadedBody.multiplicity (fibre (tm.filter fun j => pθ j ∈ tc) pθ l)
                (fun j => (Zm j).toShadedBody)
            * ShadedBody.multiplicity (fibre (s.filter fun i => pτ i ∈ tm) pτ k)
                (fun i => (Zf i).toShadedBody) := by
  obtain ⟨tm, htm, Zτ, Zf, htmne, hmassτ, hZτtube, _hZftube, hprod1⟩ :=
    exists_oneScaleProductOnly hdim hδ hδτ (hτθ.trans hθ1) T Tτ pτ hball hfine hmass
  have hparent2 : IsParentFamily tm (fun k => (Zτ k).toTube) tθ Tθ pθ := by
    refine ⟨?_, hcoarse.injOn, ?_⟩
    · intro k hk
      exact hcoarse.mapsTo k (htm hk)
    · intro k hk
      rw [hZτtube k hk]
      exact hcoarse.le_parent k (htm hk)
  have hball2 : ∀ k ∈ tm, (Zτ k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk
    change (Zτ k).toTube.carrier ⊆ Metric.closedBall 0 1
    rw [hZτtube k hk]
    exact hballτ k (htm hk)
  obtain ⟨tc, htc, Zc, Zm, htcne, _hmassc, _hZctube, _hZmtube, hprod2⟩ :=
    exists_oneScaleProductOnly hdim (lt_of_lt_of_le hδ hδτ) hτθ hθ1
      Zτ Tθ pθ hball2 hparent2 hmassτ
  refine ⟨tm, Zτ, Zf, tc, Zc, Zm, htmne, htcne, htm, htc, ?_⟩
  intro k hk l hl
  calc
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
        ≤ (factorOneScale.C s.card δ : ENNReal)
          * ShadedBody.multiplicity tm (fun j => (Zτ j).toShadedBody)
          * ShadedBody.multiplicity (fibre (s.filter fun i => pτ i ∈ tm) pτ k)
              (fun i => (Zf i).toShadedBody) := hprod1 k hk
    _ ≤ (factorOneScale.C s.card δ : ENNReal) *
          ((factorOneScale.C tm.card τ : ENNReal)
            * ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody)
            * ShadedBody.multiplicity (fibre (tm.filter fun j => pθ j ∈ tc) pθ l)
                (fun j => (Zm j).toShadedBody)) *
          ShadedBody.multiplicity (fibre (s.filter fun i => pτ i ∈ tm) pτ k)
              (fun i => (Zf i).toShadedBody) := by
          exact mul_le_mul_right' (mul_le_mul_left' (hprod2 l hl) _) _
    _ = _ := by
      rw [factorTwoScales.C, ENNReal.coe_mul]
      ring

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.exists_twoScaleProductOnly

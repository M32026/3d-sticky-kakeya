module

public import Kakeya.DimensionThree.MainLemma1.AnalyticEndgame

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! The scalar estimate used by the rich post assembly, copied verbatim from
`LossLedger` so this module remains a legal `module` import. -/
theorem factorTwoScales_C_le_exact_upstream_w50
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {delta tau : NNReal} (hdelta1 : delta <= 1)
    (C0 : NNReal) (hC0 : 1 <= C0) (sCard midCard : Nat) :
    (factorTwoScales.C sCard delta midCard tau : ENNReal)
      <= (((C0 * factorTwoScales.C sCard delta midCard tau : NNReal) : ENNReal)) *
        (delta : ENNReal) ^ (-p.ε') := by
  have heps : 0 <= p.ε' := by
    rw [hp.epsPrimeEq]
    nlinarith [hp.etaZeroPos]
  have hdeltaE : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  have hone : (1 : ENNReal) <= (delta : ENNReal) ^ (-p.ε') := by
    rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
    exact ENNReal.rpow_le_one hdeltaE heps
  have hC0E : (1 : ENNReal) <= (C0 : ENNReal) := by exact_mod_cast hC0
  calc
    (factorTwoScales.C sCard delta midCard tau : ENNReal) =
        (factorTwoScales.C sCard delta midCard tau : ENNReal) * 1 := by ring
    _ <= (factorTwoScales.C sCard delta midCard tau : ENNReal) * (C0 : ENNReal) := by
      exact mul_le_mul_of_nonneg_left hC0E (by positivity)
    _ = ((factorTwoScales.C sCard delta midCard tau : ENNReal) * (C0 : ENNReal)) * 1 := by
      ring
    _ <= ((factorTwoScales.C sCard delta midCard tau : ENNReal) * (C0 : ENNReal)) *
          (delta : ENNReal) ^ (-p.ε') := by
      exact mul_le_mul_left' hone _
    _ = (((C0 * factorTwoScales.C sCard delta midCard tau : NNReal) : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-p.ε') := by
      rw [ENNReal.coe_mul]
      ring

/-!
The post-producer payload is kept upstream of `B3EndToEnd`.  This is the
original `B3PostCertificate` declaration, moved without changing its type, so
CaseTwo-facing producers can use it without creating the B3EndToEnd back-edge.
-/
def B3PostCertificate
    {p : Params} {γ : ℝ} {m : ℕ} {δ τ θ : NNReal}
    {ι : Type u} [DecidableEq ι]
    (C0 : NNReal) (s : Finset ι)
    (tτ : Finset ι) (pτ : ι → ι) (kF : ι) (Yf : ι → ShadedTube δ E)
    (tθ : Finset ι) (pθ : ι → ι) (lM : ι) (Ym : ι → ShadedTube τ E)
    (tθAct : Finset ι) (Yc : ι → ShadedTube θ E) (Lfact : ENNReal) : Prop :=
  ∃ Nmid : ℕ,
    0 < Nmid ∧
    (Nmid : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) ∧
    Lfact ≤ (((C0 * factorTwoScales.C s.card δ Nmid τ : NNReal) : ENNReal)) *
      (δ : ENNReal) ^ (-p.ε') ∧
    AnalyticEndgameW27.IsTwoScaleAnalyticBounds
      γ (p.η m) (p.η m + 2 * p.ε')
      s pτ kF Yf tτ pθ lM Ym tθAct Yc

#print axioms B3PostCertificate

end Kakeya.ml1Boot
end

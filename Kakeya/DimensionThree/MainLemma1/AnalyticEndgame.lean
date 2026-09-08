module

public import Kakeya.DimensionThree.MainLemma1.FactorTwoAbsorption
public import Kakeya.DimensionThree.MainLemma1.Rescaling.MiddleAverage
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization

/-!
# The analytic/numeric endgame for the scalar B3 interface

This file separates the only genuinely analytic input still needed after an
`IsTwoScaleFactors` producer from the completely deterministic exponent ledger.  The three
factor estimates are bundled together.  All remaining choices in the exact Case-II leaf are
made here: `etaVol = 2`, `c3 = 1`, `av = eta m`, and
`av' = eta m + 2 eps'`.

The factor constant is allowed to be a fixed NNReal multiple of
`factorTwoScales.C`.  The fixed multiplier covers, in particular, the `4 * M` loss of the
fixed-ball product-only port.  Its product with the hierarchy cardinality constant is absorbed
uniformly once the two relevant cardinalities obey the standard dimension-three
`delta ^ (-7)` bound.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.AnalyticEndgameW27

universe u v q w

variable {E : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The three analytic inequalities consumed by the scalar B3 collapse.  Geometry, Frostman
input, and threshold management belong in the producer of this certificate; the exponent and
capacity ledger below does not inspect how the bounds were obtained. -/
structure IsTwoScaleAnalyticBounds
    {ι : Type u} {κ : Type v} {lc : Type q}
    [DecidableEq κ] [DecidableEq lc]
    {δ τ θ : NNReal} (γ a a' : ℝ)
    (s : Finset ι) (pτ : ι → κ) (kF : κ) (Yf : ι → ShadedTube δ E)
    (tτ : Finset κ) (pθ : κ → lc) (lM : lc) (Ym : κ → ShadedTube τ E)
    (tθ : Finset lc) (Yc : lc → ShadedTube θ E) : Prop where
  fine :
    ShadedBody.multiplicity (fibre s pτ kF) (fun i => (Yf i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-4 * a') * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
        * (((fibre s pτ kF).card : ENNReal)
            * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
  middle :
    ShadedBody.multiplicity (fibre tτ pθ lM) (fun k => (Ym k).toShadedBody)
      ≤ (δ : ENNReal) ^ (10 * a) * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
        * (((fibre tτ pθ lM).card : ENNReal)
            * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
  coarse :
    ShadedBody.multiplicity tθ (fun l => (Yc l).toShadedBody)
      ≤ (δ : ENNReal) ^ (-4 * a') * (θ : ENNReal) ^ (-2 * γ)
        * ((tθ.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)

/-- A fixed constant times the genuine two-scale factoring constant is subpolynomial,
uniformly over the usual dimension-three cardinality range. -/
theorem eventually_const_mul_factorTwoScales_C_mul_rpow_le_one
    (K : NNReal) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
        ∀ N₁ N₂ : ℕ, 0 < N₁ → 0 < N₂ →
          (N₁ : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
          (N₂ : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
          (K : ENNReal) * (factorTwoScales.C N₁ δ N₂ τ : ENNReal)
              * (δ : ENNReal) ^ a ≤ 1 := by
  have ha2 : 0 < a / 2 := by positivity
  filter_upwards [eventually_factorTwoScales_C_mul_sixteen_rpow_le_one ha2,
    absorb_eventually (c := a / 2) ha2 (K := (K : ENNReal)) ENNReal.coe_ne_top,
    self_mem_nhdsWithin] with δ hfactor hK hδ0
  intro τ hδτ hτ1 N₁ N₂ hN₁ hN₂ hcard₁ hcard₂
  have hδne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
  have hfactor' : (factorTwoScales.C N₁ δ N₂ τ : ENNReal)
      * (δ : ENNReal) ^ (a / 2) ≤ 1 := by
    calc
      (factorTwoScales.C N₁ δ N₂ τ : ENNReal) * (δ : ENNReal) ^ (a / 2)
          ≤ (factorTwoScales.C N₁ δ N₂ τ : ENNReal) * (2 : ENNReal) ^ 4
              * (δ : ENNReal) ^ (a / 2) := by
            have h16 : (1 : ENNReal) ≤ (2 : ENNReal) ^ 4 := by norm_num
            calc
              (factorTwoScales.C N₁ δ N₂ τ : ENNReal) * (δ : ENNReal) ^ (a / 2)
                  = (factorTwoScales.C N₁ δ N₂ τ : ENNReal) * 1
                      * (δ : ENNReal) ^ (a / 2) := by ring
              _ ≤ (factorTwoScales.C N₁ δ N₂ τ : ENNReal) * (2 : ENNReal) ^ 4
                    * (δ : ENNReal) ^ (a / 2) := by gcongr
      _ ≤ 1 := hfactor τ hδτ hτ1 N₁ N₂ hN₁ hN₂ hcard₁ hcard₂
  have hpow : (δ : ENNReal) ^ a =
      (δ : ENNReal) ^ (a / 2) * (δ : ENNReal) ^ (a / 2) := by
    rw [← ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]
    congr 1
    ring
  rw [hpow]
  calc
    (K : ENNReal) * (factorTwoScales.C N₁ δ N₂ τ : ENNReal)
          * ((δ : ENNReal) ^ (a / 2) * (δ : ENNReal) ^ (a / 2))
        = ((K : ENNReal) * (δ : ENNReal) ^ (a / 2))
          * ((factorTwoScales.C N₁ δ N₂ τ : ENNReal)
              * (δ : ENNReal) ^ (a / 2)) := by ring
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- Once scalar B3 and the three analytic factors have been produced, this theorem fills the
entire numeric tail of the exact dividing-block leaf.  No separate volume-capacity or
absorption callback remains.

`C0` is the fixed loss in front of `factorTwoScales.C`; for the fixed-ball product-only port it
is `4 * M`.  `Nmid` is the middle cardinality at which the second one-scale constant is read. -/
theorem eventually_exists_exact_tail_of_isTwoScaleFactors
    {β γ₀ : ℝ} {p : Params} (hp : p.Spec β γ₀)
    {c : ℝ} (hc0 : 0 < c) (hcη : c ≤ p.η 0 / 4)
    (C0 Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      ∀ {τ θ : NNReal}, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
      ∀ {γ : ℝ} {m : ℕ}, 0 ≤ γ → c ≤ γ → γ ≤ 1 → m < p.N →
      ∀ {ι : Type u} {κ : Type v} {lc : Type q}
        [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]
        {s : Finset ι} {V : ι → ShadedTube δ E}
        {tτ : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
        {tθ : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
        {kF : κ} {Yf : ι → ShadedTube δ E} {lamF : NNReal}
        {lM : lc} {Ym : κ → ShadedTube τ E} {lamM : NNReal}
        {tθAct : Finset lc} {Yc : lc → ShadedTube θ E} {lamC : NNReal}
        {Lfact : ENNReal} {Nmid : ℕ},
      0 < s.card → 0 < Nmid →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
      (Nmid : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
      IsTwoScaleFactors Lfact ((Cu : ENNReal) ^ 4)
        s V tτ Vτ pτ tθ Vθ pθ kF Yf lamF lM Ym lamM tθAct Yc lamC →
      Lfact ≤ (((C0 * factorTwoScales.C s.card δ Nmid τ : NNReal) : ENNReal))
          * (δ : ENNReal) ^ (-p.ε') →
      IsTwoScaleAnalyticBounds γ (p.η m) (p.η m + 2 * p.ε')
        s pτ kF Yf tτ pθ lM Ym tθAct Yc →
      ∃ (Cf Cu' c₃ lamF' lamM' lamC' : NNReal) (ηvol av av' : ℝ),
        δ ≤ τ ∧ τ ≤ θ ∧ θ ≤ 1 ∧
        0 ≤ av ∧ av ≤ av' ∧ 8 * av' ≤ 10 * av ∧
        0 ≤ ηvol ∧ 0 < c₃ ∧ c₃ ≤ 1 ∧ 1 ≤ Cu' ∧
        IsTwoScaleFactors Lfact ((Cu' : ENNReal) ^ 4)
          s V tτ Vτ pτ tθ Vθ pθ kF Yf lamF' lM Ym lamM' tθAct Yc lamC' ∧
        Lfact ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-p.ε') ∧
        ShadedBody.multiplicity (fibre s pτ kF) (fun i => (Yf i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-4 * av') * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
            * (((fibre s pτ kF).card : ENNReal)
                * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) ∧
        ShadedBody.multiplicity (fibre tτ pθ lM) (fun k => (Ym k).toShadedBody)
          ≤ (δ : ENNReal) ^ (10 * av) * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
            * (((fibre tτ pθ lM).card : ENNReal)
                * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) ∧
        ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-4 * av') * (θ : ENNReal) ^ (-2 * γ)
            * ((tθAct.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) ∧
        (c₃ : ENNReal) * (δ : ENNReal) ^ ηvol
          ≤ (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ) ∧
        (Cf : ENNReal) * (Cu' : ENNReal) ^ 4 * (c₃ : ENNReal) ^ (-c / 2)
            * (δ : ENNReal) ^ (-p.ε') * (δ : ENNReal) ^ (10 * av - 8 * av')
            * (δ : ENNReal) ^ (-2 * c - ηvol * c / 2) ≤ 1 ∧
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-2 * (γ - c))
            * ((s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - (γ - c) / 2) := by
  have hsurplus : 0 < 3 * p.η 0 / 16 := by
    linarith [hp.etaZeroPos]
  filter_upwards [eventually_const_mul_factorTwoScales_C_mul_rpow_le_one
      (C0 * Cu ^ 4) hsurplus, self_mem_nhdsWithin] with δ habs hδ0
  intro τ θ hδτ hτθ hθ1 γ m hγ0 hcγ hγ1 hm ι κ lc _ _ _ s V tτ Vτ pτ tθ Vθ pθ kF Yf lamF lM Ym
    lamM tθAct Yc lamC Lfact Nmid hs hNmid hcardS hcardMid hB3 hLfact hanalytic
  let Cf : NNReal := C0 * factorTwoScales.C s.card δ Nmid τ
  let av : ℝ := p.η m
  let av' : ℝ := p.η m + 2 * p.ε'
  have hτ1 : τ ≤ 1 := hτθ.trans hθ1
  have hδ1 : δ ≤ 1 := hδτ.trans hτ1
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
  have hηmono : p.η 0 ≤ p.η m :=
    hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _))
      (Set.mem_Iic.mpr hm.le) (Nat.zero_le _)
  have hε' : 0 < p.ε' := by
    rw [hp.epsPrimeEq]
    linarith [hp.etaZeroPos]
  have hav0 : 0 ≤ av := by
    dsimp [av]
    exact hp.etaZeroPos.le.trans hηmono
  have havv : av ≤ av' := by
    dsimp [av']
    linarith
  have hgain : 8 * av' ≤ 10 * av := by
    dsimp [av, av']
    rw [hp.epsPrimeEq]
    linarith [hηmono]
  have hbase : (Cf : ENNReal) * (Cu : ENNReal) ^ 4
      * (δ : ENNReal) ^ (3 * p.η 0 / 16) ≤ 1 := by
    have hraw := habs τ hδτ hτ1 s.card Nmid hs hNmid hcardS hcardMid
    simpa [Cf, ENNReal.coe_mul, ENNReal.coe_pow, mul_assoc, mul_left_comm, mul_comm]
      using hraw
  have hexp : 3 * p.η 0 / 16 ≤
      -p.ε' + (10 * av - 8 * av') + (-2 * c - (2 : ℝ) * c / 2) := by
    dsimp [av, av']
    rw [hp.epsPrimeEq]
    linarith [hηmono, hcη]
  have hpows :
      (δ : ENNReal) ^ (-p.ε') * (δ : ENNReal) ^ (10 * av - 8 * av')
          * (δ : ENNReal) ^ (-2 * c - (2 : ℝ) * c / 2)
        = (δ : ENNReal) ^
            (-p.ε' + (10 * av - 8 * av') + (-2 * c - (2 : ℝ) * c / 2)) := by
    rw [← ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]
    rw [← ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]
  have habsorb :
      (Cf : ENNReal) * (Cu : ENNReal) ^ 4 * ((1 : NNReal) : ENNReal) ^ (-c / 2)
          * (δ : ENNReal) ^ (-p.ε') * (δ : ENNReal) ^ (10 * av - 8 * av')
          * (δ : ENNReal) ^ (-2 * c - (2 : ℝ) * c / 2) ≤ 1 := by
    calc
      (Cf : ENNReal) * (Cu : ENNReal) ^ 4 * ((1 : NNReal) : ENNReal) ^ (-c / 2)
            * (δ : ENNReal) ^ (-p.ε') * (δ : ENNReal) ^ (10 * av - 8 * av')
            * (δ : ENNReal) ^ (-2 * c - (2 : ℝ) * c / 2)
          = ((Cf : ENNReal) * (Cu : ENNReal) ^ 4) *
              ((δ : ENNReal) ^ (-p.ε') * (δ : ENNReal) ^ (10 * av - 8 * av')
                * (δ : ENNReal) ^ (-2 * c - (2 : ℝ) * c / 2)) := by simp; ring
      _ = ((Cf : ENNReal) * (Cu : ENNReal) ^ 4) *
              (δ : ENNReal) ^
                (-p.ε' + (10 * av - 8 * av') + (-2 * c - (2 : ℝ) * c / 2)) := by
            rw [hpows]
      _ ≤ ((Cf : ENNReal) * (Cu : ENNReal) ^ 4) *
              (δ : ENNReal) ^ (3 * p.η 0 / 16) := by
            exact mul_le_mul_left'
              (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 hexp) _
      _ ≤ 1 := hbase
  have honeCard : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Nat.succ_le_iff.mpr hs
  have hvol : ((1 : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 : ℝ)
      ≤ (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ) := by
    have hpow : (δ : ENNReal) ^ (2 : ℝ) = (δ : ENNReal) ^ (2 : ℕ) := by
      convert (ENNReal.rpow_natCast (δ : ENNReal) 2) using 1 <;> norm_num
    rw [hpow]
    simpa using mul_le_mul_right' honeCard ((δ : ENNReal) ^ (2 : ℕ))
  have hcollapse := multiplicity_le_collapse_of_isTwoScaleFactors
    hδ0 hδτ hτθ hθ1 hγ0 hγ1 hc0 hcγ hav0 havv hgain hε'
      (by norm_num : 0 ≤ (2 : ℝ)) (by norm_num : (0 : NNReal) < 1)
      (by norm_num : (1 : NNReal) ≤ 1) hCu hB3
      (by simpa [Cf] using hLfact) hs hanalytic.fine hanalytic.middle hanalytic.coarse
      hvol habsorb
  refine ⟨Cf, Cu, 1, lamF, lamM, lamC, 2, av, av',
    hδτ, hτθ, hθ1, hav0, havv, hgain, by norm_num, by norm_num, by norm_num, hCu,
    hB3, ?_, hanalytic.fine, hanalytic.middle, hanalytic.coarse, hvol, habsorb,
    hcollapse⟩
  simpa [Cf] using hLfact

end Kakeya.ml1Boot.AnalyticEndgameW27

#print axioms Kakeya.ml1Boot.AnalyticEndgameW27.eventually_const_mul_factorTwoScales_C_mul_rpow_le_one
#print axioms Kakeya.ml1Boot.AnalyticEndgameW27.eventually_exists_exact_tail_of_isTwoScaleFactors

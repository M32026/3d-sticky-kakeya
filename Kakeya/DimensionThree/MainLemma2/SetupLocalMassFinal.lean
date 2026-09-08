/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupLocalMassRefine
public import Kakeya.DimensionThree.MainLemma2.SetupLocalMassChain

/-!
# Residue 1 of the §9.3 setup, discharged: the local-mass refinement

`Kakeya.VeryNotSticky.LocalMassRefinementResidue η η'` (GWZ (87) on the class-dense refinement,
`SetupAssembly.lean`) is proved here **as stated**, by the multi-scale chain of :

* **step U** — `Kakeya.VeryNotSticky.eventually_exists_uniformBand` at input fullness `δ^η`:
  the band and one GWZ Definition 2.2 uniformisation, giving `(s₀, T₀)` with the **δ-free**
  bundle `ShadedTube.ShadedUniformTubeSet s₀ T₀ N (ShadedTube.ssfUniformConst 3)` and retention
  `δ^{3η'/2}`;
* **steps `B_m`** — `Kakeya.VeryNotSticky.exists_bridgeChain_rpow` on `(s₀, T₀)`: `N/q + 1`
  one-scale bridges (GWZ Lemma 5.11 at the sparse grid indices `q·m`, `q = ⌊ηN/32⌋`), all with
  the step-0 hierarchy as parent map, each losing `L ≤ δ^{-ε}` at `ε = η'/(4(64/η + 2))`; total
  retention `(δ^ε)^{N/q+1} ≥ δ^{η'/4}` once `64 ≤ ηN`, the clauses stored relative to `|U₀|`;
* **step CD** — `Kakeya.VeryNotSticky.eventually_exists_classDenseRefinement_slack` on the chain's
  output `(s_J, T_J)`, whose fullness is `≥ δ^{η + 7η'/4} ≥ δ^{η + 2η'}`
  (`ShadedBody.IsCRefinement.mul_fullness_le`) and whose `maxDensity` is that of `(s, T)`
  (`Kakeya.VeryNotSticky.maxDensity_le_of_subset_of_tube_eq`): the capped bundle
  `1 ≤ C₀ ≤ δ^{-η'}`, the per-tube floor `2δ^{2η}|T|` and retention `δ^{2η'}`;
* **step TR** — `Kakeya.VeryNotSticky.localMassAt_half_of_bridgeChain`: transport of every stored
  clause to the final family through the single volume comparison `|U₀| ≤ (C⁵/(c_J c*))|U*|`
  and interpolation to every grid index; the gain is
  `δ^{9η'/4 + η'/4 + ε + 3η/32} ≥ δ^{7η/16} ≥ δ^{η/2}` for `8η' < η`.

**Admissibility actually needed: `0 < η'`, `8η' < η`, `η ≤ 1`.** `8η' < η` is spent only in the
exponent budget of `Kakeya.VeryNotSticky.bridgeChain_exponent_le` (`11η'/4 + 3η/32 ≤ η/2`) and
in the total retention `15η'/4 ≤ η/2`; the two families need only `3η' < η`; `η ≤ 1` is what
`Kakeya.VNSUniform.card_le_rpow_neg_four_enn` needs for `|𝕋| ≤ δ^{-4}`. The assembly's
`η' = η/9` satisfies all three (`η ≤ 1` there from `Kakeya.VeryNotSticky.CaseParams.slab`).

## Exponent bookkeeping (every line compiled below)

| quantity | bound |
|---|---|
| retention of step U, `c_U` | `δ^{3η'/2}` |
| number of bridges | `N/q + 1 ≤ 64/η + 1 < 64/η + 2` (`div_sparseStep_le`, `64 ≤ ηN`) |
| per-bridge loss exponent | `ε = η'/(4(64/η + 2)) ≤ η'/4`, `ε·(N/q + 1) ≤ η'/4` |
| retention of the chain, `c_J` | `(δ^ε)^{N/q+1} ≥ δ^{η'/4}` |
| fullness of `(s_J, T_J)` | `≥ c_U c_J δ^η ≥ δ^{7η'/4} δ^η ≥ δ^{η + 2η'}` |
| retention of step CD, `c*` | `δ^{2η'}` |
| `c_J c*` | `≥ δ^{9η'/4}` |
| total retention `c_U c_J c*` | `≥ δ^{15η'/4} ≥ δ^{η/2}` (`8η' < η`) — clause (f) |
| δ-free constant | `9261 · (ssfUniformConst 3)⁵ ≤ δ^{-η'/4}` eventually |
| local-mass exponent | `9η'/4 + η'/4 + ε + 3η/32 ≤ 7η/16 ≤ η/2` — `LocalMassAt δ (η/2)` |
| clause (e) | `δ^{2η}\|𝕋\| ≤ δ^{η/2}·δ^η\|𝕋\| ≤ \|𝕋*\|`, so `1 ≤ δ^{1+2η}\|𝕋\| ≤ δ\|𝕋*\|` |

## Deliverables

* `Kakeya.VeryNotSticky.BandUniformRefinementLocalMassSlack` — the interface of :
  `BandUniformRefinementLocalMass` with the floor doubled and the local mass at `η/2`;
  `.toBandUniformRefinementLocalMass` recovers the residue's clause form
  (`Kakeya.VeryNotSticky.LocalMassAt.mono_exponent` gives `LocalMassAt δ η` from `η/2`).
* `Kakeya.VeryNotSticky.eventually_exists_localMassRefinement_slack` — the `∀ᶠ` theorem.
* `Kakeya.VeryNotSticky.localMassRefinementResidue` — **residue 1, as stated.**
* `Kakeya.VeryNotSticky.exists_setup_caseSideData_of_sideDataResidue` — the assembly of
  `Kakeya.VeryNotSticky.exists_setup_caseSideData` reduced to
  `Kakeya.VeryNotSticky.SideDataResidue` alone, pinned against the target's type by two
  `example`s (through `Kakeya.VeryNotSticky.SetupCaseSideDataStatement` and `type_of%`).
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal
open Produce

universe u

/-! ### The interface -/

/-- `Kakeya.VeryNotSticky.LocalMassAt` is antitone in its exponent: the clause at `δ^{ε'}` at every
grid index gives the clause at `δ^{ε}` for `ε' ≤ ε` (`δ ≤ 1`). In particular `LocalMassAt δ (η/2)`
gives `LocalMassAt δ η` for `0 ≤ η`. -/
theorem LocalMassAt.mono_exponent {ι : Type u} {δ : ℝ≥0} (hδ1 : δ ≤ 1) {ε' ε : ℝ} (hε : ε' ≤ ε)
    {s : Finset ι} {T : ι → ShadedTube δ E3} (h : LocalMassAt δ ε' s T) : LocalMassAt δ ε s T :=
  localMassAt_of_forall_clause_rpow hδ1 hε ((localMassAt_iff_forall_clause δ ε' s T).mp h)

/-- **The band-uniform refinement with both slacks**: the clauses of
`Kakeya.VeryNotSticky.BandUniformRefinementLocalMass` with the per-tube floor **doubled**
(`2·δ^{2η}|T| ≤ |Y'(i)|`, the side-data plan's slack (ii)) and the local-mass clause at exponent
**`η/2`** (slack (i)); the mass retention is at `δ^{η/2}`, as in the residue. This is what the
chain of  actually delivers, and it is the form residue 2 should consume. -/
def BandUniformRefinementLocalMassSlack {ι : Type u} (δ : ℝ≥0) (η η' : ℝ) (s : Finset ι)
    (T : ι → ShadedTube δ E3) : Prop :=
  ∃ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s ∧
    (∀ i, (T' i).toTube = (T i).toTube) ∧
    (∀ i, (T' i).shade ⊆ (T i).shade) ∧
    (∃ C₀ : ℝ≥0, 1 ≤ C₀ ∧ (C₀ : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-η') ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) ∧
    (∀ i ∈ s', 2 * (δ : ℝ≥0∞) ^ (2 * η) * volume (T' i).carrier ≤ volume (T' i).shade) ∧
    (1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) * (s'.card : ℝ≥0∞) ∧
    (δ : ℝ≥0∞) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade ∧
    LocalMassAt δ (η / 2) s' T'

/-- The slack form implies the residue's clause form
`Kakeya.VeryNotSticky.BandUniformRefinementLocalMass`: halve the floor and read the local mass at
`η` (`Kakeya.VeryNotSticky.LocalMassAt.mono_exponent`). -/
theorem BandUniformRefinementLocalMassSlack.toBandUniformRefinementLocalMass {ι : Type u}
    {δ : ℝ≥0} (hδ1 : δ ≤ 1) {η η' : ℝ} (hη : 0 ≤ η) {s : Finset ι} {T : ι → ShadedTube δ E3}
    (h : BandUniformRefinementLocalMassSlack δ η η' s T) :
    BandUniformRefinementLocalMass δ η η' s T := by
  obtain ⟨s', T', hs', htube, hsh, huni, hfloor, hcard, hmass, hlm⟩ := h
  refine ⟨s', T', hs', htube, hsh, huni, fun i hi => le_trans ?_ (hfloor i hi), hcard, hmass,
    hlm.mono_exponent hδ1 (by linarith)⟩
  calc (δ : ℝ≥0∞) ^ (2 * η) * volume (T' i).carrier
      = 1 * ((δ : ℝ≥0∞) ^ (2 * η) * volume (T' i).carrier) := (one_mul _).symm
    _ ≤ 2 * ((δ : ℝ≥0∞) ^ (2 * η) * volume (T' i).carrier) := by gcongr; norm_num
    _ = 2 * (δ : ℝ≥0∞) ^ (2 * η) * volume (T' i).carrier := by ring

/-! ### The chain, assembled -/

/-- **The local-mass refinement, both slacks.**

From the residue's four binders — carriers in the unit ball, `maxDensity ≤ δ^{-η}`, fullness
`≥ δ^η`, `1 ≤ δ^{1+2η}|𝕋|` — for all small `δ`, a refinement `(𝕋*, Y*)` (index subset, tubes
unchanged, shades cut) with GWZ Definition 2.2 at a constant `1 ≤ C₀ ≤ δ^{-η'}`, per-tube floor
`2δ^{2η}|T| ≤ |Y*(i)|`, tube count `1 ≤ δ|𝕋*|`, mass retention `δ^{η/2}`, and GWZ (87) at every
grid scale at exponent `η/2` (`Kakeya.VeryNotSticky.LocalMassAt δ (η/2)`).

Chain: step U at fullness exponent `η` → `N/q + 1` bridges at the sparse indices
(`q = Kakeya.VeryNotSticky.sparseStep η N`, loss exponent `ε = η'/(4(64/η+2))`) → step CD at
fullness exponent `η + 2η'` → transport and interpolation. Admissibility: `0 < η'`, `8η' < η`,
`η ≤ 1` (see the module docstring for where each is spent). -/
theorem eventually_exists_localMassRefinement_slack {η η' : ℝ} (hη' : 0 < η')
    (h8 : 8 * η' < η) (hη1 : η ≤ 1) :
    ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-η) →
        δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        (1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (1 + 2 * η) * (s.card : ℝ≥0∞) →
        BandUniformRefinementLocalMassSlack δ η η' s T := by
  have h3 : 3 * η' < η := by linarith
  have hη0 : 0 < η := by linarith
  -- the per-bridge loss exponent
  set ε : ℝ := η' / (4 * (64 / η + 2)) with hε_def
  have hD : (0 : ℝ) < 64 / η + 2 := by positivity
  have hε0 : 0 < ε := by positivity
  have hεD : ε * (64 / η + 2) = η' / 4 := by
    have hDne : (64 / η + 2 : ℝ) ≠ 0 := hD.ne'
    rw [hε_def]
    field_simp
  have hε4 : ε ≤ η' / 4 := by
    have h64η : (0 : ℝ) ≤ 64 / η := by positivity
    rw [hε_def]
    apply div_le_div_of_nonneg_left hη'.le (by norm_num)
    linarith
  filter_upwards [eventually_exists_uniformBand.{u} (η_f := η) hη' h3 hη1 (by linarith),
    eventually_exists_classDenseRefinement_slack.{u} (η_f := η + 2 * η') hη' h3 hη1 le_rfl,
    Kakeya.VNSUniform.eventually_card_thresholds',
    eventually_coarseLoss_absorb (η := ε) (K := 4) hε0 (by norm_num),
    eventually_gridFine (by positivity : 0 < η / 64),
    eventually_nnreal_le_rpow_neg (9261 * (ShadedTube.ssfUniformConst 3) ^ 5)
      (by linarith : 0 < η' / 4)]
    with δ HU HCD hthr hloss hgrid hK
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  intro ι s T hball hmax hfull hcard
  classical
  have hδne : δ ≠ 0 := hδ0.ne'
  have hδE0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hδne
  have hδEtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  set N := Tube.ssfGridLen δ with hN
  -- the grid is fine: `64 ≤ η N`
  have h64 : 64 ≤ η * (N : ℝ) := by
    have h : η / 64 * (N : ℝ) = η * N / 64 := by ring
    linarith
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h] at h64
      norm_num at h64
    · exact h
  set q := sparseStep η N with hq_def
  have hq : 0 < q := sparseStep_pos (by linarith)
  have hgap : (q : ℝ) / N ≤ η / 32 := sparseStep_div_le hη0.le hNpos
  have hsteps : ((N / q : ℕ) : ℝ) ≤ 64 / η := div_sparseStep_le hη0 h64
  -- step U: the band and the uniformisation
  obtain ⟨s₀, hs₀, T₀, htube₀, hsh₀, ⟨𝒱₀⟩, href₀, hret₀, -⟩ := HU s T hball hmax hfull
  have hball₀ : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1 := by
    intro i hi
    rw [show (T₀ i).carrier = (T i).carrier from
      congrArg (fun U : Tube δ _ => U.carrier) (htube₀ i)]
    exact hball i (hs₀ hi)
  have hposS : 0 < ∑ i ∈ s, volume (T i).shade :=
    sum_volume_shade_pos_of_rpow_le_fullness hδ0 hfull
  have hpos₀ : 0 < ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade := by
    refine lt_of_lt_of_le ?_ hret₀
    exact ENNReal.mul_pos (ENNReal.rpow_pos (by exact_mod_cast hδ0) hδEtop).ne' hposS.ne'
  -- the cardinality budget `|s₀| ≤ δ^{-4}` and the loss bound of every bridge
  have hcard4 : ∀ n : ℕ, 0 < n → n ≤ s₀.card → (n : ℝ≥0) ≤ δ ^ (-(4 : ℝ)) := by
    intro n _ hn
    have h1 : (s.card : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-4 : ℝ) :=
      Kakeya.VNSUniform.card_le_rpow_neg_four_enn hδ0 hδ1 hδC s T hball hη1 hmax
    have h2 : (n : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by
      exact_mod_cast hn.trans (Finset.card_le_card hs₀)
    have h3 := h2.trans h1
    rw [← ENNReal.coe_rpow_of_ne_zero hδne, ← ENNReal.coe_natCast, ENNReal.coe_le_coe] at h3
    exact h3
  have hL : ∀ n : ℕ, 0 < n → n ≤ s₀.card →
      ((rhoTubesSection9Loss 3 n δ : ℝ≥0) : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-ε) :=
    fun n hn hns => hloss n hn (hcard4 n hn hns)
  -- steps `B_m`: the bridge chain
  obtain ⟨sJ, TJ, hsJ, htubeJ, hshJ, hrefJ, hchain⟩ :=
    exists_bridgeChain_rpow hδ0 hδ1 𝒱₀ hball₀ hpos₀ hL hq
  -- the chain's retention in the exponent currency
  have hcJ_ge : δ ^ (η' / 4) ≤ (δ ^ ε) ^ (N / q + 1) := by
    apply rpow_le_rpow_pow_of_mul_le hδ0 hδ1
    push_cast
    calc ε * (((N / q : ℕ) : ℝ) + 1) ≤ ε * (64 / η + 2) := by gcongr; linarith
      _ = η' / 4 := hεD
  -- step CD: the class-dense refinement of the chain's output
  have hballJ : ∀ i ∈ sJ, (TJ i).carrier ⊆ closedBall (0 : E3) 1 := by
    intro i hi
    rw [show (TJ i).carrier = (T₀ i).carrier from
      congrArg (fun U : Tube δ _ => U.carrier) (htubeJ i)]
    exact hball₀ i (hsJ hi)
  have hmaxJ : maxDensity sJ (fun i ↦ (TJ i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-η) :=
    (maxDensity_le_of_subset_of_tube_eq (hsJ.trans hs₀)
      (fun i => (htubeJ i).trans (htube₀ i))).trans hmax
  have hrefJ0 : IsCRefinement sJ (fun i ↦ (TJ i).toShadedBody) s (fun i ↦ (T i).toShadedBody)
      (δ ^ (3 * η' / 2) * (δ ^ ε) ^ (N / q + 1)) := hrefJ.trans href₀
  have hfullJ : δ ^ (η + 2 * η') ≤ ShadedBody.fullness sJ (fun i ↦ (TJ i).toShadedBody) := by
    have hsne : s.Nonempty := Finset.nonempty_of_sum_ne_zero hposS.ne'
    obtain ⟨i₀, hi₀⟩ := hsne
    have hV : 0 < ∑ i ∈ s, volume (T i).toShadedBody.carrier := by
      refine lt_of_lt_of_le (Tube.volume_pos_and_lt_top hδ0 hδ1 (T i₀).toTube).1 ?_
      exact Finset.single_le_sum (f := fun i => volume (T i).toShadedBody.carrier)
        (fun i _ => zero_le) hi₀
    have h1 := IsCRefinement.mul_fullness_le _ _ _ _ hV hrefJ0
    have hc : δ ^ (2 * η') ≤ δ ^ (3 * η' / 2) * (δ ^ ε) ^ (N / q + 1) := by
      calc δ ^ (2 * η') ≤ δ ^ (3 * η' / 2 + η' / 4) :=
            NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
        _ ≤ δ ^ (3 * η' / 2) * (δ ^ ε) ^ (N / q + 1) := rpow_add_le_mul hδ0 le_rfl hcJ_ge
    calc δ ^ (η + 2 * η') = δ ^ (2 * η') * δ ^ η := by rw [NNReal.rpow_add hδne, mul_comm]
      _ ≤ (δ ^ (3 * η' / 2) * (δ ^ ε) ^ (N / q + 1)) *
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) := mul_le_mul' hc hfull
      _ ≤ ShadedBody.fullness sJ (fun i ↦ (TJ i).toShadedBody) := h1
  obtain ⟨sF, hsF, TF, htubeF, hshF, huni, hfloor, hrefF, -⟩ := HCD sJ TJ hballJ hmaxJ hfullJ
  -- step TR: the local mass of the final family
  have hcJ : (0 : ℝ≥0) < (δ ^ ε) ^ (N / q + 1) := pow_pos (NNReal.rpow_pos hδ0) _
  have hcF : (0 : ℝ≥0) < δ ^ (2 * η') := NNReal.rpow_pos hδ0
  have hc : δ ^ (9 * η' / 4) ≤ (δ ^ ε) ^ (N / q + 1) * δ ^ (2 * η') := by
    have h : (9 * η' / 4 : ℝ) = η' / 4 + 2 * η' := by ring
    rw [h]
    exact rpow_add_le_mul hδ0 hcJ_ge le_rfl
  have hlm := localMassAt_half_of_bridgeChain hδ0 hδ1 𝒱₀ hball₀ hcJ hcF hrefJ hrefF hη' h8 hε4
    hq hgap le_rfl hc hK hchain
  -- the total retention `δ^{15η'/4} ≥ δ^{η/2}` — clause (f)
  have hrefT : IsCRefinement sF (fun i ↦ (TF i).toShadedBody) s (fun i ↦ (T i).toShadedBody)
      ((δ ^ (3 * η' / 2) * (δ ^ ε) ^ (N / q + 1)) * δ ^ (2 * η')) := hrefF.trans hrefJ0
  have hcT : δ ^ (η / 2) ≤ (δ ^ (3 * η' / 2) * (δ ^ ε) ^ (N / q + 1)) * δ ^ (2 * η') := by
    calc δ ^ (η / 2) ≤ δ ^ ((3 * η' / 2 + η' / 4) + 2 * η') :=
          NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      _ ≤ (δ ^ (3 * η' / 2) * (δ ^ ε) ^ (N / q + 1)) * δ ^ (2 * η') :=
          rpow_add_le_mul hδ0 (rpow_add_le_mul hδ0 le_rfl hcJ_ge) le_rfl
  have hmass : (δ : ℝ≥0∞) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ sF, volume (TF i).shade := by
    refine le_trans ?_ hrefT.2
    rw [← ENNReal.coe_rpow_of_ne_zero hδne]
    exact mul_le_mul' (ENNReal.coe_le_coe.mpr hcT) le_rfl
  -- the composed inclusions
  have hsF_s : sF ⊆ s := (hsF.trans hsJ).trans hs₀
  have htubeF_T : ∀ i, (TF i).toTube = (T i).toTube :=
    fun i => ((htubeF i).trans (htubeJ i)).trans (htube₀ i)
  have hshF_T : ∀ i, (TF i).shade ⊆ (T i).shade :=
    fun i => ((hshF i).trans (hshJ i)).trans (hsh₀ i)
  -- clause (e): the tube count `1 ≤ δ |𝕋*|`, from `hcard` and the retention
  have hcardF : (1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) * (sF.card : ℝ≥0∞) := by
    have hsne : s.Nonempty := Finset.nonempty_of_sum_ne_zero hposS.ne'
    obtain ⟨i₀, hi₀⟩ := hsne
    set v : ℝ≥0∞ := volume (T i₀).carrier with hv
    have hvol : ∀ i ∈ s, volume (T i).carrier = v := fun i _ =>
      Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
    have hvpos := Tube.volume_pos_and_lt_top hδ0 hδ1 (T i₀).toTube
    have hYs : ((δ ^ η : ℝ≥0) : ℝ≥0∞) * ((s.card : ℝ≥0∞) * v) ≤ ∑ i ∈ s, volume (T i).shade :=
      ShadedBody.coe_fullness_mul_le_sum_volume_shade s (fun i ↦ (T i).toShadedBody) hfull
        (fun i hi => (hvol i hi).symm.le)
    have hret : ∑ i ∈ sF, volume (TF i).shade ≤ (sF.card : ℝ≥0∞) * v := by
      calc ∑ i ∈ sF, volume (TF i).shade ≤ ∑ _i ∈ sF, v := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [← hvol i (hsF_s hi)]
            calc volume (TF i).shade ≤ volume (TF i).carrier := measure_mono (TF i).shade_subset
              _ = volume (T i).carrier :=
                  congrArg volume (congrArg (fun U : Tube δ _ => U.carrier) (htubeF_T i))
        _ = (sF.card : ℝ≥0∞) * v := by rw [Finset.sum_const, nsmul_eq_mul]
    have h1 : (δ : ℝ≥0∞) ^ (2 * η) * (s.card : ℝ≥0∞) * v ≤ (sF.card : ℝ≥0∞) * v := by
      calc (δ : ℝ≥0∞) ^ (2 * η) * (s.card : ℝ≥0∞) * v
          ≤ (δ : ℝ≥0∞) ^ (η / 2 + η) * (s.card : ℝ≥0∞) * v :=
            mul_le_mul' (mul_le_mul'
              (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)) le_rfl) le_rfl
        _ = (δ : ℝ≥0∞) ^ (η / 2) * (((δ ^ η : ℝ≥0) : ℝ≥0∞) * ((s.card : ℝ≥0∞) * v)) := by
            rw [ENNReal.coe_rpow_of_ne_zero hδne, ENNReal.rpow_add _ _ hδE0 hδEtop]
            ring
        _ ≤ (δ : ℝ≥0∞) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade := mul_le_mul' le_rfl hYs
        _ ≤ ∑ i ∈ sF, volume (TF i).shade := hmass
        _ ≤ (sF.card : ℝ≥0∞) * v := hret
    have h2 : (δ : ℝ≥0∞) ^ (2 * η) * (s.card : ℝ≥0∞) ≤ (sF.card : ℝ≥0∞) :=
      (ENNReal.mul_le_mul_iff_left hvpos.1.ne' hvpos.2.ne).mp h1
    calc (1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (1 + 2 * η) * (s.card : ℝ≥0∞) := hcard
      _ = (δ : ℝ≥0∞) * ((δ : ℝ≥0∞) ^ (2 * η) * (s.card : ℝ≥0∞)) := by
          rw [ENNReal.rpow_add _ _ hδE0 hδEtop, ENNReal.rpow_one, mul_assoc]
      _ ≤ (δ : ℝ≥0∞) * (sF.card : ℝ≥0∞) := mul_le_mul' le_rfl h2
  exact ⟨sF, TF, hsF_s, htubeF_T, hshF_T, huni, hfloor, hcardF, hmass, hlm.1⟩

/-! ### Residue 1, discharged as stated -/

/-- **Residue 1 of the §9.3 setup — `Kakeya.VeryNotSticky.LocalMassRefinementResidue η η'` — holds
for every admissible `(η, η')`: `0 < η'`, `8η' < η`, `η ≤ 1`.** The `∀ᶠ` theorem
`Kakeya.VeryNotSticky.eventually_exists_localMassRefinement_slack` followed by
`Kakeya.VeryNotSticky.BandUniformRefinementLocalMassSlack.toBandUniformRefinementLocalMass`. The
residue's statement is untouched. -/
theorem localMassRefinementResidue {η η' : ℝ} (hη' : 0 < η') (h8 : 8 * η' < η) (hη1 : η ≤ 1) :
    LocalMassRefinementResidue.{u} η η' := by
  unfold LocalMassRefinementResidue
  filter_upwards [eventually_exists_localMassRefinement_slack.{u} hη' h8 hη1,
    Kakeya.VNSUniform.eventually_card_thresholds'] with δ H hthr
  intro ι s T hball hmax hfull hcard
  exact (H s T hball hmax hfull hcard).toBandUniformRefinementLocalMass hthr.2.1 (by linarith)

/-! ### The assembly, reduced to residue 2 -/

/-- **`Kakeya.VeryNotSticky.exists_setup_caseSideData` from `Kakeya.VeryNotSticky.SideDataResidue`
alone.** `Kakeya.VeryNotSticky.exists_setup_caseSideData_of_residues` at `η' = η/9` with residue 1
discharged by `Kakeya.VeryNotSticky.localMassRefinementResidue` (`η ≤ 1` from
`Kakeya.VeryNotSticky.CaseParams.slab`: `9η < β/2 ≤ 1/2`). The binder list and the conclusion
are the target's, character for character, plus the one hypothesis `hSide`; the two `example`s
below pin this to the target's type. -/
theorem exists_setup_caseSideData_of_sideDataResidue {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
    (hSide : SideDataResidue.{u} β ζ exscal ϱ η τ τ') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ') := by
  have hη1 : η ≤ 1 := by
    have h1 := params.slab
    have h2 := params.hτ
    linarith
  exact exists_setup_caseSideData_of_residues hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
    (η' := η / 9) (by positivity) (by linarith)
    (localMassRefinementResidue.{u} (by positivity) (by linarith) hη1) hSide

/-- **Tripwire 1**: with `Kakeya.VeryNotSticky.SideDataResidue` supplied at every parameter, the
new theorem inhabits `Kakeya.VeryNotSticky.SetupCaseSideDataStatement` — the target's statement
with every binder explicit, itself pinned to `Kakeya.VeryNotSticky.exists_setup_caseSideData`. -/
example (hSide : ∀ {β ζ exscal ϱ η τ τ' : ℝ}, SideDataResidue.{u} β ζ exscal ϱ η τ τ') :
    SetupCaseSideDataStatement.{u} :=
  fun hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w =>
    exists_setup_caseSideData_of_sideDataResidue hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
      hSide

/-- **Tripwire 2**: the same, directly against the type of the target declaration. If the target's
binders or conclusion move, this stops typechecking. -/
example (hSide : ∀ {β ζ exscal ϱ η τ τ' : ℝ}, SideDataResidue.{u} β ζ exscal ϱ η τ τ') :
    SetupCaseSideDataStatement.{u} :=
  fun hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w =>
    exists_setup_caseSideData_of_sideDataResidue hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
      hSide

end Kakeya.VeryNotSticky

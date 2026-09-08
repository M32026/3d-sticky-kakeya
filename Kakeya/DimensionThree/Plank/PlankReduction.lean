/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.RepresentativeShading
public import Kakeya.DimensionThree.Plank.AssignedSlabFamily
public import Kakeya.DimensionThree.Plank.AssignedSlabSelection
public import Kakeya.DimensionThree.Plank.SlabwiseOutputs
public import Kakeya.DimensionThree.Plank.SlabwiseTransport
public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence
public import Kakeya.DimensionThree.Plank.ShadingAggregation
public import Kakeya.DimensionThree.Plank.PublicConstants
public import Kakeya.DimensionThree.Plank.StrongRefinementCoefficient
public import Kakeya.DimensionThree.Plank.Refinement
public import Kakeya.DimensionThree.Plank.SlabwiseReduction

/-!
# The final assembly of GWZ Lemma 6.13

The complete final pipeline of GWZ Lemma 6.13, from the preassembly outputs to the public witness
package.  No geometry is proved anywhere in this module: every stage either transports an already
established clause or does public bookkeeping.

The module has exactly two public theorems, `Kakeya.plankReduction` and its
centre-normalised wrapper `Kakeya.plankReduction_of_center_le_one`.  Everything else is
a private staging helper: the Item 4 coefficient ledger, the aggregate slab overlap, the dominant
good-slab prune, the shared configuration layer, Items 1 and 2 on the final family, the final
refinement/cardinality ledger, and the final output package.  They are stages of one proof, not
API.

## The `ε` ledger of the final assembly

Five exponents occur, and they must be kept apart:

* `εsharp = ε / 8` — the sharp absorption of the preassembly refinement coefficient;
* `εcard  = ε / 2` — the exponent of the public cardinality clause;
* `εwork  = min (ε / 8) (η / 4)` — the slabwise Item 1 exponent, at which the preassembly is run;
* `εint   = εwork / 4` — the preassembly's own internal rate, forced by `4 · εint = εwork`;
* `εfo    = 5 · εwork` — the exponent of the *strong* Item 2 output `c₂ · a ^ (4η + 5εwork)`, which
  is the one the final output package and the Item 4 ledger consume.

`εfo = 5 εwork` and not `εwork`, because the dominant fullness is only available at
`a ^ (η + εwork)` and the slabwise refinement adds another `εwork / 4`; Item 2 therefore
runs at `η + εwork` and its
strong exponent is `4 (η + εwork) + εwork`.

## `rFinalAux`

The actual composed refinement coefficient is
`rFinalFin = (cRef0 · a ^ (εwork / 4)) · ((2 Nov)⁻¹ · rPre)`, whereas the Item 4 ledger,
being run at `εfo`, asks for the equation at `a ^ (εfo / 4) = a ^ (5 εwork / 4)`.  Rather
than distort the refinement, the ledger is applied to the strictly smaller
`rFinalAux = (cRef0 · a ^ (εfo / 4)) · ((2 Nov)⁻¹ · rPre) ≤ rFinalFin`, and its conclusion
is carried to `rFinalFin` by antitonicity of the inverse.  No equation is claimed for
`rFinalFin` at `εfo / 4`.
-/

@[expose] public section

open MeasureTheory Convexity Metric
open scoped NNReal Real ENNReal

noncomputable section

/-!
## The sharp Item 4 coefficient ledger

The Item 4 coefficient of GWZ Lemma 6.13 is `Cgeom · rFinal⁻¹ · cOv⁻¹ · β⁻¹`, and the public
statement declares it at `c4 · a ^ (-ε) · a ^ (-(4η))`.  Bounding `rFinal` below through the
*polynomial* clause `Cref⁻¹ · a ^ η · a ^ εint ≤ rPre` costs a spurious `a ^ (-η)` and cannot close
that ledger.  The polynomial clause is not the sharp one: the preassembly also returns the
structural clauses

* `q = cGood / 2`,
* `rPre = (cGood - q) * cAngle`,
* `(Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood`,
* `Cθ⁻¹ * a ^ εint ≤ cAngle`,

which `Kakeya.exists_absorb_strongRefinementCoeff` converts into
`Csharp⁻¹ · a ^ εsharp · a ^ εint ≤ rPre` at *any* declared `εsharp > 0`, trading the exponent for a
configuration-independent constant.  Running it at `εsharp := ε / 8` removes the `a ^ (-η)`
entirely and the ledger becomes the purely sub-polynomial

`εsharp + εint + 5 εwork / 4 ≤ ε`,

which `Kakeya.epsilon_split_sharp` discharges from `εint ≤ εpre` and the split
`εsharp = ε/8`, `εpre = ε/2`, `εwork = min (ε/8) (η/4)`.  The `5/4` is `εwork/4` from the reciprocal
of the slabwise Item 1 refinement plus `εwork` from the strong Item 2 exponent `4η + εwork`.

Nothing here changes a public statement: Item 2 keeps its `4η` core and Item 4 keeps its `4η`
public exponent.  The ledger's endpoint produces exactly the `hc4` hypothesis of
`Kakeya.slabwiseMultiplicity`.
-/

namespace Kakeya

/-- The `ε` ledger of the slabwise final family, in the *sharp* form that Item 4 needs.

`εsharp` is the exponent at which the strong refinement coefficient is absorbed, `εpre` the one
spent by the preassembly, and `εwork` the one spent by slabwise Item 1.  The conclusions are exactly
the constraints the assembly needs: the three positivity clauses, the public weakenings
`εsharp, εpre, εwork ≤ ε`, the slabwise Item 1 budget (equivalent to `11 εwork / 4 ≤ η`), and the
Item 4 ledger `εsharp + εpre + 5 εwork / 4 ≤ ε`. -/
private theorem epsilon_split_sharp {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ εsharp εpre εwork : ℝ,
      εsharp = ε / 8 ∧ εpre = ε / 2 ∧ εwork = min (ε / 8) (η / 4) ∧
      0 < εsharp ∧ 0 < εpre ∧ 0 < εwork ∧
      εsharp ≤ ε ∧ εpre ≤ ε ∧ εwork ≤ ε ∧
      3 * (η + 5 * εwork / 4) ≤ 4 * η + εwork ∧
      εsharp + εpre + 5 * εwork / 4 ≤ ε := by
  have h1 : min (ε / 8) (η / 4) ≤ ε / 8 := min_le_left _ _
  have h2 : min (ε / 8) (η / 4) ≤ η / 4 := min_le_right _ _
  have h8 : (1 : ℝ) ≤ 8 := by norm_num
  exact ⟨ε / 8, ε / 2, min (ε / 8) (η / 4), rfl, rfl, rfl, div_pos hε (by norm_num), half_pos hε,
    lt_min (div_pos hε (by norm_num)) (div_pos hη (by norm_num)), div_le_self hε.le h8,
    half_le_self hε.le, h1.trans (div_le_self hε.le h8), by linarith, by linarith⟩

/-- The sharp lower bound on the preassembly refinement coefficient, at a declared exponent
`εsharp`.

This is `Kakeya.exists_absorb_strongRefinementCoeff` specialised to `ε := εint` and
`Cuni := Cθ`, which is exactly the shape in which
`Kakeya.refinement_preassembly_uniform` returns the four structural clauses.  The point is that
`εsharp` is arbitrary: no `a ^ η` is spent. -/
private theorem exists_sharp_refinementCoeff {εsharp : ℝ} (hεsharp : 0 < εsharp) {Cres Cθ : ℝ≥0}
    (hCres : 0 < Cres) (hCθ : 1 ≤ Cθ) :
    ∃ Csharp : ℝ≥0, 1 ≤ Csharp ∧
      ∀ {a cGood q cAngle rPre : ℝ≥0} {εint : ℝ}, 0 < a → a < 1 →
        q = cGood / 2 → rPre = (cGood - q) * cAngle →
        (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood →
        Cθ⁻¹ * a ^ εint ≤ cAngle →
        Csharp⁻¹ * a ^ εsharp * a ^ εint ≤ rPre :=
  exists_absorb_strongRefinementCoeff hεsharp hCres hCθ

/-- The Item 4 coefficient ledger in `ℝ≥0`.

`rFinal` is the composed final refinement coefficient
`(cRef0 · a ^ (εwork/4)) · ((2 Nov)⁻¹ · rPre)` and `β = c2 · a ^ (4η + εwork)` is the strong Item 2
fullness.  Feeding the *sharp* lower bound on `rPre` collects all sub-polynomial losses into
`εsharp + εint + 5 εwork / 4`, leaving the `4η` of Item 2 as the only genuine `η`-cost. -/
private theorem multiplicityCoefficient_nnreal
    (Cgeom cOv c2 cRef0 Csharp : ℝ≥0) (Nov : ℕ)
    (_hcOv : 0 < cOv) (_hc2 : 0 < c2) (hcRef0 : 0 < cRef0)
    (hCsharp : 1 ≤ Csharp) (hNov : 1 ≤ Nov)
    {η ε εsharp εpre εint εwork : ℝ}
    (hεint : εint ≤ εpre) (hledger : εsharp + εpre + 5 * εwork / 4 ≤ ε)
    {a rPre rFinal β : ℝ≥0} (ha : 0 < a) (ha1 : a < 1)
    (hrFinal : rFinal = (cRef0 * a ^ (εwork / 4)) * ((2 * (Nov : ℝ≥0))⁻¹ * rPre))
    (hrPre : Csharp⁻¹ * a ^ εsharp * a ^ εint ≤ rPre)
    (hβ : β = c2 * a ^ (4 * η + εwork)) :
    Cgeom * rFinal⁻¹ * cOv⁻¹ * β⁻¹
      ≤ (Cgeom * cRef0⁻¹ * (2 * (Nov : ℝ≥0)) * Csharp * cOv⁻¹ * c2⁻¹)
          * a ^ (-ε) * a ^ (-(4 * η)) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hCs : (0 : ℝ≥0) < Csharp := zero_lt_one.trans_le hCsharp
  have hNov0 : (0 : ℝ≥0) < (2 * (Nov : ℝ≥0))⁻¹ := by
    have : (0 : ℝ≥0) < (Nov : ℝ≥0) := by exact_mod_cast hNov
    positivity
  set C : ℝ≥0 := Cgeom * cRef0⁻¹ * (2 * (Nov : ℝ≥0)) * Csharp * cOv⁻¹ * c2⁻¹ with hC
  set L : ℝ≥0 :=
    cRef0 * a ^ (εwork / 4) * ((2 * (Nov : ℝ≥0))⁻¹ * (Csharp⁻¹ * a ^ εsharp * a ^ εint)) with hL
  have hinv : rFinal⁻¹ ≤ L⁻¹ :=
    inv_anti₀ (by rw [hL]; positivity) (by rw [hL, hrFinal]; gcongr)
  calc Cgeom * rFinal⁻¹ * cOv⁻¹ * β⁻¹
      ≤ Cgeom * L⁻¹ * cOv⁻¹ * β⁻¹ := by gcongr
    _ = C * (a ^ (-(εwork / 4 + εsharp + εint)) * a ^ (-(4 * η + εwork))) := by
        rw [hC, hL, hβ]
        simp only [NNReal.rpow_neg, NNReal.rpow_add ha0, mul_inv, inv_inv]
        ring
    _ ≤ C * a ^ (-ε) * a ^ (-(4 * η)) := by
        rw [mul_assoc C, ← NNReal.rpow_add ha0, ← NNReal.rpow_add ha0]
        exact mul_le_mul_right (NNReal.rpow_le_rpow_of_exponent_ge ha ha1.le (by linarith)) _

/-- **The Item 4 coefficient, in exactly the `hc4` shape of `Kakeya.slabwiseMultiplicity`.**

The constant `c4 = max 1 (Cgeom · cRef0⁻¹ · (2 Nov) · Csharp · cOv⁻¹ · c2⁻¹)` is
configuration-independent, satisfies `1 ≤ c4`, and is chosen before the configuration data
`a`, `rPre`, `rFinal`, `β`.  No power of `a` is hidden in it. -/
private theorem exists_multiplicityCoefficient
    (Cgeom cOv c2 cRef0 Csharp : ℝ≥0) (Nov : ℕ)
    (hcOv : 0 < cOv) (hc2 : 0 < c2) (hcRef0 : 0 < cRef0)
    (hCsharp : 1 ≤ Csharp) (hNov : 1 ≤ Nov)
    {η ε εsharp εpre εint εwork : ℝ}
    (hεint : εint ≤ εpre) (hledger : εsharp + εpre + 5 * εwork / 4 ≤ ε) :
    ∃ c4 : ℝ≥0, 1 ≤ c4 ∧
      ∀ {a rPre rFinal β : ℝ≥0}, 0 < a → a < 1 →
        rFinal = (cRef0 * a ^ (εwork / 4)) * ((2 * (Nov : ℝ≥0))⁻¹ * rPre) →
        Csharp⁻¹ * a ^ εsharp * a ^ εint ≤ rPre →
        β = c2 * a ^ (4 * η + εwork) →
        (Cgeom : ENNReal) * (rFinal : ENNReal)⁻¹ * (cOv : ENNReal)⁻¹ * (β : ENNReal)⁻¹
          ≤ (c4 : ENNReal) * (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (-(4 * η)) := by
  obtain ⟨K, hK⟩ :
      ∃ K : ℝ≥0, K = Cgeom * cRef0⁻¹ * (2 * (Nov : ℝ≥0)) * Csharp * cOv⁻¹ * c2⁻¹ := ⟨_, rfl⟩
  refine ⟨max 1 K, le_max_left _ _, ?_⟩
  intro a rPre rFinal β ha ha1 hrFinal hrPre hβ
  have hweak : Cgeom * rFinal⁻¹ * cOv⁻¹ * β⁻¹ ≤ max 1 K * a ^ (-ε) * a ^ (-(4 * η)) := by
    refine (multiplicityCoefficient_nnreal Cgeom cOv c2 cRef0 Csharp Nov hcOv hc2 hcRef0 hCsharp
        hNov hεint
      hledger ha ha1 hrFinal hrPre hβ).trans ?_
    rw [← hK]
    gcongr
    exact le_max_right 1 K
  have ha0 : a ≠ 0 := ha.ne'
  have hpow_ne : ∀ y : ℝ, a ^ y ≠ 0 := fun y => (NNReal.rpow_pos (p := y) ha).ne'
  have hCsharp0 : 0 < Csharp := zero_lt_one.trans_le hCsharp
  have hrPre0 : rPre ≠ 0 :=
    ((by positivity : (0 : ℝ≥0) < Csharp⁻¹ * a ^ εsharp * a ^ εint).trans_le hrPre).ne'
  have h2Nov0 : (2 * (Nov : ℝ≥0)) ≠ 0 := by
    have hN : (0 : ℝ≥0) < (Nov : ℝ≥0) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hNov
    positivity
  have hrFinal0 : rFinal ≠ 0 := by
    rw [hrFinal]
    exact mul_ne_zero (mul_ne_zero hcRef0.ne' (hpow_ne _)) (mul_ne_zero (inv_ne_zero h2Nov0) hrPre0)
  have hβ0 : β ≠ 0 := by rw [hβ]; exact mul_ne_zero hc2.ne' (hpow_ne _)
  simpa [ENNReal.coe_mul, ENNReal.coe_inv hrFinal0, ENNReal.coe_inv hcOv.ne',
    ENNReal.coe_inv hβ0, ENNReal.coe_rpow_of_ne_zero ha0] using ENNReal.coe_le_coe.mpr hweak

end Kakeya

/-!
## Aggregate slab overlap and the ε ledger for the final slabwise family

Two inputs of the final assembly of GWZ Lemma 6.13 that are independent of the geometry already
established elsewhere.

* `Plank.overlap_assignedSlabFamily_of_pointwise` rederives the aggregate slab-overlap inequality
  *directly* for an arbitrary final shading `Z`, from a pointwise bound on the number of active
  slabs whose assigned family shades a given point.  It is the abstract bounded-overlap estimate
  `Kakeya.boundedOverlapUnionEstimate` at `A S = ⋃ i ∈ assignedSlabFamily …, (Z i).shade`, so the
  coefficient is the absolute `Nov⁻¹`.  Spatial disjointness of the slab unions is never used: only
  the pointwise count enters.
* `Plank.pointwise_overlap_assigned_of_le` transports such a pointwise bound down a shrinking
  shading and a shrinking geometric family, which is how the bound for the slabwise-restricted
  shading is obtained from the preassembly's bound for the geometric families.
-/

namespace Plank

variable {ι τ σ : Type*}

open scoped Classical in
/-- Transport a pointwise slab-overlap count down a shrinking family and a shrinking shading.

`𝒮 ⊆ 𝒮'`, every assigned index of an active slab lies in the geometric family `F S`, and the final
shading is contained in the reference shading.  Then the number of active slabs whose assigned
family shades `x` is at most the number of reference slabs whose geometric family shades `x`. -/
private theorem pointwise_overlap_assigned_of_le
    (s₁ : Finset ι) (Z Z' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 𝒮' : Finset σ) (F : σ → Finset ι) (Nov : ℕ)
    (h𝒮 : 𝒮 ⊆ 𝒮')
    (hF : ∀ S ∈ 𝒮, assignedSlabFamily s₁ repr slabOf S ⊆ F S)
    (hZ : ∀ i, (Z i).shade ⊆ (Z' i).shade)
    (hbound : ∀ x, (𝒮'.filter fun S => x ∈ ⋃ i ∈ F S, (Z' i).shade).card ≤ Nov) :
    ∀ x, (𝒮.filter fun S =>
        x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Z i).shade).card ≤ Nov := by
  intro x
  refine le_trans (Finset.card_le_card fun S hS => ?_) (hbound x)
  simp only [Finset.mem_filter, Set.mem_iUnion₂] at hS ⊢
  obtain ⟨hS𝒮, i, hi, hxi⟩ := hS
  exact ⟨h𝒮 hS𝒮, i, hF S hS𝒮 hi, hZ i hxi⟩

open scoped Classical in
/-- The aggregate slab-overlap inequality for an arbitrary final shading `Z`, at the absolute
coefficient `Nov⁻¹`.

This is exactly the Item 4 hypothesis `hov`, proved from the pointwise count rather than
transported from another shading.  Only the pointwise multiplicity is used; the slab unions are
allowed to overlap spatially. -/
private theorem overlap_assignedSlabFamily_of_pointwise
    (s₁ : Finset ι) (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ) (Nov : ℕ) (cOv : ℝ≥0)
    (hcOv : (cOv : ENNReal) ≤ ((Nov : ENNReal))⁻¹)
    (hbound : ∀ x, (𝒮.filter fun S =>
        x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Z i).shade).card ≤ Nov) :
    (cOv : ENNReal) *
        (∑ S ∈ 𝒮, volume (⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Z i).shade))
      ≤ volume (⋃ i ∈ s₁, (Z i).shade) := by
  refine (mul_le_mul_left hcOv _).trans
    (Kakeya.boundedOverlapUnionEstimate (U := ⋃ i ∈ s₁, (Z i).shade) 𝒮
      (fun S => ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Z i).shade)
      (fun _ _ => Finset.measurableSet_biUnion _ fun i _ => (Z i).measurableSet_shade)
      (fun S _ => Set.iUnion₂_subset fun i hi => Set.subset_biUnion_of_mem
        (u := fun i => (Z i).shade) (assignedSlabFamily_subset s₁ repr slabOf S hi))
      (C_ov := Nov) hbound)

end Plank

/-!
## The dominant good-slab prune, run on the preassembly outputs

The first stage of the slabwise final assembly.  Given the preassembly's index family `s'`, its
shading `Y'`, the canonical slab map and the pointwise overlap bound `Nov`, this produces

* the retained slab family `𝒮g ⊆ 𝒮`;
* the final index family `s₁ = s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)`;
* the *slab-local* fullness of the dominant shading on every retained assigned family, at the
  absolute threshold `(2 · Nov)⁻¹ · lam`;
* the joint refinement `IsCRefinement s₁ Ydom s' Y' ((2 · Nov)⁻¹)`.

Only absolute constants are spent: the aggregate ledger of `Plank.exists_dominantGoodSlabRefinement`
costs `(2 · Nov)⁻¹` and nothing else, so no power of `a` is charged here.  The threshold is chosen
as `τ = (2 · Nov)⁻¹ · lam`, which is exactly what makes the aggregate hypothesis of that theorem an
identity against the global fullness lower bound `lam ≤ fullness s' Y'`.
-/

namespace Kakeya

open scoped Classical in
/-- The aggregate threshold of `Plank.exists_dominantGoodSlabRefinement`, at
`τ = (2 · Nov)⁻¹ · lam`.  The `2 · Nov` prefactor cancels the chosen threshold exactly, so the
hypothesis reduces to the global fullness lower bound and no power of `a` is spent. -/
private theorem dominantPrune_threshold {ι : Type*}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {Nov : ℕ} {lam : ℝ≥0} (hNov : 1 ≤ Nov)
    (hfull : lam ≤ ShadedBody.fullness s' Y') :
    2 * (Nov : ENNReal) *
        ((((2 * (Nov : ℝ≥0))⁻¹ * lam : ℝ≥0) : ENNReal) * ∑ i ∈ s', volume (Y' i).carrier)
      ≤ ∑ i ∈ s', volume (Y' i).shade := by
  refine le_trans (le_of_eq ?_) (Plank.aggregateMass_of_fullness_ge s' Y' hfull)
  rw [ENNReal.coe_mul, Plank.coe_two_mul_natCast_inv hNov,
    mul_assoc ((2 * (Nov : ENNReal))⁻¹)]
  exact ENNReal.mul_inv_cancel_left
    (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega)))
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top Nov))

open scoped Classical in
/-- **The dominant good-slab prune from a global fullness bound.**

The retained slabs all carry the absolute slab-local fullness `(2 · Nov)⁻¹ · lam` for the dominant
shading, and the pruned family refines the original at the absolute `(2 · Nov)⁻¹`. -/
private theorem exists_dominantPrune_of_fullness {ι τ σ : Type*}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ) {Nov : ℕ} {lam : ℝ≥0}
    (hNov : 1 ≤ Nov)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮)
    (hne : ∀ S ∈ 𝒮, (Plank.assignedSlabFamily s' repr slabOf S).Nonempty)
    (hovassigned : ∀ x : EuclideanSpace ℝ (Fin 3),
      (𝒮.filter fun S =>
        x ∈ ⋃ i ∈ Plank.assignedSlabFamily s' repr slabOf S, (Y' i).shade).card ≤ Nov)
    (hcarpos : ∀ i ∈ s', 0 < volume (Y' i).carrier)
    (hcarfin : ∀ i ∈ s', volume (Y' i).carrier ≠ ⊤)
    (hshsub : ∀ i ∈ s', (Y' i).shade ⊆ (Y' i).carrier)
    (hfull : lam ≤ ShadedBody.fullness s' Y') :
    ∃ 𝒮g ⊆ 𝒮,
      (∀ S ∈ 𝒮g, (2 * (Nov : ℝ≥0))⁻¹ * lam ≤
        ShadedBody.fullness (Plank.assignedSlabFamily s' repr slabOf S)
          (Plank.dominantSlabShading s' Y' repr slabOf Nov)) ∧
      ShadedBody.IsCRefinement (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g))
        (Plank.dominantSlabShading s' Y' repr slabOf Nov) s' Y' ((2 * (Nov : ℝ≥0))⁻¹) := by
  -- (a) Finiteness of the total shade mass, needed by the joint refinement.
  have htop : ∑ i ∈ s', volume (Y' i).shade ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hcarfin)
      (Finset.sum_le_sum fun i hi => measure_mono (hshsub i hi))
  -- (b) The joint dominant/good-slab refinement at τ = (2·Nov)⁻¹ · lam.
  obtain ⟨𝒮g, hsub, hcond, hprune⟩ :=
    Plank.exists_dominantGoodSlabRefinement s' Y' repr slabOf 𝒮 h𝒮 hNov hovassigned
      ((2 * (Nov : ℝ≥0))⁻¹ * lam) htop (dominantPrune_threshold s' Y' hNov hfull)
  refine ⟨𝒮g, hsub, ?_,
    Plank.isCRefinement_dominantGoodSlabShading s' Y' repr slabOf 𝒮g hNov hprune⟩
  -- (c) Each retained slab carries the slab-local fullness for the dominant shading.
  intro S hS
  refine Plank.fullness_ge_of_aggregateMass (Plank.assignedSlabFamily s' repr slabOf S)
    (Plank.dominantSlabShading s' Y' repr slabOf Nov) ((2 * (Nov : ℝ≥0))⁻¹ * lam) ?_ ?_
    (hcond S hS)
  · -- positivity of the retained aggregate carrier
    obtain ⟨i₀, hi₀⟩ := hne S (hsub hS)
    simpa only [Plank.dominantSlabShading_toConvexSpaceBody] using
      (hcarpos i₀ (Plank.assignedSlabFamily_subset s' repr slabOf S hi₀)).trans_le
        (Finset.single_le_sum (f := fun i => volume (Y' i).carrier)
          (fun _ _ => zero_le) hi₀)
  · -- finiteness of the retained aggregate carrier
    exact ENNReal.sum_ne_top.mpr fun i hi => by
      simpa only [Plank.dominantSlabShading_toConvexSpaceBody] using
        hcarfin i (Plank.assignedSlabFamily_subset s' repr slabOf S hi)

end Kakeya

/-!
## The final configuration layer of GWZ Lemma 6.13

The dominant/good-slab prune fixes, once and for all, the objects that Items 1–4 share:

* the retained slab family `𝒮g ⊆ 𝒮`;
* the final index family `s₁ = s₀.filter (fun i => slabOf (repr i) ∈ 𝒮g)`;
* the dominant shading `Ydom = Plank.dominantSlabShading s₀ Y₀ repr slabOf Nov`;
* the restricted typed representative `R.restrict`, whose `repr` map is *the same* `repr`.

This section collects exactly the consequences the three later layers consume, and nothing else: the
preassembly returns some forty clauses and mirroring them here would be a second copy of its
interface.

Everything below is combinatorial or a direct call to `Kakeya.exists_dominantPrune_of_fullness`; no
geometry and no power of `a` is spent.  The only quantitative input is the global fullness `lam` of
`(s₀, Y₀)`, and the only loss is the absolute `(2 · Nov)⁻¹` of the prune.
-/

namespace Plank

variable {ι τ σ : Type*}

/-! ### Finset bookkeeping for the slab-complete restriction -/

open scoped Classical in
/-- The representative fibre is unchanged by the slab-complete restriction: if `Q`'s slab survives,
so does every index mapping to `Q`.  This is what lets the preassembly fibre bounds be reused on
`s₁` verbatim, with no second pigeonhole. -/
private theorem filter_repr_filter_slab_mem (s₀ : Finset ι) (repr : ι → τ) (slabOf : τ → σ)
    (𝒮g : Finset σ) {Q : τ} (hQ : slabOf Q ∈ 𝒮g) :
    (s₀.filter (fun i => slabOf (repr i) ∈ 𝒮g)).filter (fun i => repr i = Q)
      = s₀.filter (fun i => repr i = Q) := by
  ext i
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hQ⟩, h.2⟩⟩

open scoped Classical in
/-- The retained slab family is exactly the slab image of the restricted active family, provided
every retained slab is realised by some index. -/
private theorem image_slabOf_image_repr_filter (s₀ : Finset ι) (repr : ι → τ) (slabOf : τ → σ)
    (𝒮g : Finset σ) (hcover : ∀ S ∈ 𝒮g, ∃ i ∈ s₀, slabOf (repr i) = S) :
    ((s₀.filter (fun i => slabOf (repr i) ∈ 𝒮g)).image repr).image slabOf = 𝒮g := by
  ext S
  simp only [Finset.mem_image, Finset.mem_filter]
  refine ⟨by rintro ⟨_, ⟨_, ⟨_, hmem⟩, rfl⟩, rfl⟩; exact hmem, fun hS => ?_⟩
  obtain ⟨i, his, hi⟩ := hcover S hS
  exact ⟨repr i, ⟨i, ⟨his, hi ▸ hS⟩, rfl⟩, hi⟩

open scoped Classical in
/-- Every slab of the active slab family is realised by an index, hence has a nonempty assigned
family. -/
private theorem assignedSlabFamily_nonempty_of_mem_image (s₀ : Finset ι) (repr : ι → τ)
    (slabOf : τ → σ)
    {S : σ} (hS : S ∈ (s₀.image repr).image slabOf) :
    (assignedSlabFamily s₀ repr slabOf S).Nonempty := by
  simp only [Finset.mem_image] at hS
  obtain ⟨Q, ⟨i, his, rfl⟩, hslab⟩ := hS
  exact ⟨i, mem_assignedSlabFamily.mpr ⟨his, hslab⟩⟩

end Plank

namespace Kakeya

open scoped Classical in
/-- **The final configuration layer.**

From the preassembly's configuration outputs on `(s₀, Y₀)` this returns the retained slab family
`𝒮g` together with every clause the Item 1–4 layers share.  The prune itself is
`Kakeya.exists_dominantPrune_of_fullness`; everything else is `Finset` bookkeeping.

The pointwise overlap hypothesis is stated on the *geometric* families, exactly as the preassembly
returns it, and is transported to the assigned families here by
`Plank.pointwise_overlap_assigned_of_le` — the assigned family of a slab is contained in its
geometric family, so the count only drops. -/
private theorem plankReduction_configuration
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
    {cThk Cset Cang lam : ℝ≥0} {Nov : ℕ}
    (s₀ : Finset ι) (V : ι → Plank a b hab hb1)
    (Y₀ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (R : Plank.ThickenedRepr s₀ V θ hθ1 cThk)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (hNov : 1 ≤ Nov)
    (hgeo : ∀ i ∈ s₀, i ∈ Plank.inSlabFamilyC Cset Cang s₀ V (slabOf (R.repr i)))
    (hovgeo : ∀ x : EuclideanSpace ℝ (Fin 3),
      (((s₀.image R.repr).image slabOf).filter fun S =>
        x ∈ ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s₀ V S, (Y₀ i).shade).card ≤ Nov)
    (hcarpos : ∀ i ∈ s₀, 0 < volume (Y₀ i).carrier)
    (hcarfin : ∀ i ∈ s₀, volume (Y₀ i).carrier ≠ ⊤)
    (hshsub : ∀ i ∈ s₀, (Y₀ i).shade ⊆ (Y₀ i).carrier)
    (_hlam : 0 < lam) (hfull : lam ≤ ShadedBody.fullness s₀ Y₀) :
    ∃ 𝒮g : Finset (Slab θ hθ1),
      𝒮g ⊆ (s₀.image R.repr).image slabOf ∧
      (∀ S ∈ 𝒮g, (2 * (Nov : ℝ≥0))⁻¹ * lam ≤
        ShadedBody.fullness (Plank.assignedSlabFamily s₀ R.repr slabOf S)
          (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov)) ∧
      ShadedBody.IsCRefinement (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
        (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) s₀ Y₀ ((2 * (Nov : ℝ≥0))⁻¹) ∧
      ((s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)).image R.repr).image slabOf = 𝒮g ∧
      (∀ S ∈ 𝒮g,
        Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) R.repr slabOf S
          = Plank.assignedSlabFamily s₀ R.repr slabOf S) ∧
      (∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, slabOf Q ∈ 𝒮g →
        (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)).filter (fun i => R.repr i = Q)
          = s₀.filter (fun i => R.repr i = Q)) ∧
      (∀ i ∈ s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g),
        i ∈ Plank.inSlabFamilyC Cset Cang (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) V
          (slabOf (R.repr i))) := by
  -- every active slab is realised, hence has a nonempty assigned family
  have hne := fun S (hS : S ∈ (s₀.image R.repr).image slabOf) =>
    Plank.assignedSlabFamily_nonempty_of_mem_image s₀ R.repr slabOf hS
  -- the assigned-family pointwise overlap is inlined from the geometric one
  obtain ⟨𝒮g, hsub, hfullS, hprune⟩ :=
    exists_dominantPrune_of_fullness s₀ Y₀ R.repr slabOf ((s₀.image R.repr).image slabOf) hNov
      (fun i hi => Finset.mem_image_of_mem slabOf (Finset.mem_image_of_mem R.repr hi)) hne
      (Plank.pointwise_overlap_assigned_of_le s₀ Y₀ Y₀ R.repr slabOf _ _
        (Plank.inSlabFamilyC Cset Cang s₀ V) Nov Finset.Subset.rfl
        (fun S _ => Plank.assignedSlabFamily_subset_inSlabFamilyC_of_mem Cset Cang s₀ V R.repr
          slabOf S hgeo)
        (fun _ => Set.Subset.rfl) hovgeo)
      hcarpos hcarfin hshsub hfull
  exact ⟨𝒮g, hsub, hfullS, hprune,
    Plank.image_slabOf_image_repr_filter s₀ R.repr slabOf 𝒮g fun S hS =>
      (hne S (hsub hS)).imp fun _ => Plank.mem_assignedSlabFamily.mp,
    fun _ => Plank.assignedSlabFamily_filter_slab_mem s₀ R.repr slabOf 𝒮g,
    fun _ => Plank.filter_repr_filter_slab_mem s₀ R.repr slabOf 𝒮g,
    fun i hi => Plank.mem_inSlabFamilyC.mpr
      ⟨hi, (Plank.mem_inSlabFamilyC.mp (hgeo i (Finset.mem_of_mem_filter i hi))).2⟩⟩

end Kakeya

/-!
## Item 1 of GWZ Lemma 6.13 on the final family

`Kakeya.slabwiseDensity_assigned` runs Item 1 slab by slab on the assigned families of the dominant
shading and glues the retained sets into one `G : Slab θ hθ1 → Set _`.  This section supplies its
three per-slab hypotheses from the preassembly clauses on `(s₀, Y₀)`.

The whole point is the **one-`Nov`** route.  Each of the two angular hypotheses is transported from
the preassembly source `(s₀, Y₀)` *directly* to the assigned dominant family of a retained slab, by
`Plank.isTypicalPlankAngle_assigned_of_source` and
`Plank.hasCConstantMultiplicity_assigned_of_source`, both of which run
`Plank.dominantGoodSlab_assigned_fibre_retention_source` once at `q = Nov⁻¹`.  Transporting first to
the global pruned family `s₁` and then again to the assigned family would spend `Nov` twice and
demand a reserve of order `Nov ^ 2 · A`, which the preassembly does not publish.

The reserve it does publish is `Nov · A`, and the budget `A ≤ Nov⁻¹ · (Nov · A)` holds with
equality: the transport is exactly affordable.  The two absolute prices are the multiplicity
constant `Cmult ↦ Nov · Cmult` and the fullness coefficient `↦ (2 · Nov)⁻¹`, and no power of `a` is
spent.
-/

namespace Kakeya

open scoped Classical in
/-- **Item 1 on the final family, with the one-`Nov` angular transports.**

Returns the retained sets `G`, the slab-local refinements of the slabwise shading
`Yfin = Plank.slabwiseRestrictShading Ydom R.repr slabOf G hG` over the dominant shading, and the
global ball-density clause at the outer dilation `Kakeya.plankReduction.ballDilation`. -/
private theorem slabwiseDensity_final
    (Cθ Cset Cang Cmult cLamPre : ℝ≥0)
    (hCθ : 1 ≤ Cθ) (hCset : 1 ≤ Cset) (hCang : 1 ≤ Cang)
    (hCmult : 0 < Cmult) (hcLamPre : 0 < cLamPre)
    (Novpt : ℕ) (hNovpt : 1 ≤ Novpt) (Nov : ℕ) (hNov : 1 ≤ Nov)
    {η εwork : ℝ} (hη : 0 < η) (hεwork : 0 < εwork)
    (hbudget : 3 * (η + 5 * εwork / 4) ≤ 4 * η + εwork) :
    ∃ c1 cRef0 : ℝ≥0, 0 < c1 ∧ 0 < cRef0 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*} {cThk : ℝ≥0}
        (s₀ : Finset ι) (V : ι → Plank a b hab hb1)
        (Y₀ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (R : Plank.ThickenedRepr s₀ V θ hθ1 cThk)
        (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
        (𝒮g : Finset (Slab θ hθ1)) (A : ℝ≥0),
        0 < a → a < 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ → 2 ≤ A →
        -- the configuration-layer outputs
        (∀ i ∈ s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g),
          i ∈ Plank.inSlabFamilyC Cset Cang (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) V
            (slabOf (R.repr i))) →
        (∀ S ∈ 𝒮g,
          Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) R.repr slabOf S
            = Plank.assignedSlabFamily s₀ R.repr slabOf S) →
        (∀ S ∈ 𝒮g, (2 * (Nov : ℝ≥0))⁻¹ * (cLamPre * a ^ (η + εwork)) ≤
          ShadedBody.fullness (Plank.assignedSlabFamily s₀ R.repr slabOf S)
            (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov)) →
        -- the preassembly clauses on the source family
        (∀ i ∈ s₀, (Y₀ i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s₀, ((Y₀ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        HasMaxPlankAngleBound s₀ Y₀ V θ Cθ →
        IsTypicalPlankAngle s₀ Y₀ V θ (Cθ * a ^ (-(εwork / 4))) ((Nov : ℝ≥0) * A) →
        ShadedBody.HasCConstantMultiplicity s₀ Y₀ (Cmult * a ^ (-(εwork / 4))) →
        ∃ (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S)),
          (∀ S ∈ 𝒮g,
            ShadedBody.IsCRefinement
              (Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
                R.repr slabOf S)
              (Plank.slabwiseRestrictShading
                (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf G hG)
              (Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
                R.repr slabOf S)
              (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov)
              (cRef0 * a ^ (εwork / 4))) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3),
            ((⋃ i ∈ s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g),
                (Plank.slabwiseRestrictShading
                  (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf G hG i).shade) ∩
              closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
              ((c1 * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
                  volume (closedBall x ((θ * b : ℝ≥0) : ℝ))
                ≤ volume ((⋃ i ∈ s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g),
                    (Plank.slabwiseRestrictShading
                      (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov)
                      R.repr slabOf G hG i).shade) ∩
                  closedBall x ((plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ)))) := by
  have hNov0 : (0 : ℝ≥0) < (Nov : ℝ≥0) := Nat.cast_pos.mpr hNov
  refine (slabwiseDensity_assigned Cθ Cset Cang ((Nov : ℝ≥0) * Cmult)
      ((2 * (Nov : ℝ≥0))⁻¹ * cLamPre) hCθ hCset hCang (mul_pos hNov0 hCmult)
      (mul_pos (inv_pos.mpr (mul_pos two_pos hNov0)) hcLamPre) Novpt hNovpt hη hεwork
      hbudget).imp fun c1 => Exists.imp fun cRef0 h => ⟨h.1, h.2.1, ?_⟩
  intro a b θ hab hb1 hθ1 ι cThk s₀ V Y₀ R slabOf 𝒮g A
    ha ha1 hb hθ hb1' hdivb hA hslabmem hassigned hfullDom hshV hcarEq hmax htyp hmult
  have hdom := Plank.dominantSlabShading_shade_subset s₀ Y₀ R.repr slabOf Nov
  exact h.2.2 (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) V
    (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf 𝒮g A
    ha ha1 hb hθ hb1' hdivb hA (fun i hi => (Finset.mem_filter.mp hi).2) hslabmem
    (fun i hi => (hdom i).trans (hshV i (Finset.mem_filter.mp hi).1))
    (fun i hi => hcarEq i (Finset.mem_filter.mp hi).1)
    (hmax.mono (Finset.filter_subset _ s₀) fun i _ => hdom i)
    -- the reserve-scale stability clause is transported straight from the source family
    (fun S hS => Plank.isTypicalPlankAngle_assigned_of_source s₀ Y₀ V R.repr slabOf 𝒮g hNov hS
      θ (Cθ * a ^ (-(εwork / 4))) A (one_le_two.trans hA)
      fun x hx t htsub hdcard => (htyp x hx).2 t htsub (by
        rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast]))
    (fun S hS => (mul_assoc _ _ _).trans_le (hassigned S hS ▸ hfullDom S hS))
    fun S hS => mul_assoc (Nov : ℝ≥0) Cmult (a ^ (-(εwork / 4))) ▸
      Plank.hasCConstantMultiplicity_assigned_of_source s₀ Y₀ R.repr slabOf 𝒮g hNov hS
        (Cmult * a ^ (-(εwork / 4))) hmult

end Kakeya

/-!
## Item 2 of GWZ Lemma 6.13 on the final family

`Kakeya.slabwiseRepresentativeShading` is run here once, on the slabwise shading produced by Item 1.

Three points fix the instantiation.

* **The fibre window is configuration-dependent.**  `L = N / cN` and `W = cN · N` both move with the
  configuration, so they are bound inside the configuration quantifier; only their ratio may enter
  `c₂`, and that ratio is the outer `ρ = cN⁻¹ · cN⁻¹`.  At those values `ρ · W = L` exactly, so the
  aggregate loses `cN⁻²` and no power of `a`.

* **Item 2 runs at `η + εwork`, not at `η`.**  The dominant/good-slab fullness of `Ydom` is only
  available at `a ^ (η + εwork)` — the `a ^ ε` is the preassembly's own fullness loss — and the
  slabwise refinement of Item 1 *adds* `εwork / 4` to that exponent.  So the local fullness that
  Item 2 can be fed is at `η + εwork + εwork / 4`, which is its own hypothesis exponent
  `η₂ + εwork / 4` at `η₂ = η + εwork`.  The strong output is therefore at
  `4 · η₂ + εwork = 4η + 5εwork`.

* **The stop scale costs one `Nov`.**  The angular stability clause on each assigned family comes
  from `Plank.dominantGoodSlab_assigned_stopScale` at `K = 2` and
  `Aout = max 2 (plankAngleScaleA a)`, applied directly to the preassembly's clause on `(s₀, Y₀)`.
-/

namespace Kakeya

open Plank in
open scoped Classical in
/-- **Item 2 on the final family.**

Returns one `c₂`, the carrier coherence of the thickened shading `Yθfin`, and for every retained
slab the strong fullness at `a ^ (4η + 5εwork)`, the public fullness at `a ^ (4η) · a ^ ε`, and the
shade containment in the geometric slab family. -/
private theorem slabwiseShading_final
    (cGood cStb Cang2 Cset Ccarrier cN cRef0 : ℝ≥0) (Nov : ℕ)
    (hcGood : 0 < cGood) (hcStb : 0 < cStb)
    (hCang2 : 1 ≤ Cang2) (hCset : 1 ≤ Cset) (hCcarrier : 1 ≤ Ccarrier)
    (hcN : 1 ≤ cN) (hcRef0 : 0 < cRef0) (hNov : 1 ≤ Nov)
    {η εwork : ℝ} (hη : 0 < η) (hεwork : 0 < εwork) :
    ∃ c2 : ℝ≥0, 0 < c2 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        {cThk Cang : ℝ≥0} {N : ℕ} {ε : ℝ}
        (s₀ : Finset ι) (V : ι → Plank a b hab hb1)
        (Y₀ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (R : Plank.ThickenedRepr s₀ V θ hθ1 cThk)
        (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
        (Pr : Plank.ThickenedPlank θ b hθ1 hb1 →
          Prism3D (θ * b) b 1 (Plank.thickenedWidth_le hθ1) hb1)
        (𝒮g : Finset (Slab θ hθ1))
        (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S)),
        0 < a → a ≤ 1 → a < 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ → 1 ≤ N →
        5 * εwork ≤ ε → Cang ≤ Cang2 →
        -- configuration-layer outputs
        (∀ S ∈ 𝒮g,
          Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) R.repr slabOf S
            = Plank.assignedSlabFamily s₀ R.repr slabOf S) →
        (∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, slabOf Q ∈ 𝒮g →
          (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)).filter (fun i => R.repr i = Q)
            = s₀.filter (fun i => R.repr i = Q)) →
        (∀ i ∈ s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g),
          i ∈ Plank.inSlabFamilyC Cset Cang (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) V
            (slabOf (R.repr i))) →
        (∀ S ∈ 𝒮g,
          (Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
            R.repr slabOf S).Nonempty) →
        -- Item 1 output: the slab-local refinement of the slabwise shading
        (∀ S ∈ 𝒮g,
          ShadedBody.IsCRefinement
            (Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
              R.repr slabOf S)
            (Plank.slabwiseRestrictShading
              (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf G hG)
            (Plank.assignedSlabFamily (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
              R.repr slabOf S)
            (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov)
            (cRef0 * a ^ (εwork / 4))) →
        -- configuration-layer dominant fullness, at the exponent the preassembly can supply
        (∀ S ∈ 𝒮g, ((2 * (Nov : ℝ≥0))⁻¹ * cGood) * a ^ (η + εwork) ≤
          ShadedBody.fullness (Plank.assignedSlabFamily s₀ R.repr slabOf S)
            (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov)) →
        -- preassembly clauses on the source family
        (∀ i ∈ s₀, i ∈ Plank.inSlabFamilyC Cset Cang s₀ V (slabOf (R.repr i))) →
        HasMaxPlankAngleBound s₀ Y₀ V θ 1 →
        (∀ x ∈ ⋃ i ∈ s₀, (Y₀ i).shade, ∀ t ⊆ shadeFibre s₀ Y₀ x,
          ((Nov : ℝ) * max 2 (plankAngleScaleA a))⁻¹ * ((shadeFibre s₀ Y₀ x).card : ℝ)
              ≤ (t.card : ℝ) →
            (θ : ℝ) ≤ 2 * plankAngleScaleB a * ((maxPlankAngle V t : ℝ≥0) : ℝ)) →
        (∀ i ∈ s₀, (Y₀ i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s₀, ((Y₀ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s₀, 8 * (a : ENNReal) * (b : ENNReal)
          ≤ volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s₀, (Y₀ i).shade ⊆
          (((R.repr i).toPrismNDim.dilation Ccarrier).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ t ∈ s₀.image R.repr, (Pr t).toPrismNDim = t.toPrismNDim) →
        (∀ i ∈ s₀, Prism3D.angle (Pr (R.repr i)) (slabOf (R.repr i)) ≤ (Cang2 : ℝ) * (θ : ℝ)) →
        (∀ t ∈ s₀.image R.repr,
          (N : ℝ) / (cN : ℝ) ≤ ((s₀.filter (fun i => R.repr i = t)).card : ℝ) ∧
            ((s₀.filter (fun i => R.repr i = t)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) →
        (∀ Q ∈ (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)).image R.repr,
          ((Plank.sharedSlabThickenedShadingDilation
              (plankReduction.boxDilation Cang2 Ccarrier)
              (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
              (Plank.slabwiseRestrictShading
                (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf G hG)
              (fun Q => Q.toPrismNDim) R.repr slabOf Q).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))
            = ((Q.toPrismNDim.dilation (plankReduction.boxDilation Cang2 Ccarrier)).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) ∧
        ∀ S ∈ 𝒮g,
          c2 * a ^ (4 * η + 5 * εwork) ≤
            ShadedBody.fullness
              (((s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)).image R.repr).filter
                (fun Q => slabOf Q = S))
              (Plank.sharedSlabThickenedShadingDilation
                (plankReduction.boxDilation Cang2 Ccarrier)
                (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
                (Plank.slabwiseRestrictShading
                  (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf G hG)
                (fun Q => Q.toPrismNDim) R.repr slabOf) ∧
          (c2 * a ^ (4 * η) * a ^ ε ≤
            ShadedBody.fullness
              (((s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)).image R.repr).filter
                (fun Q => slabOf Q = S))
              (Plank.sharedSlabThickenedShadingDilation
                (plankReduction.boxDilation Cang2 Ccarrier)
                (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
                (Plank.slabwiseRestrictShading
                  (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf G hG)
                (fun Q => Q.toPrismNDim) R.repr slabOf) ∧
          ∀ Q ∈ (((s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)).image R.repr).filter
              (fun Q => slabOf Q = S)),
            (Plank.sharedSlabThickenedShadingDilation
                (plankReduction.boxDilation Cang2 Ccarrier)
                (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g))
                (Plank.slabwiseRestrictShading
                  (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov) R.repr slabOf G hG)
                (fun Q => Q.toPrismNDim) R.repr slabOf Q).shade
              ⊆ ⋃ i ∈ Plank.inSlabFamilyC Cset Cang
                  (s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)) V S,
                  (Plank.slabwiseRestrictShading
                    (Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov)
                    R.repr slabOf G hG i).shade) := by
  have hcN0 : (0 : ℝ≥0) < cN := lt_of_lt_of_le zero_lt_one hcN
  have hNov0 : (0 : ℝ≥0) < (Nov : ℝ≥0) := Nat.cast_pos.mpr hNov
  have hcGood2 : (0 : ℝ≥0) < (2 * (Nov : ℝ≥0))⁻¹ * cGood :=
    mul_pos (inv_pos.mpr (mul_pos two_pos hNov0)) hcGood
  obtain ⟨cTan, hcTan, htanMain⟩ := Plank.comparableScalars_of_mem_halfBox Cang2 hCang2
  obtain ⟨c2, hc2pos, hmain⟩ :=
    slabwiseRepresentativeShading cTan ((2 * (Nov : ℝ≥0))⁻¹ * cGood) cStb Cang2 Cset Ccarrier
      (cN⁻¹ * cN⁻¹) cRef0 hcTan hcGood2 hcStb hCang2 hCset hCcarrier
      (mul_pos (inv_pos.mpr hcN0) (inv_pos.mpr hcN0)) hcRef0
      (add_pos hη hεwork) hεwork
  refine ⟨c2, hc2pos, ?_⟩
  intro a b θ hab hb1 hθ1 ι cThk Cang N ε s₀ V Y₀ R slabOf Pr 𝒮g G hG
    ha ha1' ha1 hb hθ hb1' hdivb hN h5εwle hCangle
    hassigned hfibeq hslabmem₁ hne hlocRef hfullDom
    hgeo₀ hmax1 hstop hshV₀ hcarEq₀ hcarvol₀ hsubCar₀ hPr hangPr₀ hfib₀
  refine ⟨fun Q _ => rfl, fun S₀ hS₀ => ?_⟩
  -- abbreviations, as local definitions: `set` would re-abstract the whole (large) context
  let s₁ : Finset ι := s₀.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)
  let Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    Plank.dominantSlabShading s₀ Y₀ R.repr slabOf Nov
  let Yfin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    Plank.slabwiseRestrictShading Ydom R.repr slabOf G hG
  have hs₁sub : s₁ ⊆ s₀ := Finset.filter_subset _ _
  -- the shading chain
  have hYdomsub : ∀ i, (Ydom i).shade ⊆ (Y₀ i).shade :=
    Plank.dominantSlabShading_shade_subset s₀ Y₀ R.repr slabOf Nov
  have hYfinsub₀ : ∀ i, (Yfin i).shade ⊆ (Y₀ i).shade := fun i =>
    (Plank.restrictShade_shade_subset (Ydom i) (G (slabOf (R.repr i)))
      (hG (slabOf (R.repr i)))).trans (hYdomsub i)
  -- both shading steps are `ShadedBody.restrictShade`, which leaves the carrier alone
  have hYfincarV : ∀ i ∈ s₀, ((Yfin i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := hcarEq₀
  -- membership helpers on the assigned families
  have hAsub : ∀ S : Slab θ hθ1,
      Plank.assignedSlabFamily s₁ R.repr slabOf S ⊆ s₀ := fun S i hi =>
    hs₁sub (Plank.assignedSlabFamily_subset s₁ R.repr slabOf S hi)
  have hAslab : ∀ (S : Slab θ hθ1), ∀ i ∈ Plank.assignedSlabFamily s₁ R.repr slabOf S,
      slabOf (R.repr i) = S := fun S i hi => (Plank.mem_assignedSlabFamily.mp hi).2
  -- the representative angle bound, transported from `Cang` up to `Cang2` (for `htan` below)
  have hangV : ∀ (S : Slab θ hθ1), ∀ i ∈ Plank.assignedSlabFamily s₁ R.repr slabOf S,
      Prism3D.angle (V i) S ≤ (Cang2 : ℝ) * (θ : ℝ) := fun S i hi => by
    rw [← hAslab S i hi]
    exact (Plank.mem_inSlabFamilyC.mp (hgeo₀ i (hAsub S hi))).2.2.trans
      (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCangle) θ.coe_nonneg)
  -- the fibre over a representative agrees in the assigned family and in `s₀` (used twice below)
  have hfibcard : ∀ S ∈ 𝒮g, ∀ i ∈ Plank.assignedSlabFamily s₁ R.repr slabOf S,
      (Plank.assignedSlabFamily s₁ R.repr slabOf S).filter (fun j => R.repr j = R.repr i)
        = s₀.filter (fun j => R.repr j = R.repr i) := fun S hS i hi => by
    have hsl := hAslab S i hi
    rw [Plank.filter_repr_assignedSlabFamily_eq s₁ R.repr slabOf S hsl,
      hfibeq _ (hsl ▸ hS)]
  -- `a ≤ θ * b`, needed by the tangentiality lemma
  have haθb : a ≤ θ * b := (div_le_iff₀ hb).mp hdivb
  have hN0 : (0 : ℝ≥0) < (N : ℝ≥0) := Nat.cast_pos.mpr hN
  obtain ⟨hstrong, -, hcont⟩ := hmain (Cgeo := Cang) s₁ V Ydom R.repr slabOf G hG 𝒮g Pr
    (fun Q => Q.toPrismNDim)
    (fun S sh q i => ShadedBody.restrictShade (Yfin i) (Plank.halfSlabBox S b sh q)
      (Plank.measurableSet_halfSlabBox S b sh q))
    (max 2 (plankAngleScaleA a)) ((N : ℝ≥0) / cN) (cN * (N : ℝ≥0))
    ha ha1' ha1 hb hθ hb1' hdivb (le_max_left _ _)
    (div_pos hN0 hcN0) (mul_pos hcN0 hN0)
    -- ρ * W ≤ L, with equality
    (by rw [show cN⁻¹ * cN⁻¹ * (cN * (N : ℝ≥0)) = cN⁻¹ * (cN⁻¹ * cN) * (N : ℝ≥0) by ring,
      inv_mul_cancel₀ hcN0.ne', mul_one, ← div_eq_inv_mul])
    ((le_mul_of_one_le_left hεwork.le (by norm_num)).trans h5εwle)
    -- hanchor
    (fun u hu => (hPr u (Finset.image_subset_image hs₁sub hu)).symm)
    -- hmax at Cang2
    ((HasMaxPlankAngleBound.mono hs₁sub (fun i _ => hYdomsub i) hmax1).mono_const hCang2)
    hne
    -- hZsh
    (fun _ _ _ _ _ _ => rfl)
    -- hZcar
    (fun S _ _ _ i hi => hYfincarV i (hAsub S hi))
    -- hstabDom
    (fun S hS => Plank.dominantGoodSlab_assigned_stopScale s₀ Y₀ V R.repr slabOf 𝒮g hNov hS
      (K := 2) (Aout := max 2 (plankAngleScaleA a)) two_pos
      (two_pos.trans_le (le_max_left _ _)) hstop)
    -- hfam
    (fun S _ i hi => Plank.inSlabFamilyC_mono le_rfl hCangle
      (Plank.mem_inSlabFamilyC_assignedSlabFamily Cset Cang s₁ V R.repr slabOf S hslabmem₁ i hi))
    -- hsubPr
    (fun S _ i hi => by
      rw [hPr (R.repr i) (Finset.mem_image_of_mem R.repr (hAsub S hi))]
      exact (hYfinsub₀ i).trans (hsubCar₀ i (hAsub S hi)))
    -- hshV
    (fun S _ i hi => (hYfinsub₀ i).trans (hshV₀ i (hAsub S hi)))
    -- hcarvol
    (fun S _ i hi => by
      rw [hYfincarV i (hAsub S hi)]; exact hcarvol₀ i (hAsub S hi))
    -- htan
    (fun S _ sh q i hi => by
      obtain ⟨hiA, x, hx1, hx2⟩ := Finset.mem_filter.mp hi
      exact htanMain (V i) hθ1 S sh q ha hb haθb (hangV S i hiA)
        ⟨x, (hYfinsub₀ i).trans (hshV₀ i (hAsub S hiA)) hx1, hx2⟩)
    -- hangPr
    (fun S _ u hu => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      rw [← hAslab S i hi]; exact hangPr₀ i (hAsub S hi))
    -- hlo
    (fun S hS u hu => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      rw [hfibcard S hS i hi]
      exact_mod_cast (hfib₀ _ (Finset.mem_image_of_mem R.repr (hAsub S hi))).1)
    -- hup
    (fun S hS u hu => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      rw [hfibcard S hS i hi]
      exact_mod_cast (hfib₀ _ (Finset.mem_image_of_mem R.repr (hAsub S hi))).2)
    -- the slabwise local fullness, at `η₂ + εwork / 4 = η + εwork + εwork / 4`
    (fun S hS => Plank.fullness_assignedSlabFamily_of_isCRefinement ha s₁ Ydom Yfin R.repr slabOf S
      (hlocRef S hS) (by rw [hassigned S hS]; exact hfullDom S hS))
    -- hgeo
    hslabmem₁ S₀ hS₀
  have he : (c2 * a ^ (4 * η + 5 * εwork) : ℝ≥0) = c2 * a ^ (4 * (η + εwork) + εwork) := by
    rw [show 4 * η + 5 * εwork = 4 * (η + εwork) + εwork by ring]
  replace hstrong := he.le.trans hstrong
  refine ⟨hstrong, le_trans ?_ hstrong, hcont⟩
  -- the public form comes from the *strong* one, via the Item 2 exponent budget at `5 · εwork ≤ ε`
  exact Kakeya.representativeShading_exponent_budget (εwork := 5 * εwork) ha ha1' h5εwle

end Kakeya

/-!
## The final refinement and cardinality ledger of GWZ Lemma 6.13

After the slab-complete dominant/good-slab prune the public statement still asks for a refinement of
the *original* family and for the cardinality clause

`((cP · a ^ η) · a ^ ε) · |s| ≤ |s₁|`.

Both come from a single composition followed by a single conversion:

* `ShadedBody.IsCRefinement.trans` composes the dominant/good-slab refinement at the absolute
  `(2 · Nov)⁻¹` with the preassembly's refinement at `rPre`, giving `rFinal = (2 · Nov)⁻¹ · rPre`;
* `Kakeya.card_le_of_isCRefinement_of_fullness` then converts that single refinement into a
  cardinality bound, at the incoming fullness `lam = a ^ η`.

This ordering is the whole point.  Converting either refinement to a cardinality bound first and
composing the two counts would charge `a ^ η` twice and break the public clause; converting once at
the end charges it exactly once.  The `a ^ ε` never passes through the conversion at all — it lives
inside `rPre`, via the preassembly's own `cPpre · a ^ ε ≤ rPre`.

The prune therefore costs only the absolute factor `(2 · Nov)⁻¹`, absorbed into the public constant
`cP = (2 · Nov)⁻¹ · cPpre`.  No power of `a` is spent, and no representative-retention or
slab-retention exponent appears.
-/

namespace Kakeya

open scoped Classical in
/-- **The final refinement and cardinality clause of GWZ Lemma 6.13.**

One composition (`ShadedBody.IsCRefinement.trans`) and one mass-to-cardinality conversion
(`Kakeya.card_le_of_isCRefinement_of_fullness`), in that order.

The strong refinement `IsCRefinement s₁ Ydom s Y rFinal` is returned alongside the cardinality
bound, because the Item 4 assembly consumes the refinement while only the public statement consumes
the count.  The defining equations for `cP` and `rFinal` are exposed so the caller can see that the
prune costs nothing but the absolute `(2 · Nov)⁻¹`. -/
private theorem plankReduction_refinement
    {ι : Type*} {a : ℝ≥0} {η ε : ℝ} {cPpre rPre : ℝ≥0} {Nov : ℕ} {v : ENNReal}
    {s s' s₁ : Finset ι}
    {Y Y' Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hNov : 1 ≤ Nov) (hcPpre : 0 < cPpre) (hrPre : 0 < rPre)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hDom : ShadedBody.IsCRefinement s₁ Ydom s' Y' ((2 * (Nov : ℝ≥0))⁻¹))
    (hPre : ShadedBody.IsCRefinement s' Y' s Y rPre)
    (hCref : cPpre * a ^ ε ≤ rPre)
    (hfull : a ^ η ≤ ShadedBody.fullness s Y)
    (hVlow : ∀ i ∈ s, v ≤ volume (Y i).carrier)
    (hV'up : ∀ i ∈ s₁, volume (Ydom i).shade ≤ v) :
    ∃ cP rFinal : ℝ≥0,
      0 < cP ∧ 0 < rFinal ∧
      cP = (2 * (Nov : ℝ≥0))⁻¹ * cPpre ∧
      rFinal = (2 * (Nov : ℝ≥0))⁻¹ * rPre ∧
      ShadedBody.IsCRefinement s₁ Ydom s Y rFinal ∧
      ((cP * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s₁.card : ℝ≥0) := by
  have hinv : (0 : ℝ≥0) < (2 * (Nov : ℝ≥0))⁻¹ :=
    inv_pos.mpr (mul_pos two_pos (Nat.cast_pos.mpr hNov))
  have href : ShadedBody.IsCRefinement s₁ Ydom s Y ((2 * (Nov : ℝ≥0))⁻¹ * rPre) := by
    simpa [mul_comm] using hDom.trans hPre
  have hcard := card_le_of_isCRefinement_of_fullness hv0 hvtop href hfull hVlow hV'up
  refine ⟨(2 * (Nov : ℝ≥0))⁻¹ * cPpre, (2 * (Nov : ℝ≥0))⁻¹ * rPre,
    mul_pos hinv hcPpre, mul_pos hinv hrPre, rfl, rfl, href, le_trans ?_ hcard⟩
  rw [mul_right_comm ((2 * (Nov : ℝ≥0))⁻¹ * cPpre), mul_assoc (2 * (Nov : ℝ≥0))⁻¹ cPpre]
  exact mul_le_mul_left (mul_le_mul_left (mul_le_mul_right hCref _) _) _

end Kakeya

/-!
## The final output package of GWZ Lemma 6.13

One theorem collecting Items 1–4 and the bookkeeping clauses onto a single coherent final witness

* index family `s₁`, unchanged from the dominant/good-slab restriction onward;
* plank shading `Yfin`, which the slabwise route builds as
  `Plank.slabwiseRestrictShading Ydom R₁.repr slabOf G hG`;
* typed representatives `R₁`, active family `𝒯 = R₁.indexSet`, slab family `𝒮 = 𝒯.image slabOf`;
* thickened shading `Yθfin`, pinned by `hYθfin` to
  `Plank.sharedSlabThickenedShadingDilation Cbox s₁ Yfin (fun Q => Q.toPrismNDim) R₁.repr slabOf`
  at `Cbox = plankReduction.boxDilation Cang2 Ccarrier`.

`Yfin` is left abstract: nothing in the final package uses its internal structure, only the clauses
the slabwise route proves about it.  Keeping it abstract is what makes this statement elaborate.

No geometry is proved here.  Items 1 and 2 enter as the conclusions of `Kakeya.slabwiseDensity` and
`Kakeya.slabwiseRepresentativeShading`, both of which are already stated on exactly these
objects; Item 3 is `Kakeya.slabwiseUnionVolume` and Item 4 is `Kakeya.slabwiseMultiplicity`,
applied here with the
coefficient supplied by the sharp Item 4 ledger.  What this theorem does is the public bookkeeping:

* the Item 1 exponent `4η + εwork` is weakened to the public `a ^ (4η) · a ^ ε` using `εwork ≤ ε`;
* the *strong* Item 2 exponent `4η + εwork` is used for Item 4 and separately weakened to the
  public `a ^ (4η) · a ^ ε`;
* the cardinality clause is weakened from `a ^ εpre` to `a ^ ε` using `εpre ≤ ε`, on the *unchanged*
  index set `s₁` — no second mass-to-cardinality conversion happens after `Ydom → Yfin`;
* the fullness retention is read off the composed `IsCRefinement`;
* the fibre bounds are converted to the public `cN = 2` by `Kakeya.fibre_bounds_two`;
* the carrier coherence for `Yθfin` is definitional.

`Kakeya.plankReduction.ballDilation` and the `ShadedPlank.redPlankTube.ballDilation` of the public
statement are two `def`s of the literal `3`; bridging them is a `rfl` left to the final packaging in
`Reduction.lean`.
-/

namespace Kakeya

/-- Weakening a power of `a ≤ 1`: a larger exponent gives a smaller value, so a bound stated at
`a ^ q` implies the one stated at `a ^ p` whenever `q ≤ p`.  This is the only step used to weaken
the internal exponents `εpre` and `εwork` to the public `ε`. -/
private theorem mul_rpow_le_of_exponent_le (c : ℝ≥0) {a : ℝ≥0} {p q : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hqp : q ≤ p) :
    c * a ^ p ≤ c * a ^ q :=
  mul_le_mul_right (NNReal.rpow_le_rpow_of_exponent_ge ha ha1 hqp) c

/-- The Item 1 coefficient weakening, in `ENNReal`: the public `c₁ · a ^ (4η) · a ^ ε` is at most
the internal `c₁ · a ^ (4η + εwork)` whenever `εwork ≤ ε` and `a ≤ 1`. -/
private theorem coe_mul_rpow_pair_le (c : ℝ≥0) {a : ℝ≥0} {p ε εwork : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (h : εwork ≤ ε) :
    (c : ENNReal) * (a : ENNReal) ^ p * (a : ENNReal) ^ ε
      ≤ ((c * a ^ (p + εwork) : ℝ≥0) : ENNReal) := by
  have ha0 : a ≠ 0 := ha.ne'
  rw [← ENNReal.coe_rpow_of_ne_zero ha0, ← ENNReal.coe_rpow_of_ne_zero ha0, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, mul_assoc, ← NNReal.rpow_add ha0]
  exact mul_rpow_le_of_exponent_le c ha ha1 (by linarith)

/-- The Item 1 ball radius, in the two coercion shapes the two statements use. -/
private theorem coe_ballDilation_mul (θ b : ℝ≥0) :
    ((plankReduction.ballDilation * θ * b : ℝ≥0) : ℝ)
      = (plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ) := by
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_mul, mul_assoc]

open scoped Classical in
/-- **The final output package of GWZ Lemma 6.13.**

All four Items, the refinement/cardinality/fullness ledger, the slab membership clause, the carrier
coherence and the fibre bounds at the public `cN = 2`, on one coherent final witness. -/
private theorem plankReduction_outputs
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
    {cThk Cbox Cset Cang cP cLam c1 c2 c3 c4 : ℝ≥0}
    {cOv Cgeom cN0 rFinalFin : ℝ≥0} {N : ℕ} {volP : ENNReal}
    {η ε εpre εwork : ℝ}
    (s s₁ : Finset ι) (Y : ι → ShadedPlank a b hab hb1)
    (R₁ : Plank.ThickenedRepr s₁ (ShadedPlank.planks Y) θ hθ1 cThk)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (Yfin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Yθfin : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Pass : Slab θ hθ1 → Finset ι)
    (hYθfin : Yθfin = Plank.sharedSlabThickenedShadingDilation Cbox s₁ Yfin
      (fun Q => Q.toPrismNDim) R₁.repr slabOf)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hθ : 0 < θ)
    (hN : 1 ≤ N) (hdiv : a / b ≤ θ)
    (hεwork_le : εwork ≤ ε) (hεpre_le : εpre ≤ ε)
    (hcOv : 0 < cOv) (hc2pos : 0 < c2) (hgeom : (2 : ℝ≥0) ≤ Cgeom)
    (hcN1 : 1 ≤ cN0) (hcN2 : cN0 ≤ 2)
    -- the composed final refinement, at the sharp coefficient
    (href : ShadedBody.IsCRefinement s₁ Yfin s (ShadedPlank.bodies Y) rFinalFin)
    (hrFinal0 : rFinalFin ≠ 0)
    (hcLam : cLam * a ^ ε ≤ rFinalFin)
    -- the cardinality count on the unchanged index set, at the preassembly exponent
    (hcard : ((cP * a ^ η) * a ^ εpre) * (s.card : ℝ≥0) ≤ (s₁.card : ℝ≥0))
    -- canonical slab membership
    (hslabmem : ∀ i ∈ s₁,
      i ∈ Plank.inSlabFamilyC Cset Cang s₁ (ShadedPlank.planks Y) (slabOf (R₁.repr i)))
    -- fibre bounds at the internal comparability constant
    (hfib : ∀ t ∈ R₁.indexSet,
      (N : ℝ) / (cN0 : ℝ) ≤ ((s₁.filter (fun i => R₁.repr i = t)).card : ℝ) ∧
        ((s₁.filter (fun i => R₁.repr i = t)).card : ℝ) ≤ (cN0 : ℝ) * (N : ℝ))
    -- Item 1, from `Kakeya.slabwiseDensity`
    (hitem1 : ∀ x : EuclideanSpace ℝ (Fin 3),
      ((⋃ i ∈ s₁, (Yfin i).shade) ∩ closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
        ((c1 * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
            volume (closedBall x ((θ * b : ℝ≥0) : ℝ))
          ≤ volume ((⋃ i ∈ s₁, (Yfin i).shade) ∩
            closedBall x ((plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))))
    -- Item 2, at the *strong* exponent, from `Kakeya.slabwiseRepresentativeShading`
    (hitem2 : ∀ S ∈ R₁.indexSet.image slabOf,
      c2 * a ^ (4 * η + εwork) ≤
        ShadedBody.fullness (R₁.indexSet.filter (fun Q => slabOf Q = S)) Yθfin)
    -- the Item 2 containment clause, from `Kakeya.slabwiseRepresentativeShading`
    (hitem2sub : ∀ S ∈ R₁.indexSet.image slabOf,
      ∀ Q ∈ R₁.indexSet.filter (fun Q => slabOf Q = S),
        (Yθfin Q).shade ⊆
          ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s₁ (ShadedPlank.planks Y) S, (Yfin i).shade)
    -- Item 3 inputs
    (hPass : ∀ S ∈ R₁.indexSet.image slabOf,
      Plank.assignedSlabFamily s₁ R₁.repr slabOf S ⊆ Pass S)
    (hov3 : (cOv : ENNReal) *
          ∑ S ∈ R₁.indexSet.image slabOf, volume (⋃ i ∈ Pass S, (Yfin i).shade)
        ≤ volume (⋃ i ∈ s₁, (Yfin i).shade))
    (hU : (⋃ i ∈ s₁, (Yfin i).shade) ⊆ ⋃ i ∈ s, (Y i).shade)
    (hc3 : (c3 * a ^ ε : ℝ≥0) ≤ cOv)
    -- Item 4 inputs
    (hne : (R₁.indexSet.image slabOf).Nonempty)
    (hslab : ∀ i ∈ s₁, slabOf (R₁.repr i) ∈ R₁.indexSet.image slabOf)
    (hov4 : (cOv : ENNReal) *
          (∑ S ∈ R₁.indexSet.image slabOf,
            volume (⋃ i ∈ Plank.assignedSlabFamily s₁ R₁.repr slabOf S, (Yfin i).shade))
        ≤ volume (⋃ i ∈ s₁, (Yfin i).shade))
    (hPvol : ∀ S ∈ R₁.indexSet.image slabOf,
      ∀ i ∈ Plank.assignedSlabFamily s₁ R₁.repr slabOf S, volume (Yfin i).shade ≤ volP)
    (hcarrierVolume : ∀ S ∈ R₁.indexSet.image slabOf,
      ∀ t ∈ R₁.indexSet.filter (fun Q => slabOf Q = S),
        ((θ * b / a : ℝ≥0) : ENNReal) * volP ≤ volume (Yθfin t).carrier)
    -- the sharp Item 4 coefficient, from `Kakeya.exists_multiplicityCoefficient`
    (hc4 : (Cgeom : ENNReal) * (rFinalFin : ENNReal)⁻¹ * (cOv : ENNReal)⁻¹ *
          ((c2 * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal)⁻¹
        ≤ (c4 : ENNReal) * (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (-(4 * η))) :
    ShadedBody.IsRefinement s₁ Yfin s (ShadedPlank.bodies Y) ∧
      ((cP * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s₁.card : ℝ≥0) ∧
      (cLam * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s₁ Yfin ∧
      1 ≤ N ∧ a / b ≤ θ ∧
      (∀ i ∈ s₁,
        i ∈ Plank.inSlabFamilyC Cset Cang s₁ (ShadedPlank.planks Y) (slabOf (R₁.repr i))) ∧
      (∀ Q ∈ R₁.indexSet,
        ((Yθfin Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) =
          ((Q.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ Q ∈ R₁.indexSet,
        (N : ℝ) / ((2 : ℝ≥0) : ℝ) ≤ (((s₁.filter fun i => R₁.repr i = Q).card : ℕ) : ℝ) ∧
          (((s₁.filter fun i => R₁.repr i = Q).card : ℕ) : ℝ) ≤ ((2 : ℝ≥0) : ℝ) * (N : ℝ)) ∧
      -- Item 1
      (∀ x : EuclideanSpace ℝ (Fin 3),
        ((⋃ i ∈ s₁, (Yfin i).shade) ∩ closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
          (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
              volume (closedBall x ((θ * b : ℝ≥0) : ℝ))
            ≤ volume ((⋃ i ∈ s₁, (Yfin i).shade) ∩
              closedBall x ((plankReduction.ballDilation * θ * b : ℝ≥0) : ℝ))) ∧
      -- Item 2
      (∀ S ∈ R₁.indexSet.image slabOf,
        c2 * a ^ (4 * η) * a ^ ε ≤
          ShadedBody.fullness (R₁.indexSet.filter (fun Q => slabOf Q = S)) Yθfin ∧
        ∀ Q ∈ R₁.indexSet.filter (fun Q => slabOf Q = S),
          (Yθfin Q).shade ⊆
            ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s₁ (ShadedPlank.planks Y) S, (Yfin i).shade) ∧
      -- Item 3
      (((c3 * a ^ ε : ℝ≥0) : ENNReal) *
            ∑ S ∈ R₁.indexSet.image slabOf,
              volume (⋃ Q ∈ R₁.indexSet.filter (fun Q => slabOf Q = S), (Yθfin Q).shade)
          ≤ volume (⋃ i ∈ s, (Y i).shade)) ∧
      -- Item 4
      (∃ S ∈ R₁.indexSet.image slabOf,
        ShadedBody.multiplicity s (ShadedPlank.bodies Y) ≤
          (c4 : ENNReal) * (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (-(4 * η)) *
            (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) *
            ShadedBody.multiplicity (R₁.indexSet.filter (fun Q => slabOf Q = S)) Yθfin) := by
  subst hYθfin
  refine ⟨href.1,
    (mul_le_mul_left (mul_rpow_le_of_exponent_le (cP * a ^ η) ha ha1 hεpre_le) _).trans hcard,
    (mul_le_mul_left hcLam _).trans (Plank.fullness_ge_of_isCRefinement href),
    hN, hdiv, hslabmem, fun _ _ => rfl, fibre_bounds_two hcN1 hcN2 hfib, ?_, ?_,
    slabwiseUnionVolume s₁ (ShadedPlank.planks Y) R₁ Yfin slabOf Pass
      (⋃ i ∈ s, (Y i).shade) hPass hov3 hU hc3,
    slabwiseMultiplicity (Cbox := Cbox) (rRef := rFinalFin)
      (β := c2 * a ^ (4 * η + εwork)) (cN := cN0) (volP := volP)
      s s₁ (ShadedPlank.planks Y) R₁ (ShadedPlank.bodies Y) Yfin slabOf
      ha hb hθ hrFinal0 hcOv (mul_pos hc2pos (NNReal.rpow_pos ha))
      hcN1 hcN2 hgeom hne href hslab hov4 hPvol hfib hcarrierVolume hitem2 hc4⟩
  · intro x hx
    rw [coe_ballDilation_mul]
    exact (mul_le_mul_left (coe_mul_rpow_pair_le c1 ha ha1 hεwork_le) _).trans (hitem1 x hx)
  · refine fun S hS => ⟨?_, hitem2sub S hS⟩
    rw [mul_assoc, ← NNReal.rpow_add ha.ne']
    exact (mul_rpow_le_of_exponent_le c2 ha ha1 (by linarith)).trans (hitem2 S hS)

end Kakeya

/-! ## The final assembly -/

namespace Kakeya

open scoped Classical in
/-- **The final assembly of GWZ Lemma 6.13.**

The public constants, in the public quantifier order, together with the complete witness package:
this is `ShadedPlank.reduction_to_slab` with `Kakeya.plankReduction.ballDilation` in place of the
`ShadedPlank` one (both are the literal `3`).

The working-window hypothesis is `Plank.IsWindowedFamily s (ShadedPlank.planks Y)` — containment of
the planks in the ball of radius `Plank.windowRadius = 4` — and not the stronger centre bound
`dist (Y i).center 0 ≤ 1`. The window is all the proof ever uses (through
`Plank.isWindowedFamily_of_dist_center_le_one`), and the Section 6 consumers state their hypothesis
against `Kakeya.plankWindow`, whose radius is also `4`; a plank with a centre anywhere in that
window has no reason to have its centre in the unit ball, so the centre form is not available
downstream. `Kakeya.plankReduction_of_center_le_one` keeps the centre form and
converts. -/
theorem plankReduction :
    ∃ cN cThk Cbox Cset Cang : ℝ≥0,
      1 ≤ cN ∧ 1 ≤ cThk ∧ cThk ≤ Cbox ∧ 1 ≤ Cset ∧ 1 ≤ Cang ∧
    ∀ {η ε : ℝ}, 0 < η → 0 < ε →
    ∃ cP cLam c1 c2 c3 c4 : ℝ≥0,
      0 < cP ∧ 0 < cLam ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 1 ≤ c4 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1),
      0 < a → a < 1 →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (Y i).carrier (Y j).carrier) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
    ∃ (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (N : ℕ) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
      (R : Plank.ThickenedRepr s' (ShadedPlank.planks Y) θ hθ1 cThk)
      (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
      (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ((cP * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0) ∧
      (cLam * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      1 ≤ N ∧ a / b ≤ θ ∧
      (∀ i ∈ s',
        i ∈ Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks Y) (slabOf (R.repr i))) ∧
      (∀ Q ∈ R.indexSet,
        ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) =
          ((Q.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ Q ∈ R.indexSet,
        (N : ℝ) / (cN : ℝ) ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) ∧
          (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) ≤ (cN : ℝ) * (N : ℝ)) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3),
        ((⋃ i ∈ s', (Y' i).shade) ∩ closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
          (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
              volume (closedBall x ((θ * b : ℝ≥0) : ℝ))
            ≤ volume ((⋃ i ∈ s', (Y' i).shade) ∩
              closedBall x ((plankReduction.ballDilation * θ * b : ℝ≥0) : ℝ))) ∧
      (∀ S ∈ R.indexSet.image slabOf,
        c2 * a ^ (4 * η) * a ^ ε ≤
          ShadedBody.fullness (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ ∧
        ∀ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S),
          (Yθ Q).shade ⊆
            ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks Y) S, (Y' i).shade) ∧
      (((c3 * a ^ ε : ℝ≥0) : ENNReal) *
            ∑ S ∈ R.indexSet.image slabOf,
              volume (⋃ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S), (Yθ Q).shade)
          ≤ volume (⋃ i ∈ s, (Y i).shade)) ∧
      (∃ S ∈ R.indexSet.image slabOf,
        ShadedBody.multiplicity s (ShadedPlank.bodies Y) ≤
          (c4 : ENNReal) * (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (-(4 * η)) *
            (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) *
            ShadedBody.multiplicity (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ) := by
  -- the absolute geometric block, uniform in `η` and `ε`
  obtain ⟨⟨cThk, Cset, Cang, Cang2, cOv0, cN, Ccarrier, Nov,
    h1cThk, h1Cset, h1Cang, h1Cang2, hCangLe, h1Nov, h0cOv0, h1cN, hcNle2, h1Ccarrier,
    hcThkLe, h4Cang, h4Cang2⟩, huniform⟩ := refinement_preassembly_uniform
  refine ⟨2, cThk, plankReduction.boxDilation Cang2 Ccarrier, Cset, Cang,
    one_le_two, h1cThk, plankReduction.cThk_le_boxDilation hcThkLe, h1Cset, h1Cang, ?_⟩
  intro η ε hη hε
  -- the ε ledger
  obtain ⟨εsharp, εcard, εwork, hs_eq, hp_eq, hw_eq, hs0, hp0, hw0,
    _hs_le, hp_le, _hw_le, hbudget, _hledger0⟩ := epsilon_split_sharp hη hε
  have hw8 : εwork ≤ ε / 8 := by rw [hw_eq]; exact min_le_left _ _
  have hεfo_le : 5 * εwork ≤ ε := by linarith only [hw8, hε.le]
  -- the preassembly, at `εwork`
  obtain ⟨⟨cP0, cLam0, Cθ, Cref, cEta, Cres, Cmult, εint,
    _h0cP0, h0cLam0, h1Cθ, h0Cmult, _h1Cref, _h0cEta, h0Cres, h0εint, hεint4⟩, hconfig⟩ :=
    huniform hη hw0
  have hεint_eq : εint = εwork / 4 := by linarith only [hεint4]
  have hsc : εsharp + εint ≤ εcard := by
    rw [hεint_eq]; linarith only [hs_eq, hp_eq, hw8, hε.le]
  have h4Ledger : εsharp + εint + 5 * (5 * εwork) / 4 ≤ ε := by
    rw [hεint_eq]; linarith only [hs_eq, hw8, hε.le]
  -- the sharp preassembly refinement coefficient
  obtain ⟨Csharp, hCsharp1, hsharp⟩ := exists_sharp_refinementCoeff hs0 h0Cres h1Cθ
  have hCsharp0 : (0 : ℝ≥0) < Csharp := lt_of_lt_of_le zero_lt_one hCsharp1
  have hNov0 : (0 : ℝ≥0) < (Nov : ℝ≥0) := mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1Nov
  have hcOvpos : (0 : ℝ≥0) < ((Nov : ℝ≥0))⁻¹ := inv_pos.mpr hNov0
  -- Item 1 and Item 2 constants
  obtain ⟨c1, cRef0, hc1, hcRef0, hitemOne⟩ :=
    slabwiseDensity_final Cθ Cset Cang Cmult cLam0 h1Cθ h1Cset h1Cang h0Cmult h0cLam0
      Nov h1Nov Nov h1Nov hη hw0 hbudget
  obtain ⟨c2, hc2pos, hitemTwo⟩ :=
    slabwiseShading_final cLam0 1 Cang2 Cset Ccarrier cN cRef0 Nov h0cLam0 zero_lt_one
      h1Cang2 h1Cset h1Ccarrier h1cN hcRef0 h1Nov hη hw0
  -- the Item 4 coefficient, at `εfo = 5 εwork`
  obtain ⟨c4, hc4one, hc4main⟩ :=
    exists_multiplicityCoefficient 2 ((Nov : ℝ≥0))⁻¹ c2 cRef0 Csharp Nov hcOvpos hc2pos hcRef0
      hCsharp1 h1Nov (η := η) (ε := ε) (εsharp := εsharp) (εpre := εint) (εint := εint)
      (εwork := 5 * εwork) le_rfl h4Ledger
  have hc2Nov : (0 : ℝ≥0) < (2 * (Nov : ℝ≥0))⁻¹ := inv_pos.mpr (mul_pos zero_lt_two hNov0)
  have hCsharpInv : (0 : ℝ≥0) < Csharp⁻¹ := inv_pos.mpr hCsharp0
  refine ⟨(2 * (Nov : ℝ≥0))⁻¹ * Csharp⁻¹, cRef0 * (2 * (Nov : ℝ≥0))⁻¹ * Csharp⁻¹, c1, c2,
    ((Nov : ℝ≥0))⁻¹, c4, mul_pos hc2Nov hCsharpInv,
    mul_pos (mul_pos hcRef0 hc2Nov) hCsharpInv, hc1, hc2pos, hcOvpos, hc4one, ?_⟩
  intro ι s a b hab hb1 Y ha ha1 hwin hED hfull hmult
  have ha1' : a ≤ 1 := le_of_lt ha1
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  obtain ⟨W⟩ := hconfig s (Y := Y) ha ha1 hwin hED hfull hmult
  -- `Slab W.θ _` and `Plank.ThickenedPlank …` carry no `DecidableEq`; the classical instance is the
  -- one the record's own `Finset.image` / `Finset.filter` fields were elaborated with.
  classical
  -- Aliases for the data that the mathematical body below mentions dozens of times.  Every
  -- *invariant* is read off `W` by field name, so inserting a clause upstream does not touch this
  -- proof.
  set s' := W.s'
  set Y' := W.Y'
  set θ := W.θ
  set N := W.N
  set R := W.R
  set slabOf := W.slabOf
  set rRef := W.rRef
  set Pr := W.Pr
  have hθ1 : θ ≤ 1 := W.hθ1
  have hdivb := W.θ_lb
  have hθpos := W.θ_pos
  have hN1 := W.one_le_N
  have hshV := W.shade_subset_plank
  have hcarEq := W.carrier_eq_plank
  have hfib := W.fibreCardinality
  have hov := W.pointwiseSlabOverlap
  -- volumes of the source carriers
  have hvolPlank : ∀ i, volume ((ShadedPlank.planks Y i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) = 8 * (a : ENNReal) * (b : ENNReal) :=
    fun i => ShadedPlank.volume_carrier (Y i)
  have hv0 : (8 * (a : ENNReal) * (b : ENNReal)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr ha.ne'))
      (ENNReal.coe_ne_zero.mpr hb.ne')
  have hvtop : (8 * (a : ENNReal) * (b : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.ofNat_ne_top) ENNReal.coe_ne_top)
      ENNReal.coe_ne_top
  have hY'car : ∀ i ∈ s', volume (Y' i).carrier = 8 * (a : ENNReal) * (b : ENNReal) :=
    fun i hi => by rw [hcarEq i hi]; exact hvolPlank i
  -- the configuration layer
  have hgeo : ∀ i ∈ s', i ∈ Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks Y)
      (slabOf (R.repr i)) := fun i hi => (W.slabMembership i hi).2
  obtain ⟨𝒮g, h𝒮gsub, hfullDom, hprune, h𝒮geq, hassigned, hfibeq, hslabmem₁⟩ :=
    plankReduction_configuration s' (ShadedPlank.planks Y) Y' R slabOf h1Nov hgeo hov
      (fun i hi => by rw [hY'car i hi]; exact pos_iff_ne_zero.mpr hv0)
      (fun i hi => by rw [hY'car i hi]; exact hvtop)
      (fun i _ => (Y' i).shade_subset)
      (mul_pos h0cLam0 (NNReal.rpow_pos ha))
      (by
        calc cLam0 * a ^ (η + εwork) = (cLam0 * a ^ εwork) * a ^ η := by
              rw [NNReal.rpow_add ha.ne']; ring
          _ ≤ (cLam0 * a ^ εwork) * ShadedBody.fullness s (ShadedPlank.bodies Y) :=
              mul_le_mul_right hfull _
          _ ≤ ShadedBody.fullness s' Y' := W.fullness)
  set s₁ : Finset ι := s'.filter (fun i => slabOf (R.repr i) ∈ 𝒮g)
  set Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    Plank.dominantSlabShading s' Y' R.repr slabOf Nov with hYdomdef
  have hs₁sub : s₁ ⊆ s' := Finset.filter_subset _ _
  -- Item 1 on the final family
  have hA2 : (2 : ℝ≥0) ≤ Real.toNNReal (max 2 (plankAngleScaleA a)) := by simp
  have hAmul : (Nov : ℝ≥0) * Real.toNNReal (max 2 (plankAngleScaleA a))
      = Real.toNNReal ((Nov : ℝ) * max 2 (plankAngleScaleA a)) := by
    rw [Real.toNNReal_mul (Nat.cast_nonneg _)]
    congr 1
    simp
  obtain ⟨G, hG, hlocRef, hitem1⟩ :=
    hitemOne s' (ShadedPlank.planks Y) Y' R slabOf 𝒮g
      (Real.toNNReal (max 2 (plankAngleScaleA a)))
      ha ha1 hb hθpos hb1 hdivb hA2 hslabmem₁ hassigned hfullDom hshV hcarEq W.maxAngle
      (by rw [hAmul]; simpa [hεint_eq] using W.typicalAngle_reserve)
      (by simpa [hεint_eq] using W.constantMultiplicity)
  set Yfin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    Plank.slabwiseRestrictShading Ydom R.repr slabOf G hG
  -- Item 2 on the final family
  obtain ⟨_hcarcoh, hitem2all⟩ :=
    hitemTwo s' (ShadedPlank.planks Y) Y' R slabOf Pr 𝒮g G hG
      ha ha1' ha1 hb hθpos hb1 hdivb hN1 hεfo_le hCangLe hassigned hfibeq hslabmem₁
      (fun S hS => by
        rw [hassigned S hS]
        exact Plank.assignedSlabFamily_nonempty_of_mem_image s' R.repr slabOf (h𝒮gsub hS))
      hlocRef
      (fun S hS => by
        have h := hfullDom S hS
        rwa [← mul_assoc] at h)
      hgeo (by simpa using W.maxAngle_one) W.stopScaleStability hshV hcarEq
      (fun i _ => le_of_eq (hvolPlank i).symm)
      W.shade_subset_anchor W.Pr_toPrismNDim W.reprAngle_own
      (fun t ht => ⟨(hfib t ht).2.1, (hfib t ht).2.2⟩)
  have hsh : Csharp⁻¹ * a ^ εsharp * a ^ εint ≤ rRef :=
    hsharp ha ha1 W.q_eq W.rRef_eq W.cGood_sharp W.cAngle_lb
  have hCrefSharp : Csharp⁻¹ * a ^ εcard ≤ rRef := by
    calc Csharp⁻¹ * a ^ εcard ≤ Csharp⁻¹ * a ^ (εsharp + εint) :=
          mul_le_mul_right (NNReal.rpow_le_rpow_of_exponent_ge ha ha1' hsc) _
      _ = Csharp⁻¹ * a ^ εsharp * a ^ εint := by rw [NNReal.rpow_add ha.ne']; ring
      _ ≤ rRef := hsh
  have hrRefpos : (0 : ℝ≥0) < rRef :=
    lt_of_lt_of_le (mul_pos hCsharpInv (NNReal.rpow_pos ha)) hCrefSharp
  obtain ⟨cPout, rDom, hcPoutpos, hrDompos, hcPouteq, hrDomeq, hrefDom, hcardDom⟩ :=
    plankReduction_refinement (Y := ShadedPlank.bodies Y) (Y' := Y') (Ydom := Ydom)
      (s := s) (s' := s') (s₁ := s₁) (v := 8 * (a : ENNReal) * (b : ENNReal))
      h1Nov (inv_pos.mpr hCsharp0) hrRefpos hv0 hvtop hprune W.isCRefinement hCrefSharp hfull
      (fun i _ => le_of_eq (hvolPlank i).symm)
      (fun i hi => by
        calc volume (Ydom i).shade ≤ volume (Ydom i).carrier :=
              measure_mono (Ydom i).shade_subset
          _ = volume (Y' i).carrier := by rw [hYdomdef]; rfl
          _ = 8 * (a : ENNReal) * (b : ENNReal) := hY'car i (hs₁sub hi))
  obtain ⟨_hglob, hrefFin, _hcGoodpos, _hfullFin⟩ :=
    slabwiseDensity_aggregate (a := a) (η := η + εwork) (εwork := εwork)
      (cRef0 := cRef0) (cGood := (2 * (Nov : ℝ≥0))⁻¹ * cLam0) (rFinal := rDom)
      ha hcRef0 (mul_pos hc2Nov h0cLam0) s s₁ (ShadedPlank.bodies Y) Ydom Yfin R.repr slabOf 𝒮g
      (fun i hi => (Finset.mem_filter.mp hi).2) hlocRef hrefDom
      (fun S hS => by
        rw [hassigned S hS, mul_assoc]
        exact hfullDom S hS)
  -- nonemptiness of the final family
  have hsne : s.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, show ShadedBody.multiplicity (∅ : Finset ι) (ShadedPlank.bodies Y) = 0 by
      simp [ShadedBody.multiplicity]] at hmult
    exact absurd hmult
      (not_le.mpr (ENNReal.rpow_pos (mod_cast ha) (by simp)))
  have hcard0 : (0 : ℝ≥0) < (s.card : ℝ≥0) := mod_cast Finset.card_pos.mpr hsne
  have hs₁ne : s₁.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast lt_of_lt_of_le
      (mul_pos (mul_pos (mul_pos hcPoutpos (NNReal.rpow_pos ha)) (NNReal.rpow_pos ha)) hcard0)
      hcardDom
  have hs₁ne' : (Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).Nonempty := by
    obtain ⟨i, hi⟩ := hs₁ne
    exact ⟨R.repr i, Finset.mem_image_of_mem _ hi⟩
  have hSne : ((Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).image slabOf).Nonempty :=
    hs₁ne'.image slabOf
  -- Item 3 / Item 4 overlap inputs
  have h𝒮₁sub : (Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).image slabOf
      ⊆ (s'.image R.repr).image slabOf :=
    Finset.image_subset_image (Finset.image_subset_image hs₁sub)
  have hYfinsubY' : ∀ i, (Yfin i).shade ⊆ (Y' i).shade := fun i =>
    (Plank.restrictShade_shade_subset (Ydom i) (G (slabOf (R.repr i)))
      (hG (slabOf (R.repr i)))).trans
      (Plank.dominantSlabShading_shade_subset s' Y' R.repr slabOf Nov i)
  have hbound : ∀ x : EuclideanSpace ℝ (Fin 3),
      (((Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).image slabOf).filter fun S =>
        x ∈ ⋃ i ∈ Plank.assignedSlabFamily s₁ (R.restrict hs₁sub).repr slabOf S,
          (Yfin i).shade).card ≤ Nov :=
    Plank.pointwise_overlap_assigned_of_le s₁ Yfin Y' R.repr slabOf
      ((Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).image slabOf)
      ((s'.image R.repr).image slabOf)
      (fun S => Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks Y) S) Nov h𝒮₁sub
      (fun S _ => fun i hi =>
        Plank.assignedSlabFamily_subset_inSlabFamilyC_of_mem Cset Cang s'
          (ShadedPlank.planks Y) R.repr slabOf S hgeo
          (Plank.mem_assignedSlabFamily.mpr
            ⟨hs₁sub (Plank.assignedSlabFamily_subset s₁ R.repr slabOf S hi),
              (Plank.mem_assignedSlabFamily.mp hi).2⟩))
      hYfinsubY' hov
  have hovAssigned :
      ((((Nov : ℝ≥0))⁻¹ : ℝ≥0) : ENNReal) *
          (∑ S ∈ (Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).image slabOf,
            volume (⋃ i ∈ Plank.assignedSlabFamily s₁ (R.restrict hs₁sub).repr slabOf S,
              (Yfin i).shade))
        ≤ volume (⋃ i ∈ s₁, (Yfin i).shade) := by
    refine Plank.overlap_assignedSlabFamily_of_pointwise s₁ Yfin (R.restrict hs₁sub).repr slabOf
      ((Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).image slabOf) Nov ((Nov : ℝ≥0))⁻¹
      ?_ hbound
    rw [ENNReal.coe_inv hNov0.ne']
    simp
  have h𝒮g' : (Plank.ThickenedRepr.indexSet (R.restrict hs₁sub)).image slabOf = 𝒮g := h𝒮geq
  -- the final call
  refine ⟨s₁, Yfin, N, θ, hθ1, R.restrict hs₁sub, slabOf,
    Plank.sharedSlabThickenedShadingDilation (plankReduction.boxDilation Cang2 Ccarrier) s₁ Yfin
      (fun Q => Q.toPrismNDim) (R.restrict hs₁sub).repr slabOf, ?_⟩
  refine plankReduction_outputs (Cbox := plankReduction.boxDilation Cang2 Ccarrier)
    (cP := (2 * (Nov : ℝ≥0))⁻¹ * Csharp⁻¹)
    (cLam := cRef0 * (2 * (Nov : ℝ≥0))⁻¹ * Csharp⁻¹)
    (c1 := c1) (c2 := c2) (c3 := ((Nov : ℝ≥0))⁻¹) (c4 := c4)
    (cOv := ((Nov : ℝ≥0))⁻¹) (Cgeom := 2) (cN0 := cN)
    (rFinalFin := (cRef0 * a ^ (εwork / 4)) * rDom) (N := N)
    (volP := 8 * (a : ENNReal) * (b : ENNReal))
    (η := η) (ε := ε) (εpre := εcard) (εwork := 5 * εwork)
    s s₁ Y (R.restrict hs₁sub) slabOf Yfin _
    (Plank.assignedSlabFamily s₁ (R.restrict hs₁sub).repr slabOf)
    rfl ha ha1' hb hθpos hN1 hdivb hεfo_le hp_le hcOvpos hc2pos le_rfl h1cN hcNle2
    hrefFin ?_ ?_ (by rw [← hcPouteq]; exact hcardDom) hslabmem₁ ?_ ?_ ?_ ?_
    (fun _ _ => Finset.Subset.refl _) hovAssigned ?_ ?_ hSne ?_ hovAssigned ?_ ?_ ?_
  · -- `rFinalFin ≠ 0`
    exact (mul_pos (mul_pos hcRef0 (NNReal.rpow_pos ha)) hrDompos).ne'
  · -- `cLam · a ^ ε ≤ rFinalFin`, using `εsharp + εint + εwork / 4 ≤ ε`
    rw [hrDomeq]
    calc (cRef0 * (2 * (Nov : ℝ≥0))⁻¹ * Csharp⁻¹) * a ^ ε
        ≤ (cRef0 * (2 * (Nov : ℝ≥0))⁻¹ * Csharp⁻¹) * a ^ (εwork / 4 + εsharp + εint) :=
          mul_le_mul_right (NNReal.rpow_le_rpow_of_exponent_ge ha ha1'
            (by linarith only [hεint_eq, hs_eq, hw8, hε.le])) _
      _ = (cRef0 * a ^ (εwork / 4)) *
            ((2 * (Nov : ℝ≥0))⁻¹ * (Csharp⁻¹ * a ^ εsharp * a ^ εint)) := by
          rw [NNReal.rpow_add ha.ne', NNReal.rpow_add ha.ne']; ring
      _ ≤ (cRef0 * a ^ (εwork / 4)) * ((2 * (Nov : ℝ≥0))⁻¹ * rRef) :=
          mul_le_mul_right (mul_le_mul_right hsh _) _
  · -- the fibre bounds, transported by slab-completeness
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hQ : slabOf (R.repr i) ∈ 𝒮g := (Finset.mem_filter.mp hi).2
    simp only [Plank.ThickenedRepr.restrict_repr]
    rw [hfibeq _ hQ]
    exact ⟨(hfib _ (Finset.mem_image_of_mem R.repr (hs₁sub hi))).2.1,
      (hfib _ (Finset.mem_image_of_mem R.repr (hs₁sub hi))).2.2⟩
  · -- Item 1, weakened from `4η + εwork` to `4η + εfo`
    intro x hx
    refine le_trans (mul_le_mul_left ?_ _) (hitem1 x hx)
    exact ENNReal.coe_le_coe.mpr
      (mul_le_mul_right (NNReal.rpow_le_rpow_of_exponent_ge ha ha1'
        (by linarith only [hw0.le])) _)
  · -- Item 2, strong form
    intro S hS
    rw [h𝒮g'] at hS
    exact (hitem2all S hS).1
  · -- the Item 2 shade containment
    intro S hS
    rw [h𝒮g'] at hS
    exact (hitem2all S hS).2.2
  · -- the final shading union sits inside the original one
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, W.subset (hs₁sub hi),
      (W.isRefinement.2 i (hs₁sub hi)).2 (hYfinsubY' i hxi)⟩
  · -- `c₃ · a ^ ε ≤ cOv`
    exact (mul_le_mul_right (NNReal.rpow_le_one ha1' hε.le) _).trans_eq (mul_one _)
  · -- canonical slab membership of the active family
    intro i hi
    exact Finset.mem_image_of_mem slabOf (Finset.mem_image_of_mem _ hi)
  · -- the shade volume bound
    intro S _ i hi
    have hi' : i ∈ s₁ := Plank.assignedSlabFamily_subset _ _ _ _ hi
    calc volume (Yfin i).shade ≤ volume (Y' i).carrier :=
          measure_mono ((hYfinsubY' i).trans (Y' i).shade_subset)
      _ = 8 * (a : ENNReal) * (b : ENNReal) := hY'car i (hs₁sub hi')
  · -- the carrier volume of `Yθfin`, lifted from `Ccarrier` to `Cbox`
    intro S _ t ht
    have ht' : t ∈ s'.image R.repr :=
      Finset.image_subset_image hs₁sub (Finset.mem_of_mem_filter t ht)
    exact le_trans (W.volume_anchor_lb t ht')
      (measure_mono (PrismNDim.dilation_carrier_mono t.toPrismNDim
        (plankReduction.le_boxDilation Cang2 Ccarrier)))
  · -- the Item 4 coefficient, transported from `rFinalAux` by antitonicity of the inverse
    have hbase := hc4main (a := a) (rPre := rRef)
      (rFinal := (cRef0 * a ^ (5 * εwork / 4)) * ((2 * (Nov : ℝ≥0))⁻¹ * rRef))
      (β := c2 * a ^ (4 * η + 5 * εwork)) ha ha1 rfl hsh rfl
    have hle : (cRef0 * a ^ (5 * εwork / 4)) * ((2 * (Nov : ℝ≥0))⁻¹ * rRef)
        ≤ (cRef0 * a ^ (εwork / 4)) * rDom := by
      rw [hrDomeq]
      exact mul_le_mul_left
        (mul_le_mul_right (NNReal.rpow_le_rpow_of_exponent_ge ha ha1'
          (by linarith only [hw0.le])) _) _
    refine le_trans (mul_le_mul_left (mul_le_mul_left (mul_le_mul_right ?_ _) _) _) hbase
    exact ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr hle)

open scoped Classical in
/-- **The final assembly of GWZ Lemma 6.13, in the paper's normalisation.**

Identical to `Kakeya.plankReduction` — same constants, same quantifier order,
same witness package — except that the working window is recorded by the centre bound
`dist (Y i).center 0 ≤ 1` of the paper rather than by
`Plank.IsWindowedFamily s (ShadedPlank.planks Y)`.  This is the form consumed by
`ShadedPlank.reduction_to_slab`; the windowed form is the one Section 6 calls, since its own
hypotheses are stated against `Kakeya.plankWindow`, whose radius is `Plank.windowRadius = 4`, and a
plank with a centre anywhere in that window has no reason to have its centre in the unit ball. -/
theorem plankReduction_of_center_le_one :
    ∃ cN cThk Cbox Cset Cang : ℝ≥0,
      1 ≤ cN ∧ 1 ≤ cThk ∧ cThk ≤ Cbox ∧ 1 ≤ Cset ∧ 1 ≤ Cang ∧
    ∀ {η ε : ℝ}, 0 < η → 0 < ε →
    ∃ cP cLam c1 c2 c3 c4 : ℝ≥0,
      0 < cP ∧ 0 < cLam ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 1 ≤ c4 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1),
      0 < a → a < 1 →
      (∀ i ∈ s, dist (Y i).center (0 : EuclideanSpace ℝ (Fin 3)) ≤ 1) →
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (Y i).carrier (Y j).carrier) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
    ∃ (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (N : ℕ) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
      (R : Plank.ThickenedRepr s' (ShadedPlank.planks Y) θ hθ1 cThk)
      (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
      (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ((cP * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0) ∧
      (cLam * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      1 ≤ N ∧ a / b ≤ θ ∧
      (∀ i ∈ s',
        i ∈ Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks Y) (slabOf (R.repr i))) ∧
      (∀ Q ∈ R.indexSet,
        ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) =
          ((Q.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ Q ∈ R.indexSet,
        (N : ℝ) / (cN : ℝ) ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) ∧
          (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) ≤ (cN : ℝ) * (N : ℝ)) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3),
        ((⋃ i ∈ s', (Y' i).shade) ∩ closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
          (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
              volume (closedBall x ((θ * b : ℝ≥0) : ℝ))
            ≤ volume ((⋃ i ∈ s', (Y' i).shade) ∩
              closedBall x ((plankReduction.ballDilation * θ * b : ℝ≥0) : ℝ))) ∧
      (∀ S ∈ R.indexSet.image slabOf,
        c2 * a ^ (4 * η) * a ^ ε ≤
          ShadedBody.fullness (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ ∧
        ∀ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S),
          (Yθ Q).shade ⊆
            ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks Y) S, (Y' i).shade) ∧
      (((c3 * a ^ ε : ℝ≥0) : ENNReal) *
            ∑ S ∈ R.indexSet.image slabOf,
              volume (⋃ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S), (Yθ Q).shade)
          ≤ volume (⋃ i ∈ s, (Y i).shade)) ∧
      (∃ S ∈ R.indexSet.image slabOf,
        ShadedBody.multiplicity s (ShadedPlank.bodies Y) ≤
          (c4 : ENNReal) * (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (-(4 * η)) *
            (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) *
            ShadedBody.multiplicity (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ) := by
  obtain ⟨cN, cThk, Cbox, Cset, Cang, h1cN, h1cThk, hcThkBox, h1Cset, h1Cang, hmain⟩ :=
    plankReduction
  refine ⟨cN, cThk, Cbox, Cset, Cang, h1cN, h1cThk, hcThkBox, h1Cset, h1Cang, ?_⟩
  intro η ε hη hε
  obtain ⟨cP, cLam, c1, c2, c3, c4, hcP, hcLam, hc1, hc2, hc3, hc4, hconfig⟩ := hmain hη hε
  refine ⟨cP, cLam, c1, c2, c3, c4, hcP, hcLam, hc1, hc2, hc3, hc4, ?_⟩
  intro ι s a b hab hb1 Y ha ha1 hcenter hED hfull hmult
  exact hconfig s Y ha ha1
    (Plank.isWindowedFamily_of_dist_center_le_one s (ShadedPlank.planks Y) hcenter) hED hfull hmult

end Kakeya

end

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.RepresentativeShading
public import Kakeya.DimensionThree.Plank.SlabwiseInputs
public import Kakeya.DimensionThree.Plank.ExponentBudget
public import Kakeya.DimensionThree.Plank.SlabwiseDensity
public import Kakeya.DimensionThree.Plank.RestrictShadeTransport
public import Kakeya.DimensionThree.Plank.SlabIndexOverlap
public import Kakeya.DimensionThree.Plank.StableRefinement
public import Kakeya.DimensionThree.Plank.TypicalAngleTransfer

/-!
# The slabwise route through Items 1 and 2 of GWZ Lemma 6.13

Items 1 and 2 of GWZ Lemma 6.13 are run *slabwise*, on the assigned families
`𝒜 S = Plank.assignedSlabFamily s₁ repr slabOf S`, rather than once on the whole final family.
This
module carries that route end to end, in four stages:

0. **The Item 1 output package** (`Kakeya.slabwiseDensity_of_outputs`,
   `Kakeya.slabwiseDensity_publicClauses`) — the abstract slab-local data of
   `Plank.slabwiseDensity_of_preassembly` is *chosen*, so that the hypothesis list reduces to
   clauses
   `Kakeya.plankReduction_preassembly` literally returns, and the public clauses are transported
   across the common restriction.
1. **Item 1, slabwise** (`Kakeya.slabwiseDensity_assigned`, `Kakeya.slabwiseDensity`) — one
   retained set `G S` per active slab, and the shading
   `Plank.slabwiseRestrictShading Ydom repr slabOf G hG` that cuts each plank against the retained
   set of its own slab.
2. **Aggregation and local fullness** (`Kakeya.slabwiseDensity_aggregate`) — the slab-local
   refinements add up to a global one at the same coefficient, and the slab-local fullness of the
   slabwise shading is read off at the strong exponent.
3. **Item 2, rerun on the slabwise shading** (`Kakeya.slabwiseRepresentativeShading`) — the C-linear
   Item 2 core is rebuilt on `(𝒜 S, Yfin)`, one slab at a time by a private fixed-slab theorem, and
   weakened to the public exponent pair only at the very end.

`εwork` stays symbolic throughout: no final split of `ε` is chosen in this module.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

/-!
## The Item 1 output package of GWZ Lemma 6.13

`Plank.slabwiseDensity_of_preassembly` is abstract in the slab-local data
`(Cset', Cang', cTan, Ceta, Nov, T, Z, lamScale)`.  This section *chooses* all of it, so that its
hypothesis list reduces to clauses `Kakeya.plankReduction_preassembly` literally returns.

The choices, all made before any geometric datum:

```
Cang' = 2 * Cang + 4 * Cθ
Cset' = Cset + 4 * (2 * Cang + 4 * Cθ) + 8
cTan  from Plank.tangentiality_of_trimmedSlabFamilies Cang'
Ceta  from Plank.localAngleConcentration_of_preassemblyData Cθ Cθ
        at εs := εwork/4 and ηL := η + 5εwork/4
Nov   = max Nov_pt Nov_idx,  Nov_idx from Plank.slab_index_overlap_le Cset' Cang'
```

and, per configuration,

```
T S sh q  = (inSlabFamilyC Cset' Cang' s' P S).filter fun i =>
              ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩ halfSlabBox S b sh q).Nonempty
Z S sh q i = ShadedBody.restrictShade (trimmedSlabShading Cset Cang s' P Y' S i)
               (halfSlabBox S b sh q) _
lamLower  = cLamPre * a ^ (η + εwork)
lamScale  = (2 Cmult)⁻¹ * a ^ (εwork/4) * lamLower / (512 * Nov * cTan)
cLamBox   = (2 Cmult)⁻¹ * cLamPre / (512 * Nov * cTan)
```

`Plank.tangentiality_of_trimmedSlabFamilies` and
`Plank.localAngleConcentration_of_preassemblyData` discharge the two non-formal hypotheses; every
other one is a preassembly clause, widened where necessary from `Nov_pt` / `Nov_idx` to the common
`Nov`.  No `#𝒮` factor and no new power of `a` enter: `Nov` only enlarges an absolute constant, and
`Kakeya.lamScale_eq` turns the threshold into `cLamBox · a ^ (η + 5εwork/4)` with
*equality*.
-/

namespace Kakeya

section ItemOneOutputs

variable {ι : Type*}

open scoped Classical in
/-- **The Item 1 output package, from the clauses `Kakeya.plankReduction_preassembly` returns.**

Both returned constants are fixed before the index type and the configuration:

* `c1 = cBall · cLamBox²` is the Item 1 density coefficient, so Item 1 holds at
  `c1 · a ^ (4η + εwork)` with outer dilation exactly `Kakeya.plankReduction.ballDilation = 3`;
* `cRef0 = (256 · Nov · C_mult)⁻¹` is the strong refinement coefficient of the common restriction,
  so `Yfinal = fun i => ShadedBody.restrictShade (Y' i) Gtot` is a quantitative refinement of
  `Y'` at
  `cRef0 · a ^ (εwork/4)` on the *same* index set `s'` — no cardinality is lost.

The typical-angle input is used at the *polynomial* constant `Cθ · a ^ (-εwork/4)` that the
preassembly actually delivers; see
`Kakeya/DimensionThree/Plank/PolynomialStabilityConcentration.lean`. -/
theorem slabwiseDensity_of_outputs
    (Cθ Cset Cang Cmult cLamPre : ℝ≥0)
    (hCθ : 1 ≤ Cθ) (hCset : 1 ≤ Cset) (hCang : 1 ≤ Cang)
    (hCmult : 0 < Cmult) (hcLamPre : 0 < cLamPre)
    (Novpt : ℕ) (hNovpt : 1 ≤ Novpt)
    {η εwork : ℝ} (hη : 0 < η) (hεwork : 0 < εwork)
    (hbudget : 3 * (η + 5 * εwork / 4) ≤ 4 * η + εwork) :
    ∃ c1 cRef0 : ℝ≥0, 0 < c1 ∧ 0 < cRef0 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (s' : Finset ι) (P : ι → Plank a b hab hb1)
        (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒮 : Finset (Slab θ hθ1)) (A : ℝ≥0),
        0 < a → a < 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ → 2 ≤ A →
        ((↑𝒮 : Set (Slab θ hθ1)).Pairwise
          (fun S S' => PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim)) →
        (∀ i ∈ s', ∃ S ∈ 𝒮, i ∈ Plank.inSlabFamilyC Cset Cang s' P S) →
        (∀ x : EuclideanSpace ℝ (Fin 3),
          (𝒮.filter fun S => x ∈ ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s' P S,
            (Y' i).shade).card ≤ Novpt) →
        (∀ i ∈ s', (Y' i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s', ((Y' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        HasMaxPlankAngleBound s' Y' P θ Cθ →
        IsTypicalPlankAngle s' Y' P θ (Cθ * a ^ (-(εwork / 4))) A →
        cLamPre * a ^ (η + εwork) ≤ ShadedBody.fullness s' Y' →
        ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-(εwork / 4))) →
        ∃ (Gtot : Set (EuclideanSpace ℝ (Fin 3))) (hGtot : MeasurableSet Gtot),
          ShadedBody.IsCRefinement s'
              (fun i => ShadedBody.restrictShade (Y' i) Gtot hGtot) s' Y'
              (cRef0 * a ^ (εwork / 4)) ∧
          ∀ x : EuclideanSpace ℝ (Fin 3),
            ((⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) Gtot hGtot).shade) ∩
              Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
              ((c1 * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
                  volume (Metric.closedBall x ((θ * b : ℝ≥0) : ℝ))
                ≤ volume ((⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) Gtot hGtot).shade) ∩
                  Metric.closedBall x
                    ((plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))) := by
  let Cang' : ℝ≥0 := 2 * Cang + 4 * Cθ
  let Cset' : ℝ≥0 := Cset + 4 * (2 * Cang + 4 * Cθ) + 8
  have hCangLe : Cang ≤ Cang' :=
    (le_mul_of_one_le_left zero_le one_le_two).trans le_self_add
  have hCsetLe : Cset ≤ Cset' := le_self_add.trans le_self_add
  have hCang' : 1 ≤ Cang' := hCang.trans hCangLe
  have hCset' : 1 ≤ Cset' := hCset.trans hCsetLe
  obtain ⟨cTan, hcTan, htanlem⟩ := Plank.tangentiality_of_trimmedSlabFamilies Cang' hCang'
  obtain ⟨Ceta, hCeta, hLAClem⟩ :=
    Plank.localAngleConcentration_of_preassemblyData Cθ Cθ hCθ hCθ (εs := εwork / 4)
      (ηL := η + 5 * εwork / 4) (by linarith) (by linarith)
  obtain ⟨Novidx, hNovidx1, hovidxlem⟩ := Plank.slab_index_overlap_le Cset' Cang' hCang'
  let Nov : ℕ := max Novpt Novidx
  have hNovpt_le : Novpt ≤ Nov := Nat.le_max_left Novpt Novidx
  have hNovidx_le : Novidx ≤ Nov := Nat.le_max_right Novpt Novidx
  have hNov : 1 ≤ Nov := hNovpt.trans hNovpt_le
  obtain ⟨cBall, hcBall, hitemOne⟩ := Plank.slabwiseDensity_of_preassembly cTan Ceta hCeta
  let cLamBox : ℝ≥0 := (2 * Cmult)⁻¹ * cLamPre / (512 * (Nov : ℝ≥0) * cTan)
  have hcLamBox : 0 < cLamBox := Kakeya.cLamBox_pos hCmult hcLamPre hNov hcTan
  refine ⟨cBall * cLamBox * cLamBox, (256 * (Nov : ℝ≥0) * Cmult)⁻¹,
    mul_pos (mul_pos hcBall hcLamBox) hcLamBox, inv_pos.mpr (by positivity), ?_⟩
  · intro a b θ hab hb1 hθ1 ι s' P Y' 𝒮 A ha ha1 hb hθ hb1' hdivb hA hED hcover hovPt hshV
      hcarEq hmax htyp hfull hC
    have hhalfmeas : ∀ S : Slab θ hθ1, ∀ sh q, MeasurableSet (Plank.halfSlabBox S b sh q) :=
      fun _ _ _ => PrismNDim.measurableSet_carrier _
    let T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι :=
      fun S sh q => (Plank.inSlabFamilyC Cset' Cang' s' P S).filter
        (fun i => ((Plank.trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
          Plank.halfSlabBox S b sh q).Nonempty)
    let Z : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι →
        ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
      fun S sh q i => ShadedBody.restrictShade (Plank.trimmedSlabShading Cset Cang s' P Y' S i)
        (Plank.halfSlabBox S b sh q) (hhalfmeas S sh q)
    let lamScale : ℝ≥0 :=
      (2 * Cmult)⁻¹ * a ^ (εwork / 4) * (cLamPre * a ^ (η + εwork)) /
        (512 * (Nov : ℝ≥0) * cTan)
    have hηL : 0 < η + 5 * εwork / 4 := add_pos hη (by positivity)
    have hlamScale_le : cLamBox * a ^ (η + 5 * εwork / 4) ≤ lamScale :=
      (Kakeya.lamScale_eq ha (by ring)).ge
    have haθb : a ≤ θ * b := (div_le_iff₀ hb).mp hdivb
    have hovIdx : ∀ i ∈ s', (𝒮.filter fun S => i ∈ Plank.inSlabFamilyC Cset' Cang' s' P S).card ≤
        Nov := fun i hi => (hovidxlem s' P hθ1 𝒮 hθ hdivb hED i hi).trans hNovidx_le
    have hovPt' : ∀ x, (𝒮.filter fun S => x ∈ Plank.smallSlabUnion Cset Cang s' P Y' S).card ≤
        Nov := fun x => (hovPt x).trans hNovpt_le
    have hT_def : ∀ S sh q, T S sh q = (Plank.inSlabFamilyC Cset' Cang' s' P S).filter
        (fun i => ((Plank.trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
          Plank.halfSlabBox S b sh q).Nonempty) := fun _ _ _ => rfl
    have hZsh : ∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).shade
        = (Plank.trimmedSlabShading Cset Cang s' P Y' S i).shade ∩ Plank.halfSlabBox S b sh q :=
      fun _ _ _ _ _ => rfl
    have hZcar : ∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).carrier = (P i).carrier := by
      intro S sh q i hi
      rw [Plank.restrictShade_carrier, Plank.trimmedSlabShading_carrier]
      exact hcarEq i (Plank.inSlabFamilyC_subset (Finset.mem_filter.mp hi).1)
    have htan : ∀ S sh q, ∀ i ∈ T S sh q, Kakeya.ComparableScalars cTan
        (volume (((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
          (Plank.shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2) :=
      htanlem Cset Cang Cset' s' P Y' T ha hb haθb hshV hT_def
    have hLAC : ∀ S : Slab θ hθ1, ∀ Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ),
        Plank.LocalAngleConcentration P θ Plank.gridShiftSet (Dg S) (T S) (Z S) Ceta
          (η + 5 * εwork / 4) :=
      hLAClem Cset Cang Cset' Cang' A s' P Y' T Z ha ha1 hb hθ haθb hA le_rfl le_rfl
        hshV hmax htyp hT_def hZsh
    exact hitemOne Cset Cang Cset' Cang' Cmult cLamBox (cLamPre * a ^ (η + εwork)) lamScale
      η εwork (εwork / 4) (η + 5 * εwork / 4) Nov s' P Y' 𝒮 T Z
      hcTan hCset' hCmult hNov ha ha1.le hb hθ hb1' hdivb hηL hcLamBox hbudget
      hlamScale_le rfl hCsetLe hCangLe hcover hovIdx hovPt' hshV hcarEq
      hT_def hZsh hZcar htan hZcar hLAC hfull hC

/-! ### Transporting the public clauses to the restricted family -/

/-- **The four public clauses of GWZ Lemma 6.13 survive the common restriction, at the public `ε`.**

The Item 1 output package restricts every shading to one global measurable `Gtot`.  This records
what that costs on the clauses `Kakeya.plankReduction` states, and discharges the passage from the
internal `εwork` to the public `ε`:

* *refinement*: compose the strong refinement of the restriction with the preassembly's, by
  `ShadedBody.IsRefinement.trans`;
* *cardinality*: unchanged, the index set is still `s'`; only `a ^ εwork` is weakened to `a ^ ε`;
* *fullness*: `Plank.fullness_ge_of_isCRefinement` charges the restriction coefficient
  `cRef0 · a ^ (εwork/4)`, so the composed exponent is `εwork + εwork/4 = 5εwork/4`, absorbed into
  `a ^ ε` by `5 * εwork / 4 ≤ ε`;
* *typical angle*: `Plank.isTypicalPlankAngle_restrictShade` transports the *two-sided* predicate at
  the same `θ`, the same constant and the same stability scale — the shade fibres are literally
  equal on `Gtot` — and `Kakeya.IsTypicalPlankAngle.mono_const` then enlarges the constant from
  `Cθ · a ^ (-εwork)` to `Cθ · a ^ (-ε)`.

Every weakening is an explicit `NNReal` rpow monotonicity step at `0 < a ≤ 1`; none is hidden in a
simp set.  The carrier identity and shade inclusion are recorded for Items 2–4. -/
theorem slabwiseDensity_publicClauses
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s s' : Finset ι} {Y : ι → ShadedPlank a b hab hb1}
    {Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {Gtot : Set (EuclideanSpace ℝ (Fin 3))} (hGtot : MeasurableSet Gtot)
    {cP cLam Cθ cRef0 A0 : ℝ≥0} {η ε εwork : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hεwle : εwork ≤ ε) (h54 : 5 * εwork / 4 ≤ ε)
    (hRefPre : ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y))
    (hcardPre : ((cP * a ^ η) * a ^ εwork) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0))
    (hfullPre : (cLam * a ^ εwork) * ShadedBody.fullness s (ShadedPlank.bodies Y)
      ≤ ShadedBody.fullness s' Y')
    (htypPre : IsTypicalPlankAngle s' Y' (ShadedPlank.planks Y) θ (Cθ * a ^ (-εwork)) A0)
    (hcref : ShadedBody.IsCRefinement s'
      (fun i => ShadedBody.restrictShade (Y' i) Gtot hGtot) s' Y' (cRef0 * a ^ (εwork / 4))) :
    ShadedBody.IsRefinement s' (fun i => ShadedBody.restrictShade (Y' i) Gtot hGtot) s
        (ShadedPlank.bodies Y) ∧
      ((cP * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0) ∧
      ((cRef0 * cLam) * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y)
        ≤ ShadedBody.fullness s' (fun i => ShadedBody.restrictShade (Y' i) Gtot hGtot) ∧
      IsTypicalPlankAngle s' (fun i => ShadedBody.restrictShade (Y' i) Gtot hGtot)
        (ShadedPlank.planks Y) θ (Cθ * a ^ (-ε)) A0 ∧
      (∀ i, ((ShadedBody.restrictShade (Y' i) Gtot hGtot).carrier
          : Set (EuclideanSpace ℝ (Fin 3)))
        = ((Y' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ i, (ShadedBody.restrictShade (Y' i) Gtot hGtot).shade ⊆ (Y' i).shade) := by
  have hpow1 : a ^ ε ≤ a ^ εwork := NNReal.rpow_le_rpow_of_exponent_ge ha ha1 hεwle
  have hpow2 : a ^ ε ≤ a ^ (5 * εwork / 4) := NNReal.rpow_le_rpow_of_exponent_ge ha ha1 h54
  have hpow3 : a ^ (-εwork) ≤ a ^ (-ε) :=
    NNReal.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith)
  have hpow_split : a ^ (εwork / 4) * a ^ εwork = a ^ (5 * εwork / 4) := by
    rw [← NNReal.rpow_add ha.ne', show εwork / 4 + εwork = 5 * εwork / 4 by ring]
  refine ⟨ShadedBody.IsRefinement.trans hcref.1 hRefPre,
    (mul_le_mul_left (mul_le_mul_right hpow1 (cP * a ^ η)) (s.card : ℝ≥0)).trans hcardPre, ?_,
    Kakeya.IsTypicalPlankAngle.mono_const (mul_le_mul_right hpow3 Cθ)
      (Plank.isTypicalPlankAngle_restrictShade s' Y' (ShadedPlank.planks Y) Gtot hGtot htypPre),
    fun i => Plank.restrictShade_carrier (Y' i) Gtot hGtot,
    fun i => Plank.restrictShade_shade_subset (Y' i) Gtot hGtot⟩
  calc ((cRef0 * cLam) * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y)
      ≤ ((cRef0 * cLam) * a ^ (5 * εwork / 4)) *
          ShadedBody.fullness s (ShadedPlank.bodies Y) :=
        mul_le_mul_left (mul_le_mul_right hpow2 (cRef0 * cLam)) _
    _ = (cRef0 * a ^ (εwork / 4)) *
          ((cLam * a ^ εwork) * ShadedBody.fullness s (ShadedPlank.bodies Y)) := by
        rw [← hpow_split]; ring
    _ ≤ (cRef0 * a ^ (εwork / 4)) * ShadedBody.fullness s' Y' :=
        mul_le_mul_right hfullPre (cRef0 * a ^ (εwork / 4))
    _ ≤ ShadedBody.fullness s' (fun i => ShadedBody.restrictShade (Y' i) Gtot hGtot) :=
        Plank.fullness_ge_of_isCRefinement hcref

end ItemOneOutputs

end Kakeya

/-!
## Item 1 of GWZ Lemma 6.13, run slabwise on the assigned families

Item 1 restricts every shading to one retained measurable set.  Run once on the whole final family
that set is *global*, and the resulting restriction destroys the slab-local fullness that Items 2–4
were established with.  Running Item 1 separately on each assigned family
`𝒜 S = Plank.assignedSlabFamily s₁ repr slabOf S`, with the singleton slab family `{S}`, produces
instead one retained set `G S` per slab, and the shading

`Yfin i = ShadedBody.restrictShade (Ydom i) (G (slabOf (repr i))) _`

cuts each plank against the retained set of *its own* slab.  On `𝒜 S` this is literally the common
restriction by `G S`, so all slab-local data can still be read off with the
`ShadedBody.restrictShade` transports, while globally the Item 1 density still holds: a point
of the global `Yfin` union exhibits the assigned slab of the plank shading it, and that slab's
local estimate applies.

`Kakeya.slabwiseDensity_of_outputs` binds its two constants `c1`, `cRef0` before the index type
and the configuration, so a single `obtain` before the slab binder gives constants uniform in `S`.
Only `G` depends on `S`.

The pointwise fibre retention of the assigned family is taken as a hypothesis rather than unfolded;
the intended instance is the dominant-region retention of
`Kakeya/DimensionThree/Plank/SlabSelection.lean`.  Keeping it abstract also keeps the
elaborated terms small.

`εwork` stays symbolic here: only the existing Item 1 budget
`3 * (η + 5 * εwork / 4) ≤ 4 * η + εwork` is required, and no final split of `ε` is chosen.
-/

namespace Plank

variable {ι τ : Type*}

/-! ### The slabwise restricted shading -/

/-- **The slabwise retained shading.**  Each plank is cut against the retained set of its own
assigned slab.  On `Plank.assignedSlabFamily s₁ repr slabOf S` this is the common restriction by
`G S`, which is what lets the `ShadedBody.restrictShade` transports apply slab by slab. -/
def slabwiseRestrictShading {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
    (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (hG : ∀ S, MeasurableSet (G S)) (i : ι) : ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
  ShadedBody.restrictShade (Ydom i) (G (slabOf (repr i))) (hG (slabOf (repr i)))

/-- **On the assigned family of `S`, the slabwise shading is the common restriction by `G S`.**
This is the identity that makes every slab-local `ShadedBody.restrictShade` transport applicable. -/
theorem slabwiseRestrictShading_eq_of_mem_assigned {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
    (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (hG : ∀ S, MeasurableSet (G S))
    (s₁ : Finset ι) (S : Slab θ hθ1) {i : ι} (hi : i ∈ assignedSlabFamily s₁ repr slabOf S) :
    slabwiseRestrictShading Ydom repr slabOf G hG i
      = ShadedBody.restrictShade (Ydom i) (G S) (hG S) := by
  simp only [slabwiseRestrictShading, (mem_assignedSlabFamily.mp hi).2]

/-- **The assigned shade fibre is unchanged by the slabwise restriction.**  At a point of the
slab-local `Yfin` union the restriction removes nothing from the `𝒜 S`-fibre, because on `𝒜 S` the
cut is by the single set `G S` and the point lies in it. -/
theorem shadeFibre_assignedSlabFamily_slabwiseRestrictShading {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
    (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (hG : ∀ S, MeasurableSet (G S))
    (s₁ : Finset ι) (S : Slab θ hθ1) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S,
      (slabwiseRestrictShading Ydom repr slabOf G hG i).shade) :
    Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S)
        (slabwiseRestrictShading Ydom repr slabOf G hG) x
      = Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x := by
  obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hx
  rw [slabwiseRestrictShading_eq_of_mem_assigned Ydom repr slabOf G hG s₁ S hi₀] at hxi₀
  ext i
  rw [Kakeya.mem_shadeFibre, Kakeya.mem_shadeFibre]
  refine and_congr_right fun his => ?_
  rw [slabwiseRestrictShading_eq_of_mem_assigned Ydom repr slabOf G hG s₁ S his]
  exact ⟨fun h => h.1, fun h => ⟨h, hxi₀.2⟩⟩

/-! ### The two-sided predicates on the assigned family -/

/-- **Typical plank angle on the assigned family.**  The two-sided predicate is not monotone under
deletion, so it is re-derived from the assigned-family fibre retention at the absolute rate
`Nov⁻¹`; the price is paid entirely in the reserve stability scale `Nov · A`. -/
theorem isTypicalPlankAngle_assignedSlabFamily {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (s₁ : Finset ι) (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
    {Nov : ℕ} (hNov : 1 ≤ Nov) (S : Slab θ hθ1) (C A : ℝ≥0) (hA : 1 ≤ A)
    (hret : ∀ x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade,
      ((Nov : ℝ))⁻¹ * ((Kakeya.shadeFibre s₁ Ydom x).card : ℝ)
        ≤ ((Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x).card : ℝ))
    (hstab : ∀ x ∈ ⋃ i ∈ s₁, (Ydom i).shade, ∀ t ⊆ Kakeya.shadeFibre s₁ Ydom x,
      (((Nov : ℝ≥0) * A : ℝ≥0) : ℝ)⁻¹ * ((Kakeya.shadeFibre s₁ Ydom x).card : ℝ) ≤ (t.card : ℝ) →
        θ ≤ C * Kakeya.maxPlankAngle P t ∧ Kakeya.maxPlankAngle P t ≤ C * θ) :
    Kakeya.IsTypicalPlankAngle (assignedSlabFamily s₁ repr slabOf S) Ydom P θ C A := by
  refine isTypicalPlankAngle_of_fibreRetention s₁ (assignedSlabFamily s₁ repr slabOf S)
    (assignedSlabFamily_subset s₁ repr slabOf S) Ydom Ydom P θ C A ((Nov : ℝ≥0) * A)
    ((Nov : ℝ))⁻¹ hA ?_ (fun i _ => subset_rfl) hret hstab
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (by exact_mod_cast hNov : (0 : ℝ) < (Nov : ℝ))),
    one_mul]

/-- **Constant multiplicity on the assigned family**, at the absolute cost `Nov`. -/
theorem hasCConstantMultiplicity_assignedSlabFamily
    (s₁ : Finset ι) (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {τ' : Type*} (repr : ι → τ') {θ : ℝ≥0} {hθ1 : θ ≤ 1} (slabOf : τ' → Slab θ hθ1)
    {Nov : ℕ} (hNov : 1 ≤ Nov) (S : Slab θ hθ1) {C C' : ℝ≥0}
    (hC : ShadedBody.HasCConstantMultiplicity s₁ Ydom C)
    (hscale : C ≤ ((Nov : ℝ≥0))⁻¹ * C')
    (hret : ∀ x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade,
      ((Nov : ℝ))⁻¹ * ((Kakeya.shadeFibre s₁ Ydom x).card : ℝ)
        ≤ ((Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x).card : ℝ)) :
    ShadedBody.HasCConstantMultiplicity (assignedSlabFamily s₁ repr slabOf S) Ydom C' := by
  refine hasCConstantMultiplicity_of_fibreRetention_real
    (inv_pos.mpr (Nat.cast_pos.mpr hNov)) hC (fun x i hi => ?_) (fun x hx => ?_) hscale
  · rw [Kakeya.mem_shadeFibre] at hi ⊢
    exact ⟨assignedSlabFamily_subset s₁ repr slabOf S hi.1, hi.2⟩
  · rw [NNReal.coe_inv]
    exact hret x hx

/-! ### Rewriting the slabwise shading on one assigned family -/

/-- A `c`-refinement only sees the refining family on its own index set, so it may be rewritten
along a pointwise identity there.  This is the bridge from the slab-local common restriction to the
global slabwise shading. -/
theorem isCRefinement_congr_left {s' s : Finset ι}
    {V' W' V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {c : ℝ≥0}
    (h : ∀ i ∈ s', V' i = W' i)
    (hR : ShadedBody.IsCRefinement s' V' s V c) :
    ShadedBody.IsCRefinement s' W' s V c :=
  ⟨⟨hR.1.1, fun i hi => h i hi ▸ hR.1.2 i hi⟩,
    hR.2.trans (Finset.sum_congr rfl fun i hi => by rw [h i hi]).le⟩

/-- The slab-local restricted union sits inside the global slabwise union. -/
theorem biUnion_restrictShade_subset_slabwise {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
    (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (hG : ∀ S, MeasurableSet (G S))
    (s₁ : Finset ι) (S : Slab θ hθ1) :
    (⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (ShadedBody.restrictShade (Ydom i) (G S) (hG
        S)).shade)
      ⊆ ⋃ i ∈ s₁, (slabwiseRestrictShading Ydom repr slabOf G hG i).shade := by
  refine Set.iUnion₂_subset fun i hi => ?_
  rw [← slabwiseRestrictShading_eq_of_mem_assigned Ydom repr slabOf G hG s₁ S hi]
  exact fun y hy => Set.mem_iUnion₂.mpr ⟨i, assignedSlabFamily_subset s₁ repr slabOf S hi, hy⟩

end Plank

namespace Kakeya

/-- **A measurable set chosen on a finite index subfamily extends to a measurable family on all
indices.**  Off `𝒮` the choice is `Set.univ`, which is measurable, so the extended family
carries an
unconditional measurability proof while still satisfying `Q` on `𝒮`.  The predicate `Q` is allowed
to mention the measurability proof, so the *same* proof term is available in the conclusion. -/
private lemma exists_measurableFamily_of_mem {σ X : Type*} [MeasurableSpace X] {𝒮 : Finset σ}
    {Q : σ → ∀ G : Set X, MeasurableSet G → Prop}
    (h : ∀ S ∈ 𝒮, ∃ (G : Set X) (hG : MeasurableSet G), Q S G hG) :
    ∃ (G : σ → Set X) (hG : ∀ S, MeasurableSet (G S)), ∀ S ∈ 𝒮, Q S (G S) (hG S) := by
  -- (extracted by Fuse golfer)
  classical
  have h' : ∀ S : σ, ∃ (G : Set X) (hG : MeasurableSet G), S ∈ 𝒮 → Q S G hG := fun S =>
    if hS : S ∈ 𝒮 then
      let ⟨G, hG, hQ⟩ := h S hS; ⟨G, hG, fun _ => hQ⟩
    else ⟨Set.univ, MeasurableSet.univ, fun hS' => absurd hS' hS⟩
  choose G hG hQ using h'
  exact ⟨G, hG, hQ⟩

/-- **Item 1 of GWZ Lemma 6.13, run slabwise, with the angular inputs supplied per assigned slab.**

Identical to `Kakeya.slabwiseDensity` except that the two-sided typical-angle predicate and the
constant multiplicity are taken *already on each assigned family* rather than on `(s₁, Ydom)` with a
retention transport performed inside.  That transport is what forced the caller to hold the source
predicate at a reserve stability scale of order `Nov ^ 2`: the pipeline pays one `Nov` going from
`(s', Y')` to `(s₁, Ydom)`, and this theorem's predecessor charged a second one going on to
`𝒜 S`.  The direct retention `Plank.dominantGoodSlab_assigned_fibre_retention_source` measures the
assigned fibre against the *uncut* `(s', Y')` fibre, so the caller can produce these hypotheses with
a single application of `Plank.isTypicalPlankAngle_of_fibreRetention` at `q = Nov⁻¹` and hence a
single factor of `Nov`.

`Nov` therefore does not occur here at all.  Everything else — the uniform `c1`, `cRef0` chosen
before the slab binder, the retained sets `G S`, the local refinement coefficient
`cRef0 · a ^ (εwork / 4)` and the global Item 1 conclusion — is unchanged. -/
theorem slabwiseDensity_assigned
    (Cθ Cset Cang Cmult cLamPre : ℝ≥0)
    (hCθ : 1 ≤ Cθ) (hCset : 1 ≤ Cset) (hCang : 1 ≤ Cang)
    (hCmult : 0 < Cmult) (hcLamPre : 0 < cLamPre)
    (Novpt : ℕ) (hNovpt : 1 ≤ Novpt)
    {η εwork : ℝ} (hη : 0 < η) (hεwork : 0 < εwork)
    (hbudget : 3 * (η + 5 * εwork / 4) ≤ 4 * η + εwork) :
    ∃ c1 cRef0 : ℝ≥0, 0 < c1 ∧ 0 < cRef0 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι τ : Type*}
        (s₁ : Finset ι) (P : ι → Plank a b hab hb1)
        (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
        (𝒮 : Finset (Slab θ hθ1)) (A : ℝ≥0),
        0 < a → a < 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ → 2 ≤ A →
        (∀ i ∈ s₁, slabOf (repr i) ∈ 𝒮) →
        (∀ i ∈ s₁, i ∈ Plank.inSlabFamilyC Cset Cang s₁ P (slabOf (repr i))) →
        (∀ i ∈ s₁, (Ydom i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s₁, ((Ydom i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        HasMaxPlankAngleBound s₁ Ydom P θ Cθ →
        (∀ S ∈ 𝒮, IsTypicalPlankAngle (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom P θ
          (Cθ * a ^ (-(εwork / 4))) A) →
        (∀ S ∈ 𝒮, cLamPre * a ^ (η + εwork)
          ≤ ShadedBody.fullness (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom) →
        (∀ S ∈ 𝒮, ShadedBody.HasCConstantMultiplicity
          (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom (Cmult * a ^ (-(εwork / 4)))) →
        ∃ (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S)),
          (∀ S ∈ 𝒮,
            ShadedBody.IsCRefinement
              (Plank.assignedSlabFamily s₁ repr slabOf S)
              (Plank.slabwiseRestrictShading Ydom repr slabOf G hG)
              (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom
              (cRef0 * a ^ (εwork / 4))) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3),
            ((⋃ i ∈ s₁, (Plank.slabwiseRestrictShading Ydom repr slabOf G hG i).shade) ∩
              Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
              ((c1 * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
                  volume (Metric.closedBall x ((θ * b : ℝ≥0) : ℝ))
                ≤ volume
                    ((⋃ i ∈ s₁,
                        (Plank.slabwiseRestrictShading Ydom repr slabOf G hG i).shade) ∩
                      Metric.closedBall x
                        ((plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ)))) := by
  classical
  obtain ⟨c1, cRef0, hc1, hcRef0, hitem⟩ :=
    Kakeya.slabwiseDensity_of_outputs Cθ Cset Cang Cmult cLamPre hCθ hCset hCang
      hCmult hcLamPre Novpt hNovpt hη hεwork hbudget
  refine ⟨c1, cRef0, hc1, hcRef0, ?_⟩
  intro a b θ hab hb1 hθ1 ι τ s₁ P Ydom repr slabOf 𝒮 A
    ha ha1 hb hθ hb1' hdivb hA h𝒮 hslab hshV hcarEq hmax htypS hfullS hmultS
  obtain ⟨G, hG, hGspec⟩ := exists_measurableFamily_of_mem (𝒮 := 𝒮) fun S hS =>
    hitem (Plank.assignedSlabFamily s₁ repr slabOf S) P Ydom
      ({S} : Finset (Slab θ hθ1)) A ha ha1 hb hθ hb1' hdivb hA
      (Set.Subsingleton.pairwise (by simp) _)
      (fun i hi => ⟨S, Finset.mem_singleton_self S,
        Plank.mem_inSlabFamilyC_assignedSlabFamily Cset Cang s₁ P repr slabOf S hslab i hi⟩)
      (fun _ => le_trans (le_trans (Finset.card_filter_le _ _) (Finset.card_singleton S).le) hNovpt)
      (fun i hi => hshV i (Plank.assignedSlabFamily_subset s₁ repr slabOf S hi))
      (fun i hi => hcarEq i (Plank.assignedSlabFamily_subset s₁ repr slabOf S hi))
      (Kakeya.HasMaxPlankAngleBound.mono (Plank.assignedSlabFamily_subset s₁ repr slabOf S)
        (fun i _ => subset_rfl) hmax)
      (htypS S hS) (hfullS S hS) (hmultS S hS)
  refine ⟨G, hG, ?_, ?_⟩
  · exact fun S hS => Plank.isCRefinement_congr_left
      (fun i hi =>
        (Plank.slabwiseRestrictShading_eq_of_mem_assigned Ydom repr slabOf G hG s₁ S hi).symm)
      (hGspec S hS).1
  · rintro x ⟨y, hy, hyball⟩
    obtain ⟨i₀, hi₀, hyi₀⟩ := Set.mem_iUnion₂.mp hy
    have hi₀AS : i₀ ∈ Plank.assignedSlabFamily s₁ repr slabOf (slabOf (repr i₀)) :=
      Plank.mem_assignedSlabFamily_self hi₀
    rw [Plank.slabwiseRestrictShading_eq_of_mem_assigned Ydom repr slabOf G hG s₁ _ hi₀AS] at hyi₀
    exact le_trans ((hGspec _ (h𝒮 i₀ hi₀)).2 x
        ⟨y, Set.mem_iUnion₂.mpr ⟨i₀, hi₀AS, hyi₀⟩, hyball⟩)
      (measure_mono (Set.inter_subset_inter_left _
        (Plank.biUnion_restrictShade_subset_slabwise Ydom repr slabOf G hG s₁ _)))

/-- **Item 1 of GWZ Lemma 6.13, run slabwise on the assigned families.**

The two constants `c1`, `cRef0` are obtained from `Kakeya.slabwiseDensity_of_outputs` *before*
the configuration and hence before the slab binder, so they are uniform in `S`.  Only the retained
set `G S` depends on the slab.

The output is the slabwise shading `Plank.slabwiseRestrictShading Ydom repr slabOf G hG`, together
with the slab-local refinements at `cRef0 · a ^ (εwork / 4)` and the *global* Item 1 density on
`s₁`, at the unchanged outer dilation `Kakeya.plankReduction.ballDilation`.

The local refinements are deliberately not summed to a global one; that is a separate ledger
step. -/
theorem slabwiseDensity
    (Cθ Cset Cang Cmult cLamPre : ℝ≥0)
    (hCθ : 1 ≤ Cθ) (hCset : 1 ≤ Cset) (hCang : 1 ≤ Cang)
    (hCmult : 0 < Cmult) (hcLamPre : 0 < cLamPre)
    (Novpt : ℕ) (hNovpt : 1 ≤ Novpt)
    {η εwork : ℝ} (hη : 0 < η) (hεwork : 0 < εwork)
    (hbudget : 3 * (η + 5 * εwork / 4) ≤ 4 * η + εwork) :
    ∃ c1 cRef0 : ℝ≥0, 0 < c1 ∧ 0 < cRef0 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι τ : Type*}
        (s₁ : Finset ι) (P : ι → Plank a b hab hb1)
        (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
        (𝒮 : Finset (Slab θ hθ1)) (A Cmult₀ : ℝ≥0) (Nov : ℕ),
        0 < a → a < 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ → 2 ≤ A → 1 ≤ Nov →
        (∀ i ∈ s₁, slabOf (repr i) ∈ 𝒮) →
        (∀ i ∈ s₁, i ∈ Plank.inSlabFamilyC Cset Cang s₁ P (slabOf (repr i))) →
        (∀ i ∈ s₁, (Ydom i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s₁, ((Ydom i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        HasMaxPlankAngleBound s₁ Ydom P θ Cθ →
        (∀ x ∈ ⋃ i ∈ s₁, (Ydom i).shade, ∀ t ⊆ Kakeya.shadeFibre s₁ Ydom x,
          (((Nov : ℝ≥0) * A : ℝ≥0) : ℝ)⁻¹ * ((Kakeya.shadeFibre s₁ Ydom x).card : ℝ)
              ≤ (t.card : ℝ) →
            θ ≤ (Cθ * a ^ (-(εwork / 4))) * Kakeya.maxPlankAngle P t ∧
              Kakeya.maxPlankAngle P t ≤ (Cθ * a ^ (-(εwork / 4))) * θ) →
        (∀ S ∈ 𝒮, cLamPre * a ^ (η + εwork)
          ≤ ShadedBody.fullness (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom) →
        ShadedBody.HasCConstantMultiplicity s₁ Ydom Cmult₀ →
        Cmult₀ ≤ ((Nov : ℝ≥0))⁻¹ * (Cmult * a ^ (-(εwork / 4))) →
        (∀ S : Slab θ hθ1,
          ∀ x ∈ ⋃ i ∈ Plank.assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade,
            ((Nov : ℝ))⁻¹ * ((Kakeya.shadeFibre s₁ Ydom x).card : ℝ)
              ≤ ((Kakeya.shadeFibre (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom x).card
                  : ℝ)) →
        ∃ (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S)),
          (∀ S ∈ 𝒮,
            ShadedBody.IsCRefinement
              (Plank.assignedSlabFamily s₁ repr slabOf S)
              (Plank.slabwiseRestrictShading Ydom repr slabOf G hG)
              (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom
              (cRef0 * a ^ (εwork / 4))) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3),
            ((⋃ i ∈ s₁, (Plank.slabwiseRestrictShading Ydom repr slabOf G hG i).shade) ∩
              Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
              ((c1 * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
                  volume (Metric.closedBall x ((θ * b : ℝ≥0) : ℝ))
                ≤ volume
                    ((⋃ i ∈ s₁,
                        (Plank.slabwiseRestrictShading Ydom repr slabOf G hG i).shade) ∩
                      Metric.closedBall x
                        ((plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ)))) := by
  obtain ⟨c1, cRef0, hc1, hcRef0, hmain⟩ :=
    slabwiseDensity_assigned Cθ Cset Cang Cmult cLamPre hCθ hCset hCang hCmult hcLamPre
      Novpt hNovpt hη hεwork hbudget
  refine ⟨c1, cRef0, hc1, hcRef0, ?_⟩
  intro a b θ hab hb1 hθ1 ι τ s₁ P Ydom repr slabOf 𝒮 A Cmult₀ Nov
    ha ha1 hb hθ hb1' hdivb hA hNov h𝒮 hslab hshV hcarEq hmax hstab hfullS hmultGlob
    hCmultScale hret
  have hA1 : (1 : ℝ≥0) ≤ A := le_trans (by norm_num) hA
  exact hmain s₁ P Ydom repr slabOf 𝒮 A ha ha1 hb hθ hb1' hdivb hA h𝒮 hslab hshV hcarEq hmax
    (fun S _ => Plank.isTypicalPlankAngle_assignedSlabFamily s₁ Ydom P repr slabOf hNov S
      (Cθ * a ^ (-(εwork / 4))) A hA1 (hret S) hstab)
    hfullS
    (fun S _ => Plank.hasCConstantMultiplicity_assignedSlabFamily s₁ Ydom repr slabOf hNov S
      hmultGlob hCmultScale (hret S))

end Kakeya

/-!
## Aggregating the slabwise refinements, and the local fullness of the slabwise shading

`Kakeya.slabwiseDensity` returns one refinement per active slab,

`ShadedBody.IsCRefinement (𝒜 S) Yfin (𝒜 S) Ydom rBall`,   `rBall = cRef0 · a ^ (εwork / 4)`,

where `𝒜 S = Plank.assignedSlabFamily s₁ repr slabOf S`.  This section turns those into the two
things the final reduction needs.

*Aggregation.*  The assigned families partition the **index set** `s₁` —
`Plank.biUnion_assignedSlabFamily` together with `Plank.assignedSlabFamily_disjoint`, packaged as
`Plank.sum_volume_assignedSlabFamily_eq` — so the slab-local mass inequalities add up to a single
global one at the *same* coefficient `rBall`.  No spatial disjointness of slabs is used or needed:
the sums are over indices, not over regions.  Composing with the previously proved refinement of the
original family is then one `ShadedBody.IsCRefinement.trans`, and costs only the product
`rBall · rFinal`.

The index set is unchanged by all of this, so the public cardinality clause already proved for `s₁`
still applies verbatim: no second mass-to-count conversion happens here.

*Local fullness.*  `Plank.fullness_ge_of_isCRefinement` converts the slab-local refinement into a
fullness lower bound for `Yfin`, charging exactly the refinement coefficient.  Against the
dominant/good-slab bound `cGood · a ^ η` on `Ydom` this gives

`(cRef0 · cGood) · a ^ (η + εwork / 4) ≤ ShadedBody.fullness (𝒜 S) Yfin`,

with a constant independent of `S`.  The strong exponent `η + εwork / 4` is kept; nothing is
weakened to a public `a ^ η` or `a ^ (4η + ε)` here, and `εwork` stays symbolic.
-/

namespace Plank

variable {ι τ σ : Type*}

/-! ### Aggregating the slab-local refinements -/

/-- **Slab-local `c`-refinements add up to a global one, at the same coefficient.**

The assigned families partition the *index set* `s₁`, so both mass sums split slabwise and the
per-slab inequalities add.  Only `Plank.sum_volume_assignedSlabFamily_eq` is used; no spatial
disjointness of the slabs is required. -/
theorem isCRefinement_of_assignedSlabFamily_partition
    (s₁ : Finset ι) (Ydom Yfin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ) (c : ℝ≥0)
    (h𝒮 : ∀ i ∈ s₁, slabOf (repr i) ∈ 𝒮)
    (hloc : ∀ S ∈ 𝒮, ShadedBody.IsCRefinement
      (assignedSlabFamily s₁ repr slabOf S) Yfin
      (assignedSlabFamily s₁ repr slabOf S) Ydom c) :
    ShadedBody.IsCRefinement s₁ Yfin s₁ Ydom c := by
  refine ⟨⟨Finset.Subset.refl s₁, fun i hi =>
    (hloc (slabOf (repr i)) (h𝒮 i hi)).1.2 i (mem_assignedSlabFamily_self hi)⟩, ?_⟩
  rw [← sum_volume_assignedSlabFamily_eq s₁ Ydom repr slabOf 𝒮 h𝒮,
    ← sum_volume_assignedSlabFamily_eq s₁ Yfin repr slabOf 𝒮 h𝒮, Finset.mul_sum]
  exact Finset.sum_le_sum fun S hS => (hloc S hS).2

/-! ### The fullness of the slabwise shading on one assigned family -/

/-- **The slab-local fullness of `Yfin`.**  The refinement coefficient is charged once, against the
dominant/good-slab fullness of `Ydom`; the exponents add by `NNReal.rpow_add`.

The constant `cRef0 * cGood` does not depend on the slab. -/
theorem fullness_assignedSlabFamily_of_isCRefinement
    {a : ℝ≥0} {η εwork : ℝ} {cRef0 cGood : ℝ≥0} (ha : 0 < a)
    (s₁ : Finset ι) (Ydom Yfin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (S : σ)
    (hloc : ShadedBody.IsCRefinement
      (assignedSlabFamily s₁ repr slabOf S) Yfin
      (assignedSlabFamily s₁ repr slabOf S) Ydom (cRef0 * a ^ (εwork / 4)))
    (hfull : cGood * a ^ η
      ≤ ShadedBody.fullness (assignedSlabFamily s₁ repr slabOf S) Ydom) :
    (cRef0 * cGood) * a ^ (η + εwork / 4)
      ≤ ShadedBody.fullness (assignedSlabFamily s₁ repr slabOf S) Yfin := by
  refine le_trans (le_of_eq ?_)
    ((mul_le_mul_of_nonneg_left hfull zero_le).trans (fullness_ge_of_isCRefinement hloc))
  rw [NNReal.rpow_add ha.ne']
  ring

end Plank

namespace Kakeya

/-- **The slabwise Item 1 outputs, aggregated.**

From the per-slab refinements of `Kakeya.slabwiseDensity`, the previously proved refinement of the
original family, and the dominant/good-slab fullness of `Ydom`, this returns:

* the global refinement of `Ydom` by `Yfin` on `s₁`, at the same `rBall = cRef0 · a ^ (εwork / 4)`;
* its composition with `hrefDom`, at `rBall · rFinal`;
* positivity of the local fullness constant `cRef0 * cGood`, which is independent of the slab;
* the slab-local fullness of `Yfin` at the strong exponent `η + εwork / 4`.

The index set `s₁` is untouched, so the public cardinality clause already proved for it carries over
unchanged and no further mass-to-count conversion is performed. -/
theorem slabwiseDensity_aggregate
    {ι τ σ : Type*} {a : ℝ≥0} {η εwork : ℝ} {cRef0 cGood rFinal : ℝ≥0}
    (ha : 0 < a) (hcRef0 : 0 < cRef0) (hcGood : 0 < cGood)
    (s s₁ : Finset ι) (Y Ydom Yfin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s₁, slabOf (repr i) ∈ 𝒮)
    (hlocRef : ∀ S ∈ 𝒮, ShadedBody.IsCRefinement
      (Plank.assignedSlabFamily s₁ repr slabOf S) Yfin
      (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom (cRef0 * a ^ (εwork / 4)))
    (hrefDom : ShadedBody.IsCRefinement s₁ Ydom s Y rFinal)
    (hfullDom : ∀ S ∈ 𝒮, cGood * a ^ η
      ≤ ShadedBody.fullness (Plank.assignedSlabFamily s₁ repr slabOf S) Ydom) :
    ShadedBody.IsCRefinement s₁ Yfin s₁ Ydom (cRef0 * a ^ (εwork / 4)) ∧
      ShadedBody.IsCRefinement s₁ Yfin s Y ((cRef0 * a ^ (εwork / 4)) * rFinal) ∧
      0 < cRef0 * cGood ∧
      (∀ S ∈ 𝒮, (cRef0 * cGood) * a ^ (η + εwork / 4)
        ≤ ShadedBody.fullness (Plank.assignedSlabFamily s₁ repr slabOf S) Yfin) := by
  have hglob := Plank.isCRefinement_of_assignedSlabFamily_partition s₁ Ydom Yfin repr slabOf 𝒮
    (cRef0 * a ^ (εwork / 4)) h𝒮 hlocRef
  have hcomposed : ShadedBody.IsCRefinement s₁ Yfin s Y ((cRef0 * a ^ (εwork / 4)) * rFinal) := by
    simpa [mul_comm] using hglob.trans hrefDom
  exact ⟨hglob, hcomposed, mul_pos hcRef0 hcGood, fun S hS =>
    Plank.fullness_assignedSlabFamily_of_isCRefinement ha s₁ Ydom Yfin repr slabOf S
      (hlocRef S hS) (hfullDom S hS)⟩

end Kakeya

/-!
## Item 2 rerun on the slabwise shading, at one fixed slab

The slabwise Item 1 construction replaces `Ydom` by

`Yfin = Plank.slabwiseRestrictShading Ydom repr slabOf G hG`,

which on the assigned family `𝒜 S = Plank.assignedSlabFamily s₁ repr slabOf S` is the common
restriction by the single set `G S`.  This section reruns the C-linear Item 2 core there.

The two inputs of the cover route are rebuilt directly on `(𝒜 S, Yfin)` rather than
transported:

* **Angle concentration.**  `Plank.shadeFibre_assignedSlabFamily_slabwiseRestrictShading` says the
  `𝒜 S`-shade fibre of `Yfin` at a point of the local `Yfin` union *equals* that of `Ydom` —
  the cut
  is by one set and the point lies in it.  So the stability clause transfers with no loss at all,
  and `Kakeya.HasMaxPlankAngleBound.mono` supplies the one-sided bound.  Feeding both to
  `Plank.localAngleConcentration_of_saturated` gives hypothesis (5) for `(𝒜 S, Yfin)` directly.
* **Half-box capture.**  `Plank.hcap_of_fullness_assigned` is already generic in the shading, so it
  is rerun at `Yfin` against the slabwise local fullness
  `(cRef0 · cGood) · a ^ (η + εwork / 4) ≤ ShadedBody.fullness (𝒜 S) Yfin`
  proved in the aggregation section above.

Both are then handed to `Plank.representativeShading_of_capture` at
`Yd := Yfin` and `η := η₂ := η + εwork / 4`, so the conclusion is at

`c2 · a ^ (4 · η₂) = c2 · a ^ (4η + εwork)`,

which is *stronger* than the public `a ^ (4η) · a ^ ε` and is deliberately kept in that form here.
No value of `εwork` is chosen, and the output thickened shading is built from `Yfin`.
-/

namespace Plank

variable {ι τ : Type*}

/-! ### The stability clause transfers to the slabwise shading with no loss -/

/-- **The local stability clause survives the slabwise restriction.**

On `𝒜 S` the slabwise shading is the common restriction by `G S`, and a point of the local `Yfin`
union lies in `G S`; so the `𝒜 S`-shade fibre is literally unchanged
(`Plank.shadeFibre_assignedSlabFamily_slabwiseRestrictShading`) and the clause transfers at the
*same* scale `A`.  Nothing is spent. -/
private theorem localStability_assigned_slabwiseRestrict
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {hθ1 : θ ≤ 1}
    (s₁ : Finset ι) (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (V : ι → Plank a b hab hb1) (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
    (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S))
    (S : Slab θ hθ1) (K : ℝ≥0) (A : ℝ)
    (hstabDom : ∀ x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade,
      ∀ t ⊆ Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x,
        A⁻¹ * ((Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x).card : ℝ)
            ≤ (t.card : ℝ) →
          (θ : ℝ) / ((K : ℝ) * Kakeya.plankAngleScaleB a)
            ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) :
    ∀ x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S,
        (slabwiseRestrictShading Ydom repr slabOf G hG i).shade,
      ∀ t ⊆ Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S)
          (slabwiseRestrictShading Ydom repr slabOf G hG) x,
        A⁻¹ * ((Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S)
            (slabwiseRestrictShading Ydom repr slabOf G hG) x).card : ℝ) ≤ (t.card : ℝ) →
          (θ : ℝ) / ((K : ℝ) * Kakeya.plankAngleScaleB a)
            ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) := by
  intro x hx t ht hcard
  have hxDom : x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade := by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hi, restrictShade_shade_subset (Ydom i) _ (hG _) hxi⟩
  rw [shadeFibre_assignedSlabFamily_slabwiseRestrictShading Ydom repr slabOf G hG s₁ S hx]
    at ht hcard
  exact hstabDom x hxDom t ht hcard

/-! ### Angle concentration on the slabwise shading -/

/-- **Hypothesis (5) of the cover route, on `(𝒜 S, Yfin)`.**

Rebuilt directly, not transported: the one-sided bound by `Kakeya.HasMaxPlankAngleBound.mono`
and the stability clause by `Plank.localStability_assigned_slabwiseRestrict`, both fed to
`Plank.localAngleConcentration_of_saturated`.  The constant `Ceta` is chosen before the
configuration. -/
private theorem localAngleConcentration_assigned_slabwise
    (K Cang : ℝ≥0) (hK : 1 ≤ K) (hCang : 1 ≤ Cang) {η₂ : ℝ} (hη₂ : 0 < η₂) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι τ σ : Type*}
        (s₁ : Finset ι) (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (V : ι → Plank a b hab hb1) (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
        (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S))
        (S : Slab θ hθ1)
        (𝒯' : Finset σ) (D : σ → Finset (Fin 3 → ℤ))
        (R : σ → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
        (Tq : σ → (Fin 3 → ℤ) → Finset ι)
        (Z : σ → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (A : ℝ),
        0 < a → a < 1 → 0 < b → 0 < θ → 2 ≤ A →
        Kakeya.HasMaxPlankAngleBound s₁ Ydom V θ Cang →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, Tq u q ⊆ assignedSlabFamily s₁ repr slabOf S) →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ Tq u q,
          (Z u q i).shade
            = (slabwiseRestrictShading Ydom repr slabOf G hG i).shade ∩ R u q) →
        (∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          ∀ x ∈ (slabwiseRestrictShading Ydom repr slabOf G hG i).shade,
            x ∈ R u q → i ∈ Tq u q) →
        (∀ x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade,
          ∀ t ⊆ Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x,
            A⁻¹ * ((Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x).card : ℝ)
                ≤ (t.card : ℝ) →
              (θ : ℝ) / ((K : ℝ) * Kakeya.plankAngleScaleB a)
                ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) →
        LocalAngleConcentration V θ 𝒯' D Tq Z Ceta η₂ := by
  obtain ⟨Ceta, hCetapos, hmain⟩ :=
    localAngleConcentration_of_saturated_scaled K Cang hK hCang hη₂
  refine ⟨Ceta, hCetapos, ?_⟩
  intro a b θ hab hb1 hθ1 ι τ σ s₁ Ydom V repr slabOf G hG S 𝒯' D R Tq Z A
    ha ha1 hb hθ hA hmax hTs hZeq hsat hstabDom
  exact hmain (assignedSlabFamily s₁ repr slabOf S) V
    (slabwiseRestrictShading Ydom repr slabOf G hG) 𝒯' D R Tq Z A ha ha1 hb hθ hθ1 hA
    (hmax.mono (assignedSlabFamily_subset s₁ repr slabOf S)
      fun i _ => restrictShade_shade_subset (Ydom i) _ (hG _))
    hTs hZeq hsat
    (localStability_assigned_slabwiseRestrict s₁ Ydom V repr slabOf G hG S K A hstabDom)

end Plank

namespace Kakeya

open Plank in
open scoped Classical in
/-- **Item 2 rerun on the slabwise shading, at one fixed slab.**

The angle concentration and the half-box capture are rebuilt on `(𝒜 S, Yfin)` and handed to
`Plank.representativeShading_of_capture` at `Yd := Yfin`.

The capture constant is `cGood₂ = cRef0 * cGood / (8 * cStb)`, chosen so that
`8 * cGood₂ * cStb = cRef0 * cGood` exactly; no power of `a` is spent on it.

The exponent is the C-linear `4 * η₂` at `η₂ = η + εwork / 4`, i.e. `4 * η + εwork` — stronger than
the public `a ^ (4η) * a ^ ε`, and deliberately not weakened here. -/
private theorem slabwiseShading_fixedSlab
    (cTan cGood cStb Cang Cset Cc ρ cRef0 : ℝ≥0)
    (hcTan : 1 ≤ cTan) (hcGood : 0 < cGood) (hcStb : 0 < cStb)
    (hCang : 1 ≤ Cang) (hCset : 1 ≤ Cset) (hCc : 1 ≤ Cc) (hρ : 0 < ρ)
    (hcRef0 : 0 < cRef0)
    {η εwork : ℝ} (hη : 0 < η) (hεwork : 0 < εwork) :
    ∃ c2 : ℝ≥0, 0 < c2 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθb : θ * b ≤ b} {hθ1 : θ ≤ 1}
        {ι τ : Type*}
        (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
        (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
        (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S))
        (S : Slab θ hθ1)
        (Pr : τ → Prism3D (θ * b) b 1 hθb hb1)
        (Yθfin : τ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (Zof : (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (A : ℝ) (L W : ℝ≥0),
        0 < a → a < 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ → 2 ≤ A →
        0 < L → 0 < W → ρ * W ≤ L →
        (assignedSlabFamily s₁ repr slabOf S).Nonempty →
        -- the local families, for every shift.  As with `htan`, only the planks of the assigned
        -- family are ever used, and only for them is the carrier of the input shading known to be
        -- the plank's own carrier
        (∀ sh q, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S, (Zof sh q i).shade
          = (slabwiseRestrictShading Ydom repr slabOf G hG i).shade ∩ halfSlabBox S b sh q) →
        (∀ sh q, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (Zof sh q i).carrier = (V i).carrier) →
        -- angular inputs, on the whole index set and on the assigned family
        Kakeya.HasMaxPlankAngleBound s₁ Ydom V θ Cang →
        (∀ x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade,
          ∀ t ⊆ Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x,
            A⁻¹ * ((Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x).card : ℝ)
                ≤ (t.card : ℝ) →
              (θ : ℝ) / (2 * Kakeya.plankAngleScaleB a)
                ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) →
        -- the slab-local geometry, on the assigned family
        (∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          i ∈ inSlabFamilyC Cset Cang (assignedSlabFamily s₁ repr slabOf S) V S) →
        (∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (slabwiseRestrictShading Ydom repr slabOf G hG i).shade
            ⊆ (((Pr (repr i)).toPrismNDim.dilation Cc).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (slabwiseRestrictShading Ydom repr slabOf G hG i).shade
            ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          8 * (a : ENNReal) * (b : ENNReal)
            ≤ volume (slabwiseRestrictShading Ydom repr slabOf G hG i).carrier) →
        -- tangentiality, only for the planks that actually meet the middle half of the box: for a
        -- distant lattice index the intersection is empty and the comparability is false, so the
        -- half-box filter is exactly the family the generic core consumes
        (∀ sh q, ∀ i ∈ (assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => ((slabwiseRestrictShading Ydom repr slabOf G hG i).shade ∩
              halfSlabBox S b sh q).Nonempty),
          Kakeya.ComparableScalars cTan
            (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
              (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          Prism3D.angle (Pr u) S ≤ (Cang : ℝ) * (θ : ℝ)) →
        -- fibre-size bounds, inherited verbatim from the preassembly
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          L ≤ ((((assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => repr i = u)).card : ℕ) : ℝ≥0)) →
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          ((((assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => repr i = u)).card : ℕ) : ℝ≥0) ≤ W) →
        -- the slabwise local fullness, at the strong exponent
        ((cRef0 * cGood) * a ^ (η + εwork / 4)
          ≤ ShadedBody.fullness (assignedSlabFamily s₁ repr slabOf S)
              (slabwiseRestrictShading Ydom repr slabOf G hG)) →
        -- the output thickened shading, built from `Yfin`
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          ((Yθfin u).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            = ((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier) →
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          (Yθfin u).shade
            = (⋃ i ∈ assignedSlabFamily s₁ repr slabOf S,
                (slabwiseRestrictShading Ydom repr slabOf G hG i).shade) ∩
              (((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) →
        c2 * a ^ (4 * η + εwork)
          ≤ ShadedBody.fullness ((assignedSlabFamily s₁ repr slabOf S).image repr) Yθfin := by
  have hη₂ : (0 : ℝ) < η + εwork / 4 := add_pos hη (div_pos hεwork four_pos)
  have h8 : (0 : ℝ≥0) < 8 * cStb := mul_pos (by norm_num) hcStb
  have h8c : 8 * (cRef0 * cGood / (8 * cStb)) * cStb = cRef0 * cGood := by
    rw [mul_comm (8 : ℝ≥0), mul_assoc, div_mul_cancel₀ _ h8.ne']
  obtain ⟨Ceta, hCetapos, hLACmain⟩ :=
    Plank.localAngleConcentration_assigned_slabwise 2 Cang one_le_two hCang hη₂
  obtain ⟨c2, hc2pos, hgen⟩ := Plank.representativeShading_of_capture
      cTan (cRef0 * cGood / (8 * cStb)) cStb Cang Cc Ceta ρ hcTan
      (div_pos (mul_pos hcRef0 hcGood) h8) hcStb hCang hCc hCetapos hρ hη₂
  refine ⟨c2, hc2pos, ?_⟩
  intro a b θ hab hb1 hθb hθ1 ι τ
       s₁ V Ydom repr slabOf G hG S Pr Yθfin Zof A L W
       ha ha1 hb hθ hb1b hθab hA hL hW hρLW hne
       hZsh hZcar hmax hstabDom
       hfam hsubPr hshV hcarvol htan hangPr
       hlow hup hfull hYcar hYsh
  obtain ⟨sh, -, hcap⟩ := Plank.hcap_of_fullness_assigned S Cset Cang
      (cRef0 * cGood * a ^ (η + εwork / 4)) (cRef0 * cGood / (8 * cStb)) cStb hCset
      (assignedSlabFamily s₁ repr slabOf S) V (slabwiseRestrictShading Ydom repr slabOf G hG)
      (η + εwork / 4) hθ hb hb1b hshV hfam hfull hcarvol (le_of_eq (by rw [h8c]))
  rw [show 4 * η + εwork = 4 * (η + εwork / 4) by ring]
  exact hgen s₁ V (slabwiseRestrictShading Ydom repr slabOf G hG) repr slabOf S sh
    (slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊) Pr Yθfin _ (Zof sh) L W
    ha hb hθ hθab hL hW hρLW hne (fun _ => Finset.filter_subset _ _)
    (fun q i hi => hZsh sh q i (Finset.filter_subset _ _ hi))
    (fun q i hi => hZcar sh q i (Finset.filter_subset _ _ hi))
    (fun D => hLACmain s₁ Ydom V repr slabOf G hG S _ D
      (fun _ q => halfSlabBox S b sh q) _ _ A ha ha1 hb hθ hA hmax
      (fun _ _ _ _ => Finset.filter_subset _ _)
      (fun _ _ q _ i hi => hZsh sh q i (Finset.filter_subset _ _ hi))
      (fun _ _ _ _ i hi x hx hxR => Finset.mem_filter.mpr ⟨hi, ⟨x, hx, hxR⟩⟩) hstabDom)
    hsubPr hshV (htan sh) hangPr hlow hup hcap hYcar hYsh

/-! ### The global slabwise Item 2 wrapper -/

/-- **The Item 2 exponent budget.**  The single place where Item 2's *strong* exponent is traded for
the declared public one.

The C-linear core proves the fullness at `c₂ · a ^ (4η + w)` for a working exponent `w > 0` that
the caller chooses (`w = εwork` slabwise, `w = 5 εwork` on the final family).  The declared Item 2
clause is `c₂ · a ^ (4η) · a ^ ε`, and since `a ≤ 1` the two differ only in the exponent: `w ≤ ε`
gives `a ^ (4η) · a ^ ε = a ^ (4η + ε) ≤ a ^ (4η + w)`.  So the whole exponent ledger of Item 2 is
the single condition `w ≤ ε`, no constant is spent, and the declared `4η` is untouched. -/
theorem representativeShading_exponent_budget {a c2 : ℝ≥0} {η ε εwork : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hεwork : εwork ≤ ε) :
    c2 * a ^ (4 * η) * a ^ ε ≤ c2 * a ^ (4 * η + εwork) := by
  rw [mul_assoc, ← NNReal.rpow_add ha.ne']
  exact mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith))
    zero_le

open Plank in
open scoped Classical in
/-- **The public Item 2 clauses on the slabwise shading, for every active slab.**

`c2` is obtained from `Kakeya.slabwiseShading_fixedSlab` *before* the slab binder, so one constant
serves every active slab; nothing here is chosen per slab.  The thickened shading
`Plank.sharedSlabThickenedShadingDilation (4 * Cang + 8 + Cc) s₁ Yfin anchor repr slabOf` is fixed
once and used for all of them, and the old `Ydom` does not occur in the output.

The exponent weakening is the only step here.  The fixed-slab theorem gives the strong
`c2 · a ^ (4η + εwork)`; since `a ≤ 1` and `εwork ≤ ε`,

`a ^ (4η) · a ^ ε = a ^ (4η + ε) ≤ a ^ (4η + εwork)`,

so the public `c2 · a ^ (4η) · a ^ ε` follows.  No new loss is introduced and `εwork` stays
symbolic: only `0 < εwork` and `εwork ≤ ε` are assumed.

Both exponents are returned, for the *same* `c2` and the same slab: the strong one first, then the
old public pair.  The final reduction needs both — the strong fullness feeds the multiplicity
bound through `Kakeya.exists_multiplicityCoefficient`, while the public one is the Item 2
clause of the statement —
and obtaining them from two separate existentials would produce two unrelated constants. -/
theorem slabwiseRepresentativeShading
    (cTan cGood cStb Cang Cset Cc ρ cRef0 : ℝ≥0)
    (hcTan : 1 ≤ cTan) (hcGood : 0 < cGood) (hcStb : 0 < cStb)
    (hCang : 1 ≤ Cang) (hCset : 1 ≤ Cset) (hCc : 1 ≤ Cc) (hρ : 0 < ρ)
    (hcRef0 : 0 < cRef0)
    {η εwork : ℝ} (hη : 0 < η) (hεwork : 0 < εwork) :
    ∃ c2 : ℝ≥0, 0 < c2 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθb : θ * b ≤ b} {hθ1 : θ ≤ 1}
        {ι τ : Type*} {ε : ℝ}
        (Cgeo : ℝ≥0)
        (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
        (Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (repr : ι → τ) (slabOf : τ → Slab θ hθ1)
        (G : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))) (hG : ∀ S, MeasurableSet (G S))
        (𝒮g : Finset (Slab θ hθ1))
        (Pr : τ → Prism3D (θ * b) b 1 hθb hb1)
        (anchor : τ → EnsemblePrism)
        (Zof : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (A : ℝ) (L W : ℝ≥0),
        0 < a → a ≤ 1 → a < 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ → 2 ≤ A →
        0 < L → 0 < W → ρ * W ≤ L →
        εwork ≤ ε →
        -- the anchor is the representative's own prism
        (∀ u ∈ s₁.image repr, anchor u = (Pr u).toPrismNDim) →
        -- global angular input
        Kakeya.HasMaxPlankAngleBound s₁ Ydom V θ Cang →
        -- per-slab data, on the assigned families
        (∀ S ∈ 𝒮g, (assignedSlabFamily s₁ repr slabOf S).Nonempty) →
        (∀ S ∈ 𝒮g, ∀ sh q, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S, (Zof S sh q i).shade
          = (slabwiseRestrictShading Ydom repr slabOf G hG i).shade ∩ halfSlabBox S b sh q) →
        (∀ S ∈ 𝒮g, ∀ sh q, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (Zof S sh q i).carrier = (V i).carrier) →
        (∀ S ∈ 𝒮g, ∀ x ∈ ⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Ydom i).shade,
          ∀ t ⊆ Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x,
            A⁻¹ * ((Kakeya.shadeFibre (assignedSlabFamily s₁ repr slabOf S) Ydom x).card : ℝ)
                ≤ (t.card : ℝ) →
              (θ : ℝ) / (2 * Kakeya.plankAngleScaleB a)
                ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) →
        (∀ S ∈ 𝒮g, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          i ∈ inSlabFamilyC Cset Cang (assignedSlabFamily s₁ repr slabOf S) V S) →
        (∀ S ∈ 𝒮g, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (slabwiseRestrictShading Ydom repr slabOf G hG i).shade
            ⊆ (((Pr (repr i)).toPrismNDim.dilation Cc).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ S ∈ 𝒮g, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (slabwiseRestrictShading Ydom repr slabOf G hG i).shade
            ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ S ∈ 𝒮g, ∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          8 * (a : ENNReal) * (b : ENNReal)
            ≤ volume (slabwiseRestrictShading Ydom repr slabOf G hG i).carrier) →
        -- tangentiality, only on the half-box-nonempty filtered family (see the fixed-slab theorem)
        (∀ S ∈ 𝒮g, ∀ sh q, ∀ i ∈ (assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => ((slabwiseRestrictShading Ydom repr slabOf G hG i).shade ∩
              halfSlabBox S b sh q).Nonempty),
          Kakeya.ComparableScalars cTan
            (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
              (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        (∀ S ∈ 𝒮g, ∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          Prism3D.angle (Pr u) S ≤ (Cang : ℝ) * (θ : ℝ)) →
        (∀ S ∈ 𝒮g, ∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          L ≤ ((((assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => repr i = u)).card : ℕ) : ℝ≥0)) →
        (∀ S ∈ 𝒮g, ∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          ((((assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => repr i = u)).card : ℕ) : ℝ≥0) ≤ W) →
        -- the slabwise local fullness, at the strong exponent
        (∀ S ∈ 𝒮g, (cRef0 * cGood) * a ^ (η + εwork / 4)
          ≤ ShadedBody.fullness (assignedSlabFamily s₁ repr slabOf S)
              (slabwiseRestrictShading Ydom repr slabOf G hG)) →
        -- the geometric family the containment lands in
        (∀ i ∈ s₁, i ∈ inSlabFamilyC Cset Cgeo s₁ V (slabOf (repr i))) →
        -- the Item 2 clauses, at the canonical fibre and the fixed slabwise shading.  The *strong*
        -- fullness comes first, for the same `c2`; the old public pair is the second component, so
        -- previous consumers project it with `.2`.
        ∀ S ∈ 𝒮g,
          c2 * a ^ (4 * η + εwork) ≤
            ShadedBody.fullness
              ((s₁.image repr).filter (fun Q => slabOf Q = S))
              (sharedSlabThickenedShadingDilation (4 * Cang + 8 + Cc) s₁
                (slabwiseRestrictShading Ydom repr slabOf G hG) anchor repr slabOf) ∧
          (c2 * a ^ (4 * η) * a ^ ε ≤
            ShadedBody.fullness
              ((s₁.image repr).filter (fun Q => slabOf Q = S))
              (sharedSlabThickenedShadingDilation (4 * Cang + 8 + Cc) s₁
                (slabwiseRestrictShading Ydom repr slabOf G hG) anchor repr slabOf) ∧
          ∀ Q ∈ (s₁.image repr).filter (fun Q => slabOf Q = S),
            (sharedSlabThickenedShadingDilation (4 * Cang + 8 + Cc) s₁
                (slabwiseRestrictShading Ydom repr slabOf G hG) anchor repr slabOf Q).shade
              ⊆ ⋃ i ∈ inSlabFamilyC Cset Cgeo s₁ V S,
                  (slabwiseRestrictShading Ydom repr slabOf G hG i).shade) := by
  obtain ⟨c2, hc2pos, hc2⟩ := slabwiseShading_fixedSlab cTan cGood cStb Cang Cset Cc ρ cRef0
    hcTan hcGood hcStb hCang hCset hCc hρ hcRef0 hη hεwork
  refine ⟨c2, hc2pos, ?_⟩
  intro a b θ hab hb1 hθb hθ1 ι τ ε Cgeo s₁ V Ydom repr slabOf G hG 𝒮g Pr anchor Zof A L W
    ha ha1' ha1 hb hθ hb1b habθ hA hL hW hρLW hεwork_le
    hanchor hmax hne hZsh hZcar hstabDom hfam hsubPr hshV hcarvol htan hangPr hlo hup hfull hgeo
    S hS
  let Yfin := sharedSlabThickenedShadingDilation (4 * Cang + 8 + Cc) s₁
      (slabwiseRestrictShading Ydom repr slabOf G hG) anchor repr slabOf
  have hanch : ∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
      anchor u = (Pr u).toPrismNDim := fun u hu =>
    hanchor u (Finset.image_subset_image (assignedSlabFamily_subset s₁ repr slabOf S) hu)
  have hcar : ∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
      ((Yfin u).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = ((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier := fun u hu => by
    rw [sharedSlabThickenedShadingDilation_carrier, hanch u hu]
  have hshadeY : ∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
      (Yfin u).shade
        = (⋃ i ∈ assignedSlabFamily s₁ repr slabOf S,
            (slabwiseRestrictShading Ydom repr slabOf G hG i).shade) ∩
          (((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    rw [sharedSlabThickenedShadingDilation_shade_assigned, hanch _ hu,
      (mem_assignedSlabFamily.mp hi).2]
    exact Set.inter_comm _ _
  have hkey := hc2 s₁ V Ydom repr slabOf G hG S Pr Yfin (Zof S) A L W
      ha ha1 hb hθ hb1b habθ hA hL hW hρLW
      (hne S hS) (hZsh S hS) (hZcar S hS) hmax (hstabDom S hS)
      (hfam S hS) (hsubPr S hS) (hshV S hS) (hcarvol S hS) (htan S hS) (hangPr S hS)
      (hlo S hS) (hup S hS) (hfull S hS) hcar hshadeY
  rw [image_repr_assignedSlabFamily] at hkey
  refine ⟨hkey, le_trans ?_ hkey, fun Q hQ => ?_⟩
  · exact representativeShading_exponent_budget ha ha1' hεwork_le
  · refine (sharedSlabThickenedShadingDilation_shade_subset_assigned _ s₁ _ anchor repr slabOf
      Q).trans ?_
    rw [(Finset.mem_filter.mp hQ).2]
    exact Set.biUnion_subset_biUnion_left
      (assignedSlabFamily_subset_inSlabFamilyC_of_mem Cset Cgeo s₁ V repr slabOf S hgeo)

end Kakeya

end

end

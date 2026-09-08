/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabSplit
public import Kakeya.DimensionThree.MainLemma2.PartitionBrackets

/-!
# The split/fibre chain retyped over `Tube.PartitionBrackets`

## Why a twin is needed at all, measured

The loose-hierarchy condition for `Kakeya.VeryNotSticky.SideDataObligations` to

```
∃ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
        edCoverDilateConstant cfg.C₀, <the angular clause over 𝒱>
```

and the clause is `Kakeya.VeryNotSticky.eventually_conjunct6_of_looseUniform`, stated over
`𝒱.tubeUniform.toPartitionBrackets`. Step 8 of
`Kakeya.VeryNotSticky.sideDataResidue_of_sideDataObligations` cannot consume it, because the
existing T8 producer `Kakeya.VeryNotSticky.eventually_exists_splitInputs_degenerate` wants the
same clause over `cfg.splitHierarchy` (`= cfg.uniform.some.tubeUniform`, an exact hierarchy).
That is the compiled obstruction recorded in 

A loose datum cannot supply an exact one: `Tube.GridCoverSystem.le_tube_assign` is the
**factor-1** containment `(T i).toConvexSpaceBody ≤ (tube k (assign k i)).toConvexSpaceBody`,
while `Kakeya.LooseUniform.LooseGridCoverSystem.le_dilate_tube_assign` gives only
`≤ Kakeya.Tube.dilate (tube k (assign k i)) K`, and
`Kakeya.LooseUniform.bush_obstruction` compiles that the gap is real. So the chain must be
retyped, not bridged.

## What the retype costs: nothing, because the geometry is never read

Measured on the existing proof of `Kakeya.VeryNotSticky.nonslabSplitBound`, the hierarchy is read
in exactly five places — `exists_full_fibre`, `uniform.cover.indexSet k`, `tubeFibre`,
`tubeFibre_subset`, and the two fields `fibreCount` / `angularFibre_le_fibreMult` — and none of
them touches a node's geometry. `Tube.PartitionBrackets` is precisely that part, and
`LooseUniform.lean` already carries the seven fibre lemmas over it
(`pbTubeFibre`, `pbActiveTubeNodes`, `pbTubeScaleCompare`, `pbNonslabFibrePartition`,
`pbCard_indexSet_mul_card_tubeFibre_le`, `pbOne_le_sq_of_mem_activeTubeNodes`,
`pbExists_full_fibre`). The other two consumers on 's list need no twin, and
this file records why by *not* having one: `Kakeya.VeryNotSticky.nonslabKKTPow` takes the node
count as a bare `N : ℕ` and the fibre as an arbitrary `sub : Finset cfg.ι`, and
`Kakeya.VeryNotSticky.nonslabPointwiseBound` takes the angular bound as an abstract
`{A : ENNReal}` — neither mentions a hierarchy, so both are applied below unchanged.

## Contents

* `Kakeya.VeryNotSticky.PBSplitInputs` — the twin of `Kakeya.VeryNotSticky.SplitInputs` with
  `uniform : Tube.PartitionBrackets cfg.s N Cu`. Field for field the existing text, with
  `cfg.tubeFibre uniform` → `cfg.pbTubeFibre uniform`,
  `cfg.activeTubeNodes uniform` → `cfg.pbActiveTubeNodes uniform` and
  `uniform.cover.indexSet` → `uniform.indexSet`.
* `Kakeya.VeryNotSticky.SplitInputs.toPB` — the existing structure instantiates the twin. This is
  the tripwire that the twin is a *generalisation* and not a different object: it is built by
  `Tube.UniformTubeSet.toPartitionBrackets` and every field is the existing field unchanged,
  because `Kakeya.VeryNotSticky.tubeFibre_eq_pbTubeFibre` and
  `activeTubeNodes_eq_pbActiveTubeNodes` are `rfl`.
* `Kakeya.VeryNotSticky.PBSplitInputs.ofLevel` — the twin of
  `Kakeya.VeryNotSticky.SplitInputs.ofLevel`.
* `Kakeya.VeryNotSticky.nonslabSplitBoundPB` — the twin of
  `Kakeya.VeryNotSticky.nonslabSplitBound`, and
  `Kakeya.VeryNotSticky.nonslabSplitBound_of_pb`, which **re-derives the existing statement from
  the twin**. Nothing downstream of `nonslabSplitBound` loses anything by the retype.
* `Kakeya.VeryNotSticky.eventually_exists_splitInputs_loose` — the T8 producer twin, with `𝒱`
  as a binder. The level `k` and the two `gridScale` bounds come from the existing
  `Kakeya.VeryNotSticky.exists_splitLevel`, `katzTao` from
  `Kakeya.VeryNotSticky.ktScaleData_of_ckt`, `fibreConstant` from
  `Kakeya.VeryNotSticky.fibreConstant_of_threshold` and `fibreCount` from
  `Kakeya.VeryNotSticky.pbCard_indexSet_mul_card_tubeFibre_le` — the same five inputs the
  existing producer uses, at the same two thresholds on `δ`.
* `Kakeya.VeryNotSticky.exists_pbSplitInputs_of_conjunct6` and its `∀ᶠ` form
  `eventually_exists_pbSplitInputs_of_conjunct6` — **the step-8 plug**: from conjunct 6 in
  E-L2's licensed `∃ 𝒱` shape, together with conjunct 5 retyped in lockstep, `Nonempty
  (PBSplitInputs cfg bd)`. The `𝒱` that the exact chain took by `Classical.choice` from
  `cfg.splitHierarchy` is here taken from the conjunct's own `∃`.
* `Kakeya.VeryNotSticky.conjunct5_loose_of_looseRhoParentData` — the plug's conjunct-5
  hypothesis **is** the existing loose discharge
  `Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_loose` at `Ks = 4`, so moving
  conjunct 5 in lockstep with conjunct 6 costs no new obligation and no new exponent
  (`M = 18` throughout).

## What is NOT here

No producer of `Kakeya.LooseUniform.LooseShadedUniformTubeSet` for a nonempty Section-9 family, and therefore no discharge of conjunct 6: everything
below is conditional on the datum.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace Kakeya.VeryNotSticky

universe u


/-! ### The twin structure -/

open scoped Classical in
/-- **`Kakeya.VeryNotSticky.SplitInputs` over `Tube.PartitionBrackets`**.

Field for field the existing text of `Kakeya.VeryNotSticky.SplitInputs`, with the three
vocabulary substitutions the abstraction forces and **no other change**: no field added, none
removed, no constant and no exponent moved. In particular `fibreConstant` still absorbs
`Cu²·(2 C_{lem:ml2bodyAngle}(bd.C₀))²` into `δ^{-η}`, `countConstant`
is still `δ^{-18η}` and `angularConstant` still `δ^{-η}`.

The existing structure instantiates this one (`Kakeya.VeryNotSticky.SplitInputs.toPB`); the loose datum instantiates it too, through
`Kakeya.LooseUniform.LooseUniformTubeSet.toPartitionBrackets`. That is the whole content of the
retype. -/
structure PBSplitInputs (cfg : VeryNotSticky.{u}) (bd : BallData cfg) where
  /-- the number of grid levels of the hierarchy -/
  N : ℕ
  /-- the uniformity constant of the hierarchy -/
  Cu : NNReal
  /-- item (iii): the class brackets of a partitioning hierarchy for `𝕋`. The exact hierarchy
  and the loose one both provide this, and nothing below reads more. -/
  uniform : Tube.PartitionBrackets cfg.s N Cu
  /-- the grid level sitting at the dilated angular scale `ρ₂*`, up to the grid rounding -/
  k : ℕ
  /-- that level is one of the `N` levels -/
  k_le : k ≤ N
  /-- the level at `ρ₂*` from below -/
  gridScale_ge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ N k
  /-- and from above with the grid rounding loss `δ^{-η}` -/
  gridScale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀
  /-- item (i): `K_KT(β)` at this `δ` with loss `ϱ` -/
  katzTao : cfg.KTScaleData cfg.ϱ
  /-- item (ii): the fixed-scale threshold of the hierarchy constant -/
  fibreConstant : ((Cu : ENNReal) ^ 2) *
      ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 ≤
    (cfg.δ : ENNReal) ^ (-cfg.η)
  /-- GWZ Def 2.1(iii) in the shape `Kakeya.VeryNotSticky.nonslabKKTPow` consumes, over the
  brackets. Derivable from `uniform` alone by
  `Kakeya.VeryNotSticky.pbCard_indexSet_mul_card_tubeFibre_le`, exactly as the existing field is
  derivable by `Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le`. -/
  fibreCount : ∀ j ∈ uniform.indexSet k,
    ((uniform.indexSet k).card : ℝ) * ((cfg.pbTubeFibre uniform k j).card : ℝ) ≤
      ((Cu : ℝ) ^ 2) * (cfg.s.card : ℝ)
  /-- the carried constant of the `ρ₂`-count clause -/
  Ccnt : NNReal
  /-- its fixed-scale threshold, at the measured exponent `18` -/
  countConstant : (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η))
  /-- the `ρ₂`-counting input of `Kakeya.VeryNotSticky.nonslabKKTPow`, its hypothesis `hcount` -/
  fibreScaleCount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
    (Ccnt : ℝ) * ((uniform.indexSet k).card : ℝ)
  /-- the constant hidden in GWZ's "`⪅ μ(ρ₂) ≈ μ(𝕋[T_{ρ₂}], Y)`" (`gwz.txt` l.2321-2322) -/
  Cang : NNReal
  /-- its fixed-scale threshold -/
  angularConstant : (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η)
  /-- **GWZ (100)-(101) composed**, over the brackets. In the loose model this is a *theorem*
  of GWZ Definition 2.1(ii)-(iii) and 2.2 —
  `Kakeya.VeryNotSticky.exists_Cang_angularFibre_le_of_looseUniform` — and in the exact model it
  is unreachable (`Kakeya.LooseUniform.bush_obstruction`). The two hierarchy models therefore provide different geometric information. -/
  angularFibre_le_fibreMult : ∀ j ∈ cfg.pbActiveTubeNodes uniform k,
    ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
        (Cang : ENNReal) *
          ShadedBody.multiplicity (cfg.pbTubeFibre uniform k j)
            (fun i ↦ (cfg.T i).toShadedBody)

/-! ### The existing structure is a special case -/

/-- **The existing `Kakeya.VeryNotSticky.SplitInputs` instantiates the twin**, by
`Tube.UniformTubeSet.toPartitionBrackets`. Every field is transported *unchanged* — the proofs
are literally the existing projections — because
`Kakeya.VeryNotSticky.tubeFibre_eq_pbTubeFibre` and
`Kakeya.VeryNotSticky.activeTubeNodes_eq_pbActiveTubeNodes` are `rfl` and
`Tube.UniformTubeSet.toPartitionBrackets_indexSet` is `rfl`.

This is the tripwire for the retype: if `PBSplitInputs` ever asks for something the exact model
does not have, this declaration stops elaborating. -/
noncomputable def SplitInputs.toPB {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (si : SplitInputs cfg bd) :
    PBSplitInputs cfg bd where
  N := si.N
  Cu := si.Cu
  uniform := si.uniform.toPartitionBrackets
  k := si.k
  k_le := si.k_le
  gridScale_ge := si.gridScale_ge
  gridScale_le := si.gridScale_le
  katzTao := si.katzTao
  fibreConstant := si.fibreConstant
  fibreCount := si.fibreCount
  Ccnt := si.Ccnt
  countConstant := si.countConstant
  fibreScaleCount := si.fibreScaleCount
  Cang := si.Cang
  angularConstant := si.angularConstant
  angularFibre_le_fibreMult := si.angularFibre_le_fibreMult

/-! ### The twin of `SplitInputs.ofLevel` -/

/-- **`PBSplitInputs` from a level of a bracket hierarchy and the remaining clauses.** The twin
of `Kakeya.VeryNotSticky.SplitInputs.ofLevel`, binder for binder, with `fibreCount` discharged
by `Kakeya.VeryNotSticky.pbCard_indexSet_mul_card_tubeFibre_le` where the existing one uses
`Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le`. -/
def PBSplitInputs.ofLevel (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {N : ℕ} {Cu : NNReal}
    (uniform : Tube.PartitionBrackets cfg.s N Cu) {k : ℕ}
    (k_le : k ≤ N)
    (gridScale_ge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ N k)
    (gridScale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀)
    (katzTao : cfg.KTScaleData cfg.ϱ)
    (fibreConstant : ((Cu : ENNReal) ^ 2) *
        ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η))
    (Cang : NNReal)
    (angularConstant : (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    (angularFibre_le_fibreMult : ∀ j ∈ cfg.pbActiveTubeNodes uniform k,
      ∀ x v : EuclideanSpace ℝ (Fin 3),
        (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
          (Cang : ENNReal) *
            ShadedBody.multiplicity (cfg.pbTubeFibre uniform k j)
              (fun i ↦ (cfg.T i).toShadedBody))
    (Ccnt : NNReal)
    (countConstant : (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)))
    (fibreScaleCount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      (Ccnt : ℝ) * ((uniform.indexSet k).card : ℝ)) :
    PBSplitInputs cfg bd where
  N := N
  Cu := Cu
  uniform := uniform
  k := k
  k_le := k_le
  gridScale_ge := gridScale_ge
  gridScale_le := gridScale_le
  katzTao := katzTao
  fibreConstant := fibreConstant
  fibreCount := cfg.pbCard_indexSet_mul_card_tubeFibre_le uniform k k_le
  Ccnt := Ccnt
  countConstant := countConstant
  fibreScaleCount := fibreScaleCount
  Cang := Cang
  angularConstant := angularConstant
  angularFibre_le_fibreMult := angularFibre_le_fibreMult

/-! ### The split bound over the brackets -/

/-- **`Kakeya.VeryNotSticky.nonslabSplitBound` over `Tube.PartitionBrackets`.** The existing
statement and the existing proof, with `si : cfg.SplitInputs bd` replaced by
`si : cfg.PBSplitInputs bd` and the four hierarchy reads replaced by their bracket twins:

| existing | here |
|---|---|
| `Kakeya.VeryNotSticky.exists_full_fibre` | `Kakeya.VeryNotSticky.pbExists_full_fibre` |
| `si.uniform.cover.indexSet si.k` | `si.uniform.indexSet si.k` |
| `cfg.tubeFibre si.uniform si.k j` | `cfg.pbTubeFibre si.uniform si.k j` |
| `cfg.tubeFibre_subset` | `cfg.pbTubeFibre_subset` |

Everything else is byte-identical, and in particular the two consumers  lists
as needing no twin are applied **unchanged**: `Kakeya.VeryNotSticky.nonslabKKTPow` at the bare
node count `((si.uniform.indexSet si.k).card)` and the arbitrary subfamily `F`, and
`Kakeya.VeryNotSticky.nonslabPointwiseBound` at the abstract `A := si.Cang * mF`. The conclusion
is the existing conclusion, symbol for symbol; no constant and no exponent moves. -/
theorem nonslabSplitBoundPB (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (hβ1 : cfg.β ≤ 1)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ B' (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (si : PBSplitInputs cfg bd) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4)) *
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W *
        (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β := by
  classical
  -- STEP 0: angular range
  have hnots : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := cfg.b_le_pow_mul_r₁ hnotslab
  have hrange := cfg.rho2Star_range cfg.hδ cfg.hδ1 bd.hC₀ scale.rho2Star_le_one hnots
  have hle12 : cfg.rho2 ≤ 2 * cfg.rho2 := by
    simpa using (mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) ≤ 2) (by exact zero_le))
  have hδρNN : cfg.δ ≤ cfg.rho2Star bd.C₀ :=
    le_trans (le_trans hrange.1 hle12) hrange.2.1
  have hδρ : (cfg.δ : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ) := by exact_mod_cast hδρNN
  have hρ1 : (cfg.rho2Star bd.C₀ : ℝ) ≤ 1 := by exact_mod_cast hrange.2.2
  -- STEP 1: full fibre
  have hs : cfg.s.Nonempty := by
    by_contra hne
    have hcard0 : (cfg.s.card : ENNReal) = 0 := by
      have he : cfg.s = ∅ := by
        apply Finset.ext
        intro i
        constructor
        · intro hi
          exact False.elim (hne ⟨i, hi⟩)
        · simp
      simp [he]
    have hbad : (1 : ENNReal) ≤ 0 := by
      calc
        (1 : ENNReal) ≤ (cfg.δ : ENNReal) * (cfg.s.card : ENNReal) := cfg.tube_count
        _ = 0 := by simp [hcard0]
    exact (by norm_num : ¬ (1 : ENNReal) ≤ 0) hbad
  rcases Kakeya.VeryNotSticky.pbExists_full_fibre cfg si.uniform si.k si.k_le si.gridScale_ge
      si.gridScale_le hs with
    ⟨j, hj, _hfs, hfull⟩
  have hjIdx : j ∈ si.uniform.indexSet si.k := by
    simpa [VeryNotSticky.pbActiveTubeNodes] using (Finset.mem_filter.mp hj).1
  let F : Finset cfg.ι := cfg.pbTubeFibre si.uniform si.k j
  -- STEP 2: Katz-Tao on the fibre, at the hierarchy constant `K = Cu²` and the count constant
  -- `Ccnt`; the joint threshold is `Cu² · Ccnt ≤ δ^{-19η}`.
  have hδne0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt cfg.hδ
  have hδneTop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC1e : (1 : ENNReal) ≤ ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) := by
    have h1 : (1 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant bd.C₀ :=
      one_le_mul_of_one_le_of_one_le (by norm_num) (NonSlab.one_le_bodyAngleConstant bd.hC₀)
    exact_mod_cast h1
  have hCsq : (1 : ENNReal) ≤ ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 := by
    rw [pow_two]
    calc (1 : ENNReal) = 1 * 1 := by rw [one_mul]
      _ ≤ ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) *
            ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) :=
          mul_le_mul' hC1e hC1e
  have hCuδ : ((si.Cu ^ 2 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
    have h0 : ((si.Cu ^ 2 : NNReal) : ENNReal) = (si.Cu : ENNReal) ^ 2 := by push_cast; ring
    calc ((si.Cu ^ 2 : NNReal) : ENNReal) = (si.Cu : ENNReal) ^ 2 * 1 := by rw [h0, mul_one]
      _ ≤ (si.Cu : ENNReal) ^ 2 *
            ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 :=
          mul_le_mul' le_rfl hCsq
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := si.fibreConstant
  have hCδK : ((si.Cu ^ 2 : NNReal) : ENNReal) * (si.Ccnt : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(19 * cfg.η)) := by
    have hadd : (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) =
        (cfg.δ : ENNReal) ^ (-(19 * cfg.η)) := by
      rw [← ENNReal.rpow_add _ _ hδne0 hδneTop]
      congr 1
      ring
    calc ((si.Cu ^ 2 : NNReal) : ENNReal) * (si.Ccnt : ENNReal)
        ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) :=
          mul_le_mul' hCuδ si.countConstant
      _ = (cfg.δ : ENNReal) ^ (-(19 * cfg.η)) := hadd
  have hfibK : ((si.uniform.indexSet si.k).card : ℝ) *
      ((cfg.pbTubeFibre si.uniform si.k j).card : ℝ) ≤
        ((si.Cu ^ 2 : NNReal) : ℝ) * (cfg.s.card : ℝ) := by
    exact_mod_cast si.fibreCount j hjIdx
  have hKKT : ShadedBody.multiplicity F (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ + 19 * cfg.η)) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
    simpa [F] using
      cfg.nonslabKKTPow hβ1 si.katzTao (M := 19) (by norm_num) hCδK
        (cfg.pbTubeFibre_subset si.uniform si.k j) hfull
        ((si.uniform.indexSet si.k).card) hfibK si.fibreScaleCount
  let M : ENNReal := ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W
  let mF : ENNReal := ShadedBody.multiplicity F (fun i ↦ (cfg.T i).toShadedBody)
  let Ctot : NNReal := tc.C * si.Cang
  let X : ENNReal := ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
  -- STEP 3: the pointwise bound of `multSplit`, with the composed angular clause at the node `j`
  have hang : ∀ y v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre y v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
        (si.Cang : ENNReal) * mF := by
    intro y v
    simpa [mF, F] using si.angularFibre_le_fibreMult j hj y v
  have hpt : ∀ x ∈ ShadedBody.iUnionShade cfg.s tc.Y'Body,
      (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
        (Ctot : ENNReal) * M * mF := by
    intro x hx
    have hpb : (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
        ((tc.C : ENNReal) * M) * ((si.Cang : ENNReal) * mF) := by
      simpa [M] using cfg.nonslabPointwiseBound tc hB hBmax hang hδρ hρ1 hx
    calc
      (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal)
          ≤ ((tc.C : ENNReal) * M) * ((si.Cang : ENNReal) * mF) := hpb
      _ = (Ctot : ENNReal) * M * mF := by
          simp only [Ctot, ENNReal.coe_mul]
          ring
  -- STEP 4: split
  have hCpos : (0 : NNReal) < tc.C := lt_of_lt_of_le (by norm_num) (tc.thinBall hB).one_le_C
  have href := tc.isCRefinement_Y'Body hCpos
  have hsplit := Kakeya.NonSlab.multSplit (I := cfg.s) (Y := fun i ↦ (cfg.T i).toShadedBody)
      (Y' := tc.Y'Body) (bodies' := (tc.thinBall hB).bodies') (Wsh := (tc.thinBall hB).W)
      (inn := F) (Yin := fun i ↦ (cfg.T i).toShadedBody) (c := tc.C⁻¹) (C := Ctot)
      (inv_pos.mpr hCpos) href (by simpa [M, mF] using hpt)
  have hinv : ((tc.C⁻¹ : NNReal) : ENNReal)⁻¹ = (tc.C : ENNReal) := by
    rw [ENNReal.coe_inv (ne_of_gt hCpos)]
    rw [inv_inv]
  have hsplit1 : X ≤ (tc.C : ENNReal) * (Ctot : ENNReal) * M * mF := by
    simpa [X, M, mF, hinv] using hsplit
  -- STEP 5: combine and shape
  have hrho_pow : ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β
      = (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ cfg.hβ.le]
    rw [← ENNReal.rpow_mul]
  have h19e : (cfg.δ : ENNReal) ^ (-(cfg.ϱ + 19 * cfg.η)) ≤
      (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge
    · exact_mod_cast cfg.hδ1
    · linarith [cfg.hϱ]
  have hsubKKT : mF ≤ (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
      ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
    have h0 : mF ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + 19 * cfg.η)) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := hKKT
    exact h0.trans (mul_le_mul' h19e le_rfl)
  have hX'' : X ≤ (tc.C : ENNReal) * (Ctot : ENNReal) * M *
      ((cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β) := by
    exact le_trans hsplit1 (mul_le_mul_of_nonneg_left hsubKKT (by positivity))
  let Cfin : Fin 3 → NNReal := ![tc.C, tc.C, si.Cang]
  have hprod_eq : (∏ j : Fin 3, (Cfin j : ENNReal)) =
      (tc.C : ENNReal) * (tc.C : ENNReal) * (si.Cang : ENNReal) := by
    rw [Fin.prod_univ_three]
    simp [Cfin]
  let R : ENNReal :=
    M * (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β
  have hXabsorb : X ≤ (∏ j : Fin 3, (Cfin j : ENNReal)) *
      (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) * R := by
    calc
      X ≤ (tc.C : ENNReal) * (Ctot : ENNReal) * M *
          ((cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
            ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β) := hX''
      _ = (tc.C : ENNReal) * (Ctot : ENNReal) *
          (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
          (M * (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
            (cfg.s.card : ENNReal) ^ cfg.β) := by
          rw [hrho_pow]
          ring
      _ = (∏ j : Fin 3, (Cfin j : ENNReal)) *
          (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) * R := by
          rw [hprod_eq]
          simp only [Ctot, R, ENNReal.coe_mul]
          ring
  -- STEP 6: absorb
  have hϱsum : 0 < cfg.ϱ + cfg.η := add_pos cfg.hϱ cfg.hη
  have hmono : (cfg.δ : ENNReal) ^ (-cfg.η) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge
    · exact_mod_cast cfg.hδ1
    · linarith [cfg.hϱ]
  have hthin : (tc.C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := cfg.thinConstant_le tc hB scale
  have hangC : (si.Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := si.angularConstant
  have hC : ∀ j : Fin 3, (Cfin j : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) := by
    intro j
    have hbase : ∀ c : NNReal, (c : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
        (c : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) := fun c hc => hc.trans hmono
    fin_cases j
    · exact hbase _ hthin
    · exact hbase _ hthin
    · exact hbase _ hangC
  have hXabsorb' : X ≤ (∏ j : Fin 3, (Cfin j : ENNReal)) *
      (cfg.δ : ENNReal) ^ (-(((19 : ℕ) : ℝ) * (cfg.ϱ + cfg.η))) * R := by
    simpa using hXabsorb
  have hXabs := Kakeya.VeryNotSticky.tangentialSlabMultAbsorb (δ := cfg.δ) (hδ := cfg.hδ)
      (hδ1 := cfg.hδ1) (ϱ := cfg.ϱ + cfg.η) (hϱ := hϱsum) (k := 3) (m := 19)
      (hkm := by norm_num) (C := Cfin) (hC := hC) (X := X) (R := R) hXabsorb'
  simpa [X, R, M, mul_assoc] using hXabs

/-- **The existing `Kakeya.VeryNotSticky.nonslabSplitBound` is a corollary of the twin.** The
existing statement, binder for binder, proved by `Kakeya.VeryNotSticky.nonslabSplitBoundPB` at
`si.toPB`. Nothing downstream of the split bound is weakened by the retype: whatever the exact
model could prove, the bracket model proves too, at the same constants. -/
theorem nonslabSplitBound_of_pb (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (hβ1 : cfg.β ≤ 1)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ B' (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (si : SplitInputs cfg bd) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4)) *
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W *
        (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β :=
  nonslabSplitBoundPB cfg hβ1 hnotslab tc hB hBmax scale si.toPB

end Kakeya.VeryNotSticky

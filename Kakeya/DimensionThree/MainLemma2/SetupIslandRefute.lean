/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.MainLemma2.ThinEstimates
public import Kakeya.DimensionThree.MainLemma2.BallJoint

/-!
# `exists_setup_caseSideData` forces a mass floor on every piece of the ball cover

`Kakeya.VeryNotSticky.CaseSideData` contains, through its thin-case datum
`Kakeya.VeryNotSticky.ThinConfig` and the clause `Kakeya.ThinCase.ThinBall.denseBall`, the
demand that **every** piece `B̂` of the cover of (C2) carry shading of measure at least
`C⁻¹ δ^{2η} |B_δ|` (`denseBall` at the `tb` index `2η` of
`Kakeya.VeryNotSticky.ThinConfig.tb`, F8), and through
`Kakeya.VeryNotSticky.CaseScale.transverse_ballFill` the bound
`C ≤ δ^{-η}`.  Composing the two gives an *absolute* floor,

`δ^{3η} |B_δ| ≤ |B̂ ∩ U(𝕋, Y)|` for every `B ∈ 𝔅`

with no constant left free (`Kakeya.VeryNotSticky.caseSideData_pieceMass`).

Together with the rigidity of the *old* form of `Kakeya.VeryNotSticky.fullness_ge` — the clause
`λ(cfg) ≥ δ^η`, hoisted below as `RigidFullnessField`
(`Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge`) — this refutes
`Kakeya.VeryNotSticky.SetupCaseSideDataStatement` for any family that is *flat* — every tube of
shading density exactly `δ^η`, which the target's aggregate binder `hfull` permits — and each of
whose tubes carries an **island**: a spatially isolated piece of shading of positive measure
below `δ^{3η}|B_δ|`.  The refutation is
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_flat_island`, in the same
witness-hypothesis form as
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_concentrated`.  Both refutations of this
file are **records**: since the field was repaired to `δ^{2η}` and the covering clause now applies to `Kakeya.VeryNotSticky.BallData.P_cover` to the working shading `Y_g` of
`Kakeya.VeryNotSticky.BallData.Yg`, they take the two retired clauses as the hoisted hypotheses
`RigidFullnessField` and `UniformShadingCoverField` and run against no live field; the
unconditional `Kakeya.VeryNotSticky.caseSideData_pieceMass` is what consumers of this file use.

The diagnosis it yields is precise: the offending clause is `fullness_ge`, asserted at exactly
the `δ^η` of the target's own binder **with no comparison constant**.  Because carriers are
preserved by `ShadedBody.IsRefinement`, a flat family leaves the construction no room to delete
the islands — not even a null-free fraction of the mass — while at `λ(cfg) ≥ δ^{2η}`, or at
`λ(cfg) ≥ c δ^η` with `c ⪆ 1`, deleting every island costs only a `δ^{2η+1}` fraction of the
shading mass and the obstruction disappears.  This was the fourth occurrence in Section 9 of a
GWZ `⪆` rendered without its constant, after `Kakeya.VeryNotSticky.lam_ge`,
`Kakeya.VeryNotSticky.BallData.segs_dilation` and `Kakeya.VeryNotSticky.rho_count`; all four
have since been repaired — `lam_ge` to `Cd · δ^{2η}` and `fullness_ge` to `δ^{2η}`,
`segs_dilation` with the constant `Cdil`, `rho_count` as
`Kakeya.VeryNotSticky.RhoParentData`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-- The transfer constant of the thin case dominates its own argument. -/
lemma le_transferConstant (C₀ : NNReal) {C : NNReal} (hC : 1 ≤ C) :
    C ≤ ThinCase.transferConstant C C₀ := by
  have hC3 : C ≤ C ^ 3 := le_self_pow hC (by norm_num)
  have hw : (1 : NNReal) ≤ (1 + ThinCase.w1Constant C₀) ^ 3 :=
    one_le_pow₀ (by simp : (1 : NNReal) ≤ 1 + ThinCase.w1Constant C₀)
  have h212 : (1 : NNReal) ≤ 2 ^ 12 := by norm_num
  have h1 : C ≤ 2 ^ 12 * C ^ 3 * (1 + ThinCase.w1Constant C₀) ^ 3 := by
    calc C = 1 * C * 1 := by ring
      _ ≤ 2 ^ 12 * C ^ 3 * (1 + ThinCase.w1Constant C₀) ^ 3 :=
          mul_le_mul' (mul_le_mul' h212 hC3) hw
  have hup : 2 ^ 12 * C ^ 3 * (1 + ThinCase.w1Constant C₀) ^ 3
      ≤ ThinCase.netUpperConstant C C₀ := le_max_right _ _
  have hlow : (1 : NNReal) ≤ ThinCase.netLowerConstant C := ThinCase.one_le_netLowerConstant C
  have h8 : (1 : NNReal) ≤ 2 ^ 3 := by norm_num
  change C ≤ 2 ^ 3 * ThinCase.netUpperConstant C C₀ * ThinCase.netLowerConstant C
  calc C ≤ ThinCase.netUpperConstant C C₀ := le_trans h1 hup
    _ = 1 * ThinCase.netUpperConstant C C₀ * 1 := by ring
    _ ≤ 2 ^ 3 * ThinCase.netUpperConstant C C₀ * ThinCase.netLowerConstant C :=
        mul_le_mul' (mul_le_mul' h8 le_rfl) hlow

/-- **The thin-case comparison constant is at most `δ^{-η}`**, by
`Kakeya.VeryNotSticky.CaseScale.transverse_ballFill`. -/
lemma caseSideData_C_le {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {τ τ' : ℝ}
    (sd : CaseSideData cfg bd τ τ') (hC : 1 ≤ sd.tc.C) :
    sd.tc.C ≤ cfg.δ ^ (-cfg.η) := by
  have h := sd.caseScale.transverse_ballFill
  refine le_trans (le_transferConstant bd.C₀ hC) (le_trans ?_ h)
  have hnn : (0 : NNReal) ≤ ThinCase.transferConstant sd.tc.C bd.C₀ := bot_le
  exact le_mul_of_one_le_left hnn (by norm_num)

open scoped Classical in
/-- **Every piece of the ball cover carries shading of measure at least `δ^{3η}|B_δ|`.**

This is the composite of two clauses of `Kakeya.VeryNotSticky.CaseSideData`:
`Kakeya.ThinCase.ThinBall.denseBall`, which produces inside some retained segment of the ball a
`δ`-ball on which the *refined* shading has density at least `C⁻¹δ^{2η}` (the `tb` index `2η`
of `Kakeya.VeryNotSticky.ThinConfig.tb`, F8), and
`Kakeya.VeryNotSticky.CaseScale.transverse_ballFill`, which forces `C ≤ δ^{-η}`.  The refined
shading of a segment is contained in the piece and in the union of the working shadings of the
segment's parent tubes (`Kakeya.VeryNotSticky.BallData.Y_piece`, `back`, `fam_subset`), and
`Y_g ⊆ Y` (`Kakeya.VeryNotSticky.BallData.Yg_subset`), so the mass it exhibits is mass of
`U(𝕋, Y)` inside the piece.

**No constant is left free**, which is what makes this usable as a refutation lever. -/
theorem caseSideData_pieceMass {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {τ τ' : ℝ}
    (sd : CaseSideData cfg bd τ τ') {B : bd.bι} (hB : B ∈ bd.bs) :
    (cfg.δ : ENNReal) ^ (3 * cfg.η) *
        volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (cfg.δ : ℝ))
      ≤ volume (bd.P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade) := by
  classical
  have hδ0 : cfg.δ ≠ 0 := cfg.hδ.ne'
  set tb := sd.tc.tb B hB with htb
  have hC1 : (1 : NNReal) ≤ sd.tc.C := tb.one_le_C
  have hC0 : sd.tc.C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  -- `δ^η ≤ C⁻¹`
  have hCle : sd.tc.C ≤ cfg.δ ^ (-cfg.η) := caseSideData_C_le sd hC1
  have hinvN : cfg.δ ^ cfg.η ≤ (sd.tc.C)⁻¹ := by
    have h1 : (cfg.δ ^ (-cfg.η) : NNReal)⁻¹ ≤ (sd.tc.C)⁻¹ := by
      refine inv_anti₀ ?_ hCle
      exact lt_of_lt_of_le zero_lt_one hC1
    refine le_trans (le_of_eq ?_) h1
    rw [NNReal.rpow_neg, inv_inv]
  have hinv : ((cfg.δ : ENNReal)) ^ cfg.η ≤ ((sd.tc.C : NNReal) : ENNReal)⁻¹ := by
    rw [← ENNReal.coe_inv hC0, ← ENNReal.coe_rpow_of_ne_zero hδ0]
    exact_mod_cast hinvN
  -- the dense `δ`-ball inside a retained segment
  obtain ⟨p, hpS⟩ := tb.S_nonempty
  have hpsegs : p ∈ bd.segs B := tb.S_subset hpS
  obtain ⟨x, hx⟩ := tb.denseBall p hpS
  -- the mass it exhibits is mass of `U(𝕋, Y)` inside the piece
  have hsub : ball x (cfg.δ : ℝ) ∩ (tb.Y' p).shade
      ⊆ bd.P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade := by
    intro z hz
    have hzY : z ∈ (bd.Y p).shade := tb.shade_Y'_subset p hpsegs hz.2
    refine ⟨bd.Y_piece B hB p hpsegs hzY, ?_⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (bd.back B hB p hpsegs hzY)
    exact Set.mem_biUnion (bd.fam_subset B hB p hpsegs hi)
      (bd.Yg_subset i (bd.fam_subset B hB p hpsegs hi) hzi)
  -- translation invariance of the volume of a `δ`-ball
  have hballvol : volume (ball x (cfg.δ : ℝ))
      = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (cfg.δ : ℝ)) :=
    MeasureTheory.Measure.addHaar_ball_center volume x _
  -- and the split `δ^{3η} = δ^η · δ^{2η}`
  have hsplit : ((cfg.δ : ENNReal)) ^ (3 * cfg.η)
      = ((cfg.δ : ENNReal)) ^ cfg.η * ((cfg.δ : ENNReal)) ^ (2 * cfg.η) := by
    rw [← ENNReal.rpow_add _ _ (by simpa using hδ0) ENNReal.coe_ne_top]
    congr 1
    ring
  calc ((cfg.δ : ENNReal)) ^ (3 * cfg.η) *
        volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (cfg.δ : ℝ))
      = ((cfg.δ : ENNReal)) ^ cfg.η * ((cfg.δ : ENNReal)) ^ (2 * cfg.η) *
          volume (ball x (cfg.δ : ℝ)) := by rw [hsplit, hballvol]
    _ ≤ ((sd.tc.C : NNReal) : ENNReal)⁻¹ * ((cfg.δ : ENNReal)) ^ (2 * cfg.η) *
          volume (ball x (cfg.δ : ℝ)) := by gcongr
    _ ≤ volume (ball x (cfg.δ : ℝ) ∩ (tb.Y' p).shade) := hx
    _ ≤ volume (bd.P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade) := measure_mono hsub

/-- **The OLD form of `Kakeya.VeryNotSticky.fullness_ge`, hoisted out of the structure.**

`RigidFullnessField` is the clause `λ(cfg) ≥ δ^η` — the fullness field asserted at *exactly*
the `δ^η` of the target's own binder `hfull`, with no comparison constant — quantified over
every configuration. It is the form the field carried before it was repaired to `δ^{2η}`.

It is stated as a `Prop` of its own for the reason the house `statement_of_universal_*` device
exists: **a tripwire about a *field* cannot survive that field changing.** The refutation below
exploits precisely this clause's rigidity, so it had to be restated about the clause rather than
about `Kakeya.VeryNotSticky.SetupCaseSideDataStatement`; hoisted, it keeps compiling, and the
defect stays on the record where a reader can see it and cannot silently return. Compare
`Kakeya.VeryNotSticky.RhoCountFieldOldStatement`, which does the same for `rho_count`.

**It is false**, granted the witness and the setup statement:
`not_rigidFullnessField_of_flat_island`. That is why the live field reads `δ^{2η}`. -/
def RigidFullnessField : Prop :=
  ∀ cfg : VeryNotSticky.{u},
    cfg.δ ^ cfg.η ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody)

/-- **The OLD form of `Kakeya.VeryNotSticky.BallData.P_cover`, hoisted out of the structure.**

`UniformShadingCoverField` is the covering clause of (C2) read on the *uniform* shading —
`Y(T) ⊆ ⋃_{B ∈ 𝔅} B̂` for every `T ∈ 𝕋` and every `BallData` — quantified over every
configuration and every `BallData` on it. It is the form the field carried when it was imposed on the uniform shading instead of the working shading `Y_g` of
`Kakeya.VeryNotSticky.BallData.Yg`, from which GWZ delete the shading outside the retained
balls (`gwz.txt` l.2029-2030). The live field constrains only `Y_g`; nothing in `BallData` now
forces a point of `Y(T) \ Y_g(T)` — an island, say — into a piece.

Hoisted for the same reason as `RigidFullnessField`: the refutation below reads exactly this
clause, so it had to be restated about the clause rather than about the field; hoisted, the
derivation keeps compiling and the retired clause stays on the record. Read at the coarse
producers (`Kakeya.VeryNotSticky.exists_ballDataCore`, where `Yg = Y`) it is true; as a
universal statement it is what the repair removed. -/
def UniformShadingCoverField : Prop :=
  ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bd.bs, bd.P B

open scoped Classical in
/-- **The OLD fullness clause is FALSE for a flat family with isolated islands of
shading** — in the witness-hypothesis form of
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_concentrated`.

The witness is a family satisfying **all five binders of the target**, which is moreover

* **flat**: every tube has shading density *exactly* `δ^η`.  The binder `hfull` asserts only
  the aggregate ratio `λ(𝕋, Y) ≥ δ^η`, which a flat family satisfies with equality;
* **islanded**: every tube carries a piece of shading of positive measure inside some ball
  `B(y, r₁)` such that the *total* shading of the family in `B(y, 4r₁)` has measure below
  `δ^{3η}|B_δ|`.

Then `Kakeya.VeryNotSticky.SetupCaseSideDataStatement` fails.  The derivation is short and
every step is a named clause:

1. `Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge` — since `ShadedBody.IsRefinement`
   keeps carriers and only shrinks shadings, and the old `fullness_ge` was asserted at exactly
   the `δ^η` of the binder — which is the hypothesis `RigidFullnessField` here — the produced
   configuration must retain the **full shading measure** of every tube it keeps.  So the island
   survives in `cfg`, with its measure.
2. the covering clause of (C2) on the *uniform* shading — the hypothesis
   `UniformShadingCoverField`, which was `Kakeya.VeryNotSticky.BallData.P_cover` when it was imposed on the uniform shading instead of the working shading `Y_g` — puts a point of the
   surviving island in a piece `B̂`, and `P_subset_ball` puts that whole piece inside
   `B(y, 4r₁)`.
3. `Kakeya.VeryNotSticky.caseSideData_pieceMass` — `CaseSideData` forces that piece to carry
   shading of measure at least `δ^{3η}|B_δ|`, which contradicts the island bound.

**The defective clause is `fullness_ge`,** asserted at exactly `δ^η` with no comparison
constant.  Every island together has measure at most `|𝕋| δ^{3η}|B_δ| ≍ δ^{3η+3}|𝕋|`, against a
total shading mass `≍ δ^{η+2}|𝕋|`, i.e. a `δ^{2η+1}` fraction: deleting all of them is far
cheaper than the `δ^η` fraction the target's own conjunct `δ^η ≤ c` allows to be lost.  It is
`fullness_ge` — and only `fullness_ge` — that forbids it, because at exactly `δ^η` a flat
family leaves no slack at all.  Repairing it to `λ(cfg) ≥ δ^{2η}`, in the style of the
`Kakeya.VeryNotSticky.lam_ge` repair, or to `λ(cfg) ≥ c δ^η` with `c ⪆ 1`, removes the
obstruction.

**Second retirement.** The derivation also used the covering clause
of (C2) *on the uniform shading*: `Y(T) ⊆ ⋃_{B ∈ 𝔅} B̂`, which put a point of the surviving
island in a piece. That clause is no longer a field: `Kakeya.VeryNotSticky.BallData.P_cover`
now reads the *working* shading `Y_g ⊆ Y` of `Kakeya.VeryNotSticky.BallData.Yg`, from which a
light island may simply be deleted (GWZ `gwz.txt` l.2029-2030), so the island need not meet any
piece and the refutation does not run against the live structure. It is kept on the record in
the same hoisted form as `RigidFullnessField`: the old clause is the named `Prop`
`UniformShadingCoverField`, and both refutations below take it as a hypothesis.

**This declaration now concludes `¬ RigidFullnessField` rather than
`¬ SetupCaseSideDataStatement`, and that is the repair working, not a weakening of it.** Here its hypothesis `H` is the frozen pre-F12a statement
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`: the witness discharges the uniformity
binder only in its old, unbounded form (see `not_setupCaseSideDataStatement_of_flat_island`). The
derivation is unchanged line for line; the *only* differences are where the rigid fullness clause
comes from — it was `cfg.fullness_ge`, and the field no longer supplies it, because the field was
repaired to `δ^{2η}` for exactly the reason this proof demonstrates — and, where the covering of the uniform shading comes from: it was `bd.P_cover`,
now read on the working shading `Y_g`, and it is supplied here by the hoisted
`UniformShadingCoverField`. Read the two together: the
old clause is false (here), while at `δ^{2η}` the clause is not merely affordable but **free**
(`Kakeya.VeryNotSticky.fullness_two_eta_of_isCRefinement`, whose budget at `δ^η` is exactly `1`
by `Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss`). The corollary
`not_setupCaseSideDataStatement_of_flat_island` below recovers this file's original conclusion
verbatim from the old clause, so nothing proved here has been lost. -/
theorem not_rigidFullnessField_of_flat_island
    {β ζ exscal ϱ η τ τ' : Real} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hwit : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∃ (ι : Type u) (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
        (∃ C : NNReal,
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) ∧
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η ∧
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) ∧
        (∀ i ∈ s, volume (T i).shade
          = ((δ ^ η : NNReal) : ENNReal) * volume (T i).carrier) ∧
        (∀ i ∈ s, ∃ y : EuclideanSpace ℝ (Fin 3),
          0 < volume ((T i).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ)) ∧
          volume ((⋃ j ∈ s, (T j).shade) ∩
              closedBall y (4 * ((δ ^ exscal : NNReal) : ℝ)))
            < (δ : ENNReal) ^ (3 * η) *
                volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (δ : ℝ))) )
    (H : SetupCaseSideDataStatementOld.{u})
    (hcover : UniformShadingCoverField.{u})
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ¬ RigidFullnessField.{u} := by
  classical
  intro hfield
  obtain ⟨δ, hforce, ι, s, T, hball, huni, hmax, hfull, hcount, hflat, hisland⟩ :=
    ((H hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w).and hwit).exists
  obtain ⟨cfg, bd, e, c, ⟨hβeq, hζeq, hδeq, hexeq, hϱeq, hηeq⟩, href, hc, ⟨sd⟩⟩ :=
    hforce s T hball huni hmax hfull hcount
  -- the refinement, read at an index of `cfg`
  have hmapmem : ∀ j ∈ cfg.s, e j ∈ cfg.s.map e.toEmbedding := by
    intro j hj
    exact Finset.mem_map.2 ⟨j, hj, rfl⟩
  have hsub : ∀ j ∈ cfg.s, e j ∈ s := fun j hj ↦ href.1.1 (hmapmem j hj)
  have hcarr : ∀ j ∈ cfg.s, volume (T (e j)).carrier = volume (cfg.T j).carrier := by
    intro j hj
    have h := (href.1.2 (e j) (hmapmem j hj)).1
    simp only [Equiv.symm_apply_apply] at h
    exact congrArg (fun K ↦ volume (ConvexSpaceBody.carrier K)) h.symm
  have hshsub : ∀ j ∈ cfg.s, (cfg.T j).shade ⊆ (T (e j)).shade := by
    intro j hj
    have h := (href.1.2 (e j) (hmapmem j hj)).2
    simpa using h
  -- flatness passes to `cfg`, hence `fullness_ge` is rigid there
  have hflat' : ∀ j ∈ cfg.s, volume (cfg.T j).shade
      ≤ ((δ ^ η : NNReal) : ENNReal) * volume (cfg.T j).carrier := by
    intro j hj
    calc volume (cfg.T j).shade ≤ volume (T (e j)).shade := measure_mono (hshsub j hj)
      _ = ((δ ^ η : NNReal) : ENNReal) * volume (T (e j)).carrier := hflat _ (hsub j hj)
      _ = ((δ ^ η : NNReal) : ENNReal) * volume (cfg.T j).carrier := by rw [hcarr j hj]
  have hpow : cfg.δ ^ cfg.η = (δ ^ η : NNReal) := by rw [hδeq, hηeq]
  have hfullcfg : (δ ^ η : NNReal)
      ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) := by
    calc (δ ^ η : NNReal) = cfg.δ ^ cfg.η := hpow.symm
      _ ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) := hfield cfg
  have hrigid := volume_shade_eq_of_fullness_ge cfg.s
    (fun i ↦ (cfg.T i).toShadedBody) hfullcfg hflat'
  -- a retained tube, and its island
  obtain ⟨j₀, hj₀⟩ := nonempty_s_of_tube_count cfg
  obtain ⟨y, hposI, hsmall⟩ := hisland (e j₀) (hsub j₀ hj₀)
  -- the island survives in `cfg`
  have hshtop : volume (T (e j₀)).shade ≠ ⊤ :=
    ne_top_of_le_ne_top ((T (e j₀)).toConvexSpaceBody.isCompact).measure_lt_top.ne
      (measure_mono (T (e j₀)).shade_subset)
  have hmasseq : volume (T (e j₀)).shade = volume (cfg.T j₀).shade := by
    rw [hrigid j₀ hj₀, ← hcarr j₀ hj₀]
    exact (hflat _ (hsub j₀ hj₀))
  have hfincfg : volume (cfg.T j₀).shade ≠ ⊤ := by
    rw [← hmasseq]; exact hshtop
  have hdiffnull : volume ((T (e j₀)).shade \ (cfg.T j₀).shade) = 0 := by
    rw [measure_sdiff (hshsub j₀ hj₀)
      ((cfg.T j₀).measurableSet_shade).nullMeasurableSet hfincfg, hmasseq, tsub_self]
  have hposI' : 0 < volume ((cfg.T j₀).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ)) := by
    refine lt_of_lt_of_le hposI ?_
    have hcov : (T (e j₀)).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ)
        ⊆ ((cfg.T j₀).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ))
            ∪ ((T (e j₀)).shade \ (cfg.T j₀).shade) := by
      intro z hz
      by_cases hzc : z ∈ (cfg.T j₀).shade
      · exact Or.inl ⟨hzc, hz.2⟩
      · exact Or.inr ⟨hz.1, hzc⟩
    calc volume ((T (e j₀)).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ))
        ≤ volume (((cfg.T j₀).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ))
            ∪ ((T (e j₀)).shade \ (cfg.T j₀).shade)) := measure_mono hcov
      _ ≤ volume ((cfg.T j₀).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ))
            + volume ((T (e j₀)).shade \ (cfg.T j₀).shade) := measure_union_le _ _
      _ = volume ((cfg.T j₀).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ)) := by
            rw [hdiffnull, add_zero]
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hposI'.ne'
  -- the piece of the cover that catches it — by the hoisted covering clause on the uniform
  -- shading, no longer a field of `bd`
  obtain ⟨B, hB, hx₀B⟩ := Set.mem_iUnion₂.1 (hcover cfg bd j₀ hj₀ hx₀.1)
  -- `r₁ = δ^exscal`
  have hr₁ : (cfg.r₁ : ℝ) = ((δ ^ exscal : NNReal) : ℝ) := by
    simp only [VeryNotSticky.r₁, hδeq, hexeq]
  have hr₁0 : (0 : ℝ) ≤ ((δ ^ exscal : NNReal) : ℝ) := NNReal.coe_nonneg _
  -- the piece sits inside `B(y, 4 r₁)`
  have hPsub : bd.P B ⊆ closedBall y (4 * ((δ ^ exscal : NNReal) : ℝ)) := by
    intro z hz
    have hzB : dist z (bd.ctr B) ≤ ((δ ^ exscal : NNReal) : ℝ) := by
      have := bd.P_subset_ball B hB hz
      rw [hr₁] at this
      exact Metric.mem_closedBall.1 this
    have hx₀ctr : dist (bd.ctr B) x₀ ≤ ((δ ^ exscal : NNReal) : ℝ) := by
      have := bd.P_subset_ball B hB hx₀B
      rw [hr₁] at this
      rw [dist_comm]
      exact Metric.mem_closedBall.1 this
    have hx₀y : dist x₀ y ≤ ((δ ^ exscal : NNReal) : ℝ) := Metric.mem_closedBall.1 hx₀.2
    refine Metric.mem_closedBall.2 ?_
    calc dist z y ≤ dist z (bd.ctr B) + dist (bd.ctr B) y := dist_triangle _ _ _
      _ ≤ dist z (bd.ctr B) + (dist (bd.ctr B) x₀ + dist x₀ y) := by
          gcongr
          exact dist_triangle _ _ _
      _ ≤ ((δ ^ exscal : NNReal) : ℝ) + (((δ ^ exscal : NNReal) : ℝ)
            + ((δ ^ exscal : NNReal) : ℝ)) := by gcongr
      _ ≤ 4 * ((δ ^ exscal : NNReal) : ℝ) := by linarith
  -- the shading of `cfg` inside the piece is shading of the original family near `y`
  have hUsub : bd.P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade
      ⊆ (⋃ j ∈ s, (T j).shade) ∩ closedBall y (4 * ((δ ^ exscal : NNReal) : ℝ)) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 hz.2
    exact ⟨Set.mem_biUnion (hsub i hi) (hshsub i hi hzi), hPsub hz.1⟩
  -- the mass floor forced by `CaseSideData`
  have hfloor := caseSideData_pieceMass sd hB
  have hlhs : ((cfg.δ : ENNReal)) ^ (3 * cfg.η) *
        volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (cfg.δ : ℝ))
      = (δ : ENNReal) ^ (3 * η) *
        volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (δ : ℝ)) := by
    rw [hδeq, hηeq]
  have hfloor2 : (δ : ENNReal) ^ (3 * η) *
        volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (δ : ℝ))
      ≤ volume (bd.P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade) := by
    rw [← hlhs]; exact hfloor
  exact absurd (lt_of_le_of_lt (le_trans hfloor2 (measure_mono hUsub)) hsmall)
    (lt_irrefl _)

open scoped Classical in
/-- **`exists_setup_caseSideData` is FALSE for a flat family with isolated islands** — the
original conclusion of this file, recovered verbatim from the old fullness clause.

This is the `Kakeya.ThinCase.Refute.statement_of_universal_loc` device: granting
`RigidFullnessField` — the pre-repair `fullness_ge` — universally and for free, the refutation
is exactly what it was before the field moved, with the same witness and the same derivation.
So the historical claim of this file is preserved and machine-checked, and the hypotheses the
two repairs added are named: `RigidFullnessField` (the old `fullness_ge`) and, `UniformShadingCoverField` (the old `P_cover`, on the uniform shading).

`hfield` is of course false, by `not_rigidFullnessField_of_flat_island`; combining the two merely
reproves `¬ hfield`, which is sound and is the point — it is the compiled record that repairing
`fullness_ge` was **necessary**, not merely convenient. Nothing here weakens the mathematics of
the refutation: `caseSideData_pieceMass` above, which is what consumers of this file actually use,
is unconditional and untouched.

**This counterexample concerns the frozen
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`.** The witness `hwit` supplies the
uniformity binder in its old, unbounded form (the flat-island family gets it free from
`Kakeya.VeryNotSticky.exists_shadedUniformTubeSet_of_axes_injOn`, at `C = |s| + 1`); the live
statement's binder `1 ≤ C ≤ δ^{-η}` is *not* met by that witness on any Lemma 9.1 input, so the
bounded binder excludes the flat-island family unless it is uniform at a sub-polynomial
constant — which is exactly what GWZ's hypothesis asks. -/
theorem not_setupCaseSideDataStatement_of_flat_island
    {β ζ exscal ϱ η τ τ' : Real} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hwit : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∃ (ι : Type u) (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
        (∃ C : NNReal,
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) ∧
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η ∧
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) ∧
        (∀ i ∈ s, volume (T i).shade
          = ((δ ^ η : NNReal) : ENNReal) * volume (T i).carrier) ∧
        (∀ i ∈ s, ∃ y : EuclideanSpace ℝ (Fin 3),
          0 < volume ((T i).shade ∩ closedBall y ((δ ^ exscal : NNReal) : ℝ)) ∧
          volume ((⋃ j ∈ s, (T j).shade) ∩
              closedBall y (4 * ((δ ^ exscal : NNReal) : ℝ)))
            < (δ : ENNReal) ^ (3 * η) *
                volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (δ : ℝ))) )
    (hfield : RigidFullnessField.{u})
    (hcover : UniformShadingCoverField.{u})
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ¬ SetupCaseSideDataStatementOld.{u} := fun H =>
  absurd hfield (not_rigidFullnessField_of_flat_island hβ hβ1 hζ hexscal hϱ hη params hplankF
    hKT hF hwit H hcover w)

end Kakeya.VeryNotSticky

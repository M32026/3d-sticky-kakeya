/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.PlankPresentation
public import Kakeya.DimensionThree.MainLemma2.TransverseCase
public import Kakeya.DimensionThree.MainLemma2.TangentialCase
public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence
public import Kakeya.DimensionThree.Volume
public import Kakeya.Discretization
public import Kakeya.LEApprox

/-!
# The non-slab case of Main Lemma 2

In this file we assemble the non-slab case of the thin case of Main Lemma 2 (blueprint
`lem:ml2nonslab`): the case `b ≤ δ^{exscal} r₁ = δ^{2·exscal}` of the very-not-sticky
configuration, where `b` is the middle affine thickness of the factoring bodies.

The case splits according to the size of the factoring multiplicity `μ(𝕎'_B, Y_{𝕎'_B})` at a
ball `B ∈ 𝔅` maximising it.

* If `μ(𝕎'_B, Y_{𝕎'_B}) ≤ δ^{-η}`, the splitting `Kakeya.NonSlab.multSplit` and the
  Katz–Tao bound `Kakeya.VeryNotSticky.nonslabKKT` combine directly and give the goal with
  gain `exscal · β`: this is `Kakeya.VeryNotSticky.goalMult_of_multBodies_le`.
* If `μ(𝕎'_B, Y_{𝕎'_B}) ≥ δ^{-η}`, the angle-selection lemma
  `Kakeya.findingTypicalAngleOfIntersection_perScale` may be run on `𝕎'_B` after presenting it as a
  family of `a' × b' × 1` planks (`Kakeya.VeryNotSticky.plankPresentation`,
  `Kakeya.VeryNotSticky.plankCard`), producing a typical angle `θ`
  (`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`). Splitting on `θ` against
  `δ^{-τ'} a / b` puts us in the transverse case
  (`Kakeya.VeryNotSticky.goalMult_of_theta_ge`) or in the tangential case
  (`Kakeya.VeryNotSticky.goalMult_of_theta_lt`): this is
  `Kakeya.VeryNotSticky.goalMult_of_multBodies_ge`.

Every branch lemma below is stated relative to `cfg`: the per-ball data of Configuration
`hyp:ml2setup` is the bundle `Kakeya.VeryNotSticky.BallData cfg` and the thin-case data of
Configuration `hyp:ml2thinsetup` is `Kakeya.VeryNotSticky.ThinConfig cfg bd`, both from
`Kakeya.DimensionThree.MainLemma2.ThinConfig`. The families `𝕎'_B` and shadings `Y_{𝕎'_B}`
are read off `tc.thinBall hB` at the distinguished ball, and never taken as free arguments:
with free arguments the multiplicity hypothesis `μ(𝕎'_B, Y_{𝕎'_B}) ≤ δ^{-η}` could be
satisfied vacuously by the empty family, and the branch lemmas would be at least as strong as
the theorem they are supposed to prove.

The auxiliary lemmas `Kakeya.VeryNotSticky.plankPresentation` and
`Kakeya.VeryNotSticky.plankCard` are genuinely general statements about a family of bodies,
respectively planks, and are stated for free data as before.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-! ### The small-multiplicity branch -/

/-- **Main Lemma 2, non-slab case with small factoring multiplicity** (blueprint
`lem:ml2smallmult`).

In the configuration `cfg`, with the per-ball data `bd` of Configuration `hyp:ml2setup` and
the thin-case data `tc` of Configuration `hyp:ml2thinsetup` over it, together with the
thin-case refinement `a ≤ δ^{1-τ}` and the non-slab hypothesis `b ≤ δ^{2·exscal}`, let
`B ∈ 𝔅` maximise the factoring multiplicity over the cover and suppose
`μ(𝕎'_B, Y_{𝕎'_B}) ≤ δ^{-η}` — equivalently, that `μ(𝕎'_{B'}, Y_{𝕎'_{B'}}) ≤ δ^{-η}` for
every `B' ∈ 𝔅`. Then the goal holds with the exponent `ν = exscal · β`.

The family `𝕎'_B` and its shading `Y_{𝕎'_B}` are `(tc.thinBall hB).bodies'` and
`(tc.thinBall hB).W`: they must be tied to `cfg`, since for a free family the hypothesis
`hmult` is satisfied vacuously by `bodies' = ∅` (the multiplicity of the empty family is `0`)
and the lemma would then prove the goal unconditionally.

Both `Kakeya.NonSlab.multSplit` and `Kakeya.VeryNotSticky.nonslabKKT` are stated at the
dilated scale `ρ₂*`, so they combine directly:
`μ(𝕋, Y) ⪅ δ^{-η} δ^{-(ϱ+η)} (ρ₂^{2+ζ}|𝕋|)^β ≤ δ^{-2η-ϱ} δ^{exscal(2+ζ)β}|𝕋|^β`, using
`ρ₂ ≤ δ^{exscal}` from `rho2_range`. The second `η` is the cost of raising the fibre count to
the `β`-th power, which happens once inside `Kakeya.VeryNotSticky.nonslabKKT` and which the
bound it produces already carries. The exact inequality needed is therefore
`2η + ϱ < exscal(1+ζ)β`, which is `params.smallMultiplicity`, and it leaves the required gain
`exscal·β` with a positive margin for the remaining fixed constants. The field
`scale.rho2Star_le_one` ensures `ρ₂* ≤ 1`.

The budget is stated with `2η` and not with the `η + ϱ < exscal(1+ζ)β` of earlier versions:
the surplus `exscal(1+ζ)β - (η+ϱ)` of the weaker form is positive but is not known to exceed
`η`, and `η` is fixed before `δ`, so it cannot be shrunk afterwards to absorb the second `η`.
The strengthening is free, since every field of `Kakeya.VeryNotSticky.CaseParams` bounds `η`
from above only and `η` is chosen last (blueprint `lem:ml2smallmult`, closing paragraph).

The maximality of `B` in the statement above is the hypothesis `hBmax`, and `hβ1 : β ≤ 1` is
the Katz–Tao hypothesis of `Kakeya.VeryNotSticky.nonslabKKT`; both are consumed through
`Kakeya.VeryNotSticky.nonslabSplitBound` and supplied by
`Kakeya.VeryNotSticky.goalMult_of_b_le`. -/
theorem goalMult_of_multBodies_le (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (_hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ (B' : bd.bι) (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (si : PBSplitInputs cfg bd)
    (hmult : ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
      (cfg.δ : ENNReal) ^ (-(16 * cfg.η))) :
    cfg.goalMult (cfg.exscal * cfg.β) := by
  classical
  have hδ_pos : 0 < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδ_ne0 : (cfg.δ : ENNReal) ≠ 0 := hδ_pos.ne'
  have hδ_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- `b ≤ δ^{exscal} r₁`, from `hnotslab` and `r₁ = δ^{exscal}`.
  have hnotslabR : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
    have h2 : cfg.δ ^ (2 * cfg.exscal) = cfg.δ ^ cfg.exscal * cfg.r₁ := by
      unfold r₁
      rw [← NNReal.rpow_add cfg.hδ.ne' cfg.exscal cfg.exscal]
      congr 1; ring
    exact hnotslab.trans_eq h2
  have houter := nonslabSplitBoundPB cfg hβ1 hnotslab tc hB hBmax scale si
  -- Substitute `hmult` and fuse the two powers of `δ`.
  have hbound : ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      ((cfg.δ : ENNReal) ^
          (-(16 * cfg.η + parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4))) *
        (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β := by
    calc
      ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
          ≤ ((cfg.δ : ENNReal) ^
                (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4))) *
              ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W *
              (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
              (cfg.s.card : ENNReal) ^ cfg.β := houter
      _ = ((cfg.δ : ENNReal) ^
                (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4))) *
              (ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W *
                ((cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
                  (cfg.s.card : ENNReal) ^ cfg.β)) := by
            simp [mul_assoc]
      _ ≤ ((cfg.δ : ENNReal) ^
                (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4))) *
              ((cfg.δ : ENNReal) ^ (-(16 * cfg.η)) *
                ((cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
                  (cfg.s.card : ENNReal) ^ cfg.β)) := by
            gcongr
      _ = ((cfg.δ : ENNReal) ^
                (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4))) *
              (cfg.δ : ENNReal) ^ (-(16 * cfg.η)) *
              (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
              (cfg.s.card : ENNReal) ^ cfg.β := by
            simp [mul_assoc]
      _ = ((cfg.δ : ENNReal) ^
              (-(16 * cfg.η + parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4))) *
            (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            have hfuse : (cfg.δ : ENNReal) ^
                    (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4)) *
                  (cfg.δ : ENNReal) ^ (-(16 * cfg.η)) =
                (cfg.δ : ENNReal) ^
                  (-(16 * cfg.η + parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4)) := by
              have h1 := (ENNReal.rpow_add
                  (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4)) (-(16 * cfg.η))
                  hδ_ne0 hδ_ne_top).symm
              rw [h1]
              congr 1; ring
            rw [hfuse]
  -- The exponent budget, then the loss → gain lemma.
  have hbudget : cfg.exscal * cfg.β +
      (16 * cfg.η + parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4) ≤
      cfg.exscal * (2 + cfg.ζ) * cfg.β := by
    have hsmb := smallMultiplicityBudget params cfg.hβ hβ1 cfg.hη
    nlinarith
  exact nonslabLossToGain cfg
    (L := 16 * cfg.η + parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4)
    (ν := cfg.exscal * cfg.β) hnotslabR hbudget hbound

/-! ### The large-multiplicity branch: a typical angle of intersection -/

/-- **The data produced by the plank presentation** (blueprint `lem:ml2plankpresentation`).

The ten clauses of blueprint `lem:ml2plankpresentation` are bundled here rather than listed as
a conjunctive existential, in the shape `Kakeya.VeryNotSticky.TypicalAngleData` already uses
one screen further down: they are produced together by a single assembly, and the consumer
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` destructures all of them.

The fields fall into four groups.

* *The dimensions* `a' ≤ b' ≤ 1` and the comparisons `hratio`, `hlower`/`hupper`,
  `hblower`/`hbupper`, `hδa'` of the blueprint display `plankDimensionsComparable`. The
  dimensions are only *comparable* to `a/r₁` and `b/r₁`, with the constant `C₀` of (C4),
  since (C4) gives the affine thicknesses of `W` only up to `C₀` and the exact `a' × b' × 1`
  box enclosing `L_B(W)` inherits that slack; the *ratio* `a'/b'` is nevertheless exactly
  `a/b`, which is what the transverse and tangential cases consume.

* *The plank family* `P` with its shading `YP`, together with `hshade` and the localization
  `hwin`. The planks lie in `B̄(0, plankBallRadius)` and not in the unit ball: `L_B(W)` does
  lie in `B̄(0,1)` by `hin`, but the plank is a superset of it. The clause is stated as
  `Plank.IsWindowedFamily` rather than as a bare containment because
  `Kakeya.VeryNotSticky.plankBallRadius` derives from `Plank.windowRadius`: it is in this form that
  `ShadedPlank.reduction_to_slab` consumes it, and stating it at any larger radius would leave
  that hypothesis undischarged.

* *The retained subfamily* `sel`, with `hsel` and `hselRefine`. The enclosing planks are
  **not** pairwise essentially distinct on all of `bodies'`, for any choice of them; see
  `Kakeya.VeryNotSticky.plankSelectionConstant`. What survives is the subfamily, retained at
  the cost of the refinement factor `(plankSelectionConstant C₀)⁻¹`. The clause that asserted
  the essential distinctness of `sel`'s planks, `hselEd`, was deleted by R26, so `sel` is
  carried for its mass retention alone.

* *The transported invariants* `hmult`, `hdens` and the rescaling bridge `hbridge`. Note that
  `hdens` is an inequality where `hmult` is an equality: `μ` sees only the shadings, which the
  enclosure leaves alone, whereas `Δ_max` sees the carriers, which the enclosure enlarges.

**The bridge is stated for a general sub-index-set `t ⊆ bodies'.** A `c`-refinement is allowed
to drop indices (`ShadedBody.IsRefinement`), the blueprint's `def:refinement` says so
explicitly, and `Kakeya.VeryNotSticky.exists_isCRefinement_of_plankRescale` — the lemma that
discharges this field — is stated at that generality. Restricting to `t = bodies'` would make
the field unusable for a refinement obtained by selection. Two radii appear because the
estimate to be transported — item `itemballfull` of `ShadedPlank.reduction_to_slab` — compares
the volume of a ball of one radius with the shaded mass in a concentric ball of a larger one;
no comparison constant is lost, `L_B` being an exact homothety of ratio `r₁⁻¹` followed by a
translation. The hypothesis is stated for closed balls and the conclusion for open ones, which
is what the consumer needs and costs nothing, spheres being Lebesgue null in `ℝ³`.

**The bridge also hands back the bijection.** The pulled-back shading is `L_B⁻¹(Y_{𝒫'})`
index for index, and the middle clause of `hbridge` says so, in the coordinate-free form
`∃ g : ℝ³ ≃ ℝ³, (Wsh' i).shade = g '' (Y_{𝒫'} i).shade`; the centre of the ball is not a
parameter of this structure, so the map itself cannot be named here. Without that clause the
`c`-refinement alone gives only `(Wsh' i).shade ⊆ (Wsh i).shade`, which is not enough to move
a statement about the *fibres* of `Y_{𝒫'}` to the fibres of `Wsh'`, and the two clauses
`Kakeya.VeryNotSticky.TypicalAngleData.htyp` and
`Kakeya.VeryNotSticky.TypicalAngleData.hangle` — both of which read the original-coordinate
shading against the rescaled plank family — would be unreachable. It is consumed through
`Kakeya.IsTypicalPlankAngle.congr_image` and
`ShadedBody.HasCConstantMultiplicity.congr_image`. -/
structure PlankPresentationData {ω : Type*} (bodies' : Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Wsh : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) (a b r₁ δ C₀ : NNReal) where
  /-- the smaller plank dimension -/
  a' : NNReal
  /-- the middle plank dimension -/
  b' : NNReal
  /-- the planks are `a' × b' × 1` with `a' ≤ b'` -/
  hab' : a' ≤ b'
  /-- the planks are `a' × b' × 1` with `b' ≤ 1` -/
  hb1' : b' ≤ 1
  /-- the plank family `𝒫 = L_B(𝕎'_B)`, enclosed -/
  P : ω → Plank a' b' hab' hb1'
  /-- the transported shading `Y_𝒫 = L_B(Y_{𝕎'_B})` -/
  YP : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))
  /-- the subfamily `𝕊*` on which the planks *are* pairwise essentially distinct -/
  sel : Finset ω
  /-- the planks have the aspect ratio of the factoring bodies -/
  hratio : a' / b' = a / b
  /-- the short dimension is comparable to `a / r₁` from below, with the constant `C₀` -/
  hlower : C₀⁻¹ * (a / r₁) ≤ a'
  /-- the short dimension is comparable to `a / r₁` from above, with the constant `C₀` -/
  hupper : a' ≤ C₀ * (a / r₁)
  /-- the middle dimension is comparable to `b / r₁` from below, with the constant `C₀`; this
  is the radius half of (C4), `r₁ b' ≥ C₀⁻¹ b`, and it is what
  `Kakeya.VeryNotSticky.transverseFillTransport` consumes as its hypothesis `hcomp` -/
  hblower : C₀⁻¹ * (b / r₁) ≤ b'
  /-- the middle dimension is comparable to `b / r₁` from above, with the constant `C₀`; this
  is the upper pin on `b'` that the clause
  `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` (O5) demands — without it that clause is refuted at `b' = 1`
  (`Kakeya.VeryNotSticky.false_of_transverseFill_fullness`); a lower pin alone does not
  block that refutation -/
  hbupper : b' ≤ C₀ * (b / r₁)
  /-- the rescaled small scale `δ' = δ / r₁` is at most the short dimension -/
  hδa' : δ / r₁ ≤ a'
  /-- the shading of a plank is contained in it -/
  hshade : ∀ j ∈ bodies', (YP j).shade ⊆ (P j).carrier
  /-- the planks are localized in the Section 6 window `B̄(0, plankBallRadius)` -/
  hwin : Plank.IsWindowedFamily bodies' P
  /-- **The plank of `L_B(W)` is built on the frame of `W` itself** (blueprint
  `plankFrameIdentification`).

  This is the clause that makes the plank angles of blueprint `def:typicalAnglePlank` *equal*
  to the body angles of `Kakeya.VeryNotSticky.axisAngle`, and hence the clause that makes the
  field `Kakeya.VeryNotSticky.TypicalAngleData.hangle` — the display `anglebound`, the only
  form in which `Kakeya.VeryNotSticky.tangentialSlabFibreCount` uses typicality — reachable at
  all.

  Without it the two sides are incomparable. `Kakeya.IsTypicalPlankAngle` measures
  `Kakeya.Prism3D.angle`, i.e. the angle between the planks' `basis 0`; `axisAngle` measures
  the angle between the bodies' `Kakeya.NonSlab.bodyNormal`. An enclosure
  `L_B '' (Wb j).carrier ⊆ (P j).carrier` pins the two only to within an angle `≍ C(C₀) a/b`,
  and the aperture budget of the tangential case has no room for that. What repairs it is that
  `Kakeya.VeryNotSticky.plankWindowEnclosure` accepts a *prescribed* frame and this assembly
  hands it `Kakeya.VeryNotSticky.bodyFrame (Wb j)`, transported unchanged by the homothety
  `L_B`, which does not rotate. With `Kakeya.VeryNotSticky.bodyFrame_zero` the identification
  `(P j).basis 0 = n(Wb j)` is then exact. -/
  hbasis : ∀ j ∈ bodies', (P j).basis = bodyFrame (Wb j)
  /-- `𝕊*` is a subfamily of `𝕎'_B` -/
  hsel : sel ⊆ bodies'
  /-- `𝕊*` retains a `(C^{sel})⁻¹` fraction of the shaded mass -/
  hselRefine : ShadedBody.IsCRefinement sel YP bodies' YP (plankSelectionConstant C₀)⁻¹
  /-- **The rescaling multiplies every shaded volume by `(2 r₁)⁻³`** (blueprint
  `plankRescalingVolume`).

  The normalizing scale is `2 r₁` and not `r₁`: the shaded bodies `Y_{𝕎'_B}(W)` are the
  *enlargements* `N_{τ₂(W)}(W)` of the geometric bodies of (C4), and those do not fit in
  `B̄(ctr, r₁)` (blueprint `lem:ml2plankEnlargedBall`). Only the clauses that mention the
  rescaling map record the doubled scale; the dimension clauses `hratio`, `hlower`, `hupper`,
  `hblower`, `hbupper` and `hδa'` are unchanged, because by blueprint `lem:ml2thicknessDouble` the
  doubling of the scale is exactly cancelled by the doubling of the comparison constant.

  `L_B` is an exact homothety of ratio `(2 r₁)⁻¹` followed by a translation, so it scales every
  volume by the same factor. This is the only quantitative trace of the transport that a
  consumer of the bundle needs, and it is what lets
  `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` read the fullness obligation (O5) of
  Configuration `hyp:ml2thinsetup`, which the blueprint states in the original coordinates,
  against the plank family, where `ShadedPlank.reduction_to_slab_atTypicalAngle` consumes it.
  The affine map itself is not a parameter of this structure, so the identity is recorded
  rather than the map. -/
  hvol : ∀ j ∈ bodies', volume (YP j).shade * ENNReal.ofReal ((2 * (r₁ : ℝ)) ^ 3) =
    volume (Wsh j).shade
  /-- the enclosure and the rescaling are invisible to `μ` -/
  hmult : ShadedBody.multiplicity bodies' YP = ShadedBody.multiplicity bodies' Wsh
  /-- the enclosure costs the factor `C_{lem:ml2plankpresentation}(C₀)` in `Δ_max` -/
  hdens : maxDensity bodies' (fun j ↦ (P j).toConvexSpaceBody) ≤
    (plankEnclosureConstant C₀ : ENNReal) * maxDensity bodies' Wb
  /-- a `c`-refinement of `(𝒫, Y_𝒫)`, on any sub-index-set, pulls back to a `c`-refinement of
  `(𝕎'_B, Y_{𝕎'_B})` carrying local volume estimates with it.

  **The fourth clause is the bridge unrolled once** (blueprint `plankRescalingBridge`, second
  level). The transverse case refines *twice* in plank coordinates — once to produce the
  typical angle, and once more inside `ShadedPlank.reduction_to_slab_atTypicalAngle` — and it
  must relate the second pull-back to the *first* one, i.e. to the very family `Y_{𝕎''_B}` the
  bundle `Kakeya.VeryNotSticky.TypicalAngleData` carries. The three clauses above cannot do
  that: they produce `Wsh'` from `YP'` and hide the transporting map behind an `∃ g`, so a
  second application of the same clause produces a family related to a *fresh* map and to the
  original `Wsh`, not to `Wsh'`. The fourth clause is stated relative to the `Wsh'` produced by
  the first, which is what makes the two levels composable.

  It is phrased through the shadings alone — a containment and a mass bound rather than
  `ShadedBody.IsCRefinement` — because at the second level the refining family arrives with
  the *plank* carriers demanded by `ShadedBody.IsRefinement` inside
  `ShadedPlank.reduction_to_slab_atTypicalAngle`, while `YP'` carries the rescaled bodies;
  the two are shading-congruent and nothing else of them is used. -/
  hbridge : ∀ (c : NNReal) (t : Finset ω) (YP' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
    t ⊆ bodies' → ShadedBody.IsCRefinement t YP' bodies' YP c →
      ∃ Wsh' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)),
        ShadedBody.IsCRefinement t Wsh' bodies' Wsh c ∧
        (∃ g : EuclideanSpace ℝ (Fin 3) ≃ EuclideanSpace ℝ (Fin 3),
          ∀ i ∈ t, (Wsh' i).shade = g '' (YP' i).shade) ∧
        (∀ (x' : EuclideanSpace ℝ (Fin 3)) (r' R' : ℝ) (K : ENNReal),
          K * volume (closedBall x' r') ≤ volume (iUnionShade t YP' ∩ closedBall x' R') →
          ∃ x : EuclideanSpace ℝ (Fin 3),
            K * volume (ball x (2 * (r₁ : ℝ) * r')) ≤
              volume (iUnionShade t Wsh' ∩ ball x (2 * (r₁ : ℝ) * R'))) ∧
        ∀ (c₂ : NNReal) (t₂ : Finset ω) (Z : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
          t₂ ⊆ t → (∀ i ∈ t₂, (Z i).shade ⊆ (YP' i).shade) →
          (c₂ : ENNReal) * (∑ i ∈ t, volume (YP' i).shade) ≤ ∑ i ∈ t₂, volume (Z i).shade →
          ∃ Z' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)),
            ShadedBody.IsCRefinement t₂ Z' t Wsh' c₂ ∧
            (∀ i ∈ t₂, (Z' i).shade ⊆ (Wsh' i).shade) ∧
            ∀ (x' : EuclideanSpace ℝ (Fin 3)) (r' R' : ℝ) (K : ENNReal),
              K * volume (closedBall x' r') ≤ volume (iUnionShade t₂ Z ∩ closedBall x' R') →
              ∃ x : EuclideanSpace ℝ (Fin 3),
                K * volume (ball x (2 * (r₁ : ℝ) * r')) ≤
                  volume (iUnionShade t₂ Z' ∩ ball x (2 * (r₁ : ℝ) * R'))

/-- **The rescaling bridge, unrolled once** (blueprint `plankRescalingBridge`, second level).

The fourth clause of `Kakeya.VeryNotSticky.PlankPresentationData.hbridge`, isolated: given the
first pull-back `Wsh'` of `YP'`, whose shadings are related by the fixed affine map
`L_B⁻¹ = (plankRescale ctr _).symm`, a further refinement `Z` of `YP'` — recorded through its
shadings alone, since at the call site it arrives with the plank carriers that
`ShadedPlank.reduction_to_slab_atTypicalAngle` produces — pulls back to a `c₂`-refinement `Z'`
of `(t, Wsh')` transporting local volume estimates, exactly as the first level does.

Every step is the first level's: `Kakeya.VeryNotSticky.volume_plankRescale_symm_image` for the
mass comparison, which is exact because `L_B⁻¹` multiplies every volume by the same `r₁³`, and
`Kakeya.VeryNotSticky.plankRescalingBridge` for the transport of the ball estimate. -/
theorem exists_secondRefinement_of_plankRescale {ω : Type*} (ctr : EuclideanSpace ℝ (Fin 3))
    {r₁ : ℝ} (hr₁ : 0 < r₁) {t t₂ : Finset ω}
    (YP' Wsh' Z : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hshp : ∀ i ∈ t, (Wsh' i).shade = (plankRescale ctr hr₁.ne').symm '' (YP' i).shade)
    {c₂ : NNReal} (ht₂ : t₂ ⊆ t)
    (hZsub : ∀ i ∈ t₂, (Z i).shade ⊆ (YP' i).shade)
    (hZmass : (c₂ : ENNReal) * (∑ i ∈ t, volume (YP' i).shade) ≤
      ∑ i ∈ t₂, volume (Z i).shade) :
    ∃ Z' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ i ∈ t₂, (Z' i).shade = (plankRescale ctr hr₁.ne').symm '' (Z i).shade) ∧
      ShadedBody.IsCRefinement t₂ Z' t Wsh' c₂ := by
  classical
  let Z' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i =>
    if hi : i ∈ t₂ then
      { toConvexSpaceBody := (Wsh' i).toConvexSpaceBody,
        shade := (plankRescale ctr hr₁.ne').symm '' (Z i).shade,
        measurableSet_shade :=
          (plankRescale_symm_measurableEmbedding ctr hr₁.ne').measurableSet_image'
            (Z i).measurableSet_shade,
        shade_subset := by
          calc
            (plankRescale ctr hr₁.ne').symm '' (Z i).shade ⊆
                (plankRescale ctr hr₁.ne').symm '' (YP' i).shade := by
              exact Set.image_mono (hZsub i hi)
            _ = (Wsh' i).shade := by
              rw [← hshp i (ht₂ hi)]
            _ ⊆ (Wsh' i).carrier := (Wsh' i).shade_subset }
    else Wsh' i
  have hZ'def : ∀ i ∈ t₂, (Z' i).shade = (plankRescale ctr hr₁.ne').symm '' (Z i).shade := by
    intro i hi
    simp [Z', hi]
  have hZ'sub : ∀ i ∈ t₂, (Z' i).shade ⊆ (Wsh' i).shade := by
    intro i hi
    rw [hZ'def i hi]
    calc
      (plankRescale ctr hr₁.ne').symm '' (Z i).shade ⊆
          (plankRescale ctr hr₁.ne').symm '' (YP' i).shade := by
        exact Set.image_mono (hZsub i hi)
      _ = (Wsh' i).shade := by
        rw [← hshp i (ht₂ hi)]
  refine ⟨Z', hZ'def, ?_⟩
  constructor
  · constructor
    · exact ht₂
    · intro i hi
      constructor
      · simp [Z', hi]
      · exact hZ'sub i hi
  · have hvolW : (∑ i ∈ t, volume ((Wsh' i).shade)) =
      ENNReal.ofReal (r₁ ^ 3) * (∑ i ∈ t, volume ((YP' i).shade)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hshp i hi]
      exact volume_plankRescale_symm_image ctr hr₁ ((YP' i).shade)
    have hvolZ : (∑ i ∈ t₂, volume ((Z' i).shade)) =
      ENNReal.ofReal (r₁ ^ 3) * (∑ i ∈ t₂, volume ((Z i).shade)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hZ'def i hi]
      exact volume_plankRescale_symm_image ctr hr₁ ((Z i).shade)
    rw [hvolW, hvolZ, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hZmass (by positivity : 0 ≤ ENNReal.ofReal (r₁ ^ 3))

/-- **The rescaling bridge, unrolled once, in the form the structure field carries.**

`Kakeya.VeryNotSticky.exists_secondRefinement_of_plankRescale` followed by
`Kakeya.VeryNotSticky.plankRescalingBridge` at the second level. -/
theorem plankRescalingBridge_second {ω : Type*} (ctr : EuclideanSpace ℝ (Fin 3)) {r₁ : ℝ}
    (hr₁ : 0 < r₁) {t : Finset ω}
    (YP' Wsh' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hshp : ∀ i ∈ t, (Wsh' i).shade = (plankRescale ctr hr₁.ne').symm '' (YP' i).shade) :
    ∀ (c₂ : NNReal) (t₂ : Finset ω) (Z : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      t₂ ⊆ t → (∀ i ∈ t₂, (Z i).shade ⊆ (YP' i).shade) →
      (c₂ : ENNReal) * (∑ i ∈ t, volume (YP' i).shade) ≤ ∑ i ∈ t₂, volume (Z i).shade →
      ∃ Z' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)),
        ShadedBody.IsCRefinement t₂ Z' t Wsh' c₂ ∧
        (∀ i ∈ t₂, (Z' i).shade ⊆ (Wsh' i).shade) ∧
        ∀ (x' : EuclideanSpace ℝ (Fin 3)) (r' R' : ℝ) (K : ENNReal),
          K * volume (closedBall x' r') ≤ volume (iUnionShade t₂ Z ∩ closedBall x' R') →
          ∃ x : EuclideanSpace ℝ (Fin 3),
            K * volume (ball x (r₁ * r')) ≤
              volume (iUnionShade t₂ Z' ∩ ball x (r₁ * R')) := by
  classical
  intro c₂ t₂ Z ht₂ hZsub hZmass
  obtain ⟨Z', hZ'shade, hZ'ref⟩ :=
    exists_secondRefinement_of_plankRescale ctr hr₁ YP' Wsh' Z hshp ht₂ hZsub hZmass
  refine ⟨Z', hZ'ref, fun i hi => ?_, fun x' r' R' K hK => ?_⟩
  · rw [hZ'shade i hi, hshp i (ht₂ hi)]
    exact Set.image_mono (hZsub i hi)
  · exact ⟨(plankRescale ctr hr₁.ne').symm x',
      plankRescalingBridge ctr hr₁ (s := t₂) Z Z' hZ'shade x' r' R' K hK⟩

/-! ### Attaching a shading to a plank family

`ShadedPlank.reduction_to_slab_atTypicalAngle` consumes a plank family *with its shading
attached* (`ShadedPlank`), and its refinement hypothesis `ShadedBody.IsCRefinement` demands
the carriers of the refining family to be *equal* to the planks. The plank presentation of
blueprint `lem:ml2plankpresentation` produces a bare plank family `𝒫` and a shading `Y_𝒫`
carried by the *rescaled bodies*, so both objects have to be re-carried once. The two
definitions below do exactly that, and nothing else: outside the index set on which the
shading is known to sit inside the plank they shade nothing, which is the only way to make
`ShadedBody.shade_subset` unconditional. -/

open Classical in
/-- **A plank family with a shading attached** `(𝒫, Y_𝒫)`: the planks of `P` carrying the
shadings of `Y`, which the hypothesis `hsub` places inside them. Off `s` the shading is
emptied, since that is where `hsub` says nothing; every statement about the family quantifies
over `i ∈ s`. -/
noncomputable def shadedPlankOf {ω : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ω → Plank a b hab hb1) (Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset ω) (hsub : ∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) :
    ω → ShadedPlank a b hab hb1 := fun i =>
  { toPrism3D := P i
    shade := if i ∈ s then (Y i).shade else ∅
    measurableSet_shade := by
      split_ifs with h
      · exact (Y i).measurableSet_shade
      · exact MeasurableSet.empty
    shade_subset := by
      split_ifs with h
      · simpa using hsub i h
      · exact Set.empty_subset _ }

/-- The planks of the shaded plank family are the given ones. -/
lemma shadedPlankOf_planks {ω : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ω → Plank a b hab hb1) (Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset ω) (hsub : ∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) :
    ShadedPlank.planks (shadedPlankOf P Y s hsub) = P := by
  funext i
  rfl

/-- The shadings of the shaded plank family agree with the given ones on `s`. -/
lemma shadedPlankOf_shade {ω : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ω → Plank a b hab hb1) (Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset ω) (hsub : ∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) :
    ∀ i ∈ s, (ShadedPlank.bodies (shadedPlankOf P Y s hsub) i).shade = (Y i).shade := by
  intro i hi
  classical
  change (if i ∈ s then (Y i).shade else ∅) = (Y i).shade
  simp [hi]

/-- **The rescaling multiplies every shaded volume by `r₁⁻³`** (blueprint
`plankRescalingVolume`).

`L_B` is an exact homothety of ratio `r₁⁻¹` followed by a translation, so it divides every
volume by `r₁³`; this is the identity recorded as
`Kakeya.VeryNotSticky.PlankPresentationData.hvol`. -/
lemma volume_shade_plankRescale (ctr : EuclideanSpace ℝ (Fin 3)) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (W : ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    volume ((W.plankRescale ctr hr₁.ne').shade) * ENNReal.ofReal (r₁ ^ 3) = volume W.shade := by
  have hshade : (W.plankRescale ctr hr₁.ne').shade = plankRescale ctr hr₁.ne' '' W.shade := by
    simp [ShadedBody.plankRescale, ShadedBody.affineImage_shade]
  rw [hshade]
  rw [volume_plankRescale_image ctr hr₁ W.shade]
  have hcombo : ENNReal.ofReal (r₁⁻¹ ^ 3) * ENNReal.ofReal (r₁ ^ 3) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hr₁.le) 3)]
    rw [← mul_pow]
    rw [inv_mul_cancel₀ hr₁.ne']
    rw [one_pow, ENNReal.ofReal_one]
  have hreorder : (ENNReal.ofReal (r₁⁻¹ ^ 3) * volume W.shade) * ENNReal.ofReal (r₁ ^ 3) =
      ENNReal.ofReal (r₁⁻¹ ^ 3) * ENNReal.ofReal (r₁ ^ 3) * volume W.shade := by
    ac_rfl
  rw [hreorder]
  rw [hcombo]
  rw [one_mul]

/-- The carriers of the shaded plank family are the planks'. -/
lemma shadedPlankOf_carrier {ω : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ω → Plank a b hab hb1) (Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset ω) (hsub : ∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) :
    ∀ i, ((shadedPlankOf P Y s hsub i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (P i).carrier := by
  intro i
  rfl

/-- The shaded bodies of the shaded plank family sit on the planks. -/
lemma shadedPlankOf_toConvexSpaceBody {ω : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ω → Plank a b hab hb1) (Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset ω) (hsub : ∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) :
    ∀ i, (ShadedPlank.bodies (shadedPlankOf P Y s hsub) i).toConvexSpaceBody
      = (P i).toConvexSpaceBody := by
  intro i
  rfl

/-- **Presenting the factoring bodies as a plank family** (blueprint
`lem:ml2plankpresentation`).

Let `L_B` be the affine change of variables taking the `r₁`-ball `B` (here the ball of radius
`r₁` centred at `ctr`) to the unit ball, and set `𝒫 = L_B(𝕎'_B)`, `Y_𝒫 = L_B(Y_{𝕎'_B})`,
`a' = a / r₁`, `b' = b / r₁`. By (C4) each `W ∈ 𝕎_B` has affine thicknesses `∼ (r₁, b, a)`,
so `L_B(W)` has affine thicknesses `∼ (1, b', a')`, i.e. is contained in an `a' × b' × 1`
plank with the *same* aspect ratio `a'/b' = a/b` — the ratio the transverse and tangential
cases consume through their hypothesis `hratio`. The dimensions of the plank are only
comparable to `a/r₁` and `b/r₁`, with the constant `C₀` of (C4); this is the content of the
two-sided bound on `a'` below.

The bodies of `𝕎_B` are the blocks of a factoring of `𝕋_B`, hence pairwise essentially
distinct, and an affine map preserves essential distinctness; the containment
`Y_{𝕎'_B}(W) ⊆ W` is part of the construction in blueprint
`factoringAndMultPropCombined`. Since `L_B` multiplies all volumes by the same factor, the
ratio defining `μ` and the ratios defining a `c`-refinement are unchanged, which is the last
clause: a `c`-refinement of `(𝒫, Y_𝒫)` pulls back to a `c`-refinement of
`(𝕎'_B, Y_{𝕎'_B})`.

**The rescaling bridge.** The pull-back of the previous paragraph also transports *local
volume estimates*, and this is the clause the transverse case consumes (blueprint
`plankRescalingBridge`). Writing `Wsh'` for the `c`-refinement of `(𝕎'_B, Y_{𝕎'_B})` produced
from a `c`-refinement `YP'` of `(𝒫, Y_𝒫)`, then for every centre `x'`, every *pair* of radii
`r'`, `s'` and every `K ∈ [0, ∞]`,

`K |B̄(x', r')| ≤ |U(𝒫', Y_{𝒫'}) ∩ B̄(x', s')|` implies
`∃ x, K |B(x, r₁ r')| ≤ |U(𝕎''', Y_{𝕎'''}) ∩ B(x, r₁ s')|`.

Two radii appear because the estimate to be transported — Item 1 of
`ShadedPlank.reduction_to_slab` — compares the volume of a ball of one radius with the shaded
mass in a concentric ball of a *larger* one. No comparison constant is lost: `L_B` is an exact
homothety of ratio `r₁⁻¹` followed by a translation, so it multiplies every volume by the same
factor `r₁³` and the ratio `K` is preserved exactly. The constant `C₀` of (C4) enters only
through the *dimensions*, `r₁ b' ∈ [C₀⁻¹ b, C₀ b]`, so a radius `r'` comparable to `θ b'`
transports to a radius comparable to `θ b`, and not to `θ b` itself; this is why
`Kakeya.VeryNotSticky.transverseFill` asks for its conclusion at *some* radius `r ≥ θ b`.
The hypothesis is stated for closed balls and the conclusion for open ones, which is what the
consumer needs and costs nothing, spheres being Lebesgue null in `ℝ³`.

The affine change of variables is `L_B = (· - ctr) ∘ (homothety ctr r₁⁻¹)`, i.e. a homothety
followed by a translation, so the statement is the composition of six independent facts, each
of which is now available as its own lemma:

* `ShadedBody.affineImage` / `ShadedBody.homothety` construct `L_B(Y_{𝕎'_B})`; only
  `ShadedBody.vadd` and `ShadedBody.translate` existed before;
* `IsEssentiallyDistinct.image_homothety` (with `IsEssentiallyDistinct.image_add_left` for the
  translation part) gives the essential-distinctness clause;
* `ShadedBody.multiplicity_homothety` (with `ShadedBody.multiplicity_translate_const`) gives
  `μ(𝒫, Y_𝒫) = μ(𝕎'_B, Y_{𝕎'_B})`;
* `ShadedBody.IsCRefinement.comap_homothety` gives the last clause, in the pull-back
  direction; note that `ShadedBody.IsRefinement` demands the carriers to be *equal*, which is
  why the statement produces a shading on the very bodies `Wb j`;
* `Kakeya.maxDensity_homothety` transfers `Δ_max(𝕎_B)` to the plank family, which is what
  `Kakeya.VeryNotSticky.plankCard` consumes through its `hdens`; the passage from the
  transported bodies to the planks containing them costs the factor
  `Kakeya.VeryNotSticky.plankEnclosureConstant C₀` of
  `Kakeya.maxDensity_le_of_carrier_subset`, exactly as in
  `Kakeya.VeryNotSticky.slabPrismEnclosure`;
* `Prism3D.exists_superset_of_hasThicknesses` turns the transported body, whose affine
  thicknesses are `∼ (1, b/r₁, a/r₁)` by `LipschitzWith.ethickness_image_le` applied to `L_B`
  and to `L_B⁻¹` (together with `Metric.ethickness_thickness'`), into an `a' × b' × 1` plank
  containing it.

**The two clauses `plankCard` consumes.** `Kakeya.VeryNotSticky.plankCard` needs to know both
where the planks live and how densely they are packed, and neither is recoverable from the
clauses above; they are therefore part of the conclusion.

* *Localization.* The planks lie in `B̄(0, plankBallRadius)`, not in the unit ball: `L_B(W)`
  does lie in `B̄(0,1)` by `hin`, but the plank is a superset of it. See
  `Kakeya.VeryNotSticky.plankBallRadius` for the elementary bound, and for why the enlargement
  is free downstream. The clause is stated as `Plank.IsWindowedFamily` rather than as a bare
  containment, because `plankBallRadius` derives from `Plank.windowRadius`: it is in this form that
  `ShadedPlank.reduction_to_slab` consumes it, and stating it at any larger radius would leave
  that hypothesis undischarged.
* *Density.* `Δ_max(𝒫) ≤ C_{lem:ml2plankpresentation}(C₀) Δ_max(𝕎'_B)`, which is
  `Kakeya.maxDensity_homothety` for the rescaling followed by
  `Kakeya.maxDensity_le_of_carrier_subset` for the enclosure. Note that this is an inequality
  and not the equality that holds for `μ`: `μ` sees only the shadings, which the enclosure does
  not touch, whereas `Δ_max` sees the carriers, which it enlarges. Composed with (C4)'s
  `Kakeya.VeryNotSticky.BallData.bodies_antiClustering` — through
  `Kakeya.maxDensity_mono` along `bodies'_subset` — it gives the plank family the
  unconditional density bound `Δ_max(𝒫) ≤ C(C₀) C_bias δ^{-2ϱ}` that
  `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` feeds to `plankCard`.

**Two families, and the doubled scale.** The shaded bodies `Y_{𝕎'_B}(W)` of the corrected
factoring proposition are *enlargements* `N_{τ₂(W)}(W)` of the geometric bodies of (C4), not the
bodies themselves; that is the sandwich `hWbW` / `hWcth`, which replaces the former (false)
equality `(Wsh j).toConvexSpaceBody = Wb j`. Two consequences shape the assembly.

* *Two families are passed to `Kakeya.VeryNotSticky.plankFamilyEnclosure`.* The planks must
  enclose the **enlarged** carriers, since it is their shadings that are transported; but
  pairwise essential distinctness is available only for the **geometric** bodies and is in
  general false for their neighbourhoods. So the enclosure family is
  `fun j ↦ (Wsh j).toConvexSpaceBody.plankRescale …` and the essentially-distinct core family
  is `fun j ↦ (Wb j).plankRescale …`, related by `hK₀K` from `hWbW`. Nothing is lost: the
  selection only ever needs *some* large essentially distinct core inside each plank.
* *The normalizing scale is `2 r₁`, not `r₁`.* By `Kakeya.VeryNotSticky.scale_le_of_hasThicknesses`
  the enlargement radius is at most `C₀ a ≤ C₀ b ≤ r₁`, so the enlarged carriers lie in
  `B̄(ctr, 2 r₁)` (`Kakeya.VeryNotSticky.enlarged_subset_closedBall`) and in no smaller ball of
  the form `B̄(ctr, r₁)`; the long half-width of a `Kakeya.Plank` is fixed at `1`, so no choice
  of plank dimensions could compensate. **The plank dimensions do not move**: the geometry runs
  at the doubled comparison constant `2 C₀` (`Kakeya.VeryNotSticky.hasThicknesses_double`) and
  the doubled scale `2 r₁`, and `2 C₀ · (a / (2 r₁)) = C₀ a / r₁ = a'`, so the two doublings
  cancel. The selection keeps the constants of (C4), because
  `Kakeya.VeryNotSticky.enclosureVolumeConstant_two_le_plankEnclosureConstant` absorbs the
  doubled geometric constant into `plankEnclosureConstant C₀`. Only the clauses of
  `Kakeya.VeryNotSticky.PlankPresentationData` that mention the rescaling map —
  `hvol` and `hbridge` — record the doubled scale.

**The two obligations.** Two hypotheses of the assembly are *not* supplied by Configurations
`hyp:ml2setup` and `hyp:ml2thinsetup`, and are carried here as explicit hypotheses rather than
silently assumed (blueprint, note following `lem:ml2plankpresentation`).

* (O1) is `hbr₁`, stated in the sharpened form `C₀ * b ≤ r₁` rather than `b ≤ r₁`: the middle
  thickness of `L_B(W)` is only known to be at most `C₀ * (b / r₁)`, so `b ≤ r₁` alone does not
  give `b' ≤ 1`, which the type `Plank a' b'` requires. Together with `1 ≤ C₀` it implies
  `b ≤ r₁`. At the call site it is a smallness condition on `δ`, since `b ≤ δ^{2 exscal}` and
  `r₁ = δ^{exscal}`.
* (O2) is `hUpos`, the positivity `|U(𝕎'_B, Y_{𝕎'_B})| > 0`. It is the side condition of
  `Kakeya.VeryNotSticky.multiplicity_plankRescale`, and it is the *only* route to the field
  `PlankPresentationData.hmult`; without it that field is unreachable. By `UTY` the shaded
  union is `⋃_W Y_{𝕎'_B}(W)`, so the condition says exactly that some shading has positive
  measure. -/
theorem plankPresentation {ω : Type*} (bodies' : Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Wsh : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {a b r₁ δ C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hbr₁ : C₀ * b ≤ r₁) (hr₁ : 0 < r₁)
    (ctr : EuclideanSpace ℝ (Fin 3))
    (hin : ∀ j ∈ bodies', (Wb j).carrier ⊆ closedBall ctr (r₁ : ℝ))
    (hthick : ∀ j ∈ bodies', HasThicknesses (Wb j).carrier C₀ ![(r₁ : ℝ), b, a])
    (hWbW : ∀ j ∈ bodies', Wb j ≤ (Wsh j).toConvexSpaceBody)
    (hWcth : ∀ j ∈ bodies',
      (Wsh j).toConvexSpaceBody ≤ (Wb j).cthickening (Wb j).scale)
    (hUpos : 0 < volume (ShadedBody.iUnionShade bodies' Wsh)) :
    Nonempty (PlankPresentationData bodies' Wb Wsh a b r₁ δ C₀) := by
  classical
  let E₃ : Type := EuclideanSpace ℝ (Fin 3)
  have hr₁R : (0 : ℝ) < (r₁ : ℝ) := NNReal.coe_pos.mpr hr₁
  have hr₁nz : (r₁ : ℝ) ≠ 0 := hr₁R.ne'
  have hρ : (0 : NNReal) < 2 * r₁ := by positivity
  have hρR : (0 : ℝ) < ((2 * r₁ : NNReal) : ℝ) := NNReal.coe_pos.mpr hρ
  have hρnz : ((2 * r₁ : NNReal) : ℝ) ≠ 0 := hρR.ne'
  have hρcast : ((2 * r₁ : NNReal) : ℝ) = 2 * (r₁ : ℝ) := by push_cast; ring
  let a' : NNReal := C₀ * a / r₁
  let b' : NNReal := C₀ * b / r₁
  have hab' : a' ≤ b' := by
    dsimp [a', b']
    exact plankDimensions_le hab
  have hb1' : b' ≤ 1 := by
    dsimp [b']
    exact plankDimensions_le_one hr₁ hbr₁
  -- The admissible-dimensions bundle for the enclosure.
  have hdim : IsAdmissiblePlankDimensions C₀ a b r₁ a' b' := by
    refine ⟨?_, hab', hb1', ?_, ?_⟩
    · dsimp [a']
      exact plankDimensions_pos hC₀ hr₁ hδ hδa
    · dsimp [a']
      rw [← NNReal.coe_le_coe]
      norm_num [NNReal.coe_div, NNReal.coe_mul]
      exact le_of_eq (by ring)
    · dsimp [b']
      rw [← NNReal.coe_le_coe]
      norm_num [NNReal.coe_div, NNReal.coe_mul]
      exact le_of_eq (by ring)
  -- The real coercions of the dimensions, for the volume and density steps.
  have haa' : (a' : ℝ) = C₀ * ((a : ℝ) / r₁) := by
    dsimp [a']
    ring
  have hbb' : (b' : ℝ) = C₀ * ((b : ℝ) / r₁) := by
    dsimp [b']
    ring
  have hCa : C₀ * a ≤ r₁ := le_trans (by gcongr) hbr₁
  have hsum : r₁ + C₀ * a ≤ 2 * r₁ := by
    rw [two_mul]
    exact add_le_add le_rfl hCa
  -- The enlarged bodies `V = 𝕎'_B` and the rescaled (doubled) carriers.
  let V : ω → ConvexSpaceBody E₃ := fun j => (Wsh j).toConvexSpaceBody
  obtain ⟨hVcth, hK1⟩ := plankRescaledFamilyEnlarged_subset_closedBall bodies' Wb V
    hr₁ hρ hsum ctr hin hthick hWcth
  let rV : ω → ConvexSpaceBody E₃ := fun j => (V j).plankRescale ctr hρnz
  let rW : ω → ConvexSpaceBody E₃ := fun j => (Wb j).plankRescale ctr hρnz
  let YP : ω → ShadedBody E₃ := fun j => (Wsh j).plankRescale ctr hρnz
  have hspreadR : ∀ j ∈ bodies', ∀ x ∈ ((rV j).carrier : Set E₃), ∀ u ∈ ((rV j).carrier : Set E₃),
      |(bodyFrame (Wb j)).repr (x - u) 0| ≤ 2 * (a' : ℝ) ∧
      |(bodyFrame (Wb j)).repr (x - u) 1| ≤ 2 * (b' : ℝ) := by
    simpa [rV, a', b'] using
      (plankRescaledFamilyEnlarged_spread bodies' Wb V hC₀ hab hr₁ hρ le_rfl ctr hthick hVcth)
  have hK₀K : ∀ j ∈ bodies', ((rW j).carrier : Set E₃) ⊆ ((rV j).carrier : Set E₃) := by
    intro j hj
    simp only [rW, rV, V, ConvexSpaceBody.plankRescale]
    exact Set.image_mono (SetLike.coe_subset_coe.mpr (hWbW j hj))
  -- `Y_𝒫(P) = L_B(Y_{𝕎'_B}(W)) ⊆ L_B(W) ⊆ P`.
  have hKvol : ∀ j ∈ bodies', 8 * (a' : ENNReal) * b' ≤
      (plankEnclosureConstant C₀ : ENNReal) * volume ((rW j).carrier : Set E₃) := by
    intro j hj
    have hQ : 8 * (a' : ENNReal) * b' =
        volume ((Prism3D.std a' b' (1 : NNReal) hab' hb1').carrier : Set E₃) := by
      rw [Prism3D.volume_carrier]
      simp
    rw [hQ]
    simpa [rW] using (plankEnclosureVolume_double hC₀ hr₁ hρ ctr (Wb j) (hthick j hj)
      haa' hbb' hab' hb1' (Prism3D.std a' b' (1 : NNReal) hab' hb1'))
  rcases plankFamilyEnclosure hC₀ hC₀ le_rfl hr₁ hab hdim bodies' rV rW hK₀K hK1
      (fun j => bodyFrame (Wb j)) hspreadR hKvol
      (fun j => volume (YP j).shade) with ⟨P, sel, hsel, hKP, hwin, hbasisP, hweight⟩
  have hshade_P : ∀ j ∈ bodies', (YP j).shade ⊆ (P j).carrier := by
    intro j hj
    calc
      (YP j).shade = plankRescale ctr hρnz '' (Wsh j).shade := by
        simp only [YP, ShadedBody.plankRescale, ShadedBody.affineImage_shade, plankRescale_apply]
        exact Set.image_congr (by intro y hy; exact plankRescale_apply ctr hρnz y)
      _ ⊆ plankRescale ctr hρnz '' (Wsh j).carrier := Set.image_mono (Wsh j).shade_subset
      _ = (rV j).carrier := by simp [rV, V, ConvexSpaceBody.plankRescale]
      _ ⊆ (P j).carrier := hKP j hj
  -- The selection is a `(C^sel)⁻¹`-refinement of `(𝒫, Y_𝒫)`.
  have hselRefine : ShadedBody.IsCRefinement sel YP bodies' YP (plankSelectionConstant C₀)⁻¹ := by
    constructor
    · constructor
      · exact hsel
      · intro i hi
        exact ⟨rfl, Subset.rfl⟩
    · have hsel0 : plankSelectionConstant C₀ ≠ 0 :=
        (lt_of_lt_of_le (show (0 : NNReal) < 1 by norm_num)
          (one_le_plankSelectionConstant C₀)).ne'
      simpa [ENNReal.coe_inv hsel0] using hweight
  -- The multiplicity is unchanged by the transport.
  have hmult : ShadedBody.multiplicity bodies' YP = ShadedBody.multiplicity bodies' Wsh := by
    simpa [YP] using (multiplicity_plankRescale ctr hρnz bodies' Wsh hUpos)
  -- The density of the family (rescaling free, enclosure costs `C(C₀)`).
  have hdens : maxDensity bodies' (fun j => (P j).toConvexSpaceBody) ≤
      (plankEnclosureConstant C₀ : ENNReal) * maxDensity bodies' Wb := by
    have hsub : ∀ j ∈ bodies', plankRescale ctr hρnz '' ((Wb j).carrier : Set E₃) ⊆
        (P j).carrier := by
      intro j hj
      refine Set.Subset.trans ?_ (hKP j hj)
      simpa [rW, rV, V, ConvexSpaceBody.plankRescale] using hK₀K j hj
    simpa [rW] using (plankDensity_double hC₀ hr₁ hρ hab ctr bodies' Wb hthick haa' hbb'
      hab' hb1' P hsub)
  -- The rescaling bridge.
  have hbridge :
      ∀ (c : NNReal) (t : Finset ω) (YP' : ω → ShadedBody E₃),
        t ⊆ bodies' → ShadedBody.IsCRefinement t YP' bodies' YP c →
          ∃ Wsh' : ω → ShadedBody E₃,
            ShadedBody.IsCRefinement t Wsh' bodies' Wsh c ∧
            (∃ g : E₃ ≃ E₃, ∀ i ∈ t, (Wsh' i).shade = g '' (YP' i).shade) ∧
            (∀ (x' : E₃) (r' R' : ℝ) (K : ENNReal),
              K * volume (closedBall x' r') ≤ volume (iUnionShade t YP' ∩ closedBall x' R') →
              ∃ x : E₃, K * volume (ball x (((2 * r₁ : NNReal) : ℝ) * r')) ≤
                volume (iUnionShade t Wsh' ∩ ball x (((2 * r₁ : NNReal) : ℝ) * R'))) ∧
            ∀ (c₂ : NNReal) (t₂ : Finset ω) (Z : ω → ShadedBody E₃),
              t₂ ⊆ t → (∀ i ∈ t₂, (Z i).shade ⊆ (YP' i).shade) →
              (c₂ : ENNReal) * (∑ i ∈ t, volume (YP' i).shade) ≤ ∑ i ∈ t₂, volume (Z i).shade →
              ∃ Z' : ω → ShadedBody E₃,
                ShadedBody.IsCRefinement t₂ Z' t Wsh' c₂ ∧
                (∀ i ∈ t₂, (Z' i).shade ⊆ (Wsh' i).shade) ∧
                ∀ (x' : E₃) (r' R' : ℝ) (K : ENNReal),
                  K * volume (closedBall x' r') ≤ volume (iUnionShade t₂ Z ∩ closedBall x' R') →
                  ∃ x : E₃, K * volume (ball x (((2 * r₁ : NNReal) : ℝ) * r')) ≤
                    volume (iUnionShade t₂ Z' ∩ ball x (((2 * r₁ : NNReal) : ℝ) * R')) := by
    intro c t YP' ht href
    have hYPcarrier : ∀ i ∈ bodies', (YP i).toConvexSpaceBody = rV i := by
      intro i hi
      simp [YP, rV, V, ShadedBody.plankRescale, ShadedBody.affineImage,
        ConvexSpaceBody.plankRescale]
    have hYPshade : ∀ i ∈ bodies', (YP i).shade = plankRescale ctr hρnz '' (Wsh i).shade := by
      intro i hi
      simp only [YP, ShadedBody.plankRescale, ShadedBody.affineImage_shade,
        plankRescale_apply]
      exact Set.image_congr (by intro y hy; exact plankRescale_apply ctr hρnz y)
    have hPW : ∀ i ∈ bodies', plankRescale ctr hρnz '' (Wsh i).carrier ⊆ (rV i).carrier := by
      intro i hi
      simp [rV, V, ConvexSpaceBody.plankRescale]
    rcases exists_isCRefinement_of_plankRescale ctr hρnz (W := Wsh) (P := rV) hPW (YP := YP)
        hYPcarrier hYPshade (YP' := YP') href with ⟨Wsh', _hcar, hshp, href'⟩
    refine ⟨Wsh', href', ⟨(plankRescale ctr hρnz).symm.toEquiv, ?_⟩, ?_,
      plankRescalingBridge_second ctr hρR YP' Wsh' hshp⟩
    · intro i hi
      change (Wsh' i).shade = (plankRescale ctr hρnz).symm '' (YP' i).shade
      exact hshp i hi
    · intro x' r' R' K hK
      refine ⟨(plankRescale ctr hρnz).symm x', ?_⟩
      exact plankRescalingBridge ctr hρR YP' Wsh' hshp x' r' R' K hK
  -- Assemble the structure.
  exact ⟨{ a' := a', b' := b', hab' := hab', hb1' := hb1', P := P, YP := YP, sel := sel,
            hratio := by
              dsimp [a', b']
              exact plankDimensions_ratio hC₀ hr₁ hδ hδa hab,
            hlower := by
              dsimp [a']
              exact plankDimensions_lower hC₀,
            hupper := by
              dsimp [a']
              rw [← NNReal.coe_le_coe]
              norm_num [NNReal.coe_div, NNReal.coe_mul]
              exact le_of_eq (by ring),
            hblower := by
              dsimp [b']
              exact plankDimensions_lower hC₀,
            hbupper := by
              dsimp [b']
              rw [← NNReal.coe_le_coe]
              norm_num [NNReal.coe_div, NNReal.coe_mul]
              exact le_of_eq (by ring),
            hδa' := by
              dsimp [a']
              exact plankDimensions_delta_le hC₀ hδa,
            hshade := hshade_P, hwin := hwin, hbasis := hbasisP, hsel := hsel,
            hselRefine := hselRefine,
            hvol := by
              intro j _
              simpa [YP, hρcast] using volume_shade_plankRescale ctr hρR (Wsh j),
            hmult := hmult, hdens := hdens, hbridge := by simpa only [hρcast] using hbridge }⟩

/-! The cardinality data `Kakeya.VeryNotSticky.plankCardExponent` and
`Kakeya.VeryNotSticky.plankCardConstant` of the bound below are declared in
`Kakeya.DimensionThree.MainLemma2.PlankConstants`, upstream of
`Kakeya.VeryNotSticky.CaseScale`, because the eleventh clause of Configuration `hyp:ml2scale`
names them: they are the cardinality data at which the transverse branch invokes the
plank-to-slab reduction. -/

/-- **Polynomial cardinality bound for the plank family** (blueprint `lem:ml2plankcard`).

Cover the ball `B̄(0, plankBallRadius)`, in which the planks of `𝒫` live by the
`Plank.IsWindowedFamily` clause of `Kakeya.VeryNotSticky.plankPresentation` (the hypothesis
`hin` here, `plankBallRadius` deriving from `Plank.windowRadius` by definition), by a family of
`≲ (δ')^{-M}` prisms, where
`M = plankCardExponent = exists_bounded_prism_discretization.M 3`, such that every plank of `𝒫`
lies in one of them (`Kakeya.exists_finite_test_family_maxDensity_closedBall`, applied at
`r = δ' ≤ a'`, which is the smallest affine thickness of a plank, and at `R = plankBallRadius`).
For each such prism `K`, the number of members of `𝒫` contained in `K` is at most
`Δ_max(𝒫)|K|/|P| ≲ Δ_max(𝒫) ≤ Δ`, which is the hypothesis `hdens`. Summing over the cover with
`Finset.card_biUnion_le_card_mul` gives `|𝒫| ≲ Δ (δ')^{-M}`.

**The density bound is an explicit factor, not a threshold.** An earlier version assumed
`Δ_max(𝒫) ≤ (δ')⁻¹` and folded the factor into the exponent. That is not reachable from the
configuration: the only density bound available is
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering`, `Δ_max(𝕎_B) ≤ C_bias δ^{-2ϱ}`,
transported to `𝒫` by `Kakeya.VeryNotSticky.plankPresentation`; and `C_bias` is documented as
possibly depending on `δ`, so `C(C₀) C_bias δ^{-2ϱ} ≤ (δ')⁻¹` is not a fixed-scale condition
and could not be discharged by any field of `Kakeya.VeryNotSticky.CaseScale`. Keeping `Δ` as a
parameter makes the lemma unconditional, and leaves the (genuine, but purely exponential)
conversion `δ^{-2ϱ} = (δ')^{-2ϱ/(1-exscal)} ≤ (δ')^{-4ϱ}` — valid since `exscal < 1/2` by
`params.scale` — to the caller, where `r₁ = δ^{exscal}` is in scope.

This is the cardinality bridge required by
`Kakeya.findingTypicalAngleOfIntersection_perScale`, whose hypothesis `hcard` is exactly a bound
of this shape; the caller instantiates its `N` at
`plankCardExponent + 4ϱ` and its constant at `plankCardConstant * C(C₀) * C_bias`, both fixed
before the family. The conclusion is stated in `ℝ≥0` and not in `ℝ` for that reason: `hcard`
reads `(s.card : ℝ≥0) ≤ C₀ * δ ^ (-N)`, so the two match without a coercion lemma. -/
theorem plankCard {ω : Type*} (t : Finset ω) {a' b' δ' Δ : NNReal} {hab' : a' ≤ b'}
    {hb1' : b' ≤ 1} (P : ω → Plank a' b' hab' hb1') (hδ' : 0 < δ') (hδa' : δ' ≤ a')
    (hin : Plank.IsWindowedFamily t P)
    (hdens : maxDensity t (fun j ↦ (P j).toConvexSpaceBody) ≤ (Δ : ENNReal)) :
    (t.card : NNReal) ≤ plankCardConstant * Δ * δ' ^ (-plankCardExponent) := by
  classical
  -- The window ball containing every plank, as a convex body.
  let K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := Kakeya.plankWindow
  have hwin : ∀ j, j ∈ t → (P j).toConvexSpaceBody ≤ K := by
    intro j hj
    have hsub : ((P j).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (K : Set (EuclideanSpace ℝ (Fin 3))) := by
      exact hin j hj
    exact SetLike.coe_subset_coe.mp hsub
  -- Volume of the Section 6 window (radius `Plank.windowRadius = 4`) is at most 512.
  have hBK : volume K.carrier ≤ (512 : ENNReal) := by
    change volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) ≤
      (512 : ENNReal)
    have hR : Plank.windowRadius = (4 : ℝ) := by norm_num [Plank.windowRadius]
    rw [hR]
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hunit : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ)) ≤
        (8 : ENNReal) := by
      have hc := volume_closedBall_le_two_pow_finrank (E := EuclideanSpace ℝ (Fin 3))
      rw [hfin] at hc
      rw [show (2 : ENNReal) ^ 3 = (8 : ENNReal) by norm_num] at hc
      exact hc
    have hvol4 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (4 : ℝ)) =
        (64 : ENNReal) * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ)) := by
      rw [InnerProductSpace.volume_closedBall, InnerProductSpace.volume_closedBall, hfin]
      norm_num [ENNReal.ofReal_natCast]
    calc volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (4 : ℝ))
        = (64 : ENNReal) * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ)) :=
          hvol4
      _ ≤ (64 : ENNReal) * (8 : ENNReal) := by gcongr
      _ = (512 : ENNReal) := by norm_num
  -- Total plank volume is at most Δ · (volume of the window), from the density bound.
  have hup : (∑ j ∈ t, volume ((P j).toConvexSpaceBody).carrier)
      ≤ (Δ : ENNReal) * volume K.carrier := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hdens (by positivity))
    exact Kakeya.sum_volume_le_maxDensity_mul_volume' (s := t)
      (W := fun j => (P j).toConvexSpaceBody) (K := K) hwin
  -- Each plank has volume exactly 8 · a' · b'.
  have hsum_eq : (∑ j ∈ t, volume ((P j).toConvexSpaceBody).carrier)
      = (t.card : ENNReal) * (8 : ENNReal) * (a' : ENNReal) * (b' : ENNReal) := by
    calc
      (∑ j ∈ t, volume ((P j).toConvexSpaceBody).carrier)
          = ∑ j ∈ t, (8 : ENNReal) * (a' : ENNReal) * (b' : ENNReal) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [Prism3D.volume_carrier (P j)]
            simp
      _ = (t.card : ENNReal) * ((8 : ENNReal) * (a' : ENNReal) * (b' : ENNReal)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (t.card : ENNReal) * (8 : ENNReal) * (a' : ENNReal) * (b' : ENNReal) := by ring
  -- Combine: (t.card · 8 · a' · b') ≤ Δ · 512, in ENNReal.
  have hmain : (t.card : ENNReal) * (8 : ENNReal) * (a' : ENNReal) * (b' : ENNReal)
      ≤ (Δ : ENNReal) * (512 : ENNReal) := by
    rw [← hsum_eq]
    exact hup.trans (mul_le_mul_of_nonneg_left hBK (by positivity : 0 ≤ (Δ : ENNReal)))
  -- Convert to NNReal and finish with a crude absolute constant.
  have hmain_nn : (t.card : NNReal) * (8 : NNReal) * a' * b' ≤ Δ * (512 : NNReal) := by
    exact_mod_cast hmain
  have hgrouped : (t.card : NNReal) * (8 * a' * b') ≤ Δ * (512 : NNReal) := by
    convert hmain_nn using 1
    ring
  have hdim : δ' * δ' ≤ a' * b' := by
    exact mul_le_mul hδa' (le_trans hδa' hab') (by positivity) (by positivity)
  have hδ1 : δ' ≤ 1 := le_trans (le_trans hδa' hab') hb1'
  have hE2 : (2 : ℝ) ≤ plankCardExponent := by unfold plankCardExponent; norm_num
  have hpow_le : δ' ^ (-2 : ℝ) ≤ δ' ^ (-plankCardExponent) := by
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ' hδ1 (by linarith)
  have hle2 : δ' * δ' ≤ 8 * a' * b' := by
    have h8 : (1 : NNReal) ≤ 8 := by norm_num
    have ha8 : a' * b' ≤ 8 * a' * b' := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_right h8 (by positivity : 0 ≤ a' * b'))
    exact hdim.trans ha8
  have hRpos : 0 < 8 * a' * b' := by
    have ha : 0 < a' := lt_of_lt_of_le hδ' hδa'
    have hb : 0 < b' := lt_of_lt_of_le ha hab'
    positivity
  have hinv_le : (8 * a' * b')⁻¹ ≤ δ' ^ (-2 : ℝ) := by
    calc
      (8 * a' * b')⁻¹ ≤ (δ' * δ')⁻¹ :=
        (inv_le_inv₀ hRpos (by positivity : 0 < δ' * δ')).mpr hle2
      _ = δ' ^ (-2 : ℝ) := by
        rw [NNReal.rpow_neg]
        congr 1
        simp [pow_two]
  -- Assemble: t.card ≤ Δ · 512 · δ'^{-E} ≤ plankCardConstant · Δ · δ'^{-E}.
  calc
    (t.card : NNReal)
        ≤ (Δ * (512 : NNReal)) / (8 * a' * b') := (le_div_iff₀ hRpos).mpr hgrouped
    _ = (Δ * (512 : NNReal)) * (8 * a' * b')⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (Δ * (512 : NNReal)) * δ' ^ (-2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hinv_le (by positivity)
    _ ≤ (Δ * (512 : NNReal)) * δ' ^ (-plankCardExponent) := by
          exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ ≤ (plankCardConstant * Δ) * δ' ^ (-plankCardExponent) := by
          have h512 : (512 : NNReal) ≤ plankCardConstant := by norm_num [plankCardConstant]
          have hΔle : Δ * (512 : NNReal) ≤ plankCardConstant * Δ := by
            calc
              Δ * (512 : NNReal) = (512 : NNReal) * Δ := by ring
              _ ≤ plankCardConstant * Δ := mul_le_mul_of_nonneg_right h512 (by positivity : 0 ≤ Δ)
          exact mul_le_mul_of_nonneg_right hΔle (by positivity)
    _ = plankCardConstant * Δ * δ' ^ (-plankCardExponent) := by ring

/-- **Constant in Proposition `lem:ml2typicalangle`** (blueprint
`def:ml2typicalangleConstant`).

`C_{lem:ml2typicalangle}` is the constant `C` produced by
`Kakeya.findingTypicalAngleOfIntersection_perScale` when it is applied, with `ε = η` and with the
small scale `δ' = δ / r₁`, to the plank family of
`Kakeya.VeryNotSticky.plankPresentation`. That lemma binds its constant existentially, so
there is no named function to refer to; what characterises it is that it is *sub-polynomial*
in `(δ')⁻¹`, i.e. `C ⪅ 1` in the sense of `Kakeya.LEApprox`. This predicate records exactly
that property, and it is with respect to such a constant that typicality is measured in
`Kakeya.IsTypicalPlankAngle`.

This multi-scale form is *not* what the single-scale statements below use, and it is
referenced by no statement. `Kakeya.LEApprox` quantifies over a whole family of scales `ρ`, so
at the one fixed scale `δ'` at which
`Kakeya.findingTypicalAngleOfIntersection_perScale` is applied it says nothing; the single-scale
bound `C ≤ (δ')^{-η}`, which is now part of the conclusion of
`Kakeya.findingTypicalAngleOfIntersection_perScale`, supersedes it here and is what makes the
clause `δ^{2η} ≤ c` of `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` reachable. The
definition is kept because it is the faithful rendering of the blueprint's
`C_{lem:ml2typicalangle} ⪅ 1`, and because the assembly of the whole of Main Lemma 2 over a
family of scales will want it. -/
def IsTypicalAngleConstant (C : NNReal → NNReal) : Prop := Kakeya.LEApprox C 1

/-! #### The four pieces of Proposition `lem:ml2typicalangle`

`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` is one application of
`Kakeya.findingTypicalAngleOfIntersection_perScale`, but each of that lemma's hypotheses needs a
small argument of its own, and each is stated here so that the assembly reads as the single
application it is. -/

/-- **The elementary facts about the rescaled small scale `δ' = δ / r₁`.**

All seven are consequences of `r₁ = δ^{exscal}`, of `cfg.hδ`/`cfg.hδ1`, and of the
multiplicity threshold `hmult2`, which is what forces the *strict* inequalities: at `δ' = 1`
one would have `(δ')^{-η} = 1 < 2`. The last one, `exscal < 1`, is then
`δ < r₁ = δ^{exscal}` read with `0 < δ < 1`, and it is what keeps the exponent bookkeeping of
`Kakeya.VeryNotSticky.TypicalAngleData.hc` inside its `2η` budget. -/
theorem typicalAngleScaleFacts (cfg : VeryNotSticky.{u})
    (hmult2 : 2 ≤ ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ^ (-(16 * cfg.η))) :
    0 < cfg.r₁ ∧ cfg.r₁ ≤ 1 ∧ cfg.δ / cfg.r₁ = cfg.δ ^ (1 - cfg.exscal) ∧
      0 < cfg.δ / cfg.r₁ ∧ cfg.δ / cfg.r₁ < 1 ∧ cfg.δ < 1 ∧ cfg.exscal < 1 := by
  -- (a) 0 < r₁ and r₁ ≤ 1 from r₁ = δ^exscal.
  have hr1 : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hr1le1 : cfg.r₁ ≤ 1 := NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le
  -- (b) δ / r₁ = δ^(1-exscal).
  have hdiv : cfg.δ / cfg.r₁ = cfg.δ ^ (1 - cfg.exscal) := by
    unfold r₁
    rw [NNReal.rpow_sub cfg.hδ.ne']
    rw [NNReal.rpow_one]
  -- (c) 0 < δ / r₁.
  have hdivpos : 0 < cfg.δ / cfg.r₁ := div_pos cfg.hδ hr1
  -- (d) δ / r₁ < 1, by contradiction with hmult2.
  have hdivlt1 : cfg.δ / cfg.r₁ < 1 := by
    by_contra hnot
    have hge : 1 ≤ cfg.δ / cfg.r₁ := le_of_not_gt hnot
    have hneg : -(16 * cfg.η) ≤ 0 := by linarith [cfg.hη]
    have hb1 : (1 : ENNReal) ≤ ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) :=
      ENNReal.one_le_coe_iff.mpr hge
    have hpowle : ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ^ (-(16 * cfg.η)) ≤ 1 := by
      simpa using (ENNReal.rpow_le_rpow_of_exponent_le hb1 hneg)
    have hbad : (2 : ENNReal) ≤ 1 := le_trans hmult2 hpowle
    norm_num at hbad
  -- (e) δ < 1.
  have hδr : cfg.δ < cfg.r₁ := (div_lt_one hr1).mp hdivlt1
  have hδlt1 : cfg.δ < 1 := lt_of_lt_of_le hδr hr1le1
  -- (f) exscal < 1.
  have hexscal1 : cfg.exscal < 1 := by
    have hlt : cfg.δ < cfg.δ ^ cfg.exscal := by
      simpa [r₁] using hδr
    have hltR : (cfg.δ : ℝ) < (cfg.δ : ℝ) ^ (cfg.exscal) := by
      exact_mod_cast hlt
    have hδR1 : (cfg.δ : ℝ) < 1 := by exact_mod_cast hδlt1
    have hδR0 : 0 < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
    have hmain : cfg.exscal < (1 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff_of_base_lt_one hδR0 hδR1).mp
        (by simpa [Real.rpow_one] using hltR)
    exact hmain
  exact ⟨hr1, hr1le1, hdiv, hdivpos, hdivlt1, hδlt1, hexscal1⟩

/-- **The plank presentation at a ball of the thin case** (blueprint
`lem:ml2plankpresentation`, read at the data of Configurations `hyp:ml2setup` and
`hyp:ml2thinsetup`).

This is `Kakeya.VeryNotSticky.plankPresentation` with every hypothesis discharged from `cfg`,
`bd` and `tc`: `hin`, `hthick` and `hed` are (C4) restricted along
`ThinCase.ThinBall.bodies'_subset`, the enlargement sandwich `hWbW`/`hWcth` is
`ThinCase.ThinBall.Wb_le_W` / `ThinCase.ThinBall.W_le_cthickening`, the dimension
hypotheses are `cfg.hdims`, and the positivity `hUpos` of the shaded union is
`Kakeya.VeryNotSticky.thinBallPositivity_iUnionShade_pos` at the reflexive refinement. The
only hypothesis that is not supplied by the configuration is (O1), `hbsmall`. -/
theorem exists_plankPresentationData (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hbsmall : bd.C₀ * cfg.b ≤ cfg.r₁) :
    Nonempty (PlankPresentationData (tc.thinBall hB).bodies' bd.Wb (tc.thinBall hB).W
      cfg.a cfg.b cfg.r₁ cfg.δ bd.C₀) := by
  classical
  exact plankPresentation (tc.thinBall hB).bodies' bd.Wb (tc.thinBall hB).W
    bd.hC₀ cfg.hδ cfg.hdims.1 cfg.hdims.2.1 hbsmall (by simpa [r₁] using NNReal.rpow_pos cfg.hδ)
    (bd.ctr B)
    (fun j hj => bd.bodies_subset_ball B hB j ((tc.thinBall hB).bodies'_subset hj))
    (fun j hj => bd.bodies_thickness B hB j ((tc.thinBall hB).bodies'_subset hj))
    (tc.thinBall hB).Wb_le_W
    (tc.thinBall hB).W_le_cthickening
    (thinBallPositivity_iUnionShade_pos cfg tc hB zero_lt_one
      (ShadedBody.IsCRefinement.refl (tc.thinBall hB).bodies' (tc.thinBall hB).W))

/-- **The cardinality bridge for the plank family** (blueprint
`lem:ml2typicalangleCardBridge`).

`Kakeya.VeryNotSticky.plankCard` applied to the subfamily `𝕊*` of the presentation, with the
density bound `Δ_max(𝒫) ≤ C_{lem:ml2plankpresentation}(C₀) C_bias δ^{-2ϱ}` obtained from
`PlankPresentationData.hdens` and (C4)'s
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering`, restricted along
`ThinCase.ThinBall.bodies'_subset` by `Kakeya.maxDensity_mono`. This is the hypothesis
`hcard` of `Kakeya.findingTypicalAngleOfIntersection_perScale`, whose constant and exponent are
arguments of that lemma and so may be read off the scale here. -/
theorem typicalAngleCardBridge (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (psd : PlankPresentationData (tc.thinBall hB).bodies' bd.Wb (tc.thinBall hB).W
      cfg.a cfg.b cfg.r₁ cfg.δ bd.C₀) :
    (psd.sel.card : NNReal) ≤
      plankCardConstant * (plankEnclosureConstant bd.C₀ * bd.Cbias *
          cfg.δ ^ (-(2 * cfg.ϱ))) *
        (cfg.δ / cfg.r₁ : NNReal) ^ (-plankCardExponent) := by
  classical
  have hr₁_pos : 0 < cfg.r₁ := by
    unfold r₁
    exact NNReal.rpow_pos cfg.hδ
  have hδ_pos : 0 < cfg.δ := cfg.hδ
  have hδ' : 0 < cfg.δ / cfg.r₁ := by
    positivity
  have hdens_final : maxDensity psd.sel (fun j ↦ (psd.P j).toConvexSpaceBody) ≤
      (plankEnclosureConstant bd.C₀ : ENNReal) * (bd.Cbias : ENNReal) *
        (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by
    calc
      maxDensity psd.sel (fun j ↦ (psd.P j).toConvexSpaceBody)
          ≤ maxDensity (tc.thinBall hB).bodies' (fun j ↦ (psd.P j).toConvexSpaceBody) :=
            maxDensity_mono (fun j ↦ (psd.P j).toConvexSpaceBody) psd.hsel
      _ ≤ (plankEnclosureConstant bd.C₀ : ENNReal) * maxDensity (tc.thinBall hB).bodies' bd.Wb :=
            psd.hdens
      _ ≤ (plankEnclosureConstant bd.C₀ : ENNReal) * maxDensity (bd.bodies B) bd.Wb := by
            exact mul_le_mul_of_nonneg_left
              (maxDensity_mono bd.Wb (tc.thinBall hB).bodies'_subset) (by positivity)
      _ ≤ (plankEnclosureConstant bd.C₀ : ENNReal) *
            ((bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))) := by
            exact mul_le_mul_of_nonneg_left (bd.bodies_antiClustering B hB) (by positivity)
      _ = (plankEnclosureConstant bd.C₀ : ENNReal) * (bd.Cbias : ENNReal) *
            (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by ring
  have hdens_coe :
      ((plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ (-(2 * cfg.ϱ)) : NNReal) : ENNReal) =
      (plankEnclosureConstant bd.C₀ : ENNReal) * (bd.Cbias : ENNReal) *
        (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by
    rw [ENNReal.coe_mul, ENNReal.coe_mul]
    rw [ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne']
  have hdens : maxDensity psd.sel (fun j ↦ (psd.P j).toConvexSpaceBody) ≤
      ((plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ (-(2 * cfg.ϱ)) : NNReal) : ENNReal) := by
    rw [hdens_coe]
    exact hdens_final
  have hin : Plank.IsWindowedFamily psd.sel psd.P := by
    intro i hi
    exact psd.hwin i (psd.hsel hi)
  exact plankCard psd.sel (δ' := cfg.δ / cfg.r₁)
    (Δ := plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ (-(2 * cfg.ϱ)))
    psd.P hδ' psd.hδa' hin hdens

/-- **The factoring multiplicity survives the passage to the essentially distinct subfamily**
(blueprint `lem:ml2plankSubfamilyMult`).

`Kakeya.VeryNotSticky.plankSubfamilyMult` at `Csel = plankSelectionConstant bd.C₀`, using
`PlankPresentationData.hmult` to move the hypothesis from `(𝕎'_B, Y_{𝕎'_B})` to
`(𝒫, Y_𝒫)` and `PlankPresentationData.hselRefine` for the selection. This is the
multiplicity hypothesis of `Kakeya.findingTypicalAngleOfIntersection_perScale` at the rescaled
scale. -/
theorem typicalAngleSelMult (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (psd : PlankPresentationData (tc.thinBall hB).bodies' bd.Wb (tc.thinBall hB).W
      cfg.a cfg.b cfg.r₁ cfg.δ bd.C₀)
    (hsel_thr : (plankSelectionConstant bd.C₀ : ℝ) ≤ (cfg.δ : ℝ) ^ (-(cfg.exscal * cfg.η)))
    (hmult : (cfg.δ : ENNReal) ^ (-(16 * cfg.η)) ≤
      ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W) :
    ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ^ (-(16 * cfg.η)) ≤
      ShadedBody.multiplicity psd.sel psd.YP := by
  -- the selection threshold is stated at `exscal·η`; at the O5 exponent `16η` the predicate
  -- asks only for the weaker `exscal·16η`, which `hsel_thr` gives because `δ ≤ 1`
  have hsel_thr16 :
      (plankSelectionConstant bd.C₀ : ℝ) ≤ (cfg.δ : ℝ) ^ (-(cfg.exscal * (16 * cfg.η))) := by
    refine hsel_thr.trans ?_
    have hδ0 : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
    have hδ1 : (cfg.δ : ℝ) ≤ 1 := by exact_mod_cast cfg.hδ1
    exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1
      (by nlinarith [cfg.hη, cfg.hexscal])
  exact plankSubfamilyMult (s := (tc.thinBall hB).bodies') (sel := psd.sel) (YP := psd.YP)
    (δ := cfg.δ) (r₁ := cfg.r₁) (Csel := plankSelectionConstant bd.C₀) (η := 16 * cfg.η)
    (exscal := cfg.exscal) cfg.hδ cfg.hδ1 (by linarith [cfg.hη])
    (one_le_plankSelectionConstant bd.C₀)
    (by simp [r₁]) (NNReal.rpow_pos cfg.hδ)
    (by rw [psd.hmult]; exact hmult)
    psd.hselRefine hsel_thr16

/-- **The fullness of a refinement at a thin ball** (blueprint `lem:ml2fullnessRefine` read at
(T2)).

The field `Kakeya.VeryNotSticky.TypicalAngleData.hfull`: (T2),
`ThinCase.ThinBall.fullness_bodies` at the `tb` index `2η`, gives `δ^{6η} ≤ C λ(𝕎'_B, Y_{𝕎'_B})`,
and the
`c`-refinement costs a further `δ^{2η}` through
`ShadedBody.IsCRefinement.mul_fullness_le`, whose positivity hypothesis is
`Kakeya.VeryNotSticky.thinBallPositivity_carrier_pos` at the reflexive refinement. -/
theorem typicalAngleRefinedFullness (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    {c : NNReal} (hc : cfg.δ ^ (2 * cfg.η) ≤ c)
    {sel : Finset bd.ω} {YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (href : ShadedBody.IsCRefinement sel YW (tc.thinBall hB).bodies' (tc.thinBall hB).W c) :
    cfg.δ ^ (8 * cfg.η) ≤ tc.C * ShadedBody.fullness sel YW := by
  classical
  -- reflexive refinement of `(𝕎'_B, Y_{𝕎'_B})` at `c = 1`
  let hrefl : ShadedBody.IsCRefinement (tc.thinBall hB).bodies' (tc.thinBall hB).W
      (tc.thinBall hB).bodies' (tc.thinBall hB).W 1 :=
    ShadedBody.IsCRefinement.refl (tc.thinBall hB).bodies' (tc.thinBall hB).W
  have hVol : 0 < ∑ i ∈ (tc.thinBall hB).bodies',
      volume ((tc.thinBall hB).W i).carrier :=
    thinBallPositivity_carrier_pos cfg tc hB (c := 1) one_pos hrefl
  have hrefFull : c * ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
      ShadedBody.fullness sel YW :=
    ShadedBody.IsCRefinement.mul_fullness_le sel YW
      (tc.thinBall hB).bodies' (tc.thinBall hB).W hVol href
  have hfull : cfg.δ ^ (6 * cfg.η) ≤
      tc.C * ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W := by
    rw [← ENNReal.coe_le_coe]
    rw [ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne' (6 * cfg.η)]
    rw [ENNReal.coe_mul]
    have hfb := (tc.thinBall hB).fullness_bodies
    rwa [show (3 : ℝ) * (2 * cfg.η) = 6 * cfg.η by ring] at hfb
  calc
    cfg.δ ^ (8 * cfg.η) = cfg.δ ^ ((2 * cfg.η) + (6 * cfg.η)) := by
      congr 1
      ring
    _ = cfg.δ ^ (2 * cfg.η) * cfg.δ ^ (6 * cfg.η) := by
      rw [NNReal.rpow_add cfg.hδ.ne' (2 * cfg.η) (6 * cfg.η)]
    _ ≤ c * cfg.δ ^ (6 * cfg.η) := by
      gcongr
    _ ≤ c * (tc.C * ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W) := by
      gcongr
    _ = tc.C * (c * ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W) := by
      ring
    _ ≤ tc.C * ShadedBody.fullness sel YW := by
      gcongr

/-- **From the plank angle to the body angle** (blueprint `anglebound`).

Two planks built on the frames of two bodies make the bodies' angle, by
`Kakeya.VeryNotSticky.prism_angle_eq_axisAngle`; the only work is undoing the cap of
`Kakeya.effectivePlankAngle`, which is `1 ⊓ ((a'/b') ⊔ ∠)`. If `θ < 1` the cap is inactive and
`∠ ≤ θ ≤ Ctyp θ`; if `θ ≥ 1` the bound is free, `axisAngle ≤ π/2 ≤ 2 ≤ Ctyp θ`. This is why
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` enlarges the typicality constant by the
factor `2 ≥ π/2`, and it is what the thirteenth clause
`Kakeya.VeryNotSticky.CaseScale.typicalAngle_cap` pays for. -/
theorem axisAngle_le_of_effectivePlankAngle_le {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (W W' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (P Q : Plank a' b' hab' hb1')
    (hP : P.basis = bodyFrame W) (hQ : Q.basis = bodyFrame W')
    {θ Ctyp : NNReal} (hCtyp : 2 ≤ Ctyp)
    (h : Kakeya.effectivePlankAngle P Q ≤ θ) :
    axisAngle W W' ≤ (Ctyp : ℝ) * (θ : ℝ) := by
  -- The plank angle is the body angle
  have hangle : P.angle Q = axisAngle W W' := prism_angle_eq_axisAngle P Q W W' hP hQ
  rw [← hangle]
  -- Goal: P.angle Q ≤ (Ctyp : ℝ) * (θ : ℝ)
  let X : NNReal := (a' / b') ⊔ (P.angle Q).toNNReal
  have hinf : (1 : NNReal) ⊓ X ≤ θ := by
    simpa [Kakeya.effectivePlankAngle, X, Plank.planeAngleNN_eq_toNNReal_angle] using h
  by_cases hθ1 : (θ : ℝ) < 1
  · -- Case θ < 1: the cap in effectivePlankAngle is inactive
    have hθ1nn : θ < (1 : NNReal) := by
      exact_mod_cast hθ1
    -- From (1 ⊓ X) ≤ θ and θ < 1, deduce X ≤ θ
    have hXθ : X ≤ θ := by
      by_cases h1X : (1 : NNReal) ≤ X
      · have hmin1 : (1 : NNReal) ⊓ X = (1 : NNReal) := inf_eq_left.mpr h1X
        have h1_le_θ : (1 : NNReal) ≤ θ := by simpa [hmin1] using hinf
        exact False.elim (not_le_of_gt hθ1nn h1_le_θ)
      · have hX1 : X ≤ (1 : NNReal) := le_of_not_ge h1X
        have hmin : (1 : NNReal) ⊓ X = X := inf_eq_right.mpr hX1
        simpa [hmin] using hinf
    have hθXle : (P.angle Q).toNNReal ≤ θ :=
      (le_sup_right : (P.angle Q).toNNReal ≤ (a' / b') ⊔ (P.angle Q).toNNReal).trans hXθ
    have hangle_le : P.angle Q ≤ (θ : ℝ) := Real.toNNReal_le_iff_le_coe.mp hθXle
    -- θ ≤ Ctyp * θ
    have hCtypR : (2 : ℝ) ≤ (Ctyp : ℝ) := by exact_mod_cast hCtyp
    have hθnonneg : 0 ≤ (θ : ℝ) := θ.2
    have hCtyp1 : (1 : ℝ) ≤ (Ctyp : ℝ) := le_trans (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) hCtypR
    have hθle : (θ : ℝ) ≤ (Ctyp : ℝ) * (θ : ℝ) := by
      have hmul : (1 : ℝ) * (θ : ℝ) ≤ (Ctyp : ℝ) * (θ : ℝ) :=
        mul_le_mul_of_nonneg_right hCtyp1 hθnonneg
      simpa using hmul
    exact le_trans hangle_le hθle
  · -- Case 1 ≤ θ: the bound is free, axisAngle ≤ π/2 ≤ 2 ≤ Ctyp * θ
    have hθ1ge : (1 : ℝ) ≤ (θ : ℝ) := le_of_not_gt hθ1
    have hangle_pi : P.angle Q ≤ Real.pi / 2 := Prism3D.angle_le_pi_div_two P Q
    have hpi2 : Real.pi / 2 ≤ (2 : ℝ) := by
      linarith [Real.pi_lt_four]
    have hCtypR : (2 : ℝ) ≤ (Ctyp : ℝ) := by exact_mod_cast hCtyp
    have hCtyp0 : 0 ≤ (Ctyp : ℝ) := le_trans (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hCtypR
    have hCthe : (Ctyp : ℝ) ≤ (Ctyp : ℝ) * (θ : ℝ) := by
      have hmul : (Ctyp : ℝ) * (1 : ℝ) ≤ (Ctyp : ℝ) * (θ : ℝ) :=
        mul_le_mul_of_nonneg_left hθ1ge hCtyp0
      simpa using hmul
    have h2the : (2 : ℝ) ≤ (Ctyp : ℝ) * (θ : ℝ) := le_trans hCtypR hCthe
    exact le_trans (le_trans hangle_pi hpi2) h2the

/-- **The exponent bookkeeping of Proposition `lem:ml2typicalangle`** (blueprint
`typicalAngleRefinementFactor`, `typicalAngleConstantBoundSharp`).

The three numerical clauses of the bundle, isolated from the geometry. `C` is the constant
that `Kakeya.findingTypicalAngleOfIntersection_perScale` produces at `ε = η/1024` and the small scale
`δ' = δ/r₁`, and `Csel` is `Kakeya.VeryNotSticky.plankSelectionConstant bd.C₀`.

* The refinement factor is `c = C_sel⁻¹ C⁻¹ (δ')^{η/1024} ≥ δ^{exscal·η} (δ')^{η/512}`, and
  `(δ')^{η/512} = δ^{(1-exscal)η/512}`, so `c ≥ δ^{exscal·η + (1-exscal)η/512} ≥ δ^{2η}` because
  `0 < exscal < 1`. The exponent `η/1024` and not `η/512` is what leaves room for the factor `2`
  of the third clause.
* The typicality constant `Ctyp = 2 C (δ')^{-η/1024}` is at least `2`, since `C ≥ 1` and
  `δ' ≤ 1`; the factor `2 ≥ π/2` is what absorbs the cap of `Kakeya.effectivePlankAngle` in
  `Kakeya.VeryNotSticky.axisAngle_le_of_effectivePlankAngle_le`.
* And `Ctyp ≤ 2 (δ')^{-η/512} ≤ (δ')^{-η/256}`, the second step being exactly the thirteenth
  clause `Kakeya.VeryNotSticky.CaseScale.typicalAngle_cap`, here the hypothesis `hcap_thr`.

`hCsel1 : 1 ≤ Csel` cannot be dropped, for the reason recorded on
`Kakeya.VeryNotSticky.plankSubfamilyMult`: in `ℝ≥0` one has `0⁻¹ = 0`, so at `Csel = 0` the
first clause reads `δ^{2η} ≤ 0` while `hCsel`, an upper bound, is satisfied. At the call site
it is `Kakeya.VeryNotSticky.one_le_plankSelectionConstant`. -/
theorem typicalAngleArith (cfg : VeryNotSticky.{u}) {C Csel : NNReal}
    (hexlt1 : cfg.exscal < 1)
    (hdiv : cfg.δ / cfg.r₁ = cfg.δ ^ (1 - cfg.exscal))
    (hC1 : 1 ≤ C) (hCle : C ≤ (cfg.δ / cfg.r₁) ^ (-(cfg.η / 1024)))
    (hCsel1 : 1 ≤ Csel)
    (hCsel : (Csel : ℝ) ≤ (cfg.δ : ℝ) ^ (-(cfg.exscal * cfg.η)))
    (hcap_thr : (2 : ℝ) ≤ ((cfg.δ / cfg.r₁ : NNReal) : ℝ) ^ (-(cfg.η / 512))) :
    cfg.δ ^ (2 * cfg.η) ≤ Csel⁻¹ * (C⁻¹ * (cfg.δ / cfg.r₁) ^ (cfg.η / 1024)) ∧
      2 ≤ 2 * (C * (cfg.δ / cfg.r₁) ^ (-(cfg.η / 1024))) ∧
      2 * (C * (cfg.δ / cfg.r₁) ^ (-(cfg.η / 1024))) ≤
        (cfg.δ ^ (1 - cfg.exscal)) ^ (-(cfg.η / 256)) := by
  -- `hCsel1 : 1 ≤ Csel` forces `0 < Csel`, on which the inversion below depends.
  have hCselpos : 0 < Csel := lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCsel1
  let δ' : NNReal := cfg.δ / cfg.r₁
  have hdiv' : δ' = cfg.δ ^ (1 - cfg.exscal) := by
    simpa [δ'] using hdiv
  have hδ'pos : 0 < δ' := by
    rw [hdiv']
    exact NNReal.rpow_pos cfg.hδ
  have hδ'ne0 : δ' ≠ 0 := ne_of_gt hδ'pos
  have hδ'le1 : δ' ≤ 1 := by
    rw [hdiv']
    exact NNReal.rpow_le_one cfg.hδ1 (le_of_lt (sub_pos.mpr hexlt1))
  have hηpos16 : 0 < cfg.η / 1024 := div_pos cfg.hη (by norm_num)
  have hexpnonpos : -(cfg.η / 1024) ≤ 0 := neg_nonpos.mpr (le_of_lt hηpos16)
  -- hcap_thr in NNReal
  have hcap : (2 : NNReal) ≤ δ' ^ (-(cfg.η / 512)) := by
    exact NNReal.coe_le_coe.mp (by simpa [δ'] using hcap_thr)
  -- hCle in NNReal
  have hCleNN : C ≤ δ' ^ (-(cfg.η / 1024)) := by
    simpa [δ'] using hCle
  -- clause 2: 2 ≤ 2 * (C * δ' ^ (-(η/1024)))
  have hδ'exp1 : (1 : NNReal) ≤ δ' ^ (-(cfg.η / 1024)) := by
    rw [← NNReal.rpow_zero δ']
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ'pos hδ'le1 hexpnonpos
  have h1leCδ' : (1 : NNReal) ≤ C * δ' ^ (-(cfg.η / 1024)) := by
    calc
      (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ C * δ' ^ (-(cfg.η / 1024)) :=
        mul_le_mul hC1 hδ'exp1 (by norm_num) (by norm_num : (0 : NNReal) ≤ C)
  have h2 : 2 ≤ 2 * (C * δ' ^ (-(cfg.η / 1024))) := by
    simpa using (mul_le_mul_of_nonneg_left h1leCδ' (by norm_num : (0 : NNReal) ≤ 2))
  -- clause 3: 2 * (C * δ' ^ (-(η/1024))) ≤ δ' ^ (-(η/256))
  have hcleprod : δ' ^ (-(cfg.η / 1024)) * δ' ^ (-(cfg.η / 1024)) = δ' ^ (-(cfg.η / 512)) := by
    rw [← NNReal.rpow_add hδ'ne0]
    congr
    ring
  have hCled : C * δ' ^ (-(cfg.η / 1024)) ≤ δ' ^ (-(cfg.η / 1024)) * δ' ^ (-(cfg.η / 1024)) :=
    mul_le_mul_of_nonneg_right hCleNN (by exact zero_le)
  have hcapmult : (2 : NNReal) * (C * δ' ^ (-(cfg.η / 1024))) ≤
      δ' ^ (-(cfg.η / 512)) * δ' ^ (-(cfg.η / 512)) := by
    calc
      (2 : NNReal) * (C * δ' ^ (-(cfg.η / 1024))) ≤
          δ' ^ (-(cfg.η / 512)) * (δ' ^ (-(cfg.η / 1024)) * δ' ^ (-(cfg.η / 1024))) :=
        mul_le_mul hcap hCled (by norm_num) (by exact zero_le)
      _ = δ' ^ (-(cfg.η / 512)) * δ' ^ (-(cfg.η / 512)) := by rw [hcleprod]
  have h3 : 2 * (C * δ' ^ (-(cfg.η / 1024))) ≤
      (cfg.δ ^ (1 - cfg.exscal)) ^ (-(cfg.η / 256)) := by
    rw [← hdiv']
    calc
      2 * (C * δ' ^ (-(cfg.η / 1024))) ≤ δ' ^ (-(cfg.η / 512)) * δ' ^ (-(cfg.η / 512)) := hcapmult
      _ = δ' ^ (-(cfg.η / 256)) := by
        rw [← NNReal.rpow_add hδ'ne0]
        congr
        ring
  -- clause 1: cfg.δ ^ (2*η) ≤ Csel⁻¹ * (C⁻¹ * δ' ^ (η/1024))
  have hCselNN : Csel ≤ cfg.δ ^ (-(cfg.exscal * cfg.η)) := by
    exact NNReal.coe_le_coe.mp (by simpa using hCsel)
  have hδne0 : cfg.δ ≠ 0 := ne_of_gt cfg.hδ
  have hCselmul : Csel * cfg.δ ^ (cfg.exscal * cfg.η) ≤ 1 := by
    rw [NNReal.rpow_neg cfg.δ (cfg.exscal * cfg.η)] at hCselNN
    exact (NNReal.le_inv_iff_mul_le (p := cfg.δ ^ (cfg.exscal * cfg.η))
      ((NNReal.rpow_pos cfg.hδ).ne')).mp hCselNN
  have hCselinv : cfg.δ ^ (cfg.exscal * cfg.η) ≤ Csel⁻¹ := by
    apply (NNReal.le_inv_iff_mul_le (p := Csel) hCselpos.ne').mpr
    simpa [mul_comm] using hCselmul
  have hCpos : 0 < C := by exact lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hC1
  have hCleinv2 : δ' ^ (cfg.η / 1024) ≤ C⁻¹ := by
    rw [NNReal.rpow_neg δ' (cfg.η / 1024)] at hCleNN
    apply (NNReal.le_inv_iff_mul_le (p := C) hCpos.ne').mpr
    calc
      δ' ^ (cfg.η / 1024) * C = C * δ' ^ (cfg.η / 1024) := by rw [mul_comm]
      _ ≤ (δ' ^ (cfg.η / 1024))⁻¹ * (δ' ^ (cfg.η / 1024)) :=
        mul_le_mul_of_nonneg_right hCleNN (by exact zero_le)
      _ = 1 := by
        rw [inv_mul_cancel₀ ((NNReal.rpow_pos hδ'pos).ne')]
  have hprod1 : cfg.δ ^ (cfg.exscal * cfg.η) * δ' ^ (cfg.η / 1024) ≤ Csel⁻¹ * C⁻¹ :=
    mul_le_mul hCselinv hCleinv2 (by exact zero_le) (by exact zero_le)
  have hprod2 : cfg.δ ^ (cfg.exscal * cfg.η) * δ' ^ (cfg.η / 1024) * δ' ^ (cfg.η / 1024) ≤
      Csel⁻¹ * (C⁻¹ * δ' ^ (cfg.η / 1024)) := by
    calc
      cfg.δ ^ (cfg.exscal * cfg.η) * δ' ^ (cfg.η / 1024) * δ' ^ (cfg.η / 1024)
          ≤ Csel⁻¹ * C⁻¹ * δ' ^ (cfg.η / 1024) :=
            mul_le_mul_of_nonneg_right hprod1 (by exact zero_le)
      _ = Csel⁻¹ * (C⁻¹ * δ' ^ (cfg.η / 1024)) := by ring
  have hexpsmall : cfg.exscal * cfg.η + (1 - cfg.exscal) * (cfg.η / 512) ≤ 2 * cfg.η := by
    nlinarith [cfg.hexscal, cfg.hη, hexlt1]
  have hcleprod2 : δ' ^ (cfg.η / 1024) * δ' ^ (cfg.η / 1024) = δ' ^ (cfg.η / 512) := by
    rw [← NNReal.rpow_add hδ'ne0]
    congr
    ring
  have h1 : cfg.δ ^ (2 * cfg.η) ≤ Csel⁻¹ * (C⁻¹ * δ' ^ (cfg.η / 1024)) := by
    calc
      cfg.δ ^ (2 * cfg.η) ≤ cfg.δ ^ (cfg.exscal * cfg.η + (1 - cfg.exscal) * (cfg.η / 512)) :=
        NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 hexpsmall
      _ = cfg.δ ^ (cfg.exscal * cfg.η) * cfg.δ ^ ((1 - cfg.exscal) * (cfg.η / 512)) := by
        rw [← NNReal.rpow_add hδne0]
      _ = cfg.δ ^ (cfg.exscal * cfg.η) * (cfg.δ ^ (1 - cfg.exscal)) ^ (cfg.η / 512) := by
        rw [NNReal.rpow_mul cfg.δ (1 - cfg.exscal) (cfg.η / 512)]
      _ = cfg.δ ^ (cfg.exscal * cfg.η) * δ' ^ (cfg.η / 512) := by rw [← hdiv']
      _ = cfg.δ ^ (cfg.exscal * cfg.η) * δ' ^ (cfg.η / 1024) * δ' ^ (cfg.η / 1024) := by
        rw [← hcleprod2]
        ac_rfl
      _ ≤ Csel⁻¹ * (C⁻¹ * δ' ^ (cfg.η / 1024)) := hprod2
  exact ⟨h1, h2, h3⟩

/-- **The fibre-level plank-angle bound transports along a shading image, at the same
constant.**

The exact analogue of `Kakeya.IsTypicalPlankAngle.congr_image`, and with the same one-line
proof, for `Kakeya.HasMaxPlankAngleBound`.  `HasMaxPlankAngleBound` sees the shading only
through `shadeFibre` — through *which indices shade a point* — so a bijection of the ambient
space moves it index for index, by `shadeFibre_congr_image`.  The planks are not moved.

**The constant `C` is carried through untouched, and that is the point of stating it.** The
transport is what lets the *absolute* bound `C = 1` produced by
`Kakeya.findingTypicalAngleOfIntersection_perScale` in the rescaled coordinates be recorded, in
the original coordinates, on `Kakeya.VeryNotSticky.TypicalAngleData.hmaxAbs`; before this lemma
the only route across the coordinate change was
`Kakeya.VeryNotSticky.axisAngle_of_maxPlankAngleBound`, which spends the bound and returns the
body-axis form at the *non-absolute* `Ctyp`. -/
theorem HasMaxPlankAngleBound.congr_image {ω : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ω} {Y Y' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ω → Plank a b hab hb1} {theta C : NNReal}
    (g : EuclideanSpace ℝ (Fin 3) ≃ EuclideanSpace ℝ (Fin 3))
    (hg : ∀ i ∈ s, (Y' i).shade = g '' (Y i).shade)
    (h : Kakeya.HasMaxPlankAngleBound s Y P theta C) :
    Kakeya.HasMaxPlankAngleBound s Y' P theta C := by
  intro x hx
  rw [← g.apply_symm_apply x, shadeFibre_congr_image s Y Y' g hg (g.symm x)]
  apply h
  rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
  rw [hg i hi] at hxi
  rcases hxi with ⟨w, hw, hgw⟩
  refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  simpa [← hgw] using hw

/-- **What the fibre bound buys: any two indices shading a common point have effective plank
angle at most `C · θ`.**

`Kakeya.HasMaxPlankAngleBound` is a bound on the *maximum* over a fibre, and this is that bound
read at one pair — steps 3 and 4 of `Kakeya.VeryNotSticky.axisAngle_of_maxPlankAngleBound`,
isolated so that they can be used without also paying the plank-to-body conversion and its
factor `2`. -/
theorem effectivePlankAngle_le_of_hasMaxPlankAngleBound {ω : Type*} {a b : NNReal}
    {hab : a ≤ b} {hb1 : b ≤ 1} {sel : Finset ω}
    {P : ω → Plank a b hab hb1} {Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {θ C : NNReal} (hmax : Kakeya.HasMaxPlankAngleBound sel Y P θ C)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ⋃ i ∈ sel, (Y i).shade)
    {i j : ω} (hi : i ∈ shadeFibre sel Y x) (hj : j ∈ shadeFibre sel Y x) :
    Kakeya.effectivePlankAngle (P i) (P j) ≤ C * θ := by
  have heff : Kakeya.effectivePlankAngle (P i) (P j) ≤
      Kakeya.maxPlankAngle P (shadeFibre sel Y x) := by
    simpa [Kakeya.maxPlankAngle] using
      (Kakeya.le_maxAngle (ang := fun i j => Kakeya.effectivePlankAngle (P i) (P j)) hi hj)
  exact heff.trans (hmax x hx)

/-- **The same at the absolute constant `C = 1`: the angle is bounded by `θ` itself, with no
constant at all.**

This is the form GWZ 6.13's radius transport needs, and it is the reason the absolute bound is
worth recording on `Kakeya.VeryNotSticky.TypicalAngleData` rather than being spent at the
interface.  The `Ctyp`-scaled forms the configuration already carries —
`Kakeya.VeryNotSticky.TypicalAngleData.htyp` through
`Kakeya.IsTypicalPlankAngle.hasMaxPlankAngleBound` — give only `Ctyp · θ`, and `Ctyp` is bounded
merely by `(δ')^{-η/256}` (`Kakeya.VeryNotSticky.TypicalAngleData.hCtyp`), which is unbounded as
`δ → 0`: no amount of shrinking `δ` recovers an absolute constant from them.  That is the
"wrong side" this datum fixes. -/
theorem effectivePlankAngle_le_of_hasMaxPlankAngleBound_one {ω : Type*} {a b : NNReal}
    {hab : a ≤ b} {hb1 : b ≤ 1} {sel : Finset ω}
    {P : ω → Plank a b hab hb1} {Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {θ : NNReal} (hmax : Kakeya.HasMaxPlankAngleBound sel Y P θ 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ⋃ i ∈ sel, (Y i).shade)
    {i j : ω} (hi : i ∈ shadeFibre sel Y x) (hj : j ∈ shadeFibre sel Y x) :
    Kakeya.effectivePlankAngle (P i) (P j) ≤ θ := by
  simpa using effectivePlankAngle_le_of_hasMaxPlankAngleBound hmax hx hi hj

/-- **Drift tripwire: the field is the *absolute* bound, at `1`.**

If `Kakeya.VeryNotSticky.TypicalAngleData.hmaxAbs` is ever "simplified" to the `Ctyp`-scaled
form that the rest of the structure already carries, this `exact` stops elaborating. That is the
whole content of the field — the constant, not the shape — so it is the thing worth pinning.
Compare `Kakeya.VeryNotSticky.rhoCount_field_is_parent`. -/
theorem TypicalAngleData.hmaxAbs_is_absolute {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (td : TypicalAngleData cfg tc hB τ') :
    Kakeya.HasMaxPlankAngleBound td.sel td.YW td.P td.θ 1 :=
  td.hmaxAbs

/-- **The datum is usable at the configuration, not merely stored**: any two bodies of the
selected family shading a common point have effective plank angle at most `θ`, with **no
constant**.

This is what GWZ 6.13's radius transport asks for, read directly off
`Kakeya.VeryNotSticky.TypicalAngleData`. Before `hmaxAbs` the configuration could not state it:
the available clauses give the angle only up to `Ctyp`, and `Ctyp` is bounded merely by
`(δ')^{-η/256}`, which is unbounded as `δ → 0`.

Recording this corollary is deliberate. A field that is added but never shown to deliver
anything is the "stored but dead" trap; this is the compiled evidence that the field pays. -/
theorem TypicalAngleData.effectivePlankAngle_le {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (td : TypicalAngleData cfg tc hB τ')
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ⋃ i ∈ td.sel, (td.YW i).shade)
    {i j : bd.ω} (hi : i ∈ shadeFibre td.sel td.YW x) (hj : j ∈ shadeFibre td.sel td.YW x) :
    Kakeya.effectivePlankAngle (td.P i) (td.P j) ≤ td.θ :=
  effectivePlankAngle_le_of_hasMaxPlankAngleBound_one td.hmaxAbs hx hi hj

/-- **The one-sided plank-angle bound, read on the bodies and in the original coordinates**
(blueprint `anglebound`).

The field `Kakeya.VeryNotSticky.TypicalAngleData.hangle`, assembled from the last conclusion
`Kakeya.HasMaxPlankAngleBound` of `Kakeya.findingTypicalAngleOfIntersection_perScale`. Two
transports happen at once and neither costs anything.

* *Coordinates.* The bound is produced for the rescaled shading `Y'` and is wanted for the
  original-coordinate shading `YW = L_B⁻¹(Y')`. `Kakeya.HasMaxPlankAngleBound` sees the shading
  only through `shadeFibre`, i.e. through which indices shade a point, and `L_B` is a
  bijection, so `shadeFibre_congr_image` moves it index for index. The planks are *not*
  moved: they are read in the rescaled coordinates on both sides.
* *Planks to bodies.* Each plank is built on the frame of its body (`hbasis`), so
  `Kakeya.VeryNotSticky.axisAngle_le_of_effectivePlankAngle_le` converts the plank angle into
  the body angle with no aperture loss, at the price of the factor `2` in `Ctyp`. -/
theorem axisAngle_of_maxPlankAngleBound {ω : Type*} {a' b' : NNReal} {hab' : a' ≤ b'}
    {hb1' : b' ≤ 1} (sel : Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (P : ω → Plank a' b' hab' hb1')
    (Y' YW : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) ≃ EuclideanSpace ℝ (Fin 3))
    (hg : ∀ i ∈ sel, (YW i).shade = g '' (Y' i).shade)
    (hbasis : ∀ i ∈ sel, (P i).basis = bodyFrame (Wb i))
    {θ Ctyp : NNReal} (hCtyp : 2 ≤ Ctyp)
    (hmax : Kakeya.HasMaxPlankAngleBound sel Y' P θ 1) :
    ∀ x : EuclideanSpace ℝ (Fin 3), ∀ i ∈ sel, ∀ j ∈ sel,
      x ∈ (YW i).shade → x ∈ (YW j).shade →
        axisAngle (Wb i) (Wb j) ≤ (Ctyp : ℝ) * (θ : ℝ) := by
  intro x i hi j hj hxi hxj
  let z : EuclideanSpace ℝ (Fin 3) := g.symm x
  -- 1. The preimage z = g.symm x lies in both shades of Y'.
  have hzi : z ∈ (Y' i).shade := by
    have hxgi : x ∈ g '' (Y' i).shade := by
      simpa [hg i hi] using hxi
    rcases hxgi with ⟨y, hy, hgy⟩
    have hy' : g.symm x = y := by
      rw [← hgy, Equiv.symm_apply_apply]
    simpa [z, hy']
  have hzj : z ∈ (Y' j).shade := by
    have hxgj : x ∈ g '' (Y' j).shade := by
      simpa [hg j hj] using hxj
    rcases hxgj with ⟨y, hy, hgy⟩
    have hy' : g.symm x = y := by
      rw [← hgy, Equiv.symm_apply_apply]
    simpa [z, hy']
  -- 2. z is shaded under Y', so hmax bounds its fibre.
  have hz : z ∈ ⋃ k ∈ sel, (Y' k).shade := by
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hzi⟩
  have hb : Kakeya.maxPlankAngle P (shadeFibre sel Y' z) ≤ θ := by
    simpa using hmax z hz
  -- 3. i and j both belong to that fibre.
  have hif : i ∈ shadeFibre sel Y' z := by
    dsimp [shadeFibre]
    exact Finset.mem_filter.mpr ⟨hi, hzi⟩
  have hjf : j ∈ shadeFibre sel Y' z := by
    dsimp [shadeFibre]
    exact Finset.mem_filter.mpr ⟨hj, hzj⟩
  -- 4. The effective plank angle is bounded by the fibre maximum.
  have heff : Kakeya.effectivePlankAngle (P i) (P j) ≤
      Kakeya.maxPlankAngle P (shadeFibre sel Y' z) := by
    simpa [Kakeya.maxPlankAngle] using
      (Kakeya.le_maxAngle
        (ang := fun i j => Kakeya.effectivePlankAngle (P i) (P j)) hif hjf)
  -- 5. Conclude via the plank-angle to body-angle conversion.
  exact axisAngle_le_of_effectivePlankAngle_le (Wb i) (Wb j) (P i) (P j)
    (hbasis i hi) (hbasis j hj) hCtyp (heff.trans hb)

/-! ### Transporting the typicality data to the plank carriers

`ShadedPlank.reduction_to_slab_atTypicalAngle` reads the refinement, the constant multiplicity
and the typicality at families carried by the *planks*, while
`Kakeya.findingTypicalAngleOfIntersection_perScale` produces them at families carried by the
rescaled bodies. The four lemmas below move each clause across; every one of them is a shading
congruence, the shadings being literally the same on the index set in play. -/

section PlankCarriers

variable {ω : Type*} {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}

/-- The `c`-refinement clause, read at the plank carriers. -/
lemma shadedPlankOf_isCRefinement (P : ω → Plank a' b' hab' hb1')
    (YP Y' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {s0 sel : Finset ω} (hsel : sel ⊆ s0)
    (hshade : ∀ i ∈ s0, (YP i).shade ⊆ (P i).carrier)
    (hshY' : ∀ i ∈ sel, (Y' i).shade ⊆ (P i).carrier)
    {c C : NNReal} (href : ShadedBody.IsCRefinement sel Y' sel YP c) (hC : C ≤ c) :
    ShadedBody.IsCRefinement sel (ShadedPlank.bodies (shadedPlankOf P Y' sel hshY')) sel
      (ShadedPlank.bodies (shadedPlankOf P YP s0 hshade)) C := by
  constructor
  · constructor
    · rfl
    · intro i hi
      constructor
      · calc
          (ShadedPlank.bodies (shadedPlankOf P Y' sel hshY') i).toConvexSpaceBody
              = (P i).toConvexSpaceBody := shadedPlankOf_toConvexSpaceBody P Y' sel hshY' i
          _ = (ShadedPlank.bodies (shadedPlankOf P YP s0 hshade) i).toConvexSpaceBody := by
              exact (shadedPlankOf_toConvexSpaceBody P YP s0 hshade i).symm
      · calc
          (ShadedPlank.bodies (shadedPlankOf P Y' sel hshY') i).shade
              = (Y' i).shade := shadedPlankOf_shade P Y' sel hshY' i hi
          _ ⊆ (YP i).shade := (href.1.2 i hi).2
          _ = (ShadedPlank.bodies (shadedPlankOf P YP s0 hshade) i).shade := by
              exact (shadedPlankOf_shade P YP s0 hshade i (hsel hi)).symm
  · have hsumR : (∑ i ∈ sel,
        volume ((ShadedPlank.bodies (shadedPlankOf P YP s0 hshade) i).shade)) =
        ∑ i ∈ sel, volume ((YP i).shade) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [shadedPlankOf_shade P YP s0 hshade i (hsel hi)]
    have hsumL : (∑ i ∈ sel,
        volume ((ShadedPlank.bodies (shadedPlankOf P Y' sel hshY') i).shade)) =
        ∑ i ∈ sel, volume ((Y' i).shade) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [shadedPlankOf_shade P Y' sel hshY' i hi]
    rw [hsumR, hsumL]
    exact le_trans (by gcongr) href.2

/-- The constant-multiplicity clause, read at the plank carriers. -/
lemma shadedPlankOf_hasCConstantMultiplicity (P : ω → Plank a' b' hab' hb1')
    (Y' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) {sel : Finset ω}
    (hshY' : ∀ i ∈ sel, (Y' i).shade ⊆ (P i).carrier) {C : NNReal}
    (hconst : ShadedBody.HasCConstantMultiplicity sel Y' C) :
    ShadedBody.HasCConstantMultiplicity sel
      (ShadedPlank.bodies (shadedPlankOf P Y' sel hshY')) C := by
  exact ShadedBody.HasCConstantMultiplicity.congr_image
    (g := Equiv.refl (EuclideanSpace ℝ (Fin 3)))
    (fun i hi => by
      simpa using (shadedPlankOf_shade P Y' sel hshY' i hi))
    hconst

/-- The typicality clause, read at the plank carriers. -/
lemma shadedPlankOf_isTypicalPlankAngle (P : ω → Plank a' b' hab' hb1')
    (Y' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) {sel : Finset ω}
    (hshY' : ∀ i ∈ sel, (Y' i).shade ⊆ (P i).carrier) {θ C A : NNReal}
    (htyp : Kakeya.IsTypicalPlankAngle sel Y' P θ C A) :
    Kakeya.IsTypicalPlankAngle sel (ShadedPlank.bodies (shadedPlankOf P Y' sel hshY'))
      (ShadedPlank.planks (shadedPlankOf P Y' sel hshY')) θ C A := by
  rw [shadedPlankOf_planks P Y' sel hshY']
  exact Kakeya.IsTypicalPlankAngle.congr_image
    (g := Equiv.refl (EuclideanSpace ℝ (Fin 3)))
    (fun i hi => by
      simpa using (shadedPlankOf_shade P Y' sel hshY' i hi))
    htyp

/-- **The one-sided plank-angle bound, read at the plank carriers.**

The `Kakeya.HasMaxPlankAngleBound` analogue of
`Kakeya.VeryNotSticky.shadedPlankOf_isTypicalPlankAngle`, with the same proof shape at
`g = Equiv.refl`: `Kakeya.HasMaxPlankAngleBound` sees a shading only through
`Kakeya.shadeFibre`, and `Kakeya.VeryNotSticky.shadedPlankOf_shade` says the passage to the plank
carriers leaves every shade of `sel` unchanged.

This is what carries the absolute datum from the pair `(P, Y')` in which
`Kakeya.findingTypicalAngleOfIntersection_perScale` produces it to the plank-carried pair
`(ShadedPlank.planks SP, YP)` at which
`ShadedPlank.reduction_to_slab_atTypicalAngle` is fired. -/
lemma shadedPlankOf_hasMaxPlankAngleBound (P : ω → Plank a' b' hab' hb1')
    (Y' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) {sel : Finset ω}
    (hshY' : ∀ i ∈ sel, (Y' i).shade ⊆ (P i).carrier) {θ C : NNReal}
    (hmax : Kakeya.HasMaxPlankAngleBound sel Y' P θ C) :
    Kakeya.HasMaxPlankAngleBound sel (ShadedPlank.bodies (shadedPlankOf P Y' sel hshY'))
      (ShadedPlank.planks (shadedPlankOf P Y' sel hshY')) θ C := by
  rw [shadedPlankOf_planks P Y' sel hshY']
  exact HasMaxPlankAngleBound.congr_image
    (g := Equiv.refl (EuclideanSpace ℝ (Fin 3)))
    (fun i hi => by
      simpa using (shadedPlankOf_shade P Y' sel hshY' i hi))
    hmax

/-- The multiplicity is unchanged by the passage to the plank carriers. -/
lemma shadedPlankOf_multiplicity (P : ω → Plank a' b' hab' hb1')
    (Y : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) {s0 sel : Finset ω} (hsel : sel ⊆ s0)
    (hshade : ∀ i ∈ s0, (Y i).shade ⊆ (P i).carrier) :
    ShadedBody.multiplicity sel (ShadedPlank.bodies (shadedPlankOf P Y s0 hshade))
      = ShadedBody.multiplicity sel Y := by
  exact ShadedBody.multiplicity_eq_of_forall_shade_eq sel
    (ShadedPlank.bodies (shadedPlankOf P Y s0 hshade)) Y
    (fun i hi => shadedPlankOf_shade P Y s0 hshade i (hsel hi))

end PlankCarriers

/-- The typicality constant produced by `Kakeya.findingTypicalAngleOfIntersection_perScale` is
doubled before it enters the bundle, so its reciprocal stays below the refinement factor that
lemma returns. This is the numerical step behind
`Kakeya.VeryNotSticky.TypicalAngleData.hPrefine`. -/
lemma inv_two_mul_mul_inv_le (C d : NNReal) : (2 * (C * d⁻¹))⁻¹ ≤ C⁻¹ * d := by
  calc
    (2 * (C * d⁻¹))⁻¹ = (2 : NNReal)⁻¹ * (C * d⁻¹)⁻¹ := by rw [mul_inv]
    _ = (2 : NNReal)⁻¹ * (C⁻¹ * d) := by rw [mul_inv, inv_inv]
    _ ≤ (1 : NNReal) * (C⁻¹ * d) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = C⁻¹ * d := by rw [one_mul]

/-- **The cardinality bridge with a scale-free constant** (blueprint `lem:ml2plankcard`, read
at the rescaled scale).

`Kakeya.VeryNotSticky.typicalAngleCardBridge` produces `|𝕊*| ≤ C_{card} · (C(C₀) C_bias
δ^{-2ϱ}) · (δ')^{-N}`, whose constant depends on `δ` twice over — through the biased-factoring
constant `C_bias` of (C4), which is produced after `δ`, and through the explicit `δ^{-2ϱ}`.
`ShadedPlank.reduction_to_slab_atTypicalAngle` demands its cardinality data *before* the
scale, so both have to be moved into the exponent. The tenth clause
`Kakeya.VeryNotSticky.CaseScale.plankCard_bias` pays for `C(C₀) C_bias` at `δ^{-ϱ}`, leaving
`δ^{-3ϱ}`, and `δ^{-3ϱ} = (δ')^{-3ϱ/(1-exscal)} ≤ (δ')^{-6ϱ}` since `exscal < 1/2`
(`params.scale`). The resulting bound has the constant `C_{card}` and the exponent
`N + 6ϱ`, both fixed before `δ`. -/
theorem typicalAngleCardBridge' (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (psd : PlankPresentationData (tc.thinBall hB).bodies' bd.Wb (tc.thinBall hB).W
      cfg.a cfg.b cfg.r₁ cfg.δ bd.C₀)
    (hbias : plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ cfg.ϱ ≤ 1)
    (hexscal : cfg.exscal < 1 / 2) :
    (psd.sel.card : NNReal) ≤ plankCardConstant *
      (cfg.δ / cfg.r₁ : NNReal) ^ (-(plankCardExponent + 6 * cfg.ϱ)) := by
  classical
  -- The rescaled scale δ' = δ / r₁.
  set δ' : NNReal := cfg.δ / cfg.r₁ with hδ'def
  have hr₁_pos : 0 < cfg.r₁ := by
    dsimp [r₁]
    exact NNReal.rpow_pos cfg.hδ
  have hδ'_pos : 0 < δ' := by
    dsimp [δ']
    exact div_pos cfg.hδ hr₁_pos
  have hδ'_ne : δ' ≠ 0 := ne_of_gt hδ'_pos
  have hdiv : δ' = cfg.δ ^ (1 - cfg.exscal) := by
    dsimp [δ']
    unfold r₁
    rw [NNReal.rpow_sub cfg.hδ.ne']
    rw [NNReal.rpow_one]
  have hexscal1 : cfg.exscal < 1 := by linarith
  have h1m_pos : 0 < 1 - cfg.exscal := by linarith
  have hδ'_le1 : δ' ≤ 1 := by
    rw [hdiv]
    exact NNReal.rpow_le_one cfg.hδ1 (le_of_lt h1m_pos)
  -- (1) hbias: pull the biased-factoring factor out at δ^{-ϱ}.
  have hbias_inv : plankEnclosureConstant bd.C₀ * bd.Cbias ≤ cfg.δ ^ (-cfg.ϱ) := by
    rw [NNReal.rpow_neg]
    exact (NNReal.le_inv_iff_mul_le (p := cfg.δ ^ cfg.ϱ) ((NNReal.rpow_pos cfg.hδ).ne')).mpr hbias
  -- (2) the density factor is at most δ^{-3ϱ}.
  have hmid : plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ (-(2 * cfg.ϱ)) ≤
      cfg.δ ^ (-(3 * cfg.ϱ)) := by
    calc
      plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ (-(2 * cfg.ϱ))
          ≤ cfg.δ ^ (-cfg.ϱ) * cfg.δ ^ (-(2 * cfg.ϱ)) := by
            exact mul_le_mul_of_nonneg_right hbias_inv (by positivity)
      _ = cfg.δ ^ (-(3 * cfg.ϱ)) := by
            rw [← NNReal.rpow_add cfg.hδ.ne' (-cfg.ϱ) (-(2 * cfg.ϱ))]
            congr 1
            ring
  -- (3) convert δ^{-3ϱ} into a power of δ'.
  have hpow_id : cfg.δ ^ (-(3 * cfg.ϱ)) = δ' ^ (-(3 * cfg.ϱ) / (1 - cfg.exscal)) := by
    rw [hdiv]
    rw [← NNReal.rpow_mul cfg.δ (1 - cfg.exscal) (-(3 * cfg.ϱ) / (1 - cfg.exscal))]
    congr 1
    field_simp [h1m_pos.ne']
  -- (4) exponent comparison: -(6ϱ) ≤ -(3ϱ)/(1-exscal), from exscal < 1/2.
  have hexp_le : -(6 * cfg.ϱ) ≤ -(3 * cfg.ϱ) / (1 - cfg.exscal) := by
    rw [le_div_iff₀ h1m_pos]
    nlinarith [cfg.hϱ, hexscal]
  have hpow_le : δ' ^ (-(3 * cfg.ϱ) / (1 - cfg.exscal)) ≤ δ' ^ (-(6 * cfg.ϱ)) := by
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ'_pos hδ'_le1 hexp_le
  -- (5) final assembly.
  calc
    (psd.sel.card : NNReal)
        ≤ plankCardConstant * (plankEnclosureConstant bd.C₀ * bd.Cbias *
              cfg.δ ^ (-(2 * cfg.ϱ))) * δ' ^ (-plankCardExponent) := by
          simpa [δ'] using typicalAngleCardBridge cfg tc hB psd
    _ ≤ plankCardConstant * (cfg.δ ^ (-(3 * cfg.ϱ))) * δ' ^ (-plankCardExponent) := by
          gcongr
    _ = plankCardConstant * (δ' ^ (-(3 * cfg.ϱ) / (1 - cfg.exscal))) *
          δ' ^ (-plankCardExponent) := by
          rw [hpow_id]
    _ ≤ plankCardConstant * (δ' ^ (-(6 * cfg.ϱ))) * δ' ^ (-plankCardExponent) := by
          gcongr
    _ = plankCardConstant * δ' ^ (-(plankCardExponent + 6 * cfg.ϱ)) := by
          rw [mul_assoc]
          rw [← NNReal.rpow_add hδ'_ne (-(6 * cfg.ϱ)) (-plankCardExponent)]
          congr 1
          ring_nf

/-- **The plank family is `(a')^η`-full** (blueprint `transverseFillFullness`, obligation O5 of
Configuration `hyp:ml2thinsetup`).

The obligation is granted in the original coordinates, as the clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`; this lemma reads it against the
shaded plank family `(𝒫, Y_𝒫)` where `ShadedPlank.reduction_to_slab_atTypicalAngle` consumes
it. The two pins of that clause are discharged from the presentation itself: the selection
`𝕊*` retains a `(C^{sel})⁻¹` fraction of the shaded mass by
`Kakeya.VeryNotSticky.PlankPresentationData.hselRefine`, transported to the original
coordinates by `hvol`, and the shadings of the plank family are the transports of
`Y_{𝕎'_B}`, which is `hvol` again. The upper pin on `b'` is `hbupper`, and the transverse
guard `δ^{-τ'} a/b ≤ 1` of the clause is the hypothesis `hguard`,
which the producer `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` derives from the guard
`δ^{-τ'} a/b ≤ θ` of `Kakeya.VeryNotSticky.TypicalAngleData.hfullP` and `θ ≤ 1`. -/
theorem typicalAnglePlankFullness (cfg : VeryNotSticky.{u}) {τ' : ℝ}
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (psd : PlankPresentationData (tc.thinBall hB).bodies' bd.Wb (tc.thinBall hB).W
      cfg.a cfg.b cfg.r₁ cfg.δ bd.C₀)
    (hO5 : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1 →
      ∀ {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
      (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1'),
      t ⊆ (tc.thinBall hB).bodies' →
      bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' → a' ≤ bd.C₀ * (cfg.a / cfg.r₁) →
      b' ≤ bd.C₀ * (cfg.b / cfg.r₁) →
      ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
          (∑ i ∈ (tc.thinBall hB).bodies', volume ((tc.thinBall hB).W i).shade) ≤
        ∑ i ∈ t, volume ((tc.thinBall hB).W i).shade →
      (∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade * ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3)
        = volume ((tc.thinBall hB).W i).shade) →
      a' ^ (16 * cfg.η) ≤ ShadedBody.fullness t (ShadedPlank.bodies SP))
    (hguard : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1) :
    psd.a' ^ (16 * cfg.η) ≤ ShadedBody.fullness psd.sel
      (ShadedPlank.bodies (shadedPlankOf psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade)) := by
  refine hO5 hguard psd.sel (shadedPlankOf psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade)
    psd.hsel psd.hlower psd.hupper psd.hbupper ?_ ?_
  · -- Goal A: the selection-mass pin
    let k : ENNReal := ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3)
    have hp0 : plankSelectionConstant bd.C₀ ≠ 0 :=
      (lt_of_lt_of_le (show (0 : NNReal) < 1 by norm_num)
        (one_le_plankSelectionConstant bd.C₀)).ne'
    have hk : ∀ i ∈ (tc.thinBall hB).bodies',
        volume ((psd.YP i).shade) * k = volume ((tc.thinBall hB).W i).shade := by
      intro i hi
      simpa [k] using psd.hvol i hi
    have hsum' : (∑ i ∈ (tc.thinBall hB).bodies', volume ((tc.thinBall hB).W i).shade) =
        (∑ i ∈ (tc.thinBall hB).bodies', volume ((psd.YP i).shade)) * k := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i hi => (hk i hi).symm)
    have hsum_sel : (∑ i ∈ psd.sel, volume ((tc.thinBall hB).W i).shade) =
        (∑ i ∈ psd.sel, volume ((psd.YP i).shade)) * k := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i hi => (hk i (psd.hsel hi)).symm)
    calc
      (plankSelectionConstant bd.C₀ : ENNReal)⁻¹ *
            (∑ i ∈ (tc.thinBall hB).bodies', volume ((tc.thinBall hB).W i).shade)
          = ((plankSelectionConstant bd.C₀)⁻¹ : NNReal) *
            ((∑ i ∈ (tc.thinBall hB).bodies', volume ((psd.YP i).shade)) * k) := by
            rw [← ENNReal.coe_inv hp0, hsum']
      _ = (((plankSelectionConstant bd.C₀)⁻¹ : NNReal) *
        ∑ i ∈ (tc.thinBall hB).bodies', volume ((psd.YP i).shade)) * k := by
            rw [← mul_assoc]
      _ ≤ (∑ i ∈ psd.sel, volume ((psd.YP i).shade)) * k := by
            gcongr
            exact psd.hselRefine.2
      _ = ∑ i ∈ psd.sel, volume ((tc.thinBall hB).W i).shade := hsum_sel.symm
  · -- Goal B: the per-index volume identity
    intro i hi
    rw [shadedPlankOf_shade psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade i (psd.hsel hi)]
    exact psd.hvol i (psd.hsel hi)

/-- **A typical angle of intersection in the non-slab case** (blueprint
`lem:ml2typicalangle`).

In the configuration `cfg`, with the per-ball data `bd` of Configuration `hyp:ml2setup`, the
thin-case data `tc` of Configuration `hyp:ml2thinsetup` over it, the thin-case refinement
`a ≤ δ^{1-τ}` and the non-slab hypothesis `b ≤ δ^{2·exscal}`, fix a ball `B ∈ 𝔅` and suppose
that the factoring multiplicity satisfies `δ^{-η} ≤ μ(𝕎'_B, Y_{𝕎'_B})`. Then there are

* a finite essentially distinct family `𝒫` of `a' × b' × 1` planks with `a'/b' = a/b`,
  together with a shading `Y_𝒫`, obtained from `(𝕎'_B, Y_{𝕎'_B})` as in
  `Kakeya.VeryNotSticky.plankPresentation`;
* a `⪆ 1` refinement of `(𝕎'_B, Y_{𝕎'_B})`, expressed here as an `IsCRefinement` with
  constant `c ≥ δ^{2η}`; and
* an angle `θ ∈ [a/b, 1]`

such that `θ` is a typical angle for the refined family in the sense of
`Kakeya.IsTypicalPlankAngle`, with the comparison constant `Ctyp` exposed and stopping-time
scale `Real.toNNReal (Kakeya.plankAngleScaleA a')`. The range of `θ` and constant-multiplicity
conclusion, which the former typical-angle predicate bundled, are separate fields.

All of that is the single bundle `Kakeya.VeryNotSticky.TypicalAngleData cfg tc hB τ'`, and the
conclusion is its `Nonempty`. The bundle exists because the same fourteen clauses are
consumed verbatim by three declarations — `Kakeya.VeryNotSticky.goalMult_of_theta_ge`,
`Kakeya.VeryNotSticky.goalMult_of_theta_lt` and
`Kakeya.VeryNotSticky.tangentialSlabDecomp` — and listing them at each was three copies of
one concept.

**The typicality constant is bounded, and must be.** `Ctyp` is existentially quantified here,
*after* `cfg` and hence after `δ`, so without a bound on it the last two clauses carry no
information at all: `Kakeya.IsTypicalPlankAngle` and `ShadedBody.HasCConstantMultiplicity` both
become weaker as the constant grows, and are satisfied by any family once it is large enough.
The clause bounding `Ctyp` is what keeps them non-vacuous, and it is what the consumers
consume: `Kakeya.VeryNotSticky.transverseFill` carries it as the hypothesis `hCtyp`, without
which its own typicality hypothesis would say nothing and the lemma would be unprovable rather
than merely unproved.

The bound is the *sharp* one of blueprint `typicalAngleConstantBoundSharp`, stated at the
rescaled scale `δ' = δ / r₁ = δ^{1-exscal}` and at the exponent `η/256`:
`Ctyp ≤ (δ')^{-η/256}`. It is not the weaker `Ctyp ≤ δ^{-η}` that this statement used to carry,
and the difference is forced by the exponent gap `128ε ≤ ε'` of `ShadedPlank.reduction_to_slab`:
with `ε' = η/2` fixed by the sixth clause
`Kakeya.VeryNotSticky.CaseScale.transverse_fill`, the `ε` at which
`Kakeya.VeryNotSticky.transverseFill` applies that lemma is at most `ε'/2 = η/256`, so a bound
at `δ^{-η}` would not discharge its constant-bound hypothesis and the transverse chain would
not close. Note that the sharp bound implies the weak one, `(δ')^{-η/256} ≤ δ^{-η}` for
`0 < δ ≤ 1`, since `(1-exscal)η/256 ≤ η`.

That clause is now derivable. `Kakeya.findingTypicalAngleOfIntersection_perScale` binds its constant
`C` *inside* the `∀ δ`, after `δ` is introduced, and carries `C ≤ δ^{-ε}` as a conclusion; the
proposition applies it at an `ε` small compared with `η` — `ε = η/1024` is comfortable — an
exponent fixed before the scale either way, so it costs nothing.

**The state of the four obligations.** All four are discharged; the fourth only after the
bundle's fullness clause was restated at the exponent the configuration supports.

* *Discharged (statement of Section 6).* `TypicalAngleData.hCtyp`, `Ctyp ≤ (δ')^{-η/256}`, and
  `TypicalAngleData.hc`, `δ^{2η} ≤ c`, both bottomed out on an upper bound for the constant that
  `Kakeya.findingTypicalAngleOfIntersection_perScale` produces. That lemma is now stated per
  scale with the growth clause `C ≤ δ^{-ε}`; at `ε = η/1024` it gives
  `Ctyp ≍ C (δ')^{-ε} ≤ (δ')^{-η/512}` and
  `c = C^{sel-1} C^{-1} (δ')^{ε} ≥ δ^{exscal·η} (δ')^{η/512} ≥ δ^{2η}`, using `exscal < 1/2`.
* *Discharged (hypothesis `hsel_thr` below).* `hthr` of
  `Kakeya.VeryNotSticky.plankSubfamilyMult`,
  `(plankSelectionConstant bd.C₀ : ℝ) ≤ (cfg.δ : ℝ)^{-exscal·η}`, is blueprint
  `typicalAngleSelectionThreshold`. It is now the twelfth clause
  `Kakeya.VeryNotSticky.CaseScale.typicalAngle_selection`, which the single call site
  `Kakeya.VeryNotSticky.goalMult_of_multBodies_ge` already carries, and it reaches this
  statement as the hypothesis `hsel_thr`. The module layering that blocked it is gone:
  `Kakeya.VeryNotSticky.plankSelectionConstant` now lives in
  `Kakeya.DimensionThree.MainLemma2.PlankConstants`, upstream of `CaseScale`.
* *Discharged (prescribed frames).* `TypicalAngleData.hangle`, blueprint `anglebound`, asks for
  a bound on `Kakeya.VeryNotSticky.axisAngle (bd.Wb i) (bd.Wb j)`, while `htyp` bounds
  `Kakeya.effectivePlankAngle (P i) (P j)`. The two are now *the same angle*:
  `Kakeya.VeryNotSticky.plankWindowEnclosure` builds its plank on a **prescribed** orthonormal
  frame, `Kakeya.VeryNotSticky.plankPresentation` hands it
  `Kakeya.VeryNotSticky.bodyFrame (bd.Wb j)` — transported unchanged by the homothety `L_B`,
  which does not rotate — and the resulting identification is the field
  `Kakeya.VeryNotSticky.PlankPresentationData.hbasis`, converted by
  `Kakeya.VeryNotSticky.prism_angle_eq_axisAngle`.

  One quantitative step remains inside that conversion, and it is what the thirteenth clause
  `Kakeya.VeryNotSticky.CaseScale.typicalAngle_cap` (hypothesis `hcap_thr` below) buys.
  `Kakeya.effectivePlankAngle` *caps* at `1`, so `effectivePlankAngle (P i) (P j) ≤ Ctyp θ`
  carries no information once `Ctyp θ ≥ 1`, whereas `axisAngle ≤ π/2 > 1`. Enlarging `Ctyp` by
  the factor `2 ≥ π/2` closes the gap — `Kakeya.IsTypicalPlankAngle.mono` and
  `ShadedBody.HasCConstantMultiplicity.mono` make that free — and `hcap_thr` is what keeps the
  enlarged constant inside the `(δ')^{-η/256}` budget of `hCtyp`.

* *Discharged (at the exponent the configuration supports).* `TypicalAngleData.hfull` used to
  ask for `(a')^η ≤ λ(𝕎''_B, Y_{𝕎''_B})`, and *no* choice of the refinement can supply that.
  The only lower bound on fullness in the configuration is (T2),
  `Kakeya.ThinCase.ThinBall.fullness_bodies`: `δ^{6η} ≤ C · λ(𝕎'_B, Y_{𝕎'_B})` at the `tb`
  index `2η`. Passing to a
  `c`-refinement costs a further factor `c ≤ 1`
  (`ShadedBody.IsCRefinement.mul_fullness_le`, which is sharp), so the best available is
  `λ(𝕎''_B, Y_{𝕎''_B}) ≥ c C^{-1} δ^{6η}`. But `a' ≥ δ/r₁ = δ^{1-exscal}` — this is
  `PlankPresentationData.hδa'` — so `(a')^η ≥ δ^{(1-exscal)η} > δ^{6η}` for `0 < δ < 1`, since
  `(1-exscal)η < 6η`. The gap is a positive power of `δ`, so no constant absorbs it and no
  smallness hypothesis on `δ` repairs it either: shrinking `δ` makes it worse. The blueprint
  reaches the same conclusion in the closing note of `lem:ml2typicalangle` ("what this
  proposition does *not* produce"), where the `(a')^η` fullness is declared a mathematical
  input owed by whatever produces the bodies.

  The field is therefore now stated at the exponent the configuration does support,
  `δ^{8η} ≤ C λ(𝕎''_B, Y_{𝕎''_B})` — (T2) at the `tb` index `2η` for the bodies and `δ^{2η}`
  for the refinement —
  and it is discharged by `Kakeya.VeryNotSticky.typicalAngleRefinedFullness`. The matching
  binders of `Kakeya.VeryNotSticky.transverseMassBall` and
  `Kakeya.VeryNotSticky.transverseBallFill` moved with it; the obligation that remains, and
  that is now visible where it belongs, is on `Kakeya.VeryNotSticky.transverseFill`, which
  must reach `ShadedPlank.reduction_to_slab` from the weaker fullness or else receive the
  `(a')^η` form as a genuine input from further up.

This is `Kakeya.findingTypicalAngleOfIntersection_perScale` applied with small scale `δ' = δ/r₁` and
`ε = η/1024`: its multiplicity hypothesis follows from `hmult` together with
`μ(𝒫, Y_𝒫) = μ(𝕎'_B, Y_{𝕎'_B})` and `δ' ≥ δ`, and its cardinality bridge is
`Kakeya.VeryNotSticky.plankCard`. The output data are exactly what the transverse and
tangential cases (`goalMult_of_theta_ge`, `goalMult_of_theta_lt`) consume.

**The cardinality bridge needs no extra hypothesis.** `plankCard` asks for the localization
`𝒫 ⊆ B̄(0, plankBallRadius)` and for a density bound `Δ_max(𝒫) ≤ Δ`; both are clauses of
`Kakeya.VeryNotSticky.plankPresentation`, the second with
`Δ = plankEnclosureConstant bd.C₀ * Δ_max(𝕎'_B)`, and `Δ_max(𝕎'_B) ≤ C_bias δ^{-2ϱ}` is
`bd.bodies_antiClustering` restricted along `(tc.thinBall hB).bodies'_subset` by
`Kakeya.maxDensity_mono`. The resulting bound `|𝒫| ≲ δ^{-2ϱ} (δ')^{-plankCardExponent}` is
turned into the shape `hcard` demands — a constant fixed *before* the scale, times a power of
`δ'` — by `δ^{-2ϱ} = (δ')^{-2ϱ/(1-exscal)} ≤ (δ')^{-4ϱ}`, using `r₁ = δ^{exscal}` and
`exscal < 1/2` (`params.scale`); so `N = plankCardExponent + 4ϱ`.

**A note on coordinates.** The typicality clause pairs the *original-coordinate* shading `YW`
on `(tc.thinBall hB).bodies'` with the *rescaled* plank family `P`. This is not a coordinate
error, and it is equivalent to the blueprint's fully rescaled formulation: `IsTypicalPlankAngle`
sees the shading only through `ShadedBody.shadeFibre`, i.e. through *which indices* shade a
given point, and `L_B` is a bijection, so it carries the fibres of `Y_{𝒫'}` onto the fibres of
`YW` index for index. The angles are read off `P` alone, and `L_B` is a homothety, so it
preserves them. Carrying the pair in this mixed form is what lets the transverse case state its
conclusions about `(tc.thinBall hB).bodies'` and `cfg.b` directly, instead of re-rescaling at
every step.

The data `𝕎'_B`, `W`, `Y_{𝕎'_B}` and the centre of the ball are read off `bd` and
`tc.thinBall hB` instead of being taken freely: `bodies' = (tc.thinBall hB).bodies'`,
`Wb = bd.Wb`, `Wsh = (tc.thinBall hB).W`, `ctr = bd.ctr B`. Consequently the hypotheses
`hC₀`, `ctr`, `hin`, `hthick` of the previous statement are dropped: they are
`bd.hC₀`, `bd.bodies_subset_ball` and `bd.bodies_thickness`
restricted along `(tc.thinBall hB).bodies'_subset`, and the enlargement sandwich is
`(tc.thinBall hB).Wb_le_W` / `(tc.thinBall hB).W_le_cthickening`. The remaining hypotheses are
the ones the bundle does *not*
supply: the positivity of `τ`, the thin-case and non-slab dichotomy hypotheses, the
large-multiplicity hypothesis `hmult` of this branch, and three fixed-scale conditions on `δ`.

The two positivity hypotheses `0 < δ'` and `0 < a'` of
`Kakeya.findingTypicalAngleOfIntersection_perScale` need no assumption:
`δ' = δ / r₁ > 0` by `cfg.hδ` together with `r₁ = δ^{exscal} > 0`, and `δ' ≤ a'` is part of the
conclusion of
`Kakeya.VeryNotSticky.plankPresentation`. The remaining four have no source in `cfg`, `bd` or
`tc`, and each is a genuine smallness condition in `δ`, which is legitimate because
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` is stated `∀ᶠ (δ : NNReal) in 𝓝[>] 0`. They
are therefore explicit, one per condition:

* `hbsmall : bd.C₀ * cfg.b ≤ cfg.r₁` is `plankPresentation`'s `hbr₁`; it is what forces
  `b' ≤ 1`, i.e. what makes the planks *planks*. It holds for small `δ` because
  `b ≤ δ^{2 exscal}` and `r₁ = δ^{exscal}`, so it amounts to `bd.C₀ δ^{exscal} ≤ 1`.
* `hasmall : bd.C₀ * (cfg.a / cfg.r₁) ≤ exp (-1)` discharges *two* conditions at once, and is
  stated in this single form for that reason. It gives `a' < 1`, which is
  `findingTypicalAngleOfIntersection`'s `ha1`; and it gives `1 ≤ log (a')⁻¹`, whence
  `exp ((log (a')⁻¹)^{1/4}) ≤ exp ((log (a')⁻¹)^{1/2}) =
  Real.toNNReal (Kakeya.plankAngleScaleA a')`, which is the `A`-clause of
  `Kakeya.IsTypicalPlankAngle` for the scale
  `findingTypicalAngleOfIntersection` actually produces. It holds for small `δ` because
  `a ≤ δ^{1-τ}` and `r₁ = δ^{exscal}` with `τ + exscal < 1`, the field
  `params.thinScale`, so `a / r₁ ≤ δ^{1-τ-exscal} → 0`.
* `hmult2 : 2 ≤ (δ')^{-η}` is `findingTypicalAngleOfIntersection`'s `hμ2`. It holds for small
  `δ` because `δ' = δ^{1-exscal} → 0` and `η > 0`.

The fourth condition, the sub-polynomial bound `C ≤ (δ')^{-ε}` on the constant produced, is
*not* a hypothesis here: it is a conclusion of
`Kakeya.findingTypicalAngleOfIntersection_perScale`, and it is precisely what makes the two
clauses `δ^{2η} ≤ c` and `Ctyp ≤ (δ')^{-η/256}` provable. The exponent at which the proposition
applies that lemma is `ε = η/1024`, and the whole computation is
`Kakeya.VeryNotSticky.typicalAngleArith`: with
`c = (C^{sel})⁻¹ C⁻¹ (δ')^{η/1024} ≥ δ^{exscal·η} (δ')^{η/512} ≥ δ^{2η}` and
`Ctyp = 2 C (δ')^{-η/1024} ≤ 2 (δ')^{-η/512} ≤ (δ')^{-η/256}`, the last step being `hcap_thr`. The
value `η/1024` rather than `η/512` is forced by that factor `2`: at `ε = η/512` the bound on `Ctyp`
would land at `2 (δ')^{-η/256}` and miss `hCtyp` by exactly the factor the cap of
`Kakeya.effectivePlankAngle` costs.

**The two plank-side clauses.** The localization `Plank.IsWindowedFamily` and the pairwise
essential distinctness of the plank *carriers* are passed through from
`Kakeya.VeryNotSticky.plankPresentation` rather than dropped. They say nothing about the
angle, and the typical-angle argument does not use them; they are here because they are two of
the hypotheses of `ShadedPlank.reduction_to_slab`, which
`Kakeya.VeryNotSticky.transverseFill` has to discharge and which are not recoverable from a
freely given plank family. The windowedness is stated at `Plank.windowRadius`, which is what
`plankBallRadius` is defined to be; see `Kakeya.VeryNotSticky.plankBallRadius`.

The fullness clause `(a')^η ≤ λ(𝕎''_B, Y_{𝕎''_B})` is here for the same reason, and is the
third hypothesis of `ShadedPlank.reduction_to_slab` that a freely given family cannot supply.
It is carried, in `hO5` and in the field `hfullP` it produces, only under the transverse-case
guard, since that is the
only regime in which it is read; the guard of the field implies the guard of the clause by
`hθ1 : θ ≤ 1`.
It is stated at the *refined* shading `YW` and so is not simply `ThinBall.fullness_bodies`:
discharging it means propagating that fullness through the `⪆ 1` refinement produced with
`θ`, which costs a positive power of `δ` and is the reason the clause is asserted here, where
`YW` is produced, rather than assumed by `Kakeya.VeryNotSticky.transverseFill`. Asserting it
at the producer is what keeps the transverse branch of
`Kakeya.VeryNotSticky.goalMult_of_multBodies_ge` closed: were it a hypothesis of
`transverseFill` instead, that branch would have no way to supply it and would reopen. -/
theorem exists_isTypicalAnglePlank (cfg : VeryNotSticky.{u}) {τ τ' : ℝ} (_hτ : 0 < τ)
    (_hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (_hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hbsmall : bd.C₀ * cfg.b ≤ cfg.r₁)
    (hasmall : ((bd.C₀ * (cfg.a / cfg.r₁) : NNReal) : ℝ) ≤ Real.exp (-1))
    (hmult2 : 2 ≤ ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ^ (-(16 * cfg.η)))
    (hsel_thr : (plankSelectionConstant bd.C₀ : ℝ) ≤ (cfg.δ : ℝ) ^ (-(cfg.exscal * cfg.η)))
    (hcap_thr : (2 : ℝ) ≤ ((cfg.δ / cfg.r₁ : NNReal) : ℝ) ^ (-(cfg.η / 512)))
    (htyp_const : Kakeya.typicalAngleScaledConst.{u} (cfg.η / 1024)
        (plankCardConstant * (plankEnclosureConstant bd.C₀ * bd.Cbias *
          cfg.δ ^ (-(2 * cfg.ϱ)))) plankCardExponent ≤
      (cfg.δ / cfg.r₁ : NNReal) ^ (-(cfg.η / 1024)))
    (hbias : plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ cfg.ϱ ≤ 1)
    (hexscal : cfg.exscal < 1 / 2)
    (hO5 : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1 →
      ∀ {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
      (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1'),
      t ⊆ (tc.thinBall hB).bodies' →
      bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' → a' ≤ bd.C₀ * (cfg.a / cfg.r₁) →
      b' ≤ bd.C₀ * (cfg.b / cfg.r₁) →
      ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
          (∑ i ∈ (tc.thinBall hB).bodies', volume ((tc.thinBall hB).W i).shade) ≤
        ∑ i ∈ t, volume ((tc.thinBall hB).W i).shade →
      (∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade * ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3)
        = volume ((tc.thinBall hB).W i).shade) →
      a' ^ (16 * cfg.η) ≤ ShadedBody.fullness t (ShadedPlank.bodies SP))
    (hmult : (cfg.δ : ENNReal) ^ (-(16 * cfg.η)) ≤
      ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W) :
    Nonempty (TypicalAngleData cfg tc hB τ') := by
  -- STEP 1
  obtain ⟨psd⟩ := exists_plankPresentationData cfg tc hB hbsmall
  set δ' : NNReal := cfg.δ / cfg.r₁ with hδ'def
  obtain ⟨hr₁pos, hr₁le, hdiv, hδ'pos, hδ'lt1, hδlt1, hexlt1⟩ := typicalAngleScaleFacts cfg hmult2
  -- STEP 2
  have hεpos : 0 < cfg.η / 1024 := div_pos cfg.hη (by norm_num)
  have ha : 0 < psd.a' := lt_of_lt_of_le hδ'pos psd.hδa'
  have ha1 : psd.a' < 1 := by
    have hlt : ((bd.C₀ * (cfg.a / cfg.r₁) : NNReal) : ℝ) < 1 :=
      lt_of_le_of_lt hasmall (Real.exp_lt_one_iff.mpr (by norm_num))
    have hlt' : bd.C₀ * (cfg.a / cfg.r₁) < 1 := by exact_mod_cast hlt
    exact lt_of_le_of_lt psd.hupper hlt'
  have hsh : ∀ i ∈ psd.sel, (psd.YP i).shade ⊆ (psd.P i).carrier := fun i hi =>
    psd.hshade i (psd.hsel hi)
  have hmult' : (δ' : ENNReal) ^ (-(16 * cfg.η)) ≤ ShadedBody.multiplicity psd.sel psd.YP :=
    typicalAngleSelMult cfg tc hB psd hsel_thr hmult
  have hcard : (psd.sel.card : NNReal) ≤
      plankCardConstant * (plankEnclosureConstant bd.C₀ * bd.Cbias *
          cfg.δ ^ (-(2 * cfg.ϱ))) * δ' ^ (-plankCardExponent) := by
    simpa [δ'] using typicalAngleCardBridge cfg tc hB psd
  obtain ⟨hC2, Hty⟩ :=
    Kakeya.findingTypicalAngleOfIntersection_scaled_spec.{u} (ε := cfg.η / 1024)
      (C₀ := plankCardConstant * (plankEnclosureConstant bd.C₀ * bd.Cbias *
          cfg.δ ^ (-(2 * cfg.ϱ)))) (Nexp := plankCardExponent) hεpos
  set C : NNReal :=
    Kakeya.typicalAngleScaledConst.{u} (cfg.η / 1024)
      (plankCardConstant * (plankEnclosureConstant bd.C₀ * bd.Cbias *
          cfg.δ ^ (-(2 * cfg.ϱ)))) plankCardExponent with hCdef
  have hC1 : (1 : NNReal) ≤ C := le_trans one_le_two hC2
  have hCle : C ≤ δ' ^ (-(cfg.η / 1024)) := htyp_const
  obtain ⟨Y', θ, href', hθab, hθ1, hconst', htyp', _hcomp, hmax⟩ :=
    Hty psd.sel psd.YP (a := psd.a') (b := psd.b') (δ := δ')
      ha ha1 psd.hab' psd.hb1' hδ'pos psd.hδa' psd.P
      hsh (by linarith [cfg.hη] : (0:ℝ) < 16 * cfg.η) hmult' hcard
  -- STEP 3: the three numerical clauses, isolated in `typicalAngleArith`
  let Ctyp : NNReal := 2 * (C * δ' ^ (-(cfg.η / 1024)))
  let c : NNReal := (plankSelectionConstant bd.C₀)⁻¹ * (C⁻¹ * δ' ^ (cfg.η / 1024))
  obtain ⟨hcarith, hCtyp2, hCtypbd⟩ :=
    typicalAngleArith cfg hexlt1 hdiv hC1 hCle (one_le_plankSelectionConstant bd.C₀)
      hsel_thr hcap_thr
  have hc : cfg.δ ^ (2 * cfg.η) ≤ c := by
    simpa [c, δ'] using hcarith
  have hCtyp2' : 2 ≤ Ctyp := by
    simpa [Ctyp, δ'] using hCtyp2
  have hCtypbd' : Ctyp ≤ (cfg.δ ^ (1 - cfg.exscal)) ^ (-(cfg.η / 256)) := by
    simpa [Ctyp, δ'] using hCtypbd
  have hC_le_Ctyp : C * δ' ^ (-(cfg.η / 1024)) ≤ Ctyp := by
    dsimp [Ctyp]
    simpa using (mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) ≤ 2)
      (by positivity : 0 ≤ C * δ' ^ (-(cfg.η / 1024))))
  -- The constant-multiplicity clause needs `C ≤ Ctyp` (not the sharper
  -- `C * (δ')^{-η/1024} ≤ Ctyp`), since it strengthens `C`-constant multiplicity only.
  have hpow_ge : (1 : NNReal) ≤ δ' ^ (-(cfg.η / 1024)) := by
    simpa using (NNReal.rpow_le_rpow_of_exponent_ge hδ'pos (le_of_lt hδ'lt1)
      (by linarith [cfg.hη] : -(cfg.η / 1024) ≤ (0 : ℝ)))
  have hC_le_Cpow : C ≤ C * δ' ^ (-(cfg.η / 1024)) := by
    calc
      C = C * 1 := by simp
      _ ≤ C * δ' ^ (-(cfg.η / 1024)) := by gcongr
  have hCle' : C ≤ Ctyp := hC_le_Cpow.trans hC_le_Ctyp
  -- STEP 4: compose the selection and angle refinements in plank coordinates,
  -- and pull back to the original coordinates once
  have hchain : ShadedBody.IsCRefinement psd.sel Y' (tc.thinBall hB).bodies' psd.YP c := by
    dsimp [c]
    exact href'.trans psd.hselRefine
  obtain ⟨YW, hrefine, ⟨g, hg⟩, _, hunroll⟩ := psd.hbridge c psd.sel Y' psd.hsel hchain
  -- STEP 5: the plank-carried data, blueprint items (iv) and (v) of `lem:ml2typicalangle`
  have hshY' : ∀ i ∈ psd.sel, (Y' i).shade ⊆ (psd.P i).carrier := by
    intro i hi
    exact ((href'.1.2 i hi).2).trans (hsh i hi)
  let SP : bd.ω → ShadedPlank psd.a' psd.b' psd.hab' psd.hb1' :=
    shadedPlankOf psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade
  let YPP : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    ShadedPlank.bodies (shadedPlankOf psd.P Y' psd.sel hshY')
  -- STEP 6: assemble the bundle
  let td : TypicalAngleData cfg tc hB τ' :=
    { a' := psd.a', b' := psd.b', hab' := psd.hab', hb1' := psd.hb1', P := psd.P,
      YW := YW, θ := θ, c := c, Ctyp := Ctyp, sel := psd.sel, hsel := psd.hsel,
      hratio := psd.hratio, hc := hc, hrefine := hrefine, hθab := hθab, hθ1 := hθ1,
      hwin := (fun i hi => psd.hwin i (psd.hsel hi)),
      hfull := typicalAngleRefinedFullness cfg tc hB hc hrefine,
      hCtyp1 := le_trans (by norm_num : (1 : NNReal) ≤ 2) hCtyp2',
      hCtyp := hCtypbd',
      hconst := ShadedBody.HasCConstantMultiplicity.mono psd.sel YW hCle'
        (ShadedBody.HasCConstantMultiplicity.congr_image g hg hconst'),
      htyp := Kakeya.IsTypicalPlankAngle.mono_const hC_le_Ctyp
        (Kakeya.IsTypicalPlankAngle.congr_image g hg htyp'),
      -- the absolute fibre bound `hmax`, recorded instead of only being spent on `hangle`
      hmaxAbs := HasMaxPlankAngleBound.congr_image g hg hmax,
      hangle := axisAngle_of_maxPlankAngleBound psd.sel bd.Wb psd.P Y' YW g hg
        (fun i hi => psd.hbasis i (psd.hsel hi)) hCtyp2' hmax,
      SP := SP,
      hSP := by
        dsimp [SP]
        exact shadedPlankOf_planks psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade,
      hSPcarrier := by
        dsimp [SP]
        exact shadedPlankOf_carrier psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade,
      YP := YPP,
      hPrefine := by
        refine shadedPlankOf_isCRefinement psd.P psd.YP Y' psd.hsel psd.hshade hshY' href' ?_
        dsimp [Ctyp]
        rw [NNReal.rpow_neg]
        exact inv_two_mul_mul_inv_le C (δ' ^ (cfg.η / 1024)),
      hPconst := by
        exact ShadedBody.HasCConstantMultiplicity.mono psd.sel
          (ShadedPlank.bodies (shadedPlankOf psd.P Y' psd.sel hshY')) hCle'
          (shadedPlankOf_hasCConstantMultiplicity psd.P Y' hshY' hconst'),
      hPtyp := by
        rw [shadedPlankOf_planks psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade]
        rw [← shadedPlankOf_planks psd.P Y' psd.sel hshY']
        exact Kakeya.IsTypicalPlankAngle.mono_const hC_le_Ctyp
          (shadedPlankOf_isTypicalPlankAngle psd.P Y' hshY' htyp'),
      hmaxAbsP := by
        rw [shadedPlankOf_planks psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade]
        rw [← shadedPlankOf_planks psd.P Y' psd.sel hshY']
        exact shadedPlankOf_hasMaxPlankAngleBound psd.P Y' hshY' hmax,
      hfullP := fun hθtrans =>
        typicalAnglePlankFullness cfg tc hB psd hO5 (le_trans hθtrans hθ1),
      hmultP := by
        rw [shadedPlankOf_multiplicity psd.P psd.YP psd.hsel psd.hshade]
        exact hmult',
      hb'lower := psd.hblower,
      hδa' := psd.hδa',
      ha'1 := ha1,
      hcard := by
        exact typicalAngleCardBridge' cfg tc hB psd hbias hexscal,
      hbridgeP0 := by
        intro t Z ht hZsub
        obtain ⟨Wsh0, href0, -, -, hunroll0⟩ :=
          psd.hbridge (plankSelectionConstant bd.C₀)⁻¹ psd.sel psd.YP psd.hsel psd.hselRefine
        obtain ⟨Z', -, hZ'sub, hZ'tr⟩ :=
          hunroll0 (0 : NNReal) t Z ht (fun i hi => by
            rw [← shadedPlankOf_shade psd.P psd.YP (tc.thinBall hB).bodies' psd.hshade i
              (psd.hsel (ht hi))]
            exact hZsub i hi)
            (by simp)
        exact ⟨Z', fun i hi => (hZ'sub i hi).trans ((href0.1.2 i (ht hi)).2), hZ'tr⟩
      hbridgeP := by
        intro c₂ t Z ht hZsub hZmass
        refine hunroll c₂ t Z ht ?_ ?_
        · intro i hi
          rw [← shadedPlankOf_shade psd.P Y' psd.sel hshY' i (ht hi)]
          exact hZsub i hi
        · have hsum : (∑ i ∈ psd.sel, volume (YPP i).shade) =
              ∑ i ∈ psd.sel, volume (Y' i).shade := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact congrArg volume (shadedPlankOf_shade psd.P Y' psd.sel hshY' i hi)
          rw [hsum] at hZmass
          exact hZmass }
  exact ⟨td⟩

/-! ### Assembling the non-slab case -/

/-- **Exponent in Lemma `lem:ml2bigmult`** (blueprint `def:ml2bigmultExponent`).

`ν_{lem:ml2bigmult}(β, ζ) = min(½ τ' β, ½ exscal β ζ)`, where `½ τ' β` is a lower bound for
the gain `τ' β - O(τ + η)` of the transverse case
`Kakeya.VeryNotSticky.goalMult_of_theta_ge` (using `params.transverse`) and `½ exscal β ζ` is
the gain of the tangential case `Kakeya.VeryNotSticky.goalMult_of_theta_lt`.

The blueprint treats the parameters of `hyp:ml2params` as fixed once and for all, so it
writes the constant as a function of `β` and `ζ` alone; in Lean the coarse-scale exponent
`exscal` and the transversality exponent `τ'` are separate reals, so they appear as explicit
arguments. -/
noncomputable def bigmultExponent (β ζ exscal τ' : ℝ) : ℝ :=
  min (τ' * β / 2) (exscal * β * ζ / 2)

/-- The exponent `ν_{lem:ml2bigmult}` is positive. -/
lemma bigmultExponent_pos {β ζ exscal τ' : ℝ} (hβ : 0 < β) (hζ : 0 < ζ)
    (hexscal : 0 < exscal) (hτ' : 0 < τ') : 0 < bigmultExponent β ζ exscal τ' :=
  lt_min (by positivity) (by positivity)

/-- **Main Lemma 2, non-slab case with large factoring multiplicity** (blueprint
`lem:ml2bigmult`).

With the hypotheses of `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`, in particular
`δ^{-η} ≤ μ(𝕎'_B, Y_{𝕎'_B})` at a ball `B ∈ 𝔅` maximising the factoring multiplicity, the
goal holds with exponent `ν = ν_{lem:ml2bigmult}`.

Let `θ ∈ [a/b, 1]` and the refinement be produced by `exists_isTypicalAnglePlank`. Either
`θ ≥ δ^{-τ'} a/b`, and we are in the transverse case: `goalMult_of_theta_ge` gives the
density estimate with exponent `τ' β - O(τ + η) ≥ ½ τ' β`. Or `θ < δ^{-τ'} a/b`, and we are
in the tangential case: `goalMult_of_theta_lt` gives the goal with exponent `½ exscal β ζ`.
In either case the exponent is at least `ν_{lem:ml2bigmult}`, and since `0 < δ ≤ 1` the map
`s ↦ δ^s` is antitone.

As in `exists_isTypicalAnglePlank`, the family `𝕎'_B` and its shading are read off
`tc.thinBall hB`, and the hypotheses `hC₀`, `ctr`, `hin`, `hthick`, the enlargement sandwich
`hWbW`/`hWcth`, and `hed` of the previous statement are dropped, being supplied by `bd` and by
the `ThinBall` at `B`. The only
hypotheses that remain are `hmult` — the large-multiplicity hypothesis distinguishing this
branch — `hβ1` and `hBmax`, which both angular leaves need for
`Kakeya.VeryNotSticky.nonslabSplitBound`, the tangential-leaf bundle
`tin : Kakeya.VeryNotSticky.TangentialInputs cfg tc τ'` of blueprint `lem:ml2tangential`(a)–(c),
threaded on to `Kakeya.VeryNotSticky.goalMult_of_theta_lt` and received from
`Kakeya.VeryNotSticky.goalMult_of_b_le`, and
`scale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr`. Three fields of
`scale` are consumed by `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`;
`scale.rho2Star_le_one` controls the dilated angular scale in both angular leaves,
`scale.transverse_radius` is the transfer-radius threshold of the transverse leaf, and
`scale.transverse_ballFill` and `scale.aScaleData_threshold` are spent further down that
leaf. The gain indexing `scale` is the transverse gain `τ'β/2` and not a free `νA` because
`Kakeya.VeryNotSticky.goalMult_of_theta_ge` reads the eighth clause at the gain at which it
invokes `Kakeya.VeryNotSticky.exists_aScaleData`; the tangential leaf places no constraint
on it. -/
theorem goalMult_of_multBodies_ge (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ (B' : bd.bι) (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr)
    (tin : TangentialInputs cfg tc τ')
    (hmult : (cfg.δ : ENNReal) ^ (-(16 * cfg.η)) ≤
      ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W) :
    cfg.goalMult (bigmultExponent cfg.β cfg.ζ cfg.exscal τ') := by
  obtain ⟨ta⟩ :=
    exists_isTypicalAnglePlank cfg params.hτ hthin hnotslab tc hB
      (scale.body_fits_ball hnotslab) (scale.plank_small hthin) scale.multiplicity_large
      scale.typicalAngle_selection scale.typicalAngle_cap scale.typicalAngle_const
      scale.plankCard_bias params.scale
      (fun hguard => fun t SP ht ha'l ha'u hb'u hsel hvol =>
        scale.transverseFill_fullness hthin hguard B hB (tc.thinBall hB) t SP ht ha'l ha'u
          hb'u hsel hvol)
      hmult
  rcases lt_or_ge ta.θ (cfg.δ ^ (-τ') * (cfg.a / cfg.b)) with (htang | htrans)
  · -- tangential case: θ < δ^{-τ'} (a/b)
    have h_tan_res : cfg.goalMult (cfg.exscal * cfg.β * cfg.ζ / 2) :=
      goalMult_of_theta_lt_explicit cfg params hβ1 hnotslab tc hB hBmax scale ta htang tin
    have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := bigmultExponent cfg.β cfg.ζ cfg.exscal τ' with hν_def
    have hν_le : ν ≤ cfg.exscal * cfg.β * cfg.ζ / 2 := min_le_right _ _
    have hpow : (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β * cfg.ζ / 2) ≤
      (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hν_le
    have h_mul : (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β * cfg.ζ / 2) *
      (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans h_tan_res h_mul
  · -- transverse case: δ^{-τ'} (a/b) ≤ θ
    have h_tra_res : cfg.goalMult (τ' * cfg.β / 2) :=
      goalMult_of_theta_ge_explicit cfg params hβ1 hthin hnotslab tc hB hBmax scale ta htrans
    have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := bigmultExponent cfg.β cfg.ζ cfg.exscal τ' with hν_def
    have hν_le : ν ≤ τ' * cfg.β / 2 := min_le_left _ _
    have hpow : (cfg.δ : ENNReal) ^ (τ' * cfg.β / 2) ≤
      (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hν_le
    have h_mul : (cfg.δ : ENNReal) ^ (τ' * cfg.β / 2) *
      (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans h_tra_res h_mul

/-- **Exponent in Lemma `lem:ml2nonslab`** (blueprint `def:ml2nonslabExponent`).

`ν_{lem:ml2nonslab}(β, ζ) = min(exscal · β, ν_{lem:ml2bigmult}(β, ζ))`, where `exscal · β` is
the gain of the small-multiplicity branch
`Kakeya.VeryNotSticky.goalMult_of_multBodies_le` and `ν_{lem:ml2bigmult}` is the exponent of
`Kakeya.VeryNotSticky.bigmultExponent`. It depends on the parameters of `hyp:ml2params`
only, and is fixed before `δ` and `𝕋`. -/
noncomputable def nonslabExponent (β ζ exscal τ' : ℝ) : ℝ :=
  min (exscal * β) (bigmultExponent β ζ exscal τ')

/-- The exponent `ν_{lem:ml2nonslab}` is positive. -/
lemma nonslabExponent_pos {β ζ exscal τ' : ℝ} (hβ : 0 < β) (hζ : 0 < ζ)
    (hexscal : 0 < exscal) (hτ' : 0 < τ') : 0 < nonslabExponent β ζ exscal τ' :=
  lt_min (by positivity) (bigmultExponent_pos hβ hζ hexscal hτ')

/-- **Main Lemma 2, non-slab case** (blueprint `lem:ml2nonslab`).

In the configuration `cfg`, with the per-ball data `bd` of Configuration `hyp:ml2setup` and
the thin-case data `tc` of Configuration `hyp:ml2thinsetup` over it, together with the
thin-case refinement `a ≤ δ^{1-τ}`, suppose we are in the *non-slab case*, i.e. the middle
affine thickness of the factoring bodies satisfies `b ≤ δ^{exscal} r₁ = δ^{2·exscal}`. Then
the goal holds with the positive gain `ν = ν_{lem:ml2nonslab}(β, ζ)` of
`Kakeya.VeryNotSticky.nonslabExponent`.

No distinguished ball is taken: this lemma *picks* one, and it is the unique place in the
non-slab case where the choice is made. `𝔅 = bd.bs` is a non-empty `Finset` by
`bd.bs_nonempty`, so maximising over `bd.bs.attach` supplies a `B ∈ 𝔅` maximising
`μ((tc.thinBall hB).bodies', (tc.thinBall hB).W)`, and both branches use only this one ball.
The maximality is passed on as the hypothesis `hBmax` of the two branches, which need it for
`Kakeya.VeryNotSticky.nonslabSplitBound`; taking an arbitrary ball here would leave that
hypothesis undischarged. Then `le_total` on `δ^{-η}` splits: either `μ(𝕎'_B, Y_{𝕎'_B}) ≤ δ^{-η}` and
`goalMult_of_multBodies_le` gives the goal with exponent `exscal · β`, or
`μ(𝕎'_B, Y_{𝕎'_B}) ≥ δ^{-η}` and `goalMult_of_multBodies_ge` gives it with exponent
`ν_{lem:ml2bigmult}`. In either case the exponent is at least `ν`, and since `0 < δ ≤ 1` the
map `s ↦ δ^s` is antitone.

Together with `Kakeya.goalMult_of_b_ge` (the slab case) this completes the thin case
`Kakeya.goalMult_of_a_le`, whose gain is witnessed by
`Kakeya.VeryNotSticky.thinExponent cfg.β cfg.ζ cfg.exscal τ'`, the minimum of the slab gain
`β/2` and `nonslabExponent cfg.β cfg.ζ cfg.exscal τ'`.

The bundle `scale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr` is threaded to the
large-multiplicity branch
`Kakeya.VeryNotSticky.goalMult_of_multBodies_ge` and consumed in the angular argument; only
`scale.rho2Star_le_one` is also needed by the small-multiplicity branch. So is the
tangential-leaf bundle `tin : Kakeya.VeryNotSticky.TangentialInputs cfg tc τ'`, which travels
untouched from `Kakeya.goalMult_of_a_le` to
`Kakeya.VeryNotSticky.goalMult_of_theta_lt`; the ball `B` chosen here is the one at which its
`slab` field is eventually read. -/
theorem goalMult_of_b_le (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd)
    {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr)
    (tin : TangentialInputs cfg tc τ') :
    cfg.goalMult (nonslabExponent cfg.β cfg.ζ cfg.exscal τ') := by
  classical
  -- pick B ∈ 𝔅 maximising the factoring multiplicity over the cover (𝔅 is non-empty);
  -- both branches use only this one ball
  obtain ⟨⟨B, hB⟩, _hp, hmax⟩ :=
    Finset.exists_max_image bd.bs.attach
      (fun p : {x : bd.bι // x ∈ bd.bs} =>
        ShadedBody.multiplicity (tc.thinBall p.2).bodies' (tc.thinBall p.2).W)
      (by simpa using bd.bs_nonempty)
  have hBmax : ∀ (B' : bd.bι) (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W := by
    intro B' hB'
    simpa using (hmax ⟨B', hB'⟩ (by simp))
  rcases le_total (ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    ((cfg.δ : ENNReal) ^ (-(16 * cfg.η))) with (hsmall | hbig)
  · -- small-multiplicity branch
    have hsmall_res : cfg.goalMult (cfg.exscal * cfg.β) :=
      goalMult_of_multBodies_le cfg params hβ1 hthin hnotslab tc hB hBmax scale tin.split hsmall
    have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := nonslabExponent cfg.β cfg.ζ cfg.exscal τ' with hν_def
    have hν_le : ν ≤ cfg.exscal * cfg.β := min_le_left _ _
    have hpow : (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β) ≤ (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hν_le
    have h_mul : (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans hsmall_res h_mul
  · -- large-multiplicity branch
    have hbig_res : cfg.goalMult (bigmultExponent cfg.β cfg.ζ cfg.exscal τ') :=
      goalMult_of_multBodies_ge cfg params hβ1 hthin hnotslab tc hB hBmax scale tin hbig
    have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := nonslabExponent cfg.β cfg.ζ cfg.exscal τ' with hν_def
    have hν_le : ν ≤ bigmultExponent cfg.β cfg.ζ cfg.exscal τ' := min_le_right _ _
    have hpow : (cfg.δ : ENNReal) ^ (bigmultExponent cfg.β cfg.ζ cfg.exscal τ') ≤
      (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hν_le
    have h_mul : (cfg.δ : ENNReal) ^ (bigmultExponent cfg.β cfg.ζ cfg.exscal τ') *
      (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans hbig_res h_mul

end Kakeya.VeryNotSticky

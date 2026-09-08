/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupSideData
public import Kakeya.DimensionThree.MainLemma2.PlankRescaling

/-!
# The slab package at `a = b = δ` (T9)

Row T9 of the side-data construction plan ((a)), conjunct 3 of
`Kakeya.VeryNotSticky.SideDataObligations`: for every small `δ`, every configuration on the
degenerate path `a = b = δ`, every `bd : BallData cfg` whose bodies keep the (A1') containment
margin, every ball `B ∈ 𝔅` and every typical-angle datum `ta`,
a `Kakeya.VeryNotSticky.SlabPackage cfg ta` — the input
`Kakeya.VeryNotSticky.TangentialInputs.slab` of the tangential leaf. The conjunct is the statement of
`Kakeya.VeryNotSticky.sideDataObligations_conjunct3_of_margin` below, so it is closed.

## The construction (GWZ `gwz.txt` l.2348–2385)

GWZ's tangential step covers `B` by a maximal family `𝕊` of essentially disjoint slabs of
dimensions `(a/b) r₁ × r₁ × r₁` (l.2352–2353), sorts the bodies of `𝕎''_B` into the subfamilies
`𝕎''_S = {W ∈ 𝕎''_B : W ⊂ S, ∠(T W, T S) ≤ θ}` of equation (28) (l.774–776), and, for a dense
slab `S`, makes "a linear change of variables that converts `S` to `B₁` and converts `𝕎''_S` to a
set `𝕋̃` of `ρ₂`-tubes in `B₁`" (l.2378–2380), whose `Δ_max` is controlled by Lemma 9.2, i.e. by
(83) at `U = B`.

At `a = b = δ` every piece degenerates, and the file simply writes the degenerate values down:

* the slab dimensions are `r₁ × r₁ × r₁`, so the one slab is the ball `B̄(ctr B, r₁)` itself
  (`Kakeya.VeryNotSticky.degenerateSlab`; clause (S2) is the thickness profile of a ball, clauses
  (S1), (S4) are vacuous on a singleton);
* `θ = 1` (`TypicalAngleData.hθab` with `hratio : a'/b' = a/b = 1`, and `hθ1`), so the angle
  condition of (28), read at `2θ = 2`, is void: every normal angle is at
  most `π/2 < 2` (`Kakeya.VeryNotSticky.axisAngle_le_two`), and (S3) is the containment
  `Kakeya.VeryNotSticky.BallData.bodies_subset_ball`;
* the change of variables is the isotropic homothety `x ↦ r₁⁻¹ (x - ctr B)` carrying `B` onto
  `B₁` (`Kakeya.VeryNotSticky.degenerateRescale`, i.e. `Kakeya.VeryNotSticky.plankRescale`);
  clauses (A1), (A2), (A2') are `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` and
  `Kakeya.VeryNotSticky.BallData.bodies_thickness` transported by
  `Kakeya.VeryNotSticky.hasThicknesses_plankRescale_image` at the profile `(1, ρ₂, ρ₂)`,
  `ρ₂ = b/r₁ = δ/r₁`;
* the multiplicity constant `Cμ` is `(100/99) · C^fib(C₀, Ctyp)`, the least admissible value of
  `Kakeya.VeryNotSticky.IsSlabDecompMultConstant`; it is `∝ Ctyp²` and `Ctyp ≤ δ^{-(1-exscal)η/256}`
  (`TypicalAngleData.hCtyp`), so the fixed-scale threshold `Cμ ≤ δ^{-τ'}` holds for small `δ`
  from `η < τ'` (`Kakeya.VeryNotSticky.eventually_degenerateCμ_le`);
* the `Δ_max` constant is the `δ`-free `CΔ := 2^10 C₀³ Cbias`, with
  `CΔ ≤ δ^{-ϱ/2}` for small `δ` (`Kakeya.VeryNotSticky.eventually_degenerateCΔ_le`), and clause
  (A3) is `Kakeya.VeryNotSticky.BallData.bodies_antiClustering` — GWZ (83) at `U = B` — carried
  through `Δ_max`'s monotonicity in the family and its invariance under affine equivalences
  (`Kakeya.VeryNotSticky.isKatzTao_affineImage_of_antiClustering`; it holds for every affine equivalence `L`).

## The finding: clause (A1') is not supplied by `BallData` — a margin is missing

Clause (A1') of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` asks that the closed
`τ₂(W)`-neighbourhood `N_{scale W}(W)` of every body of `𝕎''_S` be carried into the *exact* unit
ball. GWZ never need this: their `𝕋̃ ⊂ B₁` is a statement up to constants (their §2.2 convention,
l.150–160), and `2B₁` would serve them as well. The tree's (C4) field
`Kakeya.VeryNotSticky.BallData.bodies_subset_ball` places the bodies in the closed ball
`B̄(ctr B, r₁)` with **no margin**, and the neighbourhood of a body touching the sphere `∂B`
leaves `B`; under the homothety it leaves `B₁`
(`Kakeya.VeryNotSticky.degenerateRescale_not_A1'_of_touching`, compiled). Nor is the homothety
the wrong choice: at `bd.C₀ = 1` no affine equivalence at all satisfies (A1), (A1') and (A2)
together for a body of the ball (`Kakeya.VeryNotSticky.not_isAnisotropicSlabRescale_of_Cmp_eq_one`),
so at `C₀ = 1` a slab package can exist only if it has no dense slab
(`Kakeya.VeryNotSticky.not_isDenseSlab_of_rescale_Cmp_eq_one`) — the same obstruction for
every `L`, since (A1) and (A2) at one and the same constant `C₀` pin the image of a body of extreme
thickness against the unit sphere. Nothing in `Kakeya.VeryNotSticky.BallData`,
`Kakeya.VeryNotSticky.ThinConfig` or `Kakeya.VeryNotSticky.TypicalAngleData` bounds the distance
of a body to `∂B` from below.

The file therefore delivers the package **with the margin as its one extra input**, in the exact
form clause (A1') pulls back along the homothety:

  `∀ j ∈ bodies B, N_{scale (Wb j)}(Wb j) ⊆ B̄(ctr B, r₁)`

(`Kakeya.VeryNotSticky.exists_slabPackage_degenerate_of_margin`, pointwise, and
`Kakeya.VeryNotSticky.sideDataObligations_conjunct3_of_margin`, the `∀ᶠ` form with the margin as
an inner hypothesis after conjunct 3's pins). The margin is a clause of conjunct 1's `∃ bd` — producible by T4, since T3's capsules sit
within `11 r₁/16` of `ctr B` and `scale ≤ C₀ δ` — and a hypothesis of conjunct 3,
so that conjunct 3 of `Kakeya.VeryNotSticky.SideDataObligations` **is** the statement of
`sideDataObligations_conjunct3_of_margin` (tripwire A below proves the type identity by direct
term; tripwire B projects the same text out of the `Prop`). `BallData` is untouched: a
`bodies_margin` field was deferred (its existing coarse producer takes the ball itself as a body,
and `N_{r₁}(B) ⊄ B`), and `bodies_subset_ball` at `r₁/2` was rejected (a numeral GWZ do not
have). The two other forms are kept as records: bodies in the half ball `B̄(ctr B, r₁/2)`
(`Kakeya.VeryNotSticky.sideDataObligations_conjunct3_of_half_ball`; the margin then follows for
small `δ` from `C₀ δ ≤ r₁/2`, `Kakeya.VeryNotSticky.cthickening_scale_subset_closedBall_of_half`),
and the margin as an `∀ᶠ` clause over the same pins
(`Kakeya.VeryNotSticky.sideDataObligations_conjunct3_of_eventually_margin`, whose conclusion is
the pre-F15, margin-free text of conjunct 3 — true and harmless, superseded; T12 may drop it).
Every other clause of the package is closed from the tree's fields with no hypothesis.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter
open scoped NNReal ENNReal

universe u

/-! ### Angles and balls -/

/-- The normal angle of two bodies never exceeds a right angle, hence never exceeds `2`: at
`θ = 1` the angle condition of (28), read at `2θ`, is void. -/
theorem axisAngle_le_two (W W' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    axisAngle W W' ≤ 2 := by
  rw [axisAngle_eq_lineAngle, NonSlab.lineAngle, InnerProductGeometry.angle_neg_right]
  have hpi := Real.pi_lt_four
  rcases le_total (InnerProductGeometry.angle (bodyNormal W) (bodyNormal W')) (Real.pi / 2)
    with h | h
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- A closed ball of radius `r ≥ 0` in `ℝ³` has the thickness profile `(r, r, r)` at every
comparison constant `C ≥ 1`: clause (S2) of the degenerate slab family. -/
theorem hasThicknesses_closedBall_E3 {C : NNReal} (hC : 1 ≤ C)
    (x : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 ≤ r) :
    HasThicknesses (Metric.closedBall x r) C ![r, r, r] := by
  intro k
  have hk : (k : ℕ) < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [finrank_euclideanSpace_fin]; exact k.isLt
  have hge := Metric.thickness_closedBall_ge (x := x) hr hk
  have hle := Metric.thickness_closedBall_le (𝕜 := ℝ) (x := x) hr (k : ℕ)
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hk3 : ![r, r, r] k = r := by fin_cases k <;> simp
  rw [hk3]
  constructor
  · calc (C : ℝ)⁻¹ * r ≤ 1 * r := by
          apply mul_le_mul_of_nonneg_right _ hr
          exact inv_le_one_of_one_le₀ hC'
      _ = r := one_mul r
      _ ≤ _ := hge
  · calc Metric.thickness ℝ (Metric.closedBall x r) (k : ℕ) ≤ r := hle
      _ = 1 * r := (one_mul r).symm
      _ ≤ C * r := mul_le_mul_of_nonneg_right hC' hr

/-- `0 < r₁ = δ^{exscal}`. -/
theorem r₁_pos (cfg : VeryNotSticky.{u}) : (0 : ℝ) < cfg.r₁ := by
  have : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  exact_mod_cast this

/-- On the degenerate path the aspect ratio `a/b` is `1`. -/
theorem a_div_b_eq_one (cfg : VeryNotSticky.{u}) (hab : cfg.a = cfg.b) : cfg.a / cfg.b = 1 := by
  have hb : cfg.b ≠ 0 := by
    have : cfg.δ ≤ cfg.b := cfg.hdims.1.trans cfg.hdims.2.1
    exact (lt_of_lt_of_le cfg.hδ this).ne'
  rw [hab]; exact div_self hb

/-- At `a = b` the typical angle is at least `1` (`hθab` with `hratio`); with `hθ1` it is `1`. -/
theorem TypicalAngleData.one_le_theta {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ') (hab : cfg.a = cfg.b) : (1 : NNReal) ≤ ta.θ := by
  have h := ta.hθab
  rwa [ta.hratio, a_div_b_eq_one cfg hab] at h

/-! ### The degenerate slab family -/

/-- **The one slab at `a = b`**: the ball `B̄(ctr B, r₁)` itself, GWZ's `(a/b) r₁ × r₁ × r₁` slab
(`gwz.txt` l.2352) at `a/b = 1`. -/
noncomputable def degenerateSlab (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (B : bd.bι) :
    ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
  ConvexSpaceBody.closedBall (bd.ctr B) (cfg.r₁ : ℝ) (NNReal.coe_nonneg _)

theorem degenerateSlab_carrier (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (B : bd.bι) :
    (degenerateSlab cfg B).carrier = Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ) :=
  ConvexSpaceBody.closedBall_carrier _ _ _

/-- **The singleton `{B̄(ctr B, r₁)}` is a slab family for `(B, θ)` at `a = b`.** (S4″) — the
cone-restricted count — is `≤ 1` on a singleton against a constant
that is `≥ 1` times a square that is `≥ 1` (the `+1` of the cell count is what makes this hold
at every aperture `α ≥ 0`, including `α = 0`); (S2)-thicknesses is
`Kakeya.VeryNotSticky.hasThicknesses_closedBall_E3` at `a/b = 1`; (S2)-ball-meets is the ball's
own centre; (S3) is `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` for the containment and
`Kakeya.VeryNotSticky.axisAngle_le_two` against `2θ ≥ 2` for the angle, and (S3′) is the same
bound against `2 (a/b) = 2` — which is why the re-cut costs the degenerate route nothing
(`Kakeya.VeryNotSticky.a_div_b_eq_one`). The assignment in (S3) is the constant map
`slabOf := fun _ => degenerateSlab cfg B`. -/
theorem isSlabFamily_degenerate (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ') (hab : cfg.a = cfg.b) :
    IsSlabFamily cfg B ta.sel ta.θ {degenerateSlab cfg B}
      (fun _ => degenerateSlab cfg B) where
  finite := Set.finite_singleton _
  S2_thicknesses := by
    intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    rw [degenerateSlab_carrier, a_div_b_eq_one cfg hab, NNReal.coe_one, one_mul]
    exact hasThicknesses_closedBall_E3 bd.hC₀ _ (NNReal.coe_nonneg _)
  S2_ball_meets := by
    intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    refine ⟨bd.ctr B, ?_, Metric.mem_closedBall_self (NNReal.coe_nonneg _)⟩
    rw [degenerateSlab_carrier]
    exact Metric.mem_closedBall_self (NNReal.coe_nonneg _)
  S3 := by
    intro j hj
    have hjB : j ∈ bd.bodies B := (tc.thinBall hB).bodies'_subset (ta.hsel hj)
    refine ⟨Set.mem_singleton _, ?_, ?_⟩
    · rw [degenerateSlab_carrier]
      exact bd.bodies_subset_ball B hB j hjB
    · have h1 : (1 : ℝ) ≤ ta.θ := by exact_mod_cast ta.one_le_theta hab
      calc axisAngle (bd.Wb j) (degenerateSlab cfg B) ≤ 2 := axisAngle_le_two _ _
        _ = 2 * 1 := (mul_one 2).symm
        _ ≤ 2 * (ta.θ : ℝ) := by gcongr
  S3_ratio := by
    intro j _
    rw [a_div_b_eq_one cfg hab, NNReal.coe_one]
    calc axisAngle (bd.Wb j) (degenerateSlab cfg B) ≤ 2 := axisAngle_le_two _ _
      _ = 2 * 1 := (mul_one 2).symm
  S4'' := by
    intro x v α hα
    have hsub : {S ∈ ({degenerateSlab cfg B} :
        Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) |
        x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) v ≤ α} ⊆
        {degenerateSlab cfg B} := Set.sep_subset _ _
    have hcard : {S ∈ ({degenerateSlab cfg B} :
        Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) |
        x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) v ≤ α}.ncard ≤ 1 := by
      calc _ ≤ ({degenerateSlab cfg B} :
            Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton _)
        _ = 1 := Set.ncard_singleton _
    have hcardR : ((({S ∈ ({degenerateSlab cfg B} :
        Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) |
        x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) v ≤ α}.ncard : ℕ) : ℝ)) ≤ 1 := by
      exact_mod_cast hcard
    have hq0 : (0 : ℝ) ≤ ((cfg.a / cfg.b : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hfrac : (0 : ℝ) ≤ α / ((cfg.a / cfg.b : NNReal) : ℝ) := div_nonneg hα hq0
    have hCov1 : (1 : ℝ) ≤ (slabConeCountConstant bd.C₀ : ℝ) := by
      exact_mod_cast one_le_slabConeCountConstant bd.hC₀
    nlinarith [hcardR, hfrac, hCov1]

/-! ### The multiplicity constant `Cμ` -/

/-- **The multiplicity constant of the degenerate package**: the least value admissible for
`Kakeya.VeryNotSticky.IsSlabDecompMultConstant`, `(100/99) · C^fib(C₀, Ctyp)` with
`C^fib = Kakeya.VeryNotSticky.slabDecompFibreConstant`. It is `∝ Ctyp²` and carries no power of
`δ`. -/
noncomputable def degenerateCμ (C₀ Ctyp : NNReal) : NNReal :=
  (100 / 99 : NNReal) * slabDecompFibreConstant C₀ Ctyp

theorem isSlabDecompMultConstant_degenerateCμ (C₀ Ctyp : NNReal) :
    IsSlabDecompMultConstant C₀ Ctyp (degenerateCμ C₀ Ctyp) := ⟨le_rfl⟩

/-- The `Ctyp`-free factor of `Kakeya.VeryNotSticky.degenerateCμ`:
`degenerateCμ C₀ Ctyp = degenerateCμConstant C₀ · Ctyp²`. -/
noncomputable def degenerateCμConstant (C₀ : NNReal) : NNReal :=
  (100 / 99 : NNReal) * NonSlab.coneDirectionCountConstant * (3 * (2 ^ 10 * C₀ ^ 4)) ^ 2 * 16

theorem degenerateCμ_eq (C₀ Ctyp : NNReal) :
    degenerateCμ C₀ Ctyp = degenerateCμConstant C₀ * Ctyp ^ 2 := by
  unfold degenerateCμ degenerateCμConstant slabDecompFibreConstant slabConeCountConstant
    slabAxisSeparationConstant
  rw [div_inv_eq_mul]
  ring

/-- **The fixed-scale threshold `Cμ ≤ δ^{-τ'}` of `SlabPackage.Cμ_le`, for small `δ`.** With
`Ctyp ≤ (δ^{1-exscal})^{-η/256}` (`TypicalAngleData.hCtyp`) the constant is at most
`degenerateCμConstant C₀ · δ^{-(1-exscal)η/128}`, and `(1-exscal)η/128 < τ'` follows from `η < τ'`
(at the consumer, `Kakeya.VeryNotSticky.CaseParams.thick` and `Kakeya.VeryNotSticky.CaseParams.hτ'`
give `2^20 η < τ < τ'`). Stated for every `Ctyp` at once, since `ta.Ctyp` is only available under
the `∀ᶠ`. -/
theorem eventually_degenerateCμ_le (C₀ : NNReal) {exscal η τ' : ℝ} (hη : 0 < η)
    (hexscal : 0 ≤ exscal) (hητ' : η < τ') :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ Ctyp : NNReal,
      Ctyp ≤ (d ^ (1 - exscal)) ^ (-(η / 256)) →
      ((degenerateCμ C₀ Ctyp : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-τ') := by
  have hqp : -τ' < (1 - exscal) * (-(η / 256)) * 2 := by
    have h1 : 0 ≤ exscal * η := mul_nonneg hexscal hη.le
    have h2 : (1 - exscal) * (-(η / 256)) * 2 = -(η / 128) + exscal * η / 128 := by ring
    rw [h2]; linarith
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow (degenerateCμConstant C₀) hqp,
    self_mem_nhdsWithin] with d hd hd0
  intro Ctyp hCtyp
  have hdne : d ≠ 0 := (Set.mem_Ioi.mp hd0).ne'
  have hpow : ((d ^ (1 - exscal)) ^ (-(η / 256))) ^ 2 =
      d ^ ((1 - exscal) * (-(η / 256)) * 2) := by
    rw [← NNReal.rpow_mul, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    norm_num
  have h3 : degenerateCμ C₀ Ctyp ≤ d ^ (-τ') := by
    rw [degenerateCμ_eq]
    calc degenerateCμConstant C₀ * Ctyp ^ 2
        ≤ degenerateCμConstant C₀ * d ^ ((1 - exscal) * (-(η / 256)) * 2) := by
          gcongr
          rw [← hpow]
          exact pow_le_pow_left₀ (by positivity) hCtyp 2
      _ ≤ d ^ (-τ') := hd
  rw [← ENNReal.coe_rpow_of_ne_zero hdne, ENNReal.coe_le_coe]
  exact h3

/-! ### The `Δ_max` constant `CΔ` -/

/-- **The `Δ_max` constant of the degenerate package**, `2^10 C₀³ Cbias`:
`δ`-free, dominating the cardinality constant `2^10 C₀³` of
`Kakeya.VeryNotSticky.IsSlabDeltamaxConstant` and the constant `Cbias` of
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering`. -/
noncomputable def degenerateCΔ (C₀ Cbias : NNReal) : NNReal := 2 ^ 10 * C₀ ^ 3 * Cbias

theorem one_le_two_pow_ten_mul_pow_three {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    (1 : NNReal) ≤ 2 ^ 10 * C₀ ^ 3 :=
  one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hC₀)

theorem isSlabDeltamaxConstant_degenerateCΔ {C₀ Cbias : NNReal} (hC₀ : 1 ≤ C₀)
    (hCb : 1 ≤ Cbias) : IsSlabDeltamaxConstant C₀ (degenerateCΔ C₀ Cbias) where
  one_le := one_le_mul_of_one_le_of_one_le (one_le_two_pow_ten_mul_pow_three hC₀) hCb
  card_le := le_mul_of_one_le_right (by positivity) hCb

theorem Cbias_le_degenerateCΔ {C₀ : NNReal} (Cbias : NNReal) (hC₀ : 1 ≤ C₀) :
    Cbias ≤ degenerateCΔ C₀ Cbias :=
  le_mul_of_one_le_left (by positivity) (one_le_two_pow_ten_mul_pow_three hC₀)

/-- **The fixed-scale threshold `CΔ ≤ δ^{-ϱ/2}` of `SlabPackage.CΔ_le`, for small `δ`**: a `δ`-free constant against a negative power. -/
theorem eventually_degenerateCΔ_le (C₀ Cbias : NNReal) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ((degenerateCΔ C₀ Cbias : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-(ϱ / 2)) := by
  filter_upwards [eventually_nnreal_le_rpow_neg (degenerateCΔ C₀ Cbias) (half_pos hϱ),
    self_mem_nhdsWithin] with d hd hd0
  have hdne : d ≠ 0 := (Set.mem_Ioi.mp hd0).ne'
  rw [← ENNReal.coe_rpow_of_ne_zero hdne, ENNReal.coe_le_coe]
  exact hd

/-! ### Clause (A3) from anti-clustering -/

/-- **Clause (A3) for every affine equivalence `L`, from (C4) alone.** `Δ_max` of the realised
family `V` of `L(𝕎''_S)` is `Δ_max` of `L(𝕎''_S)` (`Kakeya.maxDensity_congr` on carriers), at most
`Δ_max` of `L(𝕎_B)` (`Kakeya.maxDensity_mono` along `Wd ⊆ ta.sel ⊆ 𝕎'_B ⊆ 𝕎_B`), which is `Δ_max`
of `𝕎_B` (`Kakeya.maxDensity_affineImage`), which is at most `Cbias δ^{-2ϱ}` — GWZ (83) at `U = B`
(`gwz.txt` l.1962, l.2380–2385) as recorded by
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering` — and `Cbias ≤ CΔ`. This is the affine invariance used in clause (A3). -/
theorem isKatzTao_affineImage_of_antiClustering (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ') {Wd : Finset bd.ω} (hWd : Wd ⊆ ta.sel)
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) {CΔ : NNReal}
    (hCΔ : bd.Cbias ≤ CΔ) :
    ∀ V : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
      (∀ j ∈ Wd, (V j).carrier = L '' (bd.Wb j).carrier) →
      ConvexSpaceBody.IsKatzTao Wd V ((CΔ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))) := by
  intro V hV
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  have hsub : Wd ⊆ bd.bodies B := hWd.trans (ta.hsel.trans (tc.thinBall hB).bodies'_subset)
  have hVeq : ∀ j ∈ Wd, V j = (bd.Wb j).affineImage L.toAffineMap hcont := by
    intro j hj
    apply ConvexSpaceBody.ext
    exact hV j hj
  rw [ConvexSpaceBody.IsKatzTao_def, maxDensity_congr hVeq]
  calc maxDensity Wd (fun j => (bd.Wb j).affineImage L.toAffineMap hcont)
      ≤ maxDensity (bd.bodies B) (fun j => (bd.Wb j).affineImage L.toAffineMap hcont) :=
        maxDensity_mono _ hsub
    _ = maxDensity (bd.bodies B) bd.Wb := maxDensity_affineImage _ _ L hcont
    _ ≤ (bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := bd.bodies_antiClustering B hB
    _ ≤ (CΔ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by gcongr

/-! ### The isotropic rescaling `B → B₁` -/

/-- **The change of variables at `a = b`**: the homothety `x ↦ r₁⁻¹ (x - ctr B)` carrying
`B̄(ctr B, r₁)` onto the unit ball — GWZ's "linear change of variables that converts `S` to `B₁`"
(`gwz.txt` l.2378–2379) for the one slab `S = B`. -/
noncomputable def degenerateRescale (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (B : bd.bι) :
    EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  plankRescale (bd.ctr B) (r₁_pos cfg).ne'

theorem degenerateRescale_image_ball (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (B : bd.bι) :
    degenerateRescale cfg B '' Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ) =
      Metric.closedBall 0 1 := by
  unfold degenerateRescale
  rw [plankRescale_image_closedBall (bd.ctr B) (r₁_pos cfg), plankRescale_apply, sub_self,
    smul_zero, div_self (r₁_pos cfg).ne']

/-- Clause (A1), and the shape of clause (A1'): a subset of `B` is carried into `B₁`. -/
theorem degenerateRescale_image_subset_ball (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (B : bd.bι) {X : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : X ⊆ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) :
    degenerateRescale cfg B '' X ⊆ Metric.closedBall 0 1 := by
  rw [← degenerateRescale_image_ball cfg B]
  exact Set.image_mono hX

/-- At `a = b = δ` the rescaled profile `(1, b/r₁, a/r₁)` is `(1, ρ₂, ρ₂)`,
`ρ₂ = Kakeya.VeryNotSticky.rho2 = b/r₁`. -/
theorem degenerateProfile_eq (cfg : VeryNotSticky.{u}) (ha : cfg.a = cfg.δ) (hb : cfg.b = cfg.δ) :
    ![(1 : ℝ), (cfg.b : ℝ) / (cfg.r₁ : ℝ), (cfg.a : ℝ) / (cfg.r₁ : ℝ)] =
      ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
  simp only [rho2, NNReal.coe_div, ha, hb]

/-- **Clause (A2)**: `Kakeya.VeryNotSticky.BallData.bodies_thickness` transported by
`Kakeya.VeryNotSticky.hasThicknesses_plankRescale_image`. -/
theorem hasThicknesses_degenerateRescale_body (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {B : bd.bι} (hB : B ∈ bd.bs) {j : bd.ω} (hj : j ∈ bd.bodies B)
    (ha : cfg.a = cfg.δ) (hb : cfg.b = cfg.δ) :
    HasThicknesses (degenerateRescale cfg B '' (bd.Wb j).carrier) bd.C₀
      ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
  rw [← degenerateProfile_eq cfg ha hb]
  exact hasThicknesses_plankRescale_image (bd.ctr B) bd.hC₀ (r₁_pos cfg)
    (bd.Wb j).isCompact'.isBounded (bd.bodies_thickness B hB j hj)

/-- `ConvexSpaceBody.scale` is a thickness, hence nonnegative. -/
theorem bodyScale_nonneg (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : 0 ≤ K.scale :=
  Metric.thickness_nonneg _ _

/-- In `ℝ³`, `ConvexSpaceBody.scale` is the rank-`2` thickness, the shortest dimension. -/
theorem bodyScale_eq_thickness_two (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    K.scale = Metric.thickness ℝ K.carrier 2 := by
  change Metric.thickness ℝ K.carrier (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) = _
  rw [finrank_euclideanSpace_fin]

/-- The closed `scale`-neighbourhood of a body keeps its thickness profile at the doubled
constant (`ConvexSpaceBody.hasThicknesses_cthickening` at `r = scale`). -/
theorem hasThicknesses_cthickening_scale (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    {C₀ : NNReal} {t : Fin 3 → ℝ} (ht : ∀ k, 0 ≤ t k) (hK : HasThicknesses K.carrier C₀ t) :
    HasThicknesses (K.cthickening K.scale).carrier (2 * C₀) t := by
  have h := ConvexSpaceBody.hasThicknesses_cthickening K (Real.toNNReal K.scale)
    (by rw [Real.coe_toNNReal _ (bodyScale_nonneg K)]) ht hK
  rwa [Real.coe_toNNReal _ (bodyScale_nonneg K)] at h

/-- **Clause (A2')**: the profile of the `scale`-neighbourhood at `2C₀`, transported. -/
theorem hasThicknesses_degenerateRescale_cthickening (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} {B : bd.bι} (hB : B ∈ bd.bs) {j : bd.ω} (hj : j ∈ bd.bodies B)
    (ha : cfg.a = cfg.δ) (hb : cfg.b = cfg.δ) :
    HasThicknesses (degenerateRescale cfg B '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier)
      (2 * bd.C₀) ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
  rw [← degenerateProfile_eq cfg ha hb]
  have ht : ∀ k : Fin 3, 0 ≤ ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] k := by
    intro k; fin_cases k <;> simp
  have hC₀ : (1 : NNReal) ≤ 2 * bd.C₀ :=
    bd.hC₀.trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  exact hasThicknesses_plankRescale_image (bd.ctr B) hC₀ (r₁_pos cfg)
    ((bd.Wb j).cthickening _).isCompact'.isBounded
    (hasThicknesses_cthickening_scale _ ht (bd.bodies_thickness B hB j hj))

/-! ### The margin bridge: clause (A1') from a half-ball containment -/

/-- **The margin from the half ball.** A body of profile `(r₁, b, a)` at `C₀` inside
`B̄(c, r₁/2)` has `scale ≤ C₀ a`, so when `C₀ a ≤ r₁/2` its closed `scale`-neighbourhood stays in
`B̄(c, r₁)`. This is the form in which a (C4) field `bodies_subset_ball` at `r₁/2` would supply the
margin of clause (A1'), for small `δ` (`Kakeya.VeryNotSticky.eventually_C₀_mul_le_half_r₁`). -/
theorem cthickening_scale_subset_closedBall_of_half
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {c : EuclideanSpace ℝ (Fin 3)}
    {C₀ : NNReal} {r₁ b a : ℝ} (hK : K.carrier ⊆ Metric.closedBall c (r₁ / 2))
    (hthick : HasThicknesses K.carrier C₀ ![r₁, b, a]) (ha : (C₀ : ℝ) * a ≤ r₁ / 2) :
    Metric.cthickening K.scale K.carrier ⊆ Metric.closedBall c r₁ := by
  have hs0 : 0 ≤ K.scale := bodyScale_nonneg K
  have hr₁ : 0 ≤ r₁ / 2 := Metric.nonempty_closedBall.mp (K.nonempty'.mono hK)
  have hs : K.scale ≤ r₁ / 2 := by
    have h2 := (hthick 2).2
    rw [bodyScale_eq_thickness_two]
    simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
    exact le_trans (by simpa using h2) ha
  calc Metric.cthickening K.scale K.carrier
      ⊆ Metric.cthickening K.scale (Metric.closedBall c (r₁ / 2)) :=
        Metric.cthickening_subset_of_subset _ hK
    _ = Metric.closedBall c (K.scale + r₁ / 2) := cthickening_closedBall hs0 hr₁ c
    _ ⊆ Metric.closedBall c r₁ := Metric.closedBall_subset_closedBall (by linarith)

/-- `C₀ δ ≤ δ^{exscal}/2` for small `δ` when `exscal < 1`: the threshold under which the half
ball supplies the margin (`a = δ`, `r₁ = δ^{exscal}`). -/
theorem eventually_C₀_mul_le_half_r₁ (C₀bd : NNReal) {exscal : ℝ} (hex1 : exscal < 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      (C₀bd : ℝ) * (d : ℝ) ≤ ((d ^ exscal : NNReal) : ℝ) / 2 := by
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow (2 * C₀bd) (p := 1) (q := exscal) hex1]
    with d hd
  rw [NNReal.rpow_one] at hd
  have h := NNReal.coe_le_coe.mpr hd
  push_cast at h ⊢
  linarith

/-! ### The package -/

/-- **The degenerate slab package, given the margin of clause (A1').** All of the package is
closed from the fields of `bd` and `ta` and the two fixed-scale thresholds `hCμ`, `hCΔ`
(supplied for small `δ` by `Kakeya.VeryNotSticky.eventually_degenerateCμ_le` and
`Kakeya.VeryNotSticky.eventually_degenerateCΔ_le`), except clause (A1'), which is exactly
`hmargin` pulled through the homothety: the closed `scale`-neighbourhood of every body of `𝕎_B`
lies in `B̄(ctr B, r₁)`. See the module docstring for why `hmargin` is not a consequence of
`Kakeya.VeryNotSticky.BallData.bodies_subset_ball`. -/
theorem exists_slabPackage_degenerate_of_margin (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (ha : cfg.a = cfg.δ) (hb : cfg.b = cfg.δ) {τ' : ℝ}
    (hCμ : ∀ Ctyp : NNReal, Ctyp ≤ (cfg.δ ^ (1 - cfg.exscal)) ^ (-(cfg.η / 256)) →
      ((degenerateCμ bd.C₀ Ctyp : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-τ'))
    (hCΔ : ((degenerateCΔ (latticeRescaleConstant bd.C₀) bd.Cbias : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)))
    {B : bd.bι} (hB : B ∈ bd.bs)
    (hmargin : ∀ j ∈ bd.bodies B,
      Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
        Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ))
    (ta : TypicalAngleData cfg tc hB τ') :
    Nonempty (SlabPackage cfg ta) := by
  have hab : cfg.a = cfg.b := ha.trans hb.symm
  refine ⟨{ 𝕊 := {degenerateSlab cfg B}
            slabOf := fun _ => degenerateSlab cfg B
            isSlabFamily := isSlabFamily_degenerate cfg tc hB ta hab
            Cμ := degenerateCμ bd.C₀ ta.Ctyp
            CμAdmissible := isSlabDecompMultConstant_degenerateCμ _ _
            Cμ_le := hCμ ta.Ctyp ta.hCtyp
            L := fun _ => degenerateRescale cfg B
            CΔ := degenerateCΔ (latticeRescaleConstant bd.C₀) bd.Cbias
            CΔAdmissible := isSlabDeltamaxConstant_degenerateCΔ
              (one_le_latticeRescaleConstant bd.hC₀) bd.hCbias
            CΔ_le := hCΔ
            rescale := ?_ }⟩
  intro S Wd hslab
  have hjB : ∀ j ∈ Wd, j ∈ bd.bodies B := fun j hj =>
    (tc.thinBall hB).bodies'_subset (ta.hsel (hslab.subset hj))
  -- the homothety delivers (A2)/(A2′) at `bd.C₀`; the clauses are read at the aligned constant
  -- (re-cuts R3/R4), which is larger, so they weaken into it — the degenerate route pays
  -- nothing for the re-cut.
  have hCal : bd.C₀ ≤ latticeRescaleConstant bd.C₀ :=
    le_latticeRescaleConstant bd.hC₀
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have htk : ∀ k : Fin 3, (0 : ℝ) ≤ (![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]) k := by
    intro k
    fin_cases k <;> simp
  exact
    { A1 := fun j hj => degenerateRescale_image_subset_ball cfg B
        (bd.bodies_subset_ball B hB j (hjB j hj))
      A1' := fun j hj => by
        rw [ConvexSpaceBody.cthickening_carrier]
        exact degenerateRescale_image_subset_ball cfg B (hmargin j (hjB j hj))
      A2 := fun j hj => hasThicknesses_mono_const hC₀pos hCal htk
        (hasThicknesses_degenerateRescale_body cfg hB (hjB j hj) ha hb)
      A2' := fun j hj => hasThicknesses_mono_const (by positivity)
        (by gcongr) htk
        (hasThicknesses_degenerateRescale_cthickening cfg hB (hjB j hj) ha hb)
      A3 := isKatzTao_affineImage_of_antiClustering cfg tc hB ta hslab.subset
        (degenerateRescale cfg B) (Cbias_le_degenerateCΔ bd.Cbias
          (one_le_latticeRescaleConstant bd.hC₀)) }

/-! ### Conjunct 3 of `SideDataObligations` — the margin as its inner hypothesis -/

/-- **Conjunct 3 of `Kakeya.VeryNotSticky.SideDataObligations`, verbatim**: the margin of clause (A1') is an inner hypothesis placed after the
conjunct's pins — for small `δ`, every configuration at `(δ, β, η, exscal, ϱ)` on the degenerate
path and every `bd` at `(C₀bd, Cbias)` whose bodies have their closed `scale`-neighbourhoods
inside their ball has a slab package at every ball and every typical-angle datum. Tripwire A
below closes the conjunct, spelled out, by this theorem, and tripwire B projects the same text
out of the `Prop`; the margin is what conjunct 1 promises (module docstring). -/
theorem sideDataObligations_conjunct3_of_margin {β exscal ϱ η τ' : ℝ} (hη : 0 < η)
    (hexscal : 0 ≤ exscal) (hϱ : 0 < ϱ) (hητ' : η < τ') (C₀bd Cbias : NNReal) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a = cfg.δ → cfg.b = cfg.δ → bd.C₀ = C₀bd → bd.Cbias = Cbias →
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
          Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
      ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
        Nonempty (SlabPackage cfg ta) := by
  filter_upwards [eventually_degenerateCμ_le C₀bd hη hexscal hητ',
    eventually_degenerateCΔ_le (latticeRescaleConstant C₀bd) Cbias hϱ] with d hCμ hCΔ
  intro cfg bd tc hδ _ hη' hex hϱ' ha hb hC₀ hCb hmargin B hB ta
  refine exists_slabPackage_degenerate_of_margin cfg tc ha hb ?_ ?_ hB (hmargin B hB) ta
  · intro Ctyp hCtyp
    rw [hδ, hex, hη'] at hCtyp
    rw [hδ, hC₀]
    exact hCμ Ctyp hCtyp
  · rw [hδ, hC₀, hCb, hϱ']
    exact hCΔ

/-- **Conjunct 3 with the half-ball containment as the inner hypothesis**: if the bodies of every
ball lie in `B̄(ctr B, r₁/2)` — a (C4) text `bodies_subset_ball` at `r₁/2` would say so — the
margin follows for small `δ` from `C₀ δ ≤ r₁/2` (`exscal < 1`), and the package exists. -/
theorem sideDataObligations_conjunct3_of_half_ball {β exscal ϱ η τ' : ℝ} (hη : 0 < η)
    (hexscal : 0 ≤ exscal) (hex1 : exscal < 1) (hϱ : 0 < ϱ) (hητ' : η < τ')
    (C₀bd Cbias : NNReal) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a = cfg.δ → cfg.b = cfg.δ → bd.C₀ = C₀bd → bd.Cbias = Cbias →
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) ((cfg.r₁ : ℝ) / 2)) →
      ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
        Nonempty (SlabPackage cfg ta) := by
  filter_upwards [sideDataObligations_conjunct3_of_margin.{u} (β := β) hη hexscal hϱ hητ'
    C₀bd Cbias, eventually_C₀_mul_le_half_r₁ C₀bd hex1] with d h hd
  intro cfg bd tc hδ hβ hη' hex hϱ' ha hb hC₀ hCb hhalf B hB ta
  refine h cfg bd tc hδ hβ hη' hex hϱ' ha hb hC₀ hCb ?_ hB ta
  intro B' hB' j hj
  refine cthickening_scale_subset_closedBall_of_half (hhalf B' hB' j hj)
    (bd.bodies_thickness B' hB' j hj) ?_
  have hr₁ : (cfg.r₁ : ℝ) = ((d ^ exscal : NNReal) : ℝ) := by
    simp only [VeryNotSticky.r₁, hδ, hex]
  rw [hC₀, ha, hδ, hr₁]
  exact hd

/-- A slab package from an eventual containment-margin hypothesis.
The constants and scale parameters agree with those in the degenerate
side-data construction. The pointwise variant
`sideDataObligations_conjunct3_of_margin` takes the margin directly
for the given ball datum. -/
theorem sideDataObligations_conjunct3_of_eventually_margin {β exscal ϱ η τ' : ℝ} (hη : 0 < η)
    (hexscal : 0 ≤ exscal) (hϱ : 0 < ϱ) (hητ' : η < τ') (C₀bd Cbias : NNReal)
    (hmargin : ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.a = cfg.δ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd → bd.Cbias = Cbias →
      ∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
          Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) :
    (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a = cfg.δ → cfg.b = cfg.δ → bd.C₀ = C₀bd → bd.Cbias = Cbias →
      ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
        Nonempty (SlabPackage cfg ta)) := by
  filter_upwards [sideDataObligations_conjunct3_of_margin.{u} (β := β) hη hexscal hϱ hητ'
    C₀bd Cbias, hmargin] with d h hm
  intro cfg bd tc hδ hβ hη' hex hϱ' ha hb hC₀ hCb B hB ta
  exact h cfg bd tc hδ hβ hη' hex hϱ' ha hb hC₀ hCb (hm cfg bd hδ hη' hex hϱ' ha hb hC₀ hCb) hB ta

/-- **Tripwire A.** Conjunct 3 of
`Kakeya.VeryNotSticky.SideDataObligations`, spelled out, **is** the statement of
`Kakeya.VeryNotSticky.sideDataObligations_conjunct3_of_margin`: the proof is that theorem by
direct term, so this declaration fails to elaborate if either text moves. -/
example {β exscal ϱ η τ' : ℝ} (hη : 0 < η) (hexscal : 0 ≤ exscal) (hϱ : 0 < ϱ) (hητ' : η < τ')
    (C₀bd Cbias : NNReal) :
    (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a = cfg.δ → cfg.b = cfg.δ → bd.C₀ = C₀bd → bd.Cbias = Cbias →
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
          Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
      ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
        Nonempty (SlabPackage cfg ta)) :=
  sideDataObligations_conjunct3_of_margin hη hexscal hϱ hητ' C₀bd Cbias

/-- **Tripwire B.** The same text, projected out of the re-cut `Prop`: `h.2.2.1` now carries the
margin hypothesis, so this fails to elaborate if conjunct 3 of
`Kakeya.VeryNotSticky.SideDataObligations` moves. -/
example {β exscal ϱ η τ τ' : ℝ} {C₀bd Cbias CF Cdil c₁ Cg : NNReal} {D : ℕ}
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a = cfg.δ → cfg.b = cfg.δ → bd.C₀ = C₀bd → bd.Cbias = Cbias →
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
          Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
      ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
        Nonempty (SlabPackage cfg ta)) :=
  h.2.2.1

/-! ### The finding: clause (A1') fails at a body touching the sphere `∂B`

The lemmas below are compiled evidence for the module docstring's claim. They are not used by
the package. -/

/-- The `scale` of a body of profile `(r₁, b, a)` with `a > 0` is positive. -/
theorem bodyScale_pos_of_hasThicknesses {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ : NNReal} {r₁ b a : ℝ} (hC₀ : 0 < C₀) (ha : 0 < a)
    (hK : HasThicknesses K.carrier C₀ ![r₁, b, a]) : 0 < K.scale := by
  have h := (hK 2).1
  rw [bodyScale_eq_thickness_two]
  simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  have hC₀' : (0 : ℝ) < C₀ := by exact_mod_cast hC₀
  have : (0 : ℝ) < (C₀ : ℝ)⁻¹ * a := by positivity
  exact this.trans_le (by simpa using h)

/-- **No affine equivalence carries a positive neighbourhood of a body into the unit ball once a
point of the body lands on the unit sphere.** If `‖L x‖ = 1` for some `x ∈ K` and `s > 0`, then
`y = x + (s/‖u‖) u` with `u = L.linear⁻¹ (L x)` lies in `N_s(K)` and `L y = (1 + s/‖u‖) L x` has
norm `> 1`. -/
theorem not_image_cthickening_subset_of_norm_eq_one
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {s : ℝ} (hs : 0 < s)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ K.carrier) (hLx : ‖L x‖ = 1) :
    ¬ (L '' (K.cthickening s).carrier ⊆ Metric.closedBall 0 1) := by
  intro h
  have hLx0 : L x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hLx
    exact zero_ne_one hLx
  set u : EuclideanSpace ℝ (Fin 3) := L.linear.symm (L x) with hu_def
  have hLu : L.linear u = L x := by rw [hu_def, LinearEquiv.apply_symm_apply]
  have hu0 : u ≠ 0 := by
    intro h0
    apply hLx0
    rw [← hLu, h0, map_zero]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hsu : 0 < s / ‖u‖ := div_pos hs hnu
  set y : EuclideanSpace ℝ (Fin 3) := (s / ‖u‖) • u +ᵥ x with hy_def
  have hy : y ∈ (K.cthickening s).carrier := by
    rw [ConvexSpaceBody.cthickening_carrier]
    refine Metric.mem_cthickening_of_dist_le y x s K.carrier hx ?_
    rw [hy_def, vadd_eq_add, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hsu, div_mul_cancel₀ _ hnu.ne']
  have hLy : L y = (1 + s / ‖u‖) • L x := by
    rw [hy_def, AffineEquiv.map_vadd, LinearEquiv.map_smul, hLu, vadd_eq_add, add_smul,
      one_smul, add_comm]
  have hmem := h ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff, hLy, norm_smul, Real.norm_eq_abs, hLx, mul_one,
    abs_of_pos (by positivity)] at hmem
  linarith

/-- A compact set in the closed unit ball whose rank-`0` thickness (circumradius) is at least
`1` meets the unit sphere. -/
theorem exists_norm_eq_one_of_one_le_thickness_zero {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hKc : IsCompact K) (hne : K.Nonempty) (hsub : K ⊆ Metric.closedBall 0 1)
    (hth : 1 ≤ Metric.thickness ℝ K 0) : ∃ z ∈ K, ‖z‖ = 1 := by
  obtain ⟨z, hz, hmax⟩ := hKc.exists_isMaxOn hne continuous_norm.continuousOn
  refine ⟨z, hz, le_antisymm (mem_closedBall_zero_iff.mp (hsub hz)) ?_⟩
  have hK' : K ⊆ Metric.closedBall 0 ‖z‖ := fun w hw => by
    rw [mem_closedBall_zero_iff]
    exact hmax hw
  exact hth.trans (Metric.thickness_le_of_subset_closedBall (𝕜 := ℝ) hK' (norm_nonneg z) 0)

/-- **At comparison constant `1`, no affine equivalence satisfies (A1), (A1') and (A2) for a
body of the ball.** (A2) at `Cmp = 1` makes the circumradius of `L(W)` exactly `1`, (A1) puts
`L(W)` in the
unit ball, so `L(W)` meets the unit sphere
(`Kakeya.VeryNotSticky.exists_norm_eq_one_of_one_le_thickness_zero`), and then the image of the
positive `scale`-neighbourhood leaves the unit ball
(`Kakeya.VeryNotSticky.not_image_cthickening_subset_of_norm_eq_one`), against (A1'). The
obstruction is the missing margin of (C4), not the choice of `L`. -/
theorem not_isAnisotropicSlabRescale_of_Cmp_eq_one (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} {B : bd.bι} (hB : B ∈ bd.bs)
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {Wd : Finset bd.ω} {j : bd.ω} (hj : j ∈ Wd)
    (hjB : j ∈ bd.bodies B)
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (CΔ : NNReal) :
    ¬ IsAnisotropicSlabRescale cfg S Wd L 1 CΔ := by
  intro h
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  have hsub : L '' (bd.Wb j).carrier ⊆ Metric.closedBall 0 1 := h.A1 j hj
  have hth : 1 ≤ Metric.thickness ℝ (L '' (bd.Wb j).carrier) 0 := by
    have h0 := (h.A2 j hj 0).1
    simpa using h0
  obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := exists_norm_eq_one_of_one_le_thickness_zero
    ((bd.Wb j).isCompact'.image hcont) ((bd.Wb j).nonempty'.image _) hsub hth
  have ha : (0 : ℝ) < cfg.a := by
    have : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact_mod_cast this
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  exact not_image_cthickening_subset_of_norm_eq_one L (bd.Wb j)
    (bodyScale_pos_of_hasThicknesses hC₀pos ha (bd.bodies_thickness B hB j hjB)) hx hz
    (h.A1' j hj)

/-- **At comparison constant `1` a rescaling family has no dense slab**: every `(S, Wd)` with
`Kakeya.VeryNotSticky.IsDenseSlab` would have to be rescaled by `sp.L S`, which
`Kakeya.VeryNotSticky.not_isAnisotropicSlabRescale_of_Cmp_eq_one` forbids for any body of `Wd`. -/
theorem not_isDenseSlab_of_rescale_Cmp_eq_one {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    {ta : TypicalAngleData cfg tc hB τ'}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    (L : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) →
      EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (CΔ : NNReal)
    (hres : ∀ (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Wd : Finset bd.ω),
      IsDenseSlab cfg ta 𝕊 S Wd → IsAnisotropicSlabRescale cfg S Wd (L S) 1 CΔ)
    (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Wd : Finset bd.ω) :
    ¬ IsDenseSlab cfg ta 𝕊 S Wd := by
  intro hd
  obtain ⟨j, hj⟩ := hd.nonempty
  have hjB : j ∈ bd.bodies B := (tc.thinBall hB).bodies'_subset (ta.hsel (hd.subset hj))
  exact not_isAnisotropicSlabRescale_of_Cmp_eq_one cfg hB hj hjB (L S) CΔ (hres S Wd hd)

/-- The homothety carries a point of the sphere `∂B̄(ctr B, r₁)` to the unit sphere. -/
theorem norm_degenerateRescale_of_dist_eq (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (B : bd.bι) {x : EuclideanSpace ℝ (Fin 3)} (hxr : dist x (bd.ctr B) = (cfg.r₁ : ℝ)) :
    ‖degenerateRescale cfg B x‖ = 1 := by
  unfold degenerateRescale
  rw [plankRescale_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (r₁_pos cfg),
    ← dist_eq_norm, hxr, inv_mul_cancel₀ (r₁_pos cfg).ne']

/-- **Clause (A1') fails under the homothety at every body touching `∂B`.** A body of `𝕎_B` with
a point on the sphere `∂B̄(ctr B, r₁)` — permitted by
`Kakeya.VeryNotSticky.BallData.bodies_subset_ball`, which has no margin — has its closed
`scale`-neighbourhood carried outside the unit ball. -/
theorem degenerateRescale_not_A1'_of_touching (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {B : bd.bι} (hB : B ∈ bd.bs) {j : bd.ω} (hj : j ∈ bd.bodies B)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (bd.Wb j).carrier)
    (hxr : dist x (bd.ctr B) = (cfg.r₁ : ℝ)) :
    ¬ (degenerateRescale cfg B '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier ⊆
        Metric.closedBall 0 1) := by
  have ha : (0 : ℝ) < cfg.a := by
    have : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact_mod_cast this
  have hC₀ : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  exact not_image_cthickening_subset_of_norm_eq_one (degenerateRescale cfg B) (bd.Wb j)
    (bodyScale_pos_of_hasThicknesses hC₀ ha (bd.bodies_thickness B hB j hj)) hx
    (norm_degenerateRescale_of_dist_eq cfg B hxr)

end Kakeya.VeryNotSticky

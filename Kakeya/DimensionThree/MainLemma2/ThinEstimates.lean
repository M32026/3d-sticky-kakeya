/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinSetup
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Shared density and transfer estimates for the thin case of Main Lemma 2

This file contains the estimates shared by the slab and transverse branches of the thin case.

Everything the thin case needs about the interaction of the tube segments `𝕋_B` with the
factoring bodies `𝕎'_B` is contained in a single density estimate on *centred* `A`-balls,
`Kakeya.ThinCase.ballDensity`, with `A = C_{w₁} a` as in blueprint
`def:ml2thinW1Constant`. It comes in two halves: one ball in which `U(𝕋_B, Y'_B)` is dense
(`Kakeya.ThinCase.oneDenseBall`), and the comparability (T4)(c) which spreads that ball to
every point of `U(𝕋_B, Y'_B)`. Two consequences are drawn from it, one global
(`Kakeya.ThinCase.unionLower`, with its thin-case reformulation
`Kakeya.ThinCase.unionLower_thin`) and one localized to a ball
(`Kakeya.ThinCase.transfer`, with its thin-case reformulation
`Kakeya.ThinCase.transfer_thin`, used by the transverse case); both go through the same
separated-net upper and lower bounds `Kakeya.ThinCase.netUpper`,
`Kakeya.ThinCase.netLower`.

-/

@[expose] public section

namespace Kakeya.ThinCase

open MeasureTheory Metric Set ShadedBody

section Density

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {C C₀ : NNReal} {σ ω : Type*} [DecidableEq ω] {segs : Finset σ} {Y : σ → ShadedBody E}
  {bodies : Finset ω} {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {δ a : NNReal} {η : ℝ}

/-! Each of the separated-net lemmas below carries its own constant, as required by
: `unionLower` and `transfer` *compose* `netUpper` with `netLower`, so they cannot
share a constant with either.

All of these constants are functions of the comparison constant `C` of Definition
`hyp:ml2thinsetup` and of the thickness comparison constant `C₀` of (C4) — the latter because
every covering argument below runs at the radius `A = rad C₀ a`, while the conclusions are
normalized by the volume of an `a`-ball. In particular none of them depends on the ball `B`,
on `δ`, or on the scales `a`, `b`. This ball-independence is what allows the estimates below
to be summed over `B ∈ 𝔅`.

The separated-net losses also depend on the ambient dimension, which is why every lemma using
one of these constants carries the hypothesis `Module.finrank ℝ E = 3`; the whole section is
about the three-dimensional Kakeya problem, and the powers `(δ/a)³` appearing below are false
in any other dimension. The displayed values are provisional; the exact values come out of the
proofs. -/

/-- **Constant in Lemma `lem:ml2thinBallDensity`.**

The loss in passing from the single dense ball of `Kakeya.ThinCase.oneDenseBall` to every
centred `A`-ball: a factor `C` from (T5), a factor `C` from the comparability (T4)(c), and the
cardinality `separatedNetCoverConstant 3 = 5³` of a maximal `A`-separated subset of a
`2A`-ball in dimension three (blueprint `lem:separatedNetCard` with `R = 2A`, `r = A`). -/
noncomputable def ballDensityConstant (C : NNReal) : NNReal :=
  max 1 ((separatedNetCoverConstant 3 : NNReal) * C ^ 2)

lemma one_le_ballDensityConstant (C : NNReal) : 1 ≤ ballDensityConstant C := le_max_left _ _

/-- **Constant in Lemma `lem:ml2thinNetUpper`.**

The loss in bounding `|U(𝕎'_B, Y_{𝕎'_B})|` by `|𝒩| a³`: the bounded-overlap constant
`separatedNetCoverConstant 3` of the cover of `N_A(U)` by the balls `B(y, 2A)`, `y ∈ 𝒩`,
times the volume ratio `|B(0, 2A)| / |B(0, a)| = (2 · w1Constant C₀)³`.

The dependence on the thickness comparison constant `C₀` of (C4) is *not* removable: the
radius at which the covering argument runs is `A = rad C₀ a = w1Constant C₀ * a`, not `a`,
and the conclusion of `Kakeya.ThinCase.netUpper` is normalized by `|B(0, a)|`. Nothing in
`Kakeya.ThinCase.ThinBall` relates `C` to `C₀`, so a constant depending on `C` alone would
make the lemma false. The factor `2 ^ 12` dominates `separatedNetCoverConstant 3 · 2³`. -/
noncomputable def netUpperConstant (C C₀ : NNReal) : NNReal :=
  max 1 (2 ^ 12 * C ^ 3 * (1 + w1Constant C₀) ^ 3)

lemma one_le_netUpperConstant (C C₀ : NNReal) : 1 ≤ netUpperConstant C C₀ := le_max_left _ _

/-- **Constant in Lemma `lem:ml2thinNetLower`.**

The loss in bounding `|U(𝕋_B, Y'_B) ∩ F|` from below by `|𝒩'| δ^η δ³`: the density constant
`ballDensityConstant C` of `Kakeya.ThinCase.ballDensity` at each ball of the net, times the
pointwise overlap bound `separatedNetCoverConstant 3` of the `A`-balls at an `A`-separated
set (blueprint `lem:separatedNetOverlapBound`).

No factor of `C₀` is needed here: both sides of the conclusion are stated at the radius `δ`,
and the radius `A` enters only through the overlap bound, which is scale-invariant. -/
noncomputable def netLowerConstant (C : NNReal) : NNReal :=
  max 1 ((separatedNetCoverConstant 3 : NNReal) * ballDensityConstant C)

lemma one_le_netLowerConstant (C : NNReal) : 1 ≤ netLowerConstant C := le_max_left _ _

/-- **Constant in Lemma `lem:ml2thinUnionLower`.**

Eliminating the net cardinality between `Kakeya.ThinCase.netUpper` and
`Kakeya.ThinCase.netLower` multiplies the two losses, so this constant is their product; it
is *not* the constant of either lemma. It inherits the dependence on `C₀` from
`netUpperConstant`. -/
noncomputable def unionLowerConstant (C C₀ : NNReal) : NNReal :=
  netUpperConstant C C₀ * netLowerConstant C

lemma one_le_unionLowerConstant (C C₀ : NNReal) : 1 ≤ unionLowerConstant C C₀ := by
  change (1 : NNReal) ≤ netUpperConstant C C₀ * netLowerConstant C
  simpa using mul_le_mul' (one_le_netUpperConstant C C₀) (one_le_netLowerConstant C)

/-- **Constant in Lemma `lem:ml2thinTransfer`.**

The localized counterpart of `unionLowerConstant`. It is again a product of the losses of
`Kakeya.ThinCase.netUpper` and `Kakeya.ThinCase.netLower`, with an extra factor `2³` for the
doubling of the radius: the cover balls carrying the mass of `U(𝕎'_B, Y_{𝕎'_B}) ∩ B_r` stick
out of `B_r` by `O(a)`, so the conclusion is about `B_{2r}`. -/
noncomputable def transferConstant (C C₀ : NNReal) : NNReal :=
  2 ^ 3 * netUpperConstant C C₀ * netLowerConstant C

lemma one_le_transferConstant (C C₀ : NNReal) : 1 ≤ transferConstant C C₀ := by
  change (1 : NNReal) ≤ 2 ^ 3 * netUpperConstant C C₀ * netLowerConstant C
  simpa using mul_le_mul'
    (mul_le_mul' (by norm_num : (1 : NNReal) ≤ 2 ^ 3) (one_le_netUpperConstant C C₀))
    (one_le_netLowerConstant C)

/-- **One centred ball in which the tube segments are dense** (blueprint
`lem:ml2thinOneDenseBall`).

Picking a segment of the non-empty subfamily `𝒮_B` and the `δ`-ball supplied for it by
(T5), any point `x₀` of the (positive-measure) intersection of that ball with the shading
witnesses `|U(𝕋_B, Y'_B) ∩ B(x₀, 2A)| ≳ δ^η δ³`, since the `δ`-ball is contained in
`B(x₀, 2δ) ⊆ B(x₀, 2A)`. -/
theorem oneDenseBall (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η)
    (hδ : 0 < δ) (hδa : δ ≤ a) :
    ∃ x₀ ∈ tb.U, (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball x₀ (δ : ℝ)) ≤
      volume (tb.U ∩ ball x₀ (2 * (rad C₀ a : ℝ))) := by
  obtain ⟨p, hpS⟩ := tb.S_nonempty
  have hpseg : p ∈ segs := tb.S_subset hpS
  obtain ⟨x, hx⟩ := tb.denseBall p hpS
  have hδrpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hvol_ne0 : volume (ball x (δ : ℝ)) ≠ 0 :=
    (Metric.measure_ball_pos volume x hδrpos).ne'
  have hδe_pos : 0 < (δ : ENNReal) := by exact_mod_cast hδ
  have hδe_ne_top : (δ : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
  have hδpow_ne0 : (δ : ENNReal) ^ η ≠ 0 := (ENNReal.rpow_pos hδe_pos hδe_ne_top).ne'
  have hC_ne_top : (C : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
  have hprod_ne0 : (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball x (δ : ℝ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hC_ne_top) hδpow_ne0) hvol_ne0
  have hhx_pos : 0 < volume (ball x (δ : ℝ) ∩ (tb.Y' p).shade) :=
    lt_of_lt_of_le (pos_iff_ne_zero.mpr hprod_ne0) hx
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero (μ := volume) (ne_of_gt hhx_pos)
  have hx₀ball : x₀ ∈ ball x (δ : ℝ) := hx₀.1
  have hx₀shade : x₀ ∈ (tb.Y' p).shade := hx₀.2
  have hdx₀ : dist x x₀ < δ := by
    simpa [dist_comm] using Metric.mem_ball.mp hx₀ball
  have hshadeU : (tb.Y' p).shade ⊆ tb.U := by
    intro z hz
    exact mem_iUnion₂.mpr ⟨p, hpseg, hz⟩
  have hle_rad : δ ≤ (rad C₀ a : ℝ) := by
    have ha_le : (a : ℝ) ≤ (rad C₀ a : ℝ) := by
      simpa [rad] using
        le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ (a : ℝ))
          (by exact_mod_cast (one_le_w1Constant C₀))
    exact le_trans (by exact_mod_cast hδa) ha_le
  have hball_subset : ball x (δ : ℝ) ⊆ ball x₀ (2 * (rad C₀ a : ℝ)) := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have hzle : 2 * (δ : ℝ) ≤ 2 * (rad C₀ a : ℝ) := by gcongr
    have hlt : dist z x₀ < 2 * (δ : ℝ) := by
      calc
        dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle z x x₀
        _ < δ + δ := add_lt_add hz hdx₀
        _ = 2 * (δ : ℝ) := by ring
    exact lt_of_lt_of_le hlt hzle
  have hsubset : ball x (δ : ℝ) ∩ (tb.Y' p).shade ⊆
      tb.U ∩ ball x₀ (2 * (rad C₀ a : ℝ)) := by
    intro z hz
    exact ⟨hshadeU hz.2, hball_subset hz.1⟩
  refine ⟨x₀, hshadeU hx₀shade, ?_⟩
  calc
    (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball x₀ (δ : ℝ))
        = (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball x (δ : ℝ)) := by
        rw [MeasureTheory.Measure.addHaar_ball_center volume x₀ (δ : ℝ)]
        rw [MeasureTheory.Measure.addHaar_ball_center volume x (δ : ℝ)]
    _ ≤ volume (ball x (δ : ℝ) ∩ (tb.Y' p).shade) := hx
    _ ≤ volume (tb.U ∩ ball x₀ (2 * (rad C₀ a : ℝ))) := measure_mono hsubset

/-- **Density of the tube segments in a centred `A`-ball** (blueprint
`lem:ml2thinBallDensity`).

Every point of `U(𝕋_B, Y'_B)` sees the same density, up to a factor `⪆ 1`, as the one dense
ball of `oneDenseBall`: for every `x ∈ U(𝕋_B, Y'_B)`,
`|U(𝕋_B, Y'_B) ∩ B(x, A)| ⪆ δ^η δ³ ∼ δ^η (δ/a)³ |B(x, A)|`.

Two points deserve emphasis. A `⪆ 1` refinement by itself would give nothing pointwise on a
single ball; it is the comparability (T4)(c) that does the work. And the balls must be
*centred at points of* `U(𝕋_B, Y'_B)`: for an arbitrary `A`-ball merely meeting the union
the conclusion is false, since such a ball may touch the union tangentially. -/
theorem ballDensity (hdim : Module.finrank ℝ E = 3)
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) (hδ : 0 < δ) (hδa : δ ≤ a) :
    ∀ x ∈ tb.U, ((ballDensityConstant C : NNReal) : ENNReal)⁻¹ * (δ : ENNReal) ^ η *
      volume (ball x (δ : ℝ)) ≤ volume (tb.U ∩ ball x (rad C₀ a : ℝ)) := by
  intro x hx
  classical
  let cL : NNReal := ballDensityConstant C
  let Dsep : ℕ := separatedNetCoverConstant 3
  let A : ℝ := (rad C₀ a : ℝ)
  -- positivity of the covering radius `A = rad C₀ a`
  have ha0 : (0 : NNReal) < a := lt_of_lt_of_le hδ hδa
  have hw1pos : (0 : NNReal) < w1Constant C₀ := lt_of_lt_of_le (by norm_num) (one_le_w1Constant C₀)
  have hApos : (0 : ℝ) < A := by
    dsimp [A]
    rw [rad, NNReal.coe_mul]
    exact mul_pos (by exact_mod_cast hw1pos) (by exact_mod_cast ha0)
  have hAz : A ≠ 0 := ne_of_gt hApos
  -- the one dense ball of `oneDenseBall`
  obtain ⟨x₀, hx₀U, hx₀⟩ := oneDenseBall tb hδ hδa
  -- `tb.U ∩ ball x₀ (2A)` is bounded, so it carries a maximal `A`-separated net
  let ub : Set E := tb.U ∩ ball x₀ (2 * A)
  have hbounded : Bornology.IsBounded ub := by
    dsimp [ub]
    exact Metric.isBounded_ball.subset
      (inter_subset_right : tb.U ∩ ball x₀ (2 * A) ⊆ ball x₀ (2 * A))
  rcases exists_maximal_separated hbounded hApos with ⟨N, hNsub, hsep, hmax⟩
  have hNball : (↑N : Set E) ⊆ ball x₀ (2 * A) := by
    intro z hz
    exact (hNsub hz).2
  -- the net has cardinality `≤ separatedNetCoverConstant 3 = 5³`
  have hcard :=
    finite_and_card_le_of_separated hApos (by positivity) x₀ (hsep := hsep) (hN := hNball)
  have hbase : (1 + 2 * (2 * A) / A : ℝ) = (5 : ℝ) := by
    field_simp [hAz]
    ring
  have hcard3 : (↑N : Set E).ncard ≤ 5 ^ 3 := by
    have hr : ((↑N : Set E).ncard : ℝ) ≤ (5 : ℝ) ^ 3 := by
      simpa [hdim, hbase] using hcard.2
    exact_mod_cast hr
  have hcardD : (N.card : ENNReal) ≤ (Dsep : ENNReal) := by
    calc
      (N.card : ENNReal) = ((↑N : Set E).ncard : ENNReal) := by simp [Set.ncard_coe_finset]
      _ ≤ ((5 ^ 3 : ℕ) : ENNReal) := by exact_mod_cast hcard3
      _ = (Dsep : ENNReal) := by dsimp [Dsep]; simp [separatedNetCoverConstant]
  -- the `A`-balls at the net cover `tb.U ∩ ball x₀ (2A)`
  have hcover : ub ⊆ ⋃ z ∈ N, (tb.U ∩ ball z A) := by
    intro u hu
    rcases hmax u hu with ⟨z, hzN, hzdist⟩
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzN, ⟨hu.1, hzdist⟩⟩⟩
  -- comparability (T4)(c) spreads the mass from the net to `x`
  have hsumbound : volume (tb.U ∩ ball x₀ (2 * (rad C₀ a : ℝ))) ≤
      (N.card : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A)) := by
    calc
      volume (tb.U ∩ ball x₀ (2 * (rad C₀ a : ℝ))) = volume ub := by
          simp [ub, A]
      _ ≤ volume (⋃ z ∈ N, (tb.U ∩ ball z A)) := measure_mono hcover
      _ ≤ ∑ z ∈ N, volume (tb.U ∩ ball z A) := by
          exact measure_biUnion_finset_le N (fun z => tb.U ∩ ball z A)
      _ ≤ (N.card : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A)) := by
        have h : ∀ z ∈ N, volume (tb.U ∩ ball z A) ≤ (C : ENNReal) * volume (tb.U ∩ ball x A) := by
          intro z hz
          have hzU : z ∈ tb.U := (hNsub hz).1
          have hzU' : z ∈ iUnionShade segs tb.Y' := by simpa [ThinBall.U] using hzU
          have hx' : x ∈ iUnionShade segs tb.Y' := by simpa [ThinBall.U] using hx
          exact tb.centredMult z hzU' x hx'
        calc
          (∑ z ∈ N, volume (tb.U ∩ ball z A)) ≤
            N.card • ((C : ENNReal) * volume (tb.U ∩ ball x A)) :=
            Finset.sum_le_card_nsmul N (fun z => volume (tb.U ∩ ball z A))
              ((C : ENNReal) * volume (tb.U ∩ ball x A)) h
          _ = (N.card : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A)) := by simp
  -- the dense ball's mass, shifted to the origin-normalized form
  have hCpos : (0 : ENNReal) < (C : ENNReal) :=
    lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) (ENNReal.coe_le_coe.mpr tb.one_le_C)
  have hc_ne0 : (C : ENNReal) ≠ 0 := ne_of_gt hCpos
  have hc_neTop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hxpos : (C : ENNReal)⁻¹ * ((δ : ENNReal) ^ η * volume (ball x (δ : ℝ))) ≤
      (N.card : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A)) := by
    calc
      (C : ENNReal)⁻¹ * ((δ : ENNReal) ^ η * volume (ball x (δ : ℝ)))
          = (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball x (δ : ℝ)) := by rw [mul_assoc]
      _ = (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball x₀ (δ : ℝ)) := by
          rw [MeasureTheory.Measure.addHaar_ball_center volume x (δ : ℝ)]
          rw [MeasureTheory.Measure.addHaar_ball_center volume x₀ (δ : ℝ)]
      _ ≤ volume (tb.U ∩ ball x₀ (2 * (rad C₀ a : ℝ))) := hx₀
      _ ≤ (N.card : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A)) := hsumbound
  have hxpos2 : (C : ENNReal)⁻¹ * ((δ : ENNReal) ^ η * volume (ball x (δ : ℝ))) ≤
      (Dsep : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A)) :=
    le_trans hxpos (mul_le_mul_of_nonneg_right hcardD zero_le)
  have hy : (δ : ENNReal) ^ η * volume (ball x (δ : ℝ)) ≤
      (C : ENNReal) * ((Dsep : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A))) :=
    (ENNReal.inv_mul_le_iff hc_ne0 hc_neTop).1 hxpos2
  -- rearrange: `δ^η * |B(x,δ)| ≤ (Dsep * C²) * |U ∩ B(x,A)|`
  let K : NNReal := (Dsep : NNReal) * C ^ 2
  let vol : ENNReal := volume (tb.U ∩ ball x A)
  have hKexpr : (C : ENNReal) * ((Dsep : ENNReal) * ((C : ENNReal) * vol)) =
      (K : ENNReal) * vol := by
    simp [K, ENNReal.coe_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]
  have hy2 : (δ : ENNReal) ^ η * volume (ball x (δ : ℝ)) ≤ (K : ENNReal) * vol := by
    calc
      (δ : ENNReal) ^ η * volume (ball x (δ : ℝ))
          ≤ (C : ENNReal) * ((Dsep : ENNReal) * ((C : ENNReal) * volume (tb.U ∩ ball x A))) := hy
      _ = (K : ENNReal) * vol := by simpa [vol] using hKexpr
  -- `ballDensityConstant C` dominates `Dsep * C²`
  have hK : K ≤ cL := by
    dsimp [K, cL, Dsep, ballDensityConstant]
    exact le_max_right _ _
  have hy3 : (δ : ENNReal) ^ η * volume (ball x (δ : ℝ)) ≤ (cL : ENNReal) * vol :=
    le_trans hy2 (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hK) zero_le)
  -- discharge the inverse
  have hcL1 : (1 : NNReal) ≤ cL := by dsimp [cL]; exact one_le_ballDensityConstant C
  have hcLpos : (0 : ENNReal) < (cL : ENNReal) :=
    lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) (ENNReal.coe_le_coe.mpr hcL1)
  have hcL0 : (cL : ENNReal) ≠ 0 := ne_of_gt hcLpos
  have hcLtop : (cL : ENNReal) ≠ ⊤ := by simp
  simpa [cL, vol, A, mul_assoc] using (ENNReal.inv_mul_le_iff hcL0 hcLtop).2 hy3

/-- **The shaded bodies lie in a neighbourhood of the tube segments** (blueprint
`lem:ml2thinBodiesInTubeNbhd`).

By (T6) each `Y_{𝕎'_B}(W)` lies in the `2w₁`-neighbourhood of `U(𝕋_{B,W}, Y'_B) ⊆
U(𝕋_B, Y'_B)`, and `2w₁ ≤ A` by `ThinBall.w_le`. Only the *containment* `shade_W_subset` is
used, so the proof is unaffected by the outer bodies being enlargements. -/
theorem bodiesInTubeNbhd (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) :
    tb.UW ⊆ cthickening (rad C₀ a : ℝ) tb.U := by
  intro x hx
  simp only [ThinBall.UW, iUnionShade, mem_iUnion, exists_prop] at hx
  rcases hx with ⟨j, hj', hxshade⟩
  have hxthick : x ∈ cthickening (2 * tb.w j)
      (iUnionShade (segs.filter fun p => blk p = j) tb.Y') :=
    tb.shade_W_subset j hj' hxshade
  have hmono : iUnionShade (segs.filter fun p => blk p = j) tb.Y' ⊆ iUnionShade segs tb.Y' := by
    exact Set.biUnion_subset_biUnion_left (Finset.filter_subset _ segs)
  exact (Metric.cthickening_mono (tb.w_le j hj') (iUnionShade segs tb.Y'))
    (Metric.cthickening_subset_of_subset (2 * tb.w j) hmono hxthick)

open scoped Classical in
/-- **Upper bound for the bodies by a separated net** (blueprint `lem:ml2thinNetUpper`).

If `N` is a maximal `A`-separated subset of `U(𝕋_B, Y'_B)` — so that the balls `B(y, 2A)`,
`y ∈ N`, are a boundedly overlapping cover of the `A`-neighbourhood of `U(𝕋_B, Y'_B)` —
then `|U(𝕎'_B, Y_{𝕎'_B})| ≲ |N| a³`, and the same bound localized to a ball `B_r` holds
with `N` replaced by the sub-net of points whose `2A`-ball meets `B_r`.

The net is taken *inside* `U(𝕋_B, Y'_B)`, and the covering balls are centred at its points;
this is what makes the appeal to `ballDensity` legitimate, since under (T6) a point of
`U(𝕎'_B, Y_{𝕎'_B})` is only known to be within `2w₁ ≤ A` of `U(𝕋_B, Y'_B)`.

The sub-net of the localized bound is cut out by the *closed* balls `closedBall y (2A)`. This
is forced: for `z ∈ N_A(U)` maximality of `N` only gives `dist z y ≤ 2A` in the limit (take
`u ∈ U` with `dist z u` arbitrarily close to `infDist z U ≤ A`, and `y ∈ N` with
`dist u y < A`; the net being finite, one `y` serves for a sequence of such `u`), so
`N_A(U) ⊆ ⋃_{y ∈ N} ball y (2A)` may fail at the boundary. Widening the balls to
`closedBall y (2A)` repairs this without changing the constant. -/
theorem netUpper (hdim : Module.finrank ℝ E = 3)
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η)
    (N : Finset E) (_hNU : ↑N ⊆ tb.U)
    (hmax : ∀ x ∈ tb.U, ∃ y ∈ N, dist x y < (rad C₀ a : ℝ)) :
    volume tb.UW ≤ (netUpperConstant C C₀ : ENNReal) * (N.card * volume (ball (0 : E) (a : ℝ))) ∧
      ∀ (x : E) (r : ℝ),
        volume (tb.UW ∩ ball x r) ≤ (netUpperConstant C C₀ : ENNReal) *
          (({y ∈ N | (closedBall y (2 * (rad C₀ a : ℝ)) ∩ ball x r).Nonempty}.card : ENNReal) *
            volume (ball (0 : E) (a : ℝ))) := by
  classical
  let Aₙ : NNReal := rad C₀ a
  let A : ℝ := (Aₙ : ℝ)
  let A₂ : NNReal := 2 * Aₙ
  let w : NNReal := w1Constant C₀
  let t : NNReal := 2 * w
  have hA0 : 0 ≤ (A : ℝ) := by
    dsimp [A, Aₙ]
    positivity
  have hA₂R : (A₂ : ℝ) = 2 * (A : ℝ) := by simp [A₂, A, Aₙ]
  have hA₂rad : (A₂ : ℝ) = 2 * (rad C₀ a : ℝ) := by simp [A₂, Aₙ]
  have hA₂t : (A₂ : ℝ) = (t : ℝ) * (a : ℝ) := by
    have hNN : A₂ = t * a := by
      simp [A₂, Aₙ, t, w, rad, mul_assoc]
    exact_mod_cast hNN
  have ht_pos : 0 < (t : ℝ) := by
    dsimp [t]
    have hw1r : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast one_le_w1Constant C₀
    nlinarith
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  -- `U` is contained in the `A`-neighbourhood of the net.
  have hUsubN : tb.U ⊆ cthickening A N := by
    intro u hu
    rcases hmax u hu with ⟨y, hyN, hd⟩
    exact (Metric.closedBall_subset_cthickening hyN A) (Metric.mem_closedBall.mpr (le_of_lt hd))
  -- cthickening of the cthickening.
  have hcthick : cthickening (A : ℝ) tb.U ⊆ cthickening (A₂ : ℝ) (N : Set E) := by
    calc
      cthickening (A : ℝ) tb.U ⊆ cthickening (A : ℝ) (cthickening (A : ℝ) (N : Set E)) :=
          cthickening_subset_of_subset A hUsubN
      _ ⊆ cthickening (A + A) (N : Set E) := by
          exact cthickening_cthickening_subset (s := (N : Set E)) hA0 hA0
      _ = cthickening (A₂ : ℝ) (N : Set E) := by
          congr 1
          rw [hA₂R]
          ring
  -- the shaded bodies lie in the `2A`-neighbourhood of the net.
  have hbodies : tb.UW ⊆ cthickening (A₂ : ℝ) N := (bodiesInTubeNbhd tb).trans hcthick
  -- the closed balls at `N` of radius `2A` cover that neighbourhood.
  have hIsCov : IsCover (A₂ : NNReal) (cthickening (A₂ : ℝ) (↑N : Set E)) (↑N : Set E) := by
    exact (Metric.isCover_iff_subset_cthickening (N := (↑N : Set E)) (Finset.isClosed N)).mpr
      (by intro x hx; exact hx)
  have hcthickN : cthickening (A₂ : ℝ) (↑N : Set E) ⊆
      ⋃ y ∈ (↑N : Set E), closedBall y (A₂ : ℝ) := by
    exact Metric.IsCover.subset_iUnion_closedBall hIsCov
  have hcover : tb.UW ⊆ ⋃ y ∈ (↑N : Set E), closedBall y (A₂ : ℝ) := by
    exact hbodies.trans (by simpa using hcthickN)
  -- coefficient `(2w)³ ≤ C_ref(lem:ml2thinNetUpper)(C,C₀)`, giving the ball-volume scaling.
  have hcoef_real : (t : ℝ) ^ 3 ≤ (netUpperConstant C C₀ : ℝ) := by
    dsimp [t]
    have hC1r : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast tb.one_le_C
    have hw0r : (0 : ℝ) ≤ (w : ℝ) := by positivity
    have hb : ((2 * w : NNReal) : ℝ) ^ 3 ≤
        (((2 ^ 12 : NNReal) * C ^ 3 * (1 + w) ^ 3 : NNReal) : ℝ) := by
      norm_num [NNReal.coe_pow]
      have hC3 : (1 : ℝ) ≤ (C : ℝ) ^ 3 := one_le_pow₀ hC1r
      have hnn : 0 ≤ 2 * (w : ℝ) := by positivity
      have hbase : 2 * (w : ℝ) ≤ 16 * (1 + (w : ℝ)) := by nlinarith [hw0r]
      have h2w : (2 * (w : ℝ)) ^ 3 ≤ 4096 * (1 + (w : ℝ)) ^ 3 := by
        calc
          (2 * (w : ℝ)) ^ 3 ≤ (16 * (1 + (w : ℝ))) ^ 3 := pow_le_pow_left₀ hnn hbase 3
          _ = 4096 * (1 + (w : ℝ)) ^ 3 := by ring
      have hnnb : 0 ≤ (1 + (w : ℝ)) ^ 3 := by positivity
      have hle1 : (1 + (w : ℝ)) ^ 3 ≤ (C : ℝ) ^ 3 * (1 + (w : ℝ)) ^ 3 :=
        le_mul_of_one_le_left hnnb hC3
      have hR : 4096 * (1 + (w : ℝ)) ^ 3 ≤ 4096 * (C : ℝ) ^ 3 * (1 + (w : ℝ)) ^ 3 := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hle1 (by norm_num : (0 : ℝ) ≤ 4096)
      exact le_trans h2w hR
    have hc : (((2 ^ 12 : NNReal) * C ^ 3 * (1 + w) ^ 3 : NNReal) : ℝ) ≤
        (netUpperConstant C C₀ : ℝ) := by
      have hle : (2 ^ 12 : NNReal) * C ^ 3 * (1 + w) ^ 3 ≤ netUpperConstant C C₀ := by
        dsimp [netUpperConstant]
        exact le_max_right _ _
      exact_mod_cast hle
    exact le_trans hb hc
  -- every `2A`-closed ball has the volume of the centred one.
  have hcball (y : E) : volume (closedBall y (A₂ : ℝ)) = volume (ball (0 : E) (A₂ : ℝ)) := by
    rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume y (A₂ : ℝ),
      MeasureTheory.Measure.addHaar_ball_center volume y (A₂ : ℝ)]
  -- scaling of the ball volume: `|B(0,2A)| = (2·w1 C₀)³ |B(0,a)|`.
  have hscale : volume (ball (0 : E) (A₂ : ℝ)) =
      ENNReal.ofReal ((t : ℝ) ^ 3) * volume (ball (0 : E) (a : ℝ)) := by
    calc
      volume (ball (0 : E) (A₂ : ℝ)) = volume (ball (0 : E) ((t : ℝ) * (a : ℝ))) := by
          rw [hA₂t]
      _ = ENNReal.ofReal ((t : ℝ) ^ Module.finrank ℝ E) * volume (ball (0 : E) (a : ℝ)) := by
          simpa using (MeasureTheory.Measure.addHaar_ball_mul_of_pos volume (0 : E) ht_pos (a : ℝ))
      _ = ENNReal.ofReal ((t : ℝ) ^ 3) * volume (ball (0 : E) (a : ℝ)) := by
          congr 1
          rw [hdim]
  -- `|B(0,2A)| ≤ C_ref(netUpper) |B(0,a)|`.
  have hscaled_le : volume (ball (0 : E) (A₂ : ℝ)) ≤
      (netUpperConstant C C₀ : ENNReal) * volume (ball (0 : E) (a : ℝ)) := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_right
      ((ENNReal.ofReal_le_ofReal hcoef_real).trans_eq (by simp)) (by positivity)
  constructor
  · calc
      volume tb.UW ≤ volume (⋃ y ∈ N, closedBall y (A₂ : ℝ)) := measure_mono hcover
      _ ≤ ∑ y ∈ N, volume (closedBall y (A₂ : ℝ)) :=
          measure_biUnion_finset_le N (fun y => closedBall y (A₂ : ℝ))
      _ = N.card * volume (ball (0 : E) (A₂ : ℝ)) := by
          calc
            (∑ y ∈ N, volume (closedBall y (A₂ : ℝ)))
                = ∑ y ∈ N, volume (ball (0 : E) (A₂ : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    exact hcball y
            _ = N.card * volume (ball (0 : E) (A₂ : ℝ)) := by simp
      _ ≤ (netUpperConstant C C₀ : ENNReal) * (N.card * volume (ball (0 : E) (a : ℝ))) := by
          calc
            (N.card : ENNReal) * volume (ball (0 : E) (A₂ : ℝ))
                ≤ (N.card : ENNReal) * ((netUpperConstant C C₀ : ENNReal) *
                    volume (ball (0 : E) (a : ℝ))) :=
                  mul_le_mul_of_nonneg_left hscaled_le zero_le
            _ = (netUpperConstant C C₀ : ENNReal) * ((N.card : ENNReal) *
                    volume (ball (0 : E) (a : ℝ))) := by ring
  · intro x r
    -- the sub-net of points whose `2A`-ball meets `ball x r`.
    let Nᵣ : Finset E := {y ∈ N | (closedBall y (A₂ : ℝ) ∩ ball x r).Nonempty}
    have hcov_loc : tb.UW ∩ ball x r ⊆ ⋃ y ∈ (Nᵣ : Set E), (closedBall y (A₂ : ℝ) ∩ ball x r) := by
      intro z hz
      rcases hcover hz.1 with ⟨B, hB, hzB⟩
      rcases (Set.mem_range.mp hB) with ⟨y, hy⟩
      rw [← hy] at hzB
      rcases (Set.mem_iUnion.mp hzB) with ⟨hyN, hzcly⟩
      have hyNr : y ∈ (Nᵣ : Set E) := by
        simpa [Nᵣ] using ⟨hyN, ⟨z, hzcly, hz.2⟩⟩
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyNr, ⟨hzcly, hz.2⟩⟩⟩
    have hv_loc := calc
      volume (tb.UW ∩ ball x r)
          ≤ volume (⋃ y ∈ Nᵣ, (closedBall y (A₂ : ℝ) ∩ ball x r)) := measure_mono hcov_loc
      _ ≤ ∑ y ∈ Nᵣ, volume (closedBall y (A₂ : ℝ) ∩ ball x r) :=
          measure_biUnion_finset_le Nᵣ (fun y => closedBall y (A₂ : ℝ) ∩ ball x r)
      _ ≤ ∑ y ∈ Nᵣ, volume (closedBall y (A₂ : ℝ)) := by
          apply Finset.sum_le_sum
          intro y hy
          exact measure_mono (Set.inter_subset_left :
            closedBall y (A₂ : ℝ) ∩ ball x r ⊆ closedBall y (A₂ : ℝ))
      _ = Nᵣ.card * volume (ball (0 : E) (A₂ : ℝ)) := by
          calc
            (∑ y ∈ Nᵣ, volume (closedBall y (A₂ : ℝ)))
                = ∑ y ∈ Nᵣ, volume (ball (0 : E) (A₂ : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    exact hcball y
            _ = Nᵣ.card * volume (ball (0 : E) (A₂ : ℝ)) := by simp
      _ ≤ (netUpperConstant C C₀ : ENNReal) * (Nᵣ.card * volume (ball (0 : E) (a : ℝ))) := by
          calc
            (Nᵣ.card : ENNReal) * volume (ball (0 : E) (A₂ : ℝ))
                ≤ (Nᵣ.card : ENNReal) * ((netUpperConstant C C₀ : ENNReal) *
                    volume (ball (0 : E) (a : ℝ))) :=
                  mul_le_mul_of_nonneg_left hscaled_le zero_le
            _ = (netUpperConstant C C₀ : ENNReal) * ((Nᵣ.card : ENNReal) *
                    volume (ball (0 : E) (a : ℝ))) := by ring
    simpa [Nᵣ, hA₂rad] using hv_loc

/-- **Lower bound for the tube segments by a separated net** (blueprint
`lem:ml2thinNetLower`).

If `N ⊆ U(𝕋_B, Y'_B)` is `A`-separated and `N' ⊆ N` consists of points whose `A`-ball is
contained in the measurable set `F`, then `|U(𝕋_B, Y'_B) ∩ F| ⪆ |N'| δ^η δ³`: each
`A`-ball centred at a point of `N'` carries mass `⪆ δ^η δ³` by `ballDensity`, and the
`A`-balls at an `A`-separated set have bounded overlap. -/
theorem netLower (hdim : Module.finrank ℝ E = 3)
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) (hδ : 0 < δ) (hδa : δ ≤ a)
    (N : Finset E) (hNU : ↑N ⊆ tb.U)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → (rad C₀ a : ℝ) ≤ dist y z)
    (F : Set E) (hF : MeasurableSet F) (N' : Finset E) (hN' : N' ⊆ N)
    (hball : ∀ y ∈ N', ball y (rad C₀ a : ℝ) ⊆ F) :
    ((netLowerConstant C : NNReal) : ENNReal)⁻¹ *
        ((N'.card : ENNReal) * ((δ : ENNReal) ^ η * volume (ball (0 : E) (δ : ℝ)))) ≤
      volume (tb.U ∩ F) := by
  classical
  let cL : NNReal := ballDensityConstant C
  let Dsep : ℕ := separatedNetCoverConstant (Module.finrank ℝ E)
  let m : ENNReal := (δ : ENNReal) ^ η * volume (ball (0 : E) (δ : ℝ))
  -- positivity of the covering radius `A = rad C₀ a`
  have ha0 : (0 : NNReal) < a := lt_of_lt_of_le hδ hδa
  have hw1pos : (0 : NNReal) < w1Constant C₀ := lt_of_lt_of_le (by norm_num) (one_le_w1Constant C₀)
  have hApos : (0 : ℝ) < (rad C₀ a : ℝ) := by
    rw [rad, NNReal.coe_mul]
    exact mul_pos (by exact_mod_cast hw1pos) (by exact_mod_cast ha0)
  have hAtwo : (rad C₀ a : ℝ) ≤ 2 * (rad C₀ a : ℝ) := by linarith
  -- measurability of the union of shades
  have hUmeas : MeasurableSet tb.U := by
    change MeasurableSet (iUnionShade segs tb.Y')
    exact Finset.measurableSet_biUnion segs (fun i hi => (tb.Y' i).measurableSet_shade)
  have hUFmeas : MeasurableSet (tb.U ∩ F) := MeasurableSet.inter hUmeas hF
  -- `N'` inherits the `A`-separation of `N`
  have hsepN' : ∀ y ∈ N', ∀ z ∈ N', y ≠ z → (rad C₀ a : ℝ) ≤ dist y z := by
    intro y hy z hz hne
    exact hsep y (hN' hy) z (hN' hz) hne
  -- the pointwise overlap bound for the `A`-balls at `N'`
  have hoverlap : ∀ x : E, {y ∈ N' | x ∈ ball y (rad C₀ a : ℝ)}.card ≤ Dsep := by
    intro x
    exact card_filter_ball_le (r := (rad C₀ a : ℝ)) (t := (rad C₀ a : ℝ)) hApos hAtwo
      (N := N') (hsep := hsepN') x
  -- Step B: the restricted volume sum (`boundedOverlapRestrictSum`)
  have hsumbar : (∑ y ∈ N', volume (tb.U ∩ ball y (rad C₀ a : ℝ))) ≤
      (Dsep : ENNReal) * volume (tb.U ∩ F) := by
    have hsum0 : (∑ y ∈ N', volume ((tb.U ∩ F) ∩ ball y (rad C₀ a : ℝ))) ≤
        (Dsep : ENNReal) * volume (tb.U ∩ F) :=
      sum_volume_inter_ball_le N' id (fun _ => (rad C₀ a : ℝ))
        (D := Dsep) (hoverlap := hoverlap) (F := tb.U ∩ F) (hF := hUFmeas)
    have hsum1 : (∑ y ∈ N', volume (tb.U ∩ ball y (rad C₀ a : ℝ))) =
        ∑ y ∈ N', volume ((tb.U ∩ F) ∩ ball y (rad C₀ a : ℝ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [inter_assoc, inter_eq_self_of_subset_right (hball y hy)]
    calc
      (∑ y ∈ N', volume (tb.U ∩ ball y (rad C₀ a : ℝ)))
          = ∑ y ∈ N', volume ((tb.U ∩ F) ∩ ball y (rad C₀ a : ℝ)) := hsum1
      _ ≤ (Dsep : ENNReal) * volume (tb.U ∩ F) := hsum0
  -- Step A: `ballDensity` pointwise, transported to the origin-centred ball, then summed
  have hbdAll : ∀ y ∈ N', (cL : ENNReal)⁻¹ * m ≤ volume (tb.U ∩ ball y (rad C₀ a : ℝ)) := by
    intro y hy
    have hyU : y ∈ tb.U := hNU (hN' hy)
    have hbd := ballDensity hdim tb hδ hδa y hyU
    calc
      (cL : ENNReal)⁻¹ * m
          = (cL : ENNReal)⁻¹ * ((δ : ENNReal) ^ η * volume (ball (0 : E) (δ : ℝ))) := rfl
      _ = (cL : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball (0 : E) (δ : ℝ)) := by
          rw [← mul_assoc]
      _ = (cL : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball y (δ : ℝ)) := by
          rw [← MeasureTheory.Measure.addHaar_ball_center volume y (δ : ℝ)]
      _ ≤ volume (tb.U ∩ ball y (rad C₀ a : ℝ)) := by
          simpa [cL] using hbd
  have hbdsum : (cL : ENNReal)⁻¹ * ((N'.card : ENNReal) * m) ≤
      (∑ y ∈ N', volume (tb.U ∩ ball y (rad C₀ a : ℝ))) := by
    calc
      (cL : ENNReal)⁻¹ * ((N'.card : ENNReal) * m)
          = (N'.card : ENNReal) * ((cL : ENNReal)⁻¹ * m) := by ring
      _ = ∑ y ∈ N', (cL : ENNReal)⁻¹ * m := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ N', volume (tb.U ∩ ball y (rad C₀ a : ℝ)) := by
          exact Finset.sum_le_sum (fun y hy => hbdAll y hy)
  -- combine the two halves
  have hchain : (cL : ENNReal)⁻¹ * ((N'.card : ENNReal) * m) ≤
      (Dsep : ENNReal) * volume (tb.U ∩ F) := le_trans hbdsum hsumbar
  have hcL1 : (1 : NNReal) ≤ cL := by unfold cL; exact one_le_ballDensityConstant C
  have hcLpos : (0 : ENNReal) < (cL : ENNReal) :=
    lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) (ENNReal.coe_le_coe.mpr hcL1)
  have hcL0 : (cL : ENNReal) ≠ 0 := ne_of_gt hcLpos
  have hcLtop : (cL : ENNReal) ≠ ⊤ := by simp
  have hmain : (N'.card : ENNReal) * m ≤
      ((Dsep : ENNReal) * (cL : ENNReal)) * volume (tb.U ∩ F) := by
    calc
      (N'.card : ENNReal) * m
          ≤ (cL : ENNReal) * ((Dsep : ENNReal) * volume (tb.U ∩ F)) :=
              (ENNReal.inv_mul_le_iff hcL0 hcLtop).1 hchain
      _ = ((Dsep : ENNReal) * (cL : ENNReal)) * volume (tb.U ∩ F) := by ring
  -- `netLowerConstant C` dominates `(separatedNetCoverConstant 3) * ballDensityConstant C`
  have hLge : ((Dsep : NNReal) * cL : NNReal) ≤ (netLowerConstant C : NNReal) := by
    rw [netLowerConstant]
    have hDsep : (Dsep : NNReal) = (separatedNetCoverConstant 3 : NNReal) := by
      unfold Dsep
      rw [hdim]
    have hmax : ((separatedNetCoverConstant 3 : NNReal) * ballDensityConstant C) ≤
        max 1 ((separatedNetCoverConstant 3 : NNReal) * ballDensityConstant C) := le_max_right _ _
    simp [cL, hDsep, hmax]
  have hprod : ((Dsep : NNReal) * cL : ENNReal) = (Dsep : ENNReal) * (cL : ENNReal) := by
    simp
  have hLgeE : (Dsep : ENNReal) * (cL : ENNReal) ≤ (netLowerConstant C : ENNReal) := by
    rw [← hprod]
    exact ENNReal.coe_le_coe.mpr hLge
  have hfinal : (N'.card : ENNReal) * m ≤ (netLowerConstant C : ENNReal) * volume (tb.U ∩ F) :=
    le_trans hmain (mul_le_mul' hLgeE le_rfl)
  have hL1 : (1 : NNReal) ≤ netLowerConstant C := one_le_netLowerConstant C
  have hLpos : (0 : ENNReal) < (netLowerConstant C : ENNReal) :=
    lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) (ENNReal.coe_le_coe.mpr hL1)
  have hL0 : (netLowerConstant C : ENNReal) ≠ 0 := ne_of_gt hLpos
  have hLtop : (netLowerConstant C : ENNReal) ≠ ⊤ := by simp
  exact (ENNReal.inv_mul_le_iff hL0 hLtop).2 hfinal

/-- **The tubes fill out most of the union of the bodies** (blueprint
`lem:ml2thinUnionLower`, first inequality).

Eliminating the cardinality of a maximal `A`-separated subset of `U(𝕋_B, Y'_B)` between
`netUpper` and `netLower` gives
`|U(𝕋_B, Y'_B)| ⪆ (δ/a)³ δ^η |U(𝕎'_B, Y_{𝕎'_B})|`.

This half is where the whole mechanism lives, and it uses nothing about the size of `a`; the
thin-case hypothesis `a ≤ δ^{1-τ}` enters only in `Kakeya.ThinCase.unionLower_thin`, which
rewrites `(δ/a)³` as `δ^{3τ}`. Keeping the two apart avoids saddling the general estimate
with a hypothesis it does not need. -/
theorem unionLower (hdim : Module.finrank ℝ E = 3)
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) (hδ : 0 < δ) (hδa : δ ≤ a) :
    ((unionLowerConstant C C₀ : NNReal) : ENNReal)⁻¹ * (δ : ENNReal) ^ η *
      ((δ : ENNReal) / (a : ENNReal)) ^ 3 * volume tb.UW ≤ volume tb.U := by
  let uK : ENNReal := (unionLowerConstant C C₀ : NNReal)
  let nuK : ENNReal := (netUpperConstant C C₀ : NNReal)
  let nlK : ENNReal := (netLowerConstant C : NNReal)
  let q : ENNReal := (δ : ENNReal) / (a : ENNReal)
  let vola : ENNReal := volume (ball (0 : E) (a : ℝ))
  let volδ : ENNReal := volume (ball (0 : E) (δ : ℝ))
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  have hUc : uK = nuK * nlK := by
    simp [uK, nuK, nlK, unionLowerConstant, ENNReal.coe_mul]
  have hapos : (0 : ℝ) < (a : ℝ) := by
    exact lt_of_lt_of_le (NNReal.coe_pos.mpr hδ) (NNReal.coe_le_coe.mpr hδa)
  have hδpos_real : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have ha_ne0 : (a : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hapos).ne'
  have ha_neTop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hApos : (0 : ℝ) < (rad C₀ a : ℝ) := by
    have hwa : (1 : ℝ) * (a : ℝ) ≤ (w1Constant C₀ : NNReal) * (a : ℝ) := by
      exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (one_le_w1Constant C₀))
        (le_of_lt hapos)
    have h1a : (a : ℝ) ≤ (w1Constant C₀ : ℝ) * (a : ℝ) := by simpa using hwa
    exact lt_of_lt_of_le hapos h1a
  -- boundedness of `tb.U`: a finite union of bounded (compact) carriers
  have hbounded : Bornology.IsBounded tb.U := by
    refine Bornology.IsBounded.subset (t := ⋃ p ∈ segs, (Y p).carrier) ?hbt ?hsub
    · simpa using
        (Bornology.isBounded_biUnion (s := (segs : Set σ)) (f := fun p => (Y p).carrier)
          (Finset.finite_toSet segs)).mpr (by
            intro p hp
            exact IsCompact.isBounded (Y p).isCompact')
    · rw [ThinBall.U]
      refine Set.iUnion₂_subset ?_
      intro p hp x hx
      refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
      have hcar : (tb.Y' p).carrier = (Y p).carrier :=
        congrArg ConvexSpaceBody.carrier (tb.carrier_Y' p hp)
      exact by simpa [hcar] using (tb.Y' p).shade_subset hx
  -- a maximal `rad C₀ a`-separated subset of `tb.U`
  rcases exists_separatedNetCover hbounded (r := (rad C₀ a : ℝ)) hApos with
    ⟨N, hNU, hsep, hmax, _cvA, _cv2A, _dj, _cd⟩
  -- netUpper, first conjunct
  have hnu : volume tb.UW ≤ nuK * (N.card * vola) := by
    simpa [nuK, vola] using (netUpper hdim tb N hNU hmax).1
  -- netLower with `F = univ`, `N' = N`
  have hnl_raw : nlK ⁻¹ * (N.card * ((δ : ENNReal) ^ η * volδ)) ≤
      volume (tb.U ∩ Set.univ) := by
    simpa [nlK, volδ] using
      (netLower hdim tb hδ hδa N hNU hsep Set.univ MeasurableSet.univ N
        (by simp) (by intro y hy; simp))
  -- coefficient reduction `uK⁻¹ * nuK = nlK⁻¹`
  have hnu_ne0 : nuK ≠ 0 :=
    (ENNReal.coe_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_netUpperConstant C C₀))).ne'
  have hnu_neTop : nuK ≠ ⊤ := ENNReal.coe_ne_top
  have hucanc : uK⁻¹ * nuK = nlK⁻¹ := by
    rw [hUc]
    rw [ENNReal.mul_inv (Or.inl hnu_ne0) (Or.inl hnu_neTop)]
    calc
      (nuK⁻¹ * nlK⁻¹) * nuK = nlK⁻¹ * (nuK⁻¹ * nuK) := by ac_rfl
      _ = nlK⁻¹ * 1 := by rw [ENNReal.inv_mul_cancel hnu_ne0 hnu_neTop]
      _ = nlK⁻¹ := by simp
  -- the ball-volume ratio `(δ/a)³ · |B(0,a)| = |B(0,δ)|` in dimension three
  have hδof : ENNReal.ofReal (δ : ℝ) = (δ : ENNReal) := by
    rw [ENNReal.ofReal]
    simp [Real.toNNReal_of_nonneg (le_of_lt hδpos_real)]
  have haof : ENNReal.ofReal (a : ℝ) = (a : ENNReal) := by
    rw [ENNReal.ofReal]
    simp [Real.toNNReal_of_nonneg (le_of_lt hapos)]
  let Cvol : ENNReal :=
    ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E / Real.Gamma (↑(Module.finrank ℝ E) / 2 + 1))
  have hKδ : volume (ball (0 : E) (δ : ℝ)) =
      ENNReal.ofReal (δ : ℝ) ^ Module.finrank ℝ E * Cvol := by
    rw [InnerProductSpace.volume_ball]
  have hKa : volume (ball (0 : E) (a : ℝ)) =
      ENNReal.ofReal (a : ℝ) ^ Module.finrank ℝ E * Cvol := by
    rw [InnerProductSpace.volume_ball]
  have hvol' : q ^ Module.finrank ℝ E * vola = volδ := by
    dsimp [q, volδ, vola]
    rw [hKδ, hKa]
    calc
      q ^ Module.finrank ℝ E * (ENNReal.ofReal (a : ℝ) ^ Module.finrank ℝ E * Cvol)
          = (q * ENNReal.ofReal (a : ℝ)) ^ Module.finrank ℝ E * Cvol := by
              rw [← mul_assoc, mul_pow]
      _ = ENNReal.ofReal (δ : ℝ) ^ Module.finrank ℝ E * Cvol := by
              have hbase : q * ENNReal.ofReal (a : ℝ) = ENNReal.ofReal (δ : ℝ) := by
                dsimp [q]
                rw [hδof, haof]
                exact ENNReal.div_mul_cancel ha_ne0 ha_neTop
              rw [hbase]
  have hvol : q ^ 3 * vola = volδ := by
    simpa [hdim] using hvol'
  -- eliminate `N.card` between netUpper and netLower
  calc
    uK⁻¹ * (δ : ENNReal) ^ η * q ^ 3 * volume tb.UW
        ≤ uK⁻¹ * (δ : ENNReal) ^ η * q ^ 3 * (nuK * (N.card * vola)) := by
            gcongr
    _ = nlK⁻¹ * (N.card * ((δ : ENNReal) ^ η * volδ)) := by
            calc
              uK⁻¹ * (δ : ENNReal) ^ η * q ^ 3 * (nuK * (N.card * vola))
                  = (uK⁻¹ * nuK) * ((δ : ENNReal) ^ η * q ^ 3 * N.card * vola) := by
                      ac_rfl
              _ = nlK⁻¹ * ((δ : ENNReal) ^ η * q ^ 3 * N.card * vola) := by
                      rw [hucanc]
              _ = nlK⁻¹ * ((δ : ENNReal) ^ η * N.card * (q ^ 3 * vola)) := by
                      ac_rfl
              _ = nlK⁻¹ * ((δ : ENNReal) ^ η * N.card * volδ) := by
                      rw [hvol]
              _ = nlK⁻¹ * (N.card * ((δ : ENNReal) ^ η * volδ)) := by
                      ac_rfl
    _ ≤ volume (tb.U ∩ Set.univ) := hnl_raw
    _ = volume tb.U := by simp

/-- **The tubes fill out most of the union of the bodies, in the thin case** (blueprint
`lem:ml2thinUnionLower`, second inequality).

The thin-case form of `Kakeya.ThinCase.unionLower`: since `a ≤ δ^{1-τ}` we have
`δ/a ≥ δ^τ`, so the first inequality reads
`|U(𝕋_B, Y'_B)| ⪆ δ^{3τ+η} |U(𝕎'_B, Y_{𝕎'_B})|`. -/
theorem unionLower_thin (hdim : Module.finrank ℝ E = 3)
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) (hδ : 0 < δ) (hδa : δ ≤ a)
    {τ : ℝ} (hthin : a ≤ δ ^ (1 - τ)) :
    ((unionLowerConstant C C₀ : NNReal) : ENNReal)⁻¹ * (δ : ENNReal) ^ (3 * τ + η) *
      volume tb.UW ≤ volume tb.U := by
  let uK : ENNReal := (unionLowerConstant C C₀ : NNReal)
  have hδne0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ).ne'
  have hδneTop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hapos : (0 : ℝ) < (a : ℝ) := by
    exact lt_of_lt_of_le (NNReal.coe_pos.mpr hδ) (NNReal.coe_le_coe.mpr hδa)
  have ha_ne0 : (a : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hapos).ne'
  have ha_neTop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- lift `hthin` (in `NNReal`) to `ENNReal`
  have hthin' : (a : ENNReal) ≤ (δ : ENNReal) ^ (1 - τ) := by
    have hle : (a : ENNReal) ≤ ((δ ^ (1 - τ) : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr hthin
    have hco : (δ : ENNReal) ^ (1 - τ) = ((δ ^ (1 - τ) : NNReal) : ENNReal) :=
      (ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ) (1 - τ)).symm
    simpa [hco] using hle
  -- from `a ≤ δ^(1-τ)` deduce `δ^τ ≤ δ/a`
  have hratio : (δ : ENNReal) ^ τ ≤ (δ : ENNReal) / (a : ENNReal) := by
    have hmt : (δ : ENNReal) ^ τ * (a : ENNReal) ≤
        (δ : ENNReal) ^ τ * (δ : ENNReal) ^ (1 - τ) := by
      gcongr
    have hsum : (δ : ENNReal) ^ τ * (δ : ENNReal) ^ (1 - τ) = (δ : ENNReal) := by
      rw [← ENNReal.rpow_add τ (1 - τ) hδne0 hδneTop,
        show (τ + (1 - τ) : ℝ) = 1 by ring, ENNReal.rpow_one]
    have hmul : (δ : ENNReal) ^ τ * (a : ENNReal) ≤ (δ : ENNReal) := by
      simpa [hsum] using hmt
    exact (ENNReal.le_div_iff_mul_le (Or.inl ha_ne0) (Or.inl ha_neTop)).mpr hmul
  -- cube: `δ^(3τ) ≤ (δ/a)³`
  have hcubed : (δ : ENNReal) ^ (3 * τ) ≤ ((δ : ENNReal) / (a : ENNReal)) ^ 3 := by
    calc
      (δ : ENNReal) ^ (3 * τ) = ((δ : ENNReal) ^ τ) ^ 3 := by
        simp [show (3 * τ : ℝ) = τ * 3 by ring, ENNReal.rpow_mul]
      _ ≤ ((δ : ENNReal) / (a : ENNReal)) ^ 3 := ENNReal.pow_le_pow_left hratio
  -- chain with the general estimate
  have hunion := unionLower hdim tb hδ hδa
  calc
    uK⁻¹ * (δ : ENNReal) ^ (3 * τ + η) * volume tb.UW
        = uK⁻¹ * ((δ : ENNReal) ^ η * (δ : ENNReal) ^ (3 * τ)) * volume tb.UW := by
            rw [ENNReal.rpow_add (3 * τ) η hδne0 hδneTop]
            ac_rfl
    _ ≤ uK⁻¹ * ((δ : ENNReal) ^ η * ((δ : ENNReal) / (a : ENNReal)) ^ 3) * volume tb.UW := by
            gcongr
    _ = uK⁻¹ * (δ : ENNReal) ^ η * ((δ : ENNReal) / (a : ENNReal)) ^ 3 * volume tb.UW := by
            ac_rfl
    _ ≤ volume tb.U := by
            simpa [uK] using hunion

/-- **Transferring the filling from the bodies to the tubes** (blueprint
`lem:ml2thinTransfer`, first inequality).

The same mechanism transfers a lower bound on `|U(𝕎'_B, Y_{𝕎'_B}) ∩ B_r|` inside a ball of
radius `r ≥ 3A` down to the tube segments of the ball, `U(𝕋_B, Y'_B)`.

The conclusion is stated for the *local* union `tb.U = U(𝕋_B, Y'_B)`, which is the sharper
form: a caller wanting the global union `U(𝕋, Y')` of the transverse case obtains it by
`measure_mono` from the reverse containment of (T1) (`Kakeya.ThinCase.localToGlobal`), so
carrying an ambient superset through the statement would only weaken it.

The transfer necessarily loses a factor in the radius: the cover balls carrying the mass of
`U(𝕎'_B, Y_{𝕎'_B}) ∩ B_r` are centred near `B_r` but stick out of it by `O(a)`, so the
conclusion is about the concentric ball `B_{2r}`. This is harmless downstream, where only
the ratio to `|B_r| ∼ |B_{2r}|` matters.

As for `Kakeya.ThinCase.unionLower`, this half uses nothing about the size of `a`; the
thin-case hypothesis enters only in `Kakeya.ThinCase.transfer_thin`. -/
theorem transfer (hdim : Module.finrank ℝ E = 3)
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) (hδ : 0 < δ) (hδa : δ ≤ a)
    {r : ℝ} (hr : 3 * (rad C₀ a : ℝ) ≤ r) (x : E) :
    ((transferConstant C C₀ : NNReal) : ENNReal)⁻¹ * (δ : ENNReal) ^ η *
        ((δ : ENNReal) / (a : ENNReal)) ^ 3 * volume (tb.UW ∩ ball x r) ≤
      volume (tb.U ∩ ball x (2 * r)) := by
  let uK : ENNReal := (transferConstant C C₀ : NNReal)
  let nuK : ENNReal := (netUpperConstant C C₀ : NNReal)
  let nlK : ENNReal := (netLowerConstant C : NNReal)
  let q : ENNReal := (δ : ENNReal) / (a : ENNReal)
  let vola : ENNReal := volume (ball (0 : E) (a : ℝ))
  let volδ : ENNReal := volume (ball (0 : E) (δ : ℝ))
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  -- `transferConstant = 2³ · netUpperConstant · netLowerConstant`
  have hUc : uK = 2 ^ 3 * nuK * nlK := by
    simp [uK, nuK, nlK, transferConstant, ENNReal.coe_mul, ENNReal.coe_pow]
  -- positivity of the covering radius `A = rad C₀ a`
  have ha0 : (0 : NNReal) < a := lt_of_lt_of_le hδ hδa
  have hw1pos : (0 : NNReal) < w1Constant C₀ := lt_of_lt_of_le (by norm_num) (one_le_w1Constant C₀)
  have hApos : (0 : ℝ) < (rad C₀ a : ℝ) := by
    rw [rad, NNReal.coe_mul]
    exact mul_pos (by exact_mod_cast hw1pos) (by exact_mod_cast ha0)
  -- boundedness of `tb.U`: a finite union of bounded (compact) carriers
  have hbounded : Bornology.IsBounded tb.U := by
    refine Bornology.IsBounded.subset (t := ⋃ p ∈ segs, (Y p).carrier) ?hbt ?hsub
    · simpa using
        (Bornology.isBounded_biUnion (s := (segs : Set σ)) (f := fun p => (Y p).carrier)
          (Finset.finite_toSet segs)).mpr (by
            intro p hp
            exact IsCompact.isBounded (Y p).isCompact')
    · rw [ThinBall.U]
      refine Set.iUnion₂_subset ?_
      intro p hp x hx
      refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
      have hcar : (tb.Y' p).carrier = (Y p).carrier :=
        congrArg ConvexSpaceBody.carrier (tb.carrier_Y' p hp)
      exact by simpa [hcar] using (tb.Y' p).shade_subset hx
  -- a maximal `rad C₀ a`-separated subset of `tb.U`
  rcases exists_separatedNetCover hbounded (r := (rad C₀ a : ℝ)) hApos with
    ⟨N, hNU, hsep, hmax, _cvA, _cv2A, _dj, _cd⟩
  classical
  -- the sub-net `N_r = {y ∈ N | closedBall y (2A) ∩ ball x r ≠ ∅}`
  let N_r : Finset E := {y ∈ N | (closedBall y (2 * (rad C₀ a : ℝ)) ∩ ball x r).Nonempty}
  -- the localized half of `netUpper`, applied to `N_r`
  have hnu_loc : volume (tb.UW ∩ ball x r) ≤ nuK * (N_r.card * vola) := by
    have hun := (netUpper hdim tb N hNU hmax).2 x r
    simpa [nuK, N_r, vola] using hun
  -- measurability of the target ball
  have hFmeas : MeasurableSet (ball x (2 * r)) := isOpen_ball.measurableSet
  -- `N_r ⊆ N`
  have hN' : N_r ⊆ N := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  -- for `y ∈ N_r`, the `A`-ball at `y` is contained in `borrow 2r`
  have hball : ∀ y ∈ N_r, ball y (rad C₀ a : ℝ) ⊆ ball x (2 * r) := by
    intro y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨z, hz⟩
    have hzy : dist y z ≤ 2 * (rad C₀ a : ℝ) := by
      simpa [dist_comm] using mem_closedBall.mp hz.1
    have hzx : dist z x < r := Metric.mem_ball.mp hz.2
    intro u hu
    have huey : dist u y < (rad C₀ a : ℝ) := Metric.mem_ball.mp hu
    have hydx : dist y x ≤ 2 * (rad C₀ a : ℝ) + r :=
      le_trans (dist_triangle y z x) (add_le_add hzy (le_of_lt hzx))
    have huLe : dist u x < r + 3 * (rad C₀ a : ℝ) := by
      have h1 : dist u x < (rad C₀ a : ℝ) + dist y x := by
        linarith [dist_triangle u y x, huey]
      have h2 : (rad C₀ a : ℝ) + dist y x ≤ (rad C₀ a : ℝ) + (2 * (rad C₀ a : ℝ) + r) := by
        linarith [hydx]
      have h3 : (rad C₀ a : ℝ) + (2 * (rad C₀ a : ℝ) + r) ≤ r + 3 * (rad C₀ a : ℝ) := by
        linarith
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3
    have hfin : dist u x < 2 * r := by
      exact lt_of_lt_of_le huLe (by nlinarith [hr])
    exact Metric.mem_ball.mpr hfin
  -- `netLower` with `F = ball x (2r)`, `N' = N_r`
  have hnl : nlK⁻¹ * (N_r.card * ((δ : ENNReal) ^ η * volδ)) ≤
      volume (tb.U ∩ ball x (2 * r)) := by
    simpa [nlK, volδ] using
      (netLower hdim tb hδ hδa N hNU hsep (ball x (2 * r)) hFmeas N_r hN' hball)
  -- the ball-volume ratio `(δ/a)³ · |B(0,a)| = |B(0,δ)|` in dimension three
  have hapos : (0 : ℝ) < (a : ℝ) := by
    exact lt_of_lt_of_le (NNReal.coe_pos.mpr hδ) (NNReal.coe_le_coe.mpr hδa)
  have hδpos_real : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have ha_ne0 : (a : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hapos).ne'
  have ha_neTop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδof : ENNReal.ofReal (δ : ℝ) = (δ : ENNReal) := by
    rw [ENNReal.ofReal]
    simp [Real.toNNReal_of_nonneg (le_of_lt hδpos_real)]
  have haof : ENNReal.ofReal (a : ℝ) = (a : ENNReal) := by
    rw [ENNReal.ofReal]
    simp [Real.toNNReal_of_nonneg (le_of_lt hapos)]
  let Cvol : ENNReal :=
    ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E / Real.Gamma (↑(Module.finrank ℝ E) / 2 + 1))
  have hKδ : volume (ball (0 : E) (δ : ℝ)) =
      ENNReal.ofReal (δ : ℝ) ^ Module.finrank ℝ E * Cvol := by
    rw [InnerProductSpace.volume_ball]
  have hKa : volume (ball (0 : E) (a : ℝ)) =
      ENNReal.ofReal (a : ℝ) ^ Module.finrank ℝ E * Cvol := by
    rw [InnerProductSpace.volume_ball]
  have hvol' : q ^ Module.finrank ℝ E * vola = volδ := by
    dsimp [q, volδ, vola]
    rw [hKδ, hKa]
    calc
      q ^ Module.finrank ℝ E * (ENNReal.ofReal (a : ℝ) ^ Module.finrank ℝ E * Cvol)
          = (q * ENNReal.ofReal (a : ℝ)) ^ Module.finrank ℝ E * Cvol := by
              rw [← mul_assoc, mul_pow]
      _ = ENNReal.ofReal (δ : ℝ) ^ Module.finrank ℝ E * Cvol := by
              have hbase : q * ENNReal.ofReal (a : ℝ) = ENNReal.ofReal (δ : ℝ) := by
                dsimp [q]
                rw [hδof, haof]
                exact ENNReal.div_mul_cancel ha_ne0 ha_neTop
              rw [hbase]
  have hvol : q ^ 3 * vola = volδ := by
    simpa [hdim] using hvol'
  -- the clean constant `cK = nuK · nlK`, and the cancellation inside it
  let cK : ENNReal := nuK * nlK
  have hUcK : uK = 2 ^ 3 * cK := by
    simp [hUc, cK, mul_assoc]
  have hnu_ne0 : nuK ≠ 0 :=
    (ENNReal.coe_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_netUpperConstant C C₀))).ne'
  have hnu_neTop : nuK ≠ ⊤ := ENNReal.coe_ne_top
  have hnl_ne0 : nlK ≠ 0 :=
    (ENNReal.coe_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_netLowerConstant C))).ne'
  have hnl_neTop : nlK ≠ ⊤ := ENNReal.coe_ne_top
  have hccanc : cK⁻¹ * nuK = nlK⁻¹ := by
    dsimp [cK]
    rw [ENNReal.mul_inv (Or.inl hnu_ne0) (Or.inl hnu_neTop)]
    calc
      (nuK⁻¹ * nlK⁻¹) * nuK = nlK⁻¹ * (nuK⁻¹ * nuK) := by ac_rfl
      _ = nlK⁻¹ * 1 := by rw [ENNReal.inv_mul_cancel hnu_ne0 hnu_neTop]
      _ = nlK⁻¹ := by simp
  -- `uK = 2³ · cK ≥ cK`, so `uK⁻¹ ≤ cK⁻¹`
  have hcK_le_uK : cK ≤ uK := by
    rw [hUcK]
    simpa using
      (mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ 2 ^ 3) zero_le)
  have hucK_le : uK⁻¹ ≤ cK⁻¹ := ENNReal.inv_le_inv' hcK_le_uK
  have hcuLe : uK⁻¹ * nuK ≤ nlK⁻¹ := by
    calc
      uK⁻¹ * nuK ≤ cK⁻¹ * nuK := mul_le_mul_of_nonneg_right hucK_le zero_le
      _ = nlK⁻¹ := hccanc
  -- eliminate the net cardinality between the localized upper and lower estimates
  calc
    uK⁻¹ * (δ : ENNReal) ^ η * q ^ 3 * volume (tb.UW ∩ ball x r)
        ≤ uK⁻¹ * (δ : ENNReal) ^ η * q ^ 3 * (nuK * (N_r.card * vola)) := by
            gcongr
    _ = (uK⁻¹ * nuK) * ((δ : ENNReal) ^ η * q ^ 3 * N_r.card * vola) := by ac_rfl
    _ ≤ nlK⁻¹ * ((δ : ENNReal) ^ η * q ^ 3 * N_r.card * vola) :=
            mul_le_mul_of_nonneg_right hcuLe zero_le
    _ = nlK⁻¹ * ((δ : ENNReal) ^ η * N_r.card * (q ^ 3 * vola)) := by ac_rfl
    _ = nlK⁻¹ * ((δ : ENNReal) ^ η * N_r.card * volδ) := by rw [hvol]
    _ = nlK⁻¹ * (N_r.card * ((δ : ENNReal) ^ η * volδ)) := by ac_rfl
    _ ≤ volume (tb.U ∩ ball x (2 * r)) := hnl

/-- **Transferring the filling from the bodies to the tubes, in the thin case** (blueprint
`lem:ml2thinTransfer`, second inequality).

The thin-case form of `Kakeya.ThinCase.transfer`: since `a ≤ δ^{1-τ}` we have `δ/a ≥ δ^τ`, so
the first inequality reads
`|U(𝕋_B, Y'_B) ∩ B_{2r}| ⪆ δ^{3τ+η} |U(𝕎'_B, Y_{𝕎'_B}) ∩ B_r|`. -/
theorem transfer_thin (hdim : Module.finrank ℝ E = 3)
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) (hδ : 0 < δ) (hδa : δ ≤ a)
    {τ : ℝ} (hthin : a ≤ δ ^ (1 - τ))
    {r : ℝ} (hr : 3 * (rad C₀ a : ℝ) ≤ r) (x : E) :
    ((transferConstant C C₀ : NNReal) : ENNReal)⁻¹ * (δ : ENNReal) ^ (3 * τ + η) *
      volume (tb.UW ∩ ball x r) ≤ volume (tb.U ∩ ball x (2 * r)) := by
  let uK : ENNReal := (transferConstant C C₀ : NNReal)
  have hδne0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ).ne'
  have hδneTop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hapos : (0 : ℝ) < (a : ℝ) := by
    exact lt_of_lt_of_le (NNReal.coe_pos.mpr hδ) (NNReal.coe_le_coe.mpr hδa)
  have ha_ne0 : (a : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hapos).ne'
  have ha_neTop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- lift `hthin` (in `NNReal`) to `ENNReal`
  have hthin' : (a : ENNReal) ≤ (δ : ENNReal) ^ (1 - τ) := by
    have hle : (a : ENNReal) ≤ ((δ ^ (1 - τ) : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr hthin
    have hco : (δ : ENNReal) ^ (1 - τ) = ((δ ^ (1 - τ) : NNReal) : ENNReal) :=
      (ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ) (1 - τ)).symm
    simpa [hco] using hle
  -- from `a ≤ δ^(1-τ)` deduce `δ^τ ≤ δ/a`
  have hratio : (δ : ENNReal) ^ τ ≤ (δ : ENNReal) / (a : ENNReal) := by
    have hmt : (δ : ENNReal) ^ τ * (a : ENNReal) ≤
        (δ : ENNReal) ^ τ * (δ : ENNReal) ^ (1 - τ) := by
      gcongr
    have hsum : (δ : ENNReal) ^ τ * (δ : ENNReal) ^ (1 - τ) = (δ : ENNReal) := by
      rw [← ENNReal.rpow_add τ (1 - τ) hδne0 hδneTop,
        show (τ + (1 - τ) : ℝ) = 1 by ring, ENNReal.rpow_one]
    have hmul : (δ : ENNReal) ^ τ * (a : ENNReal) ≤ (δ : ENNReal) := by
      simpa [hsum] using hmt
    exact (ENNReal.le_div_iff_mul_le (Or.inl ha_ne0) (Or.inl ha_neTop)).mpr hmul
  -- cube: `δ^(3τ) ≤ (δ/a)³`
  have hcubed : (δ : ENNReal) ^ (3 * τ) ≤ ((δ : ENNReal) / (a : ENNReal)) ^ 3 := by
    calc
      (δ : ENNReal) ^ (3 * τ) = ((δ : ENNReal) ^ τ) ^ 3 := by
        simp [show (3 * τ : ℝ) = τ * 3 by ring, ENNReal.rpow_mul]
      _ ≤ ((δ : ENNReal) / (a : ENNReal)) ^ 3 := ENNReal.pow_le_pow_left hratio
  -- chain with the general estimate
  have htransfer := transfer hdim tb hδ hδa hr x
  calc
    uK⁻¹ * (δ : ENNReal) ^ (3 * τ + η) * volume (tb.UW ∩ ball x r)
        = uK⁻¹ * ((δ : ENNReal) ^ η * (δ : ENNReal) ^ (3 * τ)) * volume (tb.UW ∩ ball x r) := by
            rw [ENNReal.rpow_add (3 * τ) η hδne0 hδneTop]
            ac_rfl
    _ ≤ uK⁻¹ * ((δ : ENNReal) ^ η * ((δ : ENNReal) / (a : ENNReal)) ^ 3) *
        volume (tb.UW ∩ ball x r) := by
            gcongr
    _ = uK⁻¹ * (δ : ENNReal) ^ η * ((δ : ENNReal) / (a : ENNReal)) ^ 3 *
        volume (tb.UW ∩ ball x r) := by ac_rfl
    _ ≤ volume (tb.U ∩ ball x (2 * r)) := by
            simpa [uK] using htransfer

end Density

end Kakeya.ThinCase

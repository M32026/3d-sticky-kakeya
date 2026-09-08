/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.KatzTaoPlankInputs

/-!
# GWZ Section 6 estimates: Katz–Tao estimate for planks

This file carries the two public statements of GWZ Lemma 6.1,
`Kakeya.KatzTaoEstimate.plankEstimate` and `Kakeya.KatzTaoEstimate.plankEstimate_of_isKatzTao`.
Their inputs — the `ENNReal`/rpow algebra (`Kakeya.plankKT_final_algebra`,
`Kakeya.plankKT_absorb`, `Kakeya.theta_factor_le_eccentricity_factor`), the wide-slab constant
`Kakeya.Rslab`, the Remark 6.3 branch `Kakeya.RHSplankKT_ge_smallMultiplicityThreshold`, the
threshold form `Kakeya.exists_b0_multiplicity_bound` of generalized Lemma 3.7, and the tube layer
(`Kakeya.plankKT_maxDensity_tube_le`, `Kakeya.plankKT_fullness_tube_le`,
`Kakeya.exists_b₀_tube_fullness_threshold`, `Kakeya.exists_anchorShading`, and
`Kakeya.plankKT_card_enn_of_mul_le`) live in `KatzTaoPlankInputs.lean`.

Keeping the helper layer separate avoids recompiling it while editing the final assembly below.

The local adapters between Lemma 6.13 and generalized Lemma 3.7 live here: `plankKT_post37` and
`plankKT_item4_post37` own the `ENNReal`/rpow algebra, `plankKT_selectedSlabPackage` owns the
reindexing from the plank indexing to the representative indexing, and `plankKT_tube_fullness` /
`plankKT_tube_card` convert Lemma 6.13's Item 2 and the wide-slab hypothesis into the exact
fullness and cardinality inputs that `plankKT_post37` consumes. `plankKT_highBranch` chains all of
those into the high-multiplicity branch, so the main theorem itself only chooses exponents, splits
on multiplicity, invokes Lemma 6.13, and absorbs once.

## The shape of the proof (GWZ Section 6.3, equations (41)–(42))

`μ(𝒫) ≲ a^(-Oη) · (aN)/(bθ) · μ(𝒫_{θ,S})` from Lemma 6.13 Item 4; then, after normalising the
selected slab to the unit ball and applying the generalized Lemma 3.7 at the analytic scale
`τ = a/8` to the `b/8`-tubes,

`μ(𝒫_{θ,S}) ≲ loss · Δ_max(𝒫_{θ,S})^(1-β) · |𝒫_{θ,S}|^β`,

with `Δ_max(𝒫_{θ,S}) ≲ (bθ)/(aN) · Δ_max(𝒫)` (`Kakeya.plankKT_maxDensity_tube_le`) and
`|𝒫_{θ,S}| ≲ N⁻¹ · a^(-η) · θ^γ · |𝒫|` (`Kakeya.plankKT_card_enn_of_mul_le` on top of the wide-slab
bridge). The fibre scale `N` cancels completely, and that cancellation is done once and for all in
`Kakeya.plankKT_final_algebra`.

## Conventions

Shaded plank families are represented directly by `V : ι → ShadedPlank a b hab hb1`, so fullness and
multiplicity use `fun i ↦ (V i).toShadedBody` while max-density uses `fun i ↦ (V i).toConvexSpaceBody`.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-- Multiplicity sees only the shades, so two shadings that agree on `s` have equal multiplicity.

Needed to move GWZ Lemma 6.13's Item 4, which bounds `μ(𝒫)` by the multiplicity of `Yθ`, onto the
Katz–Tao tube family, whose multiplicity is what `Kakeya.plankKT_post37` estimates: the anchor
shading produced by `Kakeya.exists_anchorShading` has the same shades as `Yθ` on the active set but
a different (larger) carrier, and `Plank.multiplicity_ktTubeFamily` then transports across the slab
normalisation. -/
private theorem multiplicity_congr_of_shade_eq {ι : Type*} (s : Finset ι)
    (V W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (h : ∀ i ∈ s, (V i).shade = (W i).shade) :
    ShadedBody.multiplicity s V = ShadedBody.multiplicity s W := by
  have hsum : (∑ i ∈ s, volume (V i).shade) = ∑ i ∈ s, volume (W i).shade :=
    Finset.sum_congr rfl fun i hi => by rw [h i hi]
  have hunion : (⋃ i ∈ s, (V i).shade) = ⋃ i ∈ s, (W i).shade :=
    Set.iUnion₂_congr h
  rw [ShadedBody.multiplicity_eq_div s V, ShadedBody.multiplicity_eq_div s W, hsum, hunion]

/-- The `ℝ≥0` definition of the tube-fullness constant, transported to `ENNReal`.

`Kakeya.plankKT_tube_fullness` states its constant comparison in `ENNReal`, while the natural place
to *define* `CFull` is `ℝ≥0`, where it is just `Cdil^3 · 40 (1+Cang)^3 (1+Cset)^3 / c2`. This is the
one-line cast between the two, isolated because pushing a coercion through a cube and two `1 + ·`
sums inside a larger tactic block is exactly the sort of step that derails an otherwise mechanical
proof. -/
private theorem coe_fullnessConst_le {Cdil Cang Cset c2 CFull : ℝ≥0}
    (h : c2 * CFull = Cdil ^ 3 * (40 * (1 + Cang) ^ 3 * (1 + Cset) ^ 3)) :
    (Cdil : ENNReal) ^ 3 * (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3)
      ≤ (c2 : ENNReal) * (CFull : ENNReal) := by
  rw [← ENNReal.coe_mul, h]
  push_cast
  exact le_rfl

/-- The fixed constant assembled by `Kakeya.plankKT_item4_post37` is finite, hence bounded by a
single `ℝ≥0` constant `≥ 1` of the shape `Kakeya.plankKT_absorb` consumes.

The constant produced by the assembly is `C₄ · (8^εKT · CΔ^(1-β)) · Ccard^β`, an `ENNReal`
expression mixing coercions with `rpow`s. Matching it against `plankKT_absorb`'s `(C : ℝ≥0)`
argument by hand means pushing casts through three `rpow`s; it is far cheaper to observe that every
factor is finite, so the whole product is, and to take `C` to be its `toNNReal` raised to at least
`1`. Nothing about the *value* of the constant matters downstream — only that it is fixed and
finite. -/
private theorem exists_absorbing_constant {β εKT : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hεKT : 0 ≤ εKT) {X Y Z : ENNReal} (hX : X ≠ ⊤) (hY : Y ≠ ⊤) (hZ : Z ≠ ⊤) :
    ∃ C : ℝ≥0, 1 ≤ C ∧
      X * ((8 : ENNReal) ^ εKT * Y ^ (1 - β)) * Z ^ β ≤ (C : ENNReal) := by
  let P : ENNReal := X * ((8 : ENNReal) ^ εKT * Y ^ (1 - β)) * Z ^ β
  have h8 : (8 : ENNReal) ≠ ⊤ := by norm_num
  have h8pow : (8 : ENNReal) ^ εKT ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hεKT h8
  have hYpow : Y ^ (1 - β) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith : 0 ≤ 1 - β) hY
  have hZpow : Z ^ β ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hβ0 hZ
  have hmid : (8 : ENNReal) ^ εKT * Y ^ (1 - β) ≠ ⊤ := ENNReal.mul_ne_top h8pow hYpow
  have hP : P ≠ ⊤ := by
    dsimp [P]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hX hmid) hZpow
  refine ⟨max P.toNNReal 1, le_max_right P.toNNReal 1, ?_⟩
  have hle : P ≤ ((max P.toNNReal 1 : ℝ≥0) : ENNReal) := by
    calc
      P = (P.toNNReal : ENNReal) := (ENNReal.coe_toNNReal hP).symm
      _ ≤ (max P.toNNReal 1 : ℝ≥0) := ENNReal.coe_le_coe_of_le (le_max_left P.toNNReal 1)
  exact hle

/-- **Helper A: the generalized Lemma 3.7 applied to the Katz–Tao tube family.**

This knows nothing about GWZ Lemma 6.13: it takes an already-packaged tube family together with the
three estimates the assembly has at that point (fullness, max-density, cardinality) and returns the
post-3.7 bound. The instantiation is the one GWZ Section 6.3 uses, with the *physical* tube radius
and the *analytic* scale kept apart:

`δ := b / 8` (the radius of `Plank.slabTube`) and `τ := a / 8`.

Both side conditions are discharged here: `0 < a / 8` from `0 < a`, and `a / 8 ≤ b / 8` from
`a ≤ b`. Using `τ := a` instead would be wrong — the fullness that the tube family actually has is
`(a/8) ^ ηKT`, not `a ^ ηKT`.

The only fixed constant produced is `8 ^ εKT * CΔ ^ (1 - β)`: the `8 ^ εKT` is what
`(a/8) ^ (-εKT) = 8 ^ εKT · a ^ (-εKT)` releases, and `CΔ ^ (1 - β)` is the density constant raised
through the `1 - β` power. Nothing here depends on `θ`, `N`, `A` or the plank family, and no
constant is absorbed yet — absorption happens once, at the very end of the main theorem. -/
private theorem plankKT_post37 {β εKT ηKT γ : ℝ} {a b θ : ℝ≥0} {N : ℕ} {κ : Type*}
    (A : Finset κ) (T : κ → ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3)))
    {CΔ ΔP K : ENNReal}
    (ha : 0 < a) (hab : a ≤ b) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hεKT : 0 ≤ εKT)
    (hKT : ∀ τ : ℝ≥0, 0 < τ → τ ≤ b / 8 →
      ∀ (t : Finset κ) (T' : κ → ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T' i).carrier ⊆ Metric.closedBall 0 1) →
        τ ^ ηKT ≤ ShadedBody.fullness t (fun i => (T' i).toShadedBody) →
        ShadedBody.multiplicity t (fun i => (T' i).toShadedBody) ≤
          (τ : ENNReal) ^ (-εKT)
            * (maxDensity t (fun i => (T' i).toConvexSpaceBody)) ^ (1 - β)
            * (t.card : ENNReal) ^ β)
    (hball : ∀ i, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hfull : (a / 8 : ℝ≥0) ^ ηKT ≤ ShadedBody.fullness A (fun i => (T i).toShadedBody))
    (hdens : maxDensity A (fun i => (T i).toConvexSpaceBody)
      ≤ CΔ * (((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP)
    (hcard : (A.card : ENNReal) ≤ (N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) :
    ShadedBody.multiplicity A (fun i => (T i).toShadedBody)
      ≤ ((8 : ENNReal) ^ εKT * CΔ ^ (1 - β))
          * (a : ENNReal) ^ (-εKT)
          * ((((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP) ^ (1 - β)
          * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β := by
  have ha8 : (0 : ℝ≥0) < a / 8 := by positivity
  have hab8 : (a / 8 : ℝ≥0) ≤ b / 8 := by gcongr
  have hmain := hKT (a / 8) ha8 hab8 A T hball hfull
  have ha_ne_zero : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt ha)
  have ha_ne_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have ha_rpow_ne_zero : (a : ENNReal) ^ εKT ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, ha_ne_zero, ha_ne_top]
  have ha_rpow_ne_top : (a : ENNReal) ^ εKT ≠ ⊤ := by
    simp [ENNReal.rpow_eq_top_iff, ha_ne_zero, ha_ne_top]
  have hscale : (((a / 8 : ℝ≥0)) : ENNReal) ^ (-εKT)
      = (8 : ENNReal) ^ εKT * (a : ENNReal) ^ (-εKT) := by
    rw [ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0)]
    rw [ENNReal.rpow_neg, ENNReal.div_rpow_of_nonneg _ _ hεKT]
    rw [ENNReal.inv_div (Or.inr ha_rpow_ne_top) (Or.inr ha_rpow_ne_zero)]
    rw [div_eq_mul_inv]
    rw [← ENNReal.rpow_neg]
    norm_num
  have h1mβ : (0:ℝ) ≤ 1 - β := by linarith
  have hd : (maxDensity A (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
      ≤ CΔ ^ (1 - β) * ((((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP) ^ (1 - β) := by
    calc
      (maxDensity A (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          ≤ (CΔ * (((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP) ^ (1 - β) :=
            ENNReal.rpow_le_rpow hdens h1mβ
      _ = CΔ ^ (1 - β) * ((((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP) ^ (1 - β) := by
            rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ h1mβ]
  have hc : (A.card : ENNReal) ^ β ≤ ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β :=
    ENNReal.rpow_le_rpow hcard hβ0
  calc
    ShadedBody.multiplicity A (fun i => (T i).toShadedBody)
        ≤ (((a / 8 : ℝ≥0) : ENNReal) ^ (-εKT)
            * (maxDensity A (fun i => (T i).toConvexSpaceBody)) ^ (1 - β))
            * (A.card : ENNReal) ^ β := hmain
    _ = ((8 : ENNReal) ^ εKT * (a : ENNReal) ^ (-εKT))
            * (maxDensity A (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * (A.card : ENNReal) ^ β := by
          rw [hscale]
    _ ≤ ((8 : ENNReal) ^ εKT * (a : ENNReal) ^ (-εKT))
            * (CΔ ^ (1 - β) * ((((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP) ^ (1 - β))
            * (A.card : ENNReal) ^ β := by
          gcongr
    _ ≤ ((8 : ENNReal) ^ εKT * (a : ENNReal) ^ (-εKT))
            * (CΔ ^ (1 - β) * ((((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP) ^ (1 - β))
            * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β := by
          gcongr
    _ = ((8 : ENNReal) ^ εKT * CΔ ^ (1 - β))
            * (a : ENNReal) ^ (-εKT)
            * ((((θ * b / (a * (N : ℝ≥0)) : ℝ≥0)) : ENNReal) * ΔP) ^ (1 - β)
            * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β := by
          ring

/-- **Helper B: Item 4 of GWZ Lemma 6.13 composed with the post-3.7 bound.**

This is the whole scale bookkeeping of GWZ Section 6.3 in one step. It takes Item 4,

`μ(𝒫) ≤ C₄ · a^(-εred) · a^(-4η) · (a·N)/(b·θ) · μ(𝒫_{θ,S})`,

together with the output of `Kakeya.plankKT_post37`, and returns the shape of the conclusion of
Lemma 6.1 up to a single fixed constant and a single exponent loss.

Two things happen here. First, the fibre scale `N` disappears: Item 4's `(a·N)/(b·θ)`, the density
transfer's `(θ·b)/(a·N)` raised to `1 - β`, and the cardinality's `N⁻¹` raised to `β` cancel
exactly. That cancellation is *not* redone by hand — it is `Kakeya.plankKT_final_algebra`, which
also converts the surviving `θ` factor into the eccentricity factor `(a/b)^(γβ)`. Second, the
cardinality constant is taken in expanded form `K = Ccard · a^(-η) · |s|` (option (B) of the two
possible interfaces), because `(·)^β` then contributes its own `a^(-ηβ)` loss, and collecting that
loss here rather than in the main theorem is what keeps the final assembly short: the caller is left
with a single `a ^ (-(εred + 4η + εKT + ηβ))` to compare against `a ^ (-ε)`.

`N` is absent from the conclusion, as it must be. -/
private theorem plankKT_item4_post37 {a b θ : ℝ≥0} {β γ εred εKT η : ℝ} {N : ℕ}
    {C4 CKT Ccard μP μTube ΔP scard : ENNReal}
    (ha : 0 < a) (hb : 0 < b) (hθ0 : 0 < θ) (hθ : a / b ≤ θ) (hN : 1 ≤ N)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hitem4 : μP ≤ C4 * (a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η))
        * (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) * μTube)
    (hpost : μTube ≤ CKT * (a : ENNReal) ^ (-εKT)
        * ((((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) * ΔP) ^ (1 - β)
        * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ
            * (Ccard * (a : ENNReal) ^ (-η) * scard)) ^ β) :
    μP ≤ (C4 * CKT * Ccard ^ β)
        * (a : ENNReal) ^ (-(εred + 4 * η + εKT + η * β))
        * ΔP ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
        * scard ^ β := by
  let P : ENNReal := (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
  let X : ENNReal := (((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal)
  let K : ENNReal := Ccard * (a : ENNReal) ^ (-η) * scard
  have ha_ne : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt ha)
  have ha_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hβ0 : (0 : ℝ) ≤ β := hβ.le
  -- STEP 1: chain hitem4 with hpost
  have h1 : μP ≤ C4 * (a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * P
      * (CKT * (a : ENNReal) ^ (-εKT) * (X * ΔP) ^ (1 - β)
          * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β) := by
    exact hitem4.trans (by gcongr)
  -- STEP 2: reassociate so the N-factors sit together
  have h2 : C4 * (a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * P
      * (CKT * (a : ENNReal) ^ (-εKT) * (X * ΔP) ^ (1 - β)
          * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β)
      = (C4 * CKT)
          * ((a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * (a : ENNReal) ^ (-εKT))
          * (P * (X * ΔP) ^ (1 - β) * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β) := by
    ring
  -- STEP 3: apply plankKT_final_algebra to the N-bracket
  have hfinal := Kakeya.plankKT_final_algebra ha hb hθ0 hθ hN hβ hγ0 hγ1 (Δ := ΔP) (K := K)
  have h3 : (C4 * CKT)
      * ((a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * (a : ENNReal) ^ (-εKT))
      * (P * (X * ΔP) ^ (1 - β) * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β)
      ≤ (C4 * CKT)
          * ((a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * (a : ENNReal) ^ (-εKT))
          * (ΔP ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * K ^ β) := by
    gcongr
  -- STEP 4: expand K ^ β
  have hKbeta : K ^ β = Ccard ^ β * (a : ENNReal) ^ ((-η) * β) * scard ^ β := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ0, ENNReal.mul_rpow_of_nonneg _ _ hβ0]
    rw [ENNReal.rpow_mul]
  -- STEP 5: collect the four a-powers
  have hapow : (a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * (a : ENNReal) ^ (-εKT)
      * (a : ENNReal) ^ ((-η) * β) = (a : ENNReal) ^ (-(εred + 4 * η + εKT + η * β)) := by
    rw [← ENNReal.rpow_add _ _ ha_ne ha_top,
      ← ENNReal.rpow_add _ _ ha_ne ha_top,
      ← ENNReal.rpow_add _ _ ha_ne ha_top]
    congr 1
    ring
  -- STEP 6: assemble
  calc
    μP ≤ C4 * (a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * P
        * (CKT * (a : ENNReal) ^ (-εKT) * (X * ΔP) ^ (1 - β)
            * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β) := h1
    _ = (C4 * CKT)
        * ((a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * (a : ENNReal) ^ (-εKT))
        * (P * (X * ΔP) ^ (1 - β) * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β) := h2
    _ ≤ (C4 * CKT)
        * ((a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η)) * (a : ENNReal) ^ (-εKT))
        * (ΔP ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * K ^ β) := h3
    _ = (C4 * CKT * Ccard ^ β)
        * (a : ENNReal) ^ (-(εred + 4 * η + εKT + η * β))
        * ΔP ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
        * scard ^ β := by
      rw [hKbeta]
      rw [← hapow]
      ring

/-- **Helper C: the selected-slab anchor package.**

Purely combinatorial and geometric reindexing; no `ENNReal`, no `rpow`, no density or fullness.
GWZ Lemma 6.13 speaks in the *plank* indexing `ι` — its controlled slab membership is a statement
about `i ∈ s'` relative to `slabOf (R.repr i)`. The Katz–Tao tube API instead speaks in the
*representative* indexing `Plank.ThickenedPlank θ b _ _`, relative to one fixed slab `S`. This
lemma performs that translation once.

The bridge is a local representative selector `rep`, obtained from `R.indexSet = s'.image R.repr`
by classical choice on each active `Q`. It is deliberately *not* exposed as an API: every clause
below is guarded by `Q ∈ A`, and outside `A` the value of `rep` is an arbitrary fallback. The
anchor plank map is then `W Q := V (rep Q)` — no new geometric object is introduced.

`A.Nonempty` is automatic rather than assumed: `S` comes from `R.indexSet.image slabOf`, so some
active representative already maps to `S`. That is what supplies the fallback index for `rep`, so
no nonemptiness hypothesis is buried inside the choice.

Note that `Cbox` (the shading-carrier dilation of `Yθ`) and `cThk` (the representative-to-anchor
thickening dilation) are different constants with different roles; both are carried through
unchanged. -/
private theorem plankKT_selectedSlabPackage {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cset Cang Cbox : ℝ≥0}
    {s' : Finset ι} {V : ι → Plank a b hab hb1}
    (R : Plank.ThickenedRepr s' V θ hθ1 cThk)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hslabmem : ∀ i ∈ s', i ∈ Plank.inSlabFamilyC Cset Cang s' V (slabOf (R.repr i)))
    (hYθcar : ∀ Q ∈ R.indexSet, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Q.toPrismNDim.dilation Cbox).carrier)
    {N : ℕ} {cN : ℝ≥0}
    (hfib : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ)
      ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ))
    (S : Slab θ hθ1) (hS : S ∈ R.indexSet.image slabOf)
    (A : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hA : A = R.indexSet.filter (fun Q => slabOf Q = S)) :
    A.Nonempty ∧ A ⊆ R.indexSet ∧
    ∃ rep : Plank.ThickenedPlank θ b hθ1 hb1 → ι,
      (∀ Q ∈ A, rep Q ∈ s') ∧
      (∀ Q ∈ A, R.repr (rep Q) = Q) ∧
      (∀ Q ∈ A, Q ∈ Plank.inSlabFamilyC Cset Cang A (fun Q => V (rep Q)) S) ∧
      (∀ Q ∈ A, (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (((V (rep Q)).thickened θ hθ1).toPrismNDim.dilation cThk).carrier) ∧
      (∀ Q ∈ A, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Q.toPrismNDim.dilation Cbox).carrier) ∧
      (∀ Q ∈ A, (N : ℝ) / (cN : ℝ)
        ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ)) := by
  classical
  -- STEP 1: A ⊆ R.indexSet and A.Nonempty
  have hAsub : A ⊆ R.indexSet := by
    rw [hA]
    exact Finset.filter_subset _ _
  obtain ⟨Q₀, hQ₀, hQ₀S⟩ := (Finset.mem_image.mp hS)
  have hQ₀A : Q₀ ∈ A := by
    rw [hA]
    exact Finset.mem_filter.mpr ⟨hQ₀, hQ₀S⟩
  -- STEP 2: the fallback index i₀
  obtain ⟨i₀, hi₀, hi₀R⟩ := (Finset.mem_image.mp (by
    simpa [Plank.ThickenedRepr.indexSet] using hQ₀))
  -- STEP 3: the representative selector
  let rep : Plank.ThickenedPlank θ b hθ1 hb1 → ι :=
    fun Q => if h : ∃ i, i ∈ s' ∧ R.repr i = Q then h.choose else i₀
  have hhex : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A →
      ∃ i : ι, i ∈ s' ∧ R.repr i = Q := by
    intro Q hQ
    have hQim : Q ∈ s'.image R.repr := by
      simpa [Plank.ThickenedRepr.indexSet] using hAsub hQ
    exact (Finset.mem_image.mp hQim)
  have hrep_mem : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A → rep Q ∈ s' := by
    intro Q hQ
    have hex : ∃ i : ι, i ∈ s' ∧ R.repr i = Q := hhex Q hQ
    dsimp [rep]
    rw [dif_pos hex]
    exact hex.choose_spec.1
  have hrep_repr : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A → R.repr (rep Q) = Q := by
    intro Q hQ
    have hex : ∃ i : ι, i ∈ s' ∧ R.repr i = Q := hhex Q hQ
    dsimp [rep]
    rw [dif_pos hex]
    exact hex.choose_spec.2
  -- STEP 4: slabOf Q = S for Q ∈ A
  have hslabQ : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A → slabOf Q = S := by
    intro Q hQ
    rw [hA] at hQ
    exact (Finset.mem_filter.mp hQ).2
  -- STEP 5: the reindexed slab-membership clause
  have hslabMemA : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A →
    Q ∈ Plank.inSlabFamilyC Cset Cang A (fun Q => V (rep Q)) S := by
    intro Q hQ
    have hi : rep Q ∈ s' := hrep_mem Q hQ
    have hmem := hslabmem (rep Q) hi
    rw [hrep_repr Q hQ] at hmem
    rw [hslabQ Q hQ] at hmem
    obtain ⟨-, hcar, hangle⟩ := (Plank.mem_inSlabFamilyC.mp hmem)
    exact Plank.mem_inSlabFamilyC.mpr ⟨hQ, hcar, hangle⟩
  -- STEP 6: thickening containment
  have hthickA : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A →
    (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((V (rep Q)).thickened θ hθ1).toPrismNDim.dilation cThk).carrier := by
    intro Q hQ
    have htk := R.repr_subset_thickened (rep Q) (hrep_mem Q hQ)
    rw [hrep_repr Q hQ] at htk
    exact htk
  -- STEP 7: carry the carrier and fibre hypotheses along
  have hYθcarA : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A →
    ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) = (Q.toPrismNDim.dilation Cbox).carrier :=
    fun Q hQ => hYθcar Q (hAsub hQ)
  have hfibA : ∀ Q : Plank.ThickenedPlank θ b hθ1 hb1, Q ∈ A →
    (N : ℝ) / (cN : ℝ) ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) :=
    fun Q hQ => hfib Q (hAsub hQ)
  -- ASSEMBLE
  exact ⟨⟨Q₀, hQ₀A⟩, hAsub, rep, hrep_mem, hrep_repr, hslabMemA, hthickA, hYθcarA, hfibA⟩

/-- **Helper D (fullness half): Item 2 of GWZ Lemma 6.13 becomes the Lemma 3.7 fullness input.**

`Kakeya.plankKT_post37` needs fullness in the analytic form `(a/8) ^ ηKT ≤ λ(A, T)`, while Lemma
6.13 Item 2 supplies `cFull · a^(4 ηF) ≤ λ(A, Yθ)` on the selected slab. Three things happen here,
and the fixed constant is fully absorbed at this layer — the caller never sees a bare
`a^(4η) ≤ C · λ`.

1. `Kakeya.plankKT_fullness_tube_le` transfers the fullness from the shading `Yθ` to the Katz–Tao
   tube family, at the cost of `Cdil^3 · 40 (1+Cang)^3 (1+Cset)^3`.
2. That loss is compared against `cFull · CFull` (hypothesis `hCFull`) and `cFull` is cancelled,
   leaving exactly `a^(4 ηF) ≤ CFull · λ(A, T)`.
3. `hthr`, which the caller obtains from `Kakeya.exists_b₀_tube_fullness_threshold` at this same
   `CFull`, converts that into `(a/8)^ηKT ≤ λ(A, T)`.

The exponent is written `4 * ηF` rather than `4 * η` on purpose: Item 2 carries an extra `a^ε`
alongside `a^(4η)`, so the caller takes `ηF := η + ε/4` and the two losses are absorbed together.
The gap condition then reads `4η + ε < ηKT`, which is where the main theorem's choice of `η` is
forced. -/
private theorem plankKT_tube_fullness {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cset Cang Cbox Cdil : ℝ≥0} {ηF ηKT : ℝ} {cFull CFull : ℝ≥0}
    (hθ0 : 0 < θ) (hb0 : 0 < b) (hCdil : 1 ≤ Cdil) (hCbox : 1 ≤ Cbox) (hcd : cThk ≤ Cdil)
    (ha : 0 < a)
    (W : Plank.ThickenedPlank θ b hθ1 hb1 → Plank a b hab hb1)
    (Yθ Yanc : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (S : Slab θ hθ1) (A : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hmem : ∀ Q ∈ A, Q ∈ Plank.inSlabFamilyC Cset Cang A W S)
    (hYθcar : ∀ Q ∈ A, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Q.toPrismNDim.dilation Cbox).carrier)
    (hcarEq : ∀ Q ∈ A, ((Yanc Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier)
    (hQthick : ∀ Q ∈ A, (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((W Q).thickened θ hθ1).toPrismNDim.dilation cThk).carrier)
    (hshade : ∀ Q ∈ A, (Yanc Q).shade = (Yθ Q).shade)
    (hcFull : 0 < cFull)
    (hCFull : (Cdil : ENNReal) ^ 3 * (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3)
      ≤ (cFull : ENNReal) * (CFull : ENNReal))
    (hitem2 : cFull * a ^ (4 * ηF) ≤ ShadedBody.fullness A Yθ)
    (hthr : ∀ lam : ℝ≥0, a ^ (4 * ηF) ≤ CFull * lam → (a / 8 : ℝ≥0) ^ ηKT ≤ lam) :
    (a / 8 : ℝ≥0) ^ ηKT ≤ ShadedBody.fullness A (fun Q => (Plank.slabTubeFamily A W Yanc S
        (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
        (Plank.slabTubeConst_pos _ _) Q).toShadedBody) := by
  -- STEP 1: reduce via the analytic-scale threshold hthr
  refine hthr _ ?_
  -- STEP 2: transfer fullness from Yθ to the Katz--Tao tubes
  have htube := Kakeya.plankKT_fullness_tube_le hθ0 hb0 hCdil hCbox hcd W Yθ Yanc S A
    hmem hYθcar hcarEq hQthick hshade
  -- STEP 3: move hitem2 into ENNReal
  have h2 : (cFull : ENNReal) * (a : ENNReal) ^ (4 * ηF) ≤ ShadedBody.fullness' A Yθ := by
    have hcoe : ((cFull * a ^ (4 * ηF) : ℝ≥0) : ENNReal) ≤ (ShadedBody.fullness A Yθ : ENNReal) :=
      ENNReal.coe_le_coe.mpr hitem2
    rwa [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero (ne_of_gt ha) (4 * ηF), ShadedBody.coe_fullness]
      at hcoe
  -- STEP 4: chain with htube, bound the constant by cFull * CFull, cancel cFull
  have h3 : (cFull : ENNReal) * (a : ENNReal) ^ (4 * ηF)
      ≤ (cFull : ENNReal) * ((CFull : ENNReal) * ShadedBody.fullness' A (fun Q =>
          (Plank.slabTubeFamily A W Yanc S
            (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
            (Plank.slabTubeConst_pos _ _) Q).toShadedBody)) := by
    calc (cFull : ENNReal) * (a : ENNReal) ^ (4 * ηF)
        ≤ ShadedBody.fullness' A Yθ := h2
      _ ≤ ((Cdil : ENNReal) ^ 3 * (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3))
            * ShadedBody.fullness' A (fun Q =>
                (Plank.slabTubeFamily A W Yanc S
                  (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
                  (Plank.slabTubeConst_pos _ _) Q).toShadedBody) := htube
      _ ≤ ((cFull : ENNReal) * (CFull : ENNReal)) * ShadedBody.fullness' A (fun Q =>
              (Plank.slabTubeFamily A W Yanc S
                (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
                (Plank.slabTubeConst_pos _ _) Q).toShadedBody) := by
            gcongr
      _ = (cFull : ENNReal) * ((CFull : ENNReal) * ShadedBody.fullness' A (fun Q =>
              (Plank.slabTubeFamily A W Yanc S
                (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
                (Plank.slabTubeConst_pos _ _) Q).toShadedBody)) := by
            ring
  have h4 : (a : ENNReal) ^ (4 * ηF)
      ≤ (CFull : ENNReal) * ShadedBody.fullness' A (fun Q =>
          (Plank.slabTubeFamily A W Yanc S
            (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
            (Plank.slabTubeConst_pos _ _) Q).toShadedBody) :=
    (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr (ne_of_gt hcFull)) ENNReal.coe_ne_top).mp h3
  -- STEP 5: descend to NNReal
  have h5 : ((a ^ (4 * ηF) : ℝ≥0) : ENNReal)
      ≤ ((CFull * ShadedBody.fullness A (fun Q =>
          (Plank.slabTubeFamily A W Yanc S
            (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
            (Plank.slabTubeConst_pos _ _) Q).toShadedBody) : ℝ≥0) : ENNReal) := by
    rw [ENNReal.coe_rpow_of_ne_zero (ne_of_gt ha) (4 * ηF), ENNReal.coe_mul, ShadedBody.coe_fullness]
    exact h4
  exact ENNReal.coe_le_coe.mp h5

/-- **Helper D (cardinality half): the wide-slab bridge becomes the Lemma 3.7 cardinality input.**

`Kakeya.plankKT_post37` needs `|A| ≤ N⁻¹ · θ^γ · K`. The wide-slab non-concentration hypothesis of
GWZ Lemma 6.1 is a statement about the *original* family `s` and about `Kakeya.Rslab`-wide slabs;
`Kakeya.Plank.card_assignedRepr_mul_le_of_wideSlabNonconcentration` turns it into a real
multiplicative inequality for the active representatives over the selected slab, and
`Kakeya.plankKT_card_enn_of_mul_le` moves that into `ENNReal` while dividing by the fibre lower
bound.

The `1/N` is the whole point of the fibre lower bound and must survive: it is what cancels Item 4's
`a·N/(b·θ)` in `Kakeya.plankKT_final_algebra`. The dynamic factor is exactly `N⁻¹ · θ^γ`; every
recentring, `Cset`, `Cang` and `cN` loss is collected into the fixed constant
`cN · 2 · max Cset Cang`. -/
private theorem plankKT_tube_card {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cset Cang : ℝ≥0} {η γ : ℝ} {N : ℕ} {cN : ℝ≥0}
    {s s' : Finset ι} {V : ι → Plank a b hab hb1}
    (hCang : 1 ≤ Cang) (ha : 0 < a) (hη : 0 ≤ η) (hγ1 : γ ≤ 1)
    (hθ0 : 0 < θ) (hθ : a / b ≤ θ) (hcN : 0 < cN) (hN : 1 ≤ N) (hs' : s' ⊆ s)
    (hwide : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ Sφ : Prism3D φ Rslab Rslab hφR le_rfl,
      ((Plank.inWideSlabFamily s V Sφ).card : ℝ≥0) ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0))
    (R : Plank.ThickenedRepr s' V θ hθ1 cThk)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (hslabmem : ∀ i ∈ s', i ∈ Plank.inSlabFamilyC Cset Cang s' V (slabOf (R.repr i)))
    (hfib : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ)
      ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ))
    (hwin : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ))
    (S : Slab θ hθ1) (A : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hA : A = R.indexSet.filter (fun Q => slabOf Q = S)) :
    (A.card : ENNReal) ≤ (N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ
      * (((cN * (2 * max Cset Cang) : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (-η)
          * (s.card : ENNReal)) := by
  -- STEP 1: the wide-slab bridge, reindexed from A to the active representatives
  have hbridgeA : (N : ℝ) / (cN : ℝ) * ((A.card : ℕ) : ℝ)
      ≤ ((2 * max Cset Cang * a ^ (-η) * θ ^ γ * (s.card : ℝ≥0) : ℝ≥0) : ℝ) := by
    rw [hA]
    exact Plank.card_assignedRepr_mul_le_of_wideSlabNonconcentration
      hCang (R := Rslab) (by norm_num [Rslab, plankWindowRadius])
      hs' V ha hη hγ1 hwide hθ R slabOf hslabmem
      (L := (N : ℝ) / (cN : ℝ)) (by positivity) hfib
      (r := (plankWindowRadius : ℝ)) (by norm_num [Rslab, plankWindowRadius]) hwin S
  -- STEP 2: reassociate the ℝ≥0 right-hand side to the C * θ^γ * K₀ form
  have hre : 2 * max Cset Cang * a ^ (-η) * θ ^ γ * (s.card : ℝ≥0)
      = (2 * max Cset Cang) * θ ^ γ * (a ^ (-η) * (s.card : ℝ≥0)) := by
    ring
  rw [hre] at hbridgeA
  -- STEP 3: convert to ENNReal, dividing by the fibre lower bound
  have hen := Kakeya.plankKT_card_enn_of_mul_le (N := N) (Acard := A.card)
    (C := 2 * max Cset Cang) (K₀ := a ^ (-η) * (s.card : ℝ≥0)) hcN hN hθ0 hbridgeA
  -- STEP 4: match the stated RHS by pushing the ℝ≥0 → ENNReal coercion through
  have heq : (((cN * (2 * max Cset Cang) * (a ^ (-η) * (s.card : ℝ≥0)) : ℝ≥0) : ENNReal))
      = (((cN * (2 * max Cset Cang) : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (-η))
          * (s.card : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero ha.ne' (-η), ← ENNReal.coe_natCast,
      ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    exact_mod_cast (by ring)
  rw [← heq]
  exact hen

/-- **Helper E: the high-multiplicity branch of GWZ Lemma 6.1.**

Everything between "GWZ Lemma 6.13 has fired and a slab `S` has been selected from its Item 4" and
"only a fixed constant and an exponent loss remain". It chains, in order: the selected-slab package
(`Kakeya.plankKT_selectedSlabPackage`), the anchor shading
(`Kakeya.Plank.carrier_subset_dilated_thickened_anchor` then `Kakeya.exists_anchorShading`), the
four generalized-3.7 inputs (`Kakeya.Plank.ktTubeFamily_carrier_subset_closedBall`,
`Kakeya.plankKT_tube_fullness`, `Kakeya.plankKT_maxDensity_tube_le`, `Kakeya.plankKT_tube_card`),
generalized 3.7 itself (`Kakeya.plankKT_post37`), and the scale bookkeeping
(`Kakeya.plankKT_item4_post37`).

Separating it from the main theorem keeps two independent concerns apart: this lemma is pure
plumbing at fixed `a`, `b`, `θ`, `N`, while the main theorem owns the choice of `εKT`, `εred`, `η`
and `b₀` and the single final absorption. Note the max-density on the right is still taken over the
*refined* family `s'`; the main theorem relaxes it to `s` with `Kakeya.maxDensity_mono`. -/
private theorem plankKT_highBranch {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {β γ εKT εred η ηF ηKT : ℝ} {cN cThk Cbox Cset Cang c2 c4 CFull Cdil : ℝ≥0}
    {CΔ Ccard : ENNReal} {s s' : Finset ι} {V : ι → ShadedPlank a b hab hb1}
    {N : ℕ} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (ha : 0 < a) (hb0 : 0 < b) (hβpos : 0 < β) (hβle : β ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hεKT0 : 0 ≤ εKT) (hη0 : 0 ≤ η) (hθ0 : 0 < θ) (hθab : a / b ≤ θ) (hN1 : 1 ≤ N)
    (h1cN : 1 ≤ cN) (h1cThk : 1 ≤ cThk) (hcThkCbox : cThk ≤ Cbox) (h1Cset : 1 ≤ Cset)
    (h1Cang : 1 ≤ Cang) (hc2 : 0 < c2)
    (hCdil : Cdil = (2 * Cbox + 1) * cThk)
    (hCΔ : CΔ = (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3)
      * (Cdil : ENNReal) ^ 3 * ((Plank.enlargementConst cThk * cN : ℝ≥0) : ENNReal))
    (hCcard : Ccard = ((cN * (2 * max Cset Cang) : ℝ≥0) : ENNReal))
    (hs' : s' ⊆ s)
    (hwin : ∀ i ∈ s, ((ShadedPlank.planks V) i).carrier
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ))
    (hwide : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ Sφ : Prism3D φ Rslab Rslab hφR le_rfl,
      ((Plank.inWideSlabFamily s (ShadedPlank.planks V) Sφ).card : ℝ≥0)
        ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0))
    (R : Plank.ThickenedRepr s' (ShadedPlank.planks V) θ hθ1 cThk)
    (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hslabmem : ∀ i ∈ s', i ∈ Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks V)
      (slabOf (R.repr i)))
    (hYθcar : ∀ Q ∈ R.indexSet, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Q.toPrismNDim.dilation Cbox).carrier)
    (hfib : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ)
      ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ))
    (S : Slab θ hθ1) (hS : S ∈ R.indexSet.image slabOf)
    (A : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hA : A = R.indexSet.filter (fun Q => slabOf Q = S))
    (hitem2 : c2 * a ^ (4 * η) * a ^ εred ≤ ShadedBody.fullness A Yθ)
    (hmul4 : ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
      ≤ (c4 : ENNReal) * (a : ENNReal) ^ (-εred) * (a : ENNReal) ^ (-(4 * η))
          * (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) * ShadedBody.multiplicity A Yθ)
    (hηF : ηF = η + εred / 4)
    (hCFull : c2 * CFull = Cdil ^ 3 * (40 * (1 + Cang) ^ 3 * (1 + Cset) ^ 3))
    (hthr : ∀ lam : ℝ≥0, a ^ (4 * ηF) ≤ CFull * lam → (a / 8 : ℝ≥0) ^ ηKT ≤ lam)
    (hKT : ∀ τ : ℝ≥0, 0 < τ → τ ≤ b / 8 →
      ∀ (t : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
        (T' : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T' i).carrier ⊆ Metric.closedBall 0 1) →
        τ ^ ηKT ≤ ShadedBody.fullness t (fun i => (T' i).toShadedBody) →
        ShadedBody.multiplicity t (fun i => (T' i).toShadedBody) ≤
          (τ : ENNReal) ^ (-εKT)
            * (maxDensity t (fun i => (T' i).toConvexSpaceBody)) ^ (1 - β)
            * (t.card : ENNReal) ^ β) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
      ≤ ((c4 : ENNReal) * ((8 : ENNReal) ^ εKT * CΔ ^ (1 - β)) * Ccard ^ β)
          * (a : ENNReal) ^ (-(εred + 4 * η + εKT + η * β))
          * (maxDensity s' (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
          * (s.card : ENNReal) ^ β := by
  -- STEP 1: the selected-slab package (Helper C)
  obtain ⟨hAne, hAsub, rep, hrepmem, hreprepr, hmemA, hQthick, hYθcarA, hfibA⟩ :=
    plankKT_selectedSlabPackage R slabOf Yθ hslabmem hYθcar hfib S hS A hA
  set W : Plank.ThickenedPlank θ b hθ1 hb1 → Plank a b hab hb1 :=
    fun Q => (ShadedPlank.planks V) (rep Q) with hW
  -- STEP 2: constant facts
  have hCbox0 : 0 < Cbox := by
    have hcThk0 : 0 < cThk := lt_of_lt_of_le zero_lt_one h1cThk
    exact lt_of_lt_of_le hcThk0 hcThkCbox
  have hCbox1 : 1 ≤ Cbox := h1cThk.trans hcThkCbox
  have hlarge : 1 ≤ 2 * Cbox + 1 := by
    calc
      1 ≤ 1 + 2 * Cbox := le_add_of_nonneg_right (by positivity)
      _ = 2 * Cbox + 1 := by ring
  have hCdil1 : 1 ≤ Cdil := by
    rw [hCdil]
    simpa using (mul_le_mul hlarge h1cThk (by positivity) (by positivity))
  have hcd : cThk ≤ Cdil := by
    rw [hCdil]
    simpa using (mul_le_mul hlarge (le_refl cThk) (by positivity) (by positivity))
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hcN0 : 0 < cN := lt_of_lt_of_le zero_lt_one h1cN
  -- STEP 3: anchor shading
  have hanc : ∀ Q ∈ A, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier := by
    intro Q hQ
    have hdil := PrismNDim.dilation_carrier_subset_dilation_of_carrier_subset
      (P := ((W Q).thickened θ hθ1).toPrismNDim) (Q := Q.toPrismNDim)
      (c := cThk) (C := Cbox) hCbox0 (hQthick Q hQ)
    rw [hYθcarA Q hQ, hCdil]
    exact hdil
  obtain ⟨Yanc, hYanccar, hYancshade⟩ := exists_anchorShading (ι := ι) W Yθ Cdil A hanc
  -- STEP 4: the tube family
  set T : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3)) :=
    fun Q => Plank.slabTubeFamily A W Yanc S
      (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
      (Plank.slabTubeConst_pos _ _) Q with hT
  have hball : ∀ Q, (T Q).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun Q => Plank.ktTubeFamily_carrier_subset_closedBall hθ0 hCdil1 hmemA Q
  have hCFull_le : (Cdil : ENNReal) ^ 3 *
      (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3)
      ≤ (c2 : ENNReal) * (CFull : ENNReal) := coe_fullnessConst_le hCFull
  have hit2 : c2 * a ^ (4 * ηF) ≤ ShadedBody.fullness A Yθ := by
    have hpow : a ^ (4 * η) * a ^ εred = a ^ (4 * ηF) := by
      rw [← NNReal.rpow_add ha.ne']
      congr 1
      rw [hηF]
      ring
    rw [← hpow, ← mul_assoc]
    exact hitem2
  have hfullT := plankKT_tube_fullness hθ0 hb0 hCdil1 hCbox1 hcd ha W Yθ Yanc S A
    hmemA hYθcarA (fun Q hQ => hYanccar Q) hQthick hYancshade hc2 hCFull_le hit2 hthr
  have hdensT := plankKT_maxDensity_tube_le hθ0 ha hCdil1 hcd R W Yanc S hAsub hmemA
    (fun Q hQ => hYanccar Q) hQthick hcN0 hN0 hfibA
  have hdensT' : maxDensity A (fun Q => (T Q).toConvexSpaceBody)
      ≤ CΔ * (((θ * b / (a * (N : ℝ≥0)) : ℝ≥0) : ENNReal))
          * maxDensity s' (fun i => (V i).toConvexSpaceBody) := by
    simpa [T, hCΔ, mul_assoc] using hdensT
  have hcardT := plankKT_tube_card h1Cang ha hη0 hγ1 hθ0 hθab hcN0 hN1 hs' hwide R slabOf
    hslabmem hfib hwin S A hA
  have hcardT' : (A.card : ENNReal) ≤ (N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ
      * (Ccard * (a : ENNReal) ^ (-η) * (s.card : ENNReal)) := by
    simpa [← hCcard, mul_assoc] using hcardT
  -- STEP 5: generalized Lemma 3.7
  have hpost := plankKT_post37 A T ha hab hβpos.le hβle hεKT0 hKT hball hfullT hdensT' hcardT'
  -- STEP 6: multiplicity transport
  have hmulEq : ShadedBody.multiplicity A Yθ
      = ShadedBody.multiplicity A (fun Q => (T Q).toShadedBody) := by
    rw [Plank.multiplicity_ktTubeFamily hθ0 hCdil1 hmemA (fun Q hQ => (hYanccar Q).subset)]
    exact multiplicity_congr_of_shade_eq A Yθ Yanc (fun Q hQ => (hYancshade Q hQ).symm)
  -- STEP 7: Helper B
  rw [hmulEq] at hmul4
  exact plankKT_item4_post37 ha hb0 hθ0 hθab hN1 hβpos hγ0 hγ1 hmul4 hpost

/-- **GWZ Lemma 6.1 (Katz--Tao estimate for planks)** (`plankKTUnified`).
Suppose `K_KT(β)` holds. For every `ε > 0` there are `η, b₀ > 0` so that for a finite family of
`a × b × 1` planks in `B₁` with `λ(𝒫, Y) ≥ a^η`, and any `0 ≤ γ ≤ 1` such that every `θ × 1 × 1`
slab `S` (with `a/b ≤ θ ≤ 1`) captures at most `a^(-η)·θ^γ·|s|` of the planks, the multiplicity
obeys `μ(𝒫, Y) ≤ a^(-ε)·Δ_max(𝒫)^(1-β)·(a/b)^(γβ)·|s|^β`. The `γ` is quantified after the geometric
data (avoiding the paper's "there exists γ" ambiguity). Consumed by GWZ Prop 6.6(B).

The exponents are not optimised. With `εKT := ε/8` for generalized Lemma 3.7 and
`εred := min (ε/8) (ηKT/4)` for Lemma 6.13, taking `η := min (ηKT/16) (ε/64)` gives the two
constraints room to spare: `4(η + εred/4) ≤ ηKT/2 < ηKT` is what the tube-fullness threshold needs,
and the total loss `εred + 4η + εKT + ηβ ≤ 21ε/64` stays below `ε`, leaving a positive gap for the
single final application of `Kakeya.plankKT_absorb`. That absorption is the only place `b₀` is
shrunk for the fixed constants; `b₀` is otherwise the minimum of the generalized-3.7 threshold, the
tube-fullness threshold, and `1/2` (which supplies `a < 1` for Lemma 6.13).

The Katz--Tao hypothesis is pinned to `KatzTaoEstimate.{0}` on purpose. `KatzTaoEstimate.{u}`
quantifies its tube families over `ι : Type u`, and the proof instantiates generalized Lemma 3.7
(`Kakeya.exists_b0_multiplicity_bound`, which shares that universe) at the representative index type
`Plank.ThickenedPlank θ b _ _`, a `Type 0`. Pinning to `0` strengthens the theorem, since it demands less of the caller, and
`Kakeya.KatzTao_one` is universe-polymorphic so it still applies. The plank family's own index `ι`
stays fully universe-polymorphic. -/
theorem KatzTaoEstimate.plankEstimate {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (s : Finset ι) {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (V : ι → ShadedPlank a b hab hb1),
        0 < a → b ≤ b₀ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        a ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
        ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
        (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
            ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
            ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
              ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
            (a : ENNReal) ^ (-ε)
              * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
  intro ε hε
  -- STEP 1: exponents
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨ηKT, hηKT, δ₀KT, hδ₀KT, hKT0⟩ :=
    exists_b0_multiplicity_bound hβpos.le hKKT (ε / 8) hε8
  set εred : ℝ := min (ε / 8) (ηKT / 4) with hεred_def
  set η : ℝ := min (ηKT / 16) (ε / 64) with hη_def
  set ηF : ℝ := η + εred / 4 with hηF_def
  set E : ℝ := εred + 4 * η + ε / 8 + η * β with hE_def
  have hεred0 : 0 < εred := by
    rw [hεred_def]
    exact lt_min hε8 (by positivity : 0 < ηKT / 4)
  have hη0 : 0 < η := by
    rw [hη_def]
    exact lt_min (by positivity : 0 < ηKT / 16) (by positivity : 0 < ε / 64)
  have hηF0 : 0 < ηF := by
    rw [hηF_def]
    positivity
  have hη64 : η ≤ ε / 64 := by
    rw [hη_def]
    exact min_le_right _ _
  have h4ηF : 4 * ηF < ηKT := by
    rw [hηF_def]
    have hle1 : 4 * η ≤ 4 * (ηKT / 16) := by
      rw [hη_def]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    have hle2 : εred ≤ ηKT / 4 := by
      rw [hεred_def]
      exact min_le_right _ _
    nlinarith
  have hηβ64 : η * β ≤ ε / 64 := by
    calc
      η * β ≤ (ε / 64) * β := mul_le_mul_of_nonneg_right hη64 hβpos.le
      _ ≤ (ε / 64) * 1 := mul_le_mul_of_nonneg_left hβle (by positivity : (0 : ℝ) ≤ ε / 64)
      _ = ε / 64 := by ring
  have hE : E < ε := by
    rw [hE_def]
    have h1 : εred ≤ ε / 8 := by
      rw [hεred_def]
      exact min_le_left _ _
    have h2 : 4 * η ≤ ε / 16 := by
      rw [hη_def]
      calc
        4 * min (ηKT / 16) (ε / 64) ≤ 4 * (ε / 64) := by
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ = ε / 16 := by ring
    nlinarith
  have hEpos : 0 < ε - E := by linarith
  have hηε : η + η * β ≤ ε := by
    nlinarith
  -- STEP 2: the 6.13 constants
  obtain ⟨cN, cThk, Cbox, Cset, Cang, h1cN, h1cThk, hcThkCbox, h1Cset, h1Cang, hAsm⟩ :=
    Kakeya.plankReduction
  obtain ⟨cP, cLam, c1, c2, c3, c4, hcP, hcLam, hc1, hc2, hc3, hc4, hcfg⟩ :=
    hAsm (η := η) (ε := εred) hη0 hεred0
  set Cdil : ℝ≥0 := (2 * Cbox + 1) * cThk with hCdil_def
  set CFull : ℝ≥0 := (Cdil ^ 3 * (40 * (1 + Cang) ^ 3 * (1 + Cset) ^ 3)) / c2 with hCFull_def
  have hCFull0 : 0 < CFull := by
    rw [hCFull_def]
    exact div_pos (by positivity) hc2
  have hCFulleq : c2 * CFull = Cdil ^ 3 * (40 * (1 + Cang) ^ 3 * (1 + Cset) ^ 3) := by
    rw [hCFull_def]
    field_simp [hc2.ne']
  obtain ⟨b₀F, hb₀F0, hthrF⟩ := exists_b₀_tube_fullness_threshold hηF0 hηKT h4ηF CFull hCFull0
  set CΔ : ENNReal :=
    (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3) * (Cdil : ENNReal) ^ 3
      * ((Plank.enlargementConst cThk * cN : ℝ≥0) : ENNReal) with hCΔ_def
  set Ccard : ENNReal := ((cN * (2 * max Cset Cang) : ℝ≥0) : ENNReal) with hCcard_def
  have hCΔ_ne_top : CΔ ≠ ⊤ := by
    rw [hCΔ_def]
    refine ENNReal.mul_ne_top ?_ (by exact ENNReal.coe_ne_top)
    refine ENNReal.mul_ne_top ?_ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    refine ENNReal.mul_ne_top ?_ (ENNReal.pow_ne_top
      (ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.coe_ne_top⟩))
    exact ENNReal.mul_ne_top (by norm_num : (40 : ENNReal) ≠ ⊤)
      (ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.coe_ne_top⟩))
  have hCcard_ne_top : Ccard ≠ ⊤ := by
    rw [hCcard_def]
    exact ENNReal.coe_ne_top
  obtain ⟨Cabs, hCabs1, hCabsle⟩ := exists_absorbing_constant
    (εKT := ε / 8) (X := (c4 : ENNReal)) (Y := CΔ) (Z := Ccard)
    hβpos.le hβle (by positivity : (0 : ℝ) ≤ ε / 8)
    ENNReal.coe_ne_top hCΔ_ne_top hCcard_ne_top
  obtain ⟨b₀A, hb₀A0, habs⟩ := plankKT_absorb Cabs hCabs1 (p := (1 : ℝ))
    (e := ε - E) (by norm_num) hEpos
  refine ⟨η, hη0, min (min b₀F b₀A) (min (8 * δ₀KT) (1 / 2)), ?_, ?_⟩
  · exact lt_min (lt_min hb₀F0 hb₀A0)
      (lt_min (by positivity : (0 : ℝ≥0) < 8 * δ₀KT) (by norm_num : (0 : ℝ≥0) < 1 / 2))
  · intro ι s a b hab hb1 V ha hbb₀ hVball hED hfull γ hγ0 hγ1 hslab
    have hb0 : 0 < b := lt_of_lt_of_le ha hab
    have hbF : b ≤ b₀F := le_trans hbb₀ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hbA : b ≤ b₀A := le_trans hbb₀ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hbKT : b ≤ 8 * δ₀KT := le_trans hbb₀ (le_trans (min_le_right _ _) (min_le_left _ _))
    have hbHalf : b ≤ 1 / 2 := le_trans hbb₀ (le_trans (min_le_right _ _) (min_le_right _ _))
    have ha1 : a < 1 := by
      have hle : a ≤ (1 / 2 : ℝ≥0) := le_trans hab hbHalf
      have hleR : (a : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast hle
      have hltR : (a : ℝ) < 1 := lt_of_le_of_lt hleR (by norm_num)
      exact_mod_cast hltR
    have hb8pos : (0 : ℝ≥0) < b / 8 := by positivity
    have hb8δ : b / 8 ≤ δ₀KT := by
      rw [div_le_iff₀ (show (0 : ℝ≥0) < 8 by norm_num)]
      simpa [mul_comm] using hbKT
    have hwin : ∀ i ∈ s, ((ShadedPlank.planks V) i).carrier
        ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
      intro i hi
      simpa using hVball i hi
    have hwinF : Plank.IsWindowedFamily s (ShadedPlank.planks V) := by
      intro i hi
      simpa [Plank.windowRadius, plankWindowRadius] using hVball i hi
    have hwide : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
        ∀ Sφ : Prism3D φ Rslab Rslab hφR le_rfl,
        ((Plank.inWideSlabFamily s (ShadedPlank.planks V) Sφ).card : ℝ≥0)
          ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0) := by
      intro φ hφR hφ Sφ
      simpa using hslab φ hφR hφ Sφ
    have hfullB : a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies V) := by
      simpa [ShadedPlank.bodies] using hfull
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · simp [ShadedBody.multiplicity]
    by_cases hlow : ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (a : ENNReal) ^ (-η)
    · exact hlow.trans
        (RHSplankKT_ge_smallMultiplicityThreshold s V ha hβpos hβle hγ0 hη0.le hηε hs hslab)
    · have hhigh : (a : ENNReal) ^ (-η)
        < ShadedBody.multiplicity s (fun i => (V i).toShadedBody) := lt_of_not_ge hlow
      -- high branch
      obtain ⟨s', Y', N, θ, hθ1, R, slabOf, Yθ, href, hcards, hfulls, hN1, hθab, hslabmem,
          hYθcar, hfibpair, hitem1, hitem2, hitem3, S, hS, hmul4⟩ :=
        hcfg s V ha ha1 hwinF hED hfullB hhigh.le
      have hs' : s' ⊆ s := href.1
      have hθ0 : 0 < θ := lt_of_lt_of_le (div_pos ha hb0) hθab
      have hfib : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ)
          ≤ (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) :=
        fun Q hQ => (hfibpair Q hQ).1
      set A : Finset (Plank.ThickenedPlank θ b hθ1 hb1) :=
        R.indexSet.filter (fun Q => slabOf Q = S) with hA_def
      have hHB := plankKT_highBranch (εKT := ε / 8) (εred := εred) (η := η) (ηF := ηF)
        (ηKT := ηKT) (CFull := CFull) (Cdil := Cdil) (CΔ := CΔ) (Ccard := Ccard)
        ha hb0 hβpos hβle hγ0 hγ1 (by positivity : (0 : ℝ) ≤ ε / 8) hη0.le hθ0 hθab hN1
        h1cN h1cThk hcThkCbox h1Cset h1Cang hc2 hCdil_def hCΔ_def hCcard_def hs' hwin hwide
        R slabOf Yθ hslabmem hYθcar hfib S hS A hA_def ((hitem2 S hS).1) hmul4 hηF_def hCFulleq
        (hthrF a b ha hab hbF)
        (fun τ hτ0 hτd t T' => hKT0 (b / 8) hb8pos hb8δ τ hτ0 hτd t T')
      have ha_ne_zero : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
      have ha_ne_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have hAbs : (Cabs : ENNReal) ≤ (a : ENNReal) ^ (-(ε - E)) := by
        simpa using habs a ha (le_trans hab hbA)
      have hpowsum : (a : ENNReal) ^ (-(ε - E)) * (a : ENNReal) ^ (-E)
          = (a : ENNReal) ^ (-ε) := by
        rw [← ENNReal.rpow_add (-(ε - E)) (-E) ha_ne_zero ha_ne_top]
        congr 1
        ring
      have hmono : maxDensity s' (fun i => (V i).toConvexSpaceBody)
          ≤ maxDensity s (fun i => (V i).toConvexSpaceBody) :=
        maxDensity_mono (fun i => (V i).toConvexSpaceBody) hs'
      have hpowmd : (maxDensity s' (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
          ≤ (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) :=
        ENNReal.rpow_le_rpow hmono (by linarith : (0 : ℝ) ≤ 1 - β)
      calc
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ((c4 : ENNReal) * ((8 : ENNReal) ^ (ε / 8) * CΔ ^ (1 - β)) * Ccard ^ β)
              * (a : ENNReal) ^ (-E)
              * (maxDensity s' (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
              simpa [hE_def] using hHB
        _ ≤ (Cabs : ENNReal)
              * (a : ENNReal) ^ (-E)
              * (maxDensity s' (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
              gcongr
        _ ≤ (a : ENNReal) ^ (-(ε - E))
              * (a : ENNReal) ^ (-E)
              * (maxDensity s' (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
              gcongr
        _ = (a : ENNReal) ^ (-ε)
              * (maxDensity s' (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
              rw [hpowsum]
        _ ≤ (a : ENNReal) ^ (-ε)
              * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
              gcongr

/-- **GWZ Lemma 6.1, Katz--Tao special case** (`plankKTUnified`, `_of_isKatzTao`). When the plank
family is `a^(-η)`-Katz--Tao the maximal-density factor may be dropped, giving
`μ(𝒫, Y) ≤ a^(-ε)·(a/b)^(γβ)·|s|^β`.

This is a **corollary** of `Kakeya.KatzTaoEstimate.plankEstimate`, not an independent leaf: apply
that theorem with `ε/2`, obtaining `η₀`, and take `η ≤ η₀` small enough that
`η · (1 - β) ≤ ε / 2`. The Katz--Tao hypothesis bounds `Δ_max ≤ a ^ (-η)`, so the dropped factor
`Δ_max ^ (1 - β)` is at most `a ^ (-η (1 - β)) ≤ a ^ (-ε/2)`, which the remaining `a ^ (-ε/2)`
absorbs. Shrinking `η` only strengthens both the fullness and the slab hypotheses (as `a ≤ 1`), so
they transfer. -/
theorem KatzTaoEstimate.plankEstimate_of_isKatzTao {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (s : Finset ι) {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (V : ι → ShadedPlank a b hab hb1),
        0 < a → b ≤ b₀ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        a ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
        IsKatzTao s (fun i => (V i).toConvexSpaceBody) (a ^ (-η)) →
        ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
        (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
            ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
            ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
              ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
            (a : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
              * (s.card : ENNReal) ^ β := by
  intro ε hε
  have hε2pos : 0 < ε / 2 := by linarith
  obtain ⟨η₀, hη₀, b₀, hb₀, h₀⟩ :=
    KatzTaoEstimate.plankEstimate hβpos hβle hKKT (ε/2) hε2pos
  set η := min η₀ (ε/2) with hη_def
  have hη_pos : 0 < η := lt_min hη₀ (by positivity : 0 < ε / 2)
  have hη_le_η₀ : η ≤ η₀ := min_le_left _ _
  have hη_le_ε2 : η ≤ ε / 2 := min_le_right _ _
  have h1mβ_le1 : 1 - β ≤ 1 := by linarith
  refine ⟨η, hη_pos, b₀, hb₀, ?_⟩
  intro ι s a b hab hb1 V ha hbb₀ hball hed hfull hKT γ hγ0 hγ1 hslab
  have ha1 : a ≤ 1 := hab.trans hb1
  have ha_nonzero : a ≠ 0 := ha.ne'
  have ha1' : (a : ENNReal) ≤ 1 := by exact_mod_cast ha1
  have ha_ne_zero : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha_nonzero
  have ha_ne_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- Transfer fullness hypothesis from η to η₀
  have hfull_η₀ : a ^ η₀ ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) := by
    calc
      a ^ η₀ ≤ a ^ η :=
        NNReal.rpow_le_rpow_of_exponent_ge ha ha1 hη_le_η₀
      _ ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) := hfull
  -- Transfer slab hypothesis from η to η₀
  have hslab_η₀ : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
        ≤ a ^ (-η₀) * φ ^ γ * (s.card : ℝ≥0) := by
    intro φ hφR hφ S
    have ha_neg_pow : a ^ (-η) ≤ a ^ (-η₀) :=
      NNReal.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith)
    calc
      ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0) ≤
          a ^ (-η) * φ ^ γ * (s.card : ℝ≥0) := hslab φ hφR hφ S
      _ ≤ a ^ (-η₀) * φ ^ γ * (s.card : ℝ≥0) := by
        calc
          a ^ (-η) * φ ^ γ * (s.card : ℝ≥0) = (a ^ (-η)) * (φ ^ γ * (s.card : ℝ≥0)) := by ring
          _ ≤ (a ^ (-η₀)) * (φ ^ γ * (s.card : ℝ≥0)) := mul_le_mul_of_nonneg_right ha_neg_pow (by positivity)
          _ = a ^ (-η₀) * φ ^ γ * (s.card : ℝ≥0) := by ring
  -- hKT gives us maxDensity ≤ (a : ENNReal) ^ (-η)
  -- Since IsKatzTao is defined as maxDensity s W ≤ C, hKT is already the needed inequality.
  have hmaxDensity_le : maxDensity s (fun i => (V i).toConvexSpaceBody) ≤ (a : ENNReal) ^ (-η) := hKT
  -- Apply plankEstimate with η₀, obtaining a bound with maxDensity factor
  have hresult := h₀ s hab hb1 V ha hbb₀ hball hed hfull_η₀ γ hγ0 hγ1 hslab_η₀
  -- Need: η * (1 - β) ≤ ε/2
  have h_eta_mul : η * (1 - β) ≤ ε / 2 := by
    calc
      η * (1 - β) ≤ (ε/2) * (1 : ℝ) := mul_le_mul hη_le_ε2 h1mβ_le1 (by linarith) (by positivity)
      _ = ε / 2 := by ring
  -- Bound the maxDensity factor: Δ^(1-β) ≤ (a : ENNReal)^(-(ε/2))
  have h_factor_bound : (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) ≤ (a : ENNReal) ^ (-(ε/2 : ℝ)) := by
    calc
      (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) ≤ ((a : ENNReal) ^ (-η)) ^ (1 - β) :=
        ENNReal.rpow_le_rpow hmaxDensity_le (by nlinarith : 0 ≤ 1 - β)
      _ = (a : ENNReal) ^ ((-η) * (1 - β : ℝ)) := by
        rw [ENNReal.rpow_mul]
      _ = (a : ENNReal) ^ (-η * (1 - β : ℝ)) := by ring
      _ ≤ (a : ENNReal) ^ (-(ε/2 : ℝ)) :=
        ENNReal.rpow_le_rpow_of_exponent_ge ha1' (by nlinarith)
  -- Combine the two (a : ENNReal) ^ (-(ε/2)) factors into (a : ENNReal) ^ (-ε)
  have h_add_pow : (a : ENNReal) ^ (-(ε/2 : ℝ)) * (a : ENNReal) ^ (-(ε/2 : ℝ)) = (a : ENNReal) ^ (-ε) := by
    calc
      (a : ENNReal) ^ (-(ε/2 : ℝ)) * (a : ENNReal) ^ (-(ε/2 : ℝ)) = (a : ENNReal) ^ ((-(ε/2 : ℝ)) + (-(ε/2 : ℝ))) := by
        rw [ENNReal.rpow_add (-(ε/2 : ℝ)) (-(ε/2 : ℝ)) ha_ne_zero ha_ne_top]
      _ = (a : ENNReal) ^ (-(ε/2 + ε/2 : ℝ)) := by ring
      _ = (a : ENNReal) ^ (-ε) := by ring
  -- hresult: μ ≤ (a : ENNReal)^(-(ε/2)) * Δ^(1-β) * ((a : ENNReal)/(b : ENNReal))^(γ*β) * (s.card : ENNReal)^β
  calc
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
        (a : ENNReal) ^ (-(ε/2 : ℝ)) * ((maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β))
          * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := hresult
    _ = ((a : ENNReal) ^ (-(ε/2 : ℝ)) * ((maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β))) * (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β) := by ring
    _ ≤ ((a : ENNReal) ^ (-(ε/2 : ℝ)) * ((a : ENNReal) ^ (-(ε/2 : ℝ))))
        * (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β) := by
      have htemp : (a : ENNReal) ^ (-(ε/2 : ℝ)) * ((maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)) ≤
          (a : ENNReal) ^ (-(ε/2 : ℝ)) * ((a : ENNReal) ^ (-(ε/2 : ℝ))) :=
        mul_le_mul (le_refl _) h_factor_bound (by positivity) (by positivity)
      exact mul_le_mul htemp (le_refl _) (by positivity) (by positivity)
    _ = ((a : ENNReal) ^ (-(ε/2 : ℝ)) * (a : ENNReal) ^ (-(ε/2 : ℝ)))
        * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by ring
    _ = (a : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
      rw [h_add_pow]

end Kakeya

end

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.PlankTube
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Thresholds
public import Kakeya.Factoring.FlatPrisms
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.TestBody
public import Kakeya.Tube.Center
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale
public import Kakeya.DimensionThree.MainLemma1.Rescaling.WindowTransport

/-!
# Main Lemma 1, Case (ii): Rescaling the middle factor to the unit ball

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### Rescaling the middle factor to the unit ball -/

section Rescale

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **(GWZ Lemma 8.1) The middle factor after normalization** (blueprint
`lem:ml1bootRescaleMiddle`).

Let `0 < δ ≤ τ ≤ θ` with `τ ≤ δ ^ ε θ`, and put `δ̃ = τ / θ`.  If the normalized family
`(𝕋̃, Ỹ) = ShadedTube.normalizeInto`-image of a shaded family `(𝕌, Z)` of `τ`-tubes inside a
`θ`-tube satisfies the rescaled bound `multTildeT` with loss `δ̃ ^ (10 a / ε)`, then `(𝕌, Z)`
satisfies the middle-scale bound `multTTauInsideTTheta` with loss `δ ^ (10 a)`.

The multiplicity and the index set are unchanged by the normalization
(`ShadedTube.normalizeInto_transport`), so the two displays differ only in their loss
factors, and `δ̃ ≤ δ ^ ε` converts `δ̃ ^ (10 a / ε)` into `δ ^ (10 a)`.  The direction of the
inequality is the favourable one, so no smallness assumption on `δ` is needed.

`a` is the blueprint's `η_{j-1}`.

Only `ε > 0`, `a ≥ 0` and `hsep` do any work here; the chain `hδ0`, `hδτ`, `hτθ` appears
solely to supply the positivity `0 < θ` that `ShadedTube.normalizeInto` requires, which is
why it is not assumed separately.  In particular no upper bound on `θ`, no nonemptiness of
`u` and no containment of the `τ`-tubes in `T_θ` are needed: those hypotheses belong to the
lemmas producing `hmult`, not to this conversion. -/
theorem middle_le_of_normalized {ε a γ : ℝ} (hε0 : 0 < ε) (ha : 0 ≤ a)
    {δ τ θ : NNReal} (hδ0 : 0 < δ) (hδτ : δ ≤ τ) (hτθ : τ ≤ θ)
    (hsep : τ ≤ δ ^ ε * θ)
    {ι : Type*} {u : Finset ι} (Tθ : Tube θ E) (U : ι → ShadedTube τ E)
    (hmult : ShadedBody.multiplicity u
        (fun k => (U k).normalizeInto Tθ (hδ0.trans_le (hδτ.trans hτθ)))
      ≤ ((τ / θ : NNReal) : ENNReal) ^ (10 * a / ε)
        * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((u.card : ENNReal) * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) :
    ShadedBody.multiplicity u (fun k => (U k).toShadedBody)
      ≤ (δ : ENNReal) ^ (10 * a)
        * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((u.card : ENNReal) * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  set δt : ENNReal := ((τ / θ : NNReal) : ENNReal) with hδtdef
  have htr := ShadedTube.normalizeInto_transport (hδ0.trans_le (hδτ.trans hτθ)) Tθ u U
  rw [← htr.multiplicity]
  refine le_trans hmult ?_
  have hθ0 : 0 < θ := lt_of_lt_of_le (lt_of_lt_of_le hδ0 hδτ) hτθ
  have hδtNN : (τ / θ : NNReal) ≤ δ ^ ε := by
    exact NNReal.div_le_of_le_mul hsep
  have hδtle : δt ≤ (δ : ENNReal) ^ ε := by
    rw [hδtdef]
    rw [ENNReal.rpow_ofNNReal hε0.le]
    exact_mod_cast hδtNN
  have hpow0 : 0 ≤ 10 * a / ε := by positivity
  have hle : δt ^ (10 * a / ε) ≤ (δ : ENNReal) ^ (10 * a) := by
    calc
      δt ^ (10 * a / ε) ≤ ((δ : ENNReal) ^ ε) ^ (10 * a / ε) := ENNReal.rpow_le_rpow hδtle hpow0
      _ = (δ : ENNReal) ^ (ε * (10 * a / ε)) := by rw [← ENNReal.rpow_mul]
      _ = (δ : ENNReal) ^ (10 * a) := by
        congr 1
        field_simp [ne_of_gt hε0]
  calc
    δt ^ (10 * a / ε) * δt ^ (-2 * γ) * ((u.card : ENNReal) * δt ^ (2 : ℕ)) ^ (1 - γ / 2)
        = δt ^ (10 * a / ε) *
            (δt ^ (-2 * γ) * ((u.card : ENNReal) * δt ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
        rw [mul_assoc]
    _ ≤ (δ : ENNReal) ^ (10 * a) *
            (δt ^ (-2 * γ) * ((u.card : ENNReal) * δt ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
        exact mul_le_mul hle le_rfl zero_le zero_le
    _ = (δ : ENNReal) ^ (10 * a) * δt ^ (-2 * γ) *
            ((u.card : ENNReal) * δt ^ (2 : ℕ)) ^ (1 - γ / 2) := by
        rw [← mul_assoc]

/-- The constant at which `Kakeya.ml1Boot.exists_normalizedMiddleData` returns the uniformity of
the rescaled family, given the uniformity constant `Cunif` of the input family and the two-sided
shading constant `Λ`.  It is a `max 1` of a raw value, so `1 ≤ ·` is a theorem
(`Kakeya.ml1Boot.normalizedUnif.one_le_C`) rather than an assumption. -/
noncomputable def normalizedUnif.C (Cunif Λ : NNReal) : NNReal :=
  max 1 (fineFactor.C * Cunif * Λ ^ 2)

/-- The uniformity constant of the normalized middle family is at least `1`. -/
theorem normalizedUnif.one_le_C (Cunif Λ : NNReal) : 1 ≤ normalizedUnif.C Cunif Λ :=
  le_max_left _ _

/-- **`Kakeya.ml1Boot.exists_fineNormalization` read at a named output scale** (blueprint
`lem:ml1bootFineNormalize`).

This is `Kakeya.ml1Boot.exists_fineNormalization` at the scales `τ ≤ θ ≤ 1`, with the output
scale presented as an arbitrary `dt` together with the identification `hdt : dt = fineScale τ θ`
in place of the literal `Kakeya.ml1Boot.fineScale τ θ`.  Nothing else changes.

Separating this out is not cosmetic: the consumers need the normalized tubes in the *type*
`ShadedTube dt E`, and no constant repairs a type, so the identification of the two scales has
to be performed before the existential is opened.  Doing it once here keeps that bookkeeping
out of every statement that strengthens the fine normalization.

The last five clauses are the construction-visibility clauses of
`Kakeya.ml1Boot.exists_fineNormalization`, carried through unchanged: with
`Ψ = Tube.rescaleMap T_θ C_N` they say `Ψ(U k) ⊆ T̃ k`, `(T̃ k).shade = Ψ((U k).shade)` and
`|T̃ k| ≤ (4 C_N) ^ 6 |Ψ(U k)|` for `k ∈ un`, `Ψ(T_θ) ⊆ B(0, 1/4)`, and — the fifth, added
last — the **core data** of `T̃ k`: its centre is `midpoint (Ψ (U k).x) (Ψ (U k).y)` and its
direction the unit vector of `Ψ (U k).y - Ψ (U k).x`.  The fifth is `rfl` in the construction
(`Tube.center_centredExtension`, `Tube.direction_centredExtension`), so it strengthens the
statement at no cost to the producer, and it is what lets
`Kakeya.ml1Boot.exists_itemIV_container_of_visibility` discharge every geometric hypothesis of
`Kakeya.ml1Boot.exists_itemIV_container_tube`.  They are quantified
over the **ambient** index set `un ⊇ u` — the one at which
`Kakeya.ml1Boot.exists_fineNormalization_lower` reads its item (iv) — while essential
distinctness, the density bracket and the multiplicity, fullness and Frostman items stay on `u`
and its refinement `u'`.  See the corresponding section of
`Kakeya.ml1Boot.exists_fineNormalization` for why the construction supplies the wider
quantifier for free.  Taking `un = u` recovers the plain reading. -/
theorem exists_fineNormalization_atScale (hdim : Module.finrank ℝ E = 3)
    {τ θ dt : NNReal} (hτ0 : 0 < τ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1) (hdt : dt = fineScale τ θ)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) {μ₀ : ENNReal} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u un : Finset ι} (Tθ : Tube θ E) (U : ι → ShadedTube τ E)
    (hu : u.Nonempty) (hun : u ⊆ un) (hTθ : Tθ.carrier ⊆ Metric.closedBall 0 1)
    (hsubn : ∀ k ∈ un, (U k).carrier ⊆ Tθ.carrier)
    (hED : (u : Set ι).Pairwise fun k k' => IsEssentiallyDistinct (U k).carrier (U k').carrier)
    (hdens : ∀ k ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * volume (U k).carrier ≤ volume (U k).shade ∧
      volume (U k).shade ≤ (Λ : ENNReal) * μ₀ * volume (U k).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ Ttil : ι → ShadedTube dt E,
      (u' : Set ι).Pairwise
          (fun k k' => IsEssentiallyDistinct (Ttil k).carrier (Ttil k').carrier) ∧
        (∀ k ∈ u', (Ttil k).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun k => (U k).toShadedBody)
            ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * (Λ : ENNReal) ^ 2
              * ShadedBody.multiplicity u' (fun k => (Ttil k).toShadedBody) ∧
        ShadedBody.fullness u (fun k => (U k).toShadedBody)
            ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * (Λ : ENNReal) ^ 2
              * ShadedBody.fullness u' (fun k => (Ttil k).toShadedBody) ∧
        frostmanConstIn u' (fun k => (Ttil k).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * frostmanConstIn u (fun k => (U k).toConvexSpaceBody) Tθ.toConvexSpaceBody ∧
        (∀ k ∈ un, Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' (U k).carrier
          ⊆ (Ttil k).carrier) ∧
        (∀ k ∈ un, (Ttil k).shade
          = Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' (U k).shade) ∧
        (∀ k ∈ un, volume (Ttil k).carrier
          ≤ (((4 * _root_.Tube.normalization.C 3) ^ 6 : NNReal) : ENNReal)
            * volume (Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
                '' (U k).carrier)) ∧
        Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' Tθ.carrier
          ⊆ Metric.closedBall (0 : E) (1 / 4) ∧
        (∀ k ∈ un, (Ttil k).toTube.center
              = midpoint ℝ (Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).x)
                  (Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).y) ∧
            (Ttil k).toTube.direction
              = ‖Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).y
                  - Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).x‖⁻¹
                • (Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).y
                  - Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).x)) := by
  subst hdt
  exact exists_fineNormalization hdim hτ0 hτθ hθ1 hΛ hμ₀ Tθ U hu hun hTθ hsubn hED hdens

/-- **The normalized member's core lies in `B(0, 3/4)`, and its centre in `B(0, 1/4)`.**

This is the corollary the fifth construction-visibility clause of
`Kakeya.ml1Boot.exists_fineNormalization_atScale` was added for, and it costs three lines: for
`k ∈ un` the source core endpoints `(U k).x`, `(U k).y` lie in `T_θ` by `hsubn`, so their
`Ψ`-images lie in `B(0, 1/4)` by the exposed clause `hv4`; `B(0, 1/4)` is convex, so the
midpoint — which the fifth clause identifies with `(T̃ k).center` — has norm at most `1/4`; and
`‖(T̃ k).direction‖ = 1` with `Tube.x_eq_center_sub`, `Tube.y_eq_center_add` then puts both core
endpoints of `T̃ k` inside `B(0, 3/4)`.

This is exactly the positional information
`Kakeya.ml1Boot.exists_container_tube_of_endpoints` consumes, and the hypothesis `hmk` of
`Kakeya.ml1Boot.exists_itemIV_container_tube`.  Before the fifth clause existed, the only
positional fact available about `T̃ k` was `T̃ k ⊆ B(0,1)`, which gives `‖x‖, ‖y‖ ≤ 1 - dt` and
is not enough once `ρt > dt`. -/
theorem norm_core_le_of_fineNormalization {θ τ dt : NNReal}
    {ι : Type*} {un : Finset ι} (Tθ : Tube θ E) (U : ι → ShadedTube τ E)
    (Ttil : ι → ShadedTube dt E)
    (hsubn : ∀ k ∈ un, (U k).carrier ⊆ Tθ.carrier)
    (hv4 : Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' Tθ.carrier
      ⊆ Metric.closedBall (0 : E) (1 / 4))
    (hv5 : ∀ k ∈ un, (Ttil k).toTube.center
          = midpoint ℝ (Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).x)
              (Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).y) ∧
        (Ttil k).toTube.direction
          = ‖Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).y
              - Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).x‖⁻¹
            • (Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).y
              - Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (U k).x)) :
    ∀ k ∈ un, ‖(Ttil k).toTube.center‖ ≤ 1 / 4 ∧ ‖(Ttil k).toTube.x‖ ≤ 3 / 4
      ∧ ‖(Ttil k).toTube.y‖ ≤ 3 / 4 := by
  intro k hk
  set Ψ := Tθ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) with hΨ
  have hmem : ∀ z ∈ (U k).carrier, Ψ z ∈ Metric.closedBall (0 : E) (1 / 4) := by
    intro z hz
    exact hv4 ⟨z, hsubn k hk hz, rfl⟩
  have hx : Ψ (U k).x ∈ Metric.closedBall (0 : E) (1 / 4) :=
    hmem _ (_root_.Tube.x_mem_carrier (U k).toTube)
  have hy : Ψ (U k).y ∈ Metric.closedBall (0 : E) (1 / 4) :=
    hmem _ (_root_.Tube.y_mem_carrier (U k).toTube)
  have hcen : ‖(Ttil k).toTube.center‖ ≤ 1 / 4 := by
    rw [(hv5 k hk).1]
    have hmid : midpoint ℝ (Ψ (U k).x) (Ψ (U k).y) ∈ Metric.closedBall (0 : E) (1 / 4) :=
      (convex_closedBall (0 : E) (1 / 4)).segment_subset hx hy
        (midpoint_mem_segment _ _)
    simpa [Metric.mem_closedBall, dist_zero_right] using hmid
  have hdir : ‖(Ttil k).toTube.direction‖ = 1 := (Ttil k).toTube.norm_direction
  refine ⟨hcen, ?_, ?_⟩
  · rw [_root_.Tube.x_eq_center_sub]
    calc ‖(Ttil k).toTube.center - (1 / 2 : ℝ) • (Ttil k).toTube.direction‖
        ≤ ‖(Ttil k).toTube.center‖ + ‖(1 / 2 : ℝ) • (Ttil k).toTube.direction‖ :=
          norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 2 := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, hdir]
          norm_num
      _ = 3 / 4 := by norm_num
  · rw [_root_.Tube.y_eq_center_add]
    calc ‖(Ttil k).toTube.center + (1 / 2 : ℝ) • (Ttil k).toTube.direction‖
        ≤ ‖(Ttil k).toTube.center‖ + ‖(1 / 2 : ℝ) • (Ttil k).toTube.direction‖ :=
          norm_add_le _ _
      _ ≤ 1 / 4 + 1 / 2 := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, hdir]
          norm_num
      _ = 3 / 4 := by norm_num

/-- **The one container tube of item (iv), assembled from what the normalization exposes.**

This is `Kakeya.ml1Boot.exists_itemIV_container_tube` (Rescaling/Hybrid.lean) with every
hypothesis discharged from the construction-visibility clauses of
`Kakeya.ml1Boot.exists_fineNormalization_atScale`, the fifth of which — the core data of the
output tube — was added for exactly this purpose.  Given

* the transported source container `S_ρ` of
  `Kakeya.ml1Boot.exists_rescaled_source_container`, presented through its centre and
  direction (`hScen`, `hSdir`), and
* the source container `T_σ` at `σ = ρt θ` with `T_σ ⊆ T_θ` and `U k ⊆ T_σ`,

it produces a single `ρt`-tube `T_ρ` inside `B(0,1)` which contains the member `T̃ k`, whose
`2`-dilate contains `S_ρ`, and whose `2`-dilate contains `T̃ i` for **every** ambient `i` whose
source body is caught by `T_σ`.  That last clause is the pinned `hVK` of
`ConvexSpaceBody.le_frostmanConstIn_of_transport_of_source_doubling`, and the reason the
existentially quantified enlargement form does not serve.

The four numerical inputs are `R ≥ 4` (true at `R = Tube.normalization.C 3 = 64`), `dt ≤ 1/4`,
`ρt ≤ 1/4` and `dt ≤ ρt`.  They enter only through the two centre estimates
`Kakeya.ml1Boot.norm_rescaleMap_sub_le_of_mem_carrier` — which gives
`(4R)⁻¹ (3 + 2 ρt) ≤ 7/32`, so the axial clauses have `1/2 - 1/4 - 7/32 > 0` to spare — and
`Kakeya.ml1Boot.norm_perp_rescaleMap_sub_le_of_mem_carrier`, which gives `(4R)⁻¹ 2 ρt ≤ ρt/8`,
the only clause that has to beat `ρt` itself.

What this lemma does **not** supply is the `hdilate` clause of
`ConvexSpaceBody.frostmanConstIn_ge_of_comparable`; see the "Proof status" section of
`Kakeya.ml1Boot.exists_fineNormalization_lower`. -/
theorem exists_itemIV_container_of_visibility [Nontrivial E] {θ τ dt ρt : NNReal} {R : ℝ}
    (hR4 : (4 : ℝ) ≤ R)
    (hθ0 : (0 : ℝ) < (θ : ℝ)) (hθ1 : (θ : ℝ) ≤ 1) (hτ0 : 0 < τ)
    (hdt0 : (0 : ℝ) < (dt : ℝ)) (hdtdiv : (dt : ℝ) = (τ : ℝ) / (θ : ℝ))
    (hdtρ : (dt : ℝ) ≤ (ρt : ℝ)) (hdt4 : (dt : ℝ) ≤ 1 / 4) (hρ4 : (ρt : ℝ) ≤ 1 / 4)
    {ι : Type*} {un : Finset ι} (Tθ : Tube θ E) (U : ι → ShadedTube τ E)
    (Ttil : ι → ShadedTube dt E) (Tσ : Tube (ρt * θ) E) (Sρ : Tube ρt E)
    (k : ι) (hk : k ∈ un)
    (hSdir : Sρ.direction = ‖Tθ.normalizationLinear Tσ.direction‖⁻¹
        • Tθ.normalizationLinear Tσ.direction)
    (hScen : Sρ.center = Tθ.rescaleMap R Tσ.center)
    (hTσθ : Tσ.carrier ⊆ Tθ.carrier) (hUk : (U k).carrier ⊆ Tσ.carrier)
    (hsubn : ∀ i ∈ un, (U i).carrier ⊆ Tθ.carrier)
    (hv4 : Tθ.rescaleMap R '' Tθ.carrier ⊆ Metric.closedBall (0 : E) (1 / 4))
    (hv5 : ∀ i ∈ un, (Ttil i).toTube.center
          = midpoint ℝ (Tθ.rescaleMap R (U i).x) (Tθ.rescaleMap R (U i).y) ∧
        (Ttil i).toTube.direction = ‖Tθ.rescaleMap R (U i).y - Tθ.rescaleMap R (U i).x‖⁻¹
            • (Tθ.rescaleMap R (U i).y - Tθ.rescaleMap R (U i).x)) :
    ∃ Tρ : Tube ρt E, Tρ.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
      Sρ.toConvexSpaceBody ≤ Kakeya.Tube.dilate Tρ 2 ∧
      ∀ i ∈ un, (U i).carrier ⊆ Tσ.carrier →
        (Ttil i).toConvexSpaceBody ≤ Kakeya.Tube.dilate Tρ 2 := by
  classical
  have hR0 : (0 : ℝ) < R := by linarith
  have hρ0 : (0 : ℝ) < (ρt : ℝ) := lt_of_lt_of_le hdt0 hdtρ
  have hρ0' : 0 < ρt := by exact_mod_cast hρ0
  have hθ0' : 0 < θ := by exact_mod_cast hθ0
  have hσ0 : 0 < ρt * θ := mul_pos hρ0' hθ0'
  -- `σ / θ = ρt`
  have hσθdiv : (((ρt * θ : NNReal) : ℝ)) / (θ : ℝ) = (ρt : ℝ) := by
    rw [NNReal.coe_mul]; field_simp
  have hσθ : (((ρt * θ : NNReal) : ℝ)) ≤ (θ : ℝ) := by
    rw [NNReal.coe_mul]
    nlinarith [hρ4, hθ0]
  have hτσ : (τ : ℝ) ≤ (((ρt * θ : NNReal) : ℝ)) := by
    rw [NNReal.coe_mul]
    have hτeq : (τ : ℝ) = (dt : ℝ) * (θ : ℝ) := by rw [hdtdiv]; field_simp
    rw [hτeq]
    exact mul_le_mul_of_nonneg_right hdtρ hθ0.le
  -- the centre of a tube lies in its carrier
  have hcm : ∀ {r : NNReal} (S : Tube r E), 0 < r → S.center ∈ S.carrier := by
    intro r S hr
    have h := _root_.Tube.midpoint_mem_carrier hr S
    have hmc : S.midpoint = S.center := by
      change (1 / 2 : ℝ) • (S.x + S.y) = midpoint ℝ S.x S.y
      rw [midpoint_eq_smul_add]
      norm_num
    rwa [hmc] at h
  -- the fifth visibility clause, read on centres and directions
  have hcen : ∀ i ∈ un, (Ttil i).toTube.center = Tθ.rescaleMap R (U i).toTube.center := by
    intro i hi
    rw [(hv5 i hi).1]
    exact (AffineMap.map_midpoint (Tθ.rescaleMap R) (U i).x (U i).y).symm
  have hdirid : ∀ i ∈ un, (Ttil i).toTube.direction
      = ‖Tθ.normalizationLinear (U i).toTube.direction‖⁻¹
          • Tθ.normalizationLinear (U i).toTube.direction := by
    intro i hi
    rw [(hv5 i hi).2, rescaleMap_sub]
    exact normalize_smul (by positivity) _
  -- the two centre estimates, at the container
  have hdiam : ∀ z ∈ Tσ.carrier, ∀ z' ∈ Tσ.carrier,
      ‖Tθ.rescaleMap R z - Tθ.rescaleMap R z'‖ ≤ 7 / 32 := by
    intro z hz z' hz'
    have h := norm_rescaleMap_sub_le_of_mem_carrier hR0 hθ0 hθ1 hσθ Tθ Tσ hTσθ hz hz'
    have heq : (4 * R)⁻¹ * (3 + 2 * (((ρt * θ : NNReal) : ℝ)) / (θ : ℝ))
        = (4 * R)⁻¹ * (3 + 2 * (ρt : ℝ)) := by
      rw [NNReal.coe_mul]; field_simp
    rw [heq] at h
    refine h.trans ?_
    have h1 : (4 * R)⁻¹ ≤ (16 : ℝ)⁻¹ := by
      have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16) (by linarith : (16:ℝ) ≤ 4 * R)
      simpa [one_div] using this
    have h2 : (3 : ℝ) + 2 * (ρt : ℝ) ≤ 7 / 2 := by linarith
    calc (4 * R)⁻¹ * (3 + 2 * (ρt : ℝ)) ≤ (16 : ℝ)⁻¹ * (7 / 2) := by
          apply mul_le_mul h1 h2 (by linarith) (by norm_num)
      _ = 7 / 32 := by norm_num
  have hdperp : ∀ z ∈ Tσ.carrier, ∀ z' ∈ Tσ.carrier,
      ‖(Tθ.rescaleMap R z - Tθ.rescaleMap R z')
        - (inner ℝ Sρ.direction (Tθ.rescaleMap R z - Tθ.rescaleMap R z') : ℝ)
          • Sρ.direction‖ ≤ (ρt : ℝ) := by
    intro z hz z' hz'
    rw [hSdir]
    have h := norm_perp_rescaleMap_sub_le_of_mem_carrier hR0 hθ0 hθ1 Tθ Tσ hz hz'
    have heq : (4 * R)⁻¹ * (2 * (((ρt * θ : NNReal) : ℝ)) / (θ : ℝ))
        = (4 * R)⁻¹ * (2 * (ρt : ℝ)) := by
      rw [NNReal.coe_mul]; field_simp
    rw [heq] at h
    refine h.trans ?_
    have h1 : (4 * R)⁻¹ ≤ (16 : ℝ)⁻¹ := by
      have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16) (by linarith : (16:ℝ) ≤ 4 * R)
      simpa [one_div] using this
    calc (4 * R)⁻¹ * (2 * (ρt : ℝ)) ≤ (16 : ℝ)⁻¹ * (2 * (ρt : ℝ)) := by
          apply mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ (ρt : ℝ) := by linarith
  -- the filtered ambient set
  set un' : Finset ι := un.filter (fun i => (U i).carrier ⊆ Tσ.carrier) with hun'def
  have hk' : k ∈ un' := Finset.mem_filter.mpr ⟨hk, hUk⟩
  have hmem' : ∀ i ∈ un', i ∈ un := fun i hi => (Finset.mem_filter.mp hi).1
  have hsub' : ∀ i ∈ un', (U i).carrier ⊆ Tσ.carrier := fun i hi => (Finset.mem_filter.mp hi).2
  have hctr : ∀ i ∈ un', (U i).toTube.center ∈ Tσ.carrier := fun i hi =>
    hsub' i hi (hcm (U i).toTube hτ0)
  have hcentre : ∀ i ∈ un', (Ttil i).toTube.center = Tθ.rescaleMap R (U i).toTube.center :=
    fun i hi => hcen i (hmem' i hi)
  -- the hypotheses of the hybrid container
  have hmk : ‖(Ttil k).toTube.center‖ ≤ 1 / 4 := by
    rw [hcen k hk]
    have hmemball : Tθ.rescaleMap R (U k).toTube.center ∈ Metric.closedBall (0 : E) (1 / 4) :=
      hv4 ⟨(U k).toTube.center, hsubn k hk (hcm (U k).toTube hτ0), rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hmemball
  have hdir : ∀ i ∈ un', ‖(Ttil i).toTube.direction
      - (inner ℝ Sρ.direction (Ttil i).toTube.direction : ℝ) • Sρ.direction‖
        ≤ 2 * ((ρt : ℝ) - (dt : ℝ)) := by
    intro i hi
    rw [hdirid i (hmem' i hi), hSdir]
    have h := norm_perp_direction_normalized_le (τ := τ) (σ := ρt * θ) hθ0 hθ1 hτσ
      Tθ Tσ (U i).toTube (hsub' i hi)
    refine h.trans ?_
    have heq : 2 * ((((ρt * θ : NNReal) : ℝ)) - (τ : ℝ)) / (θ : ℝ)
        = 2 * ((ρt : ℝ) - (dt : ℝ)) := by
      rw [NNReal.coe_mul, hdtdiv]
      field_simp
    exact le_of_eq heq
  have hax : ∀ i ∈ un', |(inner ℝ Sρ.direction
      ((Ttil i).toTube.center - (Ttil k).toTube.center) : ℝ)| + (dt : ℝ) ≤ 1 / 2 := by
    intro i hi
    have hb := hdiam _ (hctr i hi) _ (hctr k hk')
    rw [← hcentre i hi, ← hcentre k hk'] at hb
    have := abs_inner_le Sρ.norm_direction
      ((Ttil i).toTube.center - (Ttil k).toTube.center)
    linarith
  have hperp : ∀ i ∈ un', ‖((Ttil i).toTube.center - (Ttil k).toTube.center)
      - (inner ℝ Sρ.direction ((Ttil i).toTube.center - (Ttil k).toTube.center) : ℝ)
        • Sρ.direction‖ ≤ (ρt : ℝ) := by
    intro i hi
    have hb := hdperp _ (hctr i hi) _ (hctr k hk')
    rwa [← hcentre i hi, ← hcentre k hk'] at hb
  have hSax : |(inner ℝ Sρ.direction (Sρ.center - (Ttil k).toTube.center) : ℝ)|
      + (ρt : ℝ) ≤ 1 / 2 := by
    have hb := hdiam _ (hcm Tσ hσ0) _ (hctr k hk')
    rw [← hScen, ← hcentre k hk'] at hb
    have := abs_inner_le Sρ.norm_direction (Sρ.center - (Ttil k).toTube.center)
    linarith
  have hSperp : ‖(Sρ.center - (Ttil k).toTube.center)
      - (inner ℝ Sρ.direction (Sρ.center - (Ttil k).toTube.center) : ℝ) • Sρ.direction‖
        ≤ (ρt : ℝ) := by
    have hb := hdperp _ (hcm Tσ hσ0) _ (hctr k hk')
    rwa [← hScen, ← hcentre k hk'] at hb
  obtain ⟨Tρ, -, -, hball, hmemk, hSρ, hall⟩ :=
    exists_itemIV_container_tube (dt := dt) (ρt := ρt) (un := un')
      (fun i => (Ttil i).toTube) k hk' Sρ hρ4 hdtρ hmk hdir hax hperp hSax hSperp
  exact ⟨Tρ, hball, hmemk, hSρ, fun i hi hsubi =>
    hall i (Finset.mem_filter.mpr ⟨hi, hsubi⟩)⟩

/-- **The ambient Frostman lower bound restricts freely along a refinement of its quantifier**
(blueprint `note:ml1bootRescaledLowerAmbient`).

The hypothesis (b) of `Kakeya.ml1Boot.exists_normalizedMiddleData` reads the Frostman *lower*
bound at an ambient index set `un`, which is *not* refined, and quantifies over the members `k`
of `u`, which is.  Restricting a universally quantified statement to a smaller quantifier range
costs nothing, and that is all this lemma records.

It is stated separately because the temptation it rules out is a real one: the superseded form
of the surrounding statements read the bound at `u` and asked for it at a refinement `u' ⊆ u`,
which needs a Frostman lower bound to move from a family to a subfamily.  That principle is
false (blueprint `note:ml1bootLowerFrostmanRetired`), the repository has no lemma of that shape
— only the upper-direction `ConvexSpaceBody.frostmanConstIn_subfamily_le` — and the ambient
reading exists exactly so that nothing of the kind is ever needed. -/
theorem ambientLowerFrostman_restrict {ε e n : ℝ} {δ τ θ : NNReal}
    {ι : Type*} {u u' un : Finset ι} (hu'u : u' ⊆ u)
    (Tθ : Tube θ E) (U : ι → ShadedTube τ E)
    (hFb : ∀ σ : NNReal, τ * (θ / τ) ^ (5 * ε) ≤ σ → σ ≤ θ * (τ / θ) ^ (5 * ε) → ∀ k ∈ u,
      ∃ Tσ : Tube σ E, Tσ.toConvexSpaceBody ≤ Tθ.toConvexSpaceBody ∧
        (U k).toConvexSpaceBody ≤ Tσ.toConvexSpaceBody ∧
        (δ : ENNReal) ^ e * ((σ / τ : NNReal) : ENNReal) ^ n
          ≤ frostmanConstIn
              (familyIn un (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody)
              (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody ∧
        (∀ D : ConvexSpaceBody E, Tσ.toConvexSpaceBody ≤ D →
          volume D.carrier ≤ (fineFactor.C : ENNReal) * volume Tσ.carrier →
          densityIn un (fun k' => (U k').toConvexSpaceBody) D
            ≤ (fineFactor.C : ENNReal)
              * densityIn un (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody)) :
    ∀ σ : NNReal, τ * (θ / τ) ^ (5 * ε) ≤ σ → σ ≤ θ * (τ / θ) ^ (5 * ε) → ∀ k ∈ u',
      ∃ Tσ : Tube σ E, Tσ.toConvexSpaceBody ≤ Tθ.toConvexSpaceBody ∧
        (U k).toConvexSpaceBody ≤ Tσ.toConvexSpaceBody ∧
        (δ : ENNReal) ^ e * ((σ / τ : NNReal) : ENNReal) ^ n
          ≤ frostmanConstIn
              (familyIn un (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody)
              (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody ∧
        (∀ D : ConvexSpaceBody E, Tσ.toConvexSpaceBody ≤ D →
          volume D.carrier ≤ (fineFactor.C : ENNReal) * volume Tσ.carrier →
          densityIn un (fun k' => (U k').toConvexSpaceBody) D
            ≤ (fineFactor.C : ENNReal)
              * densityIn un (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody) := by
  exact fun sigma h1 h2 k hk => hFb sigma h1 h2 k (hu'u hk)





end Rescale

end ml1Boot

end Kakeya
open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya
namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The separation and quarter hypotheses identify the truncated fine scale with the raw ratio. -/
theorem fineScale_eq_div_of_sep_quarter {ε : ℝ} {δ τ θ : NNReal}
    (hδ0 : 0 < δ) (hδτ : δ ≤ τ) (hτθ : τ ≤ θ)
    (hsep : τ ≤ δ ^ ε * θ) (hquarter : δ ^ ε ≤ 1 / 4) :
    fineScale τ θ = τ / θ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ0 hδτ
  have hθ0 : 0 < θ := lt_of_lt_of_le hτ0 hτθ
  have hdiv : τ / θ ≤ δ ^ ε := NNReal.div_le_of_le_mul hsep
  have hq : τ / θ ≤ 1 / 4 := hdiv.trans hquarter
  exact min_eq_left hq

/-- The same bridge in the orientation used by normalized-family consumers. -/
theorem div_eq_fineScale_of_sep_quarter {ε : ℝ} {δ τ θ : NNReal}
    (hδ0 : 0 < δ) (hδτ : δ ≤ τ) (hτθ : τ ≤ θ)
    (hsep : τ ≤ δ ^ ε * θ) (hquarter : δ ^ ε ≤ 1 / 4) :
    τ / θ = fineScale τ θ := by
  exact (fineScale_eq_div_of_sep_quarter hδ0 hδτ hτθ hsep hquarter).symm

end ml1Boot
end Kakeya
